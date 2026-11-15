/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Oracle.RunState
public import CslibFrontier.Computability.Probabilistic.Oracle.Memoize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Plain numerical contracts for stateful oracle substitution

The closed client keeps a sampled bit correlated between the answer and private state. The open
client memoizes bounded reply prefixes while preserving the external oracle's state. The last
client has no queries and uses a zero resource allowance.
-/

public section

namespace CslibFrontierTests.OraclePlainSubstitution

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

noncomputable def requestHead (_ : List Bool) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), [])

theorem requestHead_isOraclePPTOn : IsOraclePPTOn encBits encBits requestHead :=
  IsOraclePPTOn.query_take' () (.const []) (.const 1)

noncomputable def respond (caller : List Bool) (_ : Unit × List Bool)
    (state : List Bool) : ProbComp (List Bool × List Bool) := do
  let bit ← ProbComp.uniform Bool
  return (bit :: caller, bit :: state)

-- Preparation, initial state and allowance are plain certificates; the invariant and both
-- resource inequalities are proved for every supported handler result.
example : IsPPTOn encBits (encPair encBits encBits) (fun word =>
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (respond word))
        (requestHead word)).run word) := by
  apply requestHead_isOraclePPTOn.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (resources := fun caller _ => caller.length + 1)
    (by fun_prop) (by unfold respond; fun_prop)
    (by fun_prop) (fun caller state => caller.length ≤ state.length)
    (fun _ => le_rfl) (by fun_prop)
  intro caller request state hstate result hresult
  simp only [respond, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨bit, _, hresult⟩ := hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp only [encBits_apply, List.length_cons]
  exact ⟨by lia, le_rfl, by lia⟩

-- The output bit remains correlated with the final private state, including empty input.
example (word : List Bool) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (respond word))
        (requestHead word)).run word) =
      (PMF.uniformOfFintype Bool).map (fun bit => ([bit], bit :: word)) := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [requestHead, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  simp [respond, PMF.map_comp, Function.comp_def]

noncomputable def client (n : ℕ) : WordOracleComp Unit (List Bool) := do
  let first ← List.take n <$> ProbOracleComp.query ((), [])
  let second ← List.take n <$> ProbOracleComp.query ((), first)
  let third ← List.take n <$> ProbOracleComp.query ((), [])
  pure (second ++ third)

theorem client_isOraclePPTOn : IsOraclePPTOn encUnary encBits client := by
  unfold client
  fun_prop

noncomputable def cached (n : ℕ) (request : Unit × List Bool)
    (cache : List (List Bool × List Bool)) :
    WordOracleComp Unit (List Bool × List (List Bool × List Bool)) :=
  memoize (fun key => List.take n <$> ProbOracleComp.query ((), key)) request.2 cache

theorem cached_isOraclePPTOn : IsOraclePPTOn
    (encPair encUnary
      (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encBits encBits))))
    (encPair encBits (encList (encPair encBits encBits)))
    (fun pair => cached pair.1 pair.2.1 pair.2.2) := by
  unfold cached
  fun_prop

noncomputable def twoLevel (n : ℕ) :
    WordOracleComp Unit (List Bool × List (List Bool × List Bool)) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (cached n)) (client n)).run []

example : IsOraclePPTOn encUnary (encPair encBits (encList (encPair encBits encBits)))
    twoLevel := by
  unfold twoLevel
  apply client_isOraclePPTOn.run_interpret_preprocess_open
    (resources := fun n request => 4 * request.length + 2 * n + 3)
    (by fun_prop) cached_isOraclePPTOn (.const [])
    (fun n cache => ∀ entry ∈ cache, entry.2.length ≤ n) (by simp) (by fun_prop)
  intro n request cache hcache result hresult
  obtain ⟨hreply, hcache', hgrowth⟩ := ProbOracleComp.memoize_call_size_le encBits encBits
    _ request.2 cache n hcache (fun value hvalue => by
      obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hvalue
      exact List.length_take_le _ _) hresult
  exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by lia), by
    simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩

noncomputable def firstOnes (_ : Unit × List Bool) : StateT ℕ PMF (List Bool) :=
  fun calls => PMF.pure (List.replicate 5 (decide (calls = 0)), calls + 1)

-- A cache hit makes no external call. The joint result records the external counter too.
example :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) firstOnes)
        (twoLevel 3)).run 0 =
      PMF.pure (([false, false, false, true, true, true],
        [([true, true, true], [false, false, false]), ([], [true, true, true])]), 2) := by
  change ProbOracleComp.runWith firstOnes (twoLevel 3) 0 = _
  rw [twoLevel, ProbOracleComp.runWith_run_interpret]
  simp [client, cached, memoize, StateT.run, firstOnes, List.lookup]

-- No query is made at all, so a handler returning no bits and unchanged state has allowance 0.
example : IsPPTOn encBits (encPair encBits encBits) (fun word =>
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun (_ : Unit × List Bool) (state : List Bool) =>
          (pure ([], state) : ProbComp (List Bool × List Bool))))
        (pure word : WordOracleComp Unit (List Bool))).run word) := by
  have hp : IsOraclePPTOn encBits encBits
      (fun word => (pure word : WordOracleComp Unit (List Bool))) := by fun_prop
  apply hp.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (resources := fun _ _ => 0) (by fun_prop) (by fun_prop)
    (by fun_prop) (fun _ _ => True) (fun _ => trivial) (.const 0)
  intro caller request state _ result hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp only [encBits_apply, List.length_nil, Nat.add_zero]
  exact ⟨trivial, Nat.le_refl 0, le_rfl⟩

end CslibFrontierTests.OraclePlainSubstitution
