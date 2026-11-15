/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CircularCorrelationRobust
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.PPT

/-!
# Circular correlation robustness is not vacuous

The constant hash, which answers every label and tweak with the empty word, is not circular
correlation robust. At level `k`, `CCR.atLevel` pads its answer to the zero label, so the circular
oracle answers the query `((0, false), 0, false)` with the zero label under every offset key, while
a random function answers it with a uniform label. The distinguisher `firstBitZero` asks that one
query and accepts when the first bit of the reply is `false`. It is oracle PPT and asks one query,
so it is tweak-unique at every level, and its advantage is `1 / 2` at every level.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.CircularCorrelationRobust

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Garbling Turing.MultiTapeTM

/-- The constant hash: every label and tweak hash to the empty word. -/
def constHash : List Bool → List Bool → List Bool := fun _ _ => []

/-- The constant hash is evaluated in polynomial time, so it fails circular correlation robustness
only through the security condition. -/
theorem constHash_polyTime :
    ComputableInPolyTime (fun (label, tweak) => constHash label tweak) (encPair encBits encBits)
      encBits :=
  ComputableInPolyTime.const []

/-- The query `((0, false), 0, false)` at level `k`. -/
def zeroQuery (k : ℕ) : CCR.Query (BitString (k + 1) × Bool) (BitString k) :=
  ⟨(0, false), 0, false⟩

/-- The request of `zeroQuery k` is the all-zero word of `2 k + 3` bits. -/
theorem encodeQuery_zeroQuery (k : ℕ) :
    (CCR.codec k).encodeQuery (zeroQuery k) = ((), List.replicate (2 * k + 3) false) := by
  have hzero (n : ℕ) : List.ofFn (0 : BitString n) = List.replicate n false := by
    rw [← List.ofFn_const]
    rfl
  simp only [CCR.codec, zeroQuery, hzero, Prod.mk.injEq, true_and, List.eq_replicate_iff]
  constructor
  · simp
    omega
  · simp

/-- Ask `zeroQuery k` and accept when the first bit of the reply is `false`. -/
noncomputable def firstBitZero : OracleDistinguisher := fun k _ => do
  let reply ← List.take 1 <$> ProbOracleComp.query ((), List.replicate (2 * k + 3) false)
  return !(reply.headD true)

theorem firstBitZero_isOraclePPT : IsOraclePPT encBool firstBitZero := by
  have hq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate (2 * p.1 + 3) false)
      (encPair encUnary encBits) encBits := by
    polytime
  have hlim : ComputableInPolyTime (fun _ : ℕ × List Bool => 1) (encPair encUnary encBits)
      encUnary :=
    ComputableInPolyTime.const 1
  have hout : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => !(p.2.headD true))
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold firstBitZero
  exact ((IsOraclePPTOn.query_take' () hq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

/-- `firstBitZero` asks one query, so it never repeats a tweak. -/
theorem firstBitZero_isTweakUnique (k : ℕ) :
    CCR.IsTweakUnique ((CCR.codec k).adapt (firstBitZero k [])) := by
  intro t
  refine (CCR.codec k).isCostBounded_adapt (wordCost := fun _ => 1) (fun _ => by split <;> simp)
    ?_
  unfold firstBitZero
  exact (((OracleComp.isCostBounded_map_iff _ _ _).mpr
    (ProbOracleComp.isCostBounded_query _ _)).bind fun _ => .pure _ 0).mono le_rfl

/-- Against the constant hash the circular oracle answers `zeroQuery k` with the zero label, so
`firstBitZero` always accepts. -/
theorem eval_realExperiment_firstBitZero (k : ℕ) :
    ProbComp.eval (PRF.realExperiment
      (CCR.keyed (CCR.atLevel constHash k) CCR.offset CCR.offset)
      ((CCR.codec k).adapt (firstBitZero k []))) = PMF.pure true := by
  have hdecode := (CCR.codec k).decodeQuery_encodeQuery (zeroQuery k)
  rw [encodeQuery_zeroQuery] at hdecode
  have hconst (x : BitString (k + 1) × Bool) (t : BitString k) :
      CCR.atLevel constHash k x t = 0 := by
    obtain ⟨_, _⟩ := x
    rfl
  have hreply (R : BitString (k + 1)) : List.take 1 ((CCR.codec k).encodeReply (zeroQuery k)
      (CCR.keyed (CCR.atLevel constHash k) CCR.offset CCR.offset R (zeroQuery k))) = [false] := by
    have hzero : (0 : Bool) = false := rfl
    simp [CCR.keyed, CCR.oracle, hconst, zeroQuery, CCR.codec, labelCodec, List.ofFn_succ, hzero]
  simp only [PRF.realExperiment, OracleCodec.run_adapt, firstBitZero, ProbOracleComp.run_bind,
    ProbOracleComp.run_map, ProbOracleComp.run_query, OracleCodec.wordOracle, hdecode, map_pure,
    hreply, pure_bind, ProbOracleComp.run_pure, List.headD_cons, Bool.not_false,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

/-- Against a random function `firstBitZero` accepts with probability `1 / 2`. -/
theorem eval_idealExperiment_firstBitZero (k : ℕ) :
    ProbComp.eval (PRF.idealExperiment ((CCR.codec k).adapt (firstBitZero k []))) =
      PMF.uniformOfFintype Bool := by
  have hdecode := (CCR.codec k).decodeQuery_encodeQuery (zeroQuery k)
  rw [encodeQuery_zeroQuery] at hdecode
  have hreply (label : BitString (k + 1) × Bool) :
      (List.take 1 ((CCR.codec k).encodeReply (zeroQuery k) label)).headD true = label.1 0 := by
    obtain ⟨key, colour⟩ := label
    simp [CCR.codec, labelCodec, List.ofFn_succ]
  simp only [PRF.idealExperiment, OracleCodec.run_adapt, firstBitZero, ProbOracleComp.run_bind,
    ProbOracleComp.run_map, ProbOracleComp.run_query, OracleCodec.wordOracle, hdecode, map_pure,
    pure_bind, ProbOracleComp.run_pure, hreply, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  have hquery : (PMF.uniformOfFintype
      (CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool)).map
        (fun f => f (zeroQuery k)) = PMF.uniformOfFintype (BitString (k + 1) × Bool) := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have hbit : (PMF.uniformOfFintype (BitString (k + 1))).map (fun key => key 0) =
      PMF.uniformOfFintype Bool := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have hnot : (PMF.uniformOfFintype Bool).map Bool.not = PMF.uniformOfFintype Bool := by
    ext b
    cases b <;> simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  conv_rhs => rw [← hnot, ← hbit, ← Cslib.Probability.PMF.uniformOfFintype_prod_map_fst (β := Bool),
    ← hquery, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  rfl

/-- **The constant hash is not circular correlation robust**: `firstBitZero` is admissible and its
advantage is `1 / 2` at every level. -/
theorem not_circularCorrelationRobust_constHash : ¬ CircularCorrelationRobust constHash := by
  intro h
  have hneg := h.secure firstBitZero ⟨firstBitZero_isOraclePPT, firstBitZero_isTweakUnique⟩
  simp only [eval_realExperiment_firstBitZero, eval_idealExperiment_firstBitZero] at hneg
  refine not_negligible_const ?_ hneg
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

end CslibFrontierTests.Crypto.CircularCorrelationRobust
