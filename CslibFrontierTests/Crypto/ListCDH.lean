/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.ListCDHFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.UniformIndex

/-!
# The list form of CDH: checked instances

An ordinary `module` client of `CslibFrontier.Crypto.Computational.DiffieHellman.ListCDH` and
`CslibFrontier.Crypto.Computational.DiffieHellman.ListCDHFamily` ([BonehShoup2023],
Section 21.11.4), of the probability lemmas they use, and of the capped residue sampler
`Cslib.ProbComp.sampleModIndex` and its certificate.

* A uniform index below `3` selects the only entry of a one-entry list with probability at least
  `1 / 3`, and a uniform index below `2` selects `x` from `[x, x]` with probability `1`. A bound
  at one outcome of every continuation survives an initial draw even where it fails at the other
  outcome, and so does an affine bound, whose constant is not multiplied.
* `sampleModIndex width 0` returns `0`, `sampleModIndex width 3` is `sampleModNat width 3`, and the
  sampler is PPT with `width n = n` and bound `3`.
* In `ZMod 7` with `g = 1`: at `Q = 0` the list experiment is never won; an adversary that returns
  the Diffie–Hellman value always wins for every `Q ≠ 0`, and the bound makes the reduction always
  right at `Q = 1` and right with probability at least `1 / 3` at `Q = 3`, larger than the list's
  length; an adversary that returns the Diffie–Hellman value twice is handled by the same bound;
  past the end of its list the reduction returns `g`; an entry beyond the first `Q` does not
  count; and the general bound applies to the deterministic index `0` at `Q = 1` with factor `1`.
  With the fair-coin index, the bound at `Q = 0` says the list experiment is never won, and at
  `Q = 3`, not a power of two, it gives `1 ≤ 3 * p + 9 / 2 ^ width` for the reduction's success
  probability `p`.
* Over any prime-order group family, the game unfolds to the fixed-group experiment, the PPT
  predicate is satisfied by the adversary that returns its two inputs, and the certificate, the
  loss bound and the conclusion under CDH apply to it with `width n = n` and `Q n = n`, including
  on Schnorr groups. The loss bound is also applied with `Q n = 0` and `Q n = 3`, and the success
  probability does not decrease from `Q n = 1` to `Q n = n + 1`.
-/

public section

namespace CslibFrontierTests.Crypto.ListCDH

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### The probability lemmas -/

/-- A member of a list shorter than `Q` is selected with probability at least `1 / Q`: the entry
`5` of `[5]` with `Q = 3`, although two of the three positions fall past the end. -/
example : ((3 : ℕ) : ℝ≥0∞)⁻¹ ≤
    (PMF.uniformOfFintype (Fin 3)).map (fun i : Fin 3 => [(5 : ZMod 7)].getD i 0) 5 :=
  PMF.inv_le_map_uniformOfFintype_getD 0 (by decide)

/-- The same through membership in the first `Q` entries: `5` is the first entry of `[5, 2]`. -/
example : ((1 : ℕ) : ℝ≥0∞)⁻¹ ≤
    (PMF.uniformOfFintype (Fin 1)).map (fun i : Fin 1 => [(5 : ZMod 7), 2].getD i 0) 5 :=
  PMF.inv_le_map_uniformOfFintype_getD 0 (by decide)

/-- Repeated entries add up: a uniform index below `2` selects `x` from `[x, x]` with probability
`1`, more than the bound `1 / 2`. -/
example (x : ZMod 7) :
    (PMF.uniformOfFintype (Fin 2)).map (fun i : Fin 2 => [x, x].getD i 0) x = 1 := by
  have h : (fun i : Fin 2 => [x, x].getD i 0) = fun _ => x := by
    funext i
    fin_cases i <;> rfl
  rw [h, show (PMF.uniformOfFintype (Fin 2)).map (fun _ => x) = PMF.pure x from PMF.map_const _ x]
  simp

/-- The bound `uniform Bool true ≤ 1 * pure true true` holds at the outcome `true` only, and it
survives the initial draw `p`. -/
example (p : PMF Bool) :
    p.bind (fun _ => PMF.uniformOfFintype Bool) true ≤ 1 * p.bind (fun _ => PMF.pure true) true :=
  PMF.bind_apply_le_mul_bind_apply p fun _ => by simp [PMF.uniformOfFintype_apply]

/-- At the other outcome the comparison fails. -/
example : ¬ PMF.uniformOfFintype Bool false ≤ 1 * PMF.pure true false := by
  simp [PMF.uniformOfFintype_apply]

/-- The affine form: `uniform Bool true ≤ 0 * pure false true + 1 / 2`, and the constant `1 / 2`
survives the initial draw `p` without being multiplied. -/
example (p : PMF Bool) :
    p.bind (fun _ => PMF.uniformOfFintype Bool) true ≤
      0 * p.bind (fun _ => PMF.pure false) true + 2⁻¹ :=
  PMF.bind_apply_le_mul_bind_apply_add p fun _ => by simp [PMF.uniformOfFintype_apply]

/-! ### The capped residue sampler -/

/-- At bound `0` the cap makes the sampler return `0`. -/
example (width : ℕ) : ProbComp.eval (ProbComp.sampleModIndex width 0) = PMF.pure 0 := by
  rw [ProbComp.sampleModIndex, ProbComp.eval_map,
    show (min 0 : ℕ → ℕ) = fun _ => 0 from funext Nat.zero_min]
  exact PMF.map_const _ 0

/-- At a positive bound, here `3`, the cap changes nothing. -/
example (width : ℕ) : ProbComp.sampleModIndex width 3 = ProbComp.sampleModNat width 3 :=
  ProbComp.sampleModIndex_eq_sampleModNat width (by decide)

/-- The certificate with `width n = n` and the constant bound `3`. -/
example : IsPPTOn encUnary encUnary fun n : ℕ => ProbComp.sampleModIndex n 3 :=
  isPPTOn_sampleModIndex (width := fun n => n) .id' (ComputableInPolyTime.const 3)

/-! ### The fixed-group experiment in `ZMod 7` with `g = 1` -/

/-- At `Q = 0` the list experiment is never won, whatever the adversary returns. -/
example (A : ZMod 7 → ZMod 7 → ProbComp (List (ZMod 7))) :
    listCDHAdvantage 7 (1 : ZMod 7) 0 A = 0 :=
  listCDHAdvantage_zero 7 1 A

/-- In `ZMod 7` with `g = 1` every element is its own exponent, so the Diffie–Hellman value of
`u` and `v` is their product: return the one-entry list `[u * v]`. -/
noncomputable def productList (u v : ZMod 7) : ProbComp (List (ZMod 7)) :=
  pure [u * v]

/-- `productList` wins the list experiment for every `Q ≠ 0`. -/
theorem listCDHAdvantage_productList {Q : ℕ} (hQ : Q ≠ 0) :
    listCDHAdvantage 7 (1 : ZMod 7) Q productList = 1 := by
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hQ
  simp only [listCDHAdvantage, Experiment.succProbability, listCDHExperiment, productList,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one,
    List.take_succ_cons]
  simp [Game.succProbability]

/-- At `Q = 1` the bound reads `listCDHAdvantage ≤ 1 * cdhAdvantage`, so the reduction, which
returns the only entry, always solves CDH. -/
example : 1 ≤ cdhAdvantage 7 (1 : ZMod 7)
    (listCDHToCDH (1 : ZMod 7) (Fin.val <$> ProbComp.unifFin 0) productList) := by
  have h := listCDHAdvantage_le_mul_cdhAdvantage 7 (1 : ZMod 7) 1 productList
  rwa [listCDHAdvantage_productList one_ne_zero, Nat.cast_one, one_mul] at h

/-- At `Q = 3`, larger than the list's length, the list counts in full and the bound gives
`1 ≤ 3 * cdhAdvantage`: the reduction is right with probability at least `1 / 3`. -/
example : 1 ≤ 3 * cdhAdvantage 7 (1 : ZMod 7)
    (listCDHToCDH (1 : ZMod 7) (Fin.val <$> ProbComp.unifFin 2) productList) := by
  have h := listCDHAdvantage_le_mul_cdhAdvantage 7 (1 : ZMod 7) 3 productList
  rwa [listCDHAdvantage_productList three_ne_zero, Nat.cast_ofNat] at h

/-- Past the end of its list the reduction returns `g`: position `2` of a one-entry list. -/
example (u v : ZMod 7) :
    ProbComp.eval (listCDHToCDH (1 : ZMod 7) (pure 2) productList u v) = PMF.pure 1 := by
  simp [listCDHToCDH, productList, ProbComp.eval_pure]

/-- An adversary that returns the Diffie–Hellman value twice, around a wrong entry. -/
noncomputable def repeatedList (u v : ZMod 7) : ProbComp (List (ZMod 7)) :=
  pure [u * v, 0, u * v]

/-- `repeatedList` wins the list experiment at `Q = 3`. -/
theorem listCDHAdvantage_repeatedList : listCDHAdvantage 7 (1 : ZMod 7) 3 repeatedList = 1 := by
  simp only [listCDHAdvantage, Experiment.succProbability, listCDHExperiment, repeatedList,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one,
    List.take_succ_cons, List.take_zero, List.mem_cons, true_or, decide_true, PMF.bind_const]
  simp [Game.succProbability]

/-- The bound applies unchanged to the list with the repeated entry. -/
example : 1 ≤ 3 * cdhAdvantage 7 (1 : ZMod 7)
    (listCDHToCDH (1 : ZMod 7) (Fin.val <$> ProbComp.unifFin 2) repeatedList) := by
  have h := listCDHAdvantage_le_mul_cdhAdvantage 7 (1 : ZMod 7) 3 repeatedList
  rwa [listCDHAdvantage_repeatedList, Nat.cast_ofNat] at h

/-- An entry beyond the first `Q` does not count: with `Q = 1`, the value `3 * 5` in the second
entry of `[0, 3 * 5]` is not among the entries the experiment checks. -/
example : ((3 : ZMod 7) * 5) ∉ [0, (3 : ZMod 7) * 5].take 1 := by
  decide

/-- With the fair-coin index, at `Q = 0` the bound says the list experiment is never won. -/
example (width : ℕ) (A : ZMod 7 → ZMod 7 → ProbComp (List (ZMod 7))) :
    ProbComp.eval (listCDHExperiment 7 (1 : ZMod 7) 0 A) true ≤ 0 := by
  simpa using eval_listCDHExperiment_le_mul_add 7 (1 : ZMod 7) width 0 A

/-- With the fair-coin index at `Q = 3`, which is not a power of two, `productList` gives
`1 ≤ 3 * p + 9 / 2 ^ width` for the reduction's success probability `p`. -/
example (width : ℕ) :
    1 ≤ 3 * ProbComp.eval (cdhExperiment 7 (1 : ZMod 7)
        (listCDHToCDH (1 : ZMod 7) (ProbComp.sampleModIndex width 3) productList)) true +
      9 / 2 ^ width := by
  have h := eval_listCDHExperiment_le_mul_add 7 (1 : ZMod 7) width 3 productList
  have h1 : ProbComp.eval (listCDHExperiment 7 (1 : ZMod 7) 3 productList) true = 1 := by
    have h' := listCDHAdvantage_productList three_ne_zero
    rw [listCDHAdvantage, Experiment.succProbability, Game.succProbability,
      ENNReal.toNNReal_eq_one_iff] at h'
    exact h'
  rw [h1, Nat.cast_ofNat] at h
  exact h.trans_eq (by norm_num)

/-- The general bound with the deterministic index `0` at `Q = 1`: reading the first entry loses
nothing, so the factor is `1`. -/
example (A : ZMod 7 → ZMod 7 → ProbComp (List (ZMod 7))) :
    ProbComp.eval (listCDHExperiment 7 (1 : ZMod 7) 1 A) true ≤
      1 * ProbComp.eval (cdhExperiment 7 (1 : ZMod 7) (listCDHToCDH 1 (pure 0) A)) true :=
  eval_listCDHExperiment_le_mul 7 1 1 (pure 0) (fun l x hx => by
    cases l with
    | nil => simp at hx
    | cons y l =>
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hx
      subst hx
      simp [ProbComp.eval_pure]) A

/-! ### The family layer -/

section Family

variable (F : PrimeOrderGroupFamily)

/-- The list game is the fixed-group experiment after the setup draw. -/
example (setup : ℕ → PMF F.Desc) (Q : ℕ → ℕ) (adversary : F.ListCDHAdversary) (n : ℕ) :
    F.listCDHGame setup Q adversary n = Game.withSetup (setup n) fun d =>
      listCDHExperiment (F.order d) (F.generator d) (Q n) (adversary n d) :=
  rfl

/-- The list adversary that returns its two inputs. -/
noncomputable def inputsListAdversary : F.ListCDHAdversary :=
  fun _ _ u v => pure [u, v]

/-- `inputsListAdversary` is uniform strict PPT, so `ListCDHAdversary.IsPPT` is satisfiable in
every family. -/
theorem inputsListAdversary_isPPT : (inputsListAdversary F).IsPPT := by
  have hu := F.encCDHInput_leftPublic_polyTime .id'
  have hv := F.encCDHInput_rightPublic_polyTime .id'
  refine (ComputableInPolyTime.cons' hu (ComputableInPolyTime.cons' hv
    (ComputableInPolyTime.const []))).isPPTOn.congr fun x => ?_
  simp [inputsListAdversary]

/-- `Q n = n` is computable in polynomial time in unary. -/
theorem computableInPolyTime_id_unary :
    ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary :=
  .id'

/-- The certified reduction at this adversary, with `width n = n` and `Q n = n`. -/
example : (F.listCDHToCDHAdversary (fun n => n) (fun n => n) (inputsListAdversary F)).IsPPT :=
  isPPT_listCDHToCDHAdversary computableInPolyTime_id_unary computableInPolyTime_id_unary
    (inputsListAdversary_isPPT F)

/-- The loss bound at this adversary, with `width n = n` and `Q n = n`. -/
example (setup : ℕ → PMF F.Desc) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup (fun n => n) (inputsListAdversary F) n) ≤
      n * Game.succProbability (F.cdhGame setup
          (F.listCDHToCDHAdversary (fun n => n) (fun n => n) (inputsListAdversary F)) n) +
        n ^ 2 / 2 ^ n :=
  F.succProbability_listCDHGame_le setup (fun n => n) (fun n => n) _ n

/-- The loss bound with `Q n = 0`: the list game is never won. -/
example (setup : ℕ → PMF F.Desc) (width : ℕ → ℕ) (adversary : F.ListCDHAdversary) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup (fun _ => 0) adversary n) = 0 :=
  le_antisymm (by simpa using F.succProbability_listCDHGame_le setup width (fun _ => 0) adversary n)
    (by positivity)

/-- The loss bound with `Q n = 3`, not a power of two, and `width n = n`. -/
example (setup : ℕ → PMF F.Desc) (adversary : F.ListCDHAdversary) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup (fun _ => 3) adversary n) ≤
      3 * Game.succProbability
          (F.cdhGame setup (F.listCDHToCDHAdversary (fun n => n) (fun _ => 3) adversary) n) +
        9 / 2 ^ n := by
  have h := F.succProbability_listCDHGame_le setup (fun n => n) (fun _ => 3) adversary n
  norm_num at h
  exact h

/-- Raising the bound from `Q n = 1` to `Q n = n + 1` does not lower the success probability. -/
example (setup : ℕ → PMF F.Desc) (adversary : F.ListCDHAdversary) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup (fun _ => 1) adversary n) ≤
      Game.succProbability (F.listCDHGame setup (fun n => n + 1) adversary n) :=
  F.succProbability_listCDHGame_mono setup (Nat.le_add_left 1 n) adversary

/-- The list form of CDH is hard under CDH, applied as a client would, with `Q n = n`. -/
example (setup : ℕ → PMF F.Desc) (h : F.CDH setup) :
    Negligible fun n =>
      Game.succProbability (F.listCDHGame setup (fun n => n) (inputsListAdversary F) n) :=
  h.negligible_listCDHGame computableInPolyTime_id_unary _ (inputsListAdversary_isPPT F)

end Family

/-- The theorem on Schnorr groups. -/
example (setup : ℕ → PMF schnorrGroups.Desc) (h : schnorrGroups.CDH setup) :
    Negligible fun n => Game.succProbability
      (schnorrGroups.listCDHGame setup (fun n => n) (inputsListAdversary schnorrGroups) n) :=
  h.negligible_listCDHGame computableInPolyTime_id_unary _ (inputsListAdversary_isPPT _)

end CslibFrontierTests.Crypto.ListCDH
