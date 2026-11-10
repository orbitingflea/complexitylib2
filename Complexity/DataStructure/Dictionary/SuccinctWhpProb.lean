/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.Dynamic.Spec
public import Complexity.DataStructure.Dictionary.FeistelQuotient
public import Complexity.DataStructure.Dictionary.SuccinctWhpParams
public import Complexity.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import Complexity.Probability.KWiseIndependent.VarianceTail
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Probability.PMF.Uniform
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# High-Probability Seed Events and Tail Bounds for the WHP Succinct Dictionary

This module defines the static hash-seed pair `SeedWhp c U n_max = BktSeed × FpSeed` (combining two
independent universe-reduced salted general-`q` double-tabulation seeds from
`BitPackedDoubleTabulation`), the concrete per-state and trailing-window deterministic seed
conditions (`GoodSeedOnState` and `GoodSeedOnWindow`), and proves the per-operation failure
probability bound:

For every exponent `c ≥ 1`, every capacity `whpThreshold c ≤ n_max`, every key universe `n_max ≤ U`,
and every admissible oblivious operation prefix `ops : List (Dynamic.Op U)`,
`(seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
  (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.w0Whp`, `BktSeed`, `FpSeed`, `SeedWhp`, `seedLawWhp`:
  combined static seed type and uniform distribution.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.bktHash`, `fpReducedKey`, `fpHash`,
  `fpHashFromReduced`: pure Feistel-bucket hash, Stage-1 reduced key, and Stage-2 salted
  fingerprint hash.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.BalancedBuckets`, `GoodSeedOnState`,
  `GoodSeedOnWindow`: deterministic load-balance, Stage-1 injectivity, collision-free salt
  existence, and epoch salt-collision count conditions.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.GoodSeedOnWindow.goodSeedOnState_of_mem`:
  `GoodSeedOnWindow` implies `GoodSeedOnState` on every state along the trailing `2 * Q + 2`
  operations (including the target post-state for deterministic self-healing).
* `Cslib.DataStructure.Dictionary.SuccinctWhp.toOuterMeasure_not_goodSeedOnWindow_le`:
  total failure probability across Stage-1 universe reduction, Stage-2 `k`-uniqueness, Feistel
  bucket load balance, multi-salt collision-freedom, and window salt-collision count is at most
  `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
open Cslib.Probability Cslib.Probability.PMF
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Static seed pair and pure hash evaluation wrappers -/

/-- Stage-1 bit-width `max 1 (keyBits U) ≥ 1`, satisfying `U ≤ 2 ^ w0Whp U` for every `U`. -/
@[expose] def w0Whp (U : ℕ) : ℕ :=
  max 1 (keyBits U)

theorem w0Whp_pos (U : ℕ) : 0 < w0Whp U := by
  unfold w0Whp
  positivity

theorem le_two_pow_w0Whp (U : ℕ) : U ≤ 2 ^ w0Whp U := by
  rcases le_or_gt U 1 with hU1 | hU1
  · exact (hU1.trans_lt (Nat.one_lt_two_pow (w0Whp_pos U).ne')).le
  · calc U ≤ 2 ^ Nat.clog 2 U := Nat.le_pow_clog Nat.one_lt_two U
      _ ≤ 2 ^ w0Whp U := Nat.pow_le_pow_right (by decide) (le_max_right 1 (keyBits U))

/-- Static seed type for the Feistel quotient bucket hash (`M_out = bWhp n_max`). -/
abbrev BktSeed (c U n_max : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max)

/-- Static seed type for the salted fingerprint hash (`M_out = fpBitsWhp n_max`). -/
abbrev FpSeed (c U n_max : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (w0Whp U) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max)

/-- Combined static seed pair `(θ_bkt, θ_fp)` sampled once during `initSetup`. -/
abbrev SeedWhp (c U n_max : ℕ) : Type :=
  BktSeed c U n_max × FpSeed c U n_max

/-- Uniform probability distribution over `SeedWhp c U n_max`. -/
noncomputable abbrev seedLawWhp (c U n_max : ℕ) : PMF (SeedWhp c U n_max) :=
  PMF.uniformOfFintype (SeedWhp c U n_max)

/-- Pure Feistel bucket hash `ℕ → ℕ` induced by `θ_bkt`, mapping quotients `q < U` into
`< 2 ^ bWhp n_max = numBucketsWhp n_max` via salt `0`. -/
@[expose] def bktHash (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (q : ℕ) : ℕ :=
  if hq : q < U then
    (evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max) 1 θ₁ (⟨0, Nat.zero_lt_one⟩, ⟨q, hq⟩)).val
  else 0

theorem bktHash_lt (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (q : ℕ) :
    bktHash c U n_max θ₁ q < numBucketsWhp n_max := by
  unfold bktHash numBucketsWhp
  split_ifs with hq
  · exact (evalSalted _ _ _ _ _ _ _ _ θ₁ _).isLt
  · exact Nat.two_pow_pos _

/-- Stage-1 reduced key `fpReducedKey c U n_max θ₂ u < 2 ^ rRedWhp c n_max` used for both Stage-2
salted fingerprint hashing and constant-depth `BufTrie` indexing. -/
@[expose] def fpReducedKey (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (u : Fin U) : ℕ :=
  (multiplyShiftReduced U (w0Whp U) (rRedWhp c n_max) θ₂.1 u).val

theorem fpReducedKey_lt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (u : Fin U) :
    fpReducedKey c U n_max θ₂ u < 2 ^ (cTabWhp c * bCharWhp n_max) := by
  unfold fpReducedKey
  exact (multiplyShiftReduced _ _ _ θ₂.1 u).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))

theorem sMaxWhp_pos (c n_max : ℕ) : 0 < sMaxWhp c n_max := by
  unfold sMaxWhp
  have := scaleWhp_pos n_max
  positivity

/-- Salted fingerprint hash `(s, u) ↦ fp < 2 ^ fpBitsWhp n_max` induced by `θ₂`. -/
@[expose] def fpHash (c U n_max : ℕ) (θ₂ : FpSeed c U n_max)
    (s : Fin (sMaxWhp c n_max)) (u : Fin U) : ℕ :=
  (evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) θ₂ (s, u)).val

theorem fpHash_lt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max)
    (s : Fin (sMaxWhp c n_max)) (u : Fin U) :
    fpHash c U n_max θ₂ s u < 2 ^ fpBitsWhp n_max :=
  (evalSalted _ _ _ _ _ _ _ _ θ₂ (s, u)).isLt

/-- Stage-2 salted fingerprint evaluation directly from `(salt, rKey)`
(`rKey = fpReducedKey θ₂ u`). -/
@[expose] def fpHashFromReduced (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (salt rKey : ℕ) : ℕ :=
  let sFin : Fin (sMaxWhp c n_max) := ⟨salt % sMaxWhp c n_max, Nat.mod_lt _ (sMaxWhp_pos c n_max)⟩
  let rFin : Fin (2 ^ min (w0Whp U) (rRedWhp c n_max)) :=
    ⟨rKey % 2 ^ min (w0Whp U) (rRedWhp c n_max), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  (simpleTabEval θ₂.2.2
    (simpleTabTuple θ₂.2.1 (saltedChars (cTabWhp c) (bCharWhp n_max) sFin rFin))).val

theorem fpHashFromReduced_lt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (salt rKey : ℕ) :
    fpHashFromReduced c U n_max θ₂ salt rKey < 2 ^ fpBitsWhp n_max :=
  (simpleTabEval θ₂.2.2 _).isLt

theorem fpHashFromReduced_fpReducedKey_eq (c U n_max : ℕ) (θ₂ : FpSeed c U n_max)
    (s : Fin (sMaxWhp c n_max)) (u : Fin U) :
    fpHashFromReduced c U n_max θ₂ s.val (fpReducedKey c U n_max θ₂ u) =
      fpHash c U n_max θ₂ s u := by
  unfold fpHashFromReduced fpReducedKey fpHash evalSalted
  dsimp only
  have hs_fin :
      (⟨s.val % sMaxWhp c n_max, Nat.mod_lt _ (sMaxWhp_pos c n_max)⟩ : Fin (sMaxWhp c n_max)) =
        s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have hr_fin :
      (⟨(multiplyShiftReduced U (w0Whp U) (rRedWhp c n_max) θ₂.1 u).val %
          2 ^ min (w0Whp U) (rRedWhp c n_max), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
        Fin (2 ^ min (w0Whp U) (rRedWhp c n_max))) =
        multiplyShiftReduced U (w0Whp U) (rRedWhp c n_max) θ₂.1 u :=
    Fin.ext (Nat.mod_eq_of_lt (multiplyShiftReduced _ _ _ θ₂.1 u).isLt)
  rw [hs_fin, hr_fin]

/-! ## Section 2: Trailing window, `BalancedBuckets`, `GoodSeedOnState`, and `GoodSeedOnWindow` -/

/-- Execute a list of dynamic dictionary operations sequentially from state `s`. -/
@[expose] def runOps {U : ℕ} : State U → List (Dynamic.Op U) → State U
  | s, [] => s
  | s, o :: rest => runOps (Dynamic.step s o).1 rest

theorem runOps_append {U : ℕ} (s : State U) (l₁ l₂ : List (Dynamic.Op U)) :
    runOps s (l₁ ++ l₂) = runOps (runOps s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons o rest ih => exact ih (Dynamic.step s o).1

/-- List of all intermediate states `[s₀, s₁, ..., s_k]` visited along `ops` from `s₀`. -/
@[expose] def stateSeq {U : ℕ} : State U → List (Dynamic.Op U) → List (State U)
  | s, [] => [s]
  | s, o :: rest => s :: stateSeq (Dynamic.step s o).1 rest

theorem length_stateSeq {U : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    (stateSeq s ops).length = ops.length + 1 := by
  induction ops generalizing s with
  | nil => rfl
  | cons o rest ih => simp [stateSeq, ih]

theorem runOps_mem_stateSeq {U : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    runOps s ops ∈ stateSeq s ops := by
  induction ops generalizing s with
  | nil => simp [runOps, stateSeq]
  | cons o rest ih => exact List.mem_cons_of_mem s (ih (Dynamic.step s o).1)

theorem self_mem_stateSeq {U : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    s ∈ stateSeq s ops := by
  cases ops <;> simp [stateSeq]

/-- Finset of all keys occurring in `.insert u v` operations in `ops`. -/
@[expose] def opInsKeys {U : ℕ} : List (Dynamic.Op U) → Finset (Fin U)
  | [] => ∅
  | .insert u _ :: rest => insert u (opInsKeys rest)
  | _ :: rest => opInsKeys rest

theorem card_opInsKeys_le {U : ℕ} (ops : List (Dynamic.Op U)) :
    #(opInsKeys ops) ≤ ops.length := by
  induction ops with
  | nil => simp [opInsKeys]
  | cons o rest ih =>
    cases o with
    | insert u _ =>
      dsimp only [opInsKeys, List.length_cons]
      exact (card_insert_le u (opInsKeys rest)).trans (Nat.add_le_add_right ih 1)
    | query _ =>
      dsimp only [opInsKeys, List.length_cons]
      omega
    | delete _ =>
      dsimp only [opInsKeys, List.length_cons]
      omega

/-- Every state visited along `ops` from `s₀` has domain contained in `dom s₀ ∪ opInsKeys ops`. -/
theorem dom_subset_union_opInsKeys {U : ℕ} (s₀ : State U) (ops : List (Dynamic.Op U)) :
    ∀ s ∈ stateSeq s₀ ops, Dictionary.dom s ⊆ Dictionary.dom s₀ ∪ opInsKeys ops := by
  induction ops generalizing s₀ with
  | nil =>
    intro s hs
    simp only [stateSeq, List.mem_singleton] at hs
    subst hs
    exact subset_union_left
  | cons o rest ih =>
    intro s hs
    simp only [stateSeq, List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · exact subset_union_left
    · have hsub := ih (Dynamic.step s₀ o).1 s hs_rest
      refine hsub.trans fun x hx => ?_
      rcases mem_union.mp hx with hx_step | hx_ins
      · cases o with
        | query _ =>
          exact mem_union_left _ hx_step
        | delete u =>
          dsimp only [Dynamic.step] at hx_step
          rw [Dynamic.dom_delete] at hx_step
          exact mem_union_left _ (mem_of_mem_erase hx_step)
        | insert u v =>
          dsimp only [Dynamic.step, opInsKeys] at hx_step ⊢
          by_cases hxu : x = u
          · subst hxu
            exact mem_union_right _ (mem_insert_self x _)
          · rw [Dictionary.mem_dom_iff, Function.update_of_ne hxu, ← Dictionary.mem_dom_iff]
              at hx_step
            exact mem_union_left _ hx_step
      · cases o <;> simp only [opInsKeys]
        · exact mem_union_right _ hx_ins
        · exact mem_union_right _ (mem_insert_of_mem hx_ins)
        · exact mem_union_right _ hx_ins

/-- Admissible operation sequence predicate from state `s`: every step satisfies
`Dynamic.valid V n_max`. -/
@[expose] def ValidOpSeq {U : ℕ} (V n_max : ℕ) : State U → List (Dynamic.Op U) → Prop
  | _, [] => True
  | s, o :: rest => Dynamic.valid V n_max s o ∧ ValidOpSeq V n_max (Dynamic.step s o).1 rest

theorem ValidOpSeq.append_iff {U V n_max : ℕ} (s : State U) (l₁ l₂ : List (Dynamic.Op U)) :
    ValidOpSeq V n_max s (l₁ ++ l₂) ↔
      ValidOpSeq V n_max s l₁ ∧ ValidOpSeq V n_max (runOps s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [ValidOpSeq, runOps]
  | cons o rest ih =>
    simp only [List.cons_append, ValidOpSeq, runOps, ih, and_assoc]

theorem card_dom_le_of_validOpSeq {U V n_max : ℕ} {s₀ : State U}
    (hc₀ : #(Dictionary.dom s₀) ≤ n_max) {ops : List (Dynamic.Op U)}
    (hv : ValidOpSeq V n_max s₀ ops) :
    ∀ s ∈ stateSeq s₀ ops, #(Dictionary.dom s) ≤ n_max := by
  induction ops generalizing s₀ with
  | nil =>
    intro s hs
    simp only [stateSeq, List.mem_singleton] at hs
    rwa [hs]
  | cons o rest ih =>
    obtain ⟨hvo, hv_rest⟩ := hv
    intro s hs
    simp only [stateSeq, List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · exact hc₀
    · exact ih (Dynamic.card_dom_step_le_of_valid hc₀ hvo) hv_rest s hs_rest

/-- Trailing window length `2 * qEpochWhp n_max + 2` covering two full epochs plus transitions. -/
@[expose] def windowLenWhp (n_max : ℕ) : ℕ :=
  2 * qEpochWhp n_max + 2

/-- State at the start of the trailing `windowLenWhp n_max` operations of `ops`. -/
@[expose] def windowStartState (U n_max : ℕ) (ops : List (Dynamic.Op U)) : State U :=
  runOps (Dictionary.empty U) (ops.take (ops.length - windowLenWhp n_max))

/-- Trailing `≤ windowLenWhp n_max` operations of `ops`. -/
@[expose] def windowSuffix (U n_max : ℕ) (ops : List (Dynamic.Op U)) : List (Dynamic.Op U) :=
  ops.drop (ops.length - windowLenWhp n_max)

theorem runOps_window_eq (U n_max : ℕ) (ops : List (Dynamic.Op U)) :
    runOps (windowStartState U n_max ops) (windowSuffix U n_max ops) =
      runOps (Dictionary.empty U) ops := by
  unfold windowStartState windowSuffix
  rw [← runOps_append, List.take_append_drop]

theorem length_windowSuffix_le (U n_max : ℕ) (ops : List (Dynamic.Op U)) :
    (windowSuffix U n_max ops).length ≤ windowLenWhp n_max := by
  unfold windowSuffix
  simp only [List.length_drop]
  omega

/-- Single-bucket load-balance condition `|X_b - #S / M| ≤ deltaWhp n_max` at bucket `b`. -/
@[expose] def BalancedBucketAt (U n_max : ℕ) (h1 : ℕ → ℕ) (S : Finset (Fin U))
    (b : Fin (numBucketsWhp n_max)) : Prop :=
  let X_b := #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val)
  numBucketsWhp n_max * X_b ≤ #S + numBucketsWhp n_max * deltaWhp n_max ∧
  #S ≤ numBucketsWhp n_max * X_b + numBucketsWhp n_max * deltaWhp n_max

/-- Multiplicative bucket-balance condition `|X_b - #S / M| ≤ deltaWhp n_max` matching
`sum_sub_capFront_le_poolSize`. -/
@[expose] def BalancedBuckets (U n_max : ℕ) (h1 : ℕ → ℕ) (S : Finset (Fin U)) : Prop :=
  ∀ b : Fin (numBucketsWhp n_max), BalancedBucketAt U n_max h1 S b

/-- Concrete single-state fast-mode eligibility condition on `(θ, s)` checked during
self-healing from `fallbackMode` to `fastMode`:
1. `fpReducedKey` is injective on `dom s`;
2. `feistelBucket` satisfies `BalancedBuckets` on `dom s`;
3. Every bucket `b` of `dom s` admits at least one collision-free salt `< sMaxWhp c n_max`. -/
@[expose] def GoodSeedOnState (c U n_max : ℕ) (θ : SeedWhp c U n_max) (s : State U) : Prop :=
  Set.InjOn (fpReducedKey c U n_max θ.2) (Dictionary.dom s : Set (Fin U)) ∧
  BalancedBuckets U n_max (bktHash c U n_max θ.1) (Dictionary.dom s) ∧
  ∀ b : Fin (numBucketsWhp n_max),
    ∃ salt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 salt)
        ((Dictionary.dom s).filter (fun u =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))

/-- Trailing-window good-seed event for operation history `ops`:
1. Stage-1 `fpReducedKey` is injective on `W_keys = dom s_start ∪ opInsKeys suf`;
2. `BalancedBuckets` holds on `dom s` for every state `s ∈ stateSeq s_start suf`;
3. `BalancedBuckets` holds on `W_ins = opInsKeys suf`;
4. Every window bucket `W_bkt(b)` admits a collision-free salt `< sMaxWhp c n_max`;
5. Fewer than `2 * rIndepWhp c n_max` inserted keys in `W_ins` ever collide with another key in
   their window bucket under any salt `< sMaxWhp c n_max`. -/
@[expose] def GoodSeedOnWindow (c U n_max : ℕ) (ops : List (Dynamic.Op U))
    (θ : SeedWhp c U n_max) : Prop :=
  let s_start := windowStartState U n_max ops
  let suf := windowSuffix U n_max ops
  let W_ins := opInsKeys suf
  let W_keys := Dictionary.dom s_start ∪ W_ins
  let h1 := bktHash c U n_max θ.1
  Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)) ∧
  (∀ s ∈ stateSeq s_start suf, BalancedBuckets U n_max h1 (Dictionary.dom s)) ∧
  BalancedBuckets U n_max h1 W_ins ∧
  (∀ b : Fin (numBucketsWhp n_max),
    ∃ salt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 salt)
        (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) : Set (Fin U))) ∧
  #(W_ins.filter fun u =>
      ∃ v ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) h1 w.val = feistelBucket (bWhp n_max) h1 u.val),
        u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt u = fpHash c U n_max θ.2 salt v) <
    2 * rIndepWhp c n_max

/-- `GoodSeedOnWindow` implies `GoodSeedOnState` on every state along the trailing window (including
the final state `runOps (empty U) ops`). -/
theorem GoodSeedOnWindow.goodSeedOnState_of_mem {c U n_max : ℕ} {ops : List (Dynamic.Op U)}
    {θ : SeedWhp c U n_max} (hg : GoodSeedOnWindow c U n_max ops θ)
    {s : State U} (hs : s ∈ stateSeq (windowStartState U n_max ops) (windowSuffix U n_max ops)) :
    GoodSeedOnState c U n_max θ s := by
  obtain ⟨hinj, hbal, _, hsalt, _⟩ := hg
  have hdom_sub : (Dictionary.dom s : Set (Fin U)) ⊆
      ((Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops) :
        Finset (Fin U)) : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys _ _ s hs
  refine ⟨hinj.mono hdom_sub, hbal s hs, fun b => ?_⟩
  obtain ⟨salt, hsalt_b⟩ := hsalt b
  refine ⟨salt, hsalt_b.mono fun u hu => ?_⟩
  rw [mem_coe, mem_filter] at hu ⊢
  exact ⟨hdom_sub hu.1, hu.2⟩

/-! ## Section 3: Density-to-`PMF` bridges and numerical `n_max ^ (-c)` tail lemmas -/

/-- Fundamental logarithmic scale inequality: `Nat.log 2 n_max ≤ scaleWhp n_max`. -/
theorem log_le_scaleWhp (n_max : ℕ) :
    Nat.log 2 n_max ≤ scaleWhp n_max := by
  unfold scaleWhp slabScale Dynamic.logLogFactor
  calc Nat.log 2 n_max
      ≤ Nat.log 2 (max n_max 4) := Nat.log_mono_right (le_max_left n_max 4)
    _ ≤ Nat.clog 2 (max n_max 4) := Nat.log_le_clog 2 _
    _ ≤ 2 ^ Nat.clog 2 (Nat.clog 2 (max n_max 4)) :=
        Nat.le_pow_clog Nat.one_lt_two _

/-- When `whpThreshold c ≤ n_max`, `6553600 ≤ scaleWhp n_max` and `cEff c + 4 ≤ scaleWhp n_max`. -/
theorem cEff_add_four_le_scaleWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    6553600 ≤ scaleWhp n_max ∧ cEff c + 4 ≤ scaleWhp n_max := by
  have hm := bMinWhp_le_log hth
  have hlogL := log_le_scaleWhp n_max
  exact ⟨(le_bMinWhp c).trans (hm.trans hlogL),
    (cEff_add_four_le_bMinWhp c).trans (hm.trans hlogL)⟩

/-- When `whpThreshold c ≤ n_max`, `(scaleWhp n_max) ^ 10 ≤ deltaWhp n_max`. -/
theorem scaleWhp_pow10_le_deltaWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (scaleWhp n_max) ^ 10 ≤ deltaWhp n_max := by
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have hL6 : 6553600 ≤ scaleWhp n_max := (cEff_add_four_le_scaleWhp hth).1
  unfold deltaWhp
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc (scaleWhp n_max) ^ 10 * (numBucketsWhp n_max * (8 * scaleWhp n_max))
      = numBucketsWhp n_max * (8 * (scaleWhp n_max) ^ 11) := by ring
    _ ≤ numBucketsWhp n_max * ((scaleWhp n_max) * (scaleWhp n_max) ^ 11) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = numBucketsWhp n_max * (scaleWhp n_max) ^ 12 := by ring
    _ ≤ n_max := hM_L12

/-- Convert a `Finset.dens` real upper bound on `F` covering `E ⊆ ↑F` into an `ENNReal`
`toOuterMeasure` bound under `PMF.uniformOfFintype`, without comparing `DecidablePred` instances. -/
theorem toOuterMeasure_uniformOfFintype_le_of_dens_le {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) (F : Finset α) {B : ℝ}
    (hsub : E ⊆ (F : Set α)) (hdens : (F.dens : ℝ) ≤ B) :
    (PMF.uniformOfFintype α).toOuterMeasure E ≤ ENNReal.ofReal B := by
  have hB0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (F.dens : ℝ)).trans hdens
  have hc_pos : 0 < Fintype.card α := Fintype.card_pos
  have hc_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hc_pos.ne'
  have hc_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcard_real : (#F : ℝ) ≤ B * (Fintype.card α : ℝ) := by
    have hd : (#F : ℝ) / (Fintype.card α : ℝ) ≤ B := by
      simpa only [Finset.nnratCast_dens, Finset.dens_eq_card_div_card, NNRat.cast_div,
        NNRat.cast_natCast] using hdens
    exact (div_le_iff₀ (Nat.cast_pos.mpr hc_pos)).mp hd
  have hcard_enn : (#F : ℝ≥0∞) ≤ ENNReal.ofReal B * (Fintype.card α : ℝ≥0∞) := by
    have h1 := ENNReal.ofReal_le_ofReal hcard_real
    rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hB0, ENNReal.ofReal_natCast] at h1
  calc (PMF.uniformOfFintype α).toOuterMeasure E
      ≤ (PMF.uniformOfFintype α).toOuterMeasure (F : Set α) :=
        MeasureTheory.measure_mono hsub
    _ = (#F : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
        rw [PMF.toOuterMeasure_apply_finset]
        simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul]
    _ ≤ (ENNReal.ofReal B * (Fintype.card α : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
        gcongr
    _ = ENNReal.ofReal B := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hc_ne hc_top, mul_one]

private theorem outerMeasure_biUnion_finset_le {α β : Type*}
    (μ : MeasureTheory.OuterMeasure α) (s : Finset β) (f : β → Set α) :
    μ (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (MeasureTheory.measure_union_le _ _).trans (add_le_add_right ih _)

private theorem outerMeasure_iUnion_fintype_le {α β : Type*} [Fintype β]
    (μ : MeasureTheory.OuterMeasure α) (f : β → Set α) :
    μ (⋃ i : β, f i) ≤ ∑ i : β, μ (f i) := by
  have heq : (⋃ i : β, f i) = ⋃ i ∈ (univ : Finset β), f i := by ext x; simp
  rw [heq]
  exact outerMeasure_biUnion_finset_le μ univ f

/-- Convert `((A : ℝ) / (B : ℝ)) ^ r` with `2 ^ E * A ≤ B` into `((2 : ℝ≥0∞) ^ (E * r))⁻¹`. -/
theorem ofReal_div_pow_le_inv_two_pow {A B E r : ℕ} (hB : 0 < B) (hAB : 2 ^ E * A ≤ B) :
    ENNReal.ofReal (((A : ℝ) / (B : ℝ)) ^ r) ≤ ((2 : ℝ≥0∞) ^ (E * r))⁻¹ := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hdiv : (A : ℝ) / (B : ℝ) ≤ ((2 : ℝ) ^ E)⁻¹ := by
    rw [ inv_eq_one_div, div_le_div_iff₀ hB_pos hpow_pos, one_mul, mul_comm]
    exact_mod_cast hAB
  have hr : ((A : ℝ) / (B : ℝ)) ^ r ≤ (((2 : ℝ) ^ E)⁻¹) ^ r :=
    pow_le_pow_left₀ (by positivity) hdiv r
  have heq : (((2 : ℝ) ^ E)⁻¹) ^ r = ((2 : ℝ) ^ (E * r))⁻¹ := by
    rw [inv_pow, ← pow_mul]
  calc ENNReal.ofReal (((A : ℝ) / (B : ℝ)) ^ r)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ (E * r))⁻¹) := ENNReal.ofReal_le_ofReal (hr.trans_eq heq)
    _ = (ENNReal.ofReal ((2 : ℝ) ^ (E * r)))⁻¹ := ENNReal.ofReal_inv_of_pos (by positivity)
    _ = ((2 : ℝ≥0∞) ^ (E * r))⁻¹ := by
        rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- Pure `ℕ`-exponent criterion showing
`(K : ℝ≥0∞) * (2 ^ D)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ * (n_max : ℝ≥0∞)⁻¹ ^ c`. -/
theorem mul_inv_two_pow_le_eighth_inv_pow {K D a b n_max c : ℕ}
    (hn_pos : 0 < n_max) (hK : K ≤ 2 ^ a) (hn : n_max ≤ 2 ^ b) (hexp : 3 + a + b * c ≤ D) :
    (K : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ D)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  have h2D_ne : ((2 : ℝ≥0∞) ^ D) ≠ 0 := by positivity
  have h2D_top : ((2 : ℝ≥0∞) ^ D) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2)
  have h8n_ne : (8 : ℝ≥0∞) * (n_max : ℝ≥0∞) ^ c ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero c (Nat.cast_ne_zero.mpr hn_pos.ne'))
  have h8n_top : (8 : ℝ≥0∞) * (n_max : ℝ≥0∞) ^ c ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  rw [← ENNReal.inv_pow,
    ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [← div_eq_mul_inv, ENNReal.div_le_iff_le_mul (Or.inl h2D_ne) (Or.inl h2D_top),
    mul_comm _ ((2 : ℝ≥0∞) ^ D), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl h8n_ne) (Or.inl h8n_top)]
  have hnat : K * (8 * n_max ^ c) ≤ 2 ^ D := by
    calc K * (8 * n_max ^ c)
        ≤ 2 ^ a * (2 ^ 3 * (2 ^ b) ^ c) :=
          Nat.mul_le_mul hK (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hn c))
      _ = 2 ^ (a + (3 + b * c)) := by
          rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hcast : ((K * (8 * n_max ^ c) : ℕ) : ℝ≥0∞) ≤ (((2 ^ D : ℕ) : ℝ≥0∞)) :=
    Nat.cast_le.mpr hnat
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcast

/-- Marginal identity for `PMF.uniformOfFintype` along the first projection of `e : γ ≃ α × β`. -/
theorem toOuterMeasure_uniformOfFintype_fst {α β γ : Type*}
    [Fintype α] [Nonempty α] [Finite β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : γ ≃ α × β) (P : α → Prop) :
    (PMF.uniformOfFintype γ).toOuterMeasure {z | P (e z).1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | P a} := by
  let _ : Fintype β := Fintype.ofFinite β
  have hfn : (fun z : γ => (e z).1) = Prod.fst ∘ e := rfl
  have hmap : (PMF.uniformOfFintype γ).map (fun z => (e z).1) = PMF.uniformOfFintype α := by
    rw [hfn, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e, uniformOfFintype_prod_map_fst]
  rw [← hmap, PMF.toOuterMeasure_map_apply]
  rfl

/-- Conditional union bound for `PMF.uniformOfFintype` along `e : γ ≃ α × β`: if `¬ G` has
probability at most `p_top` on `α`, and for every `a` with `G a` the fiber bad event has
probability at most `p_bot` on `β`, then `Bad` has probability at most `p_top + p_bot` on `γ`. -/
theorem toOuterMeasure_uniformOfFintype_cond_le {α β γ : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : γ ≃ α × β) (G : α → Prop) (Bad : γ → Prop) {p_top p_bot : ℝ≥0∞}
    (htop : (PMF.uniformOfFintype α).toOuterMeasure {a | ¬ G a} ≤ p_top)
    (hbot : ∀ a : α, G a →
      (PMF.uniformOfFintype β).toOuterMeasure {b | Bad (e.symm (a, b))} ≤ p_bot) :
    (PMF.uniformOfFintype γ).toOuterMeasure {z | Bad z} ≤ p_top + p_bot := by
  classical
  have hsub : {z : γ | Bad z} ⊆ {z : γ | ¬ G (e z).1} ∪ {z : γ | G (e z).1 ∧ Bad z} := by
    intro z hz
    by_cases hGz : G (e z).1
    · exact Or.inr ⟨hGz, hz⟩
    · exact Or.inl hGz
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  rw [toOuterMeasure_uniformOfFintype_fst e (fun a => ¬ G a)]
  refine add_le_add htop ?_
  let F : Finset γ := univ.filter fun z => G (e z).1 ∧ Bad z
  have hsF : {z : γ | G (e z).1 ∧ Bad z} = (F : Set γ) := by
    ext z; simp [F]
  rw [hsF, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  have hcγ_ne : (Fintype.card γ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hcγ_top : (Fintype.card γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff_le_mul (Or.inl hcγ_ne) (Or.inl hcγ_top)]
  have hcardF : #F = ∑ a ∈ univ.filter G, #(univ.filter fun b => Bad (e.symm (a, b))) := by
    have heq : #F = #(univ.filter fun p : α × β => G p.1 ∧ Bad (e.symm p)) :=
      Finset.card_equiv e fun z => by simp [F]
    rw [heq, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_filter]
    refine Fintype.sum_congr _ _ fun a => ?_
    by_cases hGa : G a
    · simp only [hGa, true_and, ↓reduceIte, Finset.card_filter]
    · simp only [hGa, false_and, ↓reduceIte, sum_const_zero]
  have hcardγ : (Fintype.card γ : ℝ≥0∞) =
      (Fintype.card α : ℝ≥0∞) * (Fintype.card β : ℝ≥0∞) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hcβ_ne : (Fintype.card β : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hcβ_top : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfiber : ∀ a ∈ univ.filter G,
      (#(univ.filter fun b => Bad (e.symm (a, b))) : ℝ≥0∞) ≤
        p_bot * (Fintype.card β : ℝ≥0∞) := by
    intro a ha
    have hba := hbot a (mem_filter.mp ha).2
    let Fb : Finset β := univ.filter fun b => Bad (e.symm (a, b))
    have hsFb : {b : β | Bad (e.symm (a, b))} = (Fb : Set β) := by
      ext b; simp [Fb]
    rw [hsFb, PMF.toOuterMeasure_apply_finset] at hba
    simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul, ← div_eq_mul_inv] at hba
    exact (ENNReal.div_le_iff_le_mul (Or.inl hcβ_ne) (Or.inl hcβ_top)).mp hba
  rw [hcardF, Nat.cast_sum, hcardγ]
  calc (∑ a ∈ univ.filter G, (#(univ.filter fun b => Bad (e.symm (a, b))) : ℝ≥0∞))
      ≤ ∑ _a ∈ univ.filter G, p_bot * (Fintype.card β : ℝ≥0∞) := sum_le_sum hfiber
    _ = (#(univ.filter G) : ℝ≥0∞) * (p_bot * (Fintype.card β : ℝ≥0∞)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card α : ℝ≥0∞) * (p_bot * (Fintype.card β : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast card_filter_le _ _
    _ = p_bot * ((Fintype.card α : ℝ≥0∞) * (Fintype.card β : ℝ≥0∞)) := by ring

/-- When `whpThreshold c ≤ n_max` and `#W_set ≤ 2 * n_max`, the probability that `GoodTop` fails
for a uniform seed `Seed (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max) M_out` is at most
`(4 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c`. -/
theorem toOuterMeasure_not_goodTop_seed_le {c U n_max M_out : ℕ}
    (hth : whpThreshold c ≤ n_max) (W_set : Finset (Fin U)) (hW : #W_set ≤ 2 * n_max) :
    (PMF.uniformOfFintype
      (BitPackedDoubleTabulation.Seed
        (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max) M_out)).toOuterMeasure
      {θ | ¬ GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (kIndepWhp c n_max) W_set θ.1 θ.2.1} ≤
      (4 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hq1 : 1 ≤ qTabWhp c := by have := le_qTabWhp c; omega
  have hcode := two_mul_doubleTabCodeBound_le_pow_q_sub_one hth
  have hbase := toOuterMeasure_not_goodTop_le (R := rRedWhp c n_max) (M_out := M_out)
    (w0Whp_pos U) (le_two_pow_w0Whp U) hq1 (dTabWhp_eq c) hcode W_set
  set m := Nat.log 2 n_max
  have hm_ge : bMinWhp c ≤ m := bMinWhp_le_log hth
  have hm_big : 6553600 ≤ m := (le_bMinWhp c).trans hm_ge
  have hce_m : cEff c + 4 ≤ m := (cEff_add_four_le_bMinWhp c).trans hm_ge
  have hn_pow : n_max ≤ 2 ^ (m + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
  have hbchar_4 : m ≤ 4 * bCharWhp n_max + 3 := by
    unfold bCharWhp
    change m ≤ 4 * (m / 4) + 3
    omega
  have hc_le : c ≤ cEff c := le_cEff c
  have hterm1 : (((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ rRedWhp c n_max) ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
    rw [div_eq_mul_inv]
    have hW_pow : #W_set ≤ 2 ^ (m + 2) := by
      calc #W_set ≤ 2 * n_max := hW
        _ ≤ 2 * 2 ^ (m + 1) := Nat.mul_le_mul_left 2 hn_pow
        _ = 2 ^ (m + 2) := by rw [← Nat.pow_succ']
    have hK : #W_set * (#W_set - 1) ≤ 2 ^ (2 * m + 4) := by
      calc #W_set * (#W_set - 1) ≤ #W_set * #W_set := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ 2 ^ (m + 2) * 2 ^ (m + 2) := Nat.mul_le_mul hW_pow hW_pow
        _ = 2 ^ (2 * m + 4) := by rw [← Nat.pow_add]; ring_nf
    have hexp1 : 3 + (2 * m + 4) + (m + 1) * c ≤ rRedWhp c n_max := by
      unfold rRedWhp
      rw [cTabWhp_eq c]
      have hmul : 2 * (cEff c + 5) * m ≤ 8 * (cEff c + 5) * bCharWhp n_max + 6 * (cEff c + 5) := by
        nlinarith [hbchar_4]
      nlinarith
    exact mul_inv_two_pow_le_eighth_inv_pow hn_pos hK hn_pow hexp1
  have hterm2 :
      (2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max) : ℝ≥0∞) ^ 2) /
        ((2 : ℝ≥0∞) ^ ((qTabWhp c - 1) * bCharWhp n_max)) ^ 2 ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
    have hcb_le : doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max) ≤ 2 ^ bCharWhp n_max := by
      have := two_mul_doubleTabCodeBound_le_pow_bCharWhp hth
      omega
    have hK2 : 2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max)) ^ 2 ≤ 2 ^ (2 * bCharWhp n_max + 1) := by
      calc 2 * (doubleTabCodeBound _ _ _ _) ^ 2
          ≤ 2 * (2 ^ bCharWhp n_max) ^ 2 :=
            Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hcb_le 2)
        _ = 2 ^ (2 * bCharWhp n_max + 1) := by
            rw [← Nat.pow_mul, Nat.mul_comm _ 2, Nat.pow_succ']
    have hexp2 : 3 + (2 * bCharWhp n_max + 1) + (m + 1) * c ≤
        2 * ((qTabWhp c - 1) * bCharWhp n_max) := by
      rw [qTabWhp_eq c]
      have hq_sub : 4 * (cEff c + 6) + 2 - 1 = 4 * (cEff c + 6) + 1 := by omega
      rw [hq_sub]
      nlinarith [hbchar_4]
    have hrew_num : (2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max) : ℝ≥0∞) ^ 2) =
        (((2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
          (kIndepWhp c n_max)) ^ 2 : ℕ) : ℝ≥0∞)) := by
      push_cast; ring
    have hrew_den : (((2 : ℝ≥0∞) ^ ((qTabWhp c - 1) * bCharWhp n_max)) ^ 2) =
        (2 : ℝ≥0∞) ^ (2 * ((qTabWhp c - 1) * bCharWhp n_max)) := by
      rw [← pow_mul, mul_comm]
    rw [hrew_num, hrew_den, div_eq_mul_inv]
    exact mul_inv_two_pow_le_eighth_inv_pow hn_pos hK2 hn_pow hexp2
  refine hbase.trans ((add_le_add hterm1 hterm2).trans (le_of_eq ?_))
  rw [← add_mul]
  congr 1
  have h84 : (8 : ℝ≥0∞)⁻¹ + (8 : ℝ≥0∞)⁻¹ = (4 : ℝ≥0∞)⁻¹ := by
    have h8_ne : (8 : ℝ≥0∞) ≠ 0 := by norm_num
    have h8_top : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h4_ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
    have h4_top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
    apply ENNReal.mul_right_inj h8_ne h8_top |>.mp
    rw [mul_add, ENNReal.mul_inv_cancel h8_ne h8_top,
      show (8 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞) * ((4 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹) by ring,
      ENNReal.mul_inv_cancel h4_ne h4_top]
    norm_num
  exact h84

/-! ## Section 4: Window bucket caps, Feistel load balance, salt bounds, and main theorem -/

/-- Under `BalancedBuckets`, any set `S` of size `≤ n_max` puts at most `3 * (scaleWhp n_max) ^ 12`
keys into each Feistel bucket. -/
theorem card_bucket_le_of_balanced {c U n_max : ℕ} (_hth : whpThreshold c ≤ n_max)
    {h1 : ℕ → ℕ} {S : Finset (Fin U)} (hS : #S ≤ n_max)
    (hbal : BalancedBuckets U n_max h1 S) (b : Fin (numBucketsWhp n_max)) :
    #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      3 * (scaleWhp n_max) ^ 12 := by
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have h2M := le_two_mul_numBucketsWhp_mul_scale_pow12 n_max
  have hL_pos : 0 < scaleWhp n_max := scaleWhp_pos n_max
  have hδ : numBucketsWhp n_max * deltaWhp n_max ≤ numBucketsWhp n_max * (scaleWhp n_max) ^ 12 := by
    have hmul : deltaWhp n_max * (numBucketsWhp n_max * (8 * scaleWhp n_max)) ≤
        2 * numBucketsWhp n_max * (scaleWhp n_max) ^ 12 :=
      (Nat.div_mul_le_self n_max _).trans h2M
    have hL2 := two_le_scaleWhp n_max
    nlinarith
  have hup := (hbal b).1
  have htot : numBucketsWhp n_max *
      #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      numBucketsWhp n_max * (3 * (scaleWhp n_max) ^ 12) := by
    linarith
  exact Nat.le_of_mul_le_mul_left htot hM_pos

/-- Union of two `BalancedBuckets` sets of size `≤ n_max` has at most `6 * (scaleWhp n_max) ^ 12`
keys in every Feistel bucket. -/
theorem card_union_bucket_le_of_balanced {c U n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    {h1 : ℕ → ℕ} {S₁ S₂ : Finset (Fin U)} (hS₁ : #S₁ ≤ n_max) (hS₂ : #S₂ ≤ n_max)
    (hb₁ : BalancedBuckets U n_max h1 S₁) (hb₂ : BalancedBuckets U n_max h1 S₂)
    (b : Fin (numBucketsWhp n_max)) :
    #((S₁ ∪ S₂).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      6 * (scaleWhp n_max) ^ 12 := by
  rw [filter_union]
  calc #(S₁.filter _ ∪ S₂.filter _)
      ≤ #(S₁.filter _) + #(S₂.filter _) := card_union_le _ _
    _ ≤ 3 * (scaleWhp n_max) ^ 12 + 3 * (scaleWhp n_max) ^ 12 :=
        Nat.add_le_add (card_bucket_le_of_balanced hth hS₁ hb₁ b)
          (card_bucket_le_of_balanced hth hS₂ hb₂ b)
    _ = 6 * (scaleWhp n_max) ^ 12 := by ring

/-- Map each key `u : Fin U` to its quotient `< U` packaged in `Fin U`. -/
@[expose] def keyQuotientFin {U : ℕ} (b : ℕ) (u : Fin U) : Fin U :=
  ⟨keyQuotient b u.val, (Nat.div_le_self u.val (2 ^ b)).trans_lt u.isLt⟩

/-- Per-quotient `[0, 1]` bucket indicator `g` for Feistel bucket `b` on `S`, together with its
range, expectation sum `#S / M`, and pointwise sum `X_b`. -/
private def feistelQuotScore {U : ℕ} (n_max : ℕ) (S : Finset (Fin U))
    (b : Fin (numBucketsWhp n_max)) (q : Fin U) (y : Fin (2 ^ bWhp n_max)) : ℝ :=
  (#((S.filter fun u => keyQuotient (bWhp n_max) u.val = q.val).filter
    fun u => (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) : ℝ)

private theorem feistelQuotScore_props {U n_max : ℕ} (W_quot : Finset (Fin U))
    (S : Finset (Fin U)) (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot)
    (b : Fin (numBucketsWhp n_max)) :
    let g : W_quot → Fin (2 ^ bWhp n_max) → ℝ := fun q y => feistelQuotScore n_max S b q.1 y
    (∀ q ∈ (univ : Finset W_quot), ∀ y : Fin (2 ^ bWhp n_max), g q y ∈ Set.Icc (0 : ℝ) 1) ∧
    (∑ q ∈ (univ : Finset W_quot), (𝔼 y, g q y) = (#S : ℝ) / (numBucketsWhp n_max : ℝ)) ∧
    (∀ H : W_quot → Fin (2 ^ bWhp n_max), ∀ h1 : ℕ → ℕ,
      (∀ q : W_quot, h1 q.1.val = (H q).val) →
      ∑ q ∈ (univ : Finset W_quot), g q (H q) =
        (#(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) : ℝ)) := by
  dsimp only
  let S_q (q : W_quot) : Finset (Fin U) :=
    S.filter fun u => keyQuotient (bWhp n_max) u.val = q.1.val
  have hpart_card : ∀ (P : Fin U → Prop) [DecidablePred P],
      #(S.filter P) = ∑ q : W_quot, #((S_q q).filter P) := by
    intro P _
    simp only [S_q, filter_filter]
    rw [Finset.card_filter]
    have hpoint : ∀ u ∈ S,
        (if P u then 1 else 0) =
          ∑ q : W_quot, if keyQuotient (bWhp n_max) u.val = q.1.val ∧ P u then 1 else 0 := by
      intro u hu
      let q₀ : W_quot := ⟨keyQuotientFin (bWhp n_max) u, hqS u hu⟩
      rw [Fintype.sum_eq_single q₀]
      · simp [q₀, keyQuotientFin]
      · intro q hne
        have hval_ne : keyQuotient (bWhp n_max) u.val ≠ q.1.val := fun heq =>
          hne (Subtype.ext (Fin.ext heq.symm))
        simp [hval_ne]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun q => ?_
    rw [Finset.card_filter]
  refine ⟨?_, ?_, ?_⟩
  · intro q _ y
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hle1 : #((S_q q).filter fun u => (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) ≤ 1 := by
      refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
      obtain ⟨hq₁, hx₁⟩ := mem_filter.mp hu₁
      obtain ⟨hq₂, hx₂⟩ := mem_filter.mp hu₂
      have hfb₁ : feistelBucket (bWhp n_max) (fun _ => y.val) u₁.val = b.val := by
        unfold feistelBucket
        rwa [Nat.mod_eq_of_lt y.isLt]
      have hfb₂ : feistelBucket (bWhp n_max) (fun _ => y.val) u₂.val = b.val := by
        unfold feistelBucket
        rwa [Nat.mod_eq_of_lt y.isLt]
      exact Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
        (hfb₁.trans hfb₂.symm) ((mem_filter.mp hq₁).2.trans (mem_filter.mp hq₂).2.symm))
    unfold feistelQuotScore
    exact_mod_cast hle1
  · have hg_exp : ∀ q : W_quot,
        𝔼 y : Fin (2 ^ bWhp n_max), feistelQuotScore n_max S b q.1 y =
          (#(S_q q) : ℝ) / (numBucketsWhp n_max : ℝ) := by
      intro q
      have hgs (y : Fin (2 ^ bWhp n_max)) :
          feistelQuotScore n_max S b q.1 y = ∑ u ∈ S_q q,
            if (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val then (1 : ℝ) else 0 := by
        unfold feistelQuotScore
        rw [Finset.sum_boole]
      simp_rw [hgs]
      rw [expect_sum_comm]
      have hterm_u : ∀ u ∈ S_q q,
          (𝔼 y : Fin (2 ^ bWhp n_max),
            if (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val then (1 : ℝ) else 0) =
            1 / (numBucketsWhp n_max : ℝ) := by
        intro u _
        let y₀ : Fin (2 ^ bWhp n_max) :=
          ⟨b.val ^^^ keyLow (bWhp n_max) u.val, Nat.xor_lt_two_pow b.isLt (keyLow_lt _ _)⟩
        have hiff : ∀ y : Fin (2 ^ bWhp n_max),
            ((y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) ↔ y = y₀ := by
          intro y
          constructor
          · intro hy
            apply Fin.ext
            dsimp only [y₀]
            rw [← hy, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          · rintro rfl
            dsimp only [y₀]
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        simp_rw [hiff]
        rw [Finset.expect_eq_sum_div_card, card_univ, Fintype.card_fin, Fintype.sum_ite_eq']
        rfl
      rw [Finset.sum_congr rfl hterm_u, sum_const, nsmul_eq_mul, mul_one_div]
    simp_rw [hg_exp, ← sum_div]
    congr 1
    have hcS := hpart_card (fun _ => True)
    rw [filter_true_of_mem (fun _ _ => trivial)] at hcS
    rw [hcS, Nat.cast_sum]
    refine Fintype.sum_congr _ _ fun q => ?_
    rw [filter_true_of_mem (fun _ _ => trivial)]
  · intro H h1 hH
    rw [hpart_card (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val), Nat.cast_sum]
    refine Fintype.sum_congr _ _ fun q => ?_
    unfold feistelQuotScore
    congr 2
    refine filter_congr fun u hu => ?_
    have hqu : keyQuotient (bWhp n_max) u.val = q.1.val := (mem_filter.mp hu).2
    unfold feistelBucket
    rw [hqu, hH q, Nat.mod_eq_of_lt (H q).isLt]

/-- Single-bucket bottom-table tail bound for Feistel bucket `b`. -/
private theorem toOuterMeasure_not_balancedBucket_single_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (W_quot : Finset (Fin U))
    {α₁ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_quot α₁ T₁)
    (S : Finset (Fin U)) (hS : #S ≤ n_max)
    (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot)
    (b : Fin (numBucketsWhp n_max)) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max))).toOuterMeasure
      {T₂ | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b} ≤
      (rIndepWhp c n_max : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * rIndepWhp c n_max))⁻¹ := by
  let Bot := DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max)
  let M := numBucketsWhp n_max
  let r := rIndepWhp c n_max
  let δ := deltaWhp n_max
  have hk_base := isKWiseIndependentHash_evalSalted_of_goodTop
    (M_out := bWhp n_max) (s_max := 1)
    Nat.one_le_two_pow (Nat.min_le_right _ _) hgood
  let e_in : W_quot → Fin 1 × W_quot := fun q => (⟨0, Nat.zero_lt_one⟩, q)
  have he_in : Function.Injective e_in := fun _ _ h => (Prod.mk.inj h).2
  have hk_q := hk_base.comp he_in
  have hM_pos : 0 < M := by dsimp only [M, numBucketsWhp]; positivity
  have hr_pos : 1 ≤ r := by
    dsimp only [r, rIndepWhp]
    have := one_le_cEff c
    have := two_le_scaleWhp n_max
    nlinarith
  have hL_ge := cEff_add_four_le_scaleWhp hth
  have hL_pos : 0 < scaleWhp n_max := scaleWhp_pos n_max
  have hδ_pos : 0 < δ := by
    have h10 := scaleWhp_pow10_le_deltaWhp hth
    have : 0 < (scaleWhp n_max) ^ 10 := by positivity
    omega
  obtain ⟨hg_Icc, hsum_exp, hsum_H⟩ := feistelQuotScore_props W_quot S hqS b
  let g : W_quot → Fin (2 ^ bWhp n_max) → ℝ := fun q y => feistelQuotScore n_max S b q.1 y
  have htail := hk_q.dens_filter_le_abs_sum_sub_expect_of_Icc hr_pos
    (univ : Finset W_quot) g hg_Icc (Nat.cast_pos.mpr hδ_pos)
  have hdens_le :
      _ ≤ (r : ℝ) * (((r ^ 2 * (2 * (scaleWhp n_max) ^ 12) : ℕ) : ℝ) / ((δ ^ 2 : ℕ) : ℝ)) ^ r :=
    htail.trans <| by
      rw [hsum_exp]
      have hmax_le : max ((#S : ℝ) / (M : ℝ)) 1 ≤ ((2 * (scaleWhp n_max) ^ 12 : ℕ) : ℝ) := by
        refine max_le ?_ ?_
        · rw [div_le_iff₀ (Nat.cast_pos.mpr hM_pos)]
          have hSn : #S ≤ 2 * (scaleWhp n_max) ^ 12 * M := by
            have := le_two_mul_numBucketsWhp_mul_scale_pow12 n_max
            dsimp only [M]
            linarith
          exact_mod_cast hSn
        · have : 1 ≤ 2 * (scaleWhp n_max) ^ 12 := by
            have := Nat.one_le_pow 12 _ hL_pos
            omega
          exact_mod_cast this
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ r)
        (Nat.cast_nonneg r)
      push_cast at hmax_le ⊢
      gcongr
  have hpmf :
      (PMF.uniformOfFintype Bot).toOuterMeasure
        {T₂ : Bot | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b} ≤
        ENNReal.ofReal
          ((r : ℝ) *
            (((r ^ 2 * (2 * (scaleWhp n_max) ^ 12) : ℕ) : ℝ) / ((δ ^ 2 : ℕ) : ℝ)) ^ r) := by
    refine toOuterMeasure_uniformOfFintype_le_of_dens_le _ _ ?_ hdens_le
    intro T₂ hT₂
    rw [Set.mem_ofPred_eq, BalancedBucketAt] at hT₂
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hsum_T₂ := hsum_H
      (fun q => evalSalted U (w0Whp U) (cTabWhp c * bCharWhp n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (bWhp n_max) 1 (α₁, T₁, T₂) ((e_in q).1, (e_in q).2.1))
      (bktHash c U n_max (α₁, T₁, T₂)) fun q => by
        unfold bktHash
        simp [q.1.isLt, e_in, rRedWhp]
    rw [sum_sub_distrib, hsum_T₂, hsum_exp]
    set X_b := #(S.filter fun u =>
      feistelBucket (bWhp n_max) (bktHash c U n_max (α₁, T₁, T₂)) u.val = b.val)
    have hM_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hrew : (X_b : ℝ) - (#S : ℝ) / (M : ℝ) = ((M : ℝ) * (X_b : ℝ) - (#S : ℝ)) / (M : ℝ) := by
      field_simp [hM_real.ne']
    rw [hrew, abs_div, abs_of_pos hM_real, le_div_iff₀ hM_real]
    have hdiff_nat : M * δ < M * X_b - #S ∨ M * δ < #S - M * X_b := by
      dsimp only [M, δ]
      omega
    rcases hdiff_nat with hgt | hlt
    · have hgt_r : (δ : ℝ) * (M : ℝ) ≤ (M : ℝ) * (X_b : ℝ) - (#S : ℝ) := by
        have h1 : δ * M ≤ M * X_b - #S := by linarith [hgt.le]
        have h2 : #S ≤ M * X_b := by omega
        exact_mod_cast h1
      exact hgt_r.trans (le_abs_self _)
    · have hlt_r : (δ : ℝ) * (M : ℝ) ≤ (#S : ℝ) - (M : ℝ) * (X_b : ℝ) := by
        have h1 : δ * M ≤ #S - M * X_b := by linarith [hlt.le]
        have h2 : M * X_b ≤ #S := by omega
        exact_mod_cast h1
      rw [abs_sub_comm]
      exact hlt_r.trans (le_abs_self _)
  have hAB : 2 ^ 3 * (r ^ 2 * (2 * (scaleWhp n_max) ^ 12)) ≤ δ ^ 2 := by
    have h10 := scaleWhp_pow10_le_deltaWhp hth
    set L := scaleWhp n_max
    have hL1 : 6553600 ≤ L := hL_ge.1
    have hL2 : cEff c + 4 ≤ L := hL_ge.2
    have hr_le : r ≤ L ^ 2 := by
      dsimp only [r, rIndepWhp]
      nlinarith
    calc 8 * (r ^ 2 * (2 * L ^ 12))
        = 16 * r ^ 2 * L ^ 12 := by ring
      _ ≤ 16 * (L ^ 2) ^ 2 * L ^ 12 := by gcongr
      _ = 16 * L ^ 16 := by ring
      _ ≤ L ^ 4 * L ^ 16 := by
          refine Nat.mul_le_mul_right _ ?_
          calc 16 ≤ L ^ 1 := by simp; omega
            _ ≤ L ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      _ = (L ^ 10) ^ 2 := by ring
      _ ≤ δ ^ 2 := Nat.pow_le_pow_left h10 2
  refine hpmf.trans ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
  have hdiv_pow := ofReal_div_pow_le_inv_two_pow (r := r) (by positivity) hAB
  gcongr

/-- Conditional bottom-table tail bound for `BalancedBuckets` on a single set `S` (`#S ≤ n_max`)
whose quotients lie in `W_quot`, given `GoodTop` on `W_quot`. -/
theorem toOuterMeasure_not_balancedBuckets_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (W_quot : Finset (Fin U))
    {α₁ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_quot α₁ T₁)
    (S : Finset (Fin U)) (hS : #S ≤ n_max)
    (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max))).toOuterMeasure
      {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (α₁, T₁, T₂)) S} ≤
      ((numBucketsWhp n_max * rIndepWhp c n_max : ℕ) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ (3 * rIndepWhp c n_max))⁻¹ := by
  let Bot := DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max)
  let M := numBucketsWhp n_max
  let r := rIndepWhp c n_max
  have hunion :
      {T₂ : Bot | ¬ BalancedBuckets U n_max (bktHash c U n_max (α₁, T₁, T₂)) S} ⊆
        ⋃ b : Fin M,
          {T₂ : Bot | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b} := by
    intro T₂ hT₂
    simp only [Set.mem_ofPred_eq, BalancedBuckets, not_forall] at hT₂
    exact Set.mem_iUnion.mpr hT₂
  calc (PMF.uniformOfFintype Bot).toOuterMeasure
        {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (α₁, T₁, T₂)) S}
      ≤ (PMF.uniformOfFintype Bot).toOuterMeasure
          (⋃ b : Fin M,
            {T₂ : Bot | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b}) :=
        MeasureTheory.measure_mono hunion
    _ ≤ ∑ b : Fin M,
          (PMF.uniformOfFintype Bot).toOuterMeasure
            {T₂ : Bot | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b} :=
        outerMeasure_iUnion_fintype_le _ _
    _ ≤ ∑ _b : Fin M, (r : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ :=
        Finset.sum_le_sum fun b _ =>
          toOuterMeasure_not_balancedBucket_single_le hth W_quot hgood S hS hqS b
    _ = ((M * r : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

/-- Exponent helper `3 + (2 * m + 2) + (m + 1) * c ≤ 3 * rIndepWhp c n_max` when
`whpThreshold c ≤ n_max`. -/
private theorem exp_three_mul_rIndepWhp_ge (c n_max : ℕ) (hth : whpThreshold c ≤ n_max) :
    3 + (2 * Nat.log 2 n_max + 2) + (Nat.log 2 n_max + 1) * c ≤ 3 * rIndepWhp c n_max := by
  have hm_ge : bMinWhp c ≤ Nat.log 2 n_max := bMinWhp_le_log hth
  have hm_big : 6553600 ≤ Nat.log 2 n_max := (le_bMinWhp c).trans hm_ge
  have hm_le_L : Nat.log 2 n_max ≤ scaleWhp n_max := log_le_scaleWhp n_max
  have hc_le : c ≤ cEff c := le_cEff c
  unfold rIndepWhp
  nlinarith

/-- Conditional bottom-table tail bound for multi-salt intra-bucket collision-freedom across all
`M` window buckets when each window bucket has size `≤ 6 * (scaleWhp n_max) ^ 12`. -/
theorem toOuterMeasure_not_salt_inj_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (h1 : ℕ → ℕ) (W_keys : Finset (Fin U))
    (hbkt : ∀ b : Fin (numBucketsWhp n_max),
      #(W_keys.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
        6 * (scaleWhp n_max) ^ 12)
    {α₂ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_keys α₂ T₁) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))).toOuterMeasure
      {T₂ | ¬ ∀ b : Fin (numBucketsWhp n_max),
        ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  classical
  set Bot := DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)
  set M := numBucketsWhp n_max
  set r := rIndepWhp c n_max
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hk_fp : IsKWiseIndependentHash (2 * sMaxWhp c n_max)
      (fun (T₂ : Bot) (p : Fin (sMaxWhp c n_max) × W_keys) =>
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (p.1, p.2.1)) :=
    isKWiseIndependentHash_evalSalted_of_goodTop (sMaxWhp_le_pow_bChar hth)
      (Nat.min_le_right _ _) hgood
  have hper_b : ∀ b : Fin M,
      (PMF.uniformOfFintype Bot).toOuterMeasure
        {T₂ : Bot | ¬ ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ≤
        ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ := by
    intro b
    let S_b : Finset W_keys :=
      univ.filter fun u : W_keys => feistelBucket (bWhp n_max) h1 u.1.val = b.val
    have hmap_Sb : S_b.map (Function.Embedding.subtype _) =
        W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) := by
      ext u
      simp [S_b, and_comm]
    have hcard_Sb : #S_b ≤ 6 * (scaleWhp n_max) ^ 12 := by
      rw [← Finset.card_map (Function.Embedding.subtype _), hmap_Sb]
      exact hbkt b
    let F_coll : Finset Bot :=
      {T₂ : Bot | ∀ s : Fin (sMaxWhp c n_max),
        ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧
          evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, u.1) =
          evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, v.1)}
    have hsub_b :
        {T₂ : Bot | ¬ ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ⊆
        (F_coll : Set Bot) := by
      intro T₂ hT₂
      rw [Set.mem_ofPred_eq] at hT₂
      rw [mem_coe]
      simp only [F_coll, mem_filter, mem_univ, true_and]
      intro s
      push Not at hT₂
      have hns := hT₂ s
      unfold Set.InjOn at hns
      push Not at hns
      obtain ⟨u₁, hu₁, u₂, hu₂, hfp, hne⟩ := hns
      rw [mem_coe, mem_filter] at hu₁ hu₂
      refine ⟨⟨u₁, hu₁.1⟩, mem_filter.mpr ⟨mem_univ _, hu₁.2⟩,
        ⟨u₂, hu₂.1⟩, mem_filter.mpr ⟨mem_univ _, hu₂.2⟩,
        fun h => hne (congrArg Subtype.val h), Fin.ext hfp⟩
    have hdens1 :
        (F_coll.dens : ℝ) ≤
          (((#S_b ^ 2 : ℕ) : ℝ) / ((2 ^ fpBitsWhp n_max : ℕ) : ℝ)) ^ sMaxWhp c n_max := by
      simpa only [F_coll, Fintype.card_fin, Nat.cast_pow] using
        hk_fp.dens_forall_salt_exists_collision_le S_b
    have hAB : 2 ^ 3 * (#S_b ^ 2) ≤ 2 ^ fpBitsWhp n_max := by
      set L := scaleWhp n_max
      have hL_big : 6553600 ≤ L := (cEff_add_four_le_scaleWhp hth).1
      have hfp_eq : 2 ^ fpBitsWhp n_max = L ^ 36 := by
        dsimp only [L, scaleWhp, slabScale, fpBitsWhp, ellWhp]
        rw [← Nat.pow_mul, Nat.mul_comm _ 36]
      rw [hfp_eq]
      calc 8 * #S_b ^ 2
          ≤ 8 * (6 * L ^ 12) ^ 2 := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hcard_Sb 2)
        _ = 288 * L ^ 24 := by ring
        _ ≤ L ^ 12 * L ^ 24 := by
            refine Nat.mul_le_mul_right _ ?_
            calc 288 ≤ L ^ 1 := by simp; omega
              _ ≤ L ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
        _ = L ^ 36 := by ring
    exact (toOuterMeasure_uniformOfFintype_le_of_dens_le _ F_coll hsub_b hdens1).trans
      (ofReal_div_pow_le_inv_two_pow (Nat.two_pow_pos _) hAB)
  have hunion :
      {T₂ : Bot | ¬ ∀ b : Fin M, ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
          (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
            Set (Fin U))} ⊆
        ⋃ b : Fin M,
          {T₂ : Bot | ¬ ∃ salt : Fin (sMaxWhp c n_max),
            Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
              (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
                Set (Fin U))} := by
    intro T₂ hT₂
    simp only [Set.mem_ofPred_eq, not_forall] at hT₂
    exact Set.mem_iUnion.mpr hT₂
  have hsum_le :
      (PMF.uniformOfFintype Bot).toOuterMeasure
        {T₂ | ¬ ∀ b : Fin M, ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ≤
        (M : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ := by
    calc _ ≤ _ := MeasureTheory.measure_mono hunion
      _ ≤ ∑ b : Fin M, _ := outerMeasure_iUnion_fintype_le _ _
      _ ≤ ∑ _b : Fin M, ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ := Finset.sum_le_sum fun b _ => hper_b b
      _ = (M : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * r))⁻¹ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine hsum_le.trans ?_
  have hM_le : M ≤ 2 ^ (2 * Nat.log 2 n_max + 2) := by
    have hM_n : M ≤ n_max := by
      have h12 := numBucketsWhp_mul_scale_pow12_le hth
      have : 1 ≤ (scaleWhp n_max) ^ 12 := Nat.one_le_pow 12 _ (scaleWhp_pos n_max)
      nlinarith
    have hn_pow : n_max ≤ 2 ^ (Nat.log 2 n_max + 1) :=
      (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
    exact hM_n.trans (hn_pow.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  exact mul_inv_two_pow_le_eighth_inv_pow hn_pos hM_le
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le (exp_three_mul_rIndepWhp_ge c n_max hth)

/-- Conditional bottom-table tail bound on the number of keys in `W_ins` that ever collide with
another key in their window bucket under any salt `< sMaxWhp c n_max`. -/
theorem toOuterMeasure_salt_coll_count_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (h1 : ℕ → ℕ)
    (W_ins W_keys : Finset (Fin U)) (hsub_ins : W_ins ⊆ W_keys)
    (hW_ins : #W_ins ≤ 3 * (scaleWhp n_max) ^ 18)
    (hbkt : ∀ b : Fin (numBucketsWhp n_max),
      #(W_keys.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
        6 * (scaleWhp n_max) ^ 12)
    {α₂ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_keys α₂ T₁) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))).toOuterMeasure
      {T₂ | 2 * rIndepWhp c n_max ≤
        #(W_ins.filter fun u =>
          ∃ v ∈ W_keys.filter (fun w =>
            feistelBucket (bWhp n_max) h1 w.val = feistelBucket (bWhp n_max) h1 u.val),
            u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
              fpHash c U n_max (α₂, T₁, T₂) salt u =
                fpHash c U n_max (α₂, T₁, T₂) salt v)} ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  classical
  set Bot := DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)
  set r := rIndepWhp c n_max
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hk_fp : IsKWiseIndependentHash (2 * r)
      (fun (T₂ : Bot) (p : Fin (sMaxWhp c n_max) × W_keys) =>
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (p.1, p.2.1)) :=
    isKWiseIndependentHash_evalSalted_of_goodTop (sMaxWhp_le_pow_bChar hth)
      (Nat.min_le_right _ _) hgood
  let Q_set : Finset W_keys := univ.filter fun u : W_keys => u.1 ∈ W_ins
  let W_of (u : W_keys) : Finset W_keys :=
    univ.filter fun v : W_keys =>
      feistelBucket (bWhp n_max) h1 v.1.val = feistelBucket (bWhp n_max) h1 u.1.val
  have hQ_card : #Q_set ≤ 3 * (scaleWhp n_max) ^ 18 := by
    have hmap : Q_set.map (Function.Embedding.subtype _) = W_ins := by
      ext u
      simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, Q_set, mem_filter,
        mem_univ, true_and, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨_, hu⟩ => hu, fun hu => ⟨hsub_ins hu, hu⟩⟩
    rw [← Finset.card_map (Function.Embedding.subtype _), hmap]
    exact hW_ins
  have hw_cap : ∀ u ∈ Q_set, #(W_of u) ≤ 6 * (scaleWhp n_max) ^ 12 := by
    intro u _
    let b_u : Fin (numBucketsWhp n_max) :=
      ⟨feistelBucket (bWhp n_max) h1 u.1.val, feistelBucket_lt (bWhp n_max) h1 u.1.val⟩
    have hmap : (W_of u).map (Function.Embedding.subtype _) =
        W_keys.filter (fun v => feistelBucket (bWhp n_max) h1 v.val = b_u.val) := by
      ext v
      simp [W_of, b_u, and_comm]
    rw [← Finset.card_map (Function.Embedding.subtype _), hmap]
    exact hbkt b_u
  let F_cnt : Finset Bot :=
    {T₂ : Bot | 2 * r ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin (sMaxWhp c n_max),
          evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, u.1) =
          evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, v.1))}
  have hsub_ev :
      {T₂ : Bot | 2 * r ≤
        #(W_ins.filter fun u =>
          ∃ v ∈ W_keys.filter (fun w =>
            feistelBucket (bWhp n_max) h1 w.val = feistelBucket (bWhp n_max) h1 u.val),
            u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
              fpHash c U n_max (α₂, T₁, T₂) salt u =
                fpHash c U n_max (α₂, T₁, T₂) salt v)} ⊆
      (F_cnt : Set Bot) := by
    intro T₂ hT₂
    rw [Set.mem_ofPred_eq] at hT₂
    rw [mem_coe]
    simp only [F_cnt, mem_filter, mem_univ, true_and]
    refine hT₂.trans ?_
    let f_sub : Finset W_keys := Q_set.filter fun u =>
      ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin (sMaxWhp c n_max),
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, u.1) =
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (s, v.1)
    rw [← Finset.card_map (Function.Embedding.subtype _) (s := f_sub)]
    refine Finset.card_le_card fun u hu => ?_
    simp only [mem_filter] at hu
    obtain ⟨hu_ins, v, ⟨hv_W, hfb_eq⟩, hne_uv, s, hfp⟩ := hu
    refine mem_map.mpr ⟨⟨u, hsub_ins hu_ins⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hu_ins⟩,
      ⟨v, hv_W⟩, mem_filter.mpr ⟨mem_univ _, hfb_eq⟩,
      fun h => hne_uv (congrArg Subtype.val h), s, Fin.ext hfp⟩, rfl⟩
  have hdens :
      (F_cnt.dens : ℝ) ≤
        (((#Q_set * (6 * (scaleWhp n_max) ^ 12) * sMaxWhp c n_max : ℕ) : ℝ) /
          ((2 ^ fpBitsWhp n_max : ℕ) : ℝ)) ^ r := by
    simpa only [F_cnt, Fintype.card_fin] using
      hk_fp.dens_card_local_salt_colliding_ge_le Q_set W_of hw_cap
  have hAB : 2 ^ 3 * (#Q_set * (6 * (scaleWhp n_max) ^ 12) * sMaxWhp c n_max) ≤
      2 ^ fpBitsWhp n_max := by
    set L := scaleWhp n_max
    have hL := cEff_add_four_le_scaleWhp hth
    have hL1 : 6553600 ≤ L := hL.1
    have hL2 : cEff c + 4 ≤ L := hL.2
    have hfp_eq : 2 ^ fpBitsWhp n_max = L ^ 36 := by
      dsimp only [L, scaleWhp, slabScale, fpBitsWhp, ellWhp]
      rw [← Nat.pow_mul, Nat.mul_comm _ 36]
    rw [hfp_eq]
    have hs_le : sMaxWhp c n_max ≤ L ^ 2 := by
      unfold sMaxWhp
      nlinarith
    calc 8 * (#Q_set * (6 * L ^ 12) * sMaxWhp c n_max)
        ≤ 8 * ((3 * L ^ 18) * (6 * L ^ 12) * L ^ 2) :=
          Nat.mul_le_mul_left 8 (Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ_card) hs_le)
      _ = 144 * L ^ 32 := by ring
      _ ≤ L ^ 4 * L ^ 32 := by
          refine Nat.mul_le_mul_right _ ?_
          calc 144 ≤ L ^ 1 := by simp; omega
            _ ≤ L ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
      _ = L ^ 36 := by ring
  have hpmf := (toOuterMeasure_uniformOfFintype_le_of_dens_le _ F_cnt hsub_ev hdens).trans
    (ofReal_div_pow_le_inv_two_pow (Nat.two_pow_pos _) hAB)
  refine hpmf.trans ?_
  simpa only [Nat.cast_one, one_mul] using
    (mul_inv_two_pow_le_eighth_inv_pow (K := 1) (a := 0) hn_pos le_rfl
      (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
      (by have := exp_three_mul_rIndepWhp_ge c n_max hth; linarith))

/-- **Master per-operation bad-seed probability bound**:
For every capacity `whpThreshold c ≤ n_max`, exponent `c : ℕ`, and admissible oblivious operation
sequence `ops : List (Dynamic.Op U)` (`ValidOpSeq V n_max (Dictionary.empty U) ops`),
`(seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem toOuterMeasure_not_goodSeedOnWindow_le {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max)
    {ops : List (Dynamic.Op U)}
    (hv : ValidOpSeq V n_max (Dictionary.empty U) ops) :
    (seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
      (max n_max 1 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hmax_eq : max (n_max : ℝ≥0∞) 1 = (n_max : ℝ≥0∞) :=
    max_eq_left (by exact_mod_cast hn_pos)
  rw [hmax_eq]
  set s_start := windowStartState U n_max ops
  set suf := windowSuffix U n_max ops
  set W_ins := opInsKeys suf
  set W_keys := Dictionary.dom s_start ∪ W_ins
  set W_quot := W_keys.image (keyQuotientFin (bWhp n_max))
  have hv_split : ValidOpSeq V n_max (Dictionary.empty U)
      (ops.take (ops.length - windowLenWhp n_max) ++ suf) := by
    dsimp only [suf, windowSuffix]
    rwa [List.take_append_drop]
  obtain ⟨hv_pre, hv_suf⟩ := (ValidOpSeq.append_iff _ _ _).mp hv_split
  have hdom_empty : #(Dictionary.dom (Dictionary.empty U)) ≤ n_max := by simp
  have hdom_start : #(Dictionary.dom s_start) ≤ n_max :=
    card_dom_le_of_validOpSeq hdom_empty hv_pre s_start (runOps_mem_stateSeq _ _)
  have hdom_seq : ∀ s ∈ stateSeq s_start suf, #(Dictionary.dom s) ≤ n_max :=
    card_dom_le_of_validOpSeq hdom_start hv_suf
  set L := scaleWhp n_max
  have hL_big : 6553600 ≤ L := (cEff_add_four_le_scaleWhp hth).1
  have hL96 : L ^ 96 ≤ n_max := scaleWhp_pow96_le_n_max hth
  have hlen_suf : suf.length ≤ 2 * L ^ 18 + 2 := length_windowSuffix_le U n_max ops
  have hW_ins_3 : #W_ins ≤ 3 * L ^ 18 := by
    have hc : #W_ins ≤ 2 * L ^ 18 + 2 := (card_opInsKeys_le suf).trans hlen_suf
    have h2 : 2 ≤ L ^ 18 := by
      calc 2 ≤ L ^ 1 := by simp; omega
        _ ≤ L ^ 18 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hW_ins_n : #W_ins ≤ n_max := by
    refine hW_ins_3.trans ((?_: 3 * L ^ 18 ≤ L ^ 96).trans hL96)
    calc 3 * L ^ 18 ≤ L * L ^ 18 := Nat.mul_le_mul_right _ (by omega)
      _ = L ^ 19 := by ring
      _ ≤ L ^ 96 := Nat.pow_le_pow_right (by omega) (by decide)
  have hW_keys_2n : #W_keys ≤ 2 * n_max := by
    calc #W_keys ≤ #(Dictionary.dom s_start) + #W_ins := card_union_le _ _
      _ ≤ n_max + n_max := Nat.add_le_add hdom_start hW_ins_n
      _ = 2 * n_max := by ring
  have hW_quot_2n : #W_quot ≤ 2 * n_max := card_image_le.trans hW_keys_2n
  let G₁ (θ₁ : BktSeed c U n_max) : Prop :=
    (∀ s ∈ stateSeq s_start suf,
      BalancedBuckets U n_max (bktHash c U n_max θ₁) (Dictionary.dom s)) ∧
    BalancedBuckets U n_max (bktHash c U n_max θ₁) W_ins
  have hbkt_bad : (PMF.uniformOfFintype (BktSeed c U n_max)).toOuterMeasure
      {θ₁ | ¬ G₁ θ₁} ≤ (2 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
    let e₁ : BktSeed c U n_max ≃
        (Fin (2 ^ (w0Whp U - 1)) ×
          DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)) ×
        DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max) :=
      { toFun := fun θ => ((θ.1, θ.2.1), θ.2.2)
        invFun := fun q => (q.1.1, (q.1.2, q.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    let G_top₁ (p : Fin (2 ^ (w0Whp U - 1)) ×
        DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)) : Prop :=
      GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (kIndepWhp c n_max) W_quot p.1 p.2
    have htop₁ : (PMF.uniformOfFintype _).toOuterMeasure {p | ¬ G_top₁ p} ≤
        (4 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
      rw [← toOuterMeasure_uniformOfFintype_fst e₁ (fun p => ¬ G_top₁ p)]
      exact toOuterMeasure_not_goodTop_seed_le hth W_quot hW_quot_2n
    have hbot₁ : ∀ p, G_top₁ p →
        (PMF.uniformOfFintype
          (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max))).toOuterMeasure
          {T₂ | ¬ G₁ (e₁.symm (p, T₂))} ≤
          ((8 : ℝ≥0∞)⁻¹ + (8 : ℝ≥0∞)⁻¹) * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
      intro p hp
      have hsub_or : {T₂ | ¬ G₁ (e₁.symm (p, T₂))} ⊆
          {T₂ | ¬ ∀ s ∈ stateSeq s_start suf,
            BalancedBuckets U n_max (bktHash c U n_max (p.1, p.2, T₂)) (Dictionary.dom s)} ∪
          {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (p.1, p.2, T₂)) W_ins} := by
        intro T₂ hT₂
        exact not_and_or.mp hT₂
      refine (MeasureTheory.measure_mono hsub_or).trans ?_
      refine (MeasureTheory.measure_union_le _ _).trans ?_
      rw [add_mul]
      refine add_le_add ?_ ?_
      · let stFin : Finset (State U) := (stateSeq s_start suf).toFinset
        have hsub_st :
            {T₂ | ¬ ∀ s ∈ stateSeq s_start suf,
              BalancedBuckets U n_max (bktHash c U n_max (p.1, p.2, T₂)) (Dictionary.dom s)} ⊆
              ⋃ s ∈ stFin,
                {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (p.1, p.2, T₂))
                  (Dictionary.dom s)} := by
          intro T₂ hT₂
          simp only [Set.mem_ofPred_eq, not_forall] at hT₂
          obtain ⟨s, hs, hnb⟩ := hT₂
          exact Set.mem_biUnion (List.mem_toFinset.mpr hs) hnb
        have hsum_st :
            (PMF.uniformOfFintype _).toOuterMeasure
              {T₂ | ¬ ∀ s ∈ stateSeq s_start suf,
                BalancedBuckets U n_max (bktHash c U n_max (p.1, p.2, T₂)) (Dictionary.dom s)} ≤
              ((#stFin * (numBucketsWhp n_max * rIndepWhp c n_max) : ℕ) : ℝ≥0∞) *
                ((2 : ℝ≥0∞) ^ (3 * rIndepWhp c n_max))⁻¹ := by
          calc _ ≤ _ := MeasureTheory.measure_mono hsub_st
            _ ≤ ∑ s ∈ stFin, _ := outerMeasure_biUnion_finset_le _ _ _
            _ ≤ ∑ _s ∈ stFin,
                  ((numBucketsWhp n_max * rIndepWhp c n_max : ℕ) : ℝ≥0∞) *
                    ((2 : ℝ≥0∞) ^ (3 * rIndepWhp c n_max))⁻¹ := by
                refine Finset.sum_le_sum fun s hs => ?_
                have hs_mem := List.mem_toFinset.mp hs
                refine toOuterMeasure_not_balancedBuckets_bot_le hth W_quot hp
                  (Dictionary.dom s) (hdom_seq s hs_mem) fun u hu => ?_
                exact mem_image_of_mem _ (dom_subset_union_opInsKeys _ _ s hs_mem hu)
            _ = _ := by rw [sum_const, nsmul_eq_mul]; push_cast; ring
        refine hsum_st.trans ?_
        have hK_st : #stFin * (numBucketsWhp n_max * rIndepWhp c n_max) ≤
            2 ^ (2 * Nat.log 2 n_max + 2) := by
          have hst_len : #stFin ≤ 3 * L ^ 18 := by
            have hl1 : #stFin ≤ (stateSeq s_start suf).length := List.toFinset_card_le _
            rw [length_stateSeq] at hl1
            have h3 : 3 ≤ L ^ 18 := by
              calc 3 ≤ L ^ 1 := by simp; omega
                _ ≤ L ^ 18 := Nat.pow_le_pow_right (by omega) (by decide)
            omega
          have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
          have hr_L2 : rIndepWhp c n_max ≤ L ^ 2 := by
            have := (cEff_add_four_le_scaleWhp hth).2
            unfold rIndepWhp
            nlinarith
          have hprod_n2 : #stFin * (numBucketsWhp n_max * rIndepWhp c n_max) ≤ n_max * n_max := by
            have hp1 : #stFin * rIndepWhp c n_max ≤ n_max := by
              calc #stFin * rIndepWhp c n_max ≤ (3 * L ^ 18) * L ^ 2 := Nat.mul_le_mul hst_len hr_L2
                _ = 3 * L ^ 20 := by ring
                _ ≤ L * L ^ 20 := Nat.mul_le_mul_right _ (by omega)
                _ = L ^ 21 := by ring
                _ ≤ L ^ 96 := Nat.pow_le_pow_right (by omega) (by decide)
                _ ≤ n_max := hL96
            have hM_n : numBucketsWhp n_max ≤ n_max := by
              have : 1 ≤ L ^ 12 := Nat.one_le_pow 12 _ (scaleWhp_pos n_max)
              nlinarith
            calc #stFin * (numBucketsWhp n_max * rIndepWhp c n_max)
                = (#stFin * rIndepWhp c n_max) * numBucketsWhp n_max := by ring
              _ ≤ n_max * n_max := Nat.mul_le_mul hp1 hM_n
          have hn_pow := (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
          calc #stFin * (numBucketsWhp n_max * rIndepWhp c n_max)
              ≤ n_max * n_max := hprod_n2
            _ ≤ 2 ^ (Nat.log 2 n_max + 1) * 2 ^ (Nat.log 2 n_max + 1) :=
                Nat.mul_le_mul hn_pow hn_pow
            _ = 2 ^ (2 * Nat.log 2 n_max + 2) := by rw [← Nat.pow_add]; ring_nf
        exact mul_inv_two_pow_le_eighth_inv_pow hn_pos hK_st
          (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
          (exp_three_mul_rIndepWhp_ge c n_max hth)
      · refine (toOuterMeasure_not_balancedBuckets_bot_le hth W_quot hp W_ins hW_ins_n
          (fun u hu => mem_image_of_mem _ (mem_union_right _ hu))).trans ?_
        have hK_ins : numBucketsWhp n_max * rIndepWhp c n_max ≤
            2 ^ (2 * Nat.log 2 n_max + 2) := by
          have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
          have hr_L2 : rIndepWhp c n_max ≤ L ^ 2 := by
            have := (cEff_add_four_le_scaleWhp hth).2
            unfold rIndepWhp
            nlinarith
          have hMr_n : numBucketsWhp n_max * rIndepWhp c n_max ≤ n_max := by
            have h2_12 : L ^ 2 ≤ L ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
            exact (Nat.mul_le_mul_left _ (hr_L2.trans h2_12)).trans hM_L12
          have hn_pow := (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
          exact hMr_n.trans (hn_pow.trans (Nat.pow_le_pow_right (by decide) (by omega)))
        exact mul_inv_two_pow_le_eighth_inv_pow hn_pos hK_ins
          (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
          (exp_three_mul_rIndepWhp_ge c n_max hth)
    refine (toOuterMeasure_uniformOfFintype_cond_le e₁ G_top₁ (fun θ₁ => ¬ G₁ θ₁)
      htop₁ hbot₁).trans (le_of_eq ?_)
    rw [← add_mul]
    congr 1
    have hsum_frac : (4 : ℝ≥0∞)⁻¹ + ((8 : ℝ≥0∞)⁻¹ + (8 : ℝ≥0∞)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
      have h8_ne : (8 : ℝ≥0∞) ≠ 0 := by norm_num
      have h8_top : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
      have h4_ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
      have h4_top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
      have h2_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      apply ENNReal.mul_right_inj h8_ne h8_top |>.mp
      rw [mul_add, mul_add, ENNReal.mul_inv_cancel h8_ne h8_top,
        show (8 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ = 2 * ((4 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹) by ring,
        ENNReal.mul_inv_cancel h4_ne h4_top,
        show (8 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 4 * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) by ring,
        ENNReal.mul_inv_cancel h2_ne h2_top]
      norm_num
    exact hsum_frac
  have hfp_cond : ∀ θ₁ : BktSeed c U n_max, G₁ θ₁ →
      (PMF.uniformOfFintype (FpSeed c U n_max)).toOuterMeasure
        {θ₂ | ¬ GoodSeedOnWindow c U n_max ops (θ₁, θ₂)} ≤
        (2 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
    intro θ₁ hG₁
    have hbal_start : BalancedBuckets U n_max (bktHash c U n_max θ₁) (Dictionary.dom s_start) :=
      hG₁.1 s_start (self_mem_stateSeq _ _)
    have hbkt_6L12 : ∀ b : Fin (numBucketsWhp n_max),
        #(W_keys.filter fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val = b.val) ≤
          6 * L ^ 12 :=
      card_union_bucket_le_of_balanced hth hdom_start hW_ins_n hbal_start hG₁.2
    let e₂ : FpSeed c U n_max ≃
        (Fin (2 ^ (w0Whp U - 1)) ×
          DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)) ×
        DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) :=
      { toFun := fun θ => ((θ.1, θ.2.1), θ.2.2)
        invFun := fun q => (q.1.1, (q.1.2, q.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    let G_top₂ (p : Fin (2 ^ (w0Whp U - 1)) ×
        DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)) : Prop :=
      GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (kIndepWhp c n_max) W_keys p.1 p.2
    have htop₂ : (PMF.uniformOfFintype _).toOuterMeasure {p | ¬ G_top₂ p} ≤
        (4 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
      rw [← toOuterMeasure_uniformOfFintype_fst e₂ (fun p => ¬ G_top₂ p)]
      exact toOuterMeasure_not_goodTop_seed_le hth W_keys hW_keys_2n
    have hbot₂ : ∀ p, G_top₂ p →
        (PMF.uniformOfFintype
          (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))).toOuterMeasure
          {T₂ | ¬ GoodSeedOnWindow c U n_max ops (θ₁, e₂.symm (p, T₂))} ≤
          ((8 : ℝ≥0∞)⁻¹ + (8 : ℝ≥0∞)⁻¹) * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
      intro p hp
      have hinj_rkey : Set.InjOn (fpReducedKey c U n_max (p.1, p.2, Classical.arbitrary _))
          (W_keys : Set (Fin U)) := by
        intro u₁ hu₁ u₂ hu₂ heq
        exact hp.1 hu₁ hu₂ (Fin.ext heq)
      have hsub_or₂ :
          {T₂ | ¬ GoodSeedOnWindow c U n_max ops (θ₁, e₂.symm (p, T₂))} ⊆
          {T₂ | ¬ ∀ b : Fin (numBucketsWhp n_max),
            ∃ salt : Fin (sMaxWhp c n_max),
              Set.InjOn (fpHash c U n_max (p.1, p.2, T₂) salt)
                (W_keys.filter (fun u =>
                  feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val = b.val) :
                  Set (Fin U))} ∪
          {T₂ | 2 * rIndepWhp c n_max ≤
            #(W_ins.filter fun u =>
              ∃ v ∈ W_keys.filter (fun w =>
                feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) w.val =
                  feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val),
                u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
                  fpHash c U n_max (p.1, p.2, T₂) salt u =
                    fpHash c U n_max (p.1, p.2, T₂) salt v)} := by
        intro T₂ hT₂
        change ¬ GoodSeedOnWindow c U n_max ops (θ₁, (p.1, p.2, T₂)) at hT₂
        have hinj_T₂ : Set.InjOn (fpReducedKey c U n_max (p.1, p.2, T₂))
            (W_keys : Set (Fin U)) := hinj_rkey
        by_cases hc4 : ∀ b : Fin (numBucketsWhp n_max),
            ∃ salt : Fin (sMaxWhp c n_max),
              Set.InjOn (fpHash c U n_max (p.1, p.2, T₂) salt)
                (W_keys.filter (fun u =>
                  feistelBucket (bWhp n_max) (bktHash c U n_max θ₁) u.val = b.val) :
                  Set (Fin U))
        · right
          rw [Set.mem_ofPred_eq]
          by_contra hlt
          exact hT₂ ⟨hinj_T₂, hG₁.1, hG₁.2, hc4, Nat.lt_of_not_ge hlt⟩
        · exact Or.inl hc4
      refine (MeasureTheory.measure_mono hsub_or₂).trans ?_
      refine (MeasureTheory.measure_union_le _ _).trans ?_
      rw [add_mul]
      exact add_le_add
        (toOuterMeasure_not_salt_inj_bot_le hth _ W_keys hbkt_6L12 hp)
        (toOuterMeasure_salt_coll_count_bot_le hth _ W_ins W_keys subset_union_right
          hW_ins_3 hbkt_6L12 hp)
    refine (toOuterMeasure_uniformOfFintype_cond_le e₂ G_top₂
      (fun θ₂ => ¬ GoodSeedOnWindow c U n_max ops (θ₁, θ₂)) htop₂ hbot₂).trans (le_of_eq ?_)
    rw [← add_mul]
    congr 1
    have hsum_frac : (4 : ℝ≥0∞)⁻¹ + ((8 : ℝ≥0∞)⁻¹ + (8 : ℝ≥0∞)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
      have h8_ne : (8 : ℝ≥0∞) ≠ 0 := by norm_num
      have h8_top : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
      have h4_ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
      have h4_top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
      have h2_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      apply ENNReal.mul_right_inj h8_ne h8_top |>.mp
      rw [mul_add, mul_add, ENNReal.mul_inv_cancel h8_ne h8_top,
        show (8 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ = 2 * ((4 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹) by ring,
        ENNReal.mul_inv_cancel h4_ne h4_top,
        show (8 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 4 * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) by ring,
        ENNReal.mul_inv_cancel h2_ne h2_top]
      norm_num
    exact hsum_frac
  refine (toOuterMeasure_uniformOfFintype_cond_le (Equiv.refl _) G₁
    (fun θ => ¬ GoodSeedOnWindow c U n_max ops θ) hbkt_bad hfp_cond).trans (le_of_eq ?_)
  rw [← add_mul]
  have h2_half : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
    have h2_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    apply ENNReal.mul_right_inj h2_ne h2_top |>.mp
    rw [mul_add, ENNReal.mul_inv_cancel h2_ne h2_top, mul_one]
    norm_num
  rw [h2_half, one_mul]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end


