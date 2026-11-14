/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArrayProg
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.Concentration
public import CslibFrontier.Probability.KWiseIndependent.VarianceTail

/-!
# Checked Tests for `VarianceTail`, `BitPackedArrayProg`, and `BitPackedDoubleTabulation`

Exercises the Milestone 2 high-probability dictionary foundation modules:
1. **`Cslib.Probability.IsKWiseIndependentHash` (`VarianceTail`)**:
   - Concrete non-trivial (`< 1`) instantiations of `expect_sum_pow_le_of_sq_le`,
     `dens_filter_le_abs_sum_of_sq_le`, `dens_filter_le_abs_sum_sub_expect_of_Icc` (backed by
     `Cslib.Probability.abs_expect_sub_expect_pow_le`), `dens_forall_salt_exists_collision_le`,
     `dens_card_local_salt_colliding_ge_le`, and `dens_card_salt_colliding_ge_le` over exact
     `k`-wise independent hash families (`isKWiseIndependentHash_id`).
2. **`Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray` (`BitPackedArrayProg`)**:
   - Concrete `writePackedProg` → `readPackedProg` round-trip and `ValidHistory` / `memoryCost`
     verification.
3. **`Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation`**:
   - Concrete witnesses of `HashEnv` and `EvalGenPre` (including at `s.frontier = 0`, verifying
     that `EvalGenPre` imposes no frontier side condition for `SubroutineCode` callers).
   - End-to-end instantiation of `realizes_evalGen.code_spec`, `evalProg_spec`,
     `validHistory_evalProg`, `memoryCost_evalProg`, `innerLoop_invariant`, and `SeedRep.congr_on`
     yielding Word-RAM `ExecWithin` with `¬ReadsWidth` whose output register equals `evalSalted`.
   - Non-trivial (`< 1`) instantiation of `toOuterMeasure_not_goodTop_le` and conditional
     `k`-wise independence `isKWiseIndependentHash_evalSalted_of_goodTop`.
-/

@[expose] public section

namespace CslibFrontierTests.BitPackedDoubleTabulation

open Cslib Cslib.Probability Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
open Finset Fintype
open scoped BigOperators ENNReal

/-! ## 1. `VarianceTail`: concrete non-trivial moment and multi-salt collision bounds -/

/-- Indicator score `g _ y = 1` iff `y = 0` on `Fin 8`, with mean `1 / 8` and `[0, 1]` range. -/
def zeroScore (_x : Fin 4) (y : Fin 8) : ℝ :=
  if y.val = 0 then 1 else 0

theorem zeroScore_mem_Icc (x : Fin 4) (y : Fin 8) : zeroScore x y ∈ Set.Icc 0 1 := by
  dsimp only [zeroScore]
  split_ifs <;> norm_num

theorem expect_zeroScore (x : Fin 4) : (𝔼 y : Fin 8, zeroScore x y) = (1 : ℝ) / 8 := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum : (∑ y ∈ (univ : Finset (Fin 8)), zeroScore x y) = 1 := by
    rw [Fin.sum_univ_eight]
    dsimp only [zeroScore]
    norm_num
  rw [hsum]
  simp only [card_univ, Fintype.card_fin]
  norm_num

open Classical in
/-- Non-trivial (`≤ 1 / 4 < 1`) instantiation of `dens_filter_le_abs_sum_sub_expect_of_Icc`
at `m = 1` (`2`-wise independence) and threshold `a = 2`, where `max (∑ 𝔼 g, 1) = max (1/2, 1) = 1`
gives bound `1 * (1 ^ 2 * 1 / 2 ^ 2) ^ 1 = 1 / 4`. -/
theorem varianceTail_Icc_nontrivial :
    let h := (id : (Fin 4 → Fin 8) → Fin 4 → Fin 8)
    (dens {i | (2 : ℝ) ≤ |∑ x ∈ (univ : Finset (Fin 4)),
        (zeroScore x (h i x) - 𝔼 y, zeroScore x y)|} : ℝ) ≤ (1 : ℝ) / 4 := by
  intro h
  have hh : IsKWiseIndependentHash (2 * 1) h := isKWiseIndependentHash_id 2
  have hbound := hh.dens_filter_le_abs_sum_sub_expect_of_Icc (m := 1) le_rfl univ zeroScore
    (fun x _ y => zeroScore_mem_Icc x y) (a := 2) (by norm_num)
  have hsum_exp : (∑ x ∈ (univ : Finset (Fin 4)), 𝔼 y, zeroScore x y) = (1 : ℝ) / 2 := by
    simp only [expect_zeroScore, sum_const, card_univ, Fintype.card_fin]
    norm_num
  refine hbound.trans_eq ?_
  rw [hsum_exp]
  norm_num

/-- Direct check of exposed `Cslib.Probability.abs_expect_sub_expect_pow_le` for `c = 3`. -/
theorem abs_expect_sub_expect_cube_zeroScore :
    |𝔼 y : Fin 8, (zeroScore 0 y - 𝔼 y', zeroScore 0 y') ^ 3| ≤ (1 : ℝ) / 8 :=
  (abs_expect_sub_expect_pow_le (zeroScore 0) (zeroScore_mem_Icc 0) (by decide : 2 ≤ 3)).trans_eq
    (expect_zeroScore 0)

/-- Non-trivial (`≤ 1 / 4 < 1`) instantiation of `dens_forall_salt_exists_collision_le` across
`s_max = 2` salts on a 2-element bucket `S_b ⊆ Fin 2` into `Fin 8` (`(2 ^ 2 / 8) ^ 2 = 1 / 4`),
parameterized over a `4`-wise independent family and instantiated at `isKWiseIndependentHash_id`. -/
theorem multiSalt_collision_of_kWise {ι : Type} [Fintype ι]
    {H : ι → Fin 2 × Fin 2 → Fin 8} (hh : IsKWiseIndependentHash 4 H) :
    let S_b : Finset (Fin 2) := {0, 1}
    (dens ({i | ∀ s : Fin 2, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
      Finset ι) : ℝ) ≤ (1 : ℝ) / 4 := by
  intro S_b
  have hh' : IsKWiseIndependentHash (2 * 2) H := hh
  have hbound : (dens ({i | ∀ s : Fin 2, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
      Finset ι) : ℝ) ≤ ((#S_b : ℝ) ^ 2 / Fintype.card (Fin 8)) ^ 2 := by
    convert hh'.dens_forall_salt_exists_collision_le S_b using 3
    ext i
    simp
  have hcard : #S_b = 2 := by decide
  refine hbound.trans_eq ?_
  rw [hcard, Fintype.card_fin]
  norm_num

theorem multiSalt_collision_nontrivial :
    let H := (id : (Fin 2 × Fin 2 → Fin 8) → Fin 2 × Fin 2 → Fin 8)
    let S_b : Finset (Fin 2) := {0, 1}
    (dens ({i | ∀ s : Fin 2, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
      Finset (Fin 2 × Fin 2 → Fin 8)) : ℝ) ≤ (1 : ℝ) / 4 :=
  multiSalt_collision_of_kWise (isKWiseIndependentHash_id 4)

/-- Non-trivial (`≤ 9 / 16 < 1`) instantiation of `dens_card_salt_colliding_ge_le` at `r = 2`
(`4`-wise independence), `#Q_set = 2`, `#W_set = 3`, `s_max = 2`, `|Y| = 16`
(`((2 * 3 * 2) / 16) ^ 2 = (3 / 4) ^ 2 = 9 / 16 < 1`), plus concrete instantiation via
`isKWiseIndependentHash_id 4`. -/
theorem batch_salt_colliding_of_kWise {ι : Type} [Fintype ι]
    {H : ι → Fin 2 × Fin 4 → Fin 16} (hh : IsKWiseIndependentHash 4 H) :
    let Q_set : Finset (Fin 4) := {0, 1}
    let W_set : Finset (Fin 4) := {0, 1, 2}
    (dens ({i | 2 * 2 ≤ #(Q_set.filter fun u =>
      ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin 2, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (9 : ℝ) / 16 := by
  intro Q_set W_set
  have hh' : IsKWiseIndependentHash (2 * 2) H := hh
  have hbound : (dens ({i | 2 * 2 ≤ #(Q_set.filter fun u =>
      ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin 2, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (((#Q_set * #W_set * 2 : ℕ) : ℝ) / Fintype.card (Fin 16)) ^ 2 := by
    convert hh'.dens_card_salt_colliding_ge_le Q_set W_set using 3
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    congr! 2
    ext u
    simp
  have hQ : #Q_set = 2 := by decide
  have hW : #W_set = 3 := by decide
  refine hbound.trans_eq ?_
  rw [hQ, hW, Fintype.card_fin]
  norm_num

/-- Concrete witness of `batch_salt_colliding_of_kWise` using `isKWiseIndependentHash_id 4`. -/
theorem batch_salt_colliding_nontrivial :
    let H := (id : (Fin 2 × Fin 4 → Fin 16) → Fin 2 × Fin 4 → Fin 16)
    let Q_set : Finset (Fin 4) := {0, 1}
    let W_set : Finset (Fin 4) := {0, 1, 2}
    (dens ({i | 2 * 2 ≤ #(Q_set.filter fun u =>
      ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin 2, H i (s, u) = H i (s, v))} :
      Finset (Fin 2 × Fin 4 → Fin 16)) : ℝ) ≤ (9 : ℝ) / 16 :=
  batch_salt_colliding_of_kWise (isKWiseIndependentHash_id 4)

/-! ## 2. `BitPackedArrayProg`: `writePackedProg` → `readPackedProg` round-trip and `Realizes` -/

/-- Writing two straddling 5-bit entries into an 8-bit Word-RAM packed array and reading both back
recovers the written values while charging `4 + 4 + 2 + 2 = 12` memory operations. -/
theorem bitPackedArrayProg_roundTrip :
    let prog : Memory.Prog (ℕ × ℕ) := do
      writePackedProg 4 2 5 8 1 29
      writePackedProg 4 2 5 8 2 13
      let v₁ ← readPackedProg 4 2 5 8 1
      let v₂ ← readPackedProg 4 2 5 8 2
      pure (v₁, v₂)
    let s₀ : Memory.State := { mem := fun _ => 0, frontier := 16 }
    (Memory.spec 8).ValidHistory s₀ ((Memory.spec 8).clientHistory s₀ prog) ∧
    (Memory.spec 0).clientResult s₀ prog = (29, 13) ∧
    memoryCost prog s₀ = 12 := by
  decide

/-! ## 3. `BitPackedDoubleTabulation`: unified non-vacuous witness across all endpoints -/

/-- Unified parameter tuple `(w = 64, U = 16, w₀ = 4, R = 4, c_tab = 1, q = 2, d = 8,
b_char = 25, M_out = 4, k = 2, s_max = 2, base = 8)` satisfying `HashEnv` and `EvalGenPre`
even when `s.frontier = 0` (verifying no frontier precondition in `EvalGenPre`). -/
def sampleHp : HashParams :=
  mkHashParams 64 4 4 1 8 25 4

theorem sampleHp_space_fits : Fits 64 (8 + space 64 1 8 25 4) := by
  dsimp only [Fits, space, topWords, botWords, topEntries, botEntries, packedWords]
  norm_num

theorem sampleHp_hashEnv : HashEnv 64 sampleHp 8 := by
  refine ⟨4, 4, 1, 8, 25, 4, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, by decide, by decide, sampleHp_space_fits, rfl⟩
  · dsimp only [topEntries]; norm_num
  · dsimp only [botEntries]; norm_num

/-- Regression check for `EvalGenPre`: holds at `s.frontier = 0` (`0 < base = 8`), so callers whose
`SubroutineCode` bridge runs with `frontier = 0` need not duplicate `evalGenProg`. -/
theorem sampleHp_evalGenPre_frontier_zero :
    EvalGenPre 64 (sampleHp, ((8, 1), 11)) { mem := fun _ => 3, frontier := 0 } :=
  ⟨sampleHp_hashEnv, by decide, by dsimp only [sampleHp, hpPowB_mk]; norm_num, by decide⟩

/-- Non-trivial (`≤ 1 / 4 < 1`) failure bound on `¬ GoodTop` together with conditional `2`-wise
independence on `Fin 2 × W_set` for the exact same `(U = 16, w₀ = 4, R = 4, c_tab = 1, q = 2,
d = 8, b_char = 25, M_out = 4, k = 2, s_max = 2)` parameters as `sampleHp_hashEnv`. -/
theorem sample_goodTop_and_kWise :
    let W_set : Finset (Fin 16) := {0, 1}
    (PMF.uniformOfFintype (Seed 4 1 8 25 4)).toOuterMeasure
      {θ | ¬ GoodTop 16 4 4 1 8 25 2 W_set θ.1 θ.top} ≤ (1 : ℝ≥0∞) / 4 ∧
    ∀ θ : Seed 4 1 8 25 4, GoodTop 16 4 4 1 8 25 2 W_set θ.1 θ.top →
      IsKWiseIndependentHash 2
        (fun T₂ : DoubleTabBotSeed 8 25 4 => fun su : Fin 2 × W_set =>
          evalSalted 16 4 4 1 8 25 4 2 (θ.1, θ.top, T₂) (su.1, su.2.1)) := by
  intro W_set
  refine ⟨?_, fun θ hgood => isKWiseIndependentHash_evalSalted_of_goodTop
    (by norm_num : 2 ≤ 2 ^ 25) (by decide : min 4 4 ≤ 1 * 25) hgood⟩
  have hcode : 2 * doubleTabCodeBound (1 + 1) 8 2 2 ≤ 2 ^ ((2 - 1) * 25) := by
    dsimp only [doubleTabCodeBound]
    norm_num
  have hle := toOuterMeasure_not_goodTop_le (R := 4) (M_out := 4)
    (by decide : 0 < 4) (by decide : 16 ≤ 2 ^ 4) (by decide : 1 ≤ 2)
    (by decide : 8 = 2 * 2 * (1 + 1)) hcode W_set
  have hW : #W_set = 2 := by decide
  have hcb : doubleTabCodeBound (1 + 1) 8 2 2 = 2 ^ 23 := by
    dsimp only [doubleTabCodeBound]
    norm_num
  refine hle.trans ?_
  rw [hW, hcb]
  have ht1 : (((2 * (2 - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 4) = (1 : ℝ≥0∞) / 8 := by
    rw [show (((2 * (2 - 1) : ℕ) : ℝ≥0∞)) = 2 * 1 by norm_num,
      show (2 : ℝ≥0∞) ^ 4 = 2 * 8 by norm_num]
    exact ENNReal.mul_div_mul_left 1 8 (by norm_num) (by norm_num)
  have ht2 : (2 * ((2 ^ 23 : ℕ) : ℝ≥0∞) ^ 2) / ((2 : ℝ≥0∞) ^ ((2 - 1) * 25)) ^ 2 =
      (1 : ℝ≥0∞) / 8 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have hnum : (2 * ((2 : ℝ≥0∞) ^ 23) ^ 2) = (2 : ℝ≥0∞) ^ 47 * 1 := by ring
    have hden : ((2 : ℝ≥0∞) ^ ((2 - 1) * 25)) ^ 2 = (2 : ℝ≥0∞) ^ 47 * 8 := by
      change ((2 : ℝ≥0∞) ^ 25) ^ 2 = _
      rw [← pow_mul]
      change (2 : ℝ≥0∞) ^ (47 + 3) = _
      rw [pow_add, show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num]
    rw [hnum, hden]
    exact ENNReal.mul_div_mul_left 1 8 (by positivity) (ENNReal.pow_ne_top (by norm_num))
  rw [ht1, ht2, ← ENNReal.add_div, show (1 : ℝ≥0∞) + 1 = 2 * 1 by ring,
    show (8 : ℝ≥0∞) = 2 * 4 by norm_num, ENNReal.mul_div_mul_left 1 4 (by norm_num) (by norm_num)]

private theorem fits_encode_nat {w n : ℕ} (hn : Fits w n) :
    ∀ i : Fin (WordEncoding.width ℕ), Fits w (WordEncoding.encode n i) := fun _ => hn

private theorem fits_encode_prod {α β : Type} [WordEncoding α] [WordEncoding β] {w : ℕ}
    {a : α} {b : β}
    (ha : ∀ i, Fits w (WordEncoding.encode a i))
    (hb : ∀ j, Fits w (WordEncoding.encode b j)) :
    ∀ k, Fits w (WordEncoding.encode (a, b) k) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · change Fits w (Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.castAdd _ i))
    rw [Fin.append_left]
    exact ha i
  · change Fits w (Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.natAdd _ j))
    rw [Fin.append_right]
    exact hb j

/-- End-to-end Word-RAM execution test via `realizes_evalGen.code_spec`, `evalProg_spec`,
`validHistory_evalProg`, `memoryCost_evalProg`, `innerLoop_invariant`, and `SeedRep.congr_on`:
the compiled `¬ReadsWidth` code executes fault-free within its factor budget, preserves memory and
frontier, and writes `(evalSalted 16 4 4 1 8 25 4 2 θ (salt, u)).val` to its output register. -/
theorem realizes_evalGen_endToEnd (θ : Seed 4 1 8 25 4) (mem : ℕ → ℕ)
    (hmem_bdd : ∀ a, Fits 64 (mem a))
    (hrep : SeedRep 8 64 4 1 8 25 4 θ mem)
    (salt : Fin 2) (u : Fin 16) :
    let mem' := Function.update mem 0 99
    let k_in := WordEncoding.width (HashParams × ((ℕ × ℕ) × ℕ))
    let r := (1 + k_in) + (1 + realizes_evalGen.scratchSize + 1)
    let frontier : Fin r := ⟨0, by omega⟩
    let src : Fin k_in → Fin r := fun i => ⟨1 + i.val, by omega⟩
    let tmp : Fin (1 + realizes_evalGen.scratchSize + 1) → Fin r :=
      fun j => ⟨(1 + k_in) + j.val, by omega⟩
    let code := realizes_evalGen.code frontier src tmp
    let d_arg : HashParams × ((ℕ × ℕ) × ℕ) := (sampleHp, ((8, salt.val), u.val))
    let enc := WordEncoding.encode d_arg
    let x : Data r :=
      { regs := fun i =>
          if i.val = 0 then 8 + space 64 1 8 25 4
          else if h : i.val - 1 < k_in then enc ⟨i.val - 1, h⟩
          else 0
        mem := mem' }
    SeedRep 8 64 4 1 8 25 4 θ mem' ∧
    (∀ m, m ≤ 1 →
      iterationSafe innerStepGenProg InnerStepGenPre 64 (sampleHp, (8, 0)) m ((0, 0), 0)
        (memoryState frontier x)) ∧
    ¬code.ReadsWidth ∧
    memoryCost (evalProg 64 4 4 1 8 25 4 ((8, salt.val), u.val)) (memoryState frontier x) = 49 ∧
    ∃ y, ExecWithin 64 code x y (realizes_evalGen.factor * 50) ∧
      memoryState frontier y = memoryState frontier x ∧
      y.regs (tmp ⟨0, by omega⟩) = (evalSalted 16 4 4 1 8 25 4 2 θ (salt, u)).val := by
  intro mem' k_in r frontier src tmp code d_arg enc x
  have hrep' : SeedRep 8 64 4 1 8 25 4 θ mem' :=
    hrep.congr_on (by decide : 0 < 64) fun a ha _ => by
      dsimp only [mem']
      exact Function.update_of_ne (by omega) 99 mem
  have hinv : ∀ m, m ≤ 1 →
      iterationSafe innerStepGenProg InnerStepGenPre 64 (sampleHp, (8, 0)) m ((0, 0), 0)
        (memoryState frontier x) := fun m hm =>
    (innerLoop_invariant sampleHp_hashEnv (by decide : 0 < hpD sampleHp) m 0 0 0
      (by dsimp only [sampleHp, hpCTab_mk]; omega)
      (by dsimp only [sampleHp, hpPowB_mk]; positivity)).1
  have hspec := realizes_evalGen.code_spec frontier src tmp
    (fun a b hab => Fin.ext (by
      have := congrArg Fin.val hab; dsimp only [tmp] at this; omega))
    (fun i j h => by
      have := congrArg Fin.val h; dsimp only [src, tmp] at this; omega)
    (fun j h => by
      have := congrArg Fin.val h; dsimp only [tmp, frontier] at this; omega)
    (fun i h => by
      have := congrArg Fin.val h; dsimp only [src, frontier] at this; omega)
  have hcost :
      memoryCost (evalProg 64 4 4 1 8 25 4 ((8, salt.val), u.val)) (memoryState frontier x) = 49 :=
    memoryCost_evalProg 64 4 4 1 8 25 4 ((8, salt.val), u.val) (memoryState frontier x)
  refine ⟨hrep', hinv, hspec.1, hcost, ?_⟩
  have henc_fits : ∀ j : Fin k_in, Fits 64 (enc j) :=
    fits_encode_prod (fits_mkHashParams sampleHp_hashEnv)
      (fits_encode_prod
        (fits_encode_prod (fits_encode_nat (by decide : Fits 64 8))
          (fits_encode_nat (by change salt.val < 2 ^ 64; have := salt.isLt; omega)))
        (fits_encode_nat (by change u.val < 2 ^ 64; have := u.isLt; omega)))
  have hx_bdd : x.Bounded 64 := by
    refine ⟨fun i => ?_, fun a => ?_⟩
    · dsimp only [x]
      split_ifs with h0 h19
      · exact sampleHp_space_fits
      · exact henc_fits ⟨i.val - 1, h19⟩
      · decide
    · dsimp only [x, mem']
      by_cases ha0 : a = 0
      · subst ha0; rw [Function.update_self]; decide
      · rw [Function.update_of_ne ha0]; exact hmem_bdd a
  have hsrc_eq : x.regs ∘ src = enc := by
    funext i
    have hi0 : 1 + i.val ≠ 0 := by omega
    have hi_lt : (1 + i.val) - 1 < k_in := by omega
    dsimp only [Function.comp_apply, x, src]
    simp only [hi0, hi_lt, ↓reduceIte, ↓reduceDIte]
    exact congrArg enc (Fin.ext (by dsimp only; omega))
  have hpre : EvalGenPre 64 d_arg (memoryState frontier x) := by
    refine ⟨sampleHp_hashEnv, ?_, ?_, ?_⟩
    · change mem' 8 ≤ hpMaskM sampleHp
      rw [hrep'.1]
      have := θ.1.isLt
      dsimp only [sampleHp, hpMaskM_mk]
      omega
    · dsimp only [sampleHp, hpPowB_mk]
      have := salt.isLt
      omega
    · dsimp only [sampleHp, hpMaskM_mk]
      have := u.isLt
      omega
  have hfr_le : 8 + space 64 1 8 25 4 ≤ (memoryState frontier x).frontier := by
    change 8 + space 64 1 8 25 4 ≤ x.regs frontier
    dsimp only [x, frontier]
    simp
  have hv := validHistory_evalProg hpre hfr_le
  obtain ⟨y, hex, hst, hout, -⟩ := hspec.2 64 d_arg x hx_bdd hsrc_eq hpre hv
  have heval := evalProg_spec (U := 16) (R := 4) (s_max := 2) (s := memoryState frontier x)
    (by decide : 0 < 4) (by norm_num : 2 ≤ 2 ^ 25) hrep' salt u
  have hcost_gen : memoryCost (evalGenProg d_arg) (memoryState frontier x) = 49 := hcost
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [hcost_gen] at hex
    exact hex
  · rw [hst, clientState_width]
    exact heval.2
  · have hout0 := hout ⟨0, by decide⟩
    rw [clientResult_width] at hout0
    change y.regs (tmp ⟨0, _⟩) =
      (Memory.spec 0).clientResult (memoryState frontier x)
        (evalProg 64 4 4 1 8 25 4 ((8, salt.val), u.val)) at hout0
    exact hout0.trans heval.1

end CslibFrontierTests.BitPackedDoubleTabulation

end
