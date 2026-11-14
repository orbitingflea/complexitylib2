/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSmallCsrProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Implementations of `locState`, `permuteByTarget`, and `fastToCsr`

This module implements the overflow-free 2-bit `locState` accessors (`readLocStateGenProg`,
`writeLocStateGenProg`), the bucket-interval scanner `scanBucketLoopProg`, the in-place
cycle-following permutation `permuteByTargetProg` shared by `fastToCsr` and `csrToFast`, and the
`fastToCsrGenProg` transition from `FastMemRep` to `CsrMemRep`, all certified over `Basis.exact`
with zero local work via `realize` and `Realizes.iterate₀`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readLocStateGenProg`,
  `writeLocStateGenProg`: overflow-free 2-bit `offLocState` accessors avoiding `b * totalLoc`
  product overflow when `n_max` approaches `2 ^ w`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.permuteByTargetProg`,
  `fastToCsrGenProg`: parameter-free `Memory.Prog` implementations of in-place slot permutation and
  fallback CSR compaction.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_readLocStateGen`,
  `realizes_writeLocStateGen`, `realizes_permuteByTarget`, `realizes_fastToCsrGen`: parameter-free
  `Realizes .exact` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.permuteByTargetProg_spec`,
  `fastToCsrGenProg_spec`: exact memory refinement specifications preserving `SeedWhpMemRep` and
  framing memory outside `largeSpaceWhp`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Overflow-Free 2-Bit `offLocState` Accessors -/

section LocStateHelpers

@[simp]
private theorem clientResult_pure_zero {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pure x) = x := rfl

@[simp]
private theorem clientState_pure_zero {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (pure x) = s := rfl

private theorem clientResult_memRead (addr : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl

private theorem clientState_memRead (addr : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.read addr) = s := rfl

private theorem clientState_writePackedGen (base offset k w idx val : ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (writePackedGenProg ((((base, offset), (k, w)), idx), val)) =
      { mem := writePacked (base + offset) k w s.mem idx val,
        frontier := s.frontier } := rfl

private theorem clientResult_writePackedGen (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (writePackedGenProg ((((base, offset), (k, w)), idx), val)) = () := rfl

private theorem clientState_bind_rw {α β : Type} (p : Memory.Prog α) (k : α → Memory.Prog β)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (p >>= k) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) :=
  StateTransitionSpec.clientState_bind (D := Memory.spec 0) p k s

private theorem clientResult_bind_rw {α β : Type} (p : Memory.Prog α) (k : α → Memory.Prog β)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (p >>= k) =
      (Memory.spec 0).clientResult ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) :=
  StateTransitionSpec.clientResult_bind (D := Memory.spec 0) p k s

@[simp]
private theorem clientState_readPackedGen (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedGenProg d) = s := rfl

private theorem clientResult_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedGenProg (((base, offset), (k, w)), idx)) =
      readPacked (base + offset) k w s.mem idx :=
  clientResult_readPackedProg base offset k w idx s

private theorem two_mul_totalLoc_lt_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 * totalLocalCoordsWhp n_max < n_max := by
  have hM_ge := (large_bounds_lt_n_max hth).1
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h1024 : 1024 * (scaleWhp n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ hM_ge).trans hML12
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hL_pos : 1 ≤ (scaleWhp n_max) ^ 12 := Nat.one_le_pow 12 _ (scaleWhp_pos n_max)
  omega

/-- Compute `(wordOffset 2 w (b * totalLoc + loc), bitOffset 2 w (b * totalLoc + loc))` without
forming `b * totalLoc` directly (`d = ((totalLoc, w), (b, loc))`). -/
@[irreducible] def locStateOffsetProg (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let totalLoc ← pure d.1.1
  let w ← pure d.1.2
  let b ← pure d.2.1
  let loc ← pure d.2.2
  let two_v ← pure 2
  let T2 ← pure (two_v * totalLoc)
  let L2 ← pure (two_v * loc)
  let qb ← pure (b / w)
  let rb ← pure (b % w)
  let qT ← pure (T2 / w)
  let rT ← pure (T2 % w)
  let qL ← pure (L2 / w)
  let rL ← pure (L2 % w)
  let wqT ← pure (w * qT)
  let p1 ← pure (qb * wqT)
  let p2 ← pure (qb * rT)
  let p3 ← pure (rb * qT)
  let s1 ← pure (p1 + p2)
  let s2 ← pure (s1 + p3)
  let s3 ← pure (s2 + qL)
  let rb_rT ← pure (rb * rT)
  let remSum ← pure (rb_rT + rL)
  let remDiv ← pure (remSum / w)
  let wOff ← pure (s3 + remDiv)
  let bOff ← pure (remSum % w)
  pure (wOff, bOff)

private theorem locStateOffset_eq {totalLoc w b loc : ℕ} (hw : 0 < w) :
    let T2 := 2 * totalLoc
    let L2 := 2 * loc
    let qb := b / w
    let rb := b % w
    let qT := T2 / w
    let rT := T2 % w
    let qL := L2 / w
    let rL := L2 % w
    let s3 := qb * (w * qT) + qb * rT + rb * qT + qL
    let remSum := rb * rT + rL
    s3 + remSum / w = wordOffset 2 w (b * totalLoc + loc) ∧
    remSum % w = bitOffset 2 w (b * totalLoc + loc) := by
  intro T2 L2 qb rb qT rT qL rL s3 remSum
  have hb_eq : w * qb + rb = b := Nat.div_add_mod b w
  have hT_eq : w * qT + rT = T2 := Nat.div_add_mod T2 w
  have hL_eq : w * qL + rL = L2 := Nat.div_add_mod L2 w
  have h2idx : (b * totalLoc + loc) * 2 = remSum + s3 * w := by
    dsimp only [remSum, s3]
    calc (b * totalLoc + loc) * 2
        = b * T2 + L2 := by dsimp only [T2, L2]; ring
      _ = (w * qb + rb) * (w * qT + rT) + (w * qL + rL) := by rw [hb_eq, hT_eq, hL_eq]
      _ = (rb * rT + rL) + (qb * (w * qT) + qb * rT + rb * qT + qL) * w := by ring
  rw [wordOffset_eq_mul_div hw, bitOffset_eq_mul_mod, h2idx,
    Nat.add_mul_div_right _ _ hw, Nat.add_mul_mod_self_right]
  exact ⟨Nat.add_comm _ _, rfl⟩

/-- Precondition for `locStateOffsetProg`. -/
@[expose] def LocStateOffsetPre (w : ℕ) (d : (ℕ × ℕ) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  d.1.2 = w ∧ 3 ≤ w ∧ 2 * d.1.1 < 2 ^ w ∧ d.2.2 < d.1.1 ∧
  Fits w (wordOffset 2 w (d.2.1 * d.1.1 + d.2.2))

theorem realizes_locStateOffset :
    Realizes .exact locStateOffsetProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      LocStateOffsetPre
      (fun _ _ => 0) := by
  unfold locStateOffsetProg
  realize
  all_goals (
    rcases d with ⟨⟨totalLoc, w_in⟩, b, loc⟩
    try clear hmem
    dsimp only [LocStateOffsetPre] at h
    obtain ⟨hw_in, hw3, h2T, hloc_lt, hfit_wOff⟩ := h
    subst w_in
    have hw : 0 < w := by omega
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have h2_fit : Fits w 2 :=
      (by decide : 2 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
    have h2L : 2 * loc < 2 ^ w := by omega
    have hmod_b : b % w < w := Nat.mod_lt _ hw
    have hmod_T : (2 * totalLoc) % w < w := Nat.mod_lt _ hw
    have hmod_L : (2 * loc) % w < w := Nat.mod_lt _ hw
    have hrem_lt : (b % w) * ((2 * totalLoc) % w) + (2 * loc) % w < 2 ^ w := by
      have hrb : b % w ≤ w - 1 := by omega
      have hrT : (2 * totalLoc) % w ≤ w - 1 := by omega
      have hrL : (2 * loc) % w ≤ w - 1 := by omega
      have hmul : (b % w) * ((2 * totalLoc) % w) ≤ (w - 1) * (w - 1) := Nat.mul_le_mul hrb hrT
      have hsum : (w - 1) * (w - 1) + (w - 1) = (w - 1) * w := by
        cases w with
        | zero => omega
        | succ w' => simp only [Nat.add_sub_cancel]; ring
      exact (Nat.add_le_add hmul hrL).trans_lt (hsum ▸ pred_mul_self_lt_two_pow (by omega))
    obtain ⟨hwOff_eq, _⟩ := locStateOffset_eq (totalLoc := totalLoc) (b := b) (loc := loc) hw
    try dsimp only at *
    set t1 := b / w * (w * (2 * totalLoc / w))
    set t2 := b / w * (2 * totalLoc % w)
    set t3 := b % w * (2 * totalLoc / w)
    set t4 := 2 * loc / w
    set t5 := (b % w * (2 * totalLoc % w) + 2 * loc % w) / w
    have hfit_sum : t1 + t2 + t3 + t4 + t5 < 2 ^ w := hwOff_eq.symm ▸ hfit_wOff
    clear_value t1 t2 t3 t4 t5
    first
    | omega
    | exact h2T
    | exact h2L
    | exact (Nat.mul_div_le (2 * totalLoc) w).trans_lt h2T
    | exact hrem_lt
    | exact (Nat.le_add_right _ _).trans_lt hrem_lt
    | (change _ < 2 ^ w; omega)
  )

theorem locStateOffsetProg_spec {totalLoc w b loc : ℕ} (hw : 0 < w) (s : Memory.State) :
    let prog := locStateOffsetProg ((totalLoc, w), (b, loc))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (wordOffset 2 w (b * totalLoc + loc), bitOffset 2 w (b * totalLoc + loc)) ∧
    memoryCost prog s = 0 := by
  obtain ⟨hwOff, hbOff⟩ := locStateOffset_eq (totalLoc := totalLoc) (b := b) (loc := loc) hw
  unfold locStateOffsetProg
  simp only [pure_bind]
  refine ⟨rfl, Prod.ext hwOff hbOff, rfl⟩

/-- Precondition for `readLocStateGenProg` (`d = (((base, offLoc), (totalLoc, w)), (b, loc))`). -/
@[expose] def ReadLocStatePre (w : ℕ)
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  ∃ M,
    d.1.2.2 = w ∧ 3 ≤ w ∧ 2 * d.1.2.1 < 2 ^ w ∧
    d.2.1 < M ∧ d.2.2 < d.1.2.1 ∧
    Fits w (d.1.1.1 + d.1.1.2 + packedWords (M * d.1.2.1) 2 w)

/-- Read `readPacked (base + offLoc) 2 w s.mem (b * totalLoc + loc)` without overflowing `w` bits
(`d = (((base, offLoc), (totalLoc, w)), (b, loc))`). -/
@[irreducible] def readLocStateGenProg (d : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let wb_pair ← locStateOffsetProg (d.1.2, d.2)
  let wOff ← pure wb_pair.1
  let bOff ← pure wb_pair.2
  let base ← pure d.1.1.1
  let offLoc ← pure d.1.1.2
  let w ← pure d.1.2.2
  let one_v ← pure 1
  let two_v ← pure 2
  let wb ← pure (w - bOff)
  let k0 ← if wb < two_v then pure wb else pure two_v
  let k1 ← pure (two_v - k0)
  let baseOff ← pure (base + offLoc)
  let addr0 ← pure (baseOff + wOff)
  let addr1 ← pure (addr0 + one_v)
  let word0 ← Memory.read addr0
  let word1 ← Memory.read addr1
  let m0 ← pure ((one_v <<< k0) - one_v)
  let m1 ← pure ((one_v <<< k1) - one_v)
  let low ← pure ((word0 >>> bOff) &&& m0)
  let high ← pure (word1 &&& m1)
  let highSh ← pure (high <<< k0)
  pure (low ^^^ highSh)

private theorem highSh_fits {w v1 k0 : ℕ} (hw2 : 2 ≤ w) (hk0 : k0 ≤ 2) :
    Fits w ((v1 &&& ((1 <<< (2 - k0)) - 1)) <<< k0) := by
  change ((v1 &&& ((1 <<< (2 - k0)) - 1)) <<< k0) < 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_shiftLeft]
  have hm : v1 &&& (2 ^ (2 - k0) - 1) < 2 ^ (2 - k0) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  calc (v1 &&& (2 ^ (2 - k0) - 1)) * 2 ^ k0
      < 2 ^ (2 - k0) * 2 ^ k0 := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ = 2 ^ 2 := by rw [← Nat.pow_add, Nat.sub_add_cancel hk0]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw2

private theorem low_xor_highSh_fits {w v0 v1 bOff k0 : ℕ} (hw2 : 2 ≤ w) (hk0 : k0 ≤ 2) :
    Fits w (((v0 >>> bOff) &&& ((1 <<< k0) - 1)) ^^^
      ((v1 &&& ((1 <<< (2 - k0)) - 1)) <<< k0)) := by
  refine Nat.xor_lt_two_pow ?_ (highSh_fits hw2 hk0)
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
    ((Nat.pow_le_pow_right two_pos hk0).trans (Nat.pow_le_pow_right two_pos hw2))

theorem realizes_readLocStateGen :
    Realizes .exact readLocStateGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      ReadLocStatePre
      (fun _ _ => 0) := by
  unfold readLocStateGenProg
  have hlo := realizes_locStateOffset
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, offLoc⟩, totalLoc, w_in⟩, b, loc⟩
    dsimp only [ReadLocStatePre] at h
    obtain ⟨M, hw_in, hw3, h2T, hb_lt, hloc_lt, hfit_seg⟩ := h
    subst w_in
    have hw : 0 < w := by omega
    have hw2 : 2 ≤ w := by omega
    have hidx : b * totalLoc + loc < M * totalLoc := by
      calc b * totalLoc + loc < b * totalLoc + totalLoc := Nat.add_lt_add_left hloc_lt _
        _ = (b + 1) * totalLoc := by ring
        _ ≤ M * totalLoc := Nat.mul_le_mul_right _ hb_lt
    have hw_off_lt := wordOffset_add_one_lt_packedWords (k := 2) hw hidx
    have hb_off_lt : bitOffset 2 w (b * totalLoc + loc) < w := bitOffset_lt hw
    obtain ⟨hof_st, hof_res, _⟩ := locStateOffsetProg_spec (totalLoc := totalLoc) (w := w)
      (b := b) (loc := loc) hw s
    have h2_fit : Fits w 2 :=
      (by decide : 2 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
    have h1_fit : Fits w 1 := h2_fit.of_le (by decide)
    dsimp only [LocStateOffsetPre] at *
    try simp only [hof_st, hof_res, hcs_r] at *
    first
    | exact ⟨trivial, hw3, h2T, hloc_lt, hfit_seg.of_le (by omega)⟩
    | exact h1_fit
    | exact h2_fit
    | omega
    | exact hfit_seg.of_le (by omega)
    | (rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow)
    | (change 1 <<< _ < 2 ^ w; rw [Nat.one_shiftLeft]
       exact Nat.pow_lt_pow_right (by decide) (by omega))
    | (refine highSh_fits hw2 ?_; omega)
    | (refine low_xor_highSh_fits hw2 ?_; omega)
  )

theorem readLocStateGenProg_spec {c U V w n_max base b loc : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := readLocStateGenProg
      (((base, offLocState c U V w n_max), (totalLocalCoordsWhp n_max, w)), (b, loc))
    let idx := b * totalLocalCoordsWhp n_max + loc
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      readPacked (base + offLocState c U V w n_max) 2 w s.mem idx ∧
    memoryCost prog s = 2 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hidx : b * totalLocalCoordsWhp n_max + loc <
      numBucketsWhp n_max * totalLocalCoordsWhp n_max := by
    calc b * totalLocalCoordsWhp n_max + loc
        < b * totalLocalCoordsWhp n_max + totalLocalCoordsWhp n_max := Nat.add_lt_add_left hloc _
      _ = (b + 1) * totalLocalCoordsWhp n_max := by ring
      _ ≤ numBucketsWhp n_max * totalLocalCoordsWhp n_max := Nat.mul_le_mul_right _ hb
  have hw_lt := wordOffset_add_one_lt_packedWords (k := 2) hw hidx
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
  obtain ⟨hof_st, hof_res, hof_mc⟩ :=
    locStateOffsetProg_spec (totalLoc := totalLocalCoordsWhp n_max) (w := w)
      (b := b) (loc := loc) hw s
  let idx := b * totalLocalCoordsWhp n_max + loc
  have hk0_eq : (if w - bitOffset 2 w idx < 2 then w - bitOffset 2 w idx else 2) =
      lowWidth 2 w idx := by
    unfold lowWidth; split_ifs <;> omega
  have hvp_lo : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
      (locStateOffsetProg ((totalLocalCoordsWhp n_max, w), (b, loc))) := by
    unfold locStateOffsetProg; simp only [pure_bind]; exact validWhpProg_pure _
  dsimp only
  unfold readLocStateGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind_rw, hof_st, hof_res]
    simp only [pure_bind]; split_ifs <;> rfl
  · rw [clientResult_bind_rw, hof_st, hof_res]
    simp only [pure_bind]
    unfold readPacked highWidth
    dsimp only
    split_ifs with hlt
    · rw [clientResult_bind_rw, clientState_memRead, clientResult_memRead,
        clientResult_bind_rw, clientState_memRead, clientResult_memRead]
      simp only [clientResult_pure_zero]
      have hl : lowWidth 2 w (b * totalLocalCoordsWhp n_max + loc) =
          w - bitOffset 2 w (b * totalLocalCoordsWhp n_max + loc) := by
        change lowWidth 2 w idx = w - bitOffset 2 w idx
        rw [← hk0_eq, ite_eq_left hlt]
      simp only [hl, Nat.shiftRight_zero, Nat.one_shiftLeft]
    · rw [clientResult_bind_rw, clientState_memRead, clientResult_memRead,
        clientResult_bind_rw, clientState_memRead, clientResult_memRead]
      simp only [clientResult_pure_zero]
      have hl : lowWidth 2 w (b * totalLocalCoordsWhp n_max + loc) = 2 := by
        change lowWidth 2 w idx = 2
        rw [← hk0_eq, ite_eq_right hlt]
      simp only [hl, Nat.shiftRight_zero, Nat.one_shiftLeft]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hof_st, hof_res, hof_mc]
    split_ifs <;> rfl
  · refine validWhpProg_bind hvp_lo ?_
    rw [hof_st, hof_res]
    simp only [pure_bind]
    split_ifs <;>
      (refine validWhpProg_bind (validWhpProg_read (by omega)) ?_
       exact validWhpProg_bind (validWhpProg_read (by omega)) (validWhpProg_pure _))

/-- Precondition for `writeLocStateGenProg`
(`d = ((((base, offLoc), (totalLoc, w)), (b, loc)), val)`). -/
@[expose] def WriteLocStatePre (w : ℕ)
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  ReadLocStatePre w d.1 _s

/-- Write `val` (`< 4`) into `offLocState` at `b * totalLoc + loc` without overflowing `w` bits
(`d = ((((base, offLoc), (totalLoc, w)), (b, loc)), val)`). -/
@[irreducible] def writeLocStateGenProg
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) : Memory.Prog Unit := do
  let wb_pair ← locStateOffsetProg (d.1.1.2, d.1.2)
  let wOff ← pure wb_pair.1
  let bOff ← pure wb_pair.2
  let base ← pure d.1.1.1.1
  let offLoc ← pure d.1.1.1.2
  let w ← pure d.1.1.2.2
  let val ← pure d.2
  let one_v ← pure 1
  let two_v ← pure 2
  let wb ← pure (w - bOff)
  let k0 ← if wb < two_v then pure wb else pure two_v
  let k1 ← pure (two_v - k0)
  let baseOff ← pure (base + offLoc)
  let addr0 ← pure (baseOff + wOff)
  let addr1 ← pure (addr0 + one_v)
  let m0 ← pure ((one_v <<< k0) - one_v)
  let m1 ← pure ((one_v <<< k1) - one_v)
  let word0 ← Memory.read addr0
  let old0 ← pure ((word0 >>> bOff) &&& m0)
  let val0 ← pure (val &&& m0)
  let diff0 ← pure ((old0 ^^^ val0) <<< bOff)
  Memory.write addr0 (word0 ^^^ diff0)
  let word1 ← Memory.read addr1
  let old1 ← pure (word1 &&& m1)
  let val1 ← pure ((val >>> k0) &&& m1)
  let diff1 ← pure (old1 ^^^ val1)
  Memory.write addr1 (word1 ^^^ diff1)

private theorem writeLoc_diff0_fits {w v0 val bOff k0 : ℕ} (hbw : bOff + k0 ≤ w) :
    Fits w ((((v0 >>> bOff) &&& ((1 <<< k0) - 1)) ^^^ (val &&& ((1 <<< k0) - 1))) <<< bOff) := by
  change ((((v0 >>> bOff) &&& ((1 <<< k0) - 1)) ^^^ (val &&& ((1 <<< k0) - 1))) <<< bOff) < 2 ^ w
  have hxor : (((v0 >>> bOff) &&& ((1 <<< k0) - 1)) ^^^ (val &&& ((1 <<< k0) - 1))) < 2 ^ k0 := by
    rw [Nat.one_shiftLeft]
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
      (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.shiftLeft_eq]
  calc _ < 2 ^ k0 * 2 ^ bOff := Nat.mul_lt_mul_of_pos_right hxor (Nat.two_pow_pos _)
    _ = 2 ^ (bOff + k0) := by rw [← Nat.pow_add, Nat.add_comm]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hbw

private theorem writeLoc_diff1_fits {w v1 val k0 : ℕ} (hk1 : 2 - k0 ≤ w) :
    Fits w ((v1 &&& ((1 <<< (2 - k0)) - 1)) ^^^ ((val >>> k0) &&& ((1 <<< (2 - k0)) - 1))) := by
  change ((v1 &&& ((1 <<< (2 - k0)) - 1)) ^^^ ((val >>> k0) &&& ((1 <<< (2 - k0)) - 1))) < 2 ^ w
  rw [Nat.one_shiftLeft]
  refine (Nat.xor_lt_two_pow ?_ ?_).trans_le (Nat.pow_le_pow_right two_pos hk1) <;>
    (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))

theorem realizes_writeLocStateGen :
    Realizes .exact writeLocStateGenProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      WriteLocStatePre
      (fun _ _ => 0) := by
  unfold writeLocStateGenProg
  have hlo := realizes_locStateOffset
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨base, offLoc⟩, totalLoc, w_in⟩, b, loc⟩, val⟩
    dsimp only [WriteLocStatePre, ReadLocStatePre] at h
    obtain ⟨M, hw_in, hw3, h2T, hb_lt, hloc_lt, hfit_seg⟩ := h
    subst w_in
    have hw : 0 < w := by omega
    have hidx : b * totalLoc + loc < M * totalLoc := by
      calc b * totalLoc + loc < b * totalLoc + totalLoc := Nat.add_lt_add_left hloc_lt _
        _ = (b + 1) * totalLoc := by ring
        _ ≤ M * totalLoc := Nat.mul_le_mul_right _ hb_lt
    have hw_off_lt := wordOffset_add_one_lt_packedWords (k := 2) hw hidx
    have hb_off_lt : bitOffset 2 w (b * totalLoc + loc) < w := bitOffset_lt hw
    obtain ⟨hof_st, hof_res, _⟩ := locStateOffsetProg_spec (totalLoc := totalLoc) (w := w)
      (b := b) (loc := loc) hw s
    have h2_fit : Fits w 2 :=
      (by decide : 2 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
    have h1_fit : Fits w 1 := h2_fit.of_le (by decide)
    dsimp only [LocStateOffsetPre] at *
    try simp only [hof_st, hof_res, hcs_r] at *
    first
    | exact ⟨trivial, hw3, h2T, hloc_lt, hfit_seg.of_le (by omega)⟩
    | exact h1_fit
    | exact h2_fit
    | omega
    | exact hfit_seg.of_le (by omega)
    | (rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow)
    | (change 1 <<< _ < 2 ^ w; rw [Nat.one_shiftLeft]
       exact Nat.pow_lt_pow_right (by decide) (by omega))
    | (refine writeLoc_diff0_fits ?_; omega)
    | (refine Nat.xor_lt_two_pow (hmem.2 _) (writeLoc_diff0_fits ?_); omega)
    | (refine writeLoc_diff1_fits ?_; omega)
    | (rw [Function.update_of_ne (by omega)]
       refine Nat.xor_lt_two_pow (hmem.2 _) (writeLoc_diff1_fits ?_); omega)
  )

theorem writeLocStateGenProg_spec {c U V w n_max base b loc val : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := writeLocStateGenProg
      ((((base, offLocState c U V w n_max), (totalLocalCoordsWhp n_max, w)), (b, loc)), val)
    let idx := b * totalLocalCoordsWhp n_max + loc
    (Memory.spec 0).clientState s prog =
      { mem := writePacked (base + offLocState c U V w n_max) 2 w s.mem idx val
        frontier := s.frontier } ∧
    memoryCost prog s = 4 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have hw2 : 2 ≤ w := by
    have := henv.log_lt_w; have := mul_ell_le_log hth; have := one_le_ellWhp n_max; omega
  set totalLoc := totalLocalCoordsWhp n_max
  set idx := b * totalLoc + loc
  have hidx : idx < numBucketsWhp n_max * totalLoc := by
    calc b * totalLoc + loc < b * totalLoc + totalLoc := Nat.add_lt_add_left hloc _
      _ = (b + 1) * totalLoc := by ring
      _ ≤ numBucketsWhp n_max * totalLoc := Nat.mul_le_mul_right _ hb
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
  have hseg_b : base + offLocState c U V w n_max +
      packedWords (numBucketsWhp n_max * totalLoc) 2 w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  obtain ⟨hof_st, hof_res, hof_mc⟩ :=
    locStateOffsetProg_spec (totalLoc := totalLoc) (w := w) (b := b) (loc := loc) hw s
  have hk0_eq : (if w - bitOffset 2 w idx < 2 then w - bitOffset 2 w idx else 2) =
      lowWidth 2 w idx := by
    unfold lowWidth; split_ifs <;> omega
  have hvp_lo : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
      (locStateOffsetProg ((totalLoc, w), (b, loc))) := by
    unfold locStateOffsetProg; simp only [pure_bind]; exact validWhpProg_pure _
  have hvp_wp : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
      (writePackedProg base (offLocState c U V w n_max) 2 w idx val) :=
    validWhpProg_writePacked hw hw2 hidx hseg_b
  dsimp only
  unfold writeLocStateGenProg
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind_rw, hof_st, hof_res]
    simp only [pure_bind]
    unfold writePacked highWidth
    dsimp only
    split_ifs with hlt
    · have hl : lowWidth 2 w idx = w - bitOffset 2 w idx := by
        rw [← hk0_eq, ite_eq_left hlt]
      simp only [hl, Nat.one_shiftLeft]
      rfl
    · have hl : lowWidth 2 w idx = 2 := by
        rw [← hk0_eq, ite_eq_right hlt]
      simp only [hl, Nat.one_shiftLeft]
      rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hof_st, hof_res, hof_mc, Nat.zero_add]
    split_ifs <;> rfl
  · refine validWhpProg_bind hvp_lo ?_
    rw [hof_st, hof_res]
    simp only [pure_bind]
    split_ifs with hlt
    · have hl : lowWidth 2 w idx = w - bitOffset 2 w idx := by rw [← hk0_eq, ite_eq_left hlt]
      set k0 := w - bitOffset 2 w idx
      have heq_p : (do
          let word0 ← Memory.read (base + offLocState c U V w n_max + wordOffset 2 w idx)
          Memory.write (base + offLocState c U V w n_max + wordOffset 2 w idx)
            (word0 ^^^ ((((word0 >>> bitOffset 2 w idx) &&& ((1 <<< k0) - 1)) ^^^
              (val &&& ((1 <<< k0) - 1))) <<< bitOffset 2 w idx))
          let word1 ← Memory.read (base + offLocState c U V w n_max + wordOffset 2 w idx + 1)
          Memory.write (base + offLocState c U V w n_max + wordOffset 2 w idx + 1)
            (word1 ^^^ ((word1 &&& ((1 <<< (2 - k0)) - 1)) ^^^
              ((val >>> k0) &&& ((1 <<< (2 - k0)) - 1))))) =
        writePackedProg base (offLocState c U V w n_max) 2 w idx val := by
        unfold writePackedProg highWidth
        simp only [hl, Nat.one_shiftLeft, Nat.shiftRight_zero, Nat.shiftLeft_zero]
      rw [heq_p]; exact hvp_wp
    · have hl : lowWidth 2 w idx = 2 := by rw [← hk0_eq, ite_eq_right hlt]
      have heq_p : (do
          let word0 ← Memory.read (base + offLocState c U V w n_max + wordOffset 2 w idx)
          Memory.write (base + offLocState c U V w n_max + wordOffset 2 w idx)
            (word0 ^^^ ((((word0 >>> bitOffset 2 w idx) &&& ((1 <<< 2) - 1)) ^^^
              (val &&& ((1 <<< 2) - 1))) <<< bitOffset 2 w idx))
          let word1 ← Memory.read (base + offLocState c U V w n_max + wordOffset 2 w idx + 1)
          Memory.write (base + offLocState c U V w n_max + wordOffset 2 w idx + 1)
            (word1 ^^^ ((word1 &&& ((1 <<< (2 - 2)) - 1)) ^^^
              ((val >>> 2) &&& ((1 <<< (2 - 2)) - 1))))) =
        writePackedProg base (offLocState c U V w n_max) 2 w idx val := by
        unfold writePackedProg highWidth
        simp only [hl, Nat.one_shiftLeft, Nat.shiftRight_zero, Nat.shiftLeft_zero]
      rw [heq_p]; exact hvp_wp

end LocStateHelpers

/-! ## Section 2: `PermRt`, `scanBucketProg`, `permuteByTargetProg`, and `fastToCsrGenProg` -/

/-- Congruence of `permuteByTarget` when `dest₁` and `dest₂` agree on all active indices `< n_max`.
-/
theorem permuteByTarget_congr_dest {n_max : ℕ} {d₁ d₂ : ℕ → ℕ} {act₀ : ℕ → Bool}
    (hd : ∀ x < n_max, act₀ x = true → d₁ x = d₂ x) (qArr vArr : ℕ → ℕ) :
    permuteByTarget n_max d₁ act₀ qArr vArr = permuteByTarget n_max d₂ act₀ qArr vArr := by
  have hinner : ∀ (k : ℕ) (st : PermChainState),
      (∀ i, st.2.2.2.2.1 i = true → i < n_max ∧ act₀ i = true) →
      permuteInnerLoop d₁ k st = permuteInnerLoop d₂ k st ∧
      (∀ i, (permuteInnerLoop d₁ k st).2.2.2.2.1 i = true → i < n_max ∧ act₀ i = true) := by
    intro k
    induction k with
    | zero => intro st hinv; exact ⟨rfl, hinv⟩
    | succ k ih =>
      intro ⟨running, curDest, curQ, curV, act, q, v⟩ hinv
      by_cases hr : running = true
      · subst hr
        by_cases ha : act curDest = true
        · obtain ⟨hcd_lt, hcd_act⟩ := hinv curDest ha
          have hdeq := hd curDest hcd_lt hcd_act
          have hstep : permuteInnerStep d₁ (true, curDest, curQ, curV, act, q, v) =
              permuteInnerStep d₂ (true, curDest, curQ, curV, act, q, v) := by
            simp [permuteInnerStep, ha, hdeq]
          have hinv' : ∀ i, Function.update act curDest false i = true →
              i < n_max ∧ act₀ i = true := by
            intro i hi
            by_cases hic : i = curDest
            · subst hic; simp at hi
            · rw [Function.update_of_ne hic] at hi; exact hinv i hi
          obtain ⟨heq_k, hinv_k⟩ :=
            ih (permuteInnerStep d₁ (true, curDest, curQ, curV, act, q, v))
              (by simpa [permuteInnerStep, ha] using hinv')
          exact ⟨by dsimp only [permuteInnerLoop]; rw [← hstep]; exact heq_k, hinv_k⟩
        · have hstep1 : permuteInnerStep d₁ (true, curDest, curQ, curV, act, q, v) =
              (false, curDest, curQ, curV, act, Function.update q curDest curQ,
                Function.update v curDest curV) := by simp [permuteInnerStep, ha]
          have hstep2 : permuteInnerStep d₂ (true, curDest, curQ, curV, act, q, v) =
              (false, curDest, curQ, curV, act, Function.update q curDest curQ,
                Function.update v curDest curV) := by simp [permuteInnerStep, ha]
          obtain ⟨heq_k, hinv_k⟩ := ih
            (false, curDest, curQ, curV, act, Function.update q curDest curQ,
              Function.update v curDest curV) hinv
          exact ⟨by dsimp only [permuteInnerLoop]; rw [hstep1, hstep2]; exact heq_k,
            by dsimp only [permuteInnerLoop]; rw [hstep1]; exact hinv_k⟩
      · have hr_f : running = false := by revert hr; cases running <;> simp
        subst hr_f
        have hstep1 : permuteInnerStep d₁ (false, curDest, curQ, curV, act, q, v) =
            (false, curDest, curQ, curV, act, q, v) := rfl
        have hstep2 : permuteInnerStep d₂ (false, curDest, curQ, curV, act, q, v) =
            (false, curDest, curQ, curV, act, q, v) := rfl
        obtain ⟨heq_k, hinv_k⟩ := ih (false, curDest, curQ, curV, act, q, v) hinv
        exact ⟨by dsimp only [permuteInnerLoop]; rw [hstep1, hstep2]; exact heq_k, hinv_k⟩
  have houter : ∀ k : ℕ,
      let t₁ := permuteOuterLoop n_max d₁ k (fun i => decide (i < n_max) && act₀ i, qArr, vArr)
      let t₂ := permuteOuterLoop n_max d₂ k (fun i => decide (i < n_max) && act₀ i, qArr, vArr)
      t₁ = t₂ ∧ (∀ i, t₁.1 i = true → i < n_max ∧ act₀ i = true) := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, fun i hi => ?_⟩
      dsimp only [permuteOuterLoop] at hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi
    | succ k ih =>
      obtain ⟨heq_k, hinv_k⟩ := ih
      dsimp only at heq_k hinv_k ⊢
      dsimp only [permuteOuterLoop]
      rw [← heq_k]
      rcases htk :
          permuteOuterLoop n_max d₁ k (fun i => decide (i < n_max) && act₀ i, qArr, vArr) with
        ⟨act, q, v⟩
      rw [htk] at hinv_k
      by_cases ha : act k = true
      · obtain ⟨hk_lt, hk_act⟩ := hinv_k k ha
        have hdk := hd k hk_lt hk_act
        have hinv0 : ∀ i, Function.update act k false i = true → i < n_max ∧ act₀ i = true := by
          intro i hi
          by_cases hik : i = k
          · subst hik; simp at hi
          · rw [Function.update_of_ne hik] at hi; exact hinv_k i hi
        obtain ⟨hin_eq, hin_inv⟩ :=
          hinner n_max (true, d₁ k, q k, v k, Function.update act k false, q, v) hinv0
        dsimp only [permuteOuterStep]
        simp only [ha, ↓reduceIte, ← hdk, ← hin_eq]
        exact ⟨trivial, hin_inv⟩
      · dsimp only [permuteOuterStep]
        simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, hinv_k⟩
  dsimp only [permuteByTarget]
  rw [(houter n_max).1]

/-- Compact 18-word runtime parameter bundle for `permuteByTarget`, `fastToCsr`, and `csrToFast`
array loops:
`(((base, w), (n_max, M)), (((cf, cb), (frontTotal, poolSize)),`
`(((gBits, quotBits), (valBits, permActBits)),`
`((offQuot, offVal), ((offPermAct, offBktMeta), (offFbStart, (offBackPtr, offPoolOwner)))))))`. -/
abbrev PermRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) ×
    (((ℕ × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) ×
        ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))))

@[expose] def prBase (p : PermRt) : ℕ := p.1.1.1
@[expose] def prW (p : PermRt) : ℕ := p.1.1.2
@[expose] def prNMax (p : PermRt) : ℕ := p.1.2.1
@[expose] def prM (p : PermRt) : ℕ := p.1.2.2
@[expose] def prCF (p : PermRt) : ℕ := p.2.1.1.1
@[expose] def prCB (p : PermRt) : ℕ := p.2.1.1.2
@[expose] def prFrontTotal (p : PermRt) : ℕ := p.2.1.2.1
@[expose] def prPoolSize (p : PermRt) : ℕ := p.2.1.2.2
@[expose] def prGBits (p : PermRt) : ℕ := p.2.2.1.1.1
@[expose] def prQuotBits (p : PermRt) : ℕ := p.2.2.1.1.2
@[expose] def prValBits (p : PermRt) : ℕ := p.2.2.1.2.1
@[expose] def prPermActBits (p : PermRt) : ℕ := p.2.2.1.2.2
@[expose] def prOffQuot (p : PermRt) : ℕ := p.2.2.2.1.1
@[expose] def prOffVal (p : PermRt) : ℕ := p.2.2.2.1.2
@[expose] def prOffPermAct (p : PermRt) : ℕ := p.2.2.2.2.1.1
@[expose] def prOffBktMeta (p : PermRt) : ℕ := p.2.2.2.2.1.2
@[expose] def prOffFbStart (p : PermRt) : ℕ := p.2.2.2.2.2.1
@[expose] def prOffBackPtr (p : PermRt) : ℕ := p.2.2.2.2.2.2.1
@[expose] def prOffPoolOwner (p : PermRt) : ℕ := p.2.2.2.2.2.2.2

/-- Pure constructor for `PermRt` (19 words). -/
@[expose] def mkPermRt (c U V w n_max base : ℕ) : PermRt :=
  (((base, w), (n_max, numBucketsWhp n_max)),
   (((capFrontWhp n_max, capBackWhp n_max),
     (numBucketsWhp n_max * capFrontWhp n_max, poolSizeWhp n_max)),
    (((globalPtrBits n_max, quotBitsWhp U n_max),
      (valBits V, 12 * ellWhp n_max + 4)),
     ((offQuotWhp c w n_max, offValWhp c U w n_max),
      ((offPermAct c U V w n_max, offBktMeta c U V w n_max),
       (offFbStart c U V w n_max,
        (offBackPtr c U V w n_max, offPoolOwner c U V w n_max)))))))

/-- Runtime envelope for `PermRt` in the large regime. -/
@[expose] def PermRtEnvGen (w : ℕ) (prt : PermRt) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (prBase prt) ∧
    prt = mkPermRt c U V w₀ n_max (prBase prt)

/-- Extract `PermRt` from `(cp, base)` in 0 memory operations. -/
@[irreducible] def mkPermRtGenProg (d : WhpCoreParams × ℕ) : Memory.Prog PermRt := do
  let cp := d.1
  let base ← pure d.2
  pure (((base, wpW cp), (wpNMax cp, wpM cp)),
    (((wpCapFront cp, wpCapBack cp), (wpFrontTotal cp, wpPoolSize cp)),
     (((wpGlobalPtrBits cp, wpQuotBits cp), (wpValBits cp, wpPermActBits cp)),
      ((wpOffQuot cp, wpOffVal cp),
       ((wpOffPermAct cp, wpOffBktMeta cp),
        (wpOffFbStart cp, (wpOffBackPtr cp, wpOffPoolOwner cp)))))))

theorem realizes_mkPermRtGen :
    Realizes .exact mkPermRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := PermRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkPermRtGenProg
  realize

theorem mkPermRtGenProg_spec {c U V w n_max base : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkPermRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkPermRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkPermRtGenProg mkPermRt
  simp only [pure_bind, wp_large_w hth, wp_large_nMax hth, wp_large_M hth,
    wp_large_capFront hth, wp_large_capBack hth, wp_large_frontTotal hth, wp_large_poolSize hth,
    wp_large_globalPtrBits hth, wp_large_quotBits hth, wp_large_valBits hth,
    wp_large_permActBits hth, wp_large_offQuot hth, wp_large_offVal hth,
    wp_large_offPermAct hth, wp_large_offBktMeta hth, wp_large_offFbStart hth,
    wp_large_offBackPtr hth, wp_large_offPoolOwner hth]
  exact ⟨rfl, rfl, rfl, validWhpProg_pure _⟩

section PermSafety

private theorem to_true_exists {w : ℕ} {P : ℕ → Prop}
    (h : ∃ N, w = w ∧ P N) : ∃ N, True ∧ P N :=
  let ⟨N, _, hP⟩ := h; ⟨N, trivial, hP⟩

private theorem perm_bounds {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let M := numBucketsWhp n_max
    M < n_max ∧
    M + 1 ≤ n_max ∧
    16 * M ≤ n_max ∧
    M * capBackWhp n_max ≤ n_max ∧
    poolSizeWhp n_max ≤ n_max ∧
    12 * ellWhp n_max + 4 ≤ w ∧
    quotBitsWhp U n_max ≤ w ∧
    valBits V ≤ w ∧
    globalPtrBits n_max ≤ w := by
  have hth := henv.2.2.2.1
  have hL2 := two_le_scaleWhp n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  have hM_lt : numBucketsWhp n_max < n_max := by omega
  have hcb_le : capBackWhp n_max ≤ (scaleWhp n_max) ^ 12 := by
    unfold capBackWhp
    calc 2 * (scaleWhp n_max) ^ 11 ≤ scaleWhp n_max * (scaleWhp n_max) ^ 11 :=
          Nat.mul_le_mul_right _ hL2
      _ = (scaleWhp n_max) ^ 12 := by ring
  have hMcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have hps : poolSizeWhp n_max ≤ n_max := Nat.sub_le _ _
  have hlog_w := henv.log_lt_w
  have hlog_ge := mul_ell_le_log hth
  have hell1 := one_le_ellWhp n_max
  have hpa_w : 12 * ellWhp n_max + 4 ≤ w := by omega
  have hqk : quotBitsWhp U n_max ≤ w :=
    (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  exact ⟨hM_lt, by omega, h16M, hMcb, hps, hpa_w, hqk,
    valBits_le_w henv.2.2.2.2.2.2.1,
    globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1⟩

private theorem pr_quot_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ quotBitsWhp U n_max ≤ w ∧ idx < N ∧
      Fits w (base + offQuotWhp c w n_max + packedWords N (quotBitsWhp U n_max) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.2.1 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).1

private theorem pr_val_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ valBits V ≤ w ∧ idx < N ∧
      Fits w (base + offValWhp c U w n_max + packedWords N (valBits V) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.2.2.1 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.1

private theorem pr_act_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ 12 * ellWhp n_max + 4 ≤ w ∧ idx < N ∧
      Fits w (base + offPermAct c U V w n_max + packedWords N (12 * ellWhp n_max + 4) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.1 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.2.1

private theorem pr_bm_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < 16 * numBucketsWhp n_max) :
    ∃ N, w = w ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBktMeta c U V w n_max + packedWords N (globalPtrBits n_max) w) :=
  henv.bktMeta_safe hidx

private theorem pr_fb_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < numBucketsWhp n_max + 1) :
    ∃ N, w = w ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offFbStart c U V w n_max + packedWords N (globalPtrBits n_max) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.2.2.2 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1

private theorem pr_bp_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ)
    (hidx : idx < numBucketsWhp n_max * capBackWhp n_max) :
    ∃ N, w = w ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBackPtr c U V w n_max + packedWords N (globalPtrBits n_max) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.2.2.2 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1

private theorem pr_po_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (idx : ℕ) (hidx : idx < poolSizeWhp n_max) :
    ∃ N, w = w ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offPoolOwner c U V w n_max + packedWords N (globalPtrBits n_max) w) :=
  henv.packed_safe_of_le (perm_bounds henv).2.2.2.2.2.2.2.2 hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1

end PermSafety

/-- Step of `csrBucketOfIdx` over a packed `globalPtrBits` array at `offArr` with index multiplier
`stride ∈ {1, 2}` (`d = ((((base, offArr), (gBits, w)), (stride, target)), (k, acc))`). -/
@[irreducible] def scanBucketStepProg
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let base ← pure d.1.1.1.1
  let offArr ← pure d.1.1.1.2
  let gBits ← pure d.1.1.2.1
  let w ← pure d.1.1.2.2
  let stride ← pure d.1.2.1
  let target ← pure d.1.2.2
  let k ← pure d.2.1
  let acc ← pure d.2.2
  let one_v ← pure 1
  let k1 ← pure (k + one_v)
  let idx0 ← pure (stride * k)
  let idx1 ← pure (stride * k1)
  let lo ← readPackedGenProg (((base, offArr), (gBits, w)), idx0)
  let hi ← readPackedGenProg (((base, offArr), (gBits, w)), idx1)
  if target < lo then
    pure (k1, acc)
  else if target < hi then
    pure (k1, k)
  else
    pure (k1, acc)

private theorem memoryCost_scanBucketStep_pos
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (scanBucketStepProg d) s := by
  unfold scanBucketStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

/-- Precondition for `scanBucketStepProg` (`stride = 1` on `offFbStart` or `stride = 2` on
`offBktMeta`, with `k < M`). -/
@[expose] def ScanBucketStepPre (w : ℕ)
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.1 ∧
    d.1.1.2.1 = globalPtrBits n_max ∧
    d.1.1.2.2 = w₀ ∧
    d.2.1 < numBucketsWhp n_max ∧
    ((d.1.2.1 = 1 ∧ d.1.1.1.2 = offFbStart c U V w₀ n_max) ∨
     (d.1.2.1 = 2 ∧ d.1.1.1.2 = offBktMeta c U V w₀ n_max))

theorem realizes_scanBucketStep :
    Realizes .exact scanBucketStepProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ScanBucketStepPre
      (fun _ _ => 0) := by
  unfold scanBucketStepProg
  have hrp := realizes_readPackedGen
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨base, offArr⟩, gBits, w_in⟩, stride, target⟩, k, acc⟩
    try clear hwords hmem
    dsimp only [ScanBucketStepPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl, rfl, hk_lt, hmode⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hM_lt, hM1_le, h16M, _, _, _, _, _, _⟩ := perm_bounds henv
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | (rcases hmode with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       · exact henv.fits_of_le_n_max (by omega)
       · exact henv.fits_of_le_n_max (by omega))
    | (rcases hmode with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       · apply to_true_exists (w := w); refine pr_fb_safe henv _ ?_; omega
       · apply to_true_exists (w := w); refine pr_bm_safe henv _ ?_; omega)
  )

/-- `iterate` wrapper for `scanBucketStepProg` computing `csrBucketOfIdx` across `0 .. rem - 1`. -/
@[irreducible] def scanBucketLoopProg
    (p : ((((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) :=
  iterate scanBucketStepProg p.1.1 p.2 p.1.2

theorem realizes_scanBucketLoop :
    Realizes .exact scanBucketLoopProg
      (WordEncoding.encode (α := ((((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w p s => iterationSafe scanBucketStepProg ScanBucketStepPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold scanBucketLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_scanBucketStep
    memoryCost_scanBucketStep_pos

private def scanFrom (arr : ℕ → ℕ) (target : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | r + 1, k₀, acc =>
    let acc1 := if target < arr k₀ then acc else if target < arr (k₀ + 1) then k₀ else acc
    scanFrom arr target r (k₀ + 1) acc1

private theorem scanFrom_step_last (arr : ℕ → ℕ) (target : ℕ) :
    ∀ r k₀ acc,
      scanFrom arr target (r + 1) k₀ acc =
        (let prev := scanFrom arr target r k₀ acc
         if target < arr (k₀ + r) then prev
         else if target < arr (k₀ + r + 1) then k₀ + r
         else prev) := by
  intro r
  induction r with
  | zero =>
    intro k₀ acc
    simp only [scanFrom, Nat.add_zero]
  | succ r ih =>
    intro k₀ acc
    change scanFrom arr target (r + 1) (k₀ + 1) _ = _
    rw [ih (k₀ + 1)]
    have h1 : k₀ + 1 + r = k₀ + (r + 1) := by omega
    rw [h1]
    rfl

private theorem scanFrom_zero_eq_csrBucketOfIdx (arr : ℕ → ℕ) (target : ℕ) :
    ∀ rem, scanFrom arr target rem 0 0 = csrBucketOfIdx arr target rem := by
  intro rem
  induction rem with
  | zero => rfl
  | succ rem ih =>
    rw [scanFrom_step_last, Nat.zero_add, ih]
    dsimp only [csrBucketOfIdx]
    by_cases h1 : arr rem ≤ target
    · have hnlt : ¬(target < arr rem) := Nat.not_lt.mpr h1
      by_cases h2 : target < arr (rem + 1) <;> simp [h1, hnlt, h2]
    · have hlt : target < arr rem := Nat.lt_of_not_ge h1
      simp [h1, hlt]

private theorem scanBucketLoop_spec {c U V w n_max base offArr stride target : ℕ}
    {arr : ℕ → ℕ} {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base)
    (hmode : (stride = 1 ∧ offArr = offFbStart c U V w n_max) ∨
             (stride = 2 ∧ offArr = offBktMeta c U V w n_max))
    (harr : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offArr) (globalPtrBits n_max) w s.mem (stride * x) = arr x) :
    let cfg := (((base, offArr), (globalPtrBits n_max, w)), (stride, target))
    ∀ rem k₀ acc,
      k₀ + rem ≤ numBucketsWhp n_max →
      let prog := scanBucketLoopProg ((cfg, (k₀, acc)), rem)
      iterationSafe scanBucketStepProg ScanBucketStepPre w cfg rem (k₀, acc) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog = (k₀ + rem, scanFrom arr target rem k₀ acc) ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro cfg rem
  have hw := henv.2.1
  have h16M := (perm_bounds henv).2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  induction rem with
  | zero =>
    intro k₀ acc _
    unfold scanBucketLoopProg iterate
    exact ⟨trivial, rfl, Prod.ext (Nat.add_zero k₀).symm rfl, validWhpProg_pure _⟩
  | succ rem ih =>
    intro k₀ acc hle
    have hk_lt : k₀ < numBucketsWhp n_max := by omega
    have hpre : ScanBucketStepPre w (cfg, (k₀, acc)) s :=
      ⟨c, U, V, w, n_max, henv, rfl, rfl, hk_lt, hmode⟩
    have hst1 : (Memory.spec 0).clientState s (scanBucketStepProg (cfg, (k₀, acc))) = s := by
      unfold scanBucketStepProg
      dsimp only [cfg]
      simp only [pure_bind]
      rw [clientState_bind_rw, clientState_readPackedGen,
        clientState_bind_rw, clientState_readPackedGen]
      split_ifs <;> rfl
    set acc1 := if target < arr k₀ then acc else if target < arr (k₀ + 1) then k₀ else acc
    have hres1 : (Memory.spec 0).clientResult s (scanBucketStepProg (cfg, (k₀, acc))) =
        (k₀ + 1, acc1) := by
      unfold scanBucketStepProg
      dsimp only [cfg]
      simp only [pure_bind]
      rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
        clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
        harr k₀ hk_lt.le, harr (k₀ + 1) hk_lt]
      dsimp only [acc1]
      split_ifs <;> rfl
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (scanBucketStepProg (cfg, (k₀, acc))) := by
      unfold scanBucketStepProg
      dsimp only [cfg]
      simp only [pure_bind]
      rcases hmode with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hfb_b : base + offFbStart c U V w n_max +
            packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ≤
            base + largeSpaceWhp c U V w n_max := by
          rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
        refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedGen]
        refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hfb_b) ?_
        split_ifs <;> exact validWhpProg_pure _
      · have hbm_b : base + offBktMeta c U V w n_max +
            packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
            base + largeSpaceWhp c U V w n_max := by
          rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
        refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hbm_b) ?_
        rw [clientState_readPackedGen]
        refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hbm_b) ?_
        split_ifs <;> exact validWhpProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (k₀ + 1) acc1 (by omega)
    dsimp only at hst_r hres_r hvp_r ⊢
    unfold scanBucketLoopProg at hst_r hres_r hvp_r ⊢
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hst1, hres1]
      exact hsafe_r
    · change (Memory.spec 0).clientState s (scanBucketStepProg (cfg, (k₀, acc)) >>= _) = s
      rw [clientState_bind_rw, hst1, hres1]
      exact hst_r
    · change (Memory.spec 0).clientResult s (scanBucketStepProg (cfg, (k₀, acc)) >>= _) = _
      rw [clientResult_bind_rw, hst1, hres1, hres_r]
      exact Prod.ext (by omega) rfl
    · change ValidWhpProg _ _ s (scanBucketStepProg (cfg, (k₀, acc)) >>= _)
      refine validWhpProg_bind hvp1 ?_
      rw [hst1, hres1]
      exact hvp_r

theorem scanBucketLoop_invariant {c U V w n_max base offArr stride target : ℕ}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base)
    (hmode : (stride = 1 ∧ offArr = offFbStart c U V w n_max) ∨
             (stride = 2 ∧ offArr = offBktMeta c U V w n_max)) :
    let arr := fun x => readPacked (base + offArr) (globalPtrBits n_max) w s.mem (stride * x)
    let cfg := (((base, offArr), (globalPtrBits n_max, w)), (stride, target))
    let prog := scanBucketLoopProg ((cfg, (0, 0)), numBucketsWhp n_max)
    iterationSafe scanBucketStepProg ScanBucketStepPre w cfg (numBucketsWhp n_max) (0, 0) s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (numBucketsWhp n_max, csrBucketOfIdx arr target (numBucketsWhp n_max)) ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  set arr := fun x => readPacked (base + offArr) (globalPtrBits n_max) w s.mem (stride * x)
  obtain ⟨hsf, hst, hres, hvp⟩ := scanBucketLoop_spec (target := target) (arr := arr)
    henv hmode (fun _ _ => rfl) (numBucketsWhp n_max) 0 0 (by omega)
  rw [Nat.zero_add, scanFrom_zero_eq_csrBucketOfIdx] at hres
  exact ⟨hsf, hst, hres, hvp⟩

/-- Evaluate `(actBit, destVal)` for `permuteByTarget` in mode `1` (`fastToCsr`) or mode `0`
(`csrToFast`), guaranteeing `destVal < prNMax prt` unconditionally (`d = ((prt, mode), x)`). -/
@[irreducible] def permEvalActDestProg (d : (PermRt × ℕ) × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let prt := d.1.1
  let mode ← pure d.1.2
  let x ← pure d.2
  let base ← pure (prBase prt)
  let w ← pure (prW prt)
  let nMax ← pure (prNMax prt)
  let M ← pure (prM prt)
  let cf ← pure (prCF prt)
  let cb ← pure (prCB prt)
  let frontTotal ← pure (prFrontTotal prt)
  let poolSize ← pure (prPoolSize prt)
  let gBits ← pure (prGBits prt)
  let offBm ← pure (prOffBktMeta prt)
  let offFb ← pure (prOffFbStart prt)
  let offBp ← pure (prOffBackPtr prt)
  let offPo ← pure (prOffPoolOwner prt)
  let zero_v ← pure 0
  let one_v ← pure 1
  if mode = one_v then
    if x < frontTotal then
      if zero_v < cf then
        let b ← pure (x / cf)
        let loc ← pure (x % cf)
        if b < M then
          let idxCnt ← pure (16 * b)
          let cnt ← readPackedGenProg (((base, offBm), (gBits, w)), idxCnt)
          if loc < cnt then
            let fbb ← readPackedGenProg (((base, offFb), (gBits, w)), b)
            if fbb < nMax then
              let remN ← pure (nMax - fbb)
              if loc < remN then
                pure (one_v, fbb + loc)
              else pure (zero_v, zero_v)
            else pure (zero_v, zero_v)
          else pure (zero_v, zero_v)
        else pure (zero_v, zero_v)
      else pure (zero_v, zero_v)
    else
      let poolIdx ← pure (x - frontTotal)
      if poolIdx < poolSize then
        if zero_v < cb then
          let enc ← readPackedGenProg (((base, offPo), (gBits, w)), poolIdx)
          let b ← pure (enc / cb)
          let k ← pure (enc % cb)
          if b < M then
            let idxCnt ← pure (16 * b)
            let cnt ← readPackedGenProg (((base, offBm), (gBits, w)), idxCnt)
            if nMax < cnt then
              pure (zero_v, zero_v)
            else if cf < cnt then
              let remCnt ← pure (cnt - cf)
              if k < remCnt then
                let idxBp ← pure (b * cb + k)
                let bpVal ← readPackedGenProg (((base, offBp), (gBits, w)), idxBp)
                if bpVal = poolIdx then
                  let loc ← pure (cf + k)
                  let fbb ← readPackedGenProg (((base, offFb), (gBits, w)), b)
                  if fbb < nMax then
                    let remN ← pure (nMax - fbb)
                    if loc < remN then
                      pure (one_v, fbb + loc)
                    else pure (zero_v, zero_v)
                  else pure (zero_v, zero_v)
                else pure (zero_v, zero_v)
              else pure (zero_v, zero_v)
            else pure (zero_v, zero_v)
          else pure (zero_v, zero_v)
        else pure (zero_v, zero_v)
      else pure (zero_v, zero_v)
  else
    let N ← readPackedGenProg (((base, offFb), (gBits, w)), M)
    if x < N then
      let sb ← scanBucketLoopProg
        (((((base, offFb), (gBits, w)), (one_v, x)), (zero_v, zero_v)), M)
      let b ← pure sb.2
      if b < M then
        let fbb ← readPackedGenProg (((base, offFb), (gBits, w)), b)
        if x < fbb then
          pure (zero_v, zero_v)
        else
          let loc ← pure (x - fbb)
          if loc < cf then
            pure (one_v, b * cf + loc)
          else
            let k ← pure (loc - cf)
            if k < cb then
              let idxBp ← pure (b * cb + k)
              let bpVal ← readPackedGenProg (((base, offBp), (gBits, w)), idxBp)
              if bpVal < poolSize then
                pure (one_v, frontTotal + bpVal)
              else pure (zero_v, zero_v)
            else pure (zero_v, zero_v)
      else pure (zero_v, zero_v)
    else pure (zero_v, zero_v)

/-- Precondition for `permEvalActDestProg`. -/
@[expose] def PermEvalPre (w : ℕ) (d : (PermRt × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  PermRtEnvGen w d.1.1 ∧ d.2 < prNMax d.1.1

private theorem mul_add_lt_mul {b k cap M : ℕ} (hb : b < M) (hk : k < cap) :
    b * cap + k < M * cap := by
  calc b * cap + k < b * cap + cap := Nat.add_lt_add_left hk _
    _ = (b + 1) * cap := by ring
    _ ≤ M * cap := Nat.mul_le_mul_right _ hb

private theorem front_add_pool_lt_n_max {n_max bpVal : ℕ} (h : bpVal < poolSizeWhp n_max) :
    numBucketsWhp n_max * capFrontWhp n_max + bpVal < n_max := by
  unfold poolSizeWhp at h; omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem realizes_permEvalActDest :
    Realizes .exact permEvalActDestProg
      (WordEncoding.encode (α := (PermRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      PermEvalPre
      (fun _ _ => 0) := by
  unfold permEvalActDestProg
  have hrp := realizes_readPackedGen
  have hsbl := realizes_scanBucketLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨prt, mode⟩, x⟩
    try clear hwords hmem
    dsimp only [PermEvalPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_prt⟩, hx_lt⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    generalize prBase prt = base at henv heq_prt
    subst heq_prt
    obtain ⟨hM_lt, hM1_le, h16M, hMcb, hps, _, _, _, _⟩ := perm_bounds henv
    have hcs_sb := (scanBucketLoop_invariant (target := x) henv (Or.inl ⟨rfl, rfl⟩) (s := s)).2.1
    dsimp only [mkPermRt, prBase, prW, prNMax, prM, prCF, prCB, prFrontTotal, prPoolSize, prGBits,
      prOffBktMeta, prOffFbStart, prOffBackPtr, prOffPoolOwner] at *
    try simp only [hcs, hcs_sb] at *
    have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (refine (henv.fits_of_le_n_max hMcb).of_le (mul_add_lt_mul ?_ ?_).le
       · assumption
       · first | exact Nat.mod_lt _ (by assumption) | assumption)
    | (apply to_true_exists (w := w)
       refine pr_bp_safe henv _ (mul_add_lt_mul ?_ ?_)
       · assumption
       · first | exact Nat.mod_lt _ (by assumption) | assumption)
    | (refine (henv.fits_of_le_n_max hMcf_le).of_le (mul_add_lt_mul ?_ ?_).le <;> assumption)
    | (refine henv.fits_of_le_n_max (front_add_pool_lt_n_max ?_).le; assumption)
    | (apply to_true_exists (w := w); refine pr_bm_safe henv _ ?_; omega)
    | (apply to_true_exists (w := w); refine pr_fb_safe henv _ ?_; omega)
    | (apply to_true_exists (w := w); refine pr_po_safe henv _ ?_; omega)
    | exact (scanBucketLoop_invariant (target := x) henv (Or.inl ⟨rfl, rfl⟩)).1
  )

/-- Structural invariant of `permEvalActDestProg`: leaves memory unchanged, satisfies
`ValidWhpProg`, and returns `(actBit, destVal)` with `destVal < n_max`. -/
theorem permEvalActDestProg_invariant {c U V w n_max base mode x : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (_hx : x < n_max) :
    let prog := permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x)
    (Memory.spec 0).clientState s prog = s ∧
    ((Memory.spec 0).clientResult s prog).2 < n_max ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le henv.2.2.2.1
  obtain ⟨hM_lt, hM1_le, h16M, hMcb, _, _, _, _, _⟩ := perm_bounds henv
  have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbp_b : base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.1 _
  have hpo_b : base + offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.1 _
  obtain ⟨_, hsb_st, _, hsb_vp⟩ :=
    scanBucketLoop_invariant (target := x) henv (Or.inl ⟨rfl, rfl⟩) (s := s)
  dsimp only
  unfold permEvalActDestProg
  dsimp only [mkPermRt, prBase, prW, prNMax, prM, prCF, prCB, prFrontTotal, prPoolSize, prGBits,
    prOffBktMeta, prOffFbStart, prOffBackPtr, prOffPoolOwner]
  simp only [pure_bind]
  by_cases hm : mode = 1
  · simp only [hm, ↓reduceIte]
    by_cases hft : x < numBucketsWhp n_max * capFrontWhp n_max
    · simp only [hft, ↓reduceIte]
      by_cases hcf : 0 < capFrontWhp n_max
      · simp only [hcf, ↓reduceIte]
        by_cases hb : x / capFrontWhp n_max < numBucketsWhp n_max
        · simp only [hb, ↓reduceIte]
          refine ⟨?_, ?_, ?_⟩
          · rw [clientState_bind_rw, clientState_readPackedGen]
            split_ifs
            · rw [clientState_bind_rw, clientState_readPackedGen]; split_ifs <;> rfl
            · rfl
          · rw [clientResult_bind_rw, clientState_readPackedGen]
            split_ifs
            · rw [clientResult_bind_rw, clientState_readPackedGen]
              split_ifs <;> (simp only [StateTransitionSpec.clientResult_pure]; omega)
            · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
          · refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hbm_b) ?_
            rw [clientState_readPackedGen]
            split_ifs
            · refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hfb_b) ?_
              split_ifs <;> exact validWhpProg_pure _
            · exact validWhpProg_pure _
        · simp only [hb, ↓reduceIte]; exact ⟨rfl, hn_pos, validWhpProg_pure _⟩
      · simp only [hcf, ↓reduceIte]; exact ⟨rfl, hn_pos, validWhpProg_pure _⟩
    · simp only [hft, ↓reduceIte]
      by_cases hps : x - numBucketsWhp n_max * capFrontWhp n_max < poolSizeWhp n_max
      · simp only [hps, ↓reduceIte]
        by_cases hcb : 0 < capBackWhp n_max
        · simp only [hcb, ↓reduceIte]
          set pIdx := x - numBucketsWhp n_max * capFrontWhp n_max
          set enc := readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s.mem
            pIdx
          have hk_cb : enc % capBackWhp n_max < capBackWhp n_max := Nat.mod_lt _ hcb
          refine ⟨?_, ?_, ?_⟩
          · rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
            split_ifs with hb
            · rw [clientState_bind_rw, clientState_readPackedGen]
              split_ifs
              · rfl
              · rw [clientState_bind_rw, clientState_readPackedGen]
                split_ifs
                · rw [clientState_bind_rw, clientState_readPackedGen]
                  split_ifs <;> rfl
                · rfl
              · rfl
              · rfl
            · rfl
          · rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
            split_ifs with hb
            · rw [clientResult_bind_rw, clientState_readPackedGen]
              split_ifs
              · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
              · rw [clientResult_bind_rw, clientState_readPackedGen]
                split_ifs
                · rw [clientResult_bind_rw, clientState_readPackedGen]
                  split_ifs <;> (simp only [StateTransitionSpec.clientResult_pure]; omega)
                · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
              · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
              · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
            · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
          · refine validWhpProg_bind (validWhpProg_readPacked hw hps hpo_b) ?_
            rw [clientState_readPackedGen, clientResult_readPackedGen]
            split_ifs with hb
            · refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hbm_b) ?_
              rw [clientState_readPackedGen]
              split_ifs
              · exact validWhpProg_pure _
              · have hbk_lt : (enc / capBackWhp n_max) * capBackWhp n_max +
                    enc % capBackWhp n_max < numBucketsWhp n_max * capBackWhp n_max := by
                  calc _ < (enc / capBackWhp n_max) * capBackWhp n_max + capBackWhp n_max :=
                        Nat.add_lt_add_left hk_cb _
                    _ = (enc / capBackWhp n_max + 1) * capBackWhp n_max := by ring
                    _ ≤ numBucketsWhp n_max * capBackWhp n_max := Nat.mul_le_mul_right _ hb
                refine validWhpProg_bind (validWhpProg_readPacked hw hbk_lt hbp_b) ?_
                rw [clientState_readPackedGen]
                split_ifs
                · refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hfb_b) ?_
                  split_ifs <;> exact validWhpProg_pure _
                · exact validWhpProg_pure _
              · exact validWhpProg_pure _
              · exact validWhpProg_pure _
            · exact validWhpProg_pure _
        · simp only [hcb, ↓reduceIte]; exact ⟨rfl, hn_pos, validWhpProg_pure _⟩
      · simp only [hps, ↓reduceIte]; exact ⟨rfl, hn_pos, validWhpProg_pure _⟩
  · simp only [hm, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · rw [clientState_bind_rw, clientState_readPackedGen]
      split_ifs
      · rw [clientState_bind_rw, hsb_st]
        split_ifs with hb
        · rw [clientState_bind_rw, clientState_readPackedGen]
          split_ifs
          · rfl
          · rfl
          · rw [clientState_bind_rw, clientState_readPackedGen]; split_ifs <;> rfl
          · rfl
        · rfl
      · rfl
    · rw [clientResult_bind_rw, clientState_readPackedGen]
      split_ifs
      · rw [clientResult_bind_rw, hsb_st]
        set b_idx := ((Memory.spec 0).clientResult s
          (scanBucketLoopProg
            (((((base, offFbStart c U V w n_max), (globalPtrBits n_max, w)), (1, x)), (0, 0)),
             numBucketsWhp n_max))).2
        split_ifs with hb
        · rw [clientResult_bind_rw, clientState_readPackedGen]
          split_ifs with hxf hloc hk
          · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
          · simp only [StateTransitionSpec.clientResult_pure]
            exact (mul_add_lt_mul hb hloc).trans_le hMcf_le
          · rw [clientResult_bind_rw, clientState_readPackedGen]
            split_ifs with hbp'
            · simp only [StateTransitionSpec.clientResult_pure]
              unfold poolSizeWhp at hbp'
              omega
            · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
          · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
        · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
      · simp only [StateTransitionSpec.clientResult_pure]; exact hn_pos
    · refine validWhpProg_bind (validWhpProg_readPacked hw (Nat.lt_succ_self _) hfb_b) ?_
      rw [clientState_readPackedGen]
      split_ifs
      · refine validWhpProg_bind hsb_vp ?_
        rw [hsb_st]
        set b_idx := ((Memory.spec 0).clientResult s
          (scanBucketLoopProg
            (((((base, offFbStart c U V w n_max), (globalPtrBits n_max, w)), (1, x)), (0, 0)),
             numBucketsWhp n_max))).2
        split_ifs with hb
        · refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedGen]
          split_ifs with hxf hloc hk
          · exact validWhpProg_pure _
          · exact validWhpProg_pure _
          · refine validWhpProg_bind
              (validWhpProg_readPacked hw (mul_add_lt_mul hb hk) hbp_b) ?_
            split_ifs <;> exact validWhpProg_pure _
          · exact validWhpProg_pure _
        · exact validWhpProg_pure _
      · exact validWhpProg_pure _

/-- Step initializing `offPermAct[i] := act₀ i` (`d = ((prt, mode), i)`). -/
@[irreducible] def permInitActStepProg (d : (PermRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let prt := d.1.1
  let i ← pure d.2
  let ad ← permEvalActDestProg d
  writePackedGenProg
    ((((prBase prt, prOffPermAct prt), (prPermActBits prt, prW prt)), i), ad.1)
  pure (i + 1)

private theorem memoryCost_permInitActStep_pos (d : (PermRt × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (permInitActStepProg d) s := by
  unfold permInitActStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < _ + (4 + 0)
  omega

theorem realizes_permInitActStep :
    Realizes .exact permInitActStepProg
      (WordEncoding.encode (α := (PermRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PermEvalPre
      (fun _ _ => 0) := by
  unfold permInitActStepProg
  have hpe := realizes_permEvalActDest
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨prt, mode⟩, i⟩
    try clear hwords hmem
    dsimp only [PermEvalPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_prt⟩, hi_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    generalize prBase prt = base at henv heq_prt
    subst heq_prt
    dsimp only [mkPermRt, prBase, prW, prNMax, prPermActBits, prOffPermAct] at *
    first
    | exact ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hi_lt⟩
    | exact henv.fits_of_le_n_max (by omega)
    | exact pr_act_safe henv i hi_lt
  )

/-- `iterate` wrapper initializing `offPermAct[0 .. rem - 1]`. -/
@[irreducible] def permInitActLoopProg (p : ((PermRt × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate permInitActStepProg p.1.1 p.2 p.1.2

theorem realizes_permInitActLoop :
    Realizes .exact permInitActLoopProg
      (WordEncoding.encode (α := ((PermRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w p s => iterationSafe permInitActStepProg PermEvalPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold permInitActLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := PermRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_permInitActStep
    memoryCost_permInitActStep_pos

/-- Single step of `permuteInnerLoop`: `st = ((running, curDest), (curQ, curV))`
(`d = ((prt, mode), st)`). -/
@[irreducible] def permInnerStepProg
    (d : (PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) : Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ)) := do
  let prt := d.1.1
  let running ← pure d.2.1.1
  let curDest ← pure d.2.1.2
  let curQ ← pure d.2.2.1
  let curV ← pure d.2.2.2
  let base ← pure (prBase prt)
  let w ← pure (prW prt)
  let qBits ← pure (prQuotBits prt)
  let vBits ← pure (prValBits prt)
  let paBits ← pure (prPermActBits prt)
  let offQ ← pure (prOffQuot prt)
  let offV ← pure (prOffVal prt)
  let offPA ← pure (prOffPermAct prt)
  let zero_v ← pure 0
  let one_v ← pure 1
  if running = zero_v then
    let _ ← Memory.read base
    pure d.2
  else
    let actBit ← readPackedGenProg (((base, offPA), (paBits, w)), curDest)
    if actBit = one_v then
      let ad ← permEvalActDestProg (d.1, curDest)
      let nxtQ ← readPackedGenProg (((base, offQ), (qBits, w)), curDest)
      let nxtV ← readPackedGenProg (((base, offV), (vBits, w)), curDest)
      writePackedGenProg ((((base, offPA), (paBits, w)), curDest), zero_v)
      writePackedGenProg ((((base, offQ), (qBits, w)), curDest), curQ)
      writePackedGenProg ((((base, offV), (vBits, w)), curDest), curV)
      pure ((one_v, ad.2), (nxtQ, nxtV))
    else
      writePackedGenProg ((((base, offQ), (qBits, w)), curDest), curQ)
      writePackedGenProg ((((base, offV), (vBits, w)), curDest), curV)
      pure ((zero_v, curDest), (curQ, curV))

private theorem memoryCost_permInnerStep_pos
    (d : (PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    0 < memoryCost (permInnerStepProg d) s := by
  unfold permInnerStepProg
  simp only [pure_bind]
  split_ifs with hr
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change 0 < 1 + 0
    omega
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change 0 < 2 + _
    omega

/-- Precondition for `permInnerStepProg` (`curDest < prNMax prt`). -/
@[expose] def PermInnerStepPre (w : ℕ)
    (d : (PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (_s : Memory.State) : Prop :=
  PermRtEnvGen w d.1.1 ∧ d.2.1.2 < prNMax d.1.1

theorem realizes_permInnerStep :
    Realizes .exact permInnerStepProg
      (WordEncoding.encode (α := (PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      PermInnerStepPre
      (fun _ _ => 0) := by
  unfold permInnerStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hpe := realizes_permEvalActDest
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨prt, mode⟩, ⟨running, curDest⟩, curQ, curV⟩
    try clear hwords hmem
    dsimp only [PermInnerStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_prt⟩, hcd_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    generalize prBase prt = base at henv heq_prt
    subst heq_prt
    dsimp only [mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
      prOffQuot, prOffVal, prOffPermAct] at *
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | (have := henv.fits_hdr_addr (off := 0) (by decide); simpa using this)
    | exact ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hcd_lt⟩
    | (apply to_true_exists (w := w); exact pr_act_safe henv curDest hcd_lt)
    | (apply to_true_exists (w := w); exact pr_quot_safe henv curDest hcd_lt)
    | (apply to_true_exists (w := w); exact pr_val_safe henv curDest hcd_lt)
  )

/-- `iterate` wrapper for `permInnerStepProg` (`permuteInnerLoop`). -/
@[irreducible] def permInnerLoopProg
    (p : ((PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ) : Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ)) :=
  iterate permInnerStepProg p.1.1 p.2 p.1.2

theorem realizes_permInnerLoop :
    Realizes .exact permInnerLoopProg
      (WordEncoding.encode (α := ((PermRt × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun w p s => iterationSafe permInnerStepProg PermInnerStepPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold permInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := PermRt × ℕ))
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    realizes_permInnerStep
    memoryCost_permInnerStep_pos

/-- Unconditional `iterationSafe` + `ValidWhpProg` for `permInnerLoopProg` from any
`curDest < n_max`. -/
private theorem permInnerLoop_safe_and_valid {c U V w n_max base mode : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let prt := mkPermRt c U V w n_max base
    ∀ k st (s : Memory.State),
      st.1.2 < n_max →
      let prog := permInnerLoopProg (((prt, mode), st), k)
      iterationSafe permInnerStepProg PermInnerStepPre w (prt, mode) k st s ∧
      ((Memory.spec 0).clientResult s prog).1.2 < n_max ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro prt k
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, hpa_w, hqk_w, hvk_w, _⟩ := perm_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.1 _
  have hv_b : base + offValWhp c U w n_max +
      packedWords n_max (valBits V) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.1 _
  have hpa_b : base + offPermAct c U V w n_max +
      packedWords n_max (12 * ellWhp n_max + 4) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.1 _
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by
      change hdrWordsWhp ≤ _; unfold largeSpaceWhp; omega
    omega
  induction k with
  | zero =>
    intro st s hcd
    unfold permInnerLoopProg
    exact ⟨trivial, hcd, validWhpProg_pure _⟩
  | succ k ih =>
    intro ⟨⟨running, curDest⟩, curQ, curV⟩ s hcd
    have hpre : PermInnerStepPre w ((prt, mode), ((running, curDest), (curQ, curV))) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hcd⟩
    have hstep :
        let p1 := permInnerStepProg ((prt, mode), ((running, curDest), (curQ, curV)))
        ((Memory.spec 0).clientResult s p1).1.2 < n_max ∧
        ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      unfold permInnerStepProg
      dsimp only [prt, mkPermRt, prBase, prW, prQuotBits, prValBits, prPermActBits,
        prOffQuot, prOffVal, prOffPermAct]
      simp only [pure_bind]
      by_cases hr : running = 0
      · simp only [hr, ↓reduceIte]
        exact ⟨hcd, validWhpProg_bind (validWhpProg_read hbase_lt) (validWhpProg_pure _)⟩
      · simp only [hr, ↓reduceIte]
        have hr_pa := validWhpProg_readPacked (s := s) hw hcd hpa_b
        by_cases ha : readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
            s.mem curDest = 1
        · obtain ⟨hpe_st, hpe_lt, hpe_vp⟩ :=
            permEvalActDestProg_invariant (mode := mode) henv hcd (s := s)
          dsimp only [mkPermRt] at hpe_st hpe_lt hpe_vp
          refine ⟨?_, ?_⟩
          · rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
            simp only [ha, ↓reduceIte]
            rw [clientResult_bind_rw, hpe_st,
              clientResult_bind_rw, clientState_readPackedGen,
              clientResult_bind_rw, clientState_readPackedGen,
              clientResult_bind_rw, clientResult_bind_rw, clientResult_bind_rw,
              StateTransitionSpec.clientResult_pure]
            exact hpe_lt
          · refine validWhpProg_bind hr_pa ?_
            rw [clientState_readPackedGen, clientResult_readPackedGen]
            simp only [ha, ↓reduceIte]
            refine validWhpProg_bind hpe_vp ?_
            rw [hpe_st]
            refine validWhpProg_bind (validWhpProg_readPacked hw hcd hq_b) ?_
            rw [clientState_readPackedGen]
            refine validWhpProg_bind (validWhpProg_readPacked hw hcd hv_b) ?_
            rw [clientState_readPackedGen]
            refine validWhpProg_bind (validWhpProg_writePacked hw hpa_w hcd hpa_b) ?_
            refine validWhpProg_bind (validWhpProg_writePacked hw hqk_w hcd hq_b) ?_
            refine validWhpProg_bind (validWhpProg_writePacked hw hvk_w hcd hv_b) ?_
            exact validWhpProg_pure _
        · refine ⟨?_, ?_⟩
          · rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
            simp only [ha, ↓reduceIte]
            rw [clientResult_bind_rw, clientResult_bind_rw,
              StateTransitionSpec.clientResult_pure]
            exact hcd
          · refine validWhpProg_bind hr_pa ?_
            rw [clientState_readPackedGen, clientResult_readPackedGen]
            simp only [ha, ↓reduceIte]
            refine validWhpProg_bind (validWhpProg_writePacked hw hqk_w hcd hq_b) ?_
            refine validWhpProg_bind (validWhpProg_writePacked hw hvk_w hcd hv_b) ?_
            exact validWhpProg_pure _
    set p1 := permInnerStepProg ((prt, mode), ((running, curDest), (curQ, curV)))
    obtain ⟨hcd1, hvp1⟩ := hstep
    obtain ⟨hsafe_k, hcd_k, hvp_k⟩ :=
      ih ((Memory.spec 0).clientResult s p1) ((Memory.spec 0).clientState s p1) hcd1
    unfold permInnerLoopProg at hcd_k hvp_k ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_⟩
    · rw [clientState_width, clientResult_width]
      exact hsafe_k
    · change ((Memory.spec 0).clientResult s
        (p1 >>= fun s' => iterate permInnerStepProg (prt, mode) k s')).1.2 < n_max
      rw [clientResult_bind_rw]
      exact hcd_k
    · exact validWhpProg_bind hvp1 hvp_k

/-- Outer step of `permuteOuterLoop` at slot `idx` (`d = ((prt, mode), idx)`). -/
@[irreducible] def permOuterStepProg (d : (PermRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let prt := d.1.1
  let idx ← pure d.2
  let base ← pure (prBase prt)
  let w ← pure (prW prt)
  let nMax ← pure (prNMax prt)
  let qBits ← pure (prQuotBits prt)
  let vBits ← pure (prValBits prt)
  let paBits ← pure (prPermActBits prt)
  let offQ ← pure (prOffQuot prt)
  let offV ← pure (prOffVal prt)
  let offPA ← pure (prOffPermAct prt)
  let zero_v ← pure 0
  let one_v ← pure 1
  let actBit ← readPackedGenProg (((base, offPA), (paBits, w)), idx)
  if actBit = one_v then
    let ad ← permEvalActDestProg d
    let q0 ← readPackedGenProg (((base, offQ), (qBits, w)), idx)
    let v0 ← readPackedGenProg (((base, offV), (vBits, w)), idx)
    writePackedGenProg ((((base, offPA), (paBits, w)), idx), zero_v)
    let _ ← permInnerLoopProg (((d.1, ((one_v, ad.2), (q0, v0))), nMax))
    pure (idx + one_v)
  else
    pure (idx + one_v)

private theorem memoryCost_permOuterStep_pos (d : (PermRt × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (permOuterStepProg d) s := by
  unfold permOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

theorem realizes_permOuterStep :
    Realizes .exact permOuterStepProg
      (WordEncoding.encode (α := (PermRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PermEvalPre
      (fun _ _ => 0) := by
  unfold permOuterStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hpe := realizes_permEvalActDest
  have hil := realizes_permInnerLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨prt, mode⟩, idx⟩
    try clear hwords hmem
    dsimp only [PermEvalPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_prt⟩, hidx_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    generalize prBase prt = base at henv heq_prt
    subst heq_prt
    dsimp only [mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
      prOffQuot, prOffVal, prOffPermAct] at *
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hidx_lt⟩
    | (apply to_true_exists (w := w); exact pr_act_safe henv idx hidx_lt)
    | (apply to_true_exists (w := w); exact pr_quot_safe henv idx hidx_lt)
    | (apply to_true_exists (w := w); exact pr_val_safe henv idx hidx_lt)
    | (have hlt_pe : ((Memory.spec 0).clientResult s
           (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), idx))).2 < n_max :=
         (permEvalActDestProg_invariant henv hidx_lt).2.1
       dsimp only [mkPermRt] at hlt_pe
       exact (permInnerLoop_safe_and_valid henv n_max _ _ hlt_pe).1)
  )

/-- `iterate` wrapper for `permOuterStepProg` (`permuteOuterLoop`). -/
@[irreducible] def permOuterLoopProg (p : ((PermRt × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate permOuterStepProg p.1.1 p.2 p.1.2

theorem realizes_permOuterLoop :
    Realizes .exact permOuterLoopProg
      (WordEncoding.encode (α := ((PermRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w p s => iterationSafe permOuterStepProg PermEvalPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold permOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := PermRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_permOuterStep
    memoryCost_permOuterStep_pos

/-- Complete in-place `permuteByTarget` in `Memory.Prog` (`d = (prt, mode)`). -/
@[irreducible] def permuteByTargetProg (d : PermRt × ℕ) : Memory.Prog Unit := do
  let nMax ← pure (prNMax d.1)
  let zero_v ← pure 0
  let _ ← permInitActLoopProg ((d, zero_v), nMax)
  let _ ← permOuterLoopProg ((d, zero_v), nMax)
  pure ()

private theorem permInitActLoop_safe {c U V w n_max base mode : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let prt := mkPermRt c U V w n_max base
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ n_max →
      iterationSafe permInitActStepProg PermEvalPre w (prt, mode) rem k₀ s ∧
      ((Memory.spec 0).clientResult s (permInitActLoopProg (((prt, mode), k₀), rem))) =
        k₀ + rem := by
  intro prt rem
  induction rem with
  | zero =>
    intro k₀ _ _
    unfold permInitActLoopProg iterate
    exact ⟨trivial, (Nat.add_zero k₀).symm⟩
  | succ rem ih =>
    intro k₀ s hle
    have hk_lt : k₀ < n_max := by omega
    have hpre : PermEvalPre w ((prt, mode), k₀) s := ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hk_lt⟩
    have hres1 : (Memory.spec 0).clientResult s (permInitActStepProg ((prt, mode), k₀)) =
        k₀ + 1 := by
      unfold permInitActStepProg
      simp only [pure_bind, clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
    obtain ⟨hsafe_r, hres_r⟩ :=
      ih (k₀ + 1) ((Memory.spec 0).clientState s (permInitActStepProg ((prt, mode), k₀))) (by omega)
    refine ⟨⟨hpre, ?_⟩, ?_⟩
    · rw [clientState_width, clientResult_width, hres1]
      exact hsafe_r
    · unfold permInitActLoopProg at hres_r ⊢
      change (Memory.spec 0).clientResult s (permInitActStepProg ((prt, mode), k₀) >>= _) = _
      rw [clientResult_bind_rw, hres1, hres_r]
      omega

private theorem permOuterLoop_safe {c U V w n_max base mode : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let prt := mkPermRt c U V w n_max base
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ n_max →
      iterationSafe permOuterStepProg PermEvalPre w (prt, mode) rem k₀ s ∧
      ((Memory.spec 0).clientResult s (permOuterLoopProg (((prt, mode), k₀), rem))) =
        k₀ + rem := by
  intro prt rem
  induction rem with
  | zero =>
    intro k₀ _ _
    unfold permOuterLoopProg iterate
    exact ⟨trivial, (Nat.add_zero k₀).symm⟩
  | succ rem ih =>
    intro k₀ s hle
    have hk_lt : k₀ < n_max := by omega
    have hpre : PermEvalPre w ((prt, mode), k₀) s := ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hk_lt⟩
    have hres1 : (Memory.spec 0).clientResult s (permOuterStepProg ((prt, mode), k₀)) =
        k₀ + 1 := by
      unfold permOuterStepProg
      simp only [pure_bind, clientResult_bind_rw]
      split_ifs <;>
        simp only [clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
    obtain ⟨hsafe_r, hres_r⟩ :=
      ih (k₀ + 1) ((Memory.spec 0).clientState s (permOuterStepProg ((prt, mode), k₀))) (by omega)
    refine ⟨⟨hpre, ?_⟩, ?_⟩
    · rw [clientState_width, clientResult_width, hres1]
      exact hsafe_r
    · unfold permOuterLoopProg at hres_r ⊢
      change (Memory.spec 0).clientResult s (permOuterStepProg ((prt, mode), k₀) >>= _) = _
      rw [clientResult_bind_rw, hres1, hres_r]
      omega

theorem realizes_permuteByTarget :
    Realizes .exact permuteByTargetProg
      (WordEncoding.encode (α := PermRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => PermRtEnvGen w d.1)
      (fun _ _ => 0) := by
  unfold permuteByTargetProg
  have hia := realizes_permInitActLoop
  have hol := realizes_permOuterLoop
  realize
  all_goals (
    rcases d with ⟨prt, mode⟩
    try clear hwords hmem
    obtain ⟨c, U, V, w₀, n_max, henv, heq_prt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hN_eq : prt.1.2.1 = n_max := congrArg prNMax heq_prt
    dsimp only [prNMax] at *
    rw [heq_prt]
    first
    | exact (permInitActLoop_safe henv n_max 0 s (by omega)).1
    | exact (permOuterLoop_safe henv n_max 0 _ (by omega)).1
  )

section PermuteSpec

private theorem perm_seg_disjoint (c U V w n_max : ℕ) :
    offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w = offValWhp c U w n_max ∧
    offValWhp c U w n_max + packedWords n_max (valBits V) w = offPermAct c U V w n_max ∧
    offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w =
      offLocState c U V w n_max :=
  ⟨rfl, rfl, rfl⟩

private def PermTripleMem (base c U V w n_max : ℕ) (act : ℕ → Bool) (qArr vArr : ℕ → ℕ)
    (mem₀ mem : ℕ → ℕ) : Prop :=
  (∀ i < n_max,
    readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w mem i =
      if act i then 1 else 0) ∧
  (∀ i < n_max,
    readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w mem i = qArr i ∧
    qArr i < 2 ^ quotBitsWhp U n_max) ∧
  (∀ i < n_max,
    readPacked (base + offValWhp c U w n_max) (valBits V) w mem i = vArr i ∧
    vArr i < 2 ^ valBits V) ∧
  (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
    mem a = mem₀ a)

private theorem permInitActLoop_spec {c U V w n_max base mode : ℕ}
    {act₀ : ℕ → Bool} {qArr vArr : ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (_hq : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem i = qArr i ∧
      qArr i < 2 ^ quotBitsWhp U n_max)
    (_hv : ∀ i < n_max,
      readPacked (base + offValWhp c U w n_max) (valBits V) w s₀.mem i = vArr i ∧
      vArr i < 2 ^ valBits V)
    (heval : ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x))).1 =
        (if act₀ x then 1 else 0)) :
    let prt := mkPermRt c U V w n_max base
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ n_max →
      (∀ i < k₀,
        readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w s.mem i =
          if act₀ i then 1 else 0) →
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i = qArr i) →
      (∀ i < n_max,
        readPacked (base + offValWhp c U w n_max) (valBits V) w s.mem i = vArr i) →
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := permInitActLoopProg (((prt, mode), k₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      (∀ i < k₀ + rem,
        readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w s'.mem i =
          if act₀ i then 1 else 0) ∧
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s'.mem i = qArr i) ∧
      (∀ i < n_max,
        readPacked (base + offValWhp c U w n_max) (valBits V) w s'.mem i = vArr i) ∧
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro prt rem
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, hpa_w, _, _, _⟩ := perm_bounds henv
  have hdisj := perm_seg_disjoint c U V w n_max
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hpa_b : base + offPermAct c U V w n_max +
      packedWords n_max (12 * ellWhp n_max + 4) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.1 _
  have hbit_lt : ∀ b : Bool, (if b then 1 else 0) < 2 ^ (12 * ellWhp n_max + 4) := by
    intro b; cases b <;> simp
  induction rem with
  | zero =>
    intro k₀ s _ hact hqr hvr hout
    unfold permInitActLoopProg iterate
    have hs' : (Memory.spec 0).clientState s (pure k₀) = s := rfl
    dsimp only
    rw [hs']
    exact ⟨hact, hqr, hvr, hout, rfl, validWhpProg_pure _⟩
  | succ rem ih =>
    intro k₀ s hle hact hqr hvr hout
    have hk_lt : k₀ < n_max := by omega
    obtain ⟨hpe_st, _, hpe_vp⟩ := permEvalActDestProg_invariant (mode := mode) henv hk_lt (s := s)
    have had1 := heval k₀ hk_lt s hout
    set p1 := permInitActStepProg ((prt, mode), k₀)
    have hs1 : (Memory.spec 0).clientState s p1 =
        { mem := writePacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w s.mem
            k₀ (if act₀ k₀ then 1 else 0)
          frontier := s.frontier } := by
      dsimp only [p1]; unfold permInitActStepProg
      dsimp only [prt, mkPermRt, prBase, prOffPermAct, prPermActBits, prW]
      simp only [pure_bind]
      dsimp only [mkPermRt] at hpe_st had1
      rw [clientState_bind_rw, hpe_st, had1, clientState_bind_rw]
      rfl
    have hr1 : (Memory.spec 0).clientResult s p1 = k₀ + 1 := by
      dsimp only [p1]; unfold permInitActStepProg
      simp only [pure_bind, clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold permInitActStepProg
      simp only [pure_bind]
      refine validWhpProg_bind hpe_vp ?_
      rw [hpe_st]
      exact validWhpProg_bind (validWhpProg_writePacked hw hpa_w hk_lt hpa_b)
        (validWhpProg_pure _)
    set s1 := (Memory.spec 0).clientState s p1
    have hact1 : ∀ i < k₀ + 1,
        readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w s1.mem i =
          if act₀ i then 1 else 0 := by
      intro i hi
      rw [hs1]; dsimp only
      by_cases heq : i = k₀
      · subst heq
        exact readPacked_writePacked_self _ _ _ _ _ (hbit_lt _)
      · rw [readPacked_writePacked_of_ne hw s.mem heq _]
        exact hact i (by omega)
    have hqr1 : ∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s1.mem i = qArr i := by
      intro i hi
      rw [hs1]; dsimp only
      rw [readPacked_writePacked_disjoint hw hi hk_lt (Or.inl (by omega))]
      exact hqr i hi
    have hvr1 : ∀ i < n_max,
        readPacked (base + offValWhp c U w n_max) (valBits V) w s1.mem i = vArr i := by
      intro i hi
      rw [hs1]; dsimp only
      rw [readPacked_writePacked_disjoint hw hi hk_lt (Or.inl (by omega))]
      exact hvr i hi
    have hout1 : ∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha
      rw [hs1]; dsimp only
      rw [mem_writePacked_of_outside hw hk_lt (by omega)]
      exact hout a ha
    obtain ⟨ha_r, hq_r, hv_r, ho_r, hf_r, hvp_r⟩ :=
      ih (k₀ + 1) s1 (by omega) hact1 hqr1 hvr1 hout1
    unfold permInitActLoopProg at ha_r hq_r hv_r ho_r hf_r hvp_r ⊢
    dsimp only [iterate]
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ ValidWhpProg _ _ s (p1 >>= _)
    have hst_eq : (Memory.spec 0).clientState s
        (p1 >>= fun s' => iterate permInitActStepProg (prt, mode) rem s') =
        (Memory.spec 0).clientState s1 (iterate permInitActStepProg (prt, mode) rem (k₀ + 1)) := by
      rw [clientState_bind_rw, hr1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; rw [hst_eq]; exact ha_r i (by omega)
    · intro i hi; rw [hst_eq]; exact hq_r i hi
    · intro i hi; rw [hst_eq]; exact hv_r i hi
    · intro a ha; rw [hst_eq]; exact ho_r a ha
    · rw [hst_eq, hf_r, hs1]
    · refine validWhpProg_bind hvp1 ?_
      rw [hr1]; exact hvp_r

private theorem permInnerLoop_spec {c U V w n_max base mode : ℕ}
    {act₀ : ℕ → Bool} {dest : ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (heval : ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) →
      act₀ x = true →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x))).2 = dest x ∧
      dest x < n_max) :
    let prt := mkPermRt c U V w n_max base
    ∀ k (st : PermChainState) (s : Memory.State),
      let (running, curDest, curQ, curV, act, q, v) := st
      PermTripleMem base c U V w n_max act q v s₀.mem s.mem →
      (∀ i, act i = true → i < n_max ∧ act₀ i = true) →
      curDest < n_max →
      curQ < 2 ^ quotBitsWhp U n_max →
      curV < 2 ^ valBits V →
      let prog := permInnerLoopProg
        (((prt, mode), ((if running then 1 else 0, curDest), (curQ, curV))), k)
      let s' := (Memory.spec 0).clientState s prog
      let st' := permuteInnerLoop dest k st
      PermTripleMem base c U V w n_max st'.2.2.2.2.1 st'.2.2.2.2.2.1 st'.2.2.2.2.2.2
        s₀.mem s'.mem ∧
      (∀ i, st'.2.2.2.2.1 i = true → i < n_max ∧ act₀ i = true) ∧
      s'.frontier = s.frontier := by
  intro prt k
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, hpa_w, hqk_w, hvk_w, _⟩ := perm_bounds henv
  have hdisj := perm_seg_disjoint c U V w n_max
  have h0_lt : 0 < 2 ^ (12 * ellWhp n_max + 4) := Nat.two_pow_pos _
  induction k with
  | zero =>
    intro ⟨running, curDest, curQ, curV, act, q, v⟩ s htm hinv _ _ _
    unfold permInnerLoopProg iterate
    exact ⟨htm, hinv, rfl⟩
  | succ k ih =>
    intro ⟨running, curDest, curQ, curV, act, q, v⟩ s htm hinv hcd hcq hcv
    set runBit := if running then 1 else 0
    set p1 := permInnerStepProg ((prt, mode), ((runBit, curDest), (curQ, curV)))
    cases running with
    | false =>
      have hs1 : (Memory.spec 0).clientState s p1 = s := by
        dsimp only [p1, runBit]; unfold permInnerStepProg; simp [pure_bind]; rfl
      have hr1 : (Memory.spec 0).clientResult s p1 = ((0, curDest), (curQ, curV)) := by
        dsimp only [p1, runBit]; unfold permInnerStepProg; simp [pure_bind]; rfl
      obtain ⟨htm', hinv', hf'⟩ :=
        ih (false, curDest, curQ, curV, act, q, v) s htm hinv hcd hcq hcv
      unfold permInnerLoopProg at htm' hf' ⊢
      dsimp only [iterate, permuteInnerLoop]
      have hstep_p : permuteInnerStep dest (false, curDest, curQ, curV, act, q, v) =
          (false, curDest, curQ, curV, act, q, v) := rfl
      have hst_eq : (Memory.spec 0).clientState s
          (p1 >>= fun s' => iterate permInnerStepProg (prt, mode) k s') =
          (Memory.spec 0).clientState s
            (iterate permInnerStepProg (prt, mode) k ((0, curDest), (curQ, curV))) := by
        rw [clientState_bind_rw, hs1, hr1]
      rw [hstep_p, hst_eq]
      exact ⟨htm', hinv', hf'⟩
    | true =>
      have hpa_cd := htm.1 curDest hcd
      by_cases ha : act curDest = true
      · obtain ⟨_, ha0⟩ := hinv curDest ha
        obtain ⟨had2_eq, hdest_lt⟩ := heval curDest hcd s htm.2.2.2 ha0
        obtain ⟨hpe_st, _, _⟩ := permEvalActDestProg_invariant (mode := mode) henv hcd (s := s)
        dsimp only [mkPermRt] at hpe_st had2_eq
        have hpa1 : readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
            s.mem curDest = 1 := by simpa [ha] using hpa_cd
        set m1 := writePacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
          s.mem curDest 0
        set m2 := writePacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w m1 curDest curQ
        set m3 := writePacked (base + offValWhp c U w n_max) (valBits V) w m2 curDest curV
        have hs1 : (Memory.spec 0).clientState s p1 = { mem := m3, frontier := s.frontier } := by
          dsimp only [p1, runBit]; unfold permInnerStepProg
          dsimp only [prt, mkPermRt, prBase, prW, prQuotBits, prValBits, prPermActBits,
            prOffQuot, prOffVal, prOffPermAct]
          simp only [pure_bind, ↓reduceIte, Nat.one_ne_zero]
          rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
          simp only [hpa1, ↓reduceIte]
          rw [clientState_bind_rw, hpe_st,
            clientState_bind_rw, clientState_readPackedGen,
            clientState_bind_rw, clientState_readPackedGen,
            clientState_bind_rw, clientState_bind_rw, clientState_bind_rw]
          rfl
        have hr1 : (Memory.spec 0).clientResult s p1 =
            ((1, dest curDest), (q curDest, v curDest)) := by
          dsimp only [p1, runBit]; unfold permInnerStepProg
          dsimp only [prt, mkPermRt, prBase, prW, prQuotBits, prValBits, prPermActBits,
            prOffQuot, prOffVal, prOffPermAct]
          simp only [pure_bind, ↓reduceIte, Nat.one_ne_zero]
          rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
          simp only [hpa1, ↓reduceIte]
          rw [clientResult_bind_rw, hpe_st, had2_eq,
            clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
            clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
            (htm.2.1 curDest hcd).1, (htm.2.2.1 curDest hcd).1,
            clientResult_bind_rw, clientResult_bind_rw, clientResult_bind_rw,
            StateTransitionSpec.clientResult_pure]
        have htm1 : PermTripleMem base c U V w n_max
            (Function.update act curDest false)
            (Function.update q curDest curQ)
            (Function.update v curDest curV)
            s₀.mem m3 := by
          refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a ha_out => ?_⟩
          · dsimp only [m3, m2, m1]
            rw [readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega)),
              readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega))]
            by_cases heq : i = curDest
            · subst heq; simp [readPacked_writePacked_self _ _ _ _ _ h0_lt]
            · rw [readPacked_writePacked_of_ne hw s.mem heq 0, Function.update_of_ne heq,
                htm.1 i hi]
          · dsimp only [m3, m2, m1]
            rw [readPacked_writePacked_disjoint hw hi hcd (Or.inl (by omega))]
            by_cases heq : i = curDest
            · subst heq
              simp [readPacked_writePacked_self _ _ _ _ _ hcq, hcq]
            · rw [readPacked_writePacked_of_ne hw m1 heq curQ,
                readPacked_writePacked_disjoint hw hi hcd (Or.inl (by omega)),
                Function.update_of_ne heq]
              exact htm.2.1 i hi
          · dsimp only [m3, m2, m1]
            by_cases heq : i = curDest
            · subst heq
              simp [readPacked_writePacked_self _ _ _ _ _ hcv, hcv]
            · rw [readPacked_writePacked_of_ne hw m2 heq curV,
                readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega)),
                readPacked_writePacked_disjoint hw hi hcd (Or.inl (by omega)),
                Function.update_of_ne heq]
              exact htm.2.2.1 i hi
          · dsimp only [m3, m2, m1]
            rw [mem_writePacked_of_outside hw hcd (by omega),
              mem_writePacked_of_outside hw hcd (by omega),
              mem_writePacked_of_outside hw hcd (by omega)]
            exact htm.2.2.2 a ha_out
        have hinv1 : ∀ i, Function.update act curDest false i = true →
            i < n_max ∧ act₀ i = true := by
          intro i hi
          by_cases heq : i = curDest
          · subst heq; simp at hi
          · rw [Function.update_of_ne heq] at hi; exact hinv i hi
        obtain ⟨htm', hinv', hf'⟩ := ih
          (true, dest curDest, q curDest, v curDest,
            Function.update act curDest false,
            Function.update q curDest curQ,
            Function.update v curDest curV)
          { mem := m3, frontier := s.frontier }
          htm1 hinv1 hdest_lt (htm.2.1 curDest hcd).2 (htm.2.2.1 curDest hcd).2
        unfold permInnerLoopProg at htm' hf' ⊢
        dsimp only [iterate, permuteInnerLoop]
        have hstep_p : permuteInnerStep dest (true, curDest, curQ, curV, act, q, v) =
            (true, dest curDest, q curDest, v curDest,
              Function.update act curDest false,
              Function.update q curDest curQ,
              Function.update v curDest curV) := by simp [permuteInnerStep, ha]
        have hst_eq : (Memory.spec 0).clientState s
            (p1 >>= fun s' => iterate permInnerStepProg (prt, mode) k s') =
            (Memory.spec 0).clientState { mem := m3, frontier := s.frontier }
              (iterate permInnerStepProg (prt, mode) k
                ((1, dest curDest), (q curDest, v curDest))) := by
          rw [clientState_bind_rw, hs1, hr1]
        rw [hstep_p, hst_eq]
        exact ⟨htm', hinv', hf'⟩
      · have haf : act curDest = false := by revert ha; cases act curDest <;> simp
        have hpa0 : readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
            s.mem curDest = 0 := by simpa [haf] using hpa_cd
        set m2 := writePacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
          s.mem curDest curQ
        set m3 := writePacked (base + offValWhp c U w n_max) (valBits V) w m2 curDest curV
        have hs1 : (Memory.spec 0).clientState s p1 = { mem := m3, frontier := s.frontier } := by
          dsimp only [p1, runBit]; unfold permInnerStepProg
          dsimp only [prt, mkPermRt, prBase, prW, prQuotBits, prValBits, prPermActBits,
            prOffQuot, prOffVal, prOffPermAct]
          simp only [pure_bind, ↓reduceIte, Nat.one_ne_zero]
          rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
          simp only [hpa0, Nat.zero_ne_one, ↓reduceIte]
          rw [clientState_bind_rw, clientState_bind_rw]
          rfl
        have hr1 : (Memory.spec 0).clientResult s p1 = ((0, curDest), (curQ, curV)) := by
          dsimp only [p1, runBit]; unfold permInnerStepProg
          dsimp only [prt, mkPermRt, prBase, prW, prQuotBits, prValBits, prPermActBits,
            prOffQuot, prOffVal, prOffPermAct]
          simp only [pure_bind, ↓reduceIte, Nat.one_ne_zero]
          rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
          simp only [hpa0, Nat.zero_ne_one, ↓reduceIte]
          rw [clientResult_bind_rw, clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
        have htm1 : PermTripleMem base c U V w n_max act
            (Function.update q curDest curQ)
            (Function.update v curDest curV)
            s₀.mem m3 := by
          refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a ha_out => ?_⟩
          · dsimp only [m3, m2]
            rw [readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega)),
              readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega))]
            exact htm.1 i hi
          · dsimp only [m3, m2]
            rw [readPacked_writePacked_disjoint hw hi hcd (Or.inl (by omega))]
            by_cases heq : i = curDest
            · subst heq; simp [readPacked_writePacked_self _ _ _ _ _ hcq, hcq]
            · rw [readPacked_writePacked_of_ne hw s.mem heq curQ, Function.update_of_ne heq]
              exact htm.2.1 i hi
          · dsimp only [m3, m2]
            by_cases heq : i = curDest
            · subst heq; simp [readPacked_writePacked_self _ _ _ _ _ hcv, hcv]
            · rw [readPacked_writePacked_of_ne hw m2 heq curV,
                readPacked_writePacked_disjoint hw hi hcd (Or.inr (by omega)),
                Function.update_of_ne heq]
              exact htm.2.2.1 i hi
          · dsimp only [m3, m2]
            rw [mem_writePacked_of_outside hw hcd (by omega),
              mem_writePacked_of_outside hw hcd (by omega)]
            exact htm.2.2.2 a ha_out
        obtain ⟨htm', hinv', hf'⟩ := ih
          (false, curDest, curQ, curV, act,
            Function.update q curDest curQ, Function.update v curDest curV)
          { mem := m3, frontier := s.frontier }
          htm1 hinv hcd hcq hcv
        unfold permInnerLoopProg at htm' hf' ⊢
        dsimp only [iterate, permuteInnerLoop]
        have hstep_p : permuteInnerStep dest (true, curDest, curQ, curV, act, q, v) =
            (false, curDest, curQ, curV, act,
              Function.update q curDest curQ, Function.update v curDest curV) := by
          simp [permuteInnerStep, haf]
        have hst_eq : (Memory.spec 0).clientState s
            (p1 >>= fun s' => iterate permInnerStepProg (prt, mode) k s') =
            (Memory.spec 0).clientState { mem := m3, frontier := s.frontier }
              (iterate permInnerStepProg (prt, mode) k ((0, curDest), (curQ, curV))) := by
          rw [clientState_bind_rw, hs1, hr1]
        rw [hstep_p, hst_eq]
        exact ⟨htm', hinv', hf'⟩

private theorem permOuterLoop_spec {c U V w n_max base mode : ℕ}
    {act₀ : ℕ → Bool} {dest qArr vArr : ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (heval : ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) →
      act₀ x = true →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x))).2 = dest x ∧
      dest x < n_max) :
    let prt := mkPermRt c U V w n_max base
    let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ n_max →
      PermTripleMem base c U V w n_max
        (permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr)).1
        (permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr)).2.1
        (permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr)).2.2 s₀.mem s.mem →
      (∀ i, (permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr)).1 i = true →
        i < n_max ∧ act₀ i = true) →
      let prog := permOuterLoopProg (((prt, mode), k₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      let fin := permuteOuterLoop n_max dest (k₀ + rem) (actInit, qArr, vArr)
      PermTripleMem base c U V w n_max fin.1 fin.2.1 fin.2.2 s₀.mem s'.mem ∧
      (∀ i, fin.1 i = true → i < n_max ∧ act₀ i = true) ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro prt actInit rem
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, hpa_w, hqk_w, hvk_w, _⟩ := perm_bounds henv
  have hdisj := perm_seg_disjoint c U V w n_max
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.1 _
  have hv_b : base + offValWhp c U w n_max +
      packedWords n_max (valBits V) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.1 _
  have hpa_b : base + offPermAct c U V w n_max +
      packedWords n_max (12 * ellWhp n_max + 4) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.1 _
  have h0_lt : 0 < 2 ^ (12 * ellWhp n_max + 4) := Nat.two_pow_pos _
  induction rem with
  | zero =>
    intro k₀ s _ htm hinv
    unfold permOuterLoopProg iterate
    have hs' : (Memory.spec 0).clientState s (pure k₀) = s := rfl
    dsimp only
    rw [hs']
    exact ⟨htm, hinv, rfl, validWhpProg_pure _⟩
  | succ rem ih =>
    intro k₀ s hle htm hinv
    have hk_lt : k₀ < n_max := by omega
    set cur := permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr)
    rcases hcur : cur with ⟨act, q, v⟩
    have hcur_eq : permuteOuterLoop n_max dest k₀ (actInit, qArr, vArr) = (act, q, v) := hcur
    rw [hcur] at htm hinv
    set p1 := permOuterStepProg ((prt, mode), k₀)
    have hr1 : (Memory.spec 0).clientResult s p1 = k₀ + 1 := by
      dsimp only [p1]; unfold permOuterStepProg
      simp only [pure_bind, clientResult_bind_rw]
      split_ifs <;> simp only [clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
    have hpa_k := htm.1 k₀ hk_lt
    by_cases ha : act k₀ = true
    · obtain ⟨_, ha0⟩ := hinv k₀ ha
      obtain ⟨had2_eq, hdest_lt⟩ := heval k₀ hk_lt s htm.2.2.2 ha0
      obtain ⟨hpe_st, _, hpe_vp⟩ := permEvalActDestProg_invariant (mode := mode) henv hk_lt (s := s)
      dsimp only [mkPermRt] at hpe_st had2_eq
      have hpa1 : readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
          s.mem k₀ = 1 := by simpa [ha] using hpa_k
      set m_clr := writePacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
        s.mem k₀ 0
      set s_clr : Memory.State := { mem := m_clr, frontier := s.frontier }
      have htm_clr : PermTripleMem base c U V w n_max (Function.update act k₀ false) q v
          s₀.mem s_clr.mem := by
        refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a ha_out => ?_⟩
        · dsimp only [s_clr, m_clr]
          by_cases heq : i = k₀
          · subst heq; simp [readPacked_writePacked_self _ _ _ _ _ h0_lt]
          · rw [readPacked_writePacked_of_ne hw s.mem heq, Function.update_of_ne heq, htm.1 i hi]
        · dsimp only [s_clr, m_clr]
          rw [readPacked_writePacked_disjoint hw hi hk_lt (Or.inl (by omega))]
          exact htm.2.1 i hi
        · dsimp only [s_clr, m_clr]
          rw [readPacked_writePacked_disjoint hw hi hk_lt (Or.inl (by omega))]
          exact htm.2.2.1 i hi
        · dsimp only [s_clr, m_clr]
          rw [mem_writePacked_of_outside hw hk_lt (by omega)]
          exact htm.2.2.2 a ha_out
      have hinv_clr : ∀ i, Function.update act k₀ false i = true →
          i < n_max ∧ act₀ i = true := by
        intro i hi
        by_cases heq : i = k₀
        · subst heq; simp at hi
        · rw [Function.update_of_ne heq] at hi; exact hinv i hi
      obtain ⟨htm_in, hinv_in, hf_in⟩ := permInnerLoop_spec (mode := mode) henv heval n_max
        (true, dest k₀, q k₀, v k₀, Function.update act k₀ false, q, v) s_clr
        htm_clr hinv_clr hdest_lt (htm.2.1 k₀ hk_lt).2 (htm.2.2.1 k₀ hk_lt).2
      have hvp_in := (permInnerLoop_safe_and_valid (mode := mode) henv n_max
        ((1, dest k₀), (q k₀, v k₀)) s_clr hdest_lt).2.2
      set s_in := (Memory.spec 0).clientState s_clr
        (permInnerLoopProg (((prt, mode), ((1, dest k₀), (q k₀, v k₀))), n_max))
      have hs1 : (Memory.spec 0).clientState s p1 = s_in := by
        dsimp only [p1]; unfold permOuterStepProg
        dsimp only [prt, mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
          prOffQuot, prOffVal, prOffPermAct]
        simp only [pure_bind]
        rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
        simp only [hpa1, ↓reduceIte]
        rw [clientState_bind_rw, hpe_st, had2_eq,
          clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
          clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen,
          (htm.2.1 k₀ hk_lt).1, (htm.2.2.1 k₀ hk_lt).1,
          clientState_bind_rw, clientState_bind_rw]
        rfl
      have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
        dsimp only [p1]; unfold permOuterStepProg
        dsimp only [prt, mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
          prOffQuot, prOffVal, prOffPermAct]
        simp only [pure_bind]
        refine validWhpProg_bind (validWhpProg_readPacked hw hk_lt hpa_b) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen]
        simp only [hpa1, ↓reduceIte]
        dsimp only [mkPermRt] at hpe_vp hvp_in
        refine validWhpProg_bind hpe_vp ?_
        rw [hpe_st, had2_eq]
        refine validWhpProg_bind (validWhpProg_readPacked hw hk_lt hq_b) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, (htm.2.1 k₀ hk_lt).1]
        refine validWhpProg_bind (validWhpProg_readPacked hw hk_lt hv_b) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, (htm.2.2.1 k₀ hk_lt).1]
        refine validWhpProg_bind (validWhpProg_writePacked hw hpa_w hk_lt hpa_b) ?_
        exact validWhpProg_bind hvp_in (validWhpProg_pure _)
      have hstep_cur : permuteOuterLoop n_max dest (k₀ + 1) (actInit, qArr, vArr) =
          (let (_, _, _, _, act', q', v') :=
             permuteInnerLoop dest n_max
               (true, dest k₀, q k₀, v k₀, Function.update act k₀ false, q, v)
           (act', q', v')) := by
        change permuteOuterStep n_max dest k₀ cur = _
        rw [hcur]
        simp [permuteOuterStep, ha]
      obtain ⟨htm_r, hinv_r, hf_r, hvp_r⟩ := ih (k₀ + 1) s_in (by omega)
        (by rw [hstep_cur]; exact htm_in)
        (by rw [hstep_cur]; exact hinv_in)
      unfold permOuterLoopProg at htm_r hf_r hvp_r ⊢
      dsimp only [iterate]
      have hst_eq : (Memory.spec 0).clientState s
          (p1 >>= fun s' => iterate permOuterStepProg (prt, mode) rem s') =
          (Memory.spec 0).clientState s_in
            (iterate permOuterStepProg (prt, mode) rem (k₀ + 1)) := by
        rw [clientState_bind_rw, hs1, hr1]
      have hadd : k₀ + 1 + rem = k₀ + (rem + 1) := by omega
      rw [hadd] at htm_r hinv_r
      refine ⟨?_, hinv_r, ?_, ?_⟩
      · rw [hst_eq]; exact htm_r
      · rw [hst_eq, hf_r]; exact hf_in
      · change ValidWhpProg _ _ s (p1 >>= _)
        refine validWhpProg_bind hvp1 ?_
        rw [hs1, hr1]; exact hvp_r
    · have haf : act k₀ = false := by revert ha; cases act k₀ <;> simp
      have hpa0 : readPacked (base + offPermAct c U V w n_max) (12 * ellWhp n_max + 4) w
          s.mem k₀ = 0 := by simpa [haf] using hpa_k
      have hs1 : (Memory.spec 0).clientState s p1 = s := by
        dsimp only [p1]; unfold permOuterStepProg
        dsimp only [prt, mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
          prOffQuot, prOffVal, prOffPermAct]
        simp only [pure_bind]
        rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen]
        simp [hpa0]
        rfl
      have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
        dsimp only [p1]; unfold permOuterStepProg
        dsimp only [prt, mkPermRt, prBase, prW, prNMax, prQuotBits, prValBits, prPermActBits,
          prOffQuot, prOffVal, prOffPermAct]
        simp only [pure_bind]
        refine validWhpProg_bind (validWhpProg_readPacked hw hk_lt hpa_b) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen]
        simp only [hpa0, Nat.zero_ne_one, ↓reduceIte]
        exact validWhpProg_pure _
      have hstep_cur : permuteOuterLoop n_max dest (k₀ + 1) (actInit, qArr, vArr) =
          (act, q, v) := by
        change permuteOuterStep n_max dest k₀ cur = _
        rw [hcur]
        simp [permuteOuterStep, haf]
      obtain ⟨htm_r, hinv_r, hf_r, hvp_r⟩ := ih (k₀ + 1) s (by omega)
        (by rw [hstep_cur]; exact htm)
        (by rw [hstep_cur]; exact hinv)
      unfold permOuterLoopProg at htm_r hf_r hvp_r ⊢
      dsimp only [iterate]
      have hst_eq : (Memory.spec 0).clientState s
          (p1 >>= fun s' => iterate permOuterStepProg (prt, mode) rem s') =
          (Memory.spec 0).clientState s
            (iterate permOuterStepProg (prt, mode) rem (k₀ + 1)) := by
        rw [clientState_bind_rw, hs1, hr1]
      have hadd : k₀ + 1 + rem = k₀ + (rem + 1) := by omega
      rw [hadd] at htm_r hinv_r
      refine ⟨?_, hinv_r, ?_, ?_⟩
      · rw [hst_eq]; exact htm_r
      · rw [hst_eq, hf_r]
      · change ValidWhpProg _ _ s (p1 >>= _)
        refine validWhpProg_bind hvp1 ?_
        rw [hs1, hr1]; exact hvp_r

/-- Exact memory specification of `permuteByTargetProg`: rearranges `offQuotWhp` and `offValWhp`
according to `permuteByTarget n_max dest act₀ qArr vArr` while leaving all memory words outside
`[base + offQuotWhp c w n_max, base + offLocState c U V w n_max)` unchanged. -/
theorem permuteByTargetProg_spec {c U V w n_max base mode : ℕ}
    {act₀ : ℕ → Bool} {dest qArr vArr : ℕ → ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hq : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i = qArr i ∧
      qArr i < 2 ^ quotBitsWhp U n_max)
    (hv : ∀ i < n_max,
      readPacked (base + offValWhp c U w n_max) (valBits V) w s.mem i = vArr i ∧
      vArr i < 2 ^ valBits V)
    (heval : ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s.mem a) →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x))).1 =
          (if act₀ x then 1 else 0) ∧
      (act₀ x = true →
        ((Memory.spec 0).clientResult s'
          (permEvalActDestProg ((mkPermRt c U V w n_max base, mode), x))).2 = dest x ∧
        dest x < n_max)) :
    let prog := permuteByTargetProg (mkPermRt c U V w n_max base, mode)
    let s' := (Memory.spec 0).clientState s prog
    let pv := permuteByTarget n_max dest act₀ qArr vArr
    (∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s'.mem i = pv.1 i ∧
      readPacked (base + offValWhp c U w n_max) (valBits V) w s'.mem i = pv.2 i) ∧
    (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
      s'.mem a = s.mem a) ∧
    s'.frontier = s.frontier ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  set prt := mkPermRt c U V w n_max base
  obtain ⟨hia_a, hia_q, hia_v, hia_o, hia_f, hia_vp⟩ := permInitActLoop_spec (mode := mode) henv
    hq hv (fun x hx s' hout => (heval x hx s' hout).1) n_max 0 s (by omega)
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i hi => (hq i hi).1) (fun i hi => (hv i hi).1) (fun _ _ => rfl)
  rw [Nat.zero_add] at hia_a
  set s1 := (Memory.spec 0).clientState s (permInitActLoopProg (((prt, mode), 0), n_max))
  let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
  have htm1 : PermTripleMem base c U V w n_max actInit qArr vArr s.mem s1.mem := by
    refine ⟨fun i hi => ?_, fun i hi => ⟨hia_q i hi, (hq i hi).2⟩,
      fun i hi => ⟨hia_v i hi, (hv i hi).2⟩, hia_o⟩
    dsimp only [actInit]
    simp only [hi, decide_true, Bool.true_and]
    exact hia_a i hi
  have hinv1 : ∀ i, actInit i = true → i < n_max ∧ act₀ i = true := by
    intro i hi
    dsimp only [actInit] at hi
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hi
  obtain ⟨hol_tm, _, hol_f, hol_vp⟩ := permOuterLoop_spec (mode := mode) (qArr := qArr)
    (vArr := vArr) henv (fun x hx s' hout ha0 => (heval x hx s' hout).2 ha0)
    n_max 0 s1 (by omega) htm1 hinv1
  rw [Nat.zero_add] at hol_tm
  set s2 := (Memory.spec 0).clientState s1 (permOuterLoopProg (((prt, mode), 0), n_max))
  have hst_eq : (Memory.spec 0).clientState s (permuteByTargetProg (prt, mode)) = s2 := by
    unfold permuteByTargetProg
    have hN : prNMax prt = n_max := rfl
    simp only [pure_bind, hN]
    rw [clientState_bind_rw, clientState_bind_rw]
    rfl
  refine ⟨fun i hi => ?_, fun a ha => ?_, ?_, ?_⟩
  · rw [hst_eq]
    exact ⟨(hol_tm.2.1 i hi).1, (hol_tm.2.2.1 i hi).1⟩
  · rw [hst_eq]; exact hol_tm.2.2.2 a ha
  · rw [hst_eq, hol_f, hia_f]
  · unfold permuteByTargetProg
    have hN : prNMax prt = n_max := rfl
    simp only [pure_bind, hN]
    refine validWhpProg_bind hia_vp ?_
    exact validWhpProg_bind hol_vp (validWhpProg_pure _)

end PermuteSpec

/-! ## Section 3: `fastToCsrGenProg` (`FastMemRep → CsrMemRep`) -/

/-- Step computing `fbStart[b + 1] := acc + bktCount[b]` (`d = (prt, (b, acc))`). -/
@[irreducible] def fbPrefixStepProg (d : PermRt × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let prt := d.1
  let b ← pure d.2.1
  let acc ← pure d.2.2
  let base ← pure (prBase prt)
  let w ← pure (prW prt)
  let nMax ← pure (prNMax prt)
  let gBits ← pure (prGBits prt)
  let offBm ← pure (prOffBktMeta prt)
  let offFb ← pure (prOffFbStart prt)
  let one_v ← pure 1
  let idxCnt ← pure (16 * b)
  let cnt ← readPackedGenProg (((base, offBm), (gBits, w)), idxCnt)
  let acc1 ←
    if acc < nMax then
      let rem ← pure (nMax - acc)
      if rem < cnt then pure nMax else pure (acc + cnt)
    else pure nMax
  let b1 ← pure (b + one_v)
  writePackedGenProg ((((base, offFb), (gBits, w)), b1), acc1)
  pure (b1, acc1)

private theorem memoryCost_fbPrefixStep_pos (d : PermRt × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (fbPrefixStepProg d) s := by
  unfold fbPrefixStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

/-- Precondition for `fbPrefixStepProg`. -/
@[expose] def FbPrefixStepPre (w : ℕ) (d : PermRt × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  PermRtEnvGen w d.1 ∧ d.2.1 < prM d.1

theorem realizes_fbPrefixStep :
    Realizes .exact fbPrefixStepProg
      (WordEncoding.encode (α := PermRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      FbPrefixStepPre
      (fun _ _ => 0) := by
  unfold fbPrefixStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨prt, b, acc⟩
    try clear hwords hmem
    dsimp only [FbPrefixStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_prt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    generalize prBase prt = base at henv heq_prt
    subst heq_prt
    obtain ⟨hM_lt, hM1_le, h16M, _, _, _, _, _, _⟩ := perm_bounds henv
    dsimp only [mkPermRt, prBase, prW, prNMax, prM, prGBits, prOffBktMeta, prOffFbStart] at *
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (apply to_true_exists (w := w); refine pr_bm_safe henv _ ?_; omega)
    | (apply to_true_exists (w := w); refine pr_fb_safe henv _ ?_; omega)
  )

/-- `iterate` wrapper computing `offFbStart[1 .. M]`. -/
@[irreducible] def fbPrefixLoopProg (p : (PermRt × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) :=
  iterate fbPrefixStepProg p.1.1 p.2 p.1.2

theorem realizes_fbPrefixLoop :
    Realizes .exact fbPrefixLoopProg
      (WordEncoding.encode (α := (PermRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w p s => iterationSafe fbPrefixStepProg FbPrefixStepPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold fbPrefixLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := PermRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_fbPrefixStep
    memoryCost_fbPrefixStep_pos

private theorem fbPrefixLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let prt := mkPermRt c U V w n_max base
    ∀ rem b₀ acc (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fbPrefixStepProg FbPrefixStepPre w prt rem (b₀, acc) s := by
  intro prt rem
  induction rem with
  | zero => intro _ _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ acc s hle
    have hb_lt : b₀ < numBucketsWhp n_max := by omega
    have hpre : FbPrefixStepPre w (prt, (b₀, acc)) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb_lt⟩
    have hr1 : ((Memory.spec 0).clientResult s (fbPrefixStepProg (prt, (b₀, acc)))).1 = b₀ + 1 := by
      unfold fbPrefixStepProg
      simp only [pure_bind, clientResult_bind_rw]
      split_ifs <;> simp only [clientResult_bind_rw, StateTransitionSpec.clientResult_pure]
    refine ⟨hpre, ?_⟩
    rw [clientState_width, clientResult_width]
    set res := (Memory.spec 0).clientResult s (fbPrefixStepProg (prt, (b₀, acc)))
    have hres_eta : res = (b₀ + 1, res.2) := Prod.ext hr1 rfl
    rw [hres_eta]
    exact ih (b₀ + 1) res.2 _ (by omega)

/-- Convert `FastMemRep` in place to `CsrMemRep` (`d = (cp, base)`). -/
@[irreducible] def fastToCsrGenProg (d : WhpCoreParams × ℕ) : Memory.Prog Unit := do
  let prt ← mkPermRtGenProg d
  let zero_v ← pure 0
  let one_v ← pure 1
  let two_v ← pure 2
  writePackedGenProg ((((prBase prt, prOffFbStart prt), (prGBits prt, prW prt)), zero_v), zero_v)
  let _ ← fbPrefixLoopProg ((prt, (zero_v, zero_v)), prM prt)
  permuteByTargetProg (prt, one_v)
  Memory.write (prBase prt) two_v

theorem realizes_fastToCsrGen :
    Realizes .exact fastToCsrGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold fastToCsrGenProg
  have hprt := realizes_mkPermRtGen
  have hwp := realizes_writePackedGen
  have hfbl := realizes_fbPrefixLoop
  have hpbt := realizes_permuteByTarget
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    try clear hwords hmem
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hmk_st, hmk_res, _, _⟩ := mkPermRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    try simp only [hmk_st, hmk_res] at *
    try dsimp only [mkPermRt, prBase, prW, prM, prGBits, prOffFbStart] at *
    first
    | exact henv.fits_const (by decide)
    | (have := henv.fits_hdr_addr (off := 0) (by decide); simpa using this)
    | exact pr_fb_safe henv 0 (by positivity)
    | exact fbPrefixLoop_safe henv (numBucketsWhp n_max) 0 0 _ (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

private theorem fbPrefixLoop_spec {c U V w n_max base : ℕ} {bktCount : ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hbm : ∀ b < numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem (16 * b) =
        bktCount b)
    (hsum_le : ∀ b ≤ numBucketsWhp n_max, buildFbStart (numBucketsWhp n_max) bktCount b ≤ n_max) :
    let M := numBucketsWhp n_max
    let fb := buildFbStart M bktCount
    let prt := mkPermRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ x ≤ b₀,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fb x) →
      (∀ a, (a < base + offFbStart c U V w n_max ∨ base + offBackPtr c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fbPrefixLoopProg ((prt, (b₀, fb b₀)), rem)
      let s' := (Memory.spec 0).clientState s prog
      (∀ x ≤ b₀ + rem,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s'.mem x = fb x) ∧
      (∀ a, (a < base + offFbStart c U V w n_max ∨ base + offBackPtr c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro M fb prt rem
  have hw := henv.2.1
  obtain ⟨_, _, h16M, _, _, _, _, _, hg_w⟩ := perm_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hfb_end : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w = offBackPtr c U V w n_max := rfl
  induction rem with
  | zero =>
    intro b₀ s _ hfb hout
    unfold fbPrefixLoopProg iterate
    have hs' : (Memory.spec 0).clientState s (pure (b₀, fb b₀)) = s := rfl
    dsimp only
    rw [hs']
    exact ⟨hfb, hout, rfl, validWhpProg_pure _⟩
  | succ rem ih =>
    intro b₀ s hle hfb hout
    have hb_lt : b₀ < M := by omega
    have hfb_next_eq : fb (b₀ + 1) = fb b₀ + bktCount b₀ := by
      dsimp only [fb, buildFbStart, buildFbStart.go]
      simp [hb_lt]
    have hfb1_le : fb (b₀ + 1) ≤ n_max := hsum_le (b₀ + 1) hb_lt
    have hfb1_pow : fb (b₀ + 1) < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le hfb1_le
    have hcnt_s : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
        (16 * b₀) = bktCount b₀ := by
      rw [readPacked_congr_on hw (by omega : 16 * b₀ < 16 * M)
        (fun a ha1 ha2 => hout a (Or.inl (by omega)))]
      exact hbm b₀ hb_lt
    have hacc1_eq :
        (if fb b₀ < n_max then
           if n_max - fb b₀ < bktCount b₀ then n_max else fb b₀ + bktCount b₀
         else n_max) = fb (b₀ + 1) := by
      split_ifs <;> omega
    set p1 := fbPrefixStepProg (prt, (b₀, fb b₀))
    set m1 := writePacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
      (b₀ + 1) (fb (b₀ + 1))
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } := by
      dsimp only [p1]; unfold fbPrefixStepProg
      dsimp only [prt, mkPermRt, prBase, prW, prNMax, prGBits, prOffBktMeta, prOffFbStart]
      simp only [pure_bind]
      rw [clientState_bind_rw, clientState_readPackedGen, clientResult_readPackedGen, hcnt_s]
      have hle : fb b₀ + bktCount b₀ ≤ n_max := hfb_next_eq ▸ hfb1_le
      split_ifs with h1 h2
      · exfalso; omega
      · dsimp only [m1]
        rw [clientState_bind_rw, clientState_writePackedGen, clientState_pure_zero, hfb_next_eq]
      · dsimp only [m1]
        have heq_n : fb (b₀ + 1) = n_max := by omega
        rw [clientState_bind_rw, clientState_writePackedGen, clientState_pure_zero, heq_n]
    have hr1 : (Memory.spec 0).clientResult s p1 = (b₀ + 1, fb (b₀ + 1)) := by
      dsimp only [p1]; unfold fbPrefixStepProg
      dsimp only [prt, mkPermRt, prBase, prW, prNMax, prGBits, prOffBktMeta, prOffFbStart]
      simp only [pure_bind]
      rw [clientResult_bind_rw, clientState_readPackedGen, clientResult_readPackedGen, hcnt_s]
      have hle : fb b₀ + bktCount b₀ ≤ n_max := hfb_next_eq ▸ hfb1_le
      split_ifs with h1 h2
      · exfalso; omega
      · rw [clientResult_bind_rw, clientResult_pure_zero, hfb_next_eq]
      · have heq_n : fb (b₀ + 1) = n_max := by omega
        rw [clientResult_bind_rw, clientResult_pure_zero, heq_n]
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fbPrefixStepProg
      dsimp only [prt, mkPermRt, prBase, prW, prNMax, prGBits, prOffBktMeta, prOffFbStart]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw (by omega) hbm_b) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hcnt_s]
      split_ifs <;>
        exact validWhpProg_bind (validWhpProg_writePacked hw hg_w (by omega) hfb_b)
          (validWhpProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hfb1 : ∀ x ≤ b₀ + 1,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s1.mem x = fb x := by
      intro x hx
      dsimp only [s1, m1]
      by_cases heq : x = b₀ + 1
      · subst heq; exact readPacked_writePacked_self _ _ _ _ _ hfb1_pow
      · rw [readPacked_writePacked_of_ne hw s.mem heq (fb (b₀ + 1))]
        exact hfb x (by omega)
    have hout1 : ∀ a, (a < base + offFbStart c U V w n_max ∨ base + offBackPtr c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha
      dsimp only [s1, m1]
      rw [mem_writePacked_of_outside hw (by omega : b₀ + 1 < M + 1) (by omega)]
      exact hout a ha
    obtain ⟨hfb_r, ho_r, hf_r, hvp_r⟩ := ih (b₀ + 1) s1 (by omega) hfb1 hout1
    unfold fbPrefixLoopProg at hfb_r ho_r hf_r hvp_r ⊢
    dsimp only [iterate]
    have hst_eq : (Memory.spec 0).clientState s
        (p1 >>= fun s' => iterate fbPrefixStepProg prt rem s') =
        (Memory.spec 0).clientState s1
          (iterate fbPrefixStepProg prt rem (b₀ + 1, fb (b₀ + 1))) := by
      rw [clientState_bind_rw, hs1, hr1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx; rw [hst_eq]; exact hfb_r x (by omega)
    · intro a ha; rw [hst_eq]; exact ho_r a ha
    · rw [hst_eq, hf_r]
    · change ValidWhpProg _ _ s (p1 >>= _)
      refine validWhpProg_bind hvp1 ?_
      rw [hs1, hr1]; exact hvp_r

/-- Exact specification of `fastToCsrGenProg`: converts any valid `FastMemRep` into `CsrMemRep` for
`fastToCsr n_max fs` while preserving `SeedWhpMemRep` and leaving memory outside
`[base, base + largeSpaceWhp c U V w n_max)` untouched. -/
theorem fastToCsrGenProg_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : Dictionary.State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict) :
    let prog := fastToCsrGenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    CsrMemRep base c U V w n_max (fastToCsr n_max fs) s'.mem ∧
    s'.frontier = s.frontier ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, hg_w⟩ := perm_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  set M := numBucketsWhp n_max
  set cf := capFrontWhp n_max
  set cb := capBackWhp n_max
  set fb := buildFbStart M fs.bktCount
  set prt := mkPermRt c U V w n_max base
  obtain ⟨hcsr, _⟩ := hv.fastToCsr_spec
  have hfb_mono : ∀ x y, x ≤ y → y ≤ M → fb x ≤ fb y := by
    intro x y hxy hy
    induction y with
    | zero =>
      have hx0 : x = 0 := by omega
      subst hx0
      exact le_rfl
    | succ y ihy =>
      rcases Nat.eq_or_lt_of_le hxy with rfl | hlt
      · exact le_rfl
      · exact (ihy (Nat.le_of_lt_succ hlt) (by omega)).trans (hcsr.2.1 y (by omega))
  have hfb_le_n : ∀ x ≤ M, fb x ≤ n_max := fun x hx =>
    (hfb_mono x M hx le_rfl).trans hcsr.2.2.1
  have hfb_adj : ∀ b < M, fb (b + 1) = fb b + fs.bktCount b := by
    intro b hb
    dsimp only [fb, buildFbStart, buildFbStart.go]
    simp [hb]
  obtain ⟨hmk_st, hmk_res, _, hmk_vp⟩ := mkPermRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hfb_end : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w = offBackPtr c U V w n_max := rfl
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hls_end : offLocState c U V w n_max +
      packedWords (M * totalLocalCoordsWhp n_max) 2 w = offBktMeta c U V w n_max := rfl
  have hdisj := perm_seg_disjoint c U V w n_max
  set m0 := writePacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem 0 0
  set s0 : Memory.State := { mem := m0, frontier := s.frontier }
  have hfb0 : ∀ x ≤ 0,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s0.mem x = fb x := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    exact readPacked_writePacked_self _ _ _ _ _ (Nat.two_pow_pos _)
  have hout0 : ∀ a, (a < base + offFbStart c U V w n_max ∨ base + offBackPtr c U V w n_max ≤ a) →
      s0.mem a = s.mem a := by
    intro a ha
    refine mem_writePacked_of_outside hw (Nat.zero_lt_succ M) ?_
    rcases ha with hlt | hge
    · left; exact hlt
    · right; rw [Nat.add_assoc, hfb_end]; exact hge
  have hbm_rep : ∀ b < M,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b) =
        fs.bktCount b := fun b hb => by
    simpa only [Nat.add_zero] using (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb).1
  obtain ⟨hfb_all, hout_fb, hf_fb, hvp_fb⟩ :=
    fbPrefixLoop_spec henv hbm_rep hfb_le_n M 0 s0 (by omega) hfb0 hout0
  rw [Nat.zero_add] at hfb_all
  set s_fb := (Memory.spec 0).clientState s0 (fbPrefixLoopProg ((prt, (0, fb 0)), M))
  have hv_pow : ∀ p, fs.valArr p < 2 ^ valBits V := by
    intro p
    have hv_max := (hv.qv_global p).2
    by_cases hV0 : V = 0
    · subst hV0; simpa [valBits] using hv_max
    · exact (lt_of_lt_of_le hv_max (max_le le_rfl (Nat.pos_of_ne_zero hV0))).trans_le
        (Nat.le_pow_clog Nat.one_lt_two V)
  have hq_sfb : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s_fb.mem i = fs.quotArr i ∧
      fs.quotArr i < 2 ^ quotBitsWhp U n_max := by
    intro i hi
    refine ⟨?_, (hv.qv_global i).1⟩
    rw [readPacked_congr_on (mem₂ := s.mem) hw hi (fun a ha1 ha2 => hout_fb a (Or.inl (by omega)))]
    exact (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).1
  have hv_sfb : ∀ i < n_max,
      readPacked (base + offValWhp c U w n_max) (valBits V) w s_fb.mem i = fs.valArr i ∧
      fs.valArr i < 2 ^ valBits V := by
    intro i hi
    refine ⟨?_, hv_pow i⟩
    rw [readPacked_congr_on (mem₂ := s.mem) hw hi (fun a ha1 ha2 => hout_fb a (Or.inl (by omega)))]
    exact (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2
  let act₀ : ℕ → Bool := fun p =>
    if p < M * cf then
      if 0 < cf then decide (p / cf < M ∧ p % cf < fs.bktCount (p / cf)) else false
    else
      let poolIdx := p - M * cf
      if poolIdx < poolSizeWhp n_max ∧ 0 < cb then
        let enc := fs.poolOwner poolIdx
        decide (enc / cb < M ∧ cf + enc % cb < fs.bktCount (enc / cb) ∧
          fs.backPtr (enc / cb) (enc % cb) = poolIdx)
      else false
  let dest : ℕ → ℕ := fun p =>
    if p < M * cf then
      if 0 < cf then fb (p / cf) + p % cf else 0
    else
      let poolIdx := p - M * cf
      if 0 < cb then fb (fs.poolOwner poolIdx / cb) + cf + fs.poolOwner poolIdx % cb else 0
  have heval : ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s_fb.mem a) →
      ((Memory.spec 0).clientResult s' (permEvalActDestProg ((prt, 1), x))).1 =
          (if act₀ x then 1 else 0) ∧
      (act₀ x = true →
        ((Memory.spec 0).clientResult s' (permEvalActDestProg ((prt, 1), x))).2 = dest x ∧
        dest x < n_max) := by
    intro x hx_lt s' hout'
    have hbm_s' : ∀ b < numBucketsWhp n_max,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b) =
          fs.bktCount b := by
      intro b hb
      rw [readPacked_congr_on hw (by omega : 16 * b < 16 * numBucketsWhp n_max)
        (fun a ha1 _ => (hout' a (Or.inr (by omega))).trans
          (hout_fb a (Or.inl (by unfold offFbStart; omega))))]
      exact hbm_rep b hb
    have hfb_s' : ∀ b ≤ numBucketsWhp n_max,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s'.mem b = fb b := by
      intro b hb
      rw [readPacked_congr_on hw (Nat.lt_succ_of_le hb)
        (fun a ha1 _ => hout' a (Or.inr (by omega)))]
      exact hfb_all b hb
    have hbp_s' : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
          (b * capBackWhp n_max + k) = fs.backPtr b k := by
      intro b hb k hk
      have hbk := mul_add_lt_mul hb hk
      rw [readPacked_congr_on hw hbk
        (fun a ha1 _ => (hout' a (Or.inr (by omega))).trans (hout_fb a (Or.inr (by omega))))]
      exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb k hk
    have hpo_s' : ∀ j < poolSizeWhp n_max,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s'.mem j =
          fs.poolOwner j := by
      intro j hj
      have hpo_ge : offBackPtr c U V w n_max ≤ offPoolOwner c U V w n_max := by
        unfold offPoolOwner offPoolFreeStack offBackAux; omega
      rw [readPacked_congr_on hw hj
        (fun a ha1 _ => (hout' a (Or.inr (by omega))).trans (hout_fb a (Or.inr (by omega))))]
      exact (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).2
    have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
    unfold permEvalActDestProg
    dsimp only [M, cf, cb, prt, mkPermRt, prBase, prW, prNMax, prM, prCF, prCB,
      prFrontTotal, prPoolSize, prGBits, prOffBktMeta, prOffFbStart, prOffBackPtr,
      prOffPoolOwner, act₀, dest]
    simp only [pure_bind, ↓reduceIte]
    by_cases hft : x < numBucketsWhp n_max * capFrontWhp n_max
    · simp only [hft, ↓reduceIte]
      by_cases hcf : 0 < capFrontWhp n_max
      · simp only [hcf, ↓reduceIte]
        by_cases hb : x / capFrontWhp n_max < numBucketsWhp n_max
        · simp only [hb, ↓reduceIte, clientResult_bind_rw, hcs,
            clientResult_readPackedGen, hbm_s' (x / capFrontWhp n_max) hb]
          by_cases hloc : x % capFrontWhp n_max < fs.bktCount (x / capFrontWhp n_max)
          · have hfb_lt : fb (x / capFrontWhp n_max) + x % capFrontWhp n_max < n_max := by
              have := hfb_adj (x / capFrontWhp n_max) hb
              have := hfb_le_n (x / capFrontWhp n_max + 1) hb
              omega
            have h1 : fb (x / capFrontWhp n_max) < n_max := by omega
            have h2 : x % capFrontWhp n_max < n_max - fb (x / capFrontWhp n_max) := by omega
            simp only [hloc, ↓reduceIte, clientResult_bind_rw, hcs,
              clientResult_readPackedGen, hfb_s' (x / capFrontWhp n_max) hb.le, h1, h2,
              StateTransitionSpec.clientResult_pure]
            exact ⟨rfl, fun _ => ⟨trivial, hfb_lt⟩⟩
          · simp [hloc, StateTransitionSpec.clientResult_pure]
        · simp [hb, StateTransitionSpec.clientResult_pure]
      · simp [hcf, StateTransitionSpec.clientResult_pure]
    · simp only [hft, ↓reduceIte]
      have hps_lt : x - numBucketsWhp n_max * capFrontWhp n_max < poolSizeWhp n_max := by
        unfold poolSizeWhp; omega
      simp only [hps_lt, ↓reduceIte, true_and]
      by_cases hcb : 0 < capBackWhp n_max
      · simp only [hcb, ↓reduceIte, clientResult_bind_rw, hcs,
          clientResult_readPackedGen, hpo_s' (x - numBucketsWhp n_max * capFrontWhp n_max) hps_lt]
        set enc := fs.poolOwner (x - numBucketsWhp n_max * capFrontWhp n_max)
        have hk_cb : enc % capBackWhp n_max < capBackWhp n_max := Nat.mod_lt _ hcb
        by_cases hb : enc / capBackWhp n_max < numBucketsWhp n_max
        · have hcnt_le : fs.bktCount (enc / capBackWhp n_max) ≤ n_max := by
            have := hfb_adj (enc / capBackWhp n_max) hb
            have := hfb_le_n (enc / capBackWhp n_max + 1) hb
            omega
          have hn_gt : ¬(n_max < fs.bktCount (enc / capBackWhp n_max)) := Nat.not_lt.mpr hcnt_le
          simp only [hb, ↓reduceIte, clientResult_bind_rw, hcs,
            clientResult_readPackedGen, hbm_s' (enc / capBackWhp n_max) hb, hn_gt]
          by_cases hcf_cnt : capFrontWhp n_max < fs.bktCount (enc / capBackWhp n_max)
          · simp only [hcf_cnt, ↓reduceIte]
            by_cases hk_rem :
              enc % capBackWhp n_max < fs.bktCount (enc / capBackWhp n_max) - capFrontWhp n_max
            · have hloc_cnt : capFrontWhp n_max + enc % capBackWhp n_max <
                  fs.bktCount (enc / capBackWhp n_max) := by omega
              simp only [hk_rem, hloc_cnt, ↓reduceIte, true_and, clientResult_bind_rw,
                hcs, clientResult_readPackedGen,
                hbp_s' (enc / capBackWhp n_max) hb (enc % capBackWhp n_max) hk_cb]
              by_cases hbp_eq : fs.backPtr (enc / capBackWhp n_max) (enc % capBackWhp n_max) =
                  x - numBucketsWhp n_max * capFrontWhp n_max
              · have hfb_lt : fb (enc / capBackWhp n_max) +
                    (capFrontWhp n_max + enc % capBackWhp n_max) < n_max := by
                  have := hfb_adj (enc / capBackWhp n_max) hb
                  have := hfb_le_n (enc / capBackWhp n_max + 1) hb
                  omega
                have h1 : fb (enc / capBackWhp n_max) < n_max := by omega
                have h2 : capFrontWhp n_max + enc % capBackWhp n_max <
                    n_max - fb (enc / capBackWhp n_max) := by omega
                simp only [hbp_eq, ↓reduceIte, clientResult_bind_rw, hcs,
                  clientResult_readPackedGen, hfb_s' (enc / capBackWhp n_max) hb.le, h1, h2,
                  StateTransitionSpec.clientResult_pure]
                exact ⟨rfl, fun _ => ⟨by omega, by omega⟩⟩
              · simp [hbp_eq, StateTransitionSpec.clientResult_pure]
            · have hn_loc : ¬(capFrontWhp n_max + enc % capBackWhp n_max <
                  fs.bktCount (enc / capBackWhp n_max)) := by omega
              simp [hk_rem, hn_loc, StateTransitionSpec.clientResult_pure]
          · have hn_loc : ¬(capFrontWhp n_max + enc % capBackWhp n_max <
                fs.bktCount (enc / capBackWhp n_max)) := by omega
            simp [hcf_cnt, hn_loc, StateTransitionSpec.clientResult_pure]
        · simp [hb, StateTransitionSpec.clientResult_pure]
      · simp [hcb, StateTransitionSpec.clientResult_pure]
  obtain ⟨hp_qv, hp_out, hp_f, hp_vp⟩ :=
    permuteByTargetProg_spec (mode := 1) henv hq_sfb hv_sfb heval
  set s_p := (Memory.spec 0).clientState s_fb (permuteByTargetProg (prt, 1))
  set s_fin : Memory.State := { mem := Function.update s_p.mem base 2, frontier := s_p.frontier }
  have hst_eq : (Memory.spec 0).clientState s
      (fastToCsrGenProg (mkWhpCoreParams c U V w n_max, base)) = s_fin := by
    unfold fastToCsrGenProg
    rw [clientState_bind_rw, hmk_st, hmk_res]
    dsimp only [mkPermRt, prBase, prW, prM, prGBits, prOffFbStart]
    simp only [pure_bind]
    rw [clientState_bind_rw, clientState_bind_rw, clientState_bind_rw]
    rfl
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by
      change hdrWordsWhp ≤ _; unfold largeSpaceWhp; omega
    omega
  have h2_fit : Fits w 2 := henv.fits_const (by decide)
  have h32_q : 32 ≤ offQuotWhp c w n_max := by
    change offHashBkt ≤ _; unfold offQuotWhp offHashFp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hst_eq]
    refine SeedWhpMemRep.congr_hash hw (fun a ha1 ha2 => ?_) hseed
    dsimp only [offHashBkt, hdrWordsWhp] at ha1
    have h_eq : s_fin.mem a = s.mem a := by
      dsimp only [s_fin]
      rw [Function.update_of_ne (by omega)]
      exact (hp_out a (Or.inl ha2)).trans (hout_fb a (Or.inl (by omega)))
    exact h_eq.symm
  · rw [hst_eq]
    refine ⟨?_, fun b hb => ?_, fun i hi => ⟨?_, ?_⟩⟩
    · dsimp only [s_fin, hdrMode]
      rw [Nat.add_zero, Function.update_self]
    · dsimp only [s_fin]
      rw [readPacked_update_outside hw (Nat.lt_succ_of_le hb) (Or.inl (by omega)),
        readPacked_congr_on hw (Nat.lt_succ_of_le hb)
          (fun a ha1 _ => hp_out a (Or.inr (by omega)))]
      exact hfb_all b hb
    · dsimp only [s_fin]
      rw [readPacked_update_outside hw hi (Or.inl (by omega))]
      exact (hp_qv i hi).1
    · dsimp only [s_fin]
      rw [readPacked_update_outside hw hi (Or.inl (by omega))]
      exact (hp_qv i hi).2
  · rw [hst_eq]; dsimp only [s_fin]; exact hp_f.trans hf_fb
  · unfold fastToCsrGenProg
    refine validWhpProg_bind hmk_vp ?_
    rw [hmk_st, hmk_res]
    dsimp only [mkPermRt, prBase, prW, prM, prGBits, prOffFbStart]
    simp only [pure_bind]
    refine validWhpProg_bind (validWhpProg_writePacked hw hg_w (Nat.zero_lt_succ M) hfb_b) ?_
    refine validWhpProg_bind hvp_fb ?_
    exact validWhpProg_bind hp_vp (validWhpProg_write hbase_lt h2_fit)
  · intro a ha
    rw [hst_eq]; dsimp only [s_fin]
    rw [Function.update_of_ne (by omega)]
    rcases ha with ha_lo | ha_hi
    · exact (hp_out a (Or.inl (by omega))).trans (hout_fb a (Or.inl (by omega)))
    · have hls : base + offLocState c U V w n_max ≤ a := by
        have := hseg.2.2.2.1; omega
      have hbp : base + offBackPtr c U V w n_max ≤ a := by
        have := hseg.2.2.2.2.2.2.1; omega
      exact (hp_out a (Or.inr hls)).trans (hout_fb a (Or.inr hbp))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
