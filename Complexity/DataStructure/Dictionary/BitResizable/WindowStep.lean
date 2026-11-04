/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.InEpoch
import all Complexity.DataStructure.Dictionary.BitResizable.Layout
import all Complexity.DataStructure.Dictionary.BitResizable.InEpoch
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlotStore
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctBucketOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctValidHistory
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Window and `diffCount` Transitions for the Bit-Resizable Dictionary

This module proves the window-bijection (`TailDenseInv`) and changed-word (`diffCount` /
`diffCount2`) transitions for `pushBackSlotProg`, `popBackSlotProg`, `insertWithHashProg`, and
`deleteFinishWithHashProg` on the fixed-capacity companion state, as well as the unconditional
footprint inequality `succinctSpace_le_dictBitSize`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.WindowStepPost`: bundled postcondition for a
  companion window and `diffCount` transition from `(s₀, td, dt)` to `(s', td', dt')` with
  slab-rebalancing work `W`.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.succinctSpace_le_dictBitSize`: unconditional space
  inequality `Succinct.space U V w N ≤ dictBitSize U V w N N` for `0 < w` and `0 < N`.
* `Cslib.DataStructure.Dictionary.BitResizable.insertWithHashProg_window`: window and `diffCount`
  transition for `Succinct.insertWithHashProg`.
* `Cslib.DataStructure.Dictionary.BitResizable.deleteFinishWithHashProg_window`: window and
  `diffCount` transition for `Succinct.deleteFinishWithHashProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Finset

/-! ## Section 1: Unconditional space inequality (`succinctSpace_le_dictBitSize`) -/

private theorem div_ceil_le_self {A w : ℕ} (hw : 0 < w) : (A + w - 1) / w ≤ A := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp [Nat.div_eq_of_lt (by omega : w - 1 < w)]
  · have hle : A + w - 1 ≤ A * w := by
      have : A + w ≤ A * w + 1 := by nlinarith
      omega
    calc (A + w - 1) / w ≤ (A * w) / w := Nat.div_le_div_right hle
      _ = A := Nat.mul_div_cancel _ hw

private theorem packedWords_le_mul_add_two (N k : ℕ) {w : ℕ} (hw : 0 < w) :
    packedWords N k w ≤ N * k + 2 := by
  unfold packedWords
  have := div_ceil_le_self (A := N * k) hw
  omega

/-- For any `0 < w` and `0 < N`, the word footprint `Succinct.space U V w N` of the fixed-capacity
companion is at most `dictBitSize U V w N N`. -/
theorem succinctSpace_le_dictBitSize {U V w N : ℕ} (hw : 0 < w) (hN : 0 < N) :
    Succinct.space U V w N ≤ dictBitSize U V w N N := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hq := packedWords_le_mul_add_two N (quotientBits U N) hw
  have hv := packedWords_le_mul_add_two N (valBits V) hw
  have hmul : N * quotientBits U N + N * valBits V = N * itemBits U V N := by
    unfold itemBits; rw [Nat.mul_add]
  have hmeta_le : epochMetaWords U w N ≤ epochMetaBits U w N :=
    Nat.le_mul_of_pos_right _ hw
  unfold epochMetaWords at hmeta_le
  rw [ite_eq_right hN0] at hmeta_le
  unfold dictBitSize Succinct.space Succinct.totalSpace Succinct.offGM Succinct.offLM
    Succinct.offVal Succinct.offQuot
  omega

theorem dictEnv_of_fits_dictBitSize {U V w N : ℕ}
    (hw : 0 < w) (hN : 0 < N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_sz : Fits w (dictBitSize U V w N N)) :
    Succinct.DictParamsWf U V w N ∧
    Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0 ∧
    Fits w (offHash + Succinct.hashSpace U w N) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hsp_le : 0 + Succinct.space U V w N ≤ dictBitSize U V w N N := by
    rw [Nat.zero_add]; exact succinctSpace_le_dictBitSize hw hN
  have hhash_le : offHash + Succinct.hashSpace U w N ≤ dictBitSize U V w N N := by
    have hmeta_le : epochMetaWords U w N ≤ epochMetaBits U w N :=
      Nat.le_mul_of_pos_right _ hw
    unfold epochMetaWords at hmeta_le
    rw [ite_eq_right hN0] at hmeta_le
    unfold dictBitSize offHash; omega
  exact ⟨⟨hw, hNU, hU, hV⟩, ⟨rfl, hfit_sz.of_le hsp_le⟩, hfit_sz.of_le hhash_le⟩

/-! ## Section 2: `diffCount2` bounds for `promoteSlabProg` and `demoteSlabProg` -/

theorem iterate_promoteStepProg_diffCount2 {U V w₀ n_max h_space base b : ℕ}
    {L_p : List ℕ} (hnodup_p : L_p.Nodup) (qA₀ vA₀ : ℕ → ℕ)
    {s₀ : Memory.State} (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max) :
    ∀ m k (s : Memory.State),
      k + m ≤ slabSize n_max →
      Succinct.PromoteLoopInv U V w₀ n_max h_space base b s₀ k s →
      let s' := (Memory.spec 0).clientState s
        (iterate (Succinct.promoteStepProg U V w₀ n_max h_space) (base, b) m k)
      diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s'.mem)
        (Succinct.valAt base U V w₀ n_max h_space s'.mem) qA₀ vA₀ ≤
        diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s.mem)
          (Succinct.valAt base U V w₀ n_max h_space s.mem) qA₀ vA₀ + 3 * m := by
  intro m
  induction m with
  | zero =>
    intro k s _ _; simp only [iterate, Nat.mul_zero, Nat.add_zero]; exact le_rfl
  | succ m ih =>
    intro k s hkm hinv
    have hk_lt : k < slabSize n_max := by omega
    obtain ⟨hres, hinv1⟩ := Succinct.promoteLoopInv_step hw hb_pos hinv hk_lt
    obtain ⟨_, _, _, hq1, hv1, _, _⟩ :=
      Succinct.promoteStepProg_effect hw hb_pos s (Succinct.promoteStepInv_of_loopInv hinv hk_lt)
    set s₁ := (Memory.spec 0).clientState s
      (Succinct.promoteStepProg U V w₀ n_max h_space ((base, b), k))
    have hstep : diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s₁.mem)
        (Succinct.valAt base U V w₀ n_max h_space s₁.mem) qA₀ vA₀ ≤
        diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s.mem)
          (Succinct.valAt base U V w₀ n_max h_space s.mem) qA₀ vA₀ + 3 := by
      rw [hq1, hv1]
      refine (diffCount2_update_both_le hnodup_p _ _ qA₀ vA₀ _ _ _).trans ?_
      refine (Nat.add_le_add_right
        (diffCount2_update_both_le hnodup_p _ _ qA₀ vA₀ _ _ _) 1).trans ?_
      refine (Nat.add_le_add_right (Nat.add_le_add_right
        (diffCount2_update_both_le hnodup_p _ _ qA₀ vA₀ _ _ _) 1) 1).trans ?_
      omega
    have hrec := ih (k + 1) s₁ (by omega) hinv1
    dsimp only at hrec ⊢; unfold iterate; rw [StateTransitionSpec.clientState_bind, hres]
    dsimp only [s₁] at hstep hrec ⊢; omega

theorem promoteSlabProg_diffCount2_and_gm {U V w n_max h_space base b : ℕ}
    {L_p : List ℕ} (hnodup_p : L_p.Nodup) (qA₀ vA₀ : ℕ → ℕ)
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State) (hpre : Succinct.PromoteSlabInv U V w n_max h_space base b s) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.promoteSlabProg U V w n_max h_space (base, b))
    let gm := Succinct.gmAt base U V w n_max h_space s.mem
    let gm' := Succinct.gmAt base U V w n_max h_space s'.mem
    gm' 0 = gm 0 + 1 ∧ gm' 1 + slabSize n_max = gm 1 ∧
    diffCount2 L_p (Succinct.quotAt base U w n_max h_space s'.mem)
      (Succinct.valAt base U V w n_max h_space s'.mem) qA₀ vA₀ ≤
      diffCount2 L_p (Succinct.quotAt base U w n_max h_space s.mem)
        (Succinct.valAt base U V w n_max h_space s.mem) qA₀ vA₀ + 3 * slabSize n_max := by
  intro s' gm gm'
  have hloop0 := Succinct.promoteLoopInv_zero hpre
  obtain ⟨hloopK, _, _⟩ :=
    Succinct.iterate_promoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) hloop0
  rw [Nat.zero_add] at hloopK
  have hdiffK := iterate_promoteStepProg_diffCount2 hnodup_p qA₀ vA₀ hw hb_pos
    (slabSize n_max) 0 s (by omega) hloop0
  set s₁ := (Memory.spec 0).clientState s
    (Succinct.promoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change Succinct.PromoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  have htot1 : (Succinct.gmAt base U V w n_max h_space s₁.mem 0 + 1) * slabSize n_max ≤ n_max := by
    have := hloopK.tot_le; rw [Nat.add_one_mul]; omega
  have hp_lt1 : Succinct.gmAt base U V w n_max h_space s₁.mem 0 < maxFullSlabs n_max :=
    Succinct.nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  obtain ⟨_, _, hq_push, hv_push, _, hgm_push⟩ :=
    Succinct.gmPushSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hp_lt1
  have hst : s' =
      (Memory.spec 0).clientState s₁ (Succinct.gmPushSlabProg U V w n_max h_space (base, b)) := by
    change (Memory.spec 0).clientState s
      (Succinct.promoteSlabProg U V w n_max h_space (base, b)) = _
    unfold Succinct.promoteSlabProg; rw [StateTransitionSpec.clientState_bind]
  have hf_fields := gmPushSlab_fields (Succinct.gmAt base U V w n_max h_space s₁.mem) hloopK.b_lt
  refine ⟨by dsimp only [gm', gm]; rw [hst, hgm_push, hf_fields.1, hloopK.gm0_eq],
    by dsimp only [gm', gm]; rw [hst, hgm_push, hf_fields.2.1, hloopK.gm1_eq],
    by rw [hst, hq_push, hv_push]; exact hdiffK⟩

theorem iterate_demoteStepProg_diffCount2 {U V w₀ n_max h_space base b : ℕ}
    {L_p : List ℕ} (hnodup_p : L_p.Nodup) (qA₀ vA₀ : ℕ → ℕ)
    {s₀ : Memory.State} (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max) :
    ∀ m k (s : Memory.State),
      k + m ≤ slabSize n_max →
      Succinct.DemoteLoopInv U V w₀ n_max h_space base b s₀ k s →
      let s' := (Memory.spec 0).clientState s
        (iterate (Succinct.demoteStepProg U V w₀ n_max h_space) (base, b) m k)
      diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s'.mem)
        (Succinct.valAt base U V w₀ n_max h_space s'.mem) qA₀ vA₀ ≤
        diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s.mem)
          (Succinct.valAt base U V w₀ n_max h_space s.mem) qA₀ vA₀ + 2 * m := by
  intro m
  induction m with
  | zero =>
    intro k s _ _; simp only [iterate, Nat.mul_zero, Nat.add_zero]; exact le_rfl
  | succ m ih =>
    intro k s hkm hinv
    have hk_lt : k < slabSize n_max := by omega
    obtain ⟨hres, hinv1⟩ := Succinct.demoteLoopInv_step hw hb_pos hinv hk_lt
    obtain ⟨_, _, _, hq1, hv1, _, _⟩ :=
      Succinct.demoteStepProg_effect hw hb_pos s (Succinct.demoteLoopInv_to_stepInv hinv hk_lt)
    set s₁ := (Memory.spec 0).clientState s
      (Succinct.demoteStepProg U V w₀ n_max h_space ((base, b), k))
    have hstep : diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s₁.mem)
        (Succinct.valAt base U V w₀ n_max h_space s₁.mem) qA₀ vA₀ ≤
        diffCount2 L_p (Succinct.quotAt base U w₀ n_max h_space s.mem)
          (Succinct.valAt base U V w₀ n_max h_space s.mem) qA₀ vA₀ + 2 := by
      rw [hq1, hv1]
      refine (diffCount2_update_both_le hnodup_p _ _ qA₀ vA₀ _ _ _).trans ?_
      refine (Nat.add_le_add_right
        (diffCount2_update_both_le hnodup_p _ _ qA₀ vA₀ _ _ _) 1).trans ?_
      omega
    have hrec := ih (k + 1) s₁ (by omega) hinv1
    dsimp only at hrec ⊢; unfold iterate; rw [StateTransitionSpec.clientState_bind, hres]
    dsimp only [s₁] at hstep hrec ⊢; omega

theorem demoteSlabProg_diffCount2_and_gm {U V w n_max h_space base b : ℕ}
    {L_p : List ℕ} (hnodup_p : L_p.Nodup) (qA₀ vA₀ : ℕ → ℕ)
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State) (hpre : Succinct.DemoteSlabInv U V w n_max h_space base b s) :
    let s' := (Memory.spec 0).clientState s
      (Succinct.demoteSlabProg U V w n_max h_space (base, b))
    let gm := Succinct.gmAt base U V w n_max h_space s.mem
    let gm' := Succinct.gmAt base U V w n_max h_space s'.mem
    gm' 0 + 1 = gm 0 ∧ gm' 1 = gm 1 + slabSize n_max ∧
    diffCount2 L_p (Succinct.quotAt base U w n_max h_space s'.mem)
      (Succinct.valAt base U V w n_max h_space s'.mem) qA₀ vA₀ ≤
      diffCount2 L_p (Succinct.quotAt base U w n_max h_space s.mem)
        (Succinct.valAt base U V w n_max h_space s.mem) qA₀ vA₀ + 2 * slabSize n_max := by
  intro s' gm gm'
  have hloop0 := Succinct.demoteLoopInv_zero hpre
  obtain ⟨hloopK, _, _⟩ :=
    Succinct.iterate_demoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) hloop0
  rw [Nat.zero_add] at hloopK
  have hdiffK := iterate_demoteStepProg_diffCount2 hnodup_p qA₀ vA₀ hw hb_pos
    (slabSize n_max) 0 s (by omega) hloop0
  set s₁ := (Memory.spec 0).clientState s
    (Succinct.demoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change Succinct.DemoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  obtain ⟨_, _, hq_pop, hv_pop, _, hgm_pop⟩ :=
    Succinct.gmPopSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hloopK.qb_pos
  have hst : s' =
      (Memory.spec 0).clientState s₁ (Succinct.gmPopSlabProg U V w n_max h_space (base, b)) := by
    change (Memory.spec 0).clientState s
      (Succinct.demoteSlabProg U V w n_max h_space (base, b)) = _
    unfold Succinct.demoteSlabProg; rw [StateTransitionSpec.clientState_bind]
  have hf_fields := gmPopSlab_preserves_tail hloopK.b_lt hloopK.slab_bij
  have hgm0_pos : 1 ≤ gm 0 := by
    have := Succinct.q_le_nslabs_of_slabBijection hpre.2.2.1 hpre.1
    have := hpre.2.2.2.2.1; dsimp only [gm]; omega
  refine ⟨by
      dsimp only [gm', gm] at hgm0_pos ⊢; rw [hst, hgm_pop, hf_fields.1, hloopK.gm0_eq]; omega,
    by dsimp only [gm', gm]; rw [hst, hgm_pop, hf_fields.2.1, hloopK.gm1_eq],
    by rw [hst, hq_pop, hv_pop]; exact hdiffK⟩

/-! ## Section 3: Window and `diffCount` transitions for `pushBackSlotProg` and `popBackSlotProg` -/

/-- Bundled postcondition for a companion window and `diffCount` transition from `(s₀, td, dt)` to
`(s', td', dt')` with slab-rebalancing work `W`. -/
structure WindowStepPost (U V w N m₀ : ℕ) (L_p L_m : List ℕ)
    (s₀ s' : Memory.State) (td dt td' dt' : ℕ → ℕ) (W : ℕ) : Prop where
  tailDense :
    let h_space := Succinct.hashSpace U w N
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    TailDenseInv N (gm' 0) (gm' 1) td' dt'
  td_lt : ∀ i, td' i < max (maxTailItems N) 1
  dt_lt : ∀ i, dt' i < max (maxTailItems N) 1
  pot_le :
    let h_space := Succinct.hashSpace U w N
    let gm₀ := Succinct.gmAt 0 U V w N h_space s₀.mem
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    slotPotential N gm' + W ≤ slotPotential N gm₀ + 1
  diff_qv :
    let h_space := Succinct.hashSpace U w N
    diffCount2 L_p (Succinct.quotAt 0 U w N h_space s'.mem)
      (Succinct.valAt 0 U V w N h_space s'.mem)
      (Succinct.quotAt 0 U w N h_space s₀.mem)
      (Succinct.valAt 0 U V w N h_space s₀.mem) ≤ 2 + 3 * W
  diff_phys :
    let h_space := Succinct.hashSpace U w N
    let gm₀ := Succinct.gmAt 0 U V w N h_space s₀.mem
    let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
    diffCount (List.range m₀) (physByBase N (gm' 0 * slabSize N) dt')
      (physByBase N (gm₀ 0 * slabSize N) dt) ≤ 1 + 2 * W
  diff_td :
    let M := maxTailItems N
    let zMem : ℕ → ℕ := fun _ => 0
    diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w td' M zMem)
      (packArray (offTD U w N) (globalPtrBits N) w td M zMem) ≤ 2 + 2 * W
  diff_dt :
    let M := maxTailItems N
    let zMem : ℕ → ℕ := fun _ => 0
    diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w dt' M zMem)
      (packArray (offDT U w N) (globalPtrBits N) w dt M zMem) ≤ 2 + 2 * W

theorem pushBackSlotProg_window {U V w N m₀ b q_val v_val : ℕ}
    {L_p L_m : List ℕ} (hnodup_p : L_p.Nodup) (hnodup_m : L_m.Nodup)
    (hw : 0 < w) (s : Memory.State) (td dt : ℕ → ℕ)
    (hinv : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem))
    (hb : b < numBuckets N)
    (htot : Succinct.totalSlots N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem) < N)
    (hq_lt : q_val < 2 ^ quotientBits U N) (hv_lt : v_val < 2 ^ valBits V)
    (hm₀ : m₀ ≤ Succinct.totalSlots N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem))
    (htd : TailDenseInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 0)
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 1) td dt)
    (htd_b : ∀ i, td i < max (maxTailItems N) 1)
    (hdt_b : ∀ i, dt i < max (maxTailItems N) 1) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s
      (Succinct.pushBackSlotProg U V w N h_space (((0, b), q_val), v_val))
    ∃ td' dt' W, WindowStepPost U V w N m₀ L_p L_m s s' td dt td' dt' W := by
  intro h_space s'
  let gm₀ := Succinct.gmAt 0 U V w N h_space s.mem
  let qA₀ := Succinct.quotAt 0 U w N h_space s.mem
  let vA₀ := Succinct.valAt 0 U V w N h_space s.mem
  let d := (((0, b), q_val), v_val)
  by_cases hb0 : bucketBits N = 0
  · refine ⟨td, dt, 0, ?_⟩
    have hb_eq : b = 0 := by
      have : numBuckets N = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    have htot0 : gm₀ 0 < N := by
      unfold Succinct.totalSlots at htot; rwa [ite_eq_left hb0] at htot
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hc1_lt : gm₀ 0 + 1 < 2 ^ globalPtrBits N :=
      Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    obtain ⟨_, _, hq1, hv1, _, hg1⟩ :=
      Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := h_space) hw htot0 hq_lt s
    let s₁ := (Memory.spec 0).clientState s
      (Succinct.writeQuotProg U w N h_space ((0, gm₀ 0), q_val))
    obtain ⟨_, _, hq2, hv2, _, hg2⟩ :=
      Succinct.writeValProg_effect (base := 0) (h_space := h_space) hw htot0 hv_lt s₁
    let s₂ := (Memory.spec 0).clientState s₁
      (Succinct.writeValProg U V w N h_space ((0, gm₀ 0), v_val))
    obtain ⟨_, _, hq3, hv3, _, hg3⟩ :=
      Succinct.writeGMProg_effect (base := 0) (V := V) (h_space := h_space) hw h0_lt hc1_lt s₂
    let s₃ := (Memory.spec 0).clientState s₂
      (Succinct.writeGMProg U V w N h_space ((0, 0), gm₀ 0 + 1))
    have hst : s' = s₃ := by
      change (Memory.spec 0).clientState s (Succinct.pushBackSlotProg U V w N h_space d) = s₃
      unfold Succinct.pushBackSlotProg
      simp only [hb0, ↓reduceIte, d]
      rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg,
        Succinct.clientResult_readGMProg s h0_lt]
      repeat rw [StateTransitionSpec.clientState_bind]
    have hgm'_eq : Succinct.gmAt 0 U V w N h_space s'.mem =
        Function.update gm₀ 0 (gm₀ 0 + 1) := by
      rw [hst, hg3, hg2, hg1]
    have hgm'1 : Succinct.gmAt 0 U V w N h_space s'.mem 1 = 0 := by
      rw [hgm'_eq, Function.update_of_ne (by decide)]
      have hM0 : maxTailItems N = 0 := by simp [maxTailItems, tailCapPerBucket, hb0]
      by_contra hpos
      have := htd.td_lt 0 (Nat.pos_of_ne_zero hpos)
      omega
    refine ⟨?_, htd_b, hdt_b, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hgm'1]; exact tailDenseInv_zero N _ td dt
    · have hpot' : slotPotential N (Succinct.gmAt 0 U V w N h_space s'.mem) = 0 := by
        unfold slotPotential; simp [hb0]
      have hpot0 : slotPotential N gm₀ = 0 := by unfold slotPotential; simp [hb0]
      dsimp only [h_space, gm₀] at hpot' hpot0 ⊢
      omega
    · dsimp only
      rw [hst, hq3, hq2, hq1, hv3, hv2, hv1]
      have hup := diffCount2_update_both_le hnodup_p qA₀ vA₀ qA₀ vA₀ (gm₀ 0) q_val v_val
      rw [diffCount2_self] at hup
      dsimp only [h_space, qA₀, vA₀] at hup ⊢
      omega
    · dsimp only
      have hphys_eq : physByBase N (Succinct.gmAt 0 U V w N h_space s'.mem 0 * slabSize N) dt =
          physByBase N (gm₀ 0 * slabSize N) dt := by
        funext x; unfold physByBase; simp [hb0]
      rw [hphys_eq, diffCount_self]; omega
    · dsimp only; rw [diffCount_self]; omega
    · dsimp only; rw [diffCount_self]; omega
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    let M := maxTailItems N
    let K := slabSize N
    have hK_pos : 0 < K := slabSize_pos N
    have hM_pos : 0 < M := by
      unfold M maxTailItems tailCapPerBucket
      rw [ite_eq_right hb0]
      exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)
    have hmax_M : max M 1 = M := max_eq_left hM_pos
    have htd_M : ∀ i, td i < M := fun i => by have := htd_b i; omega
    have hdt_M : ∀ i, dt i < M := fun i => by have := hdt_b i; omega
    have hr0_lt : gm₀ (Succinct.gmRIdx b) < 2 * K := by
      have := (hinv.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this; rwa [ite_eq_right hb0] at this
    have htail₀ := hinv.multi_tail hb_pos
    have hslab₀ := hinv.multi_slab hb_pos
    have ht_lt : gm₀ 1 < M :=
      Succinct.ntails_lt_maxTailItems_of_r_lt hb (hinv.multi_r_bounds hb_pos b hb).1 htail₀
    have hm₀_le : m₀ ≤ gm₀ 0 * K + M := by
      unfold Succinct.totalSlots at hm₀
      rw [ite_eq_right hb0] at hm₀
      change m₀ ≤ gm₀ 0 * K + gm₀ 1 at hm₀
      omega
    -- Step 1: pushBackTailWriteProg
    obtain ⟨hres1, _, _, _, hgm1_eq, htail1, hslab1, htot1, hqb1, hrb1, hother1, _⟩ :=
      Succinct.pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    let s₁ := (Memory.spec 0).clientState s (Succinct.pushBackTailWriteProg U V w N h_space d)
    let gm₁ := Succinct.gmAt 0 U V w N h_space s₁.mem
    have hpres1 := gmAppendTail_preserves_nonTail gm₀ hb
      (hinv.multi_r_bounds hb_pos b hb).1 ht_lt
    have hgm1_0 : gm₁ 0 = gm₀ 0 := by
      dsimp only [gm₁]; rw [hgm1_eq, hpres1.1]
    have hgm1_1 : gm₁ 1 = gm₀ 1 + 1 := by
      dsimp only [gm₁]; rw [hgm1_eq, hpres1.2.1]
    -- Bounded diffCount2 for pushBackTailWriteProg (1 writeQuot + 1 writeVal at g_new)
    have hqv1 : diffCount2 L_p (Succinct.quotAt 0 U w N h_space s₁.mem)
        (Succinct.valAt 0 U V w N h_space s₁.mem) qA₀ vA₀ ≤ 1 := by
      obtain ⟨hres_app, _, _, hq_app, hv_app, _, _⟩ :=
        Succinct.appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
          hw hb_pos hb s htail₀ (hinv.multi_r_bounds hb_pos b hb).1
      let s_app := (Memory.spec 0).clientState s
        (Succinct.appendTailItemProg U V w N h_space (0, b))
      let g_new := (N - 1) - gm₀ 1
      have hg_new_lt : g_new < N := by
        unfold Succinct.totalSlots at htot; rw [ite_eq_right hb0] at htot
        dsimp only [g_new, gm₀] at htot ⊢; omega
      obtain ⟨_, _, hq_wq, hv_wq, _, _⟩ :=
        Succinct.writeQuotProg_effect (base := 0) (V := V) (h_space := h_space)
          hw hg_new_lt hq_lt s_app
      let s_wq := (Memory.spec 0).clientState s_app
        (Succinct.writeQuotProg U w N h_space ((0, g_new), q_val))
      obtain ⟨_, _, hq_wv, hv_wv, _, _⟩ :=
        Succinct.writeValProg_effect (base := 0) (h_space := h_space) hw hg_new_lt hv_lt s_wq
      have hst1 : s₁ = (Memory.spec 0).clientState s_wq
          (Succinct.writeValProg U V w N h_space ((0, g_new), v_val)) := by
        change (Memory.spec 0).clientState s (Succinct.pushBackTailWriteProg U V w N h_space d) = _
        unfold Succinct.pushBackTailWriteProg
        dsimp only [d]
        rw [StateTransitionSpec.clientState_bind, hres_app,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          Succinct.clientState_readGMProg]
      rw [hst1, hq_wv, hq_wq, hq_app, hv_wv, hv_wq, hv_app]
      have hup := diffCount2_update_both_le hnodup_p qA₀ vA₀ qA₀ vA₀ g_new q_val v_val
      rwa [diffCount2_self, Nat.zero_add] at hup
    -- Window update for pushBackTailWriteProg
    have hw0 : WindowInv M (gm₀ 0 * K) (gm₀ 1) td dt :=
      (windowInv_iff_tailDenseInv N (gm₀ 0) (gm₀ 1) td dt).mpr htd
    let p₁ := winGrowRight M (gm₀ 0 * K) (gm₀ 1) (td, dt)
    obtain ⟨hw1, htd1_M, hdt1_M⟩ := winGrowRight_spec hw0 (by omega) htd_M hdt_M
    let zMem : ℕ → ℕ := fun _ => 0
    have hphys1 : diffCount (List.range m₀) (physByBase N (gm₀ 0 * K) p₁.2)
        (physByBase N (gm₀ 0 * K) dt) ≤ 1 := by
      have hu := diffCount_physByBase_update_dt (N := N) (b_tail := gm₀ 0 * K) (m₀ := m₀)
        hm₀_le dt dt ((gm₀ 0 * K + gm₀ 1) % M) (gm₀ 1)
      rwa [diffCount_self, Nat.zero_add] at hu
    have hpack_td1 : diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p₁.1 M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td M zMem) ≤ 2 := by
      have hu := diffCount_packArray_update_le hnodup_m (offTD U w N) (globalPtrBits N) w
        td td (gm₀ 1) ((gm₀ 0 * K + gm₀ 1) % M) M zMem
      rwa [diffCount_self, Nat.zero_add] at hu
    have hpack_dt1 : diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p₁.2 M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt M zMem) ≤ 2 := by
      have hu := diffCount_packArray_update_le hnodup_m (offDT U w N) (globalPtrBits N) w
        dt dt ((gm₀ 0 * K + gm₀ 1) % M) (gm₀ 1) M zMem
      rwa [diffCount_self, Nat.zero_add] at hu
    -- Branch on whether promoteSlabProg runs
    by_cases hprom : gm₀ (Succinct.gmRIdx b) + 1 = 2 * K
    · have hst : s' = (Memory.spec 0).clientState s₁
          (Succinct.promoteSlabProg U V w N h_space (0, b)) := by
        change (Memory.spec 0).clientState s (Succinct.pushBackSlotProg U V w N h_space d) = _
        unfold Succinct.pushBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, ite_eq_left hprom]
      have htot0_lt : gm₀ 0 * K + gm₀ 1 < N := by
        unfold Succinct.totalSlots at htot; rwa [ite_eq_right hb0] at htot
      have hpre_prom : Succinct.PromoteSlabInv U V w N h_space 0 b s₁ := by
        refine ⟨hb, htail1, hslab1, by rw [hrb1, hprom], fun b' hb' hne => ?_, ?_⟩
        · rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
        · change gm₁ 0 * K + gm₁ 1 ≤ N
          rw [hgm1_0, hgm1_1]; omega
      obtain ⟨_, _, _, _, hqb2, hrb2, hother2, _⟩ :=
        Succinct.promoteSlabProg_effect hw hb_pos s₁ hpre_prom
      obtain ⟨hgm'0, hgm'1, hqv2⟩ :=
        promoteSlabProg_diffCount2_and_gm hnodup_p qA₀ vA₀ hw hb_pos s₁ hpre_prom
      rw [← hst] at hqb2 hrb2 hother2 hgm'0 hgm'1 hqv2
      let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
      change gm' 0 = gm₁ 0 + 1 at hgm'0
      change gm' 1 + K = gm₁ 1 at hgm'1
      have hgm'0_eq : gm' 0 * K = gm₀ 0 * K + K := by
        rw [hgm'0, hgm1_0, Nat.add_one_mul]
      have hgm'1_eq : gm' 1 + K = gm₀ 1 + 1 := by
        rw [hgm'1, hgm1_1]
      have hw1' : WindowInv M (gm₀ 0 * K) (gm' 1 + K) p₁.1 p₁.2 := by
        rwa [hgm'1_eq]
      let p' := iterShrinkLeft M (gm₀ 0 * K) (gm' 1) K p₁
      obtain ⟨hw', htd'_M, hdt'_M, hphys2, hpack_td2, hpack_dt2⟩ :=
        iterShrinkLeft_spec (N := N) (U := U) (w := w) (m₀ := m₀) hnodup_m
          (gm₀ 0 * K) (gm' 1) td dt K p₁ (by omega) hm₀_le hw1' htd1_M hdt1_M
      rw [← hgm'0_eq] at hw' hphys2
      have hupd : gm' (Succinct.gmQIdx b) =
            (pushBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
          gm' (Succinct.gmRIdx b) =
            (pushBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_left hprom]
        exact ⟨by dsimp only [gm', gm₁] at hqb2 hqb1 ⊢; rw [hqb2, hqb1], hrb2⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
          gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
        fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
          (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
      have hpot := Succinct.slotPotential_pushBack_le hb_pos hb hr0_lt hupd hother_all
      have hwork : pushBackWork K (gm₀ (Succinct.gmRIdx b)) = K := by
        unfold pushBackWork; rw [ite_eq_left hprom]
      rw [hwork] at hpot
      refine ⟨p'.1, p'.2, K,
        (windowInv_iff_tailDenseInv N (gm' 0) (gm' 1) p'.1 p'.2).mp hw',
        fun i => by rw [hmax_M]; exact htd'_M i,
        fun i => by rw [hmax_M]; exact hdt'_M i,
        hpot,
        by dsimp only [h_space, qA₀, vA₀, K] at hqv1 hqv2 ⊢; omega,
        by dsimp only [p', M, h_space, gm₀, gm', K] at hphys1 hphys2 ⊢; omega,
        by dsimp only [p', M, zMem, K] at hpack_td1 hpack_td2 ⊢; omega,
        by dsimp only [p', M, zMem, K] at hpack_dt1 hpack_dt2 ⊢; omega⟩
    · have hst : s' = s₁ := by
        change (Memory.spec 0).clientState s (Succinct.pushBackSlotProg U V w N h_space d) = s₁
        unfold Succinct.pushBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, ite_eq_right hprom]
        rfl
      let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
      have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hst]
      have hupd : gm' (Succinct.gmQIdx b) =
            (pushBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
          gm' (Succinct.gmRIdx b) =
            (pushBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
        unfold pushBackCounts; rw [ite_eq_right hprom, hgm'_eq]
        exact ⟨hqb1, hrb1⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
          gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') := by
        intro b' hb' hne; rw [hgm'_eq]; exact hother1 b' hb' hne
      have hpot := Succinct.slotPotential_pushBack_le hb_pos hb hr0_lt hupd hother_all
      have hwork : pushBackWork K (gm₀ (Succinct.gmRIdx b)) = 0 := by
        unfold pushBackWork; rw [ite_eq_right hprom]
      rw [hwork] at hpot
      have hw' : WindowInv M (gm' 0 * K) (gm' 1) p₁.1 p₁.2 := by
        rw [hgm'_eq, hgm1_0, hgm1_1]; exact hw1
      refine ⟨p₁.1, p₁.2, 0,
        (windowInv_iff_tailDenseInv N (gm' 0) (gm' 1) p₁.1 p₁.2).mp hw',
        fun i => by rw [hmax_M]; exact htd1_M i,
        fun i => by rw [hmax_M]; exact hdt1_M i,
        hpot,
        by dsimp only [h_space, qA₀, vA₀] at hqv1 ⊢; rw [hst]; omega,
        by have h0 : gm' 0 = gm₀ 0 := by rw [hgm'_eq, hgm1_0]
           dsimp only [h_space, gm₀, gm', K] at h0 hphys1 ⊢; rw [h0]; omega,
        by dsimp only [M, zMem] at hpack_td1 ⊢; omega,
        by dsimp only [M, zMem] at hpack_dt1 ⊢; omega⟩

theorem popBackSlotProg_window {U V w N m₀ b : ℕ}
    {L_p L_m : List ℕ} (hnodup_p : L_p.Nodup) (hnodup_m : L_m.Nodup)
    (hw : 0 < w) (s : Memory.State) (td dt : ℕ → ℕ)
    (hinv : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem))
    (hb : b < numBuckets N)
    (hbc : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem) b)
    (hm₀ : m₀ + 1 ≤ Succinct.totalSlots N
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem))
    (htd : TailDenseInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 0)
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 1) td dt)
    (htd_b : ∀ i, td i < max (maxTailItems N) 1)
    (hdt_b : ∀ i, dt i < max (maxTailItems N) 1) :
    let h_space := Succinct.hashSpace U w N
    let s' := (Memory.spec 0).clientState s
      (Succinct.popBackSlotProg U V w N h_space (0, b))
    ∃ td' dt' W, WindowStepPost U V w N m₀ L_p L_m s s' td dt td' dt' W ∧
      ∀ qA_b vA_b,
        diffCount2 L_p (Succinct.quotAt 0 U w N h_space s'.mem)
          (Succinct.valAt 0 U V w N h_space s'.mem) qA_b vA_b ≤
          diffCount2 L_p (Succinct.quotAt 0 U w N h_space s.mem)
            (Succinct.valAt 0 U V w N h_space s.mem) qA_b vA_b + 1 + 2 * W := by
  intro h_space s'
  let gm₀ := Succinct.gmAt 0 U V w N h_space s.mem
  let qA₀ := Succinct.quotAt 0 U w N h_space s.mem
  let vA₀ := Succinct.valAt 0 U V w N h_space s.mem
  let d := (0, b)
  by_cases hb0 : bucketBits N = 0
  · refine ⟨td, dt, 0, ?_, fun qA_b vA_b => ?_⟩
    · have hb_eq : b = 0 := by
        have : numBuckets N = 1 := by simp [numBuckets, hb0]
        omega
      subst hb_eq
      have hbc0 : 1 ≤ gm₀ 0 := by unfold Succinct.bCount at hbc; simpa [hb0] using hbc
      have hc_le : gm₀ 0 ≤ N := hinv.single_valid hb0
      have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
      have hc1_lt : gm₀ 0 - 1 < 2 ^ globalPtrBits N :=
        Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by omega)
      obtain ⟨_, _, hq1, hv1, _, hg1⟩ :=
        Succinct.writeGMProg_effect (base := 0) (V := V) (h_space := h_space) hw h0_lt hc1_lt s
      let s₁ := (Memory.spec 0).clientState s
        (Succinct.writeGMProg U V w N h_space ((0, 0), gm₀ 0 - 1))
      have hst : s' = s₁ := by
        change (Memory.spec 0).clientState s (Succinct.popBackSlotProg U V w N h_space d) = s₁
        unfold Succinct.popBackSlotProg; simp only [hb0, ↓reduceIte, d]
        rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg,
          Succinct.clientResult_readGMProg s h0_lt]
      have hgm'_eq : Succinct.gmAt 0 U V w N h_space s'.mem =
          Function.update gm₀ 0 (gm₀ 0 - 1) := by rw [hst, hg1]
      have hgm'1 : Succinct.gmAt 0 U V w N h_space s'.mem 1 = 0 := by
        rw [hgm'_eq, Function.update_of_ne (by decide)]
        have hM0 : maxTailItems N = 0 := by simp [maxTailItems, tailCapPerBucket, hb0]
        by_contra hpos; have := htd.td_lt 0 (Nat.pos_of_ne_zero hpos); omega
      refine ⟨by dsimp only; rw [hgm'1]; exact tailDenseInv_zero N _ td dt,
        htd_b, hdt_b, ?_, by dsimp only; rw [hst, hq1, hv1, diffCount2_self]; omega,
        ?_, by dsimp only; rw [diffCount_self]; omega, by dsimp only; rw [diffCount_self]; omega⟩
      · have hpot' : slotPotential N (Succinct.gmAt 0 U V w N h_space s'.mem) = 0 := by
          unfold slotPotential; simp [hb0]
        have hpot0 : slotPotential N gm₀ = 0 := by unfold slotPotential; simp [hb0]
        dsimp only [h_space, gm₀] at hpot' hpot0 ⊢
        omega
      · dsimp only
        have hphys_eq : physByBase N (Succinct.gmAt 0 U V w N h_space s'.mem 0 * slabSize N) dt =
            physByBase N (gm₀ 0 * slabSize N) dt := by funext x; unfold physByBase; simp [hb0]
        rw [hphys_eq, diffCount_self]; omega
    · have hb_eq : b = 0 := by
        have : numBuckets N = 1 := by simp [numBuckets, hb0]
        omega
      subst hb_eq
      have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
      have hc1_lt : gm₀ 0 - 1 < 2 ^ globalPtrBits N :=
        Succinct.lt_two_pow_globalPtrBits_of_le_n_max (by
          have : gm₀ 0 ≤ N := hinv.single_valid hb0; omega)
      obtain ⟨_, _, hq1, hv1, _, _⟩ :=
        Succinct.writeGMProg_effect (base := 0) (V := V) (h_space := h_space) hw h0_lt hc1_lt s
      have hst : s' = (Memory.spec 0).clientState s
          (Succinct.writeGMProg U V w N h_space ((0, 0), gm₀ 0 - 1)) := by
        change (Memory.spec 0).clientState s (Succinct.popBackSlotProg U V w N h_space d) = _
        unfold Succinct.popBackSlotProg; simp only [hb0, ↓reduceIte, d]
        rw [StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg,
          Succinct.clientResult_readGMProg s h0_lt]
      rw [hst, hq1, hv1]; omega
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    let M := maxTailItems N
    let K := slabSize N
    have hK_pos : 0 < K := slabSize_pos N
    have hM_pos : 0 < M := by
      unfold M maxTailItems tailCapPerBucket; rw [ite_eq_right hb0]
      exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)
    have hmax_M : max M 1 = M := max_eq_left hM_pos
    have htd_M : ∀ i, td i < M := fun i => by have := htd_b i; omega
    have hdt_M : ∀ i, dt i < M := fun i => by have := hdt_b i; omega
    have hr0_pos : 1 ≤ gm₀ (Succinct.gmRIdx b) :=
      Succinct.pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hr0_lt : gm₀ (Succinct.gmRIdx b) < 2 * K := by
      have := (hinv.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this; rwa [ite_eq_right hb0] at this
    have htail₀ := hinv.multi_tail hb_pos
    have hslab₀ := hinv.multi_slab hb_pos
    have htot₀ := hinv.multi_total_le hb_pos
    obtain ⟨_, _, hq1, hv1, _, hgm1_eq⟩ :=
      Succinct.removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos hb s htail₀ hr0_pos
    let s₁ := (Memory.spec 0).clientState s (Succinct.removeLastTailItemProg U V w N h_space d)
    let gm₁ := Succinct.gmAt 0 U V w N h_space s₁.mem
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr0_pos htail₀
    have htail1 : TailBijection N gm₁ (fun b' => gm₁ (Succinct.gmRIdx b')) (gm₁ 1) := by
      dsimp only [gm₁]; rw [hgm1_eq]; exact tailBijection_gmRemoveTail hb hr0_pos htail₀
    have hslab1 : SlabBijection N gm₁ (fun b' => gm₁ (Succinct.gmQIdx b')) (gm₁ 0) := by
      dsimp only [gm₁]; rw [hgm1_eq]; exact (slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀).2
    have hgm1_pos : 1 ≤ gm₀ 1 := by
      have := Succinct.r_le_ntails_of_tailBijection htail₀ hb
      dsimp only [gm₀, h_space] at hr0_pos ⊢; omega
    have hgm1_0 : gm₁ 0 = gm₀ 0 := by dsimp only [gm₁]; rw [hgm1_eq, hpres1.1]
    have hgm1_1 : gm₁ 1 + 1 = gm₀ 1 := by dsimp only [gm₁]; rw [hgm1_eq, hpres1.2.1]; omega
    have hqb1 : gm₁ (Succinct.gmQIdx b) = gm₀ (Succinct.gmQIdx b) := by
      dsimp only [gm₁]; rw [hgm1_eq, hpres1.2.2.2.2.1 b hb]
    have hrb1 : gm₁ (Succinct.gmRIdx b) = gm₀ (Succinct.gmRIdx b) - 1 := by
      dsimp only [gm₁]; rw [hgm1_eq, hpres1.2.2.1]
    have hother1 : ∀ b' < numBuckets N, b' ≠ b →
        gm₁ (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
        gm₁ (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') := fun b' hb' hne => by
      dsimp only [gm₁]
      exact ⟨by rw [hgm1_eq, hpres1.2.2.2.2.1 b' hb'],
        by rw [hgm1_eq, hpres1.2.2.2.1 b' hb' hne]⟩
    have hqv1_gen : ∀ qA_b vA_b, diffCount2 L_p (Succinct.quotAt 0 U w N h_space s₁.mem)
        (Succinct.valAt 0 U V w N h_space s₁.mem) qA_b vA_b ≤
        diffCount2 L_p qA₀ vA₀ qA_b vA_b + 1 := fun qA_b vA_b => by
      rw [hq1, hv1]
      exact diffCount2_update_both_le hnodup_p qA₀ vA₀ qA_b vA_b _ _ _
    have hqv1 : diffCount2 L_p (Succinct.quotAt 0 U w N h_space s₁.mem)
        (Succinct.valAt 0 U V w N h_space s₁.mem) qA₀ vA₀ ≤ 1 := by
      have := hqv1_gen qA₀ vA₀; rwa [diffCount2_self, Nat.zero_add] at this
    have hw0 : WindowInv M (gm₀ 0 * K) (gm₁ 1 + 1) td dt := by
      rw [hgm1_1]; exact (windowInv_iff_tailDenseInv N (gm₀ 0) (gm₀ 1) td dt).mpr htd
    have hnt1_le : gm₁ 1 + 1 ≤ M := by rw [hgm1_1]; exact htail₀.ntails_le
    let p₁ := winShrinkRight M (gm₀ 0 * K) (gm₁ 1) (td, dt)
    obtain ⟨hw1, htd1_M, hdt1_M⟩ := winShrinkRight_spec hw0 hnt1_le htd_M hdt_M
    let zMem : ℕ → ℕ := fun _ => 0
    have hm₀_le0 : m₀ ≤ gm₀ 0 * K + M := by
      unfold Succinct.totalSlots at hm₀; rw [ite_eq_right hb0] at hm₀
      have := htail₀.ntails_le; change m₀ + 1 ≤ gm₀ 0 * K + gm₀ 1 at hm₀; omega
    have hphys1 : diffCount (List.range m₀) (physByBase N (gm₀ 0 * K) p₁.2)
        (physByBase N (gm₀ 0 * K) dt) ≤ 1 := by
      have hu := diffCount_physByBase_update_dt (N := N) (b_tail := gm₀ 0 * K) (m₀ := m₀)
        hm₀_le0 dt dt (td (gm₁ 1)) (dt ((gm₀ 0 * K + gm₁ 1) % M))
      rwa [diffCount_self, Nat.zero_add] at hu
    have hpack_td1 : diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p₁.1 M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td M zMem) ≤ 2 := by
      have hu := diffCount_packArray_update_le hnodup_m (offTD U w N) (globalPtrBits N) w
        td td (dt ((gm₀ 0 * K + gm₁ 1) % M)) (td (gm₁ 1)) M zMem
      rwa [diffCount_self, Nat.zero_add] at hu
    have hpack_dt1 : diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p₁.2 M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt M zMem) ≤ 2 := by
      have hu := diffCount_packArray_update_le hnodup_m (offDT U w N) (globalPtrBits N) w
        dt dt (td (gm₁ 1)) (dt ((gm₀ 0 * K + gm₁ 1) % M)) M zMem
      rwa [diffCount_self, Nat.zero_add] at hu
    have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen N := Succinct.gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b < globalMetaLen N := Succinct.gmQIdx_lt hb_pos hb
    have hres_r : (Memory.spec 0).clientResult s₁
        (Succinct.readGMProg U V w N h_space (0, 4 + 3 * b + 1)) = gm₁ (Succinct.gmRIdx b) :=
      Succinct.clientResult_readGMProg s₁ hr_idx_lt
    have hres_q : (Memory.spec 0).clientResult s₁
        (Succinct.readGMProg U V w N h_space (0, 4 + 3 * b)) = gm₁ (Succinct.gmQIdx b) :=
      Succinct.clientResult_readGMProg s₁ hq_idx_lt
    by_cases hdem : gm₀ (Succinct.gmRIdx b) = 1 ∧ 0 < gm₀ (Succinct.gmQIdx b)
    · have hr1_eq0 : gm₁ (Succinct.gmRIdx b) = 0 := by rw [hrb1, hdem.1]
      have hq1_pos : 0 < gm₁ (Succinct.gmQIdx b) := by rw [hqb1]; exact hdem.2
      have hst : s' = (Memory.spec 0).clientState s₁
          (Succinct.demoteSlabProg U V w N h_space (0, b)) := by
        change (Memory.spec 0).clientState s (Succinct.popBackSlotProg U V w N h_space d) = _
        unfold Succinct.popBackSlotProg; simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_q,
          ite_eq_left hr1_eq0, ite_eq_left hq1_pos]
      have hpre_dem : Succinct.DemoteSlabInv U V w N h_space 0 b s₁ := by
        refine ⟨hb, htail1, hslab1, hr1_eq0, hq1_pos, fun b' hb' hne => ?_, ?_⟩
        · dsimp only [gm₁] at hother1
          rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
        · change gm₁ 0 * K + gm₁ 1 ≤ N
          rw [hgm1_0]
          dsimp only [gm₀, h_space, K] at htot₀ hgm1_1 ⊢; omega
      obtain ⟨_, _, _, hinv2, hqb2, hrb2, hother2, _⟩ :=
        Succinct.demoteSlabProg_effect hw hb_pos s₁ hpre_dem
      obtain ⟨hgm'0, hgm'1, hqv2⟩ :=
        demoteSlabProg_diffCount2_and_gm hnodup_p qA₀ vA₀ hw hb_pos s₁ hpre_dem
      rw [← hst] at hinv2 hqb2 hrb2 hother2 hgm'0 hgm'1 hqv2
      let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
      change Succinct.SlotStoreInv N gm' at hinv2
      change gm' 0 + 1 = gm₁ 0 at hgm'0
      change gm' 1 = gm₁ 1 + K at hgm'1
      have hgm0_eq : gm₀ 0 * K = gm' 0 * K + K := by rw [← hgm1_0, ← hgm'0, Nat.add_one_mul]
      have hnt'_le : gm₁ 1 + K ≤ M := by rw [← hgm'1]; exact (hinv2.multi_tail hb_pos).ntails_le
      have hm₀_le' : m₀ ≤ gm' 0 * K + M := by
        unfold Succinct.totalSlots at hm₀; rw [ite_eq_right hb0] at hm₀
        change m₀ + 1 ≤ gm₀ 0 * K + gm₀ 1 at hm₀; omega
      have hw1' : WindowInv M (gm' 0 * K + K) (gm₁ 1) p₁.1 p₁.2 := by rwa [← hgm0_eq]
      let p' := iterGrowLeft M (gm' 0 * K) (gm₁ 1) K p₁
      obtain ⟨hw', htd'_M, hdt'_M, hphys2, hpack_td2, hpack_dt2⟩ :=
        iterGrowLeft_spec (N := N) (U := U) (w := w) (m₀ := m₀) hnodup_m
          K (gm' 0 * K) (gm₁ 1) td dt p₁ hnt'_le hm₀_le' hw1' htd1_M hdt1_M
      rw [← hgm'1] at hw'
      rw [← hgm0_eq] at hphys2
      have hupd : gm' (Succinct.gmQIdx b) =
            (popBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
          gm' (Succinct.gmRIdx b) =
            (popBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
        unfold popBackCounts; rw [ite_eq_left hdem]
        exact ⟨by dsimp only [gm', gm₁] at hqb2 hqb1 ⊢; rw [hqb2, hqb1], hrb2⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
          gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') :=
        fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
          (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
      have hpot := Succinct.slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
      have hwork : popBackWork K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b)) = K := by
        unfold popBackWork; rw [ite_eq_left hdem]
      rw [hwork] at hpot
      refine ⟨p'.1, p'.2, K, ⟨(windowInv_iff_tailDenseInv N (gm' 0) (gm' 1) p'.1 p'.2).mp hw',
        fun i => by rw [hmax_M]; exact htd'_M i,
        fun i => by rw [hmax_M]; exact hdt'_M i,
        hpot,
        by dsimp only [h_space, qA₀, vA₀, K] at hqv1 hqv2 ⊢; omega,
        by dsimp only [p', M, h_space, gm₀, gm', K] at hphys1 hphys2 ⊢; omega,
        by dsimp only [p', M, zMem, K] at hpack_td1 hpack_td2 ⊢; omega,
        by dsimp only [p', M, zMem, K] at hpack_dt1 hpack_dt2 ⊢; omega⟩,
        fun qA_b vA_b => ?_⟩
      obtain ⟨_, _, hqv2_b⟩ :=
        demoteSlabProg_diffCount2_and_gm hnodup_p qA_b vA_b hw hb_pos s₁ hpre_dem
      rw [← hst] at hqv2_b
      have := hqv1_gen qA_b vA_b
      dsimp only [h_space, qA₀, vA₀, K] at this hqv2_b ⊢
      omega
    · have hst : s' = s₁ := by
        change (Memory.spec 0).clientState s (Succinct.popBackSlotProg U V w N h_space d) = s₁
        unfold Succinct.popBackSlotProg; simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readGMProg, hres_q]
        by_cases hr1 : gm₁ (Succinct.gmRIdx b) = 0
        · have hq1_zero : ¬0 < gm₁ (Succinct.gmQIdx b) := fun hq_pos =>
            hdem ⟨by rw [hrb1] at hr1; omega, by rwa [hqb1] at hq_pos⟩
          rw [ite_eq_left hr1, ite_eq_right hq1_zero]; rfl
        · rw [ite_eq_right hr1]; rfl
      let gm' := Succinct.gmAt 0 U V w N h_space s'.mem
      have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hst]
      have hupd : gm' (Succinct.gmQIdx b) =
            (popBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).1 ∧
          gm' (Succinct.gmRIdx b) =
            (popBackCounts K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b))).2 := by
        unfold popBackCounts; rw [ite_eq_right hdem, hgm'_eq]; exact ⟨hqb1, hrb1⟩
      have hother_all : ∀ b' < numBuckets N, b' ≠ b →
          gm' (Succinct.gmQIdx b') = gm₀ (Succinct.gmQIdx b') ∧
          gm' (Succinct.gmRIdx b') = gm₀ (Succinct.gmRIdx b') := by
        intro b' hb' hne; rw [hgm'_eq]; exact hother1 b' hb' hne
      have hpot := Succinct.slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
      have hwork : popBackWork K (gm₀ (Succinct.gmQIdx b)) (gm₀ (Succinct.gmRIdx b)) = 0 := by
        unfold popBackWork; rw [ite_eq_right hdem]
      rw [hwork] at hpot
      have hw' : WindowInv M (gm' 0 * K) (gm' 1) p₁.1 p₁.2 := by
        rw [hgm'_eq, hgm1_0]; exact hw1
      refine ⟨p₁.1, p₁.2, 0, ⟨(windowInv_iff_tailDenseInv N (gm' 0) (gm' 1) p₁.1 p₁.2).mp hw',
        fun i => by rw [hmax_M]; exact htd1_M i,
        fun i => by rw [hmax_M]; exact hdt1_M i,
        hpot,
        by dsimp only [h_space, qA₀, vA₀] at hqv1 ⊢; rw [hst]; omega,
        by have h0 : gm' 0 = gm₀ 0 := by rw [hgm'_eq, hgm1_0]
           dsimp only [h_space, gm₀, gm', K] at h0 hphys1 ⊢; rw [h0]; omega,
        by dsimp only [M, zMem] at hpack_td1 ⊢; omega,
        by dsimp only [M, zMem] at hpack_dt1 ⊢; omega⟩,
        fun qA_b vA_b => by
          rw [hst]; have := hqv1_gen qA_b vA_b; dsimp only [h_space, qA₀, vA₀] at this ⊢; omega⟩

/-! ## Section 4: Window and `diffCount` transitions for `insert` and `delete` -/

theorem insertWithHashProg_window {U V w N m₀ : ℕ}
    {L_p L_m : List ℕ} (hnodup_p : L_p.Nodup) (hnodup_m : L_m.Nodup)
    (hwf : Succinct.DictParamsWf U V w N)
    (henv : Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s : Memory.State}
    (hinv : Succinct.DictStateInv U V w N 0 θ s_abs s)
    (u : Fin U) (v : ℕ)
    (hval : (Dynamic.spec U V N).valid s_abs (.insert u v))
    (hm₀ : m₀ ≤ (Dynamic.dom s_abs).card)
    (td dt : ℕ → ℕ)
    (htd : TailDenseInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 0)
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 1) td dt)
    (htd_b : ∀ i, td i < max (maxTailItems N) 1)
    (hdt_b : ∀ i, dt i < max (maxTailItems N) 1) :
    let h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
    let d := (((0, u.val), v), h_q)
    let prog := Succinct.insertWithHashProg U V w N d
    let s' := (Memory.spec 0).clientState s prog
    ∃ td' dt' W, WindowStepPost U V w N m₀ L_p L_m s s' td dt td' dt' W := by
  intro h_q d prog s'
  have hw : 0 < w := hwf.1
  let h_space := Succinct.hashSpace U w N
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  let h1 := Succinct.hValOfSeed U N θ
  let b := feistelBucket (bucketBits N) h1 u.val
  let q := keyQuotient (bucketBits N) u.val
  let m_micro := Succinct.mOfSeed U N θ q
  have hb_eq : (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1)) = b :=
    Succinct.and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q
  have hq_eq : u.val >>> bucketBits N = q := Nat.shiftRight_eq_div_pow u.val (bucketBits N)
  have hm_eq : h_q >>> bucketBits N = m_micro := rfl
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hm_lt : m_micro < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
  have hq_lt : q < 2 ^ quotientBits U N := keyQuotient_lt_two_pow_quotientBits hwf.2.1 u.isLt
  have hv_lt : v < 2 ^ valBits V := hval.2.trans_le (Nat.le_pow_clog (by decide) V)
  have hs'_eq : s' = (Memory.spec 0).clientState s
      (Succinct.insertBodyProg U V w N h_space ((((0, b), q), v), m_micro)) := by
    refine congrArg ((Memory.spec 0).clientState s) ?_
    change Succinct.insertBodyProg U V w N h_space
      ((((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
        u.val >>> bucketBits N), v), h_q >>> bucketBits N) = _
    rw [hb_eq, hq_eq, hm_eq]
  have hsb := Succinct.searchBucketProg_bucket_spec hb_inv henv hb_lt rfl hm_lt (q_target := q)
  dsimp only at hsb
  set res := (Memory.spec 0).clientResult s
    (Succinct.searchBucketProg U V w N h_space (((0, b), q), m_micro))
  have hres := hsb.2.2
  by_cases hex : ∃ j < Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s.mem) b,
      Succinct.quotAt 0 U w N h_space s.mem
        (Succinct.slotOf N (Succinct.gmAt 0 U V w N h_space s.mem) b j) = q
  · rw [ite_eq_left hex] at hres
    rcases hres with ⟨hf1, hj_lt, _, hphys_eq⟩
    have hphys_lt : res.2 < N := by
      rw [hphys_eq]; exact (Succinct.slotOf_lt_and_injective hb_inv.hslot).1 b hb_lt res.1.2 hj_lt
    have hs'_wv : s' = (Memory.spec 0).clientState s
        (Succinct.writeValProg U V w N h_space ((0, res.2), v)) := by
      rw [hs'_eq]; unfold Succinct.insertBodyProg; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v)
         else Succinct.insertNewProg U V w N h_space ((((0, b), q), v), m_micro)) = _
      rw [ite_eq_left hf1]
    have eff := Succinct.writeValProg_effect (U := U) (base := 0) (h_space := h_space)
      hw hphys_lt hv_lt s
    have hgm_eq : Succinct.gmAt 0 U V w N h_space s'.mem =
        Succinct.gmAt 0 U V w N h_space s.mem := by rw [hs'_wv, eff.2.2.2.2.2]
    refine ⟨td, dt, 0, by dsimp only; rw [hgm_eq]; exact htd, htd_b, hdt_b,
      by dsimp only [h_space] at hgm_eq ⊢; rw [hgm_eq]; omega, ?_,
      by dsimp only [h_space] at hgm_eq ⊢; rw [hgm_eq, diffCount_self]; omega,
      by dsimp only; rw [diffCount_self]; omega, by dsimp only; rw [diffCount_self]; omega⟩
    dsimp only; rw [hs'_wv, eff.2.2.1, eff.2.2.2.1]
    have hup := diffCount2_update_both_le hnodup_p
      (Succinct.quotAt 0 U w N h_space s.mem) (Succinct.valAt 0 U V w N h_space s.mem)
      (Succinct.quotAt 0 U w N h_space s.mem) (Succinct.valAt 0 U V w N h_space s.mem)
      res.2 (Succinct.quotAt 0 U w N h_space s.mem res.2) v
    rw [Function.update_eq_self, diffCount2_self] at hup
    dsimp only [h_space] at hup ⊢; omega
  · rw [ite_eq_right hex] at hres
    have hB_eq : Succinct.bucketMapOfState U N h1 s_abs b q = s_abs u :=
      Succinct.bucketMapOfState_feistelBucket hwf.2.1 h1 s_abs u
    have hnot_some : ¬(s_abs u).isSome := by
      rw [← hB_eq]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hex
    have htot : Succinct.totalSlots N (Succinct.gmAt 0 U V w N h_space s.mem) < N := by
      rw [hinv.htot]; exact hval.1.symm.resolve_left hnot_some
    have hne1 : res.1.1 ≠ 1 := by omega
    let s₁ := (Memory.spec 0).clientState s
      (Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v))
    let j_new := Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s.mem) b
    have hs'_pr : s' = (Memory.spec 0).clientState s₁
        (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m_micro), j_new)) := by
      rw [hs'_eq]; unfold Succinct.insertBodyProg Succinct.insertNewProg; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then Succinct.writeValProg U V w N h_space ((0, res.2), v)
         else do
           let tot ← Succinct.readTotalSlotsProg U V w N h_space 0
           if tot < N then do
             let j_new ← Succinct.readBucketCountProg U V w N h_space (0, b)
             Succinct.pushBackSlotProg U V w N h_space (((0, b), q), v)
             Succinct.prependIfIndexedProg U V w N h_space (((0, b), m_micro), j_new)
           else pure ()) = _
      rw [ite_eq_right hne1, StateTransitionSpec.clientState_bind,
        Succinct.clientState_readTotalSlotsProg, Succinct.clientResult_readTotalSlotsProg,
        ite_eq_left htot, StateTransitionSpec.clientState_bind,
        Succinct.clientState_readBucketCountProg,
        Succinct.clientResult_readBucketCountProg (0, b) s hb_lt,
        StateTransitionSpec.clientState_bind]
    have eff_pb := Succinct.pushBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := N)
      (h_space := h_space) (base := 0) (b := b) (q_val := q) (v_val := v)
      hw s hb_inv.hslot hb_lt htot hq_lt hv_lt
    have hj_new_lt_n : j_new < N :=
      lt_of_le_of_lt (Succinct.bCount_le_totalSlots hb_inv.hslot b hb_lt) htot
    have hj_not : ∀ m' < numMicroPerBucket N, j_new ∉ L b m' := fun m' hm' hj_in => by
      have hlt := ((hb_inv.hchain_mem b hb_lt m' hm' j_new).mp hj_in).1
      dsimp only [j_new, h_space] at hlt; omega
    have eff_pr := Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
      (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_micro) (j_new := j_new)
      hw hb_lt hm_lt hj_new_lt_n (hb_inv.hchains.of_lm_eq eff_pb.2.2.1) hj_not
    have hgm'_eq : Succinct.gmAt 0 U V w N h_space s'.mem =
        Succinct.gmAt 0 U V w N h_space s₁.mem := by rw [hs'_pr, eff_pr.2.2.2.2.1]
    have hm₀_tot : m₀ ≤ Succinct.totalSlots N (Succinct.gmAt 0 U V w N h_space s.mem) := by
      rwa [hinv.htot]
    obtain ⟨td', dt', W, hpost⟩ :=
      pushBackSlotProg_window hnodup_p hnodup_m hw s td dt
        hb_inv.hslot hb_lt htot hq_lt hv_lt hm₀_tot htd htd_b hdt_b
    refine ⟨td', dt', W, by dsimp only; rw [hgm'_eq]; exact hpost.tailDense,
      hpost.td_lt, hpost.dt_lt,
      by dsimp only; rw [hgm'_eq]; exact hpost.pot_le,
      by dsimp only; rw [hs'_pr, eff_pr.2.2.1, eff_pr.2.2.2.1]; exact hpost.diff_qv,
      by dsimp only; rw [hgm'_eq]; exact hpost.diff_phys,
      hpost.diff_td, hpost.diff_dt⟩

theorem deleteFinishWithHashProg_window {U V w N m₀ : ℕ}
    {L_p L_m : List ℕ} (hnodup_p : L_p.Nodup) (hnodup_m : L_m.Nodup)
    (hwf : Succinct.DictParamsWf U V w N)
    (henv : Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s : Memory.State}
    (hinv : Succinct.DictStateInv U V w N 0 θ s_abs s)
    (u : Fin U)
    (hm₀ : m₀ ≤ (Dynamic.dom (Function.update s_abs u none)).card)
    (td dt : ℕ → ℕ)
    (htd : TailDenseInv N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 0)
      (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s.mem 1) td dt)
    (htd_b : ∀ i, td i < max (maxTailItems N) 1)
    (hdt_b : ∀ i, dt i < max (maxTailItems N) 1) :
    let h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
    let d_prep := ((0, u.val), h_q)
    let prep := (Memory.spec 0).clientResult s (Succinct.deletePrepWithHashProg U V w N d_prep)
    let h_q_last := Succinct.hValOfSeed U N θ prep.2
    let d_fin := ((((0, u.val), h_q), prep.1), h_q_last)
    let prog_fin := Succinct.deleteFinishWithHashProg U V w N d_fin
    let s' := (Memory.spec 0).clientState s prog_fin
    ∃ td' dt' W, WindowStepPost U V w N m₀ L_p L_m s s' td dt td' dt' W := by
  intro h_q d_prep prep h_q_last d_fin prog_fin s'
  have hw : 0 < w := hwf.1
  let h_space := Succinct.hashSpace U w N
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  let h1 := Succinct.hValOfSeed U N θ
  let b := feistelBucket (bucketBits N) h1 u.val
  let q := keyQuotient (bucketBits N) u.val
  let m_micro := Succinct.mOfSeed U N θ q
  have hb_eq : (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1)) = b :=
    Succinct.and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q
  have hq_eq : u.val >>> bucketBits N = q := Nat.shiftRight_eq_div_pow u.val (bucketBits N)
  have hm_eq : h_q >>> bucketBits N = m_micro := rfl
  have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hm_lt : m_micro < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
  have hprep_res : prep = (Memory.spec 0).clientResult s
      (Succinct.deletePrepProg U V w N h_space (((0, b), q), m_micro)) := by
    refine congrArg ((Memory.spec 0).clientResult s) ?_
    change Succinct.deletePrepProg U V w N h_space
      (((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
        u.val >>> bucketBits N), h_q >>> bucketBits N) = _
    rw [hb_eq, hq_eq, hm_eq]
  let m_last := Succinct.mOfSeed U N θ prep.2
  have hs'_eq : s' = (Memory.spec 0).clientState s
      (Succinct.deleteFinishProg U V w N h_space
        (((((0, b), prep.1.1), prep.1.2), m_micro), m_last)) := by
    refine congrArg ((Memory.spec 0).clientState s) ?_
    change Succinct.deleteFinishProg U V w N h_space
      (((((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
        prep.1.1), prep.1.2), h_q >>> bucketBits N), h_q_last >>> bucketBits N) = _
    rw [hb_eq, hm_eq]; rfl
  have hprep := Succinct.deletePrepProg_bucket_spec hb_inv henv hb_lt rfl hm_lt (q_target := q)
  dsimp only at hprep; rw [← hprep_res] at hprep
  have hm_last_lt : m_last < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ prep.2
  have hprep_branch := hprep.2.2.2
  let gm₀ := Succinct.gmAt 0 U V w N h_space s.mem
  by_cases hex : ∃ j < Succinct.bCount N gm₀ b,
      Succinct.quotAt 0 U w N h_space s.mem (Succinct.slotOf N gm₀ b j) = q
  · rw [ite_eq_left hex] at hprep_branch
    rcases hprep_branch with ⟨hf1, hj_del_lt, hq_del, hphys_del_eq, hq_last_eq⟩
    have hsome : (s_abs u).isSome := by
      rw [← Succinct.bucketMapOfState_feistelBucket hwf.2.1 h1 s_abs u]
      exact (hb_inv.hmap_dom b hb_lt q).mpr hex
    have hm₀_tot : m₀ + 1 ≤ Succinct.totalSlots N gm₀ := by
      have hpos_dom : 0 < (Dynamic.dom s_abs).card :=
        Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
      have hdel_eq := Dynamic.card_dom_delete_eq_of_isSome hsome
      dsimp only [gm₀, h_space]
      rw [hinv.htot]; omega
    let j_del := prep.1.1.2
    let phys_del := prep.1.2
    let j_last := Succinct.bCount N gm₀ b - 1
    have hj_del_lt' : j_del < Succinct.bCount N gm₀ b := hj_del_lt
    have hj_last_lt : j_last < Succinct.bCount N gm₀ b := by
      dsimp only [j_last, j_del, gm₀, h_space] at hj_del_lt ⊢; omega
    have hbc_pos : 1 ≤ Succinct.bCount N gm₀ b := by
      dsimp only [j_del, gm₀, h_space] at hj_del_lt ⊢; omega
    have hphys_del_lt : phys_del < N := by
      dsimp only [phys_del]; rw [hphys_del_eq]
      exact (Succinct.slotOf_lt_and_injective hb_inv.hslot).1 b hb_lt j_del hj_del_lt'
    have hj_del_n : j_del < N := lt_of_lt_of_le hj_del_lt (Succinct.bCount_le_n_max hb_inv.hslot b)
    have hj_last_n : j_last < N :=
      lt_of_lt_of_le hj_last_lt (Succinct.bCount_le_n_max hb_inv.hslot b)
    have hmem_del : j_del < effBucketCap N → j_del ∈ L b m_micro := fun hj_cap =>
      (hb_inv.hchain_mem b hb_lt m_micro hm_lt j_del).mpr ⟨hj_del_lt, hj_cap, by rw [hq_del]⟩
    have hmem_last : j_last < effBucketCap N → j_last ∈ L b m_last := fun hj_cap =>
      (hb_inv.hchain_mem b hb_lt m_last hm_last_lt j_last).mpr
        ⟨hj_last_lt, hj_cap, by dsimp only [m_last]; rw [hq_last_eq]⟩
    let s₁ := (Memory.spec 0).clientState s
      (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m_micro), j_del))
    obtain ⟨_, _, hq_u1, hv_u1, hgm_u1, L₁, hval₁, hmem₁⟩ :=
      Succinct.unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := N)
        (h_space := h_space) (base := 0) (b := b) (m := m_micro) (j_del := j_del)
        hw hb_lt hm_lt hj_del_n hb_inv.hchains hmem_del
    by_cases hlt : j_del < j_last
    · have hmem_last₁ : j_last < effBucketCap N → j_last ∈ L₁ b m_last := fun hj_cap => by
        rw [hmem₁ b hb_lt m_last hm_last_lt j_last]
        exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
      let s₂ := (Memory.spec 0).clientState s₁
        (Succinct.unlinkIfIndexedProg U V w N h_space (((0, b), m_last), j_last))
      obtain ⟨_, _, hq_u2, hv_u2, hgm_u2, L₂, hval₂, hmem₂⟩ :=
        Succinct.unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
          (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
          (j_del := j_last) (s := s₁) hw hb_lt hm_last_lt hj_last_n hval₁ hmem_last₁
      have hslot₂ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₂.mem) := by
        rw [hgm_u2, hgm_u1]; exact hb_inv.hslot
      have hbc₂ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₂.mem) b := by
        rw [hgm_u2, hgm_u1]; exact hbc_pos
      let s₃ := (Memory.spec 0).clientState s₂
        (Succinct.copyLastPayloadProg U V w N h_space ((0, b), phys_del))
      obtain ⟨_, _, hq_c, hv_c, hlm_c, hgm_c⟩ :=
        Succinct.copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := N)
          (h_space := h_space) (base := 0) (b := b) (phys_del := phys_del) (s := s₂)
          hw hslot₂ hb_lt hbc₂ hphys_del_lt
      have hval₃ : AllChainsValid N (Succinct.lmAt 0 U V w N h_space s₃.mem) L₂ :=
        hval₂.of_lm_eq hlm_c
      have hj_not₂ : ∀ m' < numMicroPerBucket N, j_del ∉ L₂ b m' := by
        intro m' hm' hj_in
        have hj_in₁ := ((hmem₂ b hb_lt m' hm' j_del).mp hj_in).1
        exact ((hmem₁ b hb_lt m' hm' j_del).mp hj_in₁).2 ⟨rfl, rfl⟩
      let s₄ := (Memory.spec 0).clientState s₃
        (Succinct.prependIfIndexedProg U V w N h_space (((0, b), m_last), j_del))
      obtain ⟨_, _, hq_pr, hv_pr, hgm_pr, _⟩ :=
        Succinct.prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w)
          (n_max := N) (h_space := h_space) (base := 0) (b := b) (m := m_last)
          (j_new := j_del) (s := s₃) hw hb_lt hm_last_lt hj_del_n hval₃ hj_not₂
      have hgm₄_eq : Succinct.gmAt 0 U V w N h_space s₄.mem = gm₀ := by
        rw [hgm_pr, hgm_c, hgm_u2, hgm_u1]
      have hslot₄ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₄.mem) := by
        rw [hgm₄_eq]; exact hb_inv.hslot
      have hbc₄ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₄.mem) b := by
        rw [hgm₄_eq]; exact hbc_pos
      have hm₀_tot₄ : m₀ + 1 ≤ Succinct.totalSlots N (Succinct.gmAt 0 U V w N h_space s₄.mem) := by
        rw [hgm₄_eq]; exact hm₀_tot
      have htd₄ : TailDenseInv N (Succinct.gmAt 0 U V w N h_space s₄.mem 0)
          (Succinct.gmAt 0 U V w N h_space s₄.mem 1) td dt := by rw [hgm₄_eq]; exact htd
      have hs'_pop : s' = (Memory.spec 0).clientState s₄
          (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
        rw [hs'_eq]
        unfold Succinct.deleteFinishProg Succinct.deleteFoundProg Succinct.deleteSwapProg
        simp only [pure_bind]
        rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readBucketCountProg,
          Succinct.clientResult_readBucketCountProg (0, b) s₁ hb_lt, hgm_u1,
          ite_eq_left hlt]
        repeat rw [StateTransitionSpec.clientState_bind]
      obtain ⟨td', dt', W, hpost, hpost_qv⟩ :=
        popBackSlotProg_window hnodup_p hnodup_m hw s₄ td dt
          hslot₄ hb_lt hbc₄ hm₀_tot₄ htd₄ htd_b hdt_b
      have hqv₄ : diffCount2 L_p (Succinct.quotAt 0 U w N h_space s₄.mem)
          (Succinct.valAt 0 U V w N h_space s₄.mem)
          (Succinct.quotAt 0 U w N h_space s.mem)
          (Succinct.valAt 0 U V w N h_space s.mem) ≤ 1 := by
        rw [hq_pr, hq_c, hgm_u2, hgm_u1, hq_u2, hq_u1,
          hv_pr, hv_c, hgm_u2, hgm_u1, hv_u2, hv_u1]
        refine (diffCount2_update_both_le hnodup_p
          (Succinct.quotAt 0 U w N h_space s.mem) (Succinct.valAt 0 U V w N h_space s.mem)
          (Succinct.quotAt 0 U w N h_space s.mem) (Succinct.valAt 0 U V w N h_space s.mem)
          _ _ _).trans ?_
        rw [diffCount2_self, Nat.zero_add]
      refine ⟨td', dt', W,
        by dsimp only; rw [hs'_pop]; exact hpost.tailDense,
        hpost.td_lt, hpost.dt_lt,
        by dsimp only [gm₀] at hgm₄_eq; dsimp only [h_space] at hs'_pop hgm₄_eq ⊢
           rw [hs'_pop, ← hgm₄_eq]; exact hpost.pot_le,
        by dsimp only [h_space] at hs'_pop hqv₄ ⊢; rw [hs'_pop]
           have := hpost_qv (Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s.mem)
             (Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s.mem); omega,
        by dsimp only [gm₀] at hgm₄_eq; dsimp only [h_space] at hs'_pop hgm₄_eq ⊢
           rw [hs'_pop, ← hgm₄_eq]; exact hpost.diff_phys,
        hpost.diff_td, hpost.diff_dt⟩
    · have hslot₁ : Succinct.SlotStoreInv N (Succinct.gmAt 0 U V w N h_space s₁.mem) := by
        rw [hgm_u1]; exact hb_inv.hslot
      have hbc₁ : 1 ≤ Succinct.bCount N (Succinct.gmAt 0 U V w N h_space s₁.mem) b := by
        rw [hgm_u1]; exact hbc_pos
      have hm₀_tot₁ : m₀ + 1 ≤ Succinct.totalSlots N (Succinct.gmAt 0 U V w N h_space s₁.mem) := by
        rw [hgm_u1]; exact hm₀_tot
      have htd₁ : TailDenseInv N (Succinct.gmAt 0 U V w N h_space s₁.mem 0)
          (Succinct.gmAt 0 U V w N h_space s₁.mem 1) td dt := by rw [hgm_u1]; exact htd
      have hs'_pop : s' = (Memory.spec 0).clientState s₁
          (Succinct.popBackSlotProg U V w N h_space (0, b)) := by
        rw [hs'_eq]
        unfold Succinct.deleteFinishProg Succinct.deleteFoundProg
        simp only [pure_bind]
        rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, Succinct.clientState_readBucketCountProg,
          Succinct.clientResult_readBucketCountProg (0, b) s₁ hb_lt, hgm_u1,
          ite_eq_right hlt]
      obtain ⟨td', dt', W, hpost, _⟩ :=
        popBackSlotProg_window hnodup_p hnodup_m hw s₁ td dt
          hslot₁ hb_lt hbc₁ hm₀_tot₁ htd₁ htd_b hdt_b
      refine ⟨td', dt', W,
        by dsimp only; rw [hs'_pop]; exact hpost.tailDense,
        hpost.td_lt, hpost.dt_lt,
        by dsimp only [h_space] at hs'_pop hgm_u1 ⊢; rw [hs'_pop, ← hgm_u1]; exact hpost.pot_le,
        by dsimp only [h_space] at hs'_pop hq_u1 hv_u1 ⊢
           rw [hs'_pop, ← hq_u1, ← hv_u1]; exact hpost.diff_qv,
        by dsimp only [h_space] at hs'_pop hgm_u1 ⊢; rw [hs'_pop, ← hgm_u1]; exact hpost.diff_phys,
        hpost.diff_td, hpost.diff_dt⟩
  · rw [ite_eq_right hex] at hprep_branch
    rcases hprep_branch with ⟨hf0, _⟩
    have hne1 : prep.1.1.1 ≠ 1 := by omega
    have hs'_id : s' = s := by
      rw [hs'_eq]
      unfold Succinct.deleteFinishProg
      simp only [pure_bind]
      rw [ite_eq_right hne1]; rfl
    refine ⟨td, dt, 0,
      by dsimp only; rw [hs'_id]; exact htd,
      htd_b, hdt_b,
      by dsimp only; rw [hs'_id]; omega,
      by dsimp only; rw [hs'_id, diffCount2_self]; omega,
      by dsimp only; rw [hs'_id, diffCount_self]; omega,
      by dsimp only; rw [diffCount_self]; omega,
      by dsimp only; rw [diffCount_self]; omega⟩

end Cslib.DataStructure.Dictionary.BitResizable
