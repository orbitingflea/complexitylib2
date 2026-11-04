/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Companion
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
# In-Epoch Companion Transitions and Amortized Synchronization Bounds

This module proves that every in-epoch `insert` and `delete` operation on the single-tape
bit-resizable dictionary executes in `O(1)` expected amortized `BitRAM` instructions under demonic
`.grow` (`BitRAM.DemonicExecWithin w`), and constructs the canonical companion state used on epoch
rebuilds.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.inEpochSyncCode`: unified `BitRAM.Code .standard 12`
  synchronization program for in-epoch transitions (`m' = m + 1`, `m = m' + 1`, or `m' = m`).
* `Cslib.DataStructure.Dictionary.BitResizable.WindowInv`: circular tail-to-dense bijection on an
  arbitrary dense interval `[b, b + n)`.
* `Cslib.DataStructure.Dictionary.BitResizable.Companion`: companion witness `(s_fix, td, dt)` for
  `buildBitState`.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.inEpochSyncCode_exec`: demonic execution certificate
  for `inEpochSyncCode`.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpoch_insert_step`,
  `Cslib.DataStructure.Dictionary.BitResizable.inEpoch_delete_step`: in-epoch companion transitions
  with `T + 1008 * slotPotential N gm' ≤ 1008 * slotPotential N gm + 2349 + 24 * probeExcess`.
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
open Cslib.DataStructure.HashFamily.WordRAM
open Finset

/-! ## Section 1: In-epoch same-size synchronization and unified `inEpochSyncCode` -/

/-- Concrete `BitRAM.Code .standard 12` program synchronizing an in-epoch operation that leaves the
key count `m` unchanged (`m' = m`, i.e., overwriting an existing key or deleting a missing key). -/
@[expose]
def inEpochSameSyncCode (U V w N m : ℕ) (s_cur s_tar : BitMemory.State) :
    BitRAM.Code .standard 12 :=
  .seq (syncDenseItemsListCode U V w N s_tar (changedDenseList U V w N m s_cur s_tar))
    (syncMetaWordsListCode s_tar (changedMetaList U w N s_cur s_tar))

/-- Execution certificate for `inEpochSameSyncCode`: executes in
`2 + 90 * (changedDenseList ...).length + 3 * (changedMetaList ...).length` instructions,
producing `y.toBitMemoryState = s_tar`. -/
theorem inEpochSameSyncCode_exec {U V w N m : ℕ} {x : BitRAM.Data 12}
    (s_tar : BitMemory.State)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N m)
    (htar_sz : s_tar.bitSize = dictBitSize U V w N m) :
    BitRAM.DemonicExecWithin w
      (inEpochSameSyncCode U V w N m x.toBitMemoryState s_tar) x
      (fun y => y.toBitMemoryState = s_tar ∧ y.WellFormed w)
      (2 + 90 * (changedDenseList U V w N m x.toBitMemoryState s_tar).length +
        3 * (changedMetaList U w N x.toBitMemoryState s_tar).length) := by
  set ds := changedDenseList U V w N m x.toBitMemoryState s_tar
  set as := changedMetaList U w N x.toBitMemoryState s_tar
  have hds_lt : ∀ d ∈ ds, d < m :=
    fun d hd => List.mem_range.mp (List.mem_of_mem_filter hd)
  have has_lt : ∀ a ∈ as, a < epochMetaWords U w N :=
    fun a ha => List.mem_range.mp (List.mem_of_mem_filter ha)
  refine .seq (T₁ := 1 + 90 * ds.length) (T₂ := 1 + 3 * as.length)
    (syncDenseItemsListCode_exec s_tar ds hw hU hV hx hds_lt hx_sz.symm.le)
    (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_in, hy₁_out, hy₁_meta⟩ => ?_) (by omega)
  have hmeta_le₁ : epochMetaBits U w N ≤ y₁.bitSize := by
    rw [hy₁_sz, hx_sz]; unfold dictBitSize; omega
  refine (syncMetaWordsListCode_exec (U := U) (V := V) s_tar as hw
    hy₁_wf htar has_lt hmeta_le₁).mono
    (fun y ⟨hy_wf, hy_sz, hy_in, hy_out, hy_items⟩ => ?_) le_rfl
  have hy_sz_eq : y.bitSize = dictBitSize U V w N m := hy_sz.trans (hy₁_sz.trans hx_sz)
  refine ⟨?_, hy_wf⟩
  apply bitMemoryState_eq_of_meta_and_items hw hU hV hy_wf.mem_wf htar hy_sz_eq htar_sz
  · intro a ha
    by_cases hin : a ∈ as
    · exact hy_in a hin
    · have h1 := hy_out a hin
      have h2 := hy₁_meta a ha
      have heq : x.mem a = s_tar.mem a := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr ha, decide_eq_true hne⟩)
      exact h1.trans (h2.trans heq)
  · intro d hd
    have h2 := hy_items d
    rw [h2.1, h2.2]
    by_cases hin : d ∈ ds
    · exact hy₁_in d hin
    · have h3 := hy₁_out d hd hin
      have heq_q : denseQuotAt U V w N x.toBitMemoryState d = denseQuotAt U V w N s_tar d := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd, decide_eq_true (Or.inl hne)⟩)
      have heq_v : denseValAt U V w N x.toBitMemoryState d = denseValAt U V w N s_tar d := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd, decide_eq_true (Or.inr hne)⟩)
      exact ⟨h3.1.trans heq_q, h3.2.trans heq_v⟩

/-- Unified `BitRAM.Code .standard 12` synchronization program for any in-epoch transition from key
count `m` to `m'` (`m' = m + 1`, `m = m' + 1`, or `m' = m`). -/
@[expose]
def inEpochSyncCode (U V w N m m' : ℕ) (s_cur s_tar : BitMemory.State) :
    BitRAM.Code .standard 12 :=
  if m' = m + 1 then inEpochInsertSyncCode U V w N m s_cur s_tar
  else if m = m' + 1 then inEpochDeleteSyncCode U V w N m' s_cur s_tar
  else inEpochSameSyncCode U V w N m s_cur s_tar

/-- Unified execution certificate for `inEpochSyncCode`: executes in at most
`96 + 90 * (changedDenseList U V w N (min m m') ...).length + 3 * (changedMetaList ...).length`
instructions under demonic `.grow`, producing `y.toBitMemoryState = s_tar`. -/
theorem inEpochSyncCode_exec {U V w N m m' : ℕ} {x : BitRAM.Data 12}
    (s_tar : BitMemory.State)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N m)
    (htar_sz : s_tar.bitSize = dictBitSize U V w N m')
    (hm : m' = m + 1 ∨ m = m' + 1 ∨ m' = m) :
    BitRAM.DemonicExecWithin w
      (inEpochSyncCode U V w N m m' x.toBitMemoryState s_tar) x
      (fun y => y.toBitMemoryState = s_tar ∧ y.WellFormed w)
      (96 + 90 * (changedDenseList U V w N (min m m') x.toBitMemoryState s_tar).length +
        3 * (changedMetaList U w N x.toBitMemoryState s_tar).length) := by
  unfold inEpochSyncCode
  by_cases h1 : m' = m + 1
  · subst h1
    rw [ite_eq_left rfl, Nat.min_eq_left (Nat.le_succ m)]
    exact inEpochInsertSyncCode_exec s_tar hw hU hV hx htar hx_sz htar_sz
  · rw [ite_eq_right h1]
    by_cases h2 : m = m' + 1
    · subst h2
      rw [ite_eq_left rfl, Nat.min_eq_right (Nat.le_succ m')]
      exact (inEpochDeleteSyncCode_exec s_tar hw hU hV hx htar hx_sz htar_sz).mono
        (fun _ h => h) (by omega)
    · have h3 : m' = m := by omega
      subst h3
      rw [ite_eq_right h2, Nat.min_self]
      exact (inEpochSameSyncCode_exec s_tar hw hU hV hx htar hx_sz htar_sz).mono
        (fun _ h => h) (by omega)

/-! ## Section 2: `WindowInv`, circular window updates, and `physByBase` difference bounds -/

/-- Circular tail-to-dense bijection invariant on an arbitrary dense interval `[b, b + n)` with
modulus `M`. `TailDenseInv N n_slabs n_tails td dt` is `WindowInv (maxTailItems N)
(n_slabs * slabSize N) n_tails td dt`. -/
structure WindowInv (M b n : ℕ) (td dt : ℕ → ℕ) : Prop where
  td_lt : ∀ t < n, td t < M
  dense_lt : ∀ t < n, denseOfCirc M b (td t) < b + n
  dt_td : ∀ t < n, dt (td t) = t
  owner_valid : ∀ d, b ≤ d → d < b + n → dt (d % M) < n ∧ td (dt (d % M)) = d % M

theorem windowInv_iff_tailDenseInv (N n_slabs n_tails : ℕ) (td dt : ℕ → ℕ) :
    WindowInv (maxTailItems N) (n_slabs * slabSize N) n_tails td dt ↔
      TailDenseInv N n_slabs n_tails td dt :=
  ⟨fun h => ⟨h.td_lt, h.dense_lt, h.dt_td, h.owner_valid⟩,
   fun h => ⟨h.td_lt, h.dense_lt, h.dt_td, h.owner_valid⟩⟩

theorem denseOfCirc_ge (M b c : ℕ) : b ≤ denseOfCirc M b c := by
  unfold denseOfCirc; split_ifs <;> omega

theorem denseOfCirc_eq_self_iff {M b c d : ℕ} (hM : 0 < M) (hc : c < M)
    (hlo : b ≤ d) (hhi : d < b + M) :
    denseOfCirc M b c = d ↔ c = d % M := by
  constructor
  · intro heq
    rw [← heq, denseOfCirc_mod hM hc]
  · rintro rfl
    exact denseOfCirc_mod_self hM hlo hhi

theorem denseOfCirc_succ_of_ne_mod {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M b c < b + M) (hne : c ≠ b % M) :
    denseOfCirc M (b + 1) c = denseOfCirc M b c := by
  set d := denseOfCirc M b c
  have hlo : b ≤ d := denseOfCirc_ge M b c
  have hne_d : d ≠ b := fun hd => hne ((denseOfCirc_eq_self_iff hM hc le_rfl (by omega)).mp hd)
  have hmod : d % M = c := denseOfCirc_mod hM hc
  rw [← hmod]
  exact denseOfCirc_mod_self hM (by omega) (by omega)

theorem denseOfCirc_pred_of_lt {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M (b + 1) c < b + M) :
    denseOfCirc M b c = denseOfCirc M (b + 1) c ∧ c ≠ b % M := by
  set d := denseOfCirc M (b + 1) c
  have hlo : b + 1 ≤ d := denseOfCirc_ge M (b + 1) c
  have hmod : d % M = c := denseOfCirc_mod hM hc
  have heq : denseOfCirc M b c = d := by
    rw [← hmod]
    exact denseOfCirc_mod_self hM (by omega) hhi
  refine ⟨heq, fun hmod_b => ?_⟩
  have hdb : denseOfCirc M b c = b := by
    rw [hmod_b]
    exact denseOfCirc_mod_self hM le_rfl (by omega)
  omega

/-- Canonical `td` mapping `(b + t) % M` for initial / rebuilt companions. -/
def canonTD (M b : ℕ) (t : ℕ) : ℕ :=
  if M = 0 then 0 else (b + t) % M

/-- Canonical `dt` mapping `(c + M - b % M) % M` for initial / rebuilt companions. -/
def canonDT (M b : ℕ) (c : ℕ) : ℕ :=
  if M = 0 then 0 else (c + M - b % M) % M

theorem windowInv_canon {M b n : ℕ} (hn : n ≤ M) :
    WindowInv M b n (canonTD M b) (canonDT M b) ∧
    (∀ i, canonTD M b i < max M 1) ∧
    (∀ i, canonDT M b i < max M 1) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, fun _ => ?_, fun _ => ?_⟩ <;>
    · simp [canonTD, canonDT]
  · have hM0 : M ≠ 0 := Nat.ne_of_gt hM
    have hmax : max M 1 = M := max_eq_left hM
    have htd_eq : ∀ t, canonTD M b t = (b + t) % M := fun t => by simp [canonTD, hM0]
    have hdt_eq : ∀ c, canonDT M b c = (c + M - b % M) % M := fun c => by simp [canonDT, hM0]
    have hcirc : ∀ c, denseOfCirc M b c = b + canonDT M b c := by
      intro c; unfold denseOfCirc; rw [ite_eq_right hM0, hdt_eq]
    refine ⟨⟨fun t _ => by rw [htd_eq]; exact Nat.mod_lt _ hM,
      fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
      fun i => by rw [hmax, htd_eq]; exact Nat.mod_lt _ hM,
      fun i => by rw [hmax, hdt_eq]; exact Nat.mod_lt _ hM⟩
    · rw [htd_eq, denseOfCirc_mod_self hM (by omega) (by omega)]
      omega
    · have h1 : denseOfCirc M b (canonTD M b t) = b + t := by
        rw [htd_eq]; exact denseOfCirc_mod_self hM (by omega) (by omega)
      rw [hcirc] at h1
      omega
    · have h1 : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM hlo (by omega)
      rw [hcirc] at h1
      have hdt_val : canonDT M b (d % M) = d - b := by omega
      rw [hdt_val]
      refine ⟨by omega, ?_⟩
      rw [htd_eq, Nat.add_sub_of_le hlo]

/-- Physical slot of dense item `d` parameterized explicitly by the tail base `b_tail`. -/
def physByBase (N b_tail : ℕ) (dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < b_tail then d
  else N - 1 - dt (d % maxTailItems N)

theorem physOfDense_eq_physByBase (N : ℕ) (gm dt : ℕ → ℕ) :
    physOfDense N gm dt = physByBase N (gm 0 * slabSize N) dt := by
  rfl

theorem diffCount_physByBase_update_dt {N b_tail m₀ : ℕ} (hm₀ : m₀ ≤ b_tail + maxTailItems N)
    (dt g : ℕ → ℕ) (c₀ v₀ : ℕ) :
    diffCount (List.range m₀) (physByBase N b_tail (Function.update dt c₀ v₀))
      (physByBase N b_tail g) ≤
      diffCount (List.range m₀) (physByBase N b_tail dt) (physByBase N b_tail g) + 1 := by
  have hstep : diffCount (List.range m₀)
      (physByBase N b_tail (Function.update dt c₀ v₀)) (physByBase N b_tail dt) ≤ 1 := by
    refine filter_sub_length_le (List.range m₀) _
      (fun d => decide (d = denseOfCirc (maxTailItems N) b_tail c₀)) (fun _ => false) ?_ |>.trans ?_
    · intro d hd hx
      have hd_lt : d < m₀ := List.mem_range.mp hd
      simp only [decide_eq_true_eq] at hx ⊢
      left
      unfold physByBase at hx
      split_ifs at hx with hb0 hlt
      · exact False.elim (hx rfl)
      · exact False.elim (hx rfl)
      · have hlo : b_tail ≤ d := Nat.le_of_not_lt hlt
        have hM : 0 < maxTailItems N := by omega
        have heq_c : d % maxTailItems N = c₀ := by
          by_contra hne
          rw [Function.update_of_ne hne] at hx
          exact hx rfl
        rw [← heq_c]
        exact (denseOfCirc_mod_self hM hlo (by omega)).symm
    · have h1 := filter_eq_length_le_one (L := List.range m₀) List.nodup_range
        (denseOfCirc (maxTailItems N) b_tail c₀)
      simp only [List.filter_false, List.length_nil, Nat.add_zero]
      exact h1
  calc diffCount (List.range m₀) (physByBase N b_tail (Function.update dt c₀ v₀))
        (physByBase N b_tail g)
      ≤ diffCount (List.range m₀) (physByBase N b_tail (Function.update dt c₀ v₀))
          (physByBase N b_tail dt) +
        diffCount (List.range m₀) (physByBase N b_tail dt) (physByBase N b_tail g) :=
        diffCount_triangle _ _ _ _
    _ ≤ 1 + diffCount (List.range m₀) (physByBase N b_tail dt) (physByBase N b_tail g) :=
        Nat.add_le_add_right hstep _
    _ = diffCount (List.range m₀) (physByBase N b_tail dt) (physByBase N b_tail g) + 1 :=
        Nat.add_comm _ _

theorem diffCount_physByBase_succ (N b_tail m₀ : ℕ) (dt : ℕ → ℕ) :
    diffCount (List.range m₀) (physByBase N (b_tail + 1) dt) (physByBase N b_tail dt) ≤ 1 := by
  refine diffCount_of_eq_off_one List.nodup_range b_tail fun d hne => ?_
  unfold physByBase
  split_ifs with hb0 h1 h2 h2
  · rfl
  · rfl
  · omega
  · omega
  · rfl

/-- Grow the circular window `[b, b + n)` on the right by 1 to `[b, b + (n + 1))`. -/
def winGrowRight (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c := (b + n) % M
  (Function.update p.1 n c, Function.update p.2 c n)

theorem winGrowRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winGrowRight M b n (td, dt)
    WindowInv M b (n + 1) p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_new := (b + n) % M
  have hc_lt : c_new < M := Nat.mod_lt (b + n) hM_pos
  have hcirc_new : denseOfCirc M b c_new = b + n :=
    denseOfCirc_mod_self hM_pos (by omega) (by omega)
  have htd_ne : ∀ t < n, td t ≠ c_new := by
    intro t ht heq
    have := hw.dense_lt t ht
    rw [heq, hcirc_new] at this
    omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (htd_ne t ht')]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show d < b + n + 1 by omega) with hd_lt | rfl
    · have hown := hw.owner_valid d hlo hd_lt
      have hne_c : d % M ≠ c_new := by
        rw [← hown.2]
        exact htd_ne _ hown.1
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
    · rw [Function.update_self, Function.update_self]
      exact ⟨Nat.lt_succ_self n, rfl⟩
  · dsimp only [p', winGrowRight]
    by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · dsimp only [p', winGrowRight]
    by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Grow the circular window `[b + 1, b + 1 + n)` on the left by 1 to `[b, b + (n + 1))`. -/
def winGrowLeft (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c := b % M
  (Function.update p.1 n c, Function.update p.2 c n)

theorem winGrowLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M (b + 1) n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winGrowLeft M b n (td, dt)
    WindowInv M b (n + 1) p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_new := b % M
  have hc_lt : c_new < M := Nat.mod_lt b hM_pos
  have hcirc_new : denseOfCirc M b c_new = b :=
    denseOfCirc_mod_self hM_pos le_rfl (by omega)
  have hpred : ∀ t < n, denseOfCirc M b (td t) = denseOfCirc M (b + 1) (td t) ∧ td t ≠ c_new := by
    intro t ht
    have hlt := hw.dense_lt t ht
    exact denseOfCirc_pred_of_lt hM_pos (hw.td_lt t ht) (by omega)
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), (hpred t ht').1]
      have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (hpred t ht').2]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · dsimp only [p', winGrowLeft]
    rcases eq_or_lt_of_le hlo with rfl | hd_gt
    · rw [Function.update_self, Function.update_self]
      exact ⟨Nat.lt_succ_self n, rfl⟩
    · have hown := hw.owner_valid d hd_gt (by omega)
      have hne_c : d % M ≠ c_new := by
        rw [← hown.2]
        exact (hpred _ hown.1).2
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
  · dsimp only [p', winGrowLeft]
    by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · dsimp only [p', winGrowLeft]
    by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Shrink the circular window `[b, b + (n + 1))` on the right by 1 to `[b, b + n)`. -/
def winShrinkRight (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c_rem := (b + n) % M
  let t_rem := p.2 c_rem
  let c_last := p.1 n
  (Function.update p.1 t_rem c_last, Function.update p.2 c_last t_rem)

theorem winShrinkRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winShrinkRight M b n (td, dt)
    WindowInv M b n p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_rem := (b + n) % M
  set t_rem := dt c_rem
  set c_last := td n
  have hown_rem := hw.owner_valid (b + n) (by omega) (by omega)
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  have hdt_clast : dt c_last = n := hw.dt_td n (Nat.lt_succ_self n)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hlt_bn : ∀ t < n + 1, t ≠ t_rem → denseOfCirc M b (td t) < b + n := by
    intro t ht hne
    have hlt := hw.dense_lt t ht
    have hne_d : denseOfCirc M b (td t) ≠ b + n := by
      intro hd
      have hmod : td t = c_rem := (denseOfCirc_eq_self_iff hM_pos (hw.td_lt t ht)
        (by omega) (by omega)).mp hd
      exact hne (htd_inj t ht t_rem ht_rem_lt (hmod.trans htd_trem.symm))
    omega
  have hp'1 : p'.1 = Function.update td t_rem c_last := rfl
  have hp'2 : p'.2 = Function.update dt c_last t_rem := rfl
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne heq]; exact hw.td_lt t (by omega)
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]
      exact hlt_bn n (Nat.lt_succ_self n) (by omega)
    · rw [Function.update_of_ne heq]
      exact hlt_bn t (by omega) heq
  · rw [hp'1, hp'2]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq]
      have hne_c : td t ≠ c_last := fun hc =>
         Nat.ne_of_lt ht (htd_inj t (by omega) n (Nat.lt_succ_self n) hc)
      rw [Function.update_of_ne hne_c]
      exact hw.dt_td t (by omega)
  · rw [hp'1, hp'2]
    have hown := hw.owner_valid d hlo (by omega)
    have hne_crem : d % M ≠ c_rem := by
      intro heq
      have hd_eq : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM_pos hlo (by omega)
      have hrem_eq : denseOfCirc M b c_rem = b + n :=
        denseOfCirc_mod_self hM_pos (by omega) (by omega)
      rw [heq, hrem_eq] at hd_eq
      omega
    have hne_trem : dt (d % M) ≠ t_rem := by
      intro heq
      apply hne_crem
      rw [← hown.2, heq, htd_trem]
    by_cases hclast : d % M = c_last
    · rw [hclast, Function.update_self, Function.update_self]
      have hne_n : t_rem ≠ n := by
        intro heq
        apply hne_crem
        rw [hclast, ← htd_trem, heq]
      exact ⟨by omega, rfl⟩
    · rw [Function.update_of_ne hclast, Function.update_of_ne hne_trem]
      have hne_n : dt (d % M) ≠ n := by
        intro heq
        apply hclast
        rw [← hown.2, heq]
      exact ⟨by omega, hown.2⟩
  · rw [hp'1]
    by_cases hi : i = t_rem
    · subst hi; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · rw [hp'2]
    by_cases hi : i = c_last
    · subst hi; rw [Function.update_self]; exact hdt_b c_rem
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Shrink the circular window `[b, b + (n + 1))` on the left by 1 to `[b + 1, b + 1 + n)`. -/
def winShrinkLeft (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c_rem := b % M
  let t_rem := p.2 c_rem
  let c_last := p.1 n
  (Function.update p.1 t_rem c_last, Function.update p.2 c_last t_rem)

theorem winShrinkLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winShrinkLeft M b n (td, dt)
    WindowInv M (b + 1) n p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_rem := b % M
  set t_rem := dt c_rem
  set c_last := td n
  have hown_rem := hw.owner_valid b le_rfl (by omega)
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  have hdt_clast : dt c_last = n := hw.dt_td n (Nat.lt_succ_self n)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hsucc : ∀ t < n + 1, t ≠ t_rem →
      denseOfCirc M (b + 1) (td t) < b + 1 + n := by
    intro t ht hne
    have hlt := hw.dense_lt t ht
    have hne_c : td t ≠ c_rem := fun hc =>
      hne (htd_inj t ht t_rem ht_rem_lt (hc.trans htd_trem.symm))
    rw [denseOfCirc_succ_of_ne_mod hM_pos (hw.td_lt t ht) (by omega) hne_c]
    omega
  have hp'1 : p'.1 = Function.update td t_rem c_last := rfl
  have hp'2 : p'.2 = Function.update dt c_last t_rem := rfl
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne heq]; exact hw.td_lt t (by omega)
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]
      exact hsucc n (Nat.lt_succ_self n) (by omega)
    · rw [Function.update_of_ne heq]
      exact hsucc t (by omega) heq
  · rw [hp'1, hp'2]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq]
      have hne_c : td t ≠ c_last := fun hc =>
        Nat.ne_of_lt ht (htd_inj t (by omega) n (Nat.lt_succ_self n) hc)
      rw [Function.update_of_ne hne_c]
      exact hw.dt_td t (by omega)
  · rw [hp'1, hp'2]
    have hown := hw.owner_valid d (by omega) (by omega)
    have hne_crem : d % M ≠ c_rem := by
      intro heq
      have hd_eq : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM_pos (by omega) (by omega)
      have hrem_eq : denseOfCirc M b c_rem = b :=
        denseOfCirc_mod_self hM_pos le_rfl (by omega)
      rw [heq, hrem_eq] at hd_eq
      omega
    have hne_trem : dt (d % M) ≠ t_rem := by
      intro heq
      apply hne_crem
      rw [← hown.2, heq, htd_trem]
    by_cases hclast : d % M = c_last
    · rw [hclast, Function.update_self, Function.update_self]
      have hne_n : t_rem ≠ n := by
        intro heq
        apply hne_crem
        rw [hclast, ← htd_trem, heq]
      exact ⟨by omega, rfl⟩
    · rw [Function.update_of_ne hclast, Function.update_of_ne hne_trem]
      have hne_n : dt (d % M) ≠ n := by
        intro heq
        apply hclast
        rw [← hown.2, heq]
      exact ⟨by omega, hown.2⟩
  · rw [hp'1]
    by_cases hi : i = t_rem
    · subst hi; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · rw [hp'2]
    by_cases hi : i = c_last
    · subst hi; rw [Function.update_self]; exact hdt_b c_rem
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Iterate `winShrinkLeft` `k` times from `[b, b + (n + k))` to `[b + k, b + k + n)`. -/
def iterShrinkLeft (M b n : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | k + 1, p =>
      let p₁ := iterShrinkLeft M b (n + 1) k p
      winShrinkLeft M (b + k) n p₁

theorem iterShrinkLeft_spec {N U w m₀ : ℕ} {L_m : List ℕ} (hnodup_m : L_m.Nodup)
    (b n : ℕ) (td₀ dt₀ : ℕ → ℕ) :
    let M := maxTailItems N
    let zMem : ℕ → ℕ := fun _ => 0
    ∀ k (p : (ℕ → ℕ) × (ℕ → ℕ)),
      n + k ≤ M →
      m₀ ≤ b + M →
      WindowInv M b (n + k) p.1 p.2 →
      (∀ i, p.1 i < M) → (∀ i, p.2 i < M) →
      let p' := iterShrinkLeft M b n k p
      WindowInv M (b + k) n p'.1 p'.2 ∧
      (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) ∧
      diffCount (List.range m₀) (physByBase N (b + k) p'.2) (physByBase N b dt₀) ≤
        diffCount (List.range m₀) (physByBase N b p.2) (physByBase N b dt₀) + 2 * k ∧
      diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p'.1 M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) ≤
        diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p.1 M zMem)
          (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) + 2 * k ∧
      diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p'.2 M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) ≤
        diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p.2 M zMem)
          (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) + 2 * k := by
  intro M zMem k
  induction k generalizing n with
  | zero =>
    intro p _ _ hw h1 h2
    simp only [iterShrinkLeft, Nat.add_zero, Nat.mul_zero]
    exact ⟨hw, h1, h2, le_rfl, le_rfl, le_rfl⟩
  | succ k ih =>
    intro p hnk hm₀ hw h1 h2
    have hnk' : (n + 1) + k ≤ M := by omega
    have hw' : WindowInv M b ((n + 1) + k) p.1 p.2 := by
      rwa [show (n + 1) + k = n + (k + 1) by omega]
    set p₁ := iterShrinkLeft M b (n + 1) k p
    obtain ⟨hw1, htd1, hdt1, hphys1, hpack_td1, hpack_dt1⟩ :=
      ih (n + 1) p hnk' hm₀ hw' h1 h2
    change WindowInv M (b + k) (n + 1) p₁.1 p₁.2 at hw1
    change ∀ i, p₁.1 i < M at htd1
    change ∀ i, p₁.2 i < M at hdt1
    change diffCount (List.range m₀) (physByBase N (b + k) p₁.2) (physByBase N b dt₀) ≤ _ at hphys1
    change diffCount L_m
      (packArray (offTD U w N) (globalPtrBits N) w p₁.1 M zMem) _ ≤ _ at hpack_td1
    change diffCount L_m
      (packArray (offDT U w N) (globalPtrBits N) w p₁.2 M zMem) _ ≤ _ at hpack_dt1
    obtain ⟨hw2, htd2, hdt2⟩ := winShrinkLeft_spec hw1 (by omega) htd1 hdt1
    rw [show b + k + 1 = b + (k + 1) by omega] at hw2
    refine ⟨hw2, htd2, hdt2, ?_, ?_, ?_⟩
    · set p' := winShrinkLeft M (b + k) n p₁
      have hstep1 : diffCount (List.range m₀)
          (physByBase N (b + k + 1) p'.2) (physByBase N (b + k) p'.2) ≤ 1 :=
        diffCount_physByBase_succ N (b + k) m₀ p'.2
      have hstep2' : diffCount (List.range m₀)
          (physByBase N (b + k) p'.2) (physByBase N b dt₀) ≤
          diffCount (List.range m₀) (physByBase N (b + k) p₁.2) (physByBase N b dt₀) + 1 := by
        have hu := diffCount_physByBase_update_dt (N := N) (b_tail := b + k) (m₀ := m₀)
          (by omega) p₁.2 p₁.2 (p₁.1 n) (p₁.2 ((b + k) % M))
        rw [diffCount_self] at hu
        have hp'2 : p'.2 = Function.update p₁.2 (p₁.1 n) (p₁.2 ((b + k) % M)) := rfl
        have htri := diffCount_triangle (List.range m₀)
          (physByBase N (b + k) p'.2) (physByBase N (b + k) p₁.2) (physByBase N b dt₀)
        rw [hp'2] at htri ⊢
        omega
      have htri := diffCount_triangle (List.range m₀)
        (physByBase N (b + k + 1) p'.2) (physByBase N (b + k) p'.2) (physByBase N b dt₀)
      rw [show b + (k + 1) = b + k + 1 by omega]
      change diffCount (List.range m₀) (physByBase N (b + k + 1) p'.2) (physByBase N b dt₀) ≤ _
      omega
    · have hup := diffCount_packArray_update_le hnodup_m (offTD U w N) (globalPtrBits N) w
        p₁.1 td₀ (p₁.2 ((b + k) % M)) (p₁.1 n) M zMem
      change diffCount L_m
        (packArray (offTD U w N) (globalPtrBits N) w
          (Function.update p₁.1 (p₁.2 ((b + k) % M)) (p₁.1 n)) M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) ≤ _
      omega
    · have hup := diffCount_packArray_update_le hnodup_m (offDT U w N) (globalPtrBits N) w
        p₁.2 dt₀ (p₁.1 n) (p₁.2 ((b + k) % M)) M zMem
      change diffCount L_m
        (packArray (offDT U w N) (globalPtrBits N) w
          (Function.update p₁.2 (p₁.1 n) (p₁.2 ((b + k) % M))) M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) ≤ _
      omega

/-- Iterate `winGrowLeft` `k` times from `[b + k, b + k + n)` to `[b, b + (n + k))`. -/
def iterGrowLeft (M b n : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | k + 1, p =>
      let p₁ := iterGrowLeft M (b + 1) n k p
      winGrowLeft M b (n + k) p₁

theorem iterGrowLeft_spec {N U w m₀ : ℕ} {L_m : List ℕ} (hnodup_m : L_m.Nodup) :
    let M := maxTailItems N
    let zMem : ℕ → ℕ := fun _ => 0
    ∀ k b n (td₀ dt₀ : ℕ → ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)),
      n + k ≤ M →
      m₀ ≤ b + M →
      WindowInv M (b + k) n p.1 p.2 →
      (∀ i, p.1 i < M) → (∀ i, p.2 i < M) →
      let p' := iterGrowLeft M b n k p
      WindowInv M b (n + k) p'.1 p'.2 ∧
      (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) ∧
      diffCount (List.range m₀) (physByBase N b p'.2) (physByBase N (b + k) dt₀) ≤
        diffCount (List.range m₀) (physByBase N (b + k) p.2) (physByBase N (b + k) dt₀) + 2 * k ∧
      diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p'.1 M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) ≤
        diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w p.1 M zMem)
          (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) + 2 * k ∧
      diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p'.2 M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) ≤
        diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w p.2 M zMem)
          (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) + 2 * k := by
  intro M zMem k
  induction k with
  | zero =>
    intro b n td₀ dt₀ p _ _ hw h1 h2
    simp only [iterGrowLeft, Nat.add_zero, Nat.mul_zero]
    exact ⟨hw, h1, h2, le_rfl, le_rfl, le_rfl⟩
  | succ k ih =>
    intro b n td₀ dt₀ p hnk hm₀ hw h1 h2
    have hw' : WindowInv M ((b + 1) + k) n p.1 p.2 := by
      rwa [show (b + 1) + k = b + (k + 1) by omega]
    set p₁ := iterGrowLeft M (b + 1) n k p
    obtain ⟨hw1, htd1, hdt1, hphys1, hpack_td1, hpack_dt1⟩ :=
      ih (b + 1) n td₀ dt₀ p (by omega) (by omega) hw' h1 h2
    change WindowInv M (b + 1) (n + k) p₁.1 p₁.2 at hw1
    change ∀ i, p₁.1 i < M at htd1
    change ∀ i, p₁.2 i < M at hdt1
    change diffCount (List.range m₀) (physByBase N (b + 1) p₁.2)
      (physByBase N ((b + 1) + k) dt₀) ≤ _ at hphys1
    change diffCount L_m
      (packArray (offTD U w N) (globalPtrBits N) w p₁.1 M zMem) _ ≤ _ at hpack_td1
    change diffCount L_m
      (packArray (offDT U w N) (globalPtrBits N) w p₁.2 M zMem) _ ≤ _ at hpack_dt1
    obtain ⟨hw2, htd2, hdt2⟩ := winGrowLeft_spec hw1 (by omega) htd1 hdt1
    rw [show n + k + 1 = n + (k + 1) by omega] at hw2
    rw [show (b + 1) + k = b + (k + 1) by omega] at hphys1
    refine ⟨hw2, htd2, hdt2, ?_, ?_, ?_⟩
    · set p' := winGrowLeft M b (n + k) p₁
      have hu := diffCount_physByBase_update_dt (N := N) (b_tail := b) (m₀ := m₀)
        hm₀ p₁.2 p₁.2 (b % M) (n + k)
      rw [diffCount_self] at hu
      have hstep2 : diffCount (List.range m₀)
          (physByBase N b p₁.2) (physByBase N (b + 1) p₁.2) ≤ 1 := by
        rw [diffCount_symm]
        exact diffCount_physByBase_succ N b m₀ p₁.2
      have hp'2 : p'.2 = Function.update p₁.2 (b % M) (n + k) := rfl
      have htri1 := diffCount_triangle (List.range m₀)
        (physByBase N b p'.2) (physByBase N b p₁.2) (physByBase N (b + (k + 1)) dt₀)
      have htri2 := diffCount_triangle (List.range m₀)
        (physByBase N b p₁.2) (physByBase N (b + 1) p₁.2) (physByBase N (b + (k + 1)) dt₀)
      change diffCount (List.range m₀) (physByBase N b p'.2) (physByBase N (b + (k + 1)) dt₀) ≤ _
      rw [hp'2] at htri1 ⊢
      omega
    · have hup := diffCount_packArray_update_le hnodup_m (offTD U w N) (globalPtrBits N) w
        p₁.1 td₀ (n + k) (b % M) M zMem
      change diffCount L_m
        (packArray (offTD U w N) (globalPtrBits N) w
          (Function.update p₁.1 (n + k) (b % M)) M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td₀ M zMem) ≤ _
      omega
    · have hup := diffCount_packArray_update_le hnodup_m (offDT U w N) (globalPtrBits N) w
        p₁.2 dt₀ (b % M) (n + k) M zMem
      change diffCount L_m
        (packArray (offDT U w N) (globalPtrBits N) w
          (Function.update p₁.2 (b % M) (n + k)) M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt₀ M zMem) ≤ _
      omega

/-! ## Section 3: `buildBitState` metadata and dense-item difference bounds -/

theorem diffCount2_comp (L : List ℕ) (f₁ f₂ g₁ g₂ h : ℕ → ℕ) :
    diffCount2 L (f₁ ∘ h) (f₂ ∘ h) (g₁ ∘ h) (g₂ ∘ h) = diffCount2 (L.map h) f₁ f₂ g₁ g₂ := by
  unfold diffCount2
  rw [List.filter_map, List.length_map]
  rfl

theorem diffCount2_comp_le_diffCount (L : List ℕ) (f₁ f₂ h₁ h₂ : ℕ → ℕ) :
    diffCount2 L (f₁ ∘ h₁) (f₂ ∘ h₁) (f₁ ∘ h₂) (f₂ ∘ h₂) ≤ diffCount L h₁ h₂ := by
  have h := filter_sub_length_le L
    (fun x => decide (f₁ (h₁ x) ≠ f₁ (h₂ x) ∨ f₂ (h₁ x) ≠ f₂ (h₂ x)))
    (fun x => decide (h₁ x ≠ h₂ x))
    (fun _ => false)
    (fun x _ hx => by
      simp only [decide_eq_true_eq] at hx ⊢
      left
      intro heq
      rcases hx with h1 | h2 <;> [exact h1 (congrArg f₁ heq); exact h2 (congrArg f₂ heq)])
  simpa [diffCount2, diffCount] using h

theorem denseOfPhys_physOfDense {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (htd : TailDenseInv N (gm 0) (gm 1) td dt)
    {d : ℕ} (hd : d < Succinct.totalSlots N gm) :
    physOfDense N gm dt d < N ∧
    denseOfPhys N gm td (physOfDense N gm dt d) = d := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have htot_eq : Succinct.totalSlots N gm = gm 0 := by
      unfold Succinct.totalSlots; rw [ite_eq_left hb0]
    have hlt_N : d < N := lt_of_lt_of_le (by rwa [← htot_eq]) (hslot.single_valid hb0)
    unfold physOfDense denseOfPhys
    simp only [hb0, ↓reduceIte, and_true]
    exact hlt_N
  · have hb_ne : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
    have htot_eq : Succinct.totalSlots N gm = gm 0 * slabSize N + gm 1 := by
      unfold Succinct.totalSlots; rw [ite_eq_right hb_ne]
    have htot_le := hslot.multi_total_le hb_pos
    have htail := hslot.multi_tail hb_pos
    rw [htot_eq] at hd
    by_cases hd_slab : d < gm 0 * slabSize N
    · unfold physOfDense denseOfPhys
      simp only [hb_ne, ↓reduceIte, hd_slab, and_true]
      omega
    · have hlo : gm 0 * slabSize N ≤ d := Nat.le_of_not_lt hd_slab
      have hM : 0 < maxTailItems N := by
        have := htail.ntails_le; omega
      have hown := htd.owner_valid d hlo hd
      have hdt_lt : dt (d % maxTailItems N) < gm 1 := hown.1
      have hphys_eq : physOfDense N gm dt d = N - 1 - dt (d % maxTailItems N) := by
        unfold physOfDense; simp only [hb_ne, ↓reduceIte, hd_slab]
      have hnot_lt : ¬(N - 1 - dt (d % maxTailItems N) < gm 0 * slabSize N) := by omega
      have hsub : N - 1 - (N - 1 - dt (d % maxTailItems N)) = dt (d % maxTailItems N) := by omega
      rw [hphys_eq]
      refine ⟨by omega, ?_⟩
      unfold denseOfPhys
      simp only [hb_ne, ↓reduceIte, hnot_lt, hsub]
      rw [hown.2]
      exact denseOfCirc_mod_self hM hlo (by have := htail.ntails_le; omega)

theorem nodup_map_physOfDense {N m₀ : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (htd : TailDenseInv N (gm 0) (gm 1) td dt)
    (hm₀ : m₀ ≤ Succinct.totalSlots N gm) :
    ((List.range m₀).map (physOfDense N gm dt)).Nodup := by
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro d₁ hd₁ d₂ hd₂ heq
  have hd₁_lt : d₁ < Succinct.totalSlots N gm := lt_of_lt_of_le (List.mem_range.mp hd₁) hm₀
  have hd₂_lt : d₂ < Succinct.totalSlots N gm := lt_of_lt_of_le (List.mem_range.mp hd₂) hm₀
  have h1 := (denseOfPhys_physOfDense hslot htd hd₁_lt).2
  have h2 := (denseOfPhys_physOfDense hslot htd hd₂_lt).2
  rw [← h1, ← h2, heq]

/-- Bound on `(changedDenseList U V w N m₀ s_cur s_tar).length` when `s_cur` and `s_tar` are
`buildBitState` states with `m₀ = min m m'`. -/
theorem changedDenseList_length_le {U V w N m m' : ℕ}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N)
    (s_fix s_fix' : Memory.State) (td dt td' dt' : ℕ → ℕ) :
    let m₀ := min m m'
    let h_space := Succinct.hashSpace U w N
    let gm := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let gm' := Succinct.gmAt 0 U V w N h_space s_fix'.mem
    let qA := Succinct.quotAt 0 U w N h_space s_fix.mem
    let vA := Succinct.valAt 0 U V w N h_space s_fix.mem
    let qA' := Succinct.quotAt 0 U w N h_space s_fix'.mem
    let vA' := Succinct.valAt 0 U V w N h_space s_fix'.mem
    let s_cur := buildBitState U V w N m θ s_fix td dt
    let s_tar := buildBitState U V w N m' θ s_fix' td' dt'
    (changedDenseList U V w N m₀ s_cur s_tar).length ≤
      diffCount2 ((List.range m₀).map (physOfDense N gm dt)) qA' vA' qA vA +
      diffCount (List.range m₀) (physByBase N (gm' 0 * slabSize N) dt')
        (physByBase N (gm 0 * slabSize N) dt) := by
  intro m₀ h_space gm gm' qA vA qA' vA' s_cur s_tar
  have heq_len : (changedDenseList U V w N m₀ s_cur s_tar).length =
      diffCount2 (List.range m₀)
        (qA' ∘ physOfDense N gm' dt') (vA' ∘ physOfDense N gm' dt')
        (qA ∘ physOfDense N gm dt) (vA ∘ physOfDense N gm dt) := by
    unfold changedDenseList diffCount2
    congr 1
    apply List.filter_congr
    intro d hd
    have hd_m : d < m := lt_of_lt_of_le (List.mem_range.mp hd) (Nat.min_le_left m m')
    have hd_m' : d < m' := lt_of_lt_of_le (List.mem_range.mp hd) (Nat.min_le_right m m')
    obtain ⟨hq_cur, hv_cur⟩ := buildBitState_denseQuotAt_ValAt hw hU hV θ s_fix td dt hd_m
    obtain ⟨hq_tar, hv_tar⟩ := buildBitState_denseQuotAt_ValAt hw hU hV θ s_fix' td' dt' hd_m'
    dsimp only [Function.comp_apply, s_cur, s_tar, qA, vA, qA', vA', gm, gm', h_space]
    rw [hq_cur, hv_cur, hq_tar, hv_tar]
    simp [ne_comm]
  rw [heq_len]
  calc diffCount2 (List.range m₀)
        (qA' ∘ physOfDense N gm' dt') (vA' ∘ physOfDense N gm' dt')
        (qA ∘ physOfDense N gm dt) (vA ∘ physOfDense N gm dt)
      ≤ diffCount2 (List.range m₀)
          (qA' ∘ physOfDense N gm' dt') (vA' ∘ physOfDense N gm' dt')
          (qA' ∘ physOfDense N gm dt) (vA' ∘ physOfDense N gm dt) +
        diffCount2 (List.range m₀)
          (qA' ∘ physOfDense N gm dt) (vA' ∘ physOfDense N gm dt)
          (qA ∘ physOfDense N gm dt) (vA ∘ physOfDense N gm dt) :=
        diffCount2_triangle _ _ _ _ _ _ _
    _ ≤ diffCount (List.range m₀) (physOfDense N gm' dt') (physOfDense N gm dt) +
        diffCount2 ((List.range m₀).map (physOfDense N gm dt)) qA' vA' qA vA := by
        rw [← diffCount2_comp]
        exact Nat.add_le_add_right (diffCount2_comp_le_diffCount _ _ _ _ _) _
    _ = diffCount2 ((List.range m₀).map (physOfDense N gm dt)) qA' vA' qA vA +
        diffCount (List.range m₀) (physByBase N (gm' 0 * slabSize N) dt')
          (physByBase N (gm 0 * slabSize N) dt) := by
        rw [Nat.add_comm, physOfDense_eq_physByBase, physOfDense_eq_physByBase]

/-- Bound on `(changedMetaList U w N s_cur s_tar).length` when `0 < N`, `s_cur` and `s_tar` are
`buildBitState` states, and `s_fix'` is obtained from `s_fix` by executing a frontier-preserving
`Memory.Prog` `p`. -/
theorem changedMetaList_length_le {U V w N m m' : ℕ}
    (hw : 0 < w) (hN : 0 < N)
    (θ : Succinct.QuotHashSeed U N)
    {α : Type} (p : Memory.Prog α) (s_fix : Memory.State)
    (hfr : ((Memory.spec 0).clientState s_fix p).frontier = s_fix.frontier)
    (td dt td' dt' : ℕ → ℕ) :
    let L_m := List.range (epochMetaWords U w N)
    let M := maxTailItems N
    let zMem : ℕ → ℕ := fun _ => 0
    let s_fix' := (Memory.spec 0).clientState s_fix p
    let s_cur := buildBitState U V w N m θ s_fix td dt
    let s_tar := buildBitState U V w N m' θ s_fix' td' dt'
    (changedMetaList U w N s_cur s_tar).length ≤
      1 + memoryCost p s_fix +
      diffCount L_m (packArray (offTD U w N) (globalPtrBits N) w td' M zMem)
        (packArray (offTD U w N) (globalPtrBits N) w td M zMem) +
      diffCount L_m (packArray (offDT U w N) (globalPtrBits N) w dt' M zMem)
        (packArray (offDT U w N) (globalPtrBits N) w dt M zMem) := by
  intro L_m M zMem s_fix' s_cur s_tar
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have heq_meta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN
  let h_space := Succinct.hashSpace U w N
  let L_lm := L_m.filter (fun a => decide (offLM U w N ≤ a))
  let L_fix := L_lm.map (fun a => a - offLM U w N + Succinct.offLM U V w N h_space)
  set f_fix := fun a => s_fix.mem (a - offLM U w N + Succinct.offLM U V w N h_space)
  set f_fix' := fun a => s_fix'.mem (a - offLM U w N + Succinct.offLM U V w N h_space)
  set pTD := packArray (offTD U w N) (globalPtrBits N) w td M zMem
  set pTD' := packArray (offTD U w N) (globalPtrBits N) w td' M zMem
  set pDT := packArray (offDT U w N) (globalPtrBits N) w dt M zMem
  set pDT' := packArray (offDT U w N) (globalPtrBits N) w dt' M zMem
  have hsub1 : (changedMetaList U w N s_cur s_tar).length ≤
      (L_m.filter (fun a => decide (a = 0 ∨ (f_fix' a ≠ f_fix a ∧ offLM U w N ≤ a)))).length +
      (L_m.filter (fun a => decide (pTD' a ≠ pTD a ∨ pDT' a ≠ pDT a))).length := by
    apply filter_sub_length_le
    intro a ha hne
    have ha_lt : a < epochMetaWords U w N := List.mem_range.mp ha
    simp only [decide_eq_true_eq] at hne ⊢
    rw [buildBitState_mem_lt_metaWords hw θ s_fix td dt ha_lt,
      buildBitState_mem_lt_metaWords hw θ s_fix' td' dt' ha_lt] at hne
    by_cases hlt_td : a < offTD U w N
    · left
      rw [epochMetaMem_lt_offTD hw θ s_fix.mem td dt hlt_td,
        epochMetaMem_lt_offTD hw θ s_fix'.mem td' dt' hlt_td] at hne
      unfold baseMetaMem at hne
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · right
        rw [ite_eq_right ha0, ite_eq_right ha0] at hne
        by_cases hlt_lm : a < offLM U w N
        · exfalso
          apply hne
          split_ifs <;> rfl
        · refine ⟨?_, Nat.le_of_not_lt hlt_lm⟩
          intro hfeq
          apply hne
          dsimp only [f_fix', f_fix, h_space] at hfeq
          rw [ite_eq_right hlt_lm, ite_eq_right hlt_lm, hfeq]
    · right
      have hge_td : offTD U w N ≤ a := Nat.le_of_not_lt hlt_td
      rw [epochMetaMem_eq_pack_zero_of_ge_offTD hN θ s_fix.mem td dt hge_td,
        epochMetaMem_eq_pack_zero_of_ge_offTD hN θ s_fix'.mem td' dt' hge_td] at hne
      by_cases hlt_dt : a < offDT U w N
      · left
        have hout : ¬(offDT U w N ≤ a ∧ a < offDT U w N + packedWords M (globalPtrBits N) w) := by
          omega
        rw [packArray_outside hw dt le_rfl _ hout,
          packArray_outside hw dt' le_rfl _ hout] at hne
        exact hne.symm
      · right
        have hge_dt : offDT U w N ≤ a := Nat.le_of_not_lt hlt_dt
        have h1 : ∀ len {addr : ℕ}, offDT U w N ≤ addr →
            packArray (offDT U w N) (globalPtrBits N) w dt len pTD addr =
              packArray (offDT U w N) (globalPtrBits N) w dt len zMem addr := by
          intro len
          induction len with
          | zero =>
            intro addr haddr
            unfold packArray
            dsimp only [pTD]
            exact packArray_outside hw td le_rfl zMem
              (by unfold offDT at haddr; dsimp only [M] at haddr ⊢; omega)
          | succ i ih =>
            intro addr haddr
            unfold packArray
            exact writePacked_apply_congr _ _ _ i (dt i) addr (ih haddr)
        have h2 : ∀ len {addr : ℕ}, offDT U w N ≤ addr →
            packArray (offDT U w N) (globalPtrBits N) w dt' len pTD' addr =
              packArray (offDT U w N) (globalPtrBits N) w dt' len zMem addr := by
          intro len
          induction len with
          | zero =>
            intro addr haddr
            unfold packArray
            dsimp only [pTD']
            exact packArray_outside hw td' le_rfl zMem
              (by unfold offDT at haddr; dsimp only [M] at haddr ⊢; omega)
          | succ i ih =>
            intro addr haddr
            unfold packArray
            exact writePacked_apply_congr _ _ _ i (dt' i) addr (ih haddr)
        rw [h1 M hge_dt, h2 M hge_dt] at hne
        exact hne.symm
  have hsub2 :
      (L_m.filter (fun a => decide (a = 0 ∨ (f_fix' a ≠ f_fix a ∧ offLM U w N ≤ a)))).length ≤
      1 + memoryCost p s_fix := by
    have hle := filter_sub_length_le L_m
      (fun a => decide (a = 0 ∨ (f_fix' a ≠ f_fix a ∧ offLM U w N ≤ a)))
      (fun a => decide (a = 0))
      (fun a => decide (f_fix' a ≠ f_fix a ∧ offLM U w N ≤ a))
      (fun a _ hx => by simp only [decide_eq_true_eq] at hx ⊢; exact hx)
    have h0 := filter_eq_length_le_one (L := L_m) List.nodup_range 0
    have hmap : (L_m.filter (fun a => decide (f_fix' a ≠ f_fix a ∧ offLM U w N ≤ a))).length =
        diffCount L_fix s_fix'.mem s_fix.mem := by
      unfold diffCount
      dsimp only [L_fix, L_lm, f_fix', f_fix]
      rw [List.filter_map, List.length_map, List.filter_filter]
      congr 2
    have hnodup_fix : L_fix.Nodup := by
      refine (List.nodup_map_iff_inj_on (List.Nodup.filter _ List.nodup_range)).mpr ?_
      intro x hx y hy hxy
      have hx_ge : offLM U w N ≤ x := (List.mem_filter.mp hx).2 |> of_decide_eq_true
      have hy_ge : offLM U w N ≤ y := (List.mem_filter.mp hy).2 |> of_decide_eq_true
      omega
    have hmem_cost : diffCount L_fix s_fix'.mem s_fix.mem ≤ memoryCost p s_fix :=
      changedWords_le_memoryCost hnodup_fix p s_fix hfr
    omega
  have hsub3 : (L_m.filter (fun a => decide (pTD' a ≠ pTD a ∨ pDT' a ≠ pDT a))).length ≤
      diffCount L_m pTD' pTD + diffCount L_m pDT' pDT := by
    apply filter_sub_length_le
    intro a _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact hx
  omega

end Cslib.DataStructure.Dictionary.BitResizable

