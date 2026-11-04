/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.DynamicArray.BitResizable

/-!
# Single-Tape Subroutine Composition and Released-Bit Reuse for Bit-Resizable Arrays

All multi-structure and subroutine compositions in this module live in a **single** linear
bit-resizable memory state `s : BitMemory.State` (`[0, s.bitSize)`):
1. `singleTape_sequential_subroutine_reuse`: a client runs a first resizable-array computation on
   `BitMemory.dirtySpec w` that shrinks back to empty (`s₁.bitSize = 0`), and a second
   resizable-array computation immediately reuses the released `[0, M)` bit address space from bit
   offset `0` on the same `BitMemory.State`.
2. `SingleTapeTwoArrays`: two resizable `b`-bit arrays `(xs₁, xs₂)` coexist simultaneously in one
   `BitMemory.State` with a `w`-bit header at `[0, w)` storing `n₁ = xs₁.length`, `xs₁` packed in
   `[w, w + n₁ * b)`, and `xs₂` packed in `[w + n₁ * b, w + (n₁ + n₂) * b)`, so the single tape
   has exact bit size `s.bitSize = w + (xs₁.length + xs₂.length) * b` at every step. When an item
   is popped from the tail of `xs₂` (shrinking `s.bitSize` by `b` bits via `shrink b`) and appended
   to `xs₁` (`singleTape_pop₂_append₁_reuses_released_bits`), the `b` bits released by `shrink b`
   are immediately reused by `grow b` on the same `BitMemory.State` under demonic `dirtySpec w`
   without exceeding `w + (xs₁.length + xs₂.length) * b` bits.

## Main definitions

* `SingleTapeTwoArrays`: concurrent single-tape representation of two `b`-bit arrays in one
  `BitMemory.State`.
* `initSingleTapeTwoArrays`: initializes `(xs₁ = [], xs₂ = [])` from `BitMemory.empty`.
* `singleTapePop₂Append₁Prog`: pops the sole item of `xs₂` via `shrink b` and appends it to `xs₁`
  via `grow b` in the same linear `BitMemory.State`.

## Main results

* `link_bind`: linking commutes with monadic bind on `Client`.
* `singleTape_sequential_subroutine_reuse`: sequential single-tape subroutine reuse on demonic
  `BitMemory.dirtySpec w`.
* `initSingleTapeTwoArrays_demonic`: demonic initialization of `SingleTapeTwoArrays`.
* `singleTape_pop₂_append₁_reuses_released_bits`: concurrent single-tape released-bit reuse on
  demonic `BitMemory.dirtySpec w`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.DataStructure.DynamicArray.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory

variable {w b : ℕ}

/-- Linking commutes with monadic bind on `Client`. -/
theorem link_bind {D E : StateTransitionSpec} {α β : Type} (m : Methods D E)
    (p : D.Client α) (k : α → D.Client β) :
    (link m p).bind (fun a => link m (k a)) = link m (p.bind k) := by
  induction p with
  | pure a => rfl
  | liftBind o cont ih =>
    change ((m o).bind (fun x => link m (cont x))).bind (fun a => link m (k a)) =
      (m o).bind (fun x => link m ((cont x).bind k))
    rw [PFunctor.FreeM.bind_assoc]
    congr 1
    funext x
    exact ih x

/-- **Sequential single-tape subroutine composition on demonic `BitMemory.dirtySpec w`**:
when a client runs a phase-1 array program `p₁` from `BitMemory.empty` that returns the array to
empty (`(DynamicArray.spec w b).clientState [] p₁ = []`, releasing all allocated bits via `shrink`
so `s₁.bitSize = 0`), and then runs a phase-2 array program `p₂` on the **same** single tape `s₁`,
phase 2 reuses the released bit address space `[0, M)` from bit offset `0`, producing the exact
phase-2 result and final array `xs₂'` with `s₂.bitSize = xs₂'.length * b` and combined cost at most
`3 * (m₁ + m₂)`. -/
theorem singleTape_sequential_subroutine_reuse {α β : Type}
    (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (p₁ : (DynamicArray.spec w b).Client α)
    (p₂ : α → (DynamicArray.spec w b).Client β)
    (hv₁ : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory [] p₁))
    (hempty₁ : (DynamicArray.spec w b).clientState [] p₁ = [])
    (hv₂ : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory []
        (p₂ ((DynamicArray.spec w b).clientResult [] p₁)))) :
    let a₁ := (DynamicArray.spec w b).clientResult [] p₁
    let combined := do
      let a ← link (dirtyMethods w b) p₁
      link (dirtyMethods w b) (p₂ a)
    (BitMemory.dirtySpec w).DemonicValid BitMemory.empty combined ∧
      ∀ r s₂ tr,
        (BitMemory.dirtySpec w).ClientRun BitMemory.empty combined r s₂ tr →
        (BitMemory.dirtySpec w).ValidTranscript BitMemory.empty tr s₂ ∧
          r = (DynamicArray.spec w b).clientResult [] (p₂ a₁) ∧
          abs w b s₂ = (DynamicArray.spec w b).clientState [] (p₂ a₁) ∧
          s₂.bitSize = ((DynamicArray.spec w b).clientState [] (p₂ a₁)).length * b ∧
          (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) BitMemory.empty tr ≤
            3 * (((DynamicArray.spec w b).clientHistory [] p₁).length +
              ((DynamicArray.spec w b).clientHistory [] (p₂ a₁)).length) := by
  intro a₁ combined
  have hcomp : combined = link (dirtyMethods w b) (p₁ >>= p₂) :=
    link_bind (dirtyMethods w b) p₁ p₂
  have hv_both : (DynamicArray.spec w b).ValidHistory []
      ((DynamicArray.spec w b).clientHistory [] (p₁ >>= p₂)) := by
    rw [StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append]
    refine ⟨hv₁, ?_⟩
    rw [(DynamicArray.spec w b).run_runClient p₁ [], hempty₁]
    exact hv₂
  obtain ⟨hdv, hmain_run⟩ := dirty_client_run_from_empty hw hb hbw (p₁ >>= p₂) hv_both
  rw [← hcomp] at hdv hmain_run
  refine ⟨hdv, fun r s₂ tr hrun => ?_⟩
  rcases hmain_run r s₂ tr hrun with ⟨hv_low, hr, habs₂, hsz₂, hcost⟩
  have hr_eq : (DynamicArray.spec w b).clientResult [] (p₁ >>= p₂) =
      (DynamicArray.spec w b).clientResult [] (p₂ a₁) := by
    rw [StateTransitionSpec.clientResult_bind, hempty₁]
  have hst_eq : (DynamicArray.spec w b).clientState [] (p₁ >>= p₂) =
      (DynamicArray.spec w b).clientState [] (p₂ a₁) := by
    rw [StateTransitionSpec.clientState_bind, hempty₁]
  have hhist_eq : ((DynamicArray.spec w b).clientHistory [] (p₁ >>= p₂)).length =
      ((DynamicArray.spec w b).clientHistory [] p₁).length +
        ((DynamicArray.spec w b).clientHistory [] (p₂ a₁)).length := by
    rw [StateTransitionSpec.clientHistory_bind, hempty₁, List.length_append]
  rw [hr_eq] at hr
  rw [hst_eq] at habs₂ hsz₂
  rw [hhist_eq] at hcost
  exact ⟨hv_low, hr, habs₂, hsz₂, hcost⟩

/-- **Concurrent single-tape two-array representation (`SingleTapeTwoArrays`)**:
two resizable `b`-bit arrays `(xs₁, xs₂)` stored simultaneously in a **single** linear
`s : BitMemory.State` (`[0, s.bitSize)`):
* Bits `[0, w)` hold the `w`-bit header `n₁ = xs₁.length`.
* Bits `[w, w + n₁ * b)` hold the `n₁` items of `xs₁`.
* Bits `[w + n₁ * b, w + (n₁ + n₂) * b)` hold the `n₂` items of `xs₂`.
* The total allocated bit size of the single tape is `s.bitSize = w + (n₁ + n₂) * b`. -/
structure SingleTapeTwoArrays (w b : ℕ) (s : BitMemory.State)
    (xs₁ xs₂ : DynamicArray.State) : Prop where
  /-- The single bit-memory state is well-formed at word width `w`. -/
  wellFormed : s.WellFormed w
  /-- Header `[0, w)` stores `xs₁.length`. -/
  header_eq : s.getField w 0 w = xs₁.length
  /-- `xs₁.length` fits in a `w`-bit word. -/
  len₁_fits : Fits w xs₁.length
  /-- Total allocated bit size is `w + (xs₁.length + xs₂.length) * b`. -/
  bitSize_eq : s.bitSize = w + (xs₁.length + xs₂.length) * b
  /-- Array 1 items sit in `[w, w + xs₁.length * b)`. -/
  items₁ : ∀ i (hi : i < xs₁.length), s.getField w (w + i * b) b = xs₁[i]
  /-- Array 2 items sit in `[w + xs₁.length * b, w + (xs₁.length + xs₂.length) * b)`. -/
  items₂ : ∀ j (hj : j < xs₂.length),
    s.getField w (w + (xs₁.length + j) * b) b = xs₂[j]

/-- Initialize the single-tape two-array layout `(xs₁ = [], xs₂ = [])` from `BitMemory.empty` by
growing `w` bits for the header and writing `0` into `[0, w)`. -/
def initSingleTapeTwoArrays (w : ℕ) : BitMemory.Prog Unit := do
  let _ ← BitMemory.grow w
  BitMemory.writeBits 0 w 0

/-- Initializing `SingleTapeTwoArrays` from `BitMemory.empty` on demonic `BitMemory.dirtySpec w`
establishes `SingleTapeTwoArrays w b s' [] []` with `s'.bitSize = w` in `2` bit-memory units. -/
theorem initSingleTapeTwoArrays_demonic (hw : 0 < w)
    {r : Unit} {s' : BitMemory.State} {tr : (BitMemory.dirtySpec w).Transcript}
    (hrun : (BitMemory.dirtySpec w).ClientRun BitMemory.empty
      (initSingleTapeTwoArrays w) r s' tr) :
    SingleTapeTwoArrays w b s' [] [] ∧ s'.bitSize = w ∧
      (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) BitMemory.empty tr = 2 := by
  obtain ⟨_, off, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
  obtain ⟨_, u, s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
  obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₂
  have hoff : off = 0 := hstep₁.2.1
  subst hoff
  have hsz₁ : s₁.bitSize = w := by simpa using hstep₁.1
  have hvalid₁ : BitMemory.valid w BitMemory.empty (.grow w) := by
    change Fits w (0 + w)
    simpa using fits_self w
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow w) hw (BitMemory.wellFormed_empty w)
      hvalid₁ hstep₁
  obtain ⟨h2, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
  have hs'_wf : s'.WellFormed w := by
    rw [← h2]
    exact BitMemory.wellFormed_stepFn (o := .writeBits 0 w 0) hw hs₁_wf
      ⟨le_rfl, by omega, fits_zero w⟩
  have hsz' : s'.bitSize = w := by
    rw [← h2]
    exact hsz₁
  refine ⟨⟨hs'_wf, ?_, fits_zero w, by simp [hsz'], fun i hi => by simp at hi,
    fun j hj => by simp at hj⟩, hsz', ?_⟩
  · rw [← h2]
    change readField w 0 (writeFieldMem w 0 s₁.mem 0 w 0) 0 w = 0
    exact readField_writeFieldMem_same hw s₁.mem le_rfl (fits_zero w)
  · have hch : BitMemory.charge w BitMemory.empty (.grow w) = 1 :=
      BitMemory.charge_grow_of_le hw le_rfl BitMemory.empty
    simp [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, hch]

/-- Single-tape program that pops the sole item of `xs₂ = [v]` (at bit offset `w + n₁ * b`) by
calling `shrink b` on the single tape, and then appends `v` to `xs₁` by calling `grow b`, writing
`v` into `[w + n₁ * b, w + (n₁ + 1) * b)`, and incrementing the header `n₁` in `[0, w)`. -/
def singleTapePop₂Append₁Prog (w b : ℕ) : BitMemory.Prog ℕ := do
  let n₁ ← BitMemory.readBits 0 w
  let v ← BitMemory.readBits (w + n₁ * b) b
  BitMemory.shrink b
  let off ← BitMemory.grow b
  BitMemory.writeBits off b v
  BitMemory.writeBits 0 w (n₁ + 1)
  pure v

/-- **Single-tape released-memory reuse (`singleTape_pop₂_append₁_reuses_released_bits`)**:
in a **single** linear `BitMemory.State` holding `SingleTapeTwoArrays w b s xs₁ [v]`, executing
`singleTapePop₂Append₁Prog w b` on demonic `BitMemory.dirtySpec w` pops `v` from array 2 via
`shrink b` (reducing `s.bitSize` from `w + (xs₁.length + 1) * b` to `w + xs₁.length * b`) and
immediately reuses those `b` bits via `grow b` to append `v` to array 1, ending in a state `s'`
on the **same** single tape satisfying `SingleTapeTwoArrays w b s' (xs₁ ++ [v]) []` with
`s'.bitSize = s.bitSize = w + (xs₁.length + 1) * b` in `6` bit-memory units (`O(1)` time). -/
theorem singleTape_pop₂_append₁_reuses_released_bits (hw : 0 < w) (hbw : b ≤ w)
    {s : BitMemory.State} {xs₁ : DynamicArray.State} {v : ℕ}
    (hst : SingleTapeTwoArrays w b s xs₁ [v])
    (hn₁_succ : Fits w (xs₁.length + 1)) (hv_fits : Fits b v)
    {r : ℕ} {s' : BitMemory.State} {tr : (BitMemory.dirtySpec w).Transcript}
    (hrun : (BitMemory.dirtySpec w).ClientRun s (singleTapePop₂Append₁Prog w b) r s' tr) :
    r = v ∧
      SingleTapeTwoArrays w b s' (xs₁ ++ [v]) [] ∧
      s'.bitSize = s.bitSize ∧
      (BitMemory.dirtySpec w).totalCostTranscript (BitMemory.charge w) s tr = 6 := by
  obtain ⟨_, n₁, s₁, tr₁, hstep₁, hrun₁, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun
  obtain ⟨h1, h1v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₁
  subst h1; subst h1v
  obtain ⟨_, v', s₂, tr₂, hstep₂, hrun₂, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₁
  obtain ⟨h2, h2v⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₂
  subst h2; subst h2v
  obtain ⟨_, u₃, s₃, tr₃, hstep₃, hrun₃, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₂
  obtain ⟨h3, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₃
  subst h3
  obtain ⟨_, off, s₄, tr₄, hstep₄, hrun₄, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₃
  obtain ⟨_, u₅, s₅, tr₅, hstep₅, hrun₅, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₄
  obtain ⟨h5, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₅
  subst h5
  obtain ⟨_, u₆, s₆, tr₆, hstep₆, hrun₆, rfl⟩ :=
    ((BitMemory.dirtySpec w).clientRun_liftBind_iff _ _ _ _ _ _).mp hrun₅
  obtain ⟨h6, -⟩ := (Prod.mk.injEq _ _ _ _).mp hstep₆
  subst h6
  obtain ⟨rfl, rfl, rfl⟩ := ((BitMemory.dirtySpec w).clientRun_pure_iff _ _ _ _ _).mp hrun₆
  have hn₁_eq : readField w 0 s.mem 0 w = xs₁.length := hst.header_eq
  have hv_eq : readField w 0 s.mem (w + readField w 0 s.mem 0 w * b) b = v := by
    rw [hn₁_eq]
    have h0 := hst.items₂ 0 (by simp)
    change readField w 0 s.mem (w + (xs₁.length + 0) * b) b = [v][0] at h0
    simpa using h0
  have hsz_s : s.bitSize = w + (xs₁.length + 1) * b := by
    simpa using hst.bitSize_eq
  have hle_b : b ≤ s.bitSize := by
    rw [hsz_s, Nat.add_mul, Nat.one_mul]
    omega
  have hs₃_wf : (BitMemory.stepFn w s (.shrink b)).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink b) hw hst.wellFormed hle_b
  have hsz₃ : s.bitSize - b = w + xs₁.length * b := by
    rw [hsz_s, Nat.add_mul, Nat.one_mul]
    omega
  have hoff_step : off = s.bitSize - b := hstep₄.2.1
  subst hoff_step
  have hstep₄_sz : s₄.bitSize = (s.bitSize - b) + b := hstep₄.1
  have hsz₄ : s₄.bitSize = s.bitSize := by
    rw [hstep₄_sz, Nat.sub_add_cancel hle_b]
  have hgrow_valid : BitMemory.valid w (BitMemory.stepFn w s (.shrink b)).1 (.grow b) := by
    change Fits w ((s.bitSize - b) + b)
    rw [Nat.sub_add_cancel hle_b]
    exact hst.wellFormed.bitSize_fits
  have hs₄_wf : s₄.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow b) hw hs₃_wf hgrow_valid hstep₄
  have hmem₅_eq : writeFieldMem w 0 s₄.mem (s.bitSize - b) b v =
      writeFieldMem w 0 (BitMemory.stepFn w s (.shrink b)).1.mem (w + xs₁.length * b) b v := by
    have h1 := writeFieldMem_of_dirtyStep_grow hw hs₃_wf hbw hstep₄ (val := v)
    change writeFieldMem w 0 s₄.mem (s.bitSize - b) b v =
      writeFieldMem w 0 (BitMemory.stepFn w s (.shrink b)).1.mem (s.bitSize - b) b v at h1
    exact h1.trans (by rw [hsz₃])
  rw [hv_eq, hn₁_eq]
  have hs₅_wf : (BitMemory.stepFn w s₄ (.writeBits (s.bitSize - b) b v)).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .writeBits (s.bitSize - b) b v) hw hs₄_wf
      ⟨hbw, by rw [hsz₄]; exact (Nat.sub_add_cancel hle_b).le, hv_fits⟩
  have hs'_wf : (BitMemory.stepFn w (BitMemory.stepFn w s₄ (.writeBits (s.bitSize - b) b v)).1
      (.writeBits 0 w (xs₁.length + 1))).1.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .writeBits 0 w (xs₁.length + 1)) hw hs₅_wf
      ⟨le_rfl, by change 0 + w ≤ s₄.bitSize; omega, hn₁_succ⟩
  refine ⟨rfl, ⟨hs'_wf, ?_, ?_, ?_, ?_, ?_⟩, hsz₄, ?_⟩
  · change readField w 0 (writeFieldMem w 0 _ 0 w (xs₁.length + 1)) 0 w = (xs₁ ++ [v]).length
    rw [List.length_append, List.length_singleton]
    exact readField_writeFieldMem_same hw _ le_rfl hn₁_succ
  · simpa using hn₁_succ
  · change s₄.bitSize = w + ((xs₁ ++ [v]).length + [].length) * b
    simpa [hsz_s] using hsz₄
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    change readField w 0 (writeFieldMem w 0 (writeFieldMem w 0 s₄.mem (s.bitSize - b) b v)
        0 w (xs₁.length + 1)) (w + i * b) b = (xs₁ ++ [v])[i]
    rw [readField_writeFieldMem_of_disjoint hw _ le_rfl hbw (Or.inr (by omega)), hmem₅_eq]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi_lt | rfl
    · rw [List.getElem_append_left hi_lt]
      have hdisj : (w + i * b) + b ≤ w + xs₁.length * b := by
        have := slot_end_le_of_lt b hi_lt
        omega
      rw [readField_writeFieldMem_of_disjoint hw _ hbw hbw (Or.inl hdisj)]
      have hsh := getField_stepFn_shrink (a := w + i * b) hw s b hbw (by omega)
      exact hsh.trans (hst.items₁ i hi_lt)
    · rw [List.getElem_append_right (le_rfl)]
      simp only [Nat.sub_self, List.getElem_singleton]
      exact readField_writeFieldMem_same hw _ hbw hv_fits
  · intro j hj
    simp at hj
  · have hch_sh : BitMemory.charge w s (.shrink b) = 1 :=
      BitMemory.charge_shrink_of_le hw hbw s
    have hch_gr : BitMemory.charge w
        { mem := clearRangeMem w s.mem (s.bitSize - b) s.bitSize, bitSize := s.bitSize - b }
        (.grow b) = 1 :=
      BitMemory.charge_grow_of_le hw hbw _
    simp only [StateTransitionSpec.totalCostTranscript_cons,
      StateTransitionSpec.totalCostTranscript_nil, BitMemory.charge_readBits,
      BitMemory.charge_writeBits, hch_sh, hch_gr]

end Cslib.DataStructure.DynamicArray.BitResizable
