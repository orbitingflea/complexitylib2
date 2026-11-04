/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Operations
public import Complexity.DataStructure.Dictionary.BitResizable.Sync

/-!
# Companion State Construction and Word/Item Difference Counting

This module bridges the fixed-capacity dictionary state (`Succinct.DictStateInv`) with the
single-tape bit-resizable representation (`Rep`) and provides the difference-counting machinery
(`diffCount`, `diffCount2`, `changedWords_le_memoryCost`) used to bound the number of dense items
and metadata words modified during an in-epoch `insert` or `delete`.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.diffCount`,
  `Cslib.DataStructure.Dictionary.BitResizable.diffCount2`: difference counts on duplicate-free
  lists.
* `Cslib.DataStructure.Dictionary.BitResizable.packArray`: functional bit-packing of a length-`len`
  array into word-indexed memory via `BitPackedArray.writePacked`.
* `Cslib.DataStructure.Dictionary.BitResizable.packDenseItems`: functional bit-packing of `m` dense
  `(quotient, value)` items into `[epochMetaBits U w N, dictBitSize U V w N m)`.
* `Cslib.DataStructure.Dictionary.BitResizable.buildBitState`: canonical single-tape
  `BitMemory.State` induced by a companion `(s_fix, td, dt)` triple.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.changedWords_le_memoryCost`: any `Memory.Prog`
  preserving `s.frontier` modifies at most `memoryCost p s` word addresses.
* `Cslib.DataStructure.Dictionary.BitResizable.diffCount_packArray_update_le`: updating one entry of
  a packed array modifies at most `2` words.
* `Cslib.DataStructure.Dictionary.BitResizable.rep_buildBitState`: `buildBitState` satisfies `Rep`
  whenever `s_fix` satisfies `Succinct.DictStateInv` and `(td, dt)` satisfies `TailDenseInv`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability

/-! ## Section 1: Difference counting (`diffCount`, `diffCount2`) and `memoryCost` word bound -/

/-- Number of elements `x ∈ L` where `f x ≠ g x`. -/
@[expose] def diffCount (L : List ℕ) (f g : ℕ → ℕ) : ℕ :=
  (L.filter (fun x => decide (f x ≠ g x))).length

/-- Number of elements `x ∈ L` where `f₁ x ≠ g₁ x ∨ f₂ x ≠ g₂ x`. -/
@[expose] def diffCount2 (L : List ℕ) (f₁ f₂ g₁ g₂ : ℕ → ℕ) : ℕ :=
  (L.filter (fun x => decide (f₁ x ≠ g₁ x ∨ f₂ x ≠ g₂ x))).length

@[simp]
theorem diffCount_self (L : List ℕ) (f : ℕ → ℕ) : diffCount L f f = 0 := by
  unfold diffCount; simp

@[simp]
theorem diffCount2_self (L : List ℕ) (f₁ f₂ : ℕ → ℕ) : diffCount2 L f₁ f₂ f₁ f₂ = 0 := by
  unfold diffCount2; simp

theorem diffCount_symm (L : List ℕ) (f g : ℕ → ℕ) : diffCount L f g = diffCount L g f := by
  unfold diffCount; congr 1; apply List.filter_congr; intro x _; simp [ne_comm]

theorem filter_sub_length_le {α : Type} (L : List α) (p q r : α → Bool)
    (himp : ∀ x ∈ L, p x = true → q x = true ∨ r x = true) :
    (L.filter p).length ≤ (L.filter q).length + (L.filter r).length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => himp y (List.mem_cons_of_mem x hy))
    have hx := himp x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> cases hr : r x
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih'
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · exfalso; rcases hx hp with h | h <;> [rw [hq] at h; rw [hr] at h] <;> contradiction
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · simp only [↓reduceIte, List.length_cons]; omega

theorem diffCount_triangle (L : List ℕ) (f g h : ℕ → ℕ) :
    diffCount L f h ≤ diffCount L f g + diffCount L g h := by
  apply filter_sub_length_le
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  by_cases hfg : f x = g x
  · exact Or.inr (by omega)
  · exact Or.inl hfg

theorem diffCount2_triangle (L : List ℕ) (f₁ f₂ g₁ g₂ h₁ h₂ : ℕ → ℕ) :
    diffCount2 L f₁ f₂ h₁ h₂ ≤ diffCount2 L f₁ f₂ g₁ g₂ + diffCount2 L g₁ g₂ h₁ h₂ := by
  apply filter_sub_length_le
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  rcases hx with h1 | h2
  · by_cases heq : f₁ x = g₁ x
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (Or.inl heq)
  · by_cases heq : f₂ x = g₂ x
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inl (Or.inr heq)

theorem filter_eq_length_le_one {L : List ℕ} (hnodup : L.Nodup) (a : ℕ) :
    (L.filter (fun x => decide (x = a))).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hx_not, hxs⟩
    simp only [List.filter_cons]
    by_cases hxa : x = a
    · subst hxa
      simp only [decide_true, ↓reduceIte]
      have h0 : xs.filter (fun y => decide (y = x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        simp only [decide_eq_true_eq]
        rintro rfl
        exact hx_not hy
      rw [h0]
      exact le_rfl
    · simp only [hxa, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih hxs

theorem diffCount_of_eq_off_one {L : List ℕ} (hnodup : L.Nodup) {f g : ℕ → ℕ} (a : ℕ)
    (h : ∀ x, x ≠ a → f x = g x) :
    diffCount L f g ≤ 1 := by
  calc diffCount L f g
      ≤ (L.filter (fun x => decide (x = a))).length + (L.filter (fun _ => false)).length := by
        apply filter_sub_length_le
        intro x _ hx
        simp only [decide_eq_true_eq] at hx ⊢
        by_cases hxa : x = a
        · exact Or.inl hxa
        · exact False.elim (hx (h x hxa))
    _ ≤ 1 + 0 := Nat.add_le_add (filter_eq_length_le_one hnodup a) (by simp)
    _ = 1 := by omega

theorem diffCount_of_eq_off_two {L : List ℕ} (hnodup : L.Nodup) {f g : ℕ → ℕ} (a₀ a₁ : ℕ)
    (h : ∀ x, x ≠ a₀ → x ≠ a₁ → f x = g x) :
    diffCount L f g ≤ 2 := by
  calc diffCount L f g
      ≤ (L.filter (fun x => decide (x = a₀))).length +
          (L.filter (fun x => decide (x = a₁))).length := by
        apply filter_sub_length_le
        intro x _ hx
        simp only [decide_eq_true_eq] at hx ⊢
        by_cases h0 : x = a₀
        · exact Or.inl h0
        · by_cases h1 : x = a₁
          · exact Or.inr h1
          · exact False.elim (hx (h x h0 h1))
    _ ≤ 1 + 1 := Nat.add_le_add (filter_eq_length_le_one hnodup a₀)
        (filter_eq_length_le_one hnodup a₁)
    _ = 2 := by omega

theorem diffCount_update_self {L : List ℕ} (hnodup : L.Nodup) (f : ℕ → ℕ) (a v : ℕ) :
    diffCount L (Function.update f a v) f ≤ 1 :=
  diffCount_of_eq_off_one hnodup a fun _ hne => Function.update_of_ne hne v f

theorem diffCount_update_le {L : List ℕ} (hnodup : L.Nodup) (f g : ℕ → ℕ) (a v : ℕ) :
    diffCount L (Function.update f a v) g ≤ diffCount L f g + 1 := by
  calc diffCount L (Function.update f a v) g
      ≤ diffCount L (Function.update f a v) f + diffCount L f g :=
        diffCount_triangle L _ f g
    _ ≤ 1 + diffCount L f g := Nat.add_le_add_right (diffCount_update_self hnodup f a v) _
    _ = diffCount L f g + 1 := Nat.add_comm _ _

theorem diffCount2_update_both_self {L : List ℕ} (hnodup : L.Nodup) (f₁ f₂ : ℕ → ℕ)
    (a v₁ v₂ : ℕ) :
    diffCount2 L (Function.update f₁ a v₁) (Function.update f₂ a v₂) f₁ f₂ ≤ 1 := by
  calc diffCount2 L (Function.update f₁ a v₁) (Function.update f₂ a v₂) f₁ f₂
      ≤ (L.filter (fun x => decide (x = a))).length + (L.filter (fun _ => false)).length := by
        apply filter_sub_length_le
        intro x _ hx
        simp only [decide_eq_true_eq] at hx ⊢
        by_cases hxa : x = a
        · exact Or.inl hxa
        · rcases hx with h1 | h2
          · exact False.elim (h1 (Function.update_of_ne hxa v₁ f₁))
          · exact False.elim (h2 (Function.update_of_ne hxa v₂ f₂))
    _ ≤ 1 + 0 := Nat.add_le_add (filter_eq_length_le_one hnodup a) (by simp)
    _ = 1 := by omega

theorem diffCount2_update_both_le {L : List ℕ} (hnodup : L.Nodup) (f₁ f₂ g₁ g₂ : ℕ → ℕ)
    (a v₁ v₂ : ℕ) :
    diffCount2 L (Function.update f₁ a v₁) (Function.update f₂ a v₂) g₁ g₂ ≤
      diffCount2 L f₁ f₂ g₁ g₂ + 1 := by
  calc diffCount2 L (Function.update f₁ a v₁) (Function.update f₂ a v₂) g₁ g₂
      ≤ diffCount2 L (Function.update f₁ a v₁) (Function.update f₂ a v₂) f₁ f₂ +
          diffCount2 L f₁ f₂ g₁ g₂ :=
        diffCount2_triangle L _ _ f₁ f₂ g₁ g₂
    _ ≤ 1 + diffCount2 L f₁ f₂ g₁ g₂ :=
        Nat.add_le_add_right (diffCount2_update_both_self hnodup f₁ f₂ a v₁ v₂) _
    _ = diffCount2 L f₁ f₂ g₁ g₂ + 1 := Nat.add_comm _ _

theorem diffCount2_update_right_le {L : List ℕ} (hnodup : L.Nodup) (f₁ f₂ g₁ g₂ : ℕ → ℕ)
    (a v₂ : ℕ) :
    diffCount2 L f₁ (Function.update f₂ a v₂) g₁ g₂ ≤ diffCount2 L f₁ f₂ g₁ g₂ + 1 := by
  have h1 := diffCount2_update_both_le hnodup f₁ f₂ g₁ g₂ a (f₁ a) v₂
  rwa [Function.update_eq_self] at h1

theorem diffCount2_update_left_le {L : List ℕ} (hnodup : L.Nodup) (f₁ f₂ g₁ g₂ : ℕ → ℕ)
    (a v₁ : ℕ) :
    diffCount2 L (Function.update f₁ a v₁) f₂ g₁ g₂ ≤ diffCount2 L f₁ f₂ g₁ g₂ + 1 := by
  have h1 := diffCount2_update_both_le hnodup f₁ f₂ g₁ g₂ a v₁ (f₂ a)
  rwa [Function.update_eq_self] at h1

/-- Any single `Memory.step s o` that preserves `s.frontier` modifies at most `Memory.charge s o`
addresses in any duplicate-free list `L`. -/
theorem diffCount_memoryStep_le {L : List ℕ} (hnodup : L.Nodup) (s : Memory.State) (o : Memory.Op)
    (hfr : (Memory.step s o).1.frontier = s.frontier) :
    diffCount L (Memory.step s o).1.mem s.mem ≤ Memory.charge s o := by
  cases o with
  | read a =>
    simp [Memory.step]
  | write a v =>
    have hle : diffCount L (Function.update s.mem a v) s.mem ≤ 1 :=
      diffCount_update_self hnodup s.mem a v
    have hpos : 1 ≤ Memory.charge s (.write a v) := Memory.one_le_charge s (.write a v)
    exact hle.trans hpos
  | alloc k =>
    have hk0 : k = 0 := by
      change s.frontier + k = s.frontier at hfr
      omega
    subst hk0
    have hclr : clear s.mem s.frontier 0 = s.mem := by
      funext addr
      simp [clear]
    change diffCount L (clear s.mem s.frontier 0) s.mem ≤ _
    rw [hclr, diffCount_self]
    exact Nat.zero_le _
  | allocDirty k =>
    simp [Memory.step]

/-- **Memory-cost bound on modified words (`changedWords_le_memoryCost`):**
for any `p : Memory.Prog α` and `s : Memory.State` such that
`((Memory.spec 0).clientState s p).frontier = s.frontier`, the number of addresses in any
duplicate-free list `L` where `((Memory.spec 0).clientState s p).mem` differs from `s.mem` is at
most `memoryCost p s`. -/
theorem changedWords_le_memoryCost {α : Type} {L : List ℕ} (hnodup : L.Nodup)
    (p : Memory.Prog α) :
    ∀ (s : Memory.State),
      ((Memory.spec 0).clientState s p).frontier = s.frontier →
      diffCount L ((Memory.spec 0).clientState s p).mem s.mem ≤ memoryCost p s := by
  induction p with
  | pure x =>
    intro s _
    change diffCount L s.mem s.mem ≤ 0
    rw [diffCount_self]
  | liftBind o r ih =>
    intro s hfr
    have hle1 : s.frontier ≤ (Memory.step s o).1.frontier := Memory.frontier_le_step s o
    have hle2 : (Memory.step s o).1.frontier ≤
        ((Memory.spec 0).clientState (Memory.step s o).1 (r (Memory.step s o).2)).frontier :=
      Memory.frontier_le_clientState (Memory.step s o).1 _
    change ((Memory.spec 0).clientState (Memory.step s o).1 (r (Memory.step s o).2)).frontier =
      s.frontier at hfr
    have hfr_step : (Memory.step s o).1.frontier = s.frontier := by omega
    have hfr_rec :
        ((Memory.spec 0).clientState (Memory.step s o).1 (r (Memory.step s o).2)).frontier =
          (Memory.step s o).1.frontier := by omega
    have hstep := diffCount_memoryStep_le hnodup s o hfr_step
    have hrec := ih (Memory.step s o).2 (Memory.step s o).1 hfr_rec
    calc diffCount L ((Memory.spec 0).clientState (Memory.step s o).1 (r (Memory.step s o).2)).mem
          s.mem
        ≤ diffCount L
            ((Memory.spec 0).clientState (Memory.step s o).1 (r (Memory.step s o).2)).mem
            (Memory.step s o).1.mem +
          diffCount L (Memory.step s o).1.mem s.mem :=
          diffCount_triangle L _ (Memory.step s o).1.mem s.mem
      _ ≤ memoryCost (r (Memory.step s o).2) (Memory.step s o).1 +
            Memory.charge s o := Nat.add_le_add hrec hstep
      _ = memoryCost (PFunctor.FreeM.liftBind o r) s := Nat.add_comm _ _

/-! ## Section 2: Functional bit-packing (`packArray`, `packDenseItems`) and update laws -/

/-- Pack `len` entries of `f : ℕ → ℕ` (width `k` bits each) starting at word `base` on a `w`-bit
machine via `BitPackedArray.writePacked`. -/
@[expose] def packArray (base k w : ℕ) (f : ℕ → ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, mem => mem
  | i + 1, mem => writePacked base k w (packArray base k w f i mem) i (f i)

theorem packArray_lt_two_pow {base k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) (f : ℕ → ℕ) :
    ∀ (len : ℕ) {mem : ℕ → ℕ}, (∀ addr, mem addr < 2 ^ w) →
      ∀ addr, packArray base k w f len mem addr < 2 ^ w
  | 0, _, hmem, addr => hmem addr
  | i + 1, _, hmem, addr =>
    writePacked_lt_two_pow hw hkw (packArray_lt_two_pow hw hkw f i hmem) i (f i) addr

theorem packArray_outside {base N k w : ℕ} (hw : 0 < w) (f : ℕ → ℕ) :
    ∀ {len : ℕ}, len ≤ N → ∀ (mem : ℕ → ℕ) {addr : ℕ},
      ¬(base ≤ addr ∧ addr < base + packedWords N k w) →
      packArray base k w f len mem addr = mem addr
  | 0, _, _, _, _ => rfl
  | i + 1, hle, mem, addr, haddr => by
    unfold packArray
    rw [writePacked_outside hw _ (by omega) (f i) haddr,
      packArray_outside hw f (by omega) mem haddr]

theorem readPacked_packArray {base k w : ℕ} (hw : 0 < w) (f : ℕ → ℕ) :
    ∀ (len : ℕ) (mem : ℕ → ℕ) {idx : ℕ}, idx < len → f idx < 2 ^ k →
      readPacked base k w (packArray base k w f len mem) idx = f idx
  | 0, _, _, hidx, _ => by omega
  | i + 1, mem, idx, hidx, hf => by
    unfold packArray
    by_cases heq : idx = i
    · subst heq
      exact readPacked_writePacked_self base k w _ idx hf
    · rw [readPacked_writePacked_of_ne hw _ heq (f i)]
      exact readPacked_packArray hw f i mem (by omega) hf

/-- Pointwise congruence of `writePacked`: the value at `addr` after `writePacked` depends only on
`mem addr` and `(idx, val)`. -/
theorem writePacked_apply_congr (base k w : ℕ) {mem₁ mem₂ : ℕ → ℕ} (idx val addr : ℕ)
    (h : mem₁ addr = mem₂ addr) :
    writePacked base k w mem₁ idx val addr = writePacked base k w mem₂ idx val addr := by
  unfold writePacked
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  by_cases h1 : addr = base + wOff + 1
  · subst h1
    have hne : base + wOff + 1 ≠ base + wOff := by omega
    simp only [Function.update_self, Function.update_of_ne hne, h]
  · rw [Function.update_of_ne h1, Function.update_of_ne h1]
    by_cases h0 : addr = base + wOff
    · subst h0
      simp only [Function.update_self, h]
    · rw [Function.update_of_ne h0, Function.update_of_ne h0, h]

/-- Updating `f` at a single index `idx₀` changes `packArray base k w f len mem` at most at the two
words `base + wordOffset k w idx₀` and `base + wordOffset k w idx₀ + 1`. -/
theorem packArray_update_eq_of_ne (base k w : ℕ) (f : ℕ → ℕ) (idx₀ val : ℕ) :
    ∀ (len : ℕ) (mem : ℕ → ℕ) {addr : ℕ},
      addr ≠ base + wordOffset k w idx₀ →
      addr ≠ base + wordOffset k w idx₀ + 1 →
      packArray base k w (Function.update f idx₀ val) len mem addr =
        packArray base k w f len mem addr
  | 0, _, _, _, _ => rfl
  | i + 1, mem, addr, h0, h1 => by
    unfold packArray
    have ih := packArray_update_eq_of_ne base k w f idx₀ val i mem h0 h1
    by_cases hi : i = idx₀
    · subst hi
      unfold writePacked
      rw [Function.update_of_ne h1, Function.update_of_ne h0,
        Function.update_of_ne h1, Function.update_of_ne h0, ih]
    · rw [Function.update_of_ne hi]
      exact writePacked_apply_congr base k w i (f i) addr ih

theorem diffCount_packArray_update_le {L : List ℕ} (hnodup : L.Nodup) (base k w : ℕ)
    (f g : ℕ → ℕ) (idx₀ val len : ℕ) (mem : ℕ → ℕ) :
    diffCount L (packArray base k w (Function.update f idx₀ val) len mem)
      (packArray base k w g len mem) ≤
      diffCount L (packArray base k w f len mem) (packArray base k w g len mem) + 2 := by
  have hstep : diffCount L (packArray base k w (Function.update f idx₀ val) len mem)
      (packArray base k w f len mem) ≤ 2 :=
    diffCount_of_eq_off_two hnodup (base + wordOffset k w idx₀) (base + wordOffset k w idx₀ + 1)
      fun addr h0 h1 => packArray_update_eq_of_ne base k w f idx₀ val len mem h0 h1
  calc diffCount L (packArray base k w (Function.update f idx₀ val) len mem)
        (packArray base k w g len mem)
      ≤ diffCount L (packArray base k w (Function.update f idx₀ val) len mem)
          (packArray base k w f len mem) +
        diffCount L (packArray base k w f len mem) (packArray base k w g len mem) :=
        diffCount_triangle L _ _ _
    _ ≤ 2 + diffCount L (packArray base k w f len mem) (packArray base k w g len mem) :=
        Nat.add_le_add_right hstep _
    _ = diffCount L (packArray base k w f len mem) (packArray base k w g len mem) + 2 :=
        Nat.add_comm _ _

/-- Pack `m` dense `(quotient, value)` items `(qFn d, vFn d)` (`d < m`) into
`[epochMetaBits U w N, dictBitSize U V w N m)`. -/
@[expose] def packDenseItems (U V w N : ℕ) (qFn vFn : ℕ → ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, mem => mem
  | d + 1, mem =>
      let mem₁ := writeFieldMem w 0 (packDenseItems U V w N qFn vFn d mem)
        (itemQuotBitOff U V w N d) (quotientBits U N) (qFn d)
      writeFieldMem w 0 mem₁ (itemValBitOff U V w N d) (valBits V) (vFn d)

theorem packDenseItems_fits {U V w N : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (qFn vFn : ℕ → ℕ) :
    ∀ (m : ℕ) {mem : ℕ → ℕ}, (∀ addr, Fits w (mem addr)) →
      ∀ addr, Fits w (packDenseItems U V w N qFn vFn m mem addr)
  | 0, _, hmem, addr => hmem addr
  | d + 1, _, hmem, addr => by
    unfold packDenseItems
    have hq_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
    have hv_le : valBits V ≤ w := valBits_le_of_le_pow hV
    exact writeFieldMem_fits hw
      (writeFieldMem_fits hw (packDenseItems_fits hw hU hV qFn vFn d hmem) hq_le (qFn d))
      hv_le (vFn d) addr

theorem packDenseItems_lt_metaWords {U V w N : ℕ} (hw : 0 < w) (qFn vFn : ℕ → ℕ) :
    ∀ (m : ℕ) (mem : ℕ → ℕ) {addr : ℕ}, addr < epochMetaWords U w N →
      packDenseItems U V w N qFn vFn m mem addr = mem addr
  | 0, _, _, _ => rfl
  | d + 1, mem, addr, haddr => by
    unfold packDenseItems
    have hge_q : epochMetaWords U w N ≤ itemQuotBitOff U V w N d / w := by
      have h1 : epochMetaWords U w N * w ≤ itemQuotBitOff U V w N d := by
        unfold itemQuotBitOff itemBitOff epochMetaBits
        omega
      have h2 := Nat.div_le_div_right (c := w) h1
      rwa [Nat.mul_div_cancel _ hw] at h2
    have hge_v : epochMetaWords U w N ≤ itemValBitOff U V w N d / w := by
      have h1 : epochMetaWords U w N * w ≤ itemValBitOff U V w N d := by
        unfold itemValBitOff itemBitOff epochMetaBits
        omega
      have h2 := Nat.div_le_div_right (c := w) h1
      rwa [Nat.mul_div_cancel _ hw] at h2
    rw [writeFieldMem_eq_of_ne w 0 _ _ _ _ addr (by omega) (by omega),
      writeFieldMem_eq_of_ne w 0 _ _ _ _ addr (by omega) (by omega),
      packDenseItems_lt_metaWords hw qFn vFn d mem haddr]

theorem readBit_packDenseItems_outside {U V w N : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (qFn vFn : ℕ → ℕ) :
    ∀ (m : ℕ) (mem : ℕ → ℕ) {i : ℕ},
      (i < epochMetaBits U w N ∨ dictBitSize U V w N m ≤ i) →
      readBit w 0 (packDenseItems U V w N qFn vFn m mem) i = readBit w 0 mem i
  | 0, _, _, _ => rfl
  | d + 1, mem, i, hi => by
    unfold packDenseItems
    have hq_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
    have hv_le : valBits V ≤ w := valBits_le_of_le_pow hV
    have hmul_eq : (d + 1) * (quotientBits U N + valBits V) =
        d * (quotientBits U N + valBits V) + quotientBits U N + valBits V := by ring
    have hnot_v : ¬(itemValBitOff U V w N d ≤ i ∧ i < itemValBitOff U V w N d + valBits V) := by
      unfold dictBitSize itemBits at hi
      unfold itemValBitOff itemBitOff itemBits
      rcases hi with hlt | hge <;> omega
    have hnot_q : ¬(itemQuotBitOff U V w N d ≤ i ∧
        i < itemQuotBitOff U V w N d + quotientBits U N) := by
      unfold dictBitSize itemBits at hi
      unfold itemQuotBitOff itemBitOff itemBits
      rcases hi with hlt | hge <;> omega
    rw [readBit_writeFieldMem hw _ hv_le i, ite_eq_right hnot_v,
      readBit_writeFieldMem hw _ hq_le i, ite_eq_right hnot_q]
    apply readBit_packDenseItems_outside hw hU hV qFn vFn d mem
    rcases hi with hlt | hge
    · exact Or.inl hlt
    · right
      unfold dictBitSize itemBits at hge ⊢
      omega

theorem denseQuotAt_ValAt_packDenseItems {U V w N : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hV : V ≤ 2 ^ w) (qFn vFn : ℕ → ℕ)
    (hq : ∀ d, qFn d < 2 ^ quotientBits U N) (hv : ∀ d, vFn d < 2 ^ valBits V) :
    ∀ (m : ℕ) (mem : ℕ → ℕ) {d : ℕ}, d < m →
      let s : BitMemory.State := ⟨packDenseItems U V w N qFn vFn m mem, dictBitSize U V w N m⟩
      denseQuotAt U V w N s d = qFn d ∧ denseValAt U V w N s d = vFn d
  | 0, _, _, hd => by omega
  | k + 1, mem, d, hd => by
    have hq_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
    have hv_le : valBits V ≤ w := valBits_le_of_le_pow hV
    set m₀ := packDenseItems U V w N qFn vFn k mem
    set m₁ := writeFieldMem w 0 m₀ (itemQuotBitOff U V w N k) (quotientBits U N) (qFn k)
    set m₂ := writeFieldMem w 0 m₁ (itemValBitOff U V w N k) (valBits V) (vFn k)
    by_cases hdk : d = k
    · subst hdk
      refine ⟨?_, ?_⟩
      · change readField w 0 m₂ (itemQuotBitOff U V w N d) (quotientBits U N) = qFn d
        have hcongr : readField w 0 m₂ (itemQuotBitOff U V w N d) (quotientBits U N) =
            readField w 0 m₁ (itemQuotBitOff U V w N d) (quotientBits U N) := by
          apply readField_congr_bits hw hq_le
          intro j hj
          rw [readBit_writeFieldMem hw m₁ hv_le, ite_eq_right]
          unfold itemValBitOff itemQuotBitOff
          omega
        rw [hcongr]
        exact readField_writeFieldMem_same hw m₀ hq_le (hq d)
      · change readField w 0 m₂ (itemValBitOff U V w N d) (valBits V) = vFn d
        exact readField_writeFieldMem_same hw m₁ hv_le (hv d)
    · have hd_lt : d < k := by omega
      have ih := denseQuotAt_ValAt_packDenseItems hw hU hV qFn vFn hq hv k mem hd_lt
      have hle_end : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N k := by
        unfold itemBitOff
        have : (d + 1) * itemBits U V N ≤ k * itemBits U V N := Nat.mul_le_mul_right _ hd_lt
        rw [Nat.add_one_mul] at this
        omega
      refine ⟨?_, ?_⟩
      · change readField w 0 m₂ (itemQuotBitOff U V w N d) (quotientBits U N) = qFn d
        rw [← ih.1]
        apply readField_congr_bits hw hq_le
        intro j hj
        have hnot1 : ¬(itemValBitOff U V w N k ≤ itemQuotBitOff U V w N d + j ∧
            itemQuotBitOff U V w N d + j < itemValBitOff U V w N k + valBits V) := by
          unfold itemBitOff itemBits at hle_end
          unfold itemValBitOff itemQuotBitOff itemBitOff itemBits; omega
        have hnot2 : ¬(itemQuotBitOff U V w N k ≤ itemQuotBitOff U V w N d + j ∧
            itemQuotBitOff U V w N d + j < itemQuotBitOff U V w N k + quotientBits U N) := by
          unfold itemBitOff itemBits at hle_end
          unfold itemQuotBitOff itemBitOff itemBits; omega
        rw [readBit_writeFieldMem hw m₁ hv_le, ite_eq_right hnot1,
          readBit_writeFieldMem hw m₀ hq_le, ite_eq_right hnot2]
      · change readField w 0 m₂ (itemValBitOff U V w N d) (valBits V) = vFn d
        rw [← ih.2]
        apply readField_congr_bits hw hv_le
        intro j hj
        have hnot1 : ¬(itemValBitOff U V w N k ≤ itemValBitOff U V w N d + j ∧
            itemValBitOff U V w N d + j < itemValBitOff U V w N k + valBits V) := by
          unfold itemBitOff itemBits at hle_end
          unfold itemValBitOff itemBitOff itemBits; omega
        have hnot2 : ¬(itemQuotBitOff U V w N k ≤ itemValBitOff U V w N d + j ∧
            itemValBitOff U V w N d + j < itemQuotBitOff U V w N k + quotientBits U N) := by
          unfold itemBitOff itemBits at hle_end
          unfold itemValBitOff itemQuotBitOff itemBitOff itemBits; omega
        rw [readBit_writeFieldMem hw m₁ hv_le, ite_eq_right hnot1,
          readBit_writeFieldMem hw m₀ hq_le, ite_eq_right hnot2]

/-! ## Section 3: Canonical hash memory (`canonHashMem`) and `buildBitState` -/

/-- Canonical Four-Russians carryless multiplication table memory at `offHash = 4` for `(U, w, N)`.
Uses `ReducedKWise.initTableCode_execWithin` when parameters fit in `w` bits. -/
@[expose] noncomputable def canonTableMem (U w N : ℕ) : ℕ → ℕ :=
  let w₀ := Succinct.qBits U N
  let b := Succinct.hashB N
  let b' := totalMicroBits N
  let t := reducedTrinomialStep w₀ b b'
  let x₀ : WordRAM.Data 240 := ⟨fun _ => offHash, fun _ => 0⟩
  open scoped Classical in
  if h : 2 * reducedChunkBits t ≤ w ∧ Fits w (offHash + Succinct.hashSpace U w N) then
    (Classical.choose
      (ReducedKWise.initTableCode_execWithin (x := x₀) (base := offHash)
        (w := w) (w₀ := w₀) (b := b) (b' := b') (k := 3) rfl h.1 h.2)).mem
  else fun _ => 0

/-- Canonical hash region memory `[offHash, offLM U w N)` representing seed `θ` and the
Four-Russians table at `offHash = 4`. -/
@[expose] noncomputable def canonHashMem (U w N : ℕ) (θ : Succinct.QuotHashSeed U N) (a : ℕ) : ℕ :=
  let w₀ := Succinct.qBits U N
  let b := Succinct.hashB N
  let b' := totalMicroBits N
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  if a = offHash then
    θ.1.val % 2 ^ w
  else if h_seed : offHash + 1 ≤ a ∧ a < offHash + 1 + 3 * L then
    let idx := a - (offHash + 1)
    have hj : idx / L < 3 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    let j : Fin 3 := ⟨idx / L, hj⟩
    getLimb c (θ.2 j).val (idx % L) % 2 ^ w
  else
    canonTableMem U w N a % 2 ^ w

theorem canonHashMem_fits (U w N : ℕ) (θ : Succinct.QuotHashSeed U N) (a : ℕ) :
    Fits w (canonHashMem U w N θ a) := by
  unfold canonHashMem Fits
  dsimp only
  split_ifs <;> exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem canonHashMem_rep {U w N : ℕ} (hN : N ≤ U) (hU : U ≤ 2 ^ w)
    (hfit : Fits w (offHash + Succinct.hashSpace U w N))
    (θ : Succinct.QuotHashSeed U N) :
    ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ (canonHashMem U w N θ) := by
  let w₀ := Succinct.qBits U N
  let b := Succinct.hashB N
  let b' := totalMicroBits N
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  have hw2 : 2 ≤ w := by
    have h8 := Succinct.eight_le_hashSpace U w N
    have hlt : 8 < 2 ^ w := lt_of_le_of_lt (by omega) hfit
    by_contra h
    have hw1 : w ≤ 1 := by omega
    have hpow : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right Nat.two_pos hw1
    omega
  have hw₀_le : w₀ ≤ w := Succinct.qBits_le_of_le_pow (by omega) hU
  have hc_le : 2 * c ≤ w := Succinct.two_mul_reducedChunkBits_hash_le hw2 hN hU
  have hcond : 2 * reducedChunkBits t ≤ w ∧ Fits w (offHash + Succinct.hashSpace U w N) :=
    ⟨hc_le, hfit⟩
  let x₀ : WordRAM.Data 240 := ⟨fun _ => offHash, fun _ => 0⟩
  have hspec := Classical.choose_spec
    (ReducedKWise.initTableCode_execWithin (x := x₀) (base := offHash)
      (w := w) (w₀ := w₀) (b := b) (b' := b') (k := 3) rfl hc_le hfit)
  have hx₀_bdd : x₀.Bounded w := by
    refine ⟨fun _ => hfit.of_le (Nat.le_add_right _ _), fun _ => Nat.two_pow_pos w⟩
  have hy_bdd := hspec.1.bounded hx₀_bdd
  have htab_mem : ∀ addr, canonTableMem U w N addr % 2 ^ w =
      (Classical.choose
        (ReducedKWise.initTableCode_execWithin (x := x₀) (base := offHash)
          (w := w) (w₀ := w₀) (b := b) (b' := b') (k := 3) rfl hc_le hfit)).mem addr := by
    intro addr; unfold canonTableMem; dsimp only
    rw [dite_eq_left hcond, Nat.mod_eq_of_lt (hy_bdd.2 addr)]
  have htab_orig := hspec.2.2.1
  refine ⟨?_, ?_⟩
  · have htab_addr : ∀ wIdx,
        canonHashMem U w N θ (ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx) =
          (Classical.choose
            (ReducedKWise.initTableCode_execWithin (x := x₀) (base := offHash)
              (w := w) (w₀ := w₀) (b := b) (b' := b') (k := 3) rfl hc_le hfit)).mem
            (ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx) := by
      intro wIdx
      have hge : offHash + 1 + 3 * L ≤ ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx := by
        unfold ReducedKWise.tabBase ReducedKWise.seedWords; dsimp only [L, t]; omega
      unfold canonHashMem; dsimp only
      have hne0 : ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx ≠ offHash := by
        have := ReducedKWise.seedWords_pos w₀ b b' 3; unfold ReducedKWise.tabBase; omega
      have hnot_seed : ¬(offHash + 1 ≤ ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx ∧
          ReducedKWise.tabBase offHash w₀ b b' 3 + wIdx < offHash + 1 + 3 * L) := by omega
      rw [ite_eq_right hne0, dite_eq_right hnot_seed]; exact htab_mem _
    refine ⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩
    · rw [htab_addr]; exact htab_orig.1 wIdx hwIdx
    · rw [htab_addr]; exact htab_orig.2 idx hidx
  · refine ⟨?_, fun j m => ?_⟩
    · unfold canonHashMem; dsimp only; rw [ite_eq_left rfl]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le θ.1.isLt (Nat.pow_le_pow_right Nat.two_pos (by omega)))
    · unfold canonHashMem; dsimp only
      have hne0 : offHash + 1 + (m.val + L * j.val) ≠ offHash := by omega
      have hlt_3L : m.val + L * j.val < 3 * L := by
        calc m.val + L * j.val < L + L * j.val := Nat.add_lt_add_right m.isLt _
          _ = L * (j.val + 1) := by ring
          _ ≤ L * 3 := Nat.mul_le_mul_left L j.isLt
          _ = 3 * L := Nat.mul_comm L 3
      have hseed : offHash + 1 ≤ offHash + 1 + (m.val + L * j.val) ∧
          offHash + 1 + (m.val + L * j.val) < offHash + 1 + 3 * L := ⟨by omega, by omega⟩
      rw [ite_eq_right hne0, dite_eq_left hseed]
      have hL_pos : 0 < L := reducedLimbCount_pos t
      have hsub : offHash + 1 + (m.val + L * j.val) - (offHash + 1) = L * j.val + m.val := by omega
      have hdiv : (L * j.val + m.val) / L = j.val := by
        rw [Nat.mul_add_div hL_pos, Nat.div_eq_of_lt m.isLt, Nat.add_zero]
      have hmod : (L * j.val + m.val) % L = m.val := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt m.isLt]
      have hj_eq : ∀ hlt, (⟨(offHash + 1 + (m.val + L * j.val) - (offHash + 1)) / L, hlt⟩ : Fin 3) =
          j := fun _ => Fin.ext (by dsimp only; rw [hsub, hdiv])
      have hm_eq : (offHash + 1 + (m.val + L * j.val) - (offHash + 1)) % L = m.val := by
        rw [hsub, hmod]
      rw [hj_eq, hm_eq]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (getLimb_lt c (θ.2 j).val m.val)
        (Nat.pow_le_pow_right Nat.two_pos (by omega)))

/-- Base metadata word memory on `[0, offTD U w N)` before packing `TailDense` and `DenseTail`:
stores the 4-word header at `0 .. 3`, `canonHashMem` at `[offHash, offLM U w N)` when `0 < N`,
and copies `LocalMeta ++ GlobalMeta` from `fixMem` at `[offLM U w N, offTD U w N)` when `0 < N`. -/
@[expose] noncomputable def baseMetaMem (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (fixMem : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a = 0 then m % 2 ^ w
  else if a = 1 then N % 2 ^ w
  else if a = 2 then itemBits U V N % 2 ^ w
  else if a = 3 then epochMetaBits U w N % 2 ^ w
  else if N = 0 then 0
  else if a < offLM U w N then canonHashMem U w N θ a
  else if a < offTD U w N then
    fixMem (a - offLM U w N + Succinct.offLM U V w N (Succinct.hashSpace U w N)) % 2 ^ w
  else 0

theorem baseMetaMem_fits (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (fixMem : ℕ → ℕ) (a : ℕ) :
    Fits w (baseMetaMem U V w N m θ fixMem a) := by
  unfold baseMetaMem Fits
  split_ifs <;>
    first | exact Nat.mod_lt _ (Nat.two_pow_pos w) | exact Nat.two_pow_pos w |
      exact canonHashMem_fits U w N θ a

/-- Full epoch metadata word memory on `[0, epochMetaWords U w N)`: when `N = 0`, equals
`baseMetaMem`; when `0 < N`, packs `td` into `[offTD U w N, offDT U w N)` and `dt` into
`[offDT U w N, epochMetaWords U w N)` on top of `baseMetaMem`. -/
@[expose] noncomputable def epochMetaMem (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (fixMem td dt : ℕ → ℕ) : ℕ → ℕ :=
  let m₀ := baseMetaMem U V w N m θ fixMem
  if N = 0 then m₀
  else
    let m₁ := packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N) m₀
    packArray (offDT U w N) (globalPtrBits N) w dt (maxTailItems N) m₁

theorem epochMetaMem_fits {U V w N m : ℕ} (hw : 0 < w) (hfit_N : Fits w N)
    (θ : Succinct.QuotHashSeed U N) (fixMem td dt : ℕ → ℕ) (a : ℕ) :
    Fits w (epochMetaMem U V w N m θ fixMem td dt a) := by
  have hptr_le : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow le_rfl hfit_N
  unfold epochMetaMem; dsimp only
  split_ifs with hN0
  · exact baseMetaMem_fits U V w N m θ fixMem a
  · exact packArray_lt_two_pow hw hptr_le dt (maxTailItems N)
      (packArray_lt_two_pow hw hptr_le td (maxTailItems N)
        (baseMetaMem_fits U V w N m θ fixMem)) a

theorem epochMetaMem_lt_offTD {U V w N m : ℕ} (hw : 0 < w) (θ : Succinct.QuotHashSeed U N)
    (fixMem td dt : ℕ → ℕ) {a : ℕ} (ha : a < offTD U w N) :
    epochMetaMem U V w N m θ fixMem td dt a = baseMetaMem U V w N m θ fixMem a := by
  unfold epochMetaMem; dsimp only
  split_ifs with hN0
  · rfl
  · have ha_dt : ¬(offDT U w N ≤ a ∧ a < offDT U w N +
        packedWords (maxTailItems N) (globalPtrBits N) w) := by unfold offDT; omega
    have ha_td : ¬(offTD U w N ≤ a ∧ a < offTD U w N +
        packedWords (maxTailItems N) (globalPtrBits N) w) := by omega
    rw [packArray_outside hw dt le_rfl _ ha_dt, packArray_outside hw td le_rfl _ ha_td]

theorem epochMetaMem_ge_metaWords {U V w N m : ℕ} (hw : 0 < w) (θ : Succinct.QuotHashSeed U N)
    (fixMem td dt : ℕ → ℕ) {a : ℕ} (ha : epochMetaWords U w N ≤ a) :
    epochMetaMem U V w N m θ fixMem td dt a = 0 := by
  unfold epochMetaMem; dsimp only
  split_ifs with hN0
  · subst hN0; unfold epochMetaWords at ha; simp only [↓reduceIte] at ha
    unfold baseMetaMem
    have h0 : a ≠ 0 := by omega
    have h1 : a ≠ 1 := by omega
    have h2 : a ≠ 2 := by omega
    have h3 : a ≠ 3 := by omega
    simp [h0, h1, h2, h3]
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
    have heq_meta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN_pos
    have ha_dt : ¬(offDT U w N ≤ a ∧ a < offDT U w N +
        packedWords (maxTailItems N) (globalPtrBits N) w) := by omega
    have ha_td : ¬(offTD U w N ≤ a ∧ a < offTD U w N +
        packedWords (maxTailItems N) (globalPtrBits N) w) := by unfold offDT at heq_meta; omega
    have ha_base : ¬a < offTD U w N := by unfold offDT at heq_meta; omega
    have ha_lm : ¬a < offLM U w N := by unfold offDT offTD offGM at heq_meta; omega
    rw [packArray_outside hw dt le_rfl _ ha_dt, packArray_outside hw td le_rfl _ ha_td]
    unfold baseMetaMem
    have h0 : a ≠ 0 := by unfold offDT offTD offGM offLM offHash at heq_meta; omega
    have h1 : a ≠ 1 := by unfold offDT offTD offGM offLM offHash at heq_meta; omega
    have h2 : a ≠ 2 := by unfold offDT offTD offGM offLM offHash at heq_meta; omega
    have h3 : a ≠ 3 := by unfold offDT offTD offGM offLM offHash at heq_meta; omega
    simp [h0, h1, h2, h3, hN0, ha_lm, ha_base]

/-- On `[offTD U w N, epochMetaWords U w N)` when `0 < N`, `epochMetaMem` depends only on `td` and
`dt` (starting from the all-zero memory `fun _ => 0`), and is independent of `m`, `θ`, and
`fixMem`. -/
theorem epochMetaMem_eq_pack_zero_of_ge_offTD {U V w N m : ℕ} (hN : 0 < N)
    (θ : Succinct.QuotHashSeed U N) (fixMem td dt : ℕ → ℕ) :
    let zMem : ℕ → ℕ := fun _ => 0
    ∀ {a : ℕ}, offTD U w N ≤ a →
      epochMetaMem U V w N m θ fixMem td dt a =
        packArray (offDT U w N) (globalPtrBits N) w dt (maxTailItems N)
          (packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N) zMem) a := by
  intro zMem a ha
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  unfold epochMetaMem
  dsimp only
  rw [ite_eq_right hN0]
  have h1 : ∀ len {addr : ℕ}, offTD U w N ≤ addr →
      packArray (offTD U w N) (globalPtrBits N) w td len (baseMetaMem U V w N m θ fixMem) addr =
        packArray (offTD U w N) (globalPtrBits N) w td len zMem addr := by
    intro len
    induction len with
    | zero =>
      intro addr haddr
      unfold packArray baseMetaMem
      have h0 : addr ≠ 0 := by unfold offTD offGM offLM offHash at haddr; omega
      have h1 : addr ≠ 1 := by unfold offTD offGM offLM offHash at haddr; omega
      have h2 : addr ≠ 2 := by unfold offTD offGM offLM offHash at haddr; omega
      have h3 : addr ≠ 3 := by unfold offTD offGM offLM offHash at haddr; omega
      have h4 : ¬addr < offLM U w N := by unfold offTD offGM at haddr; omega
      have h5 : ¬addr < offTD U w N := by omega
      simp [h0, h1, h2, h3, hN0, h4, h5, zMem]
    | succ i ih =>
      intro addr haddr
      unfold packArray
      exact writePacked_apply_congr _ _ _ i (td i) addr (ih haddr)
  have h2 : ∀ len {addr : ℕ}, offTD U w N ≤ addr →
      packArray (offDT U w N) (globalPtrBits N) w dt len
        (packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N)
          (baseMetaMem U V w N m θ fixMem)) addr =
      packArray (offDT U w N) (globalPtrBits N) w dt len
        (packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N) zMem) addr := by
    intro len
    induction len with
    | zero =>
      intro addr haddr
      exact h1 (maxTailItems N) haddr
    | succ i ih =>
      intro addr haddr
      unfold packArray
      exact writePacked_apply_congr _ _ _ i (dt i) addr (ih haddr)
  exact h2 (maxTailItems N) ha

/-- Build the canonical single-tape `BitMemory.State` from a fixed-capacity state `s_fix`,
key count `m`, epoch capacity `N`, hash seed `θ`, and circular compaction arrays `(td, dt)`. -/
@[expose] noncomputable def buildBitState (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_fix : Memory.State) (td dt : ℕ → ℕ) : BitMemory.State :=
  let h_space := Succinct.hashSpace U w N
  let gm := Succinct.gmAt 0 U V w N h_space s_fix.mem
  let qFn (d : ℕ) : ℕ := Succinct.quotAt 0 U w N h_space s_fix.mem (physOfDense N gm dt d)
  let vFn (d : ℕ) : ℕ := Succinct.valAt 0 U V w N h_space s_fix.mem (physOfDense N gm dt d)
  let m_meta := epochMetaMem U V w N m θ s_fix.mem td dt
  ⟨packDenseItems U V w N qFn vFn m m_meta, dictBitSize U V w N m⟩

@[simp]
theorem buildBitState_bitSize (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_fix : Memory.State) (td dt : ℕ → ℕ) :
    (buildBitState U V w N m θ s_fix td dt).bitSize = dictBitSize U V w N m :=
  rfl

theorem buildBitState_mem_lt_metaWords {U V w N m : ℕ} (hw : 0 < w)
    (θ : Succinct.QuotHashSeed U N) (s_fix : Memory.State) (td dt : ℕ → ℕ)
    {a : ℕ} (ha : a < epochMetaWords U w N) :
    (buildBitState U V w N m θ s_fix td dt).mem a =
      epochMetaMem U V w N m θ s_fix.mem td dt a :=
  packDenseItems_lt_metaWords hw _ _ m _ ha

theorem buildBitState_wellFormed {U V w N m : ℕ} (hw : 0 < w) (hfit_N : Fits w N)
    (hfit_sz : Fits w (dictBitSize U V w N m))
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) (θ : Succinct.QuotHashSeed U N)
    (s_fix : Memory.State) (td dt : ℕ → ℕ) :
    (buildBitState U V w N m θ s_fix td dt).WellFormed w := by
  refine ⟨?_, hfit_sz, ?_⟩
  · exact packDenseItems_fits hw hU hV _ _ m (epochMetaMem_fits hw hfit_N θ s_fix.mem td dt)
  · intro i hi
    change readBit w 0 (buildBitState U V w N m θ s_fix td dt).mem i = false
    unfold buildBitState
    rw [readBit_packDenseItems_outside hw hU hV _ _ m _ (Or.inr hi)]
    unfold readBit
    rw [Nat.zero_add]
    have ha : epochMetaWords U w N ≤ i / w := by
      rw [buildBitState_bitSize] at hi
      have h1 : epochMetaWords U w N * w ≤ i := by
        unfold dictBitSize epochMetaBits at hi
        omega
      have h2 := Nat.div_le_div_right (c := w) h1
      rwa [Nat.mul_div_cancel _ hw] at h2
    rw [epochMetaMem_ge_metaWords hw θ s_fix.mem td dt ha]
    exact Nat.zero_testBit (i % w)

theorem buildBitState_denseQuotAt_ValAt {U V w N m : ℕ} (hw : 0 < w)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) (θ : Succinct.QuotHashSeed U N)
    (s_fix : Memory.State) (td dt : ℕ → ℕ) {d : ℕ} (hd : d < m) :
    let h_space := Succinct.hashSpace U w N
    let gm := Succinct.gmAt 0 U V w N h_space s_fix.mem
    let s_bit := buildBitState U V w N m θ s_fix td dt
    denseQuotAt U V w N s_bit d =
      Succinct.quotAt 0 U w N h_space s_fix.mem (physOfDense N gm dt d) ∧
    denseValAt U V w N s_bit d =
      Succinct.valAt 0 U V w N h_space s_fix.mem (physOfDense N gm dt d) := by
  have hq : ∀ i, Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
      (physOfDense N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) dt i) <
      2 ^ quotientBits U N :=
    fun i => Succinct.quotAt_lt 0 U w N (Succinct.hashSpace U w N) s_fix.mem _
  have hv : ∀ i, Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
      (physOfDense N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) dt i) <
      2 ^ valBits V :=
    fun i => Succinct.valAt_lt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem _
  exact denseQuotAt_ValAt_packDenseItems hw hU hV _ _ hq hv m _ hd

private theorem shiftRight_and_mod_two_pow {x bOff len w : ℕ} (hle : bOff + len ≤ w) :
    ((x % 2 ^ w) >>> bOff) &&& (2 ^ len - 1) = (x >>> bOff) &&& (2 ^ len - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < len
  · have hbw : bOff + i < w := by omega
    simp [hi, hbw]
  · simp [hi]

theorem buildBitState_lmAtBit_gmAtBit {U V w N m : ℕ} (hw : 0 < w) (hN : 0 < N)
    (hNU : N ≤ U) (hU : U < 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) (s_fix : Memory.State) (td dt : ℕ → ℕ) :
    let s_bit := buildBitState U V w N m θ s_fix td dt
    lmAtBit U w N s_bit.mem =
      Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem ∧
    gmAtBit U w N s_bit.mem =
      Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem := by
  intro s_bit
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have heq_meta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN
  have hcopy : ∀ k < 9 * Succinct.lmSubWords N w +
      packedWords (globalMetaLen N) (globalPtrBits N) w,
      s_bit.mem (offLM U w N + k) =
        s_fix.mem (Succinct.offLM U V w N (Succinct.hashSpace U w N) + k) % 2 ^ w := by
    intro k hk
    have ha_td : offLM U w N + k < offTD U w N := by
      unfold offTD offGM
      omega
    have ha_meta : offLM U w N + k < epochMetaWords U w N := by
      unfold offDT at heq_meta
      omega
    rw [buildBitState_mem_lt_metaWords hw θ s_fix td dt ha_meta,
      epochMetaMem_lt_offTD hw θ s_fix.mem td dt ha_td]
    unfold baseMetaMem
    have h0 : offLM U w N + k ≠ 0 := by unfold offLM offHash; omega
    have h1 : offLM U w N + k ≠ 1 := by unfold offLM offHash; omega
    have h2 : offLM U w N + k ≠ 2 := by unfold offLM offHash; omega
    have h3 : offLM U w N + k ≠ 3 := by unfold offLM offHash; omega
    have h4 : ¬offLM U w N + k < offLM U w N := by omega
    simp only [h0, h1, h2, h3, hN0, h4, ha_td, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [Nat.add_comm _ (Succinct.offLM U V w N (Succinct.hashSpace U w N))]
  refine ⟨?_, ?_⟩
  · funext p
    unfold lmAtBit Succinct.lmAt
    split_ifs with hp
    · rcases hp with ⟨hc, hidx⟩
      unfold readPacked
      have hkw : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hNU hU
      have hlo_le : bitOffset (effBucketPosBits N) w p.2 + lowWidth (effBucketPosBits N) w p.2 ≤
          w := bitOffset_add_lowWidth_le hw
      have hhi_le : 0 + highWidth (effBucketPosBits N) w p.2 ≤ w := by
        have := lowWidth_add_highWidth (effBucketPosBits N) w p.2
        omega
      have hw1 : wordOffset (effBucketPosBits N) w p.2 + 1 < Succinct.lmSubWords N w :=
        wordOffset_add_one_lt_packedWords hw hidx
      have hmul : (p.1 + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.add_one_mul] at hmul
      have hk0 : p.1 * Succinct.lmSubWords N w + wordOffset (effBucketPosBits N) w p.2 <
          9 * Succinct.lmSubWords N w + packedWords (globalMetaLen N) (globalPtrBits N) w := by
        omega
      have hk1 : p.1 * Succinct.lmSubWords N w + (wordOffset (effBucketPosBits N) w p.2 + 1) <
          9 * Succinct.lmSubWords N w + packedWords (globalMetaLen N) (globalPtrBits N) w := by
        omega
      have ha0 : offLMSub U w N p.1 + wordOffset (effBucketPosBits N) w p.2 =
          offLM U w N + (p.1 * Succinct.lmSubWords N w +
            wordOffset (effBucketPosBits N) w p.2) := by
        unfold offLMSub; omega
      have hb0 : 0 + Succinct.offLMSub U V w N (Succinct.hashSpace U w N) p.1 +
          wordOffset (effBucketPosBits N) w p.2 =
          Succinct.offLM U V w N (Succinct.hashSpace U w N) +
          (p.1 * Succinct.lmSubWords N w + wordOffset (effBucketPosBits N) w p.2) := by
        unfold Succinct.offLMSub; omega
      have ha1 : offLMSub U w N p.1 + wordOffset (effBucketPosBits N) w p.2 + 1 =
          offLM U w N +
          (p.1 * Succinct.lmSubWords N w + (wordOffset (effBucketPosBits N) w p.2 + 1)) := by
        unfold offLMSub; omega
      have hb1 : 0 + Succinct.offLMSub U V w N (Succinct.hashSpace U w N) p.1 +
          wordOffset (effBucketPosBits N) w p.2 + 1 =
          Succinct.offLM U V w N (Succinct.hashSpace U w N) +
          (p.1 * Succinct.lmSubWords N w + (wordOffset (effBucketPosBits N) w p.2 + 1)) := by
        unfold Succinct.offLMSub; omega
      dsimp only
      rw [ha1, hb1, ha0, hb0, hcopy _ hk0, hcopy _ hk1,
        shiftRight_and_mod_two_pow hlo_le, shiftRight_and_mod_two_pow hhi_le]
    · rfl
  · funext idx
    unfold gmAtBit Succinct.gmAt
    split_ifs with hidx
    · unfold readPacked
      have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hNU hU
      have hlo_le : bitOffset (globalPtrBits N) w idx + lowWidth (globalPtrBits N) w idx ≤ w :=
        bitOffset_add_lowWidth_le hw
      have hhi_le : 0 + highWidth (globalPtrBits N) w idx ≤ w := by
        have := lowWidth_add_highWidth (globalPtrBits N) w idx
        omega
      have hw1 : wordOffset (globalPtrBits N) w idx + 1 <
          packedWords (globalMetaLen N) (globalPtrBits N) w :=
        wordOffset_add_one_lt_packedWords hw hidx
      have hk0 : 9 * Succinct.lmSubWords N w + wordOffset (globalPtrBits N) w idx <
          9 * Succinct.lmSubWords N w + packedWords (globalMetaLen N) (globalPtrBits N) w := by
        omega
      have hk1 : 9 * Succinct.lmSubWords N w + (wordOffset (globalPtrBits N) w idx + 1) <
          9 * Succinct.lmSubWords N w + packedWords (globalMetaLen N) (globalPtrBits N) w := by
        omega
      have ha0 : offGM U w N + wordOffset (globalPtrBits N) w idx =
          offLM U w N + (9 * Succinct.lmSubWords N w + wordOffset (globalPtrBits N) w idx) := by
        unfold offGM; omega
      have hb0 : 0 + Succinct.offGM U V w N (Succinct.hashSpace U w N) +
          wordOffset (globalPtrBits N) w idx =
          Succinct.offLM U V w N (Succinct.hashSpace U w N) +
          (9 * Succinct.lmSubWords N w + wordOffset (globalPtrBits N) w idx) := by
        unfold Succinct.offGM; omega
      have ha1 : offGM U w N + wordOffset (globalPtrBits N) w idx + 1 =
          offLM U w N +
          (9 * Succinct.lmSubWords N w + (wordOffset (globalPtrBits N) w idx + 1)) := by
        unfold offGM; omega
      have hb1 : 0 + Succinct.offGM U V w N (Succinct.hashSpace U w N) +
          wordOffset (globalPtrBits N) w idx + 1 =
          Succinct.offLM U V w N (Succinct.hashSpace U w N) +
          (9 * Succinct.lmSubWords N w + (wordOffset (globalPtrBits N) w idx + 1)) := by
        unfold Succinct.offGM; omega
      dsimp only
      rw [ha1, hb1, ha0, hb0, hcopy _ hk0, hcopy _ hk1,
        shiftRight_and_mod_two_pow hlo_le, shiftRight_and_mod_two_pow hhi_le]
    · rfl

theorem buildBitState_tdAtBit_dtAtBit {U V w N m : ℕ} (hw : 0 < w) (hN : 0 < N)
    (θ : Succinct.QuotHashSeed U N) (s_fix : Memory.State) (td dt : ℕ → ℕ)
    (htd_lt : ∀ t < maxTailItems N, td t < 2 ^ globalPtrBits N)
    (hdt_lt : ∀ c < maxTailItems N, dt c < 2 ^ globalPtrBits N) :
    let s_bit := buildBitState U V w N m θ s_fix td dt
    (∀ t < maxTailItems N, tdAtBit U w N s_bit.mem t = td t) ∧
    (∀ c < maxTailItems N, dtAtBit U w N s_bit.mem c = dt c) := by
  intro s_bit
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have heq_meta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN
  have hmeta : ∀ a < epochMetaWords U w N,
      s_bit.mem a = epochMetaMem U V w N m θ s_fix.mem td dt a :=
    fun a ha => buildBitState_mem_lt_metaWords hw θ s_fix td dt ha
  refine ⟨fun t ht => ?_, fun c hc => ?_⟩
  · unfold tdAtBit
    rw [ite_eq_left ht]
    have hcongr : readPacked (offTD U w N) (globalPtrBits N) w s_bit.mem t =
        readPacked (offTD U w N) (globalPtrBits N) w
          (packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N)
            (baseMetaMem U V w N m θ s_fix.mem)) t := by
      apply readPacked_congr hw (N := maxTailItems N) _ ht
      intro addr haddr
      have hlt_meta : addr < epochMetaWords U w N := by
        unfold offDT at heq_meta
        omega
      have hnot_dt : ¬(offDT U w N ≤ addr ∧ addr < offDT U w N +
          packedWords (maxTailItems N) (globalPtrBits N) w) := by
        unfold offDT
        omega
      rw [hmeta addr hlt_meta]
      unfold epochMetaMem
      dsimp only
      rw [ite_eq_right hN0]
      exact packArray_outside hw dt le_rfl _ hnot_dt
    rw [hcongr]
    exact readPacked_packArray hw td (maxTailItems N) _ ht (htd_lt t ht)
  · unfold dtAtBit
    rw [ite_eq_left hc]
    have hcongr : readPacked (offDT U w N) (globalPtrBits N) w s_bit.mem c =
        readPacked (offDT U w N) (globalPtrBits N) w
          (packArray (offDT U w N) (globalPtrBits N) w dt (maxTailItems N)
            (packArray (offTD U w N) (globalPtrBits N) w td (maxTailItems N)
              (baseMetaMem U V w N m θ s_fix.mem))) c := by
      apply readPacked_congr hw (N := maxTailItems N) _ hc
      intro addr haddr
      have hlt_meta : addr < epochMetaWords U w N := by omega
      rw [hmeta addr hlt_meta]
      unfold epochMetaMem
      dsimp only
      rw [ite_eq_right hN0]
    rw [hcongr]
    exact readPacked_packArray hw dt (maxTailItems N) _ hc (hdt_lt c hc)

theorem tailDenseInv_congr {N n_slabs n_tails : ℕ} {td₁ dt₁ td₂ dt₂ : ℕ → ℕ}
    (htd : TailDenseInv N n_slabs n_tails td₁ dt₁)
    (h1 : ∀ t < maxTailItems N, td₂ t = td₁ t)
    (h2 : ∀ c < maxTailItems N, dt₂ c = dt₁ c)
    (hn : n_tails ≤ maxTailItems N) :
    TailDenseInv N n_slabs n_tails td₂ dt₂ where
  td_lt t ht := by rw [h1 t (lt_of_lt_of_le ht hn)]; exact htd.td_lt t ht
  dense_lt t ht := by rw [h1 t (lt_of_lt_of_le ht hn)]; exact htd.dense_lt t ht
  dt_td t ht := by
    have htM : t < maxTailItems N := lt_of_lt_of_le ht hn
    rw [h1 t htM, h2 (td₁ t) (htd.td_lt t ht)]
    exact htd.dt_td t ht
  owner_valid d hlo hhi := by
    have hM : 0 < maxTailItems N := by omega
    have hc : d % maxTailItems N < maxTailItems N := Nat.mod_lt d hM
    have hown := htd.owner_valid d hlo hhi
    rw [h2 (d % maxTailItems N) hc]
    refine ⟨hown.1, ?_⟩
    rw [h1 _ (lt_of_lt_of_le hown.1 hn)]
    exact hown.2

/-- **Main companion bridge theorem (`rep_buildBitState`):**
whenever `s_fix` satisfies `Succinct.DictStateInv U V w N 0 θ s_abs s_fix` (when `0 < N`) and
`(td, dt)` satisfies `TailDenseInv`, `buildBitState` satisfies `Rep U V w N θ s_abs`. -/
theorem rep_buildBitState {U V w N : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U}
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card)
    (hval : Dynamic.ValuesBounded V s_abs)
    (s_fix : Memory.State) (td dt : ℕ → ℕ)
    (hfits_hdr : Fits w (Dynamic.dom s_abs).card ∧ Fits w N ∧
      Fits w (itemBits U V N) ∧ Fits w (epochMetaBits U w N) ∧
      Fits w (dictBitSize U V w N (Dynamic.dom s_abs).card))
    (hact : 0 < N →
      let h_space := Succinct.hashSpace U w N
      let gm := Succinct.gmAt 0 U V w N h_space s_fix.mem
      Fits w (offHash + h_space) ∧
      Succinct.DictStateInv U V w N 0 θ s_abs s_fix ∧
      gm 1 ≤ maxTailItems N ∧
      TailDenseInv N (gm 0) (gm 1) td dt ∧
      (∀ t < maxTailItems N, td t < 2 ^ globalPtrBits N) ∧
      (∀ c < maxTailItems N, dt c < 2 ^ globalPtrBits N)) :
    Rep U V w N θ s_abs (buildBitState U V w N (Dynamic.dom s_abs).card θ s_fix td dt) := by
  let m := (Dynamic.dom s_abs).card
  let s_bit := buildBitState U V w N m θ s_fix td dt
  have hN_le_U : N ≤ U := by
    rcases hepoch with ⟨_, rfl⟩ | ⟨_, _, _, hNU⟩
    · exact Nat.zero_le U
    · exact hNU
  have hmeta_lt : ∀ a < 4, a < epochMetaWords U w N ∧ a < offTD U w N := by
    intro a ha
    refine ⟨?_, by unfold offTD offGM offLM offHash; omega⟩
    unfold epochMetaWords
    split_ifs <;> omega
  have hhdr : ∀ a < 4, s_bit.mem a = baseMetaMem U V w N m θ s_fix.mem a := by
    intro a ha
    rw [buildBitState_mem_lt_metaWords hw θ s_fix td dt (hmeta_lt a ha).1,
      epochMetaMem_lt_offTD hw θ s_fix.mem td dt (hmeta_lt a ha).2]
  refine ⟨buildBitState_wellFormed hw hfits_hdr.2.1 hfits_hdr.2.2.2.2 hU.le hV θ s_fix td dt,
    rfl, hepoch, hval, ?_, ?_, ?_, ?_, fun hN_pos => ?_⟩
  · rw [hhdr 0 (by decide)]; unfold baseMetaMem; dsimp only [m]
    simp [Nat.mod_eq_of_lt hfits_hdr.1]
  · rw [hhdr 1 (by decide)]; unfold baseMetaMem; simp [Nat.mod_eq_of_lt hfits_hdr.2.1]
  · rw [hhdr 2 (by decide)]; unfold baseMetaMem; simp [Nat.mod_eq_of_lt hfits_hdr.2.2.1]
  · rw [hhdr 3 (by decide)]; unfold baseMetaMem; simp [Nat.mod_eq_of_lt hfits_hdr.2.2.2.1]
  · obtain ⟨hfit_hash, hdict, hntails_le, htd, htd_lt, hdt_lt⟩ := hact hN_pos
    obtain ⟨hlm, hgm⟩ := buildBitState_lmAtBit_gmAtBit hw hN_pos hN_le_U hU θ s_fix td dt
    obtain ⟨htd_eq, hdt_eq⟩ := buildBitState_tdAtBit_dtAtBit hw hN_pos θ s_fix td dt htd_lt hdt_lt
    have heq_meta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN_pos
    -- Hash rep at offHash
    have hrep_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
        (totalMicroBits N) 3 θ s_bit.mem := by
      have hrep0 := canonHashMem_rep hN_le_U hU.le hfit_hash θ
      have hhash_eq : ∀ addr, offHash ≤ addr → addr < offLM U w N →
          s_bit.mem addr = canonHashMem U w N θ addr := by
        intro addr hlo hhi
        have hlt_td : addr < offTD U w N := by unfold offTD offGM; omega
        have hlt_meta : addr < epochMetaWords U w N := by unfold offDT at heq_meta; omega
        rw [buildBitState_mem_lt_metaWords hw θ s_fix td dt hlt_meta,
          epochMetaMem_lt_offTD hw θ s_fix.mem td dt hlt_td]
        unfold baseMetaMem
        have h0 : addr ≠ 0 := by unfold offHash at hlo; omega
        have h1 : addr ≠ 1 := by unfold offHash at hlo; omega
        have h2 : addr ≠ 2 := by unfold offHash at hlo; omega
        have h3 : addr ≠ 3 := by unfold offHash at hlo; omega
        have hN0 : N ≠ 0 := Nat.ne_of_gt hN_pos
        simp [h0, h1, h2, h3, hhi, hN0]
      have htab_addr : ∀ wIdx < ReducedKWise.tableWords w (Succinct.qBits U N)
          (Succinct.hashB N) (totalMicroBits N),
          offHash ≤ ReducedKWise.tabBase offHash (Succinct.qBits U N)
            (Succinct.hashB N) (totalMicroBits N) 3 + wIdx ∧
          ReducedKWise.tabBase offHash (Succinct.qBits U N)
            (Succinct.hashB N) (totalMicroBits N) 3 + wIdx < offLM U w N := by
        intro wIdx hwIdx
        unfold offLM Succinct.hashSpace ReducedKWise.space ReducedKWise.tabBase; omega
      refine ⟨⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩, ⟨?_, fun j m_limb => ?_⟩⟩
      · rw [hhash_eq _ (htab_addr wIdx hwIdx).1 (htab_addr wIdx hwIdx).2]
        exact hrep0.1.1 wIdx hwIdx
      · have hp_lt : idx >>> reducedPackShift
            (reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N)) w <
            ReducedKWise.tableWords w (Succinct.qBits U N) (Succinct.hashB N)
              (totalMicroBits N) :=
          shiftRight_lt_reducedTableWords hidx
        have haddr := htab_addr _ hp_lt
        change getLimb _ (s_bit.mem (ReducedKWise.tabBase offHash (Succinct.qBits U N)
            (Succinct.hashB N) (totalMicroBits N) 3 + _)) _ = _
        rw [hhash_eq _ haddr.1 haddr.2]; exact hrep0.1.2 idx hidx
      · have haddr : offHash ≤ offHash ∧ offHash < offLM U w N := by
          unfold offLM Succinct.hashSpace ReducedKWise.space
          have := ReducedKWise.seedWords_pos (Succinct.qBits U N) (Succinct.hashB N)
            (totalMicroBits N) 3
          omega
        rw [hhash_eq _ haddr.1 haddr.2]; exact hrep0.2.1
      · let L_limb := reducedLimbCount
          (reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N))
        have hlt_3L : m_limb.val + L_limb * j.val < 3 * L_limb := by
          calc m_limb.val + L_limb * j.val < L_limb + L_limb * j.val :=
                Nat.add_lt_add_right m_limb.isLt _
            _ = L_limb * (j.val + 1) := by ring
            _ ≤ L_limb * 3 := Nat.mul_le_mul_left L_limb j.isLt
            _ = 3 * L_limb := Nat.mul_comm L_limb 3
        have haddr : offHash ≤ offHash + 1 + (m_limb.val + L_limb * j.val) ∧
            offHash + 1 + (m_limb.val + L_limb * j.val) < offLM U w N := by
          unfold offLM Succinct.hashSpace ReducedKWise.space ReducedKWise.seedWords
          dsimp only [L_limb] at hlt_3L ⊢; omega
        change s_bit.mem (offHash + 1 + (m_limb.val + L_limb * j.val)) = _
        rw [hhash_eq _ haddr.1 haddr.2]; exact hrep0.2.2 j m_limb
    have htot_eq : Succinct.totalSlots N (gmAtBit U w N s_bit.mem) = m := by
      rw [hgm]; exact hdict.htot
    obtain ⟨L, hbucket_fix⟩ := hdict.hbucket
    have htd_bit : TailDenseInv N (gmAtBit U w N s_bit.mem 0) (gmAtBit U w N s_bit.mem 1)
        (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) := by
      rw [hgm]; exact tailDenseInv_congr htd htd_eq hdt_eq hntails_le
    have hphys_eq : ∀ d < Succinct.totalSlots N (gmAtBit U w N s_bit.mem),
        physOfDense N (gmAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) d =
          physOfDense N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) dt d := by
      intro d hd; rw [htot_eq] at hd; rw [hgm]; unfold physOfDense
      split_ifs with hb0 hlt
      · rfl
      · rfl
      · have hM : 0 < maxTailItems N := by
          have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
          have := (hbucket_fix.hslot.multi_tail hb_pos).ntails_le
          have htot_s : Succinct.totalSlots N
              (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) = m := hdict.htot
          unfold Succinct.totalSlots at htot_s; rw [ite_eq_right hb0] at htot_s; omega
        rw [hdt_eq _ (Nat.mod_lt d hM)]
    refine ⟨hrep_hash, htot_eq, L, ?_⟩
    refine bucketRepInv_of_fixed hbucket_fix hgm hlm htd_bit (fun d hd => ?_) (fun d hd => ?_)
    · have hdm : d < (Dynamic.dom s_abs).card := by rwa [htot_eq] at hd
      rw [(buildBitState_denseQuotAt_ValAt hw hU.le hV θ s_fix td dt hdm).1, hphys_eq d hd]
    · have hdm : d < (Dynamic.dom s_abs).card := by rwa [htot_eq] at hd
      rw [(buildBitState_denseQuotAt_ValAt hw hU.le hV θ s_fix td dt hdm).2, hphys_eq d hd]

end Cslib.DataStructure.Dictionary.BitResizable
