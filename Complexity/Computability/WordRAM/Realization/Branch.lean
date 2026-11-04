/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Native branching in memory-client realizations

The branch test reads only the encoded live words. Both alternatives have uniform emitters;
only the selected alternative's domain, fit obligations and local work are required at runtime.
The two-instruction allowance includes the jump on the negative path.

## Main definitions

* `test`: interpret an existing native condition on a word-vector environment.

## Main results

* `test_rename`: a renamed native condition tests the words in its source registers.
* `Realizes.branch`: compose two realizations using an actual native conditional.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}

/-- The existing native condition observes the encoded words, without inspecting memory. -/
def test (c : Cond k) (v : Fin k → ℕ) : Prop := c.Holds ⟨v, fun _ => 0⟩

instance (c : Cond k) (v : Fin k → ℕ) : Decidable (test c v) := by
  unfold test
  infer_instance

/-- A renamed condition holds of native data exactly when it holds of the words in its source
registers. -/
theorem test_rename {r : ℕ} (c : Cond k) (src : Fin k → Fin r)
    (x : Data r) (v : Fin k → ℕ) (h : x.regs ∘ src = v) :
    (c.rename src).Holds x ↔ test c v := by
  cases c <;> simp only [Cond.rename, Cond.Holds, test] <;>
    simp only [← h, Function.comp_apply]

namespace Realizes

/-- Fixed-witness branch realization. -/
theorem branchWith {np Cp nn Cn : ℕ} {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : RealizesWith np Cp B pos input output safePos workPos)
    (hn : RealizesWith nn Cn B neg input output safeNeg workNeg) :
    RealizesWith (max np nn) (max Cp Cn + 2) B
      (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) := by
  obtain ⟨ep, hep⟩ := hp
  obtain ⟨en, hen⟩ := hn
  let ip : Fin (l + np + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  let ineg : Fin (l + nn + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  refine ⟨fun frontier src tmp =>
    .branch (c.rename src) (ep frontier src (tmp ∘ ip))
      (en frontier src (tmp ∘ ineg)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hip : Function.Injective (tmp ∘ ip) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
  have hin : Function.Injective (tmp ∘ ineg) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
  obtain ⟨hnp, hrp⟩ := hep frontier src (tmp ∘ ip) hip
    (fun i j => hd i (ip j)) (fun j => hf (ip j)) hs
  obtain ⟨hnn, hrn⟩ := hen frontier src (tmp ∘ ineg) hin
    (fun i j => hd i (ineg j)) (fun j => hf (ineg j)) hs
  refine ⟨fun h => h.elim hnp hnn, ?_⟩
  intro w d x hx hin hsafe hv
  have hc := test_rename c src x (input d) hin
  by_cases ht : test c (input d)
  · simp only [ite_eq_left ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin hsafe hv
    refine ⟨y, (hy.branch_pos (hc.mpr ht)).mono ?_, hm, ?_, ?_⟩
    · have hC : Cp ≤ max Cp Cn + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (pos d) (memoryState frontier x) + workPos d (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (pos d) (memoryState frontier x) +
              workPos d (memoryState frontier x) + 1) + 2 := by omega
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (pos d) (memoryState frontier x) + workPos d (memoryState frontier x) + 1) +
              (max Cp Cn + 2) * 2 := by omega
        _ = _ := by ring
    · intro i
      have heq : Fin.castAdd (max np nn + 1) i = ip (Fin.castAdd (np + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (ip j))
  · simp only [ite_eq_right ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin hsafe hv
    refine ⟨y, (hy.branch_neg (fun h => ht (hc.mp h))).mono ?_, hm, ?_, ?_⟩
    · have hC : Cn ≤ max Cp Cn + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (neg d) (memoryState frontier x) + workNeg d (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (neg d) (memoryState frontier x) +
              workNeg d (memoryState frontier x) + 1) + 2 := by omega
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (neg d) (memoryState frontier x) + workNeg d (memoryState frontier x) + 1) +
              (max Cp Cn + 2) * 2 := by omega
        _ = _ := by ring
    · intro i
      have heq : Fin.castAdd (max np nn + 1) i = ineg (Fin.castAdd (nn + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (ineg j))

/-- Fixed-witness zero-work branch realization with test and jump absorbed into `max Cp Cn + 2`. -/
theorem branch₀With {np Cp nn Cn : ℕ} {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop} (c : Cond k)
    (hp : RealizesWith np Cp B pos input output safePos (fun _ _ => 0))
    (hn : RealizesWith nn Cn B neg input output safeNeg (fun _ _ => 0)) :
    RealizesWith (max np nn) (max Cp Cn + 2) B
      (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) := by
  obtain ⟨ep, hep⟩ := hp
  obtain ⟨en, hen⟩ := hn
  let ip : Fin (l + np + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  let ineg : Fin (l + nn + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  refine ⟨fun frontier src tmp =>
    .branch (c.rename src) (ep frontier src (tmp ∘ ip))
      (en frontier src (tmp ∘ ineg)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hip : Function.Injective (tmp ∘ ip) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
  have hin : Function.Injective (tmp ∘ ineg) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
  obtain ⟨hnp, hrp⟩ := hep frontier src (tmp ∘ ip) hip
    (fun i j => hd i (ip j)) (fun j => hf (ip j)) hs
  obtain ⟨hnn, hrn⟩ := hen frontier src (tmp ∘ ineg) hin
    (fun i j => hd i (ineg j)) (fun j => hf (ineg j)) hs
  refine ⟨fun h => h.elim hnp hnn, ?_⟩
  intro w d x hx hin hsafe hv
  have hc := test_rename c src x (input d) hin
  by_cases ht : test c (input d)
  · simp only [ite_eq_left ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin hsafe hv
    refine ⟨y, (hy.branch_pos (hc.mpr ht)).mono ?_, hm, ?_, ?_⟩
    · have hC : Cp ≤ max Cp Cn := le_max_left Cp Cn
      have hmul := Nat.mul_le_mul_right
        (memoryCost (pos d) (memoryState frontier x) + 0 + 1) hC
      calc
        Cp * (memoryCost (pos d) (memoryState frontier x) + 0 + 1) + 1
          ≤ max Cp Cn * (memoryCost (pos d) (memoryState frontier x) + 0 + 1) +
            2 * (memoryCost (pos d) (memoryState frontier x) + 0 + 1) := by omega
        _ = (max Cp Cn + 2) *
            (memoryCost (pos d) (memoryState frontier x) + 0 + 1) := by ring
    · intro i
      have heq : Fin.castAdd (max np nn + 1) i = ip (Fin.castAdd (np + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (ip j))
  · simp only [ite_eq_right ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin hsafe hv
    refine ⟨y, (hy.branch_neg (fun h => ht (hc.mp h))).mono ?_, hm, ?_, ?_⟩
    · have hC : Cn ≤ max Cp Cn := le_max_right Cp Cn
      have hmul := Nat.mul_le_mul_right
        (memoryCost (neg d) (memoryState frontier x) + 0 + 1) hC
      calc
        Cn * (memoryCost (neg d) (memoryState frontier x) + 0 + 1) + 2
          ≤ max Cp Cn * (memoryCost (neg d) (memoryState frontier x) + 0 + 1) +
            2 * (memoryCost (neg d) (memoryState frontier x) + 0 + 1) := by omega
        _ = (max Cp Cn + 2) *
            (memoryCost (neg d) (memoryState frontier x) + 0 + 1) := by ring
    · intro i
      have heq : Fin.castAdd (max np nn + 1) i = ineg (Fin.castAdd (nn + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (ineg j))

/-- Both branch emitters precede all runtime values. Shared result slots and disjointness from
live inputs are synthesized internally; the entry domain and work charge select the actual path. -/
theorem branch {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : Realizes B pos input output safePos workPos)
    (hn : Realizes B neg input output safeNeg workNeg) :
    Realizes B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) := by
  obtain ⟨np, Cp, hp⟩ := hp
  obtain ⟨nn, Cn, hn⟩ := hn
  exact ⟨_, _, branchWith c hp hn⟩

end Realizes

namespace RealizesAt

/-- Graded conditional realization with explicit scratch and factor bounds. -/
theorem branch {np Cp nn Cn : ℕ} {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : RealizesAt np Cp B pos input output safePos workPos)
    (hn : RealizesAt nn Cn B neg input output safeNeg workNeg) :
    RealizesAt (max np nn) (max Cp Cn + 2) B
      (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) := by
  obtain ⟨np₀, hnp, Cp₀, hCp, hp⟩ := hp
  obtain ⟨nn₀, hnn, Cn₀, hCn, hn⟩ := hn
  exact ⟨max np₀ nn₀, by omega, max Cp₀ Cn₀ + 2, by omega, Realizes.branchWith c hp hn⟩

/-- Graded zero-work conditional realization with test and jump absorbed into `max Cp Cn + 2`. -/
theorem branchAbsorb {np Cp nn Cn : ℕ} {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop} (c : Cond k)
    (hp : RealizesAt np Cp B pos input output safePos (fun _ _ => 0))
    (hn : RealizesAt nn Cn B neg input output safeNeg (fun _ _ => 0)) :
    RealizesAt (max np nn) (max Cp Cn + 2) B
      (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) := by
  obtain ⟨np₀, hnp, Cp₀, hCp, hp⟩ := hp
  obtain ⟨nn₀, hnn, Cn₀, hCn, hn⟩ := hn
  exact ⟨max np₀ nn₀, by omega, max Cp₀ Cn₀ + 2, by omega, Realizes.branch₀With c hp hn⟩

end RealizesAt

end Cslib.WordRAM.Realization
