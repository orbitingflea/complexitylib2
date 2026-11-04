/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Selecting a uniform realization witness

These projections choose one witness of `Realizes` before any runtime argument, width, memory
or register layout. They use classical choice from a proposition: they do not claim executable
extraction from an arbitrary proof. They let adapters refer to the same emitted native code and
its proved exchange factor, without adding another realization judgment.

## Main definitions

* `Realizes.scratchSize`, `Realizes.factor`, `Realizes.code`: select the uniform witness.

## Main results

* `Realizes.code_spec`: the selected code has the complete original realization contract.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- Number of auxiliary registers, chosen independently of every runtime value. -/
noncomputable def scratchSize (h : Realizes B p input output safe work) : ℕ := h.choose

/-- Uniform exchange factor for memory charges plus local work. -/
noncomputable def factor (h : Realizes B p input output safe work) : ℕ := h.choose_spec.choose

/-- One emitter, selected before the register layout or any runtime data. -/
noncomputable def code (h : Realizes B p input output safe work) {r : ℕ} :
    (frontier : Fin r) → (Fin k → Fin r) → (Fin (l + h.scratchSize + 1) → Fin r) → Code B r :=
  h.choose_spec.choose_spec.choose

/-- The selected witness retains width independence, literal whole-memory semantics, all result
coordinates, and the original live-register frame. -/
theorem code_spec (h : Realizes B p input output safe work) {r : ℕ}
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(h.code frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      ∃ y, ExecWithin w (h.code frontier src tmp) x y
          (h.factor * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
        (∀ i : Fin l, y.regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i :=
  h.choose_spec.choose_spec.choose_spec frontier src tmp hi hd hf hs

end Cslib.WordRAM.Realization.Realizes

namespace Cslib.WordRAM.Realization.RealizesAt

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {n C k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- Pad the `l + n₀ + 1` witness register bank into the uniform `l + n + 1` bank. -/
noncomputable def padSlot (h : RealizesAt n C B p input output safe work) :
    Fin (l + h.choose + 1) → Fin (l + n + 1) :=
  Fin.castLE (by have := h.choose_spec.1; omega)

/-- Select the native emitter padded to the explicit scratch size `n`. -/
noncomputable def code (h : RealizesAt n C B p input output safe work) {r : ℕ}
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + n + 1) → Fin r) : Code B r :=
  h.choose_spec.2.choose_spec.2.choose frontier src (tmp ∘ h.padSlot)

/-- The selected `RealizesAt` emitter executes with explicit scratch size `n` and exchange factor
`C`. -/
theorem code_spec (h : RealizesAt n C B p input output safe work) {r : ℕ}
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + n + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(h.code frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      ∃ y, ExecWithin w (h.code frontier src tmp) x y
          (C * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
        (∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hi' : Function.Injective (tmp ∘ h.padSlot) :=
    hi.comp (Fin.castLE_injective _)
  obtain ⟨hnw, hrun⟩ :=
    h.choose_spec.2.choose_spec.2.choose_spec frontier src (tmp ∘ h.padSlot) hi'
      (fun i j => hd i (h.padSlot j)) (fun j => hf (h.padSlot j)) hs
  refine ⟨hnw, fun w d x hx hin hsafe hv => ?_⟩
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
  have hC₀ : h.choose_spec.2.choose ≤ C := h.choose_spec.2.choose_spec.1
  refine ⟨y, hy.mono (Nat.mul_le_mul_right _ hC₀), hm, fun i => ?_, fun i hif htmp => ?_⟩
  · have hcast : h.padSlot (Fin.castAdd (h.choose + 1) i) = Fin.castAdd (n + 1) i :=
      Fin.ext rfl
    simpa only [Function.comp_apply, hcast] using hout i
  · exact hframe i hif (fun j => htmp (h.padSlot j))

end Cslib.WordRAM.Realization.RealizesAt
