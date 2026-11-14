/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Embedding

/-!
# Execution through heap embeddings

Injectively embedding a valid heap in a larger valid heap preserves and reflects execution,
with the same program and exact instruction count. Allocation extends the initial address map;
it never changes the images of previously allocated source records. Extra target records need
not be absent, blank, or disconnected from the embedded records.

## Main results

* `Runs.embed`, `Runs.of_embed`: transport runs in both directions, extending the address map.
* `Executes.embed`, `Executes.of_embed`: transport successful executions with their exact costs.
* `State.Embeds.halts_iff`: successful termination at a given cost is independent of heap placement.

This is a theorem about the machine in `Defs`, not a simulation of Tarjan's undefined-value traps.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout} {f : ℕ → ℕ}

/-- A source step is matched by one target step and an extension of the address map. -/
theorem State.Embeds.step {code : List (Instr M L)} {x x' y : State M L}
    (h : State.Embeds f x y) (hs : step code x = some x') :
    ∃ y' g, step code y = some y' ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  obtain ⟨i, hi, hn, rfl⟩ := step_eq_some_iff.mp hs
  obtain ⟨g, he, hg⟩ := h.effect i
  refine ⟨{ i.effect y with pc := i.next y }, g, ?_, ?_, he⟩
  · exact step_eq_some_iff.mpr ⟨i, h.pc ▸ hi, hn, rfl⟩
  · rw [h.next i]
    exact hg.with_pc _

/-- A target step also has a source step; extra target records cannot change control flow. -/
theorem State.Embeds.step_back {code : List (Instr M L)} {x y y' : State M L}
    (h : State.Embeds f x y) (hs : PointerMachine.step code y = some y') :
    ∃ x' g, PointerMachine.step code x = some x' ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  obtain ⟨i, hi, hn, -⟩ := step_eq_some_iff.mp hs
  have hx : PointerMachine.step code x = some { i.effect x with pc := i.next x } :=
    step_eq_some_iff.mpr ⟨i, h.pc.symm ▸ hi, hn, rfl⟩
  obtain ⟨z, g, hz, hg, he⟩ := h.step hx
  cases step_deterministic hz hs
  exact ⟨_, g, hx, hg, he⟩

/-- Transport a run into a larger heap, preserving its exact length and all old address images. -/
theorem Runs.embed {code : List (Instr M L)} {x x' y : State M L} {n : ℕ}
    (hr : Runs code x x' n) (h : State.Embeds f x y) :
    ∃ y' g, Runs code y y' n ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  induction hr using Relation.RelatesInSteps.head_induction_on generalizing y f with
  | hrefl => exact ⟨y, f, .refl _, h, fun _ _ => rfl⟩
  | hhead hs hr ih =>
    obtain ⟨z, g, hz, hg, he⟩ := h.step hs
    obtain ⟨y', g', hy', hg', he'⟩ := ih hg
    refine ⟨y', g', hy'.head _ _ _ _ hz, hg', fun a ha => ?_⟩
    exact (he' a (lt_of_lt_of_le ha (step_length hs).1)).trans (he a ha)

/-- Reflect a target run back to the source heap, retaining the same number of instructions. -/
theorem Runs.of_embed {code : List (Instr M L)} {x y y' : State M L} {n : ℕ}
    (hr : Runs code y y' n) (h : State.Embeds f x y) :
    ∃ x' g, Runs code x x' n ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  induction hr using Relation.RelatesInSteps.head_induction_on generalizing x f with
  | hrefl => exact ⟨x, f, .refl _, h, fun _ _ => rfl⟩
  | hhead hs hr ih =>
    obtain ⟨z, g, hz, hg, he⟩ := h.step_back hs
    obtain ⟨x', g', hx', hg', he'⟩ := ih hg
    refine ⟨x', g', hx'.head _ _ _ _ hz, hg', fun a ha => ?_⟩
    exact (he' a (lt_of_lt_of_le ha (step_length hz).1)).trans (he a ha)

/-- A successful execution transports through a heap embedding, including the halt charge. -/
theorem Executes.embed {code : List (Instr M L)} {x x' y : State M L} {time : ℕ}
    (hr : Executes code x x' time) (h : State.Embeds f x y) :
    ∃ y' g, Executes code y y' time ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  obtain ⟨n, hr, hh, ht⟩ := hr
  obtain ⟨y', g, hy', hg, he⟩ := hr.embed h
  exact ⟨y', g, ⟨n, hy', hg.pc ▸ hh, ht⟩, hg, he⟩

/-- A successful target execution reflects to the source, with identical cost. -/
theorem Executes.of_embed {code : List (Instr M L)} {x y y' : State M L} {time : ℕ}
    (hr : Executes code y y' time) (h : State.Embeds f x y) :
    ∃ x' g, Executes code x x' time ∧ State.Embeds g x' y' ∧
      ∀ a, a < x.heap.length → g a = f a := by
  obtain ⟨n, hr, hh, ht⟩ := hr
  obtain ⟨x', g, hx', hg, he⟩ := hr.of_embed h
  exact ⟨x', g, ⟨n, hx', hg.pc.symm ▸ hh, ht⟩, hg, he⟩

/-- Heap placement and extra target records cannot change successful termination or its cost. -/
theorem State.Embeds.halts_iff {code : List (Instr M L)} {x y : State M L} {time : ℕ}
    (h : State.Embeds f x y) :
    (∃ x', Executes code x x' time) ↔ ∃ y', Executes code y y' time := by
  constructor
  · rintro ⟨x', hx⟩
    obtain ⟨y', _, hy, _, _⟩ := hx.embed h
    exact ⟨y', hy⟩
  · rintro ⟨y', hy⟩
    obtain ⟨x', _, hx, _, _⟩ := hy.of_embed h
    exact ⟨x', hx⟩

end Cslib.PointerMachine
