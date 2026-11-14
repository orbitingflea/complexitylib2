/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module

import CslibFrontier.Computability.PointerMachine.Simulation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Heap-embedding clients

A two-node chain embeds in a larger, reordered heap with extra incoming links. A program
allocates a new head and follows the chain to null; simulation preserves its exact cost.
-/

set_option linter.privateModule false

open Cslib.PointerMachine

private def model : Model := ⟨Unit, (), Empty, Empty, nofun, nofun⟩
private abbrev layout : Layout := ⟨2, 0, 1, 0⟩
private abbrev S := State model layout
private def node (p : Pointer) : Record model layout := ⟨fun _ => p, nofun⟩

private def source : S :=
  ⟨0, (fun r => if r = 0 then some 0 else none), nofun, [node (some 1), node none]⟩

private def target : S :=
  ⟨0, (fun r => if r = 0 then some 2 else none), nofun,
    [node none, node (some 2), node (some 0), node (some 2)]⟩

-- Only the allocated source addresses must have distinct images.
private def address (a : ℕ) : ℕ := if a = 0 then 2 else 0

private theorem embedding : State.Embeds address source target := by
  constructor
  · constructor
    · intro r a h
      fin_cases r <;> simp_all [source]; omega
    · intro n hn f a ha
      simp only [source, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> simp_all [node, source]; omega
  · constructor
    · intro r a h
      fin_cases r <;> simp_all [target]; omega
    · intro n hn f a ha
      simp only [target, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp_all [node, target] <;> omega
  · rfl
  · rfl
  · intro r
    fin_cases r <;> rfl
  · intro a b ha hb hab
    have ha' : a < 2 := ha
    have hb' : b < 2 := hb
    interval_cases a <;> interval_cases b <;> simp_all [address]
  · intro a ha
    have ha' : a < 2 := ha
    interval_cases a <;> decide
  · intro a ha
    have ha' : a < 2 := ha
    interval_cases a <;> rfl

-- Allocation changes the previously irrelevant image of address 2, preserving both old images.
example : ∃ g, State.Embeds g ((Instr.create 1).effect source)
      ((Instr.create 1).effect target) ∧ g 0 = 2 ∧ g 1 = 0 ∧ g 2 = 4 := by
  obtain ⟨g, he, hg⟩ := embedding.effect (.create 1)
  refine ⟨g, hg, he 0 (by decide), he 1 (by decide), ?_⟩
  have hp := hg.ptr 1
  change some 4 = some (g 2) at hp
  exact (Option.some.inj hp).symm

private def code : List (Instr model layout) :=
  [.create 1, .storePtr 0 1 0, .movePtr 0 1, .null 1,
   .ifPtrEq 0 1 7, .loadPtr 0 0 0, .goto 4, .halt]

private def state : ℕ → S
  | 0 => source
  | n + 1 => (step code (state n)).getD (state n)

private theorem transition (n : Fin 14) : step code (state n) = some (state (n + 1)) := by
  fin_cases n <;> rfl

private theorem execution : Executes code source (state 14) 15 := by
  refine ⟨14, ?_, rfl, rfl⟩
  have run (n : ℕ) (hn : n ≤ 14) : Runs code source (state n) n := by
    induction n with
    | zero => exact .refl _
    | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (transition ⟨n, by omega⟩)
  exact run 14 le_rfl

example : (state 14).ptr 0 = none ∧ (state 14).heap.length = 3 := ⟨rfl, rfl⟩

-- The larger heap runs the same program in 15 instructions, including halt.
example : ∃ y g, Executes code target y 15 ∧ State.Embeds g (state 14) y ∧
    ∀ a, a < source.heap.length → g a = address a := execution.embed embedding

-- Reflection and determinism rule out a different successful running time in the larger heap.
example {y : S} {time : ℕ} (h : Executes code target y time) : time = 15 := by
  obtain ⟨x, _, hx, _, _⟩ := h.of_embed embedding
  exact (hx.unique execution).2

example : (∃ x, Executes code source x 15) ↔ ∃ y, Executes code target y 15 :=
  embedding.halts_iff
