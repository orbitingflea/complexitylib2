/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.BranchingProgram.Space
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Mathlib.Tactic.FinCases

/-! Concrete `module` clients for deterministic branching programs (`BranchingProgram`),
`ReadOnceProgram.toBranchingProgram`, `MultiTapeTM.toBranchingProgram`, and the native
visited-space (`DSPACE`) branching-program simulation after Arora–Barak Theorem 13.15
(`DSPACE.exists_branchingProgram_of_log_le`, `DSPACE.exists_branchingProgram_slice`,
`L.exists_branchingProgram`, `L.exists_branchingProgram_slice`). -/

public section

namespace CslibFrontierTests.SpaceBranchingProgram

open Cslib Cslib.BranchingPrograms Cslib.Complexity Language Turing Turing.MultiTapeTM

/-! ### 1. A concrete multi-read deterministic branching program -/

/-- A 5-node branching program over `Fin 2 → Bool` that queries coordinate `0`, then coordinate `1`,
and then re-queries coordinate `0` before reaching sink `3` (`true`) or `4` (`false`). -/
def rereadZeroProgram : BranchingProgram (Fin 2) Bool (Fin 5) where
  start := 0
  node v :=
    if v = 0 then .branch 0 fun b => if b then 1 else 4
    else if v = 1 then .branch 1 fun b => if b then 2 else 4
    else if v = 2 then .branch 0 fun b => if b then 3 else 4
    else if v = 3 then .sink true
    else .sink false
  rank v := 4 - v.val
  rank_lt v i next b h := by
    fin_cases v <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceEq, ↓reduceIte] at h
    · injection h with _ hnext; subst hnext; cases b <;> decide
    · injection h with _ hnext; subst hnext; cases b <;> decide
    · injection h with _ hnext; subst hnext; cases b <;> decide
    · cases h
    · cases h

example : rereadZeroProgram.size = 5 := by
  simp [BranchingProgram.size]

example (x : Fin 2 → Bool) : rereadZeroProgram.eval x = (x 0 && x 1) := by
  revert x
  decide

example (x : Fin 2 → Bool) :
    (rereadZeroProgram.rename (Equiv.swap (0 : Fin 2) 1)).eval x = (x 1 && x 0) := by
  rw [BranchingProgram.eval_rename]
  revert x
  decide

example (x : Fin 2 → Bool) :
    (rereadZeroProgram.comap Bool.not).eval x = (!x 0 && !x 1) := by
  rw [BranchingProgram.eval_comap]
  revert x
  decide

/-! ### 2. Embedding a concrete `ReadOnceProgram` into `BranchingProgram` -/

/-- A 2-step read-once program of width `2` over `Fin 2 → Bool` computing the parity
`x 0 ^^ x 1`. -/
def xorReadOnce : ReadOnceProgram 2 Bool Bool where
  start := false
  step _ s a := xor s a
  accept s := s

example (x : Fin 2 → Bool) :
    xorReadOnce.toBranchingProgram.eval x = xorReadOnce.eval x :=
  xorReadOnce.eval_toBranchingProgram x

example : xorReadOnce.toBranchingProgram.size = 6 := by
  rw [xorReadOnce.size_toBranchingProgram]
  decide

/-! ### 3. Compiling a concrete multi-tape Turing machine to a branching program -/

/-- A 0-work-tape machine with state `Bool` that reads the symbol under the input head, emits
`true` iff it is `some true`, and halts. -/
def firstBitTM : MultiTapeTM 0 Bool Bool where
  q₀ := false
  Tr _ inp _ action :=
    action =
      { inputTape := 0
        workTapes := Fin.elim0
        output := some (inp == some true)
        state := none }
  deterministic _ _ _ := ⟨_, rfl, fun _ h => h⟩

theorem firstBitTM_runsInSpace (input : List Bool) : firstBitTM.RunsInSpace input 0 :=
  fun _ => le_rfl

example (n : ℕ) (x : Fin n → Bool) :
    (firstBitTM.toBranchingProgram n 0 1).eval x =
      (((firstBitTM.runFrom (firstBitTM.initCfg (List.ofFn x)) 1).output.head?).getD false) :=
  firstBitTM.eval_toBranchingProgram (firstBitTM_runsInSpace (List.ofFn x))

example (n S : ℕ) (hlog : Nat.log 2 n ≤ S) (hS : 1 ≤ S) :
    (firstBitTM.toBranchingProgram n 0 ((n + 2) * storageBound Bool Bool 0 0)).size ≤
      (spaceBranchingProgramBase 0 Bool 0 0) ^ S :=
  firstBitTM.size_toBranchingProgram_le_pow (Nat.zero_le _) hlog hS

/-- On a 0-work-tape machine with state type `Bool` and space constants `c₁ = c₂ = 0`, the explicit
base `spaceBranchingProgramBase 0 Bool 0 0` evaluates to `1944` (`54 * 3^2 * 1 * 4`). -/
example : spaceBranchingProgramBase 0 Bool 0 0 = 1944 := by
  decide

example (n S : ℕ) (hlog : Nat.log 2 n ≤ S) (hS : 1 ≤ S) :
    (firstBitTM.toBranchingProgram n 0 ((n + 2) * storageBound Bool Bool 0 0)).size ≤
      1944 ^ S := by
  simpa [show spaceBranchingProgramBase 0 Bool 0 0 = 1944 by decide] using
    firstBitTM.size_toBranchingProgram_le_pow (c₁ := 0) (c₂ := 0) (Nat.zero_le _) hlog hS

/-- The language of non-empty bit strings whose first bit is `true`, decided in space `0` by
`firstBitTM`. -/
def FirstBit : Language Bool := {w | w.head? = some true}

/-- Native boundary witness at `n = 1` and `S 1 = 0 ≥ Nat.log 2 1`: no branching program of size
`≤ 1 = c ^ 0` can compute `FirstBit.slice 1`, witnessing that the `max (S n) 1` floor in the native
visited-space simulation (`DSPACE.exists_branchingProgram_of_log_le`) is necessary when
`S 1 = 0`. -/
theorem not_exists_size_le_one_eval_eq_firstBit_slice {Node : Type*} [Fintype Node]
    (P : BranchingProgram (Fin 1) Bool Node) (hsize : P.size ≤ 1) :
    P.eval ≠ FirstBit.slice 1 := by
  intro heval
  have hconst := P.eval_eq_of_size_le_one hsize (fun _ => false) (fun _ => true)
  rw [heval] at hconst
  have h0 : FirstBit.slice 1 (fun _ => false) = false := by
    rw [Bool.eq_false_iff, Ne, Language.slice_eq_true_iff]
    intro h
    exact Bool.false_ne_true (Option.some.inj h)
  have h1 : FirstBit.slice 1 (fun _ => true) = true := by
    rw [Language.slice_eq_true_iff]
    rfl
  rw [h0, h1] at hconst
  exact Bool.false_ne_true hconst

/-! ### 4. Native visited-space simulation (after Theorem 13.15) on `L` and `DSPACE` -/

/-- Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15)
instantiated on Reingold's `USTCON_mem_L`: undirected `s`–`t` connectivity has polynomial-size
deterministic branching programs of size at most `c ^ (Nat.log 2 n + 1)`. -/
theorem ustcon_branchingPrograms :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ (Nat.log 2 n + 1) ∧
      (∀ x ∈ encodes encUSTCON n, P.eval x = encodesMember encUSTCON USTCON n x) ∧
      (∀ a : USTCONInstance, (h : (encUSTCON a).length = n) →
        P.eval (fun i : Fin n => (encUSTCON a)[i.val]'(by omega)) = indicator USTCON a) :=
  L.exists_branchingProgram USTCON_mem_L

/-- Whether a boolean word has an odd number of ones. -/
private def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

private theorem computableInLogSpace_oddOnes : ComputableInLogSpace oddOnes encBits encBool := by
  obtain ⟨c, h, -⟩ := ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false
  exact ⟨_, c, h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun _ =>
    by simpa using Nat.le_mul_of_pos_right c (Nat.succ_pos _)⟩

/-- The parity language of bit strings with an odd number of ones. -/
def OddOnes : Language Bool := {word | oddOnes word = true}

theorem oddOnes_mem_L : (OddOnes : Set (List Bool)) ∈ L encBits :=
  ⟨oddOnes, computableInLogSpace_oddOnes, fun _ => Iff.rfl⟩

theorem oddOnes_mem_DSPACE :
    (OddOnes : Set (List Bool)) ∈ DSPACE encBits (fun n => Nat.log 2 n + 1) := by
  refine DSPACE_mono_of_le_mul_add (s₁ := Nat.log2) (C := 1) (fun n => ?_)
    (mem_L_iff_mem_DSPACE.mp oddOnes_mem_L)
  rw [Nat.log2_eq_log_two]
  omega

/-- Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15)
instantiated on `OddOnes ∈ DSPACE encBits (log₂ n + 1)` and `L`. -/
theorem oddOnes_branchingPrograms :
    (∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ (Nat.log 2 n + 1) ∧ P.eval = OddOnes.slice n) ∧
    (∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ max (Nat.log 2 n + 1) 1 ∧ P.eval = OddOnes.slice n) :=
  ⟨L.exists_branchingProgram_slice oddOnes_mem_L,
   DSPACE.exists_branchingProgram_slice oddOnes_mem_DSPACE fun _ => Nat.le_succ _⟩

end CslibFrontierTests.SpaceBranchingProgram
