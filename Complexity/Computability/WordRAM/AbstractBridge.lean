/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (proofs of the reading abstract of `Cslib.WordRAM`; not for upstream)

public import Complexity.Computability.WordRAM.Abstract

/-!
# Proofs of the word-RAM abstract

The abstract `Cslib.WordRAM.Abstract` presents the word RAM `Cslib.WordRAM` over
`Cslib.WordRAM.Basis.standard` with its own instruction type and flat states. This module
translates abstract instructions, programs, states and outcomes to `Cslib.WordRAM` and back,
shows that one step commutes with the translation (`step_toCslib`), and derives the
abstract's main results: agreeing steps and the same halting runs (`runsAgree`) and the same
"decidable in time `T`" (`decidableInTimeAgrees`).

The abstract defines inductive types, so this module imports it rather than the reverse.

## Main results

* `Cslib.WordRAM.AbstractBridge.step_toCslib`: one step agrees, outcome for outcome.
* `Cslib.WordRAM.AbstractBridge.halts_iff_executes`: halting runs agree, with output and
  instruction count.
* `Cslib.WordRAM.AbstractBridge.init_toCslib`: the start states on an input agree.
* `Cslib.WordRAM.AbstractBridge.runsAgree`, `Cslib.WordRAM.AbstractBridge.decidableInTimeAgrees`:
  the abstract's main results.
-/

@[expose] public section

namespace Cslib.WordRAM.AbstractBridge

universe u

variable {r : ℕ}

/-! ## Translations -/

/-- An abstract binary operation as a standard binary operation. -/
def aluOpToCslib : Abstract.AluOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .and => .and | .or => .or | .xor => .xor | .shl => .shiftLeft | .shr => .shiftRight

/-- A standard binary operation as an abstract one. -/
def aluOpOfCslib : BinOp → Abstract.AluOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .and => .and | .or => .or | .xor => .xor | .shiftLeft => .shl | .shiftRight => .shr

/-- The two translations of binary operations are inverse. -/
theorem aluOpToCslib_ofCslib (f : BinOp) : aluOpToCslib (aluOpOfCslib f) = f := by
  cases f <;> rfl

/-- An abstract binary operation has the value of its translation; shifts are multiplication
and division by powers of two. -/
theorem eval_aluOpToCslib (f : Abstract.AluOp) (x y : ℕ) :
    (aluOpToCslib f).eval x y = f.eval x y := by
  cases f <;> simp [aluOpToCslib, Abstract.AluOp.eval, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-- An abstract instruction as an instruction of `Cslib.WordRAM` over the standard basis. -/
def instrToCslib : Abstract.Instr r → Instr .standard r
  | .const d x => .op (.const d x)
  | .copy d i => .op (.copy d i)
  | .alu f d i j => .op (.bin (aluOpToCslib f) d i j)
  | .width d => .op (.width d)
  | .load d a => .op (.load d a)
  | .store a i => .op (.store a i)
  | .jump t => .jump t
  | .branchEq i j t => .branch (.eq i j) t
  | .branchLt i j t => .branch (.lt i j) t
  | .halt i => .halt i

/-- An instruction of `Cslib.WordRAM` over the standard basis as an abstract instruction. -/
def instrOfCslib : Instr .standard r → Abstract.Instr r
  | .op (.const d x) => .const d x
  | .op (.copy d i) => .copy d i
  | .op (.alu (.bin f) d args) => .alu (aluOpOfCslib f) d (args (0 : Fin 2)) (args (1 : Fin 2))
  | .op (.alu .width d _) => .width d
  | .op (.load d a) => .load d a
  | .op (.store a i) => .store a i
  | .jump t => .jump t
  | .branch (.eq i j) t => .branchEq i j t
  | .branch (.lt i j) t => .branchLt i j t
  | .halt i => .halt i

theorem instrToCslib_ofCslib (i : Instr .standard r) : instrToCslib (instrOfCslib i) = i := by
  rcases i with (⟨⟩ | ⟨⟩ | ⟨f | _⟩ | ⟨⟩ | ⟨⟩) | _ | ⟨⟨⟩ | ⟨⟩⟩ | _ <;> try rfl
  · cases f <;>
    · simp only [instrOfCslib, instrToCslib, Op.bin]
      congr 2
      funext k
      fin_cases k <;> rfl
  · simp only [instrOfCslib, instrToCslib, Op.width]
    congr 2
    funext k
    exact k.elim0

/-- An abstract program as a program of `Cslib.WordRAM`. -/
abbrev programToCslib (p : Abstract.Program r) : Program .standard r := p.map instrToCslib

/-- A program of `Cslib.WordRAM` as an abstract program. -/
abbrev programOfCslib (q : Program .standard r) : Abstract.Program r := q.map instrOfCslib

theorem programToCslib_ofCslib (q : Program .standard r) :
    programToCslib (programOfCslib q) = q := by
  simp [List.map_map, Function.comp_def, instrToCslib_ofCslib]

/-- An abstract state as a state of `Cslib.WordRAM`. -/
def stateToCslib (s : Abstract.State r) : State r := ⟨s.pc, ⟨s.reg, s.mem⟩⟩

/-- An abstract outcome as an outcome of `Cslib.WordRAM`. -/
def outcomeToCslib : Abstract.Outcome r → Outcome r
  | .next s => .next (stateToCslib s)
  | .halt v => .halt v
  | .fault => .fault

/-! ## One step -/

/-- **One step agrees.** A step of an abstract program is a step of its translation: same next
state, same output on halting, and a fault exactly when the translation faults. -/
theorem step_toCslib (w : ℕ) (p : Abstract.Program r) (s : Abstract.State r) :
    step w (programToCslib p) (stateToCslib s) = outcomeToCslib (Abstract.step w p s) := by
  simp only [WordRAM.step, Abstract.step, stateToCslib, List.getElem?_map]
  cases p[s.pc]? with
  | none => rfl
  | some i =>
    -- constants and operations fault on the same values; the word size is a word
    cases i with
    | const d x => by_cases h : x < 2 ^ w <;> simp [instrToCslib, Data.put, Fits, h,
        outcomeToCslib, stateToCslib, Data.set]
    | alu f d i j => by_cases h : f.eval (s.reg i) (s.reg j) < 2 ^ w <;>
        simp [-BinOp.eval, instrToCslib, Data.put, Fits, eval_aluOpToCslib, h, outcomeToCslib,
          stateToCslib, Data.set]
    | width d => simp [instrToCslib, outcomeToCslib, stateToCslib, Data.set]
    | branchEq i j t => by_cases h : s.reg i = s.reg j <;> simp [instrToCslib, h,
        outcomeToCslib, stateToCslib]
    | branchLt i j t => by_cases h : s.reg i < s.reg j <;> simp [instrToCslib, h,
        outcomeToCslib, stateToCslib]
    | _ => simp [instrToCslib, outcomeToCslib, stateToCslib, Data.set, Data.write]

/-! ## Runs -/

/-- `Cslib.WordRAM.Executes` unfolds by one step, as `Abstract.Halts` is defined. -/
theorem executes_succ_iff {w : ℕ} {q : Program .standard r} {s : State r} {v n : ℕ} :
    Executes w q s v (n + 1) ↔
      match step w q s with
      | .next t => Executes w q t v n
      | .halt x => x = v ∧ n = 0
      | .fault => False := by
  have hrun {t : State r} {m : ℕ} : Executes w q t v m ↔ run w q m t = some (v, m) :=
    ⟨Executes.run_eq, Executes.of_run⟩
  rw [hrun, run_succ]
  rcases step w q s with t | x | _ <;> dsimp only
  · rw [hrun]
    constructor
    · intro h
      obtain ⟨⟨v', k⟩, hk, hvk⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hvk
      obtain ⟨rfl, rfl⟩ := hvk
      exact hk
    · intro h
      rw [h]
      rfl
  · simp [eq_comm]
  · simp

/-- **Halting runs agree.** An abstract program halts with output `v` after `n` instructions
exactly when its translation does. -/
theorem halts_iff_executes {w : ℕ} {p : Abstract.Program r} {s : Abstract.State r} {v n : ℕ} :
    Abstract.Halts w p s v n ↔ Executes w (programToCslib p) (stateToCslib s) v n := by
  induction n generalizing s with
  | zero => exact ⟨False.elim, fun h => absurd h.pos (Nat.lt_irrefl 0)⟩
  | succ n ih =>
    rw [executes_succ_iff, step_toCslib]
    simp only [Abstract.Halts]
    rcases Abstract.step w p s with t | x | _ <;> simp only [outcomeToCslib]
    exact ih

/-- Every outcome agrees with its translation. -/
theorem outcomeAgrees_toCslib (o : Abstract.Outcome r) :
    Abstract.OutcomeAgrees o (outcomeToCslib o) := by
  rcases o <;> simp [Abstract.OutcomeAgrees, outcomeToCslib, stateToCslib]

/-- The two programs of the translation run alike, in the sense of `Abstract.RunsAgree`. -/
theorem same_programToCslib (p : Abstract.Program r) :
    Abstract.RunsAgree.Same p (programToCslib p) := fun w pc reg mem =>
  ⟨step_toCslib w p ⟨pc, reg, mem⟩ ▸ outcomeAgrees_toCslib _, fun _ _ => halts_iff_executes⟩

/-- **Main theorem (same machine)** of the abstract. -/
theorem runsAgree : Abstract.RunsAgree := fun _ =>
  ⟨fun p => ⟨_, same_programToCslib p⟩, fun q => ⟨programOfCslib q, by
    simpa only [programToCslib_ofCslib] using same_programToCslib (programOfCslib q)⟩⟩

/-! ## Decision in time `T` -/

/-- The abstract start state on an input is the start state of `Cslib.WordRAM`: the input
length at address `0`, then the input words. -/
theorem init_toCslib (input : List ℕ) :
    stateToCslib (Abstract.init input : Abstract.State r) = State.init input := by
  simp only [stateToCslib, Abstract.init, State.init, State.mk.injEq, true_and]
  ext a
  · rfl
  · rcases a with _ | a <;> simp [Data.init]

/-- An abstract program decides a problem exactly when its translation does. -/
theorem decides_iff {α : Type*} {p : Abstract.Program r} {A : Set α} {encode : α → List ℕ}
    {T bits : α → ℕ} :
    Abstract.Decides p A encode T bits ↔ (programToCslib p).DecidesInTime encode A T bits := by
  -- the input-fit conditions agree by definition; outputs `1`/`0` on yes/no instances are
  -- outputs `v ≤ 1` with `v = 1 ↔ a ∈ A`
  have hans (a : α) (v : ℕ) :
      ((a ∈ A → v = 1) ∧ (a ∉ A → v = 0)) ↔ (v ≤ 1 ∧ (v = 1 ↔ a ∈ A)) := by
    by_cases ha : a ∈ A <;> simp only [ha, not_true, not_false_eq_true, forall_const,
      false_implies, iff_true, iff_false, true_and, and_true] <;> omega
  simp only [Abstract.Decides, Program.DecidesInTime, Program.Answers, Abstract.InputFits,
    InputFits, Fits, halts_iff_executes, init_toCslib, hans]

/-- **Main theorem (same time classes)** of the abstract. -/
theorem decidableInTimeAgrees : Abstract.DecidableInTimeAgrees.{u} := by
  intro α A encode T bits
  constructor
  · rintro ⟨r, p, hp⟩
    exact ⟨r, programToCslib p, decides_iff.1 hp⟩
  · rintro ⟨r, q, hq⟩
    refine ⟨r, programOfCslib q, decides_iff.2 ?_⟩
    rwa [programToCslib_ofCslib]

end Cslib.WordRAM.AbstractBridge

end
