/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (reading abstract of `Cslib.WordRAM`; not for upstream)

public import Complexity.Computability.WordRAM.Time

/-!
# The word RAM: a formal abstract

This file is a short, independently readable account of the word RAM `Cslib.WordRAM` with its
standard operations (`Cslib.WordRAM.Basis.standard`), and of what it means for a problem to be
decidable on it in time `T`. It introduces the machine (words, registers, memory, instructions,
one step, halting runs with their instruction count, faults) and "decidable in time `T`", and
states the two main results: this machine has the same runs as `Cslib.WordRAM`, and the two
notions of "decidable in time `T`" coincide.

To check what `Cslib.WordRAM.DecidableInTime .standard` means, a reader only needs this file.
The main results are stated here as the propositions `RunsAgree` and `DecidableInTimeAgrees`;
`Complexity/Computability/WordRAM/AbstractBridge.lean` proves them (`AbstractBridge.runsAgree`,
`AbstractBridge.decidableInTimeAgrees`), and Lean checks those proofs.
-/

@[expose] public section

namespace Cslib.WordRAM.Abstract

universe u

variable {r : ℕ}

/-
A word RAM with word size `w` holds natural numbers; a *word* is a number below `2 ^ w`.
It has `r` registers, numbered by `Fin r = {0, …, r - 1}`, and a memory cell at every address
`a : ℕ`. Every instruction costs one unit of time.
-/

/-- The binary operations on words. Subtraction is truncated (`3 - 5 = 0`); division and
remainder by zero give `x / 0 = 0` and `x % 0 = x`; `&&&`, `|||`, `^^^` are bitwise and, or and
exclusive or; `shl` and `shr` shift left and right by `y` bits. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- The value of a binary operation, before any check that it fits a word. -/
def AluOp.eval : AluOp → ℕ → ℕ → ℕ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x * 2 ^ y
  | .shr, x, y => x / 2 ^ y

/-- The instructions, over `r` registers. `R[i]` is register `i` and `M[a]` the cell at
address `a`; jump targets are instruction indices. -/
inductive Instr (r : ℕ)
  /-- `R[d] := x`, for a constant `x`. -/
  | const (d : Fin r) (x : ℕ)
  /-- `R[d] := R[i]`. -/
  | copy (d i : Fin r)
  /-- `R[d] := f(R[i], R[j])`. -/
  | alu (f : AluOp) (d i j : Fin r)
  /-- `R[d] := w`, the word size. -/
  | width (d : Fin r)
  /-- `R[d] := M[R[a]]` (indirect load). -/
  | load (d a : Fin r)
  /-- `M[R[a]] := R[i]` (indirect store). -/
  | store (a i : Fin r)
  /-- Go to instruction `t`. -/
  | jump (t : ℕ)
  /-- Go to instruction `t` if `R[i] = R[j]`, else to the next one. -/
  | branchEq (i j : Fin r) (t : ℕ)
  /-- Go to instruction `t` if `R[i] < R[j]`, else to the next one. -/
  | branchLt (i j : Fin r) (t : ℕ)
  /-- Stop, with output `R[i]`. -/
  | halt (i : Fin r)

/-- A program is a list of instructions, numbered from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

/-- A machine state: the number `pc` of the next instruction, the registers and the memory. -/
structure State (r : ℕ) where
  /-- The next instruction. -/
  pc : ℕ
  /-- `reg i` is `R[i]`. -/
  reg : Fin r → ℕ
  /-- `mem a` is `M[a]`. -/
  mem : ℕ → ℕ

/-- What one step does: continue in a new state, halt with an output, or fault. -/
inductive Outcome (r : ℕ)
  | next (s : State r)
  | halt (v : ℕ)
  | fault

/-- One step of program `p` at word size `w` from state `s`. A constant or an operation whose
value is not a word *faults* (no wrap-around), and so does running off the end of the program.
Copies, loads and stores are not checked: from an input whose length and words fit
(`InputFits`), they only ever move words. -/
def step (w : ℕ) (p : Program r) (s : State r) : Outcome r :=
  -- go to the next instruction with `R[d] := x`; `setWord` faults instead if `x ≥ 2 ^ w`
  let set (d : Fin r) (x : ℕ) : Outcome r :=
    .next { s with pc := s.pc + 1, reg := Function.update s.reg d x }
  let setWord (d : Fin r) (x : ℕ) : Outcome r := if x < 2 ^ w then set d x else .fault
  match p[s.pc]? with
  | none => .fault
  | some (.const d x) => setWord d x
  | some (.copy d i) => set d (s.reg i)
  | some (.alu f d i j) => setWord d (f.eval (s.reg i) (s.reg j))
  | some (.width d) => set d w  -- `w < 2 ^ w`, so this never faults
  | some (.load d a) => set d (s.mem (s.reg a))
  | some (.store a i) =>
    .next { s with pc := s.pc + 1, mem := Function.update s.mem (s.reg a) (s.reg i) }
  | some (.jump t) => .next { s with pc := t }
  | some (.branchEq i j t) => .next { s with pc := if s.reg i = s.reg j then t else s.pc + 1 }
  | some (.branchLt i j t) => .next { s with pc := if s.reg i < s.reg j then t else s.pc + 1 }
  | some (.halt i) => .halt (s.reg i)

/-- `Halts w p s v n`: started in state `s` at word size `w`, program `p` halts with output `v`
after exactly `n` instructions, the final `halt` included. A run that faults never halts. -/
def Halts (w : ℕ) (p : Program r) : State r → ℕ → ℕ → Prop
  | _, _, 0 => False
  | s, v, n + 1 =>
    match step w p s with
    | .next t => Halts w p t v n
    | .halt x => x = v ∧ n = 0
    | .fault => False

/-- The start state on input words `x₁, …, xₖ`: instruction `0`, all registers `0`, and memory
`k, x₁, …, xₖ` at addresses `0, 1, …, k`, then `0` everywhere. Placing the input is free. -/
def init (input : List ℕ) : State r where
  pc := 0
  reg := fun _ => 0
  mem := fun a => (input.length :: input).getD a 0

/-- An input fits word size `w` if its length and all its words are words. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-- Program `p` decides the problem `A ⊆ α` in time `T`, on instances encoded as word lists by
`encode`, from word size `bits` on: for every instance `a` and every word size `w ≥ bits a` at
which the input fits, `p` halts within `T a` instructions with output `1` if `a ∈ A` and `0`
if not. The same program must work at every such word size. -/
def Decides {α : Type u} (p : Program r) (A : Set α) (encode : α → List ℕ)
    (T bits : α → ℕ) : Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ v n, Halts w p (init (encode a)) v n ∧ n ≤ T a ∧ (a ∈ A → v = 1) ∧ (a ∉ A → v = 0)

/-- `A` is decidable in time `T` (from word size `bits` on) if some program, with some number
of registers, decides it. -/
def DecidableInTime {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, Decides p A encode T bits

/-! ## Main results

Each result is a proposition here; `Cslib.WordRAM.AbstractBridge` proves it. -/

/-- An outcome of this file and an outcome of `Cslib.WordRAM` *agree* if both continue in the
same state (same next instruction, registers and memory), both halt with the same output, or
both fault. -/
def OutcomeAgrees {r : ℕ} : Outcome r → Cslib.WordRAM.Outcome r → Prop
  | .next s, .next t => t = ⟨s.pc, ⟨s.reg, s.mem⟩⟩
  | .halt v, .halt v' => v = v'
  | .fault, .fault => True
  | _, _ => False

/-- **Main theorem (same machine).** Each program of this file has a program of
`Cslib.WordRAM` over `Basis.standard` with the same registers, and conversely, such that from
every state, at every word size, one step of each has agreeing outcomes, and the halting runs
are the same: same output, same instruction count. -/
def RunsAgree : Prop :=
  ∀ r, (∀ p : Program r, ∃ q : Cslib.WordRAM.Program .standard r, Same p q) ∧
    ∀ q : Cslib.WordRAM.Program .standard r, ∃ p : Program r, Same p q
where
  /-- From every state `⟨pc, reg, mem⟩` and at every word size, one step of `p` and one step of
  `q` agree (`OutcomeAgrees`), so by induction the two runs agree step by step; in particular
  `p` and `q` halt with the same output after the same number of instructions. -/
  Same {r : ℕ} (p : Program r) (q : Cslib.WordRAM.Program .standard r) : Prop :=
    ∀ w pc reg mem,
      OutcomeAgrees (step w p ⟨pc, reg, mem⟩) (Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩) ∧
      ∀ v n, Halts w p ⟨pc, reg, mem⟩ v n ↔ Cslib.WordRAM.Executes w q ⟨pc, ⟨reg, mem⟩⟩ v n

/-- **Main theorem (same time classes).** A problem is decidable in time `T` in the sense of
this file exactly when it is in the sense of `Cslib.WordRAM.DecidableInTime .standard`, for the
same encoding, time bound and word-size threshold. -/
def DecidableInTimeAgrees : Prop :=
  ∀ {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ),
    DecidableInTime A encode T bits ↔ Cslib.WordRAM.DecidableInTime .standard A encode T bits

end Cslib.WordRAM.Abstract

end
