/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (reading abstract of the exact word RAM; Mathlib and CSLib only)

public import Cslib.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Basic

/-!
# The word RAM: a formal abstract

A short, self-contained account of the word RAM with the standard operations, each computing its
exact value, and of what it means for a problem to be decidable on it in time `T`. It imports
only Mathlib and `Cslib.Init`, and defines the machine from scratch.
`Complexity/Computability/WordRAM/AbstractBridge.lean` proves that it is the library's word RAM.

At word size `w`, a *word* is a number below `2 ^ w`. A machine has `r` registers `R[0]`, …,
`R[r - 1]` and a memory cell `M[a]` at every address `a : ℕ`; all hold natural numbers.
Every instruction takes one unit of time.
-/

@[expose] public section

namespace Cslib.WordRAM.Abstract

variable {r : ℕ}

/-- The binary operations. Division rounds down, `and`, `or`, `xor` are bitwise, and `shl`,
`shr` shift left and right by `y` bits. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- The exact value of a binary operation, before any check that it is a word, or `none` where it
is undefined: `x - y` for `y > x`, and `x / 0` and `x % 0`. -/
def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, x, y => some (x + y)
  | .sub, x, y => if y ≤ x then some (x - y) else none
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)
  | .mod, x, y => if y = 0 then none else some (x % y)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .shl, x, y => some (x * 2 ^ y)
  | .shr, x, y => some (x / 2 ^ y)

/-- The instructions over `r` registers. Jump targets are instruction numbers. -/
inductive Instr (r : ℕ)
  | const (d : Fin r) (x : ℕ)         -- `R[d] := x`
  | copy (d i : Fin r)                -- `R[d] := R[i]`
  | alu (f : AluOp) (d i j : Fin r)   -- `R[d] := f(R[i], R[j])`
  | width (d : Fin r)                 -- `R[d] := w`, the word size
  | load (d a : Fin r)                -- `R[d] := M[R[a]]`
  | store (a i : Fin r)               -- `M[R[a]] := R[i]`
  | jump (t : ℕ)                      -- go to instruction `t`
  | branchEq (i j : Fin r) (t : ℕ)    -- go to `t` if `R[i] = R[j]`, else to the next one
  | branchLt (i j : Fin r) (t : ℕ)    -- go to `t` if `R[i] < R[j]`, else to the next one
  | halt (i : Fin r)                  -- stop with output `R[i]`

/-- A program is a list of instructions, numbered from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

/-- A state: the number `pc` of the next instruction, the registers and the memory. -/
structure State (r : ℕ) where
  /-- The number of the next instruction. -/
  pc : ℕ
  /-- `reg i` is `R[i]`. -/
  reg : Fin r → ℕ
  /-- `mem a` is `M[a]`. -/
  mem : ℕ → ℕ

/-- One step continues in a new state, halts with an output, or faults. -/
inductive Outcome (r : ℕ)
  | next (s : State r)
  | halt (v : ℕ)
  | fault

/-- One step of program `p` at word size `w`. A constant or operation whose value is not a word
faults (no wrap-around), and so do an operation whose value is undefined and running off the end
of the program. Copies, loads and stores are not checked: from an input whose length and words
fit (`InputFits`), they only ever move words. -/
def step (w : ℕ) (p : Program r) (s : State r) : Outcome r :=
  let set (d : Fin r) (x : ℕ) : Outcome r :=  -- `R[d] := x`, then the next instruction
    .next { s with pc := s.pc + 1, reg := Function.update s.reg d x }
  let setWord (d : Fin r) (x : ℕ) : Outcome r := if x < 2 ^ w then set d x else .fault
  match p[s.pc]? with
  | none => .fault
  | some (.const d x) => setWord d x
  | some (.copy d i) => set d (s.reg i)
  | some (.alu f d i j) =>
    match f.eval (s.reg i) (s.reg j) with
    | some x => setWord d x
    | none => .fault
  | some (.width d) => set d w  -- `w < 2 ^ w`, so this never faults
  | some (.load d a) => set d (s.mem (s.reg a))
  | some (.store a i) =>
    .next { s with pc := s.pc + 1, mem := Function.update s.mem (s.reg a) (s.reg i) }
  | some (.jump t) => .next { s with pc := t }
  | some (.branchEq i j t) => .next { s with pc := if s.reg i = s.reg j then t else s.pc + 1 }
  | some (.branchLt i j t) => .next { s with pc := if s.reg i < s.reg j then t else s.pc + 1 }
  | some (.halt i) => .halt (s.reg i)

/-- `Halts w p s v n`: from state `s`, program `p` halts with output `v` after exactly `n`
instructions, the final `halt` included. A run that faults never halts. -/
def Halts (w : ℕ) (p : Program r) : State r → ℕ → ℕ → Prop
  | _, _, 0 => False
  | s, v, n + 1 =>
    match step w p s with
    | .next t => Halts w p t v n
    | .halt x => x = v ∧ n = 0
    | .fault => False

/-- The start state on input `x₁, …, xₖ`: instruction `0`, registers `0`, and memory
`k, x₁, …, xₖ` at addresses `0, 1, …, k`, then `0` everywhere. -/
def init (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-- An input fits word size `w` if its length and all its entries are words. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-- `p` decides `A ⊆ α` in time `T`, on instances encoded by `encode`: for every instance `a`
and every word size `w ≥ bits a` at which the input fits, `p` halts within `T a` instructions
with output `1` if `a ∈ A` and `0` if not. One program serves every such word size. -/
def Decides {α : Type*} (p : Program r) (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) :
    Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ v n, Halts w p (init (encode a)) v n ∧ n ≤ T a ∧ (a ∈ A → v = 1) ∧ (a ∉ A → v = 0)

/-- `A` is decidable in time `T` (from word size `bits` on) if some program, with some number
of registers, decides it. -/
def DecidableInTime {α : Type*} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, Decides p A encode T bits

end Cslib.WordRAM.Abstract

end
