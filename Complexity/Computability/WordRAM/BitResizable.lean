/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Randomized.Structured
public import Complexity.DataStructure.Memory.BitResizable

/-!
# Bit-Granular Resizable Word-RAM Machine (`BitRAM`)

This module grounds the bit-granular resizable memory specification
(`Cslib.DataStructure.Memory.BitMemory`) in a concrete Word-RAM instruction-execution machine
(`Cslib.WordRAM.BitRAM`) extending `Cslib.WordRAM`.

## Machine architecture and design choices

1. **Concrete machine state (`BitRAM.Data`, `BitRAM.State`):**
   - `BitRAM.Data r` extends `WordRAM.Data r` (`regs : Fin r → ℕ`, `mem : ℕ → ℕ`) with the current
     allocated bit size `bitSize : ℕ`.
   - At word width `w`, the currently allocated words are `[0, x.wordSize w)` where
     `x.wordSize w = x.bitSize ⌈/⌉ w`. Memory instructions (`Op.load dst addr` and
     `Op.store addr src`) are admissible only when `x.regs addr < x.wordSize w` (`OpAdmissible`).

2. **Flat and structured instruction sets (`BitRAM.Instr`, `BitRAM.Code`):**
   - Both the flat instruction set `Instr B r` and structured control flow `Code B r` include:
     * `.op (o : WordRAM.Op B r)`: all standard Word-RAM register, ALU (`add`, `sub`, `mul`, `div`,
       `mod`, `and`, `or`, `xor`, `shiftLeft`, `shiftRight`), `width`, `load`, and `store`
       instructions (`1` instruction unit each);
     * `.grow (dst δReg : Fin r)`: grows `bitSize` by `δ = regs δReg` bits when
       `Fits w (bitSize + δ)`, writes the old `bitSize` into register `dst`, and demonically
       places arbitrary Boolean bit values in `[bitSize, bitSize + δ)` while preserving
       `[0, bitSize)` and zeroing `[bitSize + δ, ∞)` (`max 1 (δ ⌈/⌉ w)` instruction units);
     * `.shrink (δReg : Fin r)`: shrinks `bitSize` by `δ = regs δReg` bits when `δ ≤ bitSize` and
       clears `[bitSize - δ, bitSize)` (`max 1 (δ ⌈/⌉ w)` instruction units);
     * `.size (dst : Fin r)`: loads `bitSize` into register `dst` (`1` instruction unit);
     * `.rand (dst src : Fin r)`: samples uniformly from `{0, …, regs src}` under randomized
       execution `stepRand`.

3. **Demonic execution semantics (`ExecDemonic`, `DemonicExecWithin`) and concrete bit-field
   programs (`readBitsCode`, `writeBitsCode`):**
   - Because `.grow` is demonically nondeterministic in the newly allocated bits, we define the
     demonic Hoare-style execution judgment `DemonicExecWithin w c x P T`, which requires that `c`
     never faults from `x`, has at least one execution path, and every demonic execution path of `c`
     from `x` terminates within `T` instruction units in a state satisfying `P`.
   - We implement `extractSliceCode`, `writeSliceCode`, `readBitsCode`, and `writeBitsCode` as
     explicit `BitRAM.Code .standard 12` machine programs using Word-RAM ALU and memory instructions
     (zero `Nat.ofBits`), and prove their exact `DemonicExecWithin` correctness and
     instruction-count bounds (`≤ 26` instructions for `readBitsCode`, `≤ 42` instructions for
     `writeBitsCode`).

## Main definitions

* `BitRAM.Data`, `BitRAM.State`, `BitRAM.Instr`, `BitRAM.Program`, `BitRAM.Code`: machine state,
  flat instructions, and structured programs of the bit-granular resizable Word RAM.
* `BitRAM.OpAdmissible`, `BitRAM.ExecDemonic`, `BitRAM.DemonicExecWithin`: word-bounded memory
  admissibility and demonic big-step execution with instruction-count bounds.
* `BitRAM.stepRand`: one-step randomized small-step semantics over `PMF`.
* `BitRAM.extractSliceCode`, `BitRAM.writeSliceCode`, `BitRAM.readBitsCode`,
  `BitRAM.writeBitsCode`, `BitRAM.realizeOpCode`: concrete `Code .standard 12` programs for
  bit-field extraction, bit-field update, and `BitMemory.Op` realization.

## Main results

* `BitRAM.readBitsCode_exec`: `readBitsCode` executes in at most `32` instructions on any
  admissible `.readBits` request, computes `readField`, and leaves the bit-resizable memory state
  unchanged.
* `BitRAM.writeBitsCode_exec`: `writeBitsCode` executes in at most `42` instructions on any
  admissible `.writeBits` request, updates memory to `writeFieldMem`, and preserves
  `bitSize`.
* `BitRAM.realizeOpCode_exec`: every admissible `BitMemory.Op` executes on
  `BitRAM.Code .standard 12` within `42 * BitMemory.charge w x.toBitMemoryState o` instructions,
  realizes `BitMemory.dirtyStep`, and preserves `Data.WellFormed w`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.WordRAM.BitRAM

open Cslib.WordRAM
open Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Memory.BitMemory

variable {B : Basis} {r : ℕ}

/-! ## Machine data and state -/

/-- The data of a bit-granular resizable Word RAM with `r` registers: register file `regs`,
word-indexed memory `mem`, and current allocated bit size `bitSize`. -/
@[ext]
structure Data (r : ℕ) where
  /-- Register contents (`Fin r → ℕ`). -/
  regs : Fin r → ℕ
  /-- Word-indexed memory (`ℕ → ℕ`). -/
  mem : ℕ → ℕ
  /-- Current allocated memory size in bits. -/
  bitSize : ℕ

namespace Data

/-- Project `BitRAM.Data r` to `WordRAM.Data r` by forgetting `bitSize`. -/
def toWordRAMData (x : Data r) : WordRAM.Data r where
  regs := x.regs
  mem := x.mem

/-- Project `BitRAM.Data r` to `BitMemory.State` by forgetting `regs`. -/
def toBitMemoryState (x : Data r) : BitMemory.State where
  mem := x.mem
  bitSize := x.bitSize

/-- Number of `w`-bit words currently spanned by `x.bitSize` (`⌈x.bitSize / w⌉`). -/
def wordSize (x : Data r) (w : ℕ) : ℕ :=
  x.bitSize ⌈/⌉ w

/-- Set register `i` to `v`. -/
def set (x : Data r) (i : Fin r) (v : ℕ) : Data r :=
  ⟨Function.update x.regs i v, x.mem, x.bitSize⟩

/-- Write `v` to memory word `a`. -/
def write (x : Data r) (a v : ℕ) : Data r :=
  ⟨x.regs, Function.update x.mem a v, x.bitSize⟩

/-- Set register `i` to `v` if `Fits w v`, and fault (`none`) otherwise. -/
def put (w : ℕ) (x : Data r) (i : Fin r) (v : ℕ) : Option (Data r) :=
  if Fits w v then some (x.set i v) else none

@[simp] theorem set_regs (x : Data r) (i : Fin r) (v : ℕ) :
    (x.set i v).regs = Function.update x.regs i v := rfl
@[simp] theorem set_mem (x : Data r) (i : Fin r) (v : ℕ) : (x.set i v).mem = x.mem := rfl
@[simp] theorem set_bitSize (x : Data r) (i : Fin r) (v : ℕ) :
    (x.set i v).bitSize = x.bitSize := rfl
@[simp] theorem set_wordSize (x : Data r) (i : Fin r) (v w : ℕ) :
    (x.set i v).wordSize w = x.wordSize w := rfl
@[simp] theorem set_toBitMemoryState (x : Data r) (i : Fin r) (v : ℕ) :
    (x.set i v).toBitMemoryState = x.toBitMemoryState := rfl

@[simp] theorem write_regs (x : Data r) (a v : ℕ) : (x.write a v).regs = x.regs := rfl
@[simp] theorem write_mem (x : Data r) (a v : ℕ) :
    (x.write a v).mem = Function.update x.mem a v := rfl
@[simp] theorem write_bitSize (x : Data r) (a v : ℕ) :
    (x.write a v).bitSize = x.bitSize := rfl
@[simp] theorem write_wordSize (x : Data r) (a v w : ℕ) :
    (x.write a v).wordSize w = x.wordSize w := rfl

theorem put_of_fits {w : ℕ} {x : Data r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by
  simp [put, h]

/-- Well-formedness of `BitRAM.Data r` at word width `w`: every register fits in `w` bits and
`x.toBitMemoryState` is well-formed at word width `w`. -/
structure WellFormed (x : Data r) (w : ℕ) : Prop where
  /-- Every register holds a `w`-bit word (`< 2 ^ w`). -/
  regs_fits : ∀ i : Fin r, Fits w (x.regs i)
  /-- The underlying bit-resizable memory state is well-formed at word width `w`. -/
  mem_wf : x.toBitMemoryState.WellFormed w

/-- The initial machine data with zeroed registers, zeroed memory, and `0` allocated bits. -/
def empty (r : ℕ) : Data r where
  regs _ := 0
  mem _ := 0
  bitSize := 0

theorem wellFormed_empty (r w : ℕ) : (empty r).WellFormed w where
  regs_fits _ := fits_zero w
  mem_wf := BitMemory.wellFormed_empty w

end Data

/-- A flat machine state: program counter `pc` and machine data `data`. -/
@[ext]
structure State (r : ℕ) where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers, memory, and allocated `bitSize`. -/
  data : Data r

/-! ## Instructions, admissibility, and small-step randomized semantics -/

/-- Flat instructions of the bit-granular resizable Word RAM. -/
inductive Instr (B : Basis) (r : ℕ) where
  /-- Execute a standard Word-RAM data instruction (`const`, `copy`, `alu`, `load`, `store`). -/
  | op (o : Op B r)
  /-- Grow allocated memory by `regs δReg` bits, storing the old `bitSize` in `dst`. -/
  | grow (dst δReg : Fin r)
  /-- Shrink allocated memory by `regs δReg` bits. -/
  | shrink (δReg : Fin r)
  /-- Store the current `bitSize` in register `dst`. -/
  | size (dst : Fin r)
  /-- Jump to instruction `t`. -/
  | jump (t : ℕ)
  /-- Branch to instruction `t` if `c` holds. -/
  | branch (c : Cond r) (t : ℕ)
  /-- Halt with register `i` as output. -/
  | halt (i : Fin r)
  /-- Sample uniformly from `{0, …, regs src}` into register `dst`. -/
  | rand (dst src : Fin r)
  deriving DecidableEq

/-- A flat program is a list of `Instr B r` indexed by the program counter. -/
abbrev Program (B : Basis) (r : ℕ) := List (Instr B r)

/-- Whether condition `c : Cond r` holds on `x : Data r`. -/
abbrev CondHolds (c : Cond r) (x : Data r) : Prop :=
  c.Holds x.toWordRAMData

instance (c : Cond r) (x : Data r) : Decidable (CondHolds c x) :=
  inferInstanceAs (Decidable (c.Holds x.toWordRAMData))

/-- Memory-bound admissibility of a `WordRAM.Op B r` on `BitRAM.Data r` at word width `w`:
`load` and `store` must address a word strictly below `x.wordSize w = x.bitSize ⌈/⌉ w`. -/
def OpAdmissible (w : ℕ) : Op B r → Data r → Prop
  | .const _ _, _ => True
  | .copy _ _, _ => True
  | .alu _ _ _, _ => True
  | .load _ a, x => x.regs a < x.wordSize w
  | .store a _, x => x.regs a < x.wordSize w

/-- Evaluate a `WordRAM.Op B r` on `BitRAM.Data r` at word width `w` when `OpAdmissible w o x`. -/
def evalOp (w : ℕ) (o : Op B r) (x : Data r) : Option (Data r) :=
  match o with
  | .const d v => x.put w d v
  | .copy d s => some (x.set d (x.regs s))
  | .alu f d args => do
      let value ← B.interp w f (x.regs ∘ args)
      x.put w d value
  | .load d a =>
      if x.regs a < x.wordSize w then some (x.set d (x.mem (x.regs a))) else none
  | .store a s =>
      if x.regs a < x.wordSize w then some (x.write (x.regs a) (x.regs s)) else none

/-- One-step randomized transition of a flat `Program B r` at word width `w` (with zero-initialized
`grow` for concrete `ProbComp` stepping, and uniform sampling in `{0, …, x.regs src}` on
`.rand`). -/
def stepRand (w : ℕ) (P : Program B r) (s : State r) : Option (ProbComp (State r)) :=
  match P[s.pc]? with
  | none => none
  | some instr =>
    match instr with
    | .op o =>
        (evalOp w o s.data).map fun d' => pure ⟨s.pc + 1, d'⟩
    | .grow dst δReg =>
        let δ := s.data.regs δReg
        if Fits w (s.data.bitSize + δ) then
          let s' := (BitMemory.stepFn w s.data.toBitMemoryState (.grow δ)).1
          some (pure ⟨s.pc + 1, Function.update s.data.regs dst s.data.bitSize,
            s'.mem, s'.bitSize⟩)
        else none
    | .shrink δReg =>
        let δ := s.data.regs δReg
        if δ ≤ s.data.bitSize then
          let s' := (BitMemory.stepFn w s.data.toBitMemoryState (.shrink δ)).1
          some (pure ⟨s.pc + 1, s.data.regs, s'.mem, s'.bitSize⟩)
        else none
    | .size dst =>
        (s.data.put w dst s.data.bitSize).map fun d' => pure ⟨s.pc + 1, d'⟩
    | .jump t =>
        some (pure ⟨t, s.data⟩)
    | .branch c t =>
        if CondHolds c s.data then some (pure ⟨t, s.data⟩)
        else some (pure ⟨s.pc + 1, s.data⟩)
    | .halt _ =>
        some (pure s)
    | .rand dst src =>
        let bound := s.data.regs src
        if Fits w bound then
          some (do
            let v ← ProbComp.unifFin bound
            pure ⟨s.pc + 1, s.data.set dst v.val⟩)
        else none

/-! ## Structured programs and demonic big-step execution -/

/-- Structured programs of the bit-granular resizable Word RAM. -/
inductive Code (B : Basis) (r : ℕ) where
  /-- Standard Word-RAM data instruction (`const`, `copy`, `alu`, `load`, `store`). -/
  | op (o : Op B r)
  /-- Grow allocated memory by `regs δReg` bits, storing old `bitSize` in `dst`. -/
  | grow (dst δReg : Fin r)
  /-- Shrink allocated memory by `regs δReg` bits. -/
  | shrink (δReg : Fin r)
  /-- Read current `bitSize` into register `dst`. -/
  | size (dst : Fin r)
  /-- Sequential composition `c₁; c₂`. -/
  | seq (c₁ c₂ : Code B r)
  /-- Conditional branch on `c : Cond r`. -/
  | branch (c : Cond r) (pos neg : Code B r)
  /-- While loop on `c : Cond r`. -/
  | loop (c : Cond r) (body : Code B r)
  /-- Uniform random sampling instruction. -/
  | rand (dst src : Fin r)
  deriving DecidableEq

/-- Demonic big-step execution relation `ExecDemonic w c x y n`:
at word width `w`, structured program `c` can transition from `x` to `y` in `n` instruction units,
where `.grow dst δReg` demonically chooses any `s' : BitMemory.State` satisfying
`BitMemory.dirtyStep w x.toBitMemoryState (.grow (x.regs δReg)) s' x.bitSize`. -/
inductive ExecDemonic (w : ℕ) : Code B r → Data r → Data r → ℕ → Prop where
  /-- A standard Word-RAM instruction costs `1` unit when `evalOp w o x = some y`. -/
  | op {o : Op B r} {x y : Data r} :
      evalOp w o x = some y → ExecDemonic w (.op o) x y 1
  /-- Growing by `δ = x.regs δReg` bits (when `Fits w (x.bitSize + δ)`) costs `max 1 (δ ⌈/⌉ w)`
  units and transitions demonically to any `s'` permitted by `BitMemory.dirtyStep`. -/
  | grow {dst δReg : Fin r} {x : Data r} {s' : BitMemory.State} :
      Fits w (x.bitSize + x.regs δReg) →
      BitMemory.dirtyStep w x.toBitMemoryState (.grow (x.regs δReg)) s' x.bitSize →
      ExecDemonic w (.grow dst δReg) x
        ⟨Function.update x.regs dst x.bitSize, s'.mem, s'.bitSize⟩
        (max 1 ((x.regs δReg) ⌈/⌉ w))
  /-- Shrinking by `δ = x.regs δReg` bits (when `δ ≤ x.bitSize`) costs `max 1 (δ ⌈/⌉ w)` units and
  clears the released bits `[x.bitSize - δ, x.bitSize)`. -/
  | shrink {δReg : Fin r} {x : Data r} :
      x.regs δReg ≤ x.bitSize →
      ExecDemonic w (.shrink δReg) x
        ⟨x.regs, (BitMemory.stepFn w x.toBitMemoryState (.shrink (x.regs δReg))).1.mem,
          x.bitSize - x.regs δReg⟩
        (max 1 ((x.regs δReg) ⌈/⌉ w))
  /-- Reading `x.bitSize` into `dst` (when `Fits w x.bitSize`) costs `1` unit. -/
  | size {dst : Fin r} {x : Data r} :
      Fits w x.bitSize →
      ExecDemonic w (.size dst) x (x.set dst x.bitSize) 1
  /-- Sequential composition adds instruction counts. -/
  | seq {c₁ c₂ : Code B r} {x y z : Data r} {m n : ℕ} :
      ExecDemonic w c₁ x y m → ExecDemonic w c₂ y z n →
      ExecDemonic w (.seq c₁ c₂) x z (m + n)
  /-- Positive branch costs `1` branch instruction plus the `pos` body. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      CondHolds c x → ExecDemonic w pos x y n →
      ExecDemonic w (.branch c pos neg) x y (n + 1)
  /-- Negative branch costs `2` instructions (branch + jump) plus the `neg` body. -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      ¬CondHolds c x → ExecDemonic w neg x y n →
      ExecDemonic w (.branch c pos neg) x y (n + 2)
  /-- Loop exit costs `2` instructions. -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} :
      ¬CondHolds c x → ExecDemonic w (.loop c body) x x 2
  /-- Loop iteration costs `2` instructions plus body and remaining loop. -/
  | loop_iter {c : Cond r} {body : Code B r} {x y z : Data r} {m n : ℕ} :
      CondHolds c x → ExecDemonic w body x y m → ExecDemonic w (.loop c body) y z n →
      ExecDemonic w (.loop c body) x z (m + n + 2)

/-- **Demonic total-correctness and time-bound judgment (`DemonicExecWithin w c x P T`)**:
from initial state `x` at word width `w`, structured program `c` is demonically safe (at least one
execution path exists, and no demonic choice gets stuck) and **every** demonic execution path of
`c` from `x` terminates in at most `T` instruction units in a post-state `y` satisfying `P y`. -/
inductive DemonicExecWithin (w : ℕ) : Code B r → Data r → (Data r → Prop) → ℕ → Prop where
  | op {o : Op B r} {x y : Data r} {P : Data r → Prop} {T : ℕ} :
      evalOp w o x = some y → P y → 1 ≤ T →
      DemonicExecWithin w (.op o) x P T
  | grow {dst δReg : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      Fits w (x.bitSize + x.regs δReg) →
      max 1 ((x.regs δReg) ⌈/⌉ w) ≤ T →
      (∀ s' : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow (x.regs δReg)) s' x.bitSize →
        P ⟨Function.update x.regs dst x.bitSize, s'.mem, s'.bitSize⟩) →
      DemonicExecWithin w (.grow dst δReg) x P T
  | shrink {δReg : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      x.regs δReg ≤ x.bitSize →
      max 1 ((x.regs δReg) ⌈/⌉ w) ≤ T →
      P ⟨x.regs, (BitMemory.stepFn w x.toBitMemoryState (.shrink (x.regs δReg))).1.mem,
        x.bitSize - x.regs δReg⟩ →
      DemonicExecWithin w (.shrink δReg) x P T
  | size {dst : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      Fits w x.bitSize → P (x.set dst x.bitSize) → 1 ≤ T →
      DemonicExecWithin w (.size dst) x P T
  | seq {c₁ c₂ : Code B r} {x : Data r} {Q P : Data r → Prop} {T₁ T₂ T : ℕ} :
      DemonicExecWithin w c₁ x Q T₁ →
      (∀ y, Q y → DemonicExecWithin w c₂ y P T₂) →
      T₁ + T₂ ≤ T →
      DemonicExecWithin w (.seq c₁ c₂) x P T
  | branch_pos {c : Cond r} {pos neg : Code B r} {x : Data r} {P : Data r → Prop} {T₀ T : ℕ} :
      CondHolds c x → DemonicExecWithin w pos x P T₀ → T₀ + 1 ≤ T →
      DemonicExecWithin w (.branch c pos neg) x P T
  | branch_neg {c : Cond r} {pos neg : Code B r} {x : Data r} {P : Data r → Prop} {T₀ T : ℕ} :
      ¬CondHolds c x → DemonicExecWithin w neg x P T₀ → T₀ + 2 ≤ T →
      DemonicExecWithin w (.branch c pos neg) x P T
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      ¬CondHolds c x → P x → 2 ≤ T →
      DemonicExecWithin w (.loop c body) x P T
  | loop_iter {c : Cond r} {body : Code B r} {x : Data r} {Q P : Data r → Prop} {T₁ T₂ T : ℕ} :
      CondHolds c x →
      DemonicExecWithin w body x Q T₁ →
      (∀ y, Q y → DemonicExecWithin w (.loop c body) y P T₂) →
      T₁ + T₂ + 2 ≤ T →
      DemonicExecWithin w (.loop c body) x P T

namespace DemonicExecWithin

variable {w : ℕ} {c c₁ c₂ pos neg : Code B r} {x : Data r} {P Q : Data r → Prop} {T T' : ℕ}

/-- Monotonicity of `DemonicExecWithin` in the postcondition `P` and instruction budget `T`. -/
theorem mono (h : DemonicExecWithin w c x P T) (hP : ∀ y, P y → Q y) (hT : T ≤ T') :
    DemonicExecWithin w c x Q T' := by
  induction h generalizing Q T' with
  | op heval hp h1 => exact .op heval (hP _ hp) (h1.trans hT)
  | grow hfits hcost hp => exact .grow hfits (hcost.trans hT) fun s' hs' => hP _ (hp s' hs')
  | shrink hle hcost hp => exact .shrink hle (hcost.trans hT) (hP _ hp)
  | size hfits hp h1 => exact .size hfits (hP _ hp) (h1.trans hT)
  | seq h₁ _ hsum ih₁ ih₂ =>
    exact .seq (ih₁ (fun _ h => h) le_rfl) (fun y hy => ih₂ y hy hP le_rfl) (hsum.trans hT)
  | branch_pos hc _ hsum ih => exact .branch_pos hc (ih hP le_rfl) (hsum.trans hT)
  | branch_neg hc _ hsum ih => exact .branch_neg hc (ih hP le_rfl) (hsum.trans hT)
  | loop_exit hc hp h2 => exact .loop_exit hc (hP _ hp) (h2.trans hT)
  | loop_iter hc _ _ hsum ih₁ ih₂ =>
    exact .loop_iter hc (ih₁ (fun _ h => h) le_rfl) (fun y hy => ih₂ y hy hP le_rfl)
      (hsum.trans hT)

/-- Soundness of `DemonicExecWithin` against `ExecDemonic`: every execution path of `c` from `x`
under `ExecDemonic` satisfies `P y` and takes `n ≤ T` instructions. -/
theorem sound (h : DemonicExecWithin w c x P T) {y : Data r} {n : ℕ}
    (hexec : ExecDemonic w c x y n) : P y ∧ n ≤ T := by
  induction h generalizing y n with
  | op heval hp h1 =>
    cases hexec with
    | op heval' =>
      rw [heval] at heval'
      cases heval'
      exact ⟨hp, h1⟩
  | grow _ hcost hp =>
    cases hexec with
    | grow _ hstep => exact ⟨hp _ hstep, hcost⟩
  | shrink _ hcost hp =>
    cases hexec with
    | shrink _ => exact ⟨hp, hcost⟩
  | size _ hp h1 =>
    cases hexec with
    | size _ => exact ⟨hp, h1⟩
  | seq _ _ hsum ih₁ ih₂ =>
    cases hexec with
    | seq hex₁ hex₂ =>
      obtain ⟨hq, hm⟩ := ih₁ hex₁
      obtain ⟨hp, hn⟩ := ih₂ _ hq hex₂
      exact ⟨hp, by omega⟩
  | branch_pos hc _ hsum ih =>
    cases hexec with
    | branch_pos _ hex =>
      obtain ⟨hp, hn⟩ := ih hex
      exact ⟨hp, by omega⟩
    | branch_neg hc' _ => exact absurd hc hc'
  | branch_neg hc _ hsum ih =>
    cases hexec with
    | branch_pos hc' _ => exact absurd hc' hc
    | branch_neg _ hex =>
      obtain ⟨hp, hn⟩ := ih hex
      exact ⟨hp, by omega⟩
  | loop_exit hc hp h2 =>
    cases hexec with
    | loop_exit _ => exact ⟨hp, h2⟩
    | loop_iter hc' _ _ => exact absurd hc' hc
  | loop_iter hc _ _ hsum ih₁ ih₂ =>
    cases hexec with
    | loop_exit hc' => exact absurd hc hc'
    | loop_iter _ hex₁ hex₂ =>
      obtain ⟨hq, hm⟩ := ih₁ hex₁
      obtain ⟨hp, hn⟩ := ih₂ _ hq hex₂
      exact ⟨hp, by omega⟩

/-- Forward rule for `Op.const d v`. -/
theorem const {d : Fin r} {v : ℕ} (h : Fits w v) (hP : P (x.set d v)) :
    DemonicExecWithin (B := B) w (.op (.const d v)) x P 1 :=
  .op (Data.put_of_fits h) hP le_rfl

/-- Forward rule for `Op.copy d s`. -/
theorem copy {d s : Fin r} (hP : P (x.set d (x.regs s))) :
    DemonicExecWithin (B := B) w (.op (.copy d s)) x P 1 :=
  .op rfl hP le_rfl

/-- Forward rule for `Op.width d` in the standard basis. -/
theorem width {d : Fin r} (hP : P (x.set d w)) :
    DemonicExecWithin w (.op (.width d)) x P 1 :=
  .op (Data.put_of_fits (fits_self w)) hP le_rfl

/-- Forward rule for `Op.bin f d i j` in the standard basis. -/
theorem bin {f : BinOp} {d i j : Fin r} (h : Fits w (f.eval (x.regs i) (x.regs j)))
    (hP : P (x.set d (f.eval (x.regs i) (x.regs j)))) :
    DemonicExecWithin w (.op (.bin f d i j)) x P 1 :=
  .op (Data.put_of_fits h) hP le_rfl

/-- Forward rule for `Op.load d a`. -/
theorem load {d a : Fin r} (hadm : x.regs a < x.wordSize w)
    (hP : P (x.set d (x.mem (x.regs a)))) :
    DemonicExecWithin (B := B) w (.op (.load d a)) x P 1 :=
  .op (by simp [evalOp, hadm]) hP le_rfl

/-- Forward rule for `Op.store a s`. -/
theorem store {a s : Fin r} (hadm : x.regs a < x.wordSize w)
    (hP : P (x.write (x.regs a) (x.regs s))) :
    DemonicExecWithin (B := B) w (.op (.store a s)) x P 1 :=
  .op (by simp [evalOp, hadm]) hP le_rfl

/-- Forward sequencing rule for `Op.const d v`. -/
theorem step_const {d : Fin r} {v : ℕ} {k : Code B r} (h : Fits w v)
    (hk : DemonicExecWithin w k (x.set d v) P T) :
    DemonicExecWithin w (.seq (.op (.const d v)) k) x P (T + 1) :=
  .seq (const h rfl) (fun _ hy => hy ▸ hk) (by omega)

/-- Forward sequencing rule for `Op.copy d s`. -/
theorem step_copy {d s : Fin r} {k : Code B r}
    (hk : DemonicExecWithin w k (x.set d (x.regs s)) P T) :
    DemonicExecWithin w (.seq (.op (.copy d s)) k) x P (T + 1) :=
  .seq (copy rfl) (fun _ hy => hy ▸ hk) (by omega)

/-- Forward sequencing rule for `Op.width d`. -/
theorem step_width {d : Fin r} {k : Code .standard r}
    (hk : DemonicExecWithin w k (x.set d w) P T) :
    DemonicExecWithin w (.seq (.op (.width d)) k) x P (T + 1) :=
  .seq (width rfl) (fun _ hy => hy ▸ hk) (by omega)

/-- Forward sequencing rule for `Op.bin f d i j`. -/
theorem step_bin {f : BinOp} {d i j : Fin r} {k : Code .standard r}
    (h : Fits w (f.eval (x.regs i) (x.regs j)))
    (hk : DemonicExecWithin w k (x.set d (f.eval (x.regs i) (x.regs j))) P T) :
    DemonicExecWithin w (.seq (.op (.bin f d i j)) k) x P (T + 1) :=
  .seq (bin h rfl) (fun _ hy => hy ▸ hk) (by omega)

/-- Forward sequencing rule for `Op.load d a`. -/
theorem step_load {d a : Fin r} {k : Code B r} (hadm : x.regs a < x.wordSize w)
    (hk : DemonicExecWithin w k (x.set d (x.mem (x.regs a))) P T) :
    DemonicExecWithin w (.seq (.op (.load d a)) k) x P (T + 1) :=
  .seq (load hadm rfl) (fun _ hy => hy ▸ hk) (by omega)

/-- Forward sequencing rule for `Op.store a s`. -/
theorem step_store {a s : Fin r} {k : Code B r} (hadm : x.regs a < x.wordSize w)
    (hk : DemonicExecWithin w k (x.write (x.regs a) (x.regs s)) P T) :
    DemonicExecWithin w (.seq (.op (.store a s)) k) x P (T + 1) :=
  .seq (store hadm rfl) (fun _ hy => hy ▸ hk) (by omega)

end DemonicExecWithin

/-! ## Concrete `BitRAM.Code .standard 12` programs for bit-field extraction and update

Register convention on `Fin 12`:
* `r0 = 0`: return value / extracted or updated word slice
* `r1 = 1`: `bitAddr`
* `r2 = 2`: `len`
* `r3 = 3`: `val` (for `writeBitsCode`) / high slice (for `readBitsCode`)
* `r4 = 4`: word index `q₀ = bitAddr / w` (and `q₀ + 1`)
* `r5 = 5`: bit offset within word `lo = bitAddr % w` (and `0` for high word)
* `r6 = 6`: `lowLen = w - lo`
* `r7 = 7`: `highLen = len - lowLen` / constant `0`
* `r8 = 8`: loaded memory word `word`
* `r9 = 9`: `tmp₁` (word width `w`, `bitMask`, constant `1`)
* `r10 = 10`: `tmp₂` (`sliceMask`, constant `1`)
* `r11 = 11`: `tmp₃` (scratch mask)
-/

/-- Extract the `len`-bit slice at bit offset `lo` (in register `5`) of length `sliceLen` (in
register `lenReg`, where `lenReg ∈ {2, 6, 7}`) from the word in register `8` into register `dst`
(`dst ∈ {0, 3}`), using scratch registers `9` and `10`.
When `sliceLen = w` (so `lo = 0`), copies register `8` directly into `dst`; when `sliceLen < w`,
computes `(r8 >>> r5) &&& ((1 <<< sliceLen) - 1)`. -/
def extractSliceCode (lenReg dst : Fin 12) : Code .standard 12 :=
  .seq (.op (.width 9))
    (.branch (.eq lenReg 9)
      (.op (.copy dst 8))
      (.seq (.op (.bin .shiftRight dst 8 5))
        (.seq (.op (.const 10 1))
          (.seq (.op (.bin .shiftLeft 9 10 lenReg))
            (.seq (.op (.bin .sub 9 9 10))
              (.op (.bin .and dst dst 9)))))))

private theorem shl_one_fits {w k : ℕ} (hlt : k < w) : Fits w (1 <<< k) := by
  rw [Fits, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right Nat.one_lt_two hlt

private theorem and_bitMask_shl_fits {w val lo len : ℕ} (hbound : lo + len ≤ w) :
    Fits w ((val &&& bitMask len) <<< lo) := by
  have hm : (val &&& bitMask len) * 2 ^ lo < 2 ^ len * 2 ^ lo :=
    Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow _ (bitMask_lt _)) (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_comm] at hm
  exact lt_of_lt_of_le (by simpa [Nat.shiftLeft_eq] using hm)
    (Nat.pow_le_pow_right Nat.two_pos hbound)

/-- `extractSliceCode 6 0` (for `lowLen` in `r6`, `lo` in `r5`, `word` in `r8`, output in `r0`)
executes in at most `8` instructions and sets `r0` to
`extractSlice (x.regs 8) (x.regs 5) (x.regs 6)` while preserving registers `1..8`, `mem`, and
`bitSize`. -/
theorem extractSliceCode_low_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hbound : x.regs 5 + x.regs 6 ≤ w) :
    DemonicExecWithin w (extractSliceCode 6 0) x
      (fun y =>
        y.regs 0 = extractSlice (x.regs 8) (x.regs 5) (x.regs 6) ∧
        y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧ y.regs 3 = x.regs 3 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize) 8 := by
  refine DemonicExecWithin.step_width (T := 7) ?_
  by_cases hlen : x.regs 6 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 8 = extractSlice (x.regs 8) (x.regs 5) (x.regs 6)
    rw [hlo, hlen, extractSlice_zero_self hword]
  · have hlt : x.regs 6 < w := by omega
    have hsub : Fits w ((1 <<< x.regs 6) - 1) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 5) hlen ?_ (by omega)
    refine DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword (Nat.shiftRight_le _ _)) ?_
    refine DemonicExecWithin.step_const (T := 3) (fits_one (Nat.ne_of_gt hw)) ?_
    refine DemonicExecWithin.step_bin (T := 2) (shl_one_fits hlt) ?_
    refine DemonicExecWithin.step_bin (T := 1) hsub ?_
    exact DemonicExecWithin.bin (Fits.of_le hsub Nat.and_le_right)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `extractSliceCode 7 3` (for `highLen` in `r7`, `lo` in `r5`, `word` in `r8`, output in `r3`)
executes in at most `8` instructions and sets `r3` to
`extractSlice (x.regs 8) (x.regs 5) (x.regs 7)` while preserving registers `0, 1, 2, 4, 5, 6, 7, 8`,
`mem`, and `bitSize`. -/
theorem extractSliceCode_high_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hbound : x.regs 5 + x.regs 7 ≤ w) :
    DemonicExecWithin w (extractSliceCode 7 3) x
      (fun y =>
        y.regs 3 = extractSlice (x.regs 8) (x.regs 5) (x.regs 7) ∧
        y.regs 0 = x.regs 0 ∧ y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize) 8 := by
  refine DemonicExecWithin.step_width (T := 7) ?_
  by_cases hlen : x.regs 7 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 8 = extractSlice (x.regs 8) (x.regs 5) (x.regs 7)
    rw [hlo, hlen, extractSlice_zero_self hword]
  · have hlt : x.regs 7 < w := by omega
    have hsub : Fits w ((1 <<< x.regs 7) - 1) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 5) hlen ?_ (by omega)
    refine DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword (Nat.shiftRight_le _ _)) ?_
    refine DemonicExecWithin.step_const (T := 3) (fits_one (Nat.ne_of_gt hw)) ?_
    refine DemonicExecWithin.step_bin (T := 2) (shl_one_fits hlt) ?_
    refine DemonicExecWithin.step_bin (T := 1) hsub ?_
    exact DemonicExecWithin.bin (Fits.of_le hsub Nat.and_le_right)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `extractSliceCode 2 0` (for single-word `len` in `r2`, `lo` in `r5`, `word` in `r8`, output in
`r0`) executes in at most `8` instructions and sets `r0` to
`extractSlice (x.regs 8) (x.regs 5) (x.regs 2)` while preserving registers `1..8`, `mem`, and
`bitSize`. -/
theorem extractSliceCode_single_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hbound : x.regs 5 + x.regs 2 ≤ w) :
    DemonicExecWithin w (extractSliceCode 2 0) x
      (fun y =>
        y.regs 0 = extractSlice (x.regs 8) (x.regs 5) (x.regs 2) ∧
        y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧ y.regs 3 = x.regs 3 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧
        y.mem = x.mem ∧ y.bitSize = x.bitSize) 8 := by
  refine DemonicExecWithin.step_width (T := 7) ?_
  by_cases hlen : x.regs 2 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 8 = extractSlice (x.regs 8) (x.regs 5) (x.regs 2)
    rw [hlo, hlen, extractSlice_zero_self hword]
  · have hlt : x.regs 2 < w := by omega
    have hsub : Fits w ((1 <<< x.regs 2) - 1) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 5) hlen ?_ (by omega)
    refine DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword (Nat.shiftRight_le _ _)) ?_
    refine DemonicExecWithin.step_const (T := 3) (fits_one (Nat.ne_of_gt hw)) ?_
    refine DemonicExecWithin.step_bin (T := 2) (shl_one_fits hlt) ?_
    refine DemonicExecWithin.step_bin (T := 1) hsub ?_
    exact DemonicExecWithin.bin (Fits.of_le hsub Nat.and_le_right)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Write the low `sliceLen` bits (in `lenReg ∈ {2, 6, 7}`) of `r3` (`val`) into bit offset `r5`
(`lo`) of the word in `r8`, placing the updated word in `r0` (using scratch registers `9, 10, 11`).
When `sliceLen = w` (so `lo = 0`), copies `r3` directly into `r0`; when `sliceLen < w`, computes
`clearMask r8 (sliceMask r5 sliceLen) ||| ((r3 &&& bitMask sliceLen) <<< r5)`. -/
def writeSliceCode (lenReg : Fin 12) : Code .standard 12 :=
  .seq (.op (.width 9))
    (.branch (.eq lenReg 9)
      (.op (.copy 0 3))
      (.seq (.op (.const 10 1))
        (.seq (.op (.bin .shiftLeft 9 10 lenReg))
          (.seq (.op (.bin .sub 9 9 10))
            (.seq (.op (.bin .shiftLeft 10 9 5))
              (.seq (.op (.bin .and 11 8 10))
                (.seq (.op (.bin .xor 0 8 11))
                  (.seq (.op (.bin .and 11 3 9))
                    (.seq (.op (.bin .shiftLeft 11 11 5))
                      (.op (.bin .or 0 0 11)))))))))))

/-- `writeSliceCode 6` (`lowLen` in `r6`) executes in at most `12` instructions and sets `r0` to
`writeSlice (x.regs 8) (x.regs 5) (x.regs 6) (x.regs 3)` while preserving registers `1..8`, `mem`,
and `bitSize`. -/
theorem writeSliceCode_low_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hval : Fits w (x.regs 3)) (hbound : x.regs 5 + x.regs 6 ≤ w) :
    DemonicExecWithin w (writeSliceCode 6) x
      (fun y =>
        y.regs 0 = writeSlice (x.regs 8) (x.regs 5) (x.regs 6) (x.regs 3) ∧
        y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧ y.regs 3 = x.regs 3 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧ y.mem = x.mem ∧ y.bitSize = x.bitSize) 12 := by
  refine DemonicExecWithin.step_width (T := 11) ?_
  by_cases hlen : x.regs 6 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 3 = writeSlice (x.regs 8) (x.regs 5) (x.regs 6) (x.regs 3)
    rw [hlo, hlen, writeSlice_zero_self hword hval]
  · have hlt : x.regs 6 < w := by omega
    have hsub : Fits w (bitMask (x.regs 6)) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 9) hlen ?_ (by omega)
    refine DemonicExecWithin.step_const (T := 8) (fits_one (Nat.ne_of_gt hw))
      (DemonicExecWithin.step_bin (T := 7) (shl_one_fits hlt)
        (DemonicExecWithin.step_bin (T := 6) hsub
          (DemonicExecWithin.step_bin (T := 5) (sliceMask_fits hbound)
            (DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword Nat.and_le_left)
              (DemonicExecWithin.step_bin (T := 3) (clearMask_fits hword _)
                (DemonicExecWithin.step_bin (T := 2) (Fits.of_le hsub Nat.and_le_right)
                  (DemonicExecWithin.step_bin (T := 1) (and_bitMask_shl_fits hbound) ?_)))))))
    exact DemonicExecWithin.bin (writeSlice_fits hword hbound)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `writeSliceCode 7` (`highLen` in `r7`) executes in at most `12` instructions and sets `r0` to
`writeSlice (x.regs 8) (x.regs 5) (x.regs 7) (x.regs 3)` while preserving registers `1..8`, `mem`,
and `bitSize`. -/
theorem writeSliceCode_high_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hval : Fits w (x.regs 3)) (hbound : x.regs 5 + x.regs 7 ≤ w) :
    DemonicExecWithin w (writeSliceCode 7) x
      (fun y =>
        y.regs 0 = writeSlice (x.regs 8) (x.regs 5) (x.regs 7) (x.regs 3) ∧
        y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧ y.regs 3 = x.regs 3 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧ y.mem = x.mem ∧ y.bitSize = x.bitSize) 12 := by
  refine DemonicExecWithin.step_width (T := 11) ?_
  by_cases hlen : x.regs 7 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 3 = writeSlice (x.regs 8) (x.regs 5) (x.regs 7) (x.regs 3)
    rw [hlo, hlen, writeSlice_zero_self hword hval]
  · have hlt : x.regs 7 < w := by omega
    have hsub : Fits w (bitMask (x.regs 7)) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 9) hlen ?_ (by omega)
    refine DemonicExecWithin.step_const (T := 8) (fits_one (Nat.ne_of_gt hw))
      (DemonicExecWithin.step_bin (T := 7) (shl_one_fits hlt)
        (DemonicExecWithin.step_bin (T := 6) hsub
          (DemonicExecWithin.step_bin (T := 5) (sliceMask_fits hbound)
            (DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword Nat.and_le_left)
              (DemonicExecWithin.step_bin (T := 3) (clearMask_fits hword _)
                (DemonicExecWithin.step_bin (T := 2) (Fits.of_le hsub Nat.and_le_right)
                  (DemonicExecWithin.step_bin (T := 1) (and_bitMask_shl_fits hbound) ?_)))))))
    exact DemonicExecWithin.bin (writeSlice_fits hword hbound)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `writeSliceCode 2` (single-word `len` in `r2`) executes in at most `12` instructions and sets
`r0` to `writeSlice (x.regs 8) (x.regs 5) (x.regs 2) (x.regs 3)` while preserving registers `1..8`,
`mem`, and `bitSize`. -/
theorem writeSliceCode_single_exec {w : ℕ} (hw : 0 < w) {x : Data 12}
    (hword : Fits w (x.regs 8)) (hval : Fits w (x.regs 3)) (hbound : x.regs 5 + x.regs 2 ≤ w) :
    DemonicExecWithin w (writeSliceCode 2) x
      (fun y =>
        y.regs 0 = writeSlice (x.regs 8) (x.regs 5) (x.regs 2) (x.regs 3) ∧
        y.regs 1 = x.regs 1 ∧ y.regs 2 = x.regs 2 ∧ y.regs 3 = x.regs 3 ∧
        y.regs 4 = x.regs 4 ∧ y.regs 5 = x.regs 5 ∧ y.regs 6 = x.regs 6 ∧
        y.regs 7 = x.regs 7 ∧ y.regs 8 = x.regs 8 ∧ y.mem = x.mem ∧ y.bitSize = x.bitSize) 12 := by
  refine DemonicExecWithin.step_width (T := 11) ?_
  by_cases hlen : x.regs 2 = w
  · refine .branch_pos (T₀ := 1) hlen (DemonicExecWithin.copy ?_) (by omega)
    have hlo : x.regs 5 = 0 := by omega
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    change x.regs 3 = writeSlice (x.regs 8) (x.regs 5) (x.regs 2) (x.regs 3)
    rw [hlo, hlen, writeSlice_zero_self hword hval]
  · have hlt : x.regs 2 < w := by omega
    have hsub : Fits w (bitMask (x.regs 2)) := bitMask_fits (Nat.le_of_lt hlt)
    refine .branch_neg (T₀ := 9) hlen ?_ (by omega)
    refine DemonicExecWithin.step_const (T := 8) (fits_one (Nat.ne_of_gt hw))
      (DemonicExecWithin.step_bin (T := 7) (shl_one_fits hlt)
        (DemonicExecWithin.step_bin (T := 6) hsub
          (DemonicExecWithin.step_bin (T := 5) (sliceMask_fits hbound)
            (DemonicExecWithin.step_bin (T := 4) (Fits.of_le hword Nat.and_le_left)
              (DemonicExecWithin.step_bin (T := 3) (clearMask_fits hword _)
                (DemonicExecWithin.step_bin (T := 2) (Fits.of_le hsub Nat.and_le_right)
                  (DemonicExecWithin.step_bin (T := 1) (and_bitMask_shl_fits hbound) ?_)))))))
    exact DemonicExecWithin.bin (writeSlice_fits hword hbound)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete `BitRAM.Code .standard 12` program for `BitMemory.Op.readBits`:
given `bitAddr` in `r1` and `len` in `r2` (`len ≤ w`, `bitAddr + len ≤ x.bitSize`), computes
`readField w 0 x.mem bitAddr len` into register `r0` in at most `26` instructions. -/
def readBitsCode : Code .standard 12 :=
  .seq (.op (.const 7 0))
    (.branch (.eq 2 7)
      (.op (.const 0 0))
      (.seq (.op (.width 9))
        (.seq (.op (.bin .div 4 1 9))
          (.seq (.op (.bin .mod 5 1 9))
            (.seq (.op (.bin .sub 6 9 5))
              (.seq (.op (.load 8 4))
                (.branch (.lt 6 2)
                  (.seq (extractSliceCode 6 0)
                    (.seq (.op (.const 9 1))
                      (.seq (.op (.bin .add 4 4 9))
                        (.seq (.op (.load 8 4))
                          (.seq (.op (.bin .sub 7 2 6))
                            (.seq (.op (.const 5 0))
                              (.seq (extractSliceCode 7 3)
                                (.seq (.op (.bin .shiftLeft 3 3 6))
                                  (.op (.bin .or 0 0 3))))))))))
                  (extractSliceCode 2 0))))))))

/-- **Machine-level correctness of `readBitsCode`**: for any well-formed state `x : Data 12` at
`w > 0` satisfying `BitMemory.valid w x.toBitMemoryState (.readBits (x.regs 1) (x.regs 2))`,
`readBitsCode` executes in at most `32` instructions, leaves `x.mem` and `x.bitSize` unchanged, and
stores `readField w 0 x.mem (x.regs 1) (x.regs 2)` in register `0`. -/
theorem readBitsCode_exec {w : ℕ} (hw : 0 < w) {x : Data 12} (hx : x.WellFormed w)
    (hv : BitMemory.valid w x.toBitMemoryState (.readBits (x.regs 1) (x.regs 2))) :
    DemonicExecWithin w readBitsCode x
      (fun y =>
        y.regs 0 = readField w 0 x.mem (x.regs 1) (x.regs 2) ∧
        y.toBitMemoryState = x.toBitMemoryState) 32 := by
  obtain ⟨hlen, hbound⟩ := hv
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  refine DemonicExecWithin.step_const (T := 31) h0 ?_
  by_cases hb0 : x.regs 2 = 0
  · refine .branch_pos (T₀ := 1) hb0 (DemonicExecWithin.const h0 ?_) (by omega)
    refine ⟨?_, rfl⟩
    change 0 = readField w 0 x.mem (x.regs 1) (x.regs 2)
    rw [hb0, readField_zero]
  · have hbpos : 0 < x.regs 2 := Nat.pos_of_ne_zero hb0
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    have ⟨hq₀, hq₁⟩ := word_indices_lt_of_bit_bound hw hbpos (hbound.trans hcov)
    have hmod_lt : x.regs 1 % w < w := Nat.mod_lt _ hw
    have hdiv_fits : Fits w (x.regs 1 / w) :=
      Fits.of_le (hx.regs_fits 1) (Nat.div_le_self _ _)
    have hmod_fits : Fits w (x.regs 1 % w) :=
      Fits.of_le (fits_self w) (Nat.le_of_lt hmod_lt)
    have hsub_fits : Fits w (w - x.regs 1 % w) :=
      Fits.of_le (fits_self w) (Nat.sub_le _ _)
    refine .branch_neg (T₀ := 29) hb0 ?_ (by omega)
    refine DemonicExecWithin.step_width (T := 28) ?_
    refine DemonicExecWithin.step_bin (T := 27) hdiv_fits ?_
    refine DemonicExecWithin.step_bin (T := 26) hmod_fits ?_
    refine DemonicExecWithin.step_bin (T := 25) hsub_fits ?_
    refine DemonicExecWithin.step_load (T := 24) hq₀ ?_
    by_cases hstrad : w - x.regs 1 % w < x.regs 2
    · refine .branch_pos (T₀ := 23) hstrad ?_ (by omega)
      have hne := (sub_mod_lt_iff_div_ne hw hbpos).mp hstrad
      have hq₁_eq : (x.regs 1 + x.regs 2 - 1) / w = x.regs 1 / w + 1 := by
        rcases div_add_pred_eq_or_succ hw hbpos hlen with h | h
        · exact absurd h hne
        · exact h
      have hq₁' : x.regs 1 / w + 1 < x.wordSize w := hq₁_eq ▸ hq₁
      have hq₁_fits : Fits w (x.regs 1 / w + 1) := by
        have hlt_addr : x.regs 1 / w + 1 ≤ x.regs 1 + x.regs 2 := by
          have := Nat.div_le_self (x.regs 1) w
          omega
        exact lt_of_le_of_lt hlt_addr (lt_of_le_of_lt hbound hx.mem_wf.bitSize_fits)
      refine .seq (T₁ := 8) (T₂ := 15)
        (extractSliceCode_low_exec hw (hx.mem_wf.mem_fits _)
          (by change x.regs 1 % w + (w - x.regs 1 % w) ≤ w; omega))
        (fun y₁ hy₁ => ?_) (by omega)
      rcases hy₁ with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hmem₁, hsz₁⟩
      change y₁.regs 0 =
        extractSlice (x.mem (x.regs 1 / w)) (x.regs 1 % w) (w - x.regs 1 % w) at hr0
      change y₁.regs 2 = x.regs 2 at hr2
      change y₁.regs 4 = x.regs 1 / w at hr4
      change y₁.regs 6 = w - x.regs 1 % w at hr6
      change y₁.mem = x.mem at hmem₁
      change y₁.bitSize = x.bitSize at hsz₁
      have hq₁_adm : y₁.regs 4 + 1 < y₁.wordSize w := by
        rw [hr4]
        change x.regs 1 / w + 1 < (y₁.bitSize ⌈/⌉ w)
        rw [hsz₁]
        exact hq₁'
      have hadd_fits : Fits w (y₁.regs 4 + 1) := by
        rw [hr4]
        exact hq₁_fits
      have hhigh_fits : Fits w (y₁.regs 2 - y₁.regs 6) := by
        rw [hr2, hr6]
        exact Fits.of_le (fits_self w) (by omega)
      refine DemonicExecWithin.step_const (T := 14) h1 ?_
      refine DemonicExecWithin.step_bin (T := 13) hadd_fits ?_
      refine DemonicExecWithin.step_load (T := 12) hq₁_adm ?_
      refine DemonicExecWithin.step_bin (T := 11) hhigh_fits ?_
      refine DemonicExecWithin.step_const (T := 10) h0 ?_
      have hword₂ : Fits w (y₁.mem (y₁.regs 4 + 1)) := by
        rw [hmem₁]
        exact hx.mem_wf.mem_fits _
      have hbound₂ : 0 + (y₁.regs 2 - y₁.regs 6) ≤ w := by
        rw [hr2, hr6]
        omega
      refine .seq (T₁ := 8) (T₂ := 2)
        (extractSliceCode_high_exec hw hword₂ hbound₂) (fun y₂ hy₂ => ?_) (by omega)
      rcases hy₂ with ⟨hy₂3, hy₂0, hy₂1, hy₂2, hy₂4, hy₂5, hy₂6, hy₂7, hy₂8, hmem₂, hsz₂⟩
      change y₂.regs 3 = extractSlice (y₁.mem (y₁.regs 4 + 1)) 0 (y₁.regs 2 - y₁.regs 6) at hy₂3
      change y₂.regs 0 = y₁.regs 0 at hy₂0
      change y₂.regs 6 = y₁.regs 6 at hy₂6
      change y₂.mem = y₁.mem at hmem₂
      change y₂.bitSize = y₁.bitSize at hsz₂
      have hlow_le : w - x.regs 1 % w ≤ x.regs 2 := Nat.le_of_lt hstrad
      have hsum : (x.regs 2 - (w - x.regs 1 % w)) + (w - x.regs 1 % w) = x.regs 2 :=
        Nat.sub_add_cancel hlow_le
      have hshl_fits : Fits w (y₂.regs 3 <<< y₂.regs 6) := by
        rw [hy₂3, hy₂6, hr2, hr6]
        have hm : extractSlice (y₁.mem (y₁.regs 4 + 1)) 0 (x.regs 2 - (w - x.regs 1 % w)) *
            2 ^ (w - x.regs 1 % w) <
            2 ^ (x.regs 2 - (w - x.regs 1 % w)) * 2 ^ (w - x.regs 1 % w) :=
          Nat.mul_lt_mul_of_pos_right (extractSlice_lt _ _ _) (Nat.two_pow_pos _)
        rw [← Nat.pow_add, hsum] at hm
        exact lt_of_lt_of_le (by simpa [Nat.shiftLeft_eq] using hm)
          (Nat.pow_le_pow_right Nat.two_pos hlen)
      have hor_fits : Fits w (y₂.regs 0 ||| (y₂.regs 3 <<< y₂.regs 6)) := by
        apply Nat.or_lt_two_pow
        · rw [hy₂0, hr0]
          exact lt_of_lt_of_le (extractSlice_lt _ _ _)
            (Nat.pow_le_pow_right Nat.two_pos (by omega))
        · exact hshl_fits
      refine DemonicExecWithin.step_bin (T := 1) hshl_fits ?_
      refine DemonicExecWithin.bin hor_fits ⟨?_, ?_⟩
      · change y₂.regs 0 ||| (y₂.regs 3 <<< y₂.regs 6) =
          readField w 0 x.mem (x.regs 1) (x.regs 2)
        rw [hy₂0, hy₂3, hy₂6, hr0, hmem₁, hr4, hr2, hr6]
        unfold readField
        rw [ite_eq_right hb0]
        dsimp only
        rw [ite_eq_left hstrad, Nat.zero_add]
      · ext q
        · change y₂.mem q = x.mem q
          rw [hmem₂]
          exact congrFun hmem₁ q
        · change y₂.bitSize = x.bitSize
          rw [hsz₂]
          exact hsz₁
    · refine .branch_neg (T₀ := 8) hstrad ?_ (by omega)
      refine (extractSliceCode_single_exec hw (hx.mem_wf.mem_fits _)
        (by change x.regs 1 % w + x.regs 2 ≤ w; omega)).mono
        (fun y hy => ?_) le_rfl
      rcases hy with ⟨hr0, _, _, _, _, _, _, _, _, hmem, hsz⟩
      change y.regs 0 = extractSlice (x.mem (x.regs 1 / w)) (x.regs 1 % w) (x.regs 2) at hr0
      change y.mem = x.mem at hmem
      change y.bitSize = x.bitSize at hsz
      refine ⟨?_, ?_⟩
      · rw [hr0]
        unfold readField
        rw [ite_eq_right hb0]
        dsimp only
        rw [ite_eq_right hstrad, Nat.zero_add]
      · ext q
        · exact congrFun hmem q
        · exact hsz

/-- Concrete `BitRAM.Code .standard 12` program for `BitMemory.Op.writeBits`:
given `bitAddr` in `r1`, `len` in `r2`, and `val` in `r3` (`len ≤ w`,
`bitAddr + len ≤ x.bitSize`, `Fits len val`), updates `x.mem` to
`writeFieldMem w 0 x.mem bitAddr len val` in at most `42` instructions. -/
def writeBitsCode : Code .standard 12 :=
  .seq (.op (.const 7 0))
    (.branch (.eq 2 7)
      (.op (.const 0 0))
      (.seq (.op (.width 9))
        (.seq (.op (.bin .div 4 1 9))
          (.seq (.op (.bin .mod 5 1 9))
            (.seq (.op (.bin .sub 6 9 5))
              (.seq (.op (.load 8 4))
                (.branch (.lt 6 2)
                  (.seq (writeSliceCode 6)
                    (.seq (.op (.store 4 0))
                      (.seq (.op (.const 9 1))
                        (.seq (.op (.bin .add 4 4 9))
                          (.seq (.op (.load 8 4))
                            (.seq (.op (.bin .sub 7 2 6))
                              (.seq (.op (.bin .shiftRight 3 3 6))
                                (.seq (.op (.const 5 0))
                                  (.seq (writeSliceCode 7)
                                    (.op (.store 4 0)))))))))))
                  (.seq (writeSliceCode 2)
                    (.op (.store 4 0))))))))))

/-- **Machine-level correctness of `writeBitsCode`**: for any well-formed state `x : Data 12` at
`w > 0` satisfying
`BitMemory.valid w x.toBitMemoryState (.writeBits (x.regs 1) (x.regs 2) (x.regs 3))`,
`writeBitsCode` executes in at most `42` instructions and updates `x.toBitMemoryState` to
`⟨writeFieldMem w 0 x.mem (x.regs 1) (x.regs 2) (x.regs 3), x.bitSize⟩`. -/
theorem writeBitsCode_exec {w : ℕ} (hw : 0 < w) {x : Data 12} (hx : x.WellFormed w)
    (hv : BitMemory.valid w x.toBitMemoryState (.writeBits (x.regs 1) (x.regs 2) (x.regs 3))) :
    DemonicExecWithin w writeBitsCode x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (x.regs 1) (x.regs 2) (x.regs 3))).1) 42 := by
  obtain ⟨hlen, hbound, hval_len⟩ := hv
  have hval : Fits w (x.regs 3) := hval_len.mono hlen
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  refine DemonicExecWithin.step_const (T := 41) h0 ?_
  by_cases hb0 : x.regs 2 = 0
  · refine .branch_pos (T₀ := 1) hb0 (DemonicExecWithin.const h0 ?_) (by omega)
    ext q
    · change x.mem q = writeFieldMem w 0 x.mem (x.regs 1) (x.regs 2) (x.regs 3) q
      rw [hb0, writeFieldMem_zero]
    · rfl
  · have hbpos : 0 < x.regs 2 := Nat.pos_of_ne_zero hb0
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    have ⟨hq₀, hq₁⟩ := word_indices_lt_of_bit_bound hw hbpos (hbound.trans hcov)
    have hmod_lt : x.regs 1 % w < w := Nat.mod_lt _ hw
    have hdiv_fits : Fits w (x.regs 1 / w) :=
      Fits.of_le (hx.regs_fits 1) (Nat.div_le_self _ _)
    have hmod_fits : Fits w (x.regs 1 % w) :=
      Fits.of_le (fits_self w) (Nat.le_of_lt hmod_lt)
    have hsub_fits : Fits w (w - x.regs 1 % w) :=
      Fits.of_le (fits_self w) (Nat.sub_le _ _)
    refine .branch_neg (T₀ := 39) hb0 ?_ (by omega)
    refine DemonicExecWithin.step_width (T := 38) ?_
    refine DemonicExecWithin.step_bin (T := 37) hdiv_fits ?_
    refine DemonicExecWithin.step_bin (T := 36) hmod_fits ?_
    refine DemonicExecWithin.step_bin (T := 35) hsub_fits ?_
    refine DemonicExecWithin.step_load (T := 34) hq₀ ?_
    by_cases hstrad : w - x.regs 1 % w < x.regs 2
    · refine .branch_pos (T₀ := 32) hstrad ?_ (by omega)
      have hne := (sub_mod_lt_iff_div_ne hw hbpos).mp hstrad
      have hq₁_eq : (x.regs 1 + x.regs 2 - 1) / w = x.regs 1 / w + 1 := by
        rcases div_add_pred_eq_or_succ hw hbpos hlen with h | h
        · exact absurd h hne
        · exact h
      have hq₁' : x.regs 1 / w + 1 < x.wordSize w := hq₁_eq ▸ hq₁
      have hq₁_fits : Fits w (x.regs 1 / w + 1) := by
        have hlt_addr : x.regs 1 / w + 1 ≤ x.regs 1 + x.regs 2 := by
          have := Nat.div_le_self (x.regs 1) w
          omega
        exact lt_of_le_of_lt hlt_addr (lt_of_le_of_lt hbound hx.mem_wf.bitSize_fits)
      refine .seq (T₁ := 12) (T₂ := 20)
        (writeSliceCode_low_exec hw (hx.mem_wf.mem_fits _) hval
          (by change x.regs 1 % w + (w - x.regs 1 % w) ≤ w; omega))
        (fun y₁ hy₁ => ?_) (by omega)
      rcases hy₁ with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hmem₁, hsz₁⟩
      change y₁.regs 0 =
        writeSlice (x.mem (x.regs 1 / w)) (x.regs 1 % w) (w - x.regs 1 % w) (x.regs 3) at hr0
      change y₁.regs 2 = x.regs 2 at hr2
      change y₁.regs 3 = x.regs 3 at hr3
      change y₁.regs 4 = x.regs 1 / w at hr4
      change y₁.regs 6 = w - x.regs 1 % w at hr6
      change y₁.mem = x.mem at hmem₁
      change y₁.bitSize = x.bitSize at hsz₁
      have hq₀_adm₁ : y₁.regs 4 < y₁.wordSize w := by
        rw [hr4]
        change x.regs 1 / w < (y₁.bitSize ⌈/⌉ w)
        rw [hsz₁]
        exact hq₀
      refine DemonicExecWithin.step_store (T := 19) hq₀_adm₁ ?_
      have hadd_fits : Fits w (y₁.regs 4 + 1) := by
        rw [hr4]
        exact hq₁_fits
      have hq₁_adm₁ : y₁.regs 4 + 1 < y₁.wordSize w := by
        rw [hr4]
        change x.regs 1 / w + 1 < (y₁.bitSize ⌈/⌉ w)
        rw [hsz₁]
        exact hq₁'
      have hhigh_fits : Fits w (y₁.regs 2 - y₁.regs 6) := by
        rw [hr2, hr6]
        exact Fits.of_le (fits_self w) (by omega)
      have hshr_fits : Fits w (y₁.regs 3 >>> y₁.regs 6) := by
        rw [hr3]
        exact Fits.of_le hval (Nat.shiftRight_le _ _)
      refine DemonicExecWithin.step_const (T := 18) h1 ?_
      refine DemonicExecWithin.step_bin (T := 17) hadd_fits ?_
      refine DemonicExecWithin.step_load (T := 16) hq₁_adm₁ ?_
      refine DemonicExecWithin.step_bin (T := 15) hhigh_fits ?_
      refine DemonicExecWithin.step_bin (T := 14) hshr_fits ?_
      refine DemonicExecWithin.step_const (T := 13) h0 ?_
      have hword₂ : Fits w (Function.update y₁.mem (y₁.regs 4) (y₁.regs 0) (y₁.regs 4 + 1)) := by
        rw [Function.update_of_ne (by omega), hmem₁]
        exact hx.mem_wf.mem_fits _
      have hbound₂ : 0 + (y₁.regs 2 - y₁.regs 6) ≤ w := by
        rw [hr2, hr6]
        omega
      refine .seq (T₁ := 12) (T₂ := 1)
        (writeSliceCode_high_exec hw hword₂ hshr_fits hbound₂) (fun y₂ hy₂ => ?_) (by omega)
      rcases hy₂ with ⟨hy₂0, hy₂1, hy₂2, hy₂3, hy₂4, hy₂5, hy₂6, hy₂7, hy₂8, hmem₂, hsz₂⟩
      change y₂.regs 0 =
        writeSlice (Function.update y₁.mem (y₁.regs 4) (y₁.regs 0) (y₁.regs 4 + 1))
          0 (y₁.regs 2 - y₁.regs 6) (y₁.regs 3 >>> y₁.regs 6) at hy₂0
      change y₂.regs 4 = y₁.regs 4 + 1 at hy₂4
      change y₂.mem = Function.update y₁.mem (y₁.regs 4) (y₁.regs 0) at hmem₂
      change y₂.bitSize = y₁.bitSize at hsz₂
      have hq₁_adm₂ : y₂.regs 4 < y₂.wordSize w := by
        rw [hy₂4]
        change y₁.regs 4 + 1 < (y₂.bitSize ⌈/⌉ w)
        rw [hsz₂]
        exact hq₁_adm₁
      refine DemonicExecWithin.store hq₁_adm₂ ?_
      ext q
      · change Function.update y₂.mem (y₂.regs 4) (y₂.regs 0) q =
          writeFieldMem w 0 x.mem (x.regs 1) (x.regs 2) (x.regs 3) q
        rw [hmem₂, hy₂4, hy₂0, hmem₁, hr4, hr0, hr2, hr6, hr3]
        unfold writeFieldMem
        rw [ite_eq_right hb0]
        dsimp only
        rw [ite_eq_left hstrad, Nat.zero_add]
      · change y₂.bitSize = x.bitSize
        rw [hsz₂]
        exact hsz₁
    · refine .branch_neg (T₀ := 13) hstrad ?_ (by omega)
      refine .seq (T₁ := 12) (T₂ := 1)
        (writeSliceCode_single_exec hw (hx.mem_wf.mem_fits _) hval
          (by change x.regs 1 % w + x.regs 2 ≤ w; omega))
        (fun y₁ hy₁ => ?_) (by omega)
      rcases hy₁ with ⟨hr0, _, _, _, hr4, _, _, _, _, hmem₁, hsz₁⟩
      change y₁.regs 0 =
        writeSlice (x.mem (x.regs 1 / w)) (x.regs 1 % w) (x.regs 2) (x.regs 3) at hr0
      change y₁.regs 4 = x.regs 1 / w at hr4
      change y₁.mem = x.mem at hmem₁
      change y₁.bitSize = x.bitSize at hsz₁
      have hq₀_adm₁ : y₁.regs 4 < y₁.wordSize w := by
        rw [hr4]
        change x.regs 1 / w < (y₁.bitSize ⌈/⌉ w)
        rw [hsz₁]
        exact hq₀
      refine DemonicExecWithin.store hq₀_adm₁ ?_
      ext q
      · change Function.update y₁.mem (y₁.regs 4) (y₁.regs 0) q =
          writeFieldMem w 0 x.mem (x.regs 1) (x.regs 2) (x.regs 3) q
        rw [hmem₁, hr4, hr0]
        unfold writeFieldMem
        rw [ite_eq_right hb0]
        dsimp only
        rw [ite_eq_right hstrad, Nat.zero_add]
      · change y₁.bitSize = x.bitSize
        exact hsz₁

/-- Realize any `BitMemory.Op` as a concrete `BitRAM.Code .standard 12` program (with arguments
already loaded into `r1`, `r2`, `r3` and result returned in `r0`). -/
def realizeOpCode : BitMemory.Op → Code .standard 12
  | .readBits _ _ => readBitsCode
  | .writeBits _ _ _ => writeBitsCode
  | .grow _ => .grow 0 1
  | .shrink _ => .shrink 1
  | .size => .size 0

/-- Whether the registers of `x : Data 12` hold the operands for `o : BitMemory.Op`. -/
def opArgsHold (o : BitMemory.Op) (x : Data 12) : Prop :=
  match o with
  | .readBits a b => x.regs 1 = a ∧ x.regs 2 = b
  | .writeBits a b v => x.regs 1 = a ∧ x.regs 2 = b ∧ x.regs 3 = v
  | .grow δ => x.regs 1 = δ
  | .shrink δ => x.regs 1 = δ
  | .size => True

/-- Postcondition relating the final machine state `y : Data 12` to `BitMemory.dirtyStep w`. -/
def opPost (w : ℕ) (o : BitMemory.Op) (x y : Data 12) : Prop :=
  match o with
  | .readBits a b =>
      BitMemory.dirtyStep w x.toBitMemoryState (.readBits a b) y.toBitMemoryState (y.regs 0)
  | .writeBits a b v =>
      BitMemory.dirtyStep w x.toBitMemoryState (.writeBits a b v) y.toBitMemoryState ()
  | .grow δ =>
      BitMemory.dirtyStep w x.toBitMemoryState (.grow δ) y.toBitMemoryState (y.regs 0)
  | .shrink δ =>
      BitMemory.dirtyStep w x.toBitMemoryState (.shrink δ) y.toBitMemoryState ()
  | .size =>
      BitMemory.dirtyStep w x.toBitMemoryState .size y.toBitMemoryState (y.regs 0)

/-- **Operation-level machine realization theorem**: every admissible `o : BitMemory.Op` executes on
`BitRAM.Code .standard 12` within `42 * BitMemory.charge w x.toBitMemoryState o` machine
instructions and transitions demonically according to `BitMemory.dirtyStep w`. -/
theorem realizeOpCode_exec {w : ℕ} (hw : 0 < w) {x : Data 12} (hx : x.WellFormed w)
    (o : BitMemory.Op) (hv : BitMemory.valid w x.toBitMemoryState o)
    (hargs : opArgsHold o x) :
    DemonicExecWithin w (realizeOpCode o) x (opPost w o x)
      (42 * BitMemory.charge w x.toBitMemoryState o) := by
  cases o with
  | readBits a b =>
    rcases hargs with ⟨rfl, rfl⟩
    refine (readBitsCode_exec hw hx hv).mono (fun y ⟨hr0, hst⟩ => ?_) (by simp [BitMemory.charge])
    exact Prod.ext hst.symm hr0.symm
  | writeBits a b v =>
    rcases hargs with ⟨rfl, rfl, rfl⟩
    refine (writeBitsCode_exec hw hx hv).mono (fun y hst => ?_) (by simp [BitMemory.charge])
    exact Prod.ext hst.symm rfl
  | grow δ =>
    change x.regs 1 = δ at hargs
    subst hargs
    refine .grow hv ?_ fun s' hstep => ?_
    · simp only [BitMemory.charge]
      have : 1 ≤ max 1 (x.regs 1 ⌈/⌉ w) := le_max_left _ _
      omega
    · exact hstep
  | shrink δ =>
    change x.regs 1 = δ at hargs
    subst hargs
    refine .shrink hv ?_ rfl
    simp only [BitMemory.charge]
    have : 1 ≤ max 1 (x.regs 1 ⌈/⌉ w) := le_max_left _ _
    omega
  | size =>
    exact .size hx.mem_wf.bitSize_fits rfl (by simp [BitMemory.charge])

end Cslib.WordRAM.BitRAM
