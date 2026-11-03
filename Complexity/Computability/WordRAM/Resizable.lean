/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Randomized.Defs
public import Complexity.Foundations.Data.Nat.Bitwise.Subword

/-!
# Word-granular resizable Word RAM

This module grounds the word-granular resizable memory model (`[LLYZ23a]` §2.1, `[KLZ26]` §5.1)
directly on `Cslib.WordRAM` machine instructions.

A machine state `RData r` consists of `r` registers (`regs : Fin r → ℕ`), a word-addressed memory
(`mem : ℕ → ℕ`), and the current active memory size in words (`frontier : ℕ`, written `L` in
`[LLYZ23a]` and `[KLZ26]`). Unlike the fixed-memory `Cslib.WordRAM`:

1. **Bounds-checked memory access (`Op.evalResizable`)**: `Op.load d a` and `Op.store a s` succeed
   only when the target word address `x.regs a` lies strictly inside the currently allocated prefix
   `[0, x.frontier)` (`x.regs a < x.frontier`), faulting (`none`) otherwise.
2. **Word-granular resizing instructions (`grow` and `shrink`)**:
   - `grow dst kReg` extends the active prefix `[0, frontier)` by `k = regs kReg` words to
     `[0, frontier + k)` (provided `Fits w (frontier + k)`), stores the old `frontier` in register
     `dst`, and initializes the newly allocated words `[frontier, frontier + k)` **demonically**
     (`DemonicGrow w frontier k mem mem'`, permitting any `w`-bit words in
     `[frontier, frontier + k)` while preserving existing words `< frontier` and keeping
     unallocated words `≥ frontier + k` equal to `0`, matching `[KLZ26]` §5.1 Footnotes 10 & 13).
   - `shrink kReg` contracts the active prefix `[0, frontier)` by `k = regs kReg ≤ frontier` words
     to `[0, frontier - k)`, zeroing the released suffix `[frontier - k, frontier)`.
3. **Sub-word bit-packing as concrete `WordRAM` instructions**:
   `wordMaskCode`, `extractSliceCode`, `spliceWordCode`, `readSubwordCode`, and `writeSubwordCode`
   implement sub-word bit-slice extraction, splicing, and cross-word `b`-bit array reads and writes
   using only standard `Cslib.WordRAM` ALU, shift, bitwise, and memory instructions, with proven
   instruction-count bounds (`≤ 7`, `≤ 11`, `≤ 31`, and `≤ 40` instructions respectively).

## Main definitions

* `Cslib.WordRAM.Resizable.RData`, `RData.Bounded`, `DemonicGrow`: machine data with active word
  frontier `frontier`, word/frontier boundedness invariant, and demonic word-growth relation.
* `Cslib.WordRAM.Resizable.evalResizable`: bounds-checked data instruction evaluation on
  `RData r`.
* `Cslib.WordRAM.Resizable.RInstr`, `RProgram`, `RState`, `RCfg`, `stepRandResizable`,
  `runRandResizable`: flat resizable Word-RAM instructions, programs, configurations, and clocked
  randomized execution against an adversarial memory-growth initializer.
* `Cslib.WordRAM.Resizable.RCode`, `RCode.ofCode`, `RDemonicExec`: structured resizable Word-RAM
  programs and big-step demonic execution judgment with instruction-count bounds.
* `Cslib.WordRAM.Resizable.wordMaskCode`, `extractSliceCode`, `spliceWordCode`,
  `readSubwordCode`, `writeSubwordCode`: concrete `WordRAM` machine programs for sub-word
  bit-packing.

## Main results

* `Cslib.WordRAM.Resizable.RDemonicExec.of_exec_regOnly`: any register-only `Cslib.WordRAM.Exec`
  lifts directly to `RDemonicExec` with the same instruction count.
* `Cslib.WordRAM.Resizable.wordMaskCode_exec`, `extractSliceCode_exec`, `spliceWordCode_exec`:
  exact `WordRAM` executions for overflow-safe mask generation (`5` instructions), slice extraction
  (`7` instructions), and word splicing (`11` instructions).
* `Cslib.WordRAM.Resizable.readSubwordCode_exec`, `writeSubwordCode_exec`: demonic execution and
  instruction-count bounds (`≤ 31` and `≤ 40` instructions) for cross-word `b`-bit item reads and
  writes on `RData 16`.
-/

@[expose] public section

namespace Cslib.WordRAM.Resizable

open Cslib.WordRAM Cslib.BitString

variable {B : Basis} {r : ℕ}

/-! ## Resizable machine data and demonic word growth -/

/-- Machine data of a word-granular resizable Word RAM: `r` registers, word-addressed memory `mem`,
and the current number of allocated `w`-bit words `frontier` (the active prefix is
`[0, frontier)`). -/
@[ext]
structure RData (r : ℕ) where
  /-- Register file contents. -/
  regs : Fin r → ℕ
  /-- Word-addressed memory contents. -/
  mem : ℕ → ℕ
  /-- Number of currently allocated words `L`. -/
  frontier : ℕ

namespace RData

/-- Underlying fixed-memory `WordRAM.Data r` (registers and memory). -/
def toData (x : RData r) : Data r := ⟨x.regs, x.mem⟩

/-- Set register `i` to `v`. -/
def set (x : RData r) (i : Fin r) (v : ℕ) : RData r :=
  ⟨Function.update x.regs i v, x.mem, x.frontier⟩

/-- Write `v` to memory address `a`. -/
def write (x : RData r) (a v : ℕ) : RData r :=
  ⟨x.regs, Function.update x.mem a v, x.frontier⟩

/-- Set register `i` to `v` if `Fits w v`, and fault (`none`) otherwise. -/
def put (w : ℕ) (x : RData r) (i : Fin r) (v : ℕ) : Option (RData r) :=
  if Fits w v then some (x.set i v) else none

@[simp]
theorem toData_regs (x : RData r) : x.toData.regs = x.regs := rfl

@[simp]
theorem toData_mem (x : RData r) : x.toData.mem = x.mem := rfl

@[simp]
theorem set_regs (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).regs = Function.update x.regs i v := rfl

@[simp]
theorem set_mem (x : RData r) (i : Fin r) (v : ℕ) : (x.set i v).mem = x.mem := rfl

@[simp]
theorem set_frontier (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).frontier = x.frontier := rfl

@[simp]
theorem set_toData (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).toData = x.toData.set i v := rfl

@[simp]
theorem write_regs (x : RData r) (a v : ℕ) : (x.write a v).regs = x.regs := rfl

@[simp]
theorem write_mem (x : RData r) (a v : ℕ) :
    (x.write a v).mem = Function.update x.mem a v := rfl

@[simp]
theorem write_frontier (x : RData r) (a v : ℕ) :
    (x.write a v).frontier = x.frontier := rfl

@[simp]
theorem write_toData (x : RData r) (a v : ℕ) :
    (x.write a v).toData = x.toData.write a v := rfl

theorem put_of_fits {w : ℕ} {x : RData r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by
  simp [put, h]

/-- Word-boundedness and canonical frontier invariant at word width `w`: every register and memory
cell holds a `w`-bit word, `frontier` fits in a `w`-bit word, and all unallocated cells
`a ≥ frontier` hold `0`. -/
def Bounded (w : ℕ) (x : RData r) : Prop :=
  x.toData.Bounded w ∧ Fits w x.frontier ∧ (∀ a, x.frontier ≤ a → x.mem a = 0)

theorem Bounded.regs_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (i : Fin r) :
    Fits w (x.regs i) :=
  hx.1.1 i

theorem Bounded.mem_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (a : ℕ) :
    Fits w (x.mem a) :=
  hx.1.2 a

theorem Bounded.frontier_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) :
    Fits w x.frontier :=
  hx.2.1

theorem Bounded.zero_above {w : ℕ} {x : RData r} (hx : x.Bounded w) {a : ℕ}
    (ha : x.frontier ≤ a) : x.mem a = 0 :=
  hx.2.2 a ha

theorem Bounded.set {w : ℕ} {x : RData r} (hx : x.Bounded w) {i : Fin r} {v : ℕ}
    (hv : Fits w v) : (x.set i v).Bounded w :=
  ⟨hx.1.set hv, hx.2.1, hx.2.2⟩

theorem Bounded.write {w : ℕ} {x : RData r} (hx : x.Bounded w) {a v : ℕ}
    (ha : a < x.frontier) (hv : Fits w v) : (x.write a v).Bounded w := by
  refine ⟨⟨hx.1.1, fun b => ?_⟩, hx.2.1, fun b hb => ?_⟩
  · dsimp only [RData.write, RData.toData]
    by_cases hba : b = a
    · subst hba; simpa using hv
    · simpa [Function.update_of_ne hba] using hx.1.2 b
  · dsimp only [RData.write] at hb ⊢
    have hba : b ≠ a := by omega
    simpa [Function.update_of_ne hba] using hx.2.2 b hb

end RData

/-- Demonic word-granular growth of `[0, L)` by `k` words at word width `w` (`[KLZ26]` §5.1):
existing cells `a < L` retain their values, newly allocated cells `a ∈ [L, L + k)` receive
arbitrary `w`-bit words (`Fits w (mem' a)`), and unallocated cells `a ≥ L + k` hold `0`. -/
def DemonicGrow (w L k : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < L, mem' a = mem a) ∧
    (∀ a, L ≤ a → a < L + k → Fits w (mem' a)) ∧
    (∀ a, L + k ≤ a → mem' a = 0)

/-- Zero-initializing the newly grown range `[L, L + k)` via `clear mem L k` is a particular
instance of `DemonicGrow` whenever `mem` is zero above `L`. -/
theorem demonicGrow_clear (w L k : ℕ) (mem : ℕ → ℕ) (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L k mem (clear mem L k) := by
  refine ⟨fun a ha => ?_, fun a hlo hhi => ?_, fun a ha => ?_⟩
  · exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  · rw [clear_of_owns ⟨hlo, hhi⟩]
    exact fits_zero w
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
    exact hz a (by omega)

/-- Any memory `mem'` satisfying `DemonicGrow w x.frontier k x.mem mem'` preserves `RData.Bounded w`
when the new frontier `x.frontier + k` fits in `w` bits. -/
theorem RData.Bounded.grow {w : ℕ} {x : RData r} (hx : x.Bounded w) {dst : Fin r} {k : ℕ}
    {mem' : ℕ → ℕ} (hfit : Fits w (x.frontier + k))
    (hgrow : DemonicGrow w x.frontier k x.mem mem') :
    (⟨Function.update x.regs dst x.frontier, mem', x.frontier + k⟩ : RData r).Bounded w := by
  refine ⟨⟨?_, ?_⟩, hfit, hgrow.2.2⟩
  · intro i
    dsimp only [RData.toData]
    by_cases hid : i = dst
    · subst hid; simpa using hx.frontier_fits
    · simpa [Function.update_of_ne hid] using hx.regs_fits i
  · intro a
    dsimp only [RData.toData]
    by_cases hlt : a < x.frontier
    · rw [hgrow.1 a hlt]
      exact hx.mem_fits a
    · by_cases hmid : a < x.frontier + k
      · exact hgrow.2.1 a (by omega) hmid
      · rw [hgrow.2.2 a (by omega)]
        exact fits_zero w

/-- Shrinking the frontier by `k ≤ x.frontier` words and clearing `[x.frontier - k, x.frontier)`
preserves `RData.Bounded w`. -/
theorem RData.Bounded.shrink {w : ℕ} {x : RData r} (hx : x.Bounded w) {k : ℕ}
    (hk : k ≤ x.frontier) :
    (⟨x.regs, clear x.mem (x.frontier - k) k, x.frontier - k⟩ : RData r).Bounded w := by
  refine ⟨⟨hx.1.1, fun a => ?_⟩, hx.2.1.of_le (Nat.sub_le _ _), fun a ha => ?_⟩
  · dsimp only [RData.toData]
    by_cases hown : (Block.mk (x.frontier - k) k).Owns a
    · rw [clear_of_owns hown]
      exact fits_zero w
    · rw [clear_of_not_owns hown]
      exact hx.mem_fits a
  · dsimp only at ha ⊢
    by_cases hlt : a < x.frontier
    · exact clear_of_owns (by simp only [Block.Owns]; omega)
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
      exact hx.zero_above (by omega)

/-! ## Bounds-checked data instruction evaluation on `RData r` -/

/-- Evaluate a data instruction on `RData r` at word size `w`.
Unlike fixed-memory `Op.eval`, `load d a` and `store a s` require the accessed word address
`x.regs a` to lie strictly below `x.frontier` (`x.regs a < x.frontier`), faulting (`none`) on any
access at or above the current frontier. -/
def evalResizable (w : ℕ) : Op B r → RData r → Option (RData r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.regs s))
  | .alu f d args, x => do
      let value ← B.interp w f (x.regs ∘ args)
      x.put w d value
  | .load d a, x =>
      if x.regs a < x.frontier then some (x.set d (x.mem (x.regs a))) else none
  | .store a s, x =>
      if x.regs a < x.frontier then some (x.write (x.regs a) (x.regs s)) else none

/-- Whether a data instruction touches only registers (no `load` or `store`). -/
def IsRegOnlyOp : Op B r → Prop
  | .const _ _ | .copy _ _ | .alu _ _ _ => True
  | .load _ _ | .store _ _ => False

instance (o : Op B r) : Decidable (IsRegOnlyOp o) := by
  cases o <;> unfold IsRegOnlyOp <;> infer_instance

/-- On a register-only data instruction, `evalResizable` agrees with `Op.eval` on `x.toData` and
preserves `x.frontier`. -/
theorem evalResizable_of_isRegOnly {w : ℕ} {o : Op B r} (ho : IsRegOnlyOp o) (x : RData r) :
    evalResizable w o x = (o.eval w x.toData).map fun y => ⟨y.regs, y.mem, x.frontier⟩ := by
  cases o with
  | const d v =>
    dsimp only [evalResizable, Op.eval, RData.put, Data.put]
    split_ifs <;> rfl
  | copy d s => rfl
  | alu f d args =>
    dsimp only [evalResizable, Op.eval, RData.toData]
    cases B.interp w f (x.regs ∘ args) with
    | none => rfl
    | some v =>
      dsimp only [bind, Option.bind, RData.put, Data.put]
      split_ifs <;> rfl
  | load _ _ => exact absurd ho id
  | store _ _ => exact absurd ho id

/-! ## Flat resizable Word-RAM instructions, programs, and clocked randomized execution -/

/-- Flat instructions of a word-granular resizable Word RAM over basis `B` and `r` registers. -/
inductive RInstr (B : Basis) (r : ℕ) where
  /-- Execute a bounds-checked data instruction (`load`/`store` require `regs a < frontier`). -/
  | op (o : Op B r)
  /-- Jump unconditionally to instruction `t`. -/
  | jump (t : ℕ)
  /-- Jump to `t` if `c` holds, otherwise advance `pc` by `1`. -/
  | branch (c : Cond r) (t : ℕ)
  /-- Halt with the contents of register `i` as output. -/
  | halt (i : Fin r)
  /-- Sample uniformly from `[0, regs src]` into `dst`. -/
  | rand (dst src : Fin r)
  /-- Grow the active memory prefix `[0, frontier)` by `regs kReg` words to
  `[0, frontier + regs kReg)`, storing the old `frontier` in `dst`. -/
  | grow (dst kReg : Fin r)
  /-- Shrink the active memory prefix `[0, frontier)` by `regs kReg ≤ frontier` words to
  `[0, frontier - regs kReg)`. -/
  | shrink (kReg : Fin r)
  deriving DecidableEq

/-- A flat resizable Word-RAM program is a list of `RInstr B r` indexed by the program counter. -/
abbrev RProgram (B : Basis) (r : ℕ) := List (RInstr B r)

/-- Machine state of a flat resizable Word-RAM program: program counter and `RData r`. -/
@[ext]
structure RState (r : ℕ) where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers, memory, and active word frontier. -/
  data : RData r

/-- Absorbing configuration for clocked randomized execution of a flat resizable Word-RAM
program. -/
inductive RCfg (r : ℕ) where
  /-- Active execution at state `s`. -/
  | running (s : RState r)
  /-- Halted with scalar output `v` and final resizable machine data `data`. -/
  | halted (v : ℕ) (data : RData r)
  /-- Faulted on an out-of-bounds memory access, overflow, invalid shrink, or invalid `pc`. -/
  | faulted

/-- Adversarial memory initializer for `grow` at step `t`: preserves `mem a` for `a < L`, assigns
`(adv t a) % 2 ^ w` to newly grown words `a ∈ [L, L + k)`, and sets `a ≥ L + k` to `0`. -/
def advGrowMem (w : ℕ) (adv : ℕ → ℕ → ℕ) (t L k : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  fun a =>
    if a < L then mem a
    else if a < L + k then (adv t a) % 2 ^ w
    else 0

/-- For every adversary `adv : ℕ → ℕ → ℕ` and step `t`, `advGrowMem` satisfies `DemonicGrow`. -/
theorem demonicGrow_advGrowMem (w : ℕ) (adv : ℕ → ℕ → ℕ) (t L k : ℕ) (mem : ℕ → ℕ) :
    DemonicGrow w L k mem (advGrowMem w adv t L k mem) := by
  refine ⟨fun a ha => ?_, fun a hlo hhi => ?_, fun a ha => ?_⟩
  · simp [advGrowMem, ha]
  · have hnot : ¬ (a < L) := by omega
    simp only [advGrowMem, hnot, ↓reduceIte, hhi]
    exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · have hnot1 : ¬ (a < L) := by omega
    have hnot2 : ¬ (a < L + k) := by omega
    simp [advGrowMem, hnot1, hnot2]

/-- Single step of clocked randomized execution of `p : RProgram B r` at word width `w` and step
index `t` under adversarial growth initializer `adv`. -/
def stepRandResizable (w : ℕ) (adv : ℕ → ℕ → ℕ) (p : RProgram B r) (t : ℕ) :
    RCfg r → ProbComp (RCfg r)
  | .running s =>
    match p[s.pc]? with
    | none => pure .faulted
    | some (.op o) =>
      match evalResizable w o s.data with
      | some x => pure (.running ⟨s.pc + 1, x⟩)
      | none => pure .faulted
    | some (.jump target) => pure (.running ⟨target, s.data⟩)
    | some (.branch c target) =>
      pure (.running ⟨if c.Holds s.data.toData then target else s.pc + 1, s.data⟩)
    | some (.halt i) => pure (.halted (s.data.regs i) s.data)
    | some (.rand dst src) =>
      if Fits w (s.data.regs src) then do
        let k ← ProbComp.unifFin (s.data.regs src)
        pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)
      else pure .faulted
    | some (.grow dst kReg) =>
      let k := s.data.regs kReg
      if Fits w (s.data.frontier + k) then
        let mem' := advGrowMem w adv t s.data.frontier k s.data.mem
        pure (.running ⟨s.pc + 1,
          ⟨Function.update s.data.regs dst s.data.frontier, mem', s.data.frontier + k⟩⟩)
      else pure .faulted
    | some (.shrink kReg) =>
      let k := s.data.regs kReg
      if k ≤ s.data.frontier then
        pure (.running ⟨s.pc + 1,
          ⟨s.data.regs, clear s.data.mem (s.data.frontier - k) k, s.data.frontier - k⟩⟩)
      else pure .faulted
  | cfg => pure cfg

/-- Clocked `T`-step randomized execution of a flat resizable Word-RAM program starting at step
offset `t₀`. -/
def runRandResizable (w : ℕ) (adv : ℕ → ℕ → ℕ) (p : RProgram B r) (t₀ : ℕ) :
    ℕ → RCfg r → ProbComp (RCfg r)
  | 0, cfg => pure cfg
  | T + 1, cfg => do
    let cfg' ← stepRandResizable w adv p t₀ cfg
    runRandResizable w adv p (t₀ + 1) T cfg'

/-! ## Structured resizable Word-RAM programs (`RCode`) and Demonic Execution (`RDemonicExec`) -/

/-- Structured programs of a word-granular resizable Word RAM: bounds-checked data instructions,
sequencing, conditionals, while loops, uniform random sampling (`rand`), demonic word-granular
`grow`, and word-granular `shrink`. -/
inductive RCode (B : Basis) (r : ℕ) where
  /-- Bounds-checked data instruction. -/
  | op (o : Op B r)
  /-- Sequential composition. -/
  | seq (c₁ c₂ : RCode B r)
  /-- Conditional branch on register comparison `c`. -/
  | branch (c : Cond r) (pos neg : RCode B r)
  /-- While loop on register comparison `c`. -/
  | loop (c : Cond r) (body : RCode B r)
  /-- Uniform random sample from `[0, regs src]` into `dst`. -/
  | rand (dst src : Fin r)
  /-- Grow the active prefix `[0, frontier)` by `regs kReg` words, storing the old `frontier` in
  `dst`. -/
  | grow (dst kReg : Fin r)
  /-- Shrink the active prefix `[0, frontier)` by `regs kReg ≤ frontier` words. -/
  | shrink (kReg : Fin r)
  deriving DecidableEq

namespace RCode

/-- Embed a standard structured `WordRAM.Code B r` into `RCode B r`. -/
def ofCode : Code B r → RCode B r
  | .op o => .op o
  | .seq c₁ c₂ => .seq (ofCode c₁) (ofCode c₂)
  | .branch c pos neg => .branch c (ofCode pos) (ofCode neg)
  | .loop c body => .loop c (ofCode body)
  | .rand dst src => .rand dst src

/-- Compiled flat instruction count of a structured `RCode B r`. -/
@[simp]
def size : RCode B r → ℕ
  | .op _ => 1
  | .seq c₁ c₂ => c₁.size + c₂.size
  | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3
  | .rand _ _ => 1
  | .grow _ _ => 1
  | .shrink _ => 1

end RCode

/-- Whether a structured `WordRAM.Code B r` uses only register instructions (no `load`, `store`, or
`rand`). -/
def IsRegOnlyCode : Code B r → Prop
  | .op o => IsRegOnlyOp o
  | .seq c₁ c₂ => IsRegOnlyCode c₁ ∧ IsRegOnlyCode c₂
  | .branch _ pos neg => IsRegOnlyCode pos ∧ IsRegOnlyCode neg
  | .loop _ body => IsRegOnlyCode body
  | .rand _ _ => False

instance decidableIsRegOnlyCode : (c : Code B r) → Decidable (IsRegOnlyCode c)
  | .op o => inferInstanceAs (Decidable (IsRegOnlyOp o))
  | .seq c₁ c₂ =>
    have := decidableIsRegOnlyCode c₁
    have := decidableIsRegOnlyCode c₂
    inferInstanceAs (Decidable (_ ∧ _))
  | .branch _ pos neg =>
    have := decidableIsRegOnlyCode pos
    have := decidableIsRegOnlyCode neg
    inferInstanceAs (Decidable (_ ∧ _))
  | .loop _ body => decidableIsRegOnlyCode body
  | .rand _ _ => isFalse id

/-- Big-step demonic execution judgment `RDemonicExec w c x T P`: at word width `w`, starting from
`x : RData r`, the structured resizable program `c : RCode B r` executes without faulting in at
most `T` instructions and establishes postcondition `P y` on the resulting state `y : RData r` for
**every** demonic choice of newly grown memory words (`DemonicGrow`) on `grow` instructions. -/
inductive RDemonicExec (w : ℕ) : RCode B r → RData r → ℕ → (RData r → Prop) → Prop where
  /-- A bounds-checked data instruction executes in `1` instruction. -/
  | op {o : Op B r} {x y : RData r} {P : RData r → Prop} :
      evalResizable w o x = some y → P y → RDemonicExec w (.op o) x 1 P
  /-- Growing by `x.regs kReg` words executes in `1` instruction when `Fits w (x.frontier + k)`,
  quantifying universally over all `mem'` satisfying `DemonicGrow w x.frontier k x.mem mem'`. -/
  | grow {dst kReg : Fin r} {x : RData r} {P : RData r → Prop} :
      Fits w (x.frontier + x.regs kReg) →
      (∀ mem', DemonicGrow w x.frontier (x.regs kReg) x.mem mem' →
        P ⟨Function.update x.regs dst x.frontier, mem', x.frontier + x.regs kReg⟩) →
      RDemonicExec w (.grow dst kReg) x 1 P
  /-- Shrinking by `x.regs kReg ≤ x.frontier` words executes in `1` instruction and clears the
  released suffix. -/
  | shrink {kReg : Fin r} {x : RData r} {P : RData r → Prop} :
      x.regs kReg ≤ x.frontier →
      P ⟨x.regs, clear x.mem (x.frontier - x.regs kReg) (x.regs kReg),
        x.frontier - x.regs kReg⟩ →
      RDemonicExec w (.shrink kReg) x 1 P
  /-- Sampling uniformly from `[0, x.regs src]` executes in `1` instruction when
  `Fits w (x.regs src)`. -/
  | rand {dst src : Fin r} {x : RData r} {P : RData r → Prop} :
      Fits w (x.regs src) →
      (∀ v ≤ x.regs src, P (x.set dst v)) →
      RDemonicExec w (.rand dst src) x 1 P
  /-- Sequential composition adds the instruction bounds. -/
  | seq {c₁ c₂ : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      RDemonicExec w c₁ x T₁ Q →
      (∀ y, Q y → RDemonicExec w c₂ y T₂ P) →
      RDemonicExec w (.seq c₁ c₂) x (T₁ + T₂) P
  /-- Positive branch of a conditional adds `1` branch instruction. -/
  | branch_pos {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ}
      {P : RData r → Prop} :
      c.Holds x.toData → RDemonicExec w pos x T P →
      RDemonicExec w (.branch c pos neg) x (T + 1) P
  /-- Negative branch of a conditional adds `2` instructions (branch + jump). -/
  | branch_neg {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ}
      {P : RData r → Prop} :
      ¬c.Holds x.toData → RDemonicExec w neg x T P →
      RDemonicExec w (.branch c pos neg) x (T + 2) P
  /-- Exiting a while loop takes `2` instructions. -/
  | loop_exit {c : Cond r} {body : RCode B r} {x : RData r} {P : RData r → Prop} :
      ¬c.Holds x.toData → P x →
      RDemonicExec w (.loop c body) x 2 P
  /-- One iteration of a while loop followed by the rest of the loop adds `T₁ + T₂ + 2`
  instructions. -/
  | loop_iter {c : Cond r} {body : RCode B r} {x : RData r} {T₁ T₂ : ℕ}
      {Q P : RData r → Prop} :
      c.Holds x.toData →
      RDemonicExec w body x T₁ Q →
      (∀ y, Q y → RDemonicExec w (.loop c body) y T₂ P) →
      RDemonicExec w (.loop c body) x (T₁ + T₂ + 2) P
  /-- Weakening the instruction bound and postcondition. -/
  | mono {c : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      RDemonicExec w c x T₁ Q → T₁ ≤ T₂ → (∀ y, Q y → P y) →
      RDemonicExec w c x T₂ P

namespace RDemonicExec

variable {w : ℕ} {x y : RData r} {P Q : RData r → Prop}

/-- Sequencing when the first subprogram has a deterministic post-state `y`. -/
theorem seq_eq {c₁ c₂ : RCode B r} {T₁ T₂ : ℕ}
    (h₁ : RDemonicExec w c₁ x T₁ (· = y))
    (h₂ : RDemonicExec w c₂ y T₂ P) :
    RDemonicExec w (.seq c₁ c₂) x (T₁ + T₂) P :=
  h₁.seq fun _ h => h ▸ h₂

/-- Setting register `d` to a fitting constant `v` takes `1` instruction. -/
theorem const {d : Fin r} {v : ℕ} (h : Fits w v) :
    RDemonicExec (B := B) w (.op (.const d v)) x 1 (· = x.set d v) :=
  .op (RData.put_of_fits h) rfl

/-- Copying register `s` into `d` takes `1` instruction. -/
theorem copy {d s : Fin r} :
    RDemonicExec (B := B) w (.op (.copy d s)) x 1 (· = x.set d (x.regs s)) :=
  .op rfl rfl

/-- Executing a standard binary operation whose result fits in `w` bits takes `1` instruction. -/
theorem bin {f : BinOp} {d i j : Fin r} (h : Fits w (f.eval (x.regs i) (x.regs j))) :
    RDemonicExec w (.op (.bin f d i j)) x 1 (· = x.set d (f.eval (x.regs i) (x.regs j))) :=
  .op (RData.put_of_fits h) rfl

/-- Reading the word width `w` into register `d` takes `1` instruction. -/
theorem width {d : Fin r} :
    RDemonicExec w (.op (.width d)) x 1 (· = x.set d w) :=
  .op (RData.put_of_fits (fits_self w)) rfl

/-- Loading from memory address `x.regs a < x.frontier` into `d` takes `1` instruction. -/
theorem load {d a : Fin r} (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w (.op (.load d a)) x 1 (· = x.set d (x.mem (x.regs a))) :=
  .op (by simp [evalResizable, ha]) rfl

/-- Storing `x.regs s` to memory address `x.regs a < x.frontier` takes `1` instruction. -/
theorem store {a s : Fin r} (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w (.op (.store a s)) x 1 (· = x.write (x.regs a) (x.regs s)) :=
  .op (by simp [evalResizable, ha]) rfl

/-- Any register-only `WordRAM.Exec w c x.toData y n` lifts directly to `RDemonicExec` on
`RCode.ofCode c` with the same instruction count `n` and unchanged `frontier`. -/
theorem of_exec_regOnly {c : Code B r} {x : RData r} {y : Data r} {n : ℕ}
    (hc : IsRegOnlyCode c) (h : Exec w c x.toData y n) :
    RDemonicExec w (RCode.ofCode c) x n (· = ⟨y.regs, y.mem, x.frontier⟩) := by
  generalize hx : x.toData = x₀ at h
  induction h generalizing x with
  | op ho =>
    subst hx
    refine .op ?_ rfl
    rw [evalResizable_of_isRegOnly hc, ho]
    rfl
  | seq _ _ ih₁ ih₂ =>
    subst hx
    exact (ih₁ hc.1 rfl).seq_eq (ih₂ hc.2 rfl)
  | branch_pos hcond _ ih =>
    subst hx
    exact .branch_pos hcond (ih hc.1 rfl)
  | branch_neg hcond _ ih =>
    subst hx
    exact .branch_neg hcond (ih hc.2 rfl)
  | loop_exit hcond =>
    subst hx
    exact .loop_exit hcond (by cases x; rfl)
  | loop_iter hcond _ _ ihb ihl =>
    subst hx
    refine .loop_iter hcond (ihb hc rfl) ?_
    rintro _ rfl
    exact ihl hc rfl

end RDemonicExec

/-! ## Concrete `WordRAM` machine procedures for sub-word bit-packing (`r = 16`) -/

/-- Register `0`: operation selector tag (`0 = append`, `1 = pop`, `2 = read`, `3 = write`). -/
abbrev regOp : Fin 16 := 0
/-- Register `1`: item index `i` (or current length `n`). -/
abbrev regIdx : Fin 16 := 1
/-- Register `2`: item value `x` (input to `append`/`write`, output of `read`/`pop`). -/
abbrev regVal : Fin 16 := 2
/-- Register `3`: secondary return flag (`1` if `pop` returned `some`, `0` if empty). -/
abbrev regRet : Fin 16 := 3
/-- Register `4`: base word address of the packed array (`1` with length header, `0` without). -/
abbrev regBase : Fin 16 := 4
/-- Register `5`: item bit-width `b` (`0 < b ≤ w`). -/
abbrev regB : Fin 16 := 5
/-- Register `6`: machine word width `w`. -/
abbrev regW : Fin 16 := 6
/-- Register `7`: target word index / address. -/
abbrev regWordIdx : Fin 16 := 7
/-- Register `8`: in-word bit offset `off`. -/
abbrev regOff : Fin 16 := 8
/-- Register `9`: bit-slice length `len`. -/
abbrev regLen : Fin 16 := 9
/-- Register `10`: loaded or spliced `w`-bit memory word. -/
abbrev regWord : Fin 16 := 10
/-- Register `11`: extracted slice or slice input to `spliceWordCode`. -/
abbrev regSlice : Fin 16 := 11
/-- Register `12`: low slice length `lowLen = w - inWordOff`. -/
abbrev regLow : Fin 16 := 12
/-- Register `13`: computed bitmask `wordMask len = 2 ^ len - 1`. -/
abbrev regMask : Fin 16 := 13
/-- Register `14`: scratch register 1. -/
abbrev regTmp1 : Fin 16 := 14
/-- Register `15`: scratch register 2. -/
abbrev regTmp2 : Fin 16 := 15

/-- Compute `regMask ← wordMask (regs regLen) = 2 ^ len - 1` in `5` `WordRAM` instructions without
overflowing when `1 ≤ len ≤ w`. -/
def wordMaskCode : Code .standard 16 := ram[
  regTmp1 ← #1;
  regTmp2 ← regLen - regTmp1;
  regTmp2 ← regTmp1 <<< regTmp2;
  regTmp1 ← regTmp2 - regTmp1;
  regMask ← regTmp1 + regTmp2
]

/-- Exact 5-instruction execution of `wordMaskCode` when `0 < x.regs regLen` and
`x.regs regLen ≤ w`. -/
theorem wordMaskCode_exec {w : ℕ} {x : Data 16}
    (hlen_pos : 0 < x.regs regLen) (hlen : x.regs regLen ≤ w) :
    ∃ y : Data 16,
      Exec w wordMaskCode x y 5 ∧
        y.mem = x.mem ∧
        y.regs regMask = wordMask (x.regs regLen) ∧
        (∀ r : Fin 16, r.val < 13 → y.regs r = x.regs r) := by
  have hw_ne : w ≠ 0 := by omega
  have h1 : Fits w 1 := fits_one hw_ne
  obtain ⟨hf_lm1, hf_half, hf_low, hf_mask⟩ := wordMask_intermediates_fit hlen_pos hlen
  set len := x.regs regLen
  set x₁ := x.set regTmp1 1
  set x₂ := x₁.set regTmp2 (len - 1)
  set x₃ := x₂.set regTmp2 (1 <<< (len - 1))
  set x₄ := x₃.set regTmp1 ((1 <<< (len - 1)) - 1)
  set x₅ := x₄.set regMask (wordMask len)
  have e₁ : Exec (B := .standard) w (.op (.const regTmp1 1)) x x₁ 1 := Exec.const h1
  have e₂ : Exec w (.op (.bin .sub regTmp2 regLen regTmp1)) x₁ x₂ 1 := by
    have hsub : BinOp.sub.eval (x₁.regs regLen) (x₁.regs regTmp1) = len - 1 := rfl
    rw [show x₂ = x₁.set regTmp2 (BinOp.sub.eval (x₁.regs regLen) (x₁.regs regTmp1)) by
      rw [hsub]]
    exact Exec.bin (by rw [hsub]; exact hf_lm1)
  have e₃ : Exec w (.op (.bin .shiftLeft regTmp2 regTmp1 regTmp2)) x₂ x₃ 1 := by
    have hsh : BinOp.shiftLeft.eval (x₂.regs regTmp1) (x₂.regs regTmp2) = 1 <<< (len - 1) := rfl
    rw [show x₃ = x₂.set regTmp2 (BinOp.shiftLeft.eval (x₂.regs regTmp1) (x₂.regs regTmp2)) by
      rw [hsh]]
    exact Exec.bin (by rw [hsh]; exact hf_half)
  have e₄ : Exec w (.op (.bin .sub regTmp1 regTmp2 regTmp1)) x₃ x₄ 1 := by
    have hsub : BinOp.sub.eval (x₃.regs regTmp2) (x₃.regs regTmp1) = (1 <<< (len - 1)) - 1 := rfl
    rw [show x₄ = x₃.set regTmp1 (BinOp.sub.eval (x₃.regs regTmp2) (x₃.regs regTmp1)) by
      rw [hsub]]
    exact Exec.bin (by rw [hsub]; exact hf_low)
  have e₅ : Exec w (.op (.bin .add regMask regTmp1 regTmp2)) x₄ x₅ 1 := by
    have hadd : BinOp.add.eval (x₄.regs regTmp1) (x₄.regs regTmp2) = wordMask len := rfl
    rw [show x₅ = x₄.set regMask (BinOp.add.eval (x₄.regs regTmp1) (x₄.regs regTmp2)) by
      rw [hadd]]
    exact Exec.bin (by rw [hadd]; exact hf_mask)
  refine ⟨x₅, e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))), rfl, rfl, ?_⟩
  intro r hr
  obtain ⟨hne13, hne14, hne15⟩ :=
    (by decide : ∀ k : Fin 16, k.val < 13 → k ≠ regMask ∧ k ≠ regTmp1 ∧ k ≠ regTmp2) r hr
  simp [x₅, x₄, x₃, x₂, x₁, Function.update_of_ne hne13,
    Function.update_of_ne hne14, Function.update_of_ne hne15]

/-- Extract `regs regLen` bits at offset `regs regOff` from `regs regWord` into `regSlice` in `7`
`WordRAM` instructions. -/
def extractSliceCode : Code .standard 16 := ram[
  ⟪wordMaskCode⟫;
  regTmp1 ← regWord >>> regOff;
  regSlice ← regTmp1 &&& regMask
]

/-- Exact 7-instruction execution of `extractSliceCode`: sets `regSlice` to
`extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen)` and preserves all registers
`< 11` and `regLow` (`12`) as well as `x.mem`. -/
theorem extractSliceCode_exec {w : ℕ} {x : Data 16}
    (hword : Fits w (x.regs regWord))
    (hlen_pos : 0 < x.regs regLen) (hlen : x.regs regLen ≤ w) :
    ∃ y : Data 16,
      Exec w extractSliceCode x y 7 ∧
        y.mem = x.mem ∧
        y.regs regSlice = extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen) ∧
        Fits w (y.regs regSlice) ∧
        (∀ r : Fin 16, r.val < 11 ∨ r = regLow → y.regs r = x.regs r) := by
  obtain ⟨x₁, emask, hx₁_mem, hx₁_mask, hx₁_pres⟩ :=
    wordMaskCode_exec (w := w) (x := x) hlen_pos hlen
  have hx₁_word : x₁.regs regWord = x.regs regWord := hx₁_pres regWord (by decide)
  have hx₁_off : x₁.regs regOff = x.regs regOff := hx₁_pres regOff (by decide)
  have hsh_fits : Fits w (x.regs regWord >>> x.regs regOff) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact hword.of_le (Nat.div_le_self _ _)
  set x₂ := x₁.set regTmp1 (x.regs regWord >>> x.regs regOff)
  have e₂ : Exec w (.op (.bin .shiftRight regTmp1 regWord regOff)) x₁ x₂ 1 := by
    have hev : BinOp.shiftRight.eval (x₁.regs regWord) (x₁.regs regOff) =
        x.regs regWord >>> x.regs regOff := by
      change x₁.regs regWord >>> x₁.regs regOff = _
      rw [hx₁_word, hx₁_off]
    rw [show x₂ = x₁.set regTmp1 (BinOp.shiftRight.eval (x₁.regs regWord) (x₁.regs regOff)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hsh_fits)
  have hand_eq : (x.regs regWord >>> x.regs regOff) &&& wordMask (x.regs regLen) =
      extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen) :=
    (extractSlice_eq_bitops (x.regs regWord) (x.regs regOff) hlen_pos).symm
  have hslice_fits : Fits w (extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen)) :=
    (extractSlice_fits _ _ _).mono hlen
  set x₃ := x₂.set regSlice (extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen))
  have e₃ : Exec w (.op (.bin .and regSlice regTmp1 regMask)) x₂ x₃ 1 := by
    have hev : BinOp.and.eval (x₂.regs regTmp1) (x₂.regs regMask) =
        extractSlice (x.regs regWord) (x.regs regOff) (x.regs regLen) := by
      change (x.regs regWord >>> x.regs regOff) &&& x₁.regs regMask = _
      rw [hx₁_mask, hand_eq]
    rw [show x₃ = x₂.set regSlice (BinOp.and.eval (x₂.regs regTmp1) (x₂.regs regMask)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hslice_fits)
  refine ⟨x₃, emask.seq (e₂.seq e₃), hx₁_mem, rfl, hslice_fits, ?_⟩
  intro r hr
  obtain ⟨hlt13, hne11, hne14⟩ :=
    (by decide : ∀ k : Fin 16, (k.val < 11 ∨ k = regLow) →
      k.val < 13 ∧ k ≠ regSlice ∧ k ≠ regTmp1) r hr
  simp [x₃, x₂, Function.update_of_ne hne11, Function.update_of_ne hne14, hx₁_pres r hlt13]

/-- Splice the low `regs regLen` bits of `regs regSlice` into `regs regWord` at bit offset
`regs regOff` in `11` `WordRAM` instructions. -/
def spliceWordCode : Code .standard 16 := ram[
  ⟪wordMaskCode⟫;
  regTmp1 ← regMask <<< regOff;
  regTmp1 ← regWord &&& regTmp1;
  regWord ← regWord ^^^ regTmp1;
  regTmp2 ← regSlice &&& regMask;
  regTmp2 ← regTmp2 <<< regOff;
  regWord ← regWord ||| regTmp2
]

/-- Exact 11-instruction execution of `spliceWordCode`: sets `regWord` to
`spliceWord w (x.regs regWord) (x.regs regOff) (x.regs regLen) (x.regs regSlice)` and preserves all
registers `< 10` as well as `regSlice` (`11`), `regLow` (`12`), and `x.mem`. -/
theorem spliceWordCode_exec {w : ℕ} {x : Data 16}
    (hword : Fits w (x.regs regWord))
    (hlen_pos : 0 < x.regs regLen) (hfit : x.regs regOff + x.regs regLen ≤ w) :
    ∃ y : Data 16,
      Exec w spliceWordCode x y 11 ∧
        y.mem = x.mem ∧
        y.regs regWord =
          spliceWord w (x.regs regWord) (x.regs regOff) (x.regs regLen) (x.regs regSlice) ∧
        Fits w (y.regs regWord) ∧
        (∀ r : Fin 16, r.val < 10 ∨ r = regSlice ∨ r = regLow → y.regs r = x.regs r) := by
  have hlen : x.regs regLen ≤ w := by omega
  obtain ⟨x₁, emask, hx₁_mem, hx₁_mask, hx₁_pres⟩ :=
    wordMaskCode_exec (w := w) (x := x) hlen_pos hlen
  have hx₁_word : x₁.regs regWord = x.regs regWord := hx₁_pres regWord (by decide)
  have hx₁_off : x₁.regs regOff = x.regs regOff := hx₁_pres regOff (by decide)
  have hx₁_slice : x₁.regs regSlice = x.regs regSlice := hx₁_pres regSlice (by decide)
  obtain ⟨hf_sMask, hf_vMask, hf_sVal, hf_wAnd, hf_wXor, hf_wOr, hsplice_eq⟩ :=
    spliceWord_eq_bitops (val := x.regs regSlice) hword hlen_pos hfit
  set mask := wordMask (x.regs regLen)
  set sMask := mask <<< x.regs regOff
  set wAnd := x.regs regWord &&& sMask
  set wXor := x.regs regWord ^^^ wAnd
  set vMask := x.regs regSlice &&& mask
  set sVal := vMask <<< x.regs regOff
  set res := wXor ||| sVal
  set x₂ := x₁.set regTmp1 sMask
  set x₃ := x₂.set regTmp1 wAnd
  set x₄ := x₃.set regWord wXor
  set x₅ := x₄.set regTmp2 vMask
  set x₆ := x₅.set regTmp2 sVal
  set x₇ := x₆.set regWord res
  have e₂ : Exec w (.op (.bin .shiftLeft regTmp1 regMask regOff)) x₁ x₂ 1 := by
    have hev : BinOp.shiftLeft.eval (x₁.regs regMask) (x₁.regs regOff) = sMask := by
      change x₁.regs regMask <<< x₁.regs regOff = _
      rw [hx₁_mask, hx₁_off]
    rw [show x₂ = x₁.set regTmp1 (BinOp.shiftLeft.eval (x₁.regs regMask) (x₁.regs regOff)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_sMask)
  have e₃ : Exec w (.op (.bin .and regTmp1 regWord regTmp1)) x₂ x₃ 1 := by
    have hev : BinOp.and.eval (x₂.regs regWord) (x₂.regs regTmp1) = wAnd := by
      change x₁.regs regWord &&& sMask = wAnd
      rw [hx₁_word]
    rw [show x₃ = x₂.set regTmp1 (BinOp.and.eval (x₂.regs regWord) (x₂.regs regTmp1)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_wAnd)
  have e₄ : Exec w (.op (.bin .xor regWord regWord regTmp1)) x₃ x₄ 1 := by
    have hev : BinOp.xor.eval (x₃.regs regWord) (x₃.regs regTmp1) = wXor := by
      change x₁.regs regWord ^^^ wAnd = wXor
      rw [hx₁_word]
    rw [show x₄ = x₃.set regWord (BinOp.xor.eval (x₃.regs regWord) (x₃.regs regTmp1)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_wXor)
  have e₅ : Exec w (.op (.bin .and regTmp2 regSlice regMask)) x₄ x₅ 1 := by
    have hev : BinOp.and.eval (x₄.regs regSlice) (x₄.regs regMask) = vMask := by
      change x₁.regs regSlice &&& x₁.regs regMask = vMask
      rw [hx₁_slice, hx₁_mask]
    rw [show x₅ = x₄.set regTmp2 (BinOp.and.eval (x₄.regs regSlice) (x₄.regs regMask)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_vMask)
  have e₆ : Exec w (.op (.bin .shiftLeft regTmp2 regTmp2 regOff)) x₅ x₆ 1 := by
    have hev : BinOp.shiftLeft.eval (x₅.regs regTmp2) (x₅.regs regOff) = sVal := by
      change vMask <<< x₁.regs regOff = sVal
      rw [hx₁_off]
    rw [show x₆ = x₅.set regTmp2 (BinOp.shiftLeft.eval (x₅.regs regTmp2) (x₅.regs regOff)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_sVal)
  have e₇ : Exec w (.op (.bin .or regWord regWord regTmp2)) x₆ x₇ 1 := by
    have hev : BinOp.or.eval (x₆.regs regWord) (x₆.regs regTmp2) = res := rfl
    rw [show x₇ = x₆.set regWord (BinOp.or.eval (x₆.regs regWord) (x₆.regs regTmp2)) by
      rw [hev]]
    exact Exec.bin (by rw [hev]; exact hf_wOr)
  refine ⟨x₇, emask.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq e₇))))),
    hx₁_mem, hsplice_eq.symm, hf_wOr, ?_⟩
  intro r hr
  obtain ⟨hlt13, hne10, hne14, hne15⟩ :=
    (by decide : ∀ k : Fin 16, (k.val < 10 ∨ k = regSlice ∨ k = regLow) →
      k.val < 13 ∧ k ≠ regWord ∧ k ≠ regTmp1 ∧ k ≠ regTmp2) r hr
  simp [x₇, x₆, x₅, x₄, x₃, x₂, Function.update_of_ne hne10,
    Function.update_of_ne hne14, Function.update_of_ne hne15, hx₁_pres r hlt13]

/-- Address/offset setup header for `readSubwordCode` and `writeSubwordCode` (`6` instructions):
loads `w` into `regW`, computes `bitOff = i * b`, `wordIdx = bitOff / w`, `inWordOff = bitOff % w`,
`addr0 = base + wordIdx` in `regWordIdx`, and `lowLen = w - inWordOff` in `regLow`. -/
def subwordHeaderCode : Code .standard 16 := ram[
  regW ← width%;
  regTmp1 ← regIdx * regB;
  regWordIdx ← regTmp1 / regW;
  regOff ← regTmp1 % regW;
  regWordIdx ← regBase + regWordIdx;
  regLow ← regW - regOff
]

/-- Exact 6-instruction execution of `subwordHeaderCode`. -/
theorem subwordHeaderCode_exec {w : ℕ} {x : Data 16}
    (hw : 0 < w)
    (hbitOff : Fits w (x.regs regIdx * x.regs regB))
    (haddr : Fits w (x.regs regBase + (x.regs regIdx * x.regs regB) / w)) :
    let bitOff := x.regs regIdx * x.regs regB
    let wordIdx := bitOff / w
    let inWordOff := bitOff % w
    let lowLen := w - inWordOff
    ∃ y : Data 16,
      Exec w subwordHeaderCode x y 6 ∧
        y.mem = x.mem ∧
        y.regs regW = w ∧
        y.regs regWordIdx = x.regs regBase + wordIdx ∧
        y.regs regOff = inWordOff ∧
        y.regs regLow = lowLen ∧
        (∀ r : Fin 16, r.val < 6 → y.regs r = x.regs r) := by
  intro bitOff wordIdx inWordOff lowLen
  have hwordIdx_fits : Fits w wordIdx := hbitOff.of_le (Nat.div_le_self _ _)
  have hinWordOff_fits : Fits w inWordOff := (fits_self w).of_le (le_of_lt (Nat.mod_lt _ hw))
  have hlowLen_fits : Fits w lowLen := (fits_self w).of_le (Nat.sub_le _ _)
  set x₁ := x.set regW w
  set x₂ := x₁.set regTmp1 bitOff
  set x₃ := x₂.set regWordIdx wordIdx
  set x₄ := x₃.set regOff inWordOff
  set x₅ := x₄.set regWordIdx (x.regs regBase + wordIdx)
  set x₆ := x₅.set regLow lowLen
  have e₁ : Exec w (.op (.width regW)) x x₁ 1 := Exec.width
  have e₂ : Exec w (.op (.bin .mul regTmp1 regIdx regB)) x₁ x₂ 1 := Exec.bin hbitOff
  have e₃ : Exec w (.op (.bin .div regWordIdx regTmp1 regW)) x₂ x₃ 1 := Exec.bin hwordIdx_fits
  have e₄ : Exec w (.op (.bin .mod regOff regTmp1 regW)) x₃ x₄ 1 := Exec.bin hinWordOff_fits
  have e₅ : Exec w (.op (.bin .add regWordIdx regBase regWordIdx)) x₄ x₅ 1 := Exec.bin haddr
  have e₆ : Exec w (.op (.bin .sub regLow regW regOff)) x₅ x₆ 1 := Exec.bin hlowLen_fits
  refine ⟨x₆, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆)))), rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r hr
  obtain ⟨hne6, hne7, hne8, hne12, hne14⟩ :=
    (by decide : ∀ k : Fin 16, k.val < 6 →
      k ≠ regW ∧ k ≠ regWordIdx ∧ k ≠ regOff ∧ k ≠ regLow ∧ k ≠ regTmp1) r hr
  simp [x₆, x₅, x₄, x₃, x₂, x₁, Function.update_of_ne hne6, Function.update_of_ne hne7,
    Function.update_of_ne hne8, Function.update_of_ne hne12, Function.update_of_ne hne14]

/-- Concrete structured `RCode .standard 16` procedure that reads the `b`-bit item at index
`regs regIdx` from the packed array starting at word address `regs regBase` into `regVal` in at
most `31` instructions. -/
def readSubwordCode : RCode .standard 16 :=
  .seq (RCode.ofCode subwordHeaderCode) <|
  .branch (.lt regLow regB)
    -- Cross-word branch (`w - inWordOff < b`, i.e., `¬ (inWordOff + b ≤ w)`):
    (.seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.copy regLen regLow)) <|
     .seq (RCode.ofCode extractSliceCode) <|
     .seq (.op (.copy regVal regSlice)) <|
     .seq (.op (.const regTmp1 1)) <|
     .seq (.op (.bin .add regWordIdx regWordIdx regTmp1)) <|
     .seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.const regOff 0)) <|
     .seq (.op (.bin .sub regLen regB regLow)) <|
     .seq (RCode.ofCode extractSliceCode) <|
     .seq (.op (.bin .shiftLeft regTmp1 regSlice regLow)) <|
          (.op (.bin .or regVal regVal regTmp1)))
    -- Single-word branch (`inWordOff + b ≤ w`):
    (.seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.copy regLen regB)) <|
     .seq (RCode.ofCode extractSliceCode) <|
          (.op (.copy regVal regSlice)))

/-- `readSubwordCode` executes in at most `31` instructions on `RData 16`, leaves `mem` and
`frontier` unchanged, preserves `regOp`, `regIdx`, `regRet`, `regBase`, `regB`, and sets
`regVal` to `readSubword w (fun a => x.mem (x.regs regBase + a)) (x.regs regB) (x.regs regIdx)`. -/
theorem readSubwordCode_exec {w n : ℕ} {x : RData 16}
    (hx : x.Bounded w)
    (hb_pos : 0 < x.regs regB) (hb : x.regs regB ≤ w)
    (hi : x.regs regIdx < n)
    (hbitOff : Fits w (x.regs regIdx * x.regs regB))
    (hfront : x.regs regBase + packedWords w (x.regs regB) n ≤ x.frontier) :
    RDemonicExec w readSubwordCode x 31 fun y =>
      y.Bounded w ∧
        y.mem = x.mem ∧
        y.frontier = x.frontier ∧
        y.regs regVal =
          readSubword w (fun a => x.mem (x.regs regBase + a)) (x.regs regB) (x.regs regIdx) ∧
        y.regs regOp = x.regs regOp ∧
        y.regs regIdx = x.regs regIdx ∧
        y.regs regRet = x.regs regRet ∧
        y.regs regBase = x.regs regBase ∧
        y.regs regB = x.regs regB := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  have hw_ne : w ≠ 0 := by omega
  set base := x.regs regBase
  set b := x.regs regB
  set i := x.regs regIdx
  set bitOff := i * b
  set wordIdx := bitOff / w
  set inWordOff := bitOff % w
  set lowLen := w - inWordOff
  have hmod : inWordOff < w := Nat.mod_lt _ hw
  have hw0_lt : wordIdx < packedWords w b n := wordIdx_lt_packedWords_of_pos hw hb_pos hi
  have haddr0_lt : base + wordIdx < x.frontier :=
    lt_of_lt_of_le (Nat.add_lt_add_left hw0_lt base) hfront
  have haddr0_fits : Fits w (base + wordIdx) := hx.frontier_fits.of_le (le_of_lt haddr0_lt)
  obtain ⟨d₀, hd₀_exec, hd₀_mem, hd₀_w, hd₀_widx, hd₀_off, hd₀_low, hd₀_pres⟩ :=
    subwordHeaderCode_exec (x := x.toData) hw hbitOff haddr0_fits
  have e_hdr : RDemonicExec w (RCode.ofCode subwordHeaderCode) x 6
      (· = ⟨d₀.regs, d₀.mem, x.frontier⟩) :=
    RDemonicExec.of_exec_regOnly (by decide) hd₀_exec
  set x₀ : RData 16 := ⟨d₀.regs, d₀.mem, x.frontier⟩
  have hx₀_mem : x₀.mem = x.mem := hd₀_mem
  have hx₀_widx : x₀.regs regWordIdx = base + wordIdx := hd₀_widx
  have hx₀_off : x₀.regs regOff = inWordOff := hd₀_off
  have hx₀_low : x₀.regs regLow = lowLen := hd₀_low
  have hx₀_b : x₀.regs regB = b := hd₀_pres regB (by decide)
  have hx₀_base : x₀.regs regBase = base := hd₀_pres regBase (by decide)
  have hx₀_idx : x₀.regs regIdx = i := hd₀_pres regIdx (by decide)
  have hx₀_op : x₀.regs regOp = x.regs regOp := hd₀_pres regOp (by decide)
  have hx₀_ret : x₀.regs regRet = x.regs regRet := hd₀_pres regRet (by decide)
  by_cases hsplit : lowLen < b
  · -- Cross-word branch (`lowLen < b`, i.e., `¬ (inWordOff + b ≤ w)`):
    have hnot_fit : ¬ (inWordOff + b ≤ w) := by omega
    have hcond : (Cond.lt regLow regB).Holds x₀.toData := by
      change d₀.regs regLow < x₀.regs regB
      rw [hd₀_low, hx₀_b]
      exact hsplit
    have hlow_pos : 0 < lowLen := by omega
    have hlow_le_w : lowLen ≤ w := by omega
    have hlow_le_b : lowLen ≤ b := le_of_lt hsplit
    have hhigh_pos : 0 < b - lowLen := by omega
    have hhigh_le_w : b - lowLen ≤ w := by omega
    have hw1_lt : wordIdx + 1 < packedWords w b n :=
      wordIdx_succ_lt_packedWords hw hi hnot_fit
    have haddr1_lt : base + wordIdx + 1 < x.frontier := by
      have := lt_of_lt_of_le (Nat.add_lt_add_left hw1_lt base) hfront
      omega
    have haddr1_fits : Fits w (base + wordIdx + 1) :=
      hx.frontier_fits.of_le (le_of_lt haddr1_lt)
    set x₁ := x₀.set regWord (x.mem (base + wordIdx))
    have e₁ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₀ 1 (· = x₁) := by
      rw [show x₁ = x₀.set regWord (x₀.mem (x₀.regs regWordIdx)) by
        rw [hx₀_mem, hx₀_widx]]
      exact RDemonicExec.load (by rw [hx₀_widx]; exact haddr0_lt)
    set x₂ := x₁.set regLen lowLen
    have e₂ : RDemonicExec (B := .standard) w (.op (.copy regLen regLow)) x₁ 1 (· = x₂) := by
      rw [show x₂ = x₁.set regLen (x₁.regs regLow) by
        change x₁.set regLen lowLen = x₁.set regLen (x₀.regs regLow)
        rw [hx₀_low]]
      exact RDemonicExec.copy
    obtain ⟨d₃, hd₃_exec, hd₃_mem, hd₃_slice, hd₃_fits, hd₃_pres⟩ :=
      extractSliceCode_exec (w := w) (x := x₂.toData)
        (by exact hx.mem_fits (base + wordIdx))
        hlow_pos
        hlow_le_w
    set x₃ : RData 16 := ⟨d₃.regs, d₃.mem, x.frontier⟩
    have e₃ : RDemonicExec w (RCode.ofCode extractSliceCode) x₂ 7 (· = x₃) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₃_exec
    set lowPart := extractSlice (x.mem (base + wordIdx)) inWordOff lowLen
    have hx₃_slice : x₃.regs regSlice = lowPart := by
      change d₃.regs regSlice = extractSlice (x.mem (base + wordIdx)) inWordOff lowLen
      rw [← hx₀_off]
      exact hd₃_slice
    set x₄ := x₃.set regVal lowPart
    have e₄ : RDemonicExec (B := .standard) w (.op (.copy regVal regSlice)) x₃ 1 (· = x₄) := by
      rw [show x₄ = x₃.set regVal (x₃.regs regSlice) by rw [hx₃_slice]]
      exact RDemonicExec.copy
    set x₅ := x₄.set regTmp1 1
    have e₅ : RDemonicExec (B := .standard) w (.op (.const regTmp1 1)) x₄ 1 (· = x₅) :=
      RDemonicExec.const (fits_one hw_ne)
    set x₆ := x₅.set regWordIdx (base + wordIdx + 1)
    have hx₅_widx : x₅.regs regWordIdx = base + wordIdx :=
      (hd₃_pres regWordIdx (Or.inl (by decide))).trans hx₀_widx
    have e₆ : RDemonicExec w (.op (.bin .add regWordIdx regWordIdx regTmp1)) x₅ 1 (· = x₆) := by
      have hev : BinOp.add.eval (x₅.regs regWordIdx) (x₅.regs regTmp1) = base + wordIdx + 1 := by
        change x₅.regs regWordIdx + 1 = _
        rw [hx₅_widx]
      rw [show x₆ = x₅.set regWordIdx (BinOp.add.eval (x₅.regs regWordIdx) (x₅.regs regTmp1)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact haddr1_fits)
    have hx₆_mem : x₆.mem = x.mem := by
      simpa [x₆, x₅, x₄, x₃, hd₃_mem, x₂, x₁] using hx₀_mem
    set x₇ := x₆.set regWord (x.mem (base + wordIdx + 1))
    have e₇ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₆ 1 (· = x₇) := by
      rw [show x₇ = x₆.set regWord (x₆.mem (x₆.regs regWordIdx)) by
        rw [hx₆_mem]; rfl]
      exact RDemonicExec.load haddr1_lt
    set x₈ := x₇.set regOff 0
    have e₈ : RDemonicExec (B := .standard) w (.op (.const regOff 0)) x₇ 1 (· = x₈) :=
      RDemonicExec.const (fits_zero w)
    set x₉ := x₈.set regLen (b - lowLen)
    have hx₈_b : x₈.regs regB = b :=
      (hd₃_pres regB (Or.inl (by decide))).trans hx₀_b
    have hx₈_low : x₈.regs regLow = lowLen :=
      (hd₃_pres regLow (Or.inr rfl)).trans hx₀_low
    have e₉ : RDemonicExec w (.op (.bin .sub regLen regB regLow)) x₈ 1 (· = x₉) := by
      have hev : BinOp.sub.eval (x₈.regs regB) (x₈.regs regLow) = b - lowLen := by
        change x₈.regs regB - x₈.regs regLow = _
        rw [hx₈_b, hx₈_low]
      rw [show x₉ = x₈.set regLen (BinOp.sub.eval (x₈.regs regB) (x₈.regs regLow)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact (fits_self w).of_le hhigh_le_w)
    obtain ⟨d₁₀, hd₁₀_exec, hd₁₀_mem, hd₁₀_slice, hd₁₀_fits, hd₁₀_pres⟩ :=
      extractSliceCode_exec (w := w) (x := x₉.toData)
        (by exact hx.mem_fits (base + wordIdx + 1))
        hhigh_pos
        hhigh_le_w
    set x₁₀ : RData 16 := ⟨d₁₀.regs, d₁₀.mem, x.frontier⟩
    have e₁₀ : RDemonicExec w (RCode.ofCode extractSliceCode) x₉ 7 (· = x₁₀) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₁₀_exec
    set highPart := extractSlice (x.mem (base + wordIdx + 1)) 0 (b - lowLen)
    have hx₁₀_slice : x₁₀.regs regSlice = highPart := hd₁₀_slice
    have hx₁₀_low : x₁₀.regs regLow = lowLen :=
      (hd₁₀_pres regLow (Or.inr rfl)).trans hx₈_low
    have hx₁₀_val : x₁₀.regs regVal = lowPart :=
      hd₁₀_pres regVal (Or.inl (by decide))
    obtain ⟨hshift_fits, hor_fits, hcomb_eq⟩ :=
      combineSlices_eq_bitops (w := w) (b := b) (lowLen := lowLen)
        (lowPart := lowPart) (highPart := highPart)
        hb hlow_le_b (extractSlice_fits _ _ _) (extractSlice_fits _ _ _)
    set x₁₁ := x₁₀.set regTmp1 (highPart <<< lowLen)
    have e₁₁ : RDemonicExec w (.op (.bin .shiftLeft regTmp1 regSlice regLow)) x₁₀ 1 (· = x₁₁) := by
      have hev : BinOp.shiftLeft.eval (x₁₀.regs regSlice) (x₁₀.regs regLow) =
          highPart <<< lowLen := by
        change x₁₀.regs regSlice <<< x₁₀.regs regLow = _
        rw [hx₁₀_slice, hx₁₀_low]
      rw [show x₁₁ = x₁₀.set regTmp1
          (BinOp.shiftLeft.eval (x₁₀.regs regSlice) (x₁₀.regs regLow)) by rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact hshift_fits)
    set x₁₂ := x₁₁.set regVal (lowPart ||| (highPart <<< lowLen))
    have e₁₂ : RDemonicExec w (.op (.bin .or regVal regVal regTmp1)) x₁₁ 1 (· = x₁₂) := by
      have hev : BinOp.or.eval (x₁₁.regs regVal) (x₁₁.regs regTmp1) =
          lowPart ||| (highPart <<< lowLen) := by
        change x₁₀.regs regVal ||| (highPart <<< lowLen) = _
        rw [hx₁₀_val]
      rw [show x₁₂ = x₁₁.set regVal (BinOp.or.eval (x₁₁.regs regVal) (x₁₁.regs regTmp1)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact hor_fits)
    have e_pos := e₁.seq_eq (e₂.seq_eq (e₃.seq_eq (e₄.seq_eq (e₅.seq_eq
      (e₆.seq_eq (e₇.seq_eq (e₈.seq_eq (e₉.seq_eq (e₁₀.seq_eq (e₁₁.seq_eq e₁₂))))))))))
    refine (e_hdr.seq_eq (RDemonicExec.branch_pos hcond e_pos)).mono (by decide) ?_
    rintro _ rfl
    have hx₁₂_mem : x₁₂.mem = x.mem := by
      simpa [x₁₂, x₁₁, x₁₀, hd₁₀_mem, x₉, x₈, x₇] using hx₆_mem
    have hpres_low5 : ∀ r : Fin 16, r.val < 6 → r ≠ regVal → x₁₂.regs r = x.regs r := by
      intro r hr hne
      have h10 := hd₁₀_pres r (Or.inl (by omega))
      have h3 := hd₃_pres r (Or.inl (by omega))
      have h0 := hd₀_pres r hr
      obtain ⟨hne_t1, hne_l, hne_o, hne_w, hne_wi⟩ :=
        (by decide : ∀ k : Fin 16, k.val < 6 →
          k ≠ regTmp1 ∧ k ≠ regLen ∧ k ≠ regOff ∧ k ≠ regWord ∧ k ≠ regWordIdx) r hr
      simp [x₁₂, x₁₁, Function.update_of_ne hne, Function.update_of_ne hne_t1, x₁₀, h10,
        x₉, x₈, x₇, x₆, x₅, x₄, Function.update_of_ne hne_l, Function.update_of_ne hne_o,
        Function.update_of_ne hne_w, Function.update_of_ne hne_wi, x₃, h3, x₂, x₁, x₀, h0]
    have hval_eq :
        x₁₂.regs regVal = readSubword w (fun a => x.mem (base + a)) b i := by
      simp only [x₁₂, RData.set_regs, Function.update_self, ← hcomb_eq, readSubword]
      rw [ite_eq_right hnot_fit]
      rfl
    refine ⟨?_, hx₁₂_mem, rfl, hval_eq,
      hpres_low5 regOp (by decide) (by decide),
      hpres_low5 regIdx (by decide) (by decide),
      hpres_low5 regRet (by decide) (by decide),
      hpres_low5 regBase (by decide) (by decide),
      hpres_low5 regB (by decide) (by decide)⟩
    -- Prove `x₁₂.Bounded w`:
    have h0_bdd : x₀.Bounded w := ⟨hd₀_exec.bounded hx.1, hx.2.1, by rw [hx₀_mem]; exact hx.2.2⟩
    have h2_bdd : x₂.Bounded w :=
      (h0_bdd.set (hx.mem_fits (base + wordIdx))).set ((fits_self w).of_le hlow_le_w)
    have h3_bdd : x₃.Bounded w :=
      ⟨hd₃_exec.bounded h2_bdd.1, h2_bdd.2.1, by
        change ∀ a ≥ x.frontier, d₃.mem a = 0
        rw [hd₃_mem]
        exact h2_bdd.2.2⟩
    have h9_bdd : x₉.Bounded w :=
      (((((h3_bdd.set (hx₃_slice ▸ hd₃_fits)).set (fits_one hw_ne)).set haddr1_fits).set
        (hx.mem_fits (base + wordIdx + 1))).set (fits_zero w)).set ((fits_self w).of_le hhigh_le_w)
    have h10_bdd : x₁₀.Bounded w :=
      ⟨hd₁₀_exec.bounded h9_bdd.1, h9_bdd.2.1, by
        change ∀ a ≥ x.frontier, d₁₀.mem a = 0
        rw [hd₁₀_mem]
        exact h9_bdd.2.2⟩
    exact (h10_bdd.set hshift_fits).set hor_fits
  · -- Single-word branch (`¬ (lowLen < b)`, i.e., `inWordOff + b ≤ w`):
    have hfit : inWordOff + b ≤ w := by omega
    have hcond : ¬ (Cond.lt regLow regB).Holds x₀.toData := by
      change ¬ (d₀.regs regLow < x₀.regs regB)
      rw [hd₀_low, hx₀_b]
      exact hsplit
    set x₁ := x₀.set regWord (x.mem (base + wordIdx))
    have e₁ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₀ 1 (· = x₁) := by
      rw [show x₁ = x₀.set regWord (x₀.mem (x₀.regs regWordIdx)) by
        rw [hx₀_mem, hx₀_widx]]
      exact RDemonicExec.load (by rw [hx₀_widx]; exact haddr0_lt)
    set x₂ := x₁.set regLen b
    have e₂ : RDemonicExec (B := .standard) w (.op (.copy regLen regB)) x₁ 1 (· = x₂) := by
      rw [show x₂ = x₁.set regLen (x₁.regs regB) by
        change x₁.set regLen b = x₁.set regLen (x₀.regs regB)
        rw [hx₀_b]]
      exact RDemonicExec.copy
    obtain ⟨d₃, hd₃_exec, hd₃_mem, hd₃_slice, hd₃_fits, hd₃_pres⟩ :=
      extractSliceCode_exec (w := w) (x := x₂.toData)
        (by exact hx.mem_fits (base + wordIdx))
        hb_pos
        hb
    set x₃ : RData 16 := ⟨d₃.regs, d₃.mem, x.frontier⟩
    have e₃ : RDemonicExec w (RCode.ofCode extractSliceCode) x₂ 7 (· = x₃) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₃_exec
    set sliceVal := extractSlice (x.mem (base + wordIdx)) inWordOff b
    have hx₃_slice : x₃.regs regSlice = sliceVal := by
      change d₃.regs regSlice = extractSlice (x.mem (base + wordIdx)) inWordOff b
      rw [← hx₀_off]
      exact hd₃_slice
    set x₄ := x₃.set regVal sliceVal
    have e₄ : RDemonicExec (B := .standard) w (.op (.copy regVal regSlice)) x₃ 1 (· = x₄) := by
      rw [show x₄ = x₃.set regVal (x₃.regs regSlice) by rw [hx₃_slice]]
      exact RDemonicExec.copy
    have e_neg := e₁.seq_eq (e₂.seq_eq (e₃.seq_eq e₄))
    refine (e_hdr.seq_eq (RDemonicExec.branch_neg hcond e_neg)).mono (by decide) ?_
    rintro _ rfl
    have hx₄_mem : x₄.mem = x.mem := by
      simpa [x₄, x₃, hd₃_mem, x₂, x₁] using hx₀_mem
    have hpres_low5 : ∀ r : Fin 16, r.val < 6 → r ≠ regVal → x₄.regs r = x.regs r := by
      intro r hr hne
      have h3 := hd₃_pres r (Or.inl (by omega))
      have h0 := hd₀_pres r hr
      obtain ⟨hne_l, hne_w⟩ :=
        (by decide : ∀ k : Fin 16, k.val < 6 → k ≠ regLen ∧ k ≠ regWord) r hr
      simp [x₄, Function.update_of_ne hne, x₃, h3, x₂, x₁,
        Function.update_of_ne hne_l, Function.update_of_ne hne_w, x₀, h0]
    have hval_eq :
        x₄.regs regVal = readSubword w (fun a => x.mem (base + a)) b i := by
      simp only [x₄, RData.set_regs, Function.update_self, readSubword]
      rw [ite_eq_left hfit]
    refine ⟨?_, hx₄_mem, rfl, hval_eq,
      hpres_low5 regOp (by decide) (by decide),
      hpres_low5 regIdx (by decide) (by decide),
      hpres_low5 regRet (by decide) (by decide),
      hpres_low5 regBase (by decide) (by decide),
      hpres_low5 regB (by decide) (by decide)⟩
    have h0_bdd : x₀.Bounded w := ⟨hd₀_exec.bounded hx.1, hx.2.1, by rw [hx₀_mem]; exact hx.2.2⟩
    have h2_bdd : x₂.Bounded w :=
      (h0_bdd.set (hx.mem_fits (base + wordIdx))).set ((fits_self w).of_le hb)
    have h3_bdd : x₃.Bounded w :=
      ⟨hd₃_exec.bounded h2_bdd.1, h2_bdd.2.1, by
        change ∀ a ≥ x.frontier, d₃.mem a = 0
        rw [hd₃_mem]
        exact h2_bdd.2.2⟩
    exact h3_bdd.set (hx₃_slice ▸ hd₃_fits)

/-- Concrete structured `RCode .standard 16` procedure that writes the `b`-bit value `regs regVal`
at index `regs regIdx` into the packed array starting at word address `regs regBase` in at most
`40` instructions. -/
def writeSubwordCode : RCode .standard 16 :=
  .seq (RCode.ofCode subwordHeaderCode) <|
  .branch (.lt regLow regB)
    -- Cross-word branch (`w - inWordOff < b`, i.e., `¬ (inWordOff + b ≤ w)`):
    (.seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.copy regLen regLow)) <|
     .seq (.op (.copy regSlice regVal)) <|
     .seq (RCode.ofCode spliceWordCode) <|
     .seq (.op (.store regWordIdx regWord)) <|
     .seq (.op (.const regTmp1 1)) <|
     .seq (.op (.bin .add regWordIdx regWordIdx regTmp1)) <|
     .seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.const regOff 0)) <|
     .seq (.op (.bin .sub regLen regB regLow)) <|
     .seq (.op (.bin .shiftRight regSlice regVal regLow)) <|
     .seq (RCode.ofCode spliceWordCode) <|
          (.op (.store regWordIdx regWord)))
    -- Single-word branch (`inWordOff + b ≤ w`):
    (.seq (.op (.load regWord regWordIdx)) <|
     .seq (.op (.copy regLen regB)) <|
     .seq (.op (.copy regSlice regVal)) <|
     .seq (RCode.ofCode spliceWordCode) <|
          (.op (.store regWordIdx regWord)))

private theorem shiftMem_update_eq (base : ℕ) (mem : ℕ → ℕ) (idx v : ℕ) :
    (fun a => Function.update mem (base + idx) v (base + a)) =
      Function.update (fun a => mem (base + a)) idx v := by
  funext a
  by_cases ha : a = idx
  · subst ha; simp
  · have hne : base + a ≠ base + idx := by omega
    simp [Function.update_of_ne hne, Function.update_of_ne ha]

/-- `writeSubwordCode` executes in at most `40` instructions on `RData 16`, preserves `frontier`,
all memory words `< x.regs regBase`, and registers `0..5` (`regOp`, `regIdx`, `regVal`, `regRet`,
`regBase`, `regB`), and updates the shifted memory `fun a => y.mem (base + a)` to
`writeSubword w (fun a => x.mem (base + a)) b i val`. -/
theorem writeSubwordCode_exec {w n : ℕ} {x : RData 16}
    (hx : x.Bounded w)
    (hb_pos : 0 < x.regs regB) (hb : x.regs regB ≤ w)
    (hi : x.regs regIdx < n)
    (hbitOff : Fits w (x.regs regIdx * x.regs regB))
    (hfront : x.regs regBase + packedWords w (x.regs regB) n ≤ x.frontier) :
    RDemonicExec w writeSubwordCode x 40 fun y =>
      y.Bounded w ∧
        y.frontier = x.frontier ∧
        (∀ a < x.regs regBase, y.mem a = x.mem a) ∧
        (fun a => y.mem (x.regs regBase + a)) =
          writeSubword w (fun a => x.mem (x.regs regBase + a))
            (x.regs regB) (x.regs regIdx) (x.regs regVal) ∧
        (∀ r : Fin 16, r.val < 6 → y.regs r = x.regs r) := by
  have hw : 0 < w := lt_of_lt_of_le hb_pos hb
  have hw_ne : w ≠ 0 := by omega
  set base := x.regs regBase
  set b := x.regs regB
  set i := x.regs regIdx
  set val := x.regs regVal
  set bitOff := i * b
  set wordIdx := bitOff / w
  set inWordOff := bitOff % w
  set lowLen := w - inWordOff
  have hmod : inWordOff < w := Nat.mod_lt _ hw
  have hw0_lt : wordIdx < packedWords w b n := wordIdx_lt_packedWords_of_pos hw hb_pos hi
  have haddr0_lt : base + wordIdx < x.frontier :=
    lt_of_lt_of_le (Nat.add_lt_add_left hw0_lt base) hfront
  have haddr0_fits : Fits w (base + wordIdx) := hx.frontier_fits.of_le (le_of_lt haddr0_lt)
  obtain ⟨d₀, hd₀_exec, hd₀_mem, hd₀_w, hd₀_widx, hd₀_off, hd₀_low, hd₀_pres⟩ :=
    subwordHeaderCode_exec (x := x.toData) hw hbitOff haddr0_fits
  have e_hdr : RDemonicExec w (RCode.ofCode subwordHeaderCode) x 6
      (· = ⟨d₀.regs, d₀.mem, x.frontier⟩) :=
    RDemonicExec.of_exec_regOnly (by decide) hd₀_exec
  set x₀ : RData 16 := ⟨d₀.regs, d₀.mem, x.frontier⟩
  have hx₀_mem : x₀.mem = x.mem := hd₀_mem
  have hx₀_widx : x₀.regs regWordIdx = base + wordIdx := hd₀_widx
  have hx₀_off : x₀.regs regOff = inWordOff := hd₀_off
  have hx₀_low : x₀.regs regLow = lowLen := hd₀_low
  have hx₀_b : x₀.regs regB = b := hd₀_pres regB (by decide)
  have hx₀_val : x₀.regs regVal = val := hd₀_pres regVal (by decide)
  by_cases hsplit : lowLen < b
  · -- Cross-word branch (`lowLen < b`, i.e., `¬ (inWordOff + b ≤ w)`):
    have hnot_fit : ¬ (inWordOff + b ≤ w) := by omega
    have hcond : (Cond.lt regLow regB).Holds x₀.toData := by
      change d₀.regs regLow < x₀.regs regB
      rw [hd₀_low, hx₀_b]
      exact hsplit
    have hlow_pos : 0 < lowLen := by omega
    have hlow_le_w : lowLen ≤ w := by omega
    have hhigh_pos : 0 < b - lowLen := by omega
    have hhigh_le_w : b - lowLen ≤ w := by omega
    have hw1_lt : wordIdx + 1 < packedWords w b n :=
      wordIdx_succ_lt_packedWords hw hi hnot_fit
    have haddr1_lt : base + wordIdx + 1 < x.frontier := by
      have := lt_of_lt_of_le (Nat.add_lt_add_left hw1_lt base) hfront
      omega
    have haddr1_fits : Fits w (base + wordIdx + 1) :=
      hx.frontier_fits.of_le (le_of_lt haddr1_lt)
    set x₁ := x₀.set regWord (x.mem (base + wordIdx))
    have e₁ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₀ 1 (· = x₁) := by
      rw [show x₁ = x₀.set regWord (x₀.mem (x₀.regs regWordIdx)) by
        rw [hx₀_mem, hx₀_widx]]
      exact RDemonicExec.load (by rw [hx₀_widx]; exact haddr0_lt)
    set x₂ := x₁.set regLen lowLen
    have e₂ : RDemonicExec (B := .standard) w (.op (.copy regLen regLow)) x₁ 1 (· = x₂) := by
      rw [show x₂ = x₁.set regLen (x₁.regs regLow) by
        change x₁.set regLen lowLen = x₁.set regLen (x₀.regs regLow)
        rw [hx₀_low]]
      exact RDemonicExec.copy
    set x₃ := x₂.set regSlice val
    have e₃ : RDemonicExec (B := .standard) w (.op (.copy regSlice regVal)) x₂ 1 (· = x₃) := by
      rw [show x₃ = x₂.set regSlice (x₂.regs regVal) by
        change x₂.set regSlice val = x₂.set regSlice (x₀.regs regVal)
        rw [hx₀_val]]
      exact RDemonicExec.copy
    obtain ⟨d₄, hd₄_exec, hd₄_mem, hd₄_word, hd₄_fits, hd₄_pres⟩ :=
      spliceWordCode_exec (w := w) (x := x₃.toData)
        (by exact hx.mem_fits (base + wordIdx))
        hlow_pos
        (by change x₀.regs regOff + lowLen ≤ w; rw [hx₀_off]; omega)
    set x₄ : RData 16 := ⟨d₄.regs, d₄.mem, x.frontier⟩
    have e₄ : RDemonicExec w (RCode.ofCode spliceWordCode) x₃ 11 (· = x₄) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₄_exec
    set w0' := spliceWord w (x.mem (base + wordIdx)) inWordOff lowLen val
    have hx₄_word : x₄.regs regWord = w0' := by
      change d₄.regs regWord = spliceWord w (x.mem (base + wordIdx)) inWordOff lowLen val
      rw [← hx₀_off]
      exact hd₄_word
    have hx₄_widx : x₄.regs regWordIdx = base + wordIdx :=
      (hd₄_pres regWordIdx (Or.inl (by decide))).trans hx₀_widx
    have hx₄_mem : x₄.mem = x.mem := by
      simpa [x₄, hd₄_mem, x₃, x₂, x₁] using hx₀_mem
    set mem₁ := Function.update x.mem (base + wordIdx) w0'
    set x₅ := x₄.write (base + wordIdx) w0'
    have e₅ : RDemonicExec (B := .standard) w (.op (.store regWordIdx regWord)) x₄ 1 (· = x₅) := by
      rw [show x₅ = x₄.write (x₄.regs regWordIdx) (x₄.regs regWord) by
        rw [hx₄_widx, hx₄_word]]
      exact RDemonicExec.store (by rw [hx₄_widx]; exact haddr0_lt)
    have hx₅_mem : x₅.mem = mem₁ := by simp [x₅, hx₄_mem, mem₁]
    set x₆ := x₅.set regTmp1 1
    have e₆ : RDemonicExec (B := .standard) w (.op (.const regTmp1 1)) x₅ 1 (· = x₆) :=
      RDemonicExec.const (fits_one hw_ne)
    set x₇ := x₆.set regWordIdx (base + wordIdx + 1)
    have e₇ : RDemonicExec w (.op (.bin .add regWordIdx regWordIdx regTmp1)) x₆ 1 (· = x₇) := by
      have hev : BinOp.add.eval (x₆.regs regWordIdx) (x₆.regs regTmp1) = base + wordIdx + 1 := by
        change x₄.regs regWordIdx + 1 = _
        rw [hx₄_widx]
      rw [show x₇ = x₆.set regWordIdx (BinOp.add.eval (x₆.regs regWordIdx) (x₆.regs regTmp1)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact haddr1_fits)
    set x₈ := x₇.set regWord (mem₁ (base + wordIdx + 1))
    have e₈ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₇ 1 (· = x₈) := by
      rw [show x₈ = x₇.set regWord (x₇.mem (x₇.regs regWordIdx)) by
        rw [show x₇.mem = x₅.mem from rfl, hx₅_mem]; rfl]
      exact RDemonicExec.load haddr1_lt
    set x₉ := x₈.set regOff 0
    have e₉ : RDemonicExec (B := .standard) w (.op (.const regOff 0)) x₈ 1 (· = x₉) :=
      RDemonicExec.const (fits_zero w)
    set x₁₀ := x₉.set regLen (b - lowLen)
    have hx₉_b : x₉.regs regB = b :=
      (hd₄_pres regB (Or.inl (by decide))).trans hx₀_b
    have hx₉_low : x₉.regs regLow = lowLen :=
      (hd₄_pres regLow (Or.inr (Or.inr rfl))).trans hx₀_low
    have e₁₀ : RDemonicExec w (.op (.bin .sub regLen regB regLow)) x₉ 1 (· = x₁₀) := by
      have hev : BinOp.sub.eval (x₉.regs regB) (x₉.regs regLow) = b - lowLen := by
        change x₉.regs regB - x₉.regs regLow = _
        rw [hx₉_b, hx₉_low]
      rw [show x₁₀ = x₉.set regLen (BinOp.sub.eval (x₉.regs regB) (x₉.regs regLow)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact (fits_self w).of_le hhigh_le_w)
    have hx₁₀_val : x₁₀.regs regVal = val :=
      (hd₄_pres regVal (Or.inl (by decide))).trans hx₀_val
    have hx₁₀_low : x₁₀.regs regLow = lowLen := hx₉_low
    have hval_shr_fits : Fits w (val >>> lowLen) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact (hx.regs_fits regVal).of_le (Nat.div_le_self _ _)
    set x₁₁ := x₁₀.set regSlice (val >>> lowLen)
    have e₁₁ : RDemonicExec w (.op (.bin .shiftRight regSlice regVal regLow)) x₁₀ 1 (· = x₁₁) := by
      have hev : BinOp.shiftRight.eval (x₁₀.regs regVal) (x₁₀.regs regLow) = val >>> lowLen := by
        change x₁₀.regs regVal >>> x₁₀.regs regLow = _
        rw [hx₁₀_val, hx₁₀_low]
      rw [show x₁₁ = x₁₀.set regSlice
          (BinOp.shiftRight.eval (x₁₀.regs regVal) (x₁₀.regs regLow)) by rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact hval_shr_fits)
    have hmem1_fits : Fits w (mem₁ (base + wordIdx + 1)) := by
      have hne : base + wordIdx + 1 ≠ base + wordIdx := by omega
      dsimp only [mem₁]
      rw [Function.update_of_ne hne]
      exact hx.mem_fits (base + wordIdx + 1)
    obtain ⟨d₁₂, hd₁₂_exec, hd₁₂_mem, hd₁₂_word, hd₁₂_fits, hd₁₂_pres⟩ :=
      spliceWordCode_exec (w := w) (x := x₁₁.toData)
        (by exact hmem1_fits)
        hhigh_pos
        (by change 0 + (b - lowLen) ≤ w; omega)
    set x₁₂ : RData 16 := ⟨d₁₂.regs, d₁₂.mem, x.frontier⟩
    have e₁₂ : RDemonicExec w (RCode.ofCode spliceWordCode) x₁₁ 11 (· = x₁₂) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₁₂_exec
    set w1' := spliceWord w (mem₁ (base + wordIdx + 1)) 0 (b - lowLen) (val / 2 ^ lowLen)
    have hx₁₂_word : x₁₂.regs regWord = w1' := by
      change d₁₂.regs regWord =
        spliceWord w (mem₁ (base + wordIdx + 1)) 0 (b - lowLen) (val / 2 ^ lowLen)
      rw [← Nat.shiftRight_eq_div_pow]
      exact hd₁₂_word
    have hx₁₂_widx : x₁₂.regs regWordIdx = base + wordIdx + 1 :=
      hd₁₂_pres regWordIdx (Or.inl (by decide))
    have hx₁₂_mem : x₁₂.mem = mem₁ := by
      simpa [x₁₂, hd₁₂_mem, x₁₁, x₁₀, x₉, x₈, x₇, x₆] using hx₅_mem
    set x₁₃ := x₁₂.write (base + wordIdx + 1) w1'
    have e₁₃ :
        RDemonicExec (B := .standard) w (.op (.store regWordIdx regWord)) x₁₂ 1 (· = x₁₃) := by
      rw [show x₁₃ = x₁₂.write (x₁₂.regs regWordIdx) (x₁₂.regs regWord) by
        rw [hx₁₂_widx, hx₁₂_word]]
      exact RDemonicExec.store (by rw [hx₁₂_widx]; exact haddr1_lt)
    have e_pos := e₁.seq_eq (e₂.seq_eq (e₃.seq_eq (e₄.seq_eq (e₅.seq_eq
      (e₆.seq_eq (e₇.seq_eq (e₈.seq_eq (e₉.seq_eq (e₁₀.seq_eq (e₁₁.seq_eq
        (e₁₂.seq_eq e₁₃)))))))))))
    refine (e_hdr.seq_eq (RDemonicExec.branch_pos hcond e_pos)).mono (by decide) ?_
    rintro _ rfl
    have hx₁₃_mem : x₁₃.mem = Function.update mem₁ (base + wordIdx + 1) w1' := by
      simp [x₁₃, hx₁₂_mem]
    refine ⟨?_, rfl, ?_, ?_, ?_⟩
    · -- `x₁₃.Bounded w`:
      have h0_bdd : x₀.Bounded w := ⟨hd₀_exec.bounded hx.1, hx.2.1, by rw [hx₀_mem]; exact hx.2.2⟩
      have h3_bdd : x₃.Bounded w :=
        ((h0_bdd.set (hx.mem_fits (base + wordIdx))).set ((fits_self w).of_le hlow_le_w)).set
          (hx.regs_fits regVal)
      have h4_bdd : x₄.Bounded w :=
        ⟨hd₄_exec.bounded h3_bdd.1, h3_bdd.2.1, by rw [hx₄_mem]; exact hx.2.2⟩
      have h5_bdd : x₅.Bounded w := h4_bdd.write haddr0_lt (hx₄_word ▸ hd₄_fits)
      have h11_bdd : x₁₁.Bounded w :=
        (((((h5_bdd.set (fits_one hw_ne)).set haddr1_fits).set hmem1_fits).set
          (fits_zero w)).set ((fits_self w).of_le hhigh_le_w)).set hval_shr_fits
      have h12_bdd : x₁₂.Bounded w :=
        ⟨hd₁₂_exec.bounded h11_bdd.1, h11_bdd.2.1, by rw [hx₁₂_mem, ← hx₅_mem]; exact h5_bdd.2.2⟩
      exact h12_bdd.write haddr1_lt (hx₁₂_word ▸ hd₁₂_fits)
    · intro a ha
      rw [hx₁₃_mem]
      have hne0 : a ≠ base + wordIdx :=
        ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right base wordIdx))
      have hne1 : a ≠ base + wordIdx + 1 :=
        ne_of_lt (lt_of_lt_of_le ha
          (le_trans (Nat.le_add_right base wordIdx) (Nat.le_add_right _ 1)))
      dsimp only [mem₁]
      rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
    · rw [hx₁₃_mem]
      dsimp only [mem₁, w1', w0', writeSubword, bitOff, wordIdx, inWordOff, lowLen]
      rw [ite_eq_right hnot_fit]
      have h1 : base + wordIdx + 1 = base + (wordIdx + 1) := by omega
      rw [h1, shiftMem_update_eq, shiftMem_update_eq]
      congr 2
      exact congrArg (fun f => f (wordIdx + 1)) (shiftMem_update_eq base x.mem wordIdx _)
    · intro r hr
      have h12 := hd₁₂_pres r (Or.inl (by omega))
      have h4 := hd₄_pres r (Or.inl (by omega))
      have h0 := hd₀_pres r hr
      obtain ⟨hne_s, hne_l, hne_o, hne_w, hne_wi, hne_t1⟩ :=
        (by decide : ∀ k : Fin 16, k.val < 6 →
          k ≠ regSlice ∧ k ≠ regLen ∧ k ≠ regOff ∧ k ≠ regWord ∧ k ≠ regWordIdx ∧ k ≠ regTmp1) r hr
      simp [x₁₃, x₁₂, h12, x₁₁, x₁₀, x₉, x₈, x₇, x₆, x₅,
        Function.update_of_ne hne_s, Function.update_of_ne hne_l,
        Function.update_of_ne hne_o, Function.update_of_ne hne_w,
        Function.update_of_ne hne_wi, Function.update_of_ne hne_t1,
        x₄, h4, x₃, x₂, x₁, x₀, h0]
  · -- Single-word branch (`¬ (lowLen < b)`, i.e., `inWordOff + b ≤ w`):
    have hfit : inWordOff + b ≤ w := by omega
    have hcond : ¬ (Cond.lt regLow regB).Holds x₀.toData := by
      change ¬ (d₀.regs regLow < x₀.regs regB)
      rw [hd₀_low, hx₀_b]
      exact hsplit
    set x₁ := x₀.set regWord (x.mem (base + wordIdx))
    have e₁ : RDemonicExec (B := .standard) w (.op (.load regWord regWordIdx)) x₀ 1 (· = x₁) := by
      rw [show x₁ = x₀.set regWord (x₀.mem (x₀.regs regWordIdx)) by
        rw [hx₀_mem, hx₀_widx]]
      exact RDemonicExec.load (by rw [hx₀_widx]; exact haddr0_lt)
    set x₂ := x₁.set regLen b
    have e₂ : RDemonicExec (B := .standard) w (.op (.copy regLen regB)) x₁ 1 (· = x₂) := by
      rw [show x₂ = x₁.set regLen (x₁.regs regB) by
        change x₁.set regLen b = x₁.set regLen (x₀.regs regB)
        rw [hx₀_b]]
      exact RDemonicExec.copy
    set x₃ := x₂.set regSlice val
    have e₃ : RDemonicExec (B := .standard) w (.op (.copy regSlice regVal)) x₂ 1 (· = x₃) := by
      rw [show x₃ = x₂.set regSlice (x₂.regs regVal) by
        change x₂.set regSlice val = x₂.set regSlice (x₀.regs regVal)
        rw [hx₀_val]]
      exact RDemonicExec.copy
    obtain ⟨d₄, hd₄_exec, hd₄_mem, hd₄_word, hd₄_fits, hd₄_pres⟩ :=
      spliceWordCode_exec (w := w) (x := x₃.toData)
        (by exact hx.mem_fits (base + wordIdx))
        hb_pos
        (by change x₀.regs regOff + b ≤ w; rw [hx₀_off]; exact hfit)
    set x₄ : RData 16 := ⟨d₄.regs, d₄.mem, x.frontier⟩
    have e₄ : RDemonicExec w (RCode.ofCode spliceWordCode) x₃ 11 (· = x₄) :=
      RDemonicExec.of_exec_regOnly (by decide) hd₄_exec
    set w0' := spliceWord w (x.mem (base + wordIdx)) inWordOff b val
    have hx₄_word : x₄.regs regWord = w0' := by
      change d₄.regs regWord = spliceWord w (x.mem (base + wordIdx)) inWordOff b val
      rw [← hx₀_off]
      exact hd₄_word
    have hx₄_widx : x₄.regs regWordIdx = base + wordIdx :=
      (hd₄_pres regWordIdx (Or.inl (by decide))).trans hx₀_widx
    have hx₄_mem : x₄.mem = x.mem := by
      simpa [x₄, hd₄_mem, x₃, x₂, x₁] using hx₀_mem
    set x₅ := x₄.write (base + wordIdx) w0'
    have e₅ : RDemonicExec (B := .standard) w (.op (.store regWordIdx regWord)) x₄ 1 (· = x₅) := by
      rw [show x₅ = x₄.write (x₄.regs regWordIdx) (x₄.regs regWord) by
        rw [hx₄_widx, hx₄_word]]
      exact RDemonicExec.store (by rw [hx₄_widx]; exact haddr0_lt)
    have e_neg := e₁.seq_eq (e₂.seq_eq (e₃.seq_eq (e₄.seq_eq e₅)))
    refine (e_hdr.seq_eq (RDemonicExec.branch_neg hcond e_neg)).mono (by decide) ?_
    rintro _ rfl
    have hx₅_mem : x₅.mem = Function.update x.mem (base + wordIdx) w0' := by
      simp [x₅, hx₄_mem]
    refine ⟨?_, rfl, ?_, ?_, ?_⟩
    · have h0_bdd : x₀.Bounded w := ⟨hd₀_exec.bounded hx.1, hx.2.1, by rw [hx₀_mem]; exact hx.2.2⟩
      have h3_bdd : x₃.Bounded w :=
        ((h0_bdd.set (hx.mem_fits (base + wordIdx))).set ((fits_self w).of_le hb)).set
          (hx.regs_fits regVal)
      have h4_bdd : x₄.Bounded w :=
        ⟨hd₄_exec.bounded h3_bdd.1, h3_bdd.2.1, by rw [hx₄_mem]; exact hx.2.2⟩
      exact h4_bdd.write haddr0_lt (hx₄_word ▸ hd₄_fits)
    · intro a ha
      rw [hx₅_mem]
      have hne : a ≠ base + wordIdx :=
        ne_of_lt (lt_of_lt_of_le ha (Nat.le_add_right base wordIdx))
      exact Function.update_of_ne hne _ _
    · rw [hx₅_mem]
      dsimp only [w0', writeSubword, bitOff, wordIdx, inWordOff]
      rw [ite_eq_left hfit]
      exact shiftMem_update_eq base x.mem wordIdx w0'
    · intro r hr
      have h4 := hd₄_pres r (Or.inl (by omega))
      have h0 := hd₀_pres r hr
      obtain ⟨hne_s, hne_l, hne_w⟩ :=
        (by decide : ∀ k : Fin 16, k.val < 6 → k ≠ regSlice ∧ k ≠ regLen ∧ k ≠ regWord) r hr
      simp [x₅, x₄, h4, x₃, x₂, x₁,
        Function.update_of_ne hne_s, Function.update_of_ne hne_l,
        Function.update_of_ne hne_w, x₀, h0]

end Cslib.WordRAM.Resizable
