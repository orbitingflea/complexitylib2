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

/-- Assemble a structured resizable Word-RAM program `RCode B r` at instruction index `pc`. -/
def assemble : RCode B r → ℕ → RProgram B r
  | .op o, _ => [.op o]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch c pos neg, pc =>
    .branch c (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      .jump (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop c body, pc =>
    .branch c (pc + 2) :: .jump (pc + body.size + 3) :: body.assemble (pc + 2) ++ [.jump pc]
  | .rand dst src, _ => [.rand dst src]
  | .grow dst kReg, _ => [.grow dst kReg]
  | .shrink kReg, _ => [.shrink kReg]

/-- Assembling `c : RCode B r` at any base index produces `c.size` flat instructions. -/
@[simp]
theorem length_assemble (c : RCode B r) (pc : ℕ) : (c.assemble pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [assemble, List.length_append, List.length_cons, ihp, ihn, size]
    omega
  | _ => simp_all [assemble]

/-- Complete flat resizable Word-RAM program: `c.assemble 0` followed by `halt out`. -/
def program (c : RCode B r) (out : Fin r) : RProgram B r := c.assemble 0 ++ [.halt out]

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

/-- A loop through the states `xs 0, …, xs k`: the condition holds at the first `k` of them and
fails at the last, and the body leads from each to the next in `T` instructions. -/
theorem loop {cond : Cond r} {body : RCode B r} (xs : ℕ → RData r) (k T : ℕ)
    (hc : ∀ i < k, cond.Holds (xs i).toData) (hk : ¬cond.Holds (xs k).toData)
    (hbody : ∀ i < k, RDemonicExec w body (xs i) T (· = xs (i + 1))) :
    RDemonicExec w (.loop cond body) (xs 0) (k * (T + 2) + 2) (· = xs k) := by
  induction k generalizing xs with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    exact loop_exit hk rfl
  | succ k ih =>
    have hstep := loop_iter (hc 0 (by omega)) (hbody 0 (by omega)) fun y hy => by
      subst hy
      exact ih (fun i => xs (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega))
    exact hstep.mono (by rw [Nat.succ_mul]; omega) fun _ h => h

end RDemonicExec

/-! ## Bounds-checked `zeroFill` and demonic-safe zeroed growth (`growZeroCode`) -/

/-- Updating a demonically grown memory with `clear mem' frontier k` recovers `x.mem` identically
whenever `x.Bounded w` holds (since `x.mem a = 0` for all `a ≥ x.frontier`). -/
theorem clear_demonicGrow_eq {w k : ℕ} {x : RData r} {mem' : ℕ → ℕ}
    (hx : x.Bounded w) (hdem : DemonicGrow w x.frontier k x.mem mem') :
    clear mem' x.frontier k = x.mem := by
  funext a
  by_cases ha_lt : a < x.frontier
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega), hdem.1 a ha_lt]
  · by_cases ha_in : a < x.frontier + k
    · have hown : (Block.mk x.frontier k).Owns a := by simp only [Block.Owns]; omega
      rw [clear_of_owns hown, hx.zero_above (by omega)]
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega),
        hdem.2.2 a (by omega), hx.zero_above (by omega)]

/-- Zeroing `k = x.regs stop - x.regs cur` words inside the active prefix `[0, x.frontier)` via
`RCode.ofCode (zeroFill cur stop zero one)` takes `4 * k + 2` instructions on `RData r`. -/
theorem zeroFill_rCode_exec {w : ℕ} {cur stop zero one : Fin r} {x : RData r}
    (hcs : cur ≠ stop) (hcz : cur ≠ zero) (hco : cur ≠ one)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hle : x.regs cur ≤ x.regs stop) (hstop_fr : x.regs stop ≤ x.frontier)
    (hw : Fits w (x.regs stop)) :
    RDemonicExec w (RCode.ofCode (zeroFill cur stop zero one)) x
      (4 * (x.regs stop - x.regs cur) + 2)
      (· = ⟨Function.update x.regs cur (x.regs stop),
        clear x.mem (x.regs cur) (x.regs stop - x.regs cur), x.frontier⟩) := by
  set b := x.regs cur with hb
  set k := x.regs stop - b
  let xs : ℕ → RData r := fun i =>
    ⟨Function.update x.regs cur (b + i), clear x.mem b i, x.frontier⟩
  have hstop (i : ℕ) : (xs i).regs stop = x.regs stop := by
    simp [xs, Function.update_of_ne hcs.symm]
  have hcur (i : ℕ) : (xs i).regs cur = b + i := by simp [xs]
  have hbody (i : ℕ) (hi : i < k) :
      RDemonicExec w (.seq (.op (.store cur zero)) (.op (.bin .add cur cur one)))
        (xs i) 2 (· = xs (i + 1)) := by
    have hz : (xs i).regs zero = 0 := by simp [xs, Function.update_of_ne hcz.symm, h0]
    have ho : (xs i).regs one = 1 := by simp [xs, Function.update_of_ne hco.symm, h1]
    have hlt_fr : (xs i).regs cur < (xs i).frontier := by
      rw [hcur]
      change b + i < x.frontier
      omega
    have e₁ := RDemonicExec.store (B := .standard) (w := w) (x := xs i) (a := cur) (s := zero)
      hlt_fr
    have hadd_fits : Fits w
        (BinOp.add.eval (((xs i).write ((xs i).regs cur) ((xs i).regs zero)).regs cur)
          (((xs i).write ((xs i).regs cur) ((xs i).regs zero)).regs one)) := by
      simpa [hcur, ho] using hw.of_le (by omega : b + i + 1 ≤ x.regs stop)
    have e₂ := RDemonicExec.bin (f := .add) (d := cur) (i := cur) (j := one)
      (x := (xs i).write ((xs i).regs cur) ((xs i).regs zero)) hadd_fits
    refine (e₁.seq_eq e₂).mono le_rfl ?_
    rintro _ rfl
    ext a
    · simp [xs, Function.update_of_ne hco.symm, h1, Nat.add_assoc]
    · simp [xs, Function.update_of_ne hcz.symm, h0, clear_succ]
    · rfl
  have h := RDemonicExec.loop (cond := .lt cur stop) xs k 2
    (fun i hi => by simp only [Cond.holds_lt, RData.toData, hcur, hstop]; omega)
    (by simp only [Cond.holds_lt, RData.toData, hcur, hstop]; omega) hbody
  have hx : xs 0 = x := by
    ext a
    · simp [xs, hb]
    · simp [xs]
    · rfl
  have hk : xs k =
      ⟨Function.update x.regs cur (x.regs stop), clear x.mem b k, x.frontier⟩ := by
    simp only [xs]
    congr 2
    omega
  rw [hx, hk, show k * (2 + 2) + 2 = 4 * k + 2 by omega] at h
  exact h

/-- Allocate `regs count` zeroed words at `x.frontier` under demonic `grow`:
executes `.grow result count` (`1` instruction, extending `frontier` to `frontier + count` with
arbitrary demonic `w`-bit values in `[frontier, frontier + count)`) and then zeroes
`[frontier, frontier + count)` via `zeroFill cur stop zero one` (`4 * count + 7` instructions in
total). -/
def growZeroCode (count result cur stop zero one : Fin r) : RCode .standard r :=
  .seq (.op (.const zero 0)) <|
  .seq (.op (.const one 1)) <|
  .seq (.grow result count) <|
  .seq (.op (.copy cur result)) <|
  .seq (.op (.bin .add stop result count)) <|
       (RCode.ofCode (zeroFill cur stop zero one))

/-- **Demonic-safe zeroed growth (`growZeroCode_exec`).**
Starting from any `x : RData r` satisfying `x.Bounded w`, `growZeroCode` executes in `4 * k + 7`
instructions under **demonic** `DemonicGrow`, zeroes every demonically initialized word in
`[x.frontier, x.frontier + k)`, and deterministically produces the state with memory `x.mem` (all
cells `≥ x.frontier` equal to `0`) and frontier `x.frontier + k`. -/
theorem growZeroCode_exec {w : ℕ} {count result cur stop zero one : Fin r} {x : RData r}
    (hx : x.Bounded w)
    (hd : [count, result, cur, stop, zero, one].Nodup)
    (h1 : Fits w 1)
    (hw : Fits w (x.regs count + x.frontier)) :
    let f := x.frontier
    let k := x.regs count
    RDemonicExec w (growZeroCode count result cur stop zero one) x (4 * k + 7)
      (· = ⟨Function.update (Function.update (Function.update (Function.update (Function.update
          x.regs zero 0) one 1) result f) stop (f + k)) cur (f + k),
        x.mem, f + k⟩) := by
  intro f k
  have hfk_fits : Fits w (f + k) := by rw [Nat.add_comm]; exact hw
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hcs, hcz, hco⟩, ⟨hrc, hrs, hrz, hro⟩, ⟨hcs', hcz', hco'⟩,
    ⟨hsz, hso⟩, hzo, -⟩ := hd
  set x₁ := x.set zero 0
  set x₂ := x₁.set one 1
  have e₁ : RDemonicExec (B := .standard) w (.op (.const zero 0)) x 1 (· = x₁) :=
    RDemonicExec.const (fits_zero w)
  have e₂ : RDemonicExec (B := .standard) w (.op (.const one 1)) x₁ 1 (· = x₂) :=
    RDemonicExec.const h1
  have hx₂_k : x₂.regs count = k := by
    simp [x₂, x₁, Function.update_of_ne hco, Function.update_of_ne hcz, k]
  have e_grow : RDemonicExec (B := .standard) w (.grow result count) x₂ 1 fun x₃ =>
      ∃ mem', DemonicGrow w f k x.mem mem' ∧
        x₃ = ⟨Function.update x₂.regs result f, mem', f + k⟩ := by
    refine RDemonicExec.grow (by rw [hx₂_k]; exact hfk_fits) fun mem' hdem => ?_
    rw [hx₂_k] at hdem ⊢
    exact ⟨mem', hdem, rfl⟩
  have e_tail : ∀ x₃,
      (∃ mem', DemonicGrow w f k x.mem mem' ∧
        x₃ = ⟨Function.update x₂.regs result f, mem', f + k⟩) →
      RDemonicExec w
        (.seq (.op (.copy cur result)) <|
         .seq (.op (.bin .add stop result count)) <|
              (RCode.ofCode (zeroFill cur stop zero one)))
        x₃ (4 * k + 4)
        (· = ⟨Function.update (Function.update (Function.update (Function.update (Function.update
            x.regs zero 0) one 1) result f) stop (f + k)) cur (f + k),
          x.mem, f + k⟩) := by
    rintro x₃ ⟨mem', hdem, rfl⟩
    set regs₃ := Function.update x₂.regs result f
    set x₄ : RData r := ⟨Function.update regs₃ cur f, mem', f + k⟩
    have e₄ : RDemonicExec (B := .standard) w (.op (.copy cur result))
        ⟨regs₃, mem', f + k⟩ 1 (· = x₄) := by
      have h₄ : x₄ = (⟨regs₃, mem', f + k⟩ : RData r).set cur (regs₃ result) := by
        ext a
        · simp [x₄, regs₃]
        · rfl
        · rfl
      rw [h₄]
      exact RDemonicExec.copy
    have hx₄_res : x₄.regs result = f := by
      simp [x₄, regs₃, Function.update_of_ne hrc]
    have hx₄_cnt : x₄.regs count = k := by
      simp [x₄, regs₃, Function.update_of_ne hcc, Function.update_of_ne hcr, hx₂_k]
    set x₅ := x₄.set stop (f + k)
    have e₅ : RDemonicExec w (.op (.bin .add stop result count)) x₄ 1 (· = x₅) := by
      have hev : BinOp.add.eval (x₄.regs result) (x₄.regs count) = f + k := by
        change x₄.regs result + x₄.regs count = f + k
        rw [hx₄_res, hx₄_cnt]
      rw [show x₅ = x₄.set stop (BinOp.add.eval (x₄.regs result) (x₄.regs count)) by
        rw [hev]]
      exact RDemonicExec.bin (by rw [hev]; exact hfk_fits)
    have hx₅_cur : x₅.regs cur = f := by
      simp [x₅, x₄, Function.update_of_ne hcs']
    have hx₅_stop : x₅.regs stop = f + k := by
      simp [x₅]
    have hx₅_zero : x₅.regs zero = 0 := by
      simp [x₅, x₄, regs₃, x₂, x₁,
        Function.update_of_ne (Ne.symm hsz), Function.update_of_ne (Ne.symm hcz'),
        Function.update_of_ne (Ne.symm hrz), Function.update_of_ne hzo]
    have hx₅_one : x₅.regs one = 1 := by
      simp [x₅, x₄, regs₃, x₂,
        Function.update_of_ne (Ne.symm hso), Function.update_of_ne (Ne.symm hco'),
        Function.update_of_ne (Ne.symm hro)]
    have e₆ := zeroFill_rCode_exec (w := w) (cur := cur) (stop := stop) (zero := zero) (one := one)
      (x := x₅) hcs' hcz' hco' hx₅_zero hx₅_one
      (by rw [hx₅_cur, hx₅_stop]; omega)
      (by rw [hx₅_stop]; exact le_rfl)
      (by rw [hx₅_stop]; exact hfk_fits)
    refine (e₄.seq_eq (e₅.seq_eq e₆)).mono (by rw [hx₅_cur, hx₅_stop]; omega) ?_
    rintro _ rfl
    ext a
    · rw [hx₅_stop]
      simp only [x₅, x₄, regs₃, x₂, x₁, RData.set_regs, Function.update_apply]
      split_ifs <;> rfl
    · rw [hx₅_cur, hx₅_stop, Nat.add_sub_cancel_left]
      exact congrFun (clear_demonicGrow_eq hx hdem) a
    · rfl
  exact (e₁.seq_eq (e₂.seq_eq (e_grow.seq e_tail))).mono (by omega) fun _ h => h

end Cslib.WordRAM.Resizable
