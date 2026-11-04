/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import Complexity.DataStructure.Dictionary.BitResizable.Client

/-!
# Bridge for the Bit-Resizable Succinct Dictionary Formal Abstract

`BitResizableDictionaryAbstract.lean` states the self-contained formal abstract for the
capacity-unbounded bit-resizable succinct dictionary (`Cslib.DataStructure.Dictionary.BitResizable`)
on the bit-granular resizable Word-RAM model (`Cslib.WordRAM.BitRAM`).

This bridge defines a polymorphic presentation `MachinePresentation` and `DictPresentation` of the
abstract's bit-resizable Word-RAM and dynamic dictionary types, proves the step-by-step transfer of
`BitRAM.DemonicExecWithin` (`compile_demonicExecWithin`), and packages the library theorems:
1. `DictInv.space_tight` and `dictBitSize_le_optBits` (pointwise space
   `OPT(U, V, n_t) + O(n_t log₂ log₂(max n_t 4)) + 218 * w` bits in the current size `n_t`),
2. `init_transition`, `step_transition`, and `tsum_stepOverhead_le` (`O(1)` expected amortized
   time `≤ 8034` instructions per operation),
3. `seq_transition_from_empty` (full operation-sequence execution from `0` bits), and
4. `delete_reuses_released_bits_subroutine` (client subroutine reuse of bits released by `delete`).
-/

namespace ComplexityAbstracts.BitResizableDictionaryBridge

open scoped ENNReal BigOperators Finset
open Cslib.Probability
open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.BitResizable

/-! ## Part 1: Bitwise and Memory Primitives Shared with the Abstract -/

/-- Ceiling division `⌈a / b⌉ = (a + b - 1) / b`. -/
def ceilDiv (a b : ℕ) : ℕ :=
  (a + b - 1) / b

theorem ceilDiv_eq (a b : ℕ) : ceilDiv a b = a ⌈/⌉ b :=
  (Nat.ceilDiv_eq_add_pred_div a b).symm

/-- Low-order bit mask `(1 <<< len) - 1`. -/
def bitMask (len : ℕ) : ℕ :=
  (1 <<< len) - 1

/-- Bit-slice mask `(bitMask len) <<< lo`. -/
def sliceMask (lo len : ℕ) : ℕ :=
  (bitMask len) <<< lo

/-- Clear bits of `word` selected by `mask` via `word ^^^ (word &&& mask)`. -/
def clearMask (word mask : ℕ) : ℕ :=
  word ^^^ (word &&& mask)

/-- Extract `len` bits at offset `lo` from `word`. -/
def extractSlice (word lo len : ℕ) : ℕ :=
  (word >>> lo) &&& bitMask len

/-- Read bit `i` from word-indexed memory `mem` at word width `w`. -/
def getBit (w : ℕ) (mem : ℕ → ℕ) (i : ℕ) : Bool :=
  (mem (i / w)).testBit (i % w)

theorem getBit_eq (w : ℕ) (mem : ℕ → ℕ) (bitSize i : ℕ) :
    getBit w mem i = (BitMemory.State.mk mem bitSize).getBit w i := by
  simp [getBit, BitMemory.State.getBit, BitPacking.readBit]

/-- Read a `b`-bit field at bit offset `a` from word-indexed memory `mem` at word width `w`. -/
def getField (w : ℕ) (mem : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else
    let q₀ := a / w
    let lo := a % w
    if w - lo < b then
      let lowLen := w - lo
      let highLen := b - lowLen
      extractSlice (mem q₀) lo lowLen |||
        (extractSlice (mem (q₀ + 1)) 0 highLen <<< lowLen)
    else
      extractSlice (mem q₀) lo b

theorem getField_eq (w : ℕ) (mem : ℕ → ℕ) (bitSize a b : ℕ) :
    getField w mem a b = (BitMemory.State.mk mem bitSize).getField w a b := by
  simp only [getField, BitMemory.State.getField, BitPacking.readField, extractSlice, bitMask,
    BitPacking.extractSlice, BitPacking.bitMask, Nat.zero_add]

/-- Clear bits in `[lo, hi)` of word `q` at word width `w`. -/
def clearRangeWord (w word q lo hi : ℕ) : ℕ :=
  let start := lo - q * w
  let stop := min w (hi - q * w)
  clearMask (word &&& bitMask w) (sliceMask start (stop - start))

/-- Clear bits in `[lo, hi)` across all words of `mem` at word width `w`. -/
def clearRangeMem (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → ℕ :=
  fun q => clearRangeWord w (mem q) q lo hi

theorem clearRangeMem_eq (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) :
    clearRangeMem w mem lo hi = BitMemory.clearRangeMem w mem lo hi := rfl

/-- Demonic transition relation for growing `(mem, bitSize)` by `δ` bits to `(mem', bitSize')`:
`bitSize' = bitSize + δ`, every word in `mem'` fits in `w` bits, all bits below `bitSize` are
preserved, and all bits at or above `bitSize + δ` are zero (`false`), while the newly obtained
bits in `[bitSize, bitSize + δ)` hold arbitrary demonically chosen Boolean values. -/
def DirtyGrow (w : ℕ) (mem : ℕ → ℕ) (bitSize δ : ℕ) (mem' : ℕ → ℕ) (bitSize' : ℕ) : Prop :=
  bitSize' = bitSize + δ ∧
  (∀ q, mem' q < 2 ^ w) ∧
  (∀ i < bitSize, getBit w mem' i = getBit w mem i) ∧
  (∀ i, bitSize + δ ≤ i → getBit w mem' i = false)

theorem dirtyGrow_iff (w : ℕ) (mem : ℕ → ℕ) (bitSize δ : ℕ) (mem' : ℕ → ℕ) (bitSize' : ℕ) :
    DirtyGrow w mem bitSize δ mem' bitSize' ↔
      BitMemory.dirtyStep w ⟨mem, bitSize⟩ (.grow δ) ⟨mem', bitSize'⟩ bitSize := by
  simp only [DirtyGrow, BitMemory.dirtyStep, getBit_eq w mem bitSize, getBit_eq w mem' bitSize',
    Fits, true_and]

/-! ## Part 2: Polymorphic Bit-Resizable Word-RAM Presentation -/

/-- Polymorphic signature of the bit-resizable Word-RAM definitions in
`BitResizableDictionaryAbstract.lean`. -/
structure MachinePresentation where
  BinOp : Type
  add : BinOp
  sub : BinOp
  mul : BinOp
  div : BinOp
  mod : BinOp
  and : BinOp
  or : BinOp
  xor : BinOp
  shiftLeft : BinOp
  shiftRight : BinOp
  evalBinOp : BinOp → ℕ → ℕ → ℕ
  Cond : ℕ → Type
  eq {r : ℕ} : Fin r → Fin r → Cond r
  lt {r : ℕ} : Fin r → Fin r → Cond r
  OpInstr : ℕ → Type
  const {r : ℕ} : Fin r → ℕ → OpInstr r
  copy {r : ℕ} : Fin r → Fin r → OpInstr r
  bin {r : ℕ} : BinOp → Fin r → Fin r → Fin r → OpInstr r
  width {r : ℕ} : Fin r → OpInstr r
  load {r : ℕ} : Fin r → Fin r → OpInstr r
  store {r : ℕ} : Fin r → Fin r → OpInstr r
  Code : ℕ → Type
  op {r : ℕ} : OpInstr r → Code r
  grow {r : ℕ} : Fin r → Fin r → Code r
  shrink {r : ℕ} : Fin r → Code r
  size {r : ℕ} : Fin r → Code r
  seq {r : ℕ} : Code r → Code r → Code r
  branch {r : ℕ} : Cond r → Code r → Code r → Code r
  loop {r : ℕ} : Cond r → Code r → Code r
  rand {r : ℕ} : Fin r → Fin r → Code r
  Data : ℕ → Type
  mkData {r : ℕ} : (Fin r → ℕ) → (ℕ → ℕ) → ℕ → Data r
  regs {r : ℕ} : Data r → Fin r → ℕ
  mem {r : ℕ} : Data r → ℕ → ℕ
  bitSize {r : ℕ} : Data r → ℕ
  evalOp {r : ℕ} : ℕ → OpInstr r → Data r → Option (Data r)
  CondHolds {r : ℕ} : Cond r → Data r → Prop
  DemonicExecWithin {r : ℕ} : ℕ → Code r → Data r → (Data r → Prop) → ℕ → Prop

namespace MachinePresentation

variable (S : MachinePresentation)

/-- Translate a library `Cslib.WordRAM.BinOp` to `S.BinOp`. -/
def binOpOf : Cslib.WordRAM.BinOp → S.BinOp
  | .add => S.add
  | .sub => S.sub
  | .mul => S.mul
  | .div => S.div
  | .mod => S.mod
  | .and => S.and
  | .or => S.or
  | .xor => S.xor
  | .shiftLeft => S.shiftLeft
  | .shiftRight => S.shiftRight

/-- Translate a library `Cslib.WordRAM.Cond r` to `S.Cond r`. -/
def condOf {r : ℕ} : Cslib.WordRAM.Cond r → S.Cond r
  | .eq i j => S.eq i j
  | .lt i j => S.lt i j

/-- Translate a library `Cslib.WordRAM.Op .standard r` to `S.OpInstr r`. -/
def opInstrOf {r : ℕ} : Cslib.WordRAM.Op .standard r → S.OpInstr r
  | .const d v => S.const d v
  | .copy d s => S.copy d s
  | .alu (.bin f) d args =>
    S.bin (S.binOpOf f) d (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)
  | .alu .width d _ => S.width d
  | .load d a => S.load d a
  | .store a s => S.store a s

/-- Translate a library `BitRAM.Code .standard r` to `S.Code r`. -/
def codeOf {r : ℕ} : BitRAM.Code .standard r → S.Code r
  | .op o => S.op (S.opInstrOf o)
  | .grow dst δReg => S.grow dst δReg
  | .shrink δReg => S.shrink δReg
  | .size dst => S.size dst
  | .seq c₁ c₂ => S.seq (codeOf c₁) (codeOf c₂)
  | .branch c pos neg => S.branch (S.condOf c) (codeOf pos) (codeOf neg)
  | .loop c body => S.loop (S.condOf c) (codeOf body)
  | .rand dst src => S.rand dst src

/-- Translate a library `BitRAM.Data r` to `S.Data r`. -/
def dataOf {r : ℕ} (x : BitRAM.Data r) : S.Data r :=
  S.mkData x.regs x.mem x.bitSize

/-- Translate `S.Data r` back to `BitRAM.Data r`. -/
def dataTo {r : ℕ} (x : S.Data r) : BitRAM.Data r :=
  ⟨S.regs x, S.mem x, S.bitSize x⟩

/-- Well-formedness of `S.Data r` at word width `w`. -/
def DataWellFormed {r : ℕ} (w : ℕ) (x : S.Data r) : Prop :=
  (∀ i : Fin r, S.regs x i < 2 ^ w) ∧
  (∀ q : ℕ, S.mem x q < 2 ^ w) ∧
  S.bitSize x < 2 ^ w ∧
  (∀ i : ℕ, S.bitSize x ≤ i → getBit w (S.mem x) i = false)

end MachinePresentation

/-- Equational and inductive laws for `S : MachinePresentation`. -/
structure MachineLaws (S : MachinePresentation) : Prop where
  regs_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (sz : ℕ),
    S.regs (S.mkData regs mem sz) = regs
  mem_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (sz : ℕ),
    S.mem (S.mkData regs mem sz) = mem
  bitSize_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (sz : ℕ),
    S.bitSize (S.mkData regs mem sz) = sz
  data_eta : ∀ {r : ℕ} (x : S.Data r),
    S.mkData (S.regs x) (S.mem x) (S.bitSize x) = x
  evalBinOp_eq : ∀ (f : Cslib.WordRAM.BinOp) (x y : ℕ),
    S.evalBinOp (S.binOpOf f) x y = f.eval x y
  condHolds_eq : ∀ {r : ℕ} (i j : Fin r) (x : S.Data r),
    S.CondHolds (S.eq i j) x ↔ S.regs x i = S.regs x j
  condHolds_lt : ∀ {r : ℕ} (i j : Fin r) (x : S.Data r),
    S.CondHolds (S.lt i j) x ↔ S.regs x i < S.regs x j
  evalOp_const : ∀ {r : ℕ} (w : ℕ) (d : Fin r) (v : ℕ) (x : S.Data r),
    S.evalOp w (S.const d v) x =
      if v < 2 ^ w then some (S.mkData (Function.update (S.regs x) d v) (S.mem x) (S.bitSize x))
      else none
  evalOp_copy : ∀ {r : ℕ} (w : ℕ) (d s : Fin r) (x : S.Data r),
    S.evalOp w (S.copy d s) x =
      some (S.mkData (Function.update (S.regs x) d (S.regs x s)) (S.mem x) (S.bitSize x))
  evalOp_bin : ∀ {r : ℕ} (w : ℕ) (f : S.BinOp) (d i j : Fin r) (x : S.Data r),
    S.evalOp w (S.bin f d i j) x =
      let v := S.evalBinOp f (S.regs x i) (S.regs x j)
      if v < 2 ^ w then some (S.mkData (Function.update (S.regs x) d v) (S.mem x) (S.bitSize x))
      else none
  evalOp_width : ∀ {r : ℕ} (w : ℕ) (d : Fin r) (x : S.Data r),
    S.evalOp w (S.width d) x =
      if w < 2 ^ w then some (S.mkData (Function.update (S.regs x) d w) (S.mem x) (S.bitSize x))
      else none
  evalOp_load : ∀ {r : ℕ} (w : ℕ) (d a : Fin r) (x : S.Data r),
    S.evalOp w (S.load d a) x =
      if S.regs x a < ceilDiv (S.bitSize x) w then
        some (S.mkData
          (Function.update (S.regs x) d (S.mem x (S.regs x a))) (S.mem x) (S.bitSize x))
      else none
  evalOp_store : ∀ {r : ℕ} (w : ℕ) (a s : Fin r) (x : S.Data r),
    S.evalOp w (S.store a s) x =
      if S.regs x a < ceilDiv (S.bitSize x) w then
        some (S.mkData
          (S.regs x) (Function.update (S.mem x) (S.regs x a) (S.regs x s)) (S.bitSize x))
      else none
  exec_op : ∀ {r : ℕ} {w : ℕ} {o : S.OpInstr r} {x y : S.Data r} {P : S.Data r → Prop} {T : ℕ},
    S.evalOp w o x = some y → P y → 1 ≤ T →
    S.DemonicExecWithin w (S.op o) x P T
  exec_grow : ∀ {r : ℕ} {w : ℕ} {dst δReg : Fin r} {x : S.Data r} {P : S.Data r → Prop} {T : ℕ},
    S.bitSize x + S.regs x δReg < 2 ^ w →
    max 1 (ceilDiv (S.regs x δReg) w) ≤ T →
    (∀ (mem' : ℕ → ℕ) (bitSize' : ℕ),
      DirtyGrow w (S.mem x) (S.bitSize x) (S.regs x δReg) mem' bitSize' →
      P (S.mkData (Function.update (S.regs x) dst (S.bitSize x)) mem' bitSize')) →
    S.DemonicExecWithin w (S.grow dst δReg) x P T
  exec_shrink : ∀ {r : ℕ} {w : ℕ} {δReg : Fin r} {x : S.Data r} {P : S.Data r → Prop} {T : ℕ},
    S.regs x δReg ≤ S.bitSize x →
    max 1 (ceilDiv (S.regs x δReg) w) ≤ T →
    P (S.mkData (S.regs x)
        (clearRangeMem w (S.mem x) (S.bitSize x - S.regs x δReg) (S.bitSize x))
        (S.bitSize x - S.regs x δReg)) →
    S.DemonicExecWithin w (S.shrink δReg) x P T
  exec_size : ∀ {r : ℕ} {w : ℕ} {dst : Fin r} {x : S.Data r} {P : S.Data r → Prop} {T : ℕ},
    S.bitSize x < 2 ^ w →
    P (S.mkData (Function.update (S.regs x) dst (S.bitSize x)) (S.mem x) (S.bitSize x)) →
    1 ≤ T →
    S.DemonicExecWithin w (S.size dst) x P T
  exec_seq : ∀ {r : ℕ} {w : ℕ} {c₁ c₂ : S.Code r} {x : S.Data r} {Q P : S.Data r → Prop}
    {T₁ T₂ T : ℕ},
    S.DemonicExecWithin w c₁ x Q T₁ →
    (∀ y, Q y → S.DemonicExecWithin w c₂ y P T₂) →
    T₁ + T₂ ≤ T →
    S.DemonicExecWithin w (S.seq c₁ c₂) x P T
  exec_branch_pos : ∀ {r : ℕ} {w : ℕ} {c : S.Cond r} {pos neg : S.Code r} {x : S.Data r}
    {P : S.Data r → Prop} {T₀ T : ℕ},
    S.CondHolds c x → S.DemonicExecWithin w pos x P T₀ → T₀ + 1 ≤ T →
    S.DemonicExecWithin w (S.branch c pos neg) x P T
  exec_branch_neg : ∀ {r : ℕ} {w : ℕ} {c : S.Cond r} {pos neg : S.Code r} {x : S.Data r}
    {P : S.Data r → Prop} {T₀ T : ℕ},
    ¬S.CondHolds c x → S.DemonicExecWithin w neg x P T₀ → T₀ + 2 ≤ T →
    S.DemonicExecWithin w (S.branch c pos neg) x P T

/-! ### Correspondence Lemmas for `MachinePresentation` -/

theorem dataTo_dataOf {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ} (x : BitRAM.Data r) :
    S.dataTo (S.dataOf x) = x := by
  cases x
  simp [MachinePresentation.dataTo, MachinePresentation.dataOf,
    hS.regs_mk, hS.mem_mk, hS.bitSize_mk]

theorem dataOf_dataTo {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ} (x : S.Data r) :
    S.dataOf (S.dataTo x) = x :=
  hS.data_eta x

theorem dataWellFormed_iff {S : MachinePresentation} {r w : ℕ}
    (x : S.Data r) :
    S.DataWellFormed w x ↔ (S.dataTo x).WellFormed w := by
  unfold MachinePresentation.DataWellFormed MachinePresentation.dataTo
  constructor
  · rintro ⟨hregs, hmem, hsz, hzero⟩
    refine ⟨hregs, ⟨hmem, hsz, fun i hi => ?_⟩⟩
    dsimp only [BitRAM.Data.toBitMemoryState] at hi ⊢
    rw [← getBit_eq w (S.mem x) (S.bitSize x) i]
    exact hzero i hi
  · rintro ⟨hregs, ⟨hmem, hsz, hzero⟩⟩
    refine ⟨hregs, hmem, hsz, fun i hi => ?_⟩
    rw [getBit_eq w (S.mem x) (S.bitSize x) i]
    exact hzero i hi

theorem condHolds_iff {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ}
    (c : Cslib.WordRAM.Cond r) (x : BitRAM.Data r) :
    S.CondHolds (S.condOf c) (S.dataOf x) ↔ BitRAM.CondHolds c x := by
  cases c with
  | eq i j =>
    simp only [MachinePresentation.condOf, hS.condHolds_eq, MachinePresentation.dataOf,
      hS.regs_mk, BitRAM.CondHolds, Cslib.WordRAM.Cond.Holds, BitRAM.Data.toWordRAMData]
  | lt i j =>
    simp only [MachinePresentation.condOf, hS.condHolds_lt, MachinePresentation.dataOf,
      hS.regs_mk, BitRAM.CondHolds, Cslib.WordRAM.Cond.Holds, BitRAM.Data.toWordRAMData]

theorem evalOp_map {S : MachinePresentation} (hS : MachineLaws S) {r w : ℕ}
    (o : Cslib.WordRAM.Op .standard r) (x y : BitRAM.Data r)
    (heval : BitRAM.evalOp w o x = some y) :
    S.evalOp w (S.opInstrOf o) (S.dataOf x) = some (S.dataOf y) := by
  cases o with
  | const d v =>
    change (if v < 2 ^ w then some (x.set d v) else none) = some y at heval
    split_ifs at heval with hv
    injection heval with hy
    subst hy
    simp only [MachinePresentation.opInstrOf, hS.evalOp_const, MachinePresentation.dataOf,
      hS.regs_mk, hS.mem_mk, hS.bitSize_mk, hv, ↓reduceIte, BitRAM.Data.set]
  | copy d s =>
    dsimp only [BitRAM.evalOp] at heval
    injection heval with hy
    subst hy
    simp only [MachinePresentation.opInstrOf, hS.evalOp_copy, MachinePresentation.dataOf,
      hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set]
  | alu f d args =>
    cases f with
    | bin bf =>
      change (if bf.eval (x.regs (args ⟨0, Nat.zero_lt_two⟩))
          (x.regs (args ⟨1, Nat.one_lt_two⟩)) < 2 ^ w then
        some (x.set d (bf.eval (x.regs (args ⟨0, Nat.zero_lt_two⟩))
          (x.regs (args ⟨1, Nat.one_lt_two⟩))))
      else none) = some y at heval
      split_ifs at heval with hv
      injection heval with hy
      subst hy
      simp only [MachinePresentation.opInstrOf, hS.evalOp_bin, MachinePresentation.dataOf,
        hS.regs_mk, hS.mem_mk, hS.bitSize_mk, hS.evalBinOp_eq, hv, ↓reduceIte, BitRAM.Data.set]
    | width =>
      change (if w < 2 ^ w then some (x.set d w) else none) = some y at heval
      split_ifs at heval with hw
      injection heval with hy
      subst hy
      simp only [MachinePresentation.opInstrOf, hS.evalOp_width, MachinePresentation.dataOf,
        hS.regs_mk, hS.mem_mk, hS.bitSize_mk, hw, ↓reduceIte, BitRAM.Data.set]
  | load d a =>
    dsimp only [BitRAM.evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    have hadm' : x.regs a < ceilDiv x.bitSize w := by
      rw [ceilDiv_eq]
      exact hadm
    simp only [MachinePresentation.opInstrOf, hS.evalOp_load, MachinePresentation.dataOf,
      hS.regs_mk, hS.mem_mk, hS.bitSize_mk, hadm', ↓reduceIte, BitRAM.Data.set]
  | store a s =>
    dsimp only [BitRAM.evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    have hadm' : x.regs a < ceilDiv x.bitSize w := by
      rw [ceilDiv_eq]
      exact hadm
    simp only [MachinePresentation.opInstrOf, hS.evalOp_store, MachinePresentation.dataOf,
      hS.regs_mk, hS.mem_mk, hS.bitSize_mk, hadm', ↓reduceIte, BitRAM.Data.write]

/-- Transfer any library `BitRAM.DemonicExecWithin` derivation to `S.DemonicExecWithin`. -/
theorem demonicExecWithin_mono {S : MachinePresentation} (hS : MachineLaws S)
    {r w : ℕ} {c : BitRAM.Code .standard r} {x : BitRAM.Data r}
    {P : BitRAM.Data r → Prop} {Q : S.Data r → Prop} {T : ℕ}
    (h : BitRAM.DemonicExecWithin w c x P T)
    (hPQ : ∀ y : BitRAM.Data r, P y → Q (S.dataOf y)) :
    S.DemonicExecWithin w (S.codeOf c) (S.dataOf x) Q T := by
  induction h generalizing Q with
  | op heval hp h1 =>
    exact hS.exec_op (evalOp_map hS _ _ _ heval) (hPQ _ hp) h1
  | @grow dst δReg x P T hfits hcost hp =>
    refine hS.exec_grow ?_ ?_ (fun mem' bitSize' hgrow => ?_)
    · simp only [MachinePresentation.dataOf, hS.bitSize_mk, hS.regs_mk]
      exact hfits
    · simp only [MachinePresentation.dataOf, hS.regs_mk, ceilDiv_eq]
      exact hcost
    · simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk] at hgrow ⊢
      have hstep : BitMemory.dirtyStep w x.toBitMemoryState (.grow (x.regs δReg))
          ⟨mem', bitSize'⟩ x.bitSize :=
        (dirtyGrow_iff w x.mem x.bitSize (x.regs δReg) mem' bitSize').mp hgrow
      exact hPQ ⟨Function.update x.regs dst x.bitSize, mem', bitSize'⟩ (hp ⟨mem', bitSize'⟩ hstep)
  | @shrink δReg x P T hle hcost hp =>
    refine hS.exec_shrink ?_ ?_ ?_
    · simp only [MachinePresentation.dataOf, hS.regs_mk, hS.bitSize_mk]
      exact hle
    · simp only [MachinePresentation.dataOf, hS.regs_mk, ceilDiv_eq]
      exact hcost
    · simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk,
        clearRangeMem_eq]
      exact hPQ _ hp
  | @size dst x P T hfits hp h1 =>
    refine hS.exec_size ?_ ?_ h1
    · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact hfits
    · simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk]
      exact hPQ (x.set dst x.bitSize) hp
  | @seq c₁ c₂ x Q_mid P T₁ T₂ T _ _ hsum ih₁ ih₂ =>
    refine hS.exec_seq
      (Q := fun y => Q_mid (S.dataTo y))
      (ih₁ fun y hy => by rwa [dataTo_dataOf hS])
      (fun y hy => ?_) hsum
    have h2 := ih₂ (S.dataTo y) hy hPQ
    rwa [dataOf_dataTo hS] at h2
  | branch_pos hc _ hsum ih =>
    exact hS.exec_branch_pos ((condHolds_iff hS _ _).mpr hc) (ih hPQ) hsum
  | branch_neg hc _ hsum ih =>
    exact hS.exec_branch_neg (fun h => hc ((condHolds_iff hS _ _).mp h)) (ih hPQ) hsum

/-! ## Part 3: Polymorphic Dynamic Dictionary Presentation -/

/-- Polymorphic signature of the capacity-unbounded dynamic dictionary specification in
`BitResizableDictionaryAbstract.lean`. -/
structure DictPresentation (S : MachinePresentation) where
  DictOp : ℕ → Type
  query {U : ℕ} : Fin U → DictOp U
  insert {U : ℕ} : Fin U → ℕ → DictOp U
  delete {U : ℕ} : Fin U → DictOp U
  dictOp_elim {U : ℕ} {α : Type} :
    (Fin U → α) → (Fin U → ℕ → α) → (Fin U → α) → DictOp U → α
  dictOp_induction {U : ℕ} {motive : DictOp U → Prop} :
    (∀ u, motive (query u)) → (∀ u v, motive (insert u v)) → (∀ u, motive (delete u)) →
    ∀ o, motive o
  stepDict {U : ℕ} : (Fin U → Option ℕ) → DictOp U → (Fin U → Option ℕ)
  validDictOp {U : ℕ} : ℕ → (Fin U → Option ℕ) → DictOp U → Prop
  ValidDictHistory {U : ℕ} : ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  decodeQueryRegs : S.Data 12 → Option ℕ
  ExecTrace :
    ∀ (U : ℕ), ℕ → ℕ → ∀ (EpochSeed : ℕ → Type), (∀ N, PMF (EpochSeed N)) →
      ∀ (Companion : Type),
      (∀ N, EpochSeed N → (Fin U → Option ℕ) → Companion → S.Data 12 → Prop) →
      (ℕ → (Fin U → Option ℕ) → Companion → ℕ) →
      (∀ N, EpochSeed N → (Fin U → Option ℕ) → DictOp U → ℕ) →
      List (DictOp U) → ∀ (N : ℕ), EpochSeed N → (Fin U → Option ℕ) →
        Companion → S.Data 12 → ℕ → Prop

namespace DictPresentation

variable {S : MachinePresentation} (D : DictPresentation S)

/-- Translate a library `Dynamic.Op U` to `D.DictOp U`. -/
def dictOpOf {U : ℕ} : Dynamic.Op U → D.DictOp U
  | .query u => D.query u
  | .insert u v => D.insert u v
  | .delete u => D.delete u

/-- Translate `D.DictOp U` back to `Dynamic.Op U`. -/
def dictOpTo {U : ℕ} (o : D.DictOp U) : Dynamic.Op U :=
  D.dictOp_elim Dynamic.Op.query Dynamic.Op.insert Dynamic.Op.delete o

end DictPresentation

/-- Equational specification for `D : DictPresentation S`. -/
structure DictLaws (S : MachinePresentation) (D : DictPresentation S) : Prop where
  dictOp_elim_query : ∀ {U : ℕ} {α : Type} (fq : Fin U → α) (fi : Fin U → ℕ → α)
    (fd : Fin U → α) (u : Fin U),
    D.dictOp_elim fq fi fd (D.query u) = fq u
  dictOp_elim_insert : ∀ {U : ℕ} {α : Type} (fq : Fin U → α) (fi : Fin U → ℕ → α)
    (fd : Fin U → α) (u : Fin U) (v : ℕ),
    D.dictOp_elim fq fi fd (D.insert u v) = fi u v
  dictOp_elim_delete : ∀ {U : ℕ} {α : Type} (fq : Fin U → α) (fi : Fin U → ℕ → α)
    (fd : Fin U → α) (u : Fin U),
    D.dictOp_elim fq fi fd (D.delete u) = fd u
  stepDict_query : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    D.stepDict s (D.query u) = s
  stepDict_insert : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    D.stepDict s (D.insert u v) = Function.update s u (some v)
  stepDict_delete : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    D.stepDict s (D.delete u) = Function.update s u none
  validDictOp_query : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    D.validDictOp V s (D.query u) ↔ True
  validDictOp_insert : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    D.validDictOp V s (D.insert u v) ↔ v < V
  validDictOp_delete : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    D.validDictOp V s (D.delete u) ↔ True
  validDictHistory_nil : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ),
    D.ValidDictHistory V s [] ↔ True
  validDictHistory_cons : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (o : D.DictOp U) (os : List (D.DictOp U)),
    D.ValidDictHistory V s (o :: os) ↔
      D.validDictOp V s o ∧ D.ValidDictHistory V (D.stepDict s o) os
  decodeQueryRegs_eq : ∀ (x : S.Data 12),
    D.decodeQueryRegs x =
      if S.regs x ⟨1, by decide⟩ = 0 then none else some (S.regs x ⟨0, by decide⟩)
  execTrace_nil :
    ∀ {U V w : ℕ} {EpochSeed : ℕ → Type} {epochSeedPMF : ∀ N, PMF (EpochSeed N)}
      {Companion : Type}
      {DictInv : ∀ N, EpochSeed N → (Fin U → Option ℕ) → Companion → S.Data 12 → Prop}
      {totalPotential : ℕ → (Fin U → Option ℕ) → Companion → ℕ}
      {stepOverhead : ∀ N, EpochSeed N → (Fin U → Option ℕ) → D.DictOp U → ℕ}
      {N : ℕ} {θ : EpochSeed N} {s_abs : Fin U → Option ℕ} {c : Companion} {x : S.Data 12},
      DictInv N θ s_abs c x →
      D.ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
        totalPotential stepOverhead [] N θ s_abs c x 0
  execTrace_cons :
    ∀ {U V w : ℕ} {EpochSeed : ℕ → Type} {epochSeedPMF : ∀ N, PMF (EpochSeed N)}
      {Companion : Type}
      {DictInv : ∀ N, EpochSeed N → (Fin U → Option ℕ) → Companion → S.Data 12 → Prop}
      {totalPotential : ℕ → (Fin U → Option ℕ) → Companion → ℕ}
      {stepOverhead : ∀ N, EpochSeed N → (Fin U → Option ℕ) → D.DictOp U → ℕ}
      {op : D.DictOp U} {ops : List (D.DictOp U)}
      {N N' : ℕ} {θ : EpochSeed N} {θ' : EpochSeed N'}
      {s_abs : Fin U → Option ℕ} {c c' : Companion}
      {x : S.Data 12} {code : S.Code 12} {T B_rest B_tot : ℕ},
      DictInv N θ s_abs c x →
      (∑' θ₀ : EpochSeed N,
        (epochSeedPMF N θ₀ : ℝ≥0∞) * ((stepOverhead N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 →
      B_tot = stepOverhead N θ s_abs op + B_rest →
      T + totalPotential N' (D.stepDict s_abs op) c' ≤
        totalPotential N s_abs c + stepOverhead N θ s_abs op →
      (∃ ts_rest : List ℕ,
        ts_rest.length = ops.length ∧
        ts_rest.sum ≤ totalPotential N' (D.stepDict s_abs op) c' + B_rest) →
      S.DemonicExecWithin w code x
        (fun y =>
          DictInv N' θ' (D.stepDict s_abs op) c' y ∧
          (∀ u, op = D.query u → D.decodeQueryRegs y = s_abs u) ∧
          D.ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
            totalPotential stepOverhead ops N' θ' (D.stepDict s_abs op) c' y B_rest)
        T →
      D.ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
        totalPotential stepOverhead (op :: ops) N θ s_abs c x B_tot

theorem dictOpTo_query {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (u : Fin U) :
    D.dictOpTo (D.query u) = .query u :=
  hD.dictOp_elim_query Dynamic.Op.query Dynamic.Op.insert Dynamic.Op.delete u

theorem dictOpTo_insert {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (u : Fin U) (v : ℕ) :
    D.dictOpTo (D.insert u v) = .insert u v :=
  hD.dictOp_elim_insert Dynamic.Op.query Dynamic.Op.insert Dynamic.Op.delete u v

theorem dictOpTo_delete {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (u : Fin U) :
    D.dictOpTo (D.delete u) = .delete u :=
  hD.dictOp_elim_delete Dynamic.Op.query Dynamic.Op.insert Dynamic.Op.delete u

theorem dictOpOf_dictOpTo {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (o : D.DictOp U) :
    D.dictOpOf (D.dictOpTo o) = o := by
  refine D.dictOp_induction (motive := fun o => D.dictOpOf (D.dictOpTo o) = o)
    (fun u => ?_) (fun u v => ?_) (fun u => ?_) o
  · rw [dictOpTo_query hD]; rfl
  · rw [dictOpTo_insert hD]; rfl
  · rw [dictOpTo_delete hD]; rfl

theorem stepDict_dictOpOf {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (s : Fin U → Option ℕ) (o : Dynamic.Op U) :
    D.stepDict s (D.dictOpOf o) = BitResizable.nextState s o := by
  cases o with
  | query u => exact hD.stepDict_query s u
  | insert u v => exact hD.stepDict_insert s u v
  | delete u => exact hD.stepDict_delete s u

theorem stepDict_eq_nextState {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (s : Fin U → Option ℕ) (o : D.DictOp U) :
    D.stepDict s o = BitResizable.nextState s (D.dictOpTo o) := by
  conv_lhs => rw [← dictOpOf_dictOpTo hD o]
  exact stepDict_dictOpOf hD s (D.dictOpTo o)

theorem validDictOp_iff {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U V : ℕ} (s : Fin U → Option ℕ) (o : D.DictOp U) :
    D.validDictOp V s o ↔ (BitResizable.spec U V).valid s (D.dictOpTo o) := by
  conv_lhs => rw [← dictOpOf_dictOpTo hD o]
  cases D.dictOpTo o with
  | query u => exact hD.validDictOp_query V s u
  | insert u v => exact hD.validDictOp_insert V s u v
  | delete u => exact hD.validDictOp_delete V s u

theorem validDictHistory_iff {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U V : ℕ} (s : Fin U → Option ℕ) (ops : List (D.DictOp U)) :
    D.ValidDictHistory V s ops ↔
      (BitResizable.spec U V).ValidHistory s (ops.map D.dictOpTo) := by
  induction ops generalizing s with
  | nil => exact hD.validDictHistory_nil V s
  | cons o os ih =>
    rw [List.map_cons, hD.validDictHistory_cons, validDictOp_iff hD, stepDict_eq_nextState hD]
    exact and_congr_right fun _ => ih (BitResizable.nextState s (D.dictOpTo o))

theorem decodeQueryRegs_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D) (y : BitRAM.Data 12) :
    D.decodeQueryRegs (S.dataOf y) = BitResizable.decodeQueryRegs y := by
  rw [hD.decodeQueryRegs_eq]
  simp only [MachinePresentation.dataOf, hS.regs_mk, BitResizable.decodeQueryRegs]
  rfl

/-! ## Part 4: Headline Bridge Theorems -/

/-- Exact space formula `dictBitSize U V w N n_t` from `BitResizable`. -/
abbrev dictBitSize (U V w N n_t : ℕ) : ℕ :=
  BitResizable.dictBitSize U V w N n_t

/-- Exact item bit-width `itemBits U V N` from `BitResizable`. -/
abbrev itemBits (U V N : ℕ) : ℕ :=
  BitResizable.itemBits U V N

/-- Pointwise space bound `dictBitSize_le_optBits`: whenever `EpochInv U N n_t` holds,
`dictBitSize U V w N n_t` is at most
`Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`. -/
theorem space_bound_of_epochInv {U V w N n_t : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hepoch : BitResizable.EpochInv U N n_t) :
    dictBitSize U V w N n_t ≤
      Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w :=
  BitResizable.dictBitSize_le_optBits hw hU hepoch

theorem compile_execTrace {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    {U V w : ℕ} (ops : List (D.DictOp U)) :
    ∀ {N : ℕ} {θ : Succinct.QuotHashSeed U N} {s_abs : Fin U → Option ℕ}
      {c : BitResizable.Companion} {x : BitRAM.Data 12} {B_tot : ℕ},
      BitResizable.ExecTrace U V w (ops.map D.dictOpTo) N θ s_abs c x B_tot →
      D.ExecTrace U V w
        (fun N => Succinct.QuotHashSeed U N)
        (fun N => BitResizable.epochSeedPMF U N)
        BitResizable.Companion
        (fun N θ s_abs c y => BitResizable.DictInv U V w N θ s_abs c (S.dataTo y))
        (fun N s_abs c => BitResizable.totalPotential U V w N s_abs c)
        (fun N θ s_abs op => BitResizable.stepOverhead U N θ s_abs (D.dictOpTo op))
        ops N θ s_abs c (S.dataOf x) B_tot := by
  induction ops with
  | nil =>
    intro N θ s_abs c x B_tot ⟨hinv, hB⟩
    subst hB
    refine hD.execTrace_nil ?_
    rwa [dataTo_dataOf hS]
  | cons op ops ih =>
    intro N θ s_abs c x B_tot htr
    simp only [List.map_cons, BitResizable.ExecTrace] at htr
    rcases htr with ⟨hinv, htsum, N', θ', c', code, T, B_rest, hB, hpot, hts, hexec⟩
    refine hD.execTrace_cons (N' := N') (θ' := θ') (c' := c')
      (code := S.codeOf code) (T := T) (B_rest := B_rest) ?_ htsum hB ?_ ?_ ?_
    · rwa [dataTo_dataOf hS]
    · rw [stepDict_eq_nextState hD]
      exact hpot
    · obtain ⟨ts_rest, hlen, hsum⟩ := hts
      rw [List.length_map] at hlen
      rw [stepDict_eq_nextState hD]
      exact ⟨ts_rest, hlen, hsum⟩
    · refine demonicExecWithin_mono hS hexec fun y ⟨hinv_y, hq_y, htr_y⟩ => ?_
      refine ⟨?_, ?_, ?_⟩
      · rw [dataTo_dataOf hS, stepDict_eq_nextState hD]
        exact hinv_y
      · intro u hu
        subst hu
        rw [decodeQueryRegs_dataOf hS hD]
        exact hq_y u (dictOpTo_query hD u)
      · rw [stepDict_eq_nextState hD]
        exact ih htr_y

/-- **Headline Bridge Theorem (`bitResizableDictionary`):**
For every `S : MachinePresentation` satisfying `MachineLaws S`, every `D : DictPresentation S`
satisfying `DictLaws S D`, and every `U, V, w : ℕ` with `4 ≤ w`, `U < 2 ^ w`, and `V ≤ 2 ^ w`,
there exist `(EpochSeed, epochSeedPMF, Companion, emptyCompanion, DictInv, totalPotential,
stepOverhead, dictBitSize, initCode, clientAllocBitsCode)` satisfying:
1. **Pointwise space tightness (`space_tight`):** whenever `DictInv N θ s_abs c x` holds at
   active key count `n_t = (Dynamic.dom s_abs).card`,
   * `S.DataWellFormed w x`,
   * `BitResizable.EpochInv U N n_t`,
   * `S.bitSize x = dictBitSize N n_t`, and
   * `S.bitSize x ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`;
2. **Expected `O(1)` amortized step transition (`step_transition`):** for every state satisfying
   `DictInv N θ s_abs c x` and every valid operation `op : D.DictOp U`
   (`D.validDictOp V s_abs op`),
   * the expected amortized overhead over `θ₀ ← epochSeedPMF N` is at most `8034`:
     `(∑' θ₀, (epochSeedPMF N θ₀ : ℝ≥0∞) * (stepOverhead N θ₀ s_abs op : ℝ≥0∞)) ≤ 8034`, and
   * under `∀ N' ≤ U, dictBitSize N' N' < 2 ^ w`, for any rebuild seed `θ_re`, there exist
     `N'`, `θ'`, `c'`, `code : S.Code 12`, and `T : ℕ` executing `op` in `≤ T` instructions under
     `S.DemonicExecWithin` with
     `T + totalPotential N' (D.stepDict s_abs op) c' ≤`
     `totalPotential N s_abs c + stepOverhead N θ s_abs op`;
3. **Full operation-sequence execution from empty (`seq_from_empty`):** from any well-formed state
   `x₀ : S.Data 12` with `S.bitSize x₀ = 0` and any valid history `ops : List (D.DictOp U)`
   (`D.ValidDictHistory V (Dynamic.empty U) ops`), `initCode θ₀` executes in `21` instructions
   to `y₀` (`S.bitSize y₀ = 4 * w`) and `ops` executes via `D.ExecTrace` with step instruction
   bounds `ts : List ℕ` (`ts.length = ops.length`, `ts.sum ≤ B_tot`);
4. **Client subroutine reuse of bits released by `delete` (`delete_reuses_released_bits`):** when an
   active key `u` (`(s_abs u).isSome`) is deleted within an epoch and the client immediately runs
   `clientAllocBitsCode b v_client` (`b ≤ BitResizable.itemBits U V N`, `b ≤ w`,
   `v_client < 2 ^ b`),
   `S.seq code_del (clientAllocBitsCode b v_client)` executes in `T + 46` instructions under
   `S.DemonicExecWithin`, shrinking `bitSize` by `BitResizable.itemBits U V N` bits and reusing the
   released interval `[S.bitSize x - BitResizable.itemBits U V N,`
   `S.bitSize x - BitResizable.itemBits U V N + b)` so that
   `S.bitSize z = S.bitSize x - BitResizable.itemBits U V N + b ≤ S.bitSize x`,
   `getField w (S.mem z) (S.bitSize x - BitResizable.itemBits U V N) b = v_client`, and all lower
   dictionary bits in `[0, S.bitSize x - BitResizable.itemBits U V N)` are preserved. -/
theorem bitResizableDictionary (S : MachinePresentation) (hS : MachineLaws S)
    (D : DictPresentation S) (hD : DictLaws S D)
    {U V w : ℕ} (hw : 4 ≤ w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w) :
    ∃ (EpochSeed : ℕ → Type)
      (epochSeedPMF : ∀ N, PMF (EpochSeed N))
      (_epochSeedNonempty : ∀ N, Nonempty (EpochSeed N))
      (Companion : Type)
      (emptyCompanion : Companion)
      (DictInv : ∀ N, EpochSeed N → (Fin U → Option ℕ) → Companion → S.Data 12 → Prop)
      (totalPotential : ℕ → (Fin U → Option ℕ) → Companion → ℕ)
      (stepOverhead : ∀ N, EpochSeed N → (Fin U → Option ℕ) → D.DictOp U → ℕ)
      (dictBitSize : ℕ → ℕ → ℕ)
      (initCode : EpochSeed 0 → S.Code 12)
      (clientAllocBitsCode : ℕ → ℕ → S.Code 12),
      dictBitSize 0 0 = 4 * w ∧
      (∀ N n_t, dictBitSize N (n_t + 1) = dictBitSize N n_t + BitResizable.itemBits U V N) ∧
      (∀ N n_t, BitResizable.EpochInv U N n_t →
        dictBitSize N n_t ≤
          Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w) ∧
      (∀ {N : ℕ} (θ : EpochSeed N) {s_abs : Fin U → Option ℕ} {c : Companion}
          {x : S.Data 12},
        DictInv N θ s_abs c x →
        let n_t := (Dynamic.dom s_abs).card
        S.DataWellFormed w x ∧
        BitResizable.EpochInv U N n_t ∧
        S.bitSize x = dictBitSize N n_t ∧
        S.bitSize x ≤
          Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w) ∧
      (∀ (_hfit_all : ∀ N' ≤ U, dictBitSize N' N' < 2 ^ w)
          {N : ℕ} (θ : EpochSeed N) {s_abs : Fin U → Option ℕ} {c : Companion}
          {x : S.Data 12},
        DictInv N θ s_abs c x →
        ∀ (op : D.DictOp U), D.validDictOp V s_abs op →
        ∀ (_θ_re : EpochSeed
            (BitResizable.targetCap U (Dynamic.dom (D.stepDict s_abs op)).card)),
          (∑' θ₀ : EpochSeed N,
            (epochSeedPMF N θ₀ : ℝ≥0∞) *
              ((stepOverhead N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
          ∃ (N' : ℕ) (θ' : EpochSeed N') (c' : Companion)
            (code : S.Code 12) (T : ℕ),
            S.DemonicExecWithin w code x
              (fun y =>
                DictInv N' θ' (D.stepDict s_abs op) c' y ∧
                (∀ u, op = D.query u → D.decodeQueryRegs y = s_abs u)) T ∧
            T + totalPotential N' (D.stepDict s_abs op) c' ≤
              totalPotential N s_abs c + stepOverhead N θ s_abs op) ∧
      (∀ (_hfit_all : ∀ N' ≤ U, dictBitSize N' N' < 2 ^ w)
          (θ₀ : EpochSeed 0) {x₀ : S.Data 12},
        S.DataWellFormed w x₀ → S.bitSize x₀ = 0 →
        ∀ (ops : List (D.DictOp U)), D.ValidDictHistory V (Dynamic.empty U) ops →
          ∃ B_tot : ℕ,
            S.DemonicExecWithin w (initCode θ₀) x₀
              (fun y₀ =>
                DictInv 0 θ₀ (Dynamic.empty U) emptyCompanion y₀ ∧
                S.bitSize y₀ = 4 * w ∧
                D.ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
                  totalPotential stepOverhead ops 0 θ₀ (Dynamic.empty U)
                  emptyCompanion y₀ B_tot ∧
                ∃ ts : List ℕ, ts.length = ops.length ∧ ts.sum ≤ B_tot)
              21) ∧
      (∀ {N : ℕ} (θ : EpochSeed N) {s_abs : Fin U → Option ℕ} {c : Companion}
          {x : S.Data 12},
        DictInv N θ s_abs c x →
        ∀ (u : Fin U), (s_abs u).isSome →
        BitResizable.EpochInv U N (Dynamic.dom (D.stepDict s_abs (D.delete u))).card →
        ∀ {b v_client : ℕ}, b ≤ w → b ≤ BitResizable.itemBits U V N → v_client < 2 ^ b →
          let s_abs' := D.stepDict s_abs (D.delete u)
          let bit_after_del := S.bitSize x - BitResizable.itemBits U V N
          ∃ (c' : Companion) (code_del : S.Code 12) (T : ℕ),
            T + totalPotential N s_abs' c' ≤
              totalPotential N s_abs c + stepOverhead N θ s_abs (D.delete u) ∧
            (∑' θ₀ : EpochSeed N,
              (epochSeedPMF N θ₀ : ℝ≥0∞) *
                ((stepOverhead N θ₀ s_abs (D.delete u) : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
            S.DemonicExecWithin w (S.seq code_del (clientAllocBitsCode b v_client)) x
              (fun z =>
                ∃ y : S.Data 12,
                  DictInv N θ s_abs' c' y ∧
                  S.bitSize y = bit_after_del ∧
                  S.DataWellFormed w z ∧
                  S.bitSize z = bit_after_del + b ∧
                  S.bitSize z ≤ S.bitSize x ∧
                  getField w (S.mem z) bit_after_del b = v_client ∧
                  (∀ i < bit_after_del,
                    getBit w (S.mem z) i = getBit w (S.mem y) i))
              (T + 46)) := by
  have hw0 : 0 < w := by omega
  have hU_le : U ≤ 2 ^ w := Nat.le_of_lt hU
  refine ⟨fun N => Succinct.QuotHashSeed U N,
    fun N => BitResizable.epochSeedPMF U N,
    fun N => inferInstance,
    BitResizable.Companion,
    BitResizable.Companion.empty,
    fun N θ s_abs c x => BitResizable.DictInv U V w N θ s_abs c (S.dataTo x),
    fun N s_abs c => BitResizable.totalPotential U V w N s_abs c,
    fun N θ s_abs op => BitResizable.stepOverhead U N θ s_abs (D.dictOpTo op),
    BitResizable.dictBitSize U V w,
    fun θ₀ => S.codeOf (BitResizable.initDictCode U V w θ₀),
    fun b v => S.codeOf (BitResizable.clientAllocBitsCode b v),
    by simp [BitResizable.dictBitSize, BitResizable.epochMetaBits, BitResizable.epochMetaWords],
    by intro N n_t; simp only [BitResizable.dictBitSize]; ring,
    fun N n_t hepoch => BitResizable.dictBitSize_le_optBits hw0 hU_le hepoch,
    ?_, ?_, ?_, ?_⟩
  · -- 1. Space tightness
    intro N θ s_abs c x hinv
    have hwf : S.DataWellFormed w x := (dataWellFormed_iff x).mpr hinv.wf
    have hsz : S.bitSize x = BitResizable.dictBitSize U V w N (Dynamic.dom s_abs).card :=
      hinv.bitSize_eq
    have htight : S.bitSize x ≤
        Dynamic.optBits U V (Dynamic.dom s_abs).card +
          680 * (Dynamic.dom s_abs).card * Dynamic.logLogFactor (Dynamic.dom s_abs).card +
          218 * w :=
      hinv.space_tight hw0 hU
    exact ⟨hwf, hinv.valid.epoch, hsz, htight⟩
  · -- 2. Single-step transition
    intro hfit_all N θ s_abs c x hinv op hval_op θ_re
    have hval_lib : (BitResizable.spec U V).valid s_abs (D.dictOpTo op) :=
      (validDictOp_iff hD s_abs op).mp hval_op
    have htsum := BitResizable.tsum_stepOverhead_le hinv.valid.epoch (D.dictOpTo op)
    have θ_re' : Succinct.QuotHashSeed U
        (BitResizable.targetCap U
          (Dynamic.dom (BitResizable.nextState s_abs (D.dictOpTo op))).card) := by
      rwa [← stepDict_eq_nextState hD s_abs op]
    obtain ⟨N', θ', c', code, T, _, hexec, hcost⟩ :=
      BitResizable.step_transition hw hU hV hfit_all θ hinv (D.dictOpTo op) hval_lib θ_re'
    refine ⟨htsum, N', θ', c', S.codeOf code, T, ?_, ?_⟩
    · rw [← dataOf_dataTo hS x]
      refine demonicExecWithin_mono hS hexec fun y ⟨hinv_y, hq_y⟩ => ?_
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [dataTo_dataOf hS, stepDict_eq_nextState hD]
        exact hinv_y
      · intro u hu
        subst hu
        rw [decodeQueryRegs_dataOf hS hD]
        exact hq_y u (dictOpTo_query hD u)
    · rw [stepDict_eq_nextState hD]
      exact hcost
  · -- 3. Sequence execution from empty
    intro hfit_all θ₀ x₀ hx_wf hx_sz ops hvh
    have hx_wf_lib : (S.dataTo x₀).WellFormed w := (dataWellFormed_iff x₀).mp hx_wf
    have hvh_lib : (BitResizable.spec U V).ValidHistory (Dynamic.empty U) (ops.map D.dictOpTo) :=
      (validDictHistory_iff hD (Dynamic.empty U) ops).mp hvh
    obtain ⟨B_tot, hexec⟩ :=
      BitResizable.seq_transition_from_empty hw hU hV hfit_all θ₀ hx_wf_lib hx_sz
        (ops.map D.dictOpTo) hvh_lib
    refine ⟨B_tot, ?_⟩
    rw [← dataOf_dataTo hS x₀]
    refine demonicExecWithin_mono hS hexec fun y₀ ⟨hinv₀, hsz₀, htr₀, ts, hlen, hsum⟩ => ?_
    rw [List.length_map] at hlen
    refine ⟨?_, ?_, compile_execTrace hS hD ops htr₀, ts, hlen, hsum⟩
    · dsimp only
      rwa [dataTo_dataOf hS]
    · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact hsz₀
  · -- 4. Client subroutine reuse of released bits on `delete`
    intro N θ s_abs c x hinv u hsome hepoch' b v_client hbw hb_item hv_client
    have hepoch_lib : BitResizable.EpochInv U N
        (Dynamic.dom (BitResizable.nextState s_abs (.delete u))).card := by
      rwa [← dictOpTo_delete hD u, ← stepDict_eq_nextState hD s_abs (D.delete u)]
    obtain ⟨c', code_del, T, hcost, htsum, hexec⟩ :=
      BitResizable.delete_reuses_released_bits_subroutine hw hU hV θ hinv u hsome hepoch_lib
        hbw hb_item hv_client
    refine ⟨c', S.codeOf code_del, T, ?_, ?_, ?_⟩
    · change T + BitResizable.totalPotential U V w N (D.stepDict s_abs (D.delete u)) c' ≤
        BitResizable.totalPotential U V w N s_abs c +
          BitResizable.stepOverhead U N θ s_abs (D.dictOpTo (D.delete u))
      rw [stepDict_eq_nextState hD, dictOpTo_delete hD]
      exact hcost
    · change (∑' θ₀ : Succinct.QuotHashSeed U N,
        (BitResizable.epochSeedPMF U N θ₀ : ℝ≥0∞) *
          ((BitResizable.stepOverhead U N θ₀ s_abs (D.dictOpTo (D.delete u)) : ℕ) : ℝ≥0∞)) ≤ 8034
      rw [dictOpTo_delete hD]
      exact htsum
    · have hexec' := demonicExecWithin_mono hS hexec
        (Q := fun z =>
          ∃ y : S.Data 12,
            BitResizable.DictInv U V w N θ (D.stepDict s_abs (D.delete u)) c' (S.dataTo y) ∧
            S.bitSize y = S.bitSize x - BitResizable.itemBits U V N ∧
            S.DataWellFormed w z ∧
            S.bitSize z = (S.bitSize x - BitResizable.itemBits U V N) + b ∧
            S.bitSize z ≤ S.bitSize x ∧
            getField w (S.mem z) (S.bitSize x - BitResizable.itemBits U V N) b = v_client ∧
            (∀ i < S.bitSize x - BitResizable.itemBits U V N,
              getBit w (S.mem z) i = getBit w (S.mem y) i))
        fun z ⟨y, hinv_y, hy_sz, hz_wf, hz_sz, hz_le, hz_field, hz_bits⟩ => by
          refine ⟨S.dataOf y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [dataTo_dataOf hS, stepDict_eq_nextState hD, dictOpTo_delete hD]
            exact hinv_y
          · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
            exact hy_sz
          · exact (dataWellFormed_iff (S.dataOf z)).mpr
              (by rw [dataTo_dataOf hS]; exact hz_wf)
          · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
            exact hz_sz
          · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
            exact hz_le
          · simp only [MachinePresentation.dataOf, hS.mem_mk]
            rw [getField_eq w z.mem z.bitSize]
            exact hz_field
          · intro i hi
            simp only [MachinePresentation.dataOf, hS.mem_mk]
            rw [getBit_eq w z.mem z.bitSize i, getBit_eq w y.mem y.bitSize i]
            exact hz_bits i hi
      rw [dataOf_dataTo hS] at hexec'
      exact hexec'

end ComplexityAbstracts.BitResizableDictionaryBridge
