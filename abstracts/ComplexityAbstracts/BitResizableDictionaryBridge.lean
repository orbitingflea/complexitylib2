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
bit-resizable succinct dynamic dictionary (`Cslib.DataStructure.Dictionary.BitResizable`) on the
bit-granular resizable Word-RAM model (`Cslib.WordRAM.BitRAM`).

This bridge defines polymorphic presentations `MachinePresentation` and `DictPresentation` of the
abstract's bit-resizable Word-RAM and dynamic dictionary types, proves step-by-step transfer of
both `BitRAM.DemonicExecWithin` (including `.loop`) and deterministic fuel evaluation
`BitRAM.evalWithOracle`, and packages:
1. `bitResizableDictionary_compiled`: uniform parameter-free `BitRAM.Code .standard 280` programs
   (`initEmptyRegCode`, `inEpochStepRegCode`, `inEpochDeleteOpRegCode`, `clientAllocBitsRegCode`,
   `clientFreeBitsRegCode`) quantified outside `∀ U V w`, establishing operational initialization,
   in-epoch `query`/`insert`/`delete` sequence execution in `O(1)` expected amortized instructions,
   pointwise succinct bit space `OPT(U, V, n_t) + 680 * n_t * logLogFactor n_t + 218 * w`,
   faithful representation `rep_inj`, and client subroutine reuse of bits released on `delete`;
2. `bitResizableDictionary_multiEpoch_pure`: pure mathematical multi-epoch hysteresis,
   non-vacuous reached-capacity fit (`ReachedEpochsFit`, holding even at `U = 2 ^ w - 1`),
   every-step succinct space from empty, and `O(1)` amortized rebuild potential (`epochPotential`).
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

/-! ## Part 1: Bitwise, Memory, and Oracle Primitives Shared with the Abstract -/

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

/-- Demonic transition relation for growing `(mem, bitSize)` by `δ` bits to `(mem', bitSize')`. -/
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

/-- Validity of a deterministic demonic `grow` memory oracle `oracle`. -/
def DirtyGrowOracle (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) : Prop :=
  ∀ mem bitSize δ, DirtyGrow w mem bitSize δ (oracle mem bitSize δ) (bitSize + δ)

theorem dirtyGrowOracle_iff (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) :
    DirtyGrowOracle w oracle ↔ BitRAM.DirtyGrowOracle w oracle := by
  simp only [DirtyGrowOracle, BitRAM.DirtyGrowOracle, dirtyGrow_iff]

/-- Canonical zero-initialized `grow` oracle at word width `w`. -/
def zeroGrowOracle (w : ℕ) : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ) :=
  fun mem bitSize _ q => clearRangeWord w (mem q) q bitSize ((q + 1) * w)

theorem dirtyGrowOracle_zeroGrowOracle {w : ℕ} (hw : 0 < w) :
    DirtyGrowOracle w (zeroGrowOracle w) :=
  (dirtyGrowOracle_iff w (zeroGrowOracle w)).mpr (BitRAM.dirtyGrowOracle_zeroGrowOracle hw)

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
  evalWithOracle {r : ℕ} : ℕ → ((ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) → ℕ → Code r → Data r → Data r
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

/-- Update register `i` to `v` in `S.Data r`. -/
def setReg {r : ℕ} (x : S.Data r) (i : Fin r) (v : ℕ) : S.Data r :=
  S.mkData (Function.update (S.regs x) i v) (S.mem x) (S.bitSize x)

/-- Shrink `S.Data r` by `b` bits (clearing `[bitSize - b, bitSize)`). -/
def shrinkData {r : ℕ} (w b : ℕ) (x : S.Data r) : S.Data r :=
  S.mkData (S.regs x)
    (clearRangeMem w (S.mem x) (S.bitSize x - b) (S.bitSize x))
    (S.bitSize x - b)

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
  evalWithOracle_op : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (o : S.OpInstr r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.op o) x = (S.evalOp w o x).getD x
  evalWithOracle_grow : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (dst δReg : Fin r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.grow dst δReg) x =
      S.mkData (Function.update (S.regs x) dst (S.bitSize x))
        (oracle (S.mem x) (S.bitSize x) (S.regs x δReg))
        (S.bitSize x + S.regs x δReg)
  evalWithOracle_shrink : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (δReg : Fin r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.shrink δReg) x =
      S.mkData (S.regs x)
        (clearRangeMem w (S.mem x) (S.bitSize x - S.regs x δReg) (S.bitSize x))
        (S.bitSize x - S.regs x δReg)
  evalWithOracle_size : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (dst : Fin r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.size dst) x =
      S.mkData (Function.update (S.regs x) dst (S.bitSize x)) (S.mem x) (S.bitSize x)
  evalWithOracle_rand : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (dst src : Fin r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.rand dst src) x = x
  evalWithOracle_seq : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) (c₁ c₂ : S.Code r) (x : S.Data r),
    S.evalWithOracle w oracle fuel (S.seq c₁ c₂) x =
      S.evalWithOracle w oracle fuel c₂ (S.evalWithOracle w oracle fuel c₁ x)
  evalWithOracle_branch_pos : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) {c : S.Cond r} (pos neg : S.Code r) {x : S.Data r},
    S.CondHolds c x →
    S.evalWithOracle w oracle fuel (S.branch c pos neg) x =
      S.evalWithOracle w oracle fuel pos x
  evalWithOracle_branch_neg : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) {c : S.Cond r} (pos neg : S.Code r) {x : S.Data r},
    ¬S.CondHolds c x →
    S.evalWithOracle w oracle fuel (S.branch c pos neg) x =
      S.evalWithOracle w oracle fuel neg x
  evalWithOracle_loop_zero : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (c : S.Cond r) (body : S.Code r) (x : S.Data r),
    S.evalWithOracle w oracle 0 (S.loop c body) x = x
  evalWithOracle_loop_succ_pos : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) {c : S.Cond r} (body : S.Code r) {x : S.Data r},
    S.CondHolds c x →
    S.evalWithOracle w oracle (fuel + 1) (S.loop c body) x =
      S.evalWithOracle w oracle fuel (S.loop c body) (S.evalWithOracle w oracle fuel body x)
  evalWithOracle_loop_succ_neg : ∀ {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (fuel : ℕ) {c : S.Cond r} (body : S.Code r) {x : S.Data r},
    ¬S.CondHolds c x →
    S.evalWithOracle w oracle (fuel + 1) (S.loop c body) x = x
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
  exec_loop_exit : ∀ {r : ℕ} {w : ℕ} {c : S.Cond r} {body : S.Code r} {x : S.Data r}
    {P : S.Data r → Prop} {T : ℕ},
    ¬S.CondHolds c x → P x → 2 ≤ T →
    S.DemonicExecWithin w (S.loop c body) x P T
  exec_loop_iter : ∀ {r : ℕ} {w : ℕ} {c : S.Cond r} {body : S.Code r} {x : S.Data r}
    {Q P : S.Data r → Prop} {T₁ T₂ T : ℕ},
    S.CondHolds c x →
    S.DemonicExecWithin w body x Q T₁ →
    (∀ y, Q y → S.DemonicExecWithin w (S.loop c body) y P T₂) →
    T₁ + T₂ + 2 ≤ T →
    S.DemonicExecWithin w (S.loop c body) x P T

/-! ### Correspondence Lemmas for `MachinePresentation` -/

theorem dataTo_dataOf {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ} (x : BitRAM.Data r) :
    S.dataTo (S.dataOf x) = x := by
  cases x
  simp [MachinePresentation.dataTo, MachinePresentation.dataOf,
    hS.regs_mk, hS.mem_mk, hS.bitSize_mk]

theorem dataOf_dataTo {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ} (x : S.Data r) :
    S.dataOf (S.dataTo x) = x :=
  hS.data_eta x

theorem setReg_dataOf {S : MachinePresentation} (hS : MachineLaws S) {r : ℕ}
    (x : BitRAM.Data r) (i : Fin r) (v : ℕ) :
    S.setReg (S.dataOf x) i v = S.dataOf (x.set i v) := by
  simp [MachinePresentation.setReg, MachinePresentation.dataOf,
    hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set]

theorem shrinkData_dataOf_toBitMemoryState {S : MachinePresentation} (hS : MachineLaws S)
    {r w b : ℕ} (z : BitRAM.Data r) :
    (S.dataTo (S.shrinkData w b (S.dataOf z))).toBitMemoryState =
      (BitMemory.stepFn w z.toBitMemoryState (.shrink b)).1 := by
  simp [MachinePresentation.shrinkData, MachinePresentation.dataTo, MachinePresentation.dataOf,
    hS.regs_mk, hS.mem_mk, hS.bitSize_mk, clearRangeMem_eq,
    BitRAM.Data.toBitMemoryState, BitMemory.stepFn]

theorem dataWellFormed_iff {S : MachinePresentation} {r w : ℕ} (x : S.Data r) :
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

theorem evalOp_eq_map {S : MachinePresentation} (hS : MachineLaws S) {r w : ℕ}
    (o : Cslib.WordRAM.Op .standard r) (x : BitRAM.Data r) :
    S.evalOp w (S.opInstrOf o) (S.dataOf x) = (BitRAM.evalOp w o x).map S.dataOf := by
  cases o with
  | const d v =>
    change S.evalOp w (S.const d v) (S.dataOf x) =
      (if v < 2 ^ w then some (x.set d v) else none).map S.dataOf
    rw [hS.evalOp_const]
    simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set]
    split_ifs <;> rfl
  | copy d s =>
    change S.evalOp w (S.copy d s) (S.dataOf x) = (some (x.set d (x.regs s))).map S.dataOf
    rw [hS.evalOp_copy]
    simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set,
      Option.map_some]
  | alu f d args =>
    cases f with
    | bin bf =>
      change S.evalOp w
          (S.bin (S.binOpOf bf) d (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩))
          (S.dataOf x) =
        (if bf.eval (x.regs (args ⟨0, Nat.zero_lt_two⟩))
            (x.regs (args ⟨1, Nat.one_lt_two⟩)) < 2 ^ w then
          some (x.set d (bf.eval (x.regs (args ⟨0, Nat.zero_lt_two⟩))
            (x.regs (args ⟨1, Nat.one_lt_two⟩))))
        else none).map S.dataOf
      rw [hS.evalOp_bin]
      simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk,
        hS.evalBinOp_eq, BitRAM.Data.set]
      split_ifs <;> rfl
    | width =>
      change S.evalOp w (S.width d) (S.dataOf x) =
        (if w < 2 ^ w then some (x.set d w) else none).map S.dataOf
      rw [hS.evalOp_width]
      simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set]
      split_ifs <;> rfl
  | load d a =>
    dsimp only [MachinePresentation.opInstrOf, BitRAM.evalOp]
    rw [hS.evalOp_load]
    simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, ceilDiv_eq,
      BitRAM.Data.wordSize, BitRAM.Data.set]
    by_cases h : x.regs a < x.bitSize ⌈/⌉ w <;> simp [h, MachinePresentation.dataOf]
  | store a s =>
    dsimp only [MachinePresentation.opInstrOf, BitRAM.evalOp]
    rw [hS.evalOp_store]
    simp only [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, ceilDiv_eq,
      BitRAM.Data.wordSize, BitRAM.Data.write]
    by_cases h : x.regs a < x.bitSize ⌈/⌉ w <;> simp [h, MachinePresentation.dataOf]

theorem evalOp_map {S : MachinePresentation} (hS : MachineLaws S) {r w : ℕ}
    (o : Cslib.WordRAM.Op .standard r) (x y : BitRAM.Data r)
    (heval : BitRAM.evalOp w o x = some y) :
    S.evalOp w (S.opInstrOf o) (S.dataOf x) = some (S.dataOf y) := by
  rw [evalOp_eq_map hS o x, heval]
  rfl

/-- Deterministic fuel evaluation commutes with `codeOf` and `dataOf`. -/
theorem evalWithOracle_map {S : MachinePresentation} (hS : MachineLaws S)
    {r w : ℕ} (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) (fuel : ℕ)
    (c : BitRAM.Code .standard r) (x : BitRAM.Data r) :
    S.evalWithOracle w oracle fuel (S.codeOf c) (S.dataOf x) =
      S.dataOf (BitRAM.evalWithOracle w oracle fuel c x) := by
  induction c generalizing fuel x with
  | op o =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle, hS.evalWithOracle_op, evalOp_eq_map hS o x]
    cases BitRAM.evalOp w o x <;> rfl
  | grow dst δReg =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle, hS.evalWithOracle_grow]
    simp [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk]
  | shrink δReg =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle, hS.evalWithOracle_shrink]
    simp [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk,
      clearRangeMem_eq, BitRAM.Data.toBitMemoryState, BitMemory.stepFn]
  | size dst =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle, hS.evalWithOracle_size]
    simp [MachinePresentation.dataOf, hS.regs_mk, hS.mem_mk, hS.bitSize_mk, BitRAM.Data.set]
  | rand dst src =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle]
    exact hS.evalWithOracle_rand w oracle fuel dst src (S.dataOf x)
  | seq c₁ c₂ ih₁ ih₂ =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle, hS.evalWithOracle_seq, ih₁ fuel x, ih₂ fuel]
  | branch cond pos neg ih_pos ih_neg =>
    dsimp only [MachinePresentation.codeOf]
    rw [BitRAM.evalWithOracle]
    by_cases hc : BitRAM.CondHolds cond x
    · rw [ite_eq_left hc,
        hS.evalWithOracle_branch_pos w oracle fuel _ _ ((condHolds_iff hS cond x).mpr hc),
        ih_pos fuel x]
    · rw [ite_eq_right hc,
        hS.evalWithOracle_branch_neg w oracle fuel _ _
          (fun h => hc ((condHolds_iff hS cond x).mp h)),
        ih_neg fuel x]
  | loop cond body ih_body =>
    induction fuel generalizing x with
    | zero =>
      dsimp only [MachinePresentation.codeOf]
      rw [BitRAM.evalWithOracle]
      exact hS.evalWithOracle_loop_zero w oracle (S.condOf cond) (S.codeOf body) (S.dataOf x)
    | succ fuel ih_fuel =>
      rw [BitRAM.evalWithOracle]
      by_cases hc : BitRAM.CondHolds cond x
      · rw [ite_eq_left hc]
        dsimp only [MachinePresentation.codeOf]
        rw [hS.evalWithOracle_loop_succ_pos w oracle fuel _ ((condHolds_iff hS cond x).mpr hc),
          ih_body fuel x]
        exact ih_fuel (BitRAM.evalWithOracle w oracle fuel body x)
      · rw [ite_eq_right hc]
        dsimp only [MachinePresentation.codeOf]
        exact hS.evalWithOracle_loop_succ_neg w oracle fuel _
          (fun h => hc ((condHolds_iff hS cond x).mp h))

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
  | loop_exit hc hp h2 =>
    exact hS.exec_loop_exit (fun h => hc ((condHolds_iff hS _ _).mp h)) (hPQ _ hp) h2
  | @loop_iter c body x Q_mid P T₁ T₂ T hc _ _ hsum ih₁ ih₂ =>
    refine hS.exec_loop_iter
      (Q := fun y => Q_mid (S.dataTo y))
      ((condHolds_iff hS _ _).mpr hc)
      (ih₁ fun y hy => by rwa [dataTo_dataOf hS])
      (fun y hy => ?_) hsum
    have h2 := ih₂ (S.dataTo y) hy hPQ
    rwa [dataOf_dataTo hS] at h2

/-! ## Part 3: Polymorphic Dynamic Dictionary Presentation -/

/-- Polymorphic signature of the dynamic dictionary specification in
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
  foldStepDict {U : ℕ} : (Fin U → Option ℕ) → List (DictOp U) → (Fin U → Option ℕ)
  validDictOp {U : ℕ} : ℕ → (Fin U → Option ℕ) → DictOp U → Prop
  ValidDictHistory {U : ℕ} : ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  decodeQueryRegs : S.Data 280 → Option ℕ
  OpOutputCorrect {U : ℕ} : (Fin U → Option ℕ) → DictOp U → S.Data 280 → Prop
  loadOpRegs {U : ℕ} : DictOp U → S.Data 280 → S.Data 280
  loadDeleteKeyReg {U : ℕ} : Fin U → S.Data 280 → S.Data 280
  loadClientAllocRegs : ℕ → ℕ → S.Data 280 → S.Data 280
  InEpochHistory : ∀ (U : ℕ), ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  InEpochOracleTrace :
    ∀ {U : ℕ}, ℕ → ℕ → S.Code 280 → (ℕ → ℕ → ℕ) →
      ∀ {EpochSeed : ℕ → Type},
      (∀ N, EpochSeed N → (Fin U → Option ℕ) → S.Data 280 → Prop) →
      ∀ (N : ℕ), ((ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) → EpochSeed N →
      List (DictOp U) → (Fin U → Option ℕ) → S.Data 280 →
      List ℕ → List (S.Data 280) → Prop
  nextEpochCap {U : ℕ} : ℕ → (Fin U → Option ℕ) → DictOp U → ℕ
  MaxCardLe {U : ℕ} : ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  ReachedEpochsFit {U : ℕ} :
    (ℕ → ℕ → ℕ) → ℕ → ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop
  PureMultiEpochSpaceTrace {U : ℕ} :
    (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ → (Fin U → Option ℕ) → List (DictOp U) → Prop

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
  foldStepDict_nil : ∀ {U : ℕ} (s : Fin U → Option ℕ),
    D.foldStepDict s [] = s
  foldStepDict_cons : ∀ {U : ℕ} (s : Fin U → Option ℕ) (o : D.DictOp U) (os : List (D.DictOp U)),
    D.foldStepDict s (o :: os) = D.foldStepDict (D.stepDict s o) os
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
  decodeQueryRegs_eq : ∀ (x : S.Data 280),
    D.decodeQueryRegs x =
      if S.regs x (0 : Fin 280) = 0 then none else some (S.regs x (1 : Fin 280))
  opOutputCorrect_query : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (x : S.Data 280),
    D.OpOutputCorrect s (D.query u) x ↔ D.decodeQueryRegs x = s u
  opOutputCorrect_insert : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ) (x : S.Data 280),
    D.OpOutputCorrect s (D.insert u v) x ↔ True
  opOutputCorrect_delete : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (x : S.Data 280),
    D.OpOutputCorrect s (D.delete u) x ↔ True
  loadOpRegs_query : ∀ {U : ℕ} (u : Fin U) (x : S.Data 280),
    D.loadOpRegs (D.query u) x =
      S.setReg (S.setReg (S.setReg x (278 : Fin 280) 0) (270 : Fin 280) u.val) (274 : Fin 280) 0
  loadOpRegs_insert : ∀ {U : ℕ} (u : Fin U) (v : ℕ) (x : S.Data 280),
    D.loadOpRegs (D.insert u v) x =
      S.setReg (S.setReg (S.setReg x (278 : Fin 280) 1) (270 : Fin 280) u.val) (274 : Fin 280) v
  loadOpRegs_delete : ∀ {U : ℕ} (u : Fin U) (x : S.Data 280),
    D.loadOpRegs (D.delete u) x =
      S.setReg (S.setReg (S.setReg x (278 : Fin 280) 2) (270 : Fin 280) u.val) (274 : Fin 280) 0
  loadDeleteKeyReg_eq : ∀ {U : ℕ} (u : Fin U) (x : S.Data 280),
    D.loadDeleteKeyReg u x = S.setReg x (270 : Fin 280) u.val
  loadClientAllocRegs_eq : ∀ (b v : ℕ) (y : S.Data 280),
    D.loadClientAllocRegs b v y =
      S.setReg (S.setReg y (230 : Fin 280) b) (231 : Fin 280) v
  inEpochHistory_nil : ∀ (U N : ℕ) (s : Fin U → Option ℕ),
    D.InEpochHistory U N s [] ↔ N ≤ U ∧ (Dynamic.dom s).card ≤ N
  inEpochHistory_cons : ∀ (U N : ℕ) (s : Fin U → Option ℕ)
    (o : D.DictOp U) (os : List (D.DictOp U)),
    D.InEpochHistory U N s (o :: os) ↔
      N ≤ U ∧
      (Dynamic.dom s).card ≤ N ∧
      BitResizable.EpochInv U N (Dynamic.dom (D.stepDict s o)).card ∧
      D.InEpochHistory U N (D.stepDict s o) os
  inEpochOracleTrace_nil :
    ∀ {U : ℕ} (V w : ℕ) (stepCode : S.Code 280) (dbs : ℕ → ℕ → ℕ)
      {EpochSeed : ℕ → Type}
      (Rep : ∀ N, EpochSeed N → (Fin U → Option ℕ) → S.Data 280 → Prop)
      (N : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) (seed : EpochSeed N)
      (s_abs : Fin U → Option ℕ) (x : S.Data 280),
      D.InEpochOracleTrace V w stepCode dbs Rep N oracle seed [] s_abs x [] []
  inEpochOracleTrace_cons :
    ∀ {U : ℕ} (V w : ℕ) (stepCode : S.Code 280) (dbs : ℕ → ℕ → ℕ)
      {EpochSeed : ℕ → Type}
      (Rep : ∀ N, EpochSeed N → (Fin U → Option ℕ) → S.Data 280 → Prop)
      (N : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) (seed : EpochSeed N)
      (op : D.DictOp U) (ops : List (D.DictOp U))
      (s_abs : Fin U → Option ℕ) (x : S.Data 280)
      (T : ℕ) (ts_rest : List ℕ) (xs_rest : List (S.Data 280)),
      let s_abs' := D.stepDict s_abs op
      let n' := (Dynamic.dom s_abs').card
      let y := S.evalWithOracle w oracle T stepCode (D.loadOpRegs op x)
      S.DemonicExecWithin w stepCode (D.loadOpRegs op x)
        (fun y' =>
          S.DataWellFormed w y' ∧
          Rep N seed s_abs' y' ∧
          S.bitSize y' = dbs N n' ∧
          D.OpOutputCorrect s_abs op y') T →
      (∀ fuel ≥ T, S.evalWithOracle w oracle fuel stepCode (D.loadOpRegs op x) = y) →
      S.DataWellFormed w y →
      Rep N seed s_abs' y →
      S.bitSize y = dbs N n' →
      S.bitSize y ≤ Dynamic.optBits U V n' + 680 * n' * Dynamic.logLogFactor n' + 218 * w →
      D.OpOutputCorrect s_abs op y →
      D.InEpochOracleTrace V w stepCode dbs Rep N oracle seed ops s_abs' y ts_rest xs_rest →
      D.InEpochOracleTrace V w stepCode dbs Rep N oracle seed (op :: ops) s_abs x
        (T :: ts_rest) (y :: xs_rest)
  nextEpochCap_eq : ∀ {U : ℕ} (N : ℕ) (s_abs : Fin U → Option ℕ) (op : D.DictOp U),
    D.nextEpochCap N s_abs op =
      let m' := (Dynamic.dom (D.stepDict s_abs op)).card
      if BitResizable.EpochInv U N m' then N else BitResizable.targetCap U m'
  maxCardLe_nil : ∀ {U : ℕ} (M : ℕ) (s : Fin U → Option ℕ),
    D.MaxCardLe M s [] ↔ (Dynamic.dom s).card ≤ M
  maxCardLe_cons : ∀ {U : ℕ} (M : ℕ) (s : Fin U → Option ℕ)
    (o : D.DictOp U) (os : List (D.DictOp U)),
    D.MaxCardLe M s (o :: os) ↔
      (Dynamic.dom s).card ≤ M ∧ D.MaxCardLe M (D.stepDict s o) os
  reachedEpochsFit_nil : ∀ {U : ℕ} (dbs : ℕ → ℕ → ℕ) (w N : ℕ) (s : Fin U → Option ℕ),
    D.ReachedEpochsFit dbs w N s [] ↔ dbs N N < 2 ^ w
  reachedEpochsFit_cons : ∀ {U : ℕ} (dbs : ℕ → ℕ → ℕ) (w N : ℕ) (s : Fin U → Option ℕ)
    (o : D.DictOp U) (os : List (D.DictOp U)),
    D.ReachedEpochsFit dbs w N s (o :: os) ↔
      dbs N N < 2 ^ w ∧
      D.ReachedEpochsFit dbs w (D.nextEpochCap N s o) (D.stepDict s o) os
  pureMultiEpochSpaceTrace_nil : ∀ {U : ℕ} (dbs : ℕ → ℕ → ℕ) (V w N : ℕ) (s : Fin U → Option ℕ),
    let n := (Dynamic.dom s).card
    BitResizable.EpochInv U N n →
    dbs N N < 2 ^ w →
    dbs N n ≤ Dynamic.optBits U V n + 680 * n * Dynamic.logLogFactor n + 218 * w →
    D.PureMultiEpochSpaceTrace dbs V w N s []
  pureMultiEpochSpaceTrace_cons : ∀ {U : ℕ} (dbs : ℕ → ℕ → ℕ) (V w N : ℕ) (s : Fin U → Option ℕ)
    (o : D.DictOp U) (os : List (D.DictOp U)),
    let n := (Dynamic.dom s).card
    BitResizable.EpochInv U N n →
    dbs N N < 2 ^ w →
    dbs N n ≤ Dynamic.optBits U V n + 680 * n * Dynamic.logLogFactor n + 218 * w →
    D.PureMultiEpochSpaceTrace dbs V w (D.nextEpochCap N s o) (D.stepDict s o) os →
    D.PureMultiEpochSpaceTrace dbs V w N s (o :: os)

/-! ### Correspondence Lemmas for `DictPresentation` -/

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

theorem nextEpochCap_eq_lib {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (N : ℕ) (s : Fin U → Option ℕ) (o : D.DictOp U) :
    D.nextEpochCap N s o = BitResizable.nextEpochCap N s (D.dictOpTo o) := by
  rw [hD.nextEpochCap_eq, stepDict_eq_nextState hD]
  rfl

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

theorem inEpochHistory_iff {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U N : ℕ} (s : Fin U → Option ℕ) (ops : List (D.DictOp U)) :
    D.InEpochHistory U N s ops ↔
      BitResizable.InEpochHistory U N s (ops.map D.dictOpTo) := by
  induction ops generalizing s with
  | nil => exact hD.inEpochHistory_nil U N s
  | cons o os ih =>
    rw [List.map_cons, hD.inEpochHistory_cons, stepDict_eq_nextState hD]
    exact and_congr_right fun _ =>
      and_congr_right fun _ =>
        and_congr_right fun _ => ih (BitResizable.nextState s (D.dictOpTo o))

theorem maxCardLe_iff {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U M : ℕ} (s : Fin U → Option ℕ) (ops : List (D.DictOp U)) :
    D.MaxCardLe M s ops ↔ BitResizable.MaxCardLe M s (ops.map D.dictOpTo) := by
  induction ops generalizing s with
  | nil => exact hD.maxCardLe_nil M s
  | cons o os ih =>
    rw [List.map_cons, hD.maxCardLe_cons, stepDict_eq_nextState hD]
    exact and_congr_right fun _ => ih (BitResizable.nextState s (D.dictOpTo o))

theorem reachedEpochsFit_iff {S : MachinePresentation} {D : DictPresentation S} (hD : DictLaws S D)
    {U V w N : ℕ} (s : Fin U → Option ℕ) (ops : List (D.DictOp U)) :
    D.ReachedEpochsFit (BitResizable.dictBitSize U V w) w N s ops ↔
      BitResizable.ReachedEpochsFit U V w N s (ops.map D.dictOpTo) := by
  induction ops generalizing N s with
  | nil => exact hD.reachedEpochsFit_nil (BitResizable.dictBitSize U V w) w N s
  | cons o os ih =>
    rw [List.map_cons, hD.reachedEpochsFit_cons, nextEpochCap_eq_lib hD, stepDict_eq_nextState hD]
    exact and_congr_right fun _ => ih _

theorem pureMultiEpochSpaceTrace_of {S : MachinePresentation} {D : DictPresentation S}
    (hD : DictLaws S D) {U V w N : ℕ} (s : Fin U → Option ℕ) (ops : List (D.DictOp U))
    (htr : BitResizable.PureMultiEpochSpaceTrace U V w N s (ops.map D.dictOpTo)) :
    D.PureMultiEpochSpaceTrace (BitResizable.dictBitSize U V w) V w N s ops := by
  induction ops generalizing N s with
  | nil =>
    rcases htr with ⟨he, hf, hs⟩
    exact hD.pureMultiEpochSpaceTrace_nil (BitResizable.dictBitSize U V w) V w N s he hf hs
  | cons o os ih =>
    rcases htr with ⟨he, hf, hs, hrest⟩
    refine hD.pureMultiEpochSpaceTrace_cons (BitResizable.dictBitSize U V w) V w N s o os
      he hf hs ?_
    rw [nextEpochCap_eq_lib hD, stepDict_eq_nextState hD]
    exact ih _ hrest

theorem decodeQueryRegs_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D) (y : BitRAM.Data 280) :
    D.decodeQueryRegs (S.dataOf y) = BitResizable.decodeQueryRegs y.regs := by
  rw [hD.decodeQueryRegs_eq]
  simp only [MachinePresentation.dataOf, hS.regs_mk, BitResizable.decodeQueryRegs]

theorem opOutputCorrect_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (s : Fin U → Option ℕ) (o : D.DictOp U) (y : BitRAM.Data 280) :
    D.OpOutputCorrect s o (S.dataOf y) ↔
      BitResizable.OpOutputCorrect s (D.dictOpTo o) y.regs := by
  conv_lhs => rw [← dictOpOf_dictOpTo hD o]
  cases D.dictOpTo o with
  | query u =>
    rw [DictPresentation.dictOpOf, hD.opOutputCorrect_query, decodeQueryRegs_dataOf hS hD]
    rfl
  | insert u v =>
    rw [DictPresentation.dictOpOf, hD.opOutputCorrect_insert]
    rfl
  | delete u =>
    rw [DictPresentation.dictOpOf, hD.opOutputCorrect_delete]
    rfl

theorem loadOpRegs_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (o : D.DictOp U) (x : BitRAM.Data 280) :
    D.loadOpRegs o (S.dataOf x) = S.dataOf (BitResizable.loadOpRegs (D.dictOpTo o) x) := by
  conv_lhs => rw [← dictOpOf_dictOpTo hD o]
  cases D.dictOpTo o with
  | query u =>
    rw [DictPresentation.dictOpOf, hD.loadOpRegs_query,
      setReg_dataOf hS, setReg_dataOf hS, setReg_dataOf hS]
    rfl
  | insert u v =>
    rw [DictPresentation.dictOpOf, hD.loadOpRegs_insert,
      setReg_dataOf hS, setReg_dataOf hS, setReg_dataOf hS]
    rfl
  | delete u =>
    rw [DictPresentation.dictOpOf, hD.loadOpRegs_delete,
      setReg_dataOf hS, setReg_dataOf hS, setReg_dataOf hS]
    rfl

theorem loadDeleteKeyReg_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    {U : ℕ} (u : Fin U) (x : BitRAM.Data 280) :
    D.loadDeleteKeyReg u (S.dataOf x) = S.dataOf (x.set 270 u.val) := by
  rw [hD.loadDeleteKeyReg_eq, setReg_dataOf hS]

theorem loadClientAllocRegs_dataOf {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    (b v : ℕ) (y : BitRAM.Data 280) :
    D.loadClientAllocRegs b v (S.dataOf y) =
      S.dataOf (BitResizable.loadClientAllocRegs b v y) := by
  rw [hD.loadClientAllocRegs_eq, setReg_dataOf hS, setReg_dataOf hS]
  rfl

/-! ## Part 4: Headline Bridge Theorems -/

/-- Helper sequence bridge transferring `inEpochStepRegCode` execution across `ops` into
`D.InEpochOracleTrace` while preserving `EpochDictInv` on `lastState`. -/
private theorem compile_inEpochSeq {S : MachinePresentation} (hS : MachineLaws S)
    {D : DictPresentation S} (hD : DictLaws S D)
    {U V w N : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)} (horacle : BitRAM.DirtyGrowOracle w oracle)
    (θ : Succinct.QuotHashSeed U N)
    {s_abs : Fin U → Option ℕ} {s_fix₀ : Memory.State} {x₀ : BitRAM.Data 280}
    (hinv₀ : BitResizable.EpochDictInv U V w N θ s_abs s_fix₀ x₀)
    (ops : List (D.DictOp U))
    (hhist : D.InEpochHistory U N s_abs ops)
    (hvh : D.ValidDictHistory V s_abs ops) :
    let dbs := BitResizable.dictBitSize U V w
    let RepS : ∀ N', Succinct.QuotHashSeed U N' → (Fin U → Option ℕ) → S.Data 280 → Prop :=
      fun N' θ' s y => BitResizable.Rep U V w N' θ' s (S.dataTo y).toBitMemoryState
    ∃ (ts : List ℕ) (xs : List (S.Data 280)) (s_fix_f : Memory.State),
      ts.length = ops.length ∧
      xs.length = ops.length ∧
      D.InEpochOracleTrace V w (S.codeOf BitResizable.inEpochStepRegCode) dbs RepS N oracle θ
        ops s_abs (S.dataOf x₀) ts xs ∧
      BitResizable.EpochDictInv U V w N θ (D.foldStepDict s_abs ops) s_fix_f
        (S.dataTo (xs.getLastD (S.dataOf x₀))) ∧
      ts.sum + 1967 * BitResizable.inEpochPotential U V w N s_fix_f ≤
        1967 * BitResizable.inEpochPotential U V w N s_fix₀ +
          BitResizable.inEpochSeqOverhead U N θ s_abs (ops.map D.dictOpTo) := by
  intro dbs RepS
  induction ops generalizing s_abs s_fix₀ x₀ with
  | nil =>
    refine ⟨[], [], s_fix₀, rfl, rfl,
      hD.inEpochOracleTrace_nil V w (S.codeOf BitResizable.inEpochStepRegCode) dbs RepS N oracle θ
        s_abs (S.dataOf x₀),
      ?_, by simp [BitResizable.inEpochSeqOverhead]⟩
    rw [hD.foldStepDict_nil, List.getLastD_nil, dataTo_dataOf hS]
    exact hinv₀
  | cons op ops ih =>
    rw [hD.inEpochHistory_cons] at hhist
    rcases hhist with ⟨_, _, hepoch', hhist_rest⟩
    rw [hD.validDictHistory_cons] at hvh
    rcases hvh with ⟨hval_op, hvh_rest⟩
    have hstep_eq : D.stepDict s_abs op = BitResizable.nextState s_abs (D.dictOpTo op) :=
      stepDict_eq_nextState hD s_abs op
    have hepoch_lib :
        BitResizable.EpochInv U N
          (Dynamic.dom (BitResizable.nextState s_abs (D.dictOpTo op))).card := by
      rwa [← hstep_eq]
    have hdyn_val : (Dynamic.spec U V N).valid s_abs (D.dictOpTo op) :=
      BitResizable.dynamic_valid_of_spec_valid
        ((validDictOp_iff hD s_abs op).mp hval_op) hepoch_lib.card_le
    obtain ⟨s_fix₁, T, hExec₁, hcost₁⟩ :=
      BitResizable.inEpochStepRegCode_exec hw hU hV θ hinv₀ hdyn_val
    have hstep_dyn :
        ((Dynamic.spec U V N).stepFn s_abs (D.dictOpTo op)).1 =
          BitResizable.nextState s_abs (D.dictOpTo op) := rfl
    obtain ⟨⟨hinv₁, hout₁⟩, _, hfuel₁⟩ := hExec₁.evalWithOracle_spec_of_le horacle
    rw [hstep_dyn, ← hstep_eq] at hinv₁
    let y₁_lib := BitRAM.evalWithOracle w oracle T BitResizable.inEpochStepRegCode
      (BitResizable.loadOpRegs (D.dictOpTo op) x₀)
    have hy₁_eq :
        S.evalWithOracle w oracle T (S.codeOf BitResizable.inEpochStepRegCode)
          (D.loadOpRegs op (S.dataOf x₀)) = S.dataOf y₁_lib := by
      rw [loadOpRegs_dataOf hS hD, evalWithOracle_map hS]
    have hExec₁_S :
        S.DemonicExecWithin w (S.codeOf BitResizable.inEpochStepRegCode)
          (D.loadOpRegs op (S.dataOf x₀))
          (fun y' =>
            S.DataWellFormed w y' ∧
            RepS N θ (D.stepDict s_abs op) y' ∧
            S.bitSize y' = dbs N (Dynamic.dom (D.stepDict s_abs op)).card ∧
            D.OpOutputCorrect s_abs op y') T := by
      rw [loadOpRegs_dataOf hS hD]
      refine demonicExecWithin_mono hS hExec₁ fun y' ⟨hinv', hout'⟩ => ?_
      rw [hstep_dyn, ← hstep_eq] at hinv'
      refine ⟨(dataWellFormed_iff (S.dataOf y')).mpr (by rw [dataTo_dataOf hS]; exact hinv'.wf),
        ?_, ?_, (opOutputCorrect_dataOf hS hD s_abs op y').mpr hout'⟩
      · dsimp only [RepS]
        rw [dataTo_dataOf hS]
        exact hinv'.rep hepoch'
      · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
        exact hinv'.bitSize_eq
    have hfuel₁_S : ∀ fuel ≥ T,
        S.evalWithOracle w oracle fuel (S.codeOf BitResizable.inEpochStepRegCode)
          (D.loadOpRegs op (S.dataOf x₀)) =
        S.evalWithOracle w oracle T (S.codeOf BitResizable.inEpochStepRegCode)
          (D.loadOpRegs op (S.dataOf x₀)) := by
      intro fuel hge
      rw [hy₁_eq, loadOpRegs_dataOf hS hD, evalWithOracle_map hS]
      exact congrArg S.dataOf (hfuel₁ fuel hge)
    have hy₁_wf : S.DataWellFormed w (S.dataOf y₁_lib) :=
      (dataWellFormed_iff (S.dataOf y₁_lib)).mpr (by rw [dataTo_dataOf hS]; exact hinv₁.wf)
    have hy₁_rep : RepS N θ (D.stepDict s_abs op) (S.dataOf y₁_lib) := by
      dsimp only [RepS]
      rw [dataTo_dataOf hS]
      exact hinv₁.rep hepoch'
    have hy₁_sz : S.bitSize (S.dataOf y₁_lib) = dbs N (Dynamic.dom (D.stepDict s_abs op)).card := by
      simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact hinv₁.bitSize_eq
    have hy₁_space :
        S.bitSize (S.dataOf y₁_lib) ≤
          Dynamic.optBits U V (Dynamic.dom (D.stepDict s_abs op)).card +
            680 * (Dynamic.dom (D.stepDict s_abs op)).card *
              Dynamic.logLogFactor (Dynamic.dom (D.stepDict s_abs op)).card + 218 * w := by
      simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact BitResizable.EpochDictInv.space_tight hw hU.le hinv₁ hepoch'
    have hy₁_out : D.OpOutputCorrect s_abs op (S.dataOf y₁_lib) :=
      (opOutputCorrect_dataOf hS hD s_abs op y₁_lib).mpr hout₁
    obtain ⟨ts_rest, xs_rest, s_fix_f, hlen_ts, hlen_xs, htr_rest, hinv_f, hcost_rest⟩ :=
      ih hinv₁ hhist_rest hvh_rest
    refine ⟨T :: ts_rest,
      S.evalWithOracle w oracle T (S.codeOf BitResizable.inEpochStepRegCode)
        (D.loadOpRegs op (S.dataOf x₀)) :: xs_rest,
      s_fix_f,
      by simp [hlen_ts], by simp [hlen_xs],
      hD.inEpochOracleTrace_cons V w (S.codeOf BitResizable.inEpochStepRegCode) dbs RepS N oracle θ
        op ops s_abs (S.dataOf x₀) T ts_rest xs_rest
        hExec₁_S hfuel₁_S
        (hy₁_eq.symm ▸ hy₁_wf) (hy₁_eq.symm ▸ hy₁_rep) (hy₁_eq.symm ▸ hy₁_sz)
        (hy₁_eq.symm ▸ hy₁_space) (hy₁_eq.symm ▸ hy₁_out) (hy₁_eq.symm ▸ htr_rest),
      ?_, ?_⟩
    · rw [hD.foldStepDict_cons, List.getLastD_cons, hy₁_eq]
      exact hinv_f
    · simp only [List.sum_cons, List.map_cons, BitResizable.inEpochSeqOverhead]
      rw [← hstep_eq]
      omega

/-- **Headline Bridge Theorem 1 (`bitResizableDictionary_compiled`):**
Uniform parameter-free `Code 280` compilation of empty initialization, in-epoch `query`/`insert`/
`delete` sequences in `O(1)` expected amortized instructions (`≤ 294450` per operation), succinct
bit-level space `OPT(U, V, n_t) + 680 * n_t * logLogFactor n_t + 218 * w`, faithful representation
`rep_inj`, and client subroutine reuse of bits released by `delete`. -/
theorem bitResizableDictionary_compiled (S : MachinePresentation) (hS : MachineLaws S)
    (D : DictPresentation S) (hD : DictLaws S D) :
    ∃ (initCode stepCode code_del code_client code_free : S.Code 280)
      (epochMetaWords : ℕ → ℕ → ℕ → ℕ),
      (∀ U w, epochMetaWords U w 0 = 4) ∧
      (∀ {U w N : ℕ}, 0 < w → N ≤ U → U < 2 ^ w → epochMetaWords U w N ≤ 16 * N + 209) ∧
      (∀ {U V w N n_t : ℕ}, 0 < w → U ≤ 2 ^ w → BitResizable.EpochInv U N n_t →
        epochMetaWords U w N * w + n_t * BitResizable.itemBits U V N ≤
          Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w) ∧
      ∀ {U V w : ℕ}, 4 ≤ w → U < 2 ^ w → V < 2 ^ w →
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * BitResizable.itemBits U V N
        ∃ (EpochSeed : ℕ → Type)
          (epochSeedPMF : ∀ N, PMF (EpochSeed N))
          (_epochSeedNonempty : ∀ N, Nonempty (EpochSeed N))
          (Companion : Type)
          (EpochDictInv : ∀ N, EpochSeed N → (Fin U → Option ℕ) → Companion → S.Data 280 → Prop)
          (Rep : ∀ N, EpochSeed N → (Fin U → Option ℕ) → S.Data 280 → Prop)
          (inEpochPotential : ℕ → Companion → ℕ)
          (stepOverhead : ∀ N, EpochSeed N → (Fin U → Option ℕ) → D.DictOp U → ℕ)
          (seqOverhead : ∀ N, EpochSeed N → (Fin U → Option ℕ) → List (D.DictOp U) → ℕ),
          (∀ {N : ℕ} (seed : EpochSeed N) {s₁ s₂ : Fin U → Option ℕ} {x : S.Data 280},
            Rep N seed s₁ x → Rep N seed s₂ x → s₁ = s₂) ∧
          (∀ {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}, DirtyGrowOracle w oracle →
            4 * w < 2 ^ w → ∀ (seed₀ : EpochSeed 0) {x₀ : S.Data 280},
            S.DataWellFormed w x₀ → S.bitSize x₀ = 0 →
            S.regs x₀ (240 : Fin 280) = U → S.regs x₀ (241 : Fin 280) = V →
            let T_init := 8 * w + 37
            let y₀ := S.evalWithOracle w oracle T_init initCode x₀
            ∃ c₀ : Companion,
              S.DemonicExecWithin w initCode x₀
                (fun y =>
                  EpochDictInv 0 seed₀ (Dynamic.empty U) c₀ y ∧
                  Rep 0 seed₀ (Dynamic.empty U) y ∧
                  S.bitSize y = 4 * w) T_init ∧
              EpochDictInv 0 seed₀ (Dynamic.empty U) c₀ y₀ ∧
              Rep 0 seed₀ (Dynamic.empty U) y₀ ∧
              S.bitSize y₀ = 4 * w ∧
              inEpochPotential 0 c₀ = 0 ∧
              (∀ fuel ≥ T_init, S.evalWithOracle w oracle fuel initCode x₀ = y₀)) ∧
          (∀ {N : ℕ}, N ≤ U → dbs N N < 2 ^ w → ∀ (seed : EpochSeed N),
            ∃ (c₀ : Companion) (x₀ : S.Data 280),
              EpochDictInv N seed (Dynamic.empty U) c₀ x₀ ∧
              S.DataWellFormed w x₀ ∧
              S.bitSize x₀ = epochMetaWords U w N * w ∧
              inEpochPotential N c₀ = 0) ∧
          (∀ {N : ℕ} {s_abs : Fin U → Option ℕ} {ops : List (D.DictOp U)},
            D.InEpochHistory U N s_abs ops →
            (∑' seed : EpochSeed N,
              (epochSeedPMF N seed : ℝ≥0∞) *
                ((seqOverhead N seed s_abs ops : ℕ) : ℝ≥0∞)) ≤
              294450 * (ops.length : ℝ≥0∞)) ∧
          (∀ {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}, DirtyGrowOracle w oracle →
            ∀ {N : ℕ} (seed : EpochSeed N) {s_abs : Fin U → Option ℕ} {c₀ : Companion}
              {x₀ : S.Data 280},
            EpochDictInv N seed s_abs c₀ x₀ →
            ∀ (ops : List (D.DictOp U)),
              D.InEpochHistory U N s_abs ops →
              D.ValidDictHistory V s_abs ops →
              ∃ (ts : List ℕ) (xs : List (S.Data 280)) (c_f : Companion),
                ts.length = ops.length ∧
                xs.length = ops.length ∧
                D.InEpochOracleTrace V w stepCode dbs Rep N oracle seed ops s_abs x₀ ts xs ∧
                EpochDictInv N seed (D.foldStepDict s_abs ops) c_f (xs.getLastD x₀) ∧
                ts.sum + 1967 * inEpochPotential N c_f ≤
                  1967 * inEpochPotential N c₀ + seqOverhead N seed s_abs ops) ∧
          (∀ {N : ℕ} (seed : EpochSeed N) {s_abs : Fin U → Option ℕ} {c : Companion}
              {x : S.Data 280},
            EpochDictInv N seed s_abs c x →
            ∀ (u : Fin U), (s_abs u).isSome →
            BitResizable.EpochInv U N (Dynamic.dom (D.stepDict s_abs (D.delete u))).card →
            ∀ {b v_client : ℕ}, b ≤ w → b ≤ BitResizable.itemBits U V N → v_client < 2 ^ b →
              let s_abs' := D.stepDict s_abs (D.delete u)
              let bit_after_del := S.bitSize x - BitResizable.itemBits U V N
              ∃ (c' : Companion) (T_del : ℕ),
                T_del + 1967 * inEpochPotential N c' ≤
                  1967 * inEpochPotential N c + stepOverhead N seed s_abs (D.delete u) ∧
                (∑' seed₀ : EpochSeed N,
                  (epochSeedPMF N seed₀ : ℝ≥0∞) *
                    ((stepOverhead N seed₀ s_abs (D.delete u) : ℕ) : ℝ≥0∞)) ≤ 294450 ∧
                S.DemonicExecWithin w code_del (D.loadDeleteKeyReg u x)
                  (fun y =>
                    EpochDictInv N seed s_abs' c' y ∧
                    Rep N seed s_abs' y ∧
                    S.bitSize y = bit_after_del ∧
                    S.DemonicExecWithin w code_client (D.loadClientAllocRegs b v_client y)
                      (fun z =>
                        S.DataWellFormed w z ∧
                        S.bitSize z = bit_after_del + b ∧
                        S.bitSize z ≤ S.bitSize x ∧
                        getField w (S.mem z) bit_after_del b = v_client ∧
                        (∀ i < bit_after_del,
                          getBit w (S.mem z) i = getBit w (S.mem y) i) ∧
                        Rep N seed s_abs' (S.shrinkData w b z) ∧
                        S.DemonicExecWithin w code_free z
                          (fun z' =>
                            EpochDictInv N seed s_abs' c' z' ∧
                            Rep N seed s_abs' z' ∧
                            S.bitSize z' = bit_after_del) 1)
                      46)
                  T_del) := by
  refine ⟨S.codeOf BitResizable.initEmptyRegCode,
    S.codeOf BitResizable.inEpochStepRegCode,
    S.codeOf BitResizable.inEpochDeleteOpRegCode,
    S.codeOf BitResizable.clientAllocBitsRegCode,
    S.codeOf BitResizable.clientFreeBitsRegCode,
    BitResizable.epochMetaWords,
    fun U w => by simp [BitResizable.epochMetaWords],
    fun hw hNU hU => BitResizable.epochMetaWords_le_linear hw hNU hU,
    fun hw hU hepoch => BitResizable.dictBitSize_le_optBits hw hU hepoch,
    ?_⟩
  intro U V w hw hU hV dbs
  have hw0 : 0 < w := by omega
  have hU_fits : Fits w U := hU
  have hV_fits : Fits w V := hV
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by
      ext k; simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
  have hepoch0 : BitResizable.EpochInv U 0 (Dynamic.dom (Dynamic.empty U)).card := by
    rw [hdom0]; exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun N => Succinct.QuotHashSeed U N,
    fun N => BitResizable.epochSeedPMF U N,
    fun N => inferInstance,
    Memory.State,
    fun N θ s_abs c x => BitResizable.EpochDictInv U V w N θ s_abs c (S.dataTo x),
    fun N θ s_abs x => BitResizable.Rep U V w N θ s_abs (S.dataTo x).toBitMemoryState,
    BitResizable.inEpochPotential U V w,
    fun N θ s_abs op => BitResizable.inEpochStepOverhead U N θ s_abs (D.dictOpTo op),
    fun N θ s_abs ops => BitResizable.inEpochSeqOverhead U N θ s_abs (ops.map D.dictOpTo),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Faithfulness of `Rep`
    intro N seed s₁ s₂ x hrep₁ hrep₂
    exact BitResizable.rep_inj hrep₁ hrep₂
  · -- 2. Uniform `initEmptyRegCode` execution & oracle evaluation from `bitSize = 0`
    intro oracle horacle hfit4w seed₀ x₀ hx_wf hx_sz hr240 hr241 T_init y₀
    have horacle_lib : BitRAM.DirtyGrowOracle w oracle := (dirtyGrowOracle_iff w oracle).mp horacle
    have hx_lib_wf : (S.dataTo x₀).WellFormed w := (dataWellFormed_iff x₀).mp hx_wf
    have hExec_lib := BitResizable.initEmptyRegCode_exec hw0 hU_fits hV_fits hfit4w seed₀
      hx_lib_wf hx_sz hr240 hr241
    obtain ⟨⟨hinv_y0, hsz_y0, hpot_y0⟩, _, hfuel_y0⟩ :=
      hExec_lib.evalWithOracle_spec_of_le horacle_lib
    let y₀_lib := BitRAM.evalWithOracle w oracle T_init BitResizable.initEmptyRegCode (S.dataTo x₀)
    have hy₀_eq : y₀ = S.dataOf y₀_lib := by
      dsimp only [y₀, y₀_lib]
      conv_lhs => rw [← dataOf_dataTo hS x₀]
      exact evalWithOracle_map hS oracle T_init BitResizable.initEmptyRegCode (S.dataTo x₀)
    refine ⟨⟨fun _ => 0, 0⟩, ?_, ?_, ?_, ?_, hpot_y0, ?_⟩
    · rw [← dataOf_dataTo hS x₀]
      refine demonicExecWithin_mono hS hExec_lib fun y ⟨hy_inv, hy_sz, _⟩ => ?_
      refine ⟨by dsimp only; rw [dataTo_dataOf hS]; exact hy_inv,
        by dsimp only; rw [dataTo_dataOf hS]; exact hy_inv.rep hepoch0,
        ?_⟩
      simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact hy_sz
    · dsimp only
      rw [hy₀_eq, dataTo_dataOf hS]
      exact hinv_y0
    · dsimp only
      rw [hy₀_eq, dataTo_dataOf hS]
      exact hinv_y0.rep hepoch0
    · rw [hy₀_eq]
      simp only [MachinePresentation.dataOf, hS.bitSize_mk]
      exact hsz_y0
    · intro fuel hge
      rw [hy₀_eq]
      conv_lhs => rw [← dataOf_dataTo hS x₀]
      rw [evalWithOracle_map hS]
      exact congrArg S.dataOf (hfuel_y0 fuel hge)
  · -- 3. Active-epoch empty witness (`exists_empty_epochDictInv`)
    intro N hNU hfit_cap seed
    obtain ⟨c₀, x_lib, hinv, hpot0⟩ :=
      BitResizable.exists_empty_epochDictInv hw0 hNU hU_fits hV_fits hfit_cap seed
    refine ⟨c₀, S.dataOf x_lib,
      by dsimp only; rw [dataTo_dataOf hS]; exact hinv,
      (dataWellFormed_iff _).mpr (by rw [dataTo_dataOf hS]; exact hinv.wf),
      ?_, hpot0⟩
    simp only [MachinePresentation.dataOf, hS.bitSize_mk]
    rw [hinv.bitSize_eq, hdom0]
    simp [BitResizable.dictBitSize, BitResizable.epochMetaBits]
  · -- 4. Whole-sequence expectation bound (`≤ 294450 * ops.length`)
    intro N s_abs ops hhist
    simpa only [List.length_map] using
      BitResizable.tsum_inEpochSeqOverhead_le ((inEpochHistory_iff hD s_abs ops).mp hhist)
  · -- 5. Uniform `inEpochStepRegCode` sequence execution under any `DirtyGrowOracle`
    intro oracle horacle N seed s_abs c₀ x₀ hinv₀ ops hhist hvh
    have horacle_lib : BitRAM.DirtyGrowOracle w oracle := (dirtyGrowOracle_iff w oracle).mp horacle
    obtain ⟨ts, xs, c_f, hlen_ts, hlen_xs, htrace, hinv_f, hcost⟩ :=
      compile_inEpochSeq hS hD hw0 hU_fits hV_fits horacle_lib seed hinv₀ ops hhist hvh
    rw [dataOf_dataTo hS x₀] at htrace hinv_f
    exact ⟨ts, xs, c_f, hlen_ts, hlen_xs, htrace, hinv_f, hcost⟩
  · -- 6. Uniform client subroutine reuse of bits released by `delete`
    intro N seed s_abs c x hinv u hsome hepoch' b v_client hbw hb_item hv_client
      s_abs' bit_after_del
    have hstep_del : D.stepDict s_abs (D.delete u) = BitResizable.nextState s_abs (.delete u) := by
      rw [stepDict_eq_nextState hD, dictOpTo_delete hD]
    have hepoch_lib :
        BitResizable.EpochInv U N
          (Dynamic.dom (BitResizable.nextState s_abs (.delete u))).card := by
      rwa [← hstep_del]
    obtain ⟨c', T_del, hcost, htsum, hexec_del⟩ :=
      BitResizable.inEpochDeleteOpRegCode_clientAlloc_subroutine
        hw0 hU_fits hV_fits seed hinv u hsome hepoch_lib hbw hb_item hv_client
    refine ⟨c', T_del, ?_, ?_, ?_⟩
    · dsimp only
      rw [dictOpTo_delete hD]
      exact hcost
    · dsimp only
      rw [dictOpTo_delete hD]
      exact htsum
    · have hload_del : D.loadDeleteKeyReg u x = S.dataOf ((S.dataTo x).set 270 u.val) := by
        conv_lhs => rw [← dataOf_dataTo hS x]
        exact loadDeleteKeyReg_dataOf hS hD u (S.dataTo x)
      rw [hload_del]
      refine demonicExecWithin_mono hS hexec_del
        fun y ⟨hinv_y, hrep_y, hy_sz, hexec_cl⟩ => ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp only [s_abs']
        rw [hstep_del, dataTo_dataOf hS]
        exact hinv_y
      · dsimp only [s_abs']
        rw [hstep_del, dataTo_dataOf hS]
        exact hrep_y
      · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
        exact hy_sz
      · rw [loadClientAllocRegs_dataOf hS hD]
        refine demonicExecWithin_mono hS hexec_cl
          fun z ⟨hz_wf, hz_sz, hz_le, hz_field, hz_bits, hz_rep_sh, hexec_fr⟩ => ?_
        refine ⟨(dataWellFormed_iff _).mpr (by rw [dataTo_dataOf hS]; exact hz_wf),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
          exact hz_sz
        · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
          exact hz_le
        · simp only [MachinePresentation.dataOf, hS.mem_mk, getField_eq w z.mem z.bitSize]
          exact hz_field
        · intro i hi
          simp only [MachinePresentation.dataOf, hS.mem_mk,
            getBit_eq w z.mem z.bitSize, getBit_eq w y.mem y.bitSize]
          exact hz_bits i hi
        · dsimp only [s_abs']
          rw [hstep_del, shrinkData_dataOf_toBitMemoryState hS]
          exact hz_rep_sh
        · refine demonicExecWithin_mono hS hexec_fr fun z' ⟨hz'_inv, hz'_rep, hz'_sz⟩ => ?_
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [s_abs']
            rw [hstep_del, dataTo_dataOf hS]
            exact hz'_inv
          · dsimp only [s_abs']
            rw [hstep_del, dataTo_dataOf hS]
            exact hz'_rep
          · simp only [MachinePresentation.dataOf, hS.bitSize_mk]
            exact hz'_sz

/-- **Headline Bridge Theorem 2 (`bitResizableDictionary_multiEpoch_pure`):**
Pure model-level multi-epoch hysteresis, non-vacuous reached-capacity fit (`ReachedEpochsFit`,
holding even at `U = 2 ^ w - 1` and `V = 2 ^ w`), every-step succinct space from `(0, empty)`, and
`O(1)` amortized rebuild potential (`epochPotential`). -/
theorem bitResizableDictionary_multiEpoch_pure (S : MachinePresentation)
    (D : DictPresentation S) (hD : DictLaws S D) :
    ∃ (epochMetaWords : ℕ → ℕ → ℕ → ℕ),
      (∀ U w, epochMetaWords U w 0 = 4) ∧
      (∀ {U w N : ℕ}, 0 < w → N ≤ U → U < 2 ^ w → epochMetaWords U w N ≤ 16 * N + 209) ∧
      (∀ {U V w N n_t : ℕ}, 0 < w → U ≤ 2 ^ w → BitResizable.EpochInv U N n_t →
        epochMetaWords U w N * w + n_t * BitResizable.itemBits U V N ≤
          Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w) ∧
      (∀ {U V w M : ℕ},
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * BitResizable.itemBits U V N
        (∀ N' ≤ min U (2 * M), dbs N' N' < 2 ^ w) →
        ∀ {N : ℕ} {s_abs : Fin U → Option ℕ} {ops : List (D.DictOp U)},
          N ≤ min U (2 * M) →
          D.MaxCardLe M s_abs ops →
          D.ReachedEpochsFit dbs w N s_abs ops) ∧
      (∀ {U V w : ℕ}, 0 < w → U < 2 ^ w →
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * BitResizable.itemBits U V N
        ∀ (ops : List (D.DictOp U)),
          D.ReachedEpochsFit dbs w 0 (Dynamic.empty U) ops →
          D.PureMultiEpochSpaceTrace dbs V w 0 (Dynamic.empty U) ops) ∧
      (∀ {U w N m m' : ℕ}, 0 < w → U < 2 ^ w →
        BitResizable.EpochInv U N m → m' ≤ U → m' ≤ m + 1 → m ≤ m' + 1 →
        let N' := if BitResizable.EpochInv U N m' then N else BitResizable.targetCap U m'
        let cost :=
          if BitResizable.EpochInv U N m' then 1
          else
            4 + 4 * m + 2 * epochMetaWords U w N +
              5 * epochMetaWords U w (BitResizable.targetCap U m') + 1102 * m'
        cost + 2660 * BitResizable.epochPotential U N' m' ≤
          2660 * BitResizable.epochPotential U N m + 7849) := by
  refine ⟨BitResizable.epochMetaWords,
    fun U w => by simp [BitResizable.epochMetaWords],
    fun hw hNU hU => BitResizable.epochMetaWords_le_linear hw hNU hU,
    fun hw hU hepoch => BitResizable.dictBitSize_le_optBits hw hU hepoch,
    ?_, ?_, ?_⟩
  · intro U V w M dbs hfit_le N s_abs ops hN hmax
    exact (reachedEpochsFit_iff hD s_abs ops).mpr
      (BitResizable.reachedEpochsFit_of_maxCardLe hfit_le hN ((maxCardLe_iff hD s_abs ops).mp hmax))
  · intro U V w hw hU dbs ops hfit
    exact pureMultiEpochSpaceTrace_of hD (Dynamic.empty U) ops
      (BitResizable.pureMultiEpoch_space_and_hysteresis_from_empty hw hU (ops.map D.dictOpTo)
        ((reachedEpochsFit_iff hD (Dynamic.empty U) ops).mp hfit))
  · intro U w N m m' hw hU hepoch hm'U h1 h2
    exact BitResizable.pureMultiEpochStep_amortized_le hw hU hepoch hm'U h1 h2

end ComplexityAbstracts.BitResizableDictionaryBridge
