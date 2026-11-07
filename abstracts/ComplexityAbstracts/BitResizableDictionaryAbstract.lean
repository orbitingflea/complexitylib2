/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.BitResizableDictionaryBridge
import ComplexityAbstracts.Check
import Cslib.Probability.PMF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: Succinct Dynamic Dictionary on a Bit-Resizable Word-RAM

This self-contained file states the formal specification and headline correctness, running-time,
succinct-space, memory-reuse, and multi-epoch hysteresis theorems for the succinct dynamic
dictionary with deletions on the bit-granular resizable `w`-bit Word-RAM
(`Cslib.DataStructure.Dictionary.BitResizable`), following
`[BenderFarachColtonKuszmaulKuszmaul2024]` (SOSA 2024), `[ArbitmanNaorSegev2010]` (FOCS 2010),
`[BenderConwayFarachColtonKuszmaulTagliavini2023]` (*J. ACM* 2023),
`[BenderFarachColtonKuszmaulKuszmaulLiu2022]` (*J. ACM* 2024), and `[LiLiangYuZhou2023]` (FOCS 2023)
/ `[LiLiangYuZhou2024]` (STOC 2024).

## Bit-Granular Resizable Word-RAM Model

A machine state `Data r` over `r` registers consists of:
- `regs : Fin r → ℕ`, holding `r` machine-word registers;
- `mem : ℕ → ℕ`, the underlying word array;
- `bitSize : ℕ`, the current allocated bit count.

At word width `w`, bit index `i` resides at bit offset `i % w` of word `i / w` (`getBit w mem i`).
In any well-formed state (`Data.WellFormed w`), all registers, memory words, and `bitSize` are
strictly less than `2 ^ w`, and every unallocated bit `i ≥ bitSize` is zero
(`getBit w mem i = false`). Word loads and stores are admissible on all active words
`a < ceilDiv bitSize w`.

In addition to standard `w`-bit Word-RAM instructions (`OpInstr`), structured programs (`Code`)
provide loops (`loop`), random sampling (`rand`), and three bit-granular memory-resizing primitives:
- `grow dst δReg` increases `bitSize` by `δ = regs δReg` bits, stores the old `bitSize` into
  register `dst`, and requires total correctness under demonic non-determinism (`DirtyGrow`) for
  every post-growth word array `mem'` that preserves all pre-existing bits `[0, bitSize)` and keeps
  all unallocated bits `[bitSize + δ, ∞)` zero while allowing arbitrary dirty bits in
  `[bitSize, bitSize + δ)`;
- `shrink δReg` decreases `bitSize` by `δ = regs δReg` bits (`δ ≤ bitSize`) and zeroes the released
  bit interval `[bitSize - δ, bitSize)` (`clearRangeMem`) to preserve the zeroed-tail invariant;
- `size dst` reads the current `bitSize` into register `dst` in `1` instruction.

Both `grow` and `shrink` by `δ` bits charge `max 1 (ceilDiv δ w)` instructions. Deterministic
programs (without `rand`) also evaluate functionally under any adversarial `DirtyGrowOracle` via
fuel-bounded `evalWithOracle`.

## Verification Boundary: Compiled In-Epoch Programs vs. Pure Multi-Epoch Hysteresis

To maintain complete transparency about what is compiled to uniform machine code versus proved at
the mathematical model level, this abstract separates two complementary headline theorems:

1. Compiled uniform `Code 280` execution (`bitResizableDictionary_compiled`). Five fixed,
   parameter-free 280-register programs (`initCode`, `stepCode`, `code_del`, `code_client`,
   `code_free`) are existentially quantified once outside `∀ {U V w : ℕ}`. Across all `4 ≤ w`,
   `U < 2 ^ w`, and `V < 2 ^ w`, `initCode` initializes the empty dictionary (`N = 0`) from
   `bitSize = 0` in `8 * w + 37` instructions (`bitSize = 4 * w`); `stepCode` executes any
   in-epoch sequence `ops` (`InEpochHistory U N s_abs ops`) of `query`, `insert`, and `delete`
   operations under any adversarial `DirtyGrowOracle`, maintaining a faithful representation `Rep`
   (`Rep N seed s₁ x → Rep N seed s₂ x → s₁ = s₂`), exact per-step query output (`OpOutputCorrect`),
   exact bit-level footprint `y.bitSize = epochMetaWords U w N * w + n_t * itemBits U V N` bounded
   by `optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w`, and `O(1)` expected amortized
   instruction overhead (`≤ 294450 * ops.length` over `epochSeedPMF N`); and `code_del`,
   `code_client`, `code_free` prove subroutine reuse of the `itemBits U V N` bits released by an
   in-epoch `delete` without exceeding the pre-deletion bit footprint.
2. Pure mathematical multi-epoch hysteresis and space (`bitResizableDictionary_multiEpoch_pure`).
   Cross-epoch capacity-rebuild `Code 280` compilation (re-hashing active items via lossless Feistel
   `(b, q)` key recovery and `.rand` seed sampling when `(dictDom s).card` leaves `EpochInv U N`) is
   not compiled into `stepCode`; instead, `bitResizableDictionary_multiEpoch_pure` states as a pure
   theorem (without wrapping in a synthetic `Code` existential) that under `nextEpochCap` hysteresis
   (`N' = targetCap U n'` whenever `EpochInv U N n'` fails), any sequence whose active key count
   never exceeds `M` satisfies non-vacuous `ReachedEpochsFit` (valid even at `U = 2 ^ w - 1` and
   arbitrary `V`), maintains `EpochInv` and succinct space
   `optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w` at every step from `(0, emptyDict U)`,
   and satisfies the `O(1)` amortized rebuild-potential bound (`2660 * epochPotential + 7849`).

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.BitResizableDictionaryBridge`, and `#check_abstract` audits the dependency
boundary.
-/

namespace ComplexityAbstracts.BitResizableDictionaryAbstract

/-! ## Bit-Granular Memory and Adversarial Grow Oracles -/

/-- Ceiling division `⌈a / b⌉ = (a + b - 1) / b` on natural numbers. -/
def ceilDiv (a b : ℕ) : ℕ :=
  (a + b - 1) / b

/-- Read bit `i` from a `w`-bit word memory `mem : ℕ → ℕ`: bit `i % w` of word `mem (i / w)`. -/
def getBit (w : ℕ) (mem : ℕ → ℕ) (i : ℕ) : Bool :=
  (mem (i / w)).testBit (i % w)

/-- Low-order bit mask `(1 <<< len) - 1`. -/
def bitMask (len : ℕ) : ℕ :=
  (1 <<< len) - 1

/-- Shifted mask of `len` ones starting at bit offset `lo`. -/
def sliceMask (lo len : ℕ) : ℕ :=
  (bitMask len) <<< lo

/-- Clear the bits of `word` selected by `mask` (`word ^^^ (word &&& mask)`). -/
def clearMask (word mask : ℕ) : ℕ :=
  word ^^^ (word &&& mask)

/-- Extract `len` bits at offset `lo` from `word`. -/
def extractSlice (word lo len : ℕ) : ℕ :=
  (word >>> lo) &&& bitMask len

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

/-- Demonic non-deterministic bit-allocation relation (`DirtyGrow w mem bitSize δ mem' bitSize'`):
growing by `δ` bits produces `bitSize' = bitSize + δ` and any `w`-bit word-bounded memory `mem'`
that preserves all pre-existing bits `[0, bitSize)` and zeroes all unallocated bits
`[bitSize + δ, ∞)`, while leaving newly allocated bits `[bitSize, bitSize + δ)` unconstrained. -/
def DirtyGrow (w : ℕ) (mem : ℕ → ℕ) (bitSize δ : ℕ) (mem' : ℕ → ℕ) (bitSize' : ℕ) : Prop :=
  bitSize' = bitSize + δ ∧
  (∀ q : ℕ, mem' q < 2 ^ w) ∧
  (∀ i < bitSize, getBit w mem' i = getBit w mem i) ∧
  (∀ i : ℕ, bitSize + δ ≤ i → getBit w mem' i = false)

/-- Validity of an adversarial deterministic `grow` memory oracle `oracle`: for every `(mem,
bitSize, δ)`, `oracle mem bitSize δ` is an admissible `DirtyGrow` transition to `bitSize + δ`. -/
def DirtyGrowOracle (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) : Prop :=
  ∀ mem bitSize δ, DirtyGrow w mem bitSize δ (oracle mem bitSize δ) (bitSize + δ)

/-- Clear bits in `[lo, hi)` of word `q` at word width `w`. -/
def clearRangeWord (w word q lo hi : ℕ) : ℕ :=
  let start := lo - q * w
  let stop := min w (hi - q * w)
  clearMask (word &&& bitMask w) (sliceMask start (stop - start))

/-- Clear bit range `[lo, hi)` across a `w`-bit word array `mem : ℕ → ℕ`. -/
def clearRangeMem (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → ℕ :=
  fun q => clearRangeWord w (mem q) q lo hi

/-- Canonical zero-initialized `grow` oracle at word width `w`. -/
def zeroGrowOracle (w : ℕ) : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ) :=
  fun mem bitSize _ q => clearRangeWord w (mem q) q bitSize ((q + 1) * w)

/-! ## Bit-Granular Resizable Word-RAM Machine -/

/-- Standard binary ALU operations on machine words. -/
inductive BinOp : Type where
  | add | sub | mul | div | mod | bitAnd | bitOr | bitXor | shiftLeft | shiftRight

/-- Natural-number evaluation of `BinOp`. -/
def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .bitAnd, x, y => x &&& y
  | .bitOr, x, y => x ||| y
  | .bitXor, x, y => x ^^^ y
  | .shiftLeft, x, y => x <<< y
  | .shiftRight, x, y => x >>> y

/-- Register comparison conditions for structured branches and loops. -/
inductive Cond (r : ℕ) : Type where
  | eq (i j : Fin r)
  | lt (i j : Fin r)

/-- Primitive register and word-memory operations over `r` registers. -/
inductive OpInstr (r : ℕ) : Type where
  | const (d : Fin r) (v : ℕ)
  | copy (d s : Fin r)
  | bin (f : BinOp) (d i j : Fin r)
  | width (d : Fin r)
  | load (d a : Fin r)
  | store (a s : Fin r)

/-- Structured bit-resizable Word-RAM programs over `r` registers. -/
inductive Code (r : ℕ) : Type where
  | op (o : OpInstr r)
  | grow (dst δReg : Fin r)
  | shrink (δReg : Fin r)
  | size (dst : Fin r)
  | seq (c₁ c₂ : Code r)
  | branch (c : Cond r) (pos neg : Code r)
  | loop (c : Cond r) (body : Code r)
  | rand (dst src : Fin r)

/-- Machine data state over `r` registers: register bank `regs`, word memory `mem`, and current
allocated bit size `bitSize`. -/
structure Data (r : ℕ) : Type where
  regs : Fin r → ℕ
  mem : ℕ → ℕ
  bitSize : ℕ

/-- Update register `i` to `v` in `x : Data r`, leaving `mem` and `bitSize` unchanged. -/
def Data.setReg {r : ℕ} (x : Data r) (i : Fin r) (v : ℕ) : Data r :=
  ⟨Function.update x.regs i v, x.mem, x.bitSize⟩

/-- Pure bit-shrink transformation on `x : Data r`, clearing `[x.bitSize - b, x.bitSize)` and
reducing `bitSize` to `x.bitSize - b`. -/
def Data.shrinkData {r : ℕ} (w b : ℕ) (x : Data r) : Data r :=
  ⟨x.regs, clearRangeMem w x.mem (x.bitSize - b) x.bitSize, x.bitSize - b⟩

/-- Propositional truth of `c : Cond r` on state `x : Data r`. -/
def Cond.Holds {r : ℕ} : Cond r → Data r → Prop
  | .eq i j, x => x.regs i = x.regs j
  | .lt i j, x => x.regs i < x.regs j

/-- Boolean evaluation of `c : Cond r` on state `x : Data r`. -/
def Cond.evalBool {r : ℕ} : Cond r → Data r → Bool
  | .eq i j, x => decide (x.regs i = x.regs j)
  | .lt i j, x => decide (x.regs i < x.regs j)

/-- Well-formedness of a bit-resizable Word-RAM state at word width `w`: all registers, memory
words, and `bitSize` are `< 2 ^ w`, and all unallocated bits `i ≥ bitSize` are zero. -/
def Data.WellFormed {r : ℕ} (w : ℕ) (x : Data r) : Prop :=
  (∀ i : Fin r, x.regs i < 2 ^ w) ∧
  (∀ q : ℕ, x.mem q < 2 ^ w) ∧
  x.bitSize < 2 ^ w ∧
  (∀ i : ℕ, x.bitSize ≤ i → getBit w x.mem i = false)

/-- Evaluation of a primitive instruction `o : OpInstr r` at word width `w`. Word `load` and
`store` are admissible iff the word address `x.regs a` is strictly less than the active word count
`ceilDiv x.bitSize w`. -/
def evalOp {r : ℕ} (w : ℕ) : OpInstr r → Data r → Option (Data r)
  | .const d v, x =>
    if v < 2 ^ w then some ⟨Function.update x.regs d v, x.mem, x.bitSize⟩ else none
  | .copy d s, x =>
    some ⟨Function.update x.regs d (x.regs s), x.mem, x.bitSize⟩
  | .bin f d i j, x =>
    let v := f.eval (x.regs i) (x.regs j)
    if v < 2 ^ w then some ⟨Function.update x.regs d v, x.mem, x.bitSize⟩ else none
  | .width d, x =>
    if w < 2 ^ w then some ⟨Function.update x.regs d w, x.mem, x.bitSize⟩ else none
  | .load d a, x =>
    if x.regs a < ceilDiv x.bitSize w then
      some ⟨Function.update x.regs d (x.mem (x.regs a)), x.mem, x.bitSize⟩
    else none
  | .store a s, x =>
    if x.regs a < ceilDiv x.bitSize w then
      some ⟨x.regs, Function.update x.mem (x.regs a) (x.regs s), x.bitSize⟩
    else none

/-- Fuel-bounded deterministic evaluation of a `.rand`-free structured program `c : Code r` at word
width `w` under `.grow` memory oracle `oracle`. -/
def evalWithOracle {r : ℕ} (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) :
    ℕ → Code r → Data r → Data r
  | _, .op o, x => (evalOp w o x).getD x
  | _, .grow dst δReg, x =>
    ⟨Function.update x.regs dst x.bitSize,
      oracle x.mem x.bitSize (x.regs δReg),
      x.bitSize + x.regs δReg⟩
  | _, .shrink δReg, x =>
    ⟨x.regs,
      clearRangeMem w x.mem (x.bitSize - x.regs δReg) x.bitSize,
      x.bitSize - x.regs δReg⟩
  | _, .size dst, x =>
    ⟨Function.update x.regs dst x.bitSize, x.mem, x.bitSize⟩
  | _, .rand _ _, x => x
  | fuel, .seq c₁ c₂, x =>
    evalWithOracle w oracle fuel c₂ (evalWithOracle w oracle fuel c₁ x)
  | fuel, .branch c pos neg, x =>
    if c.evalBool x then evalWithOracle w oracle fuel pos x
    else evalWithOracle w oracle fuel neg x
  | 0, .loop _ _, x => x
  | fuel + 1, .loop c body, x =>
    if c.evalBool x then
      evalWithOracle w oracle fuel (.loop c body) (evalWithOracle w oracle fuel body x)
    else x

/-- Total correctness under demonic non-determinism for `grow` (`DemonicExecWithin w c x P T`):
executing `c : Code r` from state `x : Data r` at word width `w` terminates within at most `T`
instructions and reaches a state satisfying postcondition `P` for every adversarial choice of dirty
bits in `DirtyGrow`. -/
inductive DemonicExecWithin {r : ℕ} (w : ℕ) :
    Code r → Data r → (Data r → Prop) → ℕ → Prop where
  | op {o : OpInstr r} {x y : Data r} {P : Data r → Prop} {T : ℕ} :
      evalOp w o x = some y → P y → 1 ≤ T →
      DemonicExecWithin w (.op o) x P T
  | grow {dst δReg : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      x.bitSize + x.regs δReg < 2 ^ w →
      max 1 (ceilDiv (x.regs δReg) w) ≤ T →
      (∀ (mem' : ℕ → ℕ) (bitSize' : ℕ),
        DirtyGrow w x.mem x.bitSize (x.regs δReg) mem' bitSize' →
        P ⟨Function.update x.regs dst x.bitSize, mem', bitSize'⟩) →
      DemonicExecWithin w (.grow dst δReg) x P T
  | shrink {δReg : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      x.regs δReg ≤ x.bitSize →
      max 1 (ceilDiv (x.regs δReg) w) ≤ T →
      P ⟨x.regs,
          clearRangeMem w x.mem (x.bitSize - x.regs δReg) x.bitSize,
          x.bitSize - x.regs δReg⟩ →
      DemonicExecWithin w (.shrink δReg) x P T
  | size {dst : Fin r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      x.bitSize < 2 ^ w →
      P ⟨Function.update x.regs dst x.bitSize, x.mem, x.bitSize⟩ →
      1 ≤ T →
      DemonicExecWithin w (.size dst) x P T
  | seq {c₁ c₂ : Code r} {x : Data r} {Q P : Data r → Prop} {T₁ T₂ T : ℕ} :
      DemonicExecWithin w c₁ x Q T₁ →
      (∀ y, Q y → DemonicExecWithin w c₂ y P T₂) →
      T₁ + T₂ ≤ T →
      DemonicExecWithin w (.seq c₁ c₂) x P T
  | branch_pos {c : Cond r} {pos neg : Code r} {x : Data r} {P : Data r → Prop} {T₀ T : ℕ} :
      c.Holds x → DemonicExecWithin w pos x P T₀ → T₀ + 1 ≤ T →
      DemonicExecWithin w (.branch c pos neg) x P T
  | branch_neg {c : Cond r} {pos neg : Code r} {x : Data r} {P : Data r → Prop} {T₀ T : ℕ} :
      ¬c.Holds x → DemonicExecWithin w neg x P T₀ → T₀ + 2 ≤ T →
      DemonicExecWithin w (.branch c pos neg) x P T
  | loop_exit {c : Cond r} {body : Code r} {x : Data r} {P : Data r → Prop} {T : ℕ} :
      ¬c.Holds x → P x → 2 ≤ T →
      DemonicExecWithin w (.loop c body) x P T
  | loop_iter {c : Cond r} {body : Code r} {x : Data r} {Q P : Data r → Prop} {T₁ T₂ T : ℕ} :
      c.Holds x →
      DemonicExecWithin w body x Q T₁ →
      (∀ y, Q y → DemonicExecWithin w (.loop c body) y P T₂) →
      T₁ + T₂ + 2 ≤ T →
      DemonicExecWithin w (.loop c body) x P T

/-! ## Dynamic Dictionary Specification, Succinct Space Quantities, and Traces -/

/-- Abstract state of a dictionary over key universe `Fin U`. -/
abbrev DictState (U : ℕ) := Fin U → Option ℕ

/-- The empty dictionary over `Fin U`. -/
def emptyDict (U : ℕ) : DictState U := fun _ => none

/-- The finite set of keys currently present in dictionary state `s`. -/
def dictDom {U : ℕ} (s : DictState U) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Operations on a dynamic dictionary over key universe `Fin U`:
- `query u` looks up the value associated with `u : Fin U` (`some v` if present, `none` if absent);
- `insert u v` associates key `u : Fin U` with value `v : ℕ` (inserting or overwriting in place);
- `delete u` removes key `u : Fin U` if present (no-op if absent). -/
inductive DictOp (U : ℕ) : Type where
  | query (u : Fin U)
  | insert (u : Fin U) (v : ℕ)
  | delete (u : Fin U)

/-- Non-dependent eliminator for `DictOp U`. -/
def DictOp.elim {U : ℕ} {α : Type} (fq : Fin U → α) (fi : Fin U → ℕ → α) (fd : Fin U → α) :
    DictOp U → α
  | .query u => fq u
  | .insert u v => fi u v
  | .delete u => fd u

/-- Pure state transition of a dynamic dictionary under `DictOp U`. -/
def stepDict {U : ℕ} (s : DictState U) : DictOp U → DictState U
  | .query _ => s
  | .insert u v => Function.update s u (some v)
  | .delete u => Function.update s u none

/-- Pure multi-step state transition across an operation list `ops : List (DictOp U)`. -/
def foldStepDict {U : ℕ} : DictState U → List (DictOp U) → DictState U
  | s, [] => s
  | s, o :: os => foldStepDict (stepDict s o) os

/-- Unbounded-capacity operation admissibility: `query` and `delete` are always valid, and
`insert u v` requires only `v < V` (with no cap on `(dictDom s).card`). -/
def validDictOp {U : ℕ} (V : ℕ) (_s : DictState U) : DictOp U → Prop
  | .query _ => True
  | .insert _ v => v < V
  | .delete _ => True

/-- Admissibility of an operation sequence `ops : List (DictOp U)` starting from state `s`. -/
def ValidDictHistory {U : ℕ} (V : ℕ) : DictState U → List (DictOp U) → Prop
  | _, [] => True
  | s, o :: os => validDictOp V s o ∧ ValidDictHistory V (stepDict s o) os

/-- Decode a `query` result from the post-operation registers (`reg 0 = 0` encodes `none`;
`reg 0 ≠ 0` encodes `some (reg 1)`). -/
def decodeQueryRegs (x : Data 280) : Option ℕ :=
  if x.regs (0 : Fin 280) = 0 then none else some (x.regs (1 : Fin 280))

/-- Per-operation output correctness on post-state `x : Data 280`: a `query u` returns `s u` in
`decodeQueryRegs x`, while `insert` and `delete` return unit. -/
def OpOutputCorrect {U : ℕ} (s : DictState U) : DictOp U → Data 280 → Prop
  | .query u, x => decodeQueryRegs x = s u
  | .insert _ _, _ => True
  | .delete _, _ => True

/-- Calling convention for the unified in-epoch dispatcher `stepCode`: load the operation tag into
`r278` (`0` for `query`, `1` for `insert`, `2` for `delete`), key `u.val` into `r270`, and value
`v` (or `0`) into `r274`. -/
def loadOpRegs {U : ℕ} : DictOp U → Data 280 → Data 280
  | .query u, x =>
    ((x.setReg (278 : Fin 280) 0).setReg (270 : Fin 280) u.val).setReg (274 : Fin 280) 0
  | .insert u v, x =>
    ((x.setReg (278 : Fin 280) 1).setReg (270 : Fin 280) u.val).setReg (274 : Fin 280) v
  | .delete u, x =>
    ((x.setReg (278 : Fin 280) 2).setReg (270 : Fin 280) u.val).setReg (274 : Fin 280) 0

/-- Calling convention for standalone in-epoch deletion `code_del`: load key `u.val` into `r270`. -/
def loadDeleteKeyReg {U : ℕ} (u : Fin U) (x : Data 280) : Data 280 :=
  x.setReg (270 : Fin 280) u.val

/-- Calling convention for client bit-reuse subroutine `code_client`: load requested bit width `b`
into `r230` and `b`-bit value `v` into `r231`. -/
def loadClientAllocRegs (b v : ℕ) (y : Data 280) : Data 280 :=
  (y.setReg (230 : Fin 280) b).setReg (231 : Fin 280) v

/-- Iterated logarithmic factor `⌈log₂ ⌈log₂ (max n 4)⌉⌉ ≥ 1`. -/
def logLogFactor (n : ℕ) : ℕ :=
  Nat.clog 2 (Nat.clog 2 (max n 4))

/-- Information-theoretic minimum bit count `OPT(U, V, n) = ⌈log₂ C(U, n)⌉ + n · ⌈log₂ V⌉`
required to represent an `n`-element subset of `Fin U` with values in `Fin V`. -/
def optBits (U V n : ℕ) : ℕ :=
  Nat.clog 2 (U.choose n) + n * Nat.clog 2 V

/-- Number of Feistel bucket index bits `⌊log₂ n⌋ - 3 · logLogFactor n`. -/
def bucketBits (n : ℕ) : ℕ :=
  Nat.log 2 n - 3 * logLogFactor n

/-- Number of stored quotient bits per key `⌈log₂ U⌉ - bucketBits n`. -/
def quotientBits (U n : ℕ) : ℕ :=
  Nat.clog 2 U - bucketBits n

/-- Number of value bits `⌈log₂ V⌉` per item. -/
def valBits (V : ℕ) : ℕ :=
  Nat.clog 2 V

/-- Bit width `quotientBits U N + valBits V` of a single dense `(quotient, value)` item under
epoch capacity parameter `N`. -/
def itemBits (U V N : ℕ) : ℕ :=
  quotientBits U N + valBits V

/-- Epoch capacity invariant relating the current active key count `n_t = (dictDom s_t).card` to
the epoch capacity parameter `N`: either `n_t = 0 ∧ N = 0`, or `1 ≤ n_t ≤ N ≤ 4 * n_t` and
`N ≤ U`. -/
abbrev EpochInv (U N n_t : ℕ) : Prop :=
  (n_t = 0 ∧ N = 0) ∨ (1 ≤ n_t ∧ n_t ≤ N ∧ N ≤ 4 * n_t ∧ N ≤ U)

/-- Target epoch capacity `min U (2 * n')` (or `0` when `n' = 0`) selected when an operation steps
outside `EpochInv`. -/
def targetCap (U n' : ℕ) : ℕ :=
  if n' = 0 then 0 else min U (2 * n')

/-- Multi-epoch rebuild potential `epochPotential U N m`, measuring how far the active key count
`m` has drifted from the midpoint `N / 2` of epoch `N` (suppressing the upper branch at `N = U`). -/
def epochPotential (U N m : ℕ) : ℕ :=
  (if N < U then 2 * m - N else 0) + (N - 2 * m)

/-- Predicate stating that an operation sequence `ops` stays inside epoch capacity `N ≤ U` with
`EpochInv U N` holding after every operation (starting from any state with `(dictDom s).card ≤ N`,
including an empty active epoch). -/
def InEpochHistory (U N : ℕ) : DictState U → List (DictOp U) → Prop
  | s, [] => N ≤ U ∧ (dictDom s).card ≤ N
  | s, o :: os =>
    N ≤ U ∧
    (dictDom s).card ≤ N ∧
    EpochInv U N (dictDom (stepDict s o)).card ∧
    InEpochHistory U N (stepDict s o) os

/-- Operational trace of a fixed `stepCode : Code 280` executing `ops : List (DictOp U)` inside
epoch `N` under an adversarial `oracle` with step instruction budgets `ts` and post-states `xs`.
Every step `op` executes via `DemonicExecWithin` within `T` instructions, stabilizes under
`evalWithOracle` to `y = evalWithOracle w oracle T stepCode (loadOpRegs op x)`, maintains
`Data.WellFormed w y`, `Rep N seed s_abs' y`, exact bit footprint `y.bitSize = dbs N n'`, succinct
space `y.bitSize ≤ optBits U V n' + 680 * n' * logLogFactor n' + 218 * w`, and per-step
`OpOutputCorrect s_abs op y`. -/
inductive InEpochOracleTrace {U : ℕ} (V w : ℕ) (stepCode : Code 280) (dbs : ℕ → ℕ → ℕ)
    {EpochSeed : ℕ → Type}
    (Rep : ∀ N, EpochSeed N → DictState U → Data 280 → Prop)
    (N : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) (seed : EpochSeed N) :
    List (DictOp U) → DictState U → Data 280 → List ℕ → List (Data 280) → Prop where
  | nil (s_abs : DictState U) (x : Data 280) :
      InEpochOracleTrace V w stepCode dbs Rep N oracle seed [] s_abs x [] []
  | cons (op : DictOp U) (ops : List (DictOp U))
      (s_abs : DictState U) (x : Data 280)
      (T : ℕ) (ts_rest : List ℕ) (xs_rest : List (Data 280)) :
      DemonicExecWithin w stepCode (loadOpRegs op x)
        (fun y' =>
          y'.WellFormed w ∧
          Rep N seed (stepDict s_abs op) y' ∧
          y'.bitSize = dbs N (dictDom (stepDict s_abs op)).card ∧
          OpOutputCorrect s_abs op y') T →
      (∀ fuel ≥ T,
        evalWithOracle w oracle fuel stepCode (loadOpRegs op x) =
          evalWithOracle w oracle T stepCode (loadOpRegs op x)) →
      (evalWithOracle w oracle T stepCode (loadOpRegs op x)).WellFormed w →
      Rep N seed (stepDict s_abs op)
        (evalWithOracle w oracle T stepCode (loadOpRegs op x)) →
      (evalWithOracle w oracle T stepCode (loadOpRegs op x)).bitSize =
        dbs N (dictDom (stepDict s_abs op)).card →
      (evalWithOracle w oracle T stepCode (loadOpRegs op x)).bitSize ≤
        optBits U V (dictDom (stepDict s_abs op)).card +
          680 * (dictDom (stepDict s_abs op)).card *
            logLogFactor (dictDom (stepDict s_abs op)).card +
          218 * w →
      OpOutputCorrect s_abs op
        (evalWithOracle w oracle T stepCode (loadOpRegs op x)) →
      InEpochOracleTrace V w stepCode dbs Rep N oracle seed ops
        (stepDict s_abs op)
        (evalWithOracle w oracle T stepCode (loadOpRegs op x))
        ts_rest xs_rest →
      InEpochOracleTrace V w stepCode dbs Rep N oracle seed (op :: ops) s_abs x
        (T :: ts_rest)
        (evalWithOracle w oracle T stepCode (loadOpRegs op x) :: xs_rest)

/-- Next epoch capacity after executing `op` on `s_abs` in epoch `N`: stays at `N` when `EpochInv`
still holds on `(dictDom (stepDict s_abs op)).card`, and transitions to `targetCap U m'` otherwise.
-/
def nextEpochCap {U : ℕ} (N : ℕ) (s_abs : DictState U) (op : DictOp U) : ℕ :=
  let m' := (dictDom (stepDict s_abs op)).card
  if EpochInv U N m' then N else targetCap U m'

/-- Upper bound `M` on the active key count `(dictDom s_t).card` at every visited state along
`ops` (including the initial and final states). -/
def MaxCardLe {U : ℕ} (M : ℕ) : DictState U → List (DictOp U) → Prop
  | s, [] => (dictDom s).card ≤ M
  | s, o :: os => (dictDom s).card ≤ M ∧ MaxCardLe M (stepDict s o) os

/-- Non-vacuous reached-capacity fit hypothesis along `ops`: only the epoch capacities `N_t`
actually visited by `nextEpochCap` along `ops` need satisfy `dbs N_t N_t < 2 ^ w` (`U = 2 ^ w - 1`
is fully supported whenever the active key count stays small enough to fit in memory). -/
def ReachedEpochsFit {U : ℕ} (dbs : ℕ → ℕ → ℕ) (w : ℕ) :
    ℕ → DictState U → List (DictOp U) → Prop
  | N, _, [] => dbs N N < 2 ^ w
  | N, s, o :: os =>
    dbs N N < 2 ^ w ∧
    ReachedEpochsFit dbs w (nextEpochCap N s o) (stepDict s o) os

/-- Pure multi-epoch space and hysteresis trace along `ops`: at every visited step `(N_t, s_t)`
(including the final state), `EpochInv U N_t n_t` holds, `dbs N_t N_t < 2 ^ w`, and
`dbs N_t n_t ≤ optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w`. -/
inductive PureMultiEpochSpaceTrace {U : ℕ} (dbs : ℕ → ℕ → ℕ) (V w : ℕ) :
    ℕ → DictState U → List (DictOp U) → Prop where
  | nil (N : ℕ) (s : DictState U) :
      EpochInv U N (dictDom s).card →
      dbs N N < 2 ^ w →
      dbs N (dictDom s).card ≤
        optBits U V (dictDom s).card +
          680 * (dictDom s).card * logLogFactor (dictDom s).card + 218 * w →
      PureMultiEpochSpaceTrace dbs V w N s []
  | cons (N : ℕ) (s : DictState U) (o : DictOp U) (os : List (DictOp U)) :
      EpochInv U N (dictDom s).card →
      dbs N N < 2 ^ w →
      dbs N (dictDom s).card ≤
        optBits U V (dictDom s).card +
          680 * (dictDom s).card * logLogFactor (dictDom s).card + 218 * w →
      PureMultiEpochSpaceTrace dbs V w (nextEpochCap N s o) (stepDict s o) os →
      PureMultiEpochSpaceTrace dbs V w N s (o :: os)

/-! ## Headline Theorems -/

/-- Uniform compiled `Code 280` initialization, in-epoch `query`/`insert`/`delete` sequence
execution, succinct bit-granular space, faithful representation, and client bit-reuse subroutine on
the bit-resizable Word-RAM.

All five `Code 280` programs (`initCode`, `stepCode`, `code_del`, `code_client`, `code_free`) are
fixed parameter-free machine programs quantified ahead of `∀ {U V w : ℕ}`. Across all `4 ≤ w`,
`U < 2 ^ w`, and `V < 2 ^ w`:
1. `Rep` is faithful (`Rep N seed s₁ x → Rep N seed s₂ x → s₁ = s₂`);
2. `initCode` initializes the empty dictionary (`N = 0`, `bitSize = 4 * w`) from any well-formed
   `bitSize = 0` state with `(r240, r241) = (U, V)` in `8 * w + 37` instructions under any
   `DirtyGrowOracle`;
3. every fitting active epoch `N ≤ U` admits a well-formed empty state (`inEpochPotential = 0`);
4. for any in-epoch sequence `ops` (`InEpochHistory U N s_abs ops`), the expected total amortized
   overhead over `seed ← epochSeedPMF N` is at most `294450 * ops.length`;
5. under any `DirtyGrowOracle`, `stepCode` executes `ops` (`InEpochOracleTrace`) with step times
   `ts` satisfying `ts.sum + 1967 * inEpochPotential N c_f ≤ 1967 * inEpochPotential N c₀ +
   seqOverhead N seed s_abs ops`, maintaining `Rep`, `OpOutputCorrect`, and exact bit size
   `epochMetaWords U w N * w + n_t * itemBits U V N ≤ optBits U V n_t + 680 * n_t * logLogFactor n_t
   + 218 * w` at every step;
6. when `code_del` deletes a present key `u` inside epoch `N`, `bitSize` shrinks by
   `itemBits U V N` bits, `code_client` can immediately allocate `b ≤ itemBits U V N` of those
   released bits (`z.bitSize ≤ x.bitSize`) and store `v_client` while preserving `Rep` on the
   dictionary prefix `z.shrinkData w b`, and `code_free` restores `EpochDictInv` in `1` instruction.

References: `[BenderFarachColtonKuszmaulKuszmaul2024]`; `[ArbitmanNaorSegev2010]`;
`[BenderConwayFarachColtonKuszmaulTagliavini2023]`; `[BenderFarachColtonKuszmaulKuszmaulLiu2022]`;
`[LiLiangYuZhou2023]`; `[LiLiangYuZhou2024]`. -/
theorem bitResizableDictionary_compiled :
    ∃ (initCode stepCode code_del code_client code_free : Code 280)
      (epochMetaWords : ℕ → ℕ → ℕ → ℕ),
      (∀ U w, epochMetaWords U w 0 = 4) ∧
      (∀ {U w N : ℕ}, 0 < w → N ≤ U → U < 2 ^ w → epochMetaWords U w N ≤ 16 * N + 209) ∧
      (∀ {U V w N n_t : ℕ}, 0 < w → U ≤ 2 ^ w → EpochInv U N n_t →
        epochMetaWords U w N * w + n_t * itemBits U V N ≤
          optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w) ∧
      ∀ {U V w : ℕ}, 4 ≤ w → U < 2 ^ w → V < 2 ^ w →
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * itemBits U V N
        ∃ (EpochSeed : ℕ → Type)
          (epochSeedPMF : ∀ N, PMF (EpochSeed N))
          (_epochSeedNonempty : ∀ N, Nonempty (EpochSeed N))
          (Companion : Type)
          (EpochDictInv : ∀ N, EpochSeed N → DictState U → Companion → Data 280 → Prop)
          (Rep : ∀ N, EpochSeed N → DictState U → Data 280 → Prop)
          (inEpochPotential : ℕ → Companion → ℕ)
          (stepOverhead : ∀ N, EpochSeed N → DictState U → DictOp U → ℕ)
          (seqOverhead : ∀ N, EpochSeed N → DictState U → List (DictOp U) → ℕ),
          (∀ {N : ℕ} (seed : EpochSeed N) {s₁ s₂ : DictState U} {x : Data 280},
            Rep N seed s₁ x → Rep N seed s₂ x → s₁ = s₂) ∧
          (∀ {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}, DirtyGrowOracle w oracle →
            4 * w < 2 ^ w → ∀ (seed₀ : EpochSeed 0) {x₀ : Data 280},
            x₀.WellFormed w → x₀.bitSize = 0 →
            x₀.regs (240 : Fin 280) = U → x₀.regs (241 : Fin 280) = V →
            let T_init := 8 * w + 37
            let y₀ := evalWithOracle w oracle T_init initCode x₀
            ∃ c₀ : Companion,
              DemonicExecWithin w initCode x₀
                (fun y =>
                  EpochDictInv 0 seed₀ (emptyDict U) c₀ y ∧
                  Rep 0 seed₀ (emptyDict U) y ∧
                  y.bitSize = 4 * w) T_init ∧
              EpochDictInv 0 seed₀ (emptyDict U) c₀ y₀ ∧
              Rep 0 seed₀ (emptyDict U) y₀ ∧
              y₀.bitSize = 4 * w ∧
              inEpochPotential 0 c₀ = 0 ∧
              (∀ fuel ≥ T_init, evalWithOracle w oracle fuel initCode x₀ = y₀)) ∧
          (∀ {N : ℕ}, N ≤ U → dbs N N < 2 ^ w → ∀ (seed : EpochSeed N),
            ∃ (c₀ : Companion) (x₀ : Data 280),
              EpochDictInv N seed (emptyDict U) c₀ x₀ ∧
              x₀.WellFormed w ∧
              x₀.bitSize = epochMetaWords U w N * w ∧
              inEpochPotential N c₀ = 0) ∧
          (∀ {N : ℕ} {s_abs : DictState U} {ops : List (DictOp U)},
            InEpochHistory U N s_abs ops →
            (∑' seed : EpochSeed N,
              (epochSeedPMF N seed : ENNReal) *
                ((seqOverhead N seed s_abs ops : ℕ) : ENNReal)) ≤
              294450 * (ops.length : ENNReal)) ∧
          (∀ {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}, DirtyGrowOracle w oracle →
            ∀ {N : ℕ} (seed : EpochSeed N) {s_abs : DictState U} {c₀ : Companion}
              {x₀ : Data 280},
            EpochDictInv N seed s_abs c₀ x₀ →
            ∀ (ops : List (DictOp U)),
              InEpochHistory U N s_abs ops →
              ValidDictHistory V s_abs ops →
              ∃ (ts : List ℕ) (xs : List (Data 280)) (c_f : Companion),
                ts.length = ops.length ∧
                xs.length = ops.length ∧
                InEpochOracleTrace V w stepCode dbs Rep N oracle seed ops s_abs x₀ ts xs ∧
                EpochDictInv N seed (foldStepDict s_abs ops) c_f (xs.getLastD x₀) ∧
                ts.sum + 1967 * inEpochPotential N c_f ≤
                  1967 * inEpochPotential N c₀ + seqOverhead N seed s_abs ops) ∧
          (∀ {N : ℕ} (seed : EpochSeed N) {s_abs : DictState U} {c : Companion}
              {x : Data 280},
            EpochDictInv N seed s_abs c x →
            ∀ (u : Fin U), (s_abs u).isSome →
            EpochInv U N (dictDom (stepDict s_abs (.delete u))).card →
            ∀ {b v_client : ℕ}, b ≤ w → b ≤ itemBits U V N → v_client < 2 ^ b →
              let s_abs' := stepDict s_abs (.delete u)
              let bit_after_del := x.bitSize - itemBits U V N
              ∃ (c' : Companion) (T_del : ℕ),
                T_del + 1967 * inEpochPotential N c' ≤
                  1967 * inEpochPotential N c + stepOverhead N seed s_abs (.delete u) ∧
                (∑' seed₀ : EpochSeed N,
                  (epochSeedPMF N seed₀ : ENNReal) *
                    ((stepOverhead N seed₀ s_abs (.delete u) : ℕ) : ENNReal)) ≤ 294450 ∧
                DemonicExecWithin w code_del (loadDeleteKeyReg u x)
                  (fun y =>
                    EpochDictInv N seed s_abs' c' y ∧
                    Rep N seed s_abs' y ∧
                    y.bitSize = bit_after_del ∧
                    DemonicExecWithin w code_client (loadClientAllocRegs b v_client y)
                      (fun z =>
                        z.WellFormed w ∧
                        z.bitSize = bit_after_del + b ∧
                        z.bitSize ≤ x.bitSize ∧
                        getField w z.mem bit_after_del b = v_client ∧
                        (∀ i < bit_after_del,
                          getBit w z.mem i = getBit w y.mem i) ∧
                        Rep N seed s_abs' (z.shrinkData w b) ∧
                        DemonicExecWithin w code_free z
                          (fun z' =>
                            EpochDictInv N seed s_abs' c' z' ∧
                            Rep N seed s_abs' z' ∧
                            z'.bitSize = bit_after_del) 1)
                      46)
                  T_del) := by
  exact ComplexityAbstracts.BitResizableDictionaryBridge.bitResizableDictionary_compiled
    ⟨BinOp, .add, .sub, .mul, .div, .mod, .bitAnd, .bitOr, .bitXor, .shiftLeft, .shiftRight,
      BinOp.eval,
      Cond, @Cond.eq, @Cond.lt,
      OpInstr, @OpInstr.const, @OpInstr.copy, @OpInstr.bin, @OpInstr.width, @OpInstr.load,
      @OpInstr.store,
      Code, @Code.op, @Code.grow, @Code.shrink, @Code.size, @Code.seq, @Code.branch,
      @Code.loop, @Code.rand,
      Data, @Data.mk, @Data.regs, @Data.mem, @Data.bitSize,
      @evalOp, @Cond.Holds, @evalWithOracle, @DemonicExecWithin⟩
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun x => by cases x; rfl,
      fun f _ _ => by cases f <;> rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by intros; dsimp only; (conv_lhs => rw [evalWithOracle.eq_def]); rfl,
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by
        intro _ _ _ _ c _ _ _ hc
        dsimp only at hc ⊢
        conv_lhs => rw [evalWithOracle.eq_def]
        cases c <;> simp only [Cond.Holds] at hc <;>
          simp [Cond.evalBool, hc],
      by
        intro _ _ _ _ c _ _ _ hc
        dsimp only at hc ⊢
        conv_lhs => rw [evalWithOracle.eq_def]
        cases c <;> simp only [Cond.Holds] at hc <;>
          simp [Cond.evalBool, hc],
      by intros; dsimp only; conv_lhs => rw [evalWithOracle.eq_def],
      by
        intro _ _ _ _ c _ _ hc
        dsimp only at hc ⊢
        conv_lhs => rw [evalWithOracle.eq_def]
        cases c <;> simp only [Cond.Holds] at hc <;>
          simp [Cond.evalBool, hc],
      by
        intro _ _ _ _ c _ _ hc
        dsimp only at hc ⊢
        conv_lhs => rw [evalWithOracle.eq_def]
        cases c <;> simp only [Cond.Holds] at hc <;>
          simp [Cond.evalBool, hc],
      @DemonicExecWithin.op, @DemonicExecWithin.grow, @DemonicExecWithin.shrink,
      @DemonicExecWithin.size, @DemonicExecWithin.seq,
      @DemonicExecWithin.branch_pos, @DemonicExecWithin.branch_neg,
      @DemonicExecWithin.loop_exit, @DemonicExecWithin.loop_iter⟩
    ⟨DictOp, @DictOp.query, @DictOp.insert, @DictOp.delete,
      @DictOp.elim, @DictOp.rec,
      @stepDict, @foldStepDict, @validDictOp, @ValidDictHistory,
      decodeQueryRegs, @OpOutputCorrect,
      @loadOpRegs, @loadDeleteKeyReg, loadClientAllocRegs,
      InEpochHistory, @InEpochOracleTrace, @nextEpochCap,
      @MaxCardLe, @ReachedEpochsFit, @PureMultiEpochSpaceTrace⟩
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @InEpochOracleTrace.nil, @InEpochOracleTrace.cons,
      fun _ _ _ => rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      @PureMultiEpochSpaceTrace.nil, @PureMultiEpochSpaceTrace.cons⟩

/-- Pure mathematical multi-epoch hysteresis, non-vacuous reached-capacity fit, every-step succinct
space from `(0, emptyDict U)`, and `O(1)` amortized rebuild potential across arbitrary
capacity-changing operation sequences (`ops : List (DictOp U)`).

This theorem is stated purely over the multi-epoch hysteresis state machine (`nextEpochCap`) without
a synthetic `Code` existential, cleanly separating the mathematical multi-epoch invariants from the
compiled in-epoch programs of `bitResizableDictionary_compiled`:
1. whenever the active key count along `ops` never exceeds `M` (`MaxCardLe M s_abs ops`) and every
   `N' ≤ min U (2 * M)` fits in `< 2 ^ w` bits, `ReachedEpochsFit` holds (supporting `U = 2 ^ w - 1`
   and arbitrary `V`);
2. from `(0, emptyDict U)`, any sequence `ops` satisfying `ReachedEpochsFit` maintains `EpochInv`
   and succinct bit space `optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w` at every step
   (`PureMultiEpochSpaceTrace`);
3. the rebuild-potential function `epochPotential U N m` absorbs the `O(m')`-word cost of rebuilding
   into `targetCap U m'` whenever `EpochInv U N m'` is violated, paying at most `7849` amortized
   units per operation. -/
theorem bitResizableDictionary_multiEpoch_pure :
    ∃ (epochMetaWords : ℕ → ℕ → ℕ → ℕ),
      (∀ U w, epochMetaWords U w 0 = 4) ∧
      (∀ {U w N : ℕ}, 0 < w → N ≤ U → U < 2 ^ w → epochMetaWords U w N ≤ 16 * N + 209) ∧
      (∀ {U V w N n_t : ℕ}, 0 < w → U ≤ 2 ^ w → EpochInv U N n_t →
        epochMetaWords U w N * w + n_t * itemBits U V N ≤
          optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w) ∧
      (∀ {U V w M : ℕ},
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * itemBits U V N
        (∀ N' ≤ min U (2 * M), dbs N' N' < 2 ^ w) →
        ∀ {N : ℕ} {s_abs : DictState U} {ops : List (DictOp U)},
          N ≤ min U (2 * M) →
          MaxCardLe M s_abs ops →
          ReachedEpochsFit dbs w N s_abs ops) ∧
      (∀ {U V w : ℕ}, 0 < w → U < 2 ^ w →
        let dbs : ℕ → ℕ → ℕ :=
          fun N n_t => epochMetaWords U w N * w + n_t * itemBits U V N
        ∀ (ops : List (DictOp U)),
          ReachedEpochsFit dbs w 0 (emptyDict U) ops →
          PureMultiEpochSpaceTrace dbs V w 0 (emptyDict U) ops) ∧
      (∀ {U w N m m' : ℕ}, 0 < w → U < 2 ^ w →
        EpochInv U N m → m' ≤ U → m' ≤ m + 1 → m ≤ m' + 1 →
        let N' := if EpochInv U N m' then N else targetCap U m'
        let cost :=
          if EpochInv U N m' then 1
          else
            4 + 4 * m + 2 * epochMetaWords U w N +
              5 * epochMetaWords U w (targetCap U m') + 1102 * m'
        cost + 2660 * epochPotential U N' m' ≤
          2660 * epochPotential U N m + 7849) :=
  ComplexityAbstracts.BitResizableDictionaryBridge.bitResizableDictionary_multiEpoch_pure
    ⟨BinOp, .add, .sub, .mul, .div, .mod, .bitAnd, .bitOr, .bitXor, .shiftLeft, .shiftRight,
      BinOp.eval,
      Cond, @Cond.eq, @Cond.lt,
      OpInstr, @OpInstr.const, @OpInstr.copy, @OpInstr.bin, @OpInstr.width, @OpInstr.load,
      @OpInstr.store,
      Code, @Code.op, @Code.grow, @Code.shrink, @Code.size, @Code.seq, @Code.branch,
      @Code.loop, @Code.rand,
      Data, @Data.mk, @Data.regs, @Data.mem, @Data.bitSize,
      @evalOp, @Cond.Holds, @evalWithOracle, @DemonicExecWithin⟩
    ⟨DictOp, @DictOp.query, @DictOp.insert, @DictOp.delete,
      @DictOp.elim, @DictOp.rec,
      @stepDict, @foldStepDict, @validDictOp, @ValidDictHistory,
      decodeQueryRegs, @OpOutputCorrect,
      @loadOpRegs, @loadDeleteKeyReg, loadClientAllocRegs,
      InEpochHistory, @InEpochOracleTrace, @nextEpochCap,
      @MaxCardLe, @ReachedEpochsFit, @PureMultiEpochSpaceTrace⟩
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @InEpochOracleTrace.nil, @InEpochOracleTrace.cons,
      fun _ _ _ => rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      @PureMultiEpochSpaceTrace.nil, @PureMultiEpochSpaceTrace.cons⟩

/--
info: abstract audit passed for `ComplexityAbstracts.BitResizableDictionaryAbstract`: 375 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.BitResizableDictionaryAbstract

end ComplexityAbstracts.BitResizableDictionaryAbstract
