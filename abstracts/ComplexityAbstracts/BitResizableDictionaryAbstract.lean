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
# Formal Abstract: Capacity-Unbounded Succinct Dynamic Dictionary on a Bit-Resizable Word-RAM

This self-contained file states the formal specification and headline correctness, time, space, and
memory-reuse theorems for the capacity-unbounded succinct dynamic dictionary with deletions on the
bit-granular resizable `w`-bit Word-RAM (`Cslib.DataStructure.Dictionary.BitResizable`), following
`[BenderFarachColtonKuszmaulKuszmaul2024]` (SOSA 2024), `[ArbitmanNaorSegev2010]` (FOCS 2010),
`[BenderConwayFarachColtonKuszmaulTagliavini2023]` (*J. ACM* 2023),
`[BenderFarachColtonKuszmaulKuszmaulLiu2022]` (*J. ACM* 2024), and `[LiLiangYuZhou2023]` (FOCS 2023)
/ `[LiLiangYuZhou2024]` (STOC 2024).

## Bit-Granular Resizable Word-RAM Model

A machine state `Data r` over `r` registers consists of:
- `regs : Fin r → ℕ`: `r` word registers;
- `mem : ℕ → ℕ`: the underlying word array;
- `bitSize : ℕ`: the current allocated bit count.

At word width `w`, bit index `i` resides at bit offset `i % w` of word `i / w` (`getBit w mem i`).
In any well-formed state (`Data.WellFormed w`), all registers, memory words, and `bitSize` are
strictly less than `2 ^ w`, and every unallocated bit `i ≥ bitSize` is zero
(`getBit w mem i = false`). Word loads and stores are admissible on all active words
`a < ceilDiv bitSize w`.

In addition to standard `w`-bit Word-RAM instructions (`OpInstr`), structured programs (`Code`)
provide three bit-granular memory-resizing primitives:
- `grow dst δReg`: increases `bitSize` by `δ = regs δReg` bits, stores the old `bitSize` into
  register `dst`, and requires the program to succeed under **demonic non-determinism**
  (`DirtyGrow`) for *every* post-grow word array `mem'` that preserves all pre-existing allocated
  bits `[0, bitSize)` and keeps all unallocated bits `[bitSize + δ, ∞)` zero, while allowing the
  newly allocated bit range `[bitSize, bitSize + δ)` to contain arbitrary dirty bits;
- `shrink δReg`: decreases `bitSize` by `δ = regs δReg` bits (`δ ≤ bitSize`) and zeroes the
  released bit interval `[bitSize - δ, bitSize)` (`clearRangeMem`) to maintain the zeroed-tail
  invariant;
- `size dst`: reads the current `bitSize` into register `dst` in `1` instruction.

Both `grow` and `shrink` by `δ` bits charge `max 1 (ceilDiv δ w)` instructions, reflecting the word
parallelism of clearing or initializing `⌈δ / w⌉` machine words.

## Capacity-Unbounded Succinct Dynamic Dictionary and Memory Reuse

The dictionary supports `query u`, `insert u v`, and `delete u` over keys `u : Fin U` and values
`v < V` starting from the empty dictionary `emptyDict U`, with **no capacity cap** (`n_t` may grow
and shrink arbitrarily between `0` and `U` across operation sequences of any length):
1. **Pointwise succinct bit space**: at every step `t` with `n_t = (dictDom s_abs).card` active
   keys in an epoch with capacity parameter `N`, `EpochInv U N n_t` holds (`n_t = 0 ∧ N = 0`, or
   `1 ≤ n_t ≤ N ≤ 4 * n_t` and `N ≤ U`), and the exact allocated bit count `x.bitSize` equals
   `dictBitSize N n_t ≤ optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w` bits, where
   `optBits U V n_t = ⌈log₂ C(U, n_t)⌉ + n_t · ⌈log₂ V⌉` is the information-theoretic minimum bit
   count and `logLogFactor n_t = ⌈log₂ ⌈log₂ (max n_t 4)⌉⌉`. Within each epoch, inserting or
   deleting an item changes `dictBitSize N n_t` by exactly `itemBits U V N` bits
   (`dictBitSize N (n_t + 1) = dictBitSize N n_t + itemBits U V N`), and the empty dictionary uses
   `dictBitSize 0 0 = 4 * w` bits.
2. **Expected `O(1)` amortized time per operation**: for every valid operation `op : DictOp U`, the
   expected amortized instruction overhead over the epoch's quotient-hash seed distribution
   `epochSeedPMF N` is at most `8034`, and `op` executes in `T` instructions under
   `DemonicExecWithin` satisfying the potential inequality
   `T + totalPotential N' (stepDict s_abs op) c' ≤`
   `totalPotential N s_abs c + stepOverhead N θ s_abs op`.
3. **Subroutine reuse of released bits**: when `delete u` removes an active key within an epoch,
   `x.bitSize` shrinks by `itemBits U V N` bits via `shrink`, and a client program can immediately
   re-allocate `b ≤ itemBits U V N` of those released bits via `grow` (`clientAllocBitsCode`),
   storing a `b`-bit value at bit offset `x.bitSize - itemBits U V N` without increasing peak bit
   usage (`z.bitSize ≤ x.bitSize`) while preserving all lower dictionary bits.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.BitResizableDictionaryBridge`, and `#check_abstract` audits the dependency
boundary.
-/

namespace ComplexityAbstracts.BitResizableDictionaryAbstract

open scoped ENNReal BigOperators

/-! ## Bit-Granular Memory Operations -/

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
`[bitSize + δ, ∞)`, while leaving the newly allocated bits `[bitSize, bitSize + δ)` unconstrained
(adversarially chosen dirty bits). -/
def DirtyGrow (w : ℕ) (mem : ℕ → ℕ) (bitSize δ : ℕ) (mem' : ℕ → ℕ) (bitSize' : ℕ) : Prop :=
  bitSize' = bitSize + δ ∧
  (∀ q : ℕ, mem' q < 2 ^ w) ∧
  (∀ i < bitSize, getBit w mem' i = getBit w mem i) ∧
  (∀ i : ℕ, bitSize + δ ≤ i → getBit w mem' i = false)

/-- Clear bits in `[lo, hi)` of word `q` at word width `w`. -/
def clearRangeWord (w word q lo hi : ℕ) : ℕ :=
  let start := lo - q * w
  let stop := min w (hi - q * w)
  clearMask (word &&& bitMask w) (sliceMask start (stop - start))

/-- Clear bit range `[lo, hi)` across a `w`-bit word array `mem : ℕ → ℕ`. -/
def clearRangeMem (w : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → ℕ :=
  fun q => clearRangeWord w (mem q) q lo hi

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

/-- Whether condition `c : Cond r` holds on state `x : Data r`. -/
def Cond.Holds {r : ℕ} : Cond r → Data r → Prop
  | .eq i j, x => x.regs i = x.regs j
  | .lt i j, x => x.regs i < x.regs j

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

/-- Total correctness under demonic non-determinism for `grow` (`DemonicExecWithin w c x P T`):
executing `c : Code r` from state `x : Data r` at word width `w` terminates within at most `T`
instructions and reaches a state satisfying postcondition `P` for *every* adversarial choice of
dirty bits in `DirtyGrow`. -/
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

/-! ## Capacity-Unbounded Dynamic Dictionary Specification and Succinct Space Quantities -/

/-- Abstract state of a dictionary over key universe `Fin U`. -/
abbrev DictState (U : ℕ) := Fin U → Option ℕ

/-- The empty dictionary over `Fin U`. -/
def emptyDict (U : ℕ) : DictState U := fun _ => none

/-- The finite set of keys currently present in dictionary state `s`. -/
def dictDom {U : ℕ} (s : DictState U) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Operations on a dynamic dictionary over key universe `Fin U`:
- `query u`: look up the value associated with `u : Fin U` (`some v` if present, `none` if absent);
- `insert u v`: associate key `u : Fin U` with value `v : ℕ` (inserting or overwriting in place);
- `delete u`: remove key `u : Fin U` if present (no-op if absent). -/
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

/-- Decode a `query` result from the post-operation registers (`reg 1 = 0` encodes `none`;
`reg 1 ≠ 0` encodes `some (reg 0)`). -/
def decodeQueryRegs (x : Data 12) : Option ℕ :=
  if x.regs ⟨1, by decide⟩ = 0 then none else some (x.regs ⟨0, by decide⟩)

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
def EpochInv (U N n_t : ℕ) : Prop :=
  (n_t = 0 ∧ N = 0) ∨ (1 ≤ n_t ∧ n_t ≤ N ∧ N ≤ 4 * n_t ∧ N ≤ U)

/-- Target epoch capacity `min U (2 * n')` (or `0` when `n' = 0`) selected when an operation steps
outside `EpochInv`. -/
def targetCap (U n' : ℕ) : ℕ :=
  if n' = 0 then 0 else min U (2 * n')

/-- For every `N' ≤ U`, `EpochInv U N' N'` holds (`N' = 0` or `1 ≤ N' ≤ N' ≤ 4 * N' ∧ N' ≤ U`). -/
theorem epochInv_self {U N' : ℕ} (hN' : N' ≤ U) : EpochInv U N' N' := by
  rcases Nat.eq_zero_or_pos N' with rfl | hpos
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨hpos, le_rfl, by omega, hN'⟩

/-- Multi-operation execution trace of `ops : List (DictOp U)` from state `(N, θ, s_abs, c, x)`
with total amortized instruction budget `B_tot`. At each step `op :: ops`, `DictInv` holds before
and after `op`, the expected amortized overhead over `epochSeedPMF N` is at most `8034`, `code`
executes in `T` instructions under `DemonicExecWithin` satisfying the amortized potential
inequality `T + totalPotential N' (stepDict s_abs op) c' ≤ totalPotential N s_abs c + stepOverhead`,
every `query u` returns `s_abs u` in `decodeQueryRegs y`, and the remaining operations `ops`
execute from `y` with budget `B_rest`. -/
def ExecTrace (U _V w : ℕ)
    (EpochSeed : ℕ → Type)
    (epochSeedPMF : ∀ N, PMF (EpochSeed N))
    (Companion : Type)
    (DictInv : ∀ N, EpochSeed N → DictState U → Companion → Data 12 → Prop)
    (totalPotential : ℕ → DictState U → Companion → ℕ)
    (stepOverhead : ∀ N, EpochSeed N → DictState U → DictOp U → ℕ) :
    List (DictOp U) → ∀ (N : ℕ), EpochSeed N → DictState U →
      Companion → Data 12 → ℕ → Prop
  | [], N, θ, s_abs, c, x, B_tot =>
    DictInv N θ s_abs c x ∧ B_tot = 0
  | op :: ops, N, θ, s_abs, c, x, B_tot =>
    DictInv N θ s_abs c x ∧
    (∑' θ₀ : EpochSeed N,
      (epochSeedPMF N θ₀ : ℝ≥0∞) * ((stepOverhead N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
    ∃ (N' : ℕ) (θ' : EpochSeed N') (c' : Companion)
      (code : Code 12) (T B_rest : ℕ),
      B_tot = stepOverhead N θ s_abs op + B_rest ∧
      T + totalPotential N' (stepDict s_abs op) c' ≤
        totalPotential N s_abs c + stepOverhead N θ s_abs op ∧
      (∃ ts_rest : List ℕ,
        ts_rest.length = ops.length ∧
        ts_rest.sum ≤ totalPotential N' (stepDict s_abs op) c' + B_rest) ∧
      DemonicExecWithin w code x
        (fun y =>
          DictInv N' θ' (stepDict s_abs op) c' y ∧
          (∀ u, op = .query u → decodeQueryRegs y = s_abs u) ∧
          ExecTrace U _V w EpochSeed epochSeedPMF Companion DictInv
            totalPotential stepOverhead ops N' θ' (stepDict s_abs op) c' y B_rest)
        T

/-- Base-case constructor law for `ExecTrace` on the empty operation sequence `[]`. -/
theorem execTrace_nil {U V w : ℕ} {EpochSeed : ℕ → Type} {epochSeedPMF : ∀ N, PMF (EpochSeed N)}
    {Companion : Type}
    {DictInv : ∀ N, EpochSeed N → DictState U → Companion → Data 12 → Prop}
    {totalPotential : ℕ → DictState U → Companion → ℕ}
    {stepOverhead : ∀ N, EpochSeed N → DictState U → DictOp U → ℕ}
    {N : ℕ} {θ : EpochSeed N} {s_abs : DictState U} {c : Companion} {x : Data 12}
    (hinv : DictInv N θ s_abs c x) :
    ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
      totalPotential stepOverhead [] N θ s_abs c x 0 :=
  ⟨hinv, rfl⟩

/-- Step constructor law for `ExecTrace` on `op :: ops`. -/
theorem execTrace_cons {U V w : ℕ} {EpochSeed : ℕ → Type} {epochSeedPMF : ∀ N, PMF (EpochSeed N)}
    {Companion : Type}
    {DictInv : ∀ N, EpochSeed N → DictState U → Companion → Data 12 → Prop}
    {totalPotential : ℕ → DictState U → Companion → ℕ}
    {stepOverhead : ∀ N, EpochSeed N → DictState U → DictOp U → ℕ}
    {op : DictOp U} {ops : List (DictOp U)}
    {N N' : ℕ} {θ : EpochSeed N} {θ' : EpochSeed N'}
    {s_abs : DictState U} {c c' : Companion}
    {x : Data 12} {code : Code 12} {T B_rest B_tot : ℕ}
    (hinv : DictInv N θ s_abs c x)
    (htsum : (∑' θ₀ : EpochSeed N,
      (epochSeedPMF N θ₀ : ℝ≥0∞) * ((stepOverhead N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034)
    (hB : B_tot = stepOverhead N θ s_abs op + B_rest)
    (hpot : T + totalPotential N' (stepDict s_abs op) c' ≤
      totalPotential N s_abs c + stepOverhead N θ s_abs op)
    (hts : ∃ ts_rest : List ℕ,
      ts_rest.length = ops.length ∧
      ts_rest.sum ≤ totalPotential N' (stepDict s_abs op) c' + B_rest)
    (hexec : DemonicExecWithin w code x
      (fun y =>
        DictInv N' θ' (stepDict s_abs op) c' y ∧
        (∀ u, op = .query u → decodeQueryRegs y = s_abs u) ∧
        ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
          totalPotential stepOverhead ops N' θ' (stepDict s_abs op) c' y B_rest)
      T) :
    ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
      totalPotential stepOverhead (op :: ops) N θ s_abs c x B_tot :=
  ⟨hinv, htsum, N', θ', c', code, T, B_rest, hB, hpot, hts, hexec⟩

/-! ## Headline Theorem -/

/-- **Capacity-Unbounded Succinct Dynamic Dictionary on a Bit-Resizable Word-RAM
(`bitResizableDictionary`):**
For every key universe `U`, value bound `V`, and word width `w` satisfying `4 ≤ w`, `U < 2 ^ w`,
and `V ≤ 2 ^ w`, there exist an epoch seed family `EpochSeed : ℕ → Type` with uniform distribution
`epochSeedPMF : ∀ N, PMF (EpochSeed N)`, ghost companion state `Companion` (`emptyCompanion`),
representation invariant `DictInv`, potential `totalPotential`, per-step overhead `stepOverhead`,
exact bit-footprint function `dictBitSize : ℕ → ℕ → ℕ`, initialization program `initCode`, and
client bit-allocation subroutine `clientAllocBitsCode` such that:

1. **Exact bit-level growth/shrinkage and pointwise succinct space bound**:
   - `dictBitSize 0 0 = 4 * w` (in the empty dictionary state `N = 0, n_t = 0`),
   - `dictBitSize N (n_t + 1) = dictBitSize N n_t + itemBits U V N` (each item insertion or
     deletion within epoch `N` grows or shrinks the bit footprint by exactly `itemBits U V N`
     bits),
   - whenever `EpochInv U N n_t` holds,
     `dictBitSize N n_t ≤ optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w`, and
   - at every reachable state satisfying `DictInv N θ s_abs c x` with `n_t = (dictDom s_abs).card`
     active keys, `x.WellFormed w`, `EpochInv U N n_t`, `x.bitSize = dictBitSize N n_t`, and
     `x.bitSize ≤ optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w`.
2. **Expected `O(1)` amortized step transition**: for every state satisfying
   `DictInv N θ s_abs c x` and every valid operation `op : DictOp U` (`validDictOp V s_abs op`),
   the expected amortized instruction overhead over `θ₀ ← epochSeedPMF N` is at most `8034`, and
   (when `∀ N' ≤ U, dictBitSize N' N' < 2 ^ w`) `op` executes in `T` instructions under
   `DemonicExecWithin` preserving `DictInv`, returning `s_abs u` for every `query u`, and
   satisfying
   `T + totalPotential N' (stepDict s_abs op) c' ≤`
   `totalPotential N s_abs c + stepOverhead N θ s_abs op`.
3. **Full operation-sequence execution from empty**: from any well-formed initial state
   `x₀ : Data 12` with `x₀.bitSize = 0` and any valid operation sequence `ops : List (DictOp U)` of
   arbitrary length (`ValidDictHistory V (emptyDict U) ops`), `initCode θ₀` initializes the empty
   dictionary in `21` instructions (`y₀.bitSize = 4 * w`) and `ops` executes via `ExecTrace` with
   step instruction counts `ts : List ℕ` (`ts.length = ops.length`, `ts.sum ≤ B_tot`).
4. **Client subroutine reuse of bits released by `delete`**: when an active key `u`
   (`(s_abs u).isSome`) is deleted within an epoch and a client immediately executes
   `clientAllocBitsCode b v_client` (`b ≤ w`, `b ≤ itemBits U V N`, `v_client < 2 ^ b`), the
   composed program `Code.seq code_del (clientAllocBitsCode b v_client)` executes in `T + 46`
   instructions under `DemonicExecWithin`, shrinking `bitSize` by `itemBits U V N` bits and
   reusing the released bit interval `[x.bitSize - itemBits U V N, x.bitSize - itemBits U V N + b)`
   so that `z.bitSize = x.bitSize - itemBits U V N + b ≤ x.bitSize`,
   `getField w z.mem (x.bitSize - itemBits U V N) b = v_client`, and all lower dictionary bits in
   `[0, x.bitSize - itemBits U V N)` are preserved.

References: `[BenderFarachColtonKuszmaulKuszmaul2024]`; `[ArbitmanNaorSegev2010]`;
`[BenderConwayFarachColtonKuszmaulTagliavini2023]`; `[BenderFarachColtonKuszmaulKuszmaulLiu2022]`;
`[LiLiangYuZhou2023]`; `[LiLiangYuZhou2024]`. -/
theorem bitResizableDictionary {U V w : ℕ} (hw : 4 ≤ w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w) :
    ∃ (EpochSeed : ℕ → Type)
      (epochSeedPMF : ∀ N, PMF (EpochSeed N))
      (_epochSeedNonempty : ∀ N, Nonempty (EpochSeed N))
      (Companion : Type)
      (emptyCompanion : Companion)
      (DictInv : ∀ N, EpochSeed N → DictState U → Companion → Data 12 → Prop)
      (totalPotential : ℕ → DictState U → Companion → ℕ)
      (stepOverhead : ∀ N, EpochSeed N → DictState U → DictOp U → ℕ)
      (dictBitSize : ℕ → ℕ → ℕ)
      (initCode : EpochSeed 0 → Code 12)
      (clientAllocBitsCode : ℕ → ℕ → Code 12),
      dictBitSize 0 0 = 4 * w ∧
      (∀ N n_t, dictBitSize N (n_t + 1) = dictBitSize N n_t + itemBits U V N) ∧
      (∀ N n_t, EpochInv U N n_t →
        dictBitSize N n_t ≤
          optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w) ∧
      (∀ {N : ℕ} (θ : EpochSeed N) {s_abs : DictState U} {c : Companion}
          {x : Data 12},
        DictInv N θ s_abs c x →
        let n_t := (dictDom s_abs).card
        x.WellFormed w ∧
        EpochInv U N n_t ∧
        x.bitSize = dictBitSize N n_t ∧
        x.bitSize ≤
          optBits U V n_t + 680 * n_t * logLogFactor n_t + 218 * w) ∧
      (∀ (_hfit_all : ∀ N' ≤ U, dictBitSize N' N' < 2 ^ w)
          {N : ℕ} (θ : EpochSeed N) {s_abs : DictState U} {c : Companion}
          {x : Data 12},
        DictInv N θ s_abs c x →
        ∀ (op : DictOp U), validDictOp V s_abs op →
        ∀ (_θ_re : EpochSeed (targetCap U (dictDom (stepDict s_abs op)).card)),
          (∑' θ₀ : EpochSeed N,
            (epochSeedPMF N θ₀ : ℝ≥0∞) *
              ((stepOverhead N θ₀ s_abs op : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
          ∃ (N' : ℕ) (θ' : EpochSeed N') (c' : Companion)
            (code : Code 12) (T : ℕ),
            DemonicExecWithin w code x
              (fun y =>
                DictInv N' θ' (stepDict s_abs op) c' y ∧
                (∀ u, op = .query u → decodeQueryRegs y = s_abs u)) T ∧
            T + totalPotential N' (stepDict s_abs op) c' ≤
              totalPotential N s_abs c + stepOverhead N θ s_abs op) ∧
      (∀ (_hfit_all : ∀ N' ≤ U, dictBitSize N' N' < 2 ^ w)
          (θ₀ : EpochSeed 0) {x₀ : Data 12},
        x₀.WellFormed w → x₀.bitSize = 0 →
        ∀ (ops : List (DictOp U)), ValidDictHistory V (emptyDict U) ops →
          ∃ B_tot : ℕ,
            DemonicExecWithin w (initCode θ₀) x₀
              (fun y₀ =>
                DictInv 0 θ₀ (emptyDict U) emptyCompanion y₀ ∧
                y₀.bitSize = 4 * w ∧
                ExecTrace U V w EpochSeed epochSeedPMF Companion DictInv
                  totalPotential stepOverhead ops 0 θ₀ (emptyDict U)
                  emptyCompanion y₀ B_tot ∧
                ∃ ts : List ℕ, ts.length = ops.length ∧ ts.sum ≤ B_tot)
              21) ∧
      (∀ {N : ℕ} (θ : EpochSeed N) {s_abs : DictState U} {c : Companion}
          {x : Data 12},
        DictInv N θ s_abs c x →
        ∀ (u : Fin U), (s_abs u).isSome →
        EpochInv U N (dictDom (stepDict s_abs (.delete u))).card →
        ∀ {b v_client : ℕ}, b ≤ w → b ≤ itemBits U V N → v_client < 2 ^ b →
          let s_abs' := stepDict s_abs (.delete u)
          let bit_after_del := x.bitSize - itemBits U V N
          ∃ (c' : Companion) (code_del : Code 12) (T : ℕ),
            T + totalPotential N s_abs' c' ≤
              totalPotential N s_abs c + stepOverhead N θ s_abs (.delete u) ∧
            (∑' θ₀ : EpochSeed N,
              (epochSeedPMF N θ₀ : ℝ≥0∞) *
                ((stepOverhead N θ₀ s_abs (.delete u) : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
            DemonicExecWithin w (.seq code_del (clientAllocBitsCode b v_client)) x
              (fun z =>
                ∃ y : Data 12,
                  DictInv N θ s_abs' c' y ∧
                  y.bitSize = bit_after_del ∧
                  z.WellFormed w ∧
                  z.bitSize = bit_after_del + b ∧
                  z.bitSize ≤ x.bitSize ∧
                  getField w z.mem bit_after_del b = v_client ∧
                  (∀ i < bit_after_del,
                    getBit w z.mem i = getBit w y.mem i))
              (T + 46)) :=
  ComplexityAbstracts.BitResizableDictionaryBridge.bitResizableDictionary
    ⟨BinOp, .add, .sub, .mul, .div, .mod, .bitAnd, .bitOr, .bitXor, .shiftLeft, .shiftRight,
      BinOp.eval,
      Cond, @Cond.eq, @Cond.lt,
      OpInstr, @OpInstr.const, @OpInstr.copy, @OpInstr.bin, @OpInstr.width, @OpInstr.load,
      @OpInstr.store,
      Code, @Code.op, @Code.grow, @Code.shrink, @Code.size, @Code.seq, @Code.branch,
      @Code.loop, @Code.rand,
      Data, @Data.mk, @Data.regs, @Data.mem, @Data.bitSize,
      @evalOp, @Cond.Holds, @DemonicExecWithin⟩
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun x => by cases x; rfl,
      fun f x y => by cases f <;> rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      @DemonicExecWithin.op, @DemonicExecWithin.grow, @DemonicExecWithin.shrink,
      @DemonicExecWithin.size, @DemonicExecWithin.seq,
      @DemonicExecWithin.branch_pos, @DemonicExecWithin.branch_neg⟩
    ⟨DictOp, @DictOp.query, @DictOp.insert, @DictOp.delete,
      @DictOp.elim, @DictOp.rec,
      @stepDict, @validDictOp, @ValidDictHistory, decodeQueryRegs, @ExecTrace⟩
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ => rfl,
      @execTrace_nil, @execTrace_cons⟩
    hw hU hV

/--
info: abstract audit passed for `ComplexityAbstracts.BitResizableDictionaryAbstract`: 299 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.BitResizableDictionaryAbstract

end ComplexityAbstracts.BitResizableDictionaryAbstract
