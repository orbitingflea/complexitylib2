/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.ResizableSuccinctDictionaryBridge
import Cslib.Probability.PMF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: Word-Granular Resizable Word-RAM, Dynamic Array, and Succinct Dictionary

This self-contained file states the formal model, stepwise space bounds, expected-amortized time
bounds, and client memory-reuse theorems for the word-granular resizable Word-RAM data structures
in Complexitylib:

1. **Word-Granular Resizable Word-RAM Model** (`DemonicGrow`, `shrinkMem`, `zeroSlice`, and
   `demonicGrow_zeroSlice_eq`, following `[Brodnik1999]`, `[PatrascuThorup2014]`, and `[Yu2020]`):
   A structure's active memory at step `t` is the contiguous prefix `[0, s_t)` of `s_t` machine
   words (`s_t * w` bits). Growing by `delta` words (`DemonicGrow w s delta mem mem'`) extends the
   active frontier to `s + delta` with **arbitrary (`demonic`) `w`-bit values** in
   `[s, s + delta)`, which a `4 * delta + 8`-instruction loop (`zeroSlice`) zeroes in `O(delta)`
   worst-case time. Shrinking by `k ≤ s` words (`shrinkMem`) contracts the frontier to `s - k` in
   `1` instruction so the released addresses `[s - k, s)` can be immediately reused by subsequent
   allocations.

2. **Stage 1 — Resizable Bit-Packed Array** (`resizableArray_space_tight`, following
   `[Brodnik1999]`):
   A resizable array of `n_t` `b`-bit items (`0 < b ≤ w`) packed across `w`-bit words uses
   `arrayActiveWords w b n_t = 1 + ⌈n_t * b / w⌉` words (`< n_t * b + 2 * w` bits, with explicit
   additive term `2 * w` bits: `1` header word for `n_t` plus `< w` bits of ceiling rounding) and
   supports `read` (`4` instructions), `write` (`8` instructions), `append` (`22` instructions),
   and `pop` (`5` instructions) in `O(1)` worst-case time per operation.

3. **Stage 2 — Resizable Succinct Dynamic Dictionary** (`activeEpochWords_le_two_mul`,
   `activeEpochWords_le_four_mul`, `unbounded_seq_expected_amortized`, and
   `dictionary_client_memory_reuse`, following `[BenderFarachColtonKuszmaul2022]`, `[Yu2020]`,
   `[RamanRamanRao2002]`, and `[Patrascu2008]`):
   Supporting `insert`, `delete`, and `query` from the empty dictionary over key universe `Fin U`
   and value range `Fin V` (`U, V < 2 ^ w`, **with no capacity cap** `n_max`), the resizable
   succinct dictionary maintains an epoch capacity `N_t = min (2 * n_init) U` satisfying
   `n_t ≤ N_t ≤ 4 * n_t` (`EpochValid n_t N_t`) around the current live key count `n_t`:
   - **Stepwise `n_t`-tight space:** At every step `t`, the active word footprint
     `activeEpochWords U V w N_t n_t` is at most
     `succinctWords 1227 213 U V w n_t`
     (`= ⌈(OPT(U, V, n_t) + 1227 * n_t * logLogFactor n_t) / w⌉ + 213`)
     words, which in bits is at most
     `OPT(U, V, n_t) + 1227 * n_t * logLogFactor n_t + 214 * w` bits (`214 * w` bits is the
     explicit additive term forced by word-granular allocation of the `12` sub-arrays and lookup
     tables).
   - **`O(1)` expected amortized time:** Both in-place operations within an epoch and full epoch
     rebuilds when `n_t` exits `[N_t / 4, N_t]` are paid for by a uniform `O(1)` per-operation
     amortized charge `resizableChargeVal` via the epoch potential
     `2 * rebuildUnitCost * |n_t - n_init|`.
   - **Client subroutine memory reuse:** When deletions shrink the dictionary's tail by `Δ` words
     or when the dictionary is deallocated via `.shrink`, the frontier contracts in `O(1)`
     instructions and a subsequent client allocation under demonic `DemonicGrow` reuses the exact
     same memory addresses `[base + sp₂, base + sp₂ + k_client)` (or `[base, base + k_client)`)
     while preserving all live caller data below the contraction point.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.ResizableSuccinctDictionaryBridge`, and `#check_abstract` audits the
dependency boundary.
-/

namespace ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

open scoped ENNReal

/-! ## Word-Granular Resizable Word-RAM Memory Model & Instruction Set -/

/-- Exact binary ALU operations of the Word-RAM. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- Exact natural-number evaluation of `AluOp`, or `none` on underflow / division by zero. -/
def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, x, y => x + y
  | .sub, x, y => if y ≤ x then x - y else none
  | .mul, x, y => x * y
  | .div, x, y => if y = 0 then none else x / y
  | .mod, x, y => if y = 0 then none else x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => some (x * 2 ^ y)
  | .shr, x, y => some (x / 2 ^ y)

/-- Instructions of an `r`-register word-granular resizable Word-RAM:
- Ten standard Word-RAM instructions (with `.load` and `.store` bounds-checked against the active
  memory frontier `frontier`);
- `.size d`: load the current active word frontier `frontier` into register `d`;
- `.grow k`: grow the active frontier by `regs k` words with demonic `w`-bit values (`DemonicGrow`);
- `.shrink k`: shrink the active frontier by `regs k ≤ frontier` words (`shrinkMem`);
- `.rand d i`: draw uniformly from `Fin (regs i + 1)`. -/
inductive RInstr (r : ℕ)
  | const (d : Fin r) (x : ℕ)
  | copy (d i : Fin r)
  | alu (f : AluOp) (d i j : Fin r)
  | width (d : Fin r)
  | load (d a : Fin r)
  | store (a i : Fin r)
  | size (d : Fin r)
  | grow (k : Fin r)
  | shrink (k : Fin r)
  | jump (t : ℕ)
  | branchEq (i j : Fin r) (t : ℕ)
  | branchLt (i j : Fin r) (t : ℕ)
  | halt (i : Fin r)
  | rand (d i : Fin r)

/-- A resizable Word-RAM program over `r` registers is a flat list of instructions `List (RInstr r)`
indexed by `pc : ℕ` from `0`. -/
abbrev RProgram (r : ℕ) := List (RInstr r)

/-- State of an `r`-register word-granular resizable Word-RAM:
- `regs : Fin r → ℕ`: register file;
- `mem : ℕ → ℕ`: word-addressed memory;
- `frontier : ℕ`: current active memory size `s_t` in `w`-bit words (`[0, frontier)`). -/
structure RState (r : ℕ) where
  regs : Fin r → ℕ
  mem : ℕ → ℕ
  frontier : ℕ

/-- Canonical word-boundedness invariant on `RState r` at word width `w`:
every register and memory cell holds a `w`-bit word (`< 2 ^ w`), the active frontier fits in a
`w`-bit word (`frontier < 2 ^ w`), and all unallocated addresses `a ≥ frontier` store `0`. -/
def RBounded {r : ℕ} (w : ℕ) (x : RState r) : Prop :=
  ((∀ i, x.regs i < 2 ^ w) ∧ (∀ a, x.mem a < 2 ^ w)) ∧
  x.frontier < 2 ^ w ∧
  ∀ a, x.frontier ≤ a → x.mem a = 0

/-- Nondeterministic (**demonic**) word-granular growth relation `DemonicGrow w s delta mem mem'`:
growing the active frontier from `s` to `s + delta` preserves all existing words `< s` and all
unallocated words `≥ s + delta`, while placing **arbitrary `w`-bit words (`< 2 ^ w`)** in the newly
allocated slice `[s, s + delta)`. -/
def DemonicGrow (w s delta : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < s, mem' a = mem a) ∧
  (∀ a, s ≤ a → a < s + delta → mem' a < 2 ^ w) ∧
  (∀ a, s + delta ≤ a → mem' a = mem a)

/-- Word-granular `.shrink k` memory transition from frontier `s' + k` down to `s'`: clears the
released tail `[s', s' + k)` to `0` and preserves all remaining words. -/
def shrinkMem (mem : ℕ → ℕ) (s' k : ℕ) (a : ℕ) : ℕ :=
  if s' ≤ a ∧ a < s' + k then 0 else mem a

/-- Explicit zero-initialization of the word range `[lo, hi)` produced by the `4 * delta + 8`-step
Word-RAM zero-fill loop after a demonic `.grow`. -/
def zeroSlice (mem : ℕ → ℕ) (lo hi : ℕ) (a : ℕ) : ℕ :=
  if lo ≤ a ∧ a < hi then 0 else mem a

/-- Running machine configuration (`pc` and `RState r`) or halted / faulted terminal state. -/
inductive RCfg (r : ℕ)
  | running (pc : ℕ) (data : RState r)
  | halted (v : ℕ) (data : RState r)
  | faulted

/-- Single-step demonic transition relation `stepDemonicRel w p cfg cfg'` of a resizable Word-RAM
program `p : RProgram r` at word width `w`:
- `.load d a` and `.store a i` require `data.regs a < data.frontier` (faulting on out-of-bounds
  access);
- `.size d` loads `data.frontier` into `d` when `data.frontier < 2 ^ w`;
- `.grow k` nondeterministically transitions to any `mem'` satisfying
  `DemonicGrow w data.frontier (data.regs k) data.mem mem'` when
  `data.frontier + data.regs k < 2 ^ w`;
- `.shrink k` transitions deterministically to
  `shrinkMem data.mem (data.frontier - data.regs k) (data.regs k)` when
  `data.regs k ≤ data.frontier`. -/
def stepDemonicRel {r : ℕ} (w : ℕ) (p : RProgram r) : RCfg r → RCfg r → Prop
  | .halted v x, cfg' => cfg' = .halted v x
  | .faulted, cfg' => cfg' = .faulted
  | .running pc x, cfg' =>
    let setReg (d : Fin r) (val : ℕ) : RCfg r :=
      if val < 2 ^ w then .running (pc + 1) { x with regs := Function.update x.regs d val }
      else .faulted
    match p[pc]? with
    | none => cfg' = .faulted
    | some (.const d v) => cfg' = setReg d v
    | some (.copy d i) => cfg' = setReg d (x.regs i)
    | some (.alu f d i j) =>
      match f.eval (x.regs i) (x.regs j) with
      | some v => cfg' = setReg d v
      | none => cfg' = .faulted
    | some (.width d) => cfg' = setReg d w
    | some (.load d a) =>
      cfg' = if x.regs a < x.frontier then setReg d (x.mem (x.regs a)) else .faulted
    | some (.store a i) =>
      cfg' = if x.regs a < x.frontier ∧ x.regs i < 2 ^ w then
        .running (pc + 1) { x with mem := Function.update x.mem (x.regs a) (x.regs i) }
      else .faulted
    | some (.size d) => cfg' = setReg d x.frontier
    | some (.grow k) =>
      let delta := x.regs k
      if x.frontier + delta < 2 ^ w then
        ∃ mem', DemonicGrow w x.frontier delta x.mem mem' ∧
          cfg' = .running (pc + 1) ⟨x.regs, mem', x.frontier + delta⟩
      else cfg' = .faulted
    | some (.shrink k) =>
      let delta := x.regs k
      cfg' = if delta ≤ x.frontier then
        .running (pc + 1) ⟨x.regs, shrinkMem x.mem (x.frontier - delta) delta, x.frontier - delta⟩
      else .faulted
    | some (.jump t) => cfg' = .running t x
    | some (.branchEq i j t) =>
      cfg' = .running (if x.regs i = x.regs j then t else pc + 1) x
    | some (.branchLt i j t) =>
      cfg' = .running (if x.regs i < x.regs j then t else pc + 1) x
    | some (.halt i) => cfg' = .halted (x.regs i) x
    | some (.rand d i) =>
      ∃ v ≤ x.regs i, cfg' = setReg d v

/-- Deterministic-length demonic execution relation `ExecRProgramCfg w p k cfg P`:
from configuration `cfg`, every demonic choice (`DemonicGrow` on `.grow`) reaches a configuration
satisfying `P` in `k` steps of `stepDemonicRel w p`. -/
inductive ExecRProgramCfg {r : ℕ} (w : ℕ) (p : RProgram r) :
    ℕ → RCfg r → (RCfg r → Prop) → Prop
  | refl (cfg : RCfg r) (P : RCfg r → Prop) (h : P cfg) :
      ExecRProgramCfg w p 0 cfg P
  | step (k : ℕ) (cfg : RCfg r) (Q P : RCfg r → Prop)
      (h1 : (∃ cfg', stepDemonicRel w p cfg cfg') ∧
        ∀ cfg', stepDemonicRel w p cfg cfg' → Q cfg')
      (h2 : ∀ cfg', Q cfg' → ExecRProgramCfg w p k cfg' P) :
      ExecRProgramCfg w p (k + 1) cfg P

/-- `k`-step program execution `ExecRProgramDemonic w p x x' k`: starting from `.running 0 x`,
every demonic transition path of length `k` under `stepDemonicRel w p` reaches `.running k x'`. -/
def ExecRProgramDemonic {r : ℕ} (w : ℕ) (p : RProgram r) (x x' : RState r) (k : ℕ) : Prop :=
  ExecRProgramCfg w p k (.running 0 x) (fun cfg => cfg = .running k x')

private theorem execRProgramCfg_step_eq {r : ℕ} {w k : ℕ} {p : RProgram r}
    {cfg cfg₁ : RCfg r} {P : RCfg r → Prop}
    (hstep : ∀ cfg', stepDemonicRel w p cfg cfg' ↔ cfg' = cfg₁)
    (hnext : ExecRProgramCfg w p k cfg₁ P) :
    ExecRProgramCfg w p (k + 1) cfg P :=
  ExecRProgramCfg.step k cfg (fun cfg' => cfg' = cfg₁) P
    ⟨⟨cfg₁, (hstep cfg₁).mpr rfl⟩, fun cfg' h => (hstep cfg').mp h⟩
    (fun _ h => h ▸ hnext)

/-- **Demonic-Grow + Zero-Fill Equivalence (`demonicGrow_zeroSlice_eq`):**
From any memory `mem` that is zero above the current frontier `s` (`∀ a ≥ s, mem a = 0`), applying
any demonic growth transition `DemonicGrow w s delta mem mem'` followed by
`zeroSlice mem' s (s + delta)` recovers `mem` identically and establishes
`∀ a ≥ s + delta, zeroSlice mem' s (s + delta) a = 0`. -/
theorem demonicGrow_zeroSlice_eq {w s delta : ℕ} {mem mem' : ℕ → ℕ}
    (hzero : ∀ a, s ≤ a → mem a = 0)
    (hdemonic : DemonicGrow w s delta mem mem') :
    zeroSlice mem' s (s + delta) = mem ∧
    ∀ a, s + delta ≤ a → zeroSlice mem' s (s + delta) a = 0 :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_demonicGrow_zeroSlice_eq
    hzero hdemonic

/-! ## Stage 1: Resizable Bit-Packed Array of `b`-Bit Items (`b ≤ w`) -/

/-- Number of `w`-bit data words `⌈n * b / w⌉ = (n * b + w - 1) / w` needed to pack `n` items of
`b` bits each. -/
def arrayPackedWords (w b n : ℕ) : ℕ :=
  (n * b + w - 1) / w

/-- Total active word footprint `1 + ⌈n * b / w⌉` of a Stage 1 resizable array at current length
`n` (`1` header word at address `0` storing `n`, followed by `arrayPackedWords w b n` packed data
words). -/
def arrayActiveWords (w b n : ℕ) : ℕ :=
  1 + arrayPackedWords w b n

/-- **Stage 1 Stepwise Tight Bit-Space Bound (`resizableArray_space_tight`):**
For every word width `w > 0`, item bit-width `0 < b ≤ w`, and current item count `n_t : ℕ`, the
active bit footprint `arrayActiveWords w b n_t * w` satisfies
`n_t * b ≤ arrayActiveWords w b n_t * w < n_t * b + 2 * w`, where `2 * w` bits is the exact
additive overhead forced by the word-granular model (`1` word for the length header plus `< w` bits
of ceiling word-rounding). -/
theorem resizableArray_space_tight {w b : ℕ} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) (n_t : ℕ) :
    n_t * b ≤ arrayActiveWords w b n_t * w ∧
    arrayActiveWords w b n_t * w < n_t * b + 2 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_resizableArray_space_tight
    hw hb hbw n_t

/-! ## Stage 2: Unbounded-Capacity Resizable Succinct Dictionary (`insert`/`delete`/`query`) -/

/-- Dynamic dictionary operations over key universe `Fin U` with `ℕ`-valued entries:
- `insert u v`: insert or overwrite key `u : Fin U` with value `v : ℕ`;
- `delete u`: remove key `u : Fin U` if present;
- `query u`: look up the current value associated with `u : Fin U` (`Option ℕ`). -/
inductive DynamicOp (U : ℕ) : Type where
  | insert (u : Fin U) (v : ℕ) : DynamicOp U
  | delete (u : Fin U) : DynamicOp U
  | query (u : Fin U) : DynamicOp U

/-- Empty dictionary mapping every key in `Fin U` to `none`. -/
def emptyDict (U : ℕ) : Fin U → Option ℕ :=
  fun _ => none

/-- Finite set of live keys `{u : Fin U | (s u).isSome}` currently stored in dictionary `s`. -/
def dictDom {U : ℕ} (s : Fin U → Option ℕ) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Single-step abstract state transition of a dynamic dictionary:
- `insert u v` updates `s` at `u` to `some v`;
- `delete u` updates `s` at `u` to `none`;
- `query u` leaves `s` unchanged. -/
def stepDict {U : ℕ} (s : Fin U → Option ℕ) : DynamicOp U → (Fin U → Option ℕ)
  | .insert u v => Function.update s u (some v)
  | .delete u => Function.update s u none
  | .query _ => s

/-- Resulting dictionary state after executing a sequence `ops : List (DynamicOp U)` from `s`. -/
def runDict {U : ℕ} : (Fin U → Option ℕ) → List (DynamicOp U) → (Fin U → Option ℕ)
  | s, [] => s
  | s, o :: os => runDict (stepDict s o) os

/-- Admissibility of a single dynamic dictionary operation `o : DynamicOp U` under value bound `V`
with **no capacity cap** (`n_max` is absent because `(dictDom s).card ≤ U` holds for all states on
`Fin U`):
- `insert u v` requires only `v < V`;
- `delete u` and `query u` are unconditionally valid (`True`). -/
def ValidDictOp {U : ℕ} (V : ℕ) (_ : Fin U → Option ℕ) : DynamicOp U → Prop
  | .insert _ v => v < V
  | .delete _ => True
  | .query _ => True

/-- Admissibility of an unbounded-capacity operation sequence `ops : List (DynamicOp U)` under
value bound `V`. -/
def ValidDictSeq {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → List (DynamicOp U) → Prop
  | _, [] => True
  | s, o :: os => ValidDictOp V s o ∧ ValidDictSeq V (stepDict s o) os

/-- Information-theoretic minimum bit-space benchmark `OPT(U, V, n) = ⌈log₂ C(U, n)⌉ + n * ⌈log₂ V⌉`
for a dictionary storing `n` keys from `Fin U` with values in `Fin V`. -/
def optBits (U V n : ℕ) : ℕ :=
  Nat.clog 2 (U.choose n) + n * Nat.clog 2 V

/-- Doubly-logarithmic redundancy factor `⌈log₂ ⌈log₂(max n 4)⌉⌉` (of order `log log n`). -/
def logLogFactor (n : ℕ) : ℕ :=
  Nat.clog 2 (Nat.clog 2 (max n 4))

/-- Word-space bound `⌈(optBits U V n + C₁ * n * logLogFactor n) / w⌉ + C₀` for a succinct
dictionary at current item count `n`. -/
def succinctWords (C₁ C₀ U V w n : ℕ) : ℕ :=
  (optBits U V n + C₁ * n * logLogFactor n + w - 1) / w + C₀

/-- Structural recursion helper computing the smallest `t : ℕ` with `2 * 3 ^ t ≥ B` for the
reduced `k`-wise polynomial hash field over `GF(2)[X] / (X^D + X^(D/2) + 1)`. -/
def trinomialStepLoop (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0)
    (fun _ ih B => if B ≤ 2 then 0 else ih ((B + 2) / 3) + 1)
    fuel

/-- Exact word footprint of the reduced `k`-wise hash family for universe `U`, word width `w`, and
epoch capacity `N`. -/
def hashSpace (U w N : ℕ) : ℕ :=
  let w₀ := max (Nat.clog 2 U - (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4)))) 1
  let b' := (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4))) +
    min (Nat.log 2 N) (3 * Nat.clog 2 (Nat.clog 2 (max N 4)))
  let b := b' + 1
  let B := max (min w₀ (3 * b)) (max b' 1)
  let t := trinomialStepLoop B B
  let c := 3 ^ (t - 3)
  let L := 2 * 3 ^ min t 3
  let p := min (2 * c) (Nat.log 2 (w / (2 * c)))
  (1 + 3 * L) + 2 ^ (2 * c - p)

/-- Exact word footprint of the epoch metadata region (`hashSpace` plus the bit-packed global
metadata array and the `9` micro-bucket index arrays) at epoch capacity `N`. -/
def metaWords (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let m_bits := min (Nat.log 2 N) (3 * ll)
  let tot_micro := 2 ^ (b_bits + m_bits)
  let eff_cap := 4 * 2 ^ m_bits
  let eff_pos_bits := Nat.clog 2 (min N eff_cap + 1)
  let scale := 2 ^ ll
  let slab_bits := if b_bits = 0 then 0 else 2 * ll
  let slab_sz := 2 ^ slab_bits
  let dir_slabs := if b_bits = 0 then 0 else 4 * scale
  let tail_cap := if b_bits = 0 then 0 else 2 * slab_sz
  let max_slabs := if b_bits = 0 then 0 else N / slab_sz
  let gm_var := if b_bits = 0 then 0
    else 2 ^ b_bits * (3 + dir_slabs + 2 * tail_cap) + 4 * max_slabs
  let gm_len := 4 + gm_var
  let gm_bits := Nat.clog 2 (N + 1)
  hashSpace U w N +
    ((gm_len * gm_bits + w - 1) / w + 2) +
    9 * ((tot_micro * eff_pos_bits + w - 1) / w + 2)

/-- Exact word footprint of the dynamically resized quotient and value arrays at current live key
count `n` within an epoch of capacity `N`. -/
def itemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let q_bits := Nat.clog 2 U - b_bits
  let v_bits := Nat.clog 2 V
  ((n * q_bits + w - 1) / w + 2) + ((n * v_bits + w - 1) / w + 2)

/-- Total active word footprint `metaWords U w N + itemWords U V w N n` of the resizable succinct
dictionary at current live key count `n` within epoch capacity `N`. -/
def activeEpochWords (U V w N n : ℕ) : ℕ :=
  metaWords U w N + itemWords U V w N n

/-- Full epoch word footprint `activeEpochWords U V w N N` when `n = N`. -/
def epochSpace (U V w N : ℕ) : ℕ :=
  activeEpochWords U V w N N

/-- Epoch capacity invariant `n ≤ N ≤ 4 * n`: the epoch capacity `N` is within a factor of `4` of
the current live key count `n`. -/
def EpochValid (n N : ℕ) : Prop :=
  n ≤ N ∧ N ≤ 4 * n

/-- Target epoch capacity `min (2 * n_init) U` chosen when rebuilding at live key count `n_init`. -/
def targetCap (U n_init : ℕ) : ℕ :=
  min (2 * n_init) U

/-- Trace of the epoch anchor `n_init` across an operation sequence `ops : List (DynamicOp U)`:
whenever the new live key count `n' = (dictDom s').card` exits `[N / 4, N]`
(`N = targetCap U n_init`), the dictionary rebuilds into a fresh epoch anchored at
`n_init' = n'`. -/
def runEpochInit {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  | _, n_init, [] => n_init
  | s, n_init, o :: os =>
    let s' := stepDict s o
    let n' := (dictDom s').card
    let N := targetCap U n_init
    let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
    runEpochInit V s' n_init' os

/-- Maximum epoch capacity `N_t = targetCap U n_init_t` reached at any step `t` along an operation
sequence `ops : List (DynamicOp U)` starting from `(s, n_init)`. -/
def maxEpochCap {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  | _, n_init, [] => targetCap U n_init
  | s, n_init, o :: os =>
    let s' := stepDict s o
    let n' := (dictDom s').card
    let N := targetCap U n_init
    let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
    max N (maxEpochCap V s' n_init' os)

/-- Load an operation `o : DynamicOp U` into input registers `regs[250..252]` according to
Track B's calling convention (`regs[250]` = opcode `0/1/2`, `regs[251]` = key `u.val`,
`regs[252]` = value `v` for `insert`). -/
def prepareDynDictRegs {U : ℕ} (o : DynamicOp U) (regs : Fin 9957 → ℕ) : Fin 9957 → ℕ :=
  match o with
  | .insert u v =>
    Function.update
      (Function.update (Function.update regs ⟨250, by decide⟩ 0) ⟨251, by decide⟩ u.val)
      ⟨252, by decide⟩ v
  | .delete u =>
    Function.update
      (Function.update (Function.update regs ⟨250, by decide⟩ 1) ⟨251, by decide⟩ u.val)
      ⟨252, by decide⟩ 0
  | .query u =>
    Function.update
      (Function.update (Function.update regs ⟨250, by decide⟩ 2) ⟨251, by decide⟩ u.val)
      ⟨252, by decide⟩ 0

/-- Decode a `query` result `Option ℕ` from the output registers `(regs[252], regs[253])`:
`regs[252] = 0` encodes `none`, and `regs[252] ≠ 0` encodes `some regs[253]`. -/
def decodeOptionRegs (regs : Fin 9957 → ℕ) : Option ℕ :=
  if regs ⟨252, by decide⟩ = 0 then none else some (regs ⟨253, by decide⟩)

/-- Single-operation output-register correctness on machine registers `regs : Fin 9957 → ℕ`
against abstract dictionary state `s : Fin U → Option ℕ`:
for `o = .query u`, `decodeOptionRegs regs = s u`; for `insert` and `delete` (`PUnit` output),
`True`. -/
def OpOutputCorrect {U : ℕ} (_V : ℕ) (s : Fin U → Option ℕ) (o : DynamicOp U)
    (regs : Fin 9957 → ℕ) : Prop :=
  match o with
  | .insert _ _ => True
  | .delete _ => True
  | .query u => decodeOptionRegs regs = s u

/-- Output-register correctness at the end of an operation sequence `ops : List (DynamicOp U)`
starting from abstract dictionary state `s : Fin U → Option ℕ`: if the last operation in `ops` is
`.query u`, then `decodeOptionRegs regs` equals the dictionary value `(runDict s init) u`
immediately before that query. -/
def SeqOutputCorrect {U : ℕ} (V : ℕ) :
    (Fin U → Option ℕ) → List (DynamicOp U) → (Fin 9957 → ℕ) → Prop
  | _, [], _ => True
  | s, [o], regs => OpOutputCorrect V s o regs
  | s, o₁ :: o₂ :: os, regs => SeqOutputCorrect V (stepDict s o₁) (o₂ :: os) regs

/-- **Any-Step Query Output Correctness (`seqOutputCorrect_append_singleton`):**
At any step `ops = init ++ [DynamicOp.query u]` whose final operation is `.query u`,
`SeqOutputCorrect V s (init ++ [DynamicOp.query u]) regs` is equivalent to
`decodeOptionRegs regs = (runDict s init) u`. -/
theorem seqOutputCorrect_append_singleton {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (init : List (DynamicOp U)) (u : Fin U) (regs : Fin 9957 → ℕ) :
    SeqOutputCorrect V s (init ++ [DynamicOp.query u]) regs ↔
      decodeOptionRegs regs = (runDict s init) u := by
  induction init generalizing s with
  | nil => rfl
  | cons o₁ os ih =>
    cases os with
    | nil => exact ih (stepDict s o₁)
    | cons o₂ rest => exact ih (stepDict s o₁)

/-- **Peak Epoch Capacity Bound (`maxEpochCap_empty_le_targetCap_length`):**
Starting from `(emptyDict U, 0)`, the maximum epoch capacity `maxEpochCap V (emptyDict U) 0 ops`
along `ops` never exceeds `targetCap U ops.length = min (2 * ops.length) U` (and is always `≤ U`).
In particular, machine word-size admissibility requires only that the peak epoch reached along
`ops` fits in `2 ^ w`, not `epochSpace U V w U < 2 ^ w`. -/
theorem maxEpochCap_empty_le_targetCap_length {U : ℕ} (V : ℕ) (ops : List (DynamicOp U)) :
    maxEpochCap V (emptyDict U) 0 ops ≤ targetCap U ops.length :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_maxEpochCap_empty_le_targetCap_length
    ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
      @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
      @SeqOutputCorrect, @activeEpochWords,
      RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => Iff.rfl⟩
    V ops

/-- **Word- to Bit-Space Conversion (`succinctWords_mul_w_le_bits`):**
Converting `succinctWords C₁ C₀ U V w n` words to bits adds at most `(C₀ + 1) * w` bits (`C₀ * w`
for the `C₀` constant words plus `w` bits from ceiling division). -/
theorem succinctWords_mul_w_le_bits (C₁ C₀ U V w n : ℕ) :
    w * succinctWords C₁ C₀ U V w n ≤
      optBits U V n + C₁ * n * logLogFactor n + (C₀ + 1) * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_succinctWords_mul_w_le_bits
    C₁ C₀ U V w n

/-- **Stepwise Tight Space Bound for `n ≤ N ≤ 2 * n` (`activeEpochWords_le_two_mul`):**
Immediately after an epoch rebuild (`n ≤ N ≤ 2 * n`), the active footprint is at most
`succinctWords 312 213 U V w n` words. -/
theorem activeEpochWords_le_two_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    activeEpochWords U V w N n ≤ succinctWords 312 213 U V w n :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_two_mul
    hw hnU hNU hU hnN hN2

/-- **Stepwise Tight Space Bound across a Full Epoch `n ≤ N ≤ 4 * n`
(`activeEpochWords_le_four_mul`):**
At every step `t` within a valid epoch (`EpochValid n N`, i.e., `n ≤ N ≤ 4 * n`), the active
footprint `activeEpochWords U V w N n` is at most `succinctWords 1227 213 U V w n` words, and its
bit footprint `w * activeEpochWords U V w N n` is at most
`optBits U V n + 1227 * n * logLogFactor n + 214 * w` bits (`214 * w` is the explicit additive bit
overhead of the word-granular model). -/
theorem activeEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    activeEpochWords U V w N n ≤ succinctWords 1227 213 U V w n ∧
    w * activeEpochWords U V w N n ≤
      optBits U V n + 1227 * n * logLogFactor n + 214 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_four_mul
    hw hnU hNU hU hnN hN4

private theorem activeEpochWords_le_epochSpace {U V w N n : ℕ} (hn : n ≤ N) :
    activeEpochWords U V w N n ≤ epochSpace U V w N := by
  unfold epochSpace activeEpochWords itemWords
  dsimp only
  have h1 := Nat.div_le_div_right (c := w)
    (Nat.sub_le_sub_right
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right
          (Nat.clog 2 U - (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4)))) hn) w) 1)
  have h2 := Nat.div_le_div_right (c := w)
    (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right (Nat.clog 2 V) hn) w) 1)
  omega

/-- Universal register count `9957` (`rSuccinct U V w N = 9957` for all `U, V, w, N`). -/
abbrev rResizable : ℕ := 9957

/-- Universal single-operation rebuild unit cost `53495843` (`rebuildUnitCost U V w = 53495843`
for all `U, V, w`). -/
abbrev rebuildUnitCostConst : ℕ := 53495843

/-- Universal per-operation expected amortized instruction charge `160486391`
(`resizableChargeVal U V w = 160486391` for all `U, V, w`). -/
abbrev resizableChargeValConst : ℕ := 160486391

/-- `2`-instruction resizable Word-RAM program (`RProgram r`) that contracts the physical frontier
by `Δ` words via `.shrink`: loads `Δ` into `r_cur` and executes `.shrink r_cur`. -/
def shrinkTailProgram {r : ℕ} (r_cur : Fin r) (Δ : ℕ) : RProgram r :=
  [.const r_cur Δ,
   .shrink r_cur]

/-- `3`-instruction resizable Word-RAM program (`RProgram r`) that deallocates an entire structure
at `regs[r_base]` via `.shrink`: queries `.size r_cur`, computes `r_tmp = frontier - base`, and
executes `.shrink r_tmp`. -/
def deallocProgram {r : ℕ} (r_base r_cur r_tmp : Fin r) : RProgram r :=
  [.size r_cur,
   .alu .sub r_tmp r_cur r_base,
   .shrink r_tmp]

private theorem shrinkTailProgram_exec {r w : ℕ} (r_cur : Fin r) (Δ : ℕ) (x : RState r)
    (hΔ_lt : Δ < 2 ^ w) (hΔ_le : Δ ≤ x.frontier) :
    ExecRProgramDemonic w (shrinkTailProgram r_cur Δ) x
      ⟨Function.update x.regs r_cur Δ,
        shrinkMem x.mem (x.frontier - Δ) Δ,
        x.frontier - Δ⟩ 2 := by
  let x₁ : RState r := ⟨Function.update x.regs r_cur Δ, x.mem, x.frontier⟩
  let x₂ : RState r :=
    ⟨x₁.regs, shrinkMem x.mem (x.frontier - Δ) Δ, x.frontier - Δ⟩
  refine execRProgramCfg_step_eq (cfg₁ := .running 1 x₁) (fun cfg' => ?_) ?_
  · simp [stepDemonicRel, shrinkTailProgram, hΔ_lt, x₁]
  · refine execRProgramCfg_step_eq (cfg₁ := .running 2 x₂) (fun cfg' => ?_)
      (ExecRProgramCfg.refl _ _ rfl)
    simp [stepDemonicRel, shrinkTailProgram, x₁, x₂, hΔ_le]

private theorem deallocProgram_exec {r w base : ℕ} (r_base r_cur r_tmp : Fin r) (x : RState r)
    (hne : r_base ≠ r_cur) (hfr_lt : x.frontier < 2 ^ w)
    (hr_base : x.regs r_base = base) (hle : base ≤ x.frontier) :
    ExecRProgramDemonic w (deallocProgram r_base r_cur r_tmp) x
      ⟨Function.update (Function.update x.regs r_cur x.frontier) r_tmp (x.frontier - base),
        shrinkMem x.mem base (x.frontier - base),
        base⟩ 3 := by
  let z₁ : RState r := ⟨Function.update x.regs r_cur x.frontier, x.mem, x.frontier⟩
  let z₂ : RState r := ⟨Function.update z₁.regs r_tmp (x.frontier - base), x.mem, x.frontier⟩
  let z₃ : RState r := ⟨z₂.regs, shrinkMem x.mem base (x.frontier - base), base⟩
  have hsub_lt : x.frontier - base < 2 ^ w := lt_of_le_of_lt (Nat.sub_le _ _) hfr_lt
  have hsub_le : x.frontier - base ≤ x.frontier := Nat.sub_le _ _
  have hfr_sub : x.frontier - (x.frontier - base) = base := by omega
  refine execRProgramCfg_step_eq (cfg₁ := .running 1 z₁) (fun cfg' => ?_) ?_
  · simp [stepDemonicRel, deallocProgram, hfr_lt, z₁]
  · refine execRProgramCfg_step_eq (cfg₁ := .running 2 z₂) (fun cfg' => ?_) ?_
    · simp only [stepDemonicRel, deallocProgram, List.getElem?_cons_succ, List.getElem?_cons_zero,
        AluOp.eval, z₁, z₂]
      rw [Function.update_of_ne hne, hr_base, Function.update_self]
      simp [hle, hsub_lt]
    · refine execRProgramCfg_step_eq (cfg₁ := .running 3 z₃) (fun cfg' => ?_)
        (ExecRProgramCfg.refl _ _ rfl)
      simp only [stepDemonicRel, deallocProgram, List.getElem?_cons_succ, List.getElem?_cons_zero,
        z₂, z₃]
      rw [Function.update_self]
      simp [hsub_le, hfr_sub]

private theorem rBounded_shrinkTail {r w : ℕ} (r_cur : Fin r) (Δ : ℕ) {x : RState r}
    (hx : RBounded w x) (hΔ_lt : Δ < 2 ^ w) :
    RBounded w
      ⟨Function.update x.regs r_cur Δ,
        shrinkMem x.mem (x.frontier - Δ) Δ,
        x.frontier - Δ⟩ := by
  refine ⟨⟨fun i => ?_, fun a => ?_⟩, lt_of_le_of_lt (Nat.sub_le _ _) hx.2.1, fun a ha => ?_⟩
  · dsimp only
    by_cases hi : i = r_cur
    · subst hi; simp [hΔ_lt]
    · simp [hi, hx.1.1 i]
  · dsimp only [shrinkMem]
    split_ifs
    · exact Nat.two_pow_pos w
    · exact hx.1.2 a
  · dsimp only [shrinkMem] at ha ⊢
    split_ifs with h
    · rfl
    · exact hx.2.2 a (by omega)

private theorem rBounded_dealloc {r w base : ℕ} (r_cur r_tmp : Fin r) {x : RState r}
    (hx : RBounded w x) (hle : base ≤ x.frontier) :
    RBounded w
      ⟨Function.update (Function.update x.regs r_cur x.frontier) r_tmp (x.frontier - base),
        shrinkMem x.mem base (x.frontier - base),
        base⟩ := by
  refine ⟨⟨fun i => ?_, fun a => ?_⟩, lt_of_le_of_lt hle hx.2.1, fun a ha => ?_⟩
  · dsimp only
    by_cases hi2 : i = r_tmp
    · subst hi2
      simp only [Function.update_self]
      exact lt_of_le_of_lt (Nat.sub_le _ _) hx.2.1
    · rw [Function.update_of_ne hi2]
      by_cases hi1 : i = r_cur
      · subst hi1
        simp only [Function.update_self]
        exact hx.2.1
      · rw [Function.update_of_ne hi1]
        exact hx.1.1 i
  · dsimp only [shrinkMem]
    split_ifs
    · exact Nat.two_pow_pos w
    · exact hx.1.2 a
  · dsimp only [shrinkMem] at ha ⊢
    split_ifs with h
    · rfl
    · exact hx.2.2 a (by omega)

private def r0Resizable : Fin rResizable := ⟨0, by decide⟩
private def r1Resizable : Fin rResizable := ⟨1, by decide⟩
private def r2Resizable : Fin rResizable := ⟨2, by decide⟩
private theorem r0_ne_r1 : r0Resizable ≠ r1Resizable := by decide

private theorem shrinkTail_delta_le {fr base ep act : ℕ} (hfr : fr = base + ep) :
    ep - act ≤ fr := by omega

private theorem shrinkTail_frontier_eq {fr base ep act : ℕ}
    (hfr : fr = base + ep) (hle : act ≤ ep) :
    fr - (ep - act) = base + act := by omega

private theorem shrinkTail_preserve_lt {mem mem₀ : ℕ → ℕ} {fr base ep act : ℕ}
    (hfr : fr = base + ep) (hmem : ∀ a < base, mem a = mem₀ a) :
    ∀ a < base, shrinkMem mem (fr - (ep - act)) (ep - act) a = mem₀ a := by
  intro a ha
  dsimp only [shrinkMem]
  split_ifs with h
  · omega
  · exact hmem a ha

private theorem dealloc_preserve_lt {mem mem₀ : ℕ → ℕ} {fr base : ℕ}
    (hmem : ∀ a < base, mem a = mem₀ a) :
    ∀ a < base, shrinkMem mem base (fr - base) a = mem₀ a := by
  intro a ha
  dsimp only [shrinkMem]
  split_ifs with h
  · omega
  · exact hmem a ha

private theorem seqOutputCorrect_shrinkTail {U V : ℕ} (ops : List (DynamicOp U))
    (x : RState rResizable) (Δ : ℕ)
    (hout : SeqOutputCorrect V (emptyDict U) ops x.regs) :
    SeqOutputCorrect V (emptyDict U) ops (Function.update x.regs r1Resizable Δ) := by
  have hdec :
      decodeOptionRegs (Function.update x.regs r1Resizable Δ) = decodeOptionRegs x.regs := by
    have h252 : ∀ (h : 252 < rResizable),
        Function.update x.regs r1Resizable Δ ⟨252, h⟩ = x.regs ⟨252, h⟩ :=
      fun h => Function.update_of_ne
        (fun heq : (⟨252, h⟩ : Fin rResizable) = r1Resizable =>
          nomatch (congrArg Fin.val heq : 252 = 1))
        Δ x.regs
    have h253 : ∀ (h : 253 < rResizable),
        Function.update x.regs r1Resizable Δ ⟨253, h⟩ = x.regs ⟨253, h⟩ :=
      fun h => Function.update_of_ne
        (fun heq : (⟨253, h⟩ : Fin rResizable) = r1Resizable =>
          nomatch (congrArg Fin.val heq : 253 = 1))
        Δ x.regs
    simp only [decodeOptionRegs, h252, h253]
  have hcongr : ∀ {s : Fin U → Option ℕ} (l : List (DynamicOp U)),
      SeqOutputCorrect V s l (Function.update x.regs r1Resizable Δ) ↔
        SeqOutputCorrect V s l x.regs := by
    intro s l
    induction l generalizing s with
    | nil => rfl
    | cons o os ih =>
      cases os with
      | nil =>
        cases o with
        | insert _ _ => rfl
        | delete _ => rfl
        | query _ =>
          simp only [SeqOutputCorrect, OpOutputCorrect, hdec]
      | cons _ _ => exact ih
  exact (hcongr ops).mpr hout

/-- **Stage 2 Headline Theorem — Unbounded-Capacity Resizable Succinct Dictionary
(`unbounded_seq_expected_amortized`):**
There exist **universal `O(1)` constants** `r = rResizable = 9957`,
`rebuildUnitCost = rebuildUnitCostConst = 53495843`,
`resizableChargeVal = resizableChargeValConst = 160486391`, `C_space = 1227`, and `C_word = 213`
(quantified **outside** `∀ U V w base`) such that for every key universe `U`, value range `V`, word
width `w`, and base address `base` with `0 < w`, `U < 2 ^ w`, `V < 2 ^ w`, every initial caller
machine state `x₀ : RState r` with `RBounded w x₀` and `x₀.frontier = base`, and **any** valid
operation sequence `ops : List (DynamicOp U)` (`insert`, `delete`, `query`) from `emptyDict U` under
`ValidDictSeq V` (**with no capacity cap**) whose peak reached epoch capacity
`maxEpochCap V (emptyDict U) 0 ops` (`≤ min (2 * ops.length) U`) fits in `2 ^ w`, at the resulting
state `s_final = runDict (emptyDict U) ops` with current live key count
`n_final = (dictDom s_final).card` and active epoch capacity
`N_final = targetCap U (runEpochInit V (emptyDict U) 0 ops)` (and by prefix induction at every
intermediate step `t`):
1. **Epoch & value invariants:** `EpochValid n_final N_final` (`n_final ≤ N_final ≤ 4 * n_final`),
   `N_final ≤ U`, and every stored value is `< V`;
2. **Stepwise `n_t`-tight space in words and bits:**
   `activeEpochWords U V w N_final n_final ≤ succinctWords C_space C_word U V w n_final`, and in
   bits `w * activeEpochWords U V w N_final n_final ≤`
   `optBits U V n_final + C_space * n_final * logLogFactor n_final + (C_word + 1) * w`
   (with explicit word-alignment additive term `(C_word + 1) * w = 214 * w` bits);
3. **Coupled machine-state `O(1)` expected amortized time, query output correctness, & physical
   frontier contraction:**
   there exist a final machine-state distribution `ν_final : PMF (RState r)`, cumulative expected
   operation and rebuild instruction time `T_ops : ℝ≥0∞`, and expected slot potential `E_pot : ℝ≥0∞`
   satisfying
   `T_ops + E_pot + 2 * rebuildUnitCost * |n_final - n_init_final| ≤`
   `ops.length * resizableChargeVal`,
   where every `x_epoch ∈ ν_final.support` satisfies `RBounded w x_epoch`,
   `x_epoch.frontier = base + epochSpace U V w N_final`, `x_epoch.regs ⟨0, _⟩ = base`,
   `SeqOutputCorrect V (emptyDict U) ops x_epoch.regs` (so if the last operation in `ops` is
   `.query u`, `decodeOptionRegs x_epoch.regs` decodes the queried value `(runDict ... init) u`),
   preserves all caller memory `< base`, and contracts in `2` instructions via
   `ExecRProgramDemonic w (shrinkTailProgram ...)` to a resting machine state `x_rest : RState r`
   that preserves `SeqOutputCorrect V (emptyDict U) ops x_rest.regs` and whose physical frontier
   `x_rest.frontier` satisfies
   `x_rest.frontier = base + activeEpochWords U V w N_final n_final`,
   `x_rest.frontier - base ≤ succinctWords C_space C_word U V w n_final`, and
   `w * (x_rest.frontier - base) ≤`
   `optBits U V n_final + C_space * n_final * logLogFactor n_final + (C_word + 1) * w`
   (and when `n_final = 0`, contracts in `3` instructions via
   `ExecRProgramDemonic w (deallocProgram ...)` to `x_zero : RState r` with
   `x_zero.frontier = base`). -/
theorem unbounded_seq_expected_amortized :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ),
      r = rResizable ∧
      rebuildUnitCost = rebuildUnitCostConst ∧
      resizableChargeVal = resizableChargeValConst ∧
      C_space = 1227 ∧
      C_word = 213 ∧
      ∀ (U V w base : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        ∀ (x₀ : RState rResizable),
          RBounded w x₀ →
          x₀.frontier = base →
          ∀ ops : List (DynamicOp U),
            (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochSpace U V w N < 2 ^ w) →
            ValidDictSeq V (emptyDict U) ops →
            let s_final := runDict (emptyDict U) ops
            let n_final := (dictDom s_final).card
            let n_init_final := runEpochInit V (emptyDict U) 0 ops
            let N_final := targetCap U n_init_final
            EpochValid n_final N_final ∧
            N_final ≤ U ∧
            (∀ u v, s_final u = some v → v < V) ∧
            activeEpochWords U V w N_final n_final ≤
              succinctWords C_space C_word U V w n_final ∧
            w * activeEpochWords U V w N_final n_final ≤
              optBits U V n_final + C_space * n_final * logLogFactor n_final +
                (C_word + 1) * w ∧
            2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
              ops.length * resizableChargeVal ∧
            ∃ (ν_final : PMF (RState rResizable)) (T_ops E_pot : ℝ≥0∞),
              T_ops + E_pot +
                ((2 * rebuildUnitCost *
                  ((n_final - n_init_final) + (n_init_final - n_final)) : ℕ) : ℝ≥0∞) ≤
                ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) ∧
              ∀ x_epoch ∈ ν_final.support,
                RBounded w x_epoch ∧
                x_epoch.frontier = base + epochSpace U V w N_final ∧
                x_epoch.regs ⟨0, by decide⟩ = base ∧
                SeqOutputCorrect V (emptyDict U) ops x_epoch.regs ∧
                (∀ a < base, x_epoch.mem a = x₀.mem a) ∧
                ∃ x_rest : RState rResizable,
                  ExecRProgramDemonic w
                    (shrinkTailProgram ⟨1, by decide⟩
                      (epochSpace U V w N_final - activeEpochWords U V w N_final n_final))
                    x_epoch x_rest 2 ∧
                  RBounded w x_rest ∧
                  x_rest.frontier = base + activeEpochWords U V w N_final n_final ∧
                  x_rest.frontier - base ≤ succinctWords C_space C_word U V w n_final ∧
                  w * (x_rest.frontier - base) ≤
                    optBits U V n_final + C_space * n_final * logLogFactor n_final +
                      (C_word + 1) * w ∧
                  SeqOutputCorrect V (emptyDict U) ops x_rest.regs ∧
                  (∀ a < base, x_rest.mem a = x₀.mem a) ∧
                  (n_final = 0 →
                    ∃ x_zero : RState rResizable,
                      ExecRProgramDemonic w
                        (deallocProgram ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩)
                        x_epoch x_zero 3 ∧
                      RBounded w x_zero ∧
                      x_zero.frontier = base ∧
                      ∀ a < base, x_zero.mem a = x₀.mem a) := by
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_unbounded_seq_expected_amortized
      ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
        @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
        @SeqOutputCorrect, @activeEpochWords,
        RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
        fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ => Iff.rfl⟩
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict
  ] at hbridge
  refine ⟨rResizable, rebuildUnitCostConst, resizableChargeValConst, 1227, 213,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  have hmain := hbridge U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  clear hbridge
  dsimp only at hmain ⊢
  obtain ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, hsupp⟩ := hmain
  refine ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, ?_⟩
  intro x_epoch hx_epoch
  obtain ⟨hbdd_ep, hfr_ep, hreg0_ep, hout_ep, hmem_ep,
    _, _, hfr_rest, hwords_rest, hbits_rest, _, _, _⟩ :=
    hsupp x_epoch hx_epoch
  clear hsupp
  let s_final := runDict (emptyDict U) ops
  let n_final := (dictDom s_final).card
  let n_init_final := runEpochInit V (emptyDict U) 0 ops
  let N_final := targetCap U n_init_final
  let Δ := epochSpace U V w N_final - activeEpochWords U V w N_final n_final
  have hle_ep : activeEpochWords U V w N_final n_final ≤ epochSpace U V w N_final :=
    activeEpochWords_le_epochSpace hepoch.1
  have hfr_ep' : x_epoch.frontier = base + epochSpace U V w N_final := hfr_ep
  have hΔ_le : Δ ≤ x_epoch.frontier := shrinkTail_delta_le hfr_ep'
  have hΔ_lt : Δ < 2 ^ w := lt_of_le_of_lt hΔ_le hbdd_ep.2.1
  let x_rest' : RState rResizable :=
    ⟨Function.update x_epoch.regs r1Resizable Δ,
      shrinkMem x_epoch.mem (x_epoch.frontier - Δ) Δ,
      x_epoch.frontier - Δ⟩
  have hexec_sh : ExecRProgramDemonic w (shrinkTailProgram r1Resizable Δ) x_epoch x_rest' 2 :=
    shrinkTailProgram_exec r1Resizable Δ x_epoch hΔ_lt hΔ_le
  have hbdd_rest' : RBounded w x_rest' :=
    rBounded_shrinkTail r1Resizable Δ hbdd_ep hΔ_lt
  have hfr_rest' : x_rest'.frontier = base + activeEpochWords U V w N_final n_final :=
    shrinkTail_frontier_eq hfr_ep' hle_ep
  have hout_rest' : SeqOutputCorrect V (emptyDict U) ops x_rest'.regs :=
    seqOutputCorrect_shrinkTail ops x_epoch Δ hout_ep
  refine ⟨hbdd_ep, hfr_ep, hreg0_ep, hout_ep, hmem_ep,
    x_rest', hexec_sh, hbdd_rest', hfr_rest', ?_, ?_, hout_rest',
    shrinkTail_preserve_lt hfr_ep' hmem_ep, ?_⟩
  · rw [hfr_rest']
    rw [hfr_rest] at hwords_rest
    exact hwords_rest
  · rw [hfr_rest']
    rw [hfr_rest] at hbits_rest
    exact hbits_rest
  · intro _
    let x_zero' : RState rResizable :=
      ⟨Function.update (Function.update x_epoch.regs r1Resizable x_epoch.frontier)
        r2Resizable (x_epoch.frontier - base),
        shrinkMem x_epoch.mem base (x_epoch.frontier - base),
        base⟩
    have hbase_le_fr : base ≤ x_epoch.frontier := hfr_ep' ▸ Nat.le_add_right base _
    have hexec_de :
        ExecRProgramDemonic w (deallocProgram r0Resizable r1Resizable r2Resizable)
          x_epoch x_zero' 3 :=
      deallocProgram_exec r0Resizable r1Resizable r2Resizable x_epoch
        r0_ne_r1 hbdd_ep.2.1 hreg0_ep hbase_le_fr
    have hbdd_zero' : RBounded w x_zero' :=
      rBounded_dealloc r1Resizable r2Resizable hbdd_ep hbase_le_fr
    exact ⟨x_zero', hexec_de, hbdd_zero', rfl, dealloc_preserve_lt hmem_ep⟩

/-- **Stage 2 Client Subroutine & Memory-Reuse Theorem (`dictionary_client_memory_reuse`):**
With the universal register count `r = rResizable = 9957` quantified **outside** `(U, V, w)`, for
every `U, V, w` with `0 < w`, `U < 2 ^ w`, and `V < 2 ^ w`, on the `r`-register word-granular
resizable Word-RAM (`RState r`):
1. **In-place tail contraction and reuse (`shrink_and_reuse_in_place`):** When deletions reduce the
   dictionary's active item footprint at `[base, base + sp₂ + Δ)` by `Δ` words to `base + sp₂`,
   executing `shrinkTailProgram` (`2` instructions via `ExecRProgramDemonic`) followed by a client's
   `4 * k_client + 8`-instruction demonic `.grow` + zero-fill allocation places the client's new
   block at `[base + sp₂, base + sp₂ + k_client)`—**reusing the `Δ` released words**—while
   preserving the dictionary's live prefix `[0, base + sp₂)` unchanged.
2. **Full subroutine lifecycle and address reuse (`subroutine_client_reuse_released_memory`):**
   Starting from any caller state `x₀` with `x₀.frontier = base`, executing any valid dictionary
   operation sequence `ops : List (DynamicOp U)` whose peak epoch capacity
   `maxEpochCap V (emptyDict U) 0 ops` (`≤ min (2 * ops.length) U`) fits in `2 ^ w`, deallocating
   the dictionary via `deallocProgram` (`3` instructions via `ExecRProgramDemonic`, returning
   `frontier` to `base`), and allocating `k_client` words for a subsequent client under demonic
   `DemonicGrow` (`4 * k_client + 8` instructions) produces a final state `x_reused` with
   `x_reused.frontier = base + k_client` (**reusing `[base, base + k_client)` instead of
   `[base + epochSpace U V w N_final, ...)`**), zeroed client memory `[base, base + k_client)`, and
   intact caller prefix `[0, base)`. -/
theorem dictionary_client_memory_reuse :
    ∃ r : ℕ,
      r = rResizable ∧
      ∀ (U V w : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ (base sp₂ Δ k_client : ℕ) (x : RState rResizable),
          RBounded w x →
          x.frontier = base + sp₂ + Δ →
          1 < 2 ^ w →
          base + sp₂ + k_client < 2 ^ w →
          ∃ x_shrunk x_reused : RState rResizable,
            ExecRProgramDemonic w (shrinkTailProgram ⟨1, by decide⟩ Δ) x x_shrunk 2 ∧
            RBounded w x_shrunk ∧
            x_shrunk.frontier = base + sp₂ ∧
            RBounded w x_reused ∧
            x_reused.frontier = base + sp₂ + k_client ∧
            (∀ a < base + sp₂, x_reused.mem a = x.mem a) ∧
            (∀ a, base + sp₂ ≤ a → a < base + sp₂ + k_client → x_reused.mem a = 0)) ∧
        (∀ (base k_client : ℕ) (x₀ : RState rResizable) (ops : List (DynamicOp U)),
          (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochSpace U V w N < 2 ^ w) →
          base + k_client < 2 ^ w →
          RBounded w x₀ →
          x₀.frontier = base →
          ValidDictSeq V (emptyDict U) ops →
          let N_final := targetCap U (runEpochInit V (emptyDict U) 0 ops)
          ∃ x_dict x_dealloc x_reused : RState rResizable,
            RBounded w x_dict ∧
            x_dict.frontier = base + epochSpace U V w N_final ∧
            x_dict.regs ⟨0, by decide⟩ = base ∧
            SeqOutputCorrect V (emptyDict U) ops x_dict.regs ∧
            (∀ a < base, x_dict.mem a = x₀.mem a) ∧
            ExecRProgramDemonic w
              (deallocProgram ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩)
              x_dict x_dealloc 3 ∧
            RBounded w x_dealloc ∧
            x_dealloc.frontier = base ∧
            RBounded w x_reused ∧
            x_reused.frontier = base + k_client ∧
            (∀ a < base, x_reused.mem a = x₀.mem a) ∧
            (∀ a, base ≤ a → a < base + k_client → x_reused.mem a = 0)) := by
  obtain ⟨_, rfl, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_dictionary_client_memory_reuse
      ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
        @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
        @SeqOutputCorrect, @activeEpochWords,
        RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
        fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ => Iff.rfl⟩
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict
  ] at hbridge
  refine ⟨rResizable, rfl, fun U V w hw hU hV => ?_⟩
  obtain ⟨hpart1, hpart2⟩ := hbridge U V w hw hU hV
  clear hbridge
  refine ⟨?_, ?_⟩
  · clear hpart2
    intro base sp₂ Δ k_client x hx hfr h1 hfit_client
    obtain ⟨_, x_reused, _, _, hre_bdd, hre_fr, hre_pre, hre_zero⟩ :=
      hpart1 base sp₂ Δ k_client x hx hfr h1 hfit_client
    clear hpart1
    let x_shrunk' : RState rResizable :=
      ⟨Function.update x.regs r1Resizable Δ,
        shrinkMem x.mem (x.frontier - Δ) Δ,
        x.frontier - Δ⟩
    have hfr' : x.frontier = base + sp₂ + Δ := hfr
    have hΔ_le : Δ ≤ x.frontier := hfr' ▸ Nat.le_add_left Δ (base + sp₂)
    have hΔ_lt : Δ < 2 ^ w := lt_of_le_of_lt hΔ_le hx.2.1
    have hexec_sh : ExecRProgramDemonic w (shrinkTailProgram r1Resizable Δ) x x_shrunk' 2 :=
      shrinkTailProgram_exec r1Resizable Δ x hΔ_lt hΔ_le
    have hbdd_sh' : RBounded w x_shrunk' :=
      rBounded_shrinkTail r1Resizable Δ hx hΔ_lt
    have hfr_sh' : x_shrunk'.frontier = base + sp₂ :=
      (congrArg (· - Δ) hfr').trans (Nat.add_sub_cancel (base + sp₂) Δ)
    exact ⟨x_shrunk', x_reused, hexec_sh, hbdd_sh', hfr_sh', hre_bdd, hre_fr, hre_pre, hre_zero⟩
  · clear hpart1
    intro base k_client x₀ ops hfit hfit_client hx₀ hfr₀ hv
    obtain ⟨x_dict, _, x_reused, hdict_bdd, hdict_fr, hdict_r0, hdict_out, hdict_pre,
      _, _, hre_bdd, hre_fr, hre_pre, hre_zero⟩ :=
      hpart2 base k_client x₀ ops hfit hfit_client hx₀ hfr₀ hv
    clear hpart2
    let x_dealloc' : RState rResizable :=
      ⟨Function.update (Function.update x_dict.regs r1Resizable x_dict.frontier)
        r2Resizable (x_dict.frontier - base),
        shrinkMem x_dict.mem base (x_dict.frontier - base),
        base⟩
    have hdict_fr' :
        x_dict.frontier =
          base + epochSpace U V w (targetCap U (runEpochInit V (emptyDict U) 0 ops)) := hdict_fr
    have hbase_le_fr : base ≤ x_dict.frontier := hdict_fr' ▸ Nat.le_add_right base _
    have hexec_de :
        ExecRProgramDemonic w (deallocProgram r0Resizable r1Resizable r2Resizable)
          x_dict x_dealloc' 3 :=
      deallocProgram_exec r0Resizable r1Resizable r2Resizable x_dict
        r0_ne_r1 hdict_bdd.2.1 hdict_r0 hbase_le_fr
    have hbdd_de' : RBounded w x_dealloc' :=
      rBounded_dealloc r1Resizable r2Resizable hdict_bdd hbase_le_fr
    exact ⟨x_dict, x_dealloc', x_reused,
      hdict_bdd, hdict_fr, hdict_r0, hdict_out, hdict_pre,
      hexec_de, hbdd_de', rfl,
      hre_bdd, hre_fr, hre_pre, hre_zero⟩

end ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

/--
info: abstract audit passed for `ComplexityAbstracts.ResizableSuccinctDictionaryAbstract`: 352 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.ResizableSuccinctDictionaryAbstract
