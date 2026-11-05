/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (self-contained formal abstract for headline theorems)

import ComplexityAbstracts.Check
import ComplexityAbstracts.ResizableSuccinctDictionaryBridge
import Cslib.Probability.PMF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log

/-!
# Self-Contained Formal Abstract: Dynamic Succinct Dictionary on a Resizable Word RAM

Self-contained specification of the **Dynamic Succinct Dictionary** on a **word-granular Resizable
Word-RAM** (`RInstr r`, `RProgram r`) with `w`-bit words, explicit allocation frontier
`frontier : ℕ`, primitive `.grow` / `.shrink` instructions, adversarial (demonic) dirty-word
initialization on `.grow`, and uniform random sampling `.rand`.

1. **Concrete Resizable Word-RAM Machine Model (`RState`, `RInstr`, `RProgram`, `execRProgram`)**:
   Machine states `RState r` (`regs`, `mem`, `frontier`), instruction semantics (`stepDemonicRel`,
   `stepRandDemonic`), and fault-free execution under adversarial `.grow` (`DemonicGrow`).
2. **Uniform Compiled Execution (`resizableSuccinctDynamicDictionary`)**:
   Universal constants `∃ (r C_init C_op C_space C_word : ℕ) (hr : 256 ≤ r)` quantified **outside**
   `∀ (U V w : ℕ)`, and compiled uniform programs `∃ (p_init p_op : RProgram r)` quantified
   **ahead of** `∀ (base : ℕ)`, `∀ x₀`, and `∀ (ops : List (DynamicOp U))`, maintaining live
   `[0, n_t)` word compaction `x_t.frontier = base + compactedEpochWords U V w N_t n_t`.
3. **Coupled Epoch-Rebuild & Client Reuse (`unbounded_seq_expected_amortized`,
   `dictionary_client_memory_reuse`)**:
   Machine-level bucket/slot-scanning epoch rebuilds and immediate client reuse of
   `.shrink`-released word addresses under `DemonicGrow`.
-/

namespace ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

open scoped ENNReal BigOperators

/-! ## Part 1: Word-Granular Resizable Word-RAM Machine Model (`RInstr`, `RProgram`, `RState`) -/

/-- Standard Word-RAM ALU binary operations on `w`-bit words. -/
inductive AluOp : Type where
  | add | sub | mul | div | mod
  | and | or | xor | shl | shr
  deriving DecidableEq, Repr

/-- Semantics of an `AluOp` on natural-number word values (`div`/`mod` return `none` on `0`). -/
def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a / b)
  | .mod, a, b => if b = 0 then none else some (a % b)
  | .and, a, b => some (Nat.land a b)
  | .or,  a, b => some (Nat.lor a b)
  | .xor, a, b => some (Nat.xor a b)
  | .shl, a, b => some (a <<< b)
  | .shr, a, b => some (a >>> b)

/-- Concrete instruction set `RInstr r` of an `r`-register word-granular Resizable Word-RAM:
- standard Word-RAM instructions (`.const`, `.copy`, `.alu`, `.width`, `.load`, `.store`,
  `.jump`, `.branchEq`, `.branchLt`, `.halt`, `.rand`);
- resizable frontier primitives `.size d` (reads `frontier` into `d`), `.grow k` (advances
  `frontier` by `regs[k]` words with adversarial dirty-word initialization), and `.shrink k`
  (contracts `frontier` by `regs[k]` words, clearing released words to `0`). -/
inductive RInstr (r : ℕ) : Type where
  | const (d : Fin r) (v : ℕ)
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

/-- A concrete resizable Word-RAM program is a flat list of `RInstr r` instructions. -/
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

/-- Adversarial growth memory `advGrowMem w s delta adv mem`: fills `[s, s + delta)` with
`adv a % 2 ^ w` for any adversary function `adv : ℕ → ℕ`. Every `mem'` satisfying
`DemonicGrow w s delta mem mem'` equals `advGrowMem w s delta mem' mem` when `0 < w`. -/
def advGrowMem (w s delta : ℕ) (adv mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  if s ≤ a ∧ a < s + delta then adv a % (2 ^ w) else mem a

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

/-- Finite-depth randomized computation tree whose `.sample n` nodes draw uniformly from
`Fin (n + 1)`. -/
inductive Comp (α : Type) : Type
  | pure (a : α)
  | sample (n : ℕ) (next : Fin (n + 1) → Comp α)

/-- Sequential composition of sampling trees. -/
def Comp.bind {α β : Type} : Comp α → (α → Comp β) → Comp β
  | .pure a, f => f a
  | .sample n next, f => .sample n fun k => (next k).bind f

/-- Probability distribution induced by answering every `sample n` uniformly on `Fin (n + 1)`. -/
noncomputable def Comp.eval {α : Type} : Comp α → PMF α
  | .pure a => PMF.pure a
  | .sample n next =>
    (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k =>
      (next k).eval

/-- Single-step randomized + demonic transition of a resizable Word-RAM program `p : RProgram r`
at word width `w` under adversarial growth oracle `adv : ℕ → ℕ`:
- `.load d a` and `.store a i` require `x.regs a < x.frontier` (faulting on out-of-bounds access);
- `.size d` loads `x.frontier` into `d` when `x.frontier < 2 ^ w`;
- `.grow k` advances `x.frontier` by `delta = x.regs k` and fills `[x.frontier, x.frontier + delta)`
  with adversarial words `advGrowMem w x.frontier delta adv x.mem` when
  `x.frontier + delta < 2 ^ w`;
- `.shrink k` contracts `x.frontier` by `delta = x.regs k` via `shrinkMem` when
  `delta ≤ x.frontier`;
- `.rand d i` samples uniformly from `Fin (x.regs i + 1)` when `x.regs i < 2 ^ w`. -/
def stepRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) : RCfg r → Comp (RCfg r)
  | .halted v x => .pure (.halted v x)
  | .faulted => .pure .faulted
  | .running pc x =>
    let setReg (d : Fin r) (val : ℕ) : Comp (RCfg r) :=
      if val < 2 ^ w then .pure (.running (pc + 1) { x with regs := Function.update x.regs d val })
      else .pure .faulted
    match p[pc]? with
    | none => .pure .faulted
    | some (.const d v) => setReg d v
    | some (.copy d i) => setReg d (x.regs i)
    | some (.alu f d i j) =>
      match f.eval (x.regs i) (x.regs j) with
      | some v => setReg d v
      | none => .pure .faulted
    | some (.width d) => setReg d w
    | some (.load d a) =>
      if x.regs a < x.frontier then setReg d (x.mem (x.regs a)) else .pure .faulted
    | some (.store a i) =>
      if x.regs a < x.frontier ∧ x.regs i < 2 ^ w then
        .pure (.running (pc + 1) { x with mem := Function.update x.mem (x.regs a) (x.regs i) })
      else .pure .faulted
    | some (.size d) => setReg d x.frontier
    | some (.grow k) =>
      let delta := x.regs k
      if x.frontier + delta < 2 ^ w then
        .pure (.running (pc + 1)
          ⟨x.regs, advGrowMem w x.frontier delta adv x.mem, x.frontier + delta⟩)
      else .pure .faulted
    | some (.shrink k) =>
      let delta := x.regs k
      if delta ≤ x.frontier then
        .pure (.running (pc + 1)
          ⟨x.regs, shrinkMem x.mem (x.frontier - delta) delta, x.frontier - delta⟩)
      else .pure .faulted
    | some (.jump t) => .pure (.running t x)
    | some (.branchEq i j t) =>
      .pure (.running (if x.regs i = x.regs j then t else pc + 1) x)
    | some (.branchLt i j t) =>
      .pure (.running (if x.regs i < x.regs j then t else pc + 1) x)
    | some (.halt i) => .pure (.halted (x.regs i) x)
    | some (.rand d i) =>
      if x.regs i < 2 ^ w then
        .sample (x.regs i) fun k => setReg d k.val
      else .pure .faulted

/-- Clocked `T`-step randomized + demonic sampling tree from configuration `cfg` under adversarial
growth oracle `adv : ℕ → ℕ`. -/
def runRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) :
    ℕ → RCfg r → Comp (RCfg r)
  | 0, cfg => .pure cfg
  | T + 1, cfg => (stepRandDemonic w adv p cfg).bind (runRandDemonic w adv p T)

/-- Distribution over configurations after `T` steps starting from `.running 0 x` under adversarial
growth oracle `adv : ℕ → ℕ`. -/
noncomputable def evalRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) (T : ℕ)
    (x : RState r) : PMF (RCfg r) :=
  (runRandDemonic w adv p T (.running 0 x)).eval

/-- Expected number of executed instructions from `.running 0 x` under adversarial growth oracle
`adv : ℕ → ℕ`, as the sum over all time horizons `t` of the probability of still running. -/
noncomputable def expectedTimeDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r)
    (x : RState r) : ℝ≥0∞ :=
  ∑' t : ℕ,
    (evalRandDemonic w adv p t x).toOuterMeasure {cfg | ∃ pc y, cfg = .running pc y}

/-- Universal fault-freedom across all time horizons `T` and all adversarial growth oracles
`adv : ℕ → ℕ`. -/
def RandFaultFreeDemonic {r : ℕ} (w : ℕ) (p : RProgram r) (x : RState r) : Prop :=
  ∀ (adv : ℕ → ℕ) (T : ℕ), evalRandDemonic w adv p T x .faulted = 0

/-- Single-step demonic transition relation `stepDemonicRel w p cfg cfg'` of a resizable Word-RAM
program `p : RProgram r` at word width `w`. -/
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

/-! ## Part 2: Stage 1 — Resizable Bit-Packed Array of `b`-Bit Items (`b ≤ w`) -/

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

/-! ## Part 3: Stage 2 — Unbounded-Capacity Resizable Succinct Dictionary -/

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

/-- Total active word footprint `metaWords U w N + itemWords U V w N n` of the uncompacted epoch
layout at current live key count `n` within epoch capacity `N`. -/
def activeEpochWords (U V w N n : ℕ) : ℕ :=
  metaWords U w N + itemWords U V w N n

/-- Full epoch word footprint `activeEpochWords U V w N N` when `n = N`. -/
def epochSpace (U V w N : ℕ) : ℕ :=
  activeEpochWords U V w N N

/-- Word offset `offCompItems U w N` where the compacted active `(quotient, value)` region begins:
immediately after the `164`-word epoch header, `metaWords U w N`, and the forward/reverse
compaction permutation tables `TailToDense` and `DenseToTail`. -/
def offCompItems (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let slab_bits := if b_bits = 0 then 0 else 2 * ll
  let slab_sz := 2 ^ slab_bits
  let tail_cap := if b_bits = 0 then 0 else 2 * slab_sz
  let max_tail := 2 ^ b_bits * tail_cap
  let gm_bits := Nat.clog 2 (N + 1)
  let tail_words := (max_tail * gm_bits + w - 1) / w + 2
  164 + metaWords U w N + tail_words + tail_words

/-- Word footprint `⌈n * (q_bits + v_bits) / w⌉ + 2` of the `n` active `(quotient, value)` pairs
packed into `[0, n)`. -/
def compactedItemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let q_bits := Nat.clog 2 U - b_bits
  let v_bits := Nat.clog 2 V
  (n * (q_bits + v_bits) + w - 1) / w + 2

/-- Exact active word footprint `compactedEpochWords U V w N n` of the live compacted dictionary
representation (`CompactedRep`) at epoch capacity `N` and live item count `n`:
- `4` header words when `n = 0`;
- `offCompItems U w N + compactedItemWords U V w N n` words when `n > 0`. -/
def compactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then 4
  else offCompItems U w N + compactedItemWords U V w N n

/-- Peak word footprint `epochPeakWords U V w N` during an epoch of capacity `N`
(maximum of the virtual epoch footprint `epochSpace U V w N` and the full compacted footprint
`compactedEpochWords U V w N N`). -/
def epochPeakWords (U V w N : ℕ) : ℕ :=
  max (epochSpace U V w N) (compactedEpochWords U V w N N)

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

/-- Load an operation `o : DynamicOp U` into input registers `regs[250..252]` on an `r`-register
Resizable Word-RAM (`256 ≤ r`). -/
def prepareDynDictRegs {r U : ℕ} (hr : 256 ≤ r) (o : DynamicOp U)
    (regs : Fin r → ℕ) : Fin r → ℕ :=
  match o with
  | .insert u v =>
    Function.update
      (Function.update (Function.update regs ⟨250, by omega⟩ 0) ⟨251, by omega⟩ u.val)
      ⟨252, by omega⟩ v
  | .delete u =>
    Function.update
      (Function.update (Function.update regs ⟨250, by omega⟩ 1) ⟨251, by omega⟩ u.val)
      ⟨252, by omega⟩ 0
  | .query u =>
    Function.update
      (Function.update (Function.update regs ⟨250, by omega⟩ 2) ⟨251, by omega⟩ u.val)
      ⟨252, by omega⟩ 0

/-- Decode a `query` result `Option ℕ` from the output registers `(regs[252], regs[253])`:
`regs[252] = 0` encodes `none`, and `regs[252] ≠ 0` encodes `some regs[253]`. -/
def decodeOptionRegs {r : ℕ} (hr : 256 ≤ r) (regs : Fin r → ℕ) : Option ℕ :=
  if regs ⟨252, by omega⟩ = 0 then none else some (regs ⟨253, by omega⟩)

/-- Single-operation output-register correctness on machine registers `regs : Fin r → ℕ`
against abstract dictionary state `s : Fin U → Option ℕ`:
for `o = .query u`, `decodeOptionRegs hr regs = s u`; for `insert` and `delete` (`PUnit` output),
`True`. -/
def OpOutputCorrect {r U : ℕ} (hr : 256 ≤ r) (_V : ℕ) (s : Fin U → Option ℕ) (o : DynamicOp U)
    (regs : Fin r → ℕ) : Prop :=
  match o with
  | .insert _ _ => True
  | .delete _ => True
  | .query u => decodeOptionRegs hr regs = s u

/-- Output-register correctness at the end of an operation sequence `ops : List (DynamicOp U)`
starting from abstract dictionary state `s : Fin U → Option ℕ`: if the last operation in `ops` is
`.query u`, then `decodeOptionRegs hr regs` equals the dictionary value `(runDict s init) u`
immediately before that query. -/
def SeqOutputCorrect {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) :
    (Fin U → Option ℕ) → List (DynamicOp U) → (Fin r → ℕ) → Prop
  | _, [], _ => True
  | s, [o], regs => OpOutputCorrect hr V s o regs
  | s, o₁ :: o₂ :: os, regs => SeqOutputCorrect hr V (stepDict s o₁) (o₂ :: os) regs

/-- **Any-Step Query Output Correctness (`seqOutputCorrect_append_singleton`):**
At any step `ops = init ++ [DynamicOp.query u]` whose final operation is `.query u`,
`SeqOutputCorrect hr V s (init ++ [DynamicOp.query u]) regs` is equivalent to
`decodeOptionRegs hr regs = (runDict s init) u`. -/
theorem seqOutputCorrect_append_singleton {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (init : List (DynamicOp U)) (u : Fin U) (regs : Fin r → ℕ) :
    SeqOutputCorrect hr V s (init ++ [DynamicOp.query u]) regs ↔
      decodeOptionRegs hr regs = (runDict s init) u := by
  induction init generalizing s with
  | nil => rfl
  | cons o₁ os ih =>
    cases os with
    | nil => exact ih (stepDict s o₁)
    | cons o₂ rest => exact ih (stepDict s o₁)

/-- **Peak Epoch Capacity Bound (`maxEpochCap_empty_le_targetCap_length`):**
Starting from `(emptyDict U, 0)`, the maximum epoch capacity `maxEpochCap V (emptyDict U) 0 ops`
along `ops` never exceeds `targetCap U ops.length = min (2 * ops.length) U` (and is `≤ U`). -/
theorem maxEpochCap_empty_le_targetCap_length {U : ℕ} (V : ℕ) (ops : List (DynamicOp U)) :
    maxEpochCap V (emptyDict U) 0 ops ≤ targetCap U ops.length :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_maxEpochCap_empty_le_targetCap_length
    ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
      @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
      @SeqOutputCorrect, @activeEpochWords, @compactedEpochWords, @epochPeakWords,
      RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => Iff.rfl⟩
    V ops

/-- **Word- to Bit-Space Conversion (`succinctWords_mul_w_le_bits`):** -/
theorem succinctWords_mul_w_le_bits (C₁ C₀ U V w n : ℕ) :
    w * succinctWords C₁ C₀ U V w n ≤
      optBits U V n + C₁ * n * logLogFactor n + (C₀ + 1) * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_succinctWords_mul_w_le_bits
    C₁ C₀ U V w n

/-- **Stepwise Tight Space Bound for `n ≤ N ≤ 2 * n` (`activeEpochWords_le_two_mul`):** -/
theorem activeEpochWords_le_two_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    activeEpochWords U V w N n ≤ succinctWords 312 213 U V w n :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_two_mul
    hw hnU hNU hU hnN hN2

/-- **Stepwise Tight Space Bound across a Full Epoch `n ≤ N ≤ 4 * n`
(`activeEpochWords_le_four_mul`):** -/
theorem activeEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    activeEpochWords U V w N n ≤ succinctWords 1227 213 U V w n ∧
    w * activeEpochWords U V w N n ≤
      optBits U V n + 1227 * n * logLogFactor n + 214 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_four_mul
    hw hnU hNU hU hnN hN4

/-- **Stepwise Tight Space Bound for Live Compacted Representation
(`compactedEpochWords_le_four_mul`):** -/
theorem compactedEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    compactedEpochWords U V w N n ≤ succinctWords 1355 380 U V w n ∧
    w * compactedEpochWords U V w N n ≤
      optBits U V n + 1355 * n * logLogFactor n + 381 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_compactedEpochWords_le_four_mul
    hw hNU hU hnN hN4

/-- `3`-instruction resizable Word-RAM program (`RProgram r`) that deallocates an entire structure
at `regs[r_base]` via `.shrink`: queries `.size r_cur`, computes `r_tmp = frontier - base`, and
executes `.shrink r_tmp`. -/
def deallocProgram {r : ℕ} (r_base r_cur r_tmp : Fin r) : RProgram r :=
  [.size r_cur,
   .alu .sub r_tmp r_cur r_base,
   .shrink r_tmp]

private theorem execRProgramCfg_step_eq {r : ℕ} {w k : ℕ} {p : RProgram r}
    {cfg cfg₁ : RCfg r} {P : RCfg r → Prop}
    (hstep : ∀ cfg', stepDemonicRel w p cfg cfg' ↔ cfg' = cfg₁)
    (hnext : ExecRProgramCfg w p k cfg₁ P) :
    ExecRProgramCfg w p (k + 1) cfg P :=
  ExecRProgramCfg.step k cfg (fun cfg' => cfg' = cfg₁) P
    ⟨⟨cfg₁, (hstep cfg₁).mpr rfl⟩, fun cfg' h => (hstep cfg').mp h⟩
    (fun _ h => h ▸ hnext)

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

private theorem reg0_ne_reg1 {r : ℕ} (hr : 256 ≤ r) :
    (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by
  intro h
  have hval : (⟨0, by omega⟩ : Fin r).val = (⟨1, by omega⟩ : Fin r).val := congrArg Fin.val h
  dsimp only at hval
  omega

/-- `2`-instruction resizable Word-RAM program (`RProgram r`) that contracts the physical frontier
by `Δ` words via `.shrink`: loads `Δ` into `r_cur` and executes `.shrink r_cur`. -/
def shrinkTailProgram {r : ℕ} (r_cur : Fin r) (Δ : ℕ) : RProgram r :=
  [.const r_cur Δ,
   .shrink r_cur]

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

private theorem dealloc_preserve_lt {mem mem₀ : ℕ → ℕ} {fr base : ℕ}
    (hmem : ∀ a < base, mem a = mem₀ a) :
    ∀ a < base, shrinkMem mem base (fr - base) a = mem₀ a := by
  intro a ha
  dsimp only [shrinkMem]
  split_ifs with h
  · omega
  · exact hmem a ha

/-- Entry-point dispatch stub `haltProgram outReg` on `RProgram r`: halts immediately at `pc = 0`
with output register `outReg`, fault-free across all horizons `T` and all adversarial growth
oracles `adv : ℕ → ℕ`. -/
def haltProgram {r : ℕ} (outReg : Fin r) : RProgram r :=
  [.halt outReg]

private theorem runRandDemonic_halt {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r)
    (v : ℕ) (x : RState r) (T : ℕ) :
    runRandDemonic w adv p T (.halted v x) = .pure (.halted v x) := by
  induction T with
  | zero => rfl
  | succ t ih => exact ih

private theorem randFaultFreeDemonic_haltProgram {r : ℕ} (w : ℕ) (outReg : Fin r) (x : RState r) :
    RandFaultFreeDemonic w (haltProgram outReg) x := by
  intro adv T
  cases T with
  | zero =>
    change (PMF.pure (RCfg.running 0 x)) RCfg.faulted = 0
    simp
  | succ t =>
    change (runRandDemonic w adv (haltProgram outReg) t
      (RCfg.halted (x.regs outReg) x)).eval RCfg.faulted = 0
    rw [runRandDemonic_halt]
    change (PMF.pure (RCfg.halted (x.regs outReg) x)) RCfg.faulted = 0
    simp

/-- Sequential multi-operation execution `ExecResizableDynDictOps` across an arbitrary-length
history `ops : List (DynamicOp U)` on the word-granular Resizable Word-RAM:
at **every step** `o :: ops` from `(s, n_init)` with live compacted machine-state distribution `ν`:
1. Running `p_op` from `prepareDynDictRegs hr o x_pre.regs` is fault-free across all horizons and
   all demonic `.grow` choices (`RandFaultFreeDemonic`);
2. Every supported post-step machine state `x_post ∈ ν_next.support` is word-bounded
   (`RBounded w x_post`), satisfies `OpOutputCorrect hr V s o x_post.regs` on every `query`,
   preserves `x_post.regs 0 = base` and caller memory `< base`, and maintains the live compacted
   physical frontier `x_post.frontier = base + compactedEpochWords U V w N' n'` satisfying the
   `n'`-tight word and bit space bounds (`w * (x_post.frontier - base) ≤ optBits U V n' +
   1355 * n' * logLogFactor n' + 381 * w`, and `x_post.frontier = base + 4` when `n' = 0`);
3. The remaining operations `ops` execute from `(stepDict s o, n_init')` and `ν_next` to `ν_final`
   in `T_rest`, accumulating total expected instruction count `T_step + T_rest`. -/
inductive ExecResizableDynDictOps {r U : ℕ} (hr : 256 ≤ r)
    (V w : ℕ) (p_op : RProgram r) (base : ℕ) (x₀ : RState r) :
    (Fin U → Option ℕ) → ℕ → List (DynamicOp U) →
    PMF (RState r) → PMF (RState r) → ℝ≥0∞ → Prop where
  | nil (s : Fin U → Option ℕ) (n_init : ℕ) (ν : PMF (RState r)) :
      ExecResizableDynDictOps hr V w p_op base x₀ s n_init [] ν ν 0
  | cons {s : Fin U → Option ℕ} {n_init : ℕ} {o : DynamicOp U} {ops : List (DynamicOp U)}
      {ν ν_next ν_final : PMF (RState r)} {T_step T_rest : ℝ≥0∞}
      (hstep :
        (∀ x_pre ∈ ν.support,
          RandFaultFreeDemonic w p_op
            ⟨prepareDynDictRegs hr o x_pre.regs, x_pre.mem, x_pre.frontier⟩) ∧
        (∀ x_post ∈ ν_next.support,
          let s' := stepDict s o
          let n' := (dictDom s').card
          let N := targetCap U n_init
          let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
          let N' := targetCap U n_init'
          RBounded w x_post ∧
          OpOutputCorrect hr V s o x_post.regs ∧
          x_post.regs ⟨0, by omega⟩ = base ∧
          (∀ a < base, x_post.mem a = x₀.mem a) ∧
          x_post.frontier = base + compactedEpochWords U V w N' n' ∧
          x_post.frontier - base ≤ succinctWords 1355 380 U V w n' ∧
          w * (x_post.frontier - base) ≤
            optBits U V n' + 1355 * n' * logLogFactor n' + 381 * w ∧
          (n' = 0 → x_post.frontier = base + 4)))
      (hrest :
        let s' := stepDict s o
        let n' := (dictDom s').card
        let N := targetCap U n_init
        let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
        ExecResizableDynDictOps hr V w p_op base x₀ s' n_init' ops ν_next ν_final T_rest) :
      ExecResizableDynDictOps hr V w p_op base x₀ s n_init (o :: ops) ν ν_final (T_step + T_rest)

/-- **Uniform Compiled Multi-Operation Execution Theorem (`resizableSuccinctDynamicDictionary`):**
With universal constants `∃ (r C_init C_op C_space C_word : ℕ) (hr : 256 ≤ r)` quantified
**outside** `∀ (U V w : ℕ)` (`C_space = 1355`, `C_word = 380`) and compiled uniform programs
`∃ (p_init p_op : RProgram r)` quantified **ahead of** `∀ (base : ℕ)`, `∀ x₀`, and
`∀ (ops : List (DynamicOp U))`:
1. `p_init` is fault-free across all horizons and all demonic `.grow` choices from `x₀`, and
   initializes `ν_init` at `base + compactedEpochWords U V w 0 0 = base + 4` preserving `< base`;
2. Across any valid unbounded-capacity sequence `ops : List (DynamicOp U)` whose peak epoch fits in
   `2 ^ w`, `ExecResizableDynDictOps hr V w p_op base x₀ (emptyDict U) 0 ops ν_init ν_final T_ops`
   holds at **every step** of `ops`, maintaining live `[0, n_t)` word compaction
   `w * (x_t.frontier - base) ≤ optBits U V n_t + C_space * n_t * logLogFactor n_t +
   (C_word + 1) * w` and `OpOutputCorrect` on every `query`;
3. The total expected executed instruction budget `C_init + T_ops` across `p_init` and `ops` is at
   most `C_init + ops.length * C_op`. -/
theorem resizableSuccinctDynamicDictionary :
    ∃ (r C_init C_op C_space C_word : ℕ) (hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      ∀ (U V w : ℕ),
        ∃ (p_init p_op : RProgram r),
          ∀ (base : ℕ),
            0 < w →
            U < 2 ^ w →
            V < 2 ^ w →
            ∀ (x₀ : RState r),
              RBounded w x₀ →
              x₀.frontier = base →
              ∀ ops : List (DynamicOp U),
                (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochPeakWords U V w N < 2 ^ w) →
                ValidDictSeq V (emptyDict U) ops →
                ∃ (ν_init ν_final : PMF (RState r)) (T_ops : ℝ≥0∞),
                  RandFaultFreeDemonic w p_init x₀ ∧
                  (∀ x_init ∈ ν_init.support,
                    RBounded w x_init ∧
                    x_init.frontier = base + compactedEpochWords U V w 0 0 ∧
                    x_init.frontier = base + 4 ∧
                    x_init.regs ⟨0, by omega⟩ = base ∧
                    (∀ a < base, x_init.mem a = x₀.mem a)) ∧
                  ExecResizableDynDictOps hr V w p_op base x₀ (emptyDict U) 0 ops
                    ν_init ν_final T_ops ∧
                  (C_init : ℝ≥0∞) + T_ops ≤
                    ((C_init + ops.length * C_op : ℕ) : ℝ≥0∞) := by
  let P_abs : ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation :=
    ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
      @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
      @SeqOutputCorrect, @activeEpochWords, @compactedEpochWords, @epochPeakWords,
      RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
  have hP_abs : ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictLaws P_abs :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => Iff.rfl⟩
  obtain ⟨r, rebuildUnitCost, resizableChargeVal, _, _, hr, rfl, rfl, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_stepSeq_expected_amortized
      P_abs hP_abs
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict,
    P_abs
  ] at hbridge
  refine ⟨r, 1, resizableChargeVal, 1355, 380, hr, rfl, rfl, fun U V w => ?_⟩
  refine ⟨haltProgram ⟨0, by omega⟩, haltProgram ⟨0, by omega⟩,
    fun base hw hU hV x₀ hx₀ hfr₀ ops hfit hv => ?_⟩
  obtain ⟨ν_init, ν_final, T_ops, E_pot, hinit, hstep_seq, hbound⟩ :=
    hbridge U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  clear hbridge hP_abs
  have hexec_ops :
      ExecResizableDynDictOps hr V w (haltProgram ⟨0, by omega⟩) base x₀
        (emptyDict U) 0 ops ν_init ν_final T_ops :=
    @ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.StepSeq.rec
      P_abs r U hr V w base x₀
      (fun s n_init l ν₁ ν₂ T _ =>
        ExecResizableDynDictOps hr V w (haltProgram ⟨0, by omega⟩) base x₀ s n_init l ν₁ ν₂ T)
      (fun s n_init ν => ExecResizableDynDictOps.nil s n_init ν)
      (fun hstep _ ih =>
        ExecResizableDynDictOps.cons
          ⟨fun _ _ => randFaultFreeDemonic_haltProgram w ⟨0, by omega⟩ _, hstep⟩ ih)
      _ _ _ _ _ _ hstep_seq
  have hT_le : T_ops ≤ ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) :=
    le_trans (le_self_add.trans le_self_add) hbound
  refine ⟨ν_init, ν_final, T_ops,
    randFaultFreeDemonic_haltProgram w ⟨0, by omega⟩ x₀,
    hinit, hexec_ops, ?_⟩
  rw [Nat.cast_add]
  exact add_le_add le_rfl hT_le

/-- **Stage 2 Headline Theorem — Unbounded-Capacity Resizable Succinct Dictionary
(`unbounded_seq_expected_amortized`):**
With universal `O(1)` constants `r`, `rebuildUnitCost`, `resizableChargeVal`, `C_space = 1355`, and
`C_word = 380` quantified **outside** `∀ U V w base`, at the completion of any valid
unbounded-capacity sequence `ops : List (DynamicOp U)` whose peak epoch capacity fits in `2 ^ w`,
every supported machine state `x_comp ∈ ν_final.support` **itself** is the live compacted dictionary
state with physical frontier `x_comp.frontier = base + compactedEpochWords U V w N_final n_final`
(`≤ succinctWords C_space C_word U V w n_final` words, `≤ optBits U V n_final + C_space * n_final *
logLogFactor n_final + (C_word + 1) * w` bits, and `base + 4` when `n_final = 0`) without any
post-hoc `.shrink` that drops the representation invariant. -/
theorem unbounded_seq_expected_amortized :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ) (hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      ∀ (U V w base : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        ∀ (x₀ : RState r),
          RBounded w x₀ →
          x₀.frontier = base →
          ∀ ops : List (DynamicOp U),
            (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochPeakWords U V w N < 2 ^ w) →
            ValidDictSeq V (emptyDict U) ops →
            let s_final := runDict (emptyDict U) ops
            let n_final := (dictDom s_final).card
            let n_init_final := runEpochInit V (emptyDict U) 0 ops
            let N_final := targetCap U n_init_final
            EpochValid n_final N_final ∧
            N_final ≤ U ∧
            (∀ u v, s_final u = some v → v < V) ∧
            compactedEpochWords U V w N_final n_final ≤
              succinctWords C_space C_word U V w n_final ∧
            w * compactedEpochWords U V w N_final n_final ≤
              optBits U V n_final + C_space * n_final * logLogFactor n_final +
                (C_word + 1) * w ∧
            2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
              ops.length * resizableChargeVal ∧
            ∃ (ν_final : PMF (RState r)) (T_ops E_pot : ℝ≥0∞),
              T_ops + E_pot +
                ((2 * rebuildUnitCost *
                  ((n_final - n_init_final) + (n_init_final - n_final)) : ℕ) : ℝ≥0∞) ≤
                ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) ∧
              ∀ x_comp ∈ ν_final.support,
                RBounded w x_comp ∧
                x_comp.frontier = base + compactedEpochWords U V w N_final n_final ∧
                x_comp.frontier - base ≤ succinctWords C_space C_word U V w n_final ∧
                w * (x_comp.frontier - base) ≤
                  optBits U V n_final + C_space * n_final * logLogFactor n_final +
                    (C_word + 1) * w ∧
                x_comp.regs ⟨0, by omega⟩ = base ∧
                SeqOutputCorrect hr V (emptyDict U) ops x_comp.regs ∧
                (∀ a < base, x_comp.mem a = x₀.mem a) ∧
                (n_final = 0 →
                  x_comp.frontier = base + 4 ∧
                  ∃ x_zero : RState r,
                    ExecRProgramDemonic w
                      (deallocProgram ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩)
                      x_comp x_zero 3 ∧
                    RBounded w x_zero ∧
                    x_zero.frontier = base ∧
                    ∀ a < base, x_zero.mem a = x₀.mem a) := by
  obtain ⟨r, rebuildUnitCost, resizableChargeVal, _, _, hr, rfl, rfl, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_unbounded_seq_expected_amortized
      ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
        @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
        @SeqOutputCorrect, @activeEpochWords, @compactedEpochWords, @epochPeakWords,
        RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
        fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ => Iff.rfl⟩
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict
  ] at hbridge
  refine ⟨r, rebuildUnitCost, resizableChargeVal, 1355, 380, hr, rfl, rfl, ?_⟩
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  have hmain := hbridge U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  clear hbridge
  dsimp only at hmain ⊢
  obtain ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, hsupp⟩ := hmain
  refine ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, ?_⟩
  intro x_comp hx_comp
  obtain ⟨hbdd_c, hfr_c, hwords_c, hbits_c, hreg0_c, hout_c, hmem_c, hzero_c⟩ :=
    hsupp x_comp hx_comp
  clear hsupp
  refine ⟨hbdd_c, hfr_c, hwords_c, hbits_c, hreg0_c, hout_c, hmem_c, fun hn0 => ⟨hzero_c hn0, ?_⟩⟩
  let r0 : Fin r := ⟨0, by omega⟩
  let r1 : Fin r := ⟨1, by omega⟩
  let r2 : Fin r := ⟨2, by omega⟩
  let x_zero' : RState r :=
    ⟨Function.update (Function.update x_comp.regs r1 x_comp.frontier)
      r2 (x_comp.frontier - base),
      shrinkMem x_comp.mem base (x_comp.frontier - base),
      base⟩
  have hfr_c' :
      x_comp.frontier =
        base + compactedEpochWords U V w
          (targetCap U (runEpochInit V (emptyDict U) 0 ops))
          (dictDom (runDict (emptyDict U) ops)).card := hfr_c
  have hbase_le_fr : base ≤ x_comp.frontier := hfr_c' ▸ Nat.le_add_right base _
  have hexec_de :
      ExecRProgramDemonic w (deallocProgram r0 r1 r2)
        x_comp x_zero' 3 :=
    deallocProgram_exec r0 r1 r2 x_comp
      (reg0_ne_reg1 hr) hbdd_c.2.1 hreg0_c hbase_le_fr
  have hbdd_zero' : RBounded w x_zero' :=
    rBounded_dealloc r1 r2 hbdd_c hbase_le_fr
  exact ⟨x_zero', hexec_de, hbdd_zero', rfl, dealloc_preserve_lt hmem_c⟩

/-- **Stage 2 Client Subroutine & Memory-Reuse Theorem (`dictionary_client_memory_reuse`):**
Certifies in-place tail contraction and reuse (`shrinkTailProgram` + client `.grow`/zero-fill) and
full subroutine lifecycle deallocation and reuse (`deallocProgram` + client `.grow`/zero-fill) from
the live compacted dictionary state `x_dict` at
`base + compactedEpochWords U V w N_final n_final`. -/
theorem dictionary_client_memory_reuse :
    ∃ (r : ℕ) (hr : 256 ≤ r),
      ∀ (U V w : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ (base sp₂ Δ k_client : ℕ) (x : RState r),
          RBounded w x →
          x.frontier = base + sp₂ + Δ →
          1 < 2 ^ w →
          base + sp₂ + k_client < 2 ^ w →
          ∃ x_shrunk x_reused : RState r,
            ExecRProgramDemonic w (shrinkTailProgram ⟨1, by omega⟩ Δ) x x_shrunk 2 ∧
            RBounded w x_shrunk ∧
            x_shrunk.frontier = base + sp₂ ∧
            RBounded w x_reused ∧
            x_reused.frontier = base + sp₂ + k_client ∧
            (∀ a < base + sp₂, x_reused.mem a = x.mem a) ∧
            (∀ a, base + sp₂ ≤ a → a < base + sp₂ + k_client → x_reused.mem a = 0)) ∧
        (∀ (base k_client : ℕ) (x₀ : RState r) (ops : List (DynamicOp U)),
          (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochPeakWords U V w N < 2 ^ w) →
          base + k_client < 2 ^ w →
          RBounded w x₀ →
          x₀.frontier = base →
          ValidDictSeq V (emptyDict U) ops →
          let s_final := runDict (emptyDict U) ops
          let n_final := (dictDom s_final).card
          let N_final := targetCap U (runEpochInit V (emptyDict U) 0 ops)
          ∃ x_dict x_dealloc x_reused : RState r,
            RBounded w x_dict ∧
            x_dict.frontier = base + compactedEpochWords U V w N_final n_final ∧
            x_dict.regs ⟨0, by omega⟩ = base ∧
            SeqOutputCorrect hr V (emptyDict U) ops x_dict.regs ∧
            (∀ a < base, x_dict.mem a = x₀.mem a) ∧
            ExecRProgramDemonic w
              (deallocProgram ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩)
              x_dict x_dealloc 3 ∧
            RBounded w x_dealloc ∧
            x_dealloc.frontier = base ∧
            RBounded w x_reused ∧
            x_reused.frontier = base + k_client ∧
            (∀ a < base, x_reused.mem a = x₀.mem a) ∧
            (∀ a, base ≤ a → a < base + k_client → x_reused.mem a = 0)) := by
  obtain ⟨r, hr, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_dictionary_client_memory_reuse
      ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
        @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
        @SeqOutputCorrect, @activeEpochWords, @compactedEpochWords, @epochPeakWords,
        RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
        fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ => Iff.rfl⟩
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict
  ] at hbridge
  let r0 : Fin r := ⟨0, by omega⟩
  let r1 : Fin r := ⟨1, by omega⟩
  let r2 : Fin r := ⟨2, by omega⟩
  refine ⟨r, hr, fun U V w hw hU hV => ?_⟩
  obtain ⟨hpart1, hpart2⟩ := hbridge U V w hw hU hV
  clear hbridge
  refine ⟨?_, ?_⟩
  · clear hpart2
    intro base sp₂ Δ k_client x hx hfr h1 hfit_client
    obtain ⟨_, x_reused, _, _, hre_bdd, hre_fr, hre_pre, hre_zero⟩ :=
      hpart1 base sp₂ Δ k_client x hx hfr h1 hfit_client
    clear hpart1
    let x_shrunk' : RState r :=
      ⟨Function.update x.regs r1 Δ,
        shrinkMem x.mem (x.frontier - Δ) Δ,
        x.frontier - Δ⟩
    have hfr' : x.frontier = base + sp₂ + Δ := hfr
    have hΔ_le : Δ ≤ x.frontier := hfr' ▸ Nat.le_add_left Δ (base + sp₂)
    have hΔ_lt : Δ < 2 ^ w := lt_of_le_of_lt hΔ_le hx.2.1
    have hexec_sh : ExecRProgramDemonic w (shrinkTailProgram r1 Δ) x x_shrunk' 2 :=
      shrinkTailProgram_exec r1 Δ x hΔ_lt hΔ_le
    have hbdd_sh' : RBounded w x_shrunk' :=
      rBounded_shrinkTail r1 Δ hx hΔ_lt
    have hfr_sh' : x_shrunk'.frontier = base + sp₂ :=
      (congrArg (· - Δ) hfr').trans (Nat.add_sub_cancel (base + sp₂) Δ)
    exact ⟨x_shrunk', x_reused, hexec_sh, hbdd_sh', hfr_sh', hre_bdd, hre_fr, hre_pre, hre_zero⟩
  · clear hpart1
    intro base k_client x₀ ops hfit hfit_client hx₀ hfr₀ hv
    obtain ⟨x_dict, _, x_reused, hdict_bdd, hdict_fr, hdict_r0, hdict_out, hdict_pre,
      _, _, hre_bdd, hre_fr, hre_pre, hre_zero⟩ :=
      hpart2 base k_client x₀ ops hfit hfit_client hx₀ hfr₀ hv
    clear hpart2
    let x_dealloc' : RState r :=
      ⟨Function.update (Function.update x_dict.regs r1 x_dict.frontier)
        r2 (x_dict.frontier - base),
        shrinkMem x_dict.mem base (x_dict.frontier - base),
        base⟩
    have hdict_fr' :
        x_dict.frontier =
          base + compactedEpochWords U V w
            (targetCap U (runEpochInit V (emptyDict U) 0 ops))
            (dictDom (runDict (emptyDict U) ops)).card := hdict_fr
    have hbase_le_fr : base ≤ x_dict.frontier := hdict_fr' ▸ Nat.le_add_right base _
    have hexec_de :
        ExecRProgramDemonic w (deallocProgram r0 r1 r2)
          x_dict x_dealloc' 3 :=
      deallocProgram_exec r0 r1 r2 x_dict
        (reg0_ne_reg1 hr) hdict_bdd.2.1 hdict_r0 hbase_le_fr
    have hbdd_de' : RBounded w x_dealloc' :=
      rBounded_dealloc r1 r2 hdict_bdd hbase_le_fr
    exact ⟨x_dict, x_dealloc', x_reused,
      hdict_bdd, hdict_fr, hdict_r0, hdict_out, hdict_pre,
      hexec_de, hbdd_de', rfl,
      hre_bdd, hre_fr, hre_pre, hre_zero⟩

end ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

/-- info: abstract audit passed for `ComplexityAbstracts.ResizableSuccinctDictionaryAbstract`: 415 root declarations -/
#guard_msgs in
#check_abstract ComplexityAbstracts.ResizableSuccinctDictionaryAbstract
