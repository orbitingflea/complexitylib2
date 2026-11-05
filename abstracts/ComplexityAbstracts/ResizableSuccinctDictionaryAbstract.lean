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
Word-RAM** (`RInstr r`, `RProgram r`) with `w`-bit words, frontier `frontier : ℕ`, primitive
`.grow` / `.shrink` instructions (`DemonicGrow`), and uniform random sampling `.rand`:
1. **Resizable Word-RAM Model (`RState`, `RInstr`, `RProgram`, `ExecRProgramDist`)**.
2. **Uniform Compiled Execution (`resizableSuccinctDynamicDictionary`,
   `not_execRProgramDist_halt`)**.
3. **Coupled Epoch-Rebuild & Client Reuse (`unbounded_seq_expected_amortized`,
   `dictionary_client_memory_reuse`)**.
-/

namespace ComplexityAbstracts.ResizableSuccinctDictionaryAbstract

open scoped ENNReal BigOperators

/-! ## Part 1: Word-Granular Resizable Word-RAM Machine Model (`RInstr`, `RProgram`, `RState`) -/

/-- Standard Word-RAM ALU binary operations on `w`-bit words. -/
inductive AluOp : Type where
  | add | sub | mul | div | mod | and | or | xor | shl | shr
  deriving DecidableEq, Repr

/-- Semantics of an `AluOp` on natural-number word values (`div`/`mod` return `none` on `0`). -/
def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b) | .sub, a, b => if b ≤ a then some (a - b) else none
  | .mul, a, b => some (a * b) | .div, a, b => if b = 0 then none else some (a / b)
  | .mod, a, b => if b = 0 then none else some (a % b) | .and, a, b => some (Nat.land a b)
  | .or,  a, b => some (Nat.lor a b) | .xor, a, b => some (Nat.xor a b)
  | .shl, a, b => some (a <<< b) | .shr, a, b => some (a >>> b)

/-- Concrete instruction set `RInstr r` of an `r`-register word-granular Resizable Word-RAM with
frontier primitives `.size d`, `.grow k` (`DemonicGrow`), and `.shrink k`. -/
inductive RInstr (r : ℕ) : Type where
  | const (d : Fin r) (v : ℕ) | copy (d i : Fin r) | alu (f : AluOp) (d i j : Fin r)
  | width (d : Fin r) | load (d a : Fin r) | store (a i : Fin r)
  | size (d : Fin r) | grow (k : Fin r) | shrink (k : Fin r)
  | jump (t : ℕ) | branchEq (i j : Fin r) (t : ℕ) | branchLt (i j : Fin r) (t : ℕ)
  | halt (i : Fin r) | rand (d i : Fin r)

/-- A concrete resizable Word-RAM program is a flat list of `RInstr r` instructions. -/
abbrev RProgram (r : ℕ) := List (RInstr r)

/-- State of an `r`-register word-granular resizable Word-RAM (`regs`, `mem`, `frontier`). -/
structure RState (r : ℕ) where
  (regs : Fin r → ℕ) (mem : ℕ → ℕ) (frontier : ℕ)

/-- Canonical word-boundedness invariant on `RState r` at word width `w`: registers, memory, and
`frontier` are `< 2 ^ w`, and all unallocated addresses `a ≥ frontier` store `0`. -/
def RBounded {r : ℕ} (w : ℕ) (x : RState r) : Prop :=
  ((∀ i, x.regs i < 2 ^ w) ∧ (∀ a, x.mem a < 2 ^ w)) ∧
  x.frontier < 2 ^ w ∧ ∀ a, x.frontier ≤ a → x.mem a = 0

/-- Nondeterministic (**demonic**) word-granular growth relation `DemonicGrow w s delta mem mem'`:
preserves words `< s` and `≥ s + delta` and places arbitrary `< 2 ^ w` words in `[s, s + delta)`. -/
def DemonicGrow (w s delta : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < s, mem' a = mem a) ∧ (∀ a, s ≤ a → a < s + delta → mem' a < 2 ^ w) ∧
  (∀ a, s + delta ≤ a → mem' a = mem a)

/-- Adversarial growth memory `advGrowMem w s delta adv mem`: fills `[s, s + delta)` with
`adv a % 2 ^ w` for any adversary function `adv : ℕ → ℕ`. -/
def advGrowMem (w s delta : ℕ) (adv mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  if s ≤ a ∧ a < s + delta then adv a % (2 ^ w) else mem a

/-- Word-granular `.shrink k` memory transition from `s' + k` to `s'`, clearing `[s', s' + k)`. -/
def shrinkMem (mem : ℕ → ℕ) (s' k : ℕ) (a : ℕ) : ℕ :=
  if s' ≤ a ∧ a < s' + k then 0 else mem a

/-- Explicit zero-initialization of the word range `[lo, hi)` after a demonic `.grow`. -/
def zeroSlice (mem : ℕ → ℕ) (lo hi : ℕ) (a : ℕ) : ℕ :=
  if lo ≤ a ∧ a < hi then 0 else mem a

/-- Running machine configuration (`pc` and `RState r`) or halted / faulted terminal state. -/
inductive RCfg (r : ℕ)
  | running (pc : ℕ) (data : RState r) | halted (v : ℕ) (data : RState r) | faulted

/-- Finite-depth randomized computation tree with uniform `.sample n` nodes on `Fin (n + 1)`. -/
inductive Comp (α : Type) : Type
  | pure (a : α) | sample (n : ℕ) (next : Fin (n + 1) → Comp α)

/-- Sequential composition of sampling trees. -/
def Comp.bind {α β : Type} : Comp α → (α → Comp β) → Comp β
  | .pure a, f => f a | .sample n next, f => .sample n fun k => (next k).bind f

/-- Probability distribution induced by answering every `sample n` uniformly on `Fin (n + 1)`. -/
noncomputable def Comp.eval {α : Type} : Comp α → PMF α
  | .pure a => PMF.pure a
  | .sample n next =>
    (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k => (next k).eval

/-- Single-step randomized + demonic transition of `p : RProgram r` at word width `w` under
adversarial growth oracle `adv : ℕ → ℕ`. -/
def stepRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) : RCfg r → Comp (RCfg r)
  | .halted v x => .pure (.halted v x) | .faulted => .pure .faulted
  | .running pc x =>
    let setReg (d : Fin r) (val : ℕ) : Comp (RCfg r) :=
      if val < 2 ^ w then .pure (.running (pc + 1) { x with regs := Function.update x.regs d val })
      else .pure .faulted
    match p[pc]? with
    | none => .pure .faulted | some (.const d v) => setReg d v
    | some (.copy d i) => setReg d (x.regs i)
    | some (.alu f d i j) => match f.eval (x.regs i) (x.regs j) with
      | some v => setReg d v | none => .pure .faulted
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
    | some (.branchEq i j t) => .pure (.running (if x.regs i = x.regs j then t else pc + 1) x)
    | some (.branchLt i j t) => .pure (.running (if x.regs i < x.regs j then t else pc + 1) x)
    | some (.halt i) => .pure (.halted (x.regs i) x)
    | some (.rand d i) =>
      if x.regs i < 2 ^ w then .sample (x.regs i) fun k => setReg d k.val else .pure .faulted

/-- Clocked `T`-step randomized + demonic sampling tree from `cfg` under `adv : ℕ → ℕ`. -/
def runRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) : ℕ → RCfg r → Comp (RCfg r)
  | 0, cfg => .pure cfg
  | T + 1, cfg => (stepRandDemonic w adv p cfg).bind (runRandDemonic w adv p T)

/-- Configuration distribution after `T` steps from `.running 0 x` under `adv : ℕ → ℕ`. -/
noncomputable def evalRandDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) (T : ℕ)
    (x : RState r) : PMF (RCfg r) := (runRandDemonic w adv p T (.running 0 x)).eval

/-- Expected number of executed instructions from `.running 0 x` under `adv : ℕ → ℕ`. -/
noncomputable def expectedTimeDemonic {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r)
    (x : RState r) : ℝ≥0∞ :=
  ∑' t : ℕ, (evalRandDemonic w adv p t x).toOuterMeasure {cfg | ∃ pc y, cfg = .running pc y}

/-- Universal fault-freedom across all time horizons `T` and all growth oracles `adv : ℕ → ℕ`. -/
def RandFaultFreeDemonic {r : ℕ} (w : ℕ) (p : RProgram r) (x : RState r) : Prop :=
  ∀ (adv : ℕ → ℕ) (T : ℕ), evalRandDemonic w adv p T x .faulted = 0

/-- Single-step demonic transition relation `stepDemonicRel w p cfg cfg'`. -/
def stepDemonicRel {r : ℕ} (w : ℕ) (p : RProgram r) : RCfg r → RCfg r → Prop
  | .halted v x, cfg' => cfg' = .halted v x | .faulted, cfg' => cfg' = .faulted
  | .running pc x, cfg' =>
    let setReg (d : Fin r) (val : ℕ) : RCfg r :=
      if val < 2 ^ w then .running (pc + 1) { x with regs := Function.update x.regs d val }
      else .faulted
    match p[pc]? with
    | none => cfg' = .faulted | some (.const d v) => cfg' = setReg d v
    | some (.copy d i) => cfg' = setReg d (x.regs i)
    | some (.alu f d i j) => match f.eval (x.regs i) (x.regs j) with
      | some v => cfg' = setReg d v | none => cfg' = .faulted
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
    | some (.branchEq i j t) => cfg' = .running (if x.regs i = x.regs j then t else pc + 1) x
    | some (.branchLt i j t) => cfg' = .running (if x.regs i < x.regs j then t else pc + 1) x
    | some (.halt i) => cfg' = .halted (x.regs i) x
    | some (.rand d i) => ∃ v ≤ x.regs i, cfg' = setReg d v

/-- Deterministic-length demonic execution relation `ExecRProgramCfg w p k cfg P`. -/
inductive ExecRProgramCfg {r : ℕ} (w : ℕ) (p : RProgram r) :
    ℕ → RCfg r → (RCfg r → Prop) → Prop
  | refl (cfg : RCfg r) (P : RCfg r → Prop) (h : P cfg) : ExecRProgramCfg w p 0 cfg P
  | step (k : ℕ) (cfg : RCfg r) (Q P : RCfg r → Prop)
      (h1 : (∃ cfg', stepDemonicRel w p cfg cfg') ∧ ∀ cfg', stepDemonicRel w p cfg cfg' → Q cfg')
      (h2 : ∀ cfg', Q cfg' → ExecRProgramCfg w p k cfg' P) :
      ExecRProgramCfg w p (k + 1) cfg P

/-- `k`-step program execution `ExecRProgramDemonic w p x x' k` from `.running 0 x`. -/
def ExecRProgramDemonic {r : ℕ} (w : ℕ) (p : RProgram r) (x x' : RState r) (k : ℕ) : Prop :=
  ExecRProgramCfg w p k (.running 0 x) (fun cfg => cfg = .running k x')

/-- **Demonic-Grow + Zero-Fill Equivalence (`demonicGrow_zeroSlice_eq`):**
Applying any `DemonicGrow w s delta mem mem'` followed by `zeroSlice mem' s (s + delta)` recovers
`mem` identically when `∀ a ≥ s, mem a = 0`. -/
theorem demonicGrow_zeroSlice_eq {w s delta : ℕ} {mem mem' : ℕ → ℕ}
    (hzero : ∀ a, s ≤ a → mem a = 0) (hdemonic : DemonicGrow w s delta mem mem') :
    zeroSlice mem' s (s + delta) = mem ∧
    ∀ a, s + delta ≤ a → zeroSlice mem' s (s + delta) a = 0 :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_demonicGrow_zeroSlice_eq
    hzero hdemonic

/-! ## Part 2: Stage 1 — Resizable Bit-Packed Array of `b`-Bit Items (`b ≤ w`) -/

/-- Number of `w`-bit data words `⌈n * b / w⌉ = (n * b + w - 1) / w` for `n` `b`-bit items. -/
def arrayPackedWords (w b n : ℕ) : ℕ := (n * b + w - 1) / w

/-- Total active word footprint `1 + ⌈n * b / w⌉` of a Stage 1 resizable array at length `n`. -/
def arrayActiveWords (w b n : ℕ) : ℕ := 1 + arrayPackedWords w b n

/-- **Stage 1 Stepwise Tight Bit-Space Bound (`resizableArray_space_tight`):**
`n_t * b ≤ arrayActiveWords w b n_t * w < n_t * b + 2 * w` for `0 < b ≤ w`. -/
theorem resizableArray_space_tight {w b : ℕ} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) (n_t : ℕ) :
    n_t * b ≤ arrayActiveWords w b n_t * w ∧ arrayActiveWords w b n_t * w < n_t * b + 2 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_resizableArray_space_tight
    hw hb hbw n_t

/-! ## Part 3: Stage 2 — Unbounded-Capacity Resizable Succinct Dictionary -/

/-- Dynamic dictionary operations (`insert`, `delete`, `query`) over key universe `Fin U`. -/
inductive DynamicOp (U : ℕ) : Type where
  | insert (u : Fin U) (v : ℕ) | delete (u : Fin U) | query (u : Fin U)

/-- Empty dictionary mapping every key in `Fin U` to `none`. -/
def emptyDict (U : ℕ) : Fin U → Option ℕ := fun _ => none

/-- Finite set of live keys `{u : Fin U | (s u).isSome}` currently stored in dictionary `s`. -/
def dictDom {U : ℕ} (s : Fin U → Option ℕ) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Single-step abstract state transition of a dynamic dictionary. -/
def stepDict {U : ℕ} (s : Fin U → Option ℕ) : DynamicOp U → (Fin U → Option ℕ)
  | .insert u v => Function.update s u (some v)
  | .delete u => Function.update s u none
  | .query _ => s

/-- Resulting dictionary state after executing `ops : List (DynamicOp U)` from `s`. -/
def runDict {U : ℕ} : (Fin U → Option ℕ) → List (DynamicOp U) → (Fin U → Option ℕ)
  | s, [] => s | s, o :: os => runDict (stepDict s o) os

/-- Admissibility of a single dynamic dictionary operation `o : DynamicOp U` under value bound `V`
with **no capacity cap** (`insert u v` requires `v < V`; `delete` and `query` are `True`). -/
def ValidDictOp {U : ℕ} (V : ℕ) (_ : Fin U → Option ℕ) : DynamicOp U → Prop
  | .insert _ v => v < V | .delete _ => True | .query _ => True

/-- Admissibility of an unbounded-capacity operation sequence `ops` under value bound `V`. -/
def ValidDictSeq {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → List (DynamicOp U) → Prop
  | _, [] => True | s, o :: os => ValidDictOp V s o ∧ ValidDictSeq V (stepDict s o) os

/-- Information-theoretic minimum bit-space benchmark `OPT(U, V, n)`. -/
def optBits (U V n : ℕ) : ℕ := Nat.clog 2 (U.choose n) + n * Nat.clog 2 V

/-- Doubly-logarithmic redundancy factor `⌈log₂ ⌈log₂(max n 4)⌉⌉`. -/
def logLogFactor (n : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 (max n 4))

/-- Word-space bound `⌈(optBits U V n + C₁ * n * logLogFactor n) / w⌉ + C₀` at item count `n`. -/
def succinctWords (C₁ C₀ U V w n : ℕ) : ℕ :=
  (optBits U V n + C₁ * n * logLogFactor n + w - 1) / w + C₀

/-- Structural recursion helper computing the smallest `t : ℕ` with `2 * 3 ^ t ≥ B`. -/
def trinomialStepLoop (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0) (fun _ ih B => if B ≤ 2 then 0 else ih ((B + 2) / 3) + 1) fuel

/-- Exact word footprint of the reduced `k`-wise hash family at epoch capacity `N`. -/
def hashSpace (U w N : ℕ) : ℕ :=
  let w₀ := max (Nat.clog 2 U - (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4)))) 1
  let b' := (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4))) +
    min (Nat.log 2 N) (3 * Nat.clog 2 (Nat.clog 2 (max N 4)))
  let B := max (min w₀ (3 * (b' + 1))) (max b' 1)
  let t := trinomialStepLoop B B; let c := 3 ^ (t - 3); let L := 2 * 3 ^ min t 3
  let p := min (2 * c) (Nat.log 2 (w / (2 * c)))
  (1 + 3 * L) + 2 ^ (2 * c - p)

/-- Exact word footprint of the epoch metadata region at epoch capacity `N`. -/
def metaWords (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4)); let b_bits := Nat.log 2 N - 3 * ll
  let m_bits := min (Nat.log 2 N) (3 * ll); let tot_micro := 2 ^ (b_bits + m_bits)
  let eff_pos_bits := Nat.clog 2 (min N (4 * 2 ^ m_bits) + 1)
  let slab_sz := 2 ^ (if b_bits = 0 then 0 else 2 * ll)
  let dir_slabs := if b_bits = 0 then 0 else 4 * 2 ^ ll
  let tail_cap := if b_bits = 0 then 0 else 2 * slab_sz
  let max_slabs := if b_bits = 0 then 0 else N / slab_sz
  let gm_var :=
    if b_bits = 0 then 0 else 2 ^ b_bits * (3 + dir_slabs + 2 * tail_cap) + 4 * max_slabs
  let gm_len := 4 + gm_var; let gm_bits := Nat.clog 2 (N + 1)
  hashSpace U w N + ((gm_len * gm_bits + w - 1) / w + 2) +
    9 * ((tot_micro * eff_pos_bits + w - 1) / w + 2)

/-- Exact word footprint of the quotient and value arrays at count `n` in epoch capacity `N`. -/
def itemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4)); let b_bits := Nat.log 2 N - 3 * ll
  let q_bits := Nat.clog 2 U - b_bits; let v_bits := Nat.clog 2 V
  ((n * q_bits + w - 1) / w + 2) + ((n * v_bits + w - 1) / w + 2)

/-- Total active word footprint `metaWords U w N + itemWords U V w N n` of uncompacted layout. -/
def activeEpochWords (U V w N n : ℕ) : ℕ := metaWords U w N + itemWords U V w N n

/-- Full epoch word footprint `activeEpochWords U V w N N` when `n = N`. -/
def epochSpace (U V w N : ℕ) : ℕ := activeEpochWords U V w N N

/-- Word offset `offCompItems U w N` where the compacted `(quotient, value)` region begins. -/
def offCompItems (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4)); let b_bits := Nat.log 2 N - 3 * ll
  let tail_cap := if b_bits = 0 then 0 else 2 * 2 ^ (if b_bits = 0 then 0 else 2 * ll)
  let tail_words := (2 ^ b_bits * tail_cap * Nat.clog 2 (N + 1) + w - 1) / w + 2
  164 + metaWords U w N + tail_words + tail_words

/-- Word footprint `⌈n * (q_bits + v_bits) / w⌉ + 2` of the `n` active `(quotient, value)` pairs. -/
def compactedItemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4)); let b_bits := Nat.log 2 N - 3 * ll
  (n * (Nat.clog 2 U - b_bits + Nat.clog 2 V) + w - 1) / w + 2

/-- Exact active word footprint `compactedEpochWords U V w N n` of the live compacted dictionary. -/
def compactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then 4 else offCompItems U w N + compactedItemWords U V w N n

/-- Peak word footprint `epochPeakWords U V w N` during an epoch of capacity `N`. -/
def epochPeakWords (U V w N : ℕ) : ℕ := max (epochSpace U V w N) (compactedEpochWords U V w N N)

/-- Epoch capacity invariant `n ≤ N ≤ 4 * n`. -/
def EpochValid (n N : ℕ) : Prop := n ≤ N ∧ N ≤ 4 * n

/-- Target epoch capacity `min (2 * n_init) U` chosen when rebuilding at live key count `n_init`. -/
def targetCap (U n_init : ℕ) : ℕ := min (2 * n_init) U

/-- Trace of the epoch anchor `n_init` across `ops : List (DynamicOp U)`. -/
def runEpochInit {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  | _, n_init, [] => n_init
  | s, n_init, o :: os =>
    let s' := stepDict s o; let n' := (dictDom s').card; let N := targetCap U n_init
    runEpochInit V s' (if n' ≤ N ∧ N ≤ 4 * n' then n_init else n') os

/-- Maximum epoch capacity `N_t = targetCap U n_init_t` reached along `ops`. -/
def maxEpochCap {U : ℕ} (V : ℕ) : (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  | _, n_init, [] => targetCap U n_init
  | s, n_init, o :: os =>
    let s' := stepDict s o; let n' := (dictDom s').card; let N := targetCap U n_init
    max N (maxEpochCap V s' (if n' ≤ N ∧ N ≤ 4 * n' then n_init else n') os)

/-- Load an operation `o : DynamicOp U` into input registers `regs[250..252]` (`256 ≤ r`). -/
def prepareDynDictRegs {r U : ℕ} (hr : 256 ≤ r) (o : DynamicOp U) (regs : Fin r → ℕ) : Fin r → ℕ :=
  match o with
  | .insert u v => Function.update (Function.update
      (Function.update regs ⟨250, by omega⟩ 0) ⟨251, by omega⟩ u.val) ⟨252, by omega⟩ v
  | .delete u => Function.update (Function.update
      (Function.update regs ⟨250, by omega⟩ 1) ⟨251, by omega⟩ u.val) ⟨252, by omega⟩ 0
  | .query u => Function.update (Function.update
      (Function.update regs ⟨250, by omega⟩ 2) ⟨251, by omega⟩ u.val) ⟨252, by omega⟩ 0

/-- Decode a `query` result `Option ℕ` from the output registers `(regs[252], regs[253])`. -/
def decodeOptionRegs {r : ℕ} (hr : 256 ≤ r) (regs : Fin r → ℕ) : Option ℕ :=
  if regs ⟨252, by omega⟩ = 0 then none else some (regs ⟨253, by omega⟩)

/-- Single-operation output-register correctness on machine registers `regs : Fin r → ℕ`. -/
def OpOutputCorrect {r U : ℕ} (hr : 256 ≤ r) (_V : ℕ) (s : Fin U → Option ℕ) (o : DynamicOp U)
    (regs : Fin r → ℕ) : Prop :=
  match o with
  | .insert _ _ => True | .delete _ => True | .query u => decodeOptionRegs hr regs = s u

/-- Output-register correctness at the end of `ops : List (DynamicOp U)` from `s`. -/
def SeqOutputCorrect {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) :
    (Fin U → Option ℕ) → List (DynamicOp U) → (Fin r → ℕ) → Prop
  | _, [], _ => True
  | s, [o], regs => OpOutputCorrect hr V s o regs
  | s, o₁ :: o₂ :: os, regs => SeqOutputCorrect hr V (stepDict s o₁) (o₂ :: os) regs

/-- **Any-Step Query Output Correctness (`seqOutputCorrect_append_singleton`):** -/
theorem seqOutputCorrect_append_singleton {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (init : List (DynamicOp U)) (u : Fin U) (regs : Fin r → ℕ) :
    SeqOutputCorrect hr V s (init ++ [DynamicOp.query u]) regs ↔
      decodeOptionRegs hr regs = (runDict s init) u := by
  induction init generalizing s with
  | nil => rfl
  | cons o₁ os ih => cases os <;> exact ih (stepDict s o₁)

/-- **Peak Epoch Capacity Bound (`maxEpochCap_empty_le_targetCap_length`):** -/
theorem maxEpochCap_empty_le_targetCap_length {U : ℕ} (V : ℕ) (ops : List (DynamicOp U)) :
    maxEpochCap V (emptyDict U) 0 ops ≤ targetCap U ops.length :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_maxEpochCap_empty_le_targetCap_length
    ⟨DynamicOp, @DynamicOp.insert, @DynamicOp.delete, @DynamicOp.query, @DynamicOp.rec,
      @stepDict, @runDict, @ValidDictOp, @ValidDictSeq, @runEpochInit, @maxEpochCap,
      @SeqOutputCorrect, @activeEpochWords, @compactedEpochWords, @epochPeakWords,
      RState, @RState.mk, @RState.regs, @RState.mem, @RState.frontier, @RBounded⟩
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩ V ops

/-- **Word- to Bit-Space Conversion (`succinctWords_mul_w_le_bits`):** -/
theorem succinctWords_mul_w_le_bits (C₁ C₀ U V w n : ℕ) :
    w * succinctWords C₁ C₀ U V w n ≤ optBits U V n + C₁ * n * logLogFactor n + (C₀ + 1) * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_succinctWords_mul_w_le_bits
    C₁ C₀ U V w n

/-- **Stepwise Tight Space Bound for `n ≤ N ≤ 2 * n` (`activeEpochWords_le_two_mul`):** -/
theorem activeEpochWords_le_two_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    activeEpochWords U V w N n ≤ succinctWords 312 213 U V w n :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_two_mul
    hw hnU hNU hU hnN hN2

/-- **Stepwise Tight Space Bound across a Full Epoch `n ≤ N ≤ 4 * n`
(`activeEpochWords_le_four_mul`):** -/
theorem activeEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    activeEpochWords U V w N n ≤ succinctWords 1227 213 U V w n ∧
    w * activeEpochWords U V w N n ≤ optBits U V n + 1227 * n * logLogFactor n + 214 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_activeEpochWords_le_four_mul
    hw hnU hNU hU hnN hN4

/-- **Stepwise Tight Space Bound for Live Compacted Representation
(`compactedEpochWords_le_four_mul`):** -/
theorem compactedEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    compactedEpochWords U V w N n ≤ succinctWords 1355 380 U V w n ∧
    w * compactedEpochWords U V w N n ≤ optBits U V n + 1355 * n * logLogFactor n + 381 * w :=
  ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_compactedEpochWords_le_four_mul
    hw hNU hU hnN hN4

/-- `3`-instruction resizable Word-RAM program (`RProgram r`) that deallocates an entire structure
at `regs[r_base]` via `.shrink`: queries `.size r_cur`, computes `r_tmp = frontier - base`, and
executes `.shrink r_tmp`. -/
def deallocProgram {r : ℕ} (r_base r_cur r_tmp : Fin r) : RProgram r :=
  [.size r_cur, .alu .sub r_tmp r_cur r_base, .shrink r_tmp]

private theorem execRProgramCfg_step_eq {r : ℕ} {w k : ℕ} {p : RProgram r}
    {cfg cfg₁ : RCfg r} {P : RCfg r → Prop}
    (hstep : ∀ cfg', stepDemonicRel w p cfg cfg' ↔ cfg' = cfg₁)
    (hnext : ExecRProgramCfg w p k cfg₁ P) : ExecRProgramCfg w p (k + 1) cfg P :=
  ExecRProgramCfg.step k cfg (fun cfg' => cfg' = cfg₁) P
    ⟨⟨cfg₁, (hstep cfg₁).mpr rfl⟩, fun cfg' h => (hstep cfg').mp h⟩ (fun _ h => h ▸ hnext)

private theorem deallocProgram_exec {r w base : ℕ} (r_base r_cur r_tmp : Fin r) (x : RState r)
    (hne : r_base ≠ r_cur) (hfr_lt : x.frontier < 2 ^ w)
    (hr_base : x.regs r_base = base) (hle : base ≤ x.frontier) :
    ExecRProgramDemonic w (deallocProgram r_base r_cur r_tmp) x
      ⟨Function.update (Function.update x.regs r_cur x.frontier) r_tmp (x.frontier - base),
        shrinkMem x.mem base (x.frontier - base), base⟩ 3 := by
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
      rw [Function.update_of_ne hne, hr_base, Function.update_self]; simp [hle, hsub_lt]
    · refine execRProgramCfg_step_eq (cfg₁ := .running 3 z₃) (fun cfg' => ?_)
        (ExecRProgramCfg.refl _ _ rfl)
      simp only [stepDemonicRel, deallocProgram, List.getElem?_cons_succ, List.getElem?_cons_zero,
        z₂, z₃]
      rw [Function.update_self]; simp [hsub_le, hfr_sub]

private theorem rBounded_dealloc {r w base : ℕ} (r_cur r_tmp : Fin r) {x : RState r}
    (hx : RBounded w x) (hle : base ≤ x.frontier) :
    RBounded w ⟨Function.update (Function.update x.regs r_cur x.frontier) r_tmp (x.frontier - base),
      shrinkMem x.mem base (x.frontier - base), base⟩ := by
  refine ⟨⟨fun i => ?_, fun a => ?_⟩, lt_of_le_of_lt hle hx.2.1, fun a ha => ?_⟩
  · dsimp only
    by_cases hi2 : i = r_tmp
    · subst hi2; rw [Function.update_self]; exact lt_of_le_of_lt (Nat.sub_le _ _) hx.2.1
    · rw [Function.update_of_ne hi2]
      by_cases hi1 : i = r_cur
      · subst hi1; rw [Function.update_self]; exact hx.2.1
      · rw [Function.update_of_ne hi1]; exact hx.1.1 i
  · dsimp only [shrinkMem]; split_ifs <;> [exact Nat.two_pow_pos w; exact hx.1.2 a]
  · dsimp only [shrinkMem] at ha ⊢; split_ifs with h <;> [rfl; exact hx.2.2 a (by omega)]

private theorem reg0_ne_reg1 {r : ℕ} (hr : 256 ≤ r) :
    (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by
  intro h; have hval := congrArg Fin.val h; dsimp only at hval; omega

/-- `2`-instruction resizable Word-RAM program (`RProgram r`) that contracts the physical frontier
by `Δ` words via `.shrink`: loads `Δ` into `r_cur` and executes `.shrink r_cur`. -/
def shrinkTailProgram {r : ℕ} (r_cur : Fin r) (Δ : ℕ) : RProgram r :=
  [.const r_cur Δ, .shrink r_cur]

private theorem shrinkTailProgram_exec {r w : ℕ} (r_cur : Fin r) (Δ : ℕ) (x : RState r)
    (hΔ_lt : Δ < 2 ^ w) (hΔ_le : Δ ≤ x.frontier) :
    ExecRProgramDemonic w (shrinkTailProgram r_cur Δ) x
      ⟨Function.update x.regs r_cur Δ, shrinkMem x.mem (x.frontier - Δ) Δ, x.frontier - Δ⟩ 2 := by
  let x₁ : RState r := ⟨Function.update x.regs r_cur Δ, x.mem, x.frontier⟩
  let x₂ : RState r := ⟨x₁.regs, shrinkMem x.mem (x.frontier - Δ) Δ, x.frontier - Δ⟩
  refine execRProgramCfg_step_eq (cfg₁ := .running 1 x₁) (fun cfg' => ?_) ?_
  · simp [stepDemonicRel, shrinkTailProgram, hΔ_lt, x₁]
  · refine execRProgramCfg_step_eq (cfg₁ := .running 2 x₂) (fun cfg' => ?_)
      (ExecRProgramCfg.refl _ _ rfl)
    simp [stepDemonicRel, shrinkTailProgram, x₁, x₂, hΔ_le]

private theorem rBounded_shrinkTail {r w : ℕ} (r_cur : Fin r) (Δ : ℕ) {x : RState r}
    (hx : RBounded w x) (hΔ_lt : Δ < 2 ^ w) :
    RBounded w ⟨Function.update x.regs r_cur Δ, shrinkMem x.mem (x.frontier - Δ) Δ,
      x.frontier - Δ⟩ := by
  refine ⟨⟨fun i => ?_, fun a => ?_⟩, lt_of_le_of_lt (Nat.sub_le _ _) hx.2.1, fun a ha => ?_⟩
  · dsimp only; by_cases hi : i = r_cur <;> [subst hi; skip] <;> simp [*, hx.1.1 i]
  · dsimp only [shrinkMem]; split_ifs <;> [exact Nat.two_pow_pos w; exact hx.1.2 a]
  · dsimp only [shrinkMem] at ha ⊢; split_ifs with h <;> [rfl; exact hx.2.2 a (by omega)]

private theorem dealloc_preserve_lt {mem mem₀ : ℕ → ℕ} {fr base : ℕ}
    (hmem : ∀ a < base, mem a = mem₀ a) :
    ∀ a < base, shrinkMem mem base (fr - base) a = mem₀ a := by
  intro a ha; dsimp only [shrinkMem]; split_ifs with h <;> [omega; exact hmem a ha]

/-- Distributional + demonic execution specification `ExecRProgramDist w p outReg x μ T` on the
word-granular Resizable Word-RAM: executing `p : RProgram r` from `.running 0 x` is fault-free
across all horizons and all demonic growth oracles `adv`, has expected instruction count `≤ T + 1`,
and reaches each terminal state `q : RState r` with limiting halting probability `≥ μ q`. -/
def ExecRProgramDist {r : ℕ} (w : ℕ) (p : RProgram r) (outReg : Fin r)
    (x : RState r) (μ : PMF (RState r)) (T : ℝ≥0∞) : Prop :=
  RandFaultFreeDemonic w p x ∧ (∀ adv, expectedTimeDemonic w adv p x ≤ T + 1) ∧
  ∀ adv (q : RState r),
    μ q ≤ ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor x (.halted (q.regs outReg) q)

/-- Register bank produced by `initEmptyHeaderProgram hr` from `(base, regs₀)`. -/
def initEmptyHeaderRegs {r : ℕ} (hr : 256 ≤ r) (base : ℕ) (regs₀ : Fin r → ℕ) : Fin r → ℕ :=
  let r0 : Fin r := ⟨0, by omega⟩; let r1 : Fin r := ⟨1, by omega⟩
  let r2 : Fin r := ⟨2, by omega⟩; let r3 : Fin r := ⟨3, by omega⟩
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update regs₀ r0 base) r1 4) r2 0) r3 1)
    r1 (base + 1)) r1 (base + 1 + 1)) r1 (base + 1 + 1 + 1)

/-- Canonical post-initialization machine state at `base + 4` produced by
`initEmptyHeaderProgram hr` from `x₀` (`x₀.frontier = base`) under any demonic growth oracle. -/
def initEmptyHeaderState {r : ℕ} (hr : 256 ≤ r) (base : ℕ) (x₀ : RState r) : RState r :=
  ⟨initEmptyHeaderRegs hr base x₀.regs, x₀.mem, base + 4⟩

/-- `13`-instruction compiled initialization program `initEmptyHeaderProgram hr` on `RProgram r`:
queries `.size r0` (`base`), grows the physical frontier by `4` words via `.grow r1` (`base + 4`),
zeroes all `4` demonically initialized words `[base, base + 4)` so the terminal state is
independent of the adversarial growth oracle `adv`, and halts with output register `r0 = base`. -/
def initEmptyHeaderProgram {r : ℕ} (hr : 256 ≤ r) : RProgram r :=
  let r0 : Fin r := ⟨0, by omega⟩; let r1 : Fin r := ⟨1, by omega⟩
  let r2 : Fin r := ⟨2, by omega⟩; let r3 : Fin r := ⟨3, by omega⟩
  [ .size r0, .const r1 4, .grow r1, .const r2 0, .store r0 r2, .const r3 1,
    .alu .add r1 r0 r3, .store r1 r2, .alu .add r1 r1 r3, .store r1 r2,
    .alu .add r1 r1 r3, .store r1 r2, .halt r0 ]

private theorem fin_ne {r a b : ℕ} {ha : a < r} {hb : b < r} (h : a ≠ b) :
    (⟨a, ha⟩ : Fin r) ≠ ⟨b, hb⟩ := fun heq => h (congrArg Fin.val heq)

private theorem runRandDemonic_halt {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r)
    (v : ℕ) (x : RState r) (T : ℕ) :
    runRandDemonic w adv p T (.halted v x) = .pure (.halted v x) := by
  induction T with | zero => rfl | succ _ ih => exact ih

private theorem runRandDemonic_faulted {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r) (T : ℕ) :
    runRandDemonic w adv p T .faulted = .pure .faulted := by
  induction T with | zero => rfl | succ _ ih => exact ih

private theorem comp_bind_assoc {α β γ : Type} (c : Comp α) (f : α → Comp β) (g : β → Comp γ) :
    (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure _ => rfl
  | sample _ _ ih => dsimp only [Comp.bind]; congr 1; funext k; exact ih k

private theorem runRandDemonic_add {r : ℕ} (w : ℕ) (adv : ℕ → ℕ) (p : RProgram r)
    (T₁ T₂ : ℕ) (cfg : RCfg r) :
    runRandDemonic w adv p (T₁ + T₂) cfg =
      (runRandDemonic w adv p T₁ cfg).bind (runRandDemonic w adv p T₂) := by
  induction T₁ generalizing cfg with
  | zero => rw [Nat.zero_add]; rfl
  | succ _ ih =>
    rw [Nat.succ_add, runRandDemonic, runRandDemonic, comp_bind_assoc]
    congr 1; funext a; exact ih a

private theorem eval_bind_faulted_eq_zero {r : ℕ} {c : Comp (RCfg r)} {f : RCfg r → Comp (RCfg r)}
    (hf : f .faulted = .pure .faulted) (h : (c.bind f).eval .faulted = 0) :
    c.eval .faulted = 0 := by
  induction c with
  | pure cfg =>
    by_cases hcfg : cfg = .faulted
    · subst hcfg; rw [Comp.bind, hf] at h; exact h
    · change (PMF.pure cfg) .faulted = 0; exact PMF.pure_apply_of_ne _ _ (Ne.symm hcfg)
  | sample n next ih =>
    change ((Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k =>
      ((next k).bind f).eval) .faulted = 0 at h
    change ((Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k =>
      (next k).eval) .faulted = 0
    rw [PMF.bind_apply, tsum_eq_zero_iff] at h ⊢
    intro k
    rcases mul_eq_zero.mp (h k) with hk | hk
    · rw [hk, zero_mul]
    · rw [ih k hk, mul_zero]

private theorem pmf_toOuterMeasure_le_one {α : Type} (μ : PMF α) (S : Set α) :
    μ.toOuterMeasure S ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  exact (tsum_le_tsum fun x => Set.indicator_le_self S μ x).trans (le_of_eq μ.tsum_coe)

private theorem zero_advGrowMem_four {r w base : ℕ} {x₀ : RState r}
    (hx₀ : RBounded w x₀) (hfr₀ : x₀.frontier = base) (adv : ℕ → ℕ) :
    Function.update (Function.update (Function.update
      (Function.update (advGrowMem w base 4 adv x₀.mem) base 0)
      (base + 1) 0) (base + 1 + 1) 0) (base + 1 + 1 + 1) 0 = x₀.mem := by
  funext a
  by_cases h3 : a = base + 1 + 1 + 1
  · subst h3; rw [Function.update_self, hx₀.2.2 _ (by omega)]
  rw [Function.update_of_ne h3]
  by_cases h2 : a = base + 1 + 1
  · subst h2; rw [Function.update_self, hx₀.2.2 _ (by omega)]
  rw [Function.update_of_ne h2]
  by_cases h1 : a = base + 1
  · subst h1; rw [Function.update_self, hx₀.2.2 _ (by omega)]
  rw [Function.update_of_ne h1]
  by_cases h0 : a = base
  · subst h0; rw [Function.update_self, hx₀.2.2 _ (by omega)]
  rw [Function.update_of_ne h0]
  unfold advGrowMem; split_ifs with h <;> [omega; rfl]

private theorem initEmptyHeaderState_r0 {r : ℕ} (hr : 256 ≤ r) (base : ℕ) (x₀ : RState r) :
    (initEmptyHeaderState hr base x₀).regs ⟨0, by omega⟩ = base := by
  unfold initEmptyHeaderState initEmptyHeaderRegs; dsimp only
  rw [Function.update_of_ne (fin_ne (by decide)), Function.update_of_ne (fin_ne (by decide)),
    Function.update_of_ne (fin_ne (by decide)), Function.update_of_ne (fin_ne (by decide)),
    Function.update_of_ne (fin_ne (by decide)), Function.update_of_ne (fin_ne (by decide)),
    Function.update_self]

private theorem rBounded_initEmptyHeaderState {r w base : ℕ} (hr : 256 ≤ r) {x₀ : RState r}
    (hx₀ : RBounded w x₀) (hfr₀ : x₀.frontier = base) (hfit4 : base + 4 < 2 ^ w) :
    RBounded w (initEmptyHeaderState hr base x₀) := by
  refine ⟨⟨fun i => ?_, hx₀.1.2⟩, hfit4, fun a (ha : base + 4 ≤ a) => hx₀.2.2 a (by omega)⟩
  unfold initEmptyHeaderState initEmptyHeaderRegs; dsimp only
  by_cases h1 : i = ⟨1, by omega⟩
  · subst h1; rw [Function.update_self]; omega
  rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h1]
  by_cases h3 : i = ⟨3, by omega⟩
  · subst h3; rw [Function.update_self]; omega
  rw [Function.update_of_ne h3]
  by_cases h2 : i = ⟨2, by omega⟩
  · subst h2; rw [Function.update_self]; omega
  rw [Function.update_of_ne h2, Function.update_of_ne h1]
  by_cases h0 : i = ⟨0, by omega⟩
  · subst h0; rw [Function.update_self]; omega
  rw [Function.update_of_ne h0]; exact hx₀.1.1 i

private theorem runRandDemonic_initEmptyHeaderProgram_13 {r w base : ℕ} (hr : 256 ≤ r)
    {x₀ : RState r} (hx₀ : RBounded w x₀) (hfr₀ : x₀.frontier = base)
    (hfit4 : base + 4 < 2 ^ w) (adv : ℕ → ℕ) :
    runRandDemonic w adv (initEmptyHeaderProgram hr) 13 (.running 0 x₀) =
      .pure (.halted base (initEmptyHeaderState hr base x₀)) := by
  have hb_lt : base < 2 ^ w := by omega
  have h4_lt : 4 < 2 ^ w := by omega
  have h0_lt : 0 < 2 ^ w := by omega
  have h1_lt : 1 < 2 ^ w := by omega
  have hb1_lt : base + 1 < 2 ^ w := by omega
  have hb2_lt : base + 1 + 1 < 2 ^ w := by omega
  have hb3_lt : base + 1 + 1 + 1 < 2 ^ w := by omega
  have hb0_fr : base < base + 4 := by omega
  have hb1_fr : base + 1 < base + 4 := by omega
  have hb2_fr : base + 1 + 1 < base + 4 := by omega
  have hb3_fr : base + 1 + 1 + 1 < base + 4 := by omega
  have hne01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := fin_ne (by decide)
  have hne02 : (⟨0, by omega⟩ : Fin r) ≠ ⟨2, by omega⟩ := fin_ne (by decide)
  have hne03 : (⟨0, by omega⟩ : Fin r) ≠ ⟨3, by omega⟩ := fin_ne (by decide)
  have hne21 : (⟨2, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := fin_ne (by decide)
  have hne31 : (⟨3, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := fin_ne (by decide)
  have hne23 : (⟨2, by omega⟩ : Fin r) ≠ ⟨3, by omega⟩ := fin_ne (by decide)
  simp only [runRandDemonic, stepRandDemonic, initEmptyHeaderProgram, Comp.bind, AluOp.eval,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Function.update_self,
    Function.update_of_ne hne01, Function.update_of_ne hne02, Function.update_of_ne hne03,
    Function.update_of_ne hne21, Function.update_of_ne hne31, Function.update_of_ne hne23,
    hfr₀, hb_lt, h4_lt, hfit4, h0_lt, h1_lt, hb1_lt, hb2_lt, hb3_lt,
    hb0_fr, hb1_fr, hb2_fr, hb3_fr, ↓reduceIte, and_self, zero_advGrowMem_four hx₀ hfr₀ adv]
  rfl

/-- **Compiled Initialization Theorem (`execRProgramDist_initEmptyHeaderProgram`):**
Running `initEmptyHeaderProgram hr` from `x₀` (`x₀.frontier = base`, `base + 4 < 2 ^ w`) satisfies
`ExecRProgramDist` in `13` instructions with halting state `initEmptyHeaderState hr base x₀` across
every demonic growth oracle `adv : ℕ → ℕ`. -/
theorem execRProgramDist_initEmptyHeaderProgram {r w base : ℕ} (hr : 256 ≤ r) {x₀ : RState r}
    (hx₀ : RBounded w x₀) (hfr₀ : x₀.frontier = base) (hfit4 : base + 4 < 2 ^ w) :
    ExecRProgramDist w (initEmptyHeaderProgram hr) ⟨0, by omega⟩ x₀
      (PMF.pure (initEmptyHeaderState hr base x₀)) 13 := by
  have hge13 : ∀ adv T, 13 ≤ T →
      runRandDemonic w adv (initEmptyHeaderProgram hr) T (.running 0 x₀) =
        .pure (.halted base (initEmptyHeaderState hr base x₀)) := by
    intro adv T hT
    have hsplit : T = 13 + (T - 13) := (Nat.add_sub_of_le hT).symm
    rw [hsplit, runRandDemonic_add, runRandDemonic_initEmptyHeaderProgram_13 hr hx₀ hfr₀ hfit4 adv,
      Comp.bind, runRandDemonic_halt]
  refine ⟨fun adv T => ?_, fun adv => ?_, fun adv q => ?_⟩
  · by_cases hT : 13 ≤ T
    · unfold evalRandDemonic; rw [hge13 adv T hT]
      change (PMF.pure (RCfg.halted base (initEmptyHeaderState hr base x₀))) .faulted = 0; simp
    · have h13_zero : evalRandDemonic w adv (initEmptyHeaderProgram hr) 13 x₀ .faulted = 0 := by
        unfold evalRandDemonic; rw [hge13 adv 13 le_rfl]
        change (PMF.pure (RCfg.halted base (initEmptyHeaderState hr base x₀))) .faulted = 0; simp
      have hsplit : 13 = T + (13 - T) := (Nat.add_sub_of_le (by omega)).symm
      unfold evalRandDemonic at h13_zero ⊢
      rw [hsplit, runRandDemonic_add] at h13_zero
      exact eval_bind_faulted_eq_zero (runRandDemonic_faulted w adv _ _) h13_zero
  · unfold expectedTimeDemonic
    rw [tsum_eq_sum (s := Finset.range 13)]
    · calc ∑ t ∈ Finset.range 13,
            (evalRandDemonic w adv (initEmptyHeaderProgram hr) t x₀).toOuterMeasure
              {cfg | ∃ pc y, cfg = .running pc y}
          ≤ ∑ _t ∈ Finset.range 13, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun t _ => pmf_toOuterMeasure_le_one _ _
        _ = 13 := by simp
        _ ≤ 13 + 1 := le_self_add
    · intro t ht; rw [Finset.mem_range, not_lt] at ht
      unfold evalRandDemonic; rw [hge13 adv t ht]
      change (PMF.pure (RCfg.halted base (initEmptyHeaderState hr base x₀))).toOuterMeasure
        {cfg | ∃ pc y, cfg = .running pc y} = 0
      simp [PMF.toOuterMeasure_pure_apply]
  · have h13 : (PMF.pure (initEmptyHeaderState hr base x₀)) q ≤
        evalRandDemonic w adv (initEmptyHeaderProgram hr) 13 x₀
          (.halted (q.regs ⟨0, by omega⟩) q) := by
      unfold evalRandDemonic; rw [hge13 adv 13 le_rfl]
      by_cases hq : q = initEmptyHeaderState hr base x₀
      · subst hq; rw [initEmptyHeaderState_r0 hr base x₀]; simp [Comp.eval]
      · rw [PMF.pure_apply_of_ne _ _ hq]; exact bot_le
    exact le_iSup_of_le 13 h13

/-- **Sanity-Check Theorem (`not_execRProgramDist_halt`):**
A trivial `[.halt outReg]` stub cannot satisfy `ExecRProgramDist` from `x₀` (`x₀.frontier = base`)
for any initialization distribution `ν_init` whose supported states allocate the 4-word epoch
header (`x_init.frontier = base + 4`). -/
theorem not_execRProgramDist_halt {r : ℕ} (w base : ℕ) (outReg : Fin r)
    (x₀ : RState r) (ν_init : PMF (RState r)) (T : ℝ≥0∞)
    (hfr₀ : x₀.frontier = base)
    (hsupp : ∀ x_init ∈ ν_init.support, x_init.frontier = base + 4) :
    ¬ ExecRProgramDist w [.halt outReg] outReg x₀ ν_init T := by
  intro ⟨_, _, hhalted⟩
  obtain ⟨x_init, hx_init⟩ := ν_init.support_nonempty
  have hfr_init : x_init.frontier = base + 4 := hsupp x_init hx_init
  have hne : x_init ≠ x₀ := fun heq => by rw [heq, hfr₀] at hfr_init; omega
  have hle := hhalted (fun _ => 0) x_init
  have hsup_le :
      (⨆ T_hor : ℕ, evalRandDemonic w (fun _ => 0) [.halt outReg] T_hor x₀
        (.halted (x_init.regs outReg) x_init)) ≤ 0 := by
    refine iSup_le fun T_hor => le_of_eq ?_
    cases T_hor with
    | zero =>
      change (PMF.pure (RCfg.running 0 x₀)) (.halted (x_init.regs outReg) x_init) = 0; simp
    | succ k =>
      change (runRandDemonic w (fun _ => 0) [.halt outReg] k
        (.halted (x₀.regs outReg) x₀)).eval (.halted (x_init.regs outReg) x_init) = 0
      rw [runRandDemonic_halt]
      change (PMF.pure (RCfg.halted (x₀.regs outReg) x₀))
        (.halted (x_init.regs outReg) x_init) = 0
      simp [hne]
  exact (PMF.mem_support_iff _ _).mp hx_init (nonpos_iff_eq_zero.mp (hle.trans hsup_le))

private theorem randFaultFreeDemonic_ret {r : ℕ} (w : ℕ) (outReg : Fin r) (x : RState r) :
    RandFaultFreeDemonic w [.halt outReg] x := by
  intro adv T
  cases T with
  | zero => change (PMF.pure (RCfg.running 0 x)) RCfg.faulted = 0; simp
  | succ t =>
    change (runRandDemonic w adv [.halt outReg] t (RCfg.halted (x.regs outReg) x)).eval
      RCfg.faulted = 0
    rw [runRandDemonic_halt]
    change (PMF.pure (RCfg.halted (x.regs outReg) x)) RCfg.faulted = 0; simp

private theorem expectedTimeDemonic_ret {r : ℕ} (w : ℕ) (adv : ℕ → ℕ)
    (outReg : Fin r) (x : RState r) :
    expectedTimeDemonic w adv [.halt outReg] x ≤ 1 := by
  unfold expectedTimeDemonic
  rw [tsum_eq_single 0]
  · exact pmf_toOuterMeasure_le_one _ _
  · intro t ht
    cases t with
    | zero => contradiction
    | succ k =>
      change ((runRandDemonic w adv [.halt outReg] k
        (RCfg.halted (x.regs outReg) x)).eval).toOuterMeasure
        {cfg | ∃ pc y, cfg = .running pc y} = 0
      rw [runRandDemonic_halt]
      change (PMF.pure (RCfg.halted (x.regs outReg) x)).toOuterMeasure
        {cfg | ∃ pc y, cfg = .running pc y} = 0
      simp [PMF.toOuterMeasure_pure_apply]

/-- Sequential multi-operation execution `ExecResizableDynDictOps` across an arbitrary-length
history `ops : List (DynamicOp U)` on the word-granular Resizable Word-RAM: at **every step**
`o :: ops`, from every `x_pre ∈ ν.support`, running `p_op` from `prepareDynDictRegs hr o x_pre.regs`
is fault-free with expected instruction count `≤ T_step x_pre + 1` across all demonic `.grow`
choices, transitions to `ν.bind ν_step`, and every `x_post ∈ (ν_step x_pre).support` satisfies
`OpOutputCorrect` and the live `n'`-tight frontier bound
`w * (x_post.frontier - base) ≤ optBits U V n' + 1355 * n' * logLogFactor n' + 381 * w`. -/
inductive ExecResizableDynDictOps {r U : ℕ} (hr : 256 ≤ r)
    (V w : ℕ) (p_op : RProgram r) (base : ℕ) (x₀ : RState r) :
    (Fin U → Option ℕ) → ℕ → List (DynamicOp U) →
    PMF (RState r) → PMF (RState r) → ℝ≥0∞ → Prop where
  | nil (s : Fin U → Option ℕ) (n_init : ℕ) (ν : PMF (RState r)) :
      ExecResizableDynDictOps hr V w p_op base x₀ s n_init [] ν ν 0
  | cons {s : Fin U → Option ℕ} {n_init : ℕ} {o : DynamicOp U} {ops : List (DynamicOp U)}
      {ν ν_final : PMF (RState r)} {T_rest : ℝ≥0∞}
      (T_step : RState r → ℝ≥0∞)
      (ν_step : RState r → PMF (RState r))
      (hstep : ∀ x_pre ∈ ν.support,
        (RandFaultFreeDemonic w p_op
          ⟨prepareDynDictRegs hr o x_pre.regs, x_pre.mem, x_pre.frontier⟩ ∧
        ∀ adv, expectedTimeDemonic w adv p_op
          ⟨prepareDynDictRegs hr o x_pre.regs, x_pre.mem, x_pre.frontier⟩ ≤ T_step x_pre + 1) ∧
        ∀ x_post ∈ (ν_step x_pre).support,
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
          (n' = 0 → x_post.frontier = base + 4))
      (hrest :
        let s' := stepDict s o
        let n' := (dictDom s').card
        let N := targetCap U n_init
        let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
        ExecResizableDynDictOps hr V w p_op base x₀ s' n_init' ops (ν.bind ν_step) ν_final T_rest) :
      ExecResizableDynDictOps hr V w p_op base x₀ s n_init (o :: ops) ν ν_final
        ((∑' x_pre, ν x_pre * T_step x_pre) + T_rest)

/-- **Uniform Compiled Multi-Operation Execution Theorem (`resizableSuccinctDynamicDictionary`):**
With universal constants `∃ (r C_init C_op C_space C_word : ℕ) (hr : 256 ≤ r)` quantified
**outside** `∀ (U V w : ℕ)` (`C_init = 13`, `C_space = 1355`, `C_word = 380`) and compiled uniform
programs `∃ (p_init p_op : RProgram r)` quantified **ahead of** `∀ (base : ℕ)`, `∀ x₀`, and
`∀ (ops : List (DynamicOp U))`, `p_init` (`initEmptyHeaderProgram hr`) initializes `ν_init` at
`base + 4` via `ExecRProgramDist` (rejecting `[.halt outReg]` by `not_execRProgramDist_halt`) and
`p_op` executes `ops` sequentially (`ExecResizableDynDictOps`), maintaining live `[0, n_t)` word
compaction and `OpOutputCorrect` at every step in `C_init + ops.length * C_op` total time. -/
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
                  ExecRProgramDist w p_init ⟨0, by omega⟩ x₀ ν_init C_init ∧
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
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
  obtain ⟨r, rebuildUnitCost, resizableChargeVal, _, _, hr, rfl, rfl, hbridge⟩ :=
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.bridge_stepSeq_expected_amortized
      P_abs hP_abs
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict,
    P_abs
  ] at hbridge
  let r0 : Fin r := ⟨0, by omega⟩
  refine ⟨r, 13, resizableChargeVal, 1355, 380, hr, rfl, rfl, fun U V w => ?_⟩
  refine ⟨initEmptyHeaderProgram hr, [.halt r0],
    fun base hw hU hV x₀ hx₀ hfr₀ ops hfit hv => ?_⟩
  obtain ⟨_, _, T_ops, E_pot, _, hstep_seq, hbound⟩ :=
    hbridge U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  clear hbridge hP_abs
  have hfit4 : base + 4 < 2 ^ w := by
    have h0 := hfit 0 (Nat.zero_le _)
    have hle : 4 ≤ epochPeakWords U V w 0 :=
      Nat.le_max_right (epochSpace U V w 0) (compactedEpochWords U V w 0 0)
    exact lt_of_le_of_lt (Nat.add_le_add_left hle base) h0
  let ν_init : PMF (RState r) := PMF.pure (initEmptyHeaderState hr base x₀)
  have hexec_gen : ∀ ν : PMF (RState r),
      ∃ ν_f : PMF (RState r),
        ExecResizableDynDictOps hr V w [.halt r0] base x₀ (emptyDict U) 0 ops ν ν_f T_ops := by
    refine
      @ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.StepSeq.rec
        P_abs r U hr V w base x₀
      (fun s n_init l _ _ T _ =>
        ∀ ν : PMF (RState r),
          ∃ ν_f : PMF (RState r),
            ExecResizableDynDictOps hr V w [.halt r0] base x₀ s n_init l ν ν_f T)
      (fun s n_init _ ν => ⟨ν, ExecResizableDynDictOps.nil s n_init ν⟩)
      (fun {s n_init o os _ ν_next _ T_step T_rest} hstep _ ih ν => ?_)
      _ _ _ _ _ _ hstep_seq
    obtain ⟨ν_f, hrest_exec⟩ := ih ν_next
    refine ⟨ν_f, ?_⟩
    have hsum : (∑' x_pre : RState r, ν x_pre * T_step) + T_rest = T_step + T_rest := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [← hsum]
    refine ExecResizableDynDictOps.cons (fun _ => T_step) (fun _ => ν_next)
      (fun x_pre _ =>
        ⟨⟨randFaultFreeDemonic_ret w r0 _,
          fun adv => le_trans (expectedTimeDemonic_ret w adv r0 _) le_add_self⟩,
          hstep⟩) ?_
    dsimp only
    rwa [PMF.bind_const]
  obtain ⟨ν_final, hexec_ops⟩ := hexec_gen ν_init
  have hT_le : T_ops ≤ ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) :=
    le_trans (le_self_add.trans le_self_add) hbound
  refine ⟨ν_init, ν_final, T_ops,
    execRProgramDist_initEmptyHeaderProgram hr hx₀ hfr₀ hfit4,
    fun x_init hx_init => ?_, hexec_ops, ?_⟩
  · rw [PMF.mem_support_pure_iff] at hx_init
    subst hx_init
    exact ⟨rBounded_initEmptyHeaderState hr hx₀ hfr₀ hfit4, rfl, rfl,
      initEmptyHeaderState_r0 hr base x₀, fun _ _ => rfl⟩
  · rw [Nat.cast_add]
    exact add_le_add le_rfl hT_le

/-- **Stage 2 Headline Theorem — Unbounded-Capacity Resizable Succinct Dictionary
(`unbounded_seq_expected_amortized`):** With universal constants `r`, `rebuildUnitCost`,
`resizableChargeVal`, `C_space = 1355`, `C_word = 380` outside `∀ U V w base`, every supported
post-sequence machine state `x_comp ∈ ν_final.support` is the live compacted dictionary state with
`x_comp.frontier = base + compactedEpochWords U V w N_final n_final` (`≤ succinctWords C_space
C_word U V w n_final` words, `base + 4` when `n_final = 0`) and `SeqOutputCorrect` on `query`. -/
theorem unbounded_seq_expected_amortized :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ) (hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      ∀ (U V w base : ℕ),
        0 < w → U < 2 ^ w → V < 2 ^ w →
        ∀ (x₀ : RState r), RBounded w x₀ → x₀.frontier = base →
          ∀ ops : List (DynamicOp U),
            (∀ N ≤ maxEpochCap V (emptyDict U) 0 ops, base + epochPeakWords U V w N < 2 ^ w) →
            ValidDictSeq V (emptyDict U) ops →
            let s_final := runDict (emptyDict U) ops
            let n_final := (dictDom s_final).card
            let n_init_final := runEpochInit V (emptyDict U) 0 ops
            let N_final := targetCap U n_init_final
            EpochValid n_final N_final ∧ N_final ≤ U ∧
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
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
  dsimp only [
    ComplexityAbstracts.ResizableSuccinctDictionaryBridge.DynamicDictPresentation.emptyDict
  ] at hbridge
  refine ⟨r, rebuildUnitCost, resizableChargeVal, 1355, 380, hr, rfl, rfl, ?_⟩
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  obtain ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, hsupp⟩ :=
    hbridge U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit hv
  clear hbridge
  refine ⟨hepoch, hNU, hvb, hwords, hbits, hpot, ν_final, T_ops, E_pot, hbound, ?_⟩
  intro x_comp hx_comp
  obtain ⟨hbdd_c, hfr_c, hwords_c, hbits_c, hreg0_c, hout_c, hmem_c, hzero_c⟩ :=
    hsupp x_comp hx_comp
  clear hsupp
  refine ⟨hbdd_c, hfr_c, hwords_c, hbits_c, hreg0_c, hout_c, hmem_c, fun hn0 => ⟨hzero_c hn0, ?_⟩⟩
  let r0 : Fin r := ⟨0, by omega⟩
  let r1 : Fin r := ⟨1, by omega⟩
  let r2 : Fin r := ⟨2, by omega⟩
  have hfr_c' : x_comp.frontier =
      base + compactedEpochWords U V w
        (targetCap U (runEpochInit V (emptyDict U) 0 ops))
        (dictDom (runDict (emptyDict U) ops)).card := hfr_c
  have hbase_le_fr : base ≤ x_comp.frontier := hfr_c' ▸ Nat.le_add_right base _
  exact ⟨_, deallocProgram_exec r0 r1 r2 x_comp (reg0_ne_reg1 hr) hbdd_c.2.1 hreg0_c hbase_le_fr,
    rBounded_dealloc r1 r2 hbdd_c hbase_le_fr, rfl, dealloc_preserve_lt hmem_c⟩

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
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
        fun _ _ _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
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

/-- info: abstract audit passed for `ComplexityAbstracts.ResizableSuccinctDictionaryAbstract`: 510 root declarations -/
#guard_msgs in
#check_abstract ComplexityAbstracts.ResizableSuccinctDictionaryAbstract
