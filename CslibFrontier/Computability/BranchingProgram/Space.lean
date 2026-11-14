/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.Basic
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Languages.Slice
public import Mathlib.Data.Fintype.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native visited-space computations as branching programs (after Arora–Barak Theorem 13.15)

Every deterministic multi-tape Turing machine running within visited work-tape space `s`
(`Turing.MultiTapeTM.RunsInSpace`) on inputs of length `n` for `T` steps compiles into an acyclic
deterministic branching program (`Turing.MultiTapeTM.toBranchingProgram`) over the `n` input bits
whose nodes (`Turing.MultiTapeTM.SpaceConfigNode`) are input-independent timed configuration cores:
* `step : Fin (T + 1)` — the step counter (witnessing acyclicity via `rank v = T - v.step.val`);
* `inputPos : Fin (n + 2)` — the read-only input-head position;
* `storage : BoundedStorage Bool State (fun _ : Fin k => s)` — the control state and work-tape
  contents and head positions restricted to the window `[-s, s]` on each of the `k` work tapes;
* `firstOutput : Option Bool` — the first symbol emitted on the write-only output tape.

When the input head lies on the input word (`1 ≤ inputPos ≤ n`), the node queries input bit
`inputPos - 1` and transitions to the next timed configuration core on both outcomes; when the
input head lies on the left or right boundary blank (`0` or `n + 1`), the transition reads `none`
independently of the input bit. On any input `x : Fin n → Bool` on which the machine stays within
visited space `s`, evaluating the branching program yields the first output bit of the `T`-step run
(`Turing.MultiTapeTM.eval_toBranchingProgram`).

Taking `T = (n + 2) * storageBound Bool State k s` (the configuration-counting halting bound of
`Turing.MultiTapeTM.haltsAt_le_card`) yields the **native visited-space version of Arora and Barak,
Theorem 13.15** (with the `max (S n) 1` zero-space boundary correction): for every problem
`A ∈ Cslib.Complexity.DSPACE enc S` with `S n ≥ Nat.log 2 n`, there is an explicit constant `c`
(`Turing.MultiTapeTM.spaceBranchingProgramBase`, depending on the machine's tape count `k`, state
count `Fintype.card State`, binary work-tape alphabet `Bool`, and linear space constants `c₁, c₂`
under `enc`) such that for every input length `n`, a branching program of size at most
`c ^ max (S n) 1` (and at most `c ^ S n` whenever `1 ≤ S n`, in particular for all `n ≥ 2` or
under the positive logarithmic convention `S n ≥ Nat.log 2 n + 1`) computes the length-`n` slice
of `A` (`Cslib.Complexity.DSPACE.exists_branchingProgram_of_log_le`,
`Cslib.Complexity.DSPACE.exists_branchingProgram_of_log_add_one_le`,
`Cslib.Complexity.DSPACE.exists_branchingProgram_slice`).

**Boundary at `n = 1, S(1) = 0`.** The exponent `max (S n) 1` (or the positiveness condition
`1 ≤ S n`) is necessary when `S n = 0`: at `n = 1`, `Nat.log 2 1 = 0`, so `S(n) = ⌈log₂ n⌉`
satisfies `S(1) = 0 ≥ log₂ 1`, whereas `FirstBit = {x | x₁ = 1} ∈ DSPACE 0` is nonconstant on
`{0, 1}¹` and requires at least `3 > 1 = c ^ S(1)` branching-program nodes (one query node and two
distinct sinks) for every base `c > 1`.

**Space-measure qualification.** Space in `Cslib.Complexity.DSPACE` counts distinct visited
work-tape cells (`Turing.MultiTapeNTM.RunPath.space`), the library's native convention, whereas
Arora and Barak's draft counts ever-nonblank cells (a weaker premise when a machine scans blank
cells without writing, so the draft's ever-nonblank `SPACE(S(n))` convention remains an open
model difference).

## Main definitions

* `Turing.Storage.init`, `Turing.Storage.ofBounded`, `Turing.Action.applyStorage`: initial
  storage, reconstruction of a `Storage` from a `BoundedStorage`, and action application on
  storages.
* `Turing.MultiTapeTM.SpaceConfigNode`: a timed bounded configuration core of a space-bounded
  machine.
* `Turing.MultiTapeTM.toBranchingProgram`: the branching program simulating `T` steps of a
  machine within visited space `s` on inputs of length `n`.
* `Turing.MultiTapeTM.spaceBranchingProgramBase`: the explicit base `c` of the `c ^ S n` node-count
  bound.

## Main results

* `Turing.Storage.ofBounded_toBounded`: reconstructing a storage that fits in a window from its
  bounded restriction is the identity.
* `Turing.MultiTapeTM.fitsIn_runFrom`: every step of a visited-space-`s` run fits in the uniform
  window `[-s, s]`.
* `Turing.MultiTapeTM.eval_toBranchingProgram`: the branching program computes the first output
  bit of the `T`-step run on every input within visited space `s`.
* `Turing.MultiTapeTM.size_toBranchingProgram_le_pow_max`,
  `Turing.MultiTapeTM.size_toBranchingProgram_le_pow`: the branching program for the
  configuration-counting time bound has size at most `spaceBranchingProgramBase ^ max (S n) 1`
  (and `spaceBranchingProgramBase ^ S n` when `1 ≤ S n`).
* `Cslib.Complexity.DSPACE.exists_branchingProgram_of_log_le`,
  `Cslib.Complexity.DSPACE.exists_branchingProgram_of_log_add_one_le`,
  `Cslib.Complexity.DSPACE.exists_branchingProgram_slice`: native visited-space branching-program
  simulation (after Arora–Barak Theorem 13.15, with the `max (S n) 1` boundary correction) for
  encoded problems in `DSPACE enc S` and languages in `DSPACE encBits S`.
* `Cslib.Complexity.L.exists_branchingProgram`,
  `Cslib.Complexity.L.exists_branchingProgram_slice`: specialization to native deterministic
  logarithmic space `L enc` and `L encBits`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Theorem 13.15][AroraBarak07]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-- The initial storage of a machine starting in state `q₀`: all work tapes blank and all work
heads at `0`. -/
def Storage.init (q₀ : State) : Storage Symbol State k where
  state := some q₀
  workTapes _ _ := none
  workTapePos _ := 0

/-- Reconstruct a `Storage` from a `BoundedStorage` on windows `w`, padding cells outside
`[-(w j), w j]` with `none`. -/
def Storage.ofBounded {w : Fin k → ℕ} :
    BoundedStorage Symbol State w → Storage Symbol State k
  | (state, workTapes, workTapePos) =>
    { state := state
      workTapes := fun j z => if hz : z ∈ window (w j) then workTapes j ⟨z, hz⟩ else none
      workTapePos := fun j => (workTapePos j).1 }

/-- Reconstructing a storage that fits in the windows `w` from its bounded restriction recovers
the original storage. -/
theorem Storage.ofBounded_toBounded {x : Storage Symbol State k} {w : Fin k → ℕ}
    (hx : x.FitsIn w) : Storage.ofBounded (x.toBounded w) = x := by
  refine Storage.ext rfl (funext fun j => funext fun z => ?_) (funext fun j => ?_)
  · simp only [ofBounded, toBounded]
    split_ifs with hz
    · rfl
    · exact Classical.byContradiction fun hne => hz (mem_window.mpr (hx.cell_le j z (Ne.symm hne)))
  · simp only [ofBounded, toBounded, dite_eq_left (mem_window.mpr (hx.pos_le j))]

/-- The initial storage fits in every window `w`. -/
theorem Storage.fitsIn_init (q₀ : State) (w : Fin k → ℕ) :
    (Storage.init q₀ : Storage Symbol State k).FitsIn w :=
  ⟨fun _ => Nat.zero_le _, fun _ _ h => absurd rfl h⟩

/-- The effect of a machine `Action` on the state and work-tape `Storage`. -/
def Action.applyStorage (action : Action k Symbol State) (st : Storage Symbol State k) :
    Storage Symbol State k where
  state := action.state
  workTapes i := match (action.workTapes i).1 with
    | none => st.workTapes i
    | some s => Function.update (st.workTapes i) (st.workTapePos i) s
  workTapePos i := st.workTapePos i + (action.workTapes i).2

@[simp]
theorem Action.storage_apply {input : List Symbol} (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (action.apply cfg).storage = action.applyStorage cfg.storage :=
  rfl

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- Along a space-`s` run on `input`, the storage at every step `t` fits in the uniform per-tape
window `fun _ => s`. -/
theorem fitsIn_runFrom {input : List Symbol} {s : ℕ} (hs : tm.RunsInSpace input s) (t : ℕ) :
    (tm.runFrom (tm.initCfg input) t).storage.FitsIn (fun _ => s) := by
  let p := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hlast : p.last = tm.runFrom (tm.initCfg input) t :=
    tm.computationPath_last_eq_runFrom p
  rw [← hlast]
  refine Storage.FitsIn_mono (fun i => ?_) p.storage_fitsIn
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (p.spaceUsedByTape j))
    (Finset.mem_univ i)).trans (hs p)

/-! ### Timed configuration cores and branching-program compilation -/

/-- A timed configuration core of a `k`-tape binary machine with state type `State`, for inputs of
length `n`, work-tape window `s`, and step horizon `T`. Its fields are independent of the input
word `x : Fin n → Bool`. -/
@[ext]
structure SpaceConfigNode (k : ℕ) (State : Type*) (n s T : ℕ) where
  /-- The current step counter (`0 ≤ step ≤ T`), providing the topological rank `T - step`. -/
  step : Fin (T + 1)
  /-- The input-head position (`0` and `n + 1` are the left and right boundary blanks). -/
  inputPos : Fin (n + 2)
  /-- The control state and work-tape configuration restricted to `[-s, s]` on each tape. -/
  storage : BoundedStorage Bool State (fun _ : Fin k => s)
  /-- The first output symbol emitted so far, if any. -/
  firstOutput : Option Bool

namespace SpaceConfigNode

variable {n s T : ℕ}

/-- Equivalence between `SpaceConfigNode` and the product of its four fields. -/
def equivProd (k : ℕ) (State : Type*) (n s T : ℕ) :
    SpaceConfigNode k State n s T ≃
      Fin (T + 1) × Fin (n + 2) × BoundedStorage Bool State (fun _ : Fin k => s) × Option Bool where
  toFun v := (v.step, v.inputPos, v.storage, v.firstOutput)
  invFun | (step, inputPos, storage, firstOutput) => ⟨step, inputPos, storage, firstOutput⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype State] : Fintype (SpaceConfigNode k State n s T) :=
  Fintype.ofEquiv _ (equivProd k State n s T).symm

theorem card_eq [Fintype State] :
    Fintype.card (SpaceConfigNode k State n s T) =
      (T + 1) * (n + 2) * Fintype.card (BoundedStorage Bool State (fun _ : Fin k => s)) * 3 := by
  rw [Fintype.card_congr (equivProd k State n s T)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, Fintype.card_bool]
  ring

/-- The initial timed configuration core at step `0`. -/
def init (tm : MultiTapeTM k Bool State) (n s T : ℕ) : SpaceConfigNode k State n s T where
  step := ⟨0, Nat.zero_lt_succ T⟩
  inputPos := ⟨1, by omega⟩
  storage := (Storage.init tm.q₀).toBounded (fun _ => s)
  firstOutput := none

/-- Advance a timed configuration core by one step of `tm` on reading `inp : Option Bool` under
the input head. -/
noncomputable def stepNode (tm : MultiTapeTM k Bool State)
    (v : SpaceConfigNode k State n s T) (inp : Option Bool) (ht : v.step.val < T) :
    SpaceConfigNode k State n s T :=
  let st := Storage.ofBounded v.storage
  match st.state with
  | none =>
    { step := ⟨v.step.val + 1, Nat.succ_lt_succ ht⟩
      inputPos := v.inputPos
      storage := v.storage
      firstOutput := v.firstOutput }
  | some q =>
    let act := tm.tr q inp (fun i => st.workTapes i (st.workTapePos i))
    { step := ⟨v.step.val + 1, Nat.succ_lt_succ ht⟩
      inputPos := moveInputPos v.inputPos act.inputTape
      storage := (act.applyStorage st).toBounded (fun _ => s)
      firstOutput := v.firstOutput.or act.output }

/-- The timed configuration core extracted from a machine configuration `c` at step `t`. -/
noncomputable def ofCfg {x : Fin n → Bool} (s : ℕ) (t : Fin (T + 1))
    (c : Cfg k Bool State (List.ofFn x)) : SpaceConfigNode k State n s T where
  step := t
  inputPos := c.inputPos.cast (by simp)
  storage := c.storage.toBounded (fun _ => s)
  firstOutput := c.output.head?

private lemma moveInputPos_cast {m₁ m₂ : ℕ} (h : m₁ + 2 = m₂ + 2) (pos : Fin (m₁ + 2))
    (dir : SignType) :
    moveInputPos (pos.cast h) dir = (moveInputPos pos dir).cast h := by
  obtain rfl : m₁ = m₂ := by omega
  rfl

private lemma head?_append_toList (l : List Bool) (o : Option Bool) :
    (l ++ o.toList).head? = l.head?.or o := by
  cases l <;> cases o <;> rfl

/-- When the configuration `c` fits in the uniform window `[-s, s]`, `stepNode` on `c.inputSymbol`
advances `ofCfg s t c` to `ofCfg s (t + 1) (tm.step c)`. -/
theorem stepNode_ofCfg {tm : MultiTapeTM k Bool State} {x : Fin n → Bool} {t : Fin (T + 1)}
    {c : Cfg k Bool State (List.ofFn x)} (ht : t.val < T)
    (hc : c.storage.FitsIn (fun _ => s)) :
    (ofCfg s t c).stepNode tm c.inputSymbol ht =
      ofCfg s ⟨t.val + 1, Nat.succ_lt_succ ht⟩ (tm.step c) := by
  have hst : Storage.ofBounded (ofCfg (T := T) s t c).storage = c.storage :=
    Storage.ofBounded_toBounded hc
  dsimp only [stepNode]
  rw [hst]
  cases hq : c.state with
  | none =>
    have hstate : c.storage.state = none := hq
    rw [hstate, step_of_halt hq]
    rfl
  | some q =>
    have hstate : c.storage.state = some q := hq
    rw [hstate, step_of_state hq]
    have hwork : (fun i => c.storage.workTapes i (c.storage.workTapePos i)) = c.workTapeSymbols :=
      rfl
    rw [hwork]
    simp only [ofCfg, Action.apply_inputPos, moveInputPos_cast, Action.storage_apply,
      Action.apply_output, head?_append_toList]

end SpaceConfigNode

open Cslib.BranchingPrograms

/-- The deterministic branching program over `Fin n → Bool` that simulates `T` steps of `tm`
within work-tape window `s`. Acyclicity is witnessed by the decreasing remaining-step rank
`T - v.step.val`. -/
noncomputable def toBranchingProgram (tm : MultiTapeTM k Bool State) (n s T : ℕ) :
    BranchingProgram (Fin n) Bool (SpaceConfigNode k State n s T) where
  start := SpaceConfigNode.init tm n s T
  node v :=
    if hn : 0 < n then
      if ht : v.step.val < T then
        if hpos : 1 ≤ v.inputPos.val ∧ v.inputPos.val ≤ n then
          .branch ⟨v.inputPos.val - 1, by omega⟩ fun b => v.stepNode tm (some b) ht
        else
          .branch ⟨0, hn⟩ fun _ => v.stepNode tm none ht
      else
        .sink (v.firstOutput.getD false)
    else
      .sink (((tm.runFrom (tm.initCfg []) T).output.head?).getD false)
  rank v := T - v.step.val
  rank_lt v i next b h := by
    by_cases hn : 0 < n
    · rw [dite_eq_left hn] at h
      by_cases ht : v.step.val < T
      · rw [dite_eq_left ht] at h
        by_cases hpos : 1 ≤ v.inputPos.val ∧ v.inputPos.val ≤ n
        · rw [dite_eq_left hpos] at h
          injection h with _ hnext
          subst hnext
          cases b <;>
            · dsimp only [SpaceConfigNode.stepNode]
              split <;> exact Nat.sub_lt_sub_left ht (Nat.lt_succ_self _)
        · rw [dite_eq_right hpos] at h
          injection h with _ hnext
          subst hnext
          dsimp only [SpaceConfigNode.stepNode]
          split <;> exact Nat.sub_lt_sub_left ht (Nat.lt_succ_self _)
      · rw [dite_eq_right ht] at h
        cases h
    · rw [dite_eq_right hn] at h
      cases h

/-- Evaluating `tm.toBranchingProgram n s T` from the node of the `t`-th configuration on an input
`x` (for `0 < n`) yields the first output bit of the `T`-step configuration. -/
theorem evalNode_toBranchingProgram_ofCfg {tm : MultiTapeTM k Bool State} {n s T : ℕ}
    (hn : 0 < n) {x : Fin n → Bool} (hs : tm.RunsInSpace (List.ofFn x) s) :
    ∀ (rem : ℕ) (t : Fin (T + 1)), T - t.val = rem →
      (tm.toBranchingProgram n s T).evalNode x
        (SpaceConfigNode.ofCfg s t (tm.runFrom (tm.initCfg (List.ofFn x)) t.val)) =
      ((tm.runFrom (tm.initCfg (List.ofFn x)) T).output.head?).getD false := by
  intro rem
  induction rem with
  | zero =>
    intro t hrem
    have ht : t.val = T := by have := t.isLt; omega
    have hnotlt : ¬t.val < T := by omega
    have hnode : (tm.toBranchingProgram n s T).node
        (SpaceConfigNode.ofCfg s t (tm.runFrom (tm.initCfg (List.ofFn x)) t.val)) =
        .sink (((tm.runFrom (tm.initCfg (List.ofFn x)) t.val).output.head?).getD false) := by
      simp only [toBranchingProgram, dite_eq_left hn]
      exact dite_eq_right hnotlt
    rw [BranchingProgram.evalNode_sink x hnode, ht]
  | succ rem ih =>
    intro t hrem
    have ht : t.val < T := by omega
    set c := tm.runFrom (tm.initCfg (List.ofFn x)) t.val
    set v : SpaceConfigNode k State n s T := SpaceConfigNode.ofCfg s t c
    have hc : c.storage.FitsIn (fun _ => s) := tm.fitsIn_runFrom hs t.val
    have hstep := SpaceConfigNode.stepNode_ofCfg (tm := tm) (T := T) (s := s) ht hc
    have hnext : tm.step c = tm.runFrom (tm.initCfg (List.ofFn x)) (t.val + 1) := by
      rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    have hvt : v.step.val < T := ht
    by_cases hpos : 1 ≤ v.inputPos.val ∧ v.inputPos.val ≤ n
    · have hnode : (tm.toBranchingProgram n s T).node v =
          .branch ⟨v.inputPos.val - 1, by omega⟩ (fun b => v.stepNode tm (some b) hvt) := by
        simp only [toBranchingProgram, dite_eq_left hn, dite_eq_left hvt, dite_eq_left hpos]
      have hinp : c.inputSymbol = some (x ⟨v.inputPos.val - 1, by omega⟩) := by
        have hv : v.inputPos.val = c.inputPos.val := rfl
        have h1 : c.inputPos.val = 1 + (v.inputPos.val - 1) := by omega
        have h2 : v.inputPos.val - 1 < (List.ofFn x).length := by simp; omega
        rw [inputSymbolInner (v.inputPos.val - 1) h1 h2, List.getElem_ofFn]
      rw [BranchingProgram.evalNode_branch x hnode, ← hinp, hstep, hnext]
      exact ih ⟨t.val + 1, Nat.succ_lt_succ ht⟩ (by dsimp only; omega)
    · have hnode : (tm.toBranchingProgram n s T).node v =
          .branch ⟨0, hn⟩ (fun _ => v.stepNode tm none hvt) := by
        simp only [toBranchingProgram, dite_eq_left hn, dite_eq_left hvt, dite_eq_right hpos]
      have hinp : c.inputSymbol = none := by
        have hv : v.inputPos.val = c.inputPos.val := rfl
        have hlt := c.inputPos.isLt
        have hlen : (List.ofFn x).length = n := List.length_ofFn
        exact inputSymbol_eq_none_of_boundary (by omega)
      rw [BranchingProgram.evalNode_branch x hnode, ← hinp, hstep, hnext]
      exact ih ⟨t.val + 1, Nat.succ_lt_succ ht⟩ (by dsimp only; omega)

/-- **Correctness of the branching-program compiler**: on every input `x : Fin n → Bool` on which
`tm` runs within space `s`, `tm.toBranchingProgram n s T` evaluates to the first output bit of the
`T`-step run of `tm` on `List.ofFn x`. -/
theorem eval_toBranchingProgram {tm : MultiTapeTM k Bool State} {n s T : ℕ}
    {x : Fin n → Bool} (hs : tm.RunsInSpace (List.ofFn x) s) :
    (tm.toBranchingProgram n s T).eval x =
      ((tm.runFrom (tm.initCfg (List.ofFn x)) T).output.head?).getD false := by
  by_cases hn : 0 < n
  · have hstart : (tm.toBranchingProgram n s T).start =
        SpaceConfigNode.ofCfg s ⟨0, Nat.zero_lt_succ T⟩
          (tm.runFrom (tm.initCfg (List.ofFn x)) 0) := by
      ext <;> rfl
    rw [BranchingProgram.eval, hstart]
    exact evalNode_toBranchingProgram_ofCfg hn hs T ⟨0, Nat.zero_lt_succ T⟩ (Nat.sub_zero T)
  · obtain rfl : n = 0 := by omega
    have hx : List.ofFn x = [] := List.ofFn_zero
    have hnode : (tm.toBranchingProgram 0 s T).node (tm.toBranchingProgram 0 s T).start =
        .sink (((tm.runFrom (tm.initCfg []) T).output.head?).getD false) := by
      simp [toBranchingProgram]
    rw [BranchingProgram.eval, BranchingProgram.evalNode_sink x hnode, hx]

/-! ### Explicit node-count bounds (`2 ^ O(S)`) -/

/-- `n + 2 ≤ 3 * 2 ^ ⌊log₂ n⌋` for every natural number `n`. -/
private theorem add_two_le_three_mul_two_pow_log (n : ℕ) : n + 2 ≤ 3 * 2 ^ Nat.log 2 n := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hpos : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_two_pow
  rw [Nat.pow_succ'] at hlt
  omega

/-- The explicit base `c` of the exponential size bound `c ^ S n` for the branching programs
simulating a `k`-tape deterministic machine with state type `State` running within space
`c₁ * S n + c₂` on inputs of length `n`. It depends on the tape count `k`, the state count
`Fintype.card State`, the fixed binary work-tape alphabet `Bool` (via `storageBoundBase` and
`storageBoundExp`), and the linear space constants `c₁, c₂`. -/
def spaceBranchingProgramBase (k : ℕ) (State : Type*) [Fintype State] (c₁ c₂ : ℕ) : ℕ :=
  54 * (storageBoundBase Bool State k) ^ 2 *
    2 ^ (2 * (storageBoundExp Bool k * (k + 1)) * c₂) *
    2 ^ (2 + 2 * (storageBoundExp Bool k * (k + 1)) * c₁)

private theorem one_le_storageBoundBase [Fintype State] : 1 ≤ storageBoundBase Bool State k := by
  unfold storageBoundBase
  exact Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _)

/-- The branching-program size base `spaceBranchingProgramBase k State c₁ c₂` is at least `2`. -/
theorem two_le_spaceBranchingProgramBase [Fintype State] (c₁ c₂ : ℕ) :
    2 ≤ spaceBranchingProgramBase k State c₁ c₂ := by
  have hB : 1 ≤ (storageBoundBase Bool State k) ^ 2 :=
    Nat.one_le_pow 2 _ one_le_storageBoundBase
  have h1 : 1 ≤ 2 ^ (2 * (storageBoundExp Bool k * (k + 1)) * c₂) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 + 2 * (storageBoundExp Bool k * (k + 1)) * c₁) := Nat.one_le_two_pow
  have hmul : 1 ≤ (storageBoundBase Bool State k) ^ 2 *
      2 ^ (2 * (storageBoundExp Bool k * (k + 1)) * c₂) *
      2 ^ (2 + 2 * (storageBoundExp Bool k * (k + 1)) * c₁) :=
    Nat.mul_pos (Nat.mul_pos hB h1) h2
  refine (by omega : 2 ≤ 54).trans ?_
  unfold spaceBranchingProgramBase
  rw [mul_assoc 54, mul_assoc 54]
  exact Nat.le_mul_of_pos_right 54 hmul

/-- For `s ≤ c₁ * S + c₂` and `Nat.log 2 n ≤ S`, the branching program simulating `tm` up to the
configuration-counting step bound `T = (n + 2) * storageBound Bool State k s` has size at most
`(spaceBranchingProgramBase k State c₁ c₂) ^ max S 1`. -/
theorem size_toBranchingProgram_le_pow_max [Fintype State] (tm : MultiTapeTM k Bool State)
    {n s S c₁ c₂ : ℕ} (hs : s ≤ c₁ * S + c₂) (hlog : Nat.log 2 n ≤ S) :
    (tm.toBranchingProgram n s ((n + 2) * storageBound Bool State k s)).size ≤
      (spaceBranchingProgramBase k State c₁ c₂) ^ max S 1 := by
  set B := storageBoundBase Bool State k
  set E := storageBoundExp Bool k
  set D := E * (k + 1)
  have hB1 : 1 ≤ B := one_le_storageBoundBase
  have hpowD : 1 ≤ 2 ^ (D * s) := Nat.one_le_two_pow
  have hsb1 : storageBound Bool State k s ≤ B * 2 ^ (D * s) := by
    refine (storageBound_le_base_mul_pow s).trans (Nat.mul_le_mul_left B ?_)
    refine Nat.pow_le_pow_right (by norm_num) ?_
    dsimp only [D, E]
    exact Nat.mul_le_mul_right s (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
  have hsbk : Fintype.card (BoundedStorage Bool State (fun _ : Fin k => s)) ≤ B * 2 ^ (D * s) := by
    have hcard : Fintype.card (BoundedStorage Bool State (fun _ : Fin k => s)) ≤
        storageBound Bool State k (k * s) :=
      card_boundedStorage_le (by simp)
    refine hcard.trans ((storageBound_le_base_mul_pow (k * s)).trans (Nat.mul_le_mul_left B ?_))
    refine Nat.pow_le_pow_right (by norm_num) ?_
    dsimp only [D, E]
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right s (Nat.mul_le_mul_left _ (Nat.le_succ k))
  set T := (n + 2) * storageBound Bool State k s
  have hT1 : T + 1 ≤ 2 * ((n + 2) * (B * 2 ^ (D * s))) := by
    have hT : T ≤ (n + 2) * (B * 2 ^ (D * s)) := Nat.mul_le_mul_left (n + 2) hsb1
    have hpos : 1 ≤ (n + 2) * (B * 2 ^ (D * s)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos hB1 hpowD)
    omega
  have hsize1 : (tm.toBranchingProgram n s T).size ≤
      6 * B ^ 2 * (n + 2) ^ 2 * 2 ^ (2 * D * s) := by
    rw [BranchingProgram.size, SpaceConfigNode.card_eq]
    calc (T + 1) * (n + 2) * Fintype.card (BoundedStorage Bool State (fun _ : Fin k => s)) * 3
        ≤ (2 * ((n + 2) * (B * 2 ^ (D * s)))) * (n + 2) * (B * 2 ^ (D * s)) * 3 := by
          gcongr
      _ = 6 * B ^ 2 * (n + 2) ^ 2 * (2 ^ (D * s) * 2 ^ (D * s)) := by ring
      _ = 6 * B ^ 2 * (n + 2) ^ 2 * 2 ^ (2 * D * s) := by
          rw [← Nat.pow_add]
          ring_nf
  set M := max S 1
  have hSM : S ≤ M := le_max_left S 1
  have h1M : 1 ≤ M := le_max_right S 1
  have hn2 : n + 2 ≤ 3 * 2 ^ M :=
    (add_two_le_three_mul_two_pow_log n).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (hlog.trans hSM)))
  have hn2_sq : (n + 2) ^ 2 ≤ 9 * 2 ^ (2 * M) := by
    calc (n + 2) ^ 2 ≤ (3 * 2 ^ M) ^ 2 := Nat.pow_le_pow_left hn2 2
      _ = 9 * (2 ^ M) ^ 2 := by ring
      _ = 9 * 2 ^ (2 * M) := by rw [← Nat.pow_mul, Nat.mul_comm M 2]
  have hsM : 2 * D * s ≤ 2 * D * c₂ + (2 * D * c₁) * M := by
    have : s ≤ c₁ * M + c₂ := hs.trans (by gcongr)
    nlinarith
  have hpow_s : 2 ^ (2 * D * s) ≤ 2 ^ (2 * D * c₂) * 2 ^ ((2 * D * c₁) * M) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hsM
  set C₀ := 54 * B ^ 2 * 2 ^ (2 * D * c₂)
  set C₁ := 2 ^ (2 + 2 * D * c₁)
  have hsize2 : 6 * B ^ 2 * (n + 2) ^ 2 * 2 ^ (2 * D * s) ≤ C₀ * C₁ ^ M := by
    calc 6 * B ^ 2 * (n + 2) ^ 2 * 2 ^ (2 * D * s)
        ≤ 6 * B ^ 2 * (9 * 2 ^ (2 * M)) * (2 ^ (2 * D * c₂) * 2 ^ ((2 * D * c₁) * M)) := by
          gcongr
      _ = C₀ * (2 ^ (2 * M) * 2 ^ ((2 * D * c₁) * M)) := by
          dsimp only [C₀]
          ring
      _ = C₀ * C₁ ^ M := by
          dsimp only [C₁]
          rw [← Nat.pow_add, ← Nat.add_mul, Nat.pow_mul]
  have hC₀_pow : C₀ ≤ C₀ ^ M := Nat.le_self_pow (by omega) C₀
  calc (tm.toBranchingProgram n s T).size
      ≤ C₀ * C₁ ^ M := hsize1.trans hsize2
    _ ≤ C₀ ^ M * C₁ ^ M := Nat.mul_le_mul_right (C₁ ^ M) hC₀_pow
    _ = (C₀ * C₁) ^ M := (Nat.mul_pow C₀ C₁ M).symm
    _ = (spaceBranchingProgramBase k State c₁ c₂) ^ M := rfl

/-- When `1 ≤ S` (in particular for `n ≥ 2` or when `S ≥ Nat.log 2 n + 1`), the size of the
branching program is at most `(spaceBranchingProgramBase k State c₁ c₂) ^ S`. -/
theorem size_toBranchingProgram_le_pow [Fintype State] (tm : MultiTapeTM k Bool State)
    {n s S c₁ c₂ : ℕ} (hs : s ≤ c₁ * S + c₂) (hlog : Nat.log 2 n ≤ S) (hS : 1 ≤ S) :
    (tm.toBranchingProgram n s ((n + 2) * storageBound Bool State k s)).size ≤
      (spaceBranchingProgramBase k State c₁ c₂) ^ S := by
  simpa [max_eq_left hS] using size_toBranchingProgram_le_pow_max tm hs hlog

end MultiTapeTM

end Turing

/-! ### Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15) -/

namespace Cslib.Complexity

open Language Turing Turing.MultiTapeTM Cslib.BranchingPrograms

export Turing.MultiTapeTM (spaceBranchingProgramBase)

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {S : ℕ → ℕ}

/-- **Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15, general
`S n ≥ Nat.log 2 n` form).**
For every problem `A ∈ DSPACE enc S` (where `DSPACE` measures distinct visited work-tape cells) with
`∀ n, Nat.log 2 n ≤ S n`, there is a constant `c ≥ 2` (depending on the deciding machine's tape
count, state count, binary work-tape alphabet `Bool`, and linear space constants under `enc`) such
that for every input length `n`, there is a finite node type `Node` and a deterministic branching
program `P : BranchingProgram (Fin n) Bool Node` of size at most `c ^ max (S n) 1` (hence
`≤ c ^ S n` whenever `1 ≤ S n`, and `≤ c ^ (S n + 1)` for all `n`) that computes
`encodesMember enc A n` on all encoded instances of length `n`. The `max (S n) 1` floor is needed at
`n = 1, S 1 = 0`, where a nonconstant 1-bit language in `DSPACE 0` requires at least `3 > 1 = c ^ 0`
nodes. -/
theorem DSPACE.exists_branchingProgram_of_log_le (hA : A ∈ DSPACE enc S)
    (hS : ∀ n, Nat.log 2 n ≤ S n) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ max (S n) 1 ∧
      (∀ x ∈ encodes enc n, P.eval x = encodesMember enc A n x) ∧
      (∀ a : α, (h : (enc a).length = n) →
        P.eval (fun i : Fin n => (enc a)[i.val]'(by omega)) = indicator A a) := by
  classical
  obtain ⟨c₁, c₂, t, k, State, hfin, tm, htm⟩ := hA
  let := Fintype.ofFinite State
  refine ⟨spaceBranchingProgramBase k State c₁ c₂, two_le_spaceBranchingProgramBase c₁ c₂,
    fun n => ?_⟩
  set s := c₁ * S n + c₂
  set T := (n + 2) * storageBound Bool State k s
  have heval_eq : ∀ (x : Fin n → Bool) (a : α), enc a = List.ofFn x →
      (tm.toBranchingProgram n s T).eval x = indicator A a := by
    intro x a ha
    have hlen : (enc a).length = n := by rw [ha, List.length_ofFn]
    have hcard := (htm a).of_card
    have hs : tm.RunsInSpace (List.ofFn x) s := by
      simpa [← ha, s, hlen] using hcard.2.2
    obtain ⟨u, hu_le, hu⟩ := exists_haltsAt_of_runsInTime hcard.2.1
    have hout : (tm.runFrom (tm.initCfg (List.ofFn x)) T).output = [indicator A a] := by
      have hT :
          ((enc a).length + 2) * storageBound Bool State k (c₁ * S (enc a).length + c₂) = T := by
        simp [T, s, hlen]
      rw [← ha, ← hT, hu.runFrom_eq hu_le]
      exact output_haltsAt hcard.1 hu
    rw [tm.eval_toBranchingProgram hs, hout]
    rfl
  refine ⟨SpaceConfigNode k State n s T, inferInstance, tm.toBranchingProgram n s T,
    tm.size_toBranchingProgram_le_pow_max le_rfl (hS n), ?_, ?_⟩
  · rintro x ⟨a, ha⟩
    rw [heval_eq x a ha]
    by_cases haA : a ∈ A
    · rw [(encodesMember_eq_true_iff ha).2 haA]
      simp [indicator, haA]
    · have hfalse : encodesMember enc A n x = false :=
        Bool.eq_false_iff.2 fun h => haA ((encodesMember_eq_true_iff ha).1 h)
      rw [hfalse]
      simp [indicator, haA]
  · intro a hlen
    refine heval_eq _ a ?_
    refine List.ext_getElem (hlen.trans List.length_ofFn.symm) fun i h₁ h₂ => ?_
    simp

/-- **Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15, `c ^ S n`
form for positive space bounds `S n ≥ 1`).**
When `∀ n, Nat.log 2 n ≤ S n` and `∀ n, 1 ≤ S n` (in particular under the repository's standard
logarithmic convention `S n ≥ Nat.log 2 n + 1`), every length-`n` slice of `A ∈ DSPACE enc S` is
computed on encoded instances by a branching program of size at most `c ^ S n`. -/
theorem DSPACE.exists_branchingProgram (hA : A ∈ DSPACE enc S)
    (hS : ∀ n, Nat.log 2 n ≤ S n) (hpos : ∀ n, 1 ≤ S n) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ S n ∧
      (∀ x ∈ encodes enc n, P.eval x = encodesMember enc A n x) ∧
      (∀ a : α, (h : (enc a).length = n) →
        P.eval (fun i : Fin n => (enc a)[i.val]'(by omega)) = indicator A a) := by
  obtain ⟨c, hc, hP⟩ := DSPACE.exists_branchingProgram_of_log_le hA hS
  refine ⟨c, hc, fun n => ?_⟩
  obtain ⟨Node, hfin, P, hsize, henc, ha⟩ := hP n
  rw [max_eq_left (hpos n)] at hsize
  exact ⟨Node, hfin, P, hsize, henc, ha⟩

/-- **Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15) under
`S n ≥ Nat.log 2 n + 1`.** -/
theorem DSPACE.exists_branchingProgram_of_log_add_one_le (hA : A ∈ DSPACE enc S)
    (hS : ∀ n, Nat.log 2 n + 1 ≤ S n) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ S n ∧
      (∀ x ∈ encodes enc n, P.eval x = encodesMember enc A n x) ∧
      (∀ a : α, (h : (enc a).length = n) →
        P.eval (fun i : Fin n => (enc a)[i.val]'(by omega)) = indicator A a) :=
  DSPACE.exists_branchingProgram hA (fun n => (Nat.le_succ _).trans (hS n))
    (fun n => (Nat.le_add_left 1 _).trans (hS n))

/-- **Native visited-space branching-program simulation (after Arora–Barak Theorem 13.15) for
boolean languages (`enc = encBits`).**
For every language `L ∈ DSPACE encBits S` with `∀ n, Nat.log 2 n ≤ S n`, there is a constant
`c ≥ 2` such that for every `n`, the slice `L.slice n : (Fin n → Bool) → Bool` is computed on all
`2 ^ n` inputs by a deterministic branching program of size at most `c ^ max (S n) 1` (and at most
`c ^ S n` whenever `1 ≤ S n`). -/
theorem DSPACE.exists_branchingProgram_slice {L : Language Bool} (hL : L ∈ DSPACE encBits S)
    (hS : ∀ n, Nat.log 2 n ≤ S n) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ max (S n) 1 ∧ P.eval = L.slice n := by
  obtain ⟨c, hc, hP⟩ := DSPACE.exists_branchingProgram_of_log_le hL hS
  refine ⟨c, hc, fun n => ?_⟩
  obtain ⟨Node, hfin, P, hsize, henc, -⟩ := hP n
  refine ⟨Node, hfin, P, hsize, funext fun x => ?_⟩
  have hx : x ∈ encodes encBits n := ⟨List.ofFn x, rfl⟩
  have hmem :=
    encodesMember_eq_true_iff (enc := encBits) (A := (L : Set (List Bool)))
      (x := x) (a := List.ofFn x) rfl
  rw [henc x hx, Bool.eq_iff_iff, hmem, Language.slice_eq_true_iff]
  rfl

/-- **Native deterministic logarithmic space `L` has polynomial-size branching programs** of size at
most `c ^ (Nat.log 2 n + 1)` at every input length `n` (via the visited-space simulation after
Arora–Barak Theorem 13.15). -/
theorem L.exists_branchingProgram (hA : A ∈ L enc) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ (Nat.log 2 n + 1) ∧
      (∀ x ∈ encodes enc n, P.eval x = encodesMember enc A n x) ∧
      (∀ a : α, (h : (enc a).length = n) →
        P.eval (fun i : Fin n => (enc a)[i.val]'(by omega)) = indicator A a) := by
  have hDSPACE : A ∈ DSPACE enc (fun n => Nat.log 2 n + 1) := by
    refine DSPACE_mono_of_le_mul_add (s₁ := Nat.log2) (C := 1) (fun n => ?_)
      (mem_L_iff_mem_DSPACE.mp hA)
    rw [Nat.log2_eq_log_two]
    omega
  exact DSPACE.exists_branchingProgram_of_log_add_one_le hDSPACE fun _ => le_rfl

/-- For a boolean language `L₀ ∈ L encBits`, every length-`n` slice `L₀.slice n` has a
deterministic branching program of size at most `c ^ (Nat.log 2 n + 1)` (under native visited
logarithmic space). -/
theorem L.exists_branchingProgram_slice {L₀ : Language Bool} (hL : L₀ ∈ L encBits) :
    ∃ c ≥ 2, ∀ n, ∃ (Node : Type) (_ : Fintype Node) (P : BranchingProgram (Fin n) Bool Node),
      P.size ≤ c ^ (Nat.log 2 n + 1) ∧ P.eval = L₀.slice n := by
  obtain ⟨c, hc, hP⟩ := L.exists_branchingProgram hL
  refine ⟨c, hc, fun n => ?_⟩
  obtain ⟨Node, hfin, P, hsize, henc, -⟩ := hP n
  refine ⟨Node, hfin, P, hsize, funext fun x => ?_⟩
  have hmem :=
    encodesMember_eq_true_iff (enc := encBits) (A := (L₀ : Set (List Bool)))
      (x := x) (a := List.ofFn x) rfl
  rw [henc x ⟨List.ofFn x, rfl⟩, Bool.eq_iff_iff, hmem, Language.slice_eq_true_iff]
  rfl

end Cslib.Complexity
