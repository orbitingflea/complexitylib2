/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.BitResizable
public import Complexity.Languages.Probabilistic.Expect

/-!
# Randomized Structured Execution of the Bit-Granular Resizable Word RAM

This module equips `Cslib.WordRAM.BitRAM.Code` with a randomized big-step execution
and expected-cost judgment `ExecCodeDistWithOracle` parameterized by a demonic `.grow` oracle
`oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)` satisfying `DirtyGrowOracle w oracle`.

## Main definitions

- `BitRAM.DirtyGrowOracle`: predicate stating that `oracle mem bitSize δ` is a valid post-growth
  word memory under `BitMemory.dirtyStep w ⟨mem, bitSize⟩ (.grow δ) · bitSize` (preserving all
  bits below `bitSize` and allowing arbitrary contents in `[bitSize, bitSize + δ)`).
- `BitRAM.zeroGrowOracle`: the canonical zero-initialized `.grow` oracle.
- `BitRAM.ExecCodeDistWithOracle`: big-step distribution and expected instruction-cost judgment
  `ExecCodeDistWithOracle w oracle c x μ t` where `.rand dst src` samples uniformly from
  `Fin (x.regs src + 1)` via `ProbComp.unifFin (x.regs src)` in `1` instruction unit and
  `.grow dst δReg` transitions according to `oracle` in `max 1 ((x.regs δReg) ⌈/⌉ w)` instruction
  units.
- `BitRAM.evalWithOracle`: total fuel-bounded deterministic evaluator for `.rand`-free structured
  programs `c : Code B r` under `oracle`.

## Main results

- `BitRAM.DemonicExecWithin.evalWithOracle_spec`: any `.rand`-free program satisfying
  `DemonicExecWithin w c x P T` evaluates deterministically under any `DirtyGrowOracle w oracle`
  to `y = evalWithOracle w oracle T c x` satisfying `P y` and
  `ExecCodeDistWithOracle w oracle c x (PMF.pure y) (T : ℝ≥0∞)`.
- `BitRAM.ExecCodeDistWithOracle.seq_demonic_right`: sequencing a randomized program `c₁` with a
  deterministic post-processing program `c₂` verified via `DemonicExecWithin`.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.BitRAM

open Cslib.WordRAM
open Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Memory.BitMemory

variable {B : Basis} {r : ℕ}

/-- A function `oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)` is a valid demonic `.grow` memory oracle at
word width `w` if for every word memory `mem`, current bit size `bitSize`, and bit increment `δ`,
transitioning from `⟨mem, bitSize⟩` to `⟨oracle mem bitSize δ, bitSize + δ⟩` satisfies
`BitMemory.dirtyStep w ⟨mem, bitSize⟩ (.grow δ) ⟨oracle mem bitSize δ, bitSize + δ⟩ bitSize`. -/
def DirtyGrowOracle (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) : Prop :=
  ∀ mem bitSize δ,
    BitMemory.dirtyStep w ⟨mem, bitSize⟩ (.grow δ) ⟨oracle mem bitSize δ, bitSize + δ⟩ bitSize

/-- The canonical zero-initialized `.grow` oracle at word width `w` clears all bits at or above
`bitSize` while preserving `[0, bitSize)` and masking every word to `w` bits. -/
def zeroGrowOracle (w : ℕ) : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ) :=
  fun mem bitSize _ q => clearRangeWord w (mem q) q bitSize ((q + 1) * w)

/-- `zeroGrowOracle w` is a valid `DirtyGrowOracle w` for every `0 < w`. -/
theorem dirtyGrowOracle_zeroGrowOracle {w : ℕ} (hw : 0 < w) :
    DirtyGrowOracle w (zeroGrowOracle w) := by
  intro mem bitSize δ
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro q
    exact clearMask_lt (Nat.and_lt_two_pow (mem q) (bitMask_lt w)) _
  · intro i hi
    change i < bitSize at hi
    have hmod : i % w < w := Nat.mod_lt i hw
    have hdiv_mod : i / w * w + i % w = i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i w
    have hnext : (i / w + 1) * w - i / w * w = w := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    simp only [State.getBit, readBit, Nat.zero_add, zeroGrowOracle, clearRangeWord,
      clearMask_testBit, Nat.testBit_and, bitMask_testBit, hmod, decide_true, Bool.and_true,
      sliceMask_testBit, hnext, min_self]
    have hcond : ¬(bitSize - i / w * w ≤ i % w ∧
        i % w < bitSize - i / w * w + (w - (bitSize - i / w * w))) := by
      omega
    rw [decide_eq_false hcond]
    simp
  · intro i hi
    change bitSize + δ ≤ i at hi
    have hmod : i % w < w := Nat.mod_lt i hw
    have hdiv_mod : i / w * w + i % w = i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i w
    have hnext : (i / w + 1) * w - i / w * w = w := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    simp only [State.getBit, readBit, Nat.zero_add, zeroGrowOracle, clearRangeWord,
      clearMask_testBit, Nat.testBit_and, bitMask_testBit, hmod, decide_true, Bool.and_true,
      sliceMask_testBit, hnext, min_self]
    have hcond : bitSize - i / w * w ≤ i % w ∧
        i % w < bitSize - i / w * w + (w - (bitSize - i / w * w)) := by
      omega
    simp [hcond]

/-- Fuel-bounded deterministic evaluator for `.rand`-free `BitRAM.Code` under a `.grow` memory
oracle `oracle`. -/
def evalWithOracle (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) :
    ℕ → Code B r → Data r → Data r
  | _, .op o, x => (evalOp w o x).getD x
  | _, .grow dst δReg, x =>
      ⟨Function.update x.regs dst x.bitSize,
        oracle x.mem x.bitSize (x.regs δReg),
        x.bitSize + x.regs δReg⟩
  | _, .shrink δReg, x =>
      ⟨x.regs,
        (BitMemory.stepFn w x.toBitMemoryState (.shrink (x.regs δReg))).1.mem,
        x.bitSize - x.regs δReg⟩
  | _, .size dst, x => x.set dst x.bitSize
  | _, .rand _ _, x => x
  | fuel, .seq c₁ c₂, x =>
      evalWithOracle w oracle fuel c₂ (evalWithOracle w oracle fuel c₁ x)
  | fuel, .branch c pos neg, x =>
      if CondHolds c x then evalWithOracle w oracle fuel pos x
      else evalWithOracle w oracle fuel neg x
  | 0, .loop _ _, x => x
  | fuel + 1, .loop c body, x =>
      if CondHolds c x then
        evalWithOracle w oracle fuel (.loop c body) (evalWithOracle w oracle fuel body x)
      else x

/-- Randomized big-step execution and expected instruction-cost relation
`ExecCodeDistWithOracle w oracle c x μ t`:
at word width `w` under `.grow` memory oracle `oracle`, structured program `c` starting from `x`
terminates with output state distribution `μ : PMF (Data r)` in at most `t : ℝ≥0∞` expected
instruction units. -/
inductive ExecCodeDistWithOracle (w : ℕ) (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)) :
    Code B r → Data r → PMF (Data r) → ℝ≥0∞ → Prop where
  /-- Standard Word-RAM data instruction costs `1` unit when `evalOp w o x = some y`. -/
  | op {o : Op B r} {x y : Data r} :
      evalOp w o x = some y →
      ExecCodeDistWithOracle w oracle (.op o) x (PMF.pure y) 1
  /-- Growing by `δ = x.regs δReg` bits (when `Fits w (x.bitSize + δ)`) costs
  `max 1 (δ ⌈/⌉ w)` instruction units and transitions via `oracle`. -/
  | grow {dst δReg : Fin r} {x : Data r} :
      Fits w (x.bitSize + x.regs δReg) →
      ExecCodeDistWithOracle w oracle (.grow dst δReg) x
        (PMF.pure ⟨Function.update x.regs dst x.bitSize,
          oracle x.mem x.bitSize (x.regs δReg),
          x.bitSize + x.regs δReg⟩)
        ((max 1 ((x.regs δReg) ⌈/⌉ w) : ℕ) : ℝ≥0∞)
  /-- Shrinking by `δ = x.regs δReg` bits (when `δ ≤ x.bitSize`) costs
  `max 1 (δ ⌈/⌉ w)` instruction units and clears the released bits `[x.bitSize - δ, s.bitSize)`. -/
  | shrink {δReg : Fin r} {x : Data r} :
      x.regs δReg ≤ x.bitSize →
      ExecCodeDistWithOracle w oracle (.shrink δReg) x
        (PMF.pure ⟨x.regs,
          (BitMemory.stepFn w x.toBitMemoryState (.shrink (x.regs δReg))).1.mem,
          x.bitSize - x.regs δReg⟩)
        ((max 1 ((x.regs δReg) ⌈/⌉ w) : ℕ) : ℝ≥0∞)
  /-- Reading `x.bitSize` into `dst` (when `Fits w x.bitSize`) costs `1` instruction unit. -/
  | size {dst : Fin r} {x : Data r} :
      Fits w x.bitSize →
      ExecCodeDistWithOracle w oracle (.size dst) x (PMF.pure (x.set dst x.bitSize)) 1
  /-- Uniform random sampling `.rand dst src` (when `Fits w (x.regs src)`) samples
  `v ∈ Fin (x.regs src + 1)` uniformly via `ProbComp.unifFin (x.regs src)` in `1` instruction unit,
  matching `BitRAM.stepRand`. -/
  | rand {dst src : Fin r} {x : Data r} :
      Fits w (x.regs src) →
      ExecCodeDistWithOracle w oracle (.rand dst src) x
        ((ProbComp.eval (ProbComp.unifFin (x.regs src))).map fun v => x.set dst v.val) 1
  /-- Cost weakening: if `c` executes within expected cost `t₁` and `t₁ ≤ t₂`, it executes within
  expected cost `t₂`. -/
  | mono {c : Code B r} {x : Data r} {μ : PMF (Data r)} {t₁ t₂ : ℝ≥0∞} :
      ExecCodeDistWithOracle w oracle c x μ t₁ →
      t₁ ≤ t₂ →
      ExecCodeDistWithOracle w oracle c x μ t₂
  /-- Sequential composition `c₁; c₂` adds `t₁` and the expected continuation cost
  `∑' y, μ y * t₂ y`. -/
  | seq {c₁ c₂ : Code B r} {x : Data r} {μ : PMF (Data r)} {f : Data r → PMF (Data r)}
      {t₁ : ℝ≥0∞} {t₂ : Data r → ℝ≥0∞} :
      ExecCodeDistWithOracle w oracle c₁ x μ t₁ →
      (∀ y ∈ μ.support, ExecCodeDistWithOracle w oracle c₂ y (f y) (t₂ y)) →
      (∀ y ∉ μ.support, t₂ y = 0) →
      ExecCodeDistWithOracle w oracle (.seq c₁ c₂) x (μ.bind f) (t₁ + ∑' y, μ y * t₂ y)
  /-- Positive conditional branch costs `1` instruction plus the `pos` body. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x : Data r} {μ : PMF (Data r)} {t : ℝ≥0∞} :
      CondHolds c x →
      ExecCodeDistWithOracle w oracle pos x μ t →
      ExecCodeDistWithOracle w oracle (.branch c pos neg) x μ (t + 1)
  /-- Negative conditional branch costs `2` instructions plus the `neg` body. -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x : Data r} {μ : PMF (Data r)} {t : ℝ≥0∞} :
      ¬CondHolds c x →
      ExecCodeDistWithOracle w oracle neg x μ t →
      ExecCodeDistWithOracle w oracle (.branch c pos neg) x μ (t + 2)
  /-- Loop exit costs `2` instructions. -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} :
      ¬CondHolds c x →
      ExecCodeDistWithOracle w oracle (.loop c body) x (PMF.pure x) 2
  /-- Loop iteration costs `2` instructions plus `body` and the remaining `.loop c body`. -/
  | loop_iter {c : Cond r} {body : Code B r} {x : Data r} {μ : PMF (Data r)}
      {f : Data r → PMF (Data r)} {t₁ : ℝ≥0∞} {t₂ : Data r → ℝ≥0∞} :
      CondHolds c x →
      ExecCodeDistWithOracle w oracle body x μ t₁ →
      (∀ y ∈ μ.support, ExecCodeDistWithOracle w oracle (.loop c body) y (f y) (t₂ y)) →
      (∀ y ∉ μ.support, t₂ y = 0) →
      ExecCodeDistWithOracle w oracle (.loop c body) x (μ.bind f) (t₁ + (∑' y, μ y * t₂ y) + 2)

namespace ExecCodeDistWithOracle

variable {w : ℕ} {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}

/-- Sequencing a deterministic prefix `c₁` (producing `PMF.pure y`) with `c₂`. -/
theorem seq_pure {c₁ c₂ : Code B r} {x y : Data r} {ν : PMF (Data r)} {t₁ t₂ : ℝ≥0∞}
    (h₁ : ExecCodeDistWithOracle w oracle c₁ x (PMF.pure y) t₁)
    (h₂ : ExecCodeDistWithOracle w oracle c₂ y ν t₂) :
    ExecCodeDistWithOracle w oracle (.seq c₁ c₂) x ν (t₁ + t₂) := by
  classical
  have h := ExecCodeDistWithOracle.seq (c₁ := c₁) (c₂ := c₂) h₁
    (f := fun z => if z = y then ν else PMF.pure z)
    (t₂ := fun z => if z = y then t₂ else 0)
    (by
      intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa only [↓reduceIte] using h₂)
    (by
      intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      simp [hz])
  simpa [PMF.pure_bind, tsum_ite_eq] using h

/-- One deterministic loop iteration (where `body` produces `PMF.pure y`) followed by the rest of
the loop. -/
theorem loop_iter_pure {c : Cond r} {body : Code B r} {x y : Data r} {ν : PMF (Data r)}
    {t₁ t₂ : ℝ≥0∞} (hc : CondHolds c x)
    (h₁ : ExecCodeDistWithOracle w oracle body x (PMF.pure y) t₁)
    (h₂ : ExecCodeDistWithOracle w oracle (.loop c body) y ν t₂) :
    ExecCodeDistWithOracle w oracle (.loop c body) x ν (t₁ + t₂ + 2) := by
  classical
  have h := ExecCodeDistWithOracle.loop_iter (c := c) (body := body) hc h₁
    (f := fun z => if z = y then ν else PMF.pure z)
    (t₂ := fun z => if z = y then t₂ else 0)
    (by
      intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa only [↓reduceIte] using h₂)
    (by
      intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      simp [hz])
  simpa [PMF.pure_bind, tsum_ite_eq] using h

end ExecCodeDistWithOracle

namespace DemonicExecWithin

variable {w : ℕ} {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}

/-- Any `.rand`-free structured program verified with `DemonicExecWithin w c x P T` evaluates
deterministically under any `DirtyGrowOracle w oracle` to `evalWithOracle w oracle fuel c x`
(for all `fuel ≥ T`), satisfying `P` and `ExecCodeDistWithOracle` with cost `(T : ℝ≥0∞)`. -/
theorem evalWithOracle_spec_of_le (horacle : DirtyGrowOracle w oracle)
    {c : Code B r} {x : Data r} {P : Data r → Prop} {T : ℕ}
    (h : DemonicExecWithin w c x P T) :
    P (evalWithOracle w oracle T c x) ∧
      ExecCodeDistWithOracle w oracle c x (PMF.pure (evalWithOracle w oracle T c x)) (T : ℝ≥0∞) ∧
      ∀ fuel ≥ T, evalWithOracle w oracle fuel c x = evalWithOracle w oracle T c x := by
  induction h with
  | @op o x y P T heval hp h1 =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalWithOracle, heval, hp]
    · simp only [evalWithOracle, heval, Option.getD_some]
      exact (ExecCodeDistWithOracle.op (w := w) heval).mono
        (t₂ := (T : ℝ≥0∞)) (by exact_mod_cast h1)
    · intro fuel _
      simp [evalWithOracle]
  | @grow dst δReg x P T hfits hcost hp =>
    have hstep := horacle x.mem x.bitSize (x.regs δReg)
    refine ⟨?_, ?_, ?_⟩
    · simpa [evalWithOracle] using hp _ hstep
    · simpa [evalWithOracle] using
        (ExecCodeDistWithOracle.grow (w := w) (oracle := oracle) hfits).mono
          (t₂ := (T : ℝ≥0∞)) (by exact_mod_cast hcost)
    · intro fuel _
      simp [evalWithOracle]
  | @shrink δReg x P T hle hcost hp =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [evalWithOracle] using hp
    · simpa [evalWithOracle] using
        (ExecCodeDistWithOracle.shrink (w := w) (oracle := oracle) hle).mono
          (t₂ := (T : ℝ≥0∞)) (by exact_mod_cast hcost)
    · intro fuel _
      simp [evalWithOracle]
  | @size dst x P T hfits hp h1 =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [evalWithOracle] using hp
    · simpa [evalWithOracle] using
        (ExecCodeDistWithOracle.size (w := w) (oracle := oracle) hfits).mono
          (t₂ := (T : ℝ≥0∞)) (by exact_mod_cast h1)
    · intro fuel _
      simp [evalWithOracle]
  | @seq c₁ c₂ x Q P T₁ T₂ T _ _ hsum ih₁ ih₂ =>
    obtain ⟨hq, hex₁, hfuel₁⟩ := ih₁
    obtain ⟨hp, hex₂, hfuel₂⟩ := ih₂ _ hq
    have hT₁ : T₁ ≤ T := by omega
    have hT₂ : T₂ ≤ T := by omega
    have heqT : evalWithOracle w oracle T (.seq c₁ c₂) x =
        evalWithOracle w oracle T₂ c₂ (evalWithOracle w oracle T₁ c₁ x) := by
      simp only [evalWithOracle, hfuel₁ T hT₁, hfuel₂ T hT₂]
    refine ⟨heqT ▸ hp, ?_, ?_⟩
    · rw [heqT]
      exact (ExecCodeDistWithOracle.seq_pure hex₁ hex₂).mono (by exact_mod_cast hsum)
    · intro fuel hfuel
      simp only [evalWithOracle, hfuel₁ fuel (by omega), hfuel₂ fuel (by omega), heqT]
  | @branch_pos cond pos neg x P T₀ T hc _ hsum ih =>
    obtain ⟨hp, hex, hfuel₀⟩ := ih
    have hT₀ : T₀ ≤ T := by omega
    have heqT : evalWithOracle w oracle T (.branch cond pos neg) x =
        evalWithOracle w oracle T₀ pos x := by
      simp [evalWithOracle, hc, hfuel₀ T hT₀]
    refine ⟨heqT ▸ hp, ?_, ?_⟩
    · rw [heqT]
      exact (ExecCodeDistWithOracle.branch_pos hc hex).mono (by exact_mod_cast hsum)
    · intro fuel hfuel
      simp [evalWithOracle, hc, hfuel₀ fuel (by omega), hfuel₀ T hT₀]
  | @branch_neg cond pos neg x P T₀ T hc _ hsum ih =>
    obtain ⟨hp, hex, hfuel₀⟩ := ih
    have hT₀ : T₀ ≤ T := by omega
    have heqT : evalWithOracle w oracle T (.branch cond pos neg) x =
        evalWithOracle w oracle T₀ neg x := by
      simp [evalWithOracle, hc, hfuel₀ T hT₀]
    refine ⟨heqT ▸ hp, ?_, ?_⟩
    · rw [heqT]
      exact (ExecCodeDistWithOracle.branch_neg hc hex).mono (by exact_mod_cast hsum)
    · intro fuel hfuel
      simp [evalWithOracle, hc, hfuel₀ fuel (by omega), hfuel₀ T hT₀]
  | @loop_exit cond body x P T hc hp h2 =>
    have heval_exit : ∀ f, evalWithOracle w oracle f (.loop cond body) x = x := by
      intro f
      cases f with
      | zero => simp [evalWithOracle]
      | succ f' => simp [evalWithOracle, hc]
    refine ⟨(heval_exit T).symm ▸ hp, ?_, ?_⟩
    · rw [heval_exit T]
      exact (ExecCodeDistWithOracle.loop_exit hc).mono (by exact_mod_cast h2)
    · intro fuel _
      rw [heval_exit fuel, heval_exit T]
  | @loop_iter cond body x Q P T₁ T₂ T hc _ _ hsum ih₁ ih₂ =>
    obtain ⟨hq, hex₁, hfuel₁⟩ := ih₁
    obtain ⟨hp, hex₂, hfuel₂⟩ := ih₂ _ hq
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    have hT₁ : T₁ ≤ T' := by omega
    have hT₂ : T₂ ≤ T' := by omega
    have heqT : evalWithOracle w oracle (T' + 1) (.loop cond body) x =
        evalWithOracle w oracle T₂ (.loop cond body) (evalWithOracle w oracle T₁ body x) := by
      simp only [evalWithOracle, hc, ↓reduceIte, hfuel₁ T' hT₁, hfuel₂ T' hT₂]
    refine ⟨heqT ▸ hp, ?_, ?_⟩
    · rw [heqT]
      exact (ExecCodeDistWithOracle.loop_iter_pure hc hex₁ hex₂).mono (by exact_mod_cast hsum)
    · intro fuel hfuel
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      simp only [evalWithOracle, hc, ↓reduceIte,
        hfuel₁ fuel' (by omega), hfuel₂ fuel' (by omega), heqT]

/-- Deterministic execution under `DirtyGrowOracle w oracle` extracted from `DemonicExecWithin`. -/
theorem evalWithOracle_spec (horacle : DirtyGrowOracle w oracle)
    {c : Code B r} {x : Data r} {P : Data r → Prop} {T : ℕ}
    (h : DemonicExecWithin w c x P T) :
    P (evalWithOracle w oracle T c x) ∧
      ExecCodeDistWithOracle w oracle c x
        (PMF.pure (evalWithOracle w oracle T c x)) (T : ℝ≥0∞) := by
  obtain ⟨hp, hex, _⟩ := h.evalWithOracle_spec_of_le horacle
  exact ⟨hp, hex⟩

end DemonicExecWithin

namespace ExecCodeDistWithOracle

variable {w : ℕ} {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)}

/-- Sequence a randomized program `c₁` with a deterministic continuation `c₂` verified via
`DemonicExecWithin`, without `Classical.choose`. -/
theorem seq_demonic_right (horacle : DirtyGrowOracle w oracle)
    {c₁ c₂ : Code B r} {x : Data r} {μ : PMF (Data r)} {t₁ : ℝ≥0∞}
    {P : Data r → Prop} {T₂ : ℕ}
    (h₁ : ExecCodeDistWithOracle w oracle c₁ x μ t₁)
    (h₂ : ∀ y ∈ μ.support, DemonicExecWithin w c₂ y P T₂) :
    let f : Data r → PMF (Data r) := fun y => PMF.pure (evalWithOracle w oracle T₂ c₂ y)
    ExecCodeDistWithOracle w oracle (.seq c₁ c₂) x (μ.bind f) (t₁ + (T₂ : ℝ≥0∞)) ∧
      ∀ z ∈ (μ.bind f).support, P z := by
  intro f
  classical
  have hseq := ExecCodeDistWithOracle.seq (c₁ := c₁) (c₂ := c₂) h₁ (f := f)
    (t₂ := fun y => if y ∈ μ.support then (T₂ : ℝ≥0∞) else 0)
    (by
      intro y hy
      simp only [hy, ↓reduceIte]
      exact ((h₂ y hy).evalWithOracle_spec horacle).2)
    (by
      intro y hy
      simp [hy])
  have htsum : (∑' y, μ y * (if y ∈ μ.support then (T₂ : ℝ≥0∞) else 0)) ≤ (T₂ : ℝ≥0∞) := by
    have hcongr : (fun y => μ y * (if y ∈ μ.support then (T₂ : ℝ≥0∞) else 0)) =
        fun y => μ y * (T₂ : ℝ≥0∞) := by
      ext y
      by_cases hy : y ∈ μ.support
      · simp [hy]
      · rw [PMF.mem_support_iff, not_not] at hy
        simp [hy]
    rw [hcongr, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  refine ⟨hseq.mono (add_le_add le_rfl htsum), ?_⟩
  intro z hz
  rw [PMF.mem_support_bind_iff] at hz
  obtain ⟨y, hy, hzy⟩ := hz
  rw [PMF.support_pure, Set.mem_singleton_iff] at hzy
  subst hzy
  exact ((h₂ y hy).evalWithOracle_spec horacle).1

/-- Sequence a deterministic program `c₁` verified via `DemonicExecWithin` with a randomized
continuation `c₂`, without `Classical.choose`. -/
theorem seq_demonic_left (horacle : DirtyGrowOracle w oracle)
    {c₁ c₂ : Code B r} {x : Data r} {Q : Data r → Prop} {T₁ : ℕ}
    {μ : Data r → PMF (Data r)} {t₂ : Data r → ℝ≥0∞}
    (h₁ : DemonicExecWithin w c₁ x Q T₁)
    (h₂ : ∀ y, Q y → ExecCodeDistWithOracle w oracle c₂ y (μ y) (t₂ y)) :
    let y₁ := evalWithOracle w oracle T₁ c₁ x
    Q y₁ ∧
      ExecCodeDistWithOracle w oracle (.seq c₁ c₂) x (μ y₁) ((T₁ : ℝ≥0∞) + t₂ y₁) := by
  intro y₁
  obtain ⟨hq₁, hex₁⟩ := h₁.evalWithOracle_spec horacle
  change Q y₁ at hq₁
  change ExecCodeDistWithOracle w oracle c₁ x (PMF.pure y₁) (T₁ : ℝ≥0∞) at hex₁
  have hex₂ := h₂ y₁ hq₁
  classical
  have hseq := ExecCodeDistWithOracle.seq (c₁ := c₁) (c₂ := c₂) hex₁
    (f := fun y => if y = y₁ then μ y₁ else PMF.pure y)
    (t₂ := fun y => if y = y₁ then t₂ y₁ else 0)
    (by
      intro y hy
      rw [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [↓reduceIte] using hex₂)
    (by
      intro y hy
      rw [PMF.support_pure, Set.mem_singleton_iff] at hy
      simp [hy])
  refine ⟨hq₁, ?_⟩
  simpa [PMF.pure_bind, tsum_ite_eq] using hseq

end ExecCodeDistWithOracle

namespace DemonicExecWithin

variable {w : ℕ}

/-- Loop rule with an indexed invariant `Inv : ℕ → Data r → Prop` and variable step costs
`T_step : ℕ → ℕ`. -/
theorem loop_invariant {cond : Cond r} {body : Code B r}
    (Inv : ℕ → Data r → Prop) (T_step : ℕ → ℕ)
    (h0 : ∀ z, Inv 0 z → ¬CondHolds cond z)
    (hstep : ∀ k z, Inv (k + 1) z →
      CondHolds cond z ∧ DemonicExecWithin w body z (Inv k) (T_step k)) :
    ∀ k z, Inv k z →
      DemonicExecWithin w (.loop cond body) z (Inv 0)
        (2 + ((List.range k).map (fun i => 2 + T_step i)).sum) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    exact .loop_exit (h0 z hz) hz (by simp)
  | succ k ih =>
    intro z hz
    obtain ⟨hc, hbody⟩ := hstep k z hz
    refine .loop_iter hc hbody (fun y hy => ih y hy) ?_
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    omega

/-- Loop rule with an indexed invariant `Inv : ℕ → Data r → Prop` and constant per-iteration step
bound `T₀`. -/
theorem loop_const {cond : Cond r} {body : Code B r}
    (Inv : ℕ → Data r → Prop) (T₀ : ℕ)
    (h0 : ∀ z, Inv 0 z → ¬CondHolds cond z)
    (hstep : ∀ k z, Inv (k + 1) z →
      CondHolds cond z ∧ DemonicExecWithin w body z (Inv k) T₀) :
    ∀ k z, Inv k z →
      DemonicExecWithin w (.loop cond body) z (Inv 0) (2 + k * (2 + T₀)) := by
  intro k z hz
  have h := loop_invariant Inv (fun _ => T₀) h0 hstep k z hz
  refine h.mono (fun _ h => h) ?_
  simp

end DemonicExecWithin

/-! ## Register preservation and register-bank embedding (`Code.rename`) -/

variable {r' : ℕ}

/-- Whether a `WordRAM.Op B r` preserves register `i : Fin r`. -/
def opPreserves (i : Fin r) : Op B r → Bool
  | .const d _ => d != i
  | .copy d _ => d != i
  | .alu _ d _ => d != i
  | .load d _ => d != i
  | .store _ _ => true

/-- Whether a `BitRAM.Code B r` syntactically preserves register `i : Fin r` (never writes to
`i`). -/
def Code.preserves (i : Fin r) : Code B r → Bool
  | .op o => opPreserves i o
  | .grow dst _ => dst != i
  | .shrink _ => true
  | .size dst => dst != i
  | .seq c₁ c₂ => c₁.preserves i && c₂.preserves i
  | .branch _ pos neg => pos.preserves i && neg.preserves i
  | .loop _ body => body.preserves i
  | .rand dst _ => dst != i

theorem evalOp_regs_of_opPreserves {w : ℕ} {o : Op B r} {x y : Data r} {i : Fin r}
    (hp : opPreserves i o = true) (heval : evalOp w o x = some y) :
    y.regs i = x.regs i := by
  cases o with
  | const d v =>
    have hne : d ≠ i := by simpa [opPreserves] using hp
    simp only [evalOp, Data.put] at heval
    split_ifs at heval with hfits
    injection heval with hy
    subst hy
    simp [Data.set, Function.update_of_ne hne.symm]
  | copy d s =>
    have hne : d ≠ i := by simpa [opPreserves] using hp
    injection heval with hy
    subst hy
    simp [Data.set, Function.update_of_ne hne.symm]
  | alu f d args =>
    have hne : d ≠ i := by simpa [opPreserves] using hp
    change (B.interp w f (x.regs ∘ args)).bind (Data.put w x d) = some y at heval
    cases h : B.interp w f (x.regs ∘ args) with
    | none => simp [h] at heval
    | some val =>
      rw [h] at heval
      change Data.put w x d val = some y at heval
      simp only [Data.put] at heval
      split_ifs at heval with hfits
      injection heval with hy
      subst hy
      simp [Data.set, Function.update_of_ne hne.symm]
  | load d a =>
    have hne : d ≠ i := by simpa [opPreserves] using hp
    simp only [evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    simp [Data.set, Function.update_of_ne hne.symm]
  | store a s =>
    simp only [evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    rfl

/-- Augment any `DemonicExecWithin` derivation with preservation of all registers `i` satisfying
`c.preserves i = true`. -/
theorem DemonicExecWithin.with_preserves {w : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {T : ℕ}
    (h : DemonicExecWithin w c x P T) :
    DemonicExecWithin w c x
      (fun y => P y ∧ ∀ i : Fin r, c.preserves i = true → y.regs i = x.regs i) T := by
  induction h with
  | @op o x y P T heval hp h1 =>
    refine .op heval ⟨hp, fun i hi => evalOp_regs_of_opPreserves hi heval⟩ h1
  | @grow dst δReg x P T hfits hcost hp =>
    refine .grow hfits hcost fun s' hs' => ⟨hp s' hs', fun i hi => ?_⟩
    have hne : dst ≠ i := by simpa [Code.preserves] using hi
    exact Function.update_of_ne hne.symm _ _
  | @shrink δReg x P T hle hcost hp =>
    exact .shrink hle hcost ⟨hp, fun _ _ => rfl⟩
  | @size dst x P T hfits hp h1 =>
    refine .size hfits ⟨hp, fun i hi => ?_⟩ h1
    have hne : dst ≠ i := by simpa [Code.preserves] using hi
    simp [Data.set, Function.update_of_ne hne.symm]
  | @seq c₁ c₂ x Q P T₁ T₂ T _ _ hsum ih₁ ih₂ =>
    refine .seq ih₁ (fun y₁ ⟨hq₁, hpres₁⟩ => ?_) hsum
    refine (ih₂ y₁ hq₁).mono (fun y₂ ⟨hp₂, hpres₂⟩ => ⟨hp₂, fun i hi => ?_⟩) le_rfl
    simp only [Code.preserves, Bool.and_eq_true] at hi
    exact (hpres₂ i hi.2).trans (hpres₁ i hi.1)
  | @branch_pos cond pos neg x P T₀ T hc _ hsum ih =>
    refine .branch_pos hc (ih.mono (fun y ⟨hp, hpres⟩ => ⟨hp, fun i hi => ?_⟩) le_rfl) hsum
    simp only [Code.preserves, Bool.and_eq_true] at hi
    exact hpres i hi.1
  | @branch_neg cond pos neg x P T₀ T hc _ hsum ih =>
    refine .branch_neg hc (ih.mono (fun y ⟨hp, hpres⟩ => ⟨hp, fun i hi => ?_⟩) le_rfl) hsum
    simp only [Code.preserves, Bool.and_eq_true] at hi
    exact hpres i hi.2
  | @loop_exit cond body x P T hc hp h1 =>
    exact .loop_exit hc ⟨hp, fun _ _ => rfl⟩ h1
  | @loop_iter cond body x Q P T₁ T₂ T hc _ _ hsum ih₁ ih₂ =>
    refine .loop_iter hc ih₁ (fun y₁ ⟨hq₁, hpres₁⟩ => ?_) hsum
    refine (ih₂ y₁ hq₁).mono (fun y₂ ⟨hp₂, hpres₂⟩ => ⟨hp₂, fun i hi => ?_⟩) le_rfl
    exact (hpres₂ i hi).trans (hpres₁ i hi)

/-- Project `Data r'` onto `Data r` along `f : Fin r → Fin r'`. -/
def Data.comap (f : Fin r → Fin r') (x : Data r') : Data r where
  regs := x.regs ∘ f
  mem := x.mem
  bitSize := x.bitSize

/-- Extend `y : Data r` back into `x : Data r'` along `f : Fin r → Fin r'`. -/
noncomputable def Data.extend (f : Fin r → Fin r') (y : Data r) (x : Data r') : Data r' where
  regs := Function.extend f y.regs x.regs
  mem := y.mem
  bitSize := y.bitSize

/-- Rename registers in a `BitRAM.Code B r` along `f : Fin r → Fin r'`. -/
def Code.rename (f : Fin r → Fin r') : Code B r → Code B r'
  | .op o => .op (o.rename f)
  | .grow dst δReg => .grow (f dst) (f δReg)
  | .shrink δReg => .shrink (f δReg)
  | .size dst => .size (f dst)
  | .seq c₁ c₂ => .seq (c₁.rename f) (c₂.rename f)
  | .branch c pos neg => .branch (c.rename f) (pos.rename f) (neg.rename f)
  | .loop c body => .loop (c.rename f) (body.rename f)
  | .rand dst src => .rand (f dst) (f src)

/-- Canonical embedding `Fin 12 → Fin r` when `12 ≤ r`. -/
def embedFin12 {r : ℕ} (hr : 12 ≤ r) (i : Fin 12) : Fin r :=
  Fin.castLE hr i

theorem injective_embedFin12 {r : ℕ} (hr : 12 ≤ r) :
    Function.Injective (embedFin12 hr) :=
  Fin.castLE_injective hr

/-- Embed a 12-register `BitRAM.Code B 12` (such as `readBitsCode` or `writeBitsCode`) into
`BitRAM.Code B r` (`12 ≤ r`). -/
def Code.embed12 {r : ℕ} (hr : 12 ≤ r) (c : Code B 12) : Code B r :=
  c.rename (embedFin12 hr)

@[simp]
theorem comap_extend {f : Fin r → Fin r'} (hf : Function.Injective f)
    (y : Data r) (x : Data r') :
    (y.extend f x).comap f = y := by
  ext i : 2
  · exact hf.extend_apply y.regs x.regs i
  · rfl
  · rfl

theorem evalOp_rename {w : ℕ} {f : Fin r → Fin r'} (hf : Function.Injective f)
    {o : Op B r} {x : Data r'} {y : Data r}
    (heval : evalOp w o (x.comap f) = some y) :
    evalOp w (o.rename f) x = some (y.extend f x) := by
  have hupdate : ∀ (d : Fin r) (v : ℕ),
      Function.update x.regs (f d) v =
        Function.extend f (Function.update (x.regs ∘ f) d v) x.regs := by
    intro d v
    ext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hf.extend_apply]
      by_cases hid : i = d
      · subst hid; simp
      · have hne : f i ≠ f d := fun h => hid (hf h)
        simp [Function.update_of_ne hid, Function.update_of_ne hne]
    · have hne : j ≠ f d := fun h => hj ⟨d, h.symm⟩
      rw [Function.extend_apply' _ _ _ hj, Function.update_of_ne hne]
  cases o with
  | const d v =>
    simp only [Op.rename, evalOp, Data.put, Data.comap] at heval ⊢
    split_ifs at heval with hfits
    injection heval with hy
    subst hy
    simp [hfits, Data.set, Data.extend, hupdate d v]
  | copy d s =>
    injection heval with hy
    subst hy
    simp [Op.rename, evalOp, Data.set, Data.comap, Data.extend, hupdate d (x.regs (f s))]
  | alu fn d args =>
    have hcomp : (x.comap f).regs ∘ args = x.regs ∘ f ∘ args := rfl
    change (B.interp w fn ((x.comap f).regs ∘ args)).bind (Data.put w (x.comap f) d) = some y
      at heval
    change (B.interp w fn (x.regs ∘ f ∘ args)).bind (Data.put w x (f d)) = some (y.extend f x)
    rw [hcomp] at heval
    cases h : B.interp w fn (x.regs ∘ f ∘ args) with
    | none => simp [h] at heval
    | some val =>
      rw [h] at heval
      change Data.put w (x.comap f) d val = some y at heval
      change Data.put w x (f d) val = some (y.extend f x)
      simp only [Data.put, Data.comap] at heval ⊢
      split_ifs at heval with hfits
      injection heval with hy
      subst hy
      simp [hfits, Data.set, Data.extend, hupdate d val]
  | load d a =>
    change (if x.regs (f a) < x.wordSize w then
        some ((x.comap f).set d (x.mem (x.regs (f a))))
      else none) = some y at heval
    change (if x.regs (f a) < x.wordSize w then
        some (x.set (f d) (x.mem (x.regs (f a))))
      else none) = some (y.extend f x)
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    simp [hadm, Data.set, Data.comap, Data.extend, hupdate d (x.mem (x.regs (f a)))]
  | store a s =>
    change (if x.regs (f a) < x.wordSize w then
        some ((x.comap f).write (x.regs (f a)) (x.regs (f s)))
      else none) = some y at heval
    change (if x.regs (f a) < x.wordSize w then
        some (x.write (x.regs (f a)) (x.regs (f s)))
      else none) = some (y.extend f x)
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    have hext : Function.extend f (x.regs ∘ f) x.regs = x.regs := by
      ext j
      by_cases hj : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := hj; rw [hf.extend_apply]; rfl
      · rw [Function.extend_apply' _ _ _ hj]
    simp [hadm, Data.write, Data.comap, Data.extend, hext]

theorem condHolds_rename {f : Fin r → Fin r'} (c : Cond r) (x : Data r') :
    CondHolds (c.rename f) x ↔ CondHolds c (x.comap f) := by
  cases c <;> rfl

/-- Lift a `DemonicExecWithin` derivation on `Data r` along any injective register map
`f : Fin r → Fin r'`. -/
theorem DemonicExecWithin.rename {w : ℕ} {f : Fin r → Fin r'} (hf : Function.Injective f)
    {c : Code B r} {x : Data r'} {P : Data r → Prop} {T : ℕ}
    (h : DemonicExecWithin w c (x.comap f) P T) :
    DemonicExecWithin w (c.rename f) x
      (fun y => P (y.comap f) ∧ ∀ j : Fin r', (∀ i : Fin r, f i ≠ j) → y.regs j = x.regs j) T := by
  generalize hx₀ : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o x₀ y₀ P T heval hp h1 =>
    subst hx₀
    refine .op (evalOp_rename hf heval) ⟨by simp [hf, hp], fun j hj => ?_⟩ h1
    have hnot : ¬∃ i, f i = j := fun ⟨i, hi⟩ => hj i hi
    exact Function.extend_apply' _ _ _ hnot
  | @grow dst δReg x₀ P T hfits hcost hp =>
    subst hx₀
    refine .grow hfits hcost fun s' hs' => ?_
    let y₀ : Data r := ⟨Function.update (x.regs ∘ f) dst x.bitSize, s'.mem, s'.bitSize⟩
    let y : Data r' := ⟨Function.update x.regs (f dst) x.bitSize, s'.mem, s'.bitSize⟩
    have hcomap : y.comap f = y₀ := by
      ext i : 2
      · change Function.update x.regs (f dst) x.bitSize (f i) =
          Function.update (x.regs ∘ f) dst x.bitSize i
        by_cases hid : i = dst
        · subst hid; simp
        · have hne : f i ≠ f dst := fun h => hid (hf h)
          rw [Function.update_of_ne hne, Function.update_of_ne hid]
          rfl
      · rfl
      · rfl
    refine ⟨hcomap.symm ▸ hp s' hs', fun j hj => ?_⟩
    exact Function.update_of_ne (hj dst).symm _ _
  | @shrink δReg x₀ P T hle hcost hp =>
    subst hx₀
    exact .shrink hle hcost ⟨hp, fun _ _ => rfl⟩
  | @size dst x₀ P T hfits hp h1 =>
    subst hx₀
    refine .size hfits ⟨?_, fun j hj => ?_⟩ h1
    · have hcomap : (x.set (f dst) x.bitSize).comap f = (x.comap f).set dst x.bitSize := by
        ext i : 2
        · change Function.update x.regs (f dst) x.bitSize (f i) =
            Function.update (x.regs ∘ f) dst x.bitSize i
          by_cases hid : i = dst
          · subst hid; simp
          · have hne : f i ≠ f dst := fun h => hid (hf h)
            rw [Function.update_of_ne hne, Function.update_of_ne hid]
            rfl
        · rfl
        · rfl
      rw [hcomap]
      exact hp
    · exact Function.update_of_ne (hj dst).symm _ _
  | @seq c₁ c₂ x₀ Q P T₁ T₂ T _ _ hsum ih₁ ih₂ =>
    subst hx₀
    refine .seq (ih₁ rfl) (fun y₁ ⟨hq₁, hpres₁⟩ => ?_) hsum
    refine (ih₂ (y₁.comap f) hq₁ rfl).mono (fun y₂ ⟨hp₂, hpres₂⟩ => ⟨hp₂, fun j hj => ?_⟩) le_rfl
    exact (hpres₂ j hj).trans (hpres₁ j hj)
  | @branch_pos cond pos neg x₀ P T₀ T hc _ hsum ih =>
    subst hx₀
    have hc' : CondHolds (cond.rename f) x := (condHolds_rename cond x).mpr hc
    exact .branch_pos hc' (ih rfl) hsum
  | @branch_neg cond pos neg x₀ P T₀ T hc _ hsum ih =>
    subst hx₀
    have hc' : ¬CondHolds (cond.rename f) x := fun h => hc ((condHolds_rename cond x).mp h)
    exact .branch_neg hc' (ih rfl) hsum
  | @loop_exit cond body x₀ P T hc hp h1 =>
    subst hx₀
    have hc' : ¬CondHolds (cond.rename f) x := fun h => hc ((condHolds_rename cond x).mp h)
    exact .loop_exit hc' ⟨hp, fun _ _ => rfl⟩ h1
  | @loop_iter cond body x₀ Q P T₁ T₂ T hc _ _ hsum ih₁ ih₂ =>
    subst hx₀
    have hc' : CondHolds (cond.rename f) x := (condHolds_rename cond x).mpr hc
    refine .loop_iter hc' (ih₁ rfl) (fun y₁ ⟨hq₁, hpres₁⟩ => ?_) hsum
    refine (ih₂ (y₁.comap f) hq₁ rfl).mono (fun y₂ ⟨hp₂, hpres₂⟩ => ⟨hp₂, fun j hj => ?_⟩) le_rfl
    exact (hpres₂ j hj).trans (hpres₁ j hj)

/-- Lift a 12-register `DemonicExecWithin` derivation to `Data r` (`12 ≤ r`), preserving all
registers `j` with `12 ≤ j.val`. -/
theorem DemonicExecWithin.embed12 {w r : ℕ} (hr : 12 ≤ r)
    {c : Code B 12} {x : Data r} {P : Data 12 → Prop} {T : ℕ}
    (h : DemonicExecWithin w c (x.comap (embedFin12 hr)) P T) :
    DemonicExecWithin w (Code.embed12 hr c) x
      (fun y => P (y.comap (embedFin12 hr)) ∧ ∀ j : Fin r, 12 ≤ j.val → y.regs j = x.regs j) T := by
  refine (h.rename (injective_embedFin12 hr)).mono (fun y hy => ⟨hy.1, fun j hj => ?_⟩) le_rfl
  refine hy.2 j (fun i hi => ?_)
  have : (embedFin12 hr i).val = i.val := rfl
  have : i.val < 12 := i.isLt
  omega

end Cslib.WordRAM.BitRAM
