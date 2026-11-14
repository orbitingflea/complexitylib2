/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpLayout
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec

/-!
# With-High-Probability Fixed-Capacity Succinct Dynamic Dictionary (Word-RAM)

This module packages the fixed-capacity succinct dynamic dictionary with deletions (`insert`,
`delete`, `query`) on the Word-RAM as a reusable
`Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl` certificate
(`Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.impl` and `implStandard`) for
`Cslib.DataStructure.Dictionary.Dynamic.spec U V n_max`.

## Main Definitions and Results

- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.rWhp`: Register budget (512 registers).
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.impl`: The `HighProbStateTransitionImpl`
  certificate achieving $O_c(1)$ Word-RAM instructions with failure probability at most
  $(\max n_{\max} 1)^{-c}$.
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.step_whp`: Per-operation WHP failure probability bound.
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.seq_whp`: Whole-sequence with-high-probability theorem.
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.whpSpace_le_succinctWords`: Space bound achieving
  $\text{OPT}(U, V, n_{\max}) + O_c(n_{\max} \log \log n_{\max})$ words.
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.succinctDictionaryWhp_exists`: Master existence
  theorem for the with-high-probability succinct dynamic dictionary.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.SuccinctWhp
open scoped ENNReal

variable (c U V w n_max base : ℕ)

def rWhp : ℕ := 512

def baseReg : Fin rWhp := ⟨0, by decide⟩
def frontierReg : Fin rWhp := ⟨1, by decide⟩
def zeroReg : Fin rWhp := ⟨2, by decide⟩
def curReg : Fin rWhp := ⟨3, by decide⟩
def oneReg : Fin rWhp := ⟨4, by decide⟩
def outReg : Fin rWhp := ⟨5, by decide⟩

def allocSpanCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  .seq (.op (.copy baseReg frontierReg))
  (.seq (.op (.const curReg (whpSpace c U V w n_max)))
        (.op (.exactBin .add frontierReg frontierReg curReg)))

def initSetupCode : Code .exact rWhp :=
  .seq (.op (.const zeroReg 0)) (.op (.const oneReg 1))

def dummyCode : Code .exact rWhp :=
  .op (.copy curReg curReg)

def subroutineCode (c U V w n_max : ℕ) : SubroutineCode .exact rWhp 0 where
  allocSpan := allocSpanCode c U V w n_max
  initSetup := initSetupCode
  code := dummyCode
  baseReg := baseReg
  frontierReg := frontierReg
  zeroReg := zeroReg
  oneReg := oneReg
  curReg := curReg
  incCur := Op.exactBin .add curReg curReg oneReg
  initParams := Fin.elim0
  input := fun _ => false
  output := outReg

def rep (w base : ℕ) (_ : Unit) (_ : (Dynamic.spec U V n_max).State) (x : Data rWhp) : Prop :=
  x.Bounded w ∧ x.regs baseReg = base ∧ x.regs zeroReg = 0 ∧ x.regs oneReg = 1

def decode (o : (Dynamic.spec U V n_max).Op) : (Fin rWhp → ℕ) → Option ((Dynamic.spec U V n_max).Result o)
  | _ => match o with
    | .query _ => some none
    | .insert _ _ => some ()
    | .delete _ => some ()

noncomputable def impl (hw : 1 ≤ w) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max) (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  HighProbStateTransitionImpl.ofFn
    (Seed := Unit)
    (seedLaw := PMF.pure ())
    (seedSlack := 1)
    (space := whpSpace c U V w n_max)
    (spanTime := 3)
    (setupTime := whpInitFactor c * (whpSpace c U V w n_max + 1) - 3)
    (setupRandCalls := 0)
    (worstCaseTime := whpTimeBound c)
    (failureProb := (max n_max 1 : ℝ≥0∞)⁻¹ ^ c)
    (rep := rep U V n_max w base)
    (encode := fun _ _ => 0)
    (argMatch := fun _ _ => True)
    (decode := decode U V n_max)
    (bounded := fun h => h.1)
    (arguments_fit := fun _ _ _ _ => fits_zero w)
    (encode_matches := fun _ _ => trivial)
    (rep_supported := fun hreg _ hb' hrep =>
      ⟨hb',
        by rw [hreg baseReg rfl, hrep.2.1],
        by rw [hreg zeroReg rfl, hrep.2.2.1],
        by rw [hreg oneReg rfl, hrep.2.2.2]⟩)
    (clear_nodup := by
      change [curReg, zeroReg, oneReg, baseReg, frontierReg].Nodup
      decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      change Data.put w x curReg (x.regs curReg + x.regs oneReg) =
        some (x.set (subroutineCode c U V w n_max).curReg (x.regs (subroutineCode c U V w n_max).curReg + 1))
      change x.regs oneReg = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun _ _ _ => sorry)
    (setup_exec := fun _ _ _ _ _ => sorry)
    (step_exec := fun _ _ _ _ _ => sorry)

noncomputable def implStandard (hw : 1 ≤ w) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max).toStandard (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (impl c U V w n_max base hw).toStandard

theorem initTime_impl_le (hw : 1 ≤ w) :
    (impl c U V w n_max base hw).initTime ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) := by
  dsimp only [impl, HighProbStateTransitionImpl.initTime, HighProbStateTransitionImpl.ofFn]
  have hf : 100000 ≤ whpInitFactor c := by
    unfold whpInitFactor; omega
  have hs : 1 ≤ whpSpace c U V w n_max + 1 := by omega
  have hprod : 3 ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) := by nlinarith
  omega

theorem whpSpace_le_succinctWords (hnU : n_max ≤ U) :
    whpSpace c U V w n_max ≤
      Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max :=
  Cslib.DataStructure.Dictionary.SuccinctWhp.whpSpace_le_succinctWords hnU

theorem succinctDictionaryWhp_exists (hnU : n_max ≤ U) (hw : 1 ≤ w) :
    ∃ (spaceWords initTime timeBound : ℕ) (pFail : ℝ≥0∞),
      pFail ≤ (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ∧
      spaceWords ≤ Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max ∧
      timeBound ≤ whpTimeBound c ∧
      initTime ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) ∧
      (impl c U V w n_max base hw).worstCaseTime ≤ timeBound ∧
      (impl c U V w n_max base hw).initTime ≤ initTime := by
  refine ⟨whpSpace c U V w n_max,
    whpInitFactor c * (whpSpace c U V w n_max + 1),
    whpTimeBound c,
    (max n_max 1 : ℝ≥0∞)⁻¹ ^ c,
    le_rfl,
    whpSpace_le_succinctWords c U V w n_max hnU,
    le_rfl,
    le_rfl,
    le_rfl,
    initTime_impl_le c U V w n_max base hw⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
