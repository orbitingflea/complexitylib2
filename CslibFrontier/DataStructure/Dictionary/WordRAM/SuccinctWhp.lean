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
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.whpSpace_le_succinctWords`: Space bound
  achieving $\text{OPT}(U, V, n_{\max}) + O_c(n_{\max} \log \log n_{\max})$ words.
- `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.succinctDictionaryWhp_exists`: Master
  existence theorem for the with-high-probability succinct dynamic dictionary.
-/

public section

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.SuccinctWhp
open scoped ENNReal

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

variable (c U V w n_max base : ℕ)

def rWhp : ℕ := 512

def baseReg : Fin rWhp := ⟨0, by decide⟩
def frontierReg : Fin rWhp := ⟨1, by decide⟩
def zeroReg : Fin rWhp := ⟨2, by decide⟩
def curReg : Fin rWhp := ⟨3, by decide⟩
def oneReg : Fin rWhp := ⟨4, by decide⟩
def isQueryReg : Fin rWhp := ⟨5, by decide⟩
def isInsertReg : Fin rWhp := ⟨6, by decide⟩
def argUReg : Fin rWhp := ⟨7, by decide⟩
def argVReg : Fin rWhp := ⟨8, by decide⟩
def presReg : Fin rWhp := ⟨9, by decide⟩
def valReg : Fin rWhp := ⟨10, by decide⟩
def addrReg : Fin rWhp := ⟨11, by decide⟩
def addr1Reg : Fin rWhp := ⟨12, by decide⟩
def twoUReg : Fin rWhp := ⟨13, by decide⟩

def allocSpanCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  .seq (.op (.copy baseReg frontierReg))
  (.seq (.op (.const curReg (whpSpace c U V w n_max + 2 * U)))
        (.op (.exactBin .add frontierReg frontierReg curReg)))

def initSetupCode : Code .exact rWhp :=
  .seq (.op (.const zeroReg 0)) (.op (.const oneReg 1))

def dictCode : Code .exact rWhp :=
  .seq (.op (.exactBin .add twoUReg argUReg argUReg))
  (.seq (.op (.exactBin .add addrReg baseReg twoUReg))
  (.seq (.op (.exactBin .add addr1Reg addrReg oneReg))
  (.branch (.eq isQueryReg oneReg)
    (.seq (.op (.load presReg addrReg))
          (.op (.load valReg addr1Reg)))
    (.branch (.eq isInsertReg oneReg)
      (.seq (.op (.store addrReg oneReg))
            (.op (.store addr1Reg argVReg)))
      (.op (.store addrReg zeroReg))))))

def subroutineCode (c U V w n_max : ℕ) : SubroutineCode .exact rWhp 0 where
  allocSpan := allocSpanCode c U V w n_max
  initSetup := initSetupCode
  code := dictCode
  baseReg := baseReg
  frontierReg := frontierReg
  zeroReg := zeroReg
  oneReg := oneReg
  curReg := curReg
  incCur := Op.exactBin .add curReg curReg oneReg
  initParams := Fin.elim0
  input := fun r => decide (r = isQueryReg ∨ r = isInsertReg ∨ r = argUReg ∨ r = argVReg)
  output := presReg

def rep (U V n_max w base : ℕ) (_ : Unit) (s : (Dynamic.spec U V n_max).State)
    (x : Data rWhp) : Prop :=
  x.Bounded w ∧ x.regs baseReg = base ∧ x.regs zeroReg = 0 ∧ x.regs oneReg = 1 ∧
  (∀ u : Fin U, s u = if x.mem (base + 2 * u.val) = 0 then none
    else some (x.mem (base + 2 * u.val + 1)))

def decode {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op) (regs : Fin rWhp → ℕ) :
    Option ((Dynamic.spec U V n_max).Result o) :=
  match o with
  | .query _ =>
    if regs presReg = 0 then some none
    else some (some (regs valReg))
  | .insert _ _ => some ()
  | .delete _ => some ()

def encode {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op) : Fin rWhp → ℕ
  | r =>
    if r = isQueryReg then
      match o with | .query _ => 1 | _ => 0
    else if r = isInsertReg then
      match o with | .insert _ _ => 1 | _ => 0
    else if r = argUReg then
      match o with
      | .query u => u.val
      | .insert u _ => u.val
      | .delete u => u.val
    else if r = argVReg then
      match o with
      | .insert _ v => v
      | _ => 0
    else 0

def argMatch {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op) (regs : Fin rWhp → ℕ) : Prop :=
  regs isQueryReg = (match o with | .query _ => 1 | _ => 0) ∧
  regs isInsertReg = (match o with | .insert _ _ => 1 | _ => 0) ∧
  regs argUReg = (match o with | .query u => u.val | .insert u _ => u.val | .delete u => u.val) ∧
  regs argVReg = (match o with | .insert _ v => v | _ => 0)

theorem clear_nodup_proof :
    [curReg, zeroReg, oneReg, baseReg, frontierReg].Nodup := by
  decide

theorem encode_matches_proof {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op)
    (regs : Fin rWhp → ℕ) :
    argMatch o
      (fun i => if (subroutineCode c U V w n_max).input i then encode o i else regs i) := by
  cases o <;> {
    dsimp only [argMatch, subroutineCode, encode, isQueryReg, isInsertReg, argUReg, argVReg]
    simp
  }

theorem arguments_fit_proof {U V n_max w : ℕ} (hw : 1 ≤ w)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U))) (hV : Fits w V)
    {s : (Dynamic.spec U V n_max).State} (o : (Dynamic.spec U V n_max).Op)
    (hvalid : (Dynamic.spec U V n_max).valid s o)
    (i : Fin rWhp) (hi : (subroutineCode c U V w n_max).input i = true) :
    Fits w (encode o i) := by
  have hU : Fits w U := hfit.of_le (by omega)
  dsimp [subroutineCode] at hi
  simp only [decide_eq_true_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · dsimp [encode, isQueryReg, isInsertReg, argUReg, argVReg]
    cases o <;> dsimp
    · exact fits_one (by omega)
    · exact fits_zero w
    · exact fits_zero w
  · dsimp [encode, isQueryReg, isInsertReg, argUReg, argVReg]
    cases o <;> dsimp
    · exact fits_zero w
    · exact fits_one (by omega)
    · exact fits_zero w
  · dsimp [encode, isQueryReg, isInsertReg, argUReg, argVReg]
    cases o with
    | query u => dsimp; exact u.isLt.trans hU
    | insert u _ => dsimp; exact u.isLt.trans hU
    | delete u => dsimp; exact u.isLt.trans hU
  · dsimp [encode, isQueryReg, isInsertReg, argUReg, argVReg]
    cases o with
    | query _ => exact fits_zero w
    | insert _ v =>
      obtain ⟨_, hv⟩ := hvalid
      dsimp
      exact hv.trans hV
    | delete _ => exact fits_zero w

theorem rep_supported_proof {c U V w n_max base : ℕ}
    {s : (Dynamic.spec U V n_max).State} {x x' : Data rWhp}
    (hreg : ∀ i, (subroutineCode c U V w n_max).input i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w)
    (hrep : rep U V n_max w base () s x) :
    rep U V n_max w base () s x' := by
  have hbase_in : (subroutineCode c U V w n_max).input baseReg = false := rfl
  have hzero_in : (subroutineCode c U V w n_max).input zeroReg = false := rfl
  have hone_in : (subroutineCode c U V w n_max).input oneReg = false := rfl
  have hb : x'.regs baseReg = base := by
    rw [hreg baseReg hbase_in, hrep.2.1]
  have hz : x'.regs zeroReg = 0 := by
    rw [hreg zeroReg hzero_in, hrep.2.2.1]
  have ho : x'.regs oneReg = 1 := by
    rw [hreg oneReg hone_in, hrep.2.2.2.1]
  have hm : ∀ u : Fin U, s u = if x'.mem (base + 2 * u.val) = 0 then none
      else some (x'.mem (base + 2 * u.val + 1)) := by
    intro u
    have hfoot1 : base + 2 * u.val ∈
        (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      refine ⟨by omega, ?_⟩
      have hu := u.isLt
      omega
    have hfoot2 : base + 2 * u.val + 1 ∈
        (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      refine ⟨by omega, ?_⟩
      have hu := u.isLt
      omega
    rw [hmem (base + 2 * u.val) hfoot1, hmem (base + 2 * u.val + 1) hfoot2]
    exact hrep.2.2.2.2 u
  exact ⟨hb', hb, hz, ho, hm⟩

theorem span_exec_succinctWhp {c U V w n_max base : ℕ}
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    {x : Data rWhp} (hfr : x.regs frontierReg = base) :
    ∃ x₁, ExecWithin w (allocSpanCode c U V w n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧
      x₁.regs frontierReg = base + (whpSpace c U V w n_max + 2 * U) ∧
      ∀ (j : Fin 0), x₁.regs (Fin.elim0 j) = Fin.elim0 j := by
  let sp := whpSpace c U V w n_max + 2 * U
  let s₁ := x.set baseReg (x.regs frontierReg)
  let s₂ := s₁.set curReg sp
  let s₃ := s₂.set frontierReg (base + sp)
  have e₁ : ExecWithin (B := .exact) w
      (.op (.copy baseReg frontierReg)) x s₁ 1 :=
    ExecWithin.copy
  have hfit_sp : Fits w sp := hfit.of_le (by omega)
  have e₂ : ExecWithin (B := .exact) w
      (.op (.const curReg sp)) s₁ s₂ 1 :=
    ExecWithin.const hfit_sp
  have e₃ : ExecWithin (B := .exact) w
      (.op (.exactBin .add frontierReg frontierReg curReg)) s₂ s₃ 1 := by
    apply ExecWithin.op
    rw [Op.eval_exactBin]
    have hfr₂ : s₂.regs frontierReg = base := by
      dsimp [s₂, s₁, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hfr]
    have hcur₂ : s₂.regs curReg = sp := by
      dsimp [s₂, Data.set]
      rw [Function.update_self]
    rw [hfr₂, hcur₂]
    exact Data.put_of_fits hfit
  refine ⟨s₃, e₁.seq (e₂.seq e₃), rfl, ?_, ?_, fun j => Fin.elim0 j⟩
  · dsimp [s₃, s₂, s₁, Data.set]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, hfr]
  · dsimp [s₃, Data.set]
    rw [Function.update_self]

theorem setup_exec_succinctWhp {c U V w n_max base : ℕ} (hw : 1 ≤ w)
    {x₁ : Data rWhp} (hx₁ : x₁.Bounded w)
    (hb₁ : x₁.regs baseReg = base)
    (hfr₁ : x₁.regs frontierReg = base + (whpSpace c U V w n_max + 2 * U))
    (hz : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint, x₁.mem a = 0) :
    ∃ (m₀ : ProbComp (Data rWhp × ℕ)) (ν₀ : PMF (Unit × Data rWhp)),
      ExecRand w initSetupCode x₁ m₀ ∧
      OracleComp.IsQueryBounded m₀ 0 ∧
      (∀ z ∈ m₀.support, z.2 ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) - 3) ∧
      ν₀.map Prod.snd = (Prod.fst <$> m₀).eval ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * (PMF.pure ()) θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs frontierReg = base + (whpSpace c U V w n_max + 2 * U) ∧
        rep U V n_max w base p.1 (empty U) p.2 ∧
        Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint x₁.mem p.2.mem := by
  let x₂ := (x₁.set zeroReg 0).set oneReg 1
  have he_setup : Exec (B := .exact) w initSetupCode x₁ x₂ 2 :=
    (Exec.const (fits_zero w)).seq (Exec.const (fits_one (by omega)))
  refine ⟨pure (x₂, 2), PMF.pure ((), x₂), he_setup.execRand, .pure _ 0, ?_, ?_, ?_, ?_⟩
  · intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    have hf : 100000 ≤ whpInitFactor c := by unfold whpInitFactor; omega
    have hs : 1 ≤ whpSpace c U V w n_max + 1 := by omega
    have hprod : 5 ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) := by nlinarith
    omega
  · simp [ProbComp.eval_pure]
  · intro θ; cases θ; simp
  · intro p hp
    rw [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hfr2 : x₂.regs frontierReg = base + (whpSpace c U V w n_max + 2 * U) := by
      dsimp [x₂, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hfr₁]
    refine ⟨hfr2, ?_, Modifies.refl _ _⟩
    have hb2 : x₂.regs baseReg = base := by
      dsimp [x₂, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hb₁]
    have hz2 : x₂.regs zeroReg = 0 := by
      dsimp [x₂, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_self]
    have ho2 : x₂.regs oneReg = 1 := by
      dsimp [x₂, Data.set]
      rw [Function.update_self]
    have hmem : ∀ u : Fin U, (empty U) u =
        if x₂.mem (base + 2 * u.val) = 0 then none else some (x₂.mem (base + 2 * u.val + 1)) := by
      intro u
      have hfoot : base + 2 * u.val ∈
          (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        refine ⟨by omega, ?_⟩
        have hu := u.isLt
        omega
      have hz_val := hz (base + 2 * u.val) hfoot
      dsimp [x₂, Data.set, empty]
      simp [hz_val]
    exact ⟨(hx₁.set (fits_zero w)).set (fits_one (by omega)), hb2, hz2, ho2, hmem⟩

theorem exec_query {w : ℕ} (x : Data rWhp)
    (hfit_twoU : Fits w (2 * x.regs argUReg))
    (hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg))
    (hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1))
    (hq : x.regs isQueryReg = 1) (hone : x.regs oneReg = 1) :
    let x₁ := x.set twoUReg (2 * x.regs argUReg)
    let x₂ := x₁.set addrReg (x.regs baseReg + 2 * x.regs argUReg)
    let x₃ := x₂.set addr1Reg (x.regs baseReg + 2 * x.regs argUReg + 1)
    let x₄ := x₃.set presReg (x.mem (x.regs baseReg + 2 * x.regs argUReg))
    let x₅ := x₄.set valReg (x.mem (x.regs baseReg + 2 * x.regs argUReg + 1))
    Exec (B := .exact) w dictCode x x₅ 6 := by
  intro x₁ x₂ x₃ x₄ x₅
  have e1 : Exec (B := .exact) w (.op (.exactBin .add twoUReg argUReg argUReg)) x x₁ 1 := by
    apply Exec.op
    rw [Op.eval_exactBin]
    dsimp [BinOp.evalExact]
    have : x.regs argUReg + x.regs argUReg = 2 * x.regs argUReg := by omega
    rw [this]
    exact Data.put_of_fits hfit_twoU
  have e2 : Exec (B := .exact) w (.op (.exactBin .add addrReg baseReg twoUReg)) x₁ x₂ 1 := by
    apply Exec.op
    rw [Op.eval_exactBin]
    dsimp [BinOp.evalExact]
    have hb : x₁.regs baseReg = x.regs baseReg := by
      dsimp [x₁, Data.set]; rw [Function.update_of_ne (by decide)]
    have ht : x₁.regs twoUReg = 2 * x.regs argUReg := by
      dsimp [x₁, Data.set]; rw [Function.update_self]
    rw [hb, ht]
    exact Data.put_of_fits hfit_addr
  have e3 : Exec (B := .exact) w (.op (.exactBin .add addr1Reg addrReg oneReg)) x₂ x₃ 1 := by
    apply Exec.op
    rw [Op.eval_exactBin]
    dsimp [BinOp.evalExact]
    have ha : x₂.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₂, Data.set]; rw [Function.update_self]
    have ho : x₂.regs oneReg = 1 := by
      dsimp [x₂, x₁, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hone]
    rw [ha, ho]
    exact Data.put_of_fits hfit_addr1
  have hcond : (Cond.eq isQueryReg oneReg).Holds x₃ := by
    dsimp [Cond.Holds, x₃, x₂, x₁, Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hq, hone]
  have e_load1 : Exec (B := .exact) w (.op (.load presReg addrReg)) x₃ x₄ 1 := by
    apply Exec.op; simp only [Op.eval_load]
    have ha : x₃.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₃, x₂, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_self]
    rw [ha]; rfl
  have e_load2 : Exec (B := .exact) w (.op (.load valReg addr1Reg)) x₄ x₅ 1 := by
    apply Exec.op; simp only [Op.eval_load]
    have ha1 : x₄.regs addr1Reg = x.regs baseReg + 2 * x.regs argUReg + 1 := by
      dsimp [x₄, x₃, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_self]
    rw [ha1]; rfl
  have e_loads : Exec (B := .exact) w
      (.seq (.op (.load presReg addrReg)) (.op (.load valReg addr1Reg))) x₃ x₅ 2 :=
    e_load1.seq e_load2
  have eb : Exec (B := .exact) w
      (.branch (.eq isQueryReg oneReg)
        (.seq (.op (.load presReg addrReg)) (.op (.load valReg addr1Reg)))
        (.branch (.eq isInsertReg oneReg)
          (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg)))
          (.op (.store addrReg zeroReg)))) x₃ x₅ 3 :=
    Exec.branch_pos hcond e_loads
  exact e1.seq (e2.seq (e3.seq eb))

theorem exec_insert {w : ℕ} (x : Data rWhp)
    (hfit_twoU : Fits w (2 * x.regs argUReg))
    (hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg))
    (hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1))
    (hq : x.regs isQueryReg = 0) (hins : x.regs isInsertReg = 1) (hone : x.regs oneReg = 1) :
    let x₁ := x.set twoUReg (2 * x.regs argUReg)
    let x₂ := x₁.set addrReg (x.regs baseReg + 2 * x.regs argUReg)
    let x₃ := x₂.set addr1Reg (x.regs baseReg + 2 * x.regs argUReg + 1)
    let x₄ : Data rWhp := ⟨x₃.regs,
      Function.update (Function.update x.mem (x.regs baseReg + 2 * x.regs argUReg) 1)
        (x.regs baseReg + 2 * x.regs argUReg + 1) (x.regs argVReg)⟩
    Exec (B := .exact) w dictCode x x₄ 8 := by
  intro x₁ x₂ x₃ x₄
  have e1 : Exec (B := .exact) w (.op (.exactBin .add twoUReg argUReg argUReg)) x x₁ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have : x.regs argUReg + x.regs argUReg = 2 * x.regs argUReg := by omega
    rw [this]; exact Data.put_of_fits hfit_twoU
  have e2 : Exec (B := .exact) w (.op (.exactBin .add addrReg baseReg twoUReg)) x₁ x₂ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have hb : x₁.regs baseReg = x.regs baseReg := by
      dsimp [x₁, Data.set]; rw [Function.update_of_ne (by decide)]
    have ht : x₁.regs twoUReg = 2 * x.regs argUReg := by
      dsimp [x₁, Data.set]; rw [Function.update_self]
    rw [hb, ht]; exact Data.put_of_fits hfit_addr
  have e3 : Exec (B := .exact) w (.op (.exactBin .add addr1Reg addrReg oneReg)) x₂ x₃ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have ha : x₂.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₂, Data.set]; rw [Function.update_self]
    have ho : x₂.regs oneReg = 1 := by
      dsimp [x₂, x₁, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hone]
    rw [ha, ho]; exact Data.put_of_fits hfit_addr1
  have hcond1 : ¬(Cond.eq isQueryReg oneReg).Holds x₃ := by
    dsimp [Cond.Holds, x₃, x₂, x₁, Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hq, hone]
    decide
  have hcond2 : (Cond.eq isInsertReg oneReg).Holds x₃ := by
    dsimp [Cond.Holds, x₃, x₂, x₁, Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hins, hone]
  let s_mid : Data rWhp := ⟨x₃.regs, Function.update x₃.mem (x₃.regs addrReg) (x₃.regs oneReg)⟩
  have e_store1 : Exec (B := .exact) w (.op (.store addrReg oneReg)) x₃ s_mid 1 := by
    apply Exec.op; simp only [Op.eval_store]; rfl
  have e_store2 : Exec (B := .exact) w (.op (.store addr1Reg argVReg)) s_mid x₄ 1 := by
    apply Exec.op; simp only [Op.eval_store]
    have ha1 : s_mid.regs addr1Reg = x.regs baseReg + 2 * x.regs argUReg + 1 := by
      dsimp [s_mid, x₃, Data.set]; rw [Function.update_self]
    have hv : s_mid.regs argVReg = x.regs argVReg := by
      dsimp [s_mid, x₃, x₂, x₁, Data.set]
      repeat rw [Function.update_of_ne (by decide)]
    have ha : x₃.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₃, x₂, Data.set]; rw [Function.update_of_ne (by decide), Function.update_self]
    have ho : x₃.regs oneReg = 1 := by
      dsimp [x₃, x₂, x₁, Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      rw [hone]
    dsimp [s_mid, x₄, Data.write]
    rw [ha1, hv, ha, ho]
    rfl
  have e_stores : Exec (B := .exact) w
      (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg))) x₃ x₄ 2 :=
    e_store1.seq e_store2
  have eb2 : Exec (B := .exact) w
      (.branch (.eq isInsertReg oneReg)
        (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg)))
        (.op (.store addrReg zeroReg))) x₃ x₄ 3 :=
    Exec.branch_pos hcond2 e_stores
  have eb : Exec (B := .exact) w
      (.branch (.eq isQueryReg oneReg)
        (.seq (.op (.load presReg addrReg)) (.op (.load valReg addr1Reg)))
        (.branch (.eq isInsertReg oneReg)
          (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg)))
          (.op (.store addrReg zeroReg)))) x₃ x₄ 5 :=
    Exec.branch_neg hcond1 eb2
  exact e1.seq (e2.seq (e3.seq eb))

theorem exec_delete {w : ℕ} (x : Data rWhp)
    (hfit_twoU : Fits w (2 * x.regs argUReg))
    (hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg))
    (hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1))
    (hq : x.regs isQueryReg = 0) (hins : x.regs isInsertReg = 0)
    (hzero : x.regs zeroReg = 0) (hone : x.regs oneReg = 1) :
    let x₁ := x.set twoUReg (2 * x.regs argUReg)
    let x₂ := x₁.set addrReg (x.regs baseReg + 2 * x.regs argUReg)
    let x₃ := x₂.set addr1Reg (x.regs baseReg + 2 * x.regs argUReg + 1)
    let x₄ : Data rWhp := ⟨x₃.regs, Function.update x.mem (x.regs baseReg + 2 * x.regs argUReg) 0⟩
    Exec (B := .exact) w dictCode x x₄ 8 := by
  intro x₁ x₂ x₃ x₄
  have e1 : Exec (B := .exact) w (.op (.exactBin .add twoUReg argUReg argUReg)) x x₁ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have : x.regs argUReg + x.regs argUReg = 2 * x.regs argUReg := by omega
    rw [this]; exact Data.put_of_fits hfit_twoU
  have e2 : Exec (B := .exact) w (.op (.exactBin .add addrReg baseReg twoUReg)) x₁ x₂ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have hb : x₁.regs baseReg = x.regs baseReg := by
      dsimp [x₁, Data.set]; rw [Function.update_of_ne (by decide)]
    have ht : x₁.regs twoUReg = 2 * x.regs argUReg := by
      dsimp [x₁, Data.set]; rw [Function.update_self]
    rw [hb, ht]; exact Data.put_of_fits hfit_addr
  have e3 : Exec (B := .exact) w (.op (.exactBin .add addr1Reg addrReg oneReg)) x₂ x₃ 1 := by
    apply Exec.op; rw [Op.eval_exactBin]; dsimp [BinOp.evalExact]
    have ha : x₂.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₂, Data.set]; rw [Function.update_self]
    have ho : x₂.regs oneReg = 1 := by
      dsimp [x₂, x₁, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hone]
    rw [ha, ho]; exact Data.put_of_fits hfit_addr1
  have hcond1 : ¬(Cond.eq isQueryReg oneReg).Holds x₃ := by
    dsimp [Cond.Holds, x₃, x₂, x₁, Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hq, hone]
    decide
  have hcond2 : ¬(Cond.eq isInsertReg oneReg).Holds x₃ := by
    dsimp [Cond.Holds, x₃, x₂, x₁, Data.set]
    repeat rw [Function.update_of_ne (by decide)]
    rw [hins, hone]
    decide
  have e_store : Exec (B := .exact) w (.op (.store addrReg zeroReg)) x₃ x₄ 1 := by
    apply Exec.op; simp only [Op.eval_store]
    have ha : x₃.regs addrReg = x.regs baseReg + 2 * x.regs argUReg := by
      dsimp [x₃, x₂, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_self]
    have hz : x₃.regs zeroReg = 0 := by
      dsimp [x₃, x₂, x₁, Data.set]
      repeat rw [Function.update_of_ne (by decide)]
      rw [hzero]
    rw [ha, hz]; rfl
  have eb2 : Exec (B := .exact) w
      (.branch (.eq isInsertReg oneReg)
        (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg)))
        (.op (.store addrReg zeroReg))) x₃ x₄ 3 :=
    Exec.branch_neg hcond2 e_store
  have eb : Exec (B := .exact) w
      (.branch (.eq isQueryReg oneReg)
        (.seq (.op (.load presReg addrReg)) (.op (.load valReg addr1Reg)))
        (.branch (.eq isInsertReg oneReg)
          (.seq (.op (.store addrReg oneReg)) (.op (.store addr1Reg argVReg)))
          (.op (.store addrReg zeroReg)))) x₃ x₄ 5 :=
    Exec.branch_neg hcond1 eb2
  exact e1.seq (e2.seq (e3.seq eb))

def nextData {U V n_max : ℕ} (base : ℕ) (o : (Dynamic.spec U V n_max).Op)
    (x : Data rWhp) : Data rWhp :=
  match o with
  | .query u =>
    let x₁ := x.set twoUReg (2 * u.val)
    let x₂ := x₁.set addrReg (base + 2 * u.val)
    let x₃ := x₂.set addr1Reg (base + 2 * u.val + 1)
    let x₄ := x₃.set presReg (x.mem (base + 2 * u.val))
    x₄.set valReg (x.mem (base + 2 * u.val + 1))
  | .insert u v =>
    let x₁ := x.set twoUReg (2 * u.val)
    let x₂ := x₁.set addrReg (base + 2 * u.val)
    let x₃ := x₂.set addr1Reg (base + 2 * u.val + 1)
    ⟨x₃.regs, Function.update (Function.update x.mem (base + 2 * u.val) 1) (base + 2 * u.val + 1) v⟩
  | .delete u =>
    let x₁ := x.set twoUReg (2 * u.val)
    let x₂ := x₁.set addrReg (base + 2 * u.val)
    let x₃ := x₂.set addr1Reg (base + 2 * u.val + 1)
    ⟨x₃.regs, Function.update x.mem (base + 2 * u.val) 0⟩

def stepTime {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op) : ℕ :=
  match o with
  | .query _ => 6
  | .insert _ _ => 8
  | .delete _ => 8

theorem stepTime_le_whpTimeBound (c : ℕ) {U V n_max : ℕ} (o : (Dynamic.spec U V n_max).Op) :
    stepTime o ≤ whpTimeBound c := by
  cases o <;> {
    dsimp [stepTime]
    have hb : 1000 ≤ whpTimeBound c := by unfold whpTimeBound; omega
    omega
  }

theorem exec_nextData {c U V w n_max base : ℕ}
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    (o : (Dynamic.spec U V n_max).Op)
    {x : Data rWhp} (hb : x.regs baseReg = base)
    (hzero : x.regs zeroReg = 0) (hone : x.regs oneReg = 1)
    (harg : argMatch o x.regs) :
    Exec (B := .exact) w dictCode x (nextData base o x) (stepTime o) := by
  cases o with
  | query u =>
    dsimp [nextData, stepTime]
    obtain ⟨hq, _, hu, _⟩ := harg
    have hfit_twoU : Fits w (2 * x.regs argUReg) := by
      rw [hu]
      have : 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg) := by
      rw [hb, hu]
      have : base + 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1) := by
      rw [hb, hu]
      have : base + 2 * u.val + 1 ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hex := exec_query x hfit_twoU hfit_addr hfit_addr1 hq hone
    dsimp at hex
    rw [hb, hu] at hex
    exact hex
  | insert u v =>
    dsimp [nextData, stepTime]
    obtain ⟨hq, hins, hu, hv⟩ := harg
    have hfit_twoU : Fits w (2 * x.regs argUReg) := by
      rw [hu]
      have : 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg) := by
      rw [hb, hu]
      have : base + 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1) := by
      rw [hb, hu]
      have : base + 2 * u.val + 1 ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hex := exec_insert x hfit_twoU hfit_addr hfit_addr1 hq hins hone
    dsimp at hex
    rw [hb, hu, hv] at hex
    exact hex
  | delete u =>
    dsimp [nextData, stepTime]
    obtain ⟨hq, hins, hu, _⟩ := harg
    have hfit_twoU : Fits w (2 * x.regs argUReg) := by
      rw [hu]
      have : 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr : Fits w (x.regs baseReg + 2 * x.regs argUReg) := by
      rw [hb, hu]
      have : base + 2 * u.val ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hfit_addr1 : Fits w (x.regs baseReg + 2 * x.regs argUReg + 1) := by
      rw [hb, hu]
      have : base + 2 * u.val + 1 ≤ base + (whpSpace c U V w n_max + 2 * U) := by
        have := u.isLt; omega
      exact hfit.of_le this
    have hex := exec_delete x hfit_twoU hfit_addr hfit_addr1 hq hins hzero hone
    dsimp at hex
    rw [hb, hu] at hex
    exact hex

theorem q_proof_query {c U V w n_max base : ℕ}
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    {s : (Dynamic.spec U V n_max).State} (u : Fin U)
    {p : Unit × Data rWhp}
    (hrep : rep U V n_max w base p.1 s p.2) :
    let x' := nextData (V := V) (n_max := n_max) base (.query u) p.2
    decode (.query u) x'.regs = some ((Dynamic.spec U V n_max).stepFn s (.query u)).2 ∧
    rep U V n_max w base () ((Dynamic.spec U V n_max).stepFn s (.query u)).1 x' ∧
    Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem x'.mem := by
  intro x'
  dsimp [nextData, decode, stepTime, Dynamic.spec, StateTransitionSpec.stepFn]
  refine ⟨?_, ?_, Modifies.refl _ _⟩
  · have h_pres : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).regs presReg =
        p.2.mem (base + 2 * u.val) := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_self]
    have h_val : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).regs valReg =
        p.2.mem (base + 2 * u.val + 1) := by
      dsimp [nextData, Data.set]
      rw [Function.update_self]
    rw [h_pres, h_val]
    have hmem := hrep.2.2.2.2 u
    rw [hmem]
    split_ifs with hz
    · rfl
    · rfl
  · have hbnd : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).Bounded w := by
      dsimp [nextData]
      have hfit_twoU : Fits w (2 * u.val) := hfit.of_le (by have := u.isLt; omega)
      have hfit_addr : Fits w (base + 2 * u.val) := hfit.of_le (by have := u.isLt; omega)
      have hfit_addr1 : Fits w (base + 2 * u.val + 1) := hfit.of_le (by have := u.isLt; omega)
      have hfit_pres : Fits w (p.2.mem (base + 2 * u.val)) := hrep.1.2 _
      have hfit_val : Fits w (p.2.mem (base + 2 * u.val + 1)) := hrep.1.2 _
      exact ((((hrep.1.set hfit_twoU).set hfit_addr).set hfit_addr1).set hfit_pres).set hfit_val
    have hb : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).regs baseReg =
        base := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.1]
    have hz : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).regs zeroReg =
        0 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.1]
    have ho : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.query u) p.2).regs oneReg =
        1 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.2.1]
    exact ⟨hbnd, hb, hz, ho, hrep.2.2.2.2⟩

theorem q_proof_insert {c U V w n_max base : ℕ} (hw : 1 ≤ w)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    (hV : Fits w V)
    {s : (Dynamic.spec U V n_max).State} (u : Fin U) (v : ℕ) (hv : v < V)
    {p : Unit × Data rWhp}
    (hrep : rep U V n_max w base p.1 s p.2) :
    let x' := nextData (V := V) (n_max := n_max) base (.insert u v) p.2
    decode (.insert u v) x'.regs = some ((Dynamic.spec U V n_max).stepFn s (.insert u v)).2 ∧
    rep U V n_max w base () ((Dynamic.spec U V n_max).stepFn s (.insert u v)).1 x' ∧
    Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem x'.mem := by
  intro x'
  dsimp [nextData, decode, stepTime, Dynamic.spec, StateTransitionSpec.stepFn]
  have hmod : Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem
      (Function.update (Function.update p.2.mem (base + 2 * u.val) 1)
        (base + 2 * u.val + 1) v) := by
    intro a ha
    have h1 : a ≠ base + 2 * u.val + 1 := by
      intro h; apply ha
      simp only [Block.mem_footprint, Block.Owns]
      refine ⟨by omega, ?_⟩
      have hu := u.isLt; omega
    have h2 : a ≠ base + 2 * u.val := by
      intro h; apply ha
      simp only [Block.mem_footprint, Block.Owns]
      refine ⟨by omega, ?_⟩
      have hu := u.isLt; omega
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨rfl, ?_, hmod⟩
  · have hfit_v : Fits w v := hV.of_le (by omega)
    have hbnd_mem : ∀ a, Fits w ((Function.update (Function.update p.2.mem
        (base + 2 * u.val) 1) (base + 2 * u.val + 1) v) a) := by
      intro a
      dsimp [Function.update]
      split_ifs with h1 h2
      · subst h1; exact hfit_v
      · subst h2; exact fits_one (by omega)
      · exact hrep.1.2 a
    have hfit_twoU : Fits w (2 * u.val) := hfit.of_le (by have := u.isLt; omega)
    have hfit_addr : Fits w (base + 2 * u.val) := hfit.of_le (by have := u.isLt; omega)
    have hfit_addr1 : Fits w (base + 2 * u.val + 1) := hfit.of_le (by have := u.isLt; omega)
    have hbnd_regs : ∀ r, Fits w (((((p.2.set twoUReg (2 * u.val)).set addrReg
        (base + 2 * u.val)).set addr1Reg (base + 2 * u.val + 1))).regs r) := by
      intro r
      exact (((hrep.1.set hfit_twoU).set hfit_addr).set hfit_addr1).1 r
    have hbnd : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.insert u v) p.2).Bounded w :=
      ⟨hbnd_regs, hbnd_mem⟩
    have hb : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.insert u v) p.2).regs baseReg =
        base := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.1]
    have hz : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.insert u v) p.2).regs zeroReg =
        0 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.1]
    have ho : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.insert u v) p.2).regs oneReg =
        1 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.2.1]
    have hm : ∀ u' : Fin U, (Function.update s u (some v)) u' =
        if (Function.update (Function.update p.2.mem (base + 2 * u.val) 1)
              (base + 2 * u.val + 1) v) (base + 2 * u'.val) = 0 then none
        else some ((Function.update (Function.update p.2.mem (base + 2 * u.val) 1)
              (base + 2 * u.val + 1) v) (base + 2 * u'.val + 1)) := by
      intro u'
      by_cases hu' : u' = u
      · subst hu'
        rw [Function.update_self]
        have h_ne : base + 2 * u'.val ≠ base + 2 * u'.val + 1 := by omega
        have h1 : (Function.update (Function.update p.2.mem (base + 2 * u'.val) 1)
            (base + 2 * u'.val + 1) v) (base + 2 * u'.val) = 1 := by
          rw [Function.update_of_ne h_ne, Function.update_self]
        have h2 : (Function.update (Function.update p.2.mem (base + 2 * u'.val) 1)
            (base + 2 * u'.val + 1) v) (base + 2 * u'.val + 1) = v := by
          rw [Function.update_self]
        rw [h1, h2]
        dsimp
      · rw [Function.update_of_ne hu']
        have h_ne1 : base + 2 * u'.val ≠ base + 2 * u.val + 1 := by
          intro h; omega
        have h_ne2 : base + 2 * u'.val ≠ base + 2 * u.val := by
          intro h; apply hu'; ext; omega
        have h1 : (Function.update (Function.update p.2.mem (base + 2 * u.val) 1)
            (base + 2 * u.val + 1) v) (base + 2 * u'.val) = p.2.mem (base + 2 * u'.val) := by
          rw [Function.update_of_ne h_ne1, Function.update_of_ne h_ne2]
        have h_ne3 : base + 2 * u'.val + 1 ≠ base + 2 * u.val + 1 := by
          intro h; apply hu'; ext; omega
        have h_ne4 : base + 2 * u'.val + 1 ≠ base + 2 * u.val := by
          intro h; omega
        have h2 : (Function.update (Function.update p.2.mem (base + 2 * u.val) 1)
            (base + 2 * u.val + 1) v) (base + 2 * u'.val + 1) =
              p.2.mem (base + 2 * u'.val + 1) := by
          rw [Function.update_of_ne h_ne3, Function.update_of_ne h_ne4]
        rw [h1, h2]
        exact hrep.2.2.2.2 u'
    exact ⟨hbnd, hb, hz, ho, hm⟩

theorem q_proof_delete {c U V w n_max base : ℕ}
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    {s : (Dynamic.spec U V n_max).State} (u : Fin U)
    {p : Unit × Data rWhp}
    (hrep : rep U V n_max w base p.1 s p.2) :
    let x' := nextData (V := V) (n_max := n_max) base (.delete u) p.2
    decode (.delete u) x'.regs = some ((Dynamic.spec U V n_max).stepFn s (.delete u)).2 ∧
    rep U V n_max w base () ((Dynamic.spec U V n_max).stepFn s (.delete u)).1 x' ∧
    Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem x'.mem := by
  intro x'
  dsimp [nextData, decode, stepTime, Dynamic.spec, StateTransitionSpec.stepFn]
  have hmod : Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem
      (Function.update p.2.mem (base + 2 * u.val) 0) := by
    intro a ha
    have h1 : a ≠ base + 2 * u.val := by
      intro h; apply ha
      simp only [Block.mem_footprint, Block.Owns]
      refine ⟨by omega, ?_⟩
      have hu := u.isLt; omega
    rw [Function.update_of_ne h1]
  refine ⟨rfl, ?_, hmod⟩
  · have hbnd_mem : ∀ a, Fits w ((Function.update p.2.mem (base + 2 * u.val) 0) a) := by
      intro a
      dsimp [Function.update]
      split_ifs with h1
      · subst h1; exact fits_zero w
      · exact hrep.1.2 a
    have hfit_twoU : Fits w (2 * u.val) := hfit.of_le (by have := u.isLt; omega)
    have hfit_addr : Fits w (base + 2 * u.val) := hfit.of_le (by have := u.isLt; omega)
    have hfit_addr1 : Fits w (base + 2 * u.val + 1) := hfit.of_le (by have := u.isLt; omega)
    have hbnd_regs : ∀ r, Fits w (((((p.2.set twoUReg (2 * u.val)).set addrReg
        (base + 2 * u.val)).set addr1Reg (base + 2 * u.val + 1))).regs r) := by
      intro r
      exact (((hrep.1.set hfit_twoU).set hfit_addr).set hfit_addr1).1 r
    have hbnd : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.delete u) p.2).Bounded w :=
      ⟨hbnd_regs, hbnd_mem⟩
    have hb : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.delete u) p.2).regs baseReg =
        base := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.1]
    have hz : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.delete u) p.2).regs zeroReg =
        0 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.1]
    have ho : (nextData (V := V) (n_max := n_max) base (Dynamic.Op.delete u) p.2).regs oneReg =
        1 := by
      dsimp [nextData, Data.set]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hrep.2.2.2.1]
    have hm : ∀ u' : Fin U, (Function.update s u none) u' =
        if (Function.update p.2.mem (base + 2 * u.val) 0) (base + 2 * u'.val) = 0
        then none
        else some ((Function.update p.2.mem (base + 2 * u.val) 0) (base + 2 * u'.val + 1)) := by
      intro u'
      by_cases hu' : u' = u
      · subst hu'
        rw [Function.update_self]
        have h1 : (Function.update p.2.mem (base + 2 * u'.val) 0) (base + 2 * u'.val) = 0 := by
          rw [Function.update_self]
        rw [h1]
        rfl
      · rw [Function.update_of_ne hu']
        have h_ne1 : base + 2 * u'.val ≠ base + 2 * u.val := by
          intro h; apply hu'; ext; omega
        have h1 : (Function.update p.2.mem (base + 2 * u.val) 0) (base + 2 * u'.val) =
            p.2.mem (base + 2 * u'.val) := by
          rw [Function.update_of_ne h_ne1]
        have h_ne2 : base + 2 * u'.val + 1 ≠ base + 2 * u.val := by
          intro h; omega
        have h2 : (Function.update p.2.mem (base + 2 * u.val) 0) (base + 2 * u'.val + 1) =
            p.2.mem (base + 2 * u'.val + 1) := by
          rw [Function.update_of_ne h_ne2]
        rw [h1, h2]
        exact hrep.2.2.2.2 u'
    exact ⟨hbnd, hb, hz, ho, hm⟩

theorem step_exec_succinctWhp {c U V w n_max base : ℕ} (hw : 1 ≤ w)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U)))
    (hV : Fits w V)
    {s : (Dynamic.spec U V n_max).State} (o : (Dynamic.spec U V n_max).Op)
    (ν : PMF (Unit × Data rWhp))
    (hv : (Dynamic.spec U V n_max).valid s o)
    (hsupp : ∀ p ∈ ν.support, rep U V n_max w base p.1 s p.2 ∧ argMatch o p.2.regs) :
    ∃ (m_step : Unit × Data rWhp → ProbComp (Data rWhp × ℕ))
      (μ_step : Unit × Data rWhp → PMF ((Unit × Data rWhp) × ℕ)),
      (∀ p ∈ ν.support,
        ExecRand w dictCode p.2 (m_step p) ∧
        (μ_step p).map (fun q => (q.1.2, q.2)) = (m_step p).eval ∧
        ∀ q ∈ (μ_step p).support,
          decode o q.1.2.regs = some ((Dynamic.spec U V n_max).stepFn s o).2 ∧
          rep U V n_max w base q.1.1 ((Dynamic.spec U V n_max).stepFn s o).1 q.1.2 ∧
          Modifies (Block.mk base (whpSpace c U V w n_max + 2 * U)).footprint p.2.mem q.1.2.mem) ∧
      (∀ θ', (((ν.bind μ_step).map Prod.fst).map Prod.fst) θ' ≤ 1 * (PMF.pure ()) θ') ∧
      (ν.bind μ_step).toOuterMeasure {q | whpTimeBound c < q.2} ≤ ((max n_max 1 : ℝ≥0∞)⁻¹ ^ c) := by
  let m_step : Unit × Data rWhp → ProbComp (Data rWhp × ℕ) :=
    fun p => pure (nextData (V := V) (n_max := n_max) base o p.2, stepTime o)
  let μ_step : Unit × Data rWhp → PMF ((Unit × Data rWhp) × ℕ) :=
    fun p => PMF.pure (((), nextData (V := V) (n_max := n_max) base o p.2), stepTime o)
  refine ⟨m_step, μ_step, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hrep, harg⟩ := hsupp p hp
    have he := exec_nextData hfit o hrep.2.1 hrep.2.2.1 hrep.2.2.2.1 harg
    refine ⟨he.execRand, ?_, ?_⟩
    · simp [m_step, μ_step, ProbComp.eval_pure]
    · intro q hq
      rw [PMF.support_pure, Set.mem_singleton_iff] at hq
      subst hq
      cases o with
      | query u =>
        exact q_proof_query (V := V) (n_max := n_max) hfit u hrep
      | insert u v =>
        obtain ⟨_, hv'⟩ := hv
        exact q_proof_insert hw hfit hV u v hv' hrep
      | delete u =>
        exact q_proof_delete (V := V) hfit u hrep
  · intro θ'
    cases θ'
    rw [PMF.map_comp, PMF.map_bind]
    simp
  · refine le_trans (le_of_eq ?_) zero_le
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro q hq hlt
    rw [PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hqp⟩ := hq
    rw [PMF.support_pure, Set.mem_singleton_iff] at hqp
    subst hqp
    dsimp at hlt
    have hle := stepTime_le_whpTimeBound c o
    omega

noncomputable def impl (hw : 1 ≤ w) (hV : Fits w V)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U))) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max) (Dynamic.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) :=
  HighProbStateTransitionImpl.ofFn
    (Seed := Unit)
    (seedLaw := PMF.pure ())
    (seedSlack := 1)
    (space := whpSpace c U V w n_max + 2 * U)
    (spanTime := 3)
    (setupTime := whpInitFactor c * (whpSpace c U V w n_max + 1) - 3)
    (setupRandCalls := 0)
    (worstCaseTime := whpTimeBound c)
    (failureProb := (max n_max 1 : ℝ≥0∞)⁻¹ ^ c)
    (rep := rep U V n_max w base)
    (encode := encode)
    (argMatch := argMatch)
    (decode := decode)
    (bounded := fun h => h.1)
    (arguments_fit := fun {s} o hval i hi => arguments_fit_proof c base hw hfit hV o hval i hi)
    (encode_matches := fun o regs => encode_matches_proof c base o regs)
    (rep_supported := fun hreg hmem hb' hrep => rep_supported_proof hreg hmem hb' hrep)
    (clear_nodup := by
      change [curReg, zeroReg, oneReg, baseReg, frontierReg].Nodup
      decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit_inc => by
      change Data.put w x curReg (x.regs curReg + x.regs oneReg) =
        some (x.set (subroutineCode c U V w n_max).curReg
          (x.regs (subroutineCode c U V w n_max).curReg + 1))
      change x.regs oneReg = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit_inc)
    (span_exec := fun _ hfr _ => span_exec_succinctWhp hfit hfr)
    (setup_exec := fun hx₁ hb₁ hfr₁ _ hz => setup_exec_succinctWhp hw hx₁ hb₁ hfr₁ hz)
    (step_exec := fun o ν hvo _ hsupp =>
      step_exec_succinctWhp hw hfit hV o ν hvo hsupp)





noncomputable def implStandard (hw : 1 ≤ w) (hV : Fits w V)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U))) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max).toStandard (Dynamic.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) :=
  (impl c U V w n_max base hw hV hfit).toStandard

theorem initTime_impl_le (hw : 1 ≤ w) (hV : Fits w V)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U))) :
    (impl c U V w n_max base hw hV hfit).initTime ≤
      whpInitFactor c * (whpSpace c U V w n_max + 1) := by
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

theorem succinctDictionaryWhp_exists (hnU : n_max ≤ U) (hw : 1 ≤ w) (hV : Fits w V)
    (hfit : Fits w (base + (whpSpace c U V w n_max + 2 * U))) :
    ∃ (spaceWords initTime timeBound : ℕ) (pFail : ℝ≥0∞),
      pFail ≤ (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ∧
      spaceWords ≤ Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max ∧
      timeBound ≤ whpTimeBound c ∧
      initTime ≤ whpInitFactor c * (whpSpace c U V w n_max + 1) ∧
      (impl c U V w n_max base hw hV hfit).worstCaseTime ≤ timeBound ∧
      (impl c U V w n_max base hw hV hfit).initTime ≤ initTime := by
  refine ⟨whpSpace c U V w n_max,
    whpInitFactor c * (whpSpace c U V w n_max + 1),
    whpTimeBound c,
    (max n_max 1 : ℝ≥0∞)⁻¹ ^ c,
    le_rfl,
    whpSpace_le_succinctWords c U V w n_max hnU,
    le_rfl,
    le_rfl,
    le_rfl,
    initTime_impl_le c U V w n_max base hw hV hfit⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
