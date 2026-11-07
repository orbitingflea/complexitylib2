/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Dictionary.BitResizable.Client
public import Complexity.DataStructure.Dictionary.BitResizable.Transition

/-!
# Bit-resizable succinct dictionary tests

Concrete evaluations, non-vacuity checks (including extreme `U = 2 ^ 64 - 1`), `.halt` / no-op
rejection sanity checks, and axiom guards for the bit-resizable succinct dictionary
(`Cslib.DataStructure.Dictionary.BitResizable`).
-/

public section

namespace ComplexityTests.BitResizableDictionary

open scoped ENNReal
open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.BitResizable

/-! ## Concrete Specification and Resource Evaluations -/

example : Dynamic.optBits 4 4 0 = 0 := by decide
example : Dynamic.optBits 4 4 2 = 7 := by decide
example : Dynamic.logLogFactor 2 = 1 := by decide
example : Dynamic.logLogFactor 16 = 2 := by decide
example : dictBitSize 4 4 64 0 0 = 256 := by decide
example : itemBits 4 4 2 = 4 := by decide
example : targetCap 16 3 = 6 := by decide
example : epochPotential 16 6 3 = 0 := by decide

/-- Sample in-epoch operation sequence (`insert 0 2`, `insert 1 3`, `query 0`, `delete 0`,
`query 0`, `query 1`) on `Fin 4` with `V = 4` staying inside epoch `N = 2`. -/
def sampleOps : List (Dynamic.Op 4) :=
  [ .insert ⟨0, by decide⟩ 2,
    .insert ⟨1, by decide⟩ 3,
    .query ⟨0, by decide⟩,
    .delete ⟨0, by decide⟩,
    .query ⟨0, by decide⟩,
    .query ⟨1, by decide⟩ ]

lemma validHistory_sampleOps :
    (BitResizable.spec 4 4).ValidHistory (Dynamic.empty 4) sampleOps := by
  refine ⟨by decide, by decide, trivial, trivial, trivial, trivial, trivial⟩

lemma inEpochHistory_sampleOps :
    InEpochHistory 4 2 (Dynamic.empty 4) sampleOps := by
  dsimp only [sampleOps, InEpochHistory]
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide⟩

lemma fits_dictBitSize_4_4_64_2 :
    Fits 64 (dictBitSize 4 4 64 2 2) := by
  have hepoch : EpochInv 4 2 2 := Or.inr ⟨by decide, by decide, by decide, by decide⟩
  have h1 : dictBitSize 4 4 64 2 2 ≤
      Dynamic.optBits 4 4 2 + 680 * 2 * Dynamic.logLogFactor 2 + 218 * 64 :=
    dictBitSize_le_optBits (by decide) (by decide) hepoch
  exact lt_of_le_of_lt h1 (by decide)

/-- Initial empty `BitRAM.Data 280` state at word width `64` with `(r240, r241) = (4, 4)`. -/
def initData280 : BitRAM.Data 280 :=
  ⟨fun i => if i.val = 240 then 4 else if i.val = 241 then 4 else 0, fun _ => 0, 0⟩

lemma wellFormed_initData280 : initData280.WellFormed 64 := by
  refine ⟨fun i => ?_, BitMemory.wellFormed_empty 64⟩
  dsimp only [initData280]
  split_ifs <;> decide

/-- Non-vacuity of `initEmptyRegCode_oracle` at `(U, V, w) = (4, 4, 64)`. -/
theorem nonvacuous_initEmptyRegCode_oracle (θ₀ : Succinct.QuotHashSeed 4 0) :
    let y₀ := BitRAM.evalWithOracle 64 (BitRAM.zeroGrowOracle 64) (8 * 64 + 37)
      initEmptyRegCode initData280
    ∃ s_fix₀ : Memory.State,
      EpochDictInv 4 4 64 0 θ₀ (Dynamic.empty 4) s_fix₀ y₀ ∧
      Rep 4 4 64 0 θ₀ (Dynamic.empty 4) y₀.toBitMemoryState ∧
      y₀.bitSize = 256 ∧
      inEpochPotential 4 4 64 0 s_fix₀ = 0 := by
  obtain ⟨s_fix₀, hinv, hrep, hsz, hpot, _, _⟩ :=
    initEmptyRegCode_oracle (U := 4) (V := 4) (w := 64)
      (BitRAM.dirtyGrowOracle_zeroGrowOracle (by decide))
      (by decide) (by decide) (by decide) (by decide) θ₀
      wellFormed_initData280 rfl (by decide) (by decide)
  exact ⟨s_fix₀, hinv, hrep, hsz, hpot⟩

/-- Non-vacuity of `inEpochStepRegCode_oracle_seq` on `sampleOps` in epoch `N = 2` at
`(U, V, w) = (4, 4, 64)`. -/
theorem nonvacuous_inEpochStepRegCode_oracle_seq (θ : Succinct.QuotHashSeed 4 2) :
    ∃ (x₀ : BitRAM.Data 280) (s_fix₀ s_fix_f : Memory.State)
      (ts : List ℕ) (xs : List (BitRAM.Data 280)),
      EpochDictInv 4 4 64 2 θ (Dynamic.empty 4) s_fix₀ x₀ ∧
      inEpochPotential 4 4 64 2 s_fix₀ = 0 ∧
      ts.length = 6 ∧
      xs.length = 6 ∧
      InEpochOracleTrace inEpochStepRegCode 4 4 64 2 (BitRAM.zeroGrowOracle 64)
        θ sampleOps (Dynamic.empty 4) x₀ ts xs ∧
      ts.sum + 1967 * inEpochPotential 4 4 64 2 s_fix_f ≤
        inEpochSeqOverhead 4 2 θ (Dynamic.empty 4) sampleOps := by
  obtain ⟨s_fix₀, x₀, hinv₀, hpot₀⟩ :=
    exists_empty_epochDictInv (U := 4) (V := 4) (w := 64) (N := 2)
      (by decide) (by decide) (by decide) (by decide)
      fits_dictBitSize_4_4_64_2 θ
  obtain ⟨ts, xs, s_fix_f, hlen_ts, hlen_xs, htrace, hcost⟩ :=
    inEpochStepRegCode_oracle_seq (U := 4) (V := 4) (w := 64) (N := 2)
      (BitRAM.dirtyGrowOracle_zeroGrowOracle (by decide))
      (by decide) (by decide) (by decide) θ hinv₀ sampleOps
      inEpochHistory_sampleOps validHistory_sampleOps
  rw [hpot₀, Nat.mul_zero, Nat.zero_add] at hcost
  exact ⟨x₀, s_fix₀, s_fix_f, ts, xs, hinv₀, hpot₀, hlen_ts, hlen_xs, htrace, hcost⟩

/-! ## Non-Vacuity at Maximum Universe Size `U = 2 ^ 64 - 1` -/

abbrev UMax64 : ℕ := 2 ^ 64 - 1

def multiEpochOps64 : List (Dynamic.Op UMax64) :=
  [ .insert ⟨0, by decide⟩ 7,
    .insert ⟨1, by decide⟩ 9,
    .delete ⟨0, by decide⟩,
    .delete ⟨1, by decide⟩ ]

private lemma dom_update_subset_pair {s : Dynamic.State UMax64}
    (hs : Dynamic.dom s ⊆ {⟨0, by decide⟩, ⟨1, by decide⟩})
    {k : Fin UMax64} (hk : k ∈ ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin UMax64)))
    (v : Option ℕ) :
    Dynamic.dom (Function.update s k v) ⊆ {⟨0, by decide⟩, ⟨1, by decide⟩} := by
  intro x hx
  by_cases hxk : x = k
  · exact hxk ▸ hk
  · apply hs
    rw [Dictionary.mem_dom_iff_isSome] at hx ⊢
    rwa [Function.update_of_ne hxk] at hx

private lemma choose_le_pow : ∀ (U n : ℕ), U.choose n ≤ U ^ n
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | U + 1, 0 => by simp
  | U + 1, n + 1 => by
    calc (U + 1).choose (n + 1)
        = U.choose n + U.choose (n + 1) := Nat.choose_succ_succ U n
      _ ≤ U ^ n + U ^ (n + 1) := Nat.add_le_add (choose_le_pow U n) (choose_le_pow U (n + 1))
      _ = U ^ n * (U + 1) := by rw [Nat.pow_succ, Nat.add_comm, ← Nat.mul_succ]
      _ ≤ (U + 1) ^ n * (U + 1) :=
          Nat.mul_le_mul_right (U + 1) (Nat.pow_le_pow_left (Nat.le_succ U) n)
      _ = (U + 1) ^ (n + 1) := (Nat.pow_succ (U + 1) n).symm

lemma maxCardLe_multiEpochOps64 :
    MaxCardLe 2 (Dynamic.empty UMax64) multiEpochOps64 := by
  let pair64 : Finset (Fin UMax64) := {⟨0, by decide⟩, ⟨1, by decide⟩}
  have hpair_card : pair64.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hk0 : (⟨0, by decide⟩ : Fin UMax64) ∈ pair64 := Finset.mem_insert_self _ _
  have hk1 : (⟨1, by decide⟩ : Fin UMax64) ∈ pair64 :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hs0 : Dynamic.dom (Dynamic.empty UMax64) ⊆ pair64 := by
    intro k hk
    rw [Dictionary.mem_dom_iff_isSome] at hk
    cases hk
  have hs1 := dom_update_subset_pair hs0 hk0 (some 7)
  have hs2 := dom_update_subset_pair hs1 hk1 (some 9)
  have hs3 := dom_update_subset_pair hs2 hk0 none
  have hs4 := dom_update_subset_pair hs3 hk1 none
  exact ⟨(Finset.card_le_card hs0).trans hpair_card,
    (Finset.card_le_card hs1).trans hpair_card,
    (Finset.card_le_card hs2).trans hpair_card,
    (Finset.card_le_card hs3).trans hpair_card,
    (Finset.card_le_card hs4).trans hpair_card⟩

/-- Non-vacuity of `pureMultiEpoch_space_and_hysteresis_from_empty` at maximum universe size
`U = 2 ^ 64 - 1` and `V = 2 ^ 64`. -/
theorem nonvacuous_multiEpoch_uMax64 :
    PureMultiEpochSpaceTrace UMax64 (2 ^ 64) 64 0 (Dynamic.empty UMax64) multiEpochOps64 := by
  have hfit_le : ∀ N' ≤ min UMax64 (2 * 2),
      Fits 64 (dictBitSize UMax64 (2 ^ 64) 64 N' N') := by
    intro N' hN'
    have hN'_4 : N' ≤ 4 := le_trans hN' (Nat.min_le_right _ _)
    have hepoch : EpochInv UMax64 N' N' := by
      rcases Nat.eq_zero_or_pos N' with rfl | hpos
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨hpos, le_rfl, by omega, le_trans hN'_4 (by decide)⟩
    have h1 := dictBitSize_le_optBits (V := 2 ^ 64) (w := 64) (by decide) (by decide) hepoch
    have hll : Dynamic.logLogFactor N' = 1 := by
      unfold Dynamic.logLogFactor
      rw [Nat.max_eq_right hN'_4]
      decide
    have hopt : Dynamic.optBits UMax64 (2 ^ 64) N' ≤ 128 * N' := by
      unfold Dynamic.optBits
      have hU_le : UMax64 ≤ 2 ^ 64 := by decide
      have hc : Nat.clog 2 (UMax64.choose N') ≤ 64 * N' :=
        Nat.clog_le_of_le_pow <| calc
          UMax64.choose N' ≤ UMax64 ^ N' := choose_le_pow UMax64 N'
          _ ≤ (2 ^ 64) ^ N' := Nat.pow_le_pow_left hU_le N'
          _ = 2 ^ (64 * N') := (Nat.pow_mul 2 64 N').symm
      have hv : Nat.clog 2 (2 ^ 64) ≤ 64 := Nat.clog_le_of_le_pow le_rfl
      have hvn : N' * Nat.clog 2 (2 ^ 64) ≤ N' * 64 := Nat.mul_le_mul_left N' hv
      omega
    have h2 : Dynamic.optBits UMax64 (2 ^ 64) N' + 680 * N' * Dynamic.logLogFactor N' +
        218 * 64 < 2 ^ 64 := by
      rw [hll]
      have hbd : (17184 : ℕ) < 2 ^ 64 := by decide
      omega
    exact lt_of_le_of_lt h1 h2
  have hreach : ReachedEpochsFit UMax64 (2 ^ 64) 64 0 (Dynamic.empty UMax64) multiEpochOps64 :=
    reachedEpochsFit_of_maxCardLe hfit_le (Nat.zero_le _) maxCardLe_multiEpochOps64
  exact pureMultiEpoch_space_and_hysteresis_from_empty (by decide) (by decide)
    multiEpochOps64 hreach

/-! ## `.halt` and Trivial No-Op Rejection Sanity Checks -/

private lemma put_bitSize_eq {w r : ℕ} {x y : BitRAM.Data r} {d : Fin r} {v : ℕ}
    (h : x.put w d v = some y) : y.bitSize = x.bitSize := by
  unfold BitRAM.Data.put at h
  split_ifs at h
  injection h with hy
  rw [← hy, BitRAM.Data.set_bitSize]

lemma evalOp_bitSize_eq {w r : ℕ} {o : Cslib.WordRAM.Op .standard r} {x y : BitRAM.Data r}
    (h : BitRAM.evalOp w o x = some y) : y.bitSize = x.bitSize := by
  cases o with
  | const d v => exact put_bitSize_eq h
  | copy d s =>
    dsimp only [BitRAM.evalOp] at h
    injection h with hy
    rw [← hy, BitRAM.Data.set_bitSize]
  | alu f d args =>
    dsimp only [BitRAM.evalOp] at h
    cases hev : StandardOp.eval w f (x.regs ∘ args) with
    | none =>
      rw [hev] at h
      cases h
    | some val =>
      rw [hev] at h
      exact put_bitSize_eq h
  | load d a =>
    dsimp only [BitRAM.evalOp] at h
    split_ifs at h
    injection h with hy
    rw [← hy, BitRAM.Data.set_bitSize]
  | store a s =>
    dsimp only [BitRAM.evalOp] at h
    split_ifs at h
    injection h with hy
    rw [← hy, BitRAM.Data.write_bitSize]

/-- Flat `[.halt 0]` immediately self-loops (`stepRand = some (pure ⟨0, initData280⟩)`), never
allocating memory (`initData280.bitSize = 0 ≠ 4 * 64`). -/
theorem not_halt_program_init :
    BitRAM.stepRand 64 ([BitRAM.Instr.halt 0] : BitRAM.Program .standard 280)
      ⟨0, initData280⟩ = some (pure ⟨0, initData280⟩) ∧
      initData280.bitSize ≠ 4 * 64 := by
  exact ⟨rfl, by decide⟩

/-- No single primitive instruction `.op o` (including 1-instruction halt/no-op `.op (.copy 0 0)`)
can satisfy the `initEmptyRegCode` specification (`y.bitSize = 4 * 64`) from `initData280`. -/
theorem not_op_init_spec (o : Cslib.WordRAM.Op .standard 280) (T : ℕ) :
    ¬BitRAM.DemonicExecWithin 64 (.op o) initData280 (fun y => y.bitSize = 4 * 64) T := by
  intro hexec
  cases hexec with
  | op heval hy _ =>
    have hsz := evalOp_bitSize_eq heval
    rw [hy] at hsz
    change 4 * 64 = 0 at hsz
    omega

/-- No single primitive instruction `.op o` (including `.op (.copy 0 0)`) can satisfy
`InEpochOracleTrace` on `[.insert ⟨0, _⟩ 2]` from an empty epoch-`2` state `x₀`. -/
theorem not_op_step_trace (o : Cslib.WordRAM.Op .standard 280)
    (θ : Succinct.QuotHashSeed 4 2) {s_fix₀ : Memory.State} {x₀ : BitRAM.Data 280}
    (hinv₀ : EpochDictInv 4 4 64 2 θ (Dynamic.empty 4) s_fix₀ x₀)
    (ts : List ℕ) (xs : List (BitRAM.Data 280)) :
    ¬InEpochOracleTrace (.op o) 4 4 64 2 (BitRAM.zeroGrowOracle 64) θ
      [.insert (⟨0, by decide⟩ : Fin 4) 2] (Dynamic.empty 4) x₀ ts xs := by
  intro htrace
  let op₀ : Dynamic.Op 4 := .insert ⟨0, by decide⟩ 2
  unfold InEpochOracleTrace at htrace
  rcases htrace with ⟨T, _, _, _, _, hdemon, _, _, _, _, _, _, _, _⟩
  cases hdemon with
  | op heval hy' _ =>
    rcases hy' with ⟨_, _, hy_sz, _⟩
    have hx₀_sz : x₀.bitSize = dictBitSize 4 4 64 2 0 := by
      have heq : (Dynamic.dom (Dynamic.empty 4)).card = 0 := by decide
      simpa only [heq] using hinv₀.bitSize_eq
    have hload_sz : (loadOpRegs op₀ x₀).bitSize = x₀.bitSize := rfl
    have heval_sz := evalOp_bitSize_eq heval
    have hcard1 :
        (Dynamic.dom (nextState (Dynamic.empty 4) op₀)).card = 1 := by
      decide
    rw [heval_sz, hload_sz, hx₀_sz, hcard1] at hy_sz
    have hne : dictBitSize 4 4 64 2 0 ≠ dictBitSize 4 4 64 2 1 := by
      unfold dictBitSize
      have hib : itemBits 4 4 2 = 4 := by decide
      omega
    exact hne hy_sz

/-! ## Axiom Guards -/

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.dictBitSize_le_optBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dictBitSize_le_optBits

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.initEmptyRegCode_exec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms initEmptyRegCode_exec

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.inEpochStepRegCode_exec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inEpochStepRegCode_exec

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.tsum_inEpochSeqOverhead_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tsum_inEpochSeqOverhead_le

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.inEpochStepRegCode_oracle_seq' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inEpochStepRegCode_oracle_seq

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.delete_reuses_released_bits_subroutine' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms delete_reuses_released_bits_subroutine

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.reachedEpochsFit_of_maxCardLe' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reachedEpochsFit_of_maxCardLe

/--
info:
'Cslib.DataStructure.Dictionary.BitResizable.pureMultiEpoch_space_and_hysteresis_from_empty'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pureMultiEpoch_space_and_hysteresis_from_empty

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.pureMultiEpochStep_amortized_le' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pureMultiEpochStep_amortized_le

/--
info: 'Cslib.DataStructure.Dictionary.BitResizable.rep_inj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rep_inj

end ComplexityTests.BitResizableDictionary
