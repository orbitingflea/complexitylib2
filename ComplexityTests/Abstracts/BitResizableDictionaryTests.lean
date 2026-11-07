/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.BitResizableDictionaryAbstract

/-!
# Formal Abstract Tests: Succinct Dynamic Dictionary (`BitResizableDictionaryAbstract`)

Audit (`#check_abstract`), concrete evaluations, non-vacuity checks (both compiled `Code 280`
in-epoch execution and pure multi-epoch hysteresis at `U = 2 ^ 64 - 1`), and trivial no-op
rejection checks for `ComplexityAbstracts.BitResizableDictionaryAbstract`.
-/

namespace ComplexityTests.Abstracts.BitResizableDictionaryTests

open scoped ENNReal
open ComplexityAbstracts.BitResizableDictionaryAbstract

/-! ## Abstract Axiom Guards -/

/--
info: 'ComplexityAbstracts.BitResizableDictionaryAbstract.bitResizableDictionary_compiled' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitResizableDictionary_compiled

/--
info: 'ComplexityAbstracts.BitResizableDictionaryAbstract.bitResizableDictionary_multiEpoch_pure'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitResizableDictionary_multiEpoch_pure

/-! ## Concrete Bitwise, Memory, and Succinct Space Quantity Evaluations -/

example : ceilDiv 0 64 = 0 := by decide
example : ceilDiv 1 64 = 1 := by decide
example : ceilDiv 64 64 = 1 := by decide
example : ceilDiv 65 64 = 2 := by decide

example : logLogFactor 0 = 1 := by decide
example : logLogFactor 4 = 1 := by decide
example : logLogFactor 16 = 2 := by decide

example : optBits 16 8 0 = 0 := by decide
example : optBits 16 8 2 = 13 := by decide
example : optBits 4 4 4 = 8 := by decide

example : bucketBits 0 = 0 := by decide
example : quotientBits 16 0 = 4 := by decide
example : valBits 8 = 3 := by decide
example : itemBits 16 8 0 = 7 := by decide
example : itemBits 4 4 2 = 4 := by decide

example : targetCap 16 0 = 0 := by decide
example : targetCap 16 3 = 6 := by decide
example : targetCap 4 3 = 4 := by decide
example : epochPotential 16 6 3 = 0 := by decide

example : EpochInv 16 0 0 := Or.inl ⟨rfl, rfl⟩
example : EpochInv 16 4 2 := Or.inr ⟨by decide, by decide, by decide, by decide⟩

example : getBit 64 (fun q => if q = 0 then 5 else 0) 0 = true := by decide
example : getBit 64 (fun q => if q = 0 then 5 else 0) 1 = false := by decide
example : getBit 64 (fun q => if q = 0 then 5 else 0) 2 = true := by decide
example : getField 64 (fun q => if q = 0 then 5 else 0) 0 3 = 5 := by decide
example : clearRangeMem 64 (fun _ => 7) 1 3 0 = 1 := by decide

/-! ## Sample Valid Operation Sequence and Dictionary Semantics -/

abbrev k0 : Fin 4 := ⟨0, by decide⟩
abbrev k1 : Fin 4 := ⟨1, by decide⟩
abbrev k2 : Fin 4 := ⟨2, by decide⟩

/-- Six-operation sequence (`insert 1 3`, `insert 2 1`, `query 1`, `delete 1`, `query 1`,
`query 2`) on `Fin 4` with value bound `V = 4` staying inside epoch `N = 2`. -/
def sampleOps : List (DictOp 4) :=
  [ .insert k1 3
  , .insert k2 1
  , .query k1
  , .delete k1
  , .query k1
  , .query k2 ]

theorem validDictHistory_sampleOps : ValidDictHistory 4 (emptyDict 4) sampleOps := by
  dsimp only [ValidDictHistory, validDictOp, sampleOps]
  refine ⟨by decide, by decide, trivial, trivial, trivial, trivial, trivial⟩

theorem inEpochHistory_sampleOps : InEpochHistory 4 2 (emptyDict 4) sampleOps := by
  dsimp only [InEpochHistory, sampleOps]
  refine ⟨by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, Or.inr ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

example : decodeQueryRegs ⟨fun _ => 0, fun _ => 0, 0⟩ = none := rfl
example : decodeQueryRegs ⟨fun i => if i.val = 0 then 1 else 7, fun _ => 0, 0⟩ = some 7 := rfl

/-- Initial `Data 280` state at word width `w = 64` with `(r240, r241) = (4, 4)`. -/
def initData280 : Data 280 :=
  ⟨fun i => if i.val = 240 then 4 else if i.val = 241 then 4 else 0, fun _ => 0, 0⟩

theorem wellFormed_initData280 : initData280.WellFormed 64 := by
  dsimp only [Data.WellFormed, initData280]
  refine ⟨fun i => ?_, fun _ => by decide, by decide, fun i _ => ?_⟩
  · split_ifs <;> decide
  · simp [getBit]

theorem dirtyGrowOracle_zeroGrowOracle_64 : DirtyGrowOracle 64 (zeroGrowOracle 64) := by
  intro mem bitSize δ
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro q
    dsimp only [zeroGrowOracle, clearRangeWord, clearMask]
    have hmask : bitMask 64 = 2 ^ 64 - 1 := by decide
    have hx : (mem q &&& bitMask 64) < 2 ^ 64 := by
      rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    have hy : ((mem q &&& bitMask 64) &&&
        sliceMask (bitSize - q * 64) (min 64 ((q + 1) * 64 - q * 64) - (bitSize - q * 64))) <
        2 ^ 64 :=
      lt_of_le_of_lt Nat.and_le_left hx
    exact Nat.xor_lt_two_pow hx hy
  · intro i hi
    have hmod : i % 64 < 64 := Nat.mod_lt i (by decide)
    have hdiv_mod : i / 64 * 64 + i % 64 = i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i 64
    dsimp only [getBit, zeroGrowOracle, clearRangeWord, clearMask, sliceMask]
    have hbm : (bitMask 64).testBit (i % 64) = true := by
      unfold bitMask
      change (2 ^ 64 - 1).testBit (i % 64) = true
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hmod
    have hge : ¬(bitSize - i / 64 * 64 ≤ i % 64) := by omega
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, hbm, Bool.and_true,
      decide_eq_false hge, Bool.false_and, Bool.and_false, Bool.xor_false]
  · intro i hi
    have hmod : i % 64 < 64 := Nat.mod_lt i (by decide)
    have hdiv_mod : i / 64 * 64 + i % 64 = i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i 64
    dsimp only [getBit, zeroGrowOracle, clearRangeWord, clearMask, sliceMask]
    have hbm : (bitMask 64).testBit (i % 64) = true := by
      unfold bitMask
      change (2 ^ 64 - 1).testBit (i % 64) = true
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hmod
    have hge : bitSize - i / 64 * 64 ≤ i % 64 := by omega
    have hsub_lt :
        i % 64 - (bitSize - i / 64 * 64) < 64 - (bitSize - i / 64 * 64) := by omega
    have hsm :
        (bitMask (min 64 ((i / 64 + 1) * 64 - i / 64 * 64) - (bitSize - i / 64 * 64))).testBit
          (i % 64 - (bitSize - i / 64 * 64)) = true := by
      unfold bitMask
      have hmin : min 64 ((i / 64 + 1) * 64 - i / 64 * 64) = 64 := by omega
      rw [hmin]
      have hsh : (1 <<< (64 - (bitSize - i / 64 * 64))) = 2 ^ (64 - (bitSize - i / 64 * 64)) := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [hsh, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hsub_lt
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, hbm, Bool.and_true,
      decide_eq_true hge, hsm, Bool.xor_self]

/-! ## Headline Theorem Non-Vacuity (`bitResizableDictionary_compiled` & `multiEpoch_pure`) -/

/-- Concrete instantiation of `bitResizableDictionary_compiled` at `(U, V, w) = (4, 4, 64)`,
verifying uniform `Code 280` empty initialization (`bitSize = 256` in `8 * 64 + 37 = 549` steps)
and in-epoch execution of `sampleOps` in epoch `N = 2` under `zeroGrowOracle 64`. -/
theorem bitResizableDictionary_compiled_nonvacuous_4_4_64 :
    ∃ (initCode stepCode : Code 280)
      (epochMetaWords : ℕ → ℕ → ℕ → ℕ)
      (EpochSeed : ℕ → Type)
      (epochSeedPMF : ∀ N, PMF (EpochSeed N))
      (_ : ∀ N, Nonempty (EpochSeed N))
      (Companion : Type)
      (EpochDictInv : ∀ N, EpochSeed N → DictState 4 → Companion → Data 280 → Prop)
      (Rep : ∀ N, EpochSeed N → DictState 4 → Data 280 → Prop)
      (inEpochPotential : ℕ → Companion → ℕ)
      (seqOverhead : ∀ N, EpochSeed N → DictState 4 → List (DictOp 4) → ℕ),
      let dbs := fun N n_t => epochMetaWords 4 64 N * 64 + n_t * itemBits 4 4 N
      (∀ seed₀ : EpochSeed 0,
        ∃ c₀ : Companion,
          DemonicExecWithin 64 initCode initData280
            (fun y =>
              EpochDictInv 0 seed₀ (emptyDict 4) c₀ y ∧
              Rep 0 seed₀ (emptyDict 4) y ∧
              y.bitSize = 256) 549) ∧
      (∑' seed : EpochSeed 2,
        (epochSeedPMF 2 seed : ENNReal) *
          ((seqOverhead 2 seed (emptyDict 4) sampleOps : ℕ) : ENNReal)) ≤
        294450 * 6 ∧
      (∀ seed : EpochSeed 2,
        ∃ (x₀ : Data 280) (ts : List ℕ) (xs : List (Data 280)) (c_f : Companion),
          ts.length = 6 ∧
          xs.length = 6 ∧
          InEpochOracleTrace 4 64 stepCode dbs Rep 2 (zeroGrowOracle 64)
            seed sampleOps (emptyDict 4) x₀ ts xs ∧
          ts.sum + 1967 * inEpochPotential 2 c_f ≤
            seqOverhead 2 seed (emptyDict 4) sampleOps) := by
  obtain ⟨initCode, stepCode, _code_del, _code_client, _code_free, epochMetaWords,
    _hm0, _hm_lin, hopt_le, hinst⟩ := bitResizableDictionary_compiled
  obtain ⟨EpochSeed, epochSeedPMF, hne, Companion, EpochDictInv, Rep, inEpochPotential,
    _stepOverhead, seqOverhead, _hinj, hinit, hempty_ep, htsum, hseq, _hreuse⟩ :=
    hinst (U := 4) (V := 4) (w := 64) (by decide) (by decide) (by decide)
  refine ⟨initCode, stepCode, epochMetaWords, EpochSeed, epochSeedPMF, hne,
    Companion, EpochDictInv, Rep, inEpochPotential, seqOverhead, ?_, ?_, ?_⟩
  · intro seed₀
    obtain ⟨c₀, hexec, _, _, _, _, _⟩ :=
      hinit dirtyGrowOracle_zeroGrowOracle_64 (by decide) seed₀
        wellFormed_initData280 rfl (by decide) (by decide)
    exact ⟨c₀, hexec⟩
  · simpa [sampleOps] using htsum inEpochHistory_sampleOps
  · intro seed
    have hdbs_2 : epochMetaWords 4 64 2 * 64 + 2 * itemBits 4 4 2 < 2 ^ 64 := by
      have hepoch : EpochInv 4 2 2 := Or.inr ⟨by decide, by decide, by decide, by decide⟩
      have h1 := hopt_le (V := 4) (w := 64) (by decide) (by decide) hepoch
      exact lt_of_le_of_lt h1 (by decide)
    obtain ⟨c₀, x₀, hinv₀, _, _, hpot₀⟩ := hempty_ep (by decide) hdbs_2 seed
    obtain ⟨ts, xs, c_f, hlen_ts, hlen_xs, htrace, _, hcost⟩ :=
      hseq dirtyGrowOracle_zeroGrowOracle_64 seed hinv₀ sampleOps
        inEpochHistory_sampleOps validDictHistory_sampleOps
    rw [hpot₀, Nat.mul_zero, Nat.zero_add] at hcost
    exact ⟨x₀, ts, xs, c_f, hlen_ts, hlen_xs, htrace, hcost⟩

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

/-- Non-vacuity of `bitResizableDictionary_multiEpoch_pure` at extreme `U = 2 ^ 64 - 1`,
`V = 2 ^ 64 - 1`, `w = 64` on `[.insert ⟨0, _⟩ 7]`. -/
theorem bitResizableDictionary_multiEpoch_pure_nonvacuous_uMax64 :
    ∃ (epochMetaWords : ℕ → ℕ → ℕ → ℕ),
      let U := 2 ^ 64 - 1
      let dbs := fun N n_t => epochMetaWords U 64 N * 64 + n_t * itemBits U U N
      PureMultiEpochSpaceTrace dbs U 64 0 (emptyDict U) [.insert ⟨0, by decide⟩ 7] := by
  obtain ⟨epochMetaWords, _, _, hopt_le, hreach_of_max, hpure, _⟩ :=
    bitResizableDictionary_multiEpoch_pure
  refine ⟨epochMetaWords, ?_⟩
  let U := 2 ^ 64 - 1
  have hfit_le : ∀ N' ≤ min U (2 * 1),
      epochMetaWords U 64 N' * 64 + N' * itemBits U U N' < 2 ^ 64 := by
    intro N' hN'
    have hN'_2 : N' ≤ 2 := le_trans hN' (Nat.min_le_right _ _)
    have hN'_4 : N' ≤ 4 := le_trans hN'_2 (by decide)
    have hepoch : EpochInv U N' N' := by
      rcases Nat.eq_zero_or_pos N' with rfl | hpos
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨hpos, le_rfl, by omega, le_trans hN'_2 (by decide)⟩
    have h1 := hopt_le (V := U) (w := 64) (by decide) (by decide) hepoch
    have hll : logLogFactor N' = 1 := by
      unfold logLogFactor
      rw [Nat.max_eq_right hN'_4]
      decide
    have hopt : optBits U U N' ≤ 128 * N' := by
      unfold optBits
      have hU_le : U ≤ 2 ^ 64 := by decide
      have hc : Nat.clog 2 (U.choose N') ≤ 64 * N' :=
        Nat.clog_le_of_le_pow <| calc
          U.choose N' ≤ U ^ N' := choose_le_pow U N'
          _ ≤ (2 ^ 64) ^ N' := Nat.pow_le_pow_left hU_le N'
          _ = 2 ^ (64 * N') := (Nat.pow_mul 2 64 N').symm
      have hv : Nat.clog 2 U ≤ 64 := Nat.clog_le_of_le_pow hU_le
      have hvn : N' * Nat.clog 2 U ≤ N' * 64 := Nat.mul_le_mul_left N' hv
      omega
    have h2 : optBits U U N' + 680 * N' * logLogFactor N' + 218 * 64 < 2 ^ 64 := by
      rw [hll]
      have hbd : (17184 : ℕ) < 2 ^ 64 := by decide
      omega
    exact lt_of_le_of_lt h1 h2
  have hmax : MaxCardLe 1 (emptyDict U) [.insert ⟨0, by decide⟩ 7] := by
    have hempty : dictDom (emptyDict U) = ∅ := by
      ext k; simp [dictDom, emptyDict]
    refine ⟨by simp [hempty], ?_⟩
    dsimp only [MaxCardLe, stepDict]
    have hsub : dictDom (Function.update (emptyDict U) ⟨0, by decide⟩ (some 7)) ⊆
        {⟨0, by decide⟩} := by
      intro k hk
      simp only [dictDom, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      by_cases hk0 : k = ⟨0, by decide⟩
      · exact Finset.mem_singleton.mpr hk0
      · rw [Function.update_of_ne hk0] at hk
        simp [emptyDict] at hk
    exact (Finset.card_le_card hsub).trans (by decide)
  have hreach := hreach_of_max (V := U) hfit_le (Nat.zero_le _) hmax
  exact hpure (by decide) (by decide) [.insert ⟨0, by decide⟩ 7] hreach

/-! ## Trivial No-Op / 1-Instruction Halt Rejection Check -/

lemma evalOp_bitSize_eq {w r : ℕ} {o : OpInstr r} {x y : Data r}
    (h : evalOp w o x = some y) : y.bitSize = x.bitSize := by
  cases o <;> dsimp only [evalOp] at h <;> (try split_ifs at h) <;>
    injection h with hy <;> subst hy <;> rfl

/-- No single primitive instruction `.op o` (including `.op (.copy 0 0)`) can satisfy the
empty-initialization `DemonicExecWithin` postcondition (`y.bitSize = 4 * 64`) from `initData280`. -/
theorem not_demonicExecWithin_op_init (o : OpInstr 280) (T : ℕ) :
    ¬DemonicExecWithin 64 (.op o) initData280 (fun y => y.bitSize = 4 * 64) T := by
  intro hexec
  cases hexec with
  | op heval hy _ =>
    have hsz := evalOp_bitSize_eq heval
    rw [hy] at hsz
    change 4 * 64 = 0 at hsz
    omega

/-- No single primitive instruction `.op o` (including `.op (.copy 0 0)`) can satisfy
`InEpochOracleTrace` on `[.insert k0 2]` from an empty epoch-`2` state `x₀` whose `bitSize` is
`dbs 2 0`, because `dbs 2 1 = dbs 2 0 + itemBits 4 4 2` (`itemBits 4 4 2 = 4 > 0`) whereas `.op o`
preserves `bitSize`. -/
theorem not_inEpochOracleTrace_op (o : OpInstr 280)
    (epochMetaWords : ℕ → ℕ → ℕ → ℕ)
    {EpochSeed : ℕ → Type}
    (Rep : ∀ N, EpochSeed N → DictState 4 → Data 280 → Prop)
    (oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ))
    (seed : EpochSeed 2) (x₀ : Data 280)
    (hx₀ : x₀.bitSize = epochMetaWords 4 64 2 * 64)
    (ts : List ℕ) (xs : List (Data 280)) :
    let dbs := fun N n_t => epochMetaWords 4 64 N * 64 + n_t * itemBits 4 4 N
    ¬InEpochOracleTrace 4 64 (.op o) dbs Rep 2 oracle seed
      [.insert k0 2] (emptyDict 4) x₀ ts xs := by
  intro dbs htrace
  cases htrace with
  | cons _ _ _ _ T _ _ _ _ _ _ hy_sz _ _ _ =>
    have hload_sz : (loadOpRegs (.insert k0 2) x₀).bitSize = x₀.bitSize := rfl
    have heval_sz :
        (evalWithOracle 64 oracle T (.op o) (loadOpRegs (.insert k0 2) x₀)).bitSize =
        (loadOpRegs (.insert k0 2) x₀).bitSize := by
      conv_lhs => rw [evalWithOracle.eq_def]
      dsimp only
      cases h : evalOp 64 o (loadOpRegs (.insert k0 2) x₀) with
      | none => rfl
      | some y => exact evalOp_bitSize_eq h
    have hcard1 : (dictDom (stepDict (emptyDict 4) (.insert k0 2))).card = 1 := by decide
    rw [heval_sz, hload_sz, hx₀, hcard1] at hy_sz
    dsimp only [dbs] at hy_sz
    have hib : itemBits 4 4 2 = 4 := by decide
    omega

end ComplexityTests.Abstracts.BitResizableDictionaryTests
