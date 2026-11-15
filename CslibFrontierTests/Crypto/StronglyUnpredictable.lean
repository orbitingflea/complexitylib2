/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
public import CslibFrontier.Crypto.Computational.ElGamal.StronglyUnpredictable
public import CslibFrontier.Crypto.Computational.Encryption.StronglyUnpredictable
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for strongly unpredictable ciphertexts

An ordinary `module` client verifying `Cslib.Crypto.Encryption.StronglyUnpredictable` and the
ElGamal instances across the `module` boundary:

* **Positive and negative nonvacuity**: `paddedRandomEncrypt` satisfies `StronglyUnpredictable`, its
  collision probability is negligible via `StronglyUnpredictable.negligible_collision`, and
  deterministic encryption fails `StronglyUnpredictable`.
* **Family-dependent and constant-type unification**: both genuinely `n`-dependent type families and
  constant-type schemes (including ElGamal / hybrid Hashed ElGamal) unify with
  `StronglyUnpredictable`, and `F.DDH (fun n => PMF.pure (d n))` yields strong unpredictability
  via `DDH.negligible_expected_inv_order`.
* **Necessity of hypotheses**:
  1. `hord` cannot be dropped: constant Schnorr group `d23` (order `11`) fails
     `StronglyUnpredictable`.
  2. Honest-key spreadness (`ExplicitCoinPKE.GammaSpread`) does not imply `StronglyUnpredictable`:
     `honestOnlyPKE` is `n`-spread on honest keys yet fails `StronglyUnpredictable` on an
     adversarially chosen key.
  3. Restricting to non-error ciphertexts (`some c`) is essential: `rejectEmptyKeyEncrypt` passes
     `StronglyUnpredictable` even though it outputs `none` with probability `1` on the empty key.
  4. Nonemptiness of types in `stronglyUnpredictable_iff_forall` is essential: `emptyAtZeroMsg`
     makes the sequential condition vacuously true while `StronglyUnpredictable` fails at `n ≥ 1`.
-/

public section

namespace CslibFrontierTests.Crypto.StronglyUnpredictable

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Crypto.Protocols
open Cslib.Crypto.PrimeOrderGroupFamily Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Positive nonvacuity witness: prepending `n` random bits to the message satisfies
`StronglyUnpredictable`. -/
noncomputable def paddedRandomEncrypt (n : ℕ) (_pk : Unit) (m : List Bool) :
    ProbComp (Option (List Bool)) := do
  let r ← BitString.sampleList n
  return some (r ++ m)

theorem ciphertextHitBound_paddedRandomEncrypt (n : ℕ) :
    CiphertextHitBound (paddedRandomEncrypt n) (1 / 2 ^ n) := by
  intro _pk m c
  rw [paddedRandomEncrypt, ProbComp.eval_bind]
  have hle :
      ((ProbComp.eval (BitString.sampleList n)).bind
        (fun r => ProbComp.eval (pure (some (r ++ m))))) (some c) ≤
        ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    by_cases hlen : c.length = n + m.length
    · rw [PMF.bind_apply, BitString.eval_sampleList]
      let r₀ := c.take n
      have hsub : ∀ r : List Bool,
          BitString.uniformList n r * ProbComp.eval (pure (some (r ++ m))) (some c) ≤
            if r = r₀ then ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) else 0 := by
        intro r
        by_cases hrc : r ++ m = c
        · have hrlen : r.length = n := by
            have := congrArg List.length hrc
            rw [List.length_append, hlen] at this
            omega
          have hreq : r = r₀ := by
            dsimp [r₀]
            rw [← hrc, List.take_left' hrlen]
          rw [hreq] at hrc ⊢
          simp only [↓reduceIte, ProbComp.eval_pure, PMF.pure_apply, hrc, mul_one]
          simpa [ENNReal.coe_div, ENNReal.coe_one, ENNReal.coe_pow] using
            BitString.uniformList_apply_le n r₀
        · simp [ProbComp.eval_pure, PMF.pure_apply, ne_comm.mp hrc]
      refine (tsum_le_tsum hsub).trans ?_
      simp
    · rw [PMF.bind_apply, BitString.eval_sampleList]
      have hzero : ∀ r : List Bool,
          BitString.uniformList n r * ProbComp.eval (pure (some (r ++ m))) (some c) = 0 := by
        intro r
        by_cases hr : r ∈ (BitString.uniformList n).support
        · have hlenr := BitString.length_of_mem_support_uniformList hr
          have hne : r ++ m ≠ c := fun h => hlen (by rw [← h, List.length_append, hlenr])
          simp [ProbComp.eval_pure, PMF.pure_apply, ne_comm.mp hne]
        · have h0 : BitString.uniformList n r = 0 := by
            simpa [PMF.mem_support_iff] using hr
          simp [h0]
      simp_rw [hzero]
      simp
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hle).trans_eq (ENNReal.toNNReal_coe (1 / 2 ^ n))

theorem stronglyUnpredictable_paddedRandomEncrypt :
    StronglyUnpredictable paddedRandomEncrypt :=
  StronglyUnpredictable.of_bound negligible_one_div_two_pow ciphertextHitBound_paddedRandomEncrypt

/-- Collision probability of `paddedRandomEncrypt` under arbitrary keys and messages is negligible
via `StronglyUnpredictable.negligible_collision`. -/
example (m₁ m₂ : ℕ → List Bool) :
    Negligible fun n =>
      ((ProbComp.eval (do
        let c₁ ← paddedRandomEncrypt n () (m₁ n)
        let c₂ ← paddedRandomEncrypt n () (m₂ n)
        return decide (c₁ = c₂ ∧ c₁.isSome))) true).toNNReal :=
  stronglyUnpredictable_paddedRandomEncrypt.negligible_collision (fun _ => ()) (fun _ => ()) m₁ m₂

/-- A genuinely `n`-dependent type family (`Fin (n + 1)` messages and `BitString (n + 1)`
ciphertexts) satisfies `StronglyUnpredictable` and exercises `stronglyUnpredictable_iff_forall`. -/
noncomputable def uniformBitStringEncrypt (n : ℕ) (_pk : Unit) (_m : Fin (n + 1)) :
    ProbComp (Option (BitString (n + 1))) :=
  some <$> ProbComp.uniform (BitString (n + 1))

theorem stronglyUnpredictable_uniformBitStringEncrypt :
    StronglyUnpredictable uniformBitStringEncrypt := by
  refine StronglyUnpredictable.of_bound (negligible_one_div_two_pow.shift 1) ?_
  intro n _pk _m c
  simp only [uniformBitStringEncrypt, ProbComp.eval_map,
    Cslib.Probability.PMF.map_apply_of_injective _ (Option.some_injective _),
    ProbComp.eval_uniform, PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  have hcast : ((2 ^ (n + 1) : ℕ) : ℝ≥0∞)⁻¹ = (((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞)) := by
    simp [ENNReal.coe_inv]
  rw [hcast, ENNReal.toNNReal_coe]

example :
    ∀ (pk : ∀ _n : ℕ, Unit) (m : ∀ n, Fin (n + 1)) (c : ∀ n, BitString (n + 1)),
      Negligible fun n =>
        ((ProbComp.eval (uniformBitStringEncrypt n (pk n) (m n))) (some (c n))).toNNReal :=
  (stronglyUnpredictable_iff_forall uniformBitStringEncrypt).mp
    stronglyUnpredictable_uniformBitStringEncrypt

/-- DDH implies `StronglyUnpredictable` for ElGamal and hybrid Hashed ElGamal via
`DDH.negligible_expected_inv_order` across the `module` boundary. -/
example (F : PrimeOrderGroupFamily) {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc) (hDDH : F.DDH (fun n => PMF.pure (d n))) :
    StronglyUnpredictable
      (fun n pk m => some <$> F.elGamalEncryptProb encodeMsg d n pk m) := by
  refine F.stronglyUnpredictable_elGamalEncryptProb encodeMsg d ?_
  have hexp := DDH.negligible_expected_inv_order hDDH
  convert hexp using 2 with n
  simp [PMF.pure_apply]

example (F : PrimeOrderGroupFamily) {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (d : ℕ → F.Desc) (hDDH : F.DDH (fun n => PMF.pure (d n))) :
    StronglyUnpredictable
      (fun n pk m =>
        some <$> Encryption.hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym n pk m) := by
  refine F.stronglyUnpredictable_hybrid_hashedElGamal H encryptSym d ?_
  have hexp := DDH.negligible_expected_inv_order hDDH
  convert hexp using 2 with n
  simp [PMF.pure_apply]

/-- Negative nonvacuity witness: deterministic encryption is not strongly unpredictable. -/
theorem not_stronglyUnpredictable_det :
    ¬ StronglyUnpredictable (fun (_n : ℕ) (_pk : Unit) (m : Bool) => pure (some m)) := by
  rintro ⟨ε, hε, hbound⟩
  have hconst : ∀ n, (1 : ℝ≥0) ≤ ε n := fun n => by
    have := hbound n () true true
    simpa [ProbComp.eval_pure, PMF.pure_apply] using this
  exact not_negligible_const one_ne_zero (negligible_of_le hε hconst)

/-- The Schnorr group of order `11` in `(ZMod 23)ˣ`, generated by `2`. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- Counterexample 1: `hord` is essential — constant small group `d23` (order 11) fails
`StronglyUnpredictable` even for ElGamal encryption. -/
theorem not_stronglyUnpredictable_schnorr_d23 :
    ¬ StronglyUnpredictable
      (fun n pk m =>
        some <$> schnorrGroups.elGamalEncryptProb (fun _ x => x) (fun _ => d23) n pk m) := by
  rintro ⟨ε, hε, hbound⟩
  let u := schnorrGroups.encode d23 (schnorrGroups.generator d23)
  let c0 := encPair encBits encBits
    (schnorrGroups.encodeElGamalEncrypt (d23, u, u, 0))
  have hconst : ∀ n, ((1 : ℝ≥0) / 11) ≤ ε n + 1 / 2 ^ n := fun n => by
    have hhit := hbound n (encPair encBits encBits ([], u)) u c0
    rw [ProbComp.eval_map,
      Cslib.Probability.PMF.map_apply_of_injective _ (Option.some_injective _)] at hhit
    let gReal : Game := (ProbComp.eval (schnorrGroups.sampleExp n d23)).bind fun b =>
      PMF.pure (decide ((b : ZMod (schnorrGroups.order d23)) = 0))
    let gIdeal : Game := (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23))).bind
      fun β => PMF.pure (decide (β = 0))
    have h0 : gReal true ≤
        (ProbComp.eval (schnorrGroups.elGamalEncryptProb (fun _ x => x) (fun _ => d23) n
          (encPair encBits encBits ([], u)) u)) c0 := by
      dsimp only [gReal]
      unfold PrimeOrderGroupFamily.elGamalEncryptProb
      rw [ProbComp.eval_bind, PMF.bind_apply, PMF.bind_apply]
      refine tsum_le_tsum fun b => ?_
      by_cases hb : (b : ZMod (schnorrGroups.order d23)) = 0
      · have heq : schnorrGroups.encodeElGamalEncrypt
            (d23, dropFrame (encPair encBits encBits ([], u)), u, b) =
            schnorrGroups.encodeElGamalEncrypt (d23, u, u, 0) := by
          simp only [dropFrame_encPair_encBits, encodeElGamalEncrypt, encRand, encPk, encMsg, u]
          rw [schnorrGroups.smul_encode, schnorrGroups.smul_encode, hb]
          simp
        dsimp only [c0]
        rw [heq]
        simp [hb, ProbComp.eval_pure, PMF.pure_apply]
      · simp [hb, PMF.pure_apply]
    have h0nn : gReal.succProbability ≤ ε n :=
      (ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) h0).trans hhit
    have hadv : Game.advantage gReal gIdeal ≤ 1 / 2 ^ n :=
      schnorrGroups.advantage_bind_sampleExp_le n d23 (fun β => PMF.pure (decide (β = 0)))
    have hideal : gIdeal.succProbability = (1 : ℝ≥0) / 11 := by
      have hval : gIdeal true = (((1 : ℝ≥0) / 11 : ℝ≥0) : ℝ≥0∞) := by
        have h1 : gIdeal true = (schnorrGroups.order d23 : ℝ≥0∞)⁻¹ := by
          dsimp only [gIdeal]
          rw [PMF.bind_apply, tsum_fintype]
          simp [PMF.uniformOfFintype_apply, PMF.pure_apply, ZMod.card]
        have hord23 : schnorrGroups.order d23 = 11 := rfl
        rw [h1, hord23]
        norm_num
      rw [Game.succProbability, hval, ENNReal.toNNReal_coe]
    rw [← NNReal.coe_le_coe, NNReal.coe_add]
    have hadv' :
        |(gReal.succProbability : ℝ) - gIdeal.succProbability| ≤ ((1 / 2 ^ n : ℝ≥0) : ℝ) := by
      rw [← Game.coe_advantage]
      exact NNReal.coe_le_coe.mpr hadv
    rw [hideal] at hadv'
    have h0real : (gReal.succProbability : ℝ) ≤ (ε n : ℝ) := NNReal.coe_le_coe.mpr h0nn
    rw [Game.coe_succProbability] at hadv' h0real
    push_cast at hadv' ⊢
    linarith [(abs_sub_le_iff.mp hadv').2]
  exact not_negligible_const (by norm_num)
    (negligible_of_le (hε.add negligible_one_div_two_pow) hconst)

/-- Counterexample 2: `GammaSpread` (honest keys only) does NOT imply `StronglyUnpredictable`:
an explicit-coin scheme that randomizes on genuine keys `pk = true` and ignores coins on
adversarial key `pk = false`. -/
noncomputable def honestOnlyPKE (n : ℕ) :
    ExplicitCoinPKE Bool Bool Unit (List Bool) (List Bool) where
  keyGen := pure (true, true)
  sampleCoins := BitString.sampleList n
  encDet pk _ r := if pk then r else []
  dec _ _ := some ()

theorem gammaSpread_honestOnlyPKE (n : ℕ) :
    (honestOnlyPKE n).GammaSpread n := by
  intro pk sk hsupp m c
  have hpk : pk = true :=
    (by simpa [honestOnlyPKE, ProbComp.eval_pure] using hsupp : pk = true ∧ sk = true).1
  subst hpk
  simp only [honestOnlyPKE, ↓reduceIte, PMF.toOuterMeasure_apply, BitString.eval_sampleList]
  have hsum_eq :
      (∑' x : List Bool, ({r | r = c}.indicator (BitString.uniformList n)) x) =
        BitString.uniformList n c := by
    rw [tsum_eq_single c]
    · simp
    · intro x hx
      simp [hx]
  rw [hsum_eq]
  have hle : BitString.uniformList n c ≤ ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.coe_div, ENNReal.coe_one, ENNReal.coe_pow] using
      BitString.uniformList_apply_le n c
  refine (ENNReal.toReal_mono ENNReal.coe_ne_top hle).trans_eq ?_
  rw [ENNReal.coe_toReal]
  simp [Real.rpow_neg]

theorem not_stronglyUnpredictable_honestOnlyPKE :
    ¬ StronglyUnpredictable (fun n pk m => some <$> (honestOnlyPKE n).encrypt pk m) := by
  rintro ⟨ε, hε, hbound⟩
  have hconst : ∀ n, (1 : ℝ≥0) ≤ ε n := fun n =>
    by simpa [ExplicitCoinPKE.encrypt, honestOnlyPKE, BitString.eval_sampleList] using
      hbound n false () []
  exact not_negligible_const one_ne_zero (negligible_of_le hε hconst)

/-- Counterexample 3: `c ≠ error` (`some c` vs `none`) is essential — returning `none` on empty
key passes `StronglyUnpredictable` despite hitting `none` with probability 1. -/
noncomputable def rejectEmptyKeyEncrypt (n : ℕ) (pk : List Bool) (m : List Bool) :
    ProbComp (Option (List Bool)) :=
  if pk.isEmpty then pure none else paddedRandomEncrypt n () m

theorem stronglyUnpredictable_rejectEmptyKeyEncrypt :
    StronglyUnpredictable rejectEmptyKeyEncrypt := by
  refine StronglyUnpredictable.of_bound negligible_one_div_two_pow ?_
  intro n pk m c
  by_cases hpk : pk.isEmpty
  · simp [rejectEmptyKeyEncrypt, hpk, ProbComp.eval_pure, PMF.pure_apply]
  · simp only [rejectEmptyKeyEncrypt, hpk]
    simpa using ciphertextHitBound_paddedRandomEncrypt n () m c

/-- Counterexample 4: `[∀ n, Nonempty (Msg n)]` is needed in
`stronglyUnpredictable_iff_forall`: if `Msg 0 = Empty`, the `∀` quantifier over `∀ n, Msg n`
is vacuously true, while `StronglyUnpredictable` fails at `n ≥ 1`. -/
def emptyAtZeroMsg : ℕ → Type
  | 0 => Empty
  | _ + 1 => Unit

theorem forall_emptyAtZeroMsg_vacuous :
    ∀ (pk : ∀ _n : ℕ, Unit) (m : ∀ n, emptyAtZeroMsg n) (c : ∀ _n : ℕ, Unit),
      Negligible fun n =>
        ((ProbComp.eval ((fun _ _ _ => pure (some ())) n (pk n) (m n))) (some (c n))).toNNReal :=
  fun _ m _ => (m 0).elim

theorem not_stronglyUnpredictable_emptyAtZeroMsg :
    ¬ StronglyUnpredictable
      (PK := fun _ => Unit) (Msg := emptyAtZeroMsg) (C := fun _ => Unit)
      (fun _ _ _ => pure (some ())) := by
  rintro ⟨ε, hε, hbound⟩
  have hshift := hε.shift 1
  have hconst : ∀ n, (1 : ℝ≥0) ≤ ε (n + 1) := fun n => by
    have := hbound (n + 1) () () ()
    simpa [ProbComp.eval_pure, PMF.pure_apply] using this
  exact not_negligible_const one_ne_zero (negligible_of_le hshift hconst)

end CslibFrontierTests.Crypto.StronglyUnpredictable
