/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Basic
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract.Security
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable.Encrypt
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable.Security
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Algebra.Field.ZMod

/-!
# Computational fuzzy extractor tests

Exercise the fuzzy-extractor definitions, the sketch-and-extract construction (Lemma 2.5), and the
LWE decode-then-extract construction (Construction 4.1) on concrete finite-field parameters.
Distinguishers are `Experiment` programs. Includes positive instances (zero-error
sketch-and-extract, a decoder over `ZMod 5` that satisfies `DecoderCorrectWithError` with failure
probability `1 / 5`, the additive extractor on a uniform source, the LWE security bound for
Construction 4.1 at concrete dimensions against `LWE.advantage`, a concrete Hamming distance) and a
separating negative fixture
(`revealingFuzzyExtractor`) that is perfectly reproducible for every distance threshold `t` yet
has distinguishing advantage `1 / 2` on a uniform 1-bit source. The asymptotic security step
`computationallySecure_lweFuzzyExtractor_of_decisionLWEWithErrors` is applied to the uniform
source, for which its LWE
premise holds unconditionally, and to independent-coordinate sources under `DecisionLWE`.
The reusable-extractor tests use non-degenerate parameters (secret dimension at least `1`, modulus
greater than `1`). They check the reduction bounds of the common-matrix scheme and of the Section 5
scheme, the advantage lower bound of the Section 3.3 attack (end to end with `unitDecoder`, giving
advantage at least `3 / 5`), that the setup-averaged correctness theorems apply with `δ = 1 / 5`,
and that both reduction bounds are attained (advantage `0`) for a uniform source (and uniform
encryption errors). A word adversary that sends an encoded shift is uniform strict oracle PPT, so
the admitted class of `weaklyReusable_commonMatrixFuzzyExtractor` is inhabited, and the theorem
gives it negligible advantage under the FMR security hypothesis.
-/

public section

namespace CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest

open Cslib Cslib.Crypto Cslib.Crypto.FuzzyExtractor Cslib.Probability
open scoped ENNReal NNReal

/-! ### Concrete Hamming distance -/

/-- Concrete verification of `hammingDist w w' = 1` on two 3-symbol vectors over `ZMod 5`. -/
example : hammingDist ![(1 : ZMod 5), 2, 3] ![(1 : ZMod 5), 4, 3] = 1 := by
  decide

/-! ### Concrete sketch-and-extract instance (Lemma 2.5) -/

/-- Trivial exact secure sketch on `Fin 3 → ZMod 2` for zero-noise readings (`t = 0`). -/
def trivialSecureSketch : SecureSketch (Fin 3 → ZMod 2) Unit where
  sketch _ := return ()
  recover w' _ := return w'

theorem correct_trivialSecureSketch : trivialSecureSketch.Correct hammingDist 0 := by
  intro w w' hdis s _ wHat hwHat
  simp only [trivialSecureSketch, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hwHat
  have hw : w = w' := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hdis)
  rw [hwHat, hw]

/-- Applying `sketchAndExtract` with the one-time-pad extractor `fun w x => w + x` yields a
zero-error Hamming fuzzy extractor at threshold `t = 0`. -/
theorem correctHamming_trivialSketchAndExtract :
    (trivialSecureSketch.sketchAndExtract (fun (w x : Fin 3 → ZMod 2) => w + x)).CorrectHamming
      0 :=
  correct_trivialSecureSketch.sketchAndExtract _

/-- On identical readings `w' = w`, the reproduction game of the sketch-and-extract instance
always outputs `true` with failure probability `0`. -/
example (w : Fin 3 → ZMod 2) :
    Game.failProbability
      ((trivialSecureSketch.sketchAndExtract
        (fun (v x : Fin 3 → ZMod 2) => v + x)).reproduceGame w w) = 0 := by
  have h := correctHamming_trivialSketchAndExtract.correctWithError_zero w w
    (by simp [hammingDist_self])
  exact le_antisymm h zero_le

/-! ### Average-case decoder correctness is satisfiable -/

/-- A decoder for one error-free LWE sample over `ZMod 5`: it returns `(A 0 0)⁻¹ * c 0` when
`A 0 0 ≠ 0` and gives up on the zero matrix, where `c = A s` does not depend on `s`. -/
def unitDecoder (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) (c : Fin 1 → ZMod 5) :
    ProbComp (Option (Fin 1 → ZMod 5)) :=
  return if A 0 0 = 0 then none else some fun _ => (A 0 0)⁻¹ * c 0

/-- `unitDecoder` fails only on the zero matrix, which a uniform `1 × 1` matrix over `ZMod 5`
hits with probability `1 / 5`. So `DecoderCorrectWithError` holds with `δ = 1 / 5 < 1` at
`n = 1`, `q = 5`, parameters where no decoder is correct for every matrix. -/
theorem decoderCorrectWithError_unitDecoder : DecoderCorrectWithError unitDecoder 0 (1 / 5) := by
  intro s e he
  obtain rfl : e = 0 := hammingNorm_eq_zero.mp (Nat.le_zero.mp he)
  rw [← ENNReal.coe_le_coe, Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [decodeGame, decodeCheck, unitDecoder, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind]
  -- The failure probability is the probability that the negated success test accepts.
  have hflip (E : Matrix (Fin 1) (Fin 1) (ZMod 5) → Bool) :
      ((PMF.uniformOfFintype _).bind fun A => PMF.pure (E A)) false =
        ((PMF.uniformOfFintype _).bind fun A => PMF.pure (!E A)) true := by
    simp only [PMF.bind_apply, PMF.pure_apply]
    congr 1 with A
    cases E A <;> simp
  rw [hflip]
  refine (Cslib.Probability.PMF.uniformOfFintype_bind_pure_apply_true_le ?_).trans ?_
  · -- Decoding fails only on the zero matrix.
    refine (Set.subsingleton_singleton (a := (0 : Matrix (Fin 1) (Fin 1) (ZMod 5)))).anti
      fun A hA => ?_
    rw [Set.mem_singleton_iff]
    ext i j
    obtain rfl := Subsingleton.elim i 0
    obtain rfl := Subsingleton.elim j 0
    by_contra h0
    rw [Matrix.zero_apply] at h0
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hs : (fun _ : Fin 1 => (A 0 0)⁻¹ * A.mulVec s 0) = s := by
      funext i
      obtain rfl := Subsingleton.elim i 0
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      exact inv_mul_cancel_left₀ h0 _
    simp [h0, hs] at hA
  · have hcard : Fintype.card (Matrix (Fin 1) (Fin 1) (ZMod 5)) = 5 := rfl
    rw [hcard, Nat.cast_ofNat, one_div, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-! ### Concrete decode-then-extract security (Construction 4.1) -/

/-- Concrete instantiation of `decodeThenExtract` on `m = 3, n = 2, q = 5` with the additive
extractor `fun s x => s + x`: on a uniform source `W`, every distinguisher has advantage `0`. -/
theorem securityAdvantage_decodeThenExtract_concrete_zero
    (decode : Matrix (Fin 3) (Fin 2) (ZMod 5) → (Fin 3 → ZMod 5) →
      ProbComp (Option (Fin 2 → ZMod 5)))
    (D : (Fin 2 → ZMod 5) → DecodeHelper 3 2 5 (Fin 2 → ZMod 5) → Experiment) :
    (decodeThenExtract 3 2 5 decode (fun (s x : Fin 2 → ZMod 5) => s + x)).securityAdvantage
        (PMF.uniformOfFintype (Fin 3 → ZMod 5)) D = 0 :=
  securityAdvantage_decodeThenExtract_add_uniform_eq_zero 3 2 5 decode D

/-- Construction 4.1 at `m = 4, k = 1, l = 1, q = 7`: for every source and distinguisher, the
advantage is at most the sum of two dimension-`1` decisional LWE advantages. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7)))
    (W : PMF (Fin 4 → ZMod 7))
    (D : (Fin 1 → ZMod 7) → DecodeHelper 4 (1 + 1) 7 Unit → Experiment) :
    (lweFuzzyExtractor 4 1 1 7 decode).securityAdvantage W D ≤
      LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreKeyReduction D) +
        LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreUniformReduction D) :=
  securityAdvantage_lweFuzzyExtractor_le decode W D

/-- With a uniform error distribution, the decisional LWE advantage of every distinguisher is `0`:
`A s + e` is uniform and independent of `(A, s)`. -/
theorem lweAdvantage_uniform_error_eq_zero
    (B : Matrix (Fin 4) (Fin 1) (ZMod 7) → (Fin 4 → ZMod 7) → Experiment) :
    LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7))
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) B = 0 :=
  LWE.advantage_uniform_error_eq_zero _ B

/-- For the uniform source, both LWE advantages in `securityAdvantage_lweFuzzyExtractor_le` vanish,
so Construction 4.1 is `0`-secure for it against every distinguisher. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7))) :
    (lweFuzzyExtractor 4 1 1 7 decode).ComputationallySecureFor
      {PMF.uniformOfFintype (Fin 4 → ZMod 7)} (fun _ => True) 0 := by
  intro W hW D _
  rw [Set.mem_singleton_iff] at hW
  subst hW
  simpa only [lweAdvantage_uniform_error_eq_zero, add_zero] using
    securityAdvantage_lweFuzzyExtractor_le decode (PMF.uniformOfFintype (Fin 4 → ZMod 7)) D

/-! ### Asymptotic security: the premise is satisfiable -/

/-- With uniform errors, `DecisionLWEWithErrors` holds for all dimensions: `A s + e` is uniform and
independent of `(A, s)`, so the real and random games coincide. -/
theorem decisionLWEWithErrors_uniform (n m w : ℕ → ℕ) :
    DecisionLWEWithErrors n m w fun κ => PMF.uniformOfFintype (Fin (m κ) → ZMod (2 ^ w κ)) := by
  intro D _
  simp only [LWE.realGame_uniform_error_eq_randomGame, Game.advantage_self]
  exact negligible_zero

open Turing.MultiTapeTM in
/-- The asymptotic step applies to the family with `κ` samples, key length `κ`, `κ` further
secret coordinates and modulus `2`, on the uniform source. -/
example (decode : (κ : ℕ) → Matrix (Fin κ) (Fin (κ + κ)) (ZMod (2 ^ 1)) →
      (Fin κ → ZMod (2 ^ 1)) → ProbComp (Option (Fin (κ + κ) → ZMod (2 ^ 1)))) :
    ComputationallySecure (fun κ => lweFuzzyExtractor κ κ κ (2 ^ 1) (decode κ))
      {fun κ => PMF.uniformOfFintype (Fin κ → ZMod (2 ^ 1))}
      (LWEFamily.Distinguisher.IsPPT (m := id) (k := id) (l := id) (w := fun _ => 1)) :=
  computationallySecure_lweFuzzyExtractor_of_decisionLWEWithErrors (m := id) (k := id) (l := id)
    (w := fun _ => 1) ComputableInPolyTime.id' ComputableInPolyTime.id' ComputableInPolyTime.id'
    (ComputableInPolyTime.const 1) decode (by
      rintro _ rfl
      exact decisionLWEWithErrors_uniform id id fun _ => 1)

open Turing.MultiTapeTM in
/-- On the source whose coordinates are independent draws from `noise κ`, the premise is
`DecisionLWE l m w noise`, the form of the assumption used by the Regev and GSW schemes. -/
example {m k l w : ℕ → ℕ} (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary) (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (decode : (κ : ℕ) → Matrix (Fin (m κ)) (Fin (k κ + l κ)) (ZMod (2 ^ w κ)) →
      (Fin (m κ) → ZMod (2 ^ w κ)) → ProbComp (Option (Fin (k κ + l κ) → ZMod (2 ^ w κ))))
    (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))) (hLWE : DecisionLWE l m w noise) :
    ComputationallySecure (fun κ => lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ))
      {fun κ => PMF.pi fun _ : Fin (m κ) => noise κ} LWEFamily.Distinguisher.IsPPT :=
  computationallySecure_lweFuzzyExtractor_of_decisionLWEWithErrors hm hk hl hw decode (by
    rintro _ rfl
    exact (decisionLWE_iff_decisionLWEWithErrors l m w noise).mp hLWE)

/-! ### Separating fixture: reproducible for all `t`, but insecure -/

/-- A fuzzy extractor on `Bool` that outputs `(w, w)`: `Rep` ignores `w'` and returns the helper
bit `p = w`, so reproduction succeeds for every distance threshold `t`, but the helper leaks the
key completely. -/
def revealingFuzzyExtractor : FuzzyExtractor Bool Bool Bool where
  gen w := return (w, w)
  rep _ p := return p

/-- `revealingFuzzyExtractor` is zero-error correct for every distance function `dis` and every
threshold `t`. -/
theorem correct_revealingFuzzyExtractor (dis : Bool → Bool → ℕ) (t : ℕ) :
    revealingFuzzyExtractor.Correct dis t := by
  intro w w' _ r p hrp r' hr'
  simp only [revealingFuzzyExtractor, ProbComp.eval_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hrp hr'
  rw [hr', hrp.2, hrp.1]

/-- The equality distinguisher on `Bool` keys and helpers, testing whether the key equals the
helper bit. -/
def eqBitDistinguisher (r p : Bool) : Experiment :=
  pure (decide (r = p))

/-- On a uniform 1-bit source, `revealingFuzzyExtractor` has distinguishing advantage `1 / 2`
against `eqBitDistinguisher`. -/
theorem securityAdvantage_revealingFuzzyExtractor :
    revealingFuzzyExtractor.securityAdvantage (PMF.uniformOfFintype Bool) eqBitDistinguisher =
      (1 : ℝ≥0) / 2 := by
  simp only [FuzzyExtractor.securityAdvantage, FuzzyExtractor.realGame_eq_bind,
    FuzzyExtractor.idealGame_eq_bind, FuzzyExtractor.realDistribution,
    FuzzyExtractor.idealDistribution, revealingFuzzyExtractor, eqBitDistinguisher,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, decide_true, PMF.bind_const,
    Game.advantage, Game.succProbability, PMF.pure_apply_self,
    PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool,
    Bool.true_eq_false, decide_false, PMF.pure_apply, Bool.false_eq_true, ↓reduceIte,
    mul_zero, mul_one, add_zero, zero_add]
  norm_num [NNReal.nndist_eq]
  rw [ENNReal.toNNReal_add] <;>
    norm_num [ENNReal.toNNReal_add, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat, ENNReal.mul_eq_top, ENNReal.inv_eq_top]
  norm_num [NNReal.sub_def, Real.toNNReal_div]
  rw [Real.toNNReal_of_nonpos (by norm_num)]
  positivity

/-! ### Reusable fuzzy extractors: shift clamping, common-matrix FMR, and strong attack -/

/-- Concrete verification of `clampShift`: a shift of Hamming weight `2` is zeroed out when the
allowed budget is `t = 1`, whereas a shift of Hamming weight `1` is preserved. -/
example : clampShift 1 ![(1 : ZMod 5), 2, 0] = 0 := by
  decide

example : clampShift 1 ![(0 : ZMod 5), 2, 0] = ![(0 : ZMod 5), 2, 0] := by
  decide

/-- Every decoder fails with probability at most `1`, so `DecoderCorrectWithError decode t 1`
holds at all parameters; the setup-averaged correctness theorems therefore apply to every decoder
with error term `1`. -/
theorem decoderCorrectWithError_one {m n q : ℕ} [NeZero q]
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))) (t : ℕ) :
    DecoderCorrectWithError decode t 1 := fun s e _ => by
  rw [Game.failProbability_eq]
  exact tsub_le_self

/-- The setup-averaged correctness theorem for the common-matrix scheme at
`m = 4, k = 1, l = 1, q = 7`, with a decoder hypothesis that every decoder meets (`δ = 1`). -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7))) (t : ℕ) :
    SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7)))
      (commonMatrixFuzzyExtractor 4 1 1 7 decode) t 1 :=
  (decoderCorrectWithError_one decode t).setupCorrect_commonMatrixFuzzyExtractor

/-- By the Theorem 1 reduction bound (`weakReuseAdvantage_commonMatrixFuzzyExtractor_le`), on a
uniform source at `m = 4, k = 1, l = 1, q = 7`, every weak-reusability adversary has advantage `0`
against the common-matrix scheme, for every error bound `t`. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7)))
    (t : ℕ) (St : Type)
    (adv : WeakReuseAdversary (Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7)) 4 7
      (Fin 1 → ZMod 7) (Fin 4 → ZMod 7) St) :
    weakReuseAdvantage (ProbComp.uniform (Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7)))
      (commonMatrixFuzzyExtractor 4 1 1 7 decode)
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) t adv = 0 := by
  have h := weakReuseAdvantage_commonMatrixFuzzyExtractor_le decode
    (PMF.uniformOfFintype (Fin 4 → ZMod 7)) t adv
  rw [lweAdvantage_uniform_error_eq_zero, lweAdvantage_uniform_error_eq_zero, add_zero] at h
  exact le_antisymm h zero_le

/-- Concrete instantiation of the Section 3.3 strong-reusability attack at
`m = 3, k = 1, l = 1, q = 5`: if the decoder fails with probability at most `δ` on error `0`, the
1-query attack has strong-reuse advantage at least `1 - δ - 1 / 5`. -/
example
    (decode : Matrix (Fin 3) (Fin (1 + 1)) (ZMod 5) → (Fin 3 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (δ : ℝ≥0) (hdec : DecoderCorrectWithError decode 0 δ) (W : PMF (Fin 3 → ZMod 5)) :
    1 - (δ : ℝ) - 1 / 5 ≤
      strongReuseAdvantage (ProbComp.uniform (Matrix (Fin 3) (Fin (1 + 1)) (ZMod 5)))
        (commonMatrixFuzzyExtractor 3 1 1 5 decode) W 0 (commonMatrixStrongAttack decode) := by
  simpa using strongReuseAdvantage_commonMatrixStrongAttack_ge hdec W 0

/-- Non-trivial correctness for the common-matrix scheme at `m = 1, k = 1, l = 0, q = 5`: with
`unitDecoder` (`δ = 1 / 5`), reproduction from an identical reading fails with probability at most
`1 / 5`, averaged over the common matrix. -/
example : SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin 1) (Fin (1 + 0)) (ZMod 5)))
    (commonMatrixFuzzyExtractor 1 1 0 5 unitDecoder) 0 (1 / 5) :=
  decoderCorrectWithError_unitDecoder.setupCorrect_commonMatrixFuzzyExtractor

/-- The Section 3.3 attack bound end to end, at `m = 1, k = 1, l = 0, q = 5` with `unitDecoder`
(`δ = 1 / 5 < 1 - 1 / q ^ k = 4 / 5`): on every source, the 1-query attack has strong-reuse
advantage at least `1 - 1 / 5 - 1 / 5 = 3 / 5`. -/
example (W : PMF (Fin 1 → ZMod 5)) :
    (3 / 5 : ℝ) ≤
      strongReuseAdvantage (ProbComp.uniform (Matrix (Fin 1) (Fin (1 + 0)) (ZMod 5)))
        (commonMatrixFuzzyExtractor 1 1 0 5 unitDecoder) W 0
        (commonMatrixStrongAttack unitDecoder) := by
  refine le_trans (le_of_eq ?_) (strongReuseAdvantage_commonMatrixStrongAttack_ge (k := 1)
    (l := 0) decoderCorrectWithError_unitDecoder W 0)
  push_cast
  norm_num

/-! ### Section 5 encryption-based strongly reusable fuzzy extractor -/

/-- Concrete verification of half-modulus encoding and `[3q / 8, 5q / 8]` threshold decoding
modulo `q = 16`: `encodeHalfBit 16 true = 8`, noisy residues `6, 7, 8, 9, 10` decode to `true`,
and noisy residues `15, 0, 1, 2` decode to `false`. -/
example : encodeHalfBit 16 true = (8 : ZMod 16) := by
  decide

example : decodeThresholdBit 16 (7 : ZMod 16) = true := by
  decide

example : decodeThresholdBit 16 (15 : ZMod 16) = false := by
  decide

/-- Concrete round-trip of `symDecrypt` on a 2-bit key modulo `q = 16` with error
`![1, -1]` (each coordinate satisfies `8 * |e_i| + 4 = 12 ≤ 16`). -/
example (s : Fin 2 → ZMod 16) (B : Matrix (Fin 2) (Fin 2) (ZMod 16)) (r : Fin 2 → Bool) :
    symDecrypt s B (B.mulVec s + ![(1 : ZMod 16), (-1 : ZMod 16)] + encodeHalfBits 16 r) = r := by
  apply symDecrypt_symEncrypt_eq
  intro i
  fin_cases i <;> decide

/-- Concrete strong-reusability bound for `lweEncryptFuzzyExtractor` at
`m = 4, n = 2, l = 2, q = 16`: the strong-reusability advantage of an adversary making at most `Q`
shift queries is bounded by two decisional LWE advantages with `4 + (Q + 1) * 2` rows. -/
example
    (E : ProbComp (Fin 2 → ZMod 16))
    (decode : Matrix (Fin 4) (Fin 2) (ZMod 16) → (Fin 4 → ZMod 16) →
      ProbComp (Option (Fin 2 → ZMod 16)))
    (W : PMF (Fin 4 → ZMod 16)) (t Q : ℕ) (St : Type)
    (adv : StrongReuseAdversary (Matrix (Fin 4) (Fin 2) (ZMod 16)) 4 16
      (Fin 2 → Bool) (EncryptHelper 4 2 2 16) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q) :
    strongReuseAdvantage (ProbComp.uniform (Matrix (Fin 4) (Fin 2) (ZMod 16)))
      (lweEncryptFuzzyExtractor 4 2 2 16 E decode) W t adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin 2 → ZMod 16))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptRealReduction t Q adv) +
      LWE.advantage (PMF.uniformOfFintype (Fin 2 → ZMod 16))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv) :=
  strongReuseAdvantage_lweEncryptFuzzyExtractor_le E decode W t Q adv hQ

/-! ### Section 5: the hypotheses are satisfiable and the bound can be attained -/

/-- Both hypotheses of the Section 5 setup-averaged correctness theorem hold at
`m = 4, n = 2, l = 2, q = 16` for the zero encryption error and every decoder (with `δ = 1`). -/
example
    (decode : Matrix (Fin 4) (Fin 2) (ZMod 16) → (Fin 4 → ZMod 16) →
      ProbComp (Option (Fin 2 → ZMod 16))) (t : ℕ) :
    SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin 4) (Fin 2) (ZMod 16)))
      (lweEncryptFuzzyExtractor 4 2 2 16 (return 0) decode) t 1 := by
  refine (decoderCorrectWithError_one decode t).setupCorrect_lweEncryptFuzzyExtractor
    ?_
  intro e he i
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at he
  subst he
  simp

/-- Non-trivial Section 5 correctness at `m = 1, n = 1, l = 1, q = 5`: with `unitDecoder`
(`δ = 1 / 5`) and the zero encryption error, reproduction from an identical reading fails with
probability at most `1 / 5`, averaged over the public matrix. -/
example : SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin 1) (Fin 1) (ZMod 5)))
    (lweEncryptFuzzyExtractor 1 1 1 5 (return 0) unitDecoder) 0 (1 / 5) := by
  refine decoderCorrectWithError_unitDecoder.setupCorrect_lweEncryptFuzzyExtractor ?_
  intro e he i
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at he
  subst he
  simp

/-- With a uniform source and uniform encryption errors, both LWE advantages in
`strongReuseAdvantage_lweEncryptFuzzyExtractor_le` vanish, so every strong-reusability adversary
making at most `Q` shift queries has advantage exactly `0`: the bound is attained, not vacuous. -/
example
    (decode : Matrix (Fin 4) (Fin 2) (ZMod 16) → (Fin 4 → ZMod 16) →
      ProbComp (Option (Fin 2 → ZMod 16)))
    (t Q : ℕ) (St : Type)
    (adv : StrongReuseAdversary (Matrix (Fin 4) (Fin 2) (ZMod 16)) 4 16
      (Fin 2 → Bool) (EncryptHelper 4 2 2 16) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q) :
    strongReuseAdvantage (ProbComp.uniform (Matrix (Fin 4) (Fin 2) (ZMod 16)))
      (lweEncryptFuzzyExtractor 4 2 2 16 (ProbComp.uniform (Fin 2 → ZMod 16)) decode)
      (PMF.uniformOfFintype (Fin 4 → ZMod 16)) t adv = 0 := by
  have h := strongReuseAdvantage_lweEncryptFuzzyExtractor_le
    (ProbComp.uniform (Fin 2 → ZMod 16)) decode (PMF.uniformOfFintype (Fin 4 → ZMod 16)) t Q adv
    hQ
  rw [ProbComp.eval_uniform, encryptLWEErrorLaw_uniform, LWE.advantage_uniform_error_eq_zero,
    LWE.advantage_uniform_error_eq_zero, add_zero] at h
  exact le_antisymm h zero_le

/-! ### A client of weak reusability -/

/-- A word reusability adversary that sends one shift request, the word of `κ` ones, keeps the
first `κ` bits of the reply as its state, and guesses the first bit of that state. At `κ` samples
and modulus `2 ^ 1`, the request is the word of the all-ones shift, of Hamming weight `κ`, and the
reply is the `κ`-bit word of a helper. -/
def oneShiftReuseAdversary : WordReuseAdversary where
  query κ _ := List.take κ <$> ProbOracleComp.query ((), List.replicate κ true)
  guess _ state _ := pure (state.headD false)

/-- At `κ` samples and modulus `2 ^ 1`, `shiftCodec` decodes the request of
`oneShiftReuseAdversary` to the all-ones shift. -/
example (κ : ℕ) :
    (shiftCodec κ 1 (LWEFamily.encVector κ 1)).decodeQuery ((), List.replicate κ true) =
      some fun _ => 1 := by
  rw [OracleCodec.decodeQuery_eq_some_iff]
  have hone : (1 : ZMod (2 ^ 1)).val = 1 := rfl
  simp [shiftCodec, LWEFamily.keyWord, Cslib.Matrix.toBinary_eq, hone]

open Turing.MultiTapeTM in
/-- The admitted class of `weaklyReusable_commonMatrixFuzzyExtractor` is inhabited:
`oneShiftReuseAdversary` is uniform strict oracle PPT. -/
theorem isPPT_oneShiftReuseAdversary : oneShiftReuseAdversary.IsPPT where
  query := by
    have hreq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 true)
        (encPair encUnary encBits) encBits := by fun_prop
    have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
        (encPair encUnary encBits) encUnary := by fun_prop
    exact (IsOraclePPTOn.query_take' () hreq hlim).isOraclePPT
  guess := by
    have hguess : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.1.headD false)
        (encPair encUnary (encPair encBits encBits)) encBool := by fun_prop
    exact hguess.isPPTOn

open Turing.MultiTapeTM in
/-- A client of `weaklyReusable_commonMatrixFuzzyExtractor` at `κ` samples, key length `κ`, `κ`
further secret coordinates, modulus `2 ^ 1` and shift bound `κ`: if the FMR family is secure on
`sources`, then `oneShiftReuseAdversary` has negligible weak-reusability advantage on each of
them. -/
example (decode : (κ : ℕ) → Matrix (Fin κ) (Fin (κ + κ)) (ZMod (2 ^ 1)) →
      (Fin κ → ZMod (2 ^ 1)) → ProbComp (Option (Fin (κ + κ) → ZMod (2 ^ 1))))
    {sources : Set ((κ : ℕ) → PMF (Fin κ → ZMod (2 ^ 1)))}
    (hFMR : ComputationallySecure (fun κ => lweFuzzyExtractor κ κ κ (2 ^ 1) (decode κ)) sources
      (LWEFamily.Distinguisher.IsPPT (m := id) (k := id) (l := id) (w := fun _ => 1)))
    {source : (κ : ℕ) → PMF (Fin κ → ZMod (2 ^ 1))} (hsource : source ∈ sources) :
    Negligible fun κ => weakReuseAdvantage
      (ProbComp.uniform (Matrix (Fin κ) (Fin (κ + κ)) (ZMod (2 ^ 1))))
      (commonMatrixFuzzyExtractor κ κ κ (2 ^ 1) (decode κ)) (source κ) κ
      (oneShiftReuseAdversary.toReuseAdversary κ 1 (LWEFamily.encView κ (κ + κ) 1)
        (LWEFamily.encVector κ 1) (LWEFamily.encVector κ 1) κ) :=
  weaklyReusable_commonMatrixFuzzyExtractor (m := id) (k := id) (l := id) (w := fun _ => 1)
    ComputableInPolyTime.id' ComputableInPolyTime.id' ComputableInPolyTime.id'
    (ComputableInPolyTime.const 1) ComputableInPolyTime.id' decode hFMR source hsource
    oneShiftReuseAdversary isPPT_oneShiftReuseAdversary

end CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest
