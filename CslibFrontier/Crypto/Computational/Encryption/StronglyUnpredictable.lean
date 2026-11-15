/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Negligible
public import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Map

/-!
# Strongly unpredictable ciphertexts

A public-key encryption algorithm (possibly fallible, represented as `Option (C n)` where `none`
models an encryption error) has **strongly unpredictable ciphertexts** ([BonehShoup2023], §21.4.1,
p. 872) if there is a negligible function `ε : ℕ → ℝ≥0` such that at every security parameter `n`,
for every public key `pk : PK n` (including adversarially chosen or malformed keys), every message
`m : Msg n`, and every non-error ciphertext `c : C n`, the probability that encrypting `m` under
`pk` outputs `some c` is at most `ε n`.

Fixed-type schemes (`PK Msg C : Type`) are instances of `StronglyUnpredictable` by unification with
constant type families `fun _ => PK`, `fun _ => Msg`, `fun _ => C`.

## Main definitions

* `Cslib.Crypto.Encryption.CiphertextHitBound`: uniform pointwise upper bound `ε` on
  `Pr[encrypt pk m = some c]` at a single security parameter.
* `Cslib.Crypto.Encryption.StronglyUnpredictable`: existence of a negligible uniform ciphertext
  hit bound across all security parameters, public keys, messages, and non-error ciphertexts.

## Main results

* `Cslib.Crypto.Encryption.ciphertextHitBound_map_some_iff`: characterization for total encryption
  algorithms `some <$> encrypt pk m`.
* `Cslib.Crypto.Encryption.CiphertextHitBound.collision_le`: two independent invocations (even under
  distinct adversarially chosen keys and messages) output the same non-error ciphertext with
  probability at most `ε` ([BonehShoup2023], §21.9.6, p. 897).
* `Cslib.Crypto.Encryption.stronglyUnpredictable_iff_forall`: equivalence with sequential
  negligibility over arbitrary sequences `(pk, m, c)` under `Nonempty` key, message, and ciphertext
  types.
* `Cslib.Crypto.Encryption.StronglyUnpredictable.negligible_collision`: negligible non-error
  ciphertext collision probability across two independent invocations.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section
  21.4.1 (p. 872) and Section 21.9.6 (p. 897).
-/

public section

namespace Cslib.Crypto.Encryption

open Cslib.Probability
open scoped NNReal ENNReal

/-- At one security parameter, a fallible encryption algorithm
`encrypt : PK → Msg → ProbComp (Option C)` (`none` represents `error`) has ciphertext hit
probability at most `ε` if for every public key `pk`, message `m`, and non-error ciphertext
`some c`, `Pr[encrypt pk m = some c] ≤ ε`. -/
@[expose] def CiphertextHitBound {PK Msg C : Type}
    (encrypt : PK → Msg → ProbComp (Option C)) (ε : ℝ≥0) : Prop :=
  ∀ (pk : PK) (m : Msg) (c : C),
    ((ProbComp.eval (encrypt pk m)) (some c)).toNNReal ≤ ε

/-- For an infallible encryption algorithm lifted by `some <$> ·`, `CiphertextHitBound` reduces
directly to bounding `Pr[encrypt pk m = c] ≤ ε`. -/
theorem ciphertextHitBound_map_some_iff {PK Msg C : Type}
    (encrypt : PK → Msg → ProbComp C) (ε : ℝ≥0) :
    CiphertextHitBound (fun pk m => some <$> encrypt pk m) ε ↔
      ∀ (pk : PK) (m : Msg) (c : C), ((ProbComp.eval (encrypt pk m)) c).toNNReal ≤ ε := by
  simp only [CiphertextHitBound, ProbComp.eval_map,
    Cslib.Probability.PMF.map_apply_of_injective _ (Option.some_injective _)]

/-- If `encrypt` has ciphertext hit bound `ε`, then two independent invocations (even under
distinct adversarially chosen public keys and messages) output the same non-error ciphertext with
probability at most `ε` ([BonehShoup2023], §21.9.6, p. 897). -/
theorem CiphertextHitBound.collision_le {PK Msg C : Type} [DecidableEq C]
    {encrypt : PK → Msg → ProbComp (Option C)} {ε : ℝ≥0}
    (h : CiphertextHitBound encrypt ε) (pk₁ pk₂ : PK) (m₁ m₂ : Msg) :
    ((ProbComp.eval (do
      let c₁ ← encrypt pk₁ m₁
      let c₂ ← encrypt pk₂ m₂
      return decide (c₁ = c₂ ∧ c₁.isSome))) true).toNNReal ≤ ε := by
  let p₁ := ProbComp.eval (encrypt pk₁ m₁)
  let p₂ := ProbComp.eval (encrypt pk₂ m₂)
  have heval :
      (ProbComp.eval (do
        let c₁ ← encrypt pk₁ m₁
        let c₂ ← encrypt pk₂ m₂
        return decide (c₁ = c₂ ∧ c₁.isSome))) true =
        ∑' c : C, p₁ (some c) * p₂ (some c) := by
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_apply, PMF.pure_apply]
    rw [tsum_option_eq]
    simp [p₁, p₂]
  have hle : ∑' c : C, p₁ (some c) * p₂ (some c) ≤ (ε : ℝ≥0∞) := by
    calc ∑' c : C, p₁ (some c) * p₂ (some c)
        ≤ ∑' c : C, p₁ (some c) * (ε : ℝ≥0∞) := by
          refine tsum_le_tsum fun c => ?_
          have hp2 : p₂ (some c) ≤ (ε : ℝ≥0∞) :=
            (ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)).symm ▸
              ENNReal.coe_le_coe.mpr (h pk₂ m₂ c)
          gcongr
      _ = (∑' c : C, p₁ (some c)) * (ε : ℝ≥0∞) := ENNReal.tsum_mul_right
      _ ≤ 1 * (ε : ℝ≥0∞) := by
          gcongr
          have hsum : ∑' c : Option C, p₁ c = 1 := p₁.tsum_coe
          rw [← hsum, tsum_option_eq]
          exact le_add_self
      _ = (ε : ℝ≥0∞) := one_mul _
  rw [heval]
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hle).trans_eq (ENNReal.toNNReal_coe ε)

/-- **Strongly unpredictable ciphertexts** ([BonehShoup2023], §21.4.1, p. 872) for a family of
fallible encryption algorithms `encrypt : ∀ n, PK n → Msg n → ProbComp (Option (C n))` (`none`
represents `error`): there exists a negligible bound `ε : ℕ → ℝ≥0` such that at every security
parameter `n`, every public key `pk : PK n` (including adversarially chosen ones), every message
`m : Msg n`, and every non-error ciphertext `some c`, `Pr[encrypt n pk m = some c] ≤ ε n`. -/
@[expose] def StronglyUnpredictable {PK Msg C : ℕ → Type}
    (encrypt : ∀ n, PK n → Msg n → ProbComp (Option (C n))) : Prop :=
  ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, CiphertextHitBound (encrypt n) (ε n)

/-- Construct `StronglyUnpredictable` from a negligible hit-bound sequence `B`. -/
theorem StronglyUnpredictable.of_bound {PK Msg C : ℕ → Type}
    {encrypt : ∀ n, PK n → Msg n → ProbComp (Option (C n))} {B : ℕ → ℝ≥0}
    (hB : Negligible B) (hbound : ∀ n, CiphertextHitBound (encrypt n) (B n)) :
    StronglyUnpredictable encrypt :=
  ⟨B, hB, hbound⟩

/-- Under `Nonempty` public-key, message, and ciphertext types, uniform strong ciphertext
unpredictability is equivalent to requiring `Pr[encrypt n (pk n) (m n) = some (c n)]` to be
negligible for every sequence `(pk, m, c)` ([BonehShoup2023], §21.4.1, p. 872). -/
theorem stronglyUnpredictable_iff_forall {PK Msg C : ℕ → Type}
    [∀ n, Nonempty (PK n)] [∀ n, Nonempty (Msg n)] [∀ n, Nonempty (C n)]
    (encrypt : ∀ n, PK n → Msg n → ProbComp (Option (C n))) :
    StronglyUnpredictable encrypt ↔
      ∀ (pk : ∀ n, PK n) (m : ∀ n, Msg n) (c : ∀ n, C n),
        Negligible fun n => ((ProbComp.eval (encrypt n (pk n) (m n))) (some (c n))).toNNReal := by
  constructor
  · rintro ⟨ε, hε, hbound⟩ pk m c
    exact negligible_of_le hε fun n => hbound n (pk n) (m n) (c n)
  · intro hforall
    let S : ℕ → Set ℝ≥0 := fun n =>
      {x | ∃ (pk : PK n) (m : Msg n) (c : C n),
        x = ((ProbComp.eval (encrypt n pk m)) (some c)).toNNReal}
    have hne (n : ℕ) : (S n).Nonempty :=
      ⟨_, Classical.arbitrary _, Classical.arbitrary _, Classical.arbitrary _, rfl⟩
    have hbdd (n : ℕ) : BddAbove (S n) := by
      refine ⟨1, ?_⟩
      rintro x ⟨pk, m, c, rfl⟩
      exact (ENNReal.toNNReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)).trans_eq
        ENNReal.toNNReal_one
    let ε : ℕ → ℝ≥0 := fun n => sSup (S n)
    have hbound (n : ℕ) : CiphertextHitBound (encrypt n) (ε n) :=
      fun pk m c => le_csSup (hbdd n) ⟨pk, m, c, rfl⟩
    refine ⟨ε, ?_, hbound⟩
    by_contra hnot
    rw [negligible_iff] at hnot
    push Not at hnot
    rcases hnot with ⟨k, δ, hδpos, hbad⟩
    have hhalf_pos : (0 : ℝ≥0) < δ / 2 := half_pos hδpos
    have hhalf_lt : δ / 2 < δ := NNReal.half_lt_self hδpos.ne'
    have hwitness (n : ℕ) :
        ∃ (pk : PK n) (m : Msg n) (c : C n),
          δ ≤ (n : ℝ≥0) ^ k * ε n →
            δ / 2 < (n : ℝ≥0) ^ k * ((ProbComp.eval (encrypt n pk m)) (some c)).toNNReal := by
      by_cases hcond : δ ≤ (n : ℝ≥0) ^ k * ε n
      · have hnk_pos : (0 : ℝ≥0) < (n : ℝ≥0) ^ k := by
          by_contra h0
          have hnk0 : (n : ℝ≥0) ^ k = 0 := le_antisymm (not_lt.mp h0) zero_le
          rw [hnk0, zero_mul] at hcond
          exact not_le_of_gt hδpos hcond
        have hlt_sup : (δ / 2) / (n : ℝ≥0) ^ k < sSup (S n) := by
          rw [div_lt_iff₀ hnk_pos, mul_comm]
          exact hhalf_lt.trans_le hcond
        rcases (lt_csSup_iff (hbdd n) (hne n)).mp hlt_sup with ⟨x, ⟨pk, m, c, rfl⟩, hx⟩
        refine ⟨pk, m, c, fun _ => ?_⟩
        rwa [div_lt_iff₀ hnk_pos, mul_comm] at hx
      · exact ⟨Classical.arbitrary _, Classical.arbitrary _, Classical.arbitrary _,
          fun h => False.elim (hcond h)⟩
    let pkSeq : ∀ n, PK n := fun n => (hwitness n).choose
    let mSeq : ∀ n, Msg n := fun n => (hwitness n).choose_spec.choose
    let cSeq : ∀ n, C n := fun n => (hwitness n).choose_spec.choose_spec.choose
    have hspec (n : ℕ) := (hwitness n).choose_spec.choose_spec.choose_spec
    have hneg := hforall pkSeq mSeq cSeq
    rw [negligible_iff] at hneg
    rcases hneg k (δ / 2) hhalf_pos with ⟨M, hM⟩
    rcases hbad M with ⟨n, hnM, hnδ⟩
    exact not_lt_of_gt (hspec n hnδ) (hM n hnM)

/-- If `encrypt` has strongly unpredictable ciphertexts, then two independent invocations (even
under adversarially chosen sequences of keys and messages) collide on a non-error ciphertext with
negligible probability ([BonehShoup2023], §21.9.6, p. 897). -/
theorem StronglyUnpredictable.negligible_collision {PK Msg C : ℕ → Type}
    [∀ n, DecidableEq (C n)]
    {encrypt : ∀ n, PK n → Msg n → ProbComp (Option (C n))}
    (h : StronglyUnpredictable encrypt)
    (pk₁ pk₂ : ∀ n, PK n) (m₁ m₂ : ∀ n, Msg n) :
    Negligible fun n =>
      ((ProbComp.eval (do
        let c₁ ← encrypt n (pk₁ n) (m₁ n)
        let c₂ ← encrypt n (pk₂ n) (m₂ n)
        return decide (c₁ = c₂ ∧ c₁.isSome))) true).toNNReal := by
  rcases h with ⟨ε, hε, hbound⟩
  exact negligible_of_le hε fun n => (hbound n).collision_le (pk₁ n) (pk₂ n) (m₁ n) (m₂ n)

end Cslib.Crypto.Encryption
