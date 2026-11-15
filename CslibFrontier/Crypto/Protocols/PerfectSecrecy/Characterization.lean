/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
import CslibFrontier.Probability.PMF.Map

/-!
# Characterizations of perfect security (Boneh–Shoup §2.1.2)

The equivalent forms of perfect security that [BonehShoup2023], v0.6, §2.1.2 (printed pp. 8–12)
states for Shannon ciphers, on the information-theoretic encryption schemes `EncScheme`.

A Shannon cipher `(E, D)` over `(K, M, C)` with its uniformly random key is
`EncScheme.ofPure (uniformOfFintype K) enc dec h`, where `h` is the book's correctness property
`D(k, E(k, m)) = m`. Its `CiphertextIndist` (equal ciphertext laws for any two messages) is the
book's Definition 2.1 (perfect security, p. 8): two laws on `C` are equal exactly when they give
every ciphertext the same mass. The library's `PerfectlySecret` is instead the posterior form of
[KatzLindell2020], Definition 2.3; `perfectlySecret_iff_ciphertextIndist` converts between
the two, so every result below also characterizes `PerfectlySecret`.

The ciphertext law of a deterministic scheme is the image of its key law
(`ciphertextDist_ofPure`), and under a uniform key the mass of `c` given `m` is the number of keys
taking `m` to `c` over `|K|` (`ciphertextDist_ofPure_uniformOfFintype_apply`): the identity
`P_c = N_c / |K|` in the proof of Theorem 2.1 (p. 9).

All of this is information-theoretic: there is no adversary and no resource bound.

## Main results

* `ciphertextIndist_ofPure_uniformOfFintype_iff`: Theorem 2.1, (i) ⇔ (ii) (pp. 8–9). Condition
  (iii) of that theorem is `CiphertextIndist` itself.
* `ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique`: the criterion `N_c = 1` (one key for
  each message and ciphertext) by which the book proves Theorem 2.2 and Example 2.7.
* `ciphertextIndist_iff_forall_toOuterMeasure`: Theorem 2.3 (pp. 10–11) for every scheme, with
  events `S : Set C` in place of predicates on `C`.
* `ciphertextIndist_iff_jointDist_eq_mul`: Theorem 2.4 (pp. 11–12) for every scheme and one message
  law of full support.

## Deviations from [BonehShoup2023]

* The book assumes `K`, `M` and `C` finite (§2.1.1, p. 5). Here only `K` is finite and nonempty,
  which the uniform key law needs; `M` and `C` are arbitrary types, in one universe with `K` as
  `EncScheme.ofPure` requires.
* Theorems 2.3 and 2.4 are stated for every `EncScheme`: randomized encryption and any key law. The
  book's case is `ofPure (uniformOfFintype K) enc dec h`.
* In Theorem 2.1 (ii) the integer `N_c` is a natural number, as a count of keys is.
* In Theorem 2.3 the book's predicates `φ` on `C` are events `S : Set C`.
* Theorem 2.4 is stated as one equivalence for a message law of full support. The book's first
  half holds for every message law; that is `indep_of_ciphertextIndist`.
* Independence in Theorem 2.4 is the factorization `Pr[m = m ∧ c = c] = Pr[m = m] · Pr[c = c]` of
  the joint law, not Mathlib's `ProbabilityTheory.IndepFun`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

open Cslib.Probability.PMF

open scoped ENNReal

universe u

variable {M K C : Type u}

/-- The ciphertext law of a deterministic scheme is the image of its key law under `E(·, m)`. -/
@[simp]
theorem ciphertextDist_ofPure (gen : PMF K) (enc : K → M → C) (dec : K → C → M)
    (h : ∀ k, Function.LeftInverse (dec k) (enc k)) (m : M) :
    (ofPure gen enc dec h).ciphertextDist m = gen.map (enc · m) :=
  rfl

/-- Under a uniformly random key, a deterministic scheme sends `m` to `c` with probability the
number of keys `k` with `E(k, m) = c`, divided by `|K|`. This is the identity `P_c = N_c / |K|` in
the proof of [BonehShoup2023], Theorem 2.1 (p. 9). -/
theorem ciphertextDist_ofPure_uniformOfFintype_apply [Fintype K] [Nonempty K]
    (enc : K → M → C) (dec : K → C → M) (h : ∀ k, Function.LeftInverse (dec k) (enc k))
    (m : M) (c : C) :
    (ofPure (uniformOfFintype K) enc dec h).ciphertextDist m c =
      (Nat.card {k // enc k m = c} : ℝ≥0∞) / Fintype.card K := by
  rw [ciphertextDist_ofPure, uniformOfFintype_map_apply]

/-- **Counting criterion for perfect security**: [BonehShoup2023], Theorem 2.1, (i) ⇔ (ii)
(pp. 8–9). A Shannon cipher with a uniform key is perfectly secure (Definition 2.1) if and only if,
for every ciphertext `c`, the number of keys `k` with `E(k, m) = c` is the same for all messages
`m`.

The book takes `K`, `M`, `C` finite and `N_c` an integer; here only `K` is finite (and nonempty)
and `N_c` is a natural number. Condition (iii) of the theorem, that the laws of `E(k, m)` agree for
all `m`, is `CiphertextIndist` itself. `perfectlySecret_iff_ciphertextIndist` converts the left side
to the library's `PerfectlySecret`. -/
theorem ciphertextIndist_ofPure_uniformOfFintype_iff [Fintype K] [Nonempty K]
    (enc : K → M → C) (dec : K → C → M) (h : ∀ k, Function.LeftInverse (dec k) (enc k)) :
    (ofPure (uniformOfFintype K) enc dec h).CiphertextIndist ↔
      ∀ c, ∃ N : ℕ, ∀ m, Nat.card {k // enc k m = c} = N := by
  have hK : (Fintype.card K : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hK' : (Fintype.card K : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (by simp)
  simp only [CiphertextIndist, PMF.ext_iff, ciphertextDist_ofPure_uniformOfFintype_apply,
    div_eq_mul_inv, ENNReal.mul_left_inj hK hK', Nat.cast_inj]
  refine ⟨fun hI c => ?_, fun hN m₀ m₁ c => ?_⟩
  · rcases isEmpty_or_nonempty M with hM | ⟨⟨m₀⟩⟩
    · exact ⟨0, isEmptyElim⟩
    · exact ⟨_, fun m => hI m m₀ c⟩
  · obtain ⟨N, hN⟩ := hN c
    rw [hN m₀, hN m₁]

/-- **One key per message and ciphertext**: a Shannon cipher with a uniform key in which, for every
message `m` and ciphertext `c`, exactly one key encrypts `m` to `c` is perfectly secure
(Definition 2.1). This is the case `N_c = 1` of Theorem 2.1 (ii), by which [BonehShoup2023] proves
the one-time pad perfectly secure (Theorem 2.2, p. 9) and the additive one-time pad (Example 2.7,
p. 10). -/
theorem ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique [Fintype K] [Nonempty K]
    (enc : K → M → C) (dec : K → C → M) (h : ∀ k, Function.LeftInverse (dec k) (enc k))
    (huniq : ∀ m c, ∃! k, enc k m = c) :
    (ofPure (uniformOfFintype K) enc dec h).CiphertextIndist := by
  classical
  refine (ciphertextIndist_ofPure_uniformOfFintype_iff enc dec h).mpr fun c => ⟨1, fun m => ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Fintype.existsUnique_iff_card_one]
  exact huniq m c

/-- **Perfect security as equal event probabilities**: [BonehShoup2023], Theorem 2.3 (pp. 10–11),
generalized from Shannon ciphers with a uniform key to every scheme, with randomized encryption and
any key law. A scheme has equal ciphertext laws for any two messages if and only if every event
`S` on ciphertexts has the same probability under any two messages.

The book's predicates `φ` on `C` are the events `S = {c | φ c}`; its statement is the case
`scheme = ofPure (uniformOfFintype K) enc dec h`, where `CiphertextIndist` is Definition 2.1. The
theorem is Mathlib's `PMF.toOuterMeasure_inj` read for the ciphertext laws: what it adds is the
book's formulation, not a new argument. As in the book's proof, the converse needs only singleton
events. -/
theorem ciphertextIndist_iff_forall_toOuterMeasure (scheme : EncScheme M K C) :
    scheme.CiphertextIndist ↔ ∀ (S : Set C) (m₀ m₁ : M),
      (scheme.ciphertextDist m₀).toOuterMeasure S = (scheme.ciphertextDist m₁).toOuterMeasure S :=
  ⟨fun h S m₀ m₁ => by rw [h m₀ m₁], fun h m₀ m₁ =>
    PMF.toOuterMeasure_injective (MeasureTheory.OuterMeasure.ext fun S => h S m₀ m₁)⟩

/-- **Perfect security as independence of message and ciphertext**: [BonehShoup2023], Theorem 2.4
(pp. 11–12), for every scheme and one message law `msgDist` that gives every message nonzero
probability. The message is drawn from `msgDist` and, independently, the key from the scheme's key
law; the scheme has equal ciphertext laws for any two messages if and only if message and ciphertext
are independent, written as `Pr[m = m ∧ c = c] = Pr[m = m] · Pr[c = c]`, the form the book's proof
uses.

The book states the theorem for Shannon ciphers with a uniform key, the case
`scheme = ofPure (uniformOfFintype K) enc dec h`. Its first half, that perfect security gives
independence, holds for every message law and is `indep_of_ciphertextIndist`; full support
is used only for the converse, which is the book's second half. The converse is false without it:
the identity cipher on `Bool` with a point-mass message law satisfies the factorization and is not
`CiphertextIndist`. -/
theorem ciphertextIndist_iff_jointDist_eq_mul (scheme : EncScheme M K C) (msgDist : PMF M)
    (hfull : ∀ m, msgDist m ≠ 0) :
    scheme.CiphertextIndist ↔ ∀ m c,
      scheme.jointDist msgDist (m, c) = msgDist m * scheme.marginalCiphertextDist msgDist c := by
  refine ⟨fun h => scheme.indep_of_ciphertextIndist h msgDist, fun h m₀ m₁ => ?_⟩
  have hmarg (m : M) (c : C) :
      scheme.ciphertextDist m c = scheme.marginalCiphertextDist msgDist c :=
    (ENNReal.mul_right_inj (hfull m) (PMF.apply_ne_top _ _)).mp (by rw [← jointDist_eq, h])
  exact PMF.ext fun c => (hmarg m₀ c).trans (hmarg m₁ c).symm

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
