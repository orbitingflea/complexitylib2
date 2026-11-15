/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import Mathlib.Data.Nat.Prime.Basic

/-!
# The integer factoring experiment and assumption

The modulus-only integer factoring experiment `modulusFactoringGame` and hardness assumption
`ModulusFactoringHard` ([KatzLindell2020], Section 9.2.3, Definition 9.45), parameterized by an
arbitrary modulus distribution `modGen : ℕ → PMF ℕ`.

Also provides the shared challenge-input encoding `encModulusChallengeInput` (`(1^n, (N, y))`) used
by modulus-parameterized assumptions (`QuadraticResiduosityHard`, `DCR`, `RabinOneWay`) and their
reductions to integer factoring, together with the semiprime unique-factorization lemma
`mul_eq_mul_primes_cases`.

## Main definitions

* `Cslib.Crypto.encModulusChallengeInput`: canonical encoding `(1^n, (N, y))` of a unary security
  parameter `n`, binary modulus `N`, and binary challenge element `y`.
* `Cslib.Crypto.modulusFactoringGame`, `Cslib.Crypto.ModulusFactoringHard`: the integer factoring
  experiment and assumption for a modulus distribution family `modGen : ℕ → PMF ℕ`.

## Main results

* `Cslib.Crypto.ModulusFactoringHard.congr`: transfers `ModulusFactoringHard` along pointwise
  equality of modulus distributions.
* `Cslib.Crypto.mul_eq_mul_primes_cases`: every nontrivial factorization `a * b = p * q` of a
  product of two primes `p` and `q` permutes `(p, q)`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 9.2.3, Definition 9.45 (The Factoring Assumption).
  This is the source of the definitions.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], context
  only: the book states no factoring experiment or assumption. Section 16.4, p. 696 (Analyzing the
  factoring and RSA assumptions), and the remark in Section 10.3, p. 404, that RSA can be one-way
  only if factoring is hard.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Canonical input encoding `(1^n, (N, y))` for a security parameter `n` in unary and a modulus
`N` and challenge element `y` in binary. -/
abbrev encModulusChallengeInput : (ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encUnary (encPair encNat encNat)

/-- The modulus-only integer factoring experiment ([KatzLindell2020], Section 9.2.3,
Definition 9.45): sample `N ← modGen n`, run `A n N`, and accept when `A` returns a nontrivial
factorization `1 < a`, `1 < b`, `a * b = N`. -/
noncomputable def modulusFactoringGame (modGen : ℕ → PMF ℕ) (A : ℕ → ℕ → ProbComp (ℕ × ℕ))
    (n : ℕ) : Game := do
  let N ← modGen n
  let ab ← ProbComp.eval (A n N)
  return decide (1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N)

/-- The integer factoring assumption for a modulus distribution family `modGen : ℕ → PMF ℕ`
([KatzLindell2020], Section 9.2.3, Definition 9.45): every uniform PPT factoring algorithm succeeds
with negligible probability. In place of the source's `GenModulus`, `modGen` is any law on `ℕ`,
which need not be efficiently samplable or supported on products of two primes. -/
def ModulusFactoringHard (modGen : ℕ → PMF ℕ) : Prop :=
  ∀ A : ℕ → ℕ → ProbComp (ℕ × ℕ),
    IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => A input.1 input.2) →
    Negligible (fun n => Game.succProbability (modulusFactoringGame modGen A n))

/-- Transfer `ModulusFactoringHard` along pointwise equality of modulus distributions. -/
theorem ModulusFactoringHard.congr {modGen₁ modGen₂ : ℕ → PMF ℕ}
    (h : ModulusFactoringHard modGen₁) (heq : ∀ n, modGen₁ n = modGen₂ n) :
    ModulusFactoringHard modGen₂ := by
  intro A hA
  refine (h A hA).congr fun n => ?_
  simp [modulusFactoringGame, heq n]

/-- Every nontrivial factorization `a * b = p * q` of a product of two primes `p` and `q`
permutes `(p, q)`. -/
theorem mul_eq_mul_primes_cases {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (hb : 1 < b) (hab : a * b = p * q) :
    (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  have hdvd : a ∣ p * q := ⟨b, hab.symm⟩
  by_cases hpa : p ∣ a
  · rcases hpa with ⟨k, rfl⟩
    have hkb : k * b = q := by
      have : p * (k * b) = p * q := by rw [← mul_assoc]; exact hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rcases (Nat.dvd_prime hq).mp ⟨b, hkb.symm⟩ with rfl | hk
    · left; exact ⟨mul_one p, by simpa using hkb⟩
    · rw [hk] at hkb
      have hb1 : b = 1 := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa using hkb)
      omega
  · have haq : a ∣ q := (hp.coprime_iff_not_dvd.mpr hpa).symm.dvd_of_dvd_mul_left hdvd
    rcases (Nat.dvd_prime hq).mp haq with rfl | rfl
    · exact absurd ha (by omega)
    · right
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hq.pos (by rw [hab, mul_comm])⟩

end Cslib.Crypto
