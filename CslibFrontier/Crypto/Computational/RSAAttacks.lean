/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
public import CslibFrontier.Crypto.Computational.Factoring
public import CslibFrontier.Crypto.Computational.RSACommonRoot
public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import Mathlib.Data.Nat.ChineseRemainder
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Algebra.Group.ZPowCoprime
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Units

/-!
# Attacks on plain RSA, factoring from RSA secrets, and the RSA-to-factoring hierarchy

Algebraic attacks on plain (textbook) RSA encryption `c = m ^ e % N` (`rsaEval`), the elementary
steps that recover the factorization of `N` from secret RSA data, and the polynomial-time
reductions connecting `RSAOneWay`, `RSAKeyRecoveryHard`, `TotientHard`, and
`ModulusFactoringHard`.

* **Malleability.** `rsaEval` is multiplicative, so anyone can turn an encryption of `m` into an
  encryption of `m * s % N`.
* **Common modulus.** Two encryptions `c₁`, `c₂` of the same unit `m` under one modulus `N` and
  coprime exponents `e₁, e₂` reveal `m`: Shamir's trick `commonRoot N e₂ e₁ c₁ c₂` from
  `RSACommonRoot.lean` returns `m % N` (`commonRoot_rsaEval`).
* **Small messages and the broadcast attack.** If `m ^ e < N`, the ciphertext is `m ^ e` over the
  integers, so `m` is its integer `e`-th root. If the same `m` is sent to receivers with pairwise
  coprime moduli whose product exceeds `m ^ e`, the Chinese remainder combination of the
  ciphertexts is again `m ^ e`.
* **Factoring from `φ(N)` and `TotientHard ↔ ModulusFactoringHard`.** `N = p * q` and
  `φ(N) = (p - 1) * (q - 1)` determine `p + q` and `(p - q) ^ 2`, hence `p` and `q` in polynomial
  time (`factorOfTotient`, `computableInPolyTime_factorOfTotient`), giving the polynomial-time
  equivalence `totientHard_iff_modulusFactoringHard` (after [KatzLindell2020], Theorem 9.49).
* **Computing `d` from `φ(N)` and `RSAOneWay ⇒ RSAKeyRecoveryHard ⇒ TotientHard ⇔
  ModulusFactoringHard`.** Given `(N, e)` and `φ(N)`, the unsigned extended Euclidean algorithm
  `BinaryGcd.modInv e φ(N)` recovers a valid private exponent `d'`, and `rsaInvert N d'` inverts
  `rsaEval N e` on all residues modulo `N` (`RSAOneWay.rsaKeyRecoveryHard`,
  `RSAOneWay.totientHard`, `RSAOneWay.modulusFactoringHard`).
* **Factoring from `(N, e, d)` and nontrivial square roots of `1`.** Every unit `x` modulo `N`
  satisfies `x ^ (e * d - 1) ≡ 1`, and for any `N` and `y`, a square root `y` of `1` modulo
  `N` other than `±1` gives the proper factors `gcd(y - 1, N)` and `gcd(y + 1, N)`
  (`gcd_sub_one_proper_of_sq_modEq_one`, `gcd_add_one_proper_of_sq_modEq_one`)
  [Arora–Barak, Lemma 20.24][AroraBarak07].

## Main definitions

* `Cslib.Crypto.factorOfTotient`: the two factors of `N` computed from `N` and `φ(N)`.
* `Cslib.Crypto.totientGame`, `Cslib.Crypto.TotientHard`, `Cslib.Crypto.factorToTotient`,
  `Cslib.Crypto.totientToFactor`: the Euler totient computation experiment, assumption, and PPT
  reductions to and from integer factoring.
* `Cslib.Crypto.rsaKeyRecoveryGame`, `Cslib.Crypto.RSAKeyRecoveryHard`,
  `Cslib.Crypto.totientToKeyRecovery`, `Cslib.Crypto.keyRecoveryToRSA`,
  `Cslib.Crypto.factorToRSA`: the RSA private-exponent recovery experiment, assumption, and PPT
  reductions to totient computation, integer factoring, and RSA inversion.

## Main results

* `Cslib.Crypto.rsaEval_mul`, `Cslib.Crypto.rsaInvert_rsaEval_mul`: plain RSA is multiplicatively
  homomorphic, and the blinded ciphertext decrypts to `m * s % N`.
* `Cslib.Crypto.commonRoot_rsaEval`: the common-modulus attack `commonRoot N e₂ e₁ c₁ c₂` recovers
  `m % N` for every unit `m` and coprime `e₁`, `e₂`.
* `Cslib.Crypto.rsaEval_eq_pow_of_pow_lt`, `Cslib.Crypto.eq_of_pow_eq_rsaEval`: a short message is
  the unique integer `e`-th root of its ciphertext.
* `Cslib.Crypto.chineseRemainderOfList_rsaEval_eq_pow`: the broadcast attack.
* `Cslib.Crypto.factorOfTotient_eq`, `Cslib.Crypto.RSADesc.factorOfTotient_eq`,
  `Cslib.Crypto.computableInPolyTime_factorOfTotient`: factoring from `φ(N)` in polynomial time.
* `Cslib.Crypto.totientHard_iff_modulusFactoringHard`: computing `φ(N)` from `N = p * q` is
  polynomial-time equivalent to factoring `N` (after [KatzLindell2020], Theorem 9.49).
* `Cslib.Crypto.RSAKeyRecoveryHard.totientHard`,
  `Cslib.Crypto.RSAKeyRecoveryHard.modulusFactoringHard`,
  `Cslib.Crypto.RSAOneWay.rsaKeyRecoveryHard`, `Cslib.Crypto.RSAOneWay.totientHard`,
  `Cslib.Crypto.RSAOneWay.modulusFactoringHard`:
  `RSAOneWay` implies private-exponent recovery hardness, totient hardness, and integer factoring
  hardness.
* `Cslib.Crypto.gcd_sub_one_proper_of_sq_modEq_one`,
  `Cslib.Crypto.gcd_add_one_proper_of_sq_modEq_one`,
  `Cslib.Crypto.RSADesc.pow_mul_sub_one_modEq_one`, `Cslib.Crypto.RSADesc.gcd_sub_one_proper`,
  `Cslib.Crypto.RSADesc.gcd_add_one_proper`: factoring from a nontrivial square root of `1` modulo
  `N`, and the number-theoretic steps of factoring from `(N, e, d)`.

## Implementation notes

The common-modulus attack is the program `commonRoot` of `RSACommonRoot.lean` on the two
ciphertexts, so `computableInPolyTime_commonRoot` is its polynomial-time certificate; its
correctness statement requires coprime exponents and `m` coprime to `N`.

The deterministic polynomial-time reductions
`TotientHard gen ↔ ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus)` ([KatzLindell2020],
Theorem 9.49) and `RSAOneWay gen → RSAKeyRecoveryHard gen → TotientHard gen` are proved in full.
The two statements on factoring from `(N, e, d)` are the deterministic ingredients of the reverse
direction `ModulusFactoringHard → RSAKeyRecoveryHard` ([KatzLindell2020], Theorem 9.50 and
Corollary 9.51, Section 9.2.5), which also needs the probability bound that a random unit leads to
a nontrivial square root of `1`; that probabilistic algorithm and its analysis are not formalized
here, so Theorem 9.50 and Corollary 9.51 themselves are not claimed.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach* (2007 draft)][AroraBarak07],
  Lemma 20.24.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 9.2.5, pp. 333–336 (Theorem 9.49, Theorem 9.50, and Corollary 9.51) and
  Section 12.5.1, pp. 436–440 (plain RSA encryption Construction 12.26 and its attacks for
  small messages and for one message sent to several receivers).
  This is the source of the definitions.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], context
  only: the book has no private-exponent recovery experiment. Section 10.3, Attack Game 10.3
  (p. 404) and Definition 10.5 (p. 405) state the RSA assumption, and Section 16.4, p. 696, gives
  the algorithm that factors `N`, computes `d` and then inverts.
-/

public section

namespace Cslib.Crypto

/-! ### Malleability -/

/-- Plain RSA is multiplicatively homomorphic: the encryption of a product is the product of the
encryptions, reduced modulo `N`. -/
theorem rsaEval_mul (N e m s : ℕ) :
    rsaEval N e (m * s) = rsaEval N e m * rsaEval N e s % N := by
  unfold rsaEval
  rw [mul_pow, Nat.mul_mod]

/-- Malleability of plain RSA: multiplying a ciphertext of `m` by the encryption of any `s` gives
a ciphertext that decrypts to `m * s % N`. -/
theorem rsaInvert_rsaEval_mul (desc : RSADesc) (m s : ℕ) :
    rsaInvert desc.modulus desc.d
        (rsaEval desc.modulus desc.e m * rsaEval desc.modulus desc.e s % desc.modulus) =
      m * s % desc.modulus := by
  rw [← rsaEval_mul, show rsaEval desc.modulus desc.e (m * s) =
      rsaEval desc.modulus desc.e (m * s % desc.modulus) by unfold rsaEval; rw [Nat.pow_mod]]
  exact rsaInvert_rsaEval desc (Nat.mod_lt _ desc.modulus_pos)

/-! ### Common modulus -/

/-- The common-modulus attack on plain RSA: from the encryptions `c₁ = rsaEval N e₁ m` and
`c₂ = rsaEval N e₂ m` of one message `m` under the same modulus `N` and coprime exponents `e₁`,
`e₂`, Shamir's trick `commonRoot N e₂ e₁ c₁ c₂` recovers `m % N` whenever `m` is coprime to `N`.
The attack is therefore the program `commonRoot` on the ciphertexts, and
`computableInPolyTime_commonRoot` at `(N, e₂, e₁, c₁, c₂)` is its polynomial-time certificate. -/
theorem commonRoot_rsaEval {N e₁ e₂ m : ℕ} (he : Nat.Coprime e₁ e₂) (hm : Nat.Coprime m N) :
    commonRoot N e₂ e₁ (rsaEval N e₁ m) (rsaEval N e₂ m) = m % N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : m = 1 := Nat.coprime_zero_right m |>.mp hm
    simp [commonRoot, rsaEval, Turing.MultiTapeTM.powMod]
  have hc (k : ℕ) : Nat.Coprime (rsaEval N k m) N :=
    (Nat.mod_modEq (m ^ k) N).gcd_eq.trans (Nat.Coprime.pow_left k hm)
  have h : rsaEval N e₁ m ^ e₂ ≡ rsaEval N e₂ m ^ e₁ [MOD N] :=
    calc rsaEval N e₁ m ^ e₂ ≡ (m ^ e₁) ^ e₂ [MOD N] := (Nat.mod_modEq _ _).pow _
      _ = (m ^ e₂) ^ e₁ := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≡ rsaEval N e₂ m ^ e₁ [MOD N] := ((Nat.mod_modEq _ _).pow _).symm
  set x := commonRoot N e₂ e₁ (rsaEval N e₁ m) (rsaEval N e₂ m)
  obtain ⟨u, hu⟩ : ∃ u : (ZMod N)ˣ, (u : ZMod N) = m := ⟨_, ZMod.coe_unitOfCoprime m hm⟩
  obtain ⟨v, hv⟩ : ∃ v : (ZMod N)ˣ, (v : ZMod N) = x :=
    ⟨_, ZMod.coe_unitOfCoprime x (commonRoot_coprime hN he.symm (hc e₁) (hc e₂) h)⟩
  have hpow (k : ℕ) (hk : x ^ k ≡ rsaEval N k m [MOD N]) : v ^ (k : ℤ) = u ^ (k : ℤ) := by
    ext
    rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, hv,
      ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk, rsaEval,
      ZMod.natCast_mod]
  have hbezout : (e₂ : ℤ) * Nat.gcdA e₂ e₁ + e₁ * Nat.gcdB e₂ e₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, he.symm.gcd_eq_one, Nat.cast_one]
  have hvu : v = u :=
    (eq_zpow_mul_zpow_of_zpow_eq hbezout (hpow e₂ (commonRoot_pow_modEq_right hN he.symm (hc e₁) h))
      (hpow e₁ (commonRoot_pow_modEq_left hN he.symm (hc e₁) h))).trans
      (eq_zpow_mul_zpow_of_zpow_eq hbezout rfl rfl).symm
  have hlt : x < N := commonRoot_lt hN _ _ _ _
  rw [← Nat.mod_eq_of_lt hlt, ← ZMod.natCast_eq_natCast_iff', ← hu, ← hv, hvu]

/-! ### Small messages and the broadcast attack -/

/-- For a short message, `m ^ e < N`, plain RSA performs no modular reduction: the ciphertext is
`m ^ e` over the integers. -/
theorem rsaEval_eq_pow_of_pow_lt {N e m : ℕ} (hsmall : m ^ e < N) : rsaEval N e m = m ^ e :=
  Nat.mod_eq_of_lt hsmall

/-- A short message is the unique integer `e`-th root of its ciphertext, so it is recovered by an
integer root computation. -/
theorem eq_of_pow_eq_rsaEval {N e m m' : ℕ} (he : e ≠ 0) (hsmall : m ^ e < N)
    (hroot : m' ^ e = rsaEval N e m) : m' = m :=
  Nat.pow_left_injective he (hroot.trans (rsaEval_eq_pow_of_pow_lt hsmall))

/-- The broadcast attack: if one message `m` is encrypted under pairwise coprime moduli `N i`
(`i ∈ l`) with a common exponent `e` and `m ^ e` is smaller than the product of the moduli, then
the Chinese remainder combination of the ciphertexts is `m ^ e` over the integers. -/
theorem chineseRemainderOfList_rsaEval_eq_pow {ι : Type*} {N : ι → ℕ} {e m : ℕ} (l : List ι)
    (co : l.Pairwise (Function.onFun Nat.Coprime N)) (hN : ∀ i ∈ l, N i ≠ 0)
    (hsmall : m ^ e < (l.map N).prod) :
    (Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co : ℕ) = m ^ e := by
  have hmod : m ^ e ≡ Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co
      [MOD (l.map N).prod] :=
    Nat.chineseRemainderOfList_modEq_unique _ N l co fun i _ => (Nat.mod_modEq _ _).symm
  have hlt := Nat.chineseRemainderOfList_lt_prod (fun i => rsaEval (N i) e m) N l co hN
  rw [Nat.ModEq, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hlt] at hmod
  exact hmod.symm

/-- The broadcast attack recovers the message: `m` is the unique integer `e`-th root of the Chinese
remainder combination of its ciphertexts. -/
theorem eq_of_pow_eq_chineseRemainderOfList_rsaEval {ι : Type*} {N : ι → ℕ} {e m m' : ℕ}
    (he : e ≠ 0) (l : List ι) (co : l.Pairwise (Function.onFun Nat.Coprime N))
    (hN : ∀ i ∈ l, N i ≠ 0)
    (hsmall : m ^ e < (l.map N).prod)
    (hroot : m' ^ e = Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co) :
    m' = m :=
  Nat.pow_left_injective he (hroot.trans (chineseRemainderOfList_rsaEval_eq_pow l co hN hsmall))

/-! ### Factoring from `φ(N)` -/

/-- The factors of `N` computed from `N` and `φ = φ(N)`: with `s = N + 1 - φ` (which is `p + q`)
and `r = ⌊√(s ^ 2 - 4 * N)⌋` (which is `|p - q|`), output `((s + r) / 2, (s - r) / 2)`. -/
@[expose] def factorOfTotient (N φ : ℕ) : ℕ × ℕ :=
  ((N + 1 - φ + Nat.sqrt ((N + 1 - φ) ^ 2 - 4 * N)) / 2,
    (N + 1 - φ - Nat.sqrt ((N + 1 - φ) ^ 2 - 4 * N)) / 2)

/-- For positive `q ≤ p`, `factorOfTotient` recovers `(p, q)` from `p * q` and
`(p - 1) * (q - 1)`. -/
theorem factorOfTotient_eq {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    factorOfTotient (p * q) ((p - 1) * (q - 1)) = (p, q) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hqp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have hsum : (b + 1 + t) * (b + 1) + 1 - (b + 1 + t - 1) * (b + 1 - 1) = 2 * (b + 1) + t := by
    rw [show b + 1 + t - 1 = b + t by omega, show b + 1 - 1 = b by omega]
    rw [show (b + 1 + t) * (b + 1) + 1 = (b + t) * b + (2 * (b + 1) + t) by ring]
    omega
  have hdisc : (2 * (b + 1) + t) ^ 2 - 4 * ((b + 1 + t) * (b + 1)) = t ^ 2 := by
    rw [show (2 * (b + 1) + t) ^ 2 = t ^ 2 + 4 * ((b + 1 + t) * (b + 1)) by ring]
    omega
  simp only [zero_add] at *
  rw [factorOfTotient, hsum, hdisc, Nat.sqrt_eq']
  ext <;> dsimp only <;> omega

/-! ### Factoring from a nontrivial square root of `1` and from `(N, e, d)` -/

/-- If `N > 1` divides `a * b` without dividing either `a` or `b`, then `gcd(a, N)` is a proper
factor of `N`. -/
private theorem proper_gcd_of_dvd_mul {N a b : ℕ} (hN : 1 < N) (hdvd : N ∣ a * b)
    (ha : ¬ N ∣ a) (hb : ¬ N ∣ b) : 1 < Nat.gcd a N ∧ Nat.gcd a N < N := by
  have hpos : 0 < Nat.gcd a N := Nat.gcd_pos_of_pos_right a (by omega)
  have hne1 : Nat.gcd a N ≠ 1 := fun h1 =>
    hb (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm h1) hdvd)
  exact ⟨by omega, lt_of_le_of_ne (Nat.gcd_le_right a (by omega)) fun h =>
    ha (h ▸ Nat.gcd_dvd_left a N)⟩

/-- If `y ^ 2 ≡ 1 [MOD N]` for `N > 1`, then `y ≥ 1` and `N ∣ (y - 1) * (y + 1)`. -/
private theorem dvd_sub_one_mul_add_one_of_sq_modEq_one {N y : ℕ} (hN : 1 < N)
    (hsq : y ^ 2 ≡ 1 [MOD N]) : 1 ≤ y ∧ N ∣ (y - 1) * (y + 1) := by
  have hy : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | h
    · exfalso
      have h := hsq
      rw [Nat.ModEq, zero_pow two_ne_zero, Nat.zero_mod, Nat.mod_eq_of_lt hN] at h
      exact zero_ne_one h
    · exact h
  refine ⟨hy, ?_⟩
  have h := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hy)).mp hsq.symm
  rwa [show y ^ 2 - 1 = (y - 1) * (y + 1) by
    obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hy
    rw [show 1 + z - 1 = z by omega, show (1 + z) ^ 2 = z * (1 + z + 1) + 1 by ring]
    omega] at h

/-- If `y ^ 2 ≡ 1 [MOD N]` and `y ≢ 1 [MOD N]`, then `1 < N`. -/
private theorem one_lt_of_sq_modEq_one {N y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD N])
    (hone : ¬ y ≡ 1 [MOD N]) : 1 < N := by
  rcases N with _ | _ | N
  · simp only [Nat.ModEq, Nat.mod_zero] at hsq hone
    exact False.elim (hone (by nlinarith))
  · exact False.elim (hone (by simp [Nat.ModEq, Nat.mod_one]))
  · omega

/-- **Nontrivial square root of `1` gives a proper factor (`gcd(y - 1, N)`)**: for any `N` and `y`,
if `y ^ 2 ≡ 1 [MOD N]`, `y ≢ 1 [MOD N]`, and `y + 1 ≢ 0 [MOD N]`, then `gcd(y - 1, N)` is a proper
factor of `N` [Arora–Barak, Lemma 20.24][AroraBarak07]. -/
theorem gcd_sub_one_proper_of_sq_modEq_one {N y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD N])
    (hone : ¬ y ≡ 1 [MOD N]) (hneg : ¬ y + 1 ≡ 0 [MOD N]) :
    1 < Nat.gcd (y - 1) N ∧ Nat.gcd (y - 1) N < N := by
  have hN : 1 < N := one_lt_of_sq_modEq_one hsq hone
  obtain ⟨hy, hdvd⟩ := dvd_sub_one_mul_add_one_of_sq_modEq_one hN hsq
  exact proper_gcd_of_dvd_mul hN hdvd (fun h => hone ((Nat.modEq_iff_dvd' hy).mpr h).symm)
    (fun h => hneg (Nat.modEq_zero_iff_dvd.mpr h))

/-- **Nontrivial square root of `1` gives a proper factor (`gcd(y + 1, N)`)**: for any `N` and `y`,
if `y ^ 2 ≡ 1 [MOD N]`, `y ≢ 1 [MOD N]`, and `y + 1 ≢ 0 [MOD N]`, then `gcd(y + 1, N)` is a proper
factor of `N` [Arora–Barak, Lemma 20.24][AroraBarak07]. -/
theorem gcd_add_one_proper_of_sq_modEq_one {N y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD N])
    (hone : ¬ y ≡ 1 [MOD N]) (hneg : ¬ y + 1 ≡ 0 [MOD N]) :
    1 < Nat.gcd (y + 1) N ∧ Nat.gcd (y + 1) N < N := by
  have hN : 1 < N := one_lt_of_sq_modEq_one hsq hone
  obtain ⟨hy, hdvd⟩ := dvd_sub_one_mul_add_one_of_sq_modEq_one hN hsq
  exact proper_gcd_of_dvd_mul hN (mul_comm (y - 1) (y + 1) ▸ hdvd)
    (fun h => hneg (Nat.modEq_zero_iff_dvd.mpr h))
    (fun h => hone ((Nat.modEq_iff_dvd' hy).mpr h).symm)

namespace RSADesc

/-- The factorization `(max p q, min p q)` of an RSA modulus is computed from `N` and `φ(N)`. -/
theorem factorOfTotient_eq (desc : RSADesc) :
    factorOfTotient desc.modulus desc.totient = (max desc.p desc.q, min desc.p desc.q) := by
  rcases le_total desc.q desc.p with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact Cslib.Crypto.factorOfTotient_eq desc.hq.pos h
  · rw [max_eq_right h, min_eq_left h, modulus, totient, mul_comm desc.p, mul_comm (desc.p - 1)]
    exact Cslib.Crypto.factorOfTotient_eq desc.hp.pos h

/-- `e * d - 1` is a multiple of the order of every unit modulo `N`: `x ^ (e * d - 1) ≡ 1` for
every `x` coprime to `N`. -/
theorem pow_mul_sub_one_modEq_one (desc : RSADesc) {x : ℕ} (hx : Nat.Coprime x desc.modulus) :
    x ^ (desc.e * desc.d - 1) ≡ 1 [MOD desc.modulus] := by
  have hed_pos : 0 < desc.e * desc.d := by
    have h : desc.e * desc.d % desc.totient = 1 := by
      have h := desc.hed
      rwa [Nat.ModEq, Nat.mod_eq_of_lt desc.totient_gt_one] at h
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, Nat.zero_mod] at h
    exact zero_ne_one h
  have hmul : x ^ (desc.e * desc.d - 1) * x ≡ 1 * x [MOD desc.modulus] := by
    rw [← pow_succ, Nat.sub_add_cancel hed_pos, one_mul]
    exact rsa_pow_mul_modEq desc x
  exact Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hx).gcd_eq_one hmul

/-- A square root `y` of `1` modulo an RSA modulus `N = p * q`, other than `±1`, gives a proper
factor `gcd(y - 1, N)` of `N`. -/
theorem gcd_sub_one_proper (desc : RSADesc) {y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD desc.modulus])
    (hone : ¬ y ≡ 1 [MOD desc.modulus]) (hneg : ¬ y + 1 ≡ 0 [MOD desc.modulus]) :
    1 < Nat.gcd (y - 1) desc.modulus ∧ Nat.gcd (y - 1) desc.modulus < desc.modulus :=
  gcd_sub_one_proper_of_sq_modEq_one hsq hone hneg

/-- A square root `y` of `1` modulo an RSA modulus `N = p * q`, other than `±1`, gives a proper
factor `gcd(y + 1, N)` of `N`. -/
theorem gcd_add_one_proper (desc : RSADesc) {y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD desc.modulus])
    (hone : ¬ y ≡ 1 [MOD desc.modulus]) (hneg : ¬ y + 1 ≡ 0 [MOD desc.modulus]) :
    1 < Nat.gcd (y + 1) desc.modulus ∧ Nat.gcd (y + 1) desc.modulus < desc.modulus :=
  gcd_add_one_proper_of_sq_modEq_one hsq hone hneg

end RSADesc

/-! ### Equivalence of computing `φ(N)` and factoring, and RSA-to-factoring reductions -/

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- `factorOfTotient` is computable in polynomial time on binary naturals. -/
theorem computableInPolyTime_factorOfTotient {α : Type} {enc : α ↪ List Bool} {N φ : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hφ : ComputableInPolyTime φ enc encNat) :
    ComputableInPolyTime (fun x => factorOfTotient (N x) (φ x)) enc (encPair encNat encNat) := by
  unfold factorOfTotient
  have hrad : ComputableInPolyTime (fun x => (N x + 1 - φ x) ^ 2 - 4 * N x) enc encNat := by
    simp only [sq]
    fun_prop
  have hdisc : ComputableInPolyTime
      (fun x => ((N x + 1 - φ x) ^ 2 - 4 * N x).sqrt) enc encNat :=
    ComputableInPolyTime.binary_sqrt' hrad
  have hpair : ∀ {d : α → ℕ}, ComputableInPolyTime d enc encNat →
      ComputableInPolyTime
        (fun x => ((N x + 1 - φ x + d x) / 2, (N x + 1 - φ x - d x) / 2))
        enc (encPair encNat encNat) := by
    intro d hd
    fun_prop
  exact hpair hdisc

/-- The Euler totient computation experiment ([KatzLindell2020], Section 9.2.5, Theorem 9.49):
sample `desc ← gen n`, run `T n desc.modulus`, and accept when `T` returns
`desc.totient = (desc.p - 1) * (desc.q - 1)`. -/
noncomputable def totientGame (gen : RSAGen) (T : ℕ → ℕ → ProbComp ℕ) (n : ℕ) : Game := do
  let desc ← gen n
  let φ' ← ProbComp.eval (T n desc.modulus)
  return decide (φ' = desc.totient)

/-- The Euler totient hardness assumption for `gen`: every uniform PPT algorithm has negligible
probability of computing `φ(N) = (p - 1) * (q - 1)` from `N = p * q`. This assumption is novel to
this library: [KatzLindell2020], Section 9.2.5, Theorem 9.49 shows that computing `φ(N)` is
equivalent to factoring `N` but states no separate assumption. It is equivalent to
`ModulusFactoringHard` for the modulus law of `gen` (`totientHard_iff_modulusFactoringHard`), so it
is exactly as plausible as factoring. Keys come from any law on `RSADesc`, which need not be
efficiently samplable. -/
def TotientHard (gen : RSAGen) : Prop :=
  ∀ T : ℕ → ℕ → ProbComp ℕ,
    IsPPTOn (encPair encUnary encNat) encNat (fun input => T input.1 input.2) →
    Negligible (fun n => Game.succProbability (totientGame gen T n))

/-- Explicit PPT reduction from computing `φ(N)` to factoring `N` ([KatzLindell2020],
Theorem 9.49): run the factoring algorithm `F n N`, and if it returns a nontrivial factorization
`(a, b)` of `N`, output `(a - 1) * (b - 1)`. -/
def factorToTotient (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n N : ℕ) : ProbComp ℕ := do
  let ab ← F n N
  return if 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = N then (ab.1 - 1) * (ab.2 - 1) else 0

/-- Explicit PPT reduction from factoring `N` to computing `φ(N)` ([KatzLindell2020],
Theorem 9.49): run the totient algorithm `T n N` to obtain `φ'` and output
`factorOfTotient N φ'`. -/
def totientToFactor (T : ℕ → ℕ → ProbComp ℕ) (n N : ℕ) : ProbComp (ℕ × ℕ) := do
  let φ' ← T n N
  return factorOfTotient N φ'

private theorem computableInPolyTime_totientIfFactor {α : Type} {enc : α ↪ List Bool}
    {N a b : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat)
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime
      (fun x => if 1 < a x ∧ 1 < b x ∧ a x * b x = N x then (a x - 1) * (b x - 1) else 0)
      enc encNat := by
  have hcond : ComputableInPolyTime
      (fun x => decide (1 < a x ∧ 1 < b x ∧ a x * b x = N x)) enc encBool := by
    fun_prop
  have hprod : ComputableInPolyTime (fun x => (a x - 1) * (b x - 1)) enc encNat := by
    fun_prop
  have hzero : ComputableInPolyTime (fun _ : α => 0) enc encNat := by
    fun_prop
  simpa only [decide_eq_true_eq] using ComputableInPolyTime.ite hcond hprod hzero

/-- `factorToTotient F` is uniform PPT whenever `F` is uniform PPT. -/
theorem isPPTOn_factorToTotient {F : ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hF : IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => F input.1 input.2)) :
    IsPPTOn (encPair encUnary encNat) encNat (fun input => factorToTotient F input.1 input.2) := by
  unfold factorToTotient
  refine IsPPTOn.bind_with hF ?_
  exact (computableInPolyTime_totientIfFactor (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn

/-- `totientToFactor T` is uniform PPT whenever `T` is uniform PPT. -/
theorem isPPTOn_totientToFactor {T : ℕ → ℕ → ProbComp ℕ}
    (hT : IsPPTOn (encPair encUnary encNat) encNat (fun input => T input.1 input.2)) :
    IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => totientToFactor T input.1 input.2) := by
  unfold totientToFactor
  refine IsPPTOn.bind_with hT ?_
  exact (computableInPolyTime_factorOfTotient (by fun_prop) (by fun_prop)).isPPTOn

/-- `totientGame gen (factorToTotient F) n` equals `modulusFactoringGame` on the pushed-forward
RSA modulus distribution. -/
theorem totientGame_factorToTotient (gen : RSAGen) (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    totientGame gen (factorToTotient F) n =
      modulusFactoringGame (fun k => (gen k).map RSADesc.modulus) F n := by
  unfold totientGame modulusFactoringGame factorToTotient
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  congr 1
  funext desc
  congr 1
  funext ab
  by_cases hfac : 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = desc.modulus
  · rcases hfac with ⟨ha, hb, hab⟩
    have htot : (ab.1 - 1) * (ab.2 - 1) = desc.totient := by
      rcases mul_eq_mul_primes_cases desc.hp desc.hq ha hb hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, mul_comm]
    simp [ha, hb, hab, htot]
  · have htot_pos : 0 < desc.totient := lt_trans zero_lt_one desc.totient_gt_one
    simp [hfac, htot_pos.ne]

/-- The success probability of `T` in `totientGame` is at most the factoring success probability of
`totientToFactor T`. -/
theorem succProbability_totientGame_le (gen : RSAGen) (T : ℕ → ℕ → ProbComp ℕ) (n : ℕ) :
    Game.succProbability (totientGame gen T n) ≤
      Game.succProbability
        (modulusFactoringGame (fun k => (gen k).map RSADesc.modulus) (totientToFactor T) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  unfold totientGame modulusFactoringGame totientToFactor
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    PMF.bind_apply, PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq]
  refine tsum_le_tsum fun desc => mul_le_mul_of_nonneg_left ?_ zero_le
  refine tsum_le_tsum fun φ' => mul_le_mul_of_nonneg_left ?_ zero_le
  by_cases hφ : φ' = desc.totient
  · subst hφ
    rw [desc.factorOfTotient_eq]
    have hmax : 1 < max desc.p desc.q := lt_max_of_lt_left desc.hp.one_lt
    have hmin : 1 < min desc.p desc.q := lt_min desc.hp.one_lt desc.hq.one_lt
    have hmul : max desc.p desc.q * min desc.p desc.q = desc.modulus :=
      max_mul_min desc.p desc.q
    simp [hmax, hmin, hmul]
  · simp [hφ]

/-- If computing `φ(N)` is hard for `gen`, then factoring `N` is hard for
`(gen n).map RSADesc.modulus`. -/
theorem TotientHard.modulusFactoringHard {gen : RSAGen} (h : TotientHard gen) :
    ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus) := by
  intro F hF
  refine (h (factorToTotient F) (isPPTOn_factorToTotient hF)).congr fun n => ?_
  rw [totientGame_factorToTotient]

/-- If factoring `N` is hard for `(gen n).map RSADesc.modulus`, then computing `φ(N)` is hard for
`gen`. -/
theorem ModulusFactoringHard.totientHard {gen : RSAGen}
    (h : ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus)) :
    TotientHard gen := fun T hT =>
  negligible_of_le (h (totientToFactor T) (isPPTOn_totientToFactor hT))
    (succProbability_totientGame_le gen T)

/-- After [KatzLindell2020], Theorem 9.49: computing `φ(N)` from `N = p * q` is polynomial-time
equivalent to factoring `N`. -/
theorem totientHard_iff_modulusFactoringHard (gen : RSAGen) :
    TotientHard gen ↔ ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus) :=
  ⟨TotientHard.modulusFactoringHard, ModulusFactoringHard.totientHard⟩

/-- The RSA private-exponent recovery experiment ([KatzLindell2020], Section 9.2.5, Theorem 9.50):
sample `desc ← gen n`, run `K n desc.publicKey`, and accept when `K` returns an exponent `d'` with
`desc.e * d' ≡ 1 [MOD desc.totient]`. -/
noncomputable def rsaKeyRecoveryGame (gen : RSAGen) (K : ℕ → RSAPublicKey → ProbComp ℕ)
    (n : ℕ) : Game := do
  let desc ← gen n
  let d' ← ProbComp.eval (K n desc.publicKey)
  return decide (desc.e * d' % desc.totient = 1)

/-- The RSA private-exponent recovery hardness assumption for `gen`: every uniform PPT algorithm
given `(N, e)` has negligible probability of finding a valid private exponent `d'` with
`e * d' ≡ 1 [MOD φ(N)]`. This assumption is novel to this library: [KatzLindell2020],
Section 9.2.5, Theorem 9.50 shows that computing `d` is as hard as factoring `N` (a direction not
formalized here) but states no separate assumption. It follows from `RSAOneWay`
(`RSAOneWay.rsaKeyRecoveryHard`), which makes it plausible, and implies `TotientHard`
(`RSAKeyRecoveryHard.totientHard`). Keys come from any law on `RSADesc`, which need not be
efficiently samplable. -/
def RSAKeyRecoveryHard (gen : RSAGen) : Prop :=
  ∀ K : ℕ → RSAPublicKey → ProbComp ℕ,
    IsPPTOn (encPair encUnary encRSAPublicKey) encNat (fun input => K input.1 input.2) →
    Negligible (fun n => Game.succProbability (rsaKeyRecoveryGame gen K n))

/-- Explicit PPT reduction from RSA private-exponent recovery to computing `φ(N)`: given
`pk = (N, e)`, run `T n N` to obtain `φ'` and return the modular inverse
`BinaryGcd.modInv e φ'`. -/
def totientToKeyRecovery (T : ℕ → ℕ → ProbComp ℕ) (n : ℕ) (pk : RSAPublicKey) : ProbComp ℕ := do
  let φ' ← T n pk.N
  return BinaryGcd.modInv pk.e φ'

/-- `totientToKeyRecovery T` is uniform PPT whenever `T` is uniform PPT. -/
theorem isPPTOn_totientToKeyRecovery {T : ℕ → ℕ → ProbComp ℕ}
    (hT : IsPPTOn (encPair encUnary encNat) encNat (fun input => T input.1 input.2)) :
    IsPPTOn (encPair encUnary encRSAPublicKey) encNat
      (fun input => totientToKeyRecovery T input.1 input.2) := by
  unfold totientToKeyRecovery
  refine IsPPTOn.bind_with
    (IsPPTOn.preprocess hT (prepare := fun input : ℕ × RSAPublicKey => (input.1, input.2.N))
      (by fun_prop)) ?_
  exact (ComputableInPolyTime.binary_modInv' (by fun_prop) (by fun_prop)).isPPTOn

/-- The success probability of `T` in `totientGame` is at most the key-recovery success probability
of `totientToKeyRecovery T`. -/
theorem succProbability_totientGame_le_rsaKeyRecoveryGame (gen : RSAGen)
    (T : ℕ → ℕ → ProbComp ℕ) (n : ℕ) :
    Game.succProbability (totientGame gen T n) ≤
      Game.succProbability (rsaKeyRecoveryGame gen (totientToKeyRecovery T) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  unfold totientGame rsaKeyRecoveryGame totientToKeyRecovery
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_apply, PMF.pure_apply,
    eq_comm (a := true), decide_eq_true_eq]
  refine tsum_le_tsum fun desc => mul_le_mul_of_nonneg_left ?_ zero_le
  refine tsum_le_tsum fun φ' => mul_le_mul_of_nonneg_left ?_ zero_le
  by_cases hφ : φ' = desc.totient
  · subst hφ
    have htot1 : 1 < desc.totient := desc.totient_gt_one
    have hmod := BinaryGcd.mul_modInv_modEq_one (lt_trans zero_lt_one htot1) desc.he
    rw [Nat.ModEq, Nat.mod_eq_of_lt htot1] at hmod
    simp [hmod]
  · simp [hφ]

/-- If RSA private-exponent recovery is hard for `gen`, then computing `φ(N)` is hard for `gen`. -/
theorem RSAKeyRecoveryHard.totientHard {gen : RSAGen} (h : RSAKeyRecoveryHard gen) :
    TotientHard gen := fun T hT =>
  negligible_of_le (h (totientToKeyRecovery T) (isPPTOn_totientToKeyRecovery hT))
    (succProbability_totientGame_le_rsaKeyRecoveryGame gen T)

/-- If RSA private-exponent recovery is hard for `gen`, then factoring `N` is hard for
`(gen n).map RSADesc.modulus`. -/
theorem RSAKeyRecoveryHard.modulusFactoringHard {gen : RSAGen} (h : RSAKeyRecoveryHard gen) :
    ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus) :=
  h.totientHard.modulusFactoringHard

/-- Explicit PPT reduction from RSA inversion to RSA private-exponent recovery: given `(n, pk, y)`,
run `K n pk` to obtain candidate private exponent `d'` and return `rsaInvert pk.N d' y`. -/
def keyRecoveryToRSA (K : ℕ → RSAPublicKey → ProbComp ℕ) : RSAInverter :=
  fun n pk y => (fun d' => ⟨rsaInvert pk.N d' y, Nat.mod_lt _ y.pos⟩) <$> K n pk

/-- Explicit PPT reduction from RSA inversion to integer factoring: factor `pk.N`, compute `φ(N)`,
invert `pk.e` modulo `φ(N)` via `BinaryGcd.modInv`, and raise the challenge `y` to that exponent
modulo `pk.N`. -/
def factorToRSA (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) : RSAInverter :=
  keyRecoveryToRSA (totientToKeyRecovery (factorToTotient F))

/-- `keyRecoveryToRSA K` is a PPT `RSAInverter` whenever `K` is uniform PPT. -/
theorem isPPT_keyRecoveryToRSA {K : ℕ → RSAPublicKey → ProbComp ℕ}
    (hK : IsPPTOn (encPair encUnary encRSAPublicKey) encNat (fun input => K input.1 input.2)) :
    (keyRecoveryToRSA K).IsPPT := by
  refine ((hK.preprocess (prepare := fun x : RSAInput => (x.secParam, x.publicKey))
      (by fun_prop)).map_with
    (f := fun x d' => rsaInvert x.publicKey.N d' x.challenge)
    (computableInPolyTime_rsaInvert (by fun_prop) (by fun_prop) (by fun_prop)
      (fun p => p.1.challenge.pos))).congr fun x => ?_
  simp only [keyRecoveryToRSA, Functor.map_map]

/-- `factorToRSA F` is a PPT `RSAInverter` whenever `F` is uniform PPT. -/
theorem isPPT_factorToRSA {F : ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hF : IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => F input.1 input.2)) :
    (factorToRSA F).IsPPT :=
  isPPT_keyRecoveryToRSA (isPPTOn_totientToKeyRecovery (isPPTOn_factorToTotient hF))

/-- The key-recovery success probability of `K` is at most the RSA inversion success probability of
`keyRecoveryToRSA K`. -/
theorem succProbability_rsaKeyRecoveryGame_le (gen : RSAGen)
    (K : ℕ → RSAPublicKey → ProbComp ℕ) (n : ℕ) :
    Game.succProbability (rsaKeyRecoveryGame gen K n) ≤
      Game.succProbability (rsaInversionGame gen (keyRecoveryToRSA K) n) := by
  rw [rsaInversionGame_eq]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  unfold rsaKeyRecoveryGame keyRecoveryToRSA
  simp only [ProbComp.eval_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
    Function.comp_def, PMF.bind_apply, PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq]
  refine tsum_le_tsum fun desc => mul_le_mul_of_nonneg_left ?_ zero_le
  -- The key-recovery outcome does not depend on the uniform RSA challenge `x`.
  calc _ = ∑' x : Fin desc.modulus, (PMF.uniformOfFintype (Fin desc.modulus)) x *
        ∑' d' : ℕ, (ProbComp.eval (K n desc.publicKey)) d' *
          if desc.e * d' % desc.totient = 1 then 1 else 0 := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
      refine tsum_le_tsum fun x => mul_le_mul_of_nonneg_left ?_ zero_le
      refine tsum_le_tsum fun d' => mul_le_mul_of_nonneg_left ?_ zero_le
      by_cases hd' : desc.e * d' % desc.totient = 1
      · have hed' : desc.e * d' ≡ 1 [MOD desc.totient] := by
          rw [Nat.ModEq, hd', Nat.mod_eq_of_lt desc.totient_gt_one]
        let desc' : RSADesc := { desc with d := d', hed := hed' }
        have hinv : rsaInvert desc.modulus d' (rsaEval desc.modulus desc.e x) = x :=
          rsaInvert_rsaEval desc' x.isLt
        have hfin : (⟨rsaInvert desc.modulus d' (rsaEval desc.modulus desc.e x),
            Nat.mod_lt _ x.pos⟩ : Fin desc.modulus) = x :=
          Fin.ext hinv
        simp [hd', hfin]
      · simp [hd']

/-- The factoring success probability of `F` is at most the RSA inversion success probability of
`factorToRSA F`. -/
theorem succProbability_modulusFactoringGame_le_rsaInversionGame (gen : RSAGen)
    (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    Game.succProbability
        (modulusFactoringGame (fun k => (gen k).map RSADesc.modulus) F n) ≤
      Game.succProbability (rsaInversionGame gen (factorToRSA F) n) := by
  calc Game.succProbability
        (modulusFactoringGame (fun k => (gen k).map RSADesc.modulus) F n)
      = Game.succProbability (totientGame gen (factorToTotient F) n) := by
        rw [totientGame_factorToTotient]
    _ ≤ Game.succProbability
          (rsaKeyRecoveryGame gen (totientToKeyRecovery (factorToTotient F)) n) :=
        succProbability_totientGame_le_rsaKeyRecoveryGame gen (factorToTotient F) n
    _ ≤ Game.succProbability (rsaInversionGame gen (factorToRSA F) n) :=
        succProbability_rsaKeyRecoveryGame_le gen _ n

/-- **RSA one-wayness implies private-exponent recovery hardness.** -/
theorem RSAOneWay.rsaKeyRecoveryHard {gen : RSAGen} (h : RSAOneWay gen) :
    RSAKeyRecoveryHard gen := fun K hK =>
  negligible_of_le (h (keyRecoveryToRSA K) (isPPT_keyRecoveryToRSA hK))
    (succProbability_rsaKeyRecoveryGame_le gen K)

/-- **RSA one-wayness implies Euler totient computation hardness.** -/
theorem RSAOneWay.totientHard {gen : RSAGen} (h : RSAOneWay gen) :
    TotientHard gen :=
  h.rsaKeyRecoveryHard.totientHard

/-- **RSA one-wayness implies integer factoring hardness** on `(gen n).map RSADesc.modulus`. -/
theorem RSAOneWay.modulusFactoringHard {gen : RSAGen} (h : RSAOneWay gen) :
    ModulusFactoringHard (fun n => (gen n).map RSADesc.modulus) :=
  h.totientHard.modulusFactoringHard

end Cslib.Crypto
