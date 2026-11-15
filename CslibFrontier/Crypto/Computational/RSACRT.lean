/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Foundations.Data.Nat.ChineseRemainder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Foundations.Data.ZMod.NatCast
import Mathlib.FieldTheory.Finite.Basic

/-!
# RSA-CRT inversion and the gcd identity behind its fault attack

RSA-CRT computes the RSA inverse `y ^ d mod n` from the private key `(p, q, d_p, d_q, q_inv)`:
it computes `x_p = y ^ d_p mod p` and `x_q = y ^ d_q mod q` and recombines them by the Chinese
Remainder Theorem as `x_q + (q_inv · (x_p − x_q) mod p) · q`. If `x_q` is correct and `x_p` is
not, the recombined output `σ` satisfies `gcd(σ ^ e − h, n) = q`, where `h` is the input and
`σ ^ e − h` is computed in `ℤ_n` and read in `[0, n)` ([BonehShoup2023], §16.4.3, pp. 701–702).

## Main definitions

* `Cslib.Crypto.RSACRTKey`: the RSA-CRT private key `(p, q, d_p, d_q, q_inv)`.
* `Cslib.Crypto.RSACRTKey.powP`, `Cslib.Crypto.RSACRTKey.powQ`, `Cslib.Crypto.RSACRTKey.combine`,
  `Cslib.Crypto.RSACRTKey.invert`: the three steps of RSA-CRT inversion and their composite.
* `Cslib.Crypto.RSADesc.crtKeyWith`: the key derived from an `RSADesc`, with
  `d_p = d mod (p - 1)`, `d_q = d mod (q - 1)` and a given `q_inv`.
* `Cslib.Crypto.RSADesc.crtQInv`, `Cslib.Crypto.RSADesc.crtKey`: the inverse of `q` modulo `p`
  computed by the extended Euclidean algorithm `Turing.MultiTapeTM.BinaryGcd.modInv`, and the key
  that uses it. `crtKey` is not exposed; `Cslib.Crypto.RSADesc.crtKey_eq_crtKeyWith` rewrites it
  to `crtKeyWith` with `q_inv = crtQInv`.

## Main results

* `Cslib.Crypto.RSADesc.crtQInv_eq_zmod_inv_val`, `Cslib.Crypto.RSADesc.crtQInv_mul_modEq_one`:
  `crtQInv` is the representative `((q : ZMod p)⁻¹).val` of `q⁻¹` in `ZMod p`, and an inverse
  of `q` modulo `p`.
* `Cslib.Crypto.RSACRTKey.combine_mod_mod`, `Cslib.Crypto.RSACRTKey.combine_modEq_p`,
  `Cslib.Crypto.RSACRTKey.combine_modEq_q`: recombination returns `x < p * q` from its residues,
  and its output is congruent to `x_p` modulo `p` and to `x_q` modulo `q`.
* `Cslib.Crypto.RSADesc.powP_crtKeyWith`, `Cslib.Crypto.RSADesc.powQ_crtKeyWith`: for odd `p`
  (respectively `q`), the first two steps compute `y ^ d mod p` and `y ^ d mod q`.
* `Cslib.Crypto.RSADesc.invert_crtKeyWith`, `Cslib.Crypto.RSADesc.invert_crtKey`: for odd `p` and
  `q`, RSA-CRT inversion equals `rsaInvert n d` on every input.
* `Cslib.Crypto.RSADesc.gcd_val_pow_sub_eq_q`: an output `σ` that agrees with `h ^ d` modulo `q`
  but not modulo `p` gives `gcd(σ ^ e − h, n) = q`.
* `Cslib.Crypto.RSADesc.gcd_val_pow_sub_combine_eq_q`: the gcd identity behind the fault attack:
  recombining a correct `x_q` with an `x_p'` that is not congruent to `h ^ d` modulo `p` gives an
  output `σ` with `gcd(σ ^ e − h, n) = q`.
* `Cslib.Crypto.computableInPolyTime_crtInvert`: RSA-CRT inversion is computable in polynomial
  time from polynomial-time key components and input, as natural numbers on `encNat`, when
  `p` and `q` are positive.
* `Cslib.Crypto.computableInPolyTime_crtKeyWith_invert`: the same for the key
  `RSADesc.crtKeyWith desc qInv`, from polynomial-time `p`, `q`, `d`, `q_inv` and input.
* `Cslib.Crypto.computableInPolyTime_crtQInv`, `Cslib.Crypto.computableInPolyTime_crtKey_invert`:
  `crtQInv` is computable in polynomial time from polynomial-time `p` and `q`, and RSA-CRT
  inversion with the key `RSADesc.crtKey` from polynomial-time `p`, `q`, `d` and input.
* `Cslib.Crypto.computableInPolyTime_gcd_val_pow_sub`: the gcd step of the fault attack,
  `gcd(σ ^ e − h, n)` with `σ ^ e − h` read in `[0, n)`, is computable in polynomial time when
  `n` is positive.

## Implementation notes

Residues are natural numbers. The book's `σ̂ ^ e − H(m) ∈ ℤ_n`, read as an integer in `[0, n)`, is
`((σ : ZMod n) ^ e - h).val`, and an arbitrary natural number `h` takes the place of the hash
value `H(m)`. The theorems hold for every `q_inv` with `q_inv * q ≡ 1 [MOD p]`;
`RSADesc.crtKey` uses `RSADesc.crtQInv = BinaryGcd.modInv q p` from
`CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Gcd.lean`, which
`RSADesc.crtQInv_eq_zmod_inv_val` identifies with the inverse in `ZMod p`. The definition is not
exposed and that import is proof-only: clients compute `crtQInv` through that theorem. The book
also assumes `p > q`; no result here needs it.

Recombination is `crtCombine q p x_q x_p q_inv` from
`CslibFrontier/Foundations/Data/Nat/ChineseRemainder.lean`; its congruences and correctness come
from `crtCombine_modEq_left`, `crtCombine_modEq_right` and `crtCombine_eq`.

Correctness of RSA-CRT needs `p` and `q` odd: `RSADesc` admits `p = 2`, where
`d_p = d mod 1 = 0`, so step 1 returns `1` for every `y`, which is wrong for even `y`. The tests
check the counterexample `p = 2`, `q = 5`, `e = d = 3`, `y = 2`, where RSA-CRT returns `3` and
`y ^ d mod n = 8`. The fault-attack identity does not need oddness: its hypothesis is that `x_q`
is congruent to the correct value `h ^ d` modulo `q`.

The polynomial-time certificates take their arguments as component functions `α → ℕ` on a
common input encoding, each computable in polynomial time to `encNat`, in the style of
`computableInPolyTime_rsaInvert`. In `computableInPolyTime_crtInvert` and
`computableInPolyTime_crtKeyWith_invert` the key component `q_inv` is such an argument, as in the
book, where it is part of the precomputed key. `computableInPolyTime_crtQInv` computes `crtQInv`
from `p` and `q` with the certificate `ComputableInPolyTime.binary_modInv'` of `Gcd.lean`, and
`computableInPolyTime_crtKey_invert` composes it with `computableInPolyTime_crtKeyWith_invert`.

Not formalized: the book's estimate that RSA-CRT is about four times faster, and FDH-RSA signing.
The certificates cover the computations; nothing is proved about an attacker as an adversary in a
security game.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §16.4.3, pp. 701–702.
-/

public section

namespace Cslib.Crypto

/-- An RSA-CRT private key `(p, q, d_p, d_q, q_inv)` ([BonehShoup2023], §16.4.3, p. 701). The
structure carries no conditions: `RSADesc.crtKeyWith` derives the key of an RSA key, and each
theorem states the hypotheses it uses. -/
structure RSACRTKey where
  /-- The first prime factor of the modulus. -/
  p : ℕ
  /-- The second prime factor of the modulus. -/
  q : ℕ
  /-- The exponent used modulo `p`, `d mod (p - 1)` for a key derived from `d`. -/
  dp : ℕ
  /-- The exponent used modulo `q`, `d mod (q - 1)` for a key derived from `d`. -/
  dq : ℕ
  /-- An inverse of `q` modulo `p`. -/
  qInv : ℕ

namespace RSACRTKey

/-- Step 1 of RSA-CRT inversion: `x_p = y ^ d_p mod p`. -/
@[expose] def powP (key : RSACRTKey) (y : ℕ) : ℕ :=
  y ^ key.dp % key.p

/-- Step 2 of RSA-CRT inversion: `x_q = y ^ d_q mod q`. -/
@[expose] def powQ (key : RSACRTKey) (y : ℕ) : ℕ :=
  y ^ key.dq % key.q

/-- Step 3 of RSA-CRT inversion: recombine `x_p` and `x_q` as
`x_q + (q_inv · (x_p − x_q) mod p) · q`, with `x_p − x_q` taken in `ℤ`, which is
`crtCombine q p x_q x_p q_inv` (it computes `x_p − x_q` as `x_p + (p − x_q mod p)`). -/
@[expose] def combine (key : RSACRTKey) (xp xq : ℕ) : ℕ :=
  crtCombine key.q key.p xq xp key.qInv

/-- RSA-CRT inversion ([BonehShoup2023], §16.4.3, p. 701): recombine `y ^ d_p mod p` and
`y ^ d_q mod q`. -/
@[expose] def invert (key : RSACRTKey) (y : ℕ) : ℕ :=
  key.combine (key.powP y) (key.powQ y)

/-- The hypothesis `q_inv * q ≡ 1 [MOD p]`, read in `ZMod p`. -/
private theorem natCast_qInv_mul_q {key : RSACRTKey} (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) :
    (key.qInv : ZMod key.p) * key.q = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 hinv
  push_cast at h
  exact h

/-- **CRT recombination** ([BonehShoup2023], §16.4.3, p. 701): for an inverse `q_inv` of `q`
modulo `p` and `x < p * q`, recombining `x mod p` and `x mod q` returns `x`. -/
theorem combine_mod_mod (key : RSACRTKey) (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) {x : ℕ}
    (hx : x < key.p * key.q) : key.combine (x % key.p) (x % key.q) = x :=
  crtCombine_eq (by rwa [mul_comm]) rfl rfl key.qInv (natCast_qInv_mul_q hinv)

/-- The recombined value is congruent to `x_q` modulo `q`, for all `x_p` and `x_q`. -/
theorem combine_modEq_q (key : RSACRTKey) (xp xq : ℕ) : key.combine xp xq ≡ xq [MOD key.q] :=
  crtCombine_modEq_left key.q key.p xq xp key.qInv

/-- The recombined value is congruent to `x_p` modulo `p` ([BonehShoup2023], §16.4.3, p. 701:
"The reader can verify that indeed x ≡ x_p mod p"), for every `x_p` and `x_q`. -/
theorem combine_modEq_p (key : RSACRTKey) (hp : 0 < key.p)
    (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) (xp xq : ℕ) : key.combine xp xq ≡ xp [MOD key.p] :=
  crtCombine_modEq_right hp (natCast_qInv_mul_q hinv) xq xp

end RSACRTKey

namespace RSADesc

/-- The RSA-CRT key of `desc` with a given `q_inv` ([BonehShoup2023], §16.4.3, p. 701):
`d_p = d mod (p - 1)` and `d_q = d mod (q - 1)`. The results about it assume
`qInv * q ≡ 1 [MOD p]`. -/
@[expose] def crtKeyWith (desc : RSADesc) (qInv : ℕ) : RSACRTKey where
  p := desc.p
  q := desc.q
  dp := desc.d % (desc.p - 1)
  dq := desc.d % (desc.q - 1)
  qInv := qInv

/-- The inverse of `q` modulo `p`, computed by the extended Euclidean algorithm
`Turing.MultiTapeTM.BinaryGcd.modInv q p`. Its value is given by `crtQInv_eq_zmod_inv_val`. -/
def crtQInv (desc : RSADesc) : ℕ :=
  Turing.MultiTapeTM.BinaryGcd.modInv desc.q desc.p

/-- `crtQInv` is the representative `((q : ZMod p)⁻¹).val` of the inverse of `q` in `ZMod p`. -/
theorem crtQInv_eq_zmod_inv_val (desc : RSADesc) :
    desc.crtQInv = ((desc.q : ZMod desc.p)⁻¹).val :=
  Turing.MultiTapeTM.BinaryGcd.modInv_eq_zmod_inv_val desc.hp.pos
    ((Nat.coprime_primes desc.hq desc.hp).2 desc.hpq.symm)

/-- `crtQInv` is an inverse of `q` modulo `p`. -/
theorem crtQInv_mul_modEq_one (desc : RSADesc) : desc.crtQInv * desc.q ≡ 1 [MOD desc.p] := by
  rw [mul_comm]
  exact Turing.MultiTapeTM.BinaryGcd.mul_modInv_modEq_one desc.hp.pos
    ((Nat.coprime_primes desc.hq desc.hp).2 desc.hpq.symm)

/-- The RSA-CRT key of `desc` ([BonehShoup2023], §16.4.3, p. 701), with `q_inv = crtQInv`. -/
def crtKey (desc : RSADesc) : RSACRTKey :=
  desc.crtKeyWith desc.crtQInv

/-- `crtKey` is `crtKeyWith` with `q_inv = crtQInv`. The definition of `crtKey` is not exposed;
this equation lets clients apply the results about `crtKeyWith` to it. -/
theorem crtKey_eq_crtKeyWith (desc : RSADesc) : desc.crtKey = desc.crtKeyWith desc.crtQInv := by
  rw [crtKey]

/-- `x ^ (a mod (p - 1)) ≡ x ^ a [MOD p]` for a prime `p` when `a mod (p - 1)` is positive. -/
private theorem pow_mod_sub_one_modEq {p a : ℕ} (hp : p.Prime) (ha : 0 < a % (p - 1)) (x : ℕ) :
    x ^ (a % (p - 1)) ≡ x ^ a [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  by_cases hx : (x : ZMod p) = 0
  · rw [hx, zero_pow ha.ne', zero_pow (by rintro rfl; simp at ha)]
  · exact (pow_eq_pow_mod a (ZMod.pow_card_sub_one_eq_one hx)).symm

/-- If `e * d ≡ 1 [MOD m]` and `m ≠ 1`, then `m` does not divide `d`. -/
private theorem pos_mod_of_mul_modEq_one {e d m : ℕ} (hm : m ≠ 1) (h : e * d ≡ 1 [MOD m]) :
    0 < d % m :=
  Nat.pos_of_ne_zero fun h0 => hm <|
    (Nat.coprime_of_mul_modEq_one e (by rwa [mul_comm])).symm.eq_one_of_dvd
      (Nat.dvd_of_mod_eq_zero h0)

/-- Step 1 of RSA-CRT inversion computes `y ^ d mod p` ([BonehShoup2023], §16.4.3, p. 701, "by
definition of d_p"). The hypothesis `p ≠ 2` is not in the book; it is needed because
`d_p = d mod 1 = 0` when `p = 2`. -/
theorem powP_crtKeyWith (desc : RSADesc) (hp2 : desc.p ≠ 2) (qInv y : ℕ) :
    (desc.crtKeyWith qInv).powP y = y ^ desc.d % desc.p :=
  pow_mod_sub_one_modEq desc.hp
    (pos_mod_of_mul_modEq_one (by have := desc.hp.two_le; omega)
      (desc.hed.of_dvd (dvd_mul_right _ _))) y

/-- Step 2 of RSA-CRT inversion computes `y ^ d mod q` ([BonehShoup2023], §16.4.3, p. 701, "by
definition of d_q"). The hypothesis `q ≠ 2` is not in the book; it is needed because
`d_q = d mod 1 = 0` when `q = 2`. -/
theorem powQ_crtKeyWith (desc : RSADesc) (hq2 : desc.q ≠ 2) (qInv y : ℕ) :
    (desc.crtKeyWith qInv).powQ y = y ^ desc.d % desc.q :=
  pow_mod_sub_one_modEq desc.hq
    (pos_mod_of_mul_modEq_one (by have := desc.hq.two_le; omega)
      (desc.hed.of_dvd (dvd_mul_left _ _))) y

/-- **Correctness of RSA-CRT inversion** ([BonehShoup2023], §16.4.3, p. 701): for odd primes `p`
and `q` and any inverse `q_inv` of `q` modulo `p`, RSA-CRT inversion equals `y ^ d mod n` for
every `y`. The book does not state that `p` and `q` are odd; without it the statement fails (see
the module documentation). -/
theorem invert_crtKeyWith (desc : RSADesc) (hp2 : desc.p ≠ 2) (hq2 : desc.q ≠ 2) {qInv : ℕ}
    (hinv : qInv * desc.q ≡ 1 [MOD desc.p]) (y : ℕ) :
    (desc.crtKeyWith qInv).invert y = rsaInvert desc.modulus desc.d y := by
  have hP : (desc.crtKeyWith qInv).powP y = rsaInvert desc.modulus desc.d y % desc.p := by
    rw [desc.powP_crtKeyWith hp2, rsaInvert, RSADesc.modulus, Nat.mod_mul_right_mod]
  have hQ : (desc.crtKeyWith qInv).powQ y = rsaInvert desc.modulus desc.d y % desc.q := by
    rw [desc.powQ_crtKeyWith hq2, rsaInvert, RSADesc.modulus, Nat.mod_mul_left_mod]
  rw [RSACRTKey.invert, hP, hQ]
  exact RSACRTKey.combine_mod_mod _ hinv (Nat.mod_lt _ desc.modulus_pos)

/-- **Correctness of RSA-CRT inversion** with the key `crtKey`: for odd `p` and `q`, it equals
`y ^ d mod n` for every `y`. -/
theorem invert_crtKey (desc : RSADesc) (hp2 : desc.p ≠ 2) (hq2 : desc.q ≠ 2) (y : ℕ) :
    desc.crtKey.invert y = rsaInvert desc.modulus desc.d y :=
  desc.invert_crtKeyWith hp2 hq2 desc.crtQInv_mul_modEq_one y

/-- **The gcd step of the fault attack** ([BonehShoup2023], §16.4.3, p. 702): if `σ` agrees with
`h ^ d` modulo `q` but not modulo `p`, then `q` is the gcd of `n` and the representative in
`[0, n)` of `σ ^ e − h ∈ ℤ_n`. Any natural number `h` stands in for the hash value `H(m)`. -/
theorem gcd_val_pow_sub_eq_q (desc : RSADesc) {σ h : ℕ} (hσq : σ ≡ h ^ desc.d [MOD desc.q])
    (hσp : ¬ σ ≡ h ^ desc.d [MOD desc.p]) :
    Nat.gcd ((σ : ZMod desc.modulus) ^ desc.e - h).val desc.modulus = desc.q := by
  set v := ((σ : ZMod desc.modulus) ^ desc.e - h).val with hv_def
  have hv : v + h ≡ σ ^ desc.e [MOD desc.modulus] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hv_def, ZMod.natCast_zmod_val, sub_add_cancel]
  have hvq : desc.q ∣ v := by
    have h1 : σ ^ desc.e ≡ h [MOD desc.q] :=
      calc σ ^ desc.e ≡ (h ^ desc.d) ^ desc.e [MOD desc.q] := hσq.pow _
        _ = h ^ (desc.e * desc.d) := by rw [← pow_mul, mul_comm]
        _ ≡ h [MOD desc.q] := (rsa_pow_mul_modEq desc h).of_dvd (dvd_mul_left _ _)
    have h2 : v + h ≡ 0 + h [MOD desc.q] := by
      rw [zero_add]
      exact (hv.of_dvd (dvd_mul_left _ _)).trans h1
    exact Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_right_cancel' h h2)
  have hvp : ¬ desc.p ∣ v := by
    intro hdvd
    apply hσp
    have h1 : σ ^ desc.e ≡ h [MOD desc.p] := by
      have h2 : v + h ≡ 0 + h [MOD desc.p] := (Nat.modEq_zero_iff_dvd.2 hdvd).add_right h
      rw [zero_add] at h2
      exact (hv.of_dvd (dvd_mul_right _ _)).symm.trans h2
    calc σ ≡ σ ^ (desc.e * desc.d) [MOD desc.p] :=
          ((rsa_pow_mul_modEq desc σ).of_dvd (dvd_mul_right _ _)).symm
      _ = (σ ^ desc.e) ^ desc.d := pow_mul _ _ _
      _ ≡ h ^ desc.d [MOD desc.p] := h1.pow _
  change Nat.gcd v (desc.p * desc.q) = desc.q
  rw [Nat.Coprime.gcd_mul v ((Nat.coprime_primes desc.hp desc.hq).2 desc.hpq),
    Nat.gcd_eq_right hvq,
    Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd desc.hp).2 hvp)),
    one_mul]

/-- **The gcd identity behind the fault attack on RSA-CRT** ([BonehShoup2023], §16.4.3,
pp. 701–702): recombine any `x_q ≡ h ^ d (mod q)`, such as the correct `x_q = h ^ d mod q`, with
any `x_p'` that is not congruent to `h ^ d` modulo `p` (a faulty step 1). The output `σ`
satisfies `gcd(σ ^ e − h, n) = q`, with `σ ^ e − h ∈ ℤ_n` read in `[0, n)`. Any natural number
`h` stands in for the hash value `H(m)`, and `q_inv` is any inverse of `q` modulo `p`. For a
residue `x_p' < p` the hypothesis says `x_p' ≠ h ^ d mod p`, as in the book;
`RSADesc.powQ_crtKeyWith` shows that step 2 computes `x_q = h ^ d mod q` when `q` is odd. -/
theorem gcd_val_pow_sub_combine_eq_q (desc : RSADesc) {qInv : ℕ}
    (hinv : qInv * desc.q ≡ 1 [MOD desc.p]) {h xp xq : ℕ} (hxq : xq ≡ h ^ desc.d [MOD desc.q])
    (hxp : ¬ xp ≡ h ^ desc.d [MOD desc.p]) :
    Nat.gcd ((((desc.crtKeyWith qInv).combine xp xq : ℕ) : ZMod desc.modulus) ^ desc.e - h).val
      desc.modulus = desc.q :=
  desc.gcd_val_pow_sub_eq_q (((desc.crtKeyWith qInv).combine_modEq_q _ _).trans hxq)
    fun h' => hxp (((desc.crtKeyWith qInv).combine_modEq_p desc.hp.pos hinv xp xq).symm.trans h')

end RSADesc

/-! ### Polynomial-time certificates -/

section PolyTime

open Turing.MultiTapeTM

/-- RSA-CRT inversion ([BonehShoup2023], §16.4.3, p. 701) is computable in polynomial time
whenever the key components `p`, `q`, `d_p`, `d_q`, `q_inv` and the input `y` are computable in
polynomial time as natural numbers on `encNat`, and `0 < p a` and `0 < q a`. The positivity
hypotheses are those of `binary_powMod`: for `p a = 0`, step 1 would compute
`y ^ d_p % 0 = y ^ d_p`, whose length is exponential in that of `d_p`. -/
theorem computableInPolyTime_crtInvert {α : Type} {enc : α ↪ List Bool}
    {p q dp dq qInv y : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hq : ComputableInPolyTime q enc encNat)
    (hdp : ComputableInPolyTime dp enc encNat) (hdq : ComputableInPolyTime dq enc encNat)
    (hqInv : ComputableInPolyTime qInv enc encNat) (hy : ComputableInPolyTime y enc encNat)
    (hp_pos : ∀ a, 0 < p a) (hq_pos : ∀ a, 0 < q a) :
    ComputableInPolyTime
      (fun a => ({ p := p a, q := q a, dp := dp a, dq := dq a, qInv := qInv a } :
        RSACRTKey).invert (y a)) enc encNat := by
  have hxp := ComputableInPolyTime.binary_powMod hy hdp hp hp_pos
  have hxq := ComputableInPolyTime.binary_powMod hy hdq hq hq_pos
  simp only [RSACRTKey.invert, RSACRTKey.combine, RSACRTKey.powP, RSACRTKey.powQ, crtCombine]
  exact ComputableInPolyTime.binary_add' hxq
    (ComputableInPolyTime.binary_mul' hq
      (ComputableInPolyTime.binary_mod'
        (ComputableInPolyTime.binary_mul'
          (ComputableInPolyTime.binary_add' hxp
            (ComputableInPolyTime.binary_sub' hp (ComputableInPolyTime.binary_mod' hxq hp)))
          hqInv) hp))

/-- RSA-CRT inversion with the key `RSADesc.crtKeyWith desc qInv` is computable in polynomial
time whenever `p`, `q`, `d`, `q_inv` and the input are computable in polynomial time as natural
numbers on `encNat`; `p` and `q` are positive because they are prime. Here `q_inv` is an input,
as in the book, where it is part of the precomputed key; `computableInPolyTime_crtKey_invert`
computes it as `RSADesc.crtQInv`. -/
theorem computableInPolyTime_crtKeyWith_invert {α : Type} {enc : α ↪ List Bool}
    {desc : α → RSADesc} {qInv y : α → ℕ}
    (hp : ComputableInPolyTime (fun a => (desc a).p) enc encNat)
    (hq : ComputableInPolyTime (fun a => (desc a).q) enc encNat)
    (hd : ComputableInPolyTime (fun a => (desc a).d) enc encNat)
    (hqInv : ComputableInPolyTime qInv enc encNat) (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => ((desc a).crtKeyWith (qInv a)).invert (y a)) enc encNat := by
  have := computableInPolyTime_crtInvert hp hq
    (ComputableInPolyTime.binary_mod' hd
      (ComputableInPolyTime.binary_sub' hp (ComputableInPolyTime.const 1)))
    (ComputableInPolyTime.binary_mod' hd
      (ComputableInPolyTime.binary_sub' hq (ComputableInPolyTime.const 1)))
    hqInv hy (fun a => (desc a).hp.pos) (fun a => (desc a).hq.pos)
  simpa only [RSADesc.crtKeyWith] using this

/-- The inverse `RSADesc.crtQInv` of `q` modulo `p` is computable in polynomial time whenever
`p` and `q` are computable in polynomial time as natural numbers on `encNat`. It is
`BinaryGcd.modInv q p`, certified by `ComputableInPolyTime.binary_modInv'`. -/
theorem computableInPolyTime_crtQInv {α : Type} {enc : α ↪ List Bool} {desc : α → RSADesc}
    (hp : ComputableInPolyTime (fun a => (desc a).p) enc encNat)
    (hq : ComputableInPolyTime (fun a => (desc a).q) enc encNat) :
    ComputableInPolyTime (fun a => (desc a).crtQInv) enc encNat :=
  ComputableInPolyTime.binary_modInv' hq hp

/-- RSA-CRT inversion with the key `RSADesc.crtKey` ([BonehShoup2023], §16.4.3, p. 701) is
computable in polynomial time whenever `p`, `q`, `d` and the input are computable in polynomial
time as natural numbers on `encNat`: the key component `q_inv = RSADesc.crtQInv` is computed
from `p` and `q` by `computableInPolyTime_crtQInv`. -/
theorem computableInPolyTime_crtKey_invert {α : Type} {enc : α ↪ List Bool}
    {desc : α → RSADesc} {y : α → ℕ}
    (hp : ComputableInPolyTime (fun a => (desc a).p) enc encNat)
    (hq : ComputableInPolyTime (fun a => (desc a).q) enc encNat)
    (hd : ComputableInPolyTime (fun a => (desc a).d) enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => (desc a).crtKey.invert (y a)) enc encNat :=
  computableInPolyTime_crtKeyWith_invert hp hq hd (computableInPolyTime_crtQInv hp hq) hy

/-- `σ ^ e − h ∈ ℤ_n`, read in `[0, n)`, in natural-number operations. -/
private theorem val_natCast_pow_sub_natCast {n : ℕ} [NeZero n] (σ e h : ℕ) :
    ((σ : ZMod n) ^ e - (h : ZMod n)).val = (σ ^ e % n + (n - h % n)) % n := by
  rw [← ZMod.val_natCast (n := n) (σ ^ e % n + (n - h % n))]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_sub_mod_eq_neg, ZMod.natCast_mod, Nat.cast_pow]
  ring

/-- The gcd step of the fault attack on RSA-CRT ([BonehShoup2023], §16.4.3, p. 702),
`(n, e, σ, h) ↦ gcd(σ ^ e − h, n)` with `σ ^ e − h ∈ ℤ_n` read in `[0, n)` as in
`RSADesc.gcd_val_pow_sub_combine_eq_q`, is computable in polynomial time whenever `n`, `e`, `σ`
and `h` are computable in polynomial time as natural numbers on `encNat`, and `0 < n a`. The
positivity hypothesis is that of `binary_powMod`: `ZMod 0` is `ℤ`, where `σ ^ e − h` is not
reduced. This certifies the computation; nothing is proved about an attacker. -/
theorem computableInPolyTime_gcd_val_pow_sub {α : Type} {enc : α ↪ List Bool}
    {n e σ h : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hσ : ComputableInPolyTime σ enc encNat) (hh : ComputableInPolyTime h enc encNat)
    (hn_pos : ∀ a, 0 < n a) :
    ComputableInPolyTime
      (fun a => Nat.gcd (((σ a : ZMod (n a)) ^ e a - (h a : ZMod (n a))).val) (n a))
      enc encNat := by
  have hfun : (fun a => Nat.gcd (((σ a : ZMod (n a)) ^ e a - (h a : ZMod (n a))).val) (n a)) =
      fun a => Nat.gcd ((σ a ^ e a % n a + (n a - h a % n a)) % n a) (n a) := by
    funext a
    have : NeZero (n a) := ⟨(hn_pos a).ne'⟩
    rw [val_natCast_pow_sub_natCast]
  rw [hfun]
  exact ComputableInPolyTime.binary_gcd'
    (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_powMod hσ he hn hn_pos)
        (ComputableInPolyTime.binary_sub' hn (ComputableInPolyTime.binary_mod' hh hn))) hn) hn

end PolyTime

end Cslib.Crypto
