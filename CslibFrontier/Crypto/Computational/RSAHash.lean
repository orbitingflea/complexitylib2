/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.RSACommonRoot
public import CslibFrontier.Crypto.Computational.RSAUnitInversion
public import Mathlib.Data.Nat.Dist
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Collision resistance from RSA

[BonehShoup2023], §10.6.2, defines a hash function from an RSA modulus `n`, a prime encryption
exponent `e` and a random unit `y` modulo `n` (p. 415): `H_rsa(a, b) = a ^ e * y ^ b` for a unit
`a` modulo `n` and `0 ≤ b < e`. Theorem 10.7 (pp. 416–417) says that `H_rsa` is collision
resistant under the RSA assumption, with the bound (10.3) `CRadv[A, H_rsa] ≤ RSAadv[B, ℓ, e]`. The
proof turns a collision `(a, b) ≠ (a', b')` into `(a / a') ^ e = y ^ (b' - b)`; then `b ≠ b'`, so
`b' - b` is coprime to the prime `e`, and Shamir's trick (Theorem 10.6) gives an `e`-th root of
`y`. That is a win in the RSA game with a uniform unit preimage, and Theorem 10.5 bounds it by
the RSA advantage.

Here `rsaHash` is an instance of `Cslib.Crypto.collisionGameFor`, as
`Cslib.Crypto.PrimeOrderGroupFamily.groupHash` in
`CslibFrontier/Crypto/Computational/DiscreteLog/GroupHash.lean` is for the discrete-logarithm hash
`H_dl`. The key is an `RSAHashKey`, drawn by `rsaHashSetup`. A message is a word, and
`validRSAHashInput` accepts the words that encode a pair `(a, b)` with `a < N` coprime to `N` and
`b < e`.

## Main definitions

* `Cslib.Crypto.RSAHashKey`, `Cslib.Crypto.encRSAHashKey`: the key `(N, e, y)` and its encoding.
* `Cslib.Crypto.rsaHashSetup`: draws an RSA key from a generator and a uniform unit `y`.
* `Cslib.Crypto.rsaHash`, `Cslib.Crypto.validRSAHashInput`: the hash `H_rsa` on words and its
  domain.
* `Cslib.Crypto.rsaHashRoot`: the `e`-th root of `y` that Shamir's trick computes from a collision.
* `Cslib.Crypto.rsaHashToRSA`: the adversary `B'` of the proof of Theorem 10.7, an inverter for
  the RSA game with a uniform unit preimage.

## Main results

* `Cslib.Crypto.rsaEval_rsaHashRoot`: for `e` coprime to `b.dist b'`, `rsaHashRoot` turns
  pairs `(a, b)`, `(a', b')` with equal hashes into an `e`-th root of `y`.
* `Cslib.Crypto.isPPT_rsaHashToRSA`, `Cslib.Crypto.computableInPolyTime_rsaHash`,
  `Cslib.Crypto.computableInPolyTime_validRSAHashInput`: the reduction is PPT, and the hash and
  its domain are computable in polynomial time.
* `Cslib.Crypto.succProbability_collisionGameFor_rsaHash_le_rsaUnitInversionGame`: the success
  probability of a collision finder is at most that of `rsaHashToRSA` in the RSA game with a
  uniform unit preimage, at every security parameter where `e` is prime on the support.
* `Cslib.Crypto.succProbability_collisionGameFor_rsaHash_le_rsaInversionGame`: the bound (10.3).
* `Cslib.Crypto.RSAUnitOneWay.collisionResistantForOn_rsaHash`,
  `Cslib.Crypto.RSAOneWay.collisionResistantForOn_rsaHash`: Theorem 10.7, from either RSA
  assumption.

## Implementation notes

The statements differ from the book's in four ways.

* The bound is `≤`, where the proof shows `CRadv[A, H_rsa] = uRSAadv[B', ℓ, e]`. `rsaHashToRSA`
  does not test the pair it receives, so it also wins on some pairs that the collision game
  rejects: `encPair encNat encNat (1, 0) ++ [false]` is not a valid word, but it decodes to
  `(1, 0)`. The bound (10.3) needs only `≤`.
* The domain `ℤₙ* × I_e` is a set of words. `validRSAHashInput` requires the word to be the
  encoding of the pair it decodes to, so that distinct valid words are distinct pairs.
* Digests are natural numbers below `N`, not units modulo `N`.
* The book fixes a prime `e`. Here keys come from any law on `RSADesc` (`RSAGen`), and the bounds
  assume that `e` is prime for every key in its support, eventually in the security parameter.
  `rsaEval_rsaHashRoot` needs only that `e` is coprime to `b.dist b'`, as a prime `e` greater than
  both `b` and `b'`, with `b ≠ b'`, is. Coprimality with `(p - 1) * (q - 1)` is not enough: for
  `N = 15` and `e = 9`, the pairs `(1, 0)` and `(2, 3)` collide at `y = 2`, `9` is not coprime to
  their distance `3`, and the pair gives no ninth root of `2`. There is no condition on the length
  parameter `ℓ`.

The book's proof applies Theorem 10.6 with `f = b' - b`, which may be negative. `rsaHashRoot`
orders the pair instead: it takes `f = b' - b` and `w = a * a'⁻¹` when `b < b'`, and
`f = b - b'` and `w = a' * a⁻¹` otherwise, so `Cslib.Crypto.commonRoot` keeps natural exponents.

Exercise 10.26 (p. 431) and the use of `H_rsa` as a compression function in the Merkle–Damgård
construction (p. 416) are not formalized. The accumulator of §10.9 is in `GUOAccumulator.lean`,
without its security theorem.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §10.6.2, the definition of `H_rsa`, p. 415; Theorem 10.7, pp. 416–417, with (10.3) on p. 417.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- The key of the RSA hash ([BonehShoup2023], §10.6.2, p. 415): an RSA public key `(N, e)` and a
base `y`. -/
structure RSAHashKey where
  /-- The public key `(N, e)`. -/
  publicKey : RSAPublicKey
  /-- The base `y`, a unit modulo `N` in the experiment. -/
  base : ℕ

/-- The encoding of an RSA hash key: the public key, framed, and the base in binary. -/
enc_structure encRSAHashKey : RSAHashKey where
  publicKey : encRSAPublicKey, base : encNat

/-- Messages of the RSA hash are read as pairs of binary numbers. -/
@[expose] def rsaHashDecoder : Decoder (encPair encNat encNat) := Decoder.nat.pair Decoder.nat

/-- The key law of the RSA hash ([BonehShoup2023], §10.6.2, p. 415): draw `desc ← gen n` and a
uniform unit `y` modulo `N`, and return the public key with base `y`. -/
noncomputable def rsaHashSetup (gen : RSAGen) (n : ℕ) : PMF RSAHashKey := do
  let desc ← gen n
  let y ← PMF.uniformOfFintype (ZMod desc.modulus)ˣ
  return ⟨desc.publicKey, (y : ZMod desc.modulus).val⟩

/-- The RSA hash `H_rsa(a, b) = a ^ e * y ^ b` ([BonehShoup2023], §10.6.2, p. 415), on the pair
`(a, b)` that the word `m` decodes to, as a natural number below `N` (for `0 < N`). -/
@[expose] def rsaHash (k : RSAHashKey) (m : List Bool) : ℕ :=
  powMod k.publicKey.N (rsaHashDecoder.decode m).1 k.publicKey.e *
    powMod k.publicKey.N k.base (rsaHashDecoder.decode m).2 % k.publicKey.N

/-- The domain `ℤₙ* × I_e` of the RSA hash ([BonehShoup2023], §10.6.2, p. 415) on words: `m` is
the encoding of the pair `(a, b)` it decodes to, `a < N` is coprime to `N`, and `b < e`. -/
@[expose] def validRSAHashInput (_n : ℕ) (k : RSAHashKey) (m : List Bool) : Bool :=
  (encPair encNat encNat (rsaHashDecoder.decode m) == m) &&
    decide ((rsaHashDecoder.decode m).1 < k.publicKey.N) &&
    decide (Nat.Coprime (rsaHashDecoder.decode m).1 k.publicKey.N) &&
    decide ((rsaHashDecoder.decode m).2 < k.publicKey.e)

/-- The `e`-th root of `y` modulo `N` from a collision `(a, b)`, `(a', b')` of the RSA hash, as in
the proof of [BonehShoup2023], Theorem 10.7 (p. 417): Shamir's trick (`commonRoot`) with
`f = b' - b` and `w = a * a'⁻¹ mod N` when `b < b'`, and with `f = b - b'` and
`w = a' * a⁻¹ mod N` otherwise. -/
@[expose] def rsaHashRoot (N e y a b a' b' : ℕ) : ℕ :=
  if b < b' then commonRoot N e (b' - b) (a * BinaryGcd.modInv a' N % N) y
  else commonRoot N e (b - b') (a' * BinaryGcd.modInv a N % N) y

/-- The output of `rsaHashRoot` is below a positive modulus. -/
theorem rsaHashRoot_lt {N : ℕ} (hN : 0 < N) (e y a b a' b' : ℕ) :
    rsaHashRoot N e y a b a' b' < N := by
  unfold rsaHashRoot
  split <;> exact commonRoot_lt hN _ _ _ _

/-- One case of `rsaEval_rsaHashRoot`: for `b ≤ b'` and `e` coprime to `b' - b`, Shamir's trick
with `f = b' - b` and `w = a * a'⁻¹ mod N` returns an `e`-th root of `y`. -/
private theorem rsaEval_commonRoot_of_modEq {N e y a b a' b' : ℕ} (hy : y < N)
    (hyN : Nat.Coprime y N) (ha : Nat.Coprime a N) (ha' : Nat.Coprime a' N) (hbb' : b ≤ b')
    (hef : Nat.Coprime e (b' - b)) (h : a ^ e * y ^ b ≡ a' ^ e * y ^ b' [MOD N]) :
    rsaEval N e (commonRoot N e (b' - b) (a * BinaryGcd.modInv a' N % N) y) = y := by
  have hN : 0 < N := Nat.zero_lt_of_lt hy
  set f := b' - b with hf_def
  set w := a * BinaryGcd.modInv a' N % N with hw_def
  have hcancel : a ^ e ≡ a' ^ e * y ^ f [MOD N] := by
    refine Nat.ModEq.cancel_right_of_coprime (c := y ^ b) ?_ ?_
    · exact Nat.Coprime.symm (Nat.Coprime.pow_left b hyN)
    · rw [mul_assoc, ← pow_add, hf_def, Nat.sub_add_cancel hbb']
      exact h
  have hinv : a' * BinaryGcd.modInv a' N ≡ 1 [MOD N] := BinaryGcd.mul_modInv_modEq_one hN ha'
  have hwe : w ^ e ≡ y ^ f [MOD N] :=
    calc w ^ e ≡ (a * BinaryGcd.modInv a' N) ^ e [MOD N] := (Nat.mod_modEq _ _).pow e
      _ = a ^ e * BinaryGcd.modInv a' N ^ e := mul_pow _ _ _
      _ ≡ a' ^ e * y ^ f * BinaryGcd.modInv a' N ^ e [MOD N] := hcancel.mul_right _
      _ = (a' * BinaryGcd.modInv a' N) ^ e * y ^ f := by ring
      _ ≡ 1 ^ e * y ^ f [MOD N] := (hinv.pow e).mul_right _
      _ = y ^ f := by rw [one_pow, one_mul]
  have hw : Nat.Coprime w N :=
    (ZMod.coprime_mod_iff_coprime _ _).mpr
      (ha.mul_left (Nat.coprime_of_mul_modEq_one a' (by rwa [mul_comm])))
  have hroot := commonRoot_pow_modEq_right hN hef hw hwe
  rw [rsaEval]
  exact Eq.trans hroot (Nat.mod_eq_of_lt hy)

/-- **The root from a collision** ([BonehShoup2023], proof of Theorem 10.7, p. 417). For `e`
coprime to `b.dist b'` (`b' - b` if `b ≤ b'`, else `b - b'`), units `y`, `a` and `a'` modulo `N`
with `y < N` and `a ^ e * y ^ b ≡ a' ^ e * y ^ b' [MOD N]`, `rsaHashRoot` returns an `e`-th root
of `y`. As in the book, a prime `e` greater than both `b` and `b'`, with `b ≠ b'`, is coprime to
`b.dist b'`; `b = b'` is allowed and forces `e = 1`. -/
theorem rsaEval_rsaHashRoot {N e y a b a' b' : ℕ} (hy : y < N) (hyN : Nat.Coprime y N)
    (ha : Nat.Coprime a N) (ha' : Nat.Coprime a' N) (hef : Nat.Coprime e (b.dist b'))
    (h : a ^ e * y ^ b ≡ a' ^ e * y ^ b' [MOD N]) :
    rsaEval N e (rsaHashRoot N e y a b a' b') = y := by
  unfold rsaHashRoot
  split_ifs with hbb'
  · exact rsaEval_commonRoot_of_modEq hy hyN ha ha' hbb'.le
      (Nat.dist_eq_sub_of_le hbb'.le ▸ hef) h
  · have hb'b : b' ≤ b := Nat.le_of_not_lt hbb'
    exact rsaEval_commonRoot_of_modEq hy hyN ha' ha hb'b
      (Nat.dist_eq_sub_of_le_right hb'b ▸ hef) h.symm

/-- The adversary `B'` of the proof of [BonehShoup2023], Theorem 10.7 (p. 417): on a public key
`(N, e)` and a challenge `y`, run the collision finder on the key `(N, e, y)`, decode its two words
to pairs and return `rsaHashRoot` of them. It does not check that the pair is a collision. -/
def rsaHashToRSA (A : CollisionFinderFor RSAHashKey) : RSAInverter := fun n pk y =>
  (fun pair => ⟨rsaHashRoot pk.N pk.e y (rsaHashDecoder.decode pair.1).1
      (rsaHashDecoder.decode pair.1).2 (rsaHashDecoder.decode pair.2).1
      (rsaHashDecoder.decode pair.2).2, rsaHashRoot_lt y.pos _ _ _ _ _ _⟩) <$> A n ⟨pk, y⟩

/-- `rsaHashRoot` is computable in polynomial time whenever its seven inputs are. -/
theorem computableInPolyTime_rsaHashRoot {α : Type} {enc : α ↪ List Bool}
    {N e y a b a' b' : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hy : ComputableInPolyTime y enc encNat) (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (ha' : ComputableInPolyTime a' enc encNat)
    (hb' : ComputableInPolyTime b' enc encNat) :
    ComputableInPolyTime (fun x => rsaHashRoot (N x) (e x) (y x) (a x) (b x) (a' x) (b' x))
      enc encNat := by
  have hw {u v : α → ℕ} (hu : ComputableInPolyTime u enc encNat)
      (hv : ComputableInPolyTime v enc encNat) :
      ComputableInPolyTime (fun x => u x * BinaryGcd.modInv (v x) (N x) % N x) enc encNat :=
    ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul' hu (ComputableInPolyTime.binary_modInv' hv hN)) hN
  unfold rsaHashRoot
  exact ComputableInPolyTime.ite_decide (ComputableInPolyTime.binary_lt' hb hb')
    (computableInPolyTime_commonRoot hN he (ComputableInPolyTime.binary_sub' hb' hb)
      (hw ha ha') hy)
    (computableInPolyTime_commonRoot hN he (ComputableInPolyTime.binary_sub' hb hb')
      (hw ha' ha) hy)

/-- `rsaHashToRSA A` is a PPT `RSAInverter` whenever the collision finder `A` is PPT on
`(1ⁿ, k)`. -/
theorem isPPT_rsaHashToRSA {A : CollisionFinderFor RSAHashKey}
    (hA : IsPPTOn (encPair encUnary encRSAHashKey) (encPair encBits encBits)
      (fun p => A p.1 p.2)) : (rsaHashToRSA A).IsPPT := by
  have hrun : IsPPTOn encRSAInput (encPair encBits encBits)
      (fun x : RSAInput => A x.secParam ⟨x.publicKey, x.challenge⟩) :=
    hA.preprocess
      (prepare := fun x : RSAInput => (x.secParam, (⟨x.publicKey, x.challenge⟩ : RSAHashKey)))
      (by fun_prop)
  have hd₁ : ComputableInPolyTime
      (fun p : RSAInput × (List Bool × List Bool) => rsaHashDecoder.decode p.2.1)
      (encPair encRSAInput (encPair encBits encBits)) (encPair encNat encNat) :=
    rsaHashDecoder.computableInPolyTime.comp (by fun_prop)
  have hd₂ : ComputableInPolyTime
      (fun p : RSAInput × (List Bool × List Bool) => rsaHashDecoder.decode p.2.2)
      (encPair encRSAInput (encPair encBits encBits)) (encPair encNat encNat) :=
    rsaHashDecoder.computableInPolyTime.comp (by fun_prop)
  have hroot : ComputableInPolyTime
      (fun p : RSAInput × (List Bool × List Bool) =>
        rsaHashRoot p.1.publicKey.N p.1.publicKey.e p.1.challenge
          (rsaHashDecoder.decode p.2.1).1 (rsaHashDecoder.decode p.2.1).2
          (rsaHashDecoder.decode p.2.2).1 (rsaHashDecoder.decode p.2.2).2)
      (encPair encRSAInput (encPair encBits encBits)) encNat :=
    computableInPolyTime_rsaHashRoot (by fun_prop) (by fun_prop) (by fun_prop)
      hd₁.fst' hd₁.snd' hd₂.fst' hd₂.snd'
  refine (hrun.map_with
    (f := fun x pair => rsaHashRoot x.publicKey.N x.publicKey.e x.challenge
      (rsaHashDecoder.decode pair.1).1 (rsaHashDecoder.decode pair.1).2
      (rsaHashDecoder.decode pair.2).1 (rsaHashDecoder.decode pair.2).2) hroot).congr fun x => ?_
  simp only [rsaHashToRSA, Functor.map_map]

/-- The RSA hash is computable in polynomial time from the key and the word. -/
theorem computableInPolyTime_rsaHash :
    ComputableInPolyTime (fun p : RSAHashKey × List Bool => rsaHash p.1 p.2)
      (encPair encRSAHashKey encBits) encNat := by
  have hd : ComputableInPolyTime (fun p : RSAHashKey × List Bool => rsaHashDecoder.decode p.2)
      (encPair encRSAHashKey encBits) (encPair encNat encNat) :=
    rsaHashDecoder.computableInPolyTime.comp (ComputableInPolyTime.snd _ _)
  have hN : ComputableInPolyTime (fun p : RSAHashKey × List Bool => p.1.publicKey.N)
      (encPair encRSAHashKey encBits) encNat := by fun_prop
  unfold rsaHash
  exact ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul'
      (computableInPolyTime_powMod hN hd.fst' (by fun_prop))
      (computableInPolyTime_powMod hN (by fun_prop) hd.snd')) hN

/-- The domain test of the RSA hash is computable in polynomial time. -/
theorem computableInPolyTime_validRSAHashInput :
    ComputableInPolyTime
      (fun p : (ℕ × RSAHashKey) × List Bool => validRSAHashInput p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encRSAHashKey) encBits) encBool := by
  have hd : ComputableInPolyTime
      (fun p : (ℕ × RSAHashKey) × List Bool => rsaHashDecoder.decode p.2)
      (encPair (encPair encUnary encRSAHashKey) encBits) (encPair encNat encNat) :=
    rsaHashDecoder.computableInPolyTime.comp (ComputableInPolyTime.snd _ _)
  have hN : ComputableInPolyTime (fun p : (ℕ × RSAHashKey) × List Bool => p.1.2.publicKey.N)
      (encPair (encPair encUnary encRSAHashKey) encBits) encNat := by fun_prop
  have he : ComputableInPolyTime (fun p : (ℕ × RSAHashKey) × List Bool => p.1.2.publicKey.e)
      (encPair (encPair encUnary encRSAHashKey) encBits) encNat := by fun_prop
  have hcanon : ComputableInPolyTime
      (fun p : (ℕ × RSAHashKey) × List Bool =>
        encPair encNat encNat (rsaHashDecoder.decode p.2) == p.2)
      (encPair (encPair encUnary encRSAHashKey) encBits) encBool :=
    ComputableInPolyTime.beq hd.encoding_comp (ComputableInPolyTime.snd _ _)
  have hlt := ComputableInPolyTime.binary_lt' hd.fst' hN
  have hcop := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.binary_gcd' hd.fst' hN) (ComputableInPolyTime.const 1)
  have hlt₂ := ComputableInPolyTime.binary_lt' hd.snd' he
  unfold validRSAHashInput
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and' (ComputableTidilyInPolyTime.bool_and'
    (ComputableTidilyInPolyTime.bool_and' hcanon.tidy hlt.tidy) hcop.tidy) hlt₂.tidy)

/-- A collision of the RSA hash at a key with prime `e` and a unit base `y < N` decodes to pairs
from which `rsaHashRoot` computes an `e`-th root of `y`. -/
private theorem rsaEval_rsaHashRoot_of_isCollisionFor (desc : RSADesc) (he : desc.e.Prime)
    {y : ℕ} (hy : y < desc.modulus) (hyN : Nat.Coprime y desc.modulus) {n : ℕ}
    {m₁ m₂ : List Bool}
    (hcoll : isCollisionFor (Param := RSAHashKey) (Digest := fun _ => ℕ) rsaHash
      validRSAHashInput n ⟨desc.publicKey, y⟩ m₁ m₂ = true) :
    rsaEval desc.modulus desc.e (rsaHashRoot desc.modulus desc.e y (rsaHashDecoder.decode m₁).1
      (rsaHashDecoder.decode m₁).2 (rsaHashDecoder.decode m₂).1 (rsaHashDecoder.decode m₂).2) =
      y := by
  rw [isCollisionFor_eq_true_iff] at hcoll
  obtain ⟨hv₁, hv₂, hne, hH⟩ := hcoll
  simp only [validRSAHashInput, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv₁ hv₂
  obtain ⟨⟨⟨hc₁, ha₁⟩, hu₁⟩, hb₁⟩ := hv₁
  obtain ⟨⟨⟨hc₂, ha₂⟩, hu₂⟩, hb₂⟩ := hv₂
  simp only [rsaHash, powMod_of_ne_zero desc.modulus_pos.ne'] at hH
  set a := (rsaHashDecoder.decode m₁).1
  set b := (rsaHashDecoder.decode m₁).2
  set a' := (rsaHashDecoder.decode m₂).1
  set b' := (rsaHashDecoder.decode m₂).2
  have hmod : a ^ desc.e * y ^ b ≡ a' ^ desc.e * y ^ b' [MOD desc.modulus] := by
    rwa [Nat.ModEq, Nat.mul_mod, Nat.mul_mod (a' ^ desc.e)]
  have hbb' : b ≠ b' := by
    intro hbb
    rw [← hbb] at hmod
    have hae : a ^ desc.e ≡ a' ^ desc.e [MOD desc.modulus] :=
      Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm (Nat.Coprime.pow_left b hyN)) hmod
    have haa : a = a' := congrArg Fin.val
      ((rsaEval_bijective_fin desc).injective (a₁ := ⟨a, ha₁⟩) (a₂ := ⟨a', ha₂⟩) (Fin.ext hae))
    exact hne (hc₁.symm.trans ((congrArg (encPair encNat encNat) (Prod.ext haa hbb)).trans hc₂))
  have hef : Nat.Coprime desc.e (b.dist b') :=
    (Nat.Prime.coprime_iff_not_dvd he).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.dist_pos_of_ne hbb') (by unfold Nat.dist; omega))
  exact rsaEval_rsaHashRoot hy hyN hu₁ hu₂ hef hmod

/-- **The reduction of Theorem 10.7** ([BonehShoup2023], p. 417): at every security parameter `n`
where `e` is prime for every key in the support of `gen n`, the success probability of a collision
finder `A` against the RSA hash is at most that of `rsaHashToRSA A` in the RSA game with a uniform
unit preimage. The book proves equality, `CRadv[A, H_rsa] = uRSAadv[B', ℓ, e]`; `rsaHashToRSA`
does not test its pair, so it can also win when the pair is not a collision. -/
theorem succProbability_collisionGameFor_rsaHash_le_rsaUnitInversionGame (gen : RSAGen)
    (A : CollisionFinderFor RSAHashKey) (n : ℕ)
    (hprime : ∀ desc ∈ (gen n).support, desc.e.Prime) :
    Game.succProbability
        (collisionGameFor (Param := RSAHashKey) (Digest := fun _ => ℕ)
          (rsaHashSetup gen) rsaHash validRSAHashInput A n) ≤
      Game.succProbability (rsaUnitInversionGame gen (rsaHashToRSA A) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rw [rsaUnitInversionGame_eq]
  dsimp only [collisionGameFor, Game.withSetup, collisionExperiment, rsaHashSetup,
    rsaHashToRSA, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  refine PMF.bind_apply_mono_on_support (gen n) true fun desc hdesc => ?_
  have hinj := (rsaEval_bijective_fin desc).injective
  have hchal (x : (ZMod desc.modulus)ˣ) :
      desc.publicKey.eval (desc.unitResidue x) = desc.unitResidue (x ^ desc.e) := by
    ext
    rw [RSAPublicKey.val_eval]
    simp only [RSADesc.unitResidue, rsaEval, Units.val_pow_eq_pow_val]
    rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
  have hwin (x : (ZMod desc.modulus)ˣ) (r : Fin desc.modulus) :
      r = desc.unitResidue x ↔
        rsaEval desc.modulus desc.e r = (desc.unitResidue (x ^ desc.e) : ℕ) := by
    rw [← hinj.eq_iff, hchal, Fin.ext_iff, RSAPublicKey.val_eval]
  let G : (ZMod desc.modulus)ˣ → PMF Bool := fun y =>
    (A n ⟨desc.publicKey, (y : ZMod desc.modulus).val⟩).eval.bind fun pair =>
      PMF.pure (decide (rsaEval desc.modulus desc.e (rsaHashRoot desc.modulus desc.e
        (y : ZMod desc.modulus).val (rsaHashDecoder.decode pair.1).1
        (rsaHashDecoder.decode pair.1).2 (rsaHashDecoder.decode pair.2).1
        (rsaHashDecoder.decode pair.2).2) = (y : ZMod desc.modulus).val))
  refine le_of_le_of_eq (b := ((PMF.uniformOfFintype (ZMod desc.modulus)ˣ).bind G) true) ?_
    (congrArg (· true)
      (PMF.uniformOfFintype_bind_bijective (rsaEval_bijective_units desc) (k := G)
        fun x => ?_).symm)
  · refine PMF.bind_apply_mono_on_support _ true fun y _ => ?_
    refine PMF.bind_apply_mono_on_support _ true fun pair _ => ?_
    by_cases hcoll : isCollisionFor (Param := RSAHashKey) (Digest := fun _ => ℕ) rsaHash
        validRSAHashInput n ⟨desc.publicKey, (y : ZMod desc.modulus).val⟩ pair.1 pair.2 = true
    · have hroot := rsaEval_rsaHashRoot_of_isCollisionFor desc (hprime desc hdesc)
        (ZMod.val_lt _) (ZMod.val_coe_unit_coprime y) hcoll
      exact (PMF.coe_le_one _ _).trans_eq (by simp [hroot])
    · simp [Bool.eq_false_iff.mpr hcoll]
  · simp only [G, hwin, hchal]
    rfl

/-- **The bound (10.3)** ([BonehShoup2023], Theorem 10.7, p. 417): at every security parameter
`n` where `e` is prime for every key in the support of `gen n`, the success probability of a
collision finder `A` against the RSA hash is at most that of the elementary wrapper
`unitRSAToRSA (rsaHashToRSA A)` in `rsaInversionGame`. -/
theorem succProbability_collisionGameFor_rsaHash_le_rsaInversionGame (gen : RSAGen)
    (A : CollisionFinderFor RSAHashKey) (n : ℕ)
    (hprime : ∀ desc ∈ (gen n).support, desc.e.Prime) :
    Game.succProbability
        (collisionGameFor (Param := RSAHashKey) (Digest := fun _ => ℕ)
          (rsaHashSetup gen) rsaHash validRSAHashInput A n) ≤
      Game.succProbability (rsaInversionGame gen (unitRSAToRSA (rsaHashToRSA A)) n) :=
  (succProbability_collisionGameFor_rsaHash_le_rsaUnitInversionGame gen A n hprime).trans
    (succProbability_rsaUnitInversionGame_le gen _ n)

/-- **Theorem 10.7 from the unit-preimage RSA assumption** ([BonehShoup2023], §10.6.2,
pp. 416–417): if `RSAUnitOneWay gen` holds and, for all sufficiently large `n`, `e` is prime for
every key in the support of `gen n`, then the RSA hash is collision resistant on
`validRSAHashInput` under `rsaHashSetup gen`. -/
theorem RSAUnitOneWay.collisionResistantForOn_rsaHash {gen : RSAGen} (h : RSAUnitOneWay gen)
    (hprime : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, desc.e.Prime) :
    CollisionResistantForOn (Param := RSAHashKey) (Digest := fun _ => ℕ)
      encRSAHashKey (rsaHashSetup gen) rsaHash validRSAHashInput := by
  refine CollisionResistantForOn.of_negligible fun A hA => ?_
  refine negligible_of_eventually_le (h (rsaHashToRSA A) (isPPT_rsaHashToRSA hA)) ?_
  filter_upwards [hprime] with n hn
  exact succProbability_collisionGameFor_rsaHash_le_rsaUnitInversionGame gen A n hn

/-- **Theorem 10.7** ([BonehShoup2023], §10.6.2, pp. 416–417): if `RSAOneWay gen` holds and, for
all sufficiently large `n`, `e` is prime for every key in the support of `gen n`, then the RSA
hash is collision resistant on `validRSAHashInput` under `rsaHashSetup gen`. -/
theorem RSAOneWay.collisionResistantForOn_rsaHash {gen : RSAGen} (h : RSAOneWay gen)
    (hprime : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, desc.e.Prime) :
    CollisionResistantForOn (Param := RSAHashKey) (Digest := fun _ => ℕ)
      encRSAHashKey (rsaHashSetup gen) rsaHash validRSAHashInput :=
  h.rsaUnitOneWay.collisionResistantForOn_rsaHash hprime

end Cslib.Crypto
