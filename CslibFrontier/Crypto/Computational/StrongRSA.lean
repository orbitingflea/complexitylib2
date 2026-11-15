/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Crypto.Game.Experiment
import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Support
import Mathlib.GroupTheory.OrderOfElement

/-!
# The strong RSA assumption

[BonehShoup2023], §10.9, p. 420, calls a pair `(G, g)` of a finite abelian group `G` and an
element `g ∈ G` a group of unknown order when the size of `G` is hard to deduce from `(G, g)`; a
probabilistic algorithm `GGen` draws it. In the strong RSA game the adversary receives `(G, g)`
and wins when it outputs `(x, e) ∈ G × ℤ` with `x ^ e = g` and `e ≠ ±1`. `GGen` satisfies the
strong RSA assumption when no efficient adversary wins with non-negligible probability. The book
remarks that this is a stronger assumption than standard RSA; no implication between `StrongRSA`
and `RSAOneWay` or `RSAUnitOneWay` is formalized here. On p. 421 the book observes that the
assumption is false when the order `u` of `g`, or a multiple of it, is known: for `v > 1` coprime
to `u`, the element `x = g ^ (v⁻¹ mod u)` satisfies `x ^ v = g`. Its example of `GGen` draws an
RSA modulus `n` from `RSAGen(ℓ, e)` and a uniform `g ∈ ℤₙ*`.

## Main definitions

* `Cslib.Crypto.GUOParams`, `Cslib.Crypto.encGUOParams`: the public parameters `(N, g)` of the
  group `(ZMod N)ˣ` and their encoding.
* `Cslib.Crypto.StrongRSAAdversary`, `Cslib.Crypto.StrongRSAAdversary.IsPPT`: adversaries of the
  strong RSA game and their efficiency on encodings.
* `Cslib.Crypto.isStrongRSASolution`, `Cslib.Crypto.strongRSAGame`, `Cslib.Crypto.StrongRSA`: the
  winning condition, the game and the strong RSA assumption for a setup law.
* `Cslib.Crypto.rsaGUOSetup`: the book's `GGen` for an RSA key generator.
* `Cslib.Crypto.knownOrderRoot`, `Cslib.Crypto.knownOrderAdversary`: the root `g ^ (v⁻¹ mod u)` of
  p. 421 and the adversary that outputs it with the exponent `v`.
* `Cslib.Crypto.orderMultipleAdversary`: the adversary of p. 421 for a multiple `u` of the order,
  with `v = u + 1`.

## Main results

* `Cslib.Crypto.not_strongRSA_of_orderMultiple`: **the observation of p. 421**. If a
  polynomial-time function `u` of the security parameter and `(N, g)` gives `0 < u` and
  `g ^ u ≡ 1 [MOD N]` for every supported `(N, g)`, then `StrongRSA setup` does not hold:
  `orderMultipleAdversary u` is PPT (`isPPT_orderMultipleAdversary`) and wins with probability
  `1` (`strongRSAGame_orderMultipleAdversary`).
* `Cslib.Crypto.strongRSAGame_orderMultipleAdversary`: `orderMultipleAdversary u` wins with
  probability `1` at every security parameter where `0 < u` and `g ^ u ≡ 1 [MOD N]` for every
  supported `(N, g)`.
* `Cslib.Crypto.exists_of_mem_support_rsaGUOSetup`: every `(N, g)` drawn by `rsaGUOSetup` has the
  modulus of a supported key and a base `g` coprime to `N`.
* `Cslib.Crypto.powMod_knownOrderRoot`: for `0 < u`, `g ^ u ≡ 1 [MOD N]` and `v` coprime to `u`,
  `knownOrderRoot N u v g` is a `v`-th root of `g` modulo `N`.
* `Cslib.Crypto.isPPT_knownOrderAdversary`: the known-order adversary is PPT when its exponents are
  computable in polynomial time from the security parameter and `(N, g)`.
* `Cslib.Crypto.strongRSAGame_knownOrderAdversary`: it wins with probability `1` at every security
  parameter where `g ^ u ≡ 1 [MOD N]`, `v` is coprime to `u` and `v ≠ 1` for every supported
  `(N, g)`.
* `Cslib.Crypto.not_strongRSA_of_knownOrder`: the general form of the observation, for any such
  exponent `v` computed in polynomial time.

## Implementation notes

The statements differ from the book's in three ways.

* The group is `(ZMod N)ˣ`, the group of the book's `GGen` from RSA keys (p. 421).
  `GUOParams` holds the natural numbers `N` and `g`, and a setup is any law `ℕ → PMF GUOParams`,
  which need not be efficiently samplable or give a unit `g`. `rsaGUOSetup gen` is the book's
  `GGen`, with keys from any law `gen` on `RSADesc` in place of `RSAGen(ℓ, e)`. Class groups
  (p. 423) are not covered.
* The adversary outputs natural numbers `x` and `e`, and wins when `x ^ e ≡ g` modulo `N` and
  `e ≠ 1` (`isStrongRSASolution_eq_true_iff` for `0 < N`). The book's integer exponents `e ≤ -2`
  are left out: `x ^ e = g` with `e < 0` is `(x⁻¹) ^ (-e) = g`. For a unit `g`, every output that
  wins here gives one that wins the book's game (`x` modulo `N`, or `1` when `e = 0`), so for a
  setup that gives a unit `g` this assumption is implied by the book's; that implication is not
  formalized. As in the book, `e = 0` wins exactly when `g ≡ 1`.
* "The order of `g` is known" (p. 421) is read as: a multiple `u` of the order, with `0 < u` and
  `g ^ u ≡ 1 [MOD N]`, is a polynomial-time function of the security parameter, in unary, and
  `(N, g)`. The adversary then takes `v = u + 1`, which is greater than `1` and coprime to `u`
  (`orderMultipleAdversary`). The general lemmas take any polynomial-time `v ≠ 1` coprime to `u`
  in place of the book's `v > 1`; this admits `v = 0` only when `u = 1`, so `0 < u` follows.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §10.9, the strong RSA game and assumption, p. 420; the known-order observation and `GGen` from
  `RSAGen`, p. 421.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The public parameters `(G, g)` of a group of unknown order ([BonehShoup2023], §10.9, p. 420)
for `G = (ZMod N)ˣ`: the modulus `N` and the base `g`. -/
structure GUOParams where
  /-- The modulus `N`; the group is `(ZMod N)ˣ`. -/
  modulus : ℕ
  /-- The base `g`, a unit modulo `N` under `rsaGUOSetup`. -/
  base : ℕ

/-- The encoding of the public parameters: `N` and `g` in binary, `N` framed
(`encGUOParams_apply`). -/
enc_structure encGUOParams : GUOParams where
  modulus : encNat, base : encNat

/-- An adversary of the strong RSA game: given the security parameter and the public parameters
`(N, g)`, it outputs a pair `(x, e)`. `StrongRSAAdversary.IsPPT` states its efficiency on
encodings. -/
abbrev StrongRSAAdversary : Type := ℕ → GUOParams → ProbComp (ℕ × ℕ)

/-- A strong RSA adversary is PPT when one uniform strict PPT machine reads the unary security
parameter followed by `encGUOParams`, and writes `(x, e)` as a pair of binary numbers. -/
@[expose] def StrongRSAAdversary.IsPPT (A : StrongRSAAdversary) : Prop :=
  IsPPTOn (encPair encUnary encGUOParams) (encPair encNat encNat) fun p => A p.1 p.2

/-- The winning condition of the strong RSA game ([BonehShoup2023], §10.9, p. 420) in
`(ZMod N)ˣ`: `x ^ e` and `g` agree modulo `N`, computed with `powMod`, and `e ≠ 1`. For `0 < N`
this is `x ^ e ≡ g [MOD N] ∧ e ≠ 1` (`isStrongRSASolution_eq_true_iff`). For `N = 0`,
`powMod 0 x e = 1`, so `(x, e)` wins exactly when `g = 1` and `e ≠ 1`. -/
@[expose] def isStrongRSASolution (p : GUOParams) (s : ℕ × ℕ) : Bool :=
  powMod p.modulus s.1 s.2 == p.base % p.modulus && s.2 != 1

/-- For `0 < N`, `(x, e)` wins exactly when `x ^ e ≡ g [MOD N]` and `e ≠ 1`. -/
theorem isStrongRSASolution_eq_true_iff {p : GUOParams} (hN : 0 < p.modulus) (s : ℕ × ℕ) :
    isStrongRSASolution p s = true ↔ s.1 ^ s.2 ≡ p.base [MOD p.modulus] ∧ s.2 ≠ 1 := by
  simp [isStrongRSASolution, powMod_of_ne_zero hN.ne', Nat.ModEq]

/-- The strong RSA game ([BonehShoup2023], §10.9, p. 420): draw `p ← setup n`, run the adversary on
`(n, p)`, and accept its output `(x, e)` when `isStrongRSASolution p (x, e)`. -/
@[expose] noncomputable def strongRSAGame (setup : ℕ → PMF GUOParams) (A : StrongRSAAdversary)
    (n : ℕ) : Game :=
  Game.withSetup (setup n) fun p => do
    let s ← A n p
    return isStrongRSASolution p s

/-- **The strong RSA assumption** for the setup law `setup` ([BonehShoup2023], §10.9, p. 420):
every PPT adversary wins `strongRSAGame` with negligible probability. Two differences from the
book. The group is `(ZMod N)ˣ` for public parameters `(N, g)` drawn from any law, which need not be
efficiently samplable or give a unit `g`, in place of a group of unknown order from an efficient
`GGen`; `rsaGUOSetup gen` is the book's `GGen` (p. 421). The adversary outputs natural numbers `x`
and `e ≠ 1` in place of `x ∈ G` and an integer `e ≠ ±1`. For a unit `g`, every output that wins
here gives one that wins the book's game, so for a setup that gives a unit `g` the book's
assumption implies this one. -/
@[expose] def StrongRSA (setup : ℕ → PMF GUOParams) : Prop :=
  ∀ A : StrongRSAAdversary, A.IsPPT →
    Negligible fun n => Game.succProbability (strongRSAGame setup A n)

/-- The group generator `GGen` of [BonehShoup2023], §10.9, p. 421, for the RSA key generator
`gen`: draw `desc ← gen n` and a uniform unit `g` modulo `N = desc.modulus`, and return `(N, g)`
with `g` read in `[0, N)`. The book draws `n` from `RSAGen(ℓ, e)`; here `gen` is any law on
`RSADesc`. Every base it draws is a unit (`exists_of_mem_support_rsaGUOSetup`). -/
noncomputable def rsaGUOSetup (gen : RSAGen) (n : ℕ) : PMF GUOParams := do
  let desc ← gen n
  let g ← PMF.uniformOfFintype (ZMod desc.modulus)ˣ
  return ⟨desc.modulus, (g : ZMod desc.modulus).val⟩

/-- Every `(N, g)` drawn by `rsaGUOSetup gen n` has the modulus `N` of a key in the support of
`gen n` and a base `g` coprime to `N`. -/
theorem exists_of_mem_support_rsaGUOSetup {gen : RSAGen} {n : ℕ} {p : GUOParams}
    (hp : p ∈ (rsaGUOSetup gen n).support) :
    ∃ desc ∈ (gen n).support, p.modulus = desc.modulus ∧ Nat.Coprime p.base p.modulus := by
  simp only [rsaGUOSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨desc, hdesc, g, -, rfl⟩ := hp
  exact ⟨desc, hdesc, rfl, ZMod.val_coe_unit_coprime g⟩

/-! ### The known-order observation -/

/-- The root `g ^ (v⁻¹ mod u)` modulo `N` of [BonehShoup2023], §10.9, p. 421, with `v⁻¹ mod u`
computed as `BinaryGcd.modInv v u`. When `g ^ u ≡ 1 [MOD N]` for some `0 < u` and `v` is coprime
to `u`, it is a `v`-th root of `g` (`powMod_knownOrderRoot`). The book does not name it;
`knownOrderRoot` is this library's name. -/
@[expose] def knownOrderRoot (N u v g : ℕ) : ℕ := powMod N g (BinaryGcd.modInv v u)

/-- For `0 < u` with `g ^ u ≡ 1 [MOD N]` and `v` coprime to `u`, `knownOrderRoot N u v g` is a
`v`-th root of `g` modulo `N` ([BonehShoup2023], §10.9, p. 421). There is no condition on `N`. -/
theorem powMod_knownOrderRoot {N u v g : ℕ} (hu : 0 < u) (hg : g ^ u ≡ 1 [MOD N])
    (hv : Nat.Coprime v u) : powMod N (knownOrderRoot N u v g) v = g % N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Modulo `0`, `g ^ u = 1` with `0 < u` forces `g = 1`.
    have hg1 : g = 1 :=
      (Nat.pow_eq_one.mp (by simpa only [Nat.ModEq, Nat.mod_zero] using hg)).resolve_right hu.ne'
    simp [powMod, hg1]
  · have hinv : BinaryGcd.modInv v u * v ≡ 1 [MOD u] := by
      rw [mul_comm]
      exact BinaryGcd.mul_modInv_modEq_one hu hv
    have hgu : (g : ZMod N) ^ u = 1 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hg
    rw [knownOrderRoot, powMod_of_ne_zero hN.ne', powMod_of_ne_zero hN.ne', ← Nat.pow_mod,
      ← pow_mul, ← ZMod.natCast_eq_natCast_iff']
    exact_mod_cast (pow_eq_pow_of_modEq hinv hgu).trans (pow_one _)

/-- The adversary of [BonehShoup2023], §10.9, p. 421, for exponents `u` and `v` computed from the
security parameter and the public parameters: on `(n, (N, g))` it outputs
`(knownOrderRoot N u v g, v)` for `u = u n (N, g)` and `v = v n (N, g)`. The book does not name it;
`knownOrderAdversary` is this library's name. -/
def knownOrderAdversary (u v : ℕ → GUOParams → ℕ) : StrongRSAAdversary := fun n p =>
  pure (knownOrderRoot p.modulus (u n p) (v n p) p.base, v n p)

/-- The known-order adversary is PPT when its exponents `u` and `v` are computable in polynomial
time from the unary security parameter and `encGUOParams`. -/
theorem isPPT_knownOrderAdversary {u v : ℕ → GUOParams → ℕ}
    (hu : ComputableInPolyTime (fun p : ℕ × GUOParams => u p.1 p.2)
      (encPair encUnary encGUOParams) encNat)
    (hv : ComputableInPolyTime (fun p : ℕ × GUOParams => v p.1 p.2)
      (encPair encUnary encGUOParams) encNat) :
    (knownOrderAdversary u v).IsPPT := by
  have hroot : ComputableInPolyTime
      (fun p : ℕ × GUOParams => knownOrderRoot p.2.modulus (u p.1 p.2) (v p.1 p.2) p.2.base)
      (encPair encUnary encGUOParams) encNat :=
    computableInPolyTime_powMod (by fun_prop) (by fun_prop)
      (ComputableInPolyTime.binary_modInv' hv hu)
  exact (hroot.prod hv).isPPTOn

/-- The known-order adversary wins `strongRSAGame` with probability `1` at a security parameter
`n` where, for every `(N, g)` in the support of `setup n`, `g ^ u ≡ 1 [MOD N]`, `v` is coprime to
`u` and `v ≠ 1` ([BonehShoup2023], §10.9, p. 421). -/
theorem strongRSAGame_knownOrderAdversary (setup : ℕ → PMF GUOParams) (u v : ℕ → GUOParams → ℕ)
    (n : ℕ) (h : ∀ p ∈ (setup n).support, p.base ^ u n p ≡ 1 [MOD p.modulus] ∧
      Nat.Coprime (v n p) (u n p) ∧ v n p ≠ 1) :
    strongRSAGame setup (knownOrderAdversary u v) n = PMF.pure true := by
  refine PMF.bind_eq_pure_of_forall_mem_support fun p hp => ?_
  obtain ⟨hg, hv, hv1⟩ := h p hp
  -- `v` is coprime to `0` only when `v = 1`.
  have hu : 0 < u n p := Nat.pos_of_ne_zero fun h0 => hv1 (Nat.coprime_zero_right _ |>.mp (h0 ▸ hv))
  simp [knownOrderAdversary, isStrongRSASolution, powMod_knownOrderRoot hu hg hv,
    bne_iff_ne.mpr hv1]

/-- The known-order adversary wins with probability `1`, so `StrongRSA setup` does not hold, when
polynomial-time functions `u` and `v` of the security parameter and `(N, g)` give, for every
`(N, g)` in the support of every `setup n`, `g ^ u ≡ 1 [MOD N]` and an exponent `v ≠ 1` coprime to
`u`. This is the general form of the observation of [BonehShoup2023], §10.9, p. 421, with the
exponent `v` chosen by the caller; `not_strongRSA_of_orderMultiple` is the book's form, with
hypotheses on `u` alone. -/
theorem not_strongRSA_of_knownOrder {setup : ℕ → PMF GUOParams} {u v : ℕ → GUOParams → ℕ}
    (hu : ComputableInPolyTime (fun p : ℕ × GUOParams => u p.1 p.2)
      (encPair encUnary encGUOParams) encNat)
    (hv : ComputableInPolyTime (fun p : ℕ × GUOParams => v p.1 p.2)
      (encPair encUnary encGUOParams) encNat)
    (h : ∀ n, ∀ p ∈ (setup n).support, p.base ^ u n p ≡ 1 [MOD p.modulus] ∧
      Nat.Coprime (v n p) (u n p) ∧ v n p ≠ 1) :
    ¬ StrongRSA setup := by
  intro hS
  have hneg := hS _ (isPPT_knownOrderAdversary hu hv)
  simp only [strongRSAGame_knownOrderAdversary setup u v _ (h _)] at hneg
  exact not_negligible_const (by simp [Game.succProbability]) hneg

/-- The adversary of [BonehShoup2023], §10.9, p. 421, for a multiple `u` of the order of `g`
computed from the security parameter and the public parameters: it takes `v = u + 1`, which is
greater than `1` and coprime to `u`, and outputs `(knownOrderRoot N u (u + 1) g, u + 1)`. The book
does not name it; `orderMultipleAdversary` is this library's name. -/
def orderMultipleAdversary (u : ℕ → GUOParams → ℕ) : StrongRSAAdversary :=
  knownOrderAdversary u fun n p => u n p + 1

/-- The order-multiple adversary is PPT when `u` is computable in polynomial time from the unary
security parameter and `encGUOParams`. -/
theorem isPPT_orderMultipleAdversary {u : ℕ → GUOParams → ℕ}
    (hu : ComputableInPolyTime (fun p : ℕ × GUOParams => u p.1 p.2)
      (encPair encUnary encGUOParams) encNat) :
    (orderMultipleAdversary u).IsPPT :=
  isPPT_knownOrderAdversary hu (by fun_prop)

/-- The order-multiple adversary wins `strongRSAGame` with probability `1` at a security parameter
`n` where, for every `(N, g)` in the support of `setup n`, `0 < u` and `g ^ u ≡ 1 [MOD N]`
([BonehShoup2023], §10.9, p. 421). -/
theorem strongRSAGame_orderMultipleAdversary (setup : ℕ → PMF GUOParams) (u : ℕ → GUOParams → ℕ)
    (n : ℕ) (h : ∀ p ∈ (setup n).support, 0 < u n p ∧ p.base ^ u n p ≡ 1 [MOD p.modulus]) :
    strongRSAGame setup (orderMultipleAdversary u) n = PMF.pure true :=
  strongRSAGame_knownOrderAdversary setup u _ n fun p hp =>
    ⟨(h p hp).2, by simp, by have := (h p hp).1; omega⟩

/-- **The strong RSA assumption does not hold when a multiple of the order is known**
([BonehShoup2023], §10.9, p. 421). If a polynomial-time function `u` of the security parameter and
`(N, g)` gives, for every `(N, g)` in the support of every `setup n`, a positive multiple of the
order of `g` modulo `N` (`0 < u` and `g ^ u ≡ 1 [MOD N]`), then `orderMultipleAdversary u` is PPT
(`isPPT_orderMultipleAdversary`) and wins with probability `1`
(`strongRSAGame_orderMultipleAdversary`), so `StrongRSA setup` is false. -/
theorem not_strongRSA_of_orderMultiple {setup : ℕ → PMF GUOParams} {u : ℕ → GUOParams → ℕ}
    (hu : ComputableInPolyTime (fun p : ℕ × GUOParams => u p.1 p.2)
      (encPair encUnary encGUOParams) encNat)
    (h : ∀ n, ∀ p ∈ (setup n).support, 0 < u n p ∧ p.base ^ u n p ≡ 1 [MOD p.modulus]) :
    ¬ StrongRSA setup := by
  intro hS
  have hneg := hS _ (isPPT_orderMultipleAdversary hu)
  simp only [strongRSAGame_orderMultipleAdversary setup u _ (h _)] at hneg
  exact not_negligible_const (by simp [Game.succProbability]) hneg

end Cslib.Crypto
