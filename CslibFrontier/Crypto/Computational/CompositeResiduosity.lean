/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.CompositeResiduosity.Finite
public import CslibFrontier.Crypto.Computational.Factoring
public import CslibFrontier.Crypto.Computational.Paillier.Algebra
public import CslibFrontier.Crypto.Game
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT

/-!
# The decisional composite residuosity assumption

A balanced modulus is a product `N = p * q` of distinct odd primes of the same bit length. An
element of `(ZMod (N ^ 2))ˣ` is an `N`-th residue when it equals `r ^ N` for some unit `r`. The
decisional composite residuosity (DCR) problem asks to distinguish a uniform `N`-th residue modulo
`N ^ 2` from a uniform unit modulo `N ^ 2`, given only `N`. The DCR assumption relative to a law
on moduli says that every uniform strict PPT distinguisher has negligible advantage.

A description of a balanced modulus is its pair of prime factors `(p, q)`, with validity part of
the type, as for Schnorr groups. Nothing here claims that valid descriptions can be generated
efficiently; the assumption is stated relative to an arbitrary law on descriptions. The two
worlds at one fixed modulus are `dcrRealExperiment` and `dcrRandomExperiment` in
`CslibFrontier/Crypto/Computational/CompositeResiduosity/Finite.lean`; the games here draw a
modulus and run them.

## Main definitions

* `Cslib.Crypto.BalancedModulus.Valid`, `Cslib.Crypto.BalancedModulus.Desc`: valid factor pairs
  `(p, q)` of balanced moduli.
* `Cslib.Crypto.dcrRealGame`, `Cslib.Crypto.dcrRandomGame`: the two DCR games, which draw a
  modulus and run the fixed-modulus experiments.
* `Cslib.Crypto.DCR`: the decisional composite residuosity assumption.
* `Cslib.Crypto.dcrTotientTest`, `Cslib.Crypto.factorToDCR`: explicit PPT reduction from
  decisional composite residuosity distinguishing to integer factoring via `φ(N)`-exponentiation.

## Main results

* `Cslib.Crypto.BalancedModulus.Desc.coprime_totient`: `gcd(N, φ(N)) = 1` for every valid
  description ([KatzLindell2020], Claim 15.7).
* `Cslib.Crypto.BalancedModulus.Desc.totient_eq`: the computed totient `(p - 1) * (q - 1)` is
  `φ(N)`.
* `Cslib.Crypto.succProbability_modulusFactoringGame_le_two_mul_advantage_dcrGame`,
  `Cslib.Crypto.DCR.modulusFactoringHard`: decisional composite residuosity hardness implies
  integer factoring hardness.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Section 15.3.1, Claim 15.7, and Definition 15.10.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace BalancedModulus

/-- A valid pair `(p, q)` of prime factors of a balanced modulus `N = p * q`: distinct odd primes
of the same bit length. -/
structure Valid (d : ℕ × ℕ) : Prop where
  /-- The first factor is prime. -/
  prime_fst : d.1.Prime
  /-- The second factor is prime. -/
  prime_snd : d.2.Prime
  /-- The factors are distinct. -/
  fst_ne_snd : d.1 ≠ d.2
  /-- The first factor is odd. -/
  two_lt_fst : 2 < d.1
  /-- The second factor is odd. -/
  two_lt_snd : 2 < d.2
  /-- The factors have the same bit length. -/
  size_eq : d.1.size = d.2.size

/-- Valid factor pairs `(p, q)` of balanced moduli. -/
abbrev Desc : Type := {d : ℕ × ℕ // Valid d}

/-- The first prime factor `p` of a valid description `(p, q)`. -/
abbrev Desc.p (d : Desc) : ℕ := d.val.1

/-- The second prime factor `q` of a valid description `(p, q)`. -/
abbrev Desc.q (d : Desc) : ℕ := d.val.2

/-- The modulus `N = p * q` of a valid description `(p, q)`. -/
abbrev Desc.modulus (d : Desc) : ℕ := d.p * d.q

/-- The totient `φ(N) = (p - 1) * (q - 1)`, computed from the factors. -/
abbrev Desc.totient (d : Desc) : ℕ := (d.p - 1) * (d.q - 1)

/-- The modulus is greater than `1`. -/
theorem Desc.one_lt_modulus (d : Desc) : 1 < d.modulus := by
  have hp := d.2.two_lt_fst
  have hq := d.2.two_lt_snd
  change 1 < d.val.1 * d.val.2
  nlinarith

instance (d : Desc) : NeZero d.modulus := ⟨by have := d.one_lt_modulus; lia⟩

instance (d : Desc) : NeZero (d.modulus ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne _)⟩

/-- The computed totient `(p - 1) * (q - 1)` is Euler's totient of `N = p * q`. -/
theorem Desc.totient_eq (d : Desc) : d.totient = d.modulus.totient := by
  rw [Desc.totient, Desc.modulus,
    Nat.totient_mul ((Nat.coprime_primes d.2.prime_fst d.2.prime_snd).mpr d.2.fst_ne_snd),
    Nat.totient_prime d.2.prime_fst, Nat.totient_prime d.2.prime_snd]

/-- **Claim 15.7** ([KatzLindell2020]) for a valid description: `gcd(N, φ(N)) = 1`. -/
theorem Desc.coprime_totient (d : Desc) : d.modulus.Coprime d.modulus.totient :=
  Paillier.coprime_totient d.2.prime_fst d.2.prime_snd d.2.fst_ne_snd d.2.two_lt_fst
    d.2.two_lt_snd d.2.size_eq

/-- Descriptions are encoded as the binary pair `(p, q)`. -/
def encDesc : Desc ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encPair encNat encNat)

end BalancedModulus

open BalancedModulus

/-- The real game of the decisional composite residuosity problem ([KatzLindell2020],
Definition 15.10): draw `(p, q) ← setup n` and run `dcrRealExperiment` at `N = p * q`, giving the
distinguisher `N` and the least representative of the uniform `N`-th residue modulo `N ^ 2`. -/
noncomputable def dcrRealGame (setup : ℕ → PMF Desc)
    (distinguisher : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => dcrRealExperiment d.modulus fun y =>
    distinguisher n (d.modulus, (y : ZMod (d.modulus ^ 2)).val)

/-- The random game of the decisional composite residuosity problem ([KatzLindell2020],
Definition 15.10): draw `(p, q) ← setup n` and run `dcrRandomExperiment` at `N = p * q`, giving
the distinguisher `N` and the least representative of a uniform unit modulo `N ^ 2`. -/
noncomputable def dcrRandomGame (setup : ℕ → PMF Desc)
    (distinguisher : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => dcrRandomExperiment d.modulus fun y =>
    distinguisher n (d.modulus, (y : ZMod (d.modulus ^ 2)).val)

/-- The **decisional composite residuosity assumption** relative to a law `setup` on balanced
moduli ([KatzLindell2020], Definition 15.10): every uniform strict PPT distinguisher, given `N`,
has negligible advantage in telling a uniform `N`-th residue modulo `N ^ 2` from a uniform unit
modulo `N ^ 2`. -/
def DCR (setup : ℕ → PMF Desc) : Prop :=
  Game.Indistinguishable (dcrRealGame setup) (dcrRandomGame setup) fun distinguisher =>
    IsPPTOn encModulusChallengeInput encBool
      (fun input => distinguisher input.1 input.2)

/-! ### Decisional composite residuosity hardness implies integer factoring hardness -/

/-- Totient-exponentiation test for composite residuosity modulo `N ^ 2` from candidate factors
`(a, b)` of `N`: returns `true` when `1 < a`, `1 < b`, `a * b = N`, and
`y ^ ((a - 1) * (b - 1)) % (N ^ 2) = 1`. -/
def dcrTotientTest (N y a b : ℕ) : Bool :=
  decide (1 < a ∧ 1 < b ∧ a * b = N ∧
    y ^ ((a - 1) * (b - 1)) % (if N = 0 then 1 else N ^ 2) = 1)

/-- Explicit PPT reduction from decisional composite residuosity distinguishing to integer
factoring ([KatzLindell2020], Section 15.3.1): given `(N, y)`, run the factoring algorithm `F n N`
to obtain `(a, b)` and test whether `y ^ ((a - 1) * (b - 1)) ≡ 1 [MOD N ^ 2]`. -/
def factorToDCR (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) (Ny : ℕ × ℕ) : ProbComp Bool := do
  let ab ← F n Ny.1
  return dcrTotientTest Ny.1 Ny.2 ab.1 ab.2

private theorem computableInPolyTime_dcrTotientTest {α : Type} {enc : α ↪ List Bool}
    {N y a b : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat)
    (hy : ComputableInPolyTime y enc encNat)
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun x => dcrTotientTest (N x) (y x) (a x) (b x)) enc encBool := by
  unfold dcrTotientTest
  have hN_pos : ∀ x, 0 < (if N x = 0 then 1 else N x ^ 2) := fun x => by
    split_ifs with h0
    · omega
    · exact pow_pos (Nat.pos_of_ne_zero h0) 2
  have hN2 : ComputableInPolyTime (fun x => if N x = 0 then 1 else N x ^ 2) enc encNat := by
    simp only [sq]
    fun_prop
  have hpow : ComputableInPolyTime
      (fun x => y x ^ ((a x - 1) * (b x - 1)) % (if N x = 0 then 1 else N x ^ 2)) enc encNat :=
    ComputableInPolyTime.binary_powMod hy (by fun_prop) hN2 hN_pos
  have hcheck : ∀ {r : α → ℕ}, ComputableInPolyTime r enc encNat →
      ComputableInPolyTime
        (fun x => decide (1 < a x ∧ 1 < b x ∧ a x * b x = N x ∧ r x = 1)) enc encBool := by
    intro r hr
    fun_prop
  exact hcheck hpow

/-- `factorToDCR F` is uniform PPT whenever `F` is uniform PPT. -/
theorem isPPTOn_factorToDCR {F : ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hF : IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => F input.1 input.2)) :
    IsPPTOn encModulusChallengeInput encBool
      (fun input => factorToDCR F input.1 input.2) := by
  unfold factorToDCR
  have htest := @computableInPolyTime_dcrTotientTest
  refine IsPPTOn.bind_with
    (IsPPTOn.preprocess hF (prepare := fun input : ℕ × (ℕ × ℕ) => (input.1, input.2.1))
      (by fun_prop)) ?_
  ppt

private theorem val_pow_mod_sq_eq_one_iff (d : Desc) (u : (ZMod (d.modulus ^ 2))ˣ)
    (t : ℕ) :
    (u : ZMod (d.modulus ^ 2)).val ^ t % (d.modulus ^ 2) = 1 ↔ u ^ t = 1 := by
  have h1 : 1 < d.modulus ^ 2 := by
    have := d.one_lt_modulus
    nlinarith
  have : Fact (1 < d.modulus ^ 2) := ⟨h1⟩
  have hmod : (u : ZMod (d.modulus ^ 2)).val ^ t % (d.modulus ^ 2) = 1 ↔
      (((u : ZMod (d.modulus ^ 2)).val : ZMod (d.modulus ^ 2)) ^ t = 1) := by
    rw [← Nat.cast_pow, ← ZMod.natCast_mod]
    constructor
    · intro h
      rw [h, Nat.cast_one]
    · intro h
      have hval := congrArg ZMod.val h
      rwa [ZMod.val_natCast, Nat.mod_mod, ZMod.val_one] at hval
  rw [hmod, ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, ← Units.val_one, Units.ext_iff]

private theorem powSelfHom_pow_totient (N : ℕ) [NeZero N] (b : (ZMod N)ˣ) :
    (Paillier.powSelfHom N b) ^ N.totient = 1 := by
  rw [← map_pow, ← ZMod.card_units_eq_totient, pow_card_eq_one, map_one]

private theorem pow_modulus_pow_totient (N : ℕ) [NeZero N] (s : (ZMod (N ^ 2))ˣ) :
    (s ^ N) ^ N.totient = 1 := by
  rw [← Paillier.powSelfHom_unitsMap N s]
  exact powSelfHom_pow_totient N _

private theorem dcrTotientTest_eq_decide (d : Desc) (u : (ZMod (d.modulus ^ 2))ˣ)
    (a b : ℕ) :
    dcrTotientTest d.modulus (u : ZMod (d.modulus ^ 2)).val a b =
      decide (1 < a ∧ 1 < b ∧ a * b = d.modulus ∧ u ^ d.modulus.totient = 1) := by
  have hN0 : d.modulus ≠ 0 := NeZero.ne d.modulus
  unfold dcrTotientTest
  simp only [hN0, ↓reduceIte]
  by_cases hfac : 1 < a ∧ 1 < b ∧ a * b = d.modulus
  · rcases hfac with ⟨ha, hb, hab⟩
    have htot : (a - 1) * (b - 1) = d.modulus.totient := by
      rw [← d.totient_eq]
      rcases mul_eq_mul_primes_cases d.2.prime_fst d.2.prime_snd ha hb hab with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact mul_comm _ _
    simp [ha, hb, hab, htot, val_pow_mod_sq_eq_one_iff]
  · have hf1 : decide (1 < a ∧ 1 < b ∧ a * b = d.modulus ∧
        (u : ZMod (d.modulus ^ 2)).val ^ ((a - 1) * (b - 1)) % (d.modulus ^ 2) = 1) = false :=
      decide_eq_false fun h => hfac ⟨h.1, h.2.1, h.2.2.1⟩
    have hf2 : decide (1 < a ∧ 1 < b ∧ a * b = d.modulus ∧ u ^ d.modulus.totient = 1) = false :=
      decide_eq_false fun h => hfac ⟨h.1, h.2.1, h.2.2.1⟩
    rw [hf1, hf2]

/-- In `dcrRealGame`, `factorToDCR F` succeeds with the exact distribution of `modulusFactoringGame`
on the pushed-forward modulus distribution. -/
theorem dcrRealGame_factorToDCR (setup : ℕ → PMF Desc)
    (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    dcrRealGame setup (factorToDCR F) n =
      modulusFactoringGame (fun k => (setup k).map Desc.modulus) F n := by
  unfold dcrRealGame Game.withSetup dcrRealExperiment modulusFactoringGame factorToDCR
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def]
  congr 1
  funext d
  have hconst : (fun s : (ZMod (d.modulus ^ 2))ˣ =>
      (ProbComp.eval (F n d.modulus)).bind fun ab =>
        PMF.pure (dcrTotientTest d.modulus ((s ^ d.modulus : (ZMod (d.modulus ^ 2))ˣ) :
          ZMod (d.modulus ^ 2)).val ab.1 ab.2)) =
      fun _ => (ProbComp.eval (F n d.modulus)).bind fun ab =>
        PMF.pure (decide (1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = d.modulus)) := by
    funext s
    congr 1
    funext ab
    rw [dcrTotientTest_eq_decide, pow_modulus_pow_totient]
    simp
  rw [hconst, PMF.bind_const]

private theorem unitsEquiv_pow_totient_eq_one_iff (d : Desc)
    (p : Multiplicative (ZMod d.modulus) × (ZMod d.modulus)ˣ) :
    (Paillier.unitsEquiv d.modulus d.coprime_totient p) ^ d.modulus.totient = 1 ↔ p.1 = 1 := by
  have heq : Paillier.unitsEquiv d.modulus d.coprime_totient p =
      Paillier.oneAddPowHom d.modulus p.1 * Paillier.powSelfHom d.modulus p.2 := rfl
  rw [heq, mul_pow (Paillier.oneAddPowHom d.modulus p.1) (Paillier.powSelfHom d.modulus p.2),
    powSelfHom_pow_totient, mul_one]
  constructor
  · intro hpow
    have hdvdT : orderOf (Paillier.oneAddPowHom d.modulus p.1) ∣ d.modulus.totient :=
      orderOf_dvd_of_pow_eq_one hpow
    have hdvdN : orderOf (Paillier.oneAddPowHom d.modulus p.1) ∣ d.modulus := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [Paillier.oneAddPowHom_apply, ← pow_mul, mul_comm, pow_mul]
      unfold Paillier.oneAddUnit
      rw [Units.pow_ofPowEqOne, one_pow]
    have hord1 : orderOf (Paillier.oneAddPowHom d.modulus p.1) = 1 :=
      Nat.eq_one_of_dvd_coprimes d.coprime_totient hdvdN hdvdT
    have h1 : Paillier.oneAddPowHom d.modulus p.1 = 1 := orderOf_eq_one_iff.mp hord1
    have hinj : Paillier.unitsEquiv d.modulus d.coprime_totient (p.1, 1) =
        Paillier.unitsEquiv d.modulus d.coprime_totient (1, 1) := by
      change Paillier.oneAddPowHom d.modulus p.1 * Paillier.powSelfHom d.modulus 1 = _
      rw [h1, map_one, mul_one]
      exact (map_one (Paillier.unitsEquiv d.modulus d.coprime_totient)).symm
    exact congrArg Prod.fst ((Paillier.unitsEquiv d.modulus d.coprime_totient).injective hinj)
  · rintro h1
    rw [h1, map_one, one_pow]

private theorem two_mul_card_filter_pow_totient_eq_one_le (d : Desc) :
    2 * (Finset.univ.filter (fun y : (ZMod (d.modulus ^ 2))ˣ =>
      y ^ d.modulus.totient = 1)).card ≤ Fintype.card (ZMod (d.modulus ^ 2))ˣ := by
  have hcard : (Finset.univ.filter (fun y : (ZMod (d.modulus ^ 2))ˣ =>
      y ^ d.modulus.totient = 1)).card = Fintype.card (ZMod d.modulus)ˣ := by
    rw [← Finset.card_univ]
    refine (Finset.card_bij (fun b _ => Paillier.unitsEquiv d.modulus d.coprime_totient (1, b))
      (fun b _ => ?_) (fun b₁ _ b₂ _ h => ?_) (fun y hy => ?_)).symm
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (unitsEquiv_pow_totient_eq_one_iff d (1, b)).mpr rfl⟩
    · exact congrArg Prod.snd ((Paillier.unitsEquiv d.modulus d.coprime_totient).injective h)
    · rw [Finset.mem_filter] at hy
      set p := (Paillier.unitsEquiv d.modulus d.coprime_totient).symm y
      have hp : Paillier.unitsEquiv d.modulus d.coprime_totient p = y :=
        (Paillier.unitsEquiv d.modulus d.coprime_totient).apply_symm_apply y
      have hp1 : p.1 = 1 :=
        (unitsEquiv_pow_totient_eq_one_iff d p).mp (hp.symm ▸ hy.2)
      refine ⟨p.2, Finset.mem_univ _, ?_⟩
      calc Paillier.unitsEquiv d.modulus d.coprime_totient (1, p.2)
          = Paillier.unitsEquiv d.modulus d.coprime_totient (p.1, p.2) := by rw [hp1]
        _ = y := hp
  have hcard_sq : Fintype.card (ZMod (d.modulus ^ 2))ˣ =
      d.modulus * Fintype.card (ZMod d.modulus)ˣ := by
    rw [← Fintype.card_congr (Paillier.unitsEquiv d.modulus d.coprime_totient).toEquiv,
      Fintype.card_prod, Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  rw [hcard, hcard_sq]
  exact Nat.mul_le_mul_right _ d.one_lt_modulus

/-- Twice the success probability of `factorToDCR F` in `dcrRandomGame` is at most the factoring
success probability of `F`. -/
theorem two_mul_succProbability_dcrRandomGame_factorToDCR_le (setup : ℕ → PMF Desc)
    (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    2 * Game.succProbability (dcrRandomGame setup (factorToDCR F) n) ≤
      Game.succProbability
        (modulusFactoringGame (fun k => (setup k).map Desc.modulus) F n) := by
  rw [Game.succProbability, Game.succProbability, ← ENNReal.toNNReal_ofNat 2,
    ← ENNReal.toNNReal_mul]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  unfold dcrRandomGame Game.withSetup dcrRandomExperiment modulusFactoringGame factorToDCR
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def,
    PMF.bind_apply, PMF.pure_apply, eq_comm (a := true)]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun d => ?_
  rw [mul_left_comm (2 : ℝ≥0∞)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Swap the uniform unit draw `y` and the factoring call `ab ← F n d.modulus`.
  have hswap : (2 : ℝ≥0∞) * (∑' a : (ZMod (d.modulus ^ 2))ˣ,
      (PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ) a *
        ∑' ab : ℕ × ℕ, (ProbComp.eval (F n d.modulus)) ab *
          if dcrTotientTest d.modulus (a : ZMod (d.modulus ^ 2)).val ab.1 ab.2 = true
            then 1 else 0) =
      ∑' ab : ℕ × ℕ, (ProbComp.eval (F n d.modulus)) ab *
        ((2 : ℝ≥0∞) * ∑' a : (ZMod (d.modulus ^ 2))ˣ,
          (PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ) a *
            if dcrTotientTest d.modulus (a : ZMod (d.modulus ^ 2)).val ab.1 ab.2 = true
              then 1 else 0) := by
    simp_rw [← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    refine tsum_congr fun ab => tsum_congr fun a => by ring
  rw [hswap]
  refine tsum_le_tsum fun ab => mul_le_mul_of_nonneg_left ?_ zero_le
  by_cases hfac : 1 < ab.1 ∧ 1 < ab.2 ∧ ab.1 * ab.2 = d.modulus
  · simp only [dcrTotientTest_eq_decide, hfac.1, hfac.2.1, hfac.2.2, true_and, decide_eq_true_eq,
      and_self, ↓reduceIte]
    rw [tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    rw [← mul_assoc]
    have hcard_le : ((2 : ℝ≥0∞) * ((Finset.univ.filter (fun y : (ZMod (d.modulus ^ 2))ˣ =>
        y ^ d.modulus.totient = 1)).card : ℝ≥0∞)) ≤
        (Fintype.card (ZMod (d.modulus ^ 2))ˣ : ℝ≥0∞) := by
      exact_mod_cast two_mul_card_filter_pow_totient_eq_one_le d
    calc (2 : ℝ≥0∞) * ((Finset.univ.filter (fun y : (ZMod (d.modulus ^ 2))ˣ =>
          y ^ d.modulus.totient = 1)).card : ℝ≥0∞) *
          ((Fintype.card (ZMod (d.modulus ^ 2))ˣ : ℝ≥0∞))⁻¹
        ≤ (Fintype.card (ZMod (d.modulus ^ 2))ˣ : ℝ≥0∞) *
          ((Fintype.card (ZMod (d.modulus ^ 2))ˣ : ℝ≥0∞))⁻¹ := by gcongr
      _ ≤ 1 := ENNReal.mul_inv_le_one _
  · have hf : ∀ a : (ZMod (d.modulus ^ 2))ˣ,
        dcrTotientTest d.modulus (a : ZMod (d.modulus ^ 2)).val ab.1 ab.2 = false := fun a => by
      rw [dcrTotientTest_eq_decide]
      exact decide_eq_false fun h => hfac ⟨h.1, h.2.1, h.2.2.1⟩
    simp [hf]

/-- The factoring success probability of `F` is at most twice the DCR distinguishing advantage of
`factorToDCR F`. -/
theorem succProbability_modulusFactoringGame_le_two_mul_advantage_dcrGame
    (setup : ℕ → PMF Desc) (F : ℕ → ℕ → ProbComp (ℕ × ℕ)) (n : ℕ) :
    Game.succProbability
        (modulusFactoringGame (fun k => (setup k).map Desc.modulus) F n) ≤
      2 * Game.advantage (dcrRealGame setup (factorToDCR F) n)
        (dcrRandomGame setup (factorToDCR F) n) := by
  have hreal : Game.succProbability (dcrRealGame setup (factorToDCR F) n) =
      Game.succProbability
        (modulusFactoringGame (fun k => (setup k).map Desc.modulus) F n) := by
    rw [dcrRealGame_factorToDCR]
  have hrand := two_mul_succProbability_dcrRandomGame_factorToDCR_le setup F n
  unfold Game.advantage
  rw [hreal]
  set p := Game.succProbability
    (modulusFactoringGame (fun k => (setup k).map Desc.modulus) F n)
  set q := Game.succProbability (dcrRandomGame setup (factorToDCR F) n)
  have hle : q ≤ p := by
    have : 1 * q ≤ 2 * q := mul_le_mul_of_nonneg_right (by norm_num) zero_le
    exact (one_mul q ▸ this).trans hrand
  rw [NNReal.nndist_eq]
  have hsub : p ≤ 2 * (p - q) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_sub hle]
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_ofNat] at hrand
    linarith
  exact hsub.trans (mul_le_mul_of_nonneg_left (le_max_left (p - q) (q - p)) zero_le)

/-- **Decisional composite residuosity hardness implies integer factoring hardness**: if `setup`
satisfies `DCR`, then factoring `N = d.modulus` is hard for
`(setup n).map BalancedModulus.Desc.modulus`. -/
theorem DCR.modulusFactoringHard {setup : ℕ → PMF Desc} (h : DCR setup) :
    ModulusFactoringHard (fun n => (setup n).map Desc.modulus) := by
  intro F hF
  exact negligible_of_le ((h (factorToDCR F) (isPPTOn_factorToDCR hF)).const_mul 2)
    (succProbability_modulusFactoringGame_le_two_mul_advantage_dcrGame setup F)

end Cslib.Crypto
