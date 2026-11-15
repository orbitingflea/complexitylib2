/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Crypto.Computational.RSATrapdoor
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# RSA with a uniform unit preimage

[BonehShoup2023], §10.6.2, p. 416, modifies the RSA attack game (Attack Game 10.3) so that the
challenger draws the preimage `x` uniformly from the units `ℤₙ*` and keeps everything else the
same; `uRSAadv[A, ℓ, e]` is the adversary's advantage there. Theorem 10.5 says that an elementary
wrapper `B` around `A` has `uRSAadv[A, ℓ, e] ≤ RSAadv[B, ℓ, e]`, so the RSA assumption implies
this variant. The wrapper hands a unit challenge to `A` and computes an `e`-th root of any other
challenge itself: `0` for `0`, and otherwise `y ^ d` after factoring `n` with `gcd(y, n)`.

## Main definitions

* `Cslib.Crypto.RSADesc.unitResidue`: a unit modulo `N` as a residue in `Fin N`.
* `Cslib.Crypto.rsaUnitInversionGame`, `Cslib.Crypto.RSAUnitOneWay`: the inversion experiment with
  a uniform unit preimage and its assumption.
* `Cslib.Crypto.rsaNonUnitRoot`: the `e`-th root of a challenge that is not a unit, computed from
  `N` and `e`.
* `Cslib.Crypto.unitRSAToRSA`: the wrapper `B` of Theorem 10.5.

## Main results

* `Cslib.Crypto.coprime_rsaEval_iff`: RSA evaluation maps units to units and non-units to
  non-units.
* `Cslib.Crypto.rsaNonUnitRoot_rsaEval`: `rsaNonUnitRoot` inverts RSA evaluation on every residue
  that is not a unit.
* `Cslib.Crypto.computableInPolyTime_rsaNonUnitRoot`, `Cslib.Crypto.isPPT_unitRSAToRSA`: the
  root and the wrapper are computable in polynomial time.
* `Cslib.Crypto.succProbability_rsaUnitInversionGame_le`: Theorem 10.5, at every security
  parameter and for every key generator.
* `Cslib.Crypto.RSAOneWay.rsaUnitOneWay`: `RSAOneWay gen` implies `RSAUnitOneWay gen`.

## Implementation notes

The book states Theorem 10.5 for `ℓ > 2` and odd `e > 2`, the parameters of its key generator
`RSAGen(ℓ, e)`. Here keys come from any law on `RSADesc`, and the theorem has no hypothesis on it:
the proof uses only that `N = p * q` for distinct primes `p` and `q` and that `e * d ≡ 1` modulo
`(p - 1) * (q - 1)`, so `p = 2` and `e = 1` are allowed. The challenge `x ^ e % N` is given to
the inverter as a residue in `Fin N`, as in `rsaInversionGame`, and the inverter wins when it
returns `x`; the two games differ only in the law of `x`. The bound compares success
probabilities at each security parameter. Exercise 10.26 (p. 431), the converse with a loss of
`2 ^ -(ℓ - 2)`, is not formalized.

The wrapper finds the exponent as the book's proof describes. For a challenge `y ≠ 0` that is not
a unit, `g = gcd(y, N)` is `p` or `q`, so `(g - 1) * (N / g - 1)` is `(p - 1) * (q - 1)` and its
modular inverse `d'` of `e` is a decryption exponent (`rsaNonUnitRoot_rsaEval`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], §10.6.2,
  Theorem 10.5, p. 416.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- A unit modulo `N` as a residue in `Fin N`: its value in `[0, N)`. -/
@[expose] def RSADesc.unitResidue (desc : RSADesc) (x : (ZMod desc.modulus)ˣ) : Fin desc.modulus :=
  ⟨(x : ZMod desc.modulus).val, ZMod.val_lt _⟩

theorem RSADesc.unitResidue_injective (desc : RSADesc) : Function.Injective desc.unitResidue :=
  fun _ _ h => Units.ext (ZMod.val_injective _ (Fin.ext_iff.mp h))

/-- The residues of units are exactly the residues coprime to `N`. -/
theorem RSADesc.mem_range_unitResidue_iff (desc : RSADesc) (x : Fin desc.modulus) :
    x ∈ Set.range desc.unitResidue ↔ Nat.Coprime x desc.modulus := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ZMod.val_coe_unit_coprime u
  · intro hx
    refine ⟨ZMod.unitOfCoprime x hx, Fin.ext ?_⟩
    simp [unitResidue, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]

/-- The RSA inversion experiment with a uniform unit preimage ([BonehShoup2023], §10.6.2,
p. 416): sample `desc ← gen n`, draw `x` uniformly from `(ZMod N)ˣ`, and run
`Cslib.Crypto.inversionExperiment` on its residue. The inverter receives `(pk, x ^ e % N)` and
wins when it returns a preimage. -/
noncomputable def rsaUnitInversionGame (gen : RSAGen) (inverter : RSAInverter) (n : ℕ) : Game := do
  let desc ← gen n
  ProbComp.eval (inversionExperiment (desc.unitResidue <$> ProbComp.uniform (ZMod desc.modulus)ˣ)
    desc.publicKey.eval (inverter n desc.publicKey))

/-- RSA evaluation is a bijection on `Fin N`, so an inverter wins `rsaUnitInversionGame` exactly
when it recovers the residue of the challenge unit. -/
theorem rsaUnitInversionGame_eq (gen : RSAGen) (inverter : RSAInverter) (n : ℕ) :
    rsaUnitInversionGame gen inverter n = (do
      let desc ← gen n
      let x ← PMF.uniformOfFintype (ZMod desc.modulus)ˣ
      let x' ← ProbComp.eval (inverter n desc.publicKey (desc.publicKey.eval (desc.unitResidue x)))
      return decide (x' = desc.unitResidue x)) := by
  unfold rsaUnitInversionGame
  congr 1
  funext desc
  rw [inversionExperiment_eq_of_injective _ (rsaEval_bijective_fin desc).injective]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.bind_map, Function.comp_def]
  rfl

/-- The RSA assumption with a uniform unit preimage for `gen` ([BonehShoup2023], §10.6.2, p. 416,
the variant of Attack Game 10.3 that draws `x` from `ℤₙ*`, read with Definition 10.5, p. 405):
every PPT inverter recovers a uniform unit from its RSA image with negligible probability. Keys
come from any law on `RSADesc` (`RSAGen`), which need not be efficiently samplable, in place of
Boneh–Shoup's `RSAGen(ℓ, e)`. It follows from `RSAOneWay` (`RSAOneWay.rsaUnitOneWay`, Theorem
10.5). -/
@[expose] def RSAUnitOneWay (gen : RSAGen) : Prop :=
  ∀ inverter : RSAInverter, inverter.IsPPT →
    Negligible fun n => Game.succProbability (rsaUnitInversionGame gen inverter n)

/-- An `e`-th root modulo `N` of a challenge `y` that is not a unit, computed from `N` and `e`
alone as in the proof of Theorem 10.5 ([BonehShoup2023], p. 416): `0` for `y = 0`, and otherwise
`y ^ d' % N`, where `g = gcd(y, N)` and `d'` is the inverse of `e` modulo
`(g - 1) * (N / g - 1)`. -/
@[expose] def rsaNonUnitRoot (N e y : ℕ) : ℕ :=
  if y = 0 then 0
  else rsaInvert N (BinaryGcd.modInv e ((Nat.gcd y N - 1) * (N / Nat.gcd y N - 1))) y

theorem rsaNonUnitRoot_lt {N : ℕ} (hN : 0 < N) (e y : ℕ) : rsaNonUnitRoot N e y < N := by
  unfold rsaNonUnitRoot rsaInvert
  split
  · exact hN
  · exact Nat.mod_lt _ hN

/-- RSA evaluation maps the residues coprime to `N` to residues coprime to `N`, and the others to
others. -/
theorem coprime_rsaEval_iff (desc : RSADesc) (x : ℕ) :
    Nat.Coprime (rsaEval desc.modulus desc.e x) desc.modulus ↔ Nat.Coprime x desc.modulus := by
  rw [rsaEval, ZMod.coprime_mod_iff_coprime,
    Nat.coprime_pow_left_iff desc.e_pos]

/-- `rsaNonUnitRoot` inverts RSA evaluation on every residue `x < N` that is not coprime to `N`. -/
theorem rsaNonUnitRoot_rsaEval (desc : RSADesc) {x : ℕ} (hx : x < desc.modulus)
    (hunit : ¬ Nat.Coprime x desc.modulus) :
    rsaNonUnitRoot desc.modulus desc.e (rsaEval desc.modulus desc.e x) = x := by
  have hpq : Nat.Coprime desc.p desc.q := (Nat.coprime_primes desc.hp desc.hq).mpr desc.hpq
  set y := rsaEval desc.modulus desc.e x with hy_def
  have hyN : y < desc.modulus := Nat.mod_lt _ desc.modulus_pos
  have hdvd {r : ℕ} (hr : r.Prime) (hrN : r ∣ desc.modulus) : r ∣ y ↔ r ∣ x := by
    rw [hy_def, rsaEval, Nat.dvd_mod_iff hrN]
    exact ⟨hr.dvd_of_dvd_pow, fun h => dvd_pow h desc.e_pos.ne'⟩
  have hpN : desc.p ∣ desc.modulus := dvd_mul_right _ _
  have hqN : desc.q ∣ desc.modulus := dvd_mul_left _ _
  by_cases hy : y = 0
  · have hx0 : x = 0 := Nat.eq_zero_of_dvd_of_lt (hpq.mul_dvd_of_dvd_of_dvd
      ((hdvd desc.hp hpN).mp (hy ▸ dvd_zero _)) ((hdvd desc.hq hqN).mp (hy ▸ dvd_zero _))) hx
    rw [rsaNonUnitRoot, ite_eq_left hy, hx0]
  have htot : (Nat.gcd y desc.modulus - 1) * (desc.modulus / Nat.gcd y desc.modulus - 1) =
      desc.totient := by
    rw [Nat.Coprime.gcd_mul y hpq]
    rcases Nat.coprime_or_dvd_of_prime desc.hp y with hpy | hpy <;>
      rcases Nat.coprime_or_dvd_of_prime desc.hq y with hqy | hqy
    · exact absurd ((coprime_rsaEval_iff desc x).mp
        (Nat.Coprime.mul_right hpy.symm hqy.symm)) hunit
    · rw [Nat.Coprime.gcd_eq_one hpy.symm, Nat.gcd_eq_right hqy, one_mul,
        Nat.mul_div_cancel _ desc.hq.pos, mul_comm]
    · rw [Nat.gcd_eq_right hpy, Nat.Coprime.gcd_eq_one hqy.symm, mul_one,
        Nat.mul_div_cancel_left _ desc.hp.pos]
    · exact absurd (Nat.eq_zero_of_dvd_of_lt (hpq.mul_dvd_of_dvd_of_dvd hpy hqy) hyN) hy
  rw [rsaNonUnitRoot, ite_eq_right hy, htot]
  exact rsaInvert_rsaEval { desc with
    d := BinaryGcd.modInv desc.e desc.totient
    hed := BinaryGcd.mul_modInv_modEq_one (by have := desc.totient_gt_one; lia) desc.he } hx

/-- `rsaNonUnitRoot` is computable in polynomial time whenever `N`, `e` and `y` are, and
`0 < N a`. -/
theorem computableInPolyTime_rsaNonUnitRoot {α : Type} {enc : α ↪ List Bool} {N e y : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hy : ComputableInPolyTime y enc encNat) (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => rsaNonUnitRoot (N a) (e a) (y a)) enc encNat := by
  have hg := ComputableInPolyTime.binary_gcd' hy hN
  have hphi := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_sub' hg (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_div' hN hg)
      (ComputableInPolyTime.const 1))
  unfold rsaNonUnitRoot
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.decide_eq' hy (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.const 0)
    (computableInPolyTime_rsaInvert hN (ComputableInPolyTime.binary_modInv' he hphi) hy hpos)

/-- The wrapper `B` of Theorem 10.5 ([BonehShoup2023], p. 416): on a challenge `y` coprime to
`N`, run `A`; on any other challenge, return `rsaNonUnitRoot N e y`. -/
def unitRSAToRSA (A : RSAInverter) : RSAInverter := fun n pk y =>
  if Nat.Coprime y pk.N then A n pk y
  else pure ⟨rsaNonUnitRoot pk.N pk.e y, rsaNonUnitRoot_lt y.pos _ _⟩

/-- `unitRSAToRSA A` is a PPT `RSAInverter` whenever `A` is. -/
theorem isPPT_unitRSAToRSA {A : RSAInverter} (hA : A.IsPPT) : (unitRSAToRSA A).IsPPT := by
  unfold RSAInverter.IsPPT at hA ⊢
  have hcond : ComputableInPolyTime
      (fun x : RSAInput => decide (Nat.Coprime (x.challenge : ℕ) x.publicKey.N))
      encRSAInput encBool :=
    ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.binary_gcd' (by fun_prop) (by fun_prop)) (ComputableInPolyTime.const 1)
  have hroot : ComputableInPolyTime
      (fun x : RSAInput => rsaNonUnitRoot x.publicKey.N x.publicKey.e x.challenge)
      encRSAInput encNat :=
    computableInPolyTime_rsaNonUnitRoot (by fun_prop) (by fun_prop) (by fun_prop)
      (fun x => x.challenge.pos)
  refine (IsPPTOn.ite' hcond hA hroot.isPPTOn).congr fun x => ?_
  unfold unitRSAToRSA
  split <;> simp

/-- Averaging `w` over the image of an injection `r` gives at most its average over all of `α`,
when `w ≤ 1` everywhere and `w = 1` off the image. -/
private theorem inv_card_mul_sum_comp_le {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    {r : β → α} (hr : Function.Injective r) {w : α → ℝ≥0∞} (hw : ∀ a, w a ≤ 1)
    (hone : ∀ a, a ∉ Set.range r → w a = 1) :
    (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ b, w (r b) ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, w a := by
  classical
  set S := ∑ b, w (r b)
  have hle : Fintype.card β ≤ Fintype.card α := Fintype.card_le_of_injective r hr
  have hsplit : ∑ a, w a = S + ((Fintype.card α - Fintype.card β : ℕ) : ℝ≥0∞) := by
    rw [← Finset.sum_add_sum_compl (Finset.univ.image r),
      Finset.sum_image fun _ _ _ _ h => hr h]
    congr 1
    rw [Finset.sum_congr rfl fun a ha => hone a ?_, Finset.sum_const, nsmul_one,
      Finset.card_compl, Finset.card_image_of_injective _ hr, Finset.card_univ]
    simpa [Finset.mem_compl] using ha
  have hφ0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hφtop : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hN0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    have : Nonempty α := ⟨r (Classical.arbitrary β)⟩
    simp [Fintype.card_ne_zero]
  have hNtop : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hS : S ≤ Fintype.card β :=
    (Finset.sum_le_sum fun b _ => hw (r b)).trans (by simp)
  have hfrac : (Fintype.card β : ℝ≥0∞)⁻¹ * S ≤ 1 :=
    calc (Fintype.card β : ℝ≥0∞)⁻¹ * S ≤ (Fintype.card β : ℝ≥0∞)⁻¹ * Fintype.card β := by
          gcongr
      _ = 1 := ENNReal.inv_mul_cancel hφ0 hφtop
  rw [hsplit]
  calc (Fintype.card β : ℝ≥0∞)⁻¹ * S
      = (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card α * ((Fintype.card β : ℝ≥0∞)⁻¹ * S)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ * (S + ((Fintype.card α - Fintype.card β : ℕ) : ℝ≥0∞) *
          ((Fintype.card β : ℝ≥0∞)⁻¹ * S)) := by
        congr 1
        rw [show (Fintype.card α : ℝ≥0∞) =
            Fintype.card β + ((Fintype.card α - Fintype.card β : ℕ) : ℝ≥0∞) by
          rw [← Nat.cast_add, Nat.add_sub_cancel' hle], add_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel hφ0 hφtop, one_mul]
    _ ≤ _ := by
        gcongr
        exact mul_le_of_le_one_right zero_le hfrac

/-- **Theorem 10.5** ([BonehShoup2023], §10.6.2, p. 416): the success probability of `A` with a
uniform unit preimage is at most the success probability of `unitRSAToRSA A` in
`rsaInversionGame`, at every security parameter and for every key generator. On a unit challenge
the wrapper runs `A`, and on any other challenge it always wins. The book assumes `ℓ > 2` and odd
`e > 2`; here there is no condition on the key law, so `p = 2` and `e = 1` are allowed. -/
theorem succProbability_rsaUnitInversionGame_le (gen : RSAGen) (A : RSAInverter) (n : ℕ) :
    Game.succProbability (rsaUnitInversionGame gen A n) ≤
      Game.succProbability (rsaInversionGame gen (unitRSAToRSA A) n) := by
  rw [rsaUnitInversionGame_eq, rsaInversionGame_eq]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  refine PMF.bind_apply_mono_on_support _ _ fun desc _ => ?_
  set w : Fin desc.modulus → ℝ≥0∞ := fun x =>
    ((ProbComp.eval (unitRSAToRSA A n desc.publicKey (desc.publicKey.eval x))).bind
      fun x' => PMF.pure (decide (x' = x))) true with hw_def
  have hunit (u : (ZMod desc.modulus)ˣ) :
      ((ProbComp.eval (A n desc.publicKey (desc.publicKey.eval (desc.unitResidue u)))).bind
        fun x' => PMF.pure (decide (x' = desc.unitResidue u))) true = w (desc.unitResidue u) := by
    have hcop : Nat.Coprime (desc.publicKey.eval (desc.unitResidue u) : ℕ) desc.modulus :=
      (coprime_rsaEval_iff desc _).mpr ((desc.mem_range_unitResidue_iff _).mp ⟨u, rfl⟩)
    simp only [hw_def, unitRSAToRSA, ite_eq_left hcop]
  have hnonunit (x : Fin desc.modulus) (hx : x ∉ Set.range desc.unitResidue) : w x = 1 := by
    rw [desc.mem_range_unitResidue_iff] at hx
    have hcop : ¬ Nat.Coprime (desc.publicKey.eval x : ℕ) desc.modulus := by
      rwa [RSAPublicKey.val_eval, coprime_rsaEval_iff]
    have hroot : (⟨rsaNonUnitRoot desc.modulus desc.e (rsaEval desc.modulus desc.e x),
        rsaNonUnitRoot_lt desc.modulus_pos _ _⟩ : Fin desc.modulus) = x :=
      Fin.ext (rsaNonUnitRoot_rsaEval desc x.isLt hx)
    simp only [hw_def, unitRSAToRSA, ite_eq_right hcop]
    simp [hroot]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_apply (PMF.uniformOfFintype _), PMF.uniformOfFintype_apply, tsum_fintype,
    ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun u _ => hunit u]
  exact inv_card_mul_sum_comp_le desc.unitResidue_injective (fun x => PMF.coe_le_one _ _) hnonunit

/-- **The RSA assumption implies its unit-preimage variant** ([BonehShoup2023], §10.6.2, p. 416,
after Theorem 10.5), for every key generator. -/
theorem RSAOneWay.rsaUnitOneWay {gen : RSAGen} (h : RSAOneWay gen) : RSAUnitOneWay gen :=
  fun A hA => negligible_of_le (h _ (isPPT_unitRSAToRSA hA))
    fun n => succProbability_rsaUnitInversionGame_le gen A n

end Cslib.Crypto
