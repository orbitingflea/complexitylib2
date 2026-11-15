/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.DiffieHellman.CyclicGroupFamily
import CslibFrontier.Crypto.Computational.DiffieHellman.EvenOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# The parity test for DDH in groups of even order: checked instances

Concrete checks for `CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean` and
`CslibFrontier/Crypto/Computational/DiffieHellman/CyclicGroupFamily.lean`, through ordinary imports
of their public API:

* In `ZMod 6` with `g = 1`, Lemmas 16.1 and 16.2 hold on sample exponents, the parity
  distinguisher accepts a Diffie–Hellman triple and rejects a non-Diffie–Hellman one, and its
  fixed-group DDH advantage is exactly `1 / 2`.
* For odd `q` Lemma 16.1 fails: in `ZMod 5`, `a = 2` is even but `(5 / 2) • (2 • 1) ≠ 0`.
* In `(ZMod 7)ˣ` with generator `3`, and in `(ZMod p)ˣ` for every odd prime `p`, the distinguisher
  has fixed-group DDH advantage `1 / 2`.
* The additive groups `ZMod q` of nonzero order `q`, with generator `1` and residues in binary,
  form a `CyclicGroupFamily`. With the even orders `2 (n + 1)`, DDH does not hold for it
  (`not_ddh_of_even_order`), and a prime-order family whose setup law only produces groups of
  order `2` fails `PrimeOrderGroupFamily.DDH` (through `ddh_toCyclicGroupFamily_iff`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.DiffieHellmanEvenOrder

open Cslib Cslib.Probability Cslib.Crypto

/-! ### The group `ZMod 6` with generator `1` -/

theorem zmod6_injective : Function.Injective fun c : ZMod 6 => c • (1 : ZMod 6) := by
  intro a b h
  simpa using h

theorem even_six : Even 6 := ⟨3, rfl⟩

-- Lemma 16.1 on the exponents `2` (even) and `3` (odd).
example : (6 / 2) • ((2 : ZMod 6) • (1 : ZMod 6)) = 0 :=
  (div_two_nsmul_smul_eq_zero_iff even_six zmod6_injective 2).mpr ⟨1, rfl⟩

example : (6 / 2) • ((3 : ZMod 6) • (1 : ZMod 6)) ≠ 0 := fun h =>
  absurd ((div_two_nsmul_smul_eq_zero_iff even_six zmod6_injective 3).mp h) (by decide)

-- Lemma 16.2: `3 * 5 = 3` in `ZMod 6` is odd, and neither `3` nor `5` is even.
example : ¬((6 / 2) • ((3 : ZMod 6) • (1 : ZMod 6)) = 0 ∨
    (6 / 2) • ((5 : ZMod 6) • (1 : ZMod 6)) = 0) := fun h =>
  absurd ((even_val_mul_iff even_six zmod6_injective 3 5).mpr h) (by decide)

-- The distinguisher accepts the Diffie–Hellman triple for `a = 3`, `b = 5` and rejects `w = 4`.
example : ddhParityDistinguisher 6 (3 : ZMod 6) 5 3 = pure true := congrArg pure (by decide)

example : ddhParityDistinguisher 6 (3 : ZMod 6) 5 4 = pure false := congrArg pure (by decide)

example : Pr[ddhRealExperiment 6 (1 : ZMod 6) (ddhParityDistinguisher 6)] = 1 :=
  probability_ddhRealExperiment_ddhParityDistinguisher 6 1 even_six zmod6_injective

example : Pr[ddhRandomExperiment 6 (1 : ZMod 6) (ddhParityDistinguisher 6)] = 1 / 2 :=
  probability_ddhRandomExperiment_ddhParityDistinguisher 6 1 even_six zmod6_injective

/-- In `ZMod 6` with `g = 1` the parity distinguisher has fixed-group DDH advantage exactly
`1 / 2`. -/
theorem ddhAdvantage_zmod6 : ddhAdvantage 6 (1 : ZMod 6) (ddhParityDistinguisher 6) = 1 / 2 :=
  ddhAdvantage_ddhParityDistinguisher 6 1 even_six zmod6_injective

/-! ### Lemma 16.1 needs an even order -/

/-- In `ZMod 5` (odd order) Lemma 16.1 fails at `a = 2`: the exponent is even, yet
`(5 / 2) • (2 • 1) = 4 ≠ 0`. The element `g = 1` still has order `5`. -/
theorem not_lemma16_1_zmod5 :
    ¬((5 / 2) • ((2 : ZMod 5) • (1 : ZMod 5)) = 0 ↔ Even (2 : ZMod 5).val) := by
  decide

example : Function.Injective fun c : ZMod 5 => c • (1 : ZMod 5) := by
  intro a b h
  simpa using h

/-! ### The group `(ZMod p)ˣ` -/

section Units

attribute [local instance] neZero_sub_one_of_prime zmodUnitsModule

instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The residue `3` as a unit modulo `7`. -/
def three : (ZMod 7)ˣ := ZMod.unitOfCoprime 3 (by norm_num)

/-- `3` generates `(ZMod 7)ˣ`: its order is `6`, the order of the group. -/
theorem three_generates : ∀ x, x ∈ Subgroup.zpowers three := by
  have horder : orderOf three = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have htop : Subgroup.zpowers three = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horder, Nat.card_eq_fintype_card, ZMod.card_units]
  intro x
  rw [htop]
  exact Subgroup.mem_top x

/-- In `(ZMod 7)ˣ` with generator `3`, written additively, the parity distinguisher has
fixed-group DDH advantage exactly `1 / 2`. -/
example : ddhAdvantage (7 - 1) (Additive.ofMul three) (ddhParityDistinguisher (7 - 1)) = 1 / 2 :=
  ddhAdvantage_units_ddhParityDistinguisher 7 (by norm_num) three_generates

/-- For every odd prime `p`, some generator of `(ZMod p)ˣ` exists, and with it the parity
distinguisher has fixed-group DDH advantage `1 / 2`: the hypotheses of
`ddhAdvantage_units_ddhParityDistinguisher` are satisfiable. -/
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ g : (ZMod p)ˣ,
      ddhAdvantage (p - 1) (Additive.ofMul g) (ddhParityDistinguisher (p - 1)) = 1 / 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨g, ddhAdvantage_units_ddhParityDistinguisher p hp hg⟩

end Units

/-! ### A cyclic group family of even order -/

section Family

open Turing.MultiTapeTM

/-- Nonzero moduli, as public group parameters. -/
private abbrev ModulusDesc : Type := {q : ℕ // q ≠ 0}

/-- A modulus is encoded by its binary digits. -/
private def encModulus : ModulusDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans encNat

private theorem computableInPolyTime_modulus :
    ComputableInPolyTime (Subtype.val : ModulusDesc → ℕ) encModulus encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Addition modulo `q` of binary residues. -/
private def modulusAdd : ModulusDesc × List Bool × List Bool → List Bool
  | (q, x, y) => ((ofBits x + ofBits y) % q.1).bits

/-- Multiplication modulo `q` of a binary residue by a natural number. -/
private def modulusSMul : ModulusDesc × ℕ × List Bool → List Bool
  | (q, a, x) => (a * ofBits x % q.1).bits

/-- The additive groups `ZMod q` of nonzero order `q`, with generator `1` and residues encoded in
binary. The order need not be prime. -/
private def residueGroups : CyclicGroupFamily where
  Desc := ModulusDesc
  encDesc := encModulus
  order q := q.1
  order_ne_zero q := q.2
  Carrier q := ZMod q.1
  generator _ := 1
  card_carrier q := Nat.card_zmod q.1
  smul_generator_injective _ a b h := by simpa using h
  encode _ x := x.val.bits
  encode_injective q x y h := by
    have : NeZero q.1 := ⟨q.2⟩
    exact ZMod.val_injective _ (encNat.injective h)
  add := modulusAdd
  add_encode q x y := by
    have : NeZero q.1 := ⟨q.2⟩
    simp only [modulusAdd, ofBits_bits, ZMod.val_add]
  smul := modulusSMul
  smul_encode q a x := by
    have : NeZero q.1 := ⟨q.2⟩
    simp only [modulusSMul, ofBits_bits, smul_eq_mul, ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_mul_mod]
  computableInPolyTime_order := computableInPolyTime_modulus
  computableInPolyTime_generator := by
    have := computableInPolyTime_modulus
    simp only [ZMod.val_one_eq_one_mod]
    fun_prop
  computableInPolyTime_add := by
    have := computableInPolyTime_modulus
    unfold modulusAdd
    fun_prop
  computableInPolyTime_smul := by
    have := computableInPolyTime_modulus
    unfold modulusSMul
    fun_prop

/-- The setup law that, at security parameter `n`, always produces the modulus `2 (n + 1)`. -/
private noncomputable def evenSetup (n : ℕ) : PMF residueGroups.Desc :=
  PMF.pure ⟨2 * (n + 1), by omega⟩

/-- DDH does not hold for the residue groups of even order `2 (n + 1)`: the parity test is PPT and
has advantage `1 / 2`. -/
theorem not_ddh_residueGroups : ¬ residueGroups.DDH evenSetup :=
  CyclicGroupFamily.not_ddh_of_even_order fun n d hd => by
    obtain rfl := (PMF.mem_support_pure_iff _ _).1 hd
    exact even_two_mul (n + 1)

/-- A prime-order family whose setup law only produces groups of order `2` fails DDH:
`ddh_toCyclicGroupFamily_iff` transfers `not_ddh_of_even_order`. -/
theorem not_ddh_of_order_eq_two (F : PrimeOrderGroupFamily) {setup : ℕ → PMF F.Desc}
    (htwo : ∀ n, ∀ d ∈ (setup n).support, F.order d = 2) : ¬ F.DDH setup := fun h =>
  CyclicGroupFamily.not_ddh_of_even_order (F := F.toCyclicGroupFamily)
    (fun n d hd => by
      change Even (F.order d)
      rw [htwo n d hd]
      exact even_two)
    ((F.ddh_toCyclicGroupFamily_iff setup).2 h)

end Family

end CslibFrontierTests.Crypto.DiffieHellmanEvenOrder
