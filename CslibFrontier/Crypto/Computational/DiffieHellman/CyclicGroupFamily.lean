/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiffieHellman.EvenOrder
public import CslibFrontier.Crypto.Computational.DiscreteLog.CyclicGroupFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Decisional Diffie–Hellman over cyclic group families, and the parity test in even order

This module states the Decisional Diffie–Hellman assumption over a `CyclicGroupFamily`: Attack
Game 10.6 of [BonehShoup2023] (p. 410) without the restriction that the order is prime, as in
Exercise 10.24 (p. 431). Its declarations have the shapes of the prime-order ones in
`CslibFrontier/Crypto/Computational/DiffieHellman.lean`, and on a prime-order family the two
assumptions agree (`PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`).

The parity test of [BonehShoup2023], Section 16.1.3 (`Cslib.Crypto.ddhParityDistinguisher` in
`CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean`), runs in every group of the
family. Its efficiency certificate `CyclicGroupFamily.isPPT_ddhParityDistinguisher` gives one
uniform strict PPT machine that computes it on encoded inputs. With the fixed-group laws of
`EvenOrder.lean`, this is Exercise 10.24's efficient adversary with advantage `1 / 2`: when every
group the setup law can produce has even order, DDH does not hold
(`CyclicGroupFamily.not_ddh_of_even_order`).

## Main definitions

* `Cslib.Crypto.CyclicGroupFamily.DDHInput`, `Cslib.Crypto.CyclicGroupFamily.encDDHInput`: the
  input of a DDH distinguisher and its encoding.
* `Cslib.Crypto.CyclicGroupFamily.DDHDistinguisher`,
  `Cslib.Crypto.CyclicGroupFamily.DDHDistinguisher.IsPPT`: DDH distinguishers and their
  efficiency on encodings.
* `Cslib.Crypto.CyclicGroupFamily.ddhRealGame`, `Cslib.Crypto.CyclicGroupFamily.ddhRandomGame`,
  `Cslib.Crypto.CyclicGroupFamily.DDH`: the two DDH games and the DDH assumption.
* `Cslib.Crypto.CyclicGroupFamily.ddhParityDistinguisher`: the parity test as a distinguisher
  over the family.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_toCyclicGroupFamily_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`: on a prime-order family, PPT
  distinguishers and the DDH assumption are those of `PrimeOrderGroupFamily`.
* `Cslib.Crypto.CyclicGroupFamily.isPPT_ddhParityDistinguisher`: the parity test is PPT.
* `Cslib.Crypto.CyclicGroupFamily.not_ddh_of_even_order`: DDH does not hold when every group the
  setup law can produce has even order.

## Implementation notes

`DDHInput`, `encDDHInput`, `DDHDistinguisher`, `DDHDistinguisher.IsPPT`, `ddhRealGame`,
`ddhRandomGame` and `DDH` repeat the prime-order declarations over `CyclicGroupFamily`, with the
same games `Cslib.Crypto.ddhRealExperiment` and `Cslib.Crypto.ddhRandomExperiment`.
`ddh_toCyclicGroupFamily_iff` ties the two assumptions together.

Not covered: a family of the groups `(ZMod p)ˣ`. For such a family with odd primes `p`,
`not_ddh_of_even_order` applies, since the order `p - 1` is even; without it, the book's
conclusion that DDH does not hold in `Z_p^*` (p. 687, and the remark after Exercise 10.24) is
proved here only in the fixed-group form `ddhAdvantage_units_ddhParityDistinguisher`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Attack Game 10.6 (p. 410), Exercise 10.24 (p. 431) and
  Section 16.1.3 (p. 687).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace CyclicGroupFamily

variable (F : CyclicGroupFamily)

/-! ### Distinguisher inputs and the DDH assumption -/

/-- The input of a DDH distinguisher: the security parameter, public group parameters `d` and
three elements of `F.Carrier d`, which are `a • g`, `b • g` and the candidate shared element. -/
structure DDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its order and generator within the family. -/
  groupParameters : F.Desc
  /-- The first public element, `a • g` in the experiment. -/
  leftPublic : F.Carrier groupParameters
  /-- The second public element, `b • g` in the experiment. -/
  rightPublic : F.Carrier groupParameters
  /-- The candidate shared element: `(a * b) • g` in the real experiment, an independent `c • g`
  in the random one. -/
  candidateShared : F.Carrier groupParameters

/-- The encoding of a DDH input: the unary security parameter, the group parameters and the words
of the three elements, each framed except the last (`encDDHInput_apply`). It has the layout of
`PrimeOrderGroupFamily.encDDHInput`. -/
enc_structure encDDHInput (F : CyclicGroupFamily) : DDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  candidateShared : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- A DDH distinguisher over the family: given the security parameter, public group parameters
`d` and three elements of `F.Carrier d`, it outputs a bit. -/
abbrev DDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d → ProbComp Bool

variable {F} in
/-- A DDH distinguisher is PPT when one uniform strict PPT machine reads `encDDHInput` and writes
the distinguisher's output bit. -/
@[expose] def DDHDistinguisher.IsPPT (distinguisher : F.DDHDistinguisher) : Prop :=
  IsPPTOn F.encDDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.candidateShared

/-- The real DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 0, with the order not
required to be prime as in Exercise 10.24): choose group parameters `d` using the arbitrary setup
law, then run `Cslib.Crypto.ddhRealExperiment` in `F.Carrier d`. -/
@[expose] noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The random DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 1, with the order not
required to be prime as in Exercise 10.24): choose group parameters `d` using the arbitrary setup
law, then run `Cslib.Crypto.ddhRandomExperiment` in `F.Carrier d`. -/
@[expose] noncomputable def ddhRandomGame (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The Decisional Diffie–Hellman assumption for a cyclic group family and a setup law
([BonehShoup2023], Attack Game 10.6, printed p. 410, with the order not required to be prime, as
in Exercise 10.24, printed p. 431): every PPT DDH distinguisher has negligible advantage between
`ddhRealGame` and `ddhRandomGame`. This is a hypothesis, not a theorem; on a prime-order family it
is `PrimeOrderGroupFamily.DDH` (`PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`). -/
@[expose] def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhRandomGame setup)
    DDHDistinguisher.IsPPT

end CyclicGroupFamily

/-! ### Agreement with the prime-order assumption -/

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-- The DDH inputs of `F` and of `F.toCyclicGroupFamily` correspond field by field. -/
private def ddhInputEquiv : F.DDHInput ≃ F.toCyclicGroupFamily.DDHInput where
  toFun x := ⟨x.secParam, x.groupParameters, x.leftPublic, x.rightPublic, x.candidateShared⟩
  invFun x := ⟨⟨x.secParam, x.groupParameters, x.leftPublic, x.rightPublic⟩, x.candidateShared⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Corresponding DDH inputs have the same encoding. -/
private theorem encDDHInput_ddhInputEquiv (x : F.DDHInput) :
    F.toCyclicGroupFamily.encDDHInput (F.ddhInputEquiv x) = F.encDDHInput x := by
  rw [CyclicGroupFamily.encDDHInput_apply, encDDHInput_apply]
  rfl

/-- A distinguisher over `F` is PPT for `F.toCyclicGroupFamily` exactly when it is PPT for `F`:
the two input encodings agree. -/
theorem isPPT_toCyclicGroupFamily_iff (distinguisher : F.DDHDistinguisher) :
    CyclicGroupFamily.DDHDistinguisher.IsPPT (F := F.toCyclicGroupFamily) distinguisher ↔
      distinguisher.IsPPT := by
  constructor
  · rintro ⟨k, State, hfin, machine, c, e, h⟩
    refine ⟨k, State, hfin, machine, c, e, fun a => ?_⟩
    rw [← F.encDDHInput_ddhInputEquiv a]
    exact h (F.ddhInputEquiv a)
  · rintro ⟨k, State, hfin, machine, c, e, h⟩
    refine ⟨k, State, hfin, machine, c, e, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := F.ddhInputEquiv.surjective a
    rw [F.encDDHInput_ddhInputEquiv a]
    exact h a

/-- On a prime-order family the DDH assumption over cyclic group families is the prime-order
one. -/
theorem ddh_toCyclicGroupFamily_iff (setup : ℕ → PMF F.Desc) :
    F.toCyclicGroupFamily.DDH setup ↔ F.DDH setup :=
  forall_congr' fun distinguisher =>
    imp_congr (F.isPPT_toCyclicGroupFamily_iff distinguisher) Iff.rfl

end PrimeOrderGroupFamily

/-! ### The parity test in families of even order -/

namespace CyclicGroupFamily

variable (F : CyclicGroupFamily)

/-- The parity test of [BonehShoup2023], Section 16.1.3 (p. 687), as a distinguisher over the
family: in the group selected by `d` it runs `Cslib.Crypto.ddhParityDistinguisher (F.order d)`. -/
@[expose] def ddhParityDistinguisher : F.DDHDistinguisher :=
  fun _ d => Crypto.ddhParityDistinguisher (F.order d)

/-- **The parity test is efficient**: one uniform strict PPT machine computes
`ddhParityDistinguisher` on `encDDHInput`. It computes `F.order d / 2`, multiplies each encoded
element by it with `F.smul` and compares the results with the encoded identity. -/
theorem isPPT_ddhParityDistinguisher : (ddhParityDistinguisher F).IsPPT := by
  refine (ComputableInPolyTime.isPPTOn (f := fun x : F.DDHInput =>
    decide (F.encode x.groupParameters (((F.order x.groupParameters / 2 : ℕ) :
        ZMod (F.order x.groupParameters)) • x.candidateShared) = F.encode x.groupParameters 0) ==
      decide (F.encode x.groupParameters (((F.order x.groupParameters / 2 : ℕ) :
          ZMod (F.order x.groupParameters)) • x.leftPublic) = F.encode x.groupParameters 0 ∨
        F.encode x.groupParameters (((F.order x.groupParameters / 2 : ℕ) :
          ZMod (F.order x.groupParameters)) • x.rightPublic) = F.encode x.groupParameters 0))
    (by fun_prop)).congr fun x => ?_
  simp [ddhParityDistinguisher, Crypto.ddhParityDistinguisher, (F.encode_injective _).eq_iff,
    Nat.cast_smul_eq_nsmul]

variable {F} in
/-- **DDH fails in families of even order** ([BonehShoup2023], Exercise 10.24, p. 431): when every
group the setup law can produce has even order, the parity test, which is PPT
(`isPPT_ddhParityDistinguisher`), has advantage `1 / 2` for every security parameter, so the
DDH assumption does not hold. -/
theorem not_ddh_of_even_order {setup : ℕ → PMF F.Desc}
    (heven : ∀ n, ∀ d ∈ (setup n).support, Even (F.order d)) : ¬ F.DDH setup := by
  intro h
  refine not_negligible_const (c := 1 / 2) (by norm_num) ?_
  convert h _ (isPPT_ddhParityDistinguisher F) using 2 with n
  have hreal : F.ddhRealGame setup (ddhParityDistinguisher F) n = PMF.pure true :=
    (Cslib.Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true) fun d hd =>
      eval_ddhRealExperiment_ddhParityDistinguisher _ _ (heven n d hd)
        (F.smul_generator_injective d)).trans (PMF.bind_const _ _)
  have hrand : F.ddhRandomGame setup (ddhParityDistinguisher F) n =
      PMF.uniformOfFintype Bool :=
    (Cslib.Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.uniformOfFintype Bool)
      fun d hd => eval_ddhRandomExperiment_ddhParityDistinguisher _ _ (heven n d hd)
        (F.smul_generator_injective d)).trans (PMF.bind_const _ _)
  rw [hreal, hrand]
  apply NNReal.eq
  rw [Game.coe_advantage]
  simp
  norm_num

end CyclicGroupFamily

end Cslib.Crypto
