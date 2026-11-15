/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Key-derivation security game

[BonehShoup2023], Section 11.5.2 (Attack Game 11.3, p. 448, and Definition 11.5, p. 449) defines
key-derivation security for a function `F : X × Y → Z` by comparing `(x, F(x, y))` against `(x, z)`
for independent uniform `x`, `y`, and `z`. Section 8.10.1 (pp. 325–326) states the general form: for
a secret `s` drawn from a distribution `P`, public side information `I(s)`, and derived key `H(s)`,
the pairs `(I(s), H(s))` and `(I(s), t)` with an independent key `t` are computationally
indistinguishable.

This module formalizes the game in the generality of Section 8.10.1, with the following choices
relative to the printed definitions:

1. **One game in the Section 8.10.1 form** (`sample`, `info`, `derive`). Attack Game 11.3 as
   printed is the instance where `sample n` draws independent uniform `(x, y) ∈ X × Y`,
   `info = Prod.fst`, and `derive = F`. The group-specialized notion
   `PrimeOrderGroupFamily.SecureKDF` (where the group description is sampled first and the key law
   depends on the security parameter) is an instance via
   `PrimeOrderGroupFamily.secureKDF_iff_keyDerivation`.
2. **Arbitrary secret and ideal key laws** `sample : ℕ → PMF S` and `key : ℕ → PMF Z` in place of
   efficient samplers or fixed uniform finite-type distributions, and arbitrary `info` and `derive`
   with no computability or finiteness hypotheses, so `Z` needs no `Fintype` instance and both
   `BitString.uniformList (msgLen n)` and `PMF.uniformOfFintype Z` are instances.
3. **One-parameter outputs parameterized by the distinguisher's output law** `X → Z → PMF Bool`
   (`realOutput`, `idealOutput`, `advantage`), so both program distinguishers (`ProbComp.eval`) and
   oracle distinguishers interpreted against a fixed table are instances.
4. **Equivalence of typed and word-ensemble presentations**: `Secure` is `Game.Indistinguishable`
   against typed uniform strict PPT distinguishers (`Distinguisher.IsPPT encX encZ`), and
   `secure_iff_computationallyIndistinguishable` proves it equivalent to
   `ComputationallyIndistinguishable` (Definition 3.4) of the encoded word ensembles `realEnsemble`
   and `idealEnsemble`.

## Main definitions

* `Cslib.Crypto.KeyDerivation.realOutput`: Experiment 0 at one parameter for a distinguisher output
  law.
* `Cslib.Crypto.KeyDerivation.idealOutput`: Experiment 1 at one parameter for a distinguisher output
  law.
* `Cslib.Crypto.KeyDerivation.advantage`: single-parameter key-derivation advantage `KDFadv` /
  `Distadv`.
* `Cslib.Crypto.KeyDerivation.Distinguisher`: family of probabilistic key-derivation distinguishers.
* `Cslib.Crypto.KeyDerivation.Distinguisher.IsPPT`: uniform strict PPT admissibility on
  `(1ⁿ, x, z)`.
* `Cslib.Crypto.KeyDerivation.realGame`: Experiment 0 family at each security parameter.
* `Cslib.Crypto.KeyDerivation.idealGame`: Experiment 1 family at each security parameter.
* `Cslib.Crypto.KeyDerivation.Secure`: asymptotic key-derivation security (Definition 11.5 and
  Section 8.10.1).
* `Cslib.Crypto.KeyDerivation.realEnsemble`: the encoded word ensemble `(info s, derive s)`.
* `Cslib.Crypto.KeyDerivation.idealEnsemble`: the encoded word ensemble `(info s, z)`.

## Main results

* `Cslib.Crypto.KeyDerivation.secure_iff_computationallyIndistinguishable`: `Secure` is equivalent
  to `ComputationallyIndistinguishable` of `realEnsemble` and `idealEnsemble`.
* `Cslib.Crypto.KeyDerivation.Secure.comp_info`: postprocessing the side information by a
  polynomial-time function preserves `Secure`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.10.1 (pp. 325–326) and Section 11.5.2 (Attack Game 11.3 and Definition 11.5,
  pp. 448–449).
-/

public section

open Cslib Probability Turing.MultiTapeTM
open scoped NNReal

namespace Cslib.Crypto.KeyDerivation

variable {S X Z : Type}

/-! ### One parameter -/

/-- Experiment 0 of Attack Game 11.3 ([BonehShoup2023], Section 11.5.2, p. 448) at one parameter,
in the form of Section 8.10.1 (p. 326): the law of the bit a distinguisher outputs on the side
information `info s` and the derived key `derive s`, for `s` drawn from `sample`. The distinguisher
is given by its output law, so that programs (`ProbComp.eval`) and oracle programs run against a
fixed table are both instances. -/
@[expose] noncomputable def realOutput (sample : PMF S) (info : S → X) (derive : S → Z)
    (D : X → Z → PMF Bool) : Game :=
  sample.bind fun s => D (info s) (derive s)

/-- Experiment 1 of Attack Game 11.3 ([BonehShoup2023], Section 11.5.2, p. 448) at one parameter,
in the form of Section 8.10.1 (p. 326): the distinguisher sees `info s` and an independent key
drawn from `key`. -/
@[expose] noncomputable def idealOutput (sample : PMF S) (info : S → X) (key : PMF Z)
    (D : X → Z → PMF Bool) : Game :=
  sample.bind fun s => key.bind fun z => D (info s) z

/-- `KDFadv[A, F]` of Attack Game 11.3 ([BonehShoup2023], Section 11.5.2, pp. 448–449), which is
`Distadv[A, P, I, H]` of Section 8.10.1 (p. 326) with `P = sample`, `I = info`, `H = derive`. -/
@[expose] noncomputable def advantage (sample : PMF S) (info : S → X) (derive : S → Z)
    (key : PMF Z) (D : X → Z → PMF Bool) : ℝ≥0 :=
  Game.advantage (realOutput sample info derive D) (idealOutput sample info key D)

/-! ### Families -/

/-- A key-derivation distinguisher: the security parameter, the public information and a
candidate key. -/
abbrev Distinguisher (X Z : Type) : Type := ℕ → X → Z → ProbComp Bool

/-- One uniform strict PPT machine reads `(1ⁿ, x, z)`. -/
@[expose] def Distinguisher.IsPPT (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (D : Distinguisher X Z) : Prop :=
  IsPPTOn (encPair encUnary (encPair encX encZ)) encBool fun p => D p.1 p.2.1 p.2.2

/-- Experiment 0 at each security parameter. -/
@[expose] noncomputable def realGame (sample : ℕ → PMF S) (info : S → X) (derive : S → Z)
    (D : Distinguisher X Z) (n : ℕ) : Game :=
  realOutput (sample n) info derive fun x z => ProbComp.eval (D n x z)

/-- Experiment 1 at each security parameter. -/
@[expose] noncomputable def idealGame (sample : ℕ → PMF S) (info : S → X) (key : ℕ → PMF Z)
    (D : Distinguisher X Z) (n : ℕ) : Game :=
  idealOutput (sample n) info (key n) fun x z => ProbComp.eval (D n x z)

/-- Secure key derivation ([BonehShoup2023], Section 11.5.2, Attack Game 11.3, p. 448, and
Definition 11.5, p. 449; Section 8.10.1, p. 326): every uniform strict PPT distinguisher
(`Distinguisher.IsPPT encX encZ`) has negligible advantage between `realGame` and `idealGame`.

Phrased in the form of Section 8.10.1 (secret `s` with law `sample n`, side information `info s`,
derived key `derive s`) with an arbitrary ideal key law `key : ℕ → PMF Z` in place of the uniform
distribution on a finite key space; Attack Game 11.3 as printed is the instance where `sample n` is
uniform on `X × Y`, `info = Prod.fst`, `derive = F`, and `key n` is uniform on `Z`. Neither
efficient computability of `info` and `derive` nor finiteness of the secret and key spaces is part
of the notion; it is the source's notion only when `key n` is uniform on a finite key space. -/
@[expose] def Secure (encX : X ↪ List Bool) (encZ : Z ↪ List Bool) (sample : ℕ → PMF S)
    (info : S → X) (derive : S → Z) (key : ℕ → PMF Z) : Prop :=
  Game.Indistinguishable (realGame sample info derive) (idealGame sample info key)
    (Distinguisher.IsPPT encX encZ)

/-- The word ensemble `(I(s), H(s))` of [BonehShoup2023], Section 8.10.1 (p. 326). -/
@[expose] noncomputable def realEnsemble (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (sample : ℕ → PMF S) (info : S → X) (derive : S → Z) (n : ℕ) : PMF (List Bool) := do
  let s ← sample n
  return encPair encX encZ (info s, derive s)

/-- The word ensemble `(I(s), t)` of [BonehShoup2023], Section 8.10.1 (p. 326). -/
@[expose] noncomputable def idealEnsemble (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (sample : ℕ → PMF S) (info : S → X) (key : ℕ → PMF Z) (n : ℕ) : PMF (List Bool) := do
  let s ← sample n
  let z ← key n
  return encPair encX encZ (info s, z)

/-- A word distinguisher run on the encoded pair plays the typed real game. -/
theorem distinguishingGame_realEnsemble (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (sample : ℕ → PMF S) (info : S → X) (derive : S → Z) (W : Crypto.Distinguisher) (n : ℕ) :
    distinguishingGame (realEnsemble encX encZ sample info derive n) (W n) =
      realGame sample info derive (fun n x z => W n (encPair encX encZ (x, z))) n := by
  simp only [distinguishingGame_eq_bind, realEnsemble, realGame, realOutput, pmf_norm]

/-- A word distinguisher run on the encoded pair plays the typed ideal game. -/
theorem distinguishingGame_idealEnsemble (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (sample : ℕ → PMF S) (info : S → X) (key : ℕ → PMF Z) (W : Crypto.Distinguisher) (n : ℕ) :
    distinguishingGame (idealEnsemble encX encZ sample info key n) (W n) =
      idealGame sample info key (fun n x z => W n (encPair encX encZ (x, z))) n := by
  simp only [distinguishingGame_eq_bind, idealEnsemble, idealGame, idealOutput, pmf_norm]

/-- **The two presentations agree** ([BonehShoup2023], Section 8.10.1, p. 326, and Section 11.5.2,
Attack Game 11.3, p. 448): `Secure` is computational indistinguishability (Definition 3.4) of
`(I(s), H(s))` and `(I(s), t)`. -/
theorem secure_iff_computationallyIndistinguishable (encX : X ↪ List Bool) (encZ : Z ↪ List Bool)
    (sample : ℕ → PMF S) (info : S → X) (derive : S → Z) (key : ℕ → PMF Z) :
    Secure encX encZ sample info derive key ↔
      ComputationallyIndistinguishable (realEnsemble encX encZ sample info derive)
        (idealEnsemble encX encZ sample info key) := by
  constructor
  · intro h W hW
    have hD : Distinguisher.IsPPT encX encZ (fun n x z => W n (encPair encX encZ (x, z))) :=
      hW.on.preprocess (prepare := fun p : ℕ × X × Z => (p.1, encPair encX encZ p.2))
        (ComputableInPolyTime.of_eq fun _ => rfl)
    simpa only [distinguishingGame_realEnsemble, distinguishingGame_idealEnsemble] using h _ hD
  · intro h D hD
    obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor (words := encPair encUnary encBits)
      (toWords := fun p : ℕ × X × Z => (p.1, encPair encX encZ p.2)) fun _ => rfl
    let W' : Crypto.Distinguisher := fun n word => W (n, word)
    obtain rfl : D = fun n x z => W' n (encPair encX encZ (x, z)) :=
      funext₃ fun n x z => hWD (n, x, z)
    simpa only [distinguishingGame_realEnsemble, distinguishingGame_idealEnsemble] using h W' hW

/-- Applying the assumption to one certified distinguisher. -/
theorem Secure.negligible {encX : X ↪ List Bool} {encZ : Z ↪ List Bool} {sample : ℕ → PMF S}
    {info : S → X} {derive : S → Z} {key : ℕ → PMF Z} (h : Secure encX encZ sample info derive key)
    {D : Distinguisher X Z} (hD : D.IsPPT encX encZ) :
    Negligible fun n =>
      advantage (sample n) info derive (key n) fun x z => ProbComp.eval (D n x z) :=
  h D hD

/-- Efficient preprocessing of the public information: a KDF secure given `info` is secure given
any polynomial-time function of it (less side information). -/
theorem Secure.comp_info {X' : Type} {encX : X ↪ List Bool} {encX' : X' ↪ List Bool}
    {encZ : Z ↪ List Bool} {sample : ℕ → PMF S} {info : S → X} {derive : S → Z} {key : ℕ → PMF Z}
    (h : Secure encX encZ sample info derive key) {f : X → X'}
    (hf : ComputableInPolyTime f encX encX') :
    Secure encX' encZ sample (f ∘ info) derive key := by
  intro D hD
  refine h (fun n x z => D n (f x) z) ?_
  unfold Distinguisher.IsPPT at hD ⊢
  exact IsPPTOn.preprocess (prepare := fun p : ℕ × X × Z => (p.1, f p.2.1, p.2.2)) hD
    (by fun_prop)

end Cslib.Crypto.KeyDerivation
