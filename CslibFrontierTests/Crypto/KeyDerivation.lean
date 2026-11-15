/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.KeyDerivation
import CslibFrontier.Crypto.Computational.ElGamal.KDF
import CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.PPT

/-!
# Tests for the key-derivation security game

Clients of `CslibFrontier.Crypto.Computational.KeyDerivation` and
`CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation` under module encapsulation:

* with no side information, the identity derivation of a key drawn from `key` is `Secure` for every
  `key`;
* `Secure.negligible` applies as a `Negligible` bound on `Game.advantage (realGame …) (idealGame …)`
  and `advantage` unfolds across the module boundary on a distinguisher separating uniform and
  constant keys;
* `not_secure_const`: a constant derivation is not `Secure` for a uniform one-bit key;
* side information matters: the identity derivation of a uniform bit that is also published is not
  `Secure`;
* positive test with side information: Attack Game 11.3 with `F (x, y) = x + y` on `ZMod 3`
  is `Secure`, and exercises `Secure.comp_info`, `secure_iff_computationallyIndistinguishable`, and
  unfolding `realEnsemble` and `idealEnsemble`;
* Attack Game 11.3 as printed (`F : X × Y → Z` on independent uniform `x` and `y` with `info =
  Prod.fst` and `derive = F`) unfolds `realOutput` and `idealOutput` to the textbook experiments;
* `secureKDF_linearHashKDF` transports through `secureKDF_iff_keyDerivation` to an instance of
  `KeyDerivation.Secure` with no hardness assumption under `LinearHashKDFConditions`.
-/

public section

namespace CslibFrontierTests.Crypto.KeyDerivation

open Cslib Probability Cslib.Crypto Cslib.Crypto.KeyDerivation Turing.MultiTapeTM
open scoped NNReal

/-- Nonvacuity: with no side information, the identity derivation of a key drawn from `key` is
secure, for every `key`. -/
example {Z : Type} (encU : Unit ↪ List Bool) (encZ : Z ↪ List Bool) (key : ℕ → PMF Z) :
    Secure encU encZ key (fun _ => ()) id key := fun D _ =>
  negligible_zero.congr fun n => by
    simp [realGame, idealGame, realOutput, idealOutput, Game.advantage]

/-- A constant derivation is not secure for a uniform one-bit key. -/
theorem not_secure_const : ¬ Secure encUnit encBool (fun _ => PMF.pure ()) id (fun _ => false)
    (fun _ => PMF.uniformOfFintype Bool) := by
  intro h
  have hD : Distinguisher.IsPPT encUnit encBool (fun _ _ z => pure z) := by
    unfold Distinguisher.IsPPT
    ppt
  refine not_negligible_const (c := 1 / 2) (by norm_num) ((h _ hD).congr fun n => ?_)
  have h1 : realGame (fun _ => PMF.pure ()) id (fun _ => false) (fun _ _ z => pure z) n =
      PMF.pure false := by simp [realGame, realOutput]
  have h2 : idealGame (fun _ => PMF.pure ()) (id : Unit → Unit)
      (fun _ => PMF.uniformOfFintype Bool) (fun _ _ z => pure z) n = PMF.uniformOfFintype Bool := by
    simp [idealGame, idealOutput]
  rw [h1, h2]
  apply NNReal.eq
  rw [Game.coe_guessingAdvantage]
  simp

/-- Side information matters: the identity derivation of a uniform bit that is also published is
not secure, although without the side information it is (first example). -/
example : ¬ Secure encBool encBool (fun _ => PMF.uniformOfFintype Bool) id id
    (fun _ => PMF.uniformOfFintype Bool) := by
  intro h
  have hD : Distinguisher.IsPPT encBool encBool (fun _ x z => pure (x == z)) := by
    unfold Distinguisher.IsPPT
    ppt
  refine not_negligible_const (c := 1 / 2) (by norm_num) ((h _ hD).congr fun n => ?_)
  have h1 : realGame (fun _ => PMF.uniformOfFintype Bool) id id (fun _ x z => pure (x == z)) n =
      PMF.pure true := by simp [realGame, realOutput]
  have h2 : idealGame (fun _ => PMF.uniformOfFintype Bool) (id : Bool → Bool)
      (fun _ => PMF.uniformOfFintype Bool) (fun _ x z => pure (x == z)) n =
      PMF.uniformOfFintype Bool := by
    simpa only [idealGame, idealOutput, id_eq, ProbComp.eval_pure, PMF.map, Function.comp_def,
      Bool.beq_comm] using Game.uniform_bool_bind_map_beq_const (PMF.uniformOfFintype Bool)
  rw [h1, h2]
  apply NNReal.eq
  rw [Game.coe_guessingAdvantage]
  simp
  norm_num

/-- Consuming `Secure.negligible` as a `Game.advantage` bound across the module boundary. -/
example {S X Z : Type} {encX : X ↪ List Bool} {encZ : Z ↪ List Bool} {sample : ℕ → PMF S}
    {info : S → X} {derive : S → Z} {key : ℕ → PMF Z} (h : Secure encX encZ sample info derive key)
    {D : Distinguisher X Z} (hD : D.IsPPT encX encZ) :
    Negligible fun n => Game.advantage (realGame sample info derive D n)
      (idealGame sample info key D n) :=
  h.negligible hD

/-- `advantage` unfolds across the module boundary: distinguishing a uniform bit from the constant
ideal key `PMF.pure true` has advantage `1 / 2`. -/
example :
    advantage (PMF.uniformOfFintype Bool) (fun _ => ()) id (PMF.pure true)
      (fun _ z => PMF.pure z) = 1 / 2 := by
  unfold advantage realOutput idealOutput
  simp only [id_eq, PMF.bind_const, PMF.bind_pure]
  rw [Game.advantage_comm]
  apply NNReal.eq
  rw [Game.coe_advantage]
  simp [Game.succProbability, ENNReal.toNNReal_ofNat]
  norm_num

/- Positive test with side information: Attack Game 11.3 with `F (x, y) = x + y` on `ZMod 3`
has identical real and ideal experiments, hence is `Secure` and exercises `Secure.comp_info` and
`secure_iff_computationallyIndistinguishable` (plus unfolding `realEnsemble` and
`idealEnsemble`). -/
section ZMod3OTP

private noncomputable def pairLaw : PMF (ZMod 3 × ZMod 3) := do
  let x ← PMF.uniformOfFintype (ZMod 3)
  let y ← PMF.uniformOfFintype (ZMod 3)
  return (x, y)

private theorem realOutput_add (D : ZMod 3 → ZMod 3 → PMF Bool) :
    realOutput pairLaw Prod.fst (fun p => p.1 + p.2) D =
      idealOutput pairLaw Prod.fst (PMF.uniformOfFintype (ZMod 3)) D := by
  simp only [realOutput, idealOutput, pairLaw, pmf_norm, PMF.bind_const]
  refine congrArg _ (funext fun x => ?_)
  exact PMF.uniformOfFintype_bind_add_left x fun z => D x z

private theorem secure_add (encX encZ : ZMod 3 ↪ List Bool) :
    Secure encX encZ (fun _ => pairLaw) Prod.fst (fun p => p.1 + p.2)
      (fun _ => PMF.uniformOfFintype (ZMod 3)) := fun D _ =>
  negligible_zero.congr fun _ => by
    simp only [realGame, idealGame, realOutput_add, Game.advantage_self]

example (encX encZ : ZMod 3 ↪ List Bool) :
    Secure encUnit encZ (fun _ => pairLaw) ((fun _ => ()) ∘ Prod.fst) (fun p => p.1 + p.2)
      (fun _ => PMF.uniformOfFintype (ZMod 3)) :=
  (secure_add encX encZ).comp_info (by fun_prop)

example (encX encZ : ZMod 3 ↪ List Bool) :
    ComputationallyIndistinguishable
      (realEnsemble encX encZ (fun _ => pairLaw) Prod.fst (fun p => p.1 + p.2))
      (idealEnsemble encX encZ (fun _ => pairLaw) Prod.fst
        (fun _ => PMF.uniformOfFintype (ZMod 3))) :=
  (secure_iff_computationallyIndistinguishable ..).mp (secure_add encX encZ)

example (encX encZ : ZMod 3 ↪ List Bool) (n : ℕ) :
    realEnsemble encX encZ (fun _ => pairLaw) Prod.fst (fun p => p.1 + p.2) n =
      idealEnsemble encX encZ (fun _ => pairLaw) Prod.fst
        (fun _ => PMF.uniformOfFintype (ZMod 3)) n := by
  unfold realEnsemble idealEnsemble
  simp only [pairLaw, pmf_norm, PMF.bind_const]
  refine congrArg _ (funext fun x => ?_)
  exact PMF.uniformOfFintype_bind_add_left x fun z => PMF.pure (encPair encX encZ (x, z))

end ZMod3OTP

/-- Attack Game 11.3 as printed: `F : X × Y → Z`, independent uniform `x` and `y`, and the
adversary sees `x`. It is the instance `info = Prod.fst`, `derive = F`. -/
example {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X × Y → Z)
    (D : X → Z → PMF Bool) :
    realOutput (do
        let x ← PMF.uniformOfFintype X
        let y ← PMF.uniformOfFintype Y
        return (x, y)) Prod.fst F D =
      (PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Y).bind fun y =>
        D x (F (x, y)) := by
  simp only [realOutput, pmf_norm]

example {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] [Fintype Z] [Nonempty Z]
    (D : X → Z → PMF Bool) :
    idealOutput (do
        let x ← PMF.uniformOfFintype X
        let y ← PMF.uniformOfFintype Y
        return (x, y)) Prod.fst (PMF.uniformOfFintype Z) D =
      (PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Z).bind fun z => D x z := by
  simp only [idealOutput, pmf_norm, PMF.bind_const]

/-- `secureKDF_linearHashKDF` yields an instance of `KeyDerivation.Secure` through
`secureKDF_iff_keyDerivation`. -/
example (F : PrimeOrderGroupFamily) {setup : ℕ → PMF F.Desc} {keyLen bound : F.Desc → ℕ}
    {msgLen qMin : ℕ → ℕ} (h : F.LinearHashKDFConditions setup keyLen bound msgLen qMin) :
    Secure F.withSeed.encCDHInput encBits
      (F.withSeed.kdfSecret (F.seededSetup setup (F.linearHashSeedLen msgLen bound)))
      PrimeOrderGroupFamily.DDHInput.toCDHInput
      (fun x => F.linearHashKDF keyLen bound
        (x.groupParameters, F.withSeed.encode x.groupParameters x.candidateShared))
      (fun n => Cslib.BitString.uniformList (msgLen n)) :=
  (F.withSeed.secureKDF_iff_keyDerivation _ _ _).mp (F.secureKDF_linearHashKDF h)

end CslibFrontierTests.Crypto.KeyDerivation
