/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import all CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness
import CslibFrontier.Probability.PMF.Bind

/-!
# Tests for the salted joint-oracle FO correctness hop

The fixtures below keep the direct joint-oracle witness and the decapsulation-only witness
separate. Their exact query bounds detect counting the two projections of a joint reply twice or
dropping the `qD` contribution. The connected explicit-coin PKE has one good and one bad Boolean
coin for every message, so both local bad-event probabilities and its global correctness error are
exactly `1 / 2` rather than vacuous endpoints. Distinct key and coin types make projection order a
type-level regression. A Bool-prefix execution regression checks that an off-target joint query
leaves `LD` unchanged and has an independent key from a subsequent target query. A randomized
challenge-aware client checks the public averaged theorem.
-/

public section

namespace CslibFrontierTests.SaltedFOCorrectness

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open scoped ENNReal

/-- Boolean explicit-coin PKE with failure exactly when the sampled coin is `true`. -/
noncomputable def halfErrorPKE : ExplicitCoinPKE Unit Unit Bool Bool Bool where
  keyGen := pure ((), ())
  sampleCoins := ProbComp.uniform Bool
  encDet _ message coins := message ^^ coins
  dec _ ciphertext := some ciphertext

/-- Each message has one failing coin among the two uniform Boolean coins. -/
theorem halfErrorPKE_msgFailProb (message : Bool) :
    halfErrorPKE.msgFailProb () () message = 1 / 2 := by
  cases message <;>
    simp [ExplicitCoinPKE.msgFailProb, halfErrorPKE, Set.indicator,
      PMF.uniformOfFintype_apply, Fintype.card_bool]

theorem halfErrorPKE_keyPairMaxFailProb :
    halfErrorPKE.keyPairMaxFailProb () () = 1 / 2 := by
  rw [ExplicitCoinPKE.keyPairMaxFailProb]
  simp [halfErrorPKE_msgFailProb]

/-- The fixture's expected worst-message failure is exactly `1 / 2`. -/
theorem halfErrorPKE_deltaCorrect_half : halfErrorPKE.DeltaCorrect (1 / 2) := by
  have hkg : halfErrorPKE.keyGen = pure ((), ()) := rfl
  simp [ExplicitCoinPKE.DeltaCorrect, hkg, halfErrorPKE_keyPairMaxFailProb]

/-- Concrete salted-FO handler fixture backed by `halfErrorPKE`. -/
noncomputable def halfErrorScheme :
    Scheme Unit Unit Bool Bool Bool Unit Bool Unit Unit Unit where
  pke := halfErrorPKE
  sampleKey := pure ()
  jointPrefix _ := ()
  rejectionPrefix _ := ()
  rejectionSecret _ := ()

/-! ### Connected nonzero-error handler clients -/

abbrev HalfQuery := Query Unit Bool Bool Unit Unit Bool
abbrev HalfResponse := Response (JointPrefix := Unit) (M := Bool) (Salt := Bool)
  (RejectPrefix := Unit) (Sigma := Unit) (CT := Bool) Unit Bool
abbrev HalfState := CacheState Unit Bool Bool Unit Unit Bool Unit Bool

noncomputable def halfJointInput : JointInput Unit Bool Bool :=
  halfErrorScheme.jointInput () false false

def halfCiphertext : Ciphertext Bool Bool := ⟨false, false⟩

def halfChallenge : Ciphertext Bool Bool := ⟨true, true⟩

/-- This client consumes both projections of one fused reply. The projections have distinct types,
so reversing the source order is rejected rather than hidden by a symmetric Boolean predicate. -/
noncomputable def halfDirectProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.joint halfJointInput)
  return (reply.key == ()) && (reply.coins == false)

/-- The decapsulation-only client exercises the concrete real decrypt/re-encrypt path and the
keyless patched-cache path with no external joint query. -/
def halfDecapsProgram : OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query (Query.decaps halfCiphertext)
  return reply.isSome

/-- A nontrivial completion client: decapsulation prefetches the decoded joint coordinate in the
proof-only world, then a direct query consumes both the cached key and coin. -/
noncomputable def halfDecapsThenJointProgram : OracleComp HalfResponse Bool := do
  let decapsReply ← OracleComp.query (Query.decaps halfCiphertext)
  let jointReply ← OracleComp.query (Query.joint halfJointInput)
  return (decapsReply == some jointReply.key) && (jointReply.coins == false)

theorem halfDirectProgram_bounds : QueryBounds halfDirectProgram 1 0 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.joint halfJointInput)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem halfDecapsProgram_bounds : QueryBounds halfDecapsProgram 0 1 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.decaps halfCiphertext)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem halfDecapsThenJointProgram_bounds : QueryBounds halfDecapsThenJointProgram 1 1 := by
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query (Query.decaps halfCiphertext)).bind fun _ =>
      (OracleComp.IsCostBounded.query (Query.joint halfJointInput)).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

/-- Local correctness-bad predicate for the connected fixture. -/
def halfBad (st : HalfState) : Prop := ¬halfErrorScheme.GoodCache () () st

/-- One direct joint query creates the concrete `CORR` witness with probability exactly `1 / 2`.
This is the nonvacuous `(qRO,qD) = (1,0)` execution. -/
theorem halfDirect_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.joint halfJointInput)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = ENNReal.ofReal (1 / 2 : ℝ) := by
  simpa only [halfBad, halfErrorScheme, halfJointInput, halfErrorPKE_msgFailProb] using
    (halfErrorScheme.realHandler_joint_bad_eq_msgFailProb () () halfChallenge halfJointInput
      (st := ({} : HalfState)) (by simp) rfl (by simp [halfJointInput, Scheme.jointInput]))

/-- One nonchallenge decapsulation performs the implicit joint lookup and creates the same
concrete witness with probability exactly `1 / 2`. This is the nonvacuous `(0,1)` execution. -/
theorem halfDecaps_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.decaps halfCiphertext)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = ENNReal.ofReal (1 / 2 : ℝ) := by
  simpa only [halfBad, halfErrorScheme, halfErrorPKE_msgFailProb] using
    (halfErrorScheme.realHandler_decaps_bad_eq_msgFailProb () () halfChallenge
      halfCiphertext false (st := ({} : HalfState))
        (by simp [halfCiphertext, halfChallenge]) (by simp) rfl rfl)

/-- Direct-query execution under the real concrete handler. -/
noncomputable def halfDirectReal : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
    halfDirectProgram).run ({} : HalfState)).map Prod.fst

/-- Direct-query execution under the keyless concrete handler. -/
noncomputable def halfDirectSimulated : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
    halfDirectProgram).run ({} : HalfState)).map Prod.fst

/-- Decapsulation-only execution under the real concrete handler. -/
noncomputable def halfDecapsReal : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
    halfDecapsProgram).run ({} : HalfState)).map Prod.fst

/-- Decapsulation-only execution under the keyless concrete handler. -/
noncomputable def halfDecapsSimulated : PMF Bool :=
  ((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
    halfDecapsProgram).run ({} : HalfState)).map Prod.fst

/-- The concrete direct-query hop uses the direct `qRO` coefficient and the fixture's exact
fixed-key error `1 / 2`. -/
theorem halfDirectConcrete_closeTo :
    CloseTo halfDirectReal halfDirectSimulated
      (((1 + 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfDirectReal, halfDirectSimulated, halfErrorScheme,
    halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge halfDirectProgram
      halfDirectProgram_bounds)

/-- The concrete decapsulation-only hop uses the independent `qD` coefficient. -/
theorem halfDecapsConcrete_closeTo :
    CloseTo halfDecapsReal halfDecapsSimulated
      (((0 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfDecapsReal, halfDecapsSimulated, halfErrorScheme,
    halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge halfDecapsProgram
      halfDecapsProgram_bounds)

/-- The decaps-then-joint client checks the completion-valued relation rather than equality of
the private lazy caches. -/
example :
    CloseTo
      (((OracleComp.interpret (halfErrorScheme.realHandler () () halfChallenge)
        halfDecapsThenJointProgram).run ({} : HalfState)).map Prod.fst)
      (((OracleComp.interpret (halfErrorScheme.simHandler () halfChallenge)
        halfDecapsThenJointProgram).run ({} : HalfState)).map Prod.fst)
      (((1 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ)) := by
  simpa only [halfErrorScheme, halfErrorPKE_keyPairMaxFailProb] using
    (halfErrorScheme.closeTo_run_realHandler_simHandler () () halfChallenge
      halfDecapsThenJointProgram halfDecapsThenJointProgram_bounds)

/-- Challenge decapsulation is rejected by the dispatcher before either concrete decapsulation
implementation changes its caches. -/
example (st : HalfState) :
    halfErrorScheme.realHandler () () halfChallenge (Query.decaps halfChallenge) st =
      PMF.pure (none, st) := by
  exact halfErrorScheme.realHandler_decaps_challenge () () halfChallenge st

noncomputable def halfRejectionInput : RejectionInput Unit Unit Bool Bool :=
  halfErrorScheme.rejectionInput () () halfCiphertext

/-- The post-secret-seed-guessing `J` query is executed by the concrete handler and cannot
create a local PKE correctness witness. -/
theorem halfRejection_bad_probability :
    (halfErrorScheme.realHandler () () halfChallenge (Query.rejection halfRejectionInput)
      ({} : HalfState)).toOuterMeasure {z | halfBad z.2} = 0 := by
  simpa only [halfBad] using
    (halfErrorScheme.realHandler_rejection_bad_eq_zero () () halfChallenge halfRejectionInput
      (st := ({} : HalfState)) (by simp))

/-- `J` remains a distinct source-shaped query and costs nothing in the correctness accounting. -/
example : Query.jointCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

example : Query.decapsCost (Query.rejection halfRejectionInput : HalfQuery) = 0 := rfl

/-! The private fixture below guards the distinction between the target `LD` coordinate and an
off-target fused-oracle key. Both queries use the same message, salt and derived ciphertext. -/

private noncomputable def boolPrefixPKE : ExplicitCoinPKE Unit Unit Unit Unit Unit where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ _ _ := ()
  dec _ _ := some ()

private noncomputable def boolPrefixScheme :
    Scheme Unit Unit Unit Unit Unit Bool Unit Unit Unit Bool where
  pke := boolPrefixPKE
  sampleKey := ProbComp.uniform Bool
  jointPrefix _ := false
  rejectionPrefix _ := ()
  rejectionSecret _ := ()

private abbrev BoolPrefixState := CacheState Bool Unit Unit Unit Unit Unit Bool Unit

private noncomputable def boolTargetInput : JointInput Bool Unit Unit :=
  boolPrefixScheme.jointInput () () ()

private noncomputable def boolOffTargetInput : JointInput Bool Unit Unit :=
  { boolTargetInput with keyPrefix := !boolTargetInput.keyPrefix }

private noncomputable def boolOffTargetThenTargetRun : PMF (Bool × BoolPrefixState) :=
  (boolPrefixScheme.cacheJoint () (fun _ _ => True) boolOffTargetInput {}).bind fun offTarget =>
    (boolPrefixScheme.cacheJoint () (fun _ _ => True) boolTargetInput offTarget.2).map fun target =>
      (offTarget.1.key == target.1.key, target.2)

private noncomputable def boolOffTargetState (key : Bool) : BoolPrefixState :=
  { jointCache := [(boolOffTargetInput, ⟨key, ()⟩)] }

private noncomputable def boolTargetState (offTarget target : Bool) : BoolPrefixState :=
  { jointCache :=
      [(boolTargetInput, ⟨target, ()⟩), (boolOffTargetInput, ⟨offTarget, ()⟩)]
    decapsCache := [(⟨(), ()⟩, target)] }

private theorem boolOffTarget_run :
    (boolPrefixScheme.cacheJoint () (fun _ _ => True) boolOffTargetInput)
        ({} : BoolPrefixState) =
      (PMF.uniformOfFintype Bool).map fun key =>
        (⟨key, ()⟩, boolOffTargetState key) := by
  have hoff : boolOffTargetInput ≠
      boolPrefixScheme.jointInput () boolOffTargetInput.message boolOffTargetInput.salt := by
    rw [show boolOffTargetInput.message = () from Subsingleton.elim _ _]
    rw [show boolOffTargetInput.salt = () from Subsingleton.elim _ _]
    change boolOffTargetInput ≠ boolTargetInput
    unfold boolOffTargetInput
    intro h
    have hprefix := congrArg JointInput.keyPrefix h
    apply Bool.not_ne_self boolTargetInput.keyPrefix
    simpa only using hprefix
  unfold Scheme.cacheJoint
  simp only [List.lookup_nil]
  simp only [ite_eq_right hoff]
  simp [boolPrefixScheme, boolPrefixPKE, boolOffTargetState]

private theorem boolTarget_run (offTarget : Bool) :
    (boolPrefixScheme.cacheJoint () (fun _ _ => True) boolTargetInput)
        (boolOffTargetState offTarget) =
      (PMF.uniformOfFintype Bool).map fun target =>
        (⟨target, ()⟩, boolTargetState offTarget target) := by
  have htarget : boolTargetInput =
      boolPrefixScheme.jointInput () boolTargetInput.message boolTargetInput.salt := by
    rw [show boolTargetInput.message = () from Subsingleton.elim _ _]
    rw [show boolTargetInput.salt = () from Subsingleton.elim _ _]
    rfl
  have hne : boolTargetInput ≠ boolOffTargetInput := by
    unfold boolOffTargetInput
    intro h
    have hprefix := congrArg JointInput.keyPrefix h
    apply Bool.not_ne_self boolTargetInput.keyPrefix
    simpa only using hprefix.symm
  unfold Scheme.cacheJoint
  simp only [boolOffTargetState, List.lookup_cons, beq_eq_false_iff_ne.mpr hne,
    List.lookup_nil]
  simp only [ite_eq_left htarget]
  simp [boolPrefixScheme, boolPrefixPKE, boolTargetState]

private theorem boolOffTarget_ld_unchanged :
    ((boolPrefixScheme.cacheJoint () (fun _ _ => True) boolOffTargetInput)
      ({} : BoolPrefixState)).map
        (fun z => z.2.decapsCache) = PMF.pure [] := by
  rw [boolOffTarget_run]
  rw [PMF.map_comp]
  exact PMF.map_const _ _

private theorem boolOffTargetThenTarget_law :
    boolOffTargetThenTargetRun.map Prod.fst =
      (PMF.uniformOfFintype Bool).bind fun offTarget =>
        (PMF.uniformOfFintype Bool).map fun target => offTarget == target := by
  rw [boolOffTargetThenTargetRun]
  rw [boolOffTarget_run, PMF.map_bind, PMF.bind_map]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro offTarget _
  rw [boolTarget_run]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

private theorem boolOffTargetThenTarget_probability :
    (boolOffTargetThenTargetRun.map Prod.fst) true = 1 / 2 := by
  rw [boolOffTargetThenTarget_law, PMF.bind_apply, tsum_bool]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, Bool.false_beq,
    PMF.map_apply, Bool.true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, tsum_fintype,
    Fintype.univ_bool, Finset.sum_ite_eq', Finset.mem_insert, Bool.false_eq_true,
    Finset.mem_singleton, or_true, ↓reduceIte, Bool.true_beq, or_false, one_div]
  rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-! ### Challenge-aware randomized client -/

/-- A genuinely randomized public challenge setup; both games sample this same law. -/
noncomputable def halfChallengeSetup (_ : Unit) :
    ProbComp (Ciphertext Bool Bool × Unit) := do
  let salt ← ProbComp.uniform Bool
  return (⟨true, salt⟩, ())

/-- Fixed-tape program that inspects all three public challenge fields. -/
def halfChallengeProgram (challenge : KEM.Challenge Unit (Ciphertext Bool Bool) Unit) :
    OracleComp HalfResponse Bool := do
  let reply ← OracleComp.query
    (Query.joint (⟨(), false, challenge.ct.salt⟩ : JointInput Unit Bool Bool))
  return (challenge.pk == ()) && (reply.key == challenge.key) &&
    (reply.coins == challenge.ct.salt)

/-- Explicit-coin adversary with a challenge-aware deterministic program on each tape. -/
noncomputable def halfRandomizedAdversary :
    RandomizedAdversary Unit Unit Bool Bool Unit Unit Bool Unit Bool where
  Coins := Unit
  coins := pure ()
  run _ challenge := halfChallengeProgram challenge

theorem halfRandomizedAdversary_bounded : halfRandomizedAdversary.QueryBounded 1 0 := by
  intro _ challenge
  change QueryBounds (halfChallengeProgram challenge) 1 0
  refine ⟨?_, ?_⟩ <;>
    exact (OracleComp.IsCostBounded.query
      (Query.joint (⟨(), false, challenge.ct.salt⟩ : JointInput Unit Bool Bool))).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

/-- The public randomized theorem accepts a full challenge-aware adversary and a common
randomized challenge setup without charging challenge construction as an oracle query. -/
example :
    (Game.advantage
      (halfErrorScheme.randomizedRealHandlerGame halfChallengeSetup halfRandomizedAdversary)
      (halfErrorScheme.randomizedSimHandlerGame halfChallengeSetup halfRandomizedAdversary) : ℝ) ≤
      ((1 + 0 : ℕ) : ℝ) * (1 / 2 : ℝ) := by
  exact halfErrorScheme.advantage_randomizedRealHandler_simHandler_le
    halfChallengeSetup halfRandomizedAdversary halfRandomizedAdversary_bounded
    halfErrorPKE_deltaCorrect_half

end CslibFrontierTests.SaltedFOCorrectness
