/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Functional

/-!
# Tests for functional encryption schemes and their semantic-security experiment

Concrete checks for `Cslib.Crypto.FE`, `FE.Correct`, `FE.Robust`, `FE.ssExperiment`,
`FE.cleartext` and `PKE.toFE`:
- The cleartext scheme `FE.cleartext constLeak` is correct and robust for `constLeak`, and an
  adversary that reads the challenge ciphertext in the clear wins `FE.ssExperiment` with advantage
  `1` when the null function is constant, whereas an injective null function forces advantage `0`
  for every adversary (Remark 15.13).
- Pre- and post-challenge key queries (`askFirst`, `askLast`) are logged and checked by
  `Functionality.admissible`: an admissible query (`blind`) leaves the experiment law `PMF.pure b`,
  whereas a query that distinguishes the challenge messages (`reveal`) forces `PMF.pure false` in
  both stages.
- A scheme whose full key and null key disagree on a ciphertext is not `FE.Robust`.
- For the identity public-key scheme on bits, `idPKE.toFE id` is correct for `Functionality.pke id`,
  is not correct for `Functionality.pke not`, and has the same semantic-security experiment law
  against a two-stage adversary without key queries as `idPKE.cpaExperiment`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FunctionalEncryption

open Cslib Cslib.Crypto Cslib.Crypto.FE Cslib.Probability

/-- A functionality whose null function is constant on `Bool`. -/
abbrev constLeak : Functionality (Option Unit) Bool (Bool ⊕ Unit) :=
  Functionality.pke fun _ => ()

-- The cleartext scheme is correct and robust for `constLeak`.
example : (cleartext constLeak).Correct constLeak ∧ (cleartext constLeak).Robust constLeak :=
  ⟨cleartext_correct constLeak, cleartext_robust constLeak⟩

/-- The adversary that submits `(false, true)`, asks for no key and outputs the challenge. -/
abbrev readChallenge : Adversary Unit (Option Unit) (Option Unit) Bool Bool Unit :=
  Adversary.ofTwoStage ⟨fun _ => pure (⟨false, true⟩, ()), fun _ c => pure c⟩

/-- Against the cleartext scheme that adversary's experiment `b` outputs `b`. -/
theorem eval_ssExperiment_cleartext_readChallenge (b : Bool) :
    ProbComp.eval ((cleartext constLeak).ssExperiment constLeak readChallenge b) = PMF.pure b := by
  cases b <;>
    simp [ssExperiment, cleartext, Adversary.ofTwoStage, ProbOracleComp.runLog,
      Functionality.admissible, Functionality.pke]

-- The cleartext scheme hides nothing: with a constant null function the game is won outright.
example :
    Experiment.advantage ((cleartext constLeak).ssExperiment constLeak readChallenge false)
      ((cleartext constLeak).ssExperiment constLeak readChallenge true) = 1 := by
  simp [Experiment.advantage, eval_ssExperiment_cleartext_readChallenge, Game.succProbability]

-- With an injective null function the same scheme has advantage zero (Remark 15.13).
example (A : Adversary Unit (Option Unit) (Option Unit) Bool Bool Unit) :
    Experiment.advantage
      ((cleartext (Functionality.pke (id : Bool → Bool))).ssExperiment (Functionality.pke id)
        A false)
      ((cleartext (Functionality.pke (id : Bool → Bool))).ssExperiment (Functionality.pke id)
        A true) = 0 :=
  advantage_ssExperiment_pke_eq_zero _ Function.injective_id A

/-- A scheme whose two keys read one ciphertext inconsistently: the full key returns `c`, the null
key returns `!c`. -/
def inconsistent : FE Unit Unit (Option Unit) (Option Unit) Bool Bool (Bool ⊕ Bool) where
  setup := pure ((), ())
  keyGen _ f := pure f
  encrypt _ m := pure m
  decrypt f c := match f with
    | some _ => some (Sum.inl c)
    | none => some (Sum.inr (!c))

-- Robustness is not vacuous: `inconsistent` is not robust for the functionality that reveals
-- the message under both identifiers.
example : ¬ inconsistent.Robust (Functionality.pke id) := by
  intro h
  obtain ⟨m, hm⟩ := h ((), ()) (by simp [inconsistent]) true
  have h₁ := hm (some ()) (some ()) (by simp [inconsistent]) (Sum.inl true) rfl (Sum.inl m) rfl
  have h₂ := hm none none (by simp [inconsistent]) (Sum.inr false) rfl (Sum.inr m) rfl
  cases m <;> simp_all

/-- The public-key scheme on bits that encrypts by the identity. -/
def idPKE : PKE Unit Unit Bool Bool where
  keyGen := pure ((), ())
  encrypt _ m := pure m
  decrypt _ c := some c

-- Example 15.1 on `idPKE`: with the leakage read correctly, `toFE` is correct.
example : (idPKE.toFE id).Correct (Functionality.pke id) := by
  refine (idPKE.toFE_correct_iff id id).2 ⟨?_, ?_⟩
  · intro keys _ m c hc
    simp only [idPKE, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
    simp [idPKE, hc]
  · intro keys _ m c hc
    simpa [idPKE] using hc

-- With a null key that reads the wrong leakage, `toFE` is not correct.
example : ¬ (idPKE.toFE id).Correct (Functionality.pke not) := by
  intro h
  have := ((idPKE.toFE_correct_iff not id).1 h).2 ((), ()) (by simp [idPKE]) true true
    (by simp [idPKE])
  simp at this

-- Without key queries the game of `toFE` is the chosen-plaintext game.
example (A : TwoStage Unit (MessagePair Bool) Bool Bool Unit) (b : Bool) :
    ProbComp.eval ((idPKE.toFE id).ssExperiment (Functionality.pke id)
        (Adversary.ofTwoStage A) b) =
      ProbComp.eval (idPKE.cpaExperiment (fun _ m₀ m₁ => decide (id m₀ = id m₁)) A b) :=
  idPKE.eval_ssExperiment_toFE_ofTwoStage id id A b

/-- Null function `⊥` everywhere; the other identifier reveals nothing. -/
def blind : Functionality (Option Unit) Bool Bool where
  eval f _ := f.map fun _ => true
  null := none

/-- Null function `⊥` everywhere; the other identifier reveals the message. -/
def reveal : Functionality (Option Unit) Bool Bool where
  eval f m := f.map fun _ => m
  null := none

/-- Asks for the key of `some ()` before the challenge, submits `(false, true)`, and outputs the
challenge. -/
def askFirst : Adversary Unit (Option Unit) (Option Unit) Bool Bool Unit where
  choose _ _ := do
    let _ ← ProbOracleComp.query (spec := fun _ : Option Unit => Option Unit) (some ())
    return (⟨false, true⟩, ())
  guess _ c := pure c

/-- Submits `(false, true)`, asks for the key of `some ()` after the challenge, and outputs the
challenge. -/
def askLast : Adversary Unit (Option Unit) (Option Unit) Bool Bool Unit where
  choose _ _ := pure (⟨false, true⟩, ())
  guess _ c := do
    let _ ← ProbOracleComp.query (spec := fun _ : Option Unit => Option Unit) (some ())
    return c

-- An admissible key query before the challenge succeeds with law `PMF.pure b`.
example (b : Bool) :
    ProbComp.eval ((cleartext blind).ssExperiment blind askFirst b) = PMF.pure b := by
  simp only [ssExperiment, cleartext, blind, ProbOracleComp.runLog, askFirst, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    MessagePair.select, cond_eq_ite, ProbOracleComp.runState_pure, StateT.run_pure,
    Functionality.admissible, List.map_append, decide_true, List.all_cons, List.all_append,
    List.all_map, Function.true_comp, Bool.true_and, List.all_nil, Bool.and_true, Functor.map_map,
    Bool.ite_false_right, Bool.decide_eq_true, pure_bind, ProbComp.eval_map]
  cases b <;> simp [StateT.run]

-- An admissible key query after the challenge succeeds with law `PMF.pure b`.
example (b : Bool) :
    ProbComp.eval ((cleartext blind).ssExperiment blind askLast b) = PMF.pure b := by
  simp only [ssExperiment, cleartext, blind, ProbOracleComp.runLog, askLast, bind_pure_comp,
    map_pure, ProbOracleComp.runState_pure, StateT.run_pure, MessagePair.select, cond_eq_ite,
    ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functionality.admissible, List.map_append, decide_true, List.all_cons, List.all_append,
    List.all_map, Function.true_comp, Bool.true_and, Functor.map_map, pure_bind,
    Bool.ite_false_right, Bool.decide_eq_true, Bool.and_true, List.all_nil, ProbComp.eval_map]
  cases b <;> simp [StateT.run]

-- A key query before the challenge that distinguishes the messages makes the experiment output
-- `false`.
example (b : Bool) :
    ProbComp.eval ((cleartext reveal).ssExperiment reveal askFirst b) = PMF.pure false := by
  simp only [ssExperiment, cleartext, reveal, ProbOracleComp.runLog, askFirst, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    MessagePair.select, cond_eq_ite, ProbOracleComp.runState_pure, StateT.run_pure,
    Functionality.admissible, List.map_append, List.all_cons, Option.map_none, decide_true,
    List.all_append, List.all_map, Bool.true_and, List.all_nil, Bool.and_true, Functor.map_map,
    Bool.ite_false_right, Bool.decide_eq_true, pure_bind, ProbComp.eval_map]
  cases b <;> simp [StateT.run]

-- A key query after the challenge that distinguishes the messages makes the experiment output
-- `false`.
example (b : Bool) :
    ProbComp.eval ((cleartext reveal).ssExperiment reveal askLast b) = PMF.pure false := by
  simp only [ssExperiment, cleartext, reveal, ProbOracleComp.runLog, askLast, bind_pure_comp,
    map_pure, ProbOracleComp.runState_pure, StateT.run_pure, MessagePair.select, cond_eq_ite,
    ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functionality.admissible, List.map_append, List.all_cons, Option.map_none, decide_true,
    List.all_append, List.all_map, Bool.true_and, Functor.map_map, pure_bind, Bool.ite_false_right,
    Bool.decide_eq_true, Bool.and_true, List.all_nil, ProbComp.eval_map]
  cases b <;> simp [StateT.run]

end CslibFrontierTests.Crypto.FunctionalEncryption
