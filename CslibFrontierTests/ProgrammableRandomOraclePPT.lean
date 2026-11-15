/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Probabilistic.RandomOracle.Programming
public import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max

/-! An ordinary adaptive client of both native programmable-random-oracle worlds. -/

public section

namespace CslibFrontierTests.ProgrammableRandomOraclePPT

open Cslib Cslib.Probability Cslib.RandomOracle Turing.MultiTapeTM

abbrev Log := List (List Bool × List Bool)

abbrev encLog : Log ↪ List Bool := encMemoCache encBits encBits

/-- Program once, then make an answer-dependent direct hash query. -/
noncomputable def client (_ : ℕ) (input : List Bool) :
    WordOracleComp ProgrammingOp Bool := do
  let programmed ← List.take 1 <$> ProbOracleComp.query (.program, input)
  let digest ← List.take 1 <$> ProbOracleComp.query (.hash, input ++ programmed)
  return digest == programmed

theorem client_isOraclePPT : IsOraclePPT encBool client := by
  ppt [client]

noncomputable def dist (_ : List Bool) : ProbComp (List Bool) :=
  BitString.sampleList 1

def active (_ _ : List Bool) : Bool := true

noncomputable def inactive (_ request : List Bool) (log : Log) :
    ProbComp (List Bool × Log) := pure (request.take 1, log)

noncomputable def samplePre (_ _ : List Bool) : ProbComp (List Bool) :=
  BitString.sampleList 1

def point (_ request coins : List Bool) : List Bool := request ++ coins

def finish (_ request coins digest : List Bool) (log : Log) : List Bool × Log :=
  (digest ++ coins, (request, digest) :: log)

def initial (_ : List Bool) : ProgrammingState Log := ⟨[], []⟩

theorem dist_ppt : IsPPTOn encBits encBits dist := by
  unfold dist
  fun_prop

theorem inactive_ppt : IsPPTOn (encPair (encPair encBits encBits) encLog)
    (encPair encBits encLog) (fun p => inactive p.1.1 p.1.2 p.2) := by
  unfold inactive
  fun_prop

theorem samplePre_ppt : IsPPTOn (encPair encBits encBits) encBits
    (fun p => samplePre p.1 p.2) := by
  unfold samplePre
  fun_prop

theorem point_polyTime : ComputableInPolyTime
    (fun p : (List Bool × List Bool) × List Bool => point p.1.1 p.1.2 p.2)
    (encPair (encPair encBits encBits) encBits) encBits := by
  unfold point
  fun_prop

theorem finish_polyTime : ComputableInPolyTime
    (fun p : ((((List Bool × List Bool) × List Bool) × List Bool) × Log) =>
      finish p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair (encPair encBits encBits) encBits) encBits) encLog)
    (encPair encBits encLog) := by
  unfold finish Log encLog
  fun_prop

theorem lazyHandler_ppt : IsPPTOn
    (encHandlerCall encBits encProgrammingOp (encProgrammingState Log encLog))
    (encPair encBits (encProgrammingState Log encLog))
    (fun p => lazyProgramWordHandler dist active inactive samplePre point finish
      p.1 p.2.1 p.2.2) := by
  apply isPPTOn_lazyProgramWordHandler encBits encLog dist active inactive samplePre point finish
    dist_ppt
  · unfold active
    fun_prop
  · exact inactive_ppt
  · exact samplePre_ppt
  · exact point_polyTime
  · exact finish_polyTime

theorem overwriteHandler_ppt : IsPPTOn
    (encHandlerCall encBits encProgrammingOp (encProgrammingState Log encLog))
    (encPair encBits (encProgrammingState Log encLog))
    (fun p => overwriteProgramWordHandler dist active inactive samplePre point finish
      p.1 p.2.1 p.2.2) := by
  apply isPPTOn_overwriteProgramWordHandler encBits encLog dist active inactive samplePre point
    finish dist_ppt
  · unfold active
    fun_prop
  · exact inactive_ppt
  · exact samplePre_ppt
  · exact point_polyTime
  · exact finish_polyTime

private def pointBound (_ request : List Bool) : ℕ := request.length + 1

private def replyBound (_ _ : List Bool) : ℕ := 2

private def logGrowth (_ request : List Bool) : ℕ := 4 * request.length + 5

private theorem dist_support (caller digest : List Bool)
    (h : digest ∈ (ProbComp.eval (dist caller)).support) : digest.length ≤ 1 := by
  rw [dist, BitString.eval_sampleList] at h
  exact (BitString.length_of_mem_support_uniformList h).le

private theorem point_support (caller request coins : List Bool)
    (h : coins ∈ (ProbComp.eval (samplePre caller request)).support) :
    (point caller request coins).length ≤ pointBound caller request := by
  rw [samplePre, BitString.eval_sampleList] at h
  simp [point, pointBound, BitString.length_of_mem_support_uniformList h]

private theorem inactive_support (caller request : List Bool) (log : Log) (_ : True)
    (result : List Bool × Log)
    (h : result ∈ (ProbComp.eval (inactive caller request log)).support) :
    True ∧ result.1.length ≤ replyBound caller request ∧
      (encLog result.2).length ≤ (encLog log).length + logGrowth caller request := by
  simp only [inactive, ProbComp.eval_pure, PMF.mem_support_pure_iff] at h
  subst result
  simp [replyBound, logGrowth]

private theorem finish_support (caller request coins : List Bool)
    (hcoins : coins ∈ (ProbComp.eval (samplePre caller request)).support)
    (digest : List Bool) (hdigest : digest.length ≤ 1) (log : Log) (_ : True) :
    True ∧ (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
      (encLog (finish caller request coins digest log).2).length ≤
        (encLog log).length + logGrowth caller request := by
  rw [samplePre, BitString.eval_sampleList] at hcoins
  have hcoinsLength := BitString.length_of_mem_support_uniformList hcoins
  simp only [finish, replyBound, encLog, encMemoCache, encList_cons, List.length_append,
    length_frame, length_encPair, encBits_apply, logGrowth]
  constructor
  · trivial
  constructor <;> lia

-- A source adapter can take a finite maximum of the opaque shared allowance.
example : ComputableInPolyTime (fun p : List Bool × List Bool =>
    max
      (programmingResources (fun _ => 1) pointBound replyBound logGrowth p.1 (false :: p.2))
      (programmingResources (fun _ => 1) pointBound replyBound logGrowth p.1 (true :: p.2)))
    (encPair encBits encBits) encUnary := by
  have hshared : ComputableInPolyTime (fun p : List Bool × List Bool =>
      programmingResources (fun _ => 1) pointBound replyBound logGrowth p.1 p.2)
      (encPair encBits encBits) encUnary := by
    apply computableInPolyTime_programmingResources encBits (fun _ => 1) pointBound replyBound
      logGrowth
    · fun_prop
    · unfold pointBound
      fun_prop
    · unfold replyBound
      fun_prop
    · unfold logGrowth
      fun_prop
  have hfalse : ComputableInPolyTime
      (fun p : List Bool × List Bool => (p.1, false :: p.2))
      (encPair encBits encBits) (encPair encBits encBits) := by fun_prop
  have htrue : ComputableInPolyTime
      (fun p : List Bool × List Bool => (p.1, true :: p.2))
      (encPair encBits encBits) (encPair encBits encBits) := by fun_prop
  exact ComputableInPolyTime.unary_max' (hshared.comp hfalse) (hshared.comp htrue)

-- The per-call contract is usable through an ordinary module without exposing its definitions.
example (caller : List Bool) (request : ProgrammingOp × List Bool)
    (state : ProgrammingState Log)
    (hcache : ∀ entry ∈ state.cache, entry.2.length ≤ 1)
    (result : List Bool × ProgrammingState Log)
    (hresult : result ∈ (ProbComp.eval (lazyProgramWordHandler dist active inactive samplePre
      point finish caller request state)).support) :
    ProgrammingInvariant (fun _ => 1) (fun _ _ => True) caller result.2 ∧
      result.1.length ≤
        programmingResources (fun _ => 1) pointBound replyBound logGrowth caller request.2 ∧
      (encProgrammingState Log encLog result.2).length ≤
        (encProgrammingState Log encLog state).length +
          programmingResources (fun _ => 1) pointBound replyBound logGrowth caller request.2 :=
  lazyProgramWordHandler_support encLog dist active inactive samplePre point finish (fun _ => 1)
    pointBound replyBound logGrowth (fun _ _ => True) dist_support point_support inactive_support
    finish_support caller request state
      (ProgrammingInvariant.intro (fun _ => 1) (fun _ _ => True) caller state hcache True.intro)
    result hresult

theorem lazyRun_ppt : IsPPTOn encBits
    (encPair encBool (encProgrammingState Log encLog))
    (fun input => ((client input.length input).runState
      (lazyProgramWordHandler dist active inactive samplePre point finish input)).run
        (initial input)) := by
  apply isPPTOn_run_lazyProgramWordHandler encBits encBool encLog client dist active inactive
    samplePre point finish (fun input => (input.length, input)) initial (fun _ => 1)
    pointBound replyBound logGrowth (fun _ _ => True) client_isOraclePPT
    (by fun_prop) lazyHandler_ppt (by unfold initial; fun_prop)
  · fun_prop
  · unfold pointBound
    fun_prop
  · unfold replyBound
    fun_prop
  · unfold logGrowth
    fun_prop
  · exact dist_support
  · exact point_support
  · exact inactive_support
  · exact finish_support
  · simp [initial]
  · intro
    trivial

theorem overwriteRun_ppt : IsPPTOn encBits
    (encPair encBool (encProgrammingState Log encLog))
    (fun input => ((client input.length input).runState
      (overwriteProgramWordHandler dist active inactive samplePre point finish input)).run
        (initial input)) := by
  apply isPPTOn_run_overwriteProgramWordHandler encBits encBool encLog client dist active inactive
    samplePre point finish (fun input => (input.length, input)) initial (fun _ => 1)
    pointBound replyBound logGrowth (fun _ _ => True) client_isOraclePPT
    (by fun_prop) overwriteHandler_ppt (by unfold initial; fun_prop)
  · fun_prop
  · unfold pointBound
    fun_prop
  · unfold replyBound
    fun_prop
  · unfold logGrowth
    fun_prop
  · exact dist_support
  · exact point_support
  · exact inactive_support
  · exact finish_support
  · simp [initial]
  · intro
    trivial

theorem lazy_semantics :
    (ProbOracleComp.runWith
      (lazyProgramHandler (ProbComp.eval (dist [])) (active [])
        (fun request _ log => ProbComp.eval (inactive [] request log))
        (fun request => ProbComp.eval (samplePre [] request)) (point []) (finish []))
      (programmingCodec.adapt (client 0 [])) ([], [])).map
        (fun ⟨result, cache, log⟩ =>
          (result, (⟨cache, log⟩ : ProgrammingState Log))) =
      ProbOracleComp.runWith
        (fun request state => ProbComp.eval (lazyProgramWordHandler dist active inactive samplePre
          point finish [] request state)) (client 0 []) (initial []) :=
  runWith_lazyProgramWordHandler (client 0 []) dist active inactive samplePre point finish [] [] []

theorem overwrite_semantics :
    (ProbOracleComp.runWith
      (overwriteProgramHandler (ProbComp.eval (dist [])) (active [])
        (fun request _ log => ProbComp.eval (inactive [] request log))
        (fun request => ProbComp.eval (samplePre [] request)) (point []) (finish []))
      (programmingCodec.adapt (client 0 [])) ([], [])).map
        (fun ⟨result, cache, log⟩ =>
          (result, (⟨cache, log⟩ : ProgrammingState Log))) =
      ProbOracleComp.runWith
        (fun request state => ProbComp.eval (overwriteProgramWordHandler dist active inactive
          samplePre point finish [] request state)) (client 0 []) (initial []) :=
  runWith_overwriteProgramWordHandler (client 0 []) dist active inactive samplePre point finish
    [] [] []

end CslibFrontierTests.ProgrammableRandomOraclePPT
