/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.RunState
public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Native strict-PPT programmable random oracles

This module implements the two semantic programming handlers from
`Languages.Probabilistic.RandomOracle.Programming` as word programs. One state stores the
memoized word random oracle together with arbitrary caller-defined log data. The exact per-call
laws retain the reply, cache and log jointly, so the semantic programming bounds apply without a
second probability argument.

The local resource contract separately bounds cached digest words and caller log growth. It is
stronger than polynomial time of each call: repeated calls may not multiply the encoded state.
The resulting certificates are uniform in the caller's runtime data. They do not charge a
parameter-dependent static program or machine description; concrete families with installed
program occurrences need an additional `OracleTM`-level description-size argument.

This is the plain-word specialization of the semantic handlers: requests, replies, coins,
queries and digests are words. The native `inactive` callback omits the semantic proof argument
`active request = false`; the semantic laws instantiate it as `fun request _ log => ...`.

## Main definitions

* `Cslib.RandomOracle.ProgrammingOp`, `Cslib.RandomOracle.encProgrammingOp`,
  `Cslib.RandomOracle.programmingCodec`: the programming and direct-hash word channels, their
  unary tag encoding and their typed view.
* `Cslib.RandomOracle.ProgrammingState`, `Cslib.RandomOracle.encProgrammingState`: one memoized
  word table together with an arbitrary encoded caller log.
* `Cslib.RandomOracle.lazyProgramWordHandler`,
  `Cslib.RandomOracle.overwriteProgramWordHandler`: executable closed handlers for the lazy and
  freshly programmed worlds.
* `Cslib.RandomOracle.ProgrammingInvariant`,
  `Cslib.RandomOracle.programmingResources`: the opaque state invariant and shared additive
  allowance used by source-operation adapters and whole-program certificates.

## Main results

* `Cslib.RandomOracle.eval_lazyProgramWordHandler`,
  `Cslib.RandomOracle.eval_overwriteProgramWordHandler`: exact joint per-call laws identifying the
  native handlers with `lazyProgramHandler` and `overwriteProgramHandler`.
* `Cslib.RandomOracle.runWith_lazyProgramWordHandler`,
  `Cslib.RandomOracle.runWith_overwriteProgramWordHandler`: exact adaptive whole-run laws.
* `Cslib.RandomOracle.isPPTOn_lazyProgramWordHandler`,
  `Cslib.RandomOracle.isPPTOn_overwriteProgramWordHandler`: strict-PPT call certificates.
* `Cslib.RandomOracle.computableInPolyTime_programmingResources`,
  `Cslib.RandomOracle.lazyProgramWordHandler_support`: polynomial-time computation of the shared
  allowance, invariant preservation and additive encoded-state growth for supported lazy-handler
  calls.
* `Cslib.RandomOracle.isPPTOn_run_lazyProgramWordHandler`,
  `Cslib.RandomOracle.isPPTOn_run_overwriteProgramWordHandler`: whole-program strict-PPT
  certificates derived from an adversary certificate and the additive state contract.
-/

public section

namespace Cslib.RandomOracle

open Probability Turing.MultiTapeTM

/-- The two word operations of a programmable random oracle. `program` runs the caller-defined
programming action; `hash` reads the memoized random oracle directly. -/
inductive ProgrammingOp where
  /-- Run the programming action. -/
  | program
  /-- Query the random oracle directly. -/
  | hash
  deriving DecidableEq

instance : FinEnum ProgrammingOp :=
  FinEnum.ofList [.program, .hash] (by intro op; cases op <;> simp)

/-- Unary-rank encoding of the two operations: `program` has rank zero and `hash` rank one. -/
abbrev encProgrammingOp : ProgrammingOp ↪ List Bool := encFinEnum ProgrammingOp

/-- Typed programming requests (`.inl`) and direct hash queries (`.inr`) on the two named word
channels. Replies on both channels are words. -/
def programmingCodec :
    OracleCodec ProgrammingOp (List Bool ⊕ List Bool)
      ((fun _ : List Bool => List Bool) ⊕ₒ fun _ : List Bool => List Bool) where
  encodeQuery
    | .inl request => (.program, request)
    | .inr query => (.hash, query)
  decodeQuery
    | (.program, request) => some (.inl request)
    | (.hash, query) => some (.inr query)
  decodeQuery_eq_some_iff request query := by
    rcases request with ⟨op, word⟩
    cases op <;> cases query <;> simp [eq_comm]
  encodeReply
    | .inl _ => Function.Embedding.refl _
    | .inr _ => Function.Embedding.refl _

/-- Native state of a programmable word random oracle: an association-list cache of query/digest
words and an arbitrary caller log. -/
structure ProgrammingState (Log : Type) where
  /-- Memoized query/digest words. The first occurrence of a query is authoritative. -/
  cache : List (List Bool × List Bool)
  /-- Caller-defined data updated by programming requests. -/
  log : Log

/-- Encoding of a programmable state: the framed cache encoding followed by the caller log.
Each cache entry contains its framed query word followed by its digest word. -/
enc_structure encProgrammingState (Log : Type) (encLog : Log ↪ List Bool) :
    ProgrammingState Log where
  cache : (encMemoCache encBits encBits), log : encLog

variable {Caller Log : Type}

/-- Executable lazy programmable word oracle. Active programming calls sample preimage coins,
query the memoized random oracle at the computed point and update the caller log. Inactive calls
run `inactive`; direct hash calls use the same cache. -/
def lazyProgramWordHandler
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (request : ProgrammingOp × List Bool) :
    StateT (ProgrammingState Log) ProbComp (List Bool) := fun state =>
  match request with
  | (.program, req) =>
      if active caller req then do
        let coins ← samplePre caller req
        let (digest, cache') ← memoize (fun _ => dist caller) (point caller req coins) state.cache
        let (reply, log') := finish caller req coins digest state.log
        return (reply, ⟨cache', log'⟩)
      else
        (inactive caller req state.log).map fun (reply, log') =>
          (reply, ⟨state.cache, log'⟩)
  | (.hash, query) =>
      (memoize (fun _ => dist caller) query state.cache).map fun (digest, cache') =>
        (digest, ⟨cache', state.log⟩)

/-- Executable freshly programmed word oracle. It differs from `lazyProgramWordHandler` only on
active programming calls, which sample a fresh digest and prepend the computed point without a
cache lookup. -/
def overwriteProgramWordHandler
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (request : ProgrammingOp × List Bool) :
    StateT (ProgrammingState Log) ProbComp (List Bool) := fun state =>
  match request with
  | (.program, req) =>
      if active caller req then do
        let coins ← samplePre caller req
        let digest ← dist caller
        let (reply, log') := finish caller req coins digest state.log
        return (reply, ⟨(point caller req coins, digest) :: state.cache, log'⟩)
      else
        (inactive caller req state.log).map fun (reply, log') =>
          (reply, ⟨state.cache, log'⟩)
  | (.hash, query) =>
      (memoize (fun _ => dist caller) query state.cache).map fun (digest, cache') =>
        (digest, ⟨cache', state.log⟩)

/-- A native lazy-programming call has exactly the joint reply/cache/log law of
`lazyProgramHandler`, through `programmingCodec`. -/
theorem eval_lazyProgramWordHandler
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (request : ProgrammingOp × List Bool) (state : ProgrammingState Log) :
    ProbComp.eval
        (lazyProgramWordHandler dist active inactive samplePre point finish caller request state) =
      (programmingCodec.wordOracle
        (lazyProgramHandler (ProbComp.eval (dist caller)) (active caller)
          (fun req _ log => ProbComp.eval (inactive caller req log))
          (fun req => ProbComp.eval (samplePre caller req)) (point caller) (finish caller)) request
          (state.cache, state.log)).map
        (fun ⟨reply, cache, log⟩ => (reply, ⟨cache, log⟩)) := by
  rcases request with ⟨op, word⟩
  cases op with
  | program =>
      by_cases hactive : active caller word = true
      · simp [lazyProgramWordHandler, lazyProgramHandler, programmingCodec,
          OracleCodec.wordOracle, hactive, ProbComp.eval_memoize,
          Function.Embedding.coe_refl, id_map, PMF.map, Function.comp_def]
      · have hfalse : active caller word = false := Bool.eq_false_iff.mpr hactive
        simp [lazyProgramWordHandler, lazyProgramHandler, programmingCodec,
          OracleCodec.wordOracle, hactive, Function.Embedding.coe_refl, id_map,
          PMF.map_comp, Function.comp_def]
  | hash =>
      simp [lazyProgramWordHandler, lazyProgramHandler, programmingCodec,
        OracleCodec.wordOracle, ProbComp.eval_memoize, Function.Embedding.coe_refl, id_map,
        PMF.map_comp, Function.comp_def]

/-- A native overwrite-programming call has exactly the joint reply/cache/log law of
`overwriteProgramHandler`, through `programmingCodec`. -/
theorem eval_overwriteProgramWordHandler
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (request : ProgrammingOp × List Bool) (state : ProgrammingState Log) :
    ProbComp.eval (overwriteProgramWordHandler dist active inactive samplePre point finish caller
        request state) =
      (programmingCodec.wordOracle
        (overwriteProgramHandler (ProbComp.eval (dist caller)) (active caller)
          (fun req _ log => ProbComp.eval (inactive caller req log))
          (fun req => ProbComp.eval (samplePre caller req)) (point caller) (finish caller)) request
          (state.cache, state.log)).map
        (fun ⟨reply, cache, log⟩ => (reply, ⟨cache, log⟩)) := by
  rcases request with ⟨op, word⟩
  cases op with
  | program =>
      by_cases hactive : active caller word = true
      · simp [overwriteProgramWordHandler, overwriteProgramHandler, programmingCodec,
          OracleCodec.wordOracle, hactive, Function.Embedding.coe_refl, id_map,
          PMF.map, Function.comp_def]
      · have hfalse : active caller word = false := Bool.eq_false_iff.mpr hactive
        simp [overwriteProgramWordHandler, overwriteProgramHandler, programmingCodec,
          OracleCodec.wordOracle, hactive, Function.Embedding.coe_refl, id_map,
          PMF.map_comp, Function.comp_def]
  | hash =>
      simp [overwriteProgramWordHandler, overwriteProgramHandler, programmingCodec,
        OracleCodec.wordOracle, ProbComp.eval_memoize, Function.Embedding.coe_refl, id_map,
        PMF.map_comp, Function.comp_def]

/-- Adaptive typed execution against `lazyProgramHandler` has exactly the joint result/cache/log
law of native execution against `lazyProgramWordHandler`. -/
theorem runWith_lazyProgramWordHandler {α : Type}
    (program : WordOracleComp ProgrammingOp α)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (cache : List (List Bool × List Bool)) (log : Log) :
    (ProbOracleComp.runWith
      (lazyProgramHandler (ProbComp.eval (dist caller)) (active caller)
        (fun request _ currentLog => ProbComp.eval (inactive caller request currentLog))
        (fun request => ProbComp.eval (samplePre caller request)) (point caller) (finish caller))
      (programmingCodec.adapt program) (cache, log)).map
        (fun ⟨result, cache, log⟩ =>
          (result, (⟨cache, log⟩ : ProgrammingState Log))) =
      ProbOracleComp.runWith
        (fun request state => ProbComp.eval (lazyProgramWordHandler dist active inactive samplePre
          point finish caller request state)) program ⟨cache, log⟩ := by
  rw [programmingCodec.runWith_adapt]
  refine ProbOracleComp.runWith_map_state
    (programmingCodec.wordOracle
      (lazyProgramHandler (ProbComp.eval (dist caller)) (active caller)
        (fun request _ currentLog => ProbComp.eval (inactive caller request currentLog))
        (fun request => ProbComp.eval (samplePre caller request)) (point caller) (finish caller)))
    (fun request state => ProbComp.eval (lazyProgramWordHandler dist active inactive samplePre
      point finish caller request state))
    (fun state : List (List Bool × List Bool) × Log =>
      (⟨state.1, state.2⟩ : ProgrammingState Log)) ?_ program (cache, log)
  intro request state
  symm
  simpa using eval_lazyProgramWordHandler dist active inactive samplePre point finish caller
    request (⟨state.1, state.2⟩ : ProgrammingState Log)

/-- Adaptive typed execution against `overwriteProgramHandler` has exactly the joint
result/cache/log law of native execution against `overwriteProgramWordHandler`. -/
theorem runWith_overwriteProgramWordHandler {α : Type}
    (program : WordOracleComp ProgrammingOp α)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (cache : List (List Bool × List Bool)) (log : Log) :
    (ProbOracleComp.runWith
      (overwriteProgramHandler (ProbComp.eval (dist caller)) (active caller)
        (fun request _ currentLog => ProbComp.eval (inactive caller request currentLog))
        (fun request => ProbComp.eval (samplePre caller request)) (point caller) (finish caller))
      (programmingCodec.adapt program) (cache, log)).map
        (fun ⟨result, cache, log⟩ =>
          (result, (⟨cache, log⟩ : ProgrammingState Log))) =
      ProbOracleComp.runWith
        (fun request state => ProbComp.eval (overwriteProgramWordHandler dist active inactive
          samplePre point finish caller request state)) program ⟨cache, log⟩ := by
  rw [programmingCodec.runWith_adapt]
  refine ProbOracleComp.runWith_map_state
    (programmingCodec.wordOracle
      (overwriteProgramHandler (ProbComp.eval (dist caller)) (active caller)
        (fun request _ currentLog => ProbComp.eval (inactive caller request currentLog))
        (fun request => ProbComp.eval (samplePre caller request)) (point caller) (finish caller)))
    (fun request state => ProbComp.eval (overwriteProgramWordHandler dist active inactive
      samplePre point finish caller request state))
    (fun state : List (List Bool × List Bool) × Log =>
      (⟨state.1, state.2⟩ : ProgrammingState Log)) ?_ program (cache, log)
  intro request state
  symm
  simpa using eval_overwriteProgramWordHandler dist active inactive samplePre point finish caller
    request (⟨state.1, state.2⟩ : ProgrammingState Log)

/-! ### Strict-PPT certificates -/

/-- The lazy programmable word handler is strict PPT when each caller component is. The
certificate charges the complete incoming and returned cache and log. -/
theorem isPPTOn_lazyProgramWordHandler (input : Caller ↪ List Bool) (encLog : Log ↪ List Bool)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (hdist : Probability.IsPPTOn input encBits dist)
    (hactive : ComputableInPolyTime (fun p : Caller × List Bool => active p.1 p.2)
      (encPair input encBits) encBool)
    (hinactive : Probability.IsPPTOn (encPair (encPair input encBits) encLog)
      (encPair encBits encLog) (fun p => inactive p.1.1 p.1.2 p.2))
    (hsamplePre : Probability.IsPPTOn (encPair input encBits) encBits
      (fun p => samplePre p.1 p.2))
    (hpoint : ComputableInPolyTime
      (fun p : (Caller × List Bool) × List Bool => point p.1.1 p.1.2 p.2)
      (encPair (encPair input encBits) encBits) encBits)
    (hfinish : ComputableInPolyTime
      (fun p : ((((Caller × List Bool) × List Bool) × List Bool) × Log) =>
        finish p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog)
      (encPair encBits encLog)) :
    Probability.IsPPTOn
      (encHandlerCall input encProgrammingOp (encProgrammingState Log encLog))
      (encPair encBits (encProgrammingState Log encLog))
      (fun p => lazyProgramWordHandler dist active inactive samplePre point finish
        p.1 p.2.1 p.2.2) := by
  let callEncoding :=
    encHandlerCall input encProgrammingOp (encProgrammingState Log encLog)
  have hdistCall : Probability.IsPPTOn callEncoding encBits (fun p => dist p.1) :=
    Probability.IsPPTOn.preprocess hdist (by fun_prop)
  have hhash := Probability.IsPPTOn.map_with (Probability.IsPPTOn.memoize
    (compute := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
      fun _ => dist p.1)
    (query := fun p => p.2.1.2) (cache := fun p => p.2.2.cache)
    hdistCall (by fun_prop) (by fun_prop))
    (f := fun p result =>
      (result.1, (⟨result.2, p.2.2.log⟩ : ProgrammingState Log)))
    (by fun_prop)
  have hinactiveCall : Probability.IsPPTOn callEncoding
      (encPair encBits (encProgrammingState Log encLog)) (fun p =>
        (fun result =>
          (result.1, (⟨p.2.2.cache, result.2⟩ : ProgrammingState Log))) <$>
            inactive p.1 p.2.1.2 p.2.2.log) :=
    Probability.IsPPTOn.map_with (Probability.IsPPTOn.preprocess hinactive
      (prepare := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
        ((p.1, p.2.1.2), p.2.2.log)) (by fun_prop))
      (f := fun p result =>
        (result.1, (⟨p.2.2.cache, result.2⟩ : ProgrammingState Log))) (by fun_prop)
  have hpre : Probability.IsPPTOn callEncoding encBits (fun p =>
      samplePre p.1 p.2.1.2) :=
    Probability.IsPPTOn.preprocess hsamplePre
      (prepare := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
        (p.1, p.2.1.2)) (by fun_prop)
  have hactiveCall : Probability.IsPPTOn callEncoding
      (encPair encBits (encProgrammingState Log encLog)) (fun p => do
        let coins ← samplePre p.1 p.2.1.2
        let (digest, cache') ← memoize (fun _ => dist p.1)
          (point p.1 p.2.1.2 coins) p.2.2.cache
        let (reply, log') := finish p.1 p.2.1.2 coins digest p.2.2.log
        return (reply, ⟨cache', log'⟩)) := by
    apply Probability.IsPPTOn.bind_with hpre
    have hdistCoins : Probability.IsPPTOn (encPair callEncoding encBits) encBits
        (fun p => dist p.1.1) :=
      Probability.IsPPTOn.preprocess hdist (by fun_prop)
    have hmemoCoins : Probability.IsPPTOn (encPair callEncoding encBits)
        (encPair encBits (encMemoCache encBits encBits)) (fun p =>
          memoize (fun _ => dist p.1.1) (point p.1.1 p.1.2.1.2 p.2)
            p.1.2.2.cache) :=
      have hpointInput : ComputableInPolyTime
          (fun p :
            (Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool =>
              ((p.1.1, p.1.2.1.2), p.2))
          (encPair callEncoding encBits) (encPair (encPair input encBits) encBits) := by
        fun_prop
      Probability.IsPPTOn.memoize
      (compute := fun p :
          (Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool =>
        fun _ => dist p.1.1)
      (query := fun p => point p.1.1 p.1.2.1.2 p.2)
      (cache := fun p => p.1.2.2.cache) hdistCoins
      (hpoint.comp hpointInput) (by fun_prop)
    have hdone : ComputableInPolyTime
        (fun pair :
          ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
            (List Bool × List (List Bool × List Bool)) =>
          let done := finish pair.1.1.1 pair.1.1.2.1.2 pair.1.2 pair.2.1
            pair.1.1.2.2.log
          (done.1, (⟨pair.2.2, done.2⟩ : ProgrammingState Log)))
        (encPair (encPair callEncoding encBits)
          (encPair encBits (encMemoCache encBits encBits)))
        (encPair encBits (encProgrammingState Log encLog)) := by
      let sourceEncoding := encPair (encPair callEncoding encBits)
        (encPair encBits (encMemoCache encBits encBits))
      have hfinishInput : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              (List Bool × List (List Bool × List Bool)) =>
            ((((pair.1.1.1, pair.1.1.2.1.2), pair.1.2), pair.2.1),
              pair.1.1.2.2.log)) sourceEncoding
          (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog) := by
        dsimp only [sourceEncoding]
        fun_prop
      have hfinishSource := hfinish.comp hfinishInput
      have hcache : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              (List Bool × List (List Bool × List Bool)) => pair.2.2)
          sourceEncoding (encMemoCache encBits encBits) := by
        dsimp only [sourceEncoding]
        fun_prop
      exact hfinishSource.fst'.prod (hcache.prod hfinishSource.snd')
    simpa only [bind_pure_comp] using Probability.IsPPTOn.map_with hmemoCoins
      (f := fun p result =>
        let done := finish p.1.1 p.1.2.1.2 p.2 result.1 p.1.2.2.log
        (done.1, (⟨result.2, done.2⟩ : ProgrammingState Log)))
      hdone
  have hactiveOnCall : ComputableInPolyTime (fun p => active p.1 p.2.1.2)
      callEncoding encBool := by
    have hactiveInput : ComputableInPolyTime
        (fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
          (p.1, p.2.1.2)) callEncoding (encPair input encBits) := by fun_prop
    exact hactive.comp hactiveInput
  have hprogram := Probability.IsPPTOn.cond'
    hactiveOnCall hactiveCall hinactiveCall
  have hop : ComputableInPolyTime (fun p :
      Caller × (ProgrammingOp × List Bool) × ProgrammingState Log => p.2.1.1)
      callEncoding encProgrammingOp := by fun_prop
  have hall := Probability.IsPPTOn.cond'
    (ComputableInPolyTime.beq hop
      (ComputableInPolyTime.const ProgrammingOp.program)) hprogram hhash
  refine hall.congr fun p => ?_
  obtain ⟨caller, ⟨op, request⟩, state⟩ := p
  cases op <;> simp [lazyProgramWordHandler]

/-- The overwrite programmable word handler is strict PPT when each caller component is. The
certificate charges the complete incoming and returned cache and log. -/
theorem isPPTOn_overwriteProgramWordHandler (input : Caller ↪ List Bool)
    (encLog : Log ↪ List Bool) (dist : Caller → ProbComp (List Bool))
    (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (hdist : Probability.IsPPTOn input encBits dist)
    (hactive : ComputableInPolyTime (fun p : Caller × List Bool => active p.1 p.2)
      (encPair input encBits) encBool)
    (hinactive : Probability.IsPPTOn (encPair (encPair input encBits) encLog)
      (encPair encBits encLog) (fun p => inactive p.1.1 p.1.2 p.2))
    (hsamplePre : Probability.IsPPTOn (encPair input encBits) encBits
      (fun p => samplePre p.1 p.2))
    (hpoint : ComputableInPolyTime
      (fun p : (Caller × List Bool) × List Bool => point p.1.1 p.1.2 p.2)
      (encPair (encPair input encBits) encBits) encBits)
    (hfinish : ComputableInPolyTime
      (fun p : ((((Caller × List Bool) × List Bool) × List Bool) × Log) =>
        finish p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog)
      (encPair encBits encLog)) :
    Probability.IsPPTOn
      (encHandlerCall input encProgrammingOp (encProgrammingState Log encLog))
      (encPair encBits (encProgrammingState Log encLog))
      (fun p => overwriteProgramWordHandler dist active inactive samplePre point finish
        p.1 p.2.1 p.2.2) := by
  let callEncoding :=
    encHandlerCall input encProgrammingOp (encProgrammingState Log encLog)
  have hdistCall : Probability.IsPPTOn callEncoding encBits (fun p => dist p.1) :=
    Probability.IsPPTOn.preprocess hdist (by fun_prop)
  have hhash := Probability.IsPPTOn.map_with (Probability.IsPPTOn.memoize
    (compute := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
      fun _ => dist p.1)
    (query := fun p => p.2.1.2) (cache := fun p => p.2.2.cache)
    hdistCall (by fun_prop) (by fun_prop))
    (f := fun p result =>
      (result.1, (⟨result.2, p.2.2.log⟩ : ProgrammingState Log))) (by fun_prop)
  have hinactiveCall : Probability.IsPPTOn callEncoding
      (encPair encBits (encProgrammingState Log encLog)) (fun p =>
        (fun result =>
          (result.1, (⟨p.2.2.cache, result.2⟩ : ProgrammingState Log))) <$>
            inactive p.1 p.2.1.2 p.2.2.log) :=
    Probability.IsPPTOn.map_with (Probability.IsPPTOn.preprocess hinactive
      (prepare := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
        ((p.1, p.2.1.2), p.2.2.log)) (by fun_prop))
      (f := fun p result =>
        (result.1, (⟨p.2.2.cache, result.2⟩ : ProgrammingState Log))) (by fun_prop)
  have hpre : Probability.IsPPTOn callEncoding encBits (fun p =>
      samplePre p.1 p.2.1.2) :=
    Probability.IsPPTOn.preprocess hsamplePre
      (prepare := fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
        (p.1, p.2.1.2)) (by fun_prop)
  have hactiveCall : Probability.IsPPTOn callEncoding
      (encPair encBits (encProgrammingState Log encLog)) (fun p => do
        let coins ← samplePre p.1 p.2.1.2
        let digest ← dist p.1
        let (reply, log') := finish p.1 p.2.1.2 coins digest p.2.2.log
        return (reply, ⟨(point p.1 p.2.1.2 coins, digest) :: p.2.2.cache, log'⟩)) := by
    apply Probability.IsPPTOn.bind_with hpre
    have hdistCoins : Probability.IsPPTOn (encPair callEncoding encBits) encBits
        (fun p => dist p.1.1) :=
      Probability.IsPPTOn.preprocess hdist (by fun_prop)
    have hdone : ComputableInPolyTime
        (fun pair :
          ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
            List Bool =>
          let done := finish pair.1.1.1 pair.1.1.2.1.2 pair.1.2 pair.2
            pair.1.1.2.2.log
          (done.1, (⟨(point pair.1.1.1 pair.1.1.2.1.2 pair.1.2, pair.2) ::
            pair.1.1.2.2.cache, done.2⟩ : ProgrammingState Log)))
        (encPair (encPair callEncoding encBits) encBits)
        (encPair encBits (encProgrammingState Log encLog)) := by
      let sourceEncoding := encPair (encPair callEncoding encBits) encBits
      have hfinishInput : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              List Bool =>
            ((((pair.1.1.1, pair.1.1.2.1.2), pair.1.2), pair.2),
              pair.1.1.2.2.log)) sourceEncoding
          (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog) := by
        dsimp only [sourceEncoding]
        fun_prop
      have hfinishSource := hfinish.comp hfinishInput
      have hpointInput : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              List Bool => ((pair.1.1.1, pair.1.1.2.1.2), pair.1.2))
          sourceEncoding (encPair (encPair input encBits) encBits) := by
        dsimp only [sourceEncoding]
        fun_prop
      have hpointSource := hpoint.comp hpointInput
      have hdigest : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              List Bool => pair.2) sourceEncoding encBits := by
        dsimp only [sourceEncoding]
        fun_prop
      have hcache : ComputableInPolyTime
          (fun pair :
            ((Caller × (ProgrammingOp × List Bool) × ProgrammingState Log) × List Bool) ×
              List Bool => pair.1.1.2.2.cache) sourceEncoding
          (encMemoCache encBits encBits) := by
        dsimp only [sourceEncoding]
        fun_prop
      have hnewCache := ComputableInPolyTime.cons' (hpointSource.prod hdigest) hcache
      exact hfinishSource.fst'.prod (hnewCache.prod hfinishSource.snd')
    simpa only [bind_pure_comp] using Probability.IsPPTOn.map_with hdistCoins
      (f := fun p digest =>
        let done := finish p.1.1 p.1.2.1.2 p.2 digest p.1.2.2.log
        (done.1, (⟨(point p.1.1 p.1.2.1.2 p.2, digest) :: p.1.2.2.cache,
          done.2⟩ : ProgrammingState Log))) hdone
  have hactiveOnCall : ComputableInPolyTime (fun p => active p.1 p.2.1.2)
      callEncoding encBool := by
    have hactiveInput : ComputableInPolyTime
        (fun p : Caller × (ProgrammingOp × List Bool) × ProgrammingState Log =>
          (p.1, p.2.1.2)) callEncoding (encPair input encBits) := by fun_prop
    exact hactive.comp hactiveInput
  have hprogram := Probability.IsPPTOn.cond'
    hactiveOnCall hactiveCall hinactiveCall
  have hop : ComputableInPolyTime (fun p :
      Caller × (ProgrammingOp × List Bool) × ProgrammingState Log => p.2.1.1)
      callEncoding encProgrammingOp := by fun_prop
  have hall := Probability.IsPPTOn.cond'
    (ComputableInPolyTime.beq hop
      (ComputableInPolyTime.const ProgrammingOp.program)) hprogram hhash
  refine hall.congr fun p => ?_
  obtain ⟨caller, ⟨op, request⟩, state⟩ := p
  cases op <;> simp [overwriteProgramWordHandler]

/-! ### Per-call resource contract -/

/-- State invariant used by the programmable-oracle resource contract: cached digests satisfy the
caller bound and the caller-defined log invariant holds. The representation is kept opaque; use
`ProgrammingInvariant.intro` to establish it. -/
def ProgrammingInvariant (digestBound : Caller → ℕ)
    (logInvariant : Caller → Log → Prop) (caller : Caller) (state : ProgrammingState Log) : Prop :=
  (∀ entry ∈ state.cache, entry.2.length ≤ digestBound caller) ∧
    logInvariant caller state.log

/-- Establish the programmable state invariant from its cache and log obligations. -/
theorem ProgrammingInvariant.intro (digestBound : Caller → ℕ)
    (logInvariant : Caller → Log → Prop) (caller : Caller) (state : ProgrammingState Log)
    (hcache : ∀ entry ∈ state.cache, entry.2.length ≤ digestBound caller)
    (hlog : logInvariant caller state.log) :
    ProgrammingInvariant digestBound logInvariant caller state :=
  ⟨hcache, hlog⟩

/-- Additive allowance for one programmable-oracle call. It charges the reply and request words,
the programmed point, the sampled digest, fixed framing overhead and caller log growth. -/
def programmingResources (digestBound : Caller → ℕ)
    (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (caller : Caller) (request : List Bool) : ℕ :=
  replyBound caller request + 8 * request.length + 8 * pointBound caller request +
    4 * digestBound caller + 6 + logGrowth caller request

/-- The shared per-call allowance is polynomial-time computable from certificates for its four
caller-supplied bounds. This lets finite source-operation adapters take maxima of the opaque
allowance at their framed payloads without duplicating its formula. -/
theorem computableInPolyTime_programmingResources (input : Caller ↪ List Bool)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (hdigestBound : ComputableInPolyTime digestBound input encUnary)
    (hpointBound : ComputableInPolyTime (fun p : Caller × List Bool => pointBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hreplyBound : ComputableInPolyTime (fun p : Caller × List Bool => replyBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hlogGrowth : ComputableInPolyTime (fun p : Caller × List Bool => logGrowth p.1 p.2)
      (encPair input encBits) encUnary) :
    ComputableInPolyTime (fun p : Caller × List Bool =>
      programmingResources digestBound pointBound replyBound logGrowth p.1 p.2)
      (encPair input encBits) encUnary := by
  unfold programmingResources
  fun_prop

private theorem length_encProgrammingState (encLog : Log ↪ List Bool)
    (state : ProgrammingState Log) :
    (encProgrammingState Log encLog state).length =
      2 * (encMemoCache encBits encBits state.cache).length +
        (encLog state.log).length + 1 := by
  simp only [encProgrammingState_apply, encProgrammingStateFields, length_encPair]
  ring

/-- Every supported lazy programmable-oracle call preserves `ProgrammingInvariant`, bounds the
reply word and grows the complete encoded cache/log state by at most `programmingResources`. -/
theorem lazyProgramWordHandler_support
    (encLog : Log ↪ List Bool) (dist : Caller → ProbComp (List Bool))
    (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (logInvariant : Caller → Log → Prop)
    (hdist : ∀ caller digest, digest ∈ (ProbComp.eval (dist caller)).support →
      digest.length ≤ digestBound caller)
    (hpoint : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      (point caller request coins).length ≤ pointBound caller request)
    (hinactive : ∀ caller request log, logInvariant caller log →
      ∀ result ∈ (ProbComp.eval (inactive caller request log)).support,
        logInvariant caller result.2 ∧ result.1.length ≤ replyBound caller request ∧
          (encLog result.2).length ≤ (encLog log).length + logGrowth caller request)
    (hfinish : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      ∀ digest, digest.length ≤ digestBound caller → ∀ log, logInvariant caller log →
        logInvariant caller (finish caller request coins digest log).2 ∧
          (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
          (encLog (finish caller request coins digest log).2).length ≤
            (encLog log).length + logGrowth caller request)
    (caller : Caller) (request : ProgrammingOp × List Bool) (state : ProgrammingState Log)
    (hstate : ProgrammingInvariant digestBound logInvariant caller state)
    (result : List Bool × ProgrammingState Log)
    (hresult : result ∈ (ProbComp.eval (lazyProgramWordHandler dist active inactive samplePre
      point finish caller request state)).support) :
    ProgrammingInvariant digestBound logInvariant caller result.2 ∧
      result.1.length ≤
        programmingResources digestBound pointBound replyBound logGrowth caller request.2 ∧
      (encProgrammingState Log encLog result.2).length ≤
        (encProgrammingState Log encLog state).length +
          programmingResources digestBound pointBound replyBound logGrowth caller request.2 := by
  obtain ⟨hcache, hlog⟩ := hstate
  obtain ⟨op, word⟩ := request
  cases op with
  | hash =>
      simp only [lazyProgramWordHandler] at hresult
      change result ∈ (ProbComp.eval ((fun cached =>
        (cached.1, (⟨cached.2, state.log⟩ : ProgrammingState Log))) <$>
          memoize (fun _ => dist caller) word state.cache)).support at hresult
      rw [ProbComp.eval_map, ProbComp.eval_memoize] at hresult
      obtain ⟨cached, hcached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := Probability.memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (dist caller)) word state.cache (digestBound caller) hcache
        (fun digest hdigest => hdist caller digest hdigest) cached hcached
      refine ⟨⟨hcache', hlog⟩, ?_, ?_⟩
      · unfold programmingResources
        simpa only [encBits_apply] using hreply.trans (by lia)
      · rw [length_encProgrammingState, length_encProgrammingState]
        simp only [encBits_apply] at hgrowth
        unfold programmingResources
        lia
  | program =>
      simp only [lazyProgramWordHandler] at hresult
      split_ifs at hresult with hactive
      · rw [ProbComp.eval_bind] at hresult
        obtain ⟨coins, hcoins, hresult⟩ := (PMF.mem_support_bind_iff _ _ _).mp hresult
        rw [ProbComp.eval_bind] at hresult
        obtain ⟨cached, hcached, hresult⟩ := (PMF.mem_support_bind_iff _ _ _).mp hresult
        rw [ProbComp.eval_memoize] at hcached
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
        subst result
        obtain ⟨hdigest, hcache', hcacheGrowth⟩ :=
          Probability.memoize_call_size_le encBits encBits
            (fun _ => ProbComp.eval (dist caller)) (point caller word coins) state.cache
            (digestBound caller) hcache (fun digest hdigest => hdist caller digest hdigest)
            cached hcached
        obtain ⟨hlog', hreply, hlogGrowth⟩ :=
          hfinish caller word coins hcoins cached.1 (by simpa only [encBits_apply] using hdigest)
            state.log hlog
        refine ⟨⟨hcache', hlog'⟩, ?_, ?_⟩
        · unfold programmingResources
          lia
        · rw [length_encProgrammingState, length_encProgrammingState]
          have hpointBound := hpoint caller word coins hcoins
          simp only [encBits_apply] at hcacheGrowth
          unfold programmingResources
          lia
      · change result ∈ (ProbComp.eval ((fun inactiveResult =>
          (inactiveResult.1, (⟨state.cache, inactiveResult.2⟩ : ProgrammingState Log))) <$>
            inactive caller word state.log)).support at hresult
        rw [ProbComp.eval_map] at hresult
        obtain ⟨inactiveResult, hinactiveResult, rfl⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp hresult
        obtain ⟨hlog', hreply, hlogGrowth⟩ :=
          hinactive caller word state.log hlog inactiveResult hinactiveResult
        refine ⟨⟨hcache, hlog'⟩, ?_, ?_⟩
        · unfold programmingResources
          lia
        · rw [length_encProgrammingState, length_encProgrammingState]
          unfold programmingResources
          lia

private theorem overwriteProgramWordHandler_support
    (encLog : Log ↪ List Bool) (dist : Caller → ProbComp (List Bool))
    (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (logInvariant : Caller → Log → Prop)
    (hdist : ∀ caller digest, digest ∈ (ProbComp.eval (dist caller)).support →
      digest.length ≤ digestBound caller)
    (hpoint : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      (point caller request coins).length ≤ pointBound caller request)
    (hinactive : ∀ caller request log, logInvariant caller log →
      ∀ result ∈ (ProbComp.eval (inactive caller request log)).support,
        logInvariant caller result.2 ∧ result.1.length ≤ replyBound caller request ∧
          (encLog result.2).length ≤ (encLog log).length + logGrowth caller request)
    (hfinish : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      ∀ digest, digest.length ≤ digestBound caller → ∀ log, logInvariant caller log →
        logInvariant caller (finish caller request coins digest log).2 ∧
          (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
          (encLog (finish caller request coins digest log).2).length ≤
            (encLog log).length + logGrowth caller request)
    (caller : Caller) (request : ProgrammingOp × List Bool) (state : ProgrammingState Log)
    (hstate : ProgrammingInvariant digestBound logInvariant caller state)
    (result : List Bool × ProgrammingState Log)
    (hresult : result ∈ (ProbComp.eval (overwriteProgramWordHandler dist active inactive samplePre
      point finish caller request state)).support) :
    ProgrammingInvariant digestBound logInvariant caller result.2 ∧
      result.1.length ≤
        programmingResources digestBound pointBound replyBound logGrowth caller request.2 ∧
      (encProgrammingState Log encLog result.2).length ≤
        (encProgrammingState Log encLog state).length +
          programmingResources digestBound pointBound replyBound logGrowth caller request.2 := by
  obtain ⟨hcache, hlog⟩ := hstate
  obtain ⟨op, word⟩ := request
  cases op with
  | hash =>
      simp only [overwriteProgramWordHandler] at hresult
      change result ∈ (ProbComp.eval ((fun cached =>
        (cached.1, (⟨cached.2, state.log⟩ : ProgrammingState Log))) <$>
          memoize (fun _ => dist caller) word state.cache)).support at hresult
      rw [ProbComp.eval_map, ProbComp.eval_memoize] at hresult
      obtain ⟨cached, hcached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := Probability.memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (dist caller)) word state.cache (digestBound caller) hcache
        (fun digest hdigest => hdist caller digest hdigest) cached hcached
      refine ⟨⟨hcache', hlog⟩, ?_, ?_⟩
      · unfold programmingResources
        simpa only [encBits_apply] using hreply.trans (by lia)
      · rw [length_encProgrammingState, length_encProgrammingState]
        simp only [encBits_apply] at hgrowth
        unfold programmingResources
        lia
  | program =>
      simp only [overwriteProgramWordHandler] at hresult
      split_ifs at hresult with hactive
      · rw [ProbComp.eval_bind] at hresult
        obtain ⟨coins, hcoins, hresult⟩ := (PMF.mem_support_bind_iff _ _ _).mp hresult
        rw [ProbComp.eval_bind] at hresult
        obtain ⟨digest, hdigestSupport, hresult⟩ :=
          (PMF.mem_support_bind_iff _ _ _).mp hresult
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
        subst result
        have hdigest := hdist caller digest hdigestSupport
        obtain ⟨hlog', hreply, hlogGrowth⟩ :=
          hfinish caller word coins hcoins digest hdigest state.log hlog
        refine ⟨⟨?_, hlog'⟩, ?_, ?_⟩
        · simpa using And.intro hdigest hcache
        · unfold programmingResources
          lia
        · rw [length_encProgrammingState, length_encProgrammingState]
          have hpointBound := hpoint caller word coins hcoins
          simp only [encMemoCache, encList_cons, List.length_append, length_frame,
            length_encPair, encBits_apply]
          unfold programmingResources
          lia
      · change result ∈ (ProbComp.eval ((fun inactiveResult =>
          (inactiveResult.1, (⟨state.cache, inactiveResult.2⟩ : ProgrammingState Log))) <$>
            inactive caller word state.log)).support at hresult
        rw [ProbComp.eval_map] at hresult
        obtain ⟨inactiveResult, hinactiveResult, rfl⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp hresult
        obtain ⟨hlog', hreply, hlogGrowth⟩ :=
          hinactive caller word state.log hlog inactiveResult hinactiveResult
        refine ⟨⟨hcache, hlog'⟩, ?_, ?_⟩
        · unfold programmingResources
          lia
        · rw [length_encProgrammingState, length_encProgrammingState]
          unfold programmingResources
          lia

/-! ### Whole-program strict-PPT certificates -/

/-- Running a uniform strict oracle-PPT program against the lazy programmable word handler is
strict PPT, including its final cache and log. The component bounds form a local additive
storage contract. This theorem charges runtime caller data but not a parameter-dependent static
description of `program`; such descriptions require a separate `OracleTM`-level size argument. -/
theorem isPPTOn_run_lazyProgramWordHandler {β : Type} (input : Caller ↪ List Bool)
    (output : β ↪ List Bool) (encLog : Log ↪ List Bool)
    (program : ℕ → List Bool → WordOracleComp ProgrammingOp β)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (prepare : Caller → ℕ × List Bool) (initial : Caller → ProgrammingState Log)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (logInvariant : Caller → Log → Prop)
    (hprogram : Probability.IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : Probability.IsPPTOn
      (encHandlerCall input encProgrammingOp (encProgrammingState Log encLog))
      (encPair encBits (encProgrammingState Log encLog))
      (fun p => lazyProgramWordHandler dist active inactive samplePre point finish
        p.1 p.2.1 p.2.2))
    (hinitial : ComputableInPolyTime initial input (encProgrammingState Log encLog))
    (hdigestBound : ComputableInPolyTime digestBound input encUnary)
    (hpointBound : ComputableInPolyTime (fun p : Caller × List Bool =>
      pointBound p.1 p.2) (encPair input encBits) encUnary)
    (hreplyBound : ComputableInPolyTime (fun p : Caller × List Bool =>
      replyBound p.1 p.2) (encPair input encBits) encUnary)
    (hlogGrowth : ComputableInPolyTime (fun p : Caller × List Bool =>
      logGrowth p.1 p.2) (encPair input encBits) encUnary)
    (hdist : ∀ caller digest, digest ∈ (ProbComp.eval (dist caller)).support →
      digest.length ≤ digestBound caller)
    (hpoint : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      (point caller request coins).length ≤ pointBound caller request)
    (hinactive : ∀ caller request log, logInvariant caller log →
      ∀ result ∈ (ProbComp.eval (inactive caller request log)).support,
        logInvariant caller result.2 ∧ result.1.length ≤ replyBound caller request ∧
          (encLog result.2).length ≤ (encLog log).length + logGrowth caller request)
    (hfinish : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      ∀ digest, digest.length ≤ digestBound caller → ∀ log, logInvariant caller log →
        logInvariant caller (finish caller request coins digest log).2 ∧
          (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
          (encLog (finish caller request coins digest log).2).length ≤
            (encLog log).length + logGrowth caller request)
    (hinitCache : ∀ caller entry, entry ∈ (initial caller).cache →
      entry.2.length ≤ digestBound caller)
    (hinitLog : ∀ caller, logInvariant caller (initial caller).log) :
    Probability.IsPPTOn input (encPair output (encProgrammingState Log encLog))
      (fun caller => ((program (prepare caller).1 (prepare caller).2).runState
        (lazyProgramWordHandler dist active inactive samplePre point finish caller)).run
          (initial caller)) := by
  apply Probability.IsOraclePPT.isPPTOn_runState
    (resources := programmingResources digestBound pointBound replyBound logGrowth)
    hprogram hprepare hhandler hinitial
    (ProgrammingInvariant digestBound logInvariant) (fun caller =>
      ⟨hinitCache caller, hinitLog caller⟩)
  · exact computableInPolyTime_programmingResources input digestBound pointBound replyBound
      logGrowth hdigestBound hpointBound hreplyBound hlogGrowth
  · exact fun caller request state hstate result hresult =>
      lazyProgramWordHandler_support encLog dist active inactive samplePre point finish
        digestBound pointBound replyBound logGrowth logInvariant hdist hpoint hinactive hfinish
        caller request state hstate result hresult

/-- Running a uniform strict oracle-PPT program against the overwrite programmable word handler
is strict PPT, including its final cache and log. It uses the same local additive resource
contract and the same static-description-size limitation as
`isPPTOn_run_lazyProgramWordHandler`. -/
theorem isPPTOn_run_overwriteProgramWordHandler {β : Type} (input : Caller ↪ List Bool)
    (output : β ↪ List Bool) (encLog : Log ↪ List Bool)
    (program : ℕ → List Bool → WordOracleComp ProgrammingOp β)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (prepare : Caller → ℕ × List Bool) (initial : Caller → ProgrammingState Log)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (logInvariant : Caller → Log → Prop)
    (hprogram : Probability.IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : Probability.IsPPTOn
      (encHandlerCall input encProgrammingOp (encProgrammingState Log encLog))
      (encPair encBits (encProgrammingState Log encLog))
      (fun p => overwriteProgramWordHandler dist active inactive samplePre point finish
        p.1 p.2.1 p.2.2))
    (hinitial : ComputableInPolyTime initial input (encProgrammingState Log encLog))
    (hdigestBound : ComputableInPolyTime digestBound input encUnary)
    (hpointBound : ComputableInPolyTime (fun p : Caller × List Bool =>
      pointBound p.1 p.2) (encPair input encBits) encUnary)
    (hreplyBound : ComputableInPolyTime (fun p : Caller × List Bool =>
      replyBound p.1 p.2) (encPair input encBits) encUnary)
    (hlogGrowth : ComputableInPolyTime (fun p : Caller × List Bool =>
      logGrowth p.1 p.2) (encPair input encBits) encUnary)
    (hdist : ∀ caller digest, digest ∈ (ProbComp.eval (dist caller)).support →
      digest.length ≤ digestBound caller)
    (hpoint : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      (point caller request coins).length ≤ pointBound caller request)
    (hinactive : ∀ caller request log, logInvariant caller log →
      ∀ result ∈ (ProbComp.eval (inactive caller request log)).support,
        logInvariant caller result.2 ∧ result.1.length ≤ replyBound caller request ∧
          (encLog result.2).length ≤ (encLog log).length + logGrowth caller request)
    (hfinish : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      ∀ digest, digest.length ≤ digestBound caller → ∀ log, logInvariant caller log →
        logInvariant caller (finish caller request coins digest log).2 ∧
          (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
          (encLog (finish caller request coins digest log).2).length ≤
            (encLog log).length + logGrowth caller request)
    (hinitCache : ∀ caller entry, entry ∈ (initial caller).cache →
      entry.2.length ≤ digestBound caller)
    (hinitLog : ∀ caller, logInvariant caller (initial caller).log) :
    Probability.IsPPTOn input (encPair output (encProgrammingState Log encLog))
      (fun caller => ((program (prepare caller).1 (prepare caller).2).runState
        (overwriteProgramWordHandler dist active inactive samplePre point finish caller)).run
          (initial caller)) := by
  apply Probability.IsOraclePPT.isPPTOn_runState
    (resources := programmingResources digestBound pointBound replyBound logGrowth)
    hprogram hprepare hhandler hinitial
    (ProgrammingInvariant digestBound logInvariant) (fun caller =>
      ⟨hinitCache caller, hinitLog caller⟩)
  · exact computableInPolyTime_programmingResources input digestBound pointBound replyBound
      logGrowth hdigestBound hpointBound hreplyBound hlogGrowth
  · exact fun caller request state hstate result hresult =>
      overwriteProgramWordHandler_support encLog dist active inactive samplePre point finish
        digestBound pointBound replyBound logGrowth logInvariant hdist hpoint hinactive hfinish
        caller request state hstate result hresult

end Cslib.RandomOracle
