/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.KEM
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Correctness
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.RandomOracle.Represented
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure

/-!
# Concrete-only correctness hop for salted joint-oracle FO transforms

This module isolates the `CORR` hop in the classical-ROM decapsulation simulation for an
implicit-rejection salted Fujisaki--Okamoto transform. A direct query receives the session key and
encryption coins in one `JointReply`; it therefore costs one `joint` query, not one query per
projection. The rejection oracle is a separate channel and does not create a PKE correctness
witness. Decapsulation is punctured at the challenge ciphertext and has its own cost.

`Scheme.realHandler` constructs the decrypt/re-encrypt path and `Scheme.simHandler` constructs the
secret-key-free patched-cache path. These handlers begin after the source proof's secret rejection
seed has been guessed: the adversary-visible `J` table and the proof-only `LD` table are therefore
independent here, rather than a model of the original pre-guessing HQC fallback oracle. The proof
inserts a private prefetch handler: real and prefetch are identical until one cached encryption coin
fails to decrypt, while prefetch and keyless have exactly the same output law after completing their
four independent coordinates: joint coins for every full input, off-target joint keys by full
input, target-prefix `LD` keys by ciphertext, and `J` keys. The concrete fixed-key theorem
therefore loses exactly
`(qRO + qD) * ε`; the randomized theorem averages a challenge-aware public adversary over a common
challenge law and key generation using `ExplicitCoinPKE.DeltaCorrect δ`.

This is the single-user, single-challenge specialization of the `CORR` step in Theorem 11 and
Figure 11 of [GlabushHoevelmannsStebila2025]. In HQC v5.1, Section 6.2.2, Theorem 6.4, the source
coin and key oracles are fused as `G(H(ekKEM) || m || salt) = (K, θ)`, so their direct-query
contribution is counted once. The full passive salted-FO lift, its message-guessing and collision
terms, and the HQC instantiation are outside this module.

This module is deliberately **concrete-only**: it proves a finite typed probability-level game hop
and introduces no encoding, parameter family or efficiency predicate. The word-family simulator
witness and HQC-specific executable reduction remain owned by
[cslib-frontier#5279](https://github.com/cslib-community/cslib-frontier/issues/5279). That later
theorem must reuse the existing `WordPKE`/`WordReduction` and `AttackResources`/OracleTM layers,
rather than adding a parallel efficiency bundle to this finite leaf. Accordingly, this module does
not claim a native implementation, strict-PPT closure, running-time, gate-count,
static-description-size or other resource bound for either handler.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointInput`: public prefix, message and salt of a
  joint random-oracle query.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.JointReply`: named key and encryption-coin
  projections of one joint reply.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.RejectionInput`: the public-key prefix, secret
  rejection seed and full ciphertext supplied to `J`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Query`: joint-oracle, rejection-oracle and
  punctured-decapsulation queries.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.CacheState`: lazy joint, rejection and
  decapsulation caches used by the concrete handlers.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.realHandler` and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simHandler`: the decrypt/re-encrypt and
  keyless cached handlers.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.QueryBounds`: separate `qRO` and `qD` bounds.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.RandomizedAdversary`: randomized programs whose
  external query bounds hold for each fixed coin value and public challenge.

## Main results

* `Scheme.realHandler_joint_bad_eq_msgFailProb` and
  `Scheme.realHandler_decaps_bad_eq_msgFailProb`: exact one-query `CORR` probabilities for fresh
  target-prefix direct and decapsulation inputs.
* `Scheme.realHandler_rejection_bad_eq_zero`: the separate `J` channel creates no correctness
  witness.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.closeTo_run_realHandler_simHandler`:
  concrete real-to-keyless fixed-key hop.
* `Scheme.advantage_randomizedRealHandler_simHandler_le`: concrete challenge-aware randomized
  real-to-keyless advantage bound.

## References

* [L. Glabush, K. Hövelmanns, D. Stebila, *Tight Multi-challenge Security Reductions for Key
  Encapsulation Mechanisms*][GlabushHoevelmannsStebila2025], Definition 1 (printed p. 6),
  Theorem 11 and Figure 11.
* [*Hamming Quasi-Cyclic (HQC), version 5.1*][HQC2026], Section 6.2.2,
  Definition 6.2.1 and Theorem 6.4.
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open scoped Cslib ENNReal NNReal

/-- Input of the salted joint random oracle: a public-key prefix, message and salt. HQC uses
`H(ekKEM)` as the prefix. -/
structure JointInput (Prefix M Salt : Type) where
  /-- Public prefix. For a fixed scheme key, the matching target prefix uses the ciphertext-indexed
  `LD` key; every other prefix uses an independent key indexed by the full joint input. -/
  keyPrefix : Prefix
  /-- PKE plaintext whose encryption coins are derived by the oracle. -/
  message : M
  /-- Public salt carried by the KEM ciphertext. -/
  salt : Salt
  deriving DecidableEq, Fintype

/-- One reply of the joint random oracle. Named projections prevent silently swapping the source
orders `(key, coins)` and `(coins, key)`. -/
structure JointReply (K R : Type) where
  /-- Session key derived by the joint oracle. -/
  key : K
  /-- Explicit PKE encryption coins derived by the same oracle call. -/
  coins : R
  deriving DecidableEq

/-- Ciphertext of the salted transform: an underlying PKE ciphertext and its public salt. -/
structure Ciphertext (CT Salt : Type) where
  /-- Underlying PKE ciphertext. -/
  pke : CT
  /-- Salt used by the joint-oracle input. -/
  salt : Salt
  deriving DecidableEq, Fintype

/-- Source-shaped input of the implicit-rejection oracle. HQC instantiates these fields as
`H(ekPKE)`, the secret rejection seed `σ`, and `cKEM`, respectively. Keeping the fields explicit
prevents a generic opaque oracle domain from hiding the secret-prefix boundary used by the
preceding guessing hop. -/
structure RejectionInput (Prefix Sigma CT Salt : Type) where
  /-- Public prefix selecting the PKE public key. -/
  keyPrefix : Prefix
  /-- Secret implicit-rejection seed. -/
  secret : Sigma
  /-- Full salted KEM ciphertext. -/
  ciphertext : Ciphertext CT Salt
  deriving DecidableEq, Fintype

/-- Oracle queries of the salted implicit-rejection CCA experiment. `joint` returns both the KEM
key and encryption coins in one response. `rejection` is the separate `J` channel. `decaps` is
punctured at the challenge by `Query.dispatch`. -/
inductive Query (JointPrefix M Salt RejectPrefix Sigma CT : Type) where
  /-- One query to the fused key-and-coin random oracle. -/
  | joint (input : JointInput JointPrefix M Salt)
  /-- One query to the separate implicit-rejection oracle `J`. -/
  | rejection (input : RejectionInput RejectPrefix Sigma CT Salt)
  /-- One query to the decapsulation oracle. -/
  | decaps (ciphertext : Ciphertext CT Salt)

/-- Response family for `Query`. -/
abbrev Response {JointPrefix M Salt RejectPrefix Sigma CT : Type} (K R : Type) :
    Query JointPrefix M Salt RejectPrefix Sigma CT → Type
  | .joint _ => JointReply K R
  | .rejection _ => K
  | .decaps _ => Option K

namespace Query

variable {JointPrefix M Salt RejectPrefix Sigma CT K R : Type}

/-- Dispatch a salted-FO query. A decapsulation query equal to the challenge is rejected before
the supplied decapsulation handler runs. The rejection oracle is kept separate from the joint
oracle, matching HQC's `J` fallback. -/
@[simp] def dispatch [DecidableEq (Ciphertext CT Salt)] {m : Type → Type} [Monad m]
    (joint : JointInput JointPrefix M Salt → m (JointReply K R))
    (rejection : RejectionInput RejectPrefix Sigma CT Salt → m K)
    (decaps : Ciphertext CT Salt → m (Option K)) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) → m (Response K R q)
  | .joint input => joint input
  | .rejection input => rejection input
  | .decaps ciphertext => if ciphertext = challenge then pure none else decaps ciphertext

/-- Cost counting direct joint-oracle queries. One response containing both `key` and `coins`
costs exactly one. -/
@[expose, simp] def jointCost : Query JointPrefix M Salt RejectPrefix Sigma CT → ℕ
  | .joint _ => 1
  | .rejection _ => 0
  | .decaps _ => 0

/-- Cost counting decapsulation queries. -/
@[expose, simp] def decapsCost : Query JointPrefix M Salt RejectPrefix Sigma CT → ℕ
  | .joint _ => 0
  | .rejection _ => 0
  | .decaps _ => 1

end Query

/-- Single-user salted FO data needed by the correctness simulation. The public-prefix maps make
the two oracle domains explicit without fixing a byte encoding. -/
structure Scheme (PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type) where
  /-- Underlying explicit-coin public-key encryption scheme. -/
  pke : ExplicitCoinPKE PK SK M R CT
  /-- Source of joint-oracle keys and implicit-rejection keys. -/
  sampleKey : ProbComp K
  /-- Public-key prefix of the joint `G` domain. -/
  jointPrefix : PK → JointPrefix
  /-- Public-key prefix of the rejection `J` domain. -/
  rejectionPrefix : PK → RejectPrefix
  /-- Secret seed used only in the rejection `J` domain. -/
  rejectionSecret : SK → Sigma

/-- Lazy state shared by the concrete salted-FO handlers after the secret-seed guessing hop.
`jointCache` is the fused `G` table, `rejectionCache` is the now-independent adversary-visible `J`
table, and `decapsCache` is Figure 11's patched decapsulation table `LD`. -/
structure CacheState (JointPrefix M Salt RejectPrefix Sigma CT K R : Type) where
  /-- Lazy fused-oracle table. -/
  jointCache : List (JointInput JointPrefix M Salt × JointReply K R) := []
  /-- Lazy rejection-oracle table. -/
  rejectionCache : List (RejectionInput RejectPrefix Sigma CT Salt × K) := []
  /-- Lazy patched decapsulation table. -/
  decapsCache : List (Ciphertext CT Salt × K) := []

/-- The four independent tables visible after erasing target-prefix cached joint keys: joint
coins, off-target joint keys, patched decapsulation keys and rejection keys. -/
private abbrev CompletionSpec (JointPrefix M Salt RejectPrefix Sigma CT K R : Type) :=
  (((fun _ : JointInput JointPrefix M Salt => R) ⊕ₒ
      (fun _ : JointInput JointPrefix M Salt => K)) ⊕ₒ
    (fun _ : Ciphertext CT Salt => K)) ⊕ₒ
  (fun _ : RejectionInput RejectPrefix Sigma CT Salt => K)

/-- Project the independent keys of off-target joint inputs from a concrete fused-oracle table. -/
private def offTargetKeyCache {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK) :
    List (JointInput JointPrefix M Salt × JointReply K R) →
      List (JointInput JointPrefix M Salt × K)
  | [] => []
  | (input, reply) :: rest =>
    if input = ⟨S.jointPrefix pk, input.message, input.salt⟩ then
      offTargetKeyCache S pk rest
    else
      (input, reply.key) :: offTargetKeyCache S pk rest

/-- Joined partial table represented by a concrete salted-handler cache. -/
private def completionCache {JointPrefix M Salt RejectPrefix Sigma CT K R : Type}
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {PK SK : Type} (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    RandomOracle.Cache (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) :=
  RandomOracle.Cache.sum
    (RandomOracle.Cache.sum
      (RandomOracle.Cache.sum
        (RandomOracle.ofList (st.jointCache.map fun entry => (entry.1, entry.2.coins)))
        (RandomOracle.ofList (offTargetKeyCache S pk st.jointCache)))
      (RandomOracle.ofList st.decapsCache))
    (RandomOracle.ofList st.rejectionCache)

namespace Scheme

variable {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}

/-- Independent sampling laws of the coin, off-target joint-key, `LD` and `J` tables. -/
private noncomputable abbrev completionDistribution
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) :
    (q : ((JointInput JointPrefix M Salt ⊕ JointInput JointPrefix M Salt) ⊕
      Ciphertext CT Salt) ⊕
      RejectionInput RejectPrefix Sigma CT Salt) →
      PMF (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R q) :=
  OracleComp.sumHandler
    (OracleComp.sumHandler
      (OracleComp.sumHandler (fun _ => ProbComp.eval S.pke.sampleCoins)
        (fun _ => ProbComp.eval S.sampleKey))
      (fun _ => ProbComp.eval S.sampleKey))
    (fun _ => ProbComp.eval S.sampleKey)

/-- Construct the joint-oracle input selected by a public key, message and salt. -/
def jointInput (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (m : M) (salt : Salt) : JointInput JointPrefix M Salt :=
  ⟨S.jointPrefix pk, m, salt⟩

private theorem lookup_offTargetKeyCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (entries : List (JointInput JointPrefix M Salt × JointReply K R))
    (input : JointInput JointPrefix M Salt) :
    (offTargetKeyCache S pk entries).lookup input =
      if input = ⟨S.jointPrefix pk, input.message, input.salt⟩ then none
      else (entries.lookup input).map JointReply.key := by
  induction entries with
  | nil =>
    rw [offTargetKeyCache]
    simp only [List.lookup_nil, Option.map_none]
    split <;> rfl
  | cons entry rest ih =>
    rcases entry with ⟨cached, reply⟩
    rw [offTargetKeyCache]
    by_cases hcached : cached = ⟨S.jointPrefix pk, cached.message, cached.salt⟩
    · by_cases hinput : input = ⟨S.jointPrefix pk, input.message, input.salt⟩
      · rw [ite_eq_left hcached, ih]
        simp only [ite_eq_left hinput]
      · have hne : input ≠ cached := by
          rintro rfl
          exact hinput hcached
        have hbeq : (input == cached) = false := beq_eq_false_iff_ne.mpr hne
        rw [ite_eq_left hcached, ih]
        simp only [ite_eq_right hinput, List.lookup_cons, hbeq]
    · by_cases heq : input = cached
      · subst cached
        rw [ite_eq_right hcached]
        simp only [ite_eq_right hcached, List.lookup_cons, beq_self_eq_true, Option.map_some]
      · have hbeq : (input == cached) = false := beq_eq_false_iff_ne.mpr heq
        rw [ite_eq_right hcached]
        simp only [List.lookup_cons, hbeq]
        rw [ih]

private theorem offTargetKeyCache_cons_of_target
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R)
    (entries : List (JointInput JointPrefix M Salt × JointReply K R))
    (h : input = S.jointInput pk input.message input.salt) :
    offTargetKeyCache S pk ((input, reply) :: entries) = offTargetKeyCache S pk entries := by
  change input = ⟨S.jointPrefix pk, input.message, input.salt⟩ at h
  rw [offTargetKeyCache]
  rw [ite_eq_left h]

private theorem offTargetKeyCache_cons_of_not_target
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R)
    (entries : List (JointInput JointPrefix M Salt × JointReply K R))
    (h : input ≠ S.jointInput pk input.message input.salt) :
    offTargetKeyCache S pk ((input, reply) :: entries) =
      (input, reply.key) :: offTargetKeyCache S pk entries := by
  change input ≠ ⟨S.jointPrefix pk, input.message, input.salt⟩ at h
  rw [offTargetKeyCache]
  rw [ite_eq_right h]

/-- Construct the source-shaped `J(H(ekPKE) ∥ σ ∥ cKEM)` input. -/
def rejectionInput (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    RejectionInput RejectPrefix Sigma CT Salt :=
  ⟨S.rejectionPrefix pk, S.rejectionSecret sk, ciphertext⟩

/-- Patched joint reply as a program over the erased coin and `LD` tables. -/
private def completionJointProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt) :
    OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (JointReply K R) := do
  let coins ← OracleComp.query (spec :=
    CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inl (.inl input)))
  let key ← if input = S.jointInput pk input.message input.salt then
    let ciphertext : Ciphertext CT Salt :=
      ⟨S.pke.encDet pk input.message coins, input.salt⟩
    OracleComp.query (spec :=
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))
  else
    OracleComp.query (spec :=
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inl (.inr input)))
  return ⟨key, coins⟩

/-- Prefetch decapsulation as a program over the erased independent tables. -/
private noncomputable def completionPrefetchDecapsProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (Option K) := by
  classical
  exact do
    match S.pke.dec sk ciphertext.pke with
    | none => some <$> OracleComp.query (spec :=
        CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))
    | some message =>
      let reply ← S.completionJointProgram pk (S.jointInput pk message ciphertext.salt)
      if S.pke.encDet pk message reply.coins = ciphertext.pke then
        return some reply.key
      else
        some <$> OracleComp.query (spec :=
          CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R) (.inl (.inr ciphertext))

/-- One prefetch-handler call as a program over the erased independent tables. -/
private noncomputable def completionPrefetchProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)
        (Response K R q) := by
  classical
  exact Query.dispatch
    (S.completionJointProgram pk)
    (fun input => OracleComp.query (Sum.inr input))
    (S.completionPrefetchDecapsProgram pk sk) challenge

/-- One keyless-handler call as a program over the erased independent tables. -/
private noncomputable def completionSimProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)
        (Response K R q) := by
  classical
  exact Query.dispatch
    (S.completionJointProgram pk)
    (fun input => OracleComp.query (Sum.inr input))
    (fun ciphertext => some <$> OracleComp.query (Sum.inl (Sum.inr ciphertext))) challenge

/-- On a completed table, prefetch decapsulation and keyless `LD` lookup return the same answer. -/
private theorem interpret_completionPrefetchProgram_eq_simProgram
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (table : (q : ((JointInput JointPrefix M Salt ⊕ JointInput JointPrefix M Salt) ⊕
      Ciphertext CT Salt) ⊕
      RejectionInput RejectPrefix Sigma CT Salt) →
      CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R q)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) :
    OracleComp.interpret (fun query => PMF.pure (table query))
        (S.completionPrefetchProgram pk sk challenge q) =
      OracleComp.interpret (fun query => PMF.pure (table query))
        (S.completionSimProgram pk challenge q) := by
  classical
  rcases q with input | input | ciphertext
  · rfl
  · rfl
  · rcases ciphertext with ⟨pkeCiphertext, salt⟩
    by_cases hc : (⟨pkeCiphertext, salt⟩ : Ciphertext CT Salt) = challenge
    · simp [completionPrefetchProgram, completionSimProgram, Query.dispatch, hc]
    · simp only [completionPrefetchProgram, completionSimProgram, Query.dispatch, hc, ↓reduceIte]
      cases hdec : S.pke.dec sk pkeCiphertext with
      | none => simp only [completionPrefetchDecapsProgram, hdec]
      | some message =>
        simp only [completionPrefetchDecapsProgram, completionJointProgram, jointInput, hdec,
          OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_query,
          PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.pure_map, PMF.pure_bind]
        simp only [ite_true]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
          PMF.pure_bind]
        split_ifs with h
        · rw [h]
          simp only [OracleComp.interpret_pure, PMF.monad_pure_eq_pure]
        · simp only [OracleComp.interpret_map, OracleComp.interpret_query,
            PMF.monad_map_eq_map, PMF.pure_map]

private noncomputable def cacheJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) :=
  fun st =>
    match st.jointCache.lookup input with
    | some reply => PMF.pure (reply, st)
    | none =>
      (ProbComp.eval S.pke.sampleCoins).bind fun coins =>
        if input = S.jointInput pk input.message input.salt then
          let ciphertext : Ciphertext CT Salt :=
            ⟨S.pke.encDet pk input.message coins, input.salt⟩
          if valid input.message coins then
            match st.decapsCache.lookup ciphertext with
            | some key =>
              let reply := ⟨key, coins⟩
              PMF.pure (reply, { st with jointCache := (input, reply) :: st.jointCache })
            | none =>
              (ProbComp.eval S.sampleKey).map fun key =>
                let reply := ⟨key, coins⟩
                (reply, { st with
                  jointCache := (input, reply) :: st.jointCache
                  decapsCache := (ciphertext, key) :: st.decapsCache })
          else
            (ProbComp.eval S.sampleKey).map fun key =>
              let reply := ⟨key, coins⟩
              (reply, { st with jointCache := (input, reply) :: st.jointCache })
        else
          (ProbComp.eval S.sampleKey).map fun key =>
            let reply := ⟨key, coins⟩
            (reply, { st with jointCache := (input, reply) :: st.jointCache })

/-- Coupled real joint oracle. A correctly decrypting target-prefix encryption patches the
decapsulation cache, while a failing one is left unpatched and is exactly a `CORR` witness.
An off-target query instead samples an independent key indexed by its full joint input and does
not inspect or change the decapsulation cache. -/
noncomputable def realJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) := by
  classical
  exact S.cacheJoint pk
    (fun m coins => S.pke.dec sk (S.pke.encDet pk m coins) = some m) input

/-- Keyless simulated joint oracle. A fresh target-prefix query patches the decapsulation cache;
a fresh off-target query samples an independent key indexed by its full joint input without
inspecting or changing that cache. It contains no secret-key argument. -/
noncomputable def simJoint [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (JointReply K R) :=
  S.cacheJoint pk (fun _ _ => True) input

/-- Post-secret-seed-guessing adversary-visible rejection oracle. It is independent of `LD`, is
shared by both games, and never changes the correctness cache. -/
noncomputable def rejection [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (input : RejectionInput RejectPrefix Sigma CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF K :=
  fun st =>
    match st.rejectionCache.lookup input with
    | some key => PMF.pure (key, st)
    | none => (ProbComp.eval S.sampleKey).map fun key =>
      (key, { st with rejectionCache := (input, key) :: st.rejectionCache })

/-- Figure-11 decapsulation table. This is independent of the adversary-visible `J` table after
the preceding secret-seed guessing hop. -/
noncomputable def decapsKey [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF K :=
  fun st =>
    match st.decapsCache.lookup ciphertext with
    | some key => PMF.pure (key, st)
    | none => (ProbComp.eval S.sampleKey).map fun key =>
      (key, { st with decapsCache := (ciphertext, key) :: st.decapsCache })

/-- Real decrypt/re-encrypt decapsulation path. Its implicit call to the fused joint oracle is
why a decapsulation query contributes one further correctness opportunity. -/
noncomputable def realDecaps [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) := by
  classical
  exact do
    match S.pke.dec sk ciphertext.pke with
    | none => some <$> S.decapsKey ciphertext
    | some message =>
      let reply ← S.realJoint pk sk (S.jointInput pk message ciphertext.salt)
      if S.pke.encDet pk message reply.coins = ciphertext.pke then
        return some reply.key
      else
        some <$> S.decapsKey ciphertext

/-- Proof-only prefetch decapsulation path. It decrypts and re-encrypts exactly as `realDecaps`,
but uses `simJoint`, so every joint reply it creates is linked to the patched `LD` table. -/
private noncomputable def prefetchDecaps [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) := by
  classical
  exact do
    match S.pke.dec sk ciphertext.pke with
    | none => some <$> S.decapsKey ciphertext
    | some message =>
      let reply ← S.simJoint pk (S.jointInput pk message ciphertext.salt)
      if S.pke.encDet pk message reply.coins = ciphertext.pke then
        return some reply.key
      else
        some <$> S.decapsKey ciphertext

/-- Keyless cached decapsulation simulator. Target-prefix direct joint queries patch
`decapsCache`; a fresh decapsulation query samples the same independent fallback table without
decrypting. Off-target joint keys do not use this table. -/
noncomputable def simDecaps [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt) :
    StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Option K) :=
  some <$> S.decapsKey ciphertext

/-- Concrete punctured post-secret-seed-guessing real handler. Challenge rejection happens in the
common dispatcher before `realDecaps` can decrypt or query the joint oracle. -/
noncomputable def realHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.realJoint pk sk) S.rejection (S.realDecaps pk sk) challenge

/-- Proof-only prefetch handler used between the real and keyless games. Its direct joint queries
use `simJoint`; decapsulation still decrypts, but its implicit joint query also uses `simJoint`.
Thus it has the real handler's cache evolution on good executions and the keyless handler's
lookup-visible joint/`LD` invariant. -/
private noncomputable def prefetchHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.simJoint pk) S.rejection (S.prefetchDecaps pk sk) challenge

/-- Concrete punctured post-secret-seed-guessing keyless handler. Its type has no secret key; the
independent `J` table remains a source-shaped adversary query, while decapsulation uses only
`decapsCache`. -/
noncomputable def simHandler [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (Response K R q) :=
  Query.dispatch (S.simJoint pk) S.rejection S.simDecaps challenge

/-- Message/coin projection of the target-prefix entries in the fused joint-oracle cache. -/
private def coinCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : List (M × R) :=
  (st.jointCache.filter fun entry =>
    entry.1 = S.jointInput pk entry.1.message entry.1.salt).map fun entry =>
      (entry.1.message, entry.2.coins)

/-- Every target-prefix fused-oracle entry in the cache decrypts correctly for its message. -/
def GoodCache [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : Prop :=
  S.pke.GoodCache pk sk (S.coinCache pk st)

/-- The empty salted-FO cache contains no correctness witness. -/
@[simp] theorem GoodCache.empty
    [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK) (sk : SK) :
    S.GoodCache pk sk ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) := by
  simp [GoodCache, coinCache, ExplicitCoinPKE.GoodCache]

/-- Every cached target-prefix joint reply carries the `LD` key of its derived ciphertext. -/
private def Linked [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) : Prop :=
  ∀ input reply, (input, reply) ∈ st.jointCache →
    input = S.jointInput pk input.message input.salt →
    st.decapsCache.lookup ⟨S.pke.encDet pk input.message reply.coins, input.salt⟩ =
      some reply.key

/-- Goodness is inherited by a state whose joint cache is a subcache. -/
private theorem GoodCache.of_subset
    [DecidableEq (JointInput JointPrefix M Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK}
    {st st' : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (h : S.GoodCache pk sk st')
    (hsub : ∀ entry ∈ st.jointCache, entry ∈ st'.jointCache) : S.GoodCache pk sk st := by
  apply ExplicitCoinPKE.GoodCache.of_subset h
  intro entry hentry
  obtain ⟨cached, hcached, heq⟩ := List.mem_map.mp hentry
  obtain ⟨hcached, htarget⟩ := List.mem_filter.mp hcached
  exact List.mem_map.mpr ⟨cached, List.mem_filter.mpr ⟨hsub cached hcached, htarget⟩, heq⟩

private theorem simJoint_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (input : JointInput JointPrefix M Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.simJoint pk input st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionJointProgram pk input)).run (completionCache S pk st) := by
  cases hlookup : st.jointCache.lookup input with
  | some reply =>
    have hmem : (input, reply) ∈ st.jointCache := by
      obtain ⟨left, right, htable, -⟩ := List.lookup_eq_some_iff.mp hlookup
      rw [htable]
      simp
    simp only [simJoint, cacheJoint, hlookup]
    simp only [completionCache]
    simp only [completionJointProgram, completionDistribution, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_query]
    rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl,
      RandomOracle.answer_sum_inl, PMF.map_comp]
    simp only [RandomOracle.answer, RandomOracle.ofList,
      List.lookup_map_snd, hlookup, Option.map_some,
      PMF.monad_bind_eq_bind, PMF.pure_map, PMF.pure_bind, Function.comp_apply]
    by_cases htarget : input = S.jointInput pk input.message input.salt
    · have hdecaps := hlinked input reply hmem htarget
      rw [ite_eq_left htarget]
      simp only [OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.run_interpret_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr]
      simp only [RandomOracle.answer, RandomOracle.ofList, hdecaps, PMF.pure_map, PMF.pure_bind]
    · have hkey : (offTargetKeyCache S pk st.jointCache).lookup input = some reply.key := by
        have hoff : input ≠ ⟨S.jointPrefix pk, input.message, input.salt⟩ := by
          simpa only [jointInput] using htarget
        rw [S.lookup_offTargetKeyCache pk st.jointCache input, ite_eq_right hoff, hlookup]
        rfl
      rw [ite_eq_right htarget]
      simp only [OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.run_interpret_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl,
        RandomOracle.answer_sum_inr]
      simp only [RandomOracle.answer, RandomOracle.ofList, hkey, PMF.pure_map, PMF.pure_bind]
  | none =>
    have hcoins : RandomOracle.ofList
        (st.jointCache.map fun e => (e.1, e.2.coins)) input = none := by
      simp only [RandomOracle.ofList, List.lookup_map_snd, hlookup, Option.map_none]
    simp only [simJoint, cacheJoint, hlookup]
    simp only [completionCache]
    simp only [completionJointProgram, completionDistribution, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_query]
    rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl,
      RandomOracle.answer_sum_inl, PMF.map_comp,
      RandomOracle.answer_of_none _ _ _ hcoins]
    simp only [PMF.monad_bind_eq_bind,
      PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
    apply PMF.bind_congr_on_support
    intro coins _
    by_cases htarget : input = S.jointInput pk input.message input.salt
    · rw [ite_eq_left htarget, ite_eq_left htarget]
      simp only [OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.run_interpret_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      cases hdec : st.decapsCache.lookup
        ⟨S.pke.encDet pk input.message coins, input.salt⟩ with
      | some key =>
        rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp]
        simp only [ite_true, PMF.pure_map]
        simp only [RandomOracle.answer, RandomOracle.ofList, hdec,
          S.offTargetKeyCache_cons_of_target pk input _ st.jointCache htarget,
          RandomOracle.ofList_cons, PMF.pure_map, List.map_cons, Function.comp_def]
        simp only [PMF.pure_bind]
      | none =>
        rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp]
        simp only [ite_true]
        simp only [RandomOracle.answer, RandomOracle.ofList, hdec,
          PMF.map, Function.comp_def]
        simp only [PMF.bind_bind, PMF.pure_bind,
          S.offTargetKeyCache_cons_of_target pk input _ st.jointCache htarget,
          RandomOracle.ofList_cons, List.map_cons]
    · have hkey : RandomOracle.ofList (offTargetKeyCache S pk st.jointCache) input = none := by
        have hoff : input ≠ ⟨S.jointPrefix pk, input.message, input.salt⟩ := by
          simpa only [jointInput] using htarget
        simp only [RandomOracle.ofList]
        rw [S.lookup_offTargetKeyCache pk st.jointCache input, ite_eq_right hoff, hlookup]
        rfl
      rw [ite_eq_right htarget, ite_eq_right htarget]
      simp only [OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.run_interpret_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl,
        RandomOracle.answer_sum_inr, PMF.map_comp,
        RandomOracle.answer_of_none _ _ _ hkey]
      simp only [RandomOracle.ofList_cons,
        S.offTargetKeyCache_cons_of_not_target pk input _ st.jointCache htarget,
        PMF.map, List.map_cons, Function.comp_def]
      simp only [PMF.bind_bind, PMF.pure_bind]

private theorem rejection_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (S.rejection input st).map (fun z => (z.1, completionCache S pk z.2)) =
      RandomOracle.answer S.completionDistribution (.inr input) (completionCache S pk st) := by
  simp only [completionCache]
  rw [RandomOracle.answer_sum_inr, ← RandomOracle.memoize_map_ofList, PMF.map_comp]
  cases hlookup : st.rejectionCache.lookup input <;>
    simp only [rejection, memoize, hlookup, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def]

private theorem decapsKey_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK)
    (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (S.decapsKey ciphertext st).map (fun z => (z.1, completionCache S pk z.2)) =
      RandomOracle.answer S.completionDistribution (.inl (.inr ciphertext))
        (completionCache S pk st) := by
  simp only [completionCache]
  rw [RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp,
    ← RandomOracle.memoize_map_ofList, PMF.map_comp]
  cases hlookup : st.decapsCache.lookup ciphertext <;>
    simp only [decapsKey, memoize, hlookup, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def]

private theorem Linked.of_simJoint
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {input : JointInput JointPrefix M Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.simJoint pk input st).support) : S.Linked pk z.2 := by
  simp only [simJoint, cacheJoint] at hz
  split at hz
  · simp only [PMF.mem_support_pure_iff] at hz
    subst z
    exact hlinked
  · rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨coins, _, hz⟩ := hz
    split at hz
    next htarget =>
      simp only [ite_true] at hz
      split at hz
      · simp only [PMF.mem_support_pure_iff] at hz
        subst z
        intro cached reply hmem hcached
        rcases List.mem_cons.mp hmem with hnew | hold
        · cases hnew
          simpa
        · exact hlinked cached reply hold hcached
      · rw [PMF.mem_support_map_iff] at hz
        obtain ⟨key, _, rfl⟩ := hz
        intro cached reply hmem hcached
        rcases List.mem_cons.mp hmem with hnew | hold
        · cases hnew
          simp
        · have holdLinked := hlinked cached reply hold hcached
          let oldCiphertext : Ciphertext CT Salt :=
            ⟨S.pke.encDet pk cached.message reply.coins, cached.salt⟩
          let newCiphertext : Ciphertext CT Salt :=
            ⟨S.pke.encDet pk input.message coins, input.salt⟩
          have holdLinked' : st.decapsCache.lookup oldCiphertext = some reply.key := by
            simpa only [oldCiphertext] using holdLinked
          by_cases hc : oldCiphertext = newCiphertext
          · have hnone : st.decapsCache.lookup newCiphertext = none := by assumption
            rw [hc, hnone] at holdLinked'
            cases holdLinked'
          · have hbeq : (oldCiphertext == newCiphertext) = false :=
              beq_eq_false_iff_ne.mpr hc
            simpa only [oldCiphertext, newCiphertext, List.lookup_cons, hbeq] using holdLinked'
    next htarget =>
      rw [PMF.mem_support_map_iff] at hz
      obtain ⟨key, _, rfl⟩ := hz
      intro cached reply hmem hcached
      rcases List.mem_cons.mp hmem with hnew | hold
      · cases hnew
        exact (htarget hcached).elim
      · exact hlinked cached reply hold hcached

private theorem Linked.of_decapsKey
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {ciphertext : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.decapsKey ciphertext st).support) : S.Linked pk z.2 := by
  cases hlookup : st.decapsCache.lookup ciphertext with
  | some key =>
    simp only [decapsKey, hlookup, PMF.mem_support_pure_iff] at hz
    subst z
    exact hlinked
  | none =>
    simp only [decapsKey, hlookup, PMF.mem_support_map_iff] at hz
    obtain ⟨key, _, rfl⟩ := hz
    intro input reply hmem htarget
    have hold := hlinked input reply hmem htarget
    let derived : Ciphertext CT Salt :=
      ⟨S.pke.encDet pk input.message reply.coins, input.salt⟩
    have hold' : st.decapsCache.lookup derived = some reply.key := by
      simpa only [derived] using hold
    by_cases hc : derived = ciphertext
    · rw [hc, hlookup] at hold'
      cases hold'
    · have hbeq : (derived == ciphertext) = false := beq_eq_false_iff_ne.mpr hc
      simpa only [derived, List.lookup_cons, hbeq] using hold'

private theorem Linked.of_rejection
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {input : RejectionInput RejectPrefix Sigma CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.rejection input st).support) : S.Linked pk z.2 := by
  cases hlookup : st.rejectionCache.lookup input with
  | some key =>
    simp only [rejection, hlookup, PMF.mem_support_pure_iff] at hz
    subst z
    exact hlinked
  | none =>
    simp only [rejection, hlookup, PMF.mem_support_map_iff] at hz
    obtain ⟨key, _, rfl⟩ := hz
    exact hlinked

private theorem prefetchDecaps_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.prefetchDecaps pk sk ciphertext st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionPrefetchDecapsProgram pk sk ciphertext)).run (completionCache S pk st) := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    unfold prefetchDecaps
    simp only [hdec]
    change PMF.map (fun z => (z.1, completionCache S pk z.2))
      (PMF.map (fun z => (some z.1, z.2)) (S.decapsKey ciphertext st)) = _
    rw [PMF.map_comp]
    simp only [completionPrefetchDecapsProgram, hdec,
      OracleComp.run_interpret_map, OracleComp.run_interpret_query, Function.comp_def]
    simpa only [PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
      PMF.monad_map_eq_map] using
      congrArg (PMF.map (Prod.map some id))
        (S.decapsKey_map_completionCache pk ciphertext st)
  | some message =>
    unfold prefetchDecaps
    simp only [hdec]
    have hrun :
        ((S.simJoint pk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
            if S.pke.encDet pk message reply.coins = ciphertext.pke then
              pure (some reply.key)
            else
              some <$> S.decapsKey ciphertext) st) =
          S.simJoint pk (S.jointInput pk message ciphertext.salt) st >>= fun z =>
            ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
                pure (some z.1.key)
              else
                some <$> S.decapsKey ciphertext) z.2) :=
      StateT.run_bind _ _ _
    rw [hrun, PMF.monad_bind_eq_bind]
    rw [PMF.map_bind]
    simp only [completionPrefetchDecapsProgram, hdec, OracleComp.run_interpret_bind,
      PMF.monad_bind_eq_bind]
    rw [← S.simJoint_map_completionCache pk (S.jointInput pk message ciphertext.salt) st hlinked,
      PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro z _
    split <;> rename_i henc
    · simp only [Function.comp_def, henc, ↓reduceIte, OracleComp.run_interpret_pure,
        PMF.monad_pure_eq_pure]
      change PMF.map (fun y => (y.1, completionCache S pk y.2))
        (PMF.pure (some z.1.key, z.2)) =
          PMF.pure (some z.1.key, completionCache S pk z.2)
      exact PMF.pure_map _ _
    · have hmap :
          ((some <$> S.decapsKey ciphertext) z.2) =
            (fun p => (some p.1, p.2)) <$> S.decapsKey ciphertext z.2 :=
        StateT.run_map (fun key : K => some key) (S.decapsKey ciphertext) z.2
      rw [hmap, PMF.monad_map_eq_map]
      simpa only [henc, ↓reduceIte, OracleComp.run_interpret_map,
        OracleComp.run_interpret_query, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
        PMF.monad_map_eq_map] using
        congrArg (PMF.map (Prod.map some id))
          (S.decapsKey_map_completionCache pk ciphertext z.2)

private theorem Linked.of_prefetchDecaps
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK} {ciphertext : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st)
    {z : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.prefetchDecaps pk sk ciphertext st).support) : S.Linked pk z.2 := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    unfold prefetchDecaps at hz
    simp only [hdec] at hz
    change z ∈ (PMF.map (fun x => (some x.1, x.2))
      (S.decapsKey ciphertext st)).support at hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨key, hkey, rfl⟩ := hz
    exact hlinked.of_decapsKey hkey
  | some message =>
    unfold prefetchDecaps at hz
    simp only [hdec] at hz
    have hrun :
        ((S.simJoint pk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
            if S.pke.encDet pk message reply.coins = ciphertext.pke then
              pure (some reply.key)
            else
              some <$> S.decapsKey ciphertext) st) =
          S.simJoint pk (S.jointInput pk message ciphertext.salt) st >>= fun y =>
            ((if S.pke.encDet pk message y.1.coins = ciphertext.pke then
                pure (some y.1.key)
              else
                some <$> S.decapsKey ciphertext) y.2) :=
      StateT.run_bind _ _ _
    rw [hrun, PMF.monad_bind_eq_bind] at hz
    rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨reply, hreply, hz⟩ := hz
    have hmiddle := hlinked.of_simJoint hreply
    split at hz
    · change z ∈ (PMF.pure (some reply.1.key, reply.2)).support at hz
      rw [PMF.mem_support_pure_iff] at hz
      subst z
      exact hmiddle
    · have hmap :
          ((some <$> S.decapsKey ciphertext) reply.2) =
            (fun p => (some p.1, p.2)) <$> S.decapsKey ciphertext reply.2 :=
        StateT.run_map (fun key : K => some key) (S.decapsKey ciphertext) reply.2
      rw [hmap, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hz
      obtain ⟨key, hkey, rfl⟩ := hz
      exact hmiddle.of_decapsKey hkey

private theorem Linked.of_prefetchHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK} {challenge : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st) (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {z : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.prefetchHandler pk sk challenge q st).support) : S.Linked pk z.2 := by
  rcases q with input | input | ciphertext
  · exact hlinked.of_simJoint hz
  · exact hlinked.of_rejection hz
  · by_cases hc : ciphertext = challenge
    · simp only [prefetchHandler, Query.dispatch, hc, ↓reduceIte] at hz
      change z ∈ (PMF.pure (none, st)).support at hz
      rw [PMF.mem_support_pure_iff] at hz
      subst z
      exact hlinked
    · apply hlinked.of_prefetchDecaps
      simpa only [prefetchHandler, Query.dispatch, hc, ↓reduceIte] using hz

private theorem Linked.of_simHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {challenge : Ciphertext CT Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hlinked : S.Linked pk st) (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {z : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.simHandler pk challenge q st).support) : S.Linked pk z.2 := by
  rcases q with input | input | ciphertext
  · exact hlinked.of_simJoint hz
  · exact hlinked.of_rejection hz
  · by_cases hc : ciphertext = challenge
    · simp only [simHandler, Query.dispatch, hc, ↓reduceIte] at hz
      change z ∈ (PMF.pure (none, st)).support at hz
      rw [PMF.mem_support_pure_iff] at hz
      subst z
      exact hlinked
    · simp only [simHandler, Query.dispatch, hc, ↓reduceIte, simDecaps] at hz
      change z ∈ (PMF.map (fun x => (some x.1, x.2))
        (S.decapsKey ciphertext st)).support at hz
      rw [PMF.mem_support_map_iff] at hz
      obtain ⟨key, hkey, rfl⟩ := hz
      exact hlinked.of_decapsKey hkey

private theorem prefetchHandler_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.prefetchHandler pk sk challenge q st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionPrefetchProgram pk sk challenge q)).run (completionCache S pk st) := by
  rcases q with input | input | ciphertext
  · simpa only [prefetchHandler, completionPrefetchProgram, Query.dispatch] using
      S.simJoint_map_completionCache pk input st hlinked
  · simpa only [prefetchHandler, completionPrefetchProgram, Query.dispatch,
      OracleComp.run_interpret_query] using
      S.rejection_map_completionCache pk input st
  · by_cases hc : ciphertext = challenge
    · simp only [prefetchHandler, completionPrefetchProgram, Query.dispatch, hc, ↓reduceIte]
      change PMF.map (fun z => (z.1, completionCache S pk z.2)) (PMF.pure (none, st)) =
        PMF.pure (none, completionCache S pk st)
      exact PMF.pure_map _ _
    · simpa only [prefetchHandler, completionPrefetchProgram, Query.dispatch, hc, ↓reduceIte]
        using S.prefetchDecaps_map_completionCache pk sk ciphertext st hlinked

private theorem simHandler_map_completionCache
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hlinked : S.Linked pk st) :
    (S.simHandler pk challenge q st).map (fun z => (z.1, completionCache S pk z.2)) =
      (OracleComp.interpret (RandomOracle.answer S.completionDistribution)
        (S.completionSimProgram pk challenge q)).run (completionCache S pk st) := by
  rcases q with input | input | ciphertext
  · simpa only [simHandler, completionSimProgram, Query.dispatch] using
      S.simJoint_map_completionCache pk input st hlinked
  · simpa only [simHandler, completionSimProgram, Query.dispatch,
      OracleComp.run_interpret_query] using
      S.rejection_map_completionCache pk input st
  · by_cases hc : ciphertext = challenge
    · simp only [simHandler, completionSimProgram, Query.dispatch, hc, ↓reduceIte]
      change PMF.map (fun z => (z.1, completionCache S pk z.2)) (PMF.pure (none, st)) =
        PMF.pure (none, completionCache S pk st)
      exact PMF.pure_map _ _
    · simp only [simHandler, completionSimProgram, Query.dispatch, hc, ↓reduceIte,
        simDecaps, OracleComp.run_interpret_map, OracleComp.run_interpret_query]
      change PMF.map (fun z => (z.1, completionCache S pk z.2))
        (PMF.map (fun x => (some x.1, x.2)) (S.decapsKey ciphertext st)) =
          PMF.map (fun y => (some y.1, y.2))
            (RandomOracle.answer S.completionDistribution (.inl (.inr ciphertext))
              (completionCache S pk st))
      simpa only [PMF.map_comp, Function.comp_def] using
        congrArg (PMF.map fun y => (some y.1, y.2))
          (S.decapsKey_map_completionCache pk ciphertext st)

/-- The proof-only prefetch handler and observable keyless handler have exactly the same output
law from empty caches. Their private final caches are deliberately marginalized. -/
private theorem run_prefetchHandler_eq_simHandler
    [Finite JointPrefix] [Finite M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A) :
    ((OracleComp.interpret (S.prefetchHandler pk sk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst =
      ((OracleComp.interpret (S.simHandler pk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst := by
  let _ : Fintype JointPrefix := Fintype.ofFinite JointPrefix
  let _ : Fintype M := Fintype.ofFinite M
  let _ : Fintype Salt := Fintype.ofFinite Salt
  let _ : Fintype RejectPrefix := Fintype.ofFinite RejectPrefix
  let _ : Fintype Sigma := Fintype.ofFinite Sigma
  let _ : Fintype CT := Fintype.ofFinite CT
  let initial : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R := {}
  let lazyOracle := RandomOracle.answer S.completionDistribution
  let prefetchBase := OracleComp.interpret (S.completionPrefetchProgram pk sk challenge) program
  let simBase := OracleComp.interpret (S.completionSimProgram pk challenge) program
  let completionHandlerType :=
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT (RandomOracle.Cache
        (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)) PMF
        (Response K R q)
  let prefetchCompletionHandler : completionHandlerType := fun q =>
    OracleComp.interpret lazyOracle (S.completionPrefetchProgram pk sk challenge q)
  let simCompletionHandler : completionHandlerType := fun q =>
    OracleComp.interpret lazyOracle (S.completionSimProgram pk challenge q)
  have hinitial : S.Linked pk initial := by simp [initial, Linked]
  have hempty : completionCache S pk initial =
      (fun _ => none : RandomOracle.Cache
        (CompletionSpec JointPrefix M Salt RejectPrefix Sigma CT K R)) := by
    funext q
    rcases q with ((input | input) | ciphertext) | input <;> rfl
  have hp := OracleComp.run_interpret_map_state_of_invariant
    (S.prefetchHandler pk sk challenge)
    prefetchCompletionHandler
    (completionCache S pk) (S.Linked pk)
    (fun q st hlinked _ _ hmem => hlinked.of_prefetchHandler q hmem)
    (fun q st hlinked => S.prefetchHandler_map_completionCache pk sk challenge q st hlinked)
    program initial hinitial
  have hs := OracleComp.run_interpret_map_state_of_invariant
    (S.simHandler pk challenge)
    simCompletionHandler
    (completionCache S pk) (S.Linked pk)
    (fun q st hlinked _ _ hmem => hlinked.of_simHandler q hmem)
    (fun q st hlinked => S.simHandler_map_completionCache pk challenge q st hlinked)
    program initial hinitial
  have hpout := congrArg (PMF.map Prod.fst) hp
  have hsout := congrArg (PMF.map Prod.fst) hs
  simp only [PMF.map_comp, Function.comp_def] at hpout hsout
  calc
    _ = ((OracleComp.interpret prefetchCompletionHandler program).run
        (fun _ => none)).map Prod.fst := by
      simpa only [initial, hempty] using hpout
    _ = ((OracleComp.interpret lazyOracle prefetchBase).run (fun _ => none)).map Prod.fst := by
      simp only [prefetchCompletionHandler, prefetchBase, OracleComp.interpret_interpret]
    _ = (PMF.pi S.completionDistribution).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q)) prefetchBase := by
      exact (RandomOracle.interpret_eq_lazy S.completionDistribution prefetchBase).symm
    _ = (PMF.pi S.completionDistribution).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q)) simBase := by
      congr 1 with table : 1
      simp only [prefetchBase, simBase, OracleComp.interpret_interpret]
      congr 1 with q : 1
      exact S.interpret_completionPrefetchProgram_eq_simProgram pk sk challenge table q
    _ = ((OracleComp.interpret lazyOracle simBase).run (fun _ => none)).map Prod.fst := by
      exact RandomOracle.interpret_eq_lazy S.completionDistribution simBase
    _ = ((OracleComp.interpret simCompletionHandler program).run
        (fun _ => none)).map Prod.fst := by
      simp only [simCompletionHandler, simBase, OracleComp.interpret_interpret]
    _ = _ := by
      simpa only [initial, hempty] using hsout.symm

private theorem cacheJoint_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.cacheJoint pk valid input st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ z.2.jointCache := by
  simp only [cacheJoint] at hz
  split at hz
  · simp only [PMF.mem_support_pure_iff] at hz
    subst z
    exact fun _ hentry => hentry
  · rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨coins, _, hz⟩ := hz
    split at hz
    · split at hz
      · split at hz
        · simp only [PMF.mem_support_pure_iff] at hz
          subst z
          exact fun entry hentry => List.mem_cons_of_mem _ hentry
        · rw [PMF.mem_support_map_iff] at hz
          obtain ⟨key, _, rfl⟩ := hz
          exact fun entry hentry => List.mem_cons_of_mem _ hentry
      · rw [PMF.mem_support_map_iff] at hz
        obtain ⟨key, _, rfl⟩ := hz
        exact fun entry hentry => List.mem_cons_of_mem _ hentry
    · rw [PMF.mem_support_map_iff] at hz
      obtain ⟨key, _, rfl⟩ := hz
      exact fun entry hentry => List.mem_cons_of_mem _ hentry

private theorem cacheJoint_mem_jointCache
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.cacheJoint pk valid input st).support) :
    (input, z.1) ∈ z.2.jointCache := by
  simp only [cacheJoint] at hz
  split at hz
  next reply hlookup =>
    simp only [PMF.mem_support_pure_iff] at hz
    subst z
    obtain ⟨left, right, htable, -⟩ := List.lookup_eq_some_iff.mp hlookup
    rw [htable]
    simp
  next hlookup =>
    rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨coins, _, hz⟩ := hz
    split at hz
    · split at hz
      · split at hz
        · simp only [PMF.mem_support_pure_iff] at hz
          subst z
          exact List.mem_cons_self
        · rw [PMF.mem_support_map_iff] at hz
          obtain ⟨key, _, rfl⟩ := hz
          exact List.mem_cons_self
      · rw [PMF.mem_support_map_iff] at hz
        obtain ⟨key, _, rfl⟩ := hz
        exact List.mem_cons_self
    · rw [PMF.mem_support_map_iff] at hz
      obtain ⟨key, _, rfl⟩ := hz
      exact List.mem_cons_self

private theorem cacheJoint_jointCache_eq_or_cons
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) (pk : PK)
    (valid : M → R → Prop) [∀ m r, Decidable (valid m r)]
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.cacheJoint pk valid input st).support) :
    z.2.jointCache = st.jointCache ∨
      z.2.jointCache = (input, z.1) :: st.jointCache := by
  simp only [cacheJoint] at hz
  split at hz
  · simp only [PMF.mem_support_pure_iff] at hz
    subst z
    exact Or.inl rfl
  · rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨coins, _, hz⟩ := hz
    split at hz
    · split at hz
      · split at hz
        · simp only [PMF.mem_support_pure_iff] at hz
          subst z
          exact Or.inr rfl
        · rw [PMF.mem_support_map_iff] at hz
          obtain ⟨key, _, rfl⟩ := hz
          exact Or.inr rfl
      · rw [PMF.mem_support_map_iff] at hz
        obtain ⟨key, _, rfl⟩ := hz
        exact Or.inr rfl
    · rw [PMF.mem_support_map_iff] at hz
      obtain ⟨key, _, rfl⟩ := hz
      exact Or.inr rfl

private theorem GoodCache.of_cacheJoint
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K} {pk : PK} {sk : SK}
    {valid : M → R → Prop} [∀ m r, Decidable (valid m r)]
    {input : JointInput JointPrefix M Salt}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st)
    (hcoins : input = S.jointInput pk input.message input.salt →
      S.pke.dec sk (S.pke.encDet pk input.message z.1.coins) = some input.message)
    (hz : z ∈ (S.cacheJoint pk valid input st).support) : S.GoodCache pk sk z.2 := by
  unfold GoodCache ExplicitCoinPKE.GoodCache at hs ⊢
  rcases S.cacheJoint_jointCache_eq_or_cons pk valid input hz with heq | heq
  · have hcoinCache : S.coinCache pk z.2 = S.coinCache pk st := by
      unfold coinCache
      rw [heq]
    simpa only [hcoinCache] using hs
  · by_cases htarget : input = S.jointInput pk input.message input.salt
    · have hcoinCache : S.coinCache pk z.2 =
          (input.message, z.1.coins) :: S.coinCache pk st := by
        unfold coinCache
        rw [heq]
        simp only [List.filter_cons]
        rw [decide_eq_true htarget]
        rfl
      rw [hcoinCache]
      intro entry hentry
      rcases List.mem_cons.mp hentry with hentry | hentry
      · simpa only [Prod.mk.injEq] using hentry ▸ hcoins htarget
      · exact hs entry hentry
    · have hcoinCache : S.coinCache pk z.2 = S.coinCache pk st := by
        unfold coinCache
        rw [heq]
        simp only [List.filter_cons]
        rw [decide_eq_false htarget]
        simp only [Bool.false_eq_true, ↓reduceIte]
      simpa only [hcoinCache] using hs

private theorem rejection_jointCache_eq
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.rejection input st).support) : z.2.jointCache = st.jointCache := by
  simp only [rejection] at hz
  split at hz
  · simp only [PMF.mem_support_pure_iff] at hz
    subst z
    rfl
  · rw [PMF.mem_support_map_iff] at hz
    obtain ⟨key, _, rfl⟩ := hz
    rfl

private theorem decapsKey_jointCache_eq [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {z : K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hz : z ∈ (S.decapsKey ciphertext st).support) : z.2.jointCache = st.jointCache := by
  simp only [decapsKey] at hz
  split at hz
  · simp only [PMF.mem_support_pure_iff] at hz
    subst z
    rfl
  · rw [PMF.mem_support_map_iff] at hz
    obtain ⟨key, _, rfl⟩ := hz
    rfl

private theorem toOuterMeasure_notGood_eq_zero
    [DecidableEq (JointInput JointPrefix M Salt)]
    {S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K}
    {pk : PK} {sk : SK} {A : Type}
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R} (hs : S.GoodCache pk sk st)
    {μ : PMF (A × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)}
    (hsub : ∀ x ∈ μ.support, ∀ entry ∈ x.2.jointCache, entry ∈ st.jointCache) :
    μ.toOuterMeasure {x | ¬S.GoodCache pk sk x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hbad
  exact hbad (hs.of_subset (hsub x hx))

/-- From a good cache with a fresh target-prefix input, one real joint query creates a bad cache
with exactly the underlying message's decryption-failure probability. This is the direct-query
execution property behind the `qRO` term. -/
private theorem realJoint_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hlookup : st.jointCache.lookup input = none)
    (htarget : input = S.jointInput pk input.message input.salt) :
    (S.realJoint pk sk input st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) := by
  classical
  let μ := S.realJoint pk sk input st
  have hmarg : μ.map (fun z => z.1.coins) = ProbComp.eval S.pke.sampleCoins := by
    simp only [μ, realJoint, cacheJoint, hlookup, PMF.map_bind]
    simp only [ite_eq_left htarget]
    conv_rhs => rw [← PMF.bind_pure (ProbComp.eval S.pke.sampleCoins)]
    apply PMF.bind_congr_on_support
    intro coins _
    have hmapConst : PMF.map (fun _ : K => coins) (ProbComp.eval S.sampleKey) =
        PMF.pure coins := by
      calc
        _ = PMF.map (Function.const K coins) (ProbComp.eval S.sampleKey) :=
          congrArg (fun f => PMF.map f (ProbComp.eval S.sampleKey)) (by
            funext _
            rfl)
        _ = _ := PMF.map_const (ProbComp.eval S.sampleKey) coins
    by_cases hcoins :
        S.pke.dec sk (S.pke.encDet pk input.message coins) = some input.message
    · simp only [hcoins, ↓reduceIte]
      cases hdecaps : st.decapsCache.lookup
          ⟨S.pke.encDet pk input.message coins, input.salt⟩ with
      | some key => simp only [PMF.pure_map]
      | none => simpa only [PMF.map_comp, Function.comp_def] using hmapConst
    · simpa only [hcoins, ↓reduceIte, PMF.map_comp, Function.comp_def] using hmapConst
  have hbad : μ.toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      μ.toOuterMeasure ((fun z => z.1.coins) ⁻¹' {coins |
        S.pke.dec sk (S.pke.encDet pk input.message coins) ≠ some input.message}) := by
    apply μ.toOuterMeasure_apply_eq_of_inter_support_eq
    refine Set.ext fun z => and_congr_left ?_
    intro hz
    have hcache : z.2.jointCache = (input, z.1) :: st.jointCache := by
      simp only [μ, realJoint, cacheJoint, hlookup] at hz
      simp only [ite_eq_left htarget] at hz
      rw [PMF.mem_support_bind_iff] at hz
      obtain ⟨coins, _, hz⟩ := hz
      split at hz
      · split at hz
        · simp only [PMF.mem_support_pure_iff] at hz
          subst z
          rfl
        · rw [PMF.mem_support_map_iff] at hz
          obtain ⟨key, _, rfl⟩ := hz
          rfl
      · rw [PMF.mem_support_map_iff] at hz
        obtain ⟨key, _, rfl⟩ := hz
        rfl
    have hgood : S.GoodCache pk sk z.2 ↔
        S.pke.dec sk (S.pke.encDet pk input.message z.1.coins) = some input.message := by
      have hs' : S.pke.GoodCache pk sk (S.coinCache pk st) := hs
      have hcoinCache : S.coinCache pk z.2 =
          (input.message, z.1.coins) :: S.coinCache pk st := by
        unfold coinCache
        rw [hcache]
        simp only [List.filter_cons]
        rw [decide_eq_true htarget]
        rfl
      rw [GoodCache, ExplicitCoinPKE.GoodCache, hcoinCache]
      constructor
      · intro h
        exact h (input.message, z.1.coins) (by simp)
      · intro hcoins entry hentry
        rcases List.mem_cons.mp hentry with hentry | hentry
        · simpa only [Prod.mk.injEq] using hentry ▸ hcoins
        · exact hs' entry hentry
    exact not_congr hgood
  calc
    _ = μ.toOuterMeasure ((fun z => z.1.coins) ⁻¹' {coins |
          S.pke.dec sk (S.pke.encDet pk input.message coins) ≠ some input.message}) := hbad
    _ = (ProbComp.eval S.pke.sampleCoins).toOuterMeasure
          {coins | S.pke.dec sk (S.pke.encDet pk input.message coins) ≠ some input.message} := by
      rw [← PMF.toOuterMeasure_map_apply, hmarg]
    _ = ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) := by
      rw [ExplicitCoinPKE.msgFailProb,
        ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)]

/-- From a good cache, one real joint query creates a bad cache with probability at most the
worst-message decryption-failure probability of the fixed key pair. -/
private theorem realJoint_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realJoint pk sk input st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  classical
  by_cases htarget : input = S.jointInput pk input.message input.salt
  · cases hlookup : st.jointCache.lookup input with
    | some reply =>
      refine le_of_eq_of_le ?_ zero_le
      apply toOuterMeasure_notGood_eq_zero hs
      intro z hz entry hentry
      simp only [realJoint, cacheJoint, hlookup, PMF.mem_support_pure_iff] at hz
      subst z
      exact hentry
    | none =>
      calc
        _ = ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) :=
          S.realJoint_bad_eq_msgFailProb pk sk input hs hlookup htarget
        _ ≤ ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) :=
          ENNReal.ofReal_le_ofReal
            (S.pke.msgFailProb_le_keyPairMaxFailProb pk sk input.message)
  · refine le_of_eq_of_le ?_ zero_le
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro z hz hbad
    apply hbad
    apply hs.of_cacheJoint (fun h => (htarget h).elim) hz

/-- Real and patched joint sampling assign the same mass to every outcome whose final joint cache
is good. -/
private theorem realJoint_apply_eq_simJoint
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (input : JointInput JointPrefix M Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (y : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hy : S.GoodCache pk sk y.2) :
    S.realJoint pk sk input st y = S.simJoint pk input st y := by
  by_cases htarget : input = S.jointInput pk input.message input.salt
  · unfold realJoint simJoint cacheJoint
    cases hlookup : st.jointCache.lookup input with
    | some reply => simp only
    | none =>
      simp only [PMF.bind_apply]
      simp only [ite_eq_left htarget]
      refine tsum_congr fun coins => congrArg ((ProbComp.eval S.pke.sampleCoins coins) * ·) ?_
      by_cases hcoins : S.pke.dec sk (S.pke.encDet pk input.message coins) = some input.message
      · simp only [hcoins, ↓reduceIte]
      · simp only [hcoins, ↓reduceIte]
        have hbad_of_entry (reply : JointReply K R)
            (hreply : reply.coins = coins)
            (hmem : (input, reply) ∈ y.2.jointCache) : False := by
          apply hcoins
          unfold GoodCache ExplicitCoinPKE.GoodCache coinCache at hy
          exact hreply ▸ hy (input.message, reply.coins)
            (List.mem_map.mpr ⟨(input, reply),
              List.mem_filter.mpr ⟨hmem, decide_eq_true htarget⟩, rfl⟩)
        have hraw : ((ProbComp.eval S.sampleKey).map fun key =>
            (⟨key, coins⟩, { st with jointCache := (input, ⟨key, coins⟩) :: st.jointCache }))
            y = 0 := by
          apply (PMF.apply_eq_zero_iff _ _).mpr
          intro hmem
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨key, _, rfl⟩ := hmem
          exact hbad_of_entry ⟨key, coins⟩ rfl List.mem_cons_self
        rw [hraw]
        cases hdecaps : st.decapsCache.lookup
            ⟨S.pke.encDet pk input.message coins, input.salt⟩ with
        | some key =>
          apply Eq.symm
          apply (PMF.apply_eq_zero_iff _ _).mpr
          intro hmem
          simp only [PMF.mem_support_pure_iff] at hmem
          subst y
          exact hbad_of_entry ⟨key, coins⟩ rfl List.mem_cons_self
        | none =>
          apply Eq.symm
          apply (PMF.apply_eq_zero_iff _ _).mpr
          intro hmem
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨key, _, rfl⟩ := hmem
          exact hbad_of_entry ⟨key, coins⟩ rfl List.mem_cons_self
  · unfold realJoint simJoint cacheJoint
    cases hlookup : st.jointCache.lookup input with
    | some reply => rfl
    | none =>
      simp only [ite_eq_right htarget]

/-- Mapping a `decapsKey` result into an optional key leaves the joint cache unchanged. -/
private theorem mapDecapsKey_jointCache_eq
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (PMF.map (fun x => (some x.1, x.2))
      (S.decapsKey ciphertext st)).support) :
    y.2.jointCache = st.jointCache := by
  rw [PMF.mem_support_map_iff] at hy
  obtain ⟨key, hkey, rfl⟩ := hy
  exact S.decapsKey_jointCache_eq ciphertext hkey

/-- The continuation after a successful joint lookup leaves the joint cache unchanged, whether
re-encryption succeeds or decapsulation falls back to `decapsKey`. -/
private theorem decapsContinuation_jointCache_eq
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (ciphertext : Ciphertext CT Salt)
    (z : JointReply K R × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    {condition : Prop} [Decidable condition]
    {y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ ((if condition then
        pure (some z.1.key)
      else
        some <$> S.decapsKey ciphertext) z.2).support) :
    y.2.jointCache = z.2.jointCache := by
  split at hy
  · change y ∈ (PMF.pure (some z.1.key, z.2)).support at hy
    rw [PMF.mem_support_pure_iff] at hy
    subst y
    rfl
  · have hrun :
        ((some <$> S.decapsKey ciphertext) z.2) =
          (fun p => (some p.1, p.2)) <$> S.decapsKey ciphertext z.2 :=
      StateT.run_map (fun key : K => some key) (S.decapsKey ciphertext) z.2
    rw [hrun, PMF.monad_map_eq_map] at hy
    exact S.mapDecapsKey_jointCache_eq ciphertext hy

/-- Real decapsulation and proof-only prefetch decapsulation assign the same mass to outcomes
whose final joint cache is good. -/
private theorem realDecaps_apply_eq_prefetchDecaps
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)
    (hy : S.GoodCache pk sk y.2) :
    S.realDecaps pk sk ciphertext st y = S.prefetchDecaps pk sk ciphertext st y := by
  classical
  unfold realDecaps prefetchDecaps
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none => rfl
  | some message =>
    simp only
    refine tsum_congr fun z => ?_
    by_cases hz : S.GoodCache pk sk z.2
    · rw [S.realJoint_apply_eq_simJoint pk sk (S.jointInput pk message ciphertext.salt)
          st z hz]
    · have hcont : ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
          pure (some z.1.key)
        else
          some <$> S.decapsKey ciphertext) z.2) y = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro hmem
        have heq := S.decapsContinuation_jointCache_eq ciphertext z hmem
        exact hz (hy.of_subset fun entry hentry => by rwa [heq])
      rw [hcont, mul_zero, mul_zero]

private theorem realDecaps_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (S.realDecaps pk sk ciphertext st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ y.2.jointCache := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    unfold realDecaps at hy
    simp only [hdec] at hy
    have hrun :
        ((some <$> S.decapsKey ciphertext) st) =
          (fun p => (some p.1, p.2)) <$> S.decapsKey ciphertext st :=
      StateT.run_map (fun key : K => some key) (S.decapsKey ciphertext) st
    rw [hrun, PMF.monad_map_eq_map] at hy
    intro entry hentry
    rwa [S.mapDecapsKey_jointCache_eq ciphertext hy]
  | some message =>
    unfold realDecaps at hy
    simp only [hdec] at hy
    have hrun :
        ((S.realJoint pk sk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
            if S.pke.encDet pk message reply.coins = ciphertext.pke then
              pure (some reply.key)
            else
              some <$> S.decapsKey ciphertext) st) =
          S.realJoint pk sk (S.jointInput pk message ciphertext.salt) st >>= fun z =>
            ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
                pure (some z.1.key)
              else
                some <$> S.decapsKey ciphertext) z.2) :=
      StateT.run_bind _ _ _
    rw [hrun, PMF.monad_bind_eq_bind] at hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hsub := S.cacheJoint_jointCache_subset pk
      (fun m coins => S.pke.dec sk (S.pke.encDet pk m coins) = some m)
      (S.jointInput pk message ciphertext.salt) hz
    intro entry hentry
    rw [S.decapsContinuation_jointCache_eq ciphertext z hy]
    exact hsub entry hentry

private theorem prefetchDecaps_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Option K × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (S.prefetchDecaps pk sk ciphertext st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ y.2.jointCache := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    unfold prefetchDecaps at hy
    simp only [hdec] at hy
    have hrun :
        ((some <$> S.decapsKey ciphertext) st) =
          (fun p => (some p.1, p.2)) <$> S.decapsKey ciphertext st :=
      StateT.run_map (fun key : K => some key) (S.decapsKey ciphertext) st
    rw [hrun, PMF.monad_map_eq_map] at hy
    intro entry hentry
    rwa [S.mapDecapsKey_jointCache_eq ciphertext hy]
  | some message =>
    unfold prefetchDecaps at hy
    simp only [hdec] at hy
    have hrun :
        ((S.simJoint pk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
            if S.pke.encDet pk message reply.coins = ciphertext.pke then
              pure (some reply.key)
            else
              some <$> S.decapsKey ciphertext) st) =
          S.simJoint pk (S.jointInput pk message ciphertext.salt) st >>= fun z =>
            ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
                pure (some z.1.key)
              else
                some <$> S.decapsKey ciphertext) z.2) :=
      StateT.run_bind _ _ _
    rw [hrun, PMF.monad_bind_eq_bind] at hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hsub := S.cacheJoint_jointCache_subset pk (fun _ _ => True)
      (S.jointInput pk message ciphertext.salt) hz
    intro entry hentry
    rw [S.decapsContinuation_jointCache_eq ciphertext z hy]
    exact hsub entry hentry

private theorem realHandler_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (S.realHandler pk sk challenge q st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ y.2.jointCache := by
  classical
  rcases q with input | input | ciphertext
  · apply S.cacheJoint_jointCache_subset pk
      (fun m coins => S.pke.dec sk (S.pke.encDet pk m coins) = some m) input
    simpa only [realHandler, Query.dispatch, realJoint] using hy
  · intro entry hentry
    rwa [S.rejection_jointCache_eq input hy]
  · by_cases hc : ciphertext = challenge
    · simp only [realHandler, Query.dispatch, hc, ↓reduceIte] at hy
      change y ∈ (PMF.pure (none, st)).support at hy
      rw [PMF.mem_support_pure_iff] at hy
      subst y
      exact fun _ hentry => hentry
    · apply S.realDecaps_jointCache_subset pk sk ciphertext
      simpa only [realHandler, Query.dispatch, hc, ↓reduceIte] using hy

private theorem prefetchHandler_jointCache_subset
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    {y : Response K R q × CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hy : y ∈ (S.prefetchHandler pk sk challenge q st).support) :
    ∀ entry ∈ st.jointCache, entry ∈ y.2.jointCache := by
  rcases q with input | input | ciphertext
  · apply S.cacheJoint_jointCache_subset pk (fun _ _ => True) input
    simpa only [prefetchHandler, Query.dispatch, simJoint] using hy
  · intro entry hentry
    rwa [S.rejection_jointCache_eq input hy]
  · by_cases hc : ciphertext = challenge
    · simp only [prefetchHandler, Query.dispatch, hc, ↓reduceIte] at hy
      change y ∈ (PMF.pure (none, st)).support at hy
      rw [PMF.mem_support_pure_iff] at hy
      subst y
      exact fun _ hentry => hentry
    · apply S.prefetchDecaps_jointCache_subset pk sk ciphertext
      simpa only [prefetchHandler, Query.dispatch, hc, ↓reduceIte] using hy

private theorem identicalUntilBad_realHandler_prefetchHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    OracleComp.IdenticalUntilBad (S.realHandler pk sk challenge)
      (S.prefetchHandler pk sk challenge) (fun st => ¬S.GoodCache pk sk st) where
  agree q st _ answer st' hst' := by
    rcases q with input | input | ciphertext
    · exact S.realJoint_apply_eq_simJoint pk sk input st (answer, st') (of_not_not hst')
    · rfl
    · by_cases hc : ciphertext = challenge
      · simp [realHandler, prefetchHandler, Query.dispatch, hc]
      · simpa only [realHandler, prefetchHandler, Query.dispatch, hc, ↓reduceIte] using
          S.realDecaps_apply_eq_prefetchDecaps pk sk ciphertext st (answer, st')
            (of_not_not hst')
  absorb_first q st hbad y hy hgood :=
    hbad (hgood.of_subset (S.realHandler_jointCache_subset pk sk challenge q hy))
  absorb_second q st hbad y hy hgood :=
    hbad (hgood.of_subset (S.prefetchHandler_jointCache_subset pk sk challenge q hy))

/-- A successful real decapsulation preserves exactly the bad-cache probability of its implicit
joint query: its remaining continuation never changes the joint cache. -/
private theorem realDecaps_bad_eq_realJoint_bad
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hdec : S.pke.dec sk ciphertext.pke = some message) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      (S.realJoint pk sk (S.jointInput pk message ciphertext.salt) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} := by
  classical
  unfold realDecaps
  simp only [hdec]
  have hrun :
      ((S.realJoint pk sk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
          if S.pke.encDet pk message reply.coins = ciphertext.pke then
            pure (some reply.key)
          else
            some <$> S.decapsKey ciphertext) st) =
        S.realJoint pk sk (S.jointInput pk message ciphertext.salt) st >>= fun z =>
          ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
              pure (some z.1.key)
            else
              some <$> S.decapsKey ciphertext) z.2) :=
    StateT.run_bind _ _ _
  rw [hrun, PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun z => ?_
  by_cases hbad : ¬S.GoodCache pk sk z.2
  · have hone :
        (((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
              pure (some z.1.key)
            else
              some <$> S.decapsKey ciphertext) z.2).toOuterMeasure
          {y | ¬S.GoodCache pk sk y.2}) = 1 := by
      apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
      intro y hy hgood
      apply hbad
      apply hgood.of_subset
      intro entry hentry
      rw [S.decapsContinuation_jointCache_eq ciphertext z hy]
      exact hentry
    rw [hone, mul_one, Set.indicator_of_mem hbad]
  · have hzero :
        (((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
              pure (some z.1.key)
            else
              some <$> S.decapsKey ciphertext) z.2).toOuterMeasure
          {y | ¬S.GoodCache pk sk y.2}) = 0 := by
      apply toOuterMeasure_notGood_eq_zero (not_not.mp hbad)
      intro y hy entry hentry
      rwa [S.decapsContinuation_jointCache_eq ciphertext z hy] at hentry
    rw [hzero, mul_zero, Set.indicator_of_notMem hbad]

/-- From a good cache with a fresh implicit joint input, one successful real decapsulation creates
a bad cache with exactly the decoded message's decryption-failure probability. This is the
decapsulation execution property behind the independent `qD` term. -/
private theorem realDecaps_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hdec : S.pke.dec sk ciphertext.pke = some message)
    (hlookup : st.jointCache.lookup (S.jointInput pk message ciphertext.salt) = none) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk message) := by
  rw [S.realDecaps_bad_eq_realJoint_bad pk sk ciphertext message hdec]
  exact S.realJoint_bad_eq_msgFailProb pk sk
    (S.jointInput pk message ciphertext.salt) hs hlookup rfl

/-- A fresh target-prefix joint query through the real handler has exactly the underlying
message's decryption-failure probability of creating a bad cache. -/
theorem realHandler_joint_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (input : JointInput JointPrefix M Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) (hlookup : st.jointCache.lookup input = none)
    (htarget : input = S.jointInput pk input.message input.salt) :
    (S.realHandler pk sk challenge (.joint input) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk input.message) := by
  simpa only [realHandler, Query.dispatch] using
    S.realJoint_bad_eq_msgFailProb pk sk input hs hlookup htarget

/-- A fresh nonchallenge decapsulation query through the real handler has exactly the decoded
message's decryption-failure probability of creating a bad cache. -/
theorem realHandler_decaps_bad_eq_msgFailProb
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge ciphertext : Ciphertext CT Salt) (message : M)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hne : ciphertext ≠ challenge) (hs : S.GoodCache pk sk st)
    (hdec : S.pke.dec sk ciphertext.pke = some message)
    (hlookup : st.jointCache.lookup (S.jointInput pk message ciphertext.salt) = none) :
    (S.realHandler pk sk challenge (.decaps ciphertext) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} =
      ENNReal.ofReal (S.pke.msgFailProb pk sk message) := by
  simpa only [realHandler, Query.dispatch, hne, ↓reduceIte] using
    S.realDecaps_bad_eq_msgFailProb pk sk ciphertext message hs hdec hlookup

/-- The punctured real handler rejects its challenge ciphertext without changing the state. -/
@[simp] theorem realHandler_decaps_challenge
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    S.realHandler pk sk challenge (.decaps challenge) st = PMF.pure (none, st) := by
  simp only [realHandler, Query.dispatch, ↓reduceIte]
  change PMF.pure (none, st) = PMF.pure (none, st)
  rfl

/-- A rejection-oracle query through the real handler cannot create a PKE correctness witness. -/
theorem realHandler_rejection_bad_eq_zero
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (input : RejectionInput RejectPrefix Sigma CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realHandler pk sk challenge (.rejection input) st).toOuterMeasure
        {z | ¬S.GoodCache pk sk z.2} = 0 := by
  simp only [realHandler, Query.dispatch]
  apply toOuterMeasure_notGood_eq_zero hs
  intro z hz entry hentry
  rwa [S.rejection_jointCache_eq input hz] at hentry

private theorem realDecaps_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)] [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (ciphertext : Ciphertext CT Salt)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realDecaps pk sk ciphertext st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  classical
  cases hdec : S.pke.dec sk ciphertext.pke with
  | none =>
    refine le_of_eq_of_le ?_ zero_le
    apply toOuterMeasure_notGood_eq_zero hs
    intro z hz entry hentry
    unfold realDecaps at hz
    simp only [hdec] at hz
    change z ∈ (PMF.map (fun x => (some x.1, x.2))
      (S.decapsKey ciphertext st)).support at hz
    simpa only [S.mapDecapsKey_jointCache_eq ciphertext hz] using hentry
  | some message =>
    unfold realDecaps
    simp only [hdec]
    have hrun :
        ((S.realJoint pk sk (S.jointInput pk message ciphertext.salt) >>= fun reply =>
            if S.pke.encDet pk message reply.coins = ciphertext.pke then
              pure (some reply.key)
            else
              some <$> S.decapsKey ciphertext) st) =
          S.realJoint pk sk (S.jointInput pk message ciphertext.salt) st >>= fun z =>
            ((if S.pke.encDet pk message z.1.coins = ciphertext.pke then
                pure (some z.1.key)
              else
                some <$> S.decapsKey ciphertext) z.2) :=
      StateT.run_bind _ _ _
    rw [hrun, PMF.monad_bind_eq_bind]
    refine (Probability.PMF.toOuterMeasure_bind_le_add _ _ {z | ¬S.GoodCache pk sk z.2} _ 0
      fun z _ hgood => by
        refine le_of_eq (toOuterMeasure_notGood_eq_zero (of_not_not hgood) ?_)
        intro y hy entry hentry
        have heq := S.decapsContinuation_jointCache_eq ciphertext z hy
        exact heq ▸ hentry).trans (by
          rw [add_zero]
          exact S.realJoint_bad_le pk sk (S.jointInput pk message ciphertext.salt) hs)

private theorem realHandler_bad_le [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT)
    {st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R}
    (hs : S.GoodCache pk sk st) :
    (S.realHandler pk sk challenge q st).toOuterMeasure {z | ¬S.GoodCache pk sk z.2} ≤
      (Query.jointCost q : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) +
        (Query.decapsCost q : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  rcases q with input | input | ciphertext
  · simpa only [realHandler, Query.dispatch, Query.jointCost, Query.decapsCost, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, add_zero] using S.realJoint_bad_le pk sk input hs
  · simp only [realHandler, Query.dispatch, Query.jointCost, Query.decapsCost,
      Nat.cast_zero, zero_mul, add_zero]
    exact le_of_eq (toOuterMeasure_notGood_eq_zero hs fun z hz entry hentry => by
      rwa [S.rejection_jointCache_eq input hz] at hentry)
  · by_cases hc : ciphertext = challenge
    · simp only [realHandler, Query.dispatch, hc, ↓reduceIte, Query.jointCost, Query.decapsCost,
        Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add]
      exact (le_of_eq (toOuterMeasure_notGood_eq_zero hs fun z hz entry hentry => by
          change z ∈ (PMF.pure (none, st)).support at hz
          rw [PMF.mem_support_pure_iff] at hz
          subst z
          exact hentry)).trans zero_le
    · simpa only [realHandler, Query.dispatch, hc, ↓reduceIte, Query.jointCost,
        Query.decapsCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add] using
        S.realDecaps_bad_le pk sk ciphertext hs

end Scheme

/-- Separate source-shaped query bounds: at most `qRO` calls to the joint oracle and at most `qD`
calls to decapsulation. Rejection-oracle calls do not enter the `CORR` loss. -/
@[expose] def QueryBounds {JointPrefix M Salt RejectPrefix Sigma CT K R α : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α) (qRO qD : ℕ) : Prop :=
  OracleComp.IsCostBounded Query.jointCost program qRO ∧
    OracleComp.IsCostBounded Query.decapsCost program qD

/-- A randomized single-user, single-challenge adversary for the correctness hop. Its oracle
program is selected by private coins and the full public KEM challenge; in particular, the program
can depend on the public key, challenge ciphertext and challenge key, but not on `sk`. Query bounds
are stated separately and required for every random tape and challenge. -/
structure RandomizedAdversary
    (PK JointPrefix M Salt RejectPrefix Sigma CT K R : Type) where
  /-- Type of the adversary's private random tape. -/
  Coins : Type
  /-- Distribution of private random tapes. -/
  coins : ProbComp Coins
  /-- Deterministic oracle program after fixing the private tape and public challenge. -/
  run : Coins → KEM.Challenge PK (Ciphertext CT Salt) K → OracleComp
    (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) Bool

namespace RandomizedAdversary

variable {PK JointPrefix M Salt RejectPrefix Sigma CT K R : Type}

/-- Per-random-tape and per-challenge joint-oracle and decapsulation bounds. -/
@[expose] def QueryBounded
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (qRO qD : ℕ) : Prop :=
  ∀ coins challenge, QueryBounds (A.run coins challenge) qRO qD

end RandomizedAdversary

variable {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}

/-- **Fixed-key salted-FO `CORR` hop.** Suppose the real and simulated handlers agree until
`bad`, and from any good state each joint-oracle or decapsulation query creates `bad` with
probability at most `ε`. A program bounded by `qRO` joint queries and `qD` decapsulation queries
then has output laws within `(qRO + qD) * ε`, after any shared randomized postprocessing.

The cost of `Query.rejection` is zero in both channels, so a shared `J` fallback contributes no
correctness term. `Query.joint` has cost one even though its reply has two projections. -/
private theorem closeTo_run_corr {JointPrefix M Salt RejectPrefix Sigma CT K R State α β : Type}
    {first second : (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      StateT State PMF (Response K R q)} {bad : State → Prop} {ε : ℝ≥0∞}
    (hident : OracleComp.IdenticalUntilBad first second bad)
    (hstep : ∀ q s, ¬bad s →
      (first q s).toOuterMeasure {x | bad x.2} ≤
        (Query.jointCost q : ℝ≥0∞) * ε + (Query.decapsCost q : ℝ≥0∞) * ε)
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α) {qRO qD : ℕ}
    (hbounds : QueryBounds program qRO qD) {initial : State} (hinitial : ¬bad initial)
    (next : α × State → PMF β) :
    CloseTo (((OracleComp.interpret first program).run initial).bind next)
      (((OracleComp.interpret second program).run initial).bind next)
      (((qRO + qD : ℕ) : ℝ≥0∞) * ε) := by
  have hreach :
      ((OracleComp.interpret first program).run initial).toOuterMeasure {x | bad x.2} ≤
        (qRO : ℝ≥0∞) * ε + (qD : ℝ≥0∞) * ε := by
    simpa only [mul_zero, add_zero] using
      (OracleComp.toOuterMeasure_bad_le_two Query.jointCost Query.decapsCost (fun _ => ε)
        0 0 ε hstep (fun _ _ _ _ _ _ => by simp) hbounds.1 hbounds.2 hinitial)
  refine (hident.closeTo_bind program initial next).mono (hreach.trans_eq ?_)
  rw [← add_mul, ← Nat.cast_add]

private theorem Scheme.closeTo_run_realHandler_prefetchHandler
    [Fintype M] [Nonempty M]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A)
    {qRO qD : ℕ} (hbounds : QueryBounds program qRO qD) :
    CloseTo
      (((OracleComp.interpret (S.realHandler pk sk challenge) program).run {}).map Prod.fst)
      (((OracleComp.interpret (S.prefetchHandler pk sk challenge) program).run {}).map Prod.fst)
      (((qRO + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) := by
  simpa only [PMF.bind_pure_comp] using
    (closeTo_run_corr (S.identicalUntilBad_realHandler_prefetchHandler pk sk challenge)
      (fun q st hst => S.realHandler_bad_le pk sk challenge q (of_not_not hst))
      program hbounds (by simp [Scheme.GoodCache, Scheme.coinCache,
        ExplicitCoinPKE.GoodCache]) (PMF.pure ∘ Prod.fst))

/-- **Concrete fixed-key salted-FO `CORR` hop.** The decrypt/re-encrypt real handler and the
secret-key-free keyless handler have output laws within `(qRO + qD)` times the fixed key pair's
worst-message decryption-failure probability. Private final caches are not observable. -/
theorem Scheme.closeTo_run_realHandler_simHandler
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) {A : Type}
    (program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) A)
    {qRO qD : ℕ} (hbounds : QueryBounds program qRO qD) :
    CloseTo
      (((OracleComp.interpret (S.realHandler pk sk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst)
      (((OracleComp.interpret (S.simHandler pk challenge) program).run
        ({} : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R)).map Prod.fst)
      (((qRO + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) := by
  rw [← S.run_prefetchHandler_eq_simHandler pk sk challenge program]
  exact S.closeTo_run_realHandler_prefetchHandler pk sk challenge program hbounds

/-- Run a challenge-aware randomized adversary against the post-secret-seed-guessing real
handler. The adversary's coins are sampled before the common public challenge. -/
noncomputable def Scheme.randomizedRealHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.realHandler keys.1 keys.2 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- Run the same challenge-aware randomized adversary against the post-secret-seed-guessing
keyless handler, using the identical key, coin and challenge setup laws. -/
noncomputable def Scheme.randomizedSimHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.simHandler keys.1 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- **Concrete randomized-adversary salted-FO `CORR` hop.** For a randomized adversary that
receives the full public KEM challenge and has `qRO`/`qD` bounds for every tape and challenge, the
concrete real and keyless-handler games differ by at most `(qRO + qD) * δ` under
`ExplicitCoinPKE.DeltaCorrect δ`. Both games sample the same challenge law after key generation;
challenge construction is outside the counted handler queries and therefore adds no `+1`. -/
theorem Scheme.advantage_randomizedRealHandler_simHandler_le
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    {qRO qD : ℕ} (hbounds : A.QueryBounded qRO qD)
    {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) :
    (Game.advantage
      (S.randomizedRealHandlerGame challengeSetup A)
      (S.randomizedSimHandlerGame challengeSetup A) : ℝ) ≤
      ((qRO + qD : ℕ) : ℝ) * δ := by
  change (Game.advantage
      ((ProbComp.eval S.pke.keyGen).bind fun keys =>
        (ProbComp.eval A.coins).bind fun coins =>
          (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
            ((OracleComp.interpret (S.realHandler keys.1 keys.2 challenge.1)
              (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst)
      ((ProbComp.eval S.pke.keyGen).bind fun keys =>
        (ProbComp.eval A.coins).bind fun coins =>
          (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
            ((OracleComp.interpret (S.simHandler keys.1 challenge.1)
              (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst) : ℝ) ≤ _
  refine S.pke.advantage_bind_keyGen_le
    (fun pk sk => (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup pk)).bind fun challenge =>
        ((OracleComp.interpret (S.realHandler pk sk challenge.1)
          (A.run coins ⟨pk, challenge.1, challenge.2⟩)).run {}).map Prod.fst)
    (fun pk _ => (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup pk)).bind fun challenge =>
        ((OracleComp.interpret (S.simHandler pk challenge.1)
          (A.run coins ⟨pk, challenge.1, challenge.2⟩)).run {}).map Prod.fst)
    (qRO + qD) ?_ hδ
  intro pk sk
  refine (CloseTo.bind_right_tsum (ProbComp.eval A.coins)
    (err := fun _ => (((qRO + qD : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk))) fun coins _ => ?_).mono ?_
  · refine (CloseTo.bind_right_tsum (ProbComp.eval (challengeSetup pk))
      (err := fun _ => (((qRO + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk))) fun challenge _ => ?_).mono ?_
    · exact S.closeTo_run_realHandler_simHandler pk sk challenge.1
        (A.run coins ⟨pk, challenge.1, challenge.2⟩)
        (hbounds coins ⟨pk, challenge.1, challenge.2⟩)
    · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
