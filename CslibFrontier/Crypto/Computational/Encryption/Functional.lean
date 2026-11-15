/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Scheme
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState

/-!
# Functional encryption schemes and their semantic-security experiment

A functional encryption scheme `FE MPK MSK Fn SK M C Y` has typed master public keys, master secret
keys, function identifiers, secret keys for functions, messages, ciphertexts and outputs
([BonehShoup2023], Section 15.7, Definition 15.13, pp. 658–659). Setup, key generation for a
function identifier, and encryption are probabilistic programs; decryption is deterministic and
returns `Option Y`. A functionality `FE.Functionality Fn M Y` pairs the evaluation map
`eval : Fn → M → Option Y` (where `none` represents the book's special symbol `⊥`) with the
distinguished null identifier `null : Fn` (`ε` in [BonehShoup2023], Section 15.7, p. 660) whose
secret key captures the intentional leakage of a ciphertext.

`FE.Correct` (Definition 15.13, p. 659) requires that whenever `F.eval f m = some y`, decryption of
any honest encryption of `m` under any key generated for `f` yields `some y`. `FE.Robust`
(Definition 15.15, p. 661) requires that for every supported master key pair and every ciphertext
`c`, there is a message `m` such that whenever `E.decrypt sk c = some y` for a key `sk` generated
for `f` and `F.eval f m = some y'`, the two outputs `y` and `y'` agree.

`FE.ssExperiment` is experiment `b` of the single-challenge semantic-security game for one fixed
scheme ([BonehShoup2023], Section 15.7, Attack Game 15.9, pp. 660–661): draw `(mpk, msk)`, generate
a null key `skNull ← E.keyGen msk F.null`, run both stages of an `FE.Adversary` against the logging
key-generation oracle `E.keyGen msk` flanking a single challenge encryption of `pair.select b`, and
accept the adversary's guess only when `F.admissible` holds on the logged function identifiers and
`F.null`.

When the null function `F.eval F.null` is injective, the admissibility check forces `msg₀ = msg₁`
on every accepting run, so the two experiments of Attack Game 15.9 have identical output
distributions and advantage `0` for every scheme and every adversary ([BonehShoup2023], Section
15.7, Remark 15.13, p. 661). In particular, the cleartext scheme `FE.cleartext F` (ciphertext equal
to the message and secret key equal to the function identifier) is both `Correct` and `Robust` for
every functionality `F` and has semantic-security advantage `0` whenever `F.eval F.null` is
injective.

For a public-key encryption scheme `E : PKE PK SK M C` and ciphertext-leakage function
`leak : C → L`, `E.toFE leak` is the functional encryption scheme of Example 15.1
([BonehShoup2023], Section 15.7, p. 659, equation (15.33), and p. 660): `some ()` is the identity
function identifier `I` whose secret key is `some sk`, and `none` is the null identifier `ε` whose
key `none` is public and evaluates `leak` on the ciphertext. `E.toFE leak` is correct for
`FE.Functionality.pke len` if and only if `E` is correct and `leak c = len m` on every honest
ciphertext `c` of `m` (`PKE.toFE_correct_iff`). Against an adversary that makes no key-generation
queries (`FE.Adversary.ofTwoStage A`), the semantic-security experiment of `E.toFE leak` for
`FE.Functionality.pke len` has the same output distribution as the chosen-plaintext experiment
`E.cpaExperiment` with admissibility rule `len m₀ = len m₁`
(`PKE.eval_ssExperiment_toFE_ofTwoStage`).

Design decisions and deviations from [BonehShoup2023], Section 15.7:
1. Both `F.eval` and `E.decrypt` return `Option Y`, where `Y` is the book's output set without `⊥`:
   `none` represents `⊥` in `F.eval` and represents both `⊥` and `reject` in `E.decrypt`. This does
   not affect `FE.Correct` or `FE.ssExperiment`. For `FE.Robust`, a scheme that is robust in the
   book's sense (with both `⊥` and `reject` mapped to `none`) satisfies `FE.Robust`, whereas the
   converse can fail for a scheme whose decryption outputs `⊥` where the functionality has a value;
   a scheme whose decryption never outputs `⊥` loses nothing.
2. The challenger enforces the query restriction at the end of the experiment by returning
   `guess && F.admissible ((log₁ ++ log₂).map Prod.fst) pair`, so an inadmissible run returns
   `false` in both experiments (matching `lrExperiment`), because a post-challenge key query in
   stage 2 can violate the restriction on the challenge pair.
3. The adversary makes a single challenge encryption query between its two stages (`choose` and
   `guess`), matching the book's restriction to a single encryption query.
4. The null identifier `null : Fn` (`ε`) is bundled in `FE.Functionality`; `FE.Correct` and
   `FE.Robust` do not depend on `null`, while `FE.ssExperiment` generates `sk_ε` from it and
   includes it in `FE.Functionality.admissible`.
5. Remark 15.13 (`FE.eval_ssExperiment_eq_of_injective_null` and
   `FE.advantage_ssExperiment_eq_zero_of_injective_null`) is proved under the hypothesis that
   `F.eval F.null` is injective, for every scheme and every adversary without assuming one-wayness
   or an asymptotic security definition.
6. The Remark 15.13 scheme is named `FE.cleartext` rather than `trivial` because Exercise 15.21
   ("The trivial functional encryption scheme", p. 679) refers to a different construction.
7. In Example 15.1 (`FE.Functionality.pke` and `PKE.toFE`), the two-element identifier set `{I, ε}`
   is modeled as `Option Unit` (`some ()` for `I`, `none` for `ε`), the output type is `M ⊕ L` so
   that the message and its leakage `len m` have disjoint tags, and the secret-key type is
   `Option SK`.
8. As in `PKE`, `FE` and `FE.Adversary` are typed records for one fixed scheme without an asymptotic
   security parameter or efficiency predicate; `FE.Adversary.ofTwoStage` and
   `PKE.eval_ssExperiment_toFE_ofTwoStage` compare the two experiments and carry no efficiency claim
   or security reduction.
9. The key-generation field is named `keyGen` after the book's key generation algorithm `G`.

Not formalized here: Definition 15.14 as an asymptotic security predicate over scheme families and
efficient typed oracle adversaries (#4894), a security reduction between `PKE.toFE` and IND-CPA,
Example 15.2 (identity-based encryption as functional encryption, equation (15.34), p. 659),
Exercises 15.21 and 15.22 (pp. 679–681), the concrete functionality families of Section 15.7.1,
chosen-ciphertext security for functional encryption (pp. 661–662), and multi-challenge encryption
queries.

## Main definitions

* `Cslib.Crypto.FE`: a functional encryption scheme with typed keys, function identifiers,
  messages, ciphertexts and outputs.
* `Cslib.Crypto.FE.Functionality`: a functionality `Fn → M → Option Y` bundled with its null
  identifier `null : Fn`.
* `Cslib.Crypto.FE.Correct`: correctness on every `(f, m)` where the functionality evaluates to
  `some y`.
* `Cslib.Crypto.FE.Robust`: ciphertext consistency across function keys whenever both decryption
  and the functionality return `some`.
* `Cslib.Crypto.FE.Adversary`: a two-stage adversary whose stages query the key-generation oracle.
* `Cslib.Crypto.FE.Functionality.admissible`, `Cslib.Crypto.FE.ssExperiment`: the query restriction
  and experiment `b` of Attack Game 15.9.
* `Cslib.Crypto.FE.cleartext`: the cleartext functional encryption scheme of Remark 15.13.
* `Cslib.Crypto.FE.Functionality.pke`, `Cslib.Crypto.PKE.toFE`: the public-key functionality
  (15.33) and the functional encryption view of a `PKE` scheme (Example 15.1).
* `Cslib.Crypto.FE.Adversary.ofTwoStage`: a `TwoStage` adversary lifted to an `FE.Adversary` that
  makes no key-generation queries.

## Main results

* `Cslib.Crypto.FE.eval_ssExperiment_eq_of_injective_null`,
  `Cslib.Crypto.FE.advantage_ssExperiment_eq_zero_of_injective_null`: when `F.eval F.null` is
  injective, the two semantic-security experiments have identical output distributions and
  advantage `0` for every scheme and adversary (Remark 15.13).
* `Cslib.Crypto.FE.cleartext_correct`, `Cslib.Crypto.FE.cleartext_robust`: the cleartext scheme is
  correct and robust for every functionality.
* `Cslib.Crypto.FE.advantage_ssExperiment_pke_eq_zero`: specialization of Remark 15.13 to
  `FE.Functionality.pke π` for an injective leakage map `π`.
* `Cslib.Crypto.PKE.toFE_correct_iff`: `E.toFE leak` is correct for `FE.Functionality.pke len` iff
  `E` is correct and `leak` agrees with `len` on all honest ciphertexts.
* `Cslib.Crypto.PKE.eval_ssExperiment_toFE_ofTwoStage`: against `FE.Adversary.ofTwoStage A`, the
  semantic-security experiment of `E.toFE leak` has the same output distribution as
  `E.cpaExperiment` with admissibility rule `len m₀ = len m₁`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 15.7 (Definitions 15.13 and 15.15, Attack Game 15.9, Example 15.1, Remark 15.13,
  pp. 658–661).
-/

public section

namespace Cslib.Crypto

open Probability

/-- A functional encryption scheme ([BonehShoup2023], Section 15.7, Definition 15.13, pp. 658–659)
with master public keys `MPK`, master secret keys `MSK`, function identifiers `Fn`, function secret
keys `SK`, messages `M`, ciphertexts `C` and outputs `Y`. Both the functionality's `⊥` and
decryption rejection are represented by `none : Option Y`. -/
structure FE (MPK MSK Fn SK M C Y : Type) where
  /-- Setup algorithm `S`: draw a master public key and a master secret key. -/
  setup : ProbComp (MPK × MSK)
  /-- Key generation algorithm `G`: derive a secret key for function identifier `f` from the master
  secret key. -/
  keyGen : MSK → Fn → ProbComp SK
  /-- Encryption algorithm `E`: encrypt a message under the master public key. -/
  encrypt : MPK → M → ProbComp C
  /-- Deterministic decryption algorithm `D`: evaluate a function secret key on a ciphertext,
  returning `none` for `⊥` or rejection. -/
  decrypt : SK → C → Option Y

namespace FE

variable {MPK MSK Fn SK M C Y σ : Type}

/-- A functionality `F : Fn × M → Y ∪ {⊥}` (`none` is `⊥`) bundled with its distinguished null
function identifier `null` (`ε`), whose secret key is given to every party to model intentional
ciphertext leakage ([BonehShoup2023], Section 15.7, Definition 15.13, p. 658, and p. 660). -/
structure Functionality (Fn M Y : Type) where
  /-- Evaluate function identifier `f` on message `m`; `none` represents `⊥` (decryption is
  unconstrained). -/
  eval : Fn → M → Option Y
  /-- The null function identifier `ε` whose secret key `sk_ε` is public. -/
  null : Fn

/-- Correctness of a functional encryption scheme for a functionality `F` ([BonehShoup2023],
Section 15.7, Definition 15.13, p. 659): for every supported master key pair, every function
identifier `f`, every message `m` and every output `y` with `F.eval f m = some y`, decrypting any
supported encryption of `m` under any supported key for `f` yields `some y`. -/
@[expose]
def Correct (E : FE MPK MSK Fn SK M C Y) (F : Functionality Fn M Y) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.setup).support, ∀ f m y, F.eval f m = some y →
    ∀ sk ∈ (ProbComp.eval (E.keyGen keys.2 f)).support,
      ∀ c ∈ (ProbComp.eval (E.encrypt keys.1 m)).support, E.decrypt sk c = some y

/-- Robustness of a functional encryption scheme for a functionality `F` ([BonehShoup2023],
Section 15.7, Definition 15.15, p. 661): for every supported master key pair and every ciphertext
`c`, there is a message `m` such that for every function identifier `f` and every supported secret
key `sk` for `f`, if `E.decrypt sk c = some y` and `F.eval f m = some y'`, then `y = y'`.

Because `E.decrypt` uses `none` for both `⊥` and `reject`, the book's robustness implies
`FE.Robust`; the converse fails for a scheme whose decryption outputs `⊥` where the functionality
has a value (a scheme whose decryption never outputs `⊥` loses nothing). -/
@[expose]
def Robust (E : FE MPK MSK Fn SK M C Y) (F : Functionality Fn M Y) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.setup).support, ∀ c : C, ∃ m : M, ∀ f,
    ∀ sk ∈ (ProbComp.eval (E.keyGen keys.2 f)).support, ∀ y, E.decrypt sk c = some y →
      ∀ y', F.eval f m = some y' → y = y'

/-- An adversary in the single-challenge semantic-security game for functional encryption
([BonehShoup2023], Section 15.7, Attack Game 15.9, pp. 660–661). Both stages are oracle programs
over the key-generation oracle `Fn → SK`: `choose` receives the master public key and a null key
`sk_ε` and outputs a challenge message pair together with state `σ`; `guess` receives that state
and the challenge ciphertext and outputs a Boolean guess. -/
structure Adversary (MPK Fn SK M C σ : Type) where
  /-- Stage 1: given `mpk` and `sk_ε`, query the key-generation oracle and output a challenge
  message pair and saved state. -/
  choose : MPK → SK → ProbOracleComp (fun _ : Fn => SK) (MessagePair M × σ)
  /-- Stage 2: given the saved state and challenge ciphertext, query the key-generation oracle and
  output a Boolean guess. -/
  guess : σ → C → ProbOracleComp (fun _ : Fn => SK) Bool

/-- The query restriction of Attack Game 15.9 ([BonehShoup2023], Section 15.7, p. 660): the null
identifier `F.null` (`ε`) and every queried function identifier in `queried` agree on `pair.msg₀`
and `pair.msg₁`. -/
@[expose]
def Functionality.admissible [DecidableEq Y] (F : Functionality Fn M Y) (queried : List Fn)
    (pair : MessagePair M) : Bool :=
  (F.null :: queried).all fun f => decide (F.eval f pair.msg₀ = F.eval f pair.msg₁)

/-- Experiment `b` of Attack Game 15.9 ([BonehShoup2023], Section 15.7, pp. 660–661) for a single
encryption query: generate `(mpk, msk)` and the null key `skNull ← E.keyGen msk F.null`, run
`A.choose mpk skNull` and `A.guess state challenge` against the logged key-generation oracle
`E.keyGen msk` around the challenge encryption of `pair.select b`, and return `guess` gated by
`F.admissible` on all queried function identifiers and `F.null`. -/
@[expose]
def ssExperiment [DecidableEq Y] (E : FE MPK MSK Fn SK M C Y) (F : Functionality Fn M Y)
    (A : Adversary MPK Fn SK M C σ) (b : Bool) : Experiment := do
  let (mpk, msk) ← E.setup
  let skNull ← E.keyGen msk F.null
  let ((pair, state), log₁) ← (A.choose mpk skNull).runLog (E.keyGen msk)
  let challenge ← E.encrypt mpk (pair.select b)
  let (guess, log₂) ← (A.guess state challenge).runLog (E.keyGen msk)
  return guess && F.admissible ((log₁ ++ log₂).map Prod.fst) pair

/-- If the null function `F.eval F.null` distinguishes `pair.msg₀` from `pair.msg₁`, then `pair` is
inadmissible under Attack Game 15.9 ([BonehShoup2023], Section 15.7, p. 660) regardless of which
key queries were made. -/
theorem Functionality.admissible_eq_false_of_null [DecidableEq Y] (F : Functionality Fn M Y)
    (queried : List Fn) (pair : MessagePair M)
    (h : F.eval F.null pair.msg₀ ≠ F.eval F.null pair.msg₁) :
    F.admissible queried pair = false := by
  simp [Functionality.admissible, h]

/-- If the null function `F.eval F.null` is injective, the two experiments of Attack Game 15.9 have
the same output distribution for every scheme and every adversary, because any admissible challenge
pair must satisfy `msg₀ = msg₁` ([BonehShoup2023], Section 15.7, Remark 15.13, p. 661). -/
theorem eval_ssExperiment_eq_of_injective_null [DecidableEq Y] (E : FE MPK MSK Fn SK M C Y)
    (F : Functionality Fn M Y) (hF : Function.Injective (F.eval F.null))
    (A : Adversary MPK Fn SK M C σ) :
    ProbComp.eval (E.ssExperiment F A false) = ProbComp.eval (E.ssExperiment F A true) := by
  simp only [ssExperiment, ProbComp.eval_bind]
  refine congrArg _ (funext fun keys => congrArg _ (funext fun skNull =>
    congrArg _ (funext fun out => ?_)))
  obtain ⟨⟨pair, state⟩, log₁⟩ := out
  by_cases h : pair.msg₀ = pair.msg₁
  · simp [MessagePair.select, h]
  · have hadm : ∀ l, F.admissible l pair = false := fun l =>
      F.admissible_eq_false_of_null l pair fun h' => h (hF h')
    simp [hadm]

/-- If the null function `F.eval F.null` is injective, every adversary has semantic-security
advantage `0` against every functional encryption scheme for `F` ([BonehShoup2023], Section 15.7,
Remark 15.13, p. 661). -/
theorem advantage_ssExperiment_eq_zero_of_injective_null [DecidableEq Y]
    (E : FE MPK MSK Fn SK M C Y) (F : Functionality Fn M Y)
    (hF : Function.Injective (F.eval F.null)) (A : Adversary MPK Fn SK M C σ) :
    Experiment.advantage (E.ssExperiment F A false) (E.ssExperiment F A true) = 0 := by
  simp only [Experiment.advantage, eval_ssExperiment_eq_of_injective_null E F hF A,
    Game.advantage_self]

/-! ### Remark 15.13: the cleartext scheme -/

/-- The cleartext functional encryption scheme of [BonehShoup2023], Section 15.7, Remark 15.13,
p. 661: encryption outputs the message `m` in the clear, a secret key for `f` is `f` itself, and
decryption evaluates `F.eval f` on the ciphertext. -/
@[expose]
def cleartext (F : Functionality Fn M Y) : FE Unit Unit Fn Fn M M Y where
  setup := pure ((), ())
  keyGen _ f := pure f
  encrypt _ m := pure m
  decrypt f c := F.eval f c

/-- The cleartext scheme `cleartext F` is correct for every functionality `F` ([BonehShoup2023],
Section 15.7, Definition 15.13 and Remark 15.13, pp. 659, 661). -/
theorem cleartext_correct (F : Functionality Fn M Y) : (cleartext F).Correct F := by
  intro keys _ f m y hy sk hsk c hc
  simp only [cleartext, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hsk hc
  subst hsk hc
  exact hy

/-- The cleartext scheme `cleartext F` is robust for every functionality `F` ([BonehShoup2023],
Section 15.7, Definition 15.15 and Remark 15.13, p. 661). -/
theorem cleartext_robust (F : Functionality Fn M Y) : (cleartext F).Robust F := by
  intro keys _ c
  refine ⟨c, fun f sk hsk y hy y' hy' => ?_⟩
  simp only [cleartext, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hsk
  subst hsk
  exact Option.some.inj (hy.symm.trans hy')

/-! ### Example 15.1: public-key encryption -/

variable {L : Type}

/-- The public-key encryption functionality of [BonehShoup2023], Section 15.7, Example 15.1,
equation (15.33), p. 659, extended with the null identifier of p. 660: `some ()` is the identity
identifier `I` returning `Sum.inl m`, and `none` is the null identifier `ε` returning the message
leakage `Sum.inr (len m)`. -/
@[expose]
def Functionality.pke (len : M → L) : Functionality (Option Unit) M (M ⊕ L) where
  eval f m := match f with
    | some _ => some (Sum.inl m)
    | none => some (Sum.inr (len m))
  null := none

/-- When the null leakage `π` in `Functionality.pke π` is injective, every adversary has
semantic-security advantage `0` against every scheme for `Functionality.pke π` ([BonehShoup2023],
Section 15.7, Remark 15.13, p. 661). -/
theorem advantage_ssExperiment_pke_eq_zero [DecidableEq M] [DecidableEq L]
    (E : FE MPK MSK (Option Unit) SK M C (M ⊕ L)) {π : M → L} (hπ : Function.Injective π)
    (A : Adversary MPK (Option Unit) SK M C σ) :
    Experiment.advantage (E.ssExperiment (Functionality.pke π) A false)
      (E.ssExperiment (Functionality.pke π) A true) = 0 :=
  advantage_ssExperiment_eq_zero_of_injective_null E _
    (fun _ _ h => hπ (Sum.inr.inj (Option.some.inj h))) A

/-- Lift a `TwoStage` chosen-plaintext adversary to an `FE.Adversary` that ignores the null key and
makes no key-generation queries ([BonehShoup2023], Section 15.7, Example 15.1 and Attack Game 15.9,
pp. 659–661). This checks the new game against the chosen-plaintext experiment already in the
library; it is not a reduction, carries no efficiency claim, and closes no security item. -/
@[expose]
def Adversary.ofTwoStage (A : TwoStage MPK (MessagePair M) C Bool σ) :
    Adversary MPK Fn SK M C σ where
  choose mpk _ := ProbOracleComp.sample (A.choose mpk)
  guess state c := ProbOracleComp.sample (A.guess state c)

end FE

namespace PKE

variable {PK SK M C L σ : Type}

/-- View a public-key encryption scheme `E` as a functional encryption scheme ([BonehShoup2023],
Section 15.7, Example 15.1, p. 659, and p. 660): the full key for `some ()` is `some sk`, which
decrypts with `E.decrypt sk`, and the null key for `none` is `none`, which reads `leak c` off the
ciphertext. -/
@[expose]
def toFE (E : PKE PK SK M C) (leak : C → L) :
    FE PK SK (Option Unit) (Option SK) M C (M ⊕ L) where
  setup := E.keyGen
  keyGen sk f := pure (f.map fun _ => sk)
  encrypt := E.encrypt
  decrypt key c := match key with
    | some sk => (E.decrypt sk c).map Sum.inl
    | none => some (Sum.inr (leak c))

/-- `E.toFE leak` is a correct functional encryption scheme for `FE.Functionality.pke len` if and
only if `E` is a correct public-key scheme and `leak c = len m` for every honestly generated key
pair and every honest encryption `c` of `m` ([BonehShoup2023], Section 15.7, Definition 15.13 and
Example 15.1, p. 659, and p. 660). -/
theorem toFE_correct_iff (E : PKE PK SK M C) (len : M → L) (leak : C → L) :
    (E.toFE leak).Correct (FE.Functionality.pke len) ↔
      E.Correct ∧ ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ m,
        ∀ c ∈ (ProbComp.eval (E.encrypt keys.1 m)).support, leak c = len m := by
  refine ⟨fun h => ⟨fun keys hkeys m c hc => ?_, fun keys hkeys m c hc => ?_⟩, ?_⟩
  · have := h keys hkeys (some ()) m (Sum.inl m) rfl (some keys.2) (by simp [toFE]) c hc
    simpa [toFE] using this
  · have := h keys hkeys none m (Sum.inr (len m)) rfl none (by simp [toFE]) c hc
    simpa [toFE] using this
  · rintro ⟨hE, hleak⟩ keys hkeys f m y hy sk hsk c hc
    simp only [toFE, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hsk
    subst hsk
    cases f with
    | none =>
      simp only [FE.Functionality.pke, Option.some.injEq] at hy
      simp [toFE, ← hy, hleak keys hkeys m c hc]
    | some _ =>
      simp only [FE.Functionality.pke, Option.some.injEq] at hy
      simp [toFE, ← hy, hE keys hkeys m c hc]

/-- Played against an adversary `FE.Adversary.ofTwoStage A` that makes no key-generation queries,
Attack Game 15.9 for `E.toFE leak` and `FE.Functionality.pke len` has the same output distribution
as Attack Game 11.1 (`E.cpaExperiment`) with admissibility rule `len m₀ = len m₁`
([BonehShoup2023], Section 15.7, Example 15.1 and Attack Game 15.9, pp. 659–661, and Section 11.2,
Attack Game 11.1, p. 436). This checks the new game against the chosen-plaintext experiment already
in the library; it is not a reduction, carries no efficiency claim, and closes no security item. -/
theorem eval_ssExperiment_toFE_ofTwoStage [DecidableEq M] [DecidableEq L] (E : PKE PK SK M C)
    (len : M → L) (leak : C → L) (A : TwoStage PK (MessagePair M) C Bool σ) (b : Bool) :
    ProbComp.eval ((E.toFE leak).ssExperiment (FE.Functionality.pke len)
        (FE.Adversary.ofTwoStage A) b) =
      ProbComp.eval (E.cpaExperiment (fun _ m₀ m₁ => decide (len m₀ = len m₁)) A b) := by
  simp only [FE.ssExperiment, cpaExperiment, FE.Adversary.ofTwoStage, ProbOracleComp.runLog_sample,
    toFE, FE.Functionality.pke, ProbComp.eval_bind, eval_lrExperiment, ProbComp.eval_pure,
    ProbComp.eval_map, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun keys => congrArg _ (funext fun out => ?_))
  obtain ⟨pair, state⟩ := out
  by_cases h : len pair.msg₀ = len pair.msg₁
  · simp [FE.Functionality.admissible, h]
  · simp [FE.Functionality.admissible, h]

end PKE

end Cslib.Crypto
