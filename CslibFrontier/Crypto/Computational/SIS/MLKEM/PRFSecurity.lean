/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.PRFExpansion
public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Asymptotic
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# IND-CPA of K-PKE with the matrix in the public key, from Module-LWE and a PRF

`indCPA_kpkePRF_of_decisionModuleLWEWith` is IND-CPA of the full-matrix K-PKE family with PRF seed
expansion, a step towards Kyber v3.02 Theorem 1 ([AvanziEtAl2021], §4.3.1, p. 20) and not that
theorem. The public key carries the sampled matrix in place of the seed `ρ`, the seed `σ` is
sampled directly, and neither the scheme nor the adversary has an `XOF` or `G` oracle. Theorem 1
assumes that `XOF` and `G` are random oracles and bounds the IND-CPA advantage of Kyber.CPAPKE by
`2 · Adv^mlwe_{k+1,k,η} + Adv^prf_PRF`; this theorem has the `Adv^prf_PRF` hop but not the
random-oracle model. The remaining step to Theorem 1 itself is the random-oracle lift: the scheme
with `ρ` in the public key and `XOF` and `G` oracles, with a lazily sampled, programmable simulator
and its efficiency witness. It is open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765),
and depends on that issue's §3 gap A, a reusable oracle-PPT certificate for a lazily sampled,
programmable random oracle.

Here, K-PKE with its noise expanded from seeds by a keyed function `F` (`kpkePRF P F`) is IND-CPA
secure (`WordPKE.INDCPA`: every uniform strict PPT chosen-message adversary has negligible
advantage) whenever

* decision Module-LWE (`DecisionModuleLWEWith`) holds for the two shapes of Kyber's proof with the
  centered-binomial laws `cbdLaw`, as in `indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`, and
* `F` is a pseudorandom function with `κ`-bit keys, counter words of `nonceLen` bits as inputs and
  `prfLen = n · 2 · max(η₁, η₂)`-bit outputs (`PseudorandomFunctionOver`), the source's
  `Adv^prf_PRF` term.

## The proof

At each `κ` and challenge bit `b` there are three games:

* G0, the IND-CPA game of `kpkePRF P F`;
* G1, the same game with the key generation `keyGenWord` of `kpke P`, which decodes `s` and `e`
  from fair coins;
* G2, the IND-CPA game of `kpke P`, which also draws the encryption noise from fair coins.

The key-generation hop `keyPRFReduction P F A b` is a PRF distinguisher that runs G0, reading the
noise bits of key generation from its oracle at the counters `0, …, 2k − 1`. Against `F` under a
uniform key it plays G0 (`eval_prfRealGame_keyPRFReduction`), and against a uniform random
function G1 (`eval_prfIdealGame_keyPRFReduction`): a uniform function read at the distinct
counter words gives fair coins (`BitString.uniformOfFintype_map_readPrefixes`). The encryption hop
`encPRFReduction P A b` likewise reads the encryption coins at the counters `0, …, 2k` and plays
G1 against `F` and G2 against a random function. Both reductions are oracle PPT whenever `A` is
PPT, the parameters are computable in polynomial time and, for the key-generation hop, `F` is
evaluated in polynomial time (`isOraclePPT_keyPRFReduction`, `isOraclePPT_encPRFReduction`). So
the advantage of `A` against `kpkePRF P F` is at most four PRF advantages of these reductions plus
its advantage against `kpke P` (`advantage_gameOn_kpkePRF_le`), which is negligible by
`indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`.

## Differences from Kyber v3.02 Theorem 1

The random oracles make this a step and not Theorem 1:

* The public key carries the matrix `A`, which key generation draws coefficientwise within
  `k * k * n / 2 ^ κ` of uniform, and the seed `σ` of key generation is sampled uniformly. In
  Kyber the public key is `Encode(t̂) ‖ ρ` with `(ρ, σ) := G(d)`, and encryption re-derives `A` as
  `XOF(ρ)` (Algorithms 4 and 5, pp. 8–9). Theorem 1 assumes that `XOF` and `G` are random oracles,
  which the adversary may query, so a reduction in its model must answer the adversary's `XOF`
  queries at `ρ` with its Module-LWE matrix. Here neither the scheme nor the adversary has an `XOF`
  or `G` oracle (`WordPKE.INDCPA` quantifies over adversaries without oracles), so that step is not
  formalized. The proved distance compares matrix distributions only and does not relate the
  random-oracle game to this one. The random-oracle lift is open under #5293, as above.

The remaining differences restate Theorem 1 in this library's setting:

* The statement is asymptotic over a parameter family, against uniform classical strict PPT
  adversaries, with `κ`-bit seeds in place of 32-byte ones; the source states a concrete bound at
  fixed parameter sets. The assumptions are meaningful only when the parameters grow with `κ`.
* The PRF counter is written in `(2k).size` bits rather than one byte, and `F` has one output
  length, `n · 2 · max(η₁, η₂)` bits, of which each counter reads a prefix; Kyber's `PRF` has
  outputs of any length, and SHAKE-256 outputs of different lengths are prefixes of one another.
* The Module-LWE terms are those of §4.4, eq. (6), p. 22, without compression, in place of
  `2 · Adv^mlwe_{k+1,k,η}` (see `indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`).
* The bound has four PRF advantages, the two hops for each challenge bit, in place of one
  `Adv^prf_PRF` term.
* Polynomials are in coefficient form, keys and ciphertexts are words of residue lists, and
  messages are words of exactly `n` bits.

This is IND-CPA of K-PKE (Kyber.CPAPKE) with the matrix in the public key; it is not a statement
about ML-KEM ([NISTFIPS203]) or its Fujisaki–Okamoto transform.

## Main definitions

* `Cslib.Crypto.MLKEM.queryNoise`: reading noise bits from a PRF oracle at the counter words.
* `Cslib.Crypto.MLKEM.keyPRFReduction`, `Cslib.Crypto.MLKEM.encPRFReduction`: the two PRF hops.

## Main results

* `Cslib.Crypto.MLKEM.isOraclePPT_keyPRFReduction`,
  `Cslib.Crypto.MLKEM.isOraclePPT_encPRFReduction`: the reductions are uniform strict oracle PPT,
  from the adversary's certificate.
* `Cslib.Crypto.MLKEM.advantage_gameOn_kpkePRF_le`: the concrete bound at each `κ`.
* `Cslib.Crypto.MLKEM.indCPA_kpkePRF_of_decisionModuleLWEWith`: IND-CPA of K-PKE with the matrix
  in the public key from Module-LWE and a pseudorandom function, a step towards Kyber v3.02
  Theorem 1.

## References

* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, Algorithms 4 and 5 (pp. 8–9), §4.3.1
  (Theorem 1, p. 20) and §4.4 (eq. (6), p. 22)
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Attack
  Game 4.2 and Definition 4.2, pp. 132–133
-/

public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.FujisakiOkamoto Cslib.Crypto.Encryption
open scoped NNReal

/-! ### Reading noise from the oracle -/

/-- One step of `queryNoise`: ask the oracle for the word of counter `N`, keep the first `width N`
bits of the reply and append them to the bits read so far. -/
private def queryNoiseStep (P : Params) (width : ℕ → ℕ) (state : ℕ × List Bool) :
    WordOracleComp Unit (ℕ × List Bool) :=
  (fun reply => (state.1 + 1, state.2 ++ reply)) <$>
    (List.take (width state.1) <$> ProbOracleComp.query ((), nonceWord P state.1))

/-- Read the noise of the counters `0, …, count − 1` from the oracle: the first `width N` bits of
the reply to the word of each counter `N`, concatenated. Against `F` under a key this is
`expandNoise` (`run_queryNoise_prfOracle`). -/
def queryNoise (P : Params) (count : ℕ) (width : ℕ → ℕ) : WordOracleComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate count (queryNoiseStep P width) (0, [])

/-- Against a word oracle answering each request word `x` by `oracle x`, `queryNoise` reads the
first `width N` bits of `oracle` at each counter word. -/
theorem run_queryNoise (P : Params) (count : ℕ) (width : ℕ → ℕ)
    (oracle : List Bool → List Bool) :
    (queryNoise P count width).run (fun request => pure (oracle request.2)) =
      pure ((List.range count).flatMap fun N => (oracle (nonceWord P N)).take (width N)) := by
  have hloop (m : ℕ) : ProbOracleComp.run (OracleComp.iterate m (queryNoiseStep P width) (0, []))
      (fun request => pure (oracle request.2)) =
      pure (m, (List.range m).flatMap fun N => (oracle (nonceWord P N)).take (width N)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih, pure_bind]
      simp [queryNoiseStep, List.range_succ, List.flatMap_append]
  simp only [queryNoise, ProbOracleComp.run_map, hloop, map_pure]

/-- Against `F` under the key `key`, `queryNoise` reads `expandNoise`. -/
theorem run_queryNoise_prfOracle (P : Params) (F : List Bool → List Bool → List Bool)
    (key : List Bool) (count : ℕ) (width : ℕ → ℕ) :
    (queryNoise P count width).run
        (fun request => pure (prfOracle F (nonceLen P) key request.2)) =
      pure (expandNoise P F key count width) := by
  rw [run_queryNoise]
  simp [expandNoise, prfOracle]

/-- A uniform random function on the counter words gives fair coins: reading the first
`width N ≤ w` bits of a uniform function from `nonceLen P`-bit to `w`-bit strings at the words of
the counters `N < count ≤ 2k + 1` gives a uniform word of `∑ width N` bits. -/
private theorem uniformOfFintype_map_counterWords (P : Params) {w count : ℕ}
    (hcount : count ≤ 2 * P.k + 1) (width : ℕ → ℕ) (hwidth : ∀ N < count, width N ≤ w) :
    (PMF.uniformOfFintype (BitString (nonceLen P) → BitString w)).map (fun table =>
        (List.range count).flatMap fun N =>
          (randomFunctionOracle (nonceLen P) table (nonceWord P N)).take (width N)) =
      BitString.uniformList (∑ N ∈ Finset.range count, width N) := by
  have hinj : Function.Injective fun i : Fin count =>
      BitString.ofList (nonceLen P) (nonceWord P i) := by
    intro i j h
    have hword : nonceWord P i = nonceWord P j := by
      rw [← BitString.ofFn_ofList (length_nonceWord P i),
        ← BitString.ofFn_ofList (length_nonceWord P j)]
      exact congrArg List.ofFn h
    exact Fin.ext (nonceWord_injOn P (Set.mem_Iic.mpr (by omega))
      (Set.mem_Iic.mpr (by omega)) hword)
  have h := BitString.uniformOfFintype_map_readPrefixes ⟨_, hinj⟩ (fun i => width i)
    fun i => hwidth i i.2
  rw [Fin.sum_univ_eq_sum_range (fun N => width N) count] at h
  rw [← h]
  congr 1
  funext table
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [randomFunctionOracle]

/-! ### Efficiency of reading the noise -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- **Reading the noise is oracle PPT**, with computed parameters, count and widths, when the
widths are bounded by a computed unary bound. -/
theorem isOraclePPTOn_queryNoise {P : α → Params} {count : α → ℕ} {width : α → ℕ → ℕ}
    {bound : α → ℕ} (hP : ComputableInPolyTime P input encParams)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime (fun p : α × ℕ => width p.1 p.2) (encPair input encUnary)
      encUnary)
    (hbound : ComputableInPolyTime bound input encUnary) (hle : ∀ a N, width a N ≤ bound a) :
    IsOraclePPTOn input encBits (fun a => queryNoise (P a) (count a) (width a)) := by
  unfold queryNoise
  let S := encPair encUnary encBits
  have hstep : IsOraclePPTOn (encPair input S) S
      (fun pair : α × (ℕ × List Bool) => queryNoiseStep (P pair.1) (width pair.1) pair.2) := by
    unfold queryNoiseStep
    have hreq : ComputableInPolyTime
        (fun pair : α × (ℕ × List Bool) => nonceWord (P pair.1) pair.2.1) (encPair input S)
        encBits :=
      ComputableInPolyTime.nonceWord (hP.comp (ComputableInPolyTime.fst input S))
        (by fun_prop)
    have hlim : ComputableInPolyTime
        (fun pair : α × (ℕ × List Bool) => width pair.1 pair.2.1) (encPair input S) encUnary :=
      hwidth.comp (by fun_prop : ComputableInPolyTime
        (fun pair : α × (ℕ × List Bool) => (pair.1, pair.2.1)) (encPair input S)
        (encPair input encUnary))
    have hpost : ComputableInPolyTime
        (fun p : (α × (ℕ × List Bool)) × List Bool => (p.1.2.1 + 1, p.1.2.2 ++ p.2))
        (encPair (encPair input S) encBits) S := by fun_prop
    exact (IsOraclePPTOn.query_take' () hreq hlim).map_with' hpost
  have hgrowth : ∀ a (state : ℕ × List Bool),
      ∀ next ∈ OracleComp.support (queryNoiseStep (P a) (width a) state),
        (S next).length ≤ (S state).length + (2 * bound a + 4) := by
    rintro a ⟨N, acc⟩ next hnext
    unfold queryNoiseStep at hnext
    obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    have htake : (List.take (width a N) raw).length ≤ bound a := by
      rw [List.length_take]
      exact (min_le_left _ _).trans (hle a N)
    simp only [S, length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      List.length_append]
    omega
  have hpoly : PolyBounded (fun a => (input a).length) (fun a => 2 * bound a + 4) :=
    ((PolyBounded.const 2).mul (ComputableInPolyTime.polyBounded hbound)).add (PolyBounded.const 4)
  exact (IsOraclePPTOn.iterateWith_of_bounded_growth' hcount (ComputableInPolyTime.const (0, []))
    hstep hpoly hgrowth).map' (ComputableInPolyTime.snd encUnary encBits)

end PolyTime

/-! ### The reductions -/

section Reductions

variable (P : ℕ → Params) (F : List Bool → List Bool → List Bool)

/-- The IND-CPA game of `kpkePRF P F` against `A` with challenge bit `b`, from the public key `pk`
on: run `A.choose` on `pk`; if the pair is admissible, encrypt the selected message with a uniform
`κ`-bit seed expanded by `encNoise` and return `A.guess`, and otherwise return `false`. -/
private noncomputable def afterKeyPRF (A : Encryption.WordAdversary) (b : Bool) (κ : ℕ)
    (pk : List Bool) : ProbComp Bool := do
  let choice ← A.choose κ pk
  if (kpke P).IsMessagePair κ pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let r ← BitString.sampleList κ
    A.guess κ (ChoiceOut.state choice) (encDetWord (P κ) pk
      (if b then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice) (encNoise (P κ) F r))
  else
    return false

/-- **The key-generation hop.** A PRF distinguisher that runs the IND-CPA game of `kpkePRF P F`
against `A` with challenge bit `b`, reading the noise of key generation from its oracle: it draws
the matrix as `keyGenWord` does, reads `n · 2η₁` bits at each counter `0, …, 2k − 1`
(`queryNoise`), decodes `s` and `e` from them, and runs `afterKeyPRF` on the public key. -/
noncomputable def keyPRFReduction (A : Encryption.WordAdversary) (b : Bool) :
    OracleDistinguisher := fun κ _ => do
  let matrix ← ProbOracleComp.sample (sampleMatrixResidues (P κ) κ)
  let bits ← queryNoise (P κ) (2 * (P κ).k) fun _ => (P κ).n * (2 * (P κ).η₁)
  ProbOracleComp.sample (afterKeyPRF P F A b κ (keyWords (P κ) matrix
    (bits.take ((P κ).k * ((P κ).n * (2 * (P κ).η₁))))
    (bits.drop ((P κ).k * ((P κ).n * (2 * (P κ).η₁))))).1)

/-- **The encryption hop.** A PRF distinguisher that runs the IND-CPA game of `kpke P` against `A`
with challenge bit `b`, reading the encryption coins from its oracle: it generates keys with
`keyGenWord`, runs `A.choose`, and if the pair is admissible reads the coins of the counters
`0, …, 2k` (`queryNoise` with `encWidth`), encrypts with `encDetWord` and returns `A.guess`. -/
noncomputable def encPRFReduction (A : Encryption.WordAdversary) (b : Bool) :
    OracleDistinguisher := fun κ _ => do
  let keys ← ProbOracleComp.sample (keyGenWord (P κ) κ)
  let choice ← ProbOracleComp.sample (A.choose κ keys.1)
  if (kpke P).IsMessagePair κ keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let coins ← queryNoise (P κ) (2 * (P κ).k + 1) (encWidth (P κ))
    ProbOracleComp.sample (A.guess κ (ChoiceOut.state choice) (encDetWord (P κ) keys.1
      (if b then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice) coins))
  else
    pure false

variable {P F}

/-- The continuation `afterKeyPRF` is uniform strict PPT on `(κ, pk)`. -/
private theorem isPPTOn_afterKeyPRF (hP : ComputableInPolyTime P encUnary encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    {A : Encryption.WordAdversary} (hA : A.IsPPT) (b : Bool) :
    IsPPTOn (encPair encUnary encBits) encBool (fun x => afterKeyPRF P F A b x.1 x.2) := by
  unfold afterKeyPRF
  let E := encPair encUnary encBits
  refine hA.choose.on.bind_with ?_
  let G := encPair E (Encryption.encChoiceOut encBits)
  have hκ : ComputableInPolyTime (fun y : (ℕ × List Bool) × ChoiceOut (List Bool) => y.1.1) G
      encUnary := by fun_prop
  have hPG := hP.comp hκ
  have hvalid : ComputableInPolyTime (fun y : (ℕ × List Bool) × ChoiceOut (List Bool) =>
      (kpke P).IsMessagePair y.1.1 y.1.2 (ChoiceOut.msg₀ y.2) (ChoiceOut.msg₁ y.2)) G encBool := by
    simp only [WordPKE.IsMessagePair, kpke]
    fun_prop
  refine IsPPTOn.cond' hvalid ((isPPTOn_sampleList.preprocess hκ).bind_with ?_)
    (ComputableInPolyTime.const false).isPPTOn
  let H := encPair G encBits
  have hκH : ComputableInPolyTime (fun z : ((ℕ × List Bool) × ChoiceOut (List Bool)) × List Bool =>
      z.1.1.1) H encUnary := by fun_prop
  have hPH := hP.comp hκH
  have hm : ComputableInPolyTime (fun z : ((ℕ × List Bool) × ChoiceOut (List Bool)) × List Bool =>
      if b then ChoiceOut.msg₁ z.1.2 else ChoiceOut.msg₀ z.1.2) H encBits := by
    cases b <;> fun_prop
  have hpk : ComputableInPolyTime (fun z : ((ℕ × List Bool) × ChoiceOut (List Bool)) × List Bool =>
      z.1.1.2) H encBits := by fun_prop
  have hr : ComputableInPolyTime (fun z : ((ℕ × List Bool) × ChoiceOut (List Bool)) × List Bool =>
      z.2) H encBits := by fun_prop
  have hct := ComputableInPolyTime.encDetWord hPH hpk hm (ComputableInPolyTime.encNoise hPH hF hr)
  exact hA.guess.preprocess (hκH.prod ((by fun_prop : ComputableInPolyTime
    (fun z : ((ℕ × List Bool) × ChoiceOut (List Bool)) × List Bool => ChoiceOut.state z.1.2) H
      encBits).prod hct))

/-- **The key-generation hop is uniform strict oracle PPT** when the parameters are computable in
polynomial time, `F` is evaluated in polynomial time and `A` is uniform strict PPT. -/
theorem isOraclePPT_keyPRFReduction (hP : ComputableInPolyTime P encUnary encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    {A : Encryption.WordAdversary} (hA : A.IsPPT) (b : Bool) :
    IsOraclePPT encBool (keyPRFReduction P F A b) := by
  apply IsOraclePPTOn.isOraclePPT
  unfold keyPRFReduction
  let E := encPair encUnary encBits
  have hκ : ComputableInPolyTime (fun x : ℕ × List Bool => x.1) E encUnary := by fun_prop
  have hmatrix := (isPPTOn_sampleMatrixResidues.preprocess ((hP.comp hκ).prod hκ)).isOraclePPTOn
    (Operation := Unit)
  refine hmatrix.bind_with ?_
  let E₁ := encPair E encMatrixResidues
  have hκ₁ : ComputableInPolyTime (fun y : (ℕ × List Bool) × List (List (List ℕ)) => y.1.1) E₁
      encUnary := by fun_prop
  have hP₁ := hP.comp hκ₁
  have hw₁ : ComputableInPolyTime (fun y : (ℕ × List Bool) × List (List (List ℕ)) =>
      (P y.1.1).n * (2 * (P y.1.1).η₁)) E₁ encUnary := by fun_prop
  have hquery := isOraclePPTOn_queryNoise (P := fun y => P y.1.1)
    (count := fun y => 2 * (P y.1.1).k) (width := fun y _ => (P y.1.1).n * (2 * (P y.1.1).η₁))
    hP₁ (by fun_prop) (hw₁.comp (ComputableInPolyTime.fst E₁ encUnary)) hw₁ fun _ _ => le_rfl
  refine hquery.bind_with ?_
  let E₂ := encPair E₁ encBits
  have hκ₂ : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × List (List (List ℕ))) × List Bool => z.1.1.1) E₂ encUnary := by
    fun_prop
  have hP₂ := hP.comp hκ₂
  have hL : ComputableInPolyTime (fun z : ((ℕ × List Bool) × List (List (List ℕ))) × List Bool =>
      (P z.1.1.1).k * ((P z.1.1.1).n * (2 * (P z.1.1.1).η₁))) E₂ encUnary := by fun_prop
  have hbits : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × List (List (List ℕ))) × List Bool => z.2) E₂ encBits := by
    fun_prop
  have hM : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × List (List (List ℕ))) × List Bool => z.1.2) E₂
      encMatrixResidues := by fun_prop
  have hkeys := ComputableInPolyTime.keyWords hP₂ hM
    (ComputableInPolyTime.bitsTakeWithInput hbits hL)
    (ComputableInPolyTime.bitsDropWithInput hbits hL)
  exact ((isPPTOn_afterKeyPRF hP hF hA b).preprocess (hκ₂.prod hkeys.fst')).isOraclePPTOn

/-- **The encryption hop is uniform strict oracle PPT** when the parameters are computable in
polynomial time and `A` is uniform strict PPT. -/
theorem isOraclePPT_encPRFReduction (hP : ComputableInPolyTime P encUnary encParams)
    {A : Encryption.WordAdversary} (hA : A.IsPPT) (b : Bool) :
    IsOraclePPT encBool (encPRFReduction P A b) := by
  apply IsOraclePPTOn.isOraclePPT
  unfold encPRFReduction
  let E := encPair encUnary encBits
  have hκ : ComputableInPolyTime (fun x : ℕ × List Bool => x.1) E encUnary := by fun_prop
  have hkeys := (isPPTOn_keyGenWord.preprocess ((hP.comp hκ).prod hκ)).isOraclePPTOn
    (Operation := Unit)
  refine hkeys.bind_with ?_
  let E₁ := encPair E (encPair encBits encBits)
  have hκ₁ : ComputableInPolyTime (fun y : (ℕ × List Bool) × (List Bool × List Bool) => y.1.1) E₁
      encUnary := by fun_prop
  have hpk₁ : ComputableInPolyTime (fun y : (ℕ × List Bool) × (List Bool × List Bool) => y.2.1)
      E₁ encBits := by fun_prop
  refine ((hA.choose.on.preprocess (hκ₁.prod hpk₁)).isOraclePPTOn (Operation := Unit)).bind_with ?_
  let E₂ := encPair E₁ (Encryption.encChoiceOut encBits)
  have hκ₂ : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool) => z.1.1.1) E₂
      encUnary := by fun_prop
  have hP₂ := hP.comp hκ₂
  have hvalid : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool) =>
        (kpke P).IsMessagePair z.1.1.1 z.1.2.1 (ChoiceOut.msg₀ z.2) (ChoiceOut.msg₁ z.2)) E₂
      encBool := by
    simp only [WordPKE.IsMessagePair, kpke]
    fun_prop
  refine IsOraclePPTOn.cond' hvalid ?_ (ComputableInPolyTime.const false).isOraclePPTOn
  have hbound : ComputableInPolyTime
      (fun z : ((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool) =>
        (P z.1.1.1).n * (2 * (P z.1.1.1).η₁) + (P z.1.1.1).n * (2 * (P z.1.1.1).η₂)) E₂
      encUnary := by fun_prop
  have hquery := isOraclePPTOn_queryNoise (P := fun z => P z.1.1.1)
    (count := fun z => 2 * (P z.1.1.1).k + 1) (width := fun z => encWidth (P z.1.1.1))
    hP₂ (by fun_prop) (ComputableInPolyTime.encWidth (hP₂.comp (ComputableInPolyTime.fst E₂ _))
      (ComputableInPolyTime.snd E₂ encUnary)) hbound fun z N => by
        unfold encWidth
        split_ifs <;> omega
  refine hquery.bind_with ?_
  let E₃ := encPair E₂ encBits
  have hκ₃ : ComputableInPolyTime
      (fun z : (((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool)) × List Bool =>
        z.1.1.1.1) E₃ encUnary := by fun_prop
  have hm : ComputableInPolyTime
      (fun z : (((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool)) × List Bool =>
        if b then ChoiceOut.msg₁ z.1.2 else ChoiceOut.msg₀ z.1.2) E₃ encBits := by
    cases b <;> fun_prop
  have hpk : ComputableInPolyTime
      (fun z : (((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool)) × List Bool =>
        z.1.1.2.1) E₃ encBits := by fun_prop
  have hcoins : ComputableInPolyTime
      (fun z : (((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool)) × List Bool =>
        z.2) E₃ encBits := by fun_prop
  have hct := ComputableInPolyTime.encDetWord (hP.comp hκ₃) hpk hm hcoins
  exact (hA.guess.preprocess (hκ₃.prod ((by fun_prop : ComputableInPolyTime
    (fun z : (((ℕ × List Bool) × (List Bool × List Bool)) × ChoiceOut (List Bool)) × List Bool =>
      ChoiceOut.state z.1.2) E₃ encBits).prod hct))).isOraclePPTOn

end Reductions

/-! ### The hybrids -/

section Hybrids

variable (P : ℕ → Params) (F : List Bool → List Bool → List Bool) (A : Encryption.WordAdversary)
  (b : Bool)

/-- The IND-CPA game of `kpkePRF P F` with any key generator `keyGen` is `keyGen`, then
`afterKeyPRF` on the public key. -/
private theorem eval_gameOn_kpkePRF (keyGen : ℕ → ProbComp (List Bool × List Bool)) (κ : ℕ) :
    ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair keyGen (kpkePRF P F).encrypt A b κ) =
      (ProbComp.eval (keyGen κ)).bind fun keys => ProbComp.eval (afterKeyPRF P F A b κ keys.1) := by
  have hvalid : (kpkePRF P F).IsMessagePair = (kpke P).IsMessagePair := rfl
  simp only [gameOn, afterKeyPRF, hvalid, ProbComp.eval_bind]
  refine congrArg _ (funext fun keys => congrArg _ (funext fun choice => ?_))
  by_cases hv : (kpke P).IsMessagePair κ keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice)
  · simp only [hv, ↓reduceIte, WordPKE.encrypt, kpkePRF, bind_assoc, pure_bind]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

/-- **The key-generation hop against `F` is G0**: the real PRF game of `keyPRFReduction P F A b`
is the IND-CPA game of `kpkePRF P F` with challenge bit `b`. -/
theorem eval_prfRealGame_keyPRFReduction (κ : ℕ) :
    ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F (keyPRFReduction P F A b) κ) =
      ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair (kpkePRF P F).keyGen
        (kpkePRF P F).encrypt A b κ) := by
  rw [eval_gameOn_kpkePRF]
  simp only [prfRealGame, keyPRFReduction, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, run_queryNoise_prfOracle, pure_bind, kpkePRF, keyGenPRFWord,
    keyNoise, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    BitString.eval_sampleList]
  exact PMF.bind_comm _ _ _

/-- **The key-generation hop against a random function is G1**: the ideal PRF game of
`keyPRFReduction P F A b` is the IND-CPA game of `kpkePRF P F` with challenge bit `b` and the key
generation of `kpke P`. -/
theorem eval_prfIdealGame_keyPRFReduction (κ : ℕ) :
    ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
        (keyPRFReduction P F A b) κ) =
      ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair (kpke P).keyGen
        (kpkePRF P F).encrypt A b κ) := by
  rw [eval_gameOn_kpkePRF]
  set L := (P κ).k * ((P κ).n * (2 * (P κ).η₁))
  have hread := uniformOfFintype_map_counterWords (P κ) (w := prfLen (P κ)) (Nat.le_succ _)
    (fun _ => (P κ).n * (2 * (P κ).η₁)) fun _ _ =>
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_left _ _))
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
    show 2 * (P κ).k * ((P κ).n * (2 * (P κ).η₁)) = L + L by simp only [L]; ring] at hread
  simp only [prfIdealGame, keyPRFReduction, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, run_queryNoise, pure_bind, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  rw [PMF.bind_comm]
  simp only [kpke, keyGenWord, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext matrix
  rw [← BitString.uniformList_bind_split L L, ← hread, PMF.bind_map]
  rfl

/-- **The encryption hop against `F` is G1**: the real PRF game of `encPRFReduction P A b` is the
IND-CPA game of `kpkePRF P F` with challenge bit `b` and the key generation of `kpke P`. -/
theorem eval_prfRealGame_encPRFReduction (κ : ℕ) :
    ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F (encPRFReduction P A b) κ) =
      ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair (kpke P).keyGen
        (kpkePRF P F).encrypt A b κ) := by
  rw [eval_gameOn_kpkePRF, show (kpke P).keyGen κ = keyGenWord (P κ) κ from rfl]
  simp only [prfRealGame, encPRFReduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun keys => ?_)
  simp only [afterKeyPRF, ProbComp.eval_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun choice => ?_)
  by_cases hv : (kpke P).IsMessagePair κ keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice)
  · simp only [hv, ↓reduceIte, ProbOracleComp.run_bind, run_queryNoise_prfOracle, pure_bind,
      ProbOracleComp.run_sample, ProbComp.eval_bind, BitString.eval_sampleList, encNoise]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure,
      PMF.bind_const]

/-- **The encryption hop against a random function is G2**: the ideal PRF game of
`encPRFReduction P A b` is the IND-CPA game of `kpke P` with challenge bit `b`. -/
theorem eval_prfIdealGame_encPRFReduction (κ : ℕ) :
    ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
        (encPRFReduction P A b) κ) =
      ProbComp.eval (gameOn (kpke P).IsMessagePair (kpke P).keyGen (kpke P).encrypt A b κ) := by
  have hread := uniformOfFintype_map_counterWords (P κ) (w := prfLen (P κ)) le_rfl (encWidth (P κ))
    fun N _ => by
      unfold encWidth prfLen
      split_ifs
      · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_left _ _))
      · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_right _ _))
  have hsum : ∑ N ∈ Finset.range (2 * (P κ).k + 1), encWidth (P κ) N = coinLength (P κ) := by
    have hw₁ : ∀ N ∈ Finset.range (P κ).k, encWidth (P κ) N = (P κ).n * (2 * (P κ).η₁) := by
      intro N hN
      have := Finset.mem_range.mp hN
      unfold encWidth
      split_ifs
      omega
    have hw₂ : ∀ N ∈ Finset.range (P κ).k,
        encWidth (P κ) ((P κ).k + N) = (P κ).n * (2 * (P κ).η₂) := by
      intro N _
      unfold encWidth
      split_ifs <;> omega
    have hlast : encWidth (P κ) (2 * (P κ).k) = (P κ).n * (2 * (P κ).η₂) := by
      unfold encWidth
      split_ifs <;> omega
    rw [Finset.sum_range_succ, hlast, show 2 * (P κ).k = (P κ).k + (P κ).k by omega,
      Finset.sum_range_add, Finset.sum_congr rfl hw₁, Finset.sum_congr rfl hw₂, Finset.sum_const,
      Finset.sum_const, Finset.card_range, smul_eq_mul, smul_eq_mul]
    rfl
  rw [hsum] at hread
  simp only [prfIdealGame, encPRFReduction, gameOn, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind, ProbComp.eval_uniform]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun keys => ?_)
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun choice => ?_)
  by_cases hv : (kpke P).IsMessagePair κ keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice)
  · simp only [hv, ↓reduceIte, ProbOracleComp.run_bind, run_queryNoise, pure_bind,
      ProbOracleComp.run_sample, ProbComp.eval_bind, WordPKE.encrypt, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
    rw [show (kpke P).coinLen κ = coinLength (P κ) from rfl, ← hread, PMF.bind_map]
    rfl
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_pure, ProbComp.eval_pure,
      PMF.bind_const]

end Hybrids

/-! ### IND-CPA from Module-LWE and a pseudorandom function -/

/-- **Concrete IND-CPA bound for K-PKE with seed expansion**, a step of
`indCPA_kpkePRF_of_decisionModuleLWEWith`: at each `κ`, the advantage of `A` against `kpkePRF P F`
is at most the PRF advantages of the key-generation and encryption hops for both challenge bits,
plus the advantage of `A` against `kpke P`. -/
theorem advantage_gameOn_kpkePRF_le (P : ℕ → Params) (F : List Bool → List Bool → List Bool)
    (A : Encryption.WordAdversary) (κ : ℕ) :
    Encryption.advantage
        (gameOn (kpkePRF P F).IsMessagePair (kpkePRF P F).keyGen (kpkePRF P F).encrypt A) κ ≤
      Game.advantage
          (ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F
            (keyPRFReduction P F A false) κ))
          (ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
            (keyPRFReduction P F A false) κ)) +
        (Game.advantage
          (ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F
            (encPRFReduction P A false) κ))
          (ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
            (encPRFReduction P A false) κ)) +
        (Encryption.advantage (gameOn (kpke P).IsMessagePair (kpke P).keyGen (kpke P).encrypt A)
            κ +
        (Game.advantage
          (ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F
            (encPRFReduction P A true) κ))
          (ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
            (encPRFReduction P A true) κ)) +
        Game.advantage
          (ProbComp.eval (prfRealGame (fun κ => nonceLen (P κ)) F
            (keyPRFReduction P F A true) κ))
          (ProbComp.eval (prfIdealGame (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ))
            (keyPRFReduction P F A true) κ))))) := by
  simp only [Encryption.advantage, eval_prfRealGame_keyPRFReduction,
    eval_prfIdealGame_keyPRFReduction, eval_prfRealGame_encPRFReduction,
    eval_prfIdealGame_encPRFReduction]
  rw [Game.advantage_comm (ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair (kpkePRF P F).keyGen
      (kpkePRF P F).encrypt A true κ)),
    Game.advantage_comm (ProbComp.eval (gameOn (kpkePRF P F).IsMessagePair (kpke P).keyGen
      (kpkePRF P F).encrypt A true κ))]
  refine (Game.advantage_triangle _ _ _).trans (add_le_add le_rfl ?_)
  refine (Game.advantage_triangle _ _ _).trans (add_le_add le_rfl ?_)
  refine (Game.advantage_triangle _ _ _).trans (add_le_add le_rfl ?_)
  exact Game.advantage_triangle _ _ _

/-- **IND-CPA of K-PKE with the matrix in the public key, from Module-LWE and a pseudorandom
function** (`XOF` and `G` not modeled as oracles), a step towards Kyber v3.02 Theorem 1
([AvanziEtAl2021], §4.3.1, p. 20) and not that theorem. The public key carries the sampled matrix
in place of the seed `ρ`, the seed `σ` is sampled directly, and the adversary has no `XOF` or `G`
oracle, where Theorem 1 assumes that both are random oracles. The remaining step to Theorem 1 is
the random-oracle lift: the scheme with `ρ` in the public key and `XOF` and `G` oracles, with a
lazily sampled, programmable simulator and its efficiency witness. It is open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765),
and depends on its §3 gap A, a reusable certificate for a lazily sampled, programmable random
oracle.

Let `P` be a K-PKE parameter family computable in polynomial time from the unary security
parameter, and `F` a keyed function. If decision Module-LWE is hard for the `k × k` key shape with
secrets and errors from `cbdLaw` of width `η₁` (`hkey`) and for the `(k + 1) × k` ciphertext shape
with secrets of width `η₁` and errors of width `η₂` (`hct`), and `F` is a pseudorandom function
with `κ`-bit keys, `nonceLen`-bit counter words as inputs and `prfLen`-bit outputs (`hF`), then
K-PKE with its noise expanded from seeds by `F` (`kpkePRF P F`) is IND-CPA secure
(`WordPKE.INDCPA`): every uniform strict PPT adversary has negligible advantage.

The other deviations from Theorem 1, named in the module documentation, are the asymptotic
setting with `κ`-bit seeds, counters of `(2k).size` bits, one PRF output length with prefixes, the
Module-LWE terms of §4.4, eq. (6), without compression in place of `2 · Adv^mlwe_{k+1,k,η}`, four
PRF advantages in place of one, and the representation of polynomials, keys and ciphertexts. -/
theorem indCPA_kpkePRF_of_decisionModuleLWEWith {P : ℕ → Params} [∀ κ, NeZero (P κ).q]
    {F : List Bool → List Bool → List Bool}
    (hP : ComputableInPolyTime P encUnary encParams)
    (hF : PseudorandomFunctionOver (fun κ => nonceLen (P κ)) (fun κ => prfLen (P κ)) F)
    (hkey : DecisionModuleLWEWith (fun κ => (P κ).k) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁)
      (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁))
    (hct : DecisionModuleLWEWith (fun κ => (P κ).k + 1) (fun κ => (P κ).k) (fun κ => (P κ).n)
      (fun κ => (P κ).q) (fun κ => cbdLaw (P κ).k (P κ).n (P κ).q (P κ).η₁)
      (fun κ => cbdLaw ((P κ).k + 1) (P κ).n (P κ).q (P κ).η₂)) :
    (kpkePRF P F).INDCPA := by
  intro A hA
  have hk₀ := hF.secure _ (isOraclePPT_keyPRFReduction hP hF.polyTime hA false)
  have hk₁ := hF.secure _ (isOraclePPT_keyPRFReduction hP hF.polyTime hA true)
  have he₀ := hF.secure _ (isOraclePPT_encPRFReduction hP hA false)
  have he₁ := hF.secure _ (isOraclePPT_encPRFReduction hP hA true)
  have hideal := indCPA_kpkeIdealCoins_of_decisionModuleLWEWith hP hkey hct A hA
  exact negligible_of_le (hk₀.add (he₀.add (hideal.add (he₁.add hk₁))))
    fun κ => advantage_gameOn_kpkePRF_le P F A κ

end Cslib.Crypto.MLKEM
