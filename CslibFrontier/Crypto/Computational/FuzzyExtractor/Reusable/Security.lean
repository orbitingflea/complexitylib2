/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract.Security
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
import CslibFrontier.Tactic.EncLen

/-!
# Weak reusability of the common-matrix fuzzy extractor

Apon, Cho, Eldefrawy and Katz ([AponChoEldefrawyKatz2017], Section 3.3, Theorem 1, p. 9) prove
that the Fuller–Meng–Reyzin fuzzy extractor stays secure under reuse when all enrollments share
one random matrix: "If the FMR scheme is an (M, ℓ, t, ϵ)-fuzzy extractor, and a common, random A
is used for all executions of Gen, then the scheme is also ϵ-weakly reusable." This module states
the weak-reusability experiment of `Reusable` against efficient adversaries at every security
parameter, and proves Theorem 1 in that form (`weaklyReusable_commonMatrixFuzzyExtractor`).

An adversary family is a `WordReuseAdversary`: at parameter `κ` its query stage is an oracle
program that reads the unary `κ` and a word describing the public parameter and challenge helper,
sends shift words and reads leakage words; its guessing stage reads `κ`, the saved state and the
key word. `WordReuseAdversary.IsPPT` asks for one uniform strict oracle PPT machine for the query
stage (`IsOraclePPT`) and one uniform strict PPT machine for the guess (`IsPPTOn`), as for the
library's other oracle adversaries. At modulus `2 ^ w`, a shift `δ : Fin m → ZMod (2 ^ w)` travels
as its binary word (`shiftCodec`); `WordReuseAdversary.toReuseAdversary` is the typed adversary
that a word adversary plays at one parameter. `WeaklyReusable` says that every admissible
adversary has negligible weak-reusability advantage on every source ensemble.

The reduction of Theorem 1 is the simulator of `Reusable`, `commonMatrixSimulator`, run at every
parameter: `LWEFamily.commonMatrixSimulator`, a distinguisher against the FMR family of
`DecodeThenExtract.Security`. `LWEFamily.isPPT_commonMatrixSimulator` proves it uniform strict
PPT from the adversary's certificate. Its word program samples the simulated secrets as `w`-bit
naturals and writes each simulated helper `c* + A s' + δ'` entry by entry; that program has the
law of the typed simulator.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.WordReuseAdversary`,
  `Cslib.Crypto.FuzzyExtractor.WordReuseAdversary.IsPPT`: reusability adversaries on bit words and
  their efficiency.
* `Cslib.Crypto.FuzzyExtractor.shiftCodec`,
  `Cslib.Crypto.FuzzyExtractor.WordReuseAdversary.toReuseAdversary`: binary shift words, and the
  typed adversary that a word adversary plays.
* `Cslib.Crypto.FuzzyExtractor.WeaklyReusable`: asymptotic weak reusability.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.encView`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.encVector`:
  the words the common-matrix adversary reads.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.commonMatrixSimulator`: the simulator at every parameter.

## Main results

* `Cslib.Crypto.FuzzyExtractor.LWEFamily.isPPT_commonMatrixSimulator`: the simulator is a uniform
  strict PPT FMR distinguisher when the adversary is uniform strict oracle PPT.
* `Cslib.Crypto.FuzzyExtractor.weaklyReusable_commonMatrixFuzzyExtractor`:
  [AponChoEldefrawyKatz2017] Theorem 1.

## Deviations

* The modulus is `2 ^ w κ`, the modulus of the FMR family of `DecodeThenExtract.Security`, and the
  key is `k κ` residues, not bits.
* Adversaries are uniform strict oracle PPT programs; Theorem 1 is stated for any adversary, and
  its computational form for "computationally bounded" ones (Section 2.1).
* A shift of Hamming weight above `t κ` is answered as the shift `0` (`clampShift`), where
  Definition 2 admits only shifts of weight at most `t`.
* Theorem 1 assumes that the FMR scheme "is an (M, ℓ, t, ϵ)-fuzzy extractor", which comprises
  correctness and security (Definition 1, p. 4), and Definition 2 defines weak reusability for a
  fuzzy extractor. The theorem here assumes and concludes only the security halves, since the
  weak-reusability experiment never runs reproduction (`Rec`). Correctness of the common-matrix
  scheme, averaged over the uniform matrix, is
  `DecoderCorrectWithError.setupCorrect_commonMatrixFuzzyExtractor`.

## References

* [D. Apon, C. Cho, K. Eldefrawy, and J. Katz, *Efficient, Reusable Fuzzy Extractors from
  LWE*][AponChoEldefrawyKatz2017], Definition 2 (p. 6) and Theorem 1 (p. 9).
-/

@[expose] public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

/-! ### Reusability adversaries on bit words -/

/-- A reusability adversary on bit words, at every security parameter. `query κ view` receives the
security parameter and the word of the public parameter and challenge helper, queries the shift
oracle with shift words and reads leakage words, and returns a saved state; `guess κ state key`
receives the saved state and the word of the challenge key. -/
structure WordReuseAdversary where
  /-- Read the view, query the shift oracle, and return a saved state. -/
  query : ℕ → List Bool → WordOracleComp Unit (List Bool)
  /-- Read the saved state and the key word, and return a bit. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- Uniform strict PPT admissibility of a word reusability adversary: one oracle machine for the
query stage, reading the unary parameter and the view, and one machine for the guess, reading the
unary parameter, the saved state and the key word. -/
structure WordReuseAdversary.IsPPT (A : WordReuseAdversary) : Prop where
  /-- The query stage is uniform strict oracle PPT. -/
  query : IsOraclePPT (Operation := Unit) encBits A.query
  /-- The guessing stage is uniform strict PPT. -/
  guess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    fun ⟨κ, state, key⟩ => A.guess κ state key

/-- Binary shift words at modulus `2 ^ w`: the shift `δ : Fin m → ZMod (2 ^ w)` is the request
carrying its word `LWEFamily.keyWord δ` of `m * w` bits, a request of any other length carries no
shift, and each leakage value is written with `encLeak`. -/
def shiftCodec (m w : ℕ) {Leak : Type} (encLeak : Leak ↪ List Bool) :
    OracleCodec Unit (Fin m → ZMod (2 ^ w)) fun _ => Leak where
  encodeQuery δ := ((), LWEFamily.keyWord δ)
  decodeQuery := fun ((), word) =>
    if word.length = m * w then some fun j => Cslib.Matrix.ofBinary 1 m w word 0 j else none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, word⟩ δ
    constructor
    · intro h
      dsimp only at h
      split_ifs at h with hlen
      cases h
      simp only [LWEFamily.keyWord, Prod.mk.injEq, true_and]
      have hrow :
          (_root_.Matrix.of fun _ : Fin 1 => fun j => Cslib.Matrix.ofBinary 1 m w word 0 j) =
          Cslib.Matrix.ofBinary 1 m w word := by
        ext i j
        rw [Subsingleton.elim i 0]
        rfl
      rw [hrow, Cslib.Matrix.toBinary_ofBinary (by rw [hlen, Nat.one_mul])]
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      subst h
      simp only [LWEFamily.keyWord, Cslib.Matrix.length_toBinary, Nat.one_mul, ↓reduceIte,
        Cslib.Matrix.ofBinary_toBinary, Option.some.injEq]
      rfl
  encodeReply _ := encLeak

/-- The typed reusability adversary that a word adversary plays at parameter `κ`: its query stage
reads the view word `encView (pp, p*)` and talks to the typed shift oracle through `shiftCodec`,
and its guess reads the key word `encKey r`. -/
def WordReuseAdversary.toReuseAdversary {PP Key Helper Leak : Type} (m w : ℕ)
    (encView : PP × Helper ↪ List Bool) (encLeak : Leak ↪ List Bool) (encKey : Key ↪ List Bool)
    (A : WordReuseAdversary) (κ : ℕ) : ReuseAdversary PP m (2 ^ w) Key Helper Leak (List Bool) where
  query pp p := (shiftCodec m w encLeak).adapt (A.query κ (encView (pp, p)))
  guess state key := A.guess κ state (encKey key)

/-- **Weak reusability** of a family of public-parameter fuzzy extractors at modulus `2 ^ w κ`
([AponChoEldefrawyKatz2017], Definition 2, in asymptotic form): for every source ensemble in
`sources`, every admissible word adversary has negligible weak-reusability advantage, played
through the view, helper and key encodings `encView`, `encHelper` and `encKey`, with shifts of
Hamming weight at most `t κ`. -/
def WeaklyReusable {PP Key Helper : ℕ → Type} [∀ κ, Fintype (Key κ)] [∀ κ, Nonempty (Key κ)]
    {m w : ℕ → ℕ} (setup : (κ : ℕ) → ProbComp (PP κ))
    (fe : (κ : ℕ) → PP κ → FuzzyExtractor (Fin (m κ) → ZMod (2 ^ w κ)) (Key κ) (Helper κ))
    (t : ℕ → ℕ) (sources : Set ((κ : ℕ) → PMF (Fin (m κ) → ZMod (2 ^ w κ))))
    (encView : (κ : ℕ) → PP κ × Helper κ ↪ List Bool) (encHelper : (κ : ℕ) → Helper κ ↪ List Bool)
    (encKey : (κ : ℕ) → Key κ ↪ List Bool) (Admissible : WordReuseAdversary → Prop) : Prop :=
  ∀ source ∈ sources, Game.Indistinguishable
    (fun A κ => weakReuseRealGame (setup κ) (fe κ) (source κ) (t κ)
      (A.toReuseAdversary (m κ) (w κ) (encView κ) (encHelper κ) (encKey κ) κ))
    (fun A κ => weakReuseIdealGame (setup κ) (fe κ) (source κ) (t κ)
      (A.toReuseAdversary (m κ) (w κ) (encView κ) (encHelper κ) (encKey κ) κ))
    Admissible

namespace LWEFamily

/-! ### The common-matrix adversary's words -/

/-- The word of a residue vector, `keyWord`, as an embedding. -/
def encVector (m w : ℕ) : (Fin m → ZMod (2 ^ w)) ↪ List Bool :=
  ⟨keyWord, fun u v h => by
    have h := congrArg (fun word => Cslib.Matrix.ofBinary 1 m w word 0) h
    simp only [keyWord, Cslib.Matrix.ofBinary_toBinary] at h
    exact h⟩

/-- The view of a common-matrix adversary: the public matrix `A` and the challenge helper `c*`,
as the word `helperWord ⟨A, c*, ()⟩` of the matrix `[c* | A]`, which an FMR distinguisher reads. -/
def encView (m n w : ℕ) :
    _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × (Fin m → ZMod (2 ^ w)) ↪ List Bool :=
  ⟨fun (A, c) => helperWord ⟨A, c, ()⟩, by
    rintro ⟨A, c⟩ ⟨A', c'⟩ h
    have h := congrArg (Cslib.Matrix.ofBinary m (n + 1) w) h
    simp only [helperWord, Cslib.Matrix.ofBinary_toBinary, LWE.augmentedMatrix_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl⟩

variable {m k l w : ℕ → ℕ}

/-- The simulator of [AponChoEldefrawyKatz2017], Theorem 1, at every security parameter: an FMR
distinguisher that runs the word adversary `A` through `commonMatrixSimulator`. -/
noncomputable def commonMatrixSimulator (t : ℕ → ℕ) (A : WordReuseAdversary) :
    Distinguisher m k l w := fun κ =>
  FuzzyExtractor.commonMatrixSimulator (t κ)
    (A.toReuseAdversary (m κ) (w κ) (encView (m κ) (k κ + l κ) (w κ)) (encVector (m κ) (w κ))
      (encVector (k κ) (w κ)) κ)

/-! ### The simulator's word program -/

/-- Whether a shift word has at most `t` nonzero residues among its first `m`. -/
private def lightShift (m w t : ℕ) (request : List Bool) : Bool :=
  decide (((List.range m).countP fun i =>
    decide (Cslib.Matrix.binaryEntry m w request 0 i ≠ 0)) ≤ t)

/-- The simulated helper word: entry `i` is `c i + ∑ⱼ A i j * s' j + δ' i` in `w` bits, where `A`
and `c` are read from the helper word, `s'` from the coins, and `δ'` from the request if
`lightShift` holds and is `0` otherwise. -/
private def replyWordOf (m n w t : ℕ) (helper : List Bool) (coins : List ℕ)
    (request : List Bool) : List Bool :=
  (List.range m).flatMap fun i =>
    BitString.lowBits w (Cslib.Matrix.binaryEntry (n + 1) w helper i 0 +
      ((List.range n).map fun j =>
        Cslib.Matrix.binaryEntry (n + 1) w helper i (j + 1) * coins.getD j 0).sum +
      if lightShift m w t request then Cslib.Matrix.binaryEntry m w request 0 i else 0)

/-- The simulator's word oracle on helper word `helper`: a request of `m * w` bits is answered with
`replyWordOf` on fresh `w`-bit coins, any other request with `[]`. -/
private noncomputable def simHandler (m n w t : ℕ) (helper : List Bool)
    (request : Unit × List Bool) : ProbComp (List Bool) :=
  if request.2.length = m * w then do
    let coins ← OracleComp.replicate n (ProbComp.sampleBinaryNat w)
    return replyWordOf m n w t helper coins request.2
  else pure []

/-- The simulator's word program. -/
private noncomputable def simulatorWords (t : ℕ → ℕ) (A : WordReuseAdversary)
    (x : Input m k l w) : Experiment := do
  let state ← (A.query x.secParam (helperWord x.helper)).run
    (simHandler (m x.secParam) (k x.secParam + l x.secParam) (w x.secParam) (t x.secParam)
      (helperWord x.helper))
  A.guess x.secParam state (keyWord x.key)

/-! ### The word program has the simulator's law -/

/-- `lightShift` decides the Hamming bound for the decoded shift. -/
private theorem lightShift_eq (m w t : ℕ) (request : List Bool) :
    lightShift m w t request =
      decide (hammingNorm (fun j : Fin m => Cslib.Matrix.ofBinary 1 m w request 0 j) ≤ t) := by
  have hcount : ((List.range m).countP fun i =>
      decide (Cslib.Matrix.binaryEntry m w request 0 i ≠ 0)) =
      hammingNorm (fun j : Fin m => Cslib.Matrix.ofBinary 1 m w request 0 j) := by
    have hzero (j : Fin m) : Cslib.Matrix.ofBinary 1 m w request 0 j ≠ 0 ↔
        decide (Cslib.Matrix.binaryEntry m w request 0 j.val ≠ 0) = true := by
      rw [Cslib.Matrix.ofBinary_apply, Fin.val_zero, decide_eq_true_iff, Ne, Ne,
        ZMod.natCast_eq_zero_iff]
      exact not_congr ⟨fun h => Nat.eq_zero_of_dvd_of_lt h
        (Cslib.Matrix.binaryEntry_lt m w request 0 j),
        fun h => by rw [h]; exact dvd_zero _⟩
    rw [List.countP_range_eq_card_filter, hammingNorm]
    simp only [hzero]
  rw [lightShift, hcount]

/-- The simulated helper word is the word of `c + A s' + clampShift t δ`, for the coins of `s'`
and the shift `δ` decoded from the request. -/
private theorem keyWord_reply {m n w : ℕ} (A : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (c : Fin m → ZMod (2 ^ w)) (t : ℕ) (x : Fin n → ZMod (2 ^ w)) (request : List Bool) :
    keyWord (c + A *ᵥ x + clampShift t fun j => Cslib.Matrix.ofBinary 1 m w request 0 j) =
      replyWordOf m n w t (helperWord ⟨A, c, ()⟩) (List.ofFn fun j => (x j).val) request := by
  have hc (i : Fin m) : (Cslib.Matrix.binaryEntry (n + 1) w
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix A c)) i.val 0 : ZMod (2 ^ w)) = c i := by
    simpa [LWE.augmentedMatrix] using
      Cslib.Matrix.binaryEntry_toBinary (LWE.augmentedMatrix A c) i 0
  have hA (i : Fin m) (j : Fin n) : (Cslib.Matrix.binaryEntry (n + 1) w
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix A c)) i.val (j.val + 1) : ZMod (2 ^ w)) =
        A i j := by
    simpa [LWE.augmentedMatrix] using
      Cslib.Matrix.binaryEntry_toBinary (LWE.augmentedMatrix A c) i j.succ
  have hδ (i : Fin m) : Cslib.Matrix.ofBinary 1 m w request 0 i =
      (Cslib.Matrix.binaryEntry m w request 0 i.val : ZMod (2 ^ w)) := by
    rw [Cslib.Matrix.ofBinary_apply, Fin.val_zero]
  change keyWord _ = replyWordOf m n w t (Cslib.Matrix.toBinary (LWE.augmentedMatrix A c)) _ request
  generalize Cslib.Matrix.toBinary (LWE.augmentedMatrix A c) = word at hc hA ⊢
  simp only [keyWord, replyWordOf, Cslib.Matrix.toBinary_eq, _root_.Matrix.of_apply,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_def, List.map_range_eq_ofFn, BitString.lowBits_eq_ofFn_val]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  funext b
  congr 2
  rw [lightShift_eq, clampShift]
  simp only [decide_eq_true_eq, Pi.add_apply, Nat.cast_add, Nat.cast_sum, List.sum_ofFn,
    Nat.cast_mul, hc, hA,
    List.getD_ofFn, ZMod.natCast_zmod_val, _root_.Matrix.mulVec, dotProduct]
  split_ifs <;> simp [hδ]

/-- Each request has the same reply law from the simulator's word oracle as from the typed
simulator's oracle, presented through `shiftCodec`. -/
private theorem eval_simHandler {m n w : ℕ} (A : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (c : Fin m → ZMod (2 ^ w)) (t : ℕ) (request : Unit × List Bool) :
    ProbComp.eval (simHandler m n w t (helperWord ⟨A, c, ()⟩) request) =
      ProbComp.eval ((shiftCodec m w (encVector m w)).wordOracle (fun δ => do
        let s' ← ProbComp.uniform (Fin n → ZMod (2 ^ w))
        return c + A *ᵥ s' + clampShift t δ) request) := by
  obtain ⟨⟨⟩, word⟩ := request
  by_cases hlen : word.length = m * w
  · simp only [simHandler, OracleCodec.wordOracle, shiftCodec, hlen, ↓reduceIte,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
      ProbComp.eval_replicate_sampleBinaryNat, ProbComp.eval_uniform, PMF.bind_map,
      PMF.map_bind, Function.comp_def, PMF.pure_map]
    congr 1 with x : 1
    rw [← keyWord_reply]
    rfl
  · simp [simHandler, OracleCodec.wordOracle, shiftCodec, hlen]

/-- The word program has the law of the simulator. -/
private theorem eval_simulatorWords (t : ℕ → ℕ) (A : WordReuseAdversary) (x : Input m k l w) :
    ProbComp.eval (simulatorWords t A x) =
      ProbComp.eval (commonMatrixSimulator t A x.secParam x.key x.helper) := by
  obtain ⟨κ, key, ⟨M, c, ⟨⟩⟩⟩ := x
  simp only [simulatorWords, commonMatrixSimulator, FuzzyExtractor.commonMatrixSimulator,
    WordReuseAdversary.toReuseAdversary, OracleCodec.run_adapt, ProbComp.eval_bind,
    ProbOracleComp.eval_run]
  have hhandler : (fun request => ProbComp.eval (simHandler (m κ) (k κ + l κ) (w κ) (t κ)
      (helperWord ⟨M, c, ()⟩) request)) = fun request =>
      ProbComp.eval ((shiftCodec (m κ) (w κ) (encVector (m κ) (w κ))).wordOracle (fun δ => do
        let s' ← ProbComp.uniform (Fin (k κ + l κ) → ZMod (2 ^ w κ))
        return c + M *ᵥ s' + clampShift (t κ) δ) request) :=
    funext fun request => eval_simHandler M c (t κ) request
  rw [hhandler]
  rfl

/-! ### Polynomial-time computation of the simulated helper word -/

section PolyTime

open ComputableInPolyTime

/-- `replyWordOf` is computed in polynomial time from polynomial-time inputs. -/
private theorem computableInPolyTime_replyWordOf {α : Type} {input : α ↪ List Bool}
    {m n w t : α → ℕ} {helper request : α → List Bool} {coins : α → List ℕ}
    (hm : ComputableInPolyTime m input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary) (ht : ComputableInPolyTime t input encUnary)
    (hhelper : ComputableInPolyTime helper input encBits)
    (hcoins : ComputableInPolyTime coins input (encList encNat))
    (hrequest : ComputableInPolyTime request input encBits) :
    ComputableInPolyTime
      (fun a => replyWordOf (m a) (n a) (w a) (t a) (helper a) (coins a) (request a))
      input encBits := by
  have hlight : ComputableInPolyTime (fun a => lightShift (m a) (w a) (t a) (request a))
      input encBool := by
    unfold lightShift
    refine unary_le' (countPWithInput (range.comp hm) ?_) ht
    exact decide_ne (matrixBinaryEntry (hm.comp (fst input encUnary))
      (hw.comp (fst input encUnary)) (hrequest.comp (fst input encUnary)) (const 0)
      (snd input encUnary)) (const 0)
  unfold replyWordOf
  apply flatMapToBitsWithInput (range.comp hm)
  apply bitsLow (hw.comp (fst input encUnary))
  have hcols : ComputableInPolyTime (fun p : α × ℕ => n p.1 + 1) (encPair input encUnary)
      encUnary := by fun_prop
  refine binary_add' (binary_add' ?_ ?_) ?_
  · exact matrixBinaryEntry hcols (hw.comp (fst input encUnary))
      (hhelper.comp (fst input encUnary)) (snd input encUnary) (const 0)
  · have hterm : ComputableInPolyTime
        (fun q : (α × ℕ) × ℕ => Cslib.Matrix.binaryEntry (n q.1.1 + 1) (w q.1.1) (helper q.1.1)
          q.1.2 (q.2 + 1) * (coins q.1.1).getD q.2 0)
        (encPair (encPair input encUnary) encUnary) encNat :=
      binary_mul' (matrixBinaryEntry (hcols.comp (fst _ encUnary))
          (hw.comp ((fst input encUnary).comp (fst _ encUnary)))
          (hhelper.comp ((fst input encUnary).comp (fst _ encUnary)))
          ((snd input encUnary).comp (fst _ encUnary)) (by fun_prop))
        ((listGetD (encA := encNat) 0).comp
          ((hcoins.comp ((fst input encUnary).comp (fst _ encUnary))).prod (snd _ encUnary)))
    exact (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
      (mapWithInput (range.comp (hn.comp (fst input encUnary))) hterm)
  · exact ite' (hlight.comp (fst input encUnary))
      (matrixBinaryEntry (hm.comp (fst input encUnary)) (hw.comp (fst input encUnary))
        (hrequest.comp (fst input encUnary)) (const 0) (snd input encUnary))
      (const 0)

end PolyTime

/-! ### The certificate -/

/-- The security parameter and helper word of a distinguisher input are computable in polynomial
time from its encoding. -/
private theorem computableInPolyTime_view :
    ComputableInPolyTime (fun x : Input m k l w => (x.secParam, helperWord x.helper))
      (encInput m k l w) (encPair encUnary encBits) :=
  ((ComputableInPolyTime.fst encUnary (encPair encBits encBits)).prod
    ((ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd')).comp
    (ComputableInPolyTime.of_eq (f := Input.words) fun _ => rfl)

/-- The key word of a distinguisher input is computable in polynomial time from its encoding. -/
private theorem computableInPolyTime_keyWord :
    ComputableInPolyTime (fun x : Input m k l w => keyWord x.key) (encInput m k l w) encBits :=
  (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst'.comp
    (ComputableInPolyTime.of_eq (f := Input.words) fun _ => rfl)

/-- Every reply of the simulator's word oracle has at most `m * w` bits. -/
private theorem length_le_of_mem_support_simHandler {m n w t : ℕ} {helper : List Bool}
    {request : Unit × List Bool} {reply : List Bool}
    (h : reply ∈ (ProbComp.eval (simHandler m n w t helper request)).support) :
    reply.length ≤ m * w := by
  unfold simHandler at h
  split_ifs at h
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.support_bind, PMF.support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨coins, _, rfl⟩ := h
    simp [replyWordOf, List.length_flatMap, BitString.length_lowBits]
  · simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at h
    simp [h]

/-- **`commonMatrixSimulator` is PPT.** When `m, k, l, w, t` are computable in polynomial time in
unary, the simulator of a uniform strict oracle PPT word adversary is a uniform strict PPT FMR
distinguisher. -/
theorem isPPT_commonMatrixSimulator (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary)
    {A : WordReuseAdversary} (hA : A.IsPPT) :
    (commonMatrixSimulator (m := m) (k := k) (l := l) (w := w) t A).IsPPT := by
  let input := encInput m k l w
  let Call := Input m k l w × (Unit × List Bool) × Unit
  let encCall : Call ↪ List Bool := encHandlerCall input (encFinEnum Unit) (encFinEnum Unit)
  have hκ : ComputableInPolyTime (fun x : Input m k l w => x.secParam) input encUnary :=
    (ComputableInPolyTime.fst encUnary encBits).comp computableInPolyTime_view
  have hhelper : ComputableInPolyTime (fun x : Input m k l w => helperWord x.helper) input
      encBits :=
    (ComputableInPolyTime.snd encUnary encBits).comp computableInPolyTime_view
  have hκc : ComputableInPolyTime (fun call : Call => call.1.secParam) encCall encUnary :=
    hκ.comp (ComputableInPolyTime.fst _ _)
  have hrequest : ComputableInPolyTime (fun call : Call => call.2.1.2) encCall encBits :=
    (ComputableInPolyTime.snd _ _).fst'.snd'
  -- The simulator's word oracle is PPT.
  have hreply := computableInPolyTime_replyWordOf
    (input := encPair encCall (encList encNat))
    (m := fun q => m q.1.1.secParam) (n := fun q => k q.1.1.secParam + l q.1.1.secParam)
    (w := fun q => w q.1.1.secParam) (t := fun q => t q.1.1.secParam)
    (helper := fun q => helperWord q.1.1.helper) (coins := fun q => q.2)
    (request := fun q => q.1.2.1.2)
    (hm.comp (hκc.comp (ComputableInPolyTime.fst _ _)))
    ((ComputableInPolyTime.unary_add.comp ((hk.comp (hκc.comp (ComputableInPolyTime.fst _ _))).prod
      (hl.comp (hκc.comp (ComputableInPolyTime.fst _ _))))))
    (hw.comp (hκc.comp (ComputableInPolyTime.fst _ _)))
    (ht.comp (hκc.comp (ComputableInPolyTime.fst _ _)))
    ((hhelper.comp (ComputableInPolyTime.fst _ _)).comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.snd _ _)
    (hrequest.comp (ComputableInPolyTime.fst _ _))
  have hsim : IsPPTOn encCall encBits (fun call : Call => simHandler (m call.1.secParam)
      (k call.1.secParam + l call.1.secParam) (w call.1.secParam) (t call.1.secParam)
      (helperWord call.1.helper) call.2.1) := by
    have hlen : ComputableInPolyTime (fun call : Call => call.2.1.2.length) encCall encUnary := by
      fun_prop
    have hwc : ComputableInPolyTime (fun call : Call => w call.1.secParam) encCall encUnary :=
      hw.comp hκc
    have hnc : ComputableInPolyTime (fun call : Call => k call.1.secParam + l call.1.secParam)
        encCall encUnary :=
      ComputableInPolyTime.unary_add.comp ((hk.comp hκc).prod (hl.comp hκc))
    have hcoins : IsPPTOn encCall (encList encNat) (fun call : Call =>
        OracleComp.replicate (k call.1.secParam + l call.1.secParam)
          (ProbComp.sampleBinaryNat (w call.1.secParam))) :=
      hwc.sampleBinaryNat.replicate hnc
    have hyes : IsPPTOn encCall encBits (fun call : Call => do
        let coins ← OracleComp.replicate (k call.1.secParam + l call.1.secParam)
          (ProbComp.sampleBinaryNat (w call.1.secParam))
        return replyWordOf (m call.1.secParam) (k call.1.secParam + l call.1.secParam)
          (w call.1.secParam) (t call.1.secParam) (helperWord call.1.helper) coins call.2.1.2) :=
      hcoins.bind_with hreply.isPPTOn
    have hcond : ComputableInPolyTime
        (fun call : Call => decide (call.2.1.2.length = m call.1.secParam * w call.1.secParam))
        encCall encBool :=
      ComputableInPolyTime.unary_eq' hlen (ComputableInPolyTime.unary_mul' (hm.comp hκc) hwc)
    exact IsPPTOn.ite' hcond hyes (ComputableInPolyTime.const []).isPPTOn
  have hhandler : IsPPTOn encCall (encPair encBits (encFinEnum Unit))
      (fun ⟨x, request, state⟩ => (StateT.lift (simHandler (m x.secParam)
        (k x.secParam + l x.secParam) (w x.secParam) (t x.secParam) (helperWord x.helper)
        request) : StateT Unit ProbComp (List Bool)) state) := by
    refine (hsim.map_pair (second := fun p => (p.2, ()))
      (ComputableInPolyTime.prod (g := fun _ => ()) (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.const ()))).congr fun call => ?_
    obtain ⟨x, request, ⟨⟩⟩ := call
    rfl
  have hresources : ComputableInPolyTime
      (fun pair : Input m k l w × List Bool => m pair.1.secParam * w pair.1.secParam)
      (encPair input encBits) encUnary :=
    ComputableInPolyTime.unary_mul' (hm.comp (hκ.comp (ComputableInPolyTime.fst _ _)))
      (hw.comp (hκ.comp (ComputableInPolyTime.fst _ _)))
  have hrun := hA.query.isPPTOn_runState (input := input) (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (oracle := fun x request => StateT.lift (simHandler (m x.secParam)
        (k x.secParam + l x.secParam) (w x.secParam) (t x.secParam) (helperWord x.helper)
        request))
    (initial := fun _ => ()) (resources := fun x _ => m x.secParam * w x.secParam)
    computableInPolyTime_view hhandler (ComputableInPolyTime.const ()) (fun _ _ => True)
    (fun _ => trivial) hresources fun x request state _ result hresult => by
      simp only [StateT.lift, ProbComp.eval_bind, ProbComp.eval_pure, PMF.support_bind,
        PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hresult
      obtain ⟨reply, hreply, rfl⟩ := hresult
      exact ⟨trivial, length_le_of_mem_support_simHandler hreply, Nat.le_add_right _ _⟩
  have hguess : IsPPTOn (encPair input (encPair encBits (encFinEnum Unit))) encBool
      (fun p => A.guess p.1.secParam p.2.1 (keyWord p.1.key)) :=
    hA.guess.preprocess ((hκ.comp (ComputableInPolyTime.fst _ _)).prod
      ((ComputableInPolyTime.snd _ _).fst'.prod
        (computableInPolyTime_keyWord.comp (ComputableInPolyTime.fst _ _))))
  refine (hrun.bind_with (second := fun x out => A.guess x.secParam out.1 (keyWord x.key))
    hguess).congr fun x => ?_
  rw [← eval_simulatorWords]
  simp only [simulatorWords, ProbOracleComp.runState_lift, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_map, Function.comp_def]

end LWEFamily

/-! ### Asymptotic weak reusability -/

/-- **Weak reusability of the common-matrix fuzzy extractor** ([AponChoEldefrawyKatz2017],
Theorem 1, p. 9). Let `m, k, l, w, t` be computable in polynomial time in unary, and suppose the
Fuller–Meng–Reyzin family `κ ↦ lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ)` is
`ComputationallySecure` for `sources` against uniform strict PPT distinguishers. Then the
common-matrix family `κ ↦ commonMatrixFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ)`,
whose public parameter is a uniform matrix, is `WeaklyReusable` for `sources` against uniform
strict oracle PPT word adversaries, with shifts of Hamming weight at most `t κ`.

The hypothesis is the one Theorem 1 states, security of the FMR scheme; no LWE assumption is used
here. The proof is the exact identity `weakReuseAdvantage_commonMatrixFuzzyExtractor_eq` with the
simulator, which is PPT by `LWEFamily.isPPT_commonMatrixSimulator`. The deviations from the source
are listed in the module documentation. -/
theorem weaklyReusable_commonMatrixFuzzyExtractor {m k l w : ℕ → ℕ}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary)
    (decode : (κ : ℕ) → _root_.Matrix (Fin (m κ)) (Fin (k κ + l κ)) (ZMod (2 ^ w κ)) →
      (Fin (m κ) → ZMod (2 ^ w κ)) → ProbComp (Option (Fin (k κ + l κ) → ZMod (2 ^ w κ))))
    {sources : Set ((κ : ℕ) → PMF (Fin (m κ) → ZMod (2 ^ w κ)))}
    (hFMR : ComputationallySecure
      (fun κ => lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ)) sources
      LWEFamily.Distinguisher.IsPPT) :
    WeaklyReusable (fun κ => ProbComp.uniform
        (_root_.Matrix (Fin (m κ)) (Fin (k κ + l κ)) (ZMod (2 ^ w κ))))
      (fun κ => commonMatrixFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ)) t sources
      (fun κ => LWEFamily.encView (m κ) (k κ + l κ) (w κ))
      (fun κ => LWEFamily.encVector (m κ) (w κ)) (fun κ => LWEFamily.encVector (k κ) (w κ))
      WordReuseAdversary.IsPPT := by
  intro source hsource A hA
  have h := hFMR source hsource _ (LWEFamily.isPPT_commonMatrixSimulator hm hk hl hw ht hA)
  refine negligible_of_le h fun κ => le_of_eq ?_
  exact weakReuseAdvantage_commonMatrixFuzzyExtractor_eq (decode κ) (source κ) (t κ) _


end Cslib.Crypto.FuzzyExtractor
