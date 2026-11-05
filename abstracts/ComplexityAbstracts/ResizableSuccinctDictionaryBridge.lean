/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.HashFamiliesBridge
import Complexity.DataStructure.DynamicArray.ResizableWordCode
import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinct
import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinctEpoch

/-!
# Bridge for the Word-Granular Resizable Word-RAM, Dynamic Array, and Succinct Dictionary Abstract

Connects `ResizableSuccinctDictionaryAbstract.lean` to the library proofs in
`Cslib.WordRAM.Resizable`, `Cslib.DataStructure.DynamicArray.ResizableWord`, and
`Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct`.
-/

namespace ComplexityAbstracts.ResizableSuccinctDictionaryBridge

open scoped ENNReal BigOperators
open Finset
open Cslib
open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.DynamicArray
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.Probability
open ComplexityAbstracts.HashFamiliesBridge (trinomialStepLoop trinomialStepLoop_eq)

/-! ## Part 1: Resizable Word-RAM Demonic-Grow Equivalence & Stage 1 Packed Array Bounds -/

/-- Zeroing `[s, s + delta)` after any demonic `.grow delta` transition from a memory `mem` that is
zero at `[s, ∞)` recovers `mem` identically and establishes `[s + delta, ∞) = 0`. -/
theorem bridge_demonicGrow_zeroSlice_eq {w s delta : ℕ} {mem mem' : ℕ → ℕ}
    (hzero : ∀ a, s ≤ a → mem a = 0)
    (hdemonic : (∀ a < s, mem' a = mem a) ∧
      (∀ a, s ≤ a → a < s + delta → mem' a < 2 ^ w) ∧
      (∀ a, s + delta ≤ a → mem' a = mem a)) :
    (fun a => if s ≤ a ∧ a < s + delta then 0 else mem' a) = mem ∧
    ∀ a, s + delta ≤ a → (if s ≤ a ∧ a < s + delta then 0 else mem' a) = 0 := by
  have hclear : (fun a => if s ≤ a ∧ a < s + delta then 0 else mem' a) = mem := by
    funext a
    split_ifs with h
    · exact (hzero a h.1).symm
    · by_cases hlt : a < s
      · exact hdemonic.1 a hlt
      · exact hdemonic.2.2 a (by omega)
  refine ⟨hclear, fun a ha => ?_⟩
  exact (congrFun hclear a).trans (hzero a (by omega))

/-- Stage 1 tight stepwise bit-space bound for a resizable array of `n_t` `b`-bit items in `w`-bit
words (`1 + ⌈n_t * b / w⌉` words, `< n_t * b + 2 * w` bits). -/
theorem bridge_resizableArray_space_tight {w b : ℕ} (hw : 0 < w) (_hb : 0 < b) (_hbw : b ≤ w)
    (n_t : ℕ) :
    let s_t := 1 + (n_t * b + w - 1) / w
    n_t * b ≤ s_t * w ∧ s_t * w < n_t * b + 2 * w := by
  have h1 := Cslib.BitString.mul_le_packedWords_mul (b := b) (n := n_t) hw
  have h2 := Cslib.BitString.packedWords_mul_le (w := w) (b := b) (n := n_t)
  unfold Cslib.BitString.packedWords at h1 h2
  dsimp only
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ## Part 2: Exact Correspondence of Succinct Space & Epoch Parameters -/

/-- `trinomialStepLoop B B` agrees with `Cslib.Probability.trinomialStepAux B`. -/
theorem reducedTrinomialStep_eq (w₀ b b' : ℕ) :
    let B := max (min w₀ (3 * b)) (max b' 1)
    trinomialStepLoop B B = Cslib.Probability.reducedTrinomialStep w₀ b b' := by
  intro B
  exact trinomialStepLoop_eq B B le_rfl

/-- Abstract formula for `hashSpace U w N` using `trinomialStepLoop`. -/
def absHashSpace (U w N : ℕ) : ℕ :=
  let w₀ := max (Nat.clog 2 U - (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4)))) 1
  let b' := (Nat.log 2 N - 3 * Nat.clog 2 (Nat.clog 2 (max N 4))) +
    min (Nat.log 2 N) (3 * Nat.clog 2 (Nat.clog 2 (max N 4)))
  let b := b' + 1
  let B := max (min w₀ (3 * b)) (max b' 1)
  let t := trinomialStepLoop B B
  let c := 3 ^ (t - 3)
  let L := 2 * 3 ^ min t 3
  let p := min (2 * c) (Nat.log 2 (w / (2 * c)))
  (1 + 3 * L) + 2 ^ (2 * c - p)

theorem absHashSpace_eq (U w N : ℕ) : absHashSpace U w N = hashSpace U w N := by
  unfold absHashSpace hashSpace ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedLimbCount reducedHalfLimbs reducedTableWords reducedPackShift reducedChunkBits
    qBits hashB totalMicroBits quotientBits keyBits bucketBits microBits Dynamic.logLogFactor
  dsimp only
  rw [reducedTrinomialStep_eq]

/-- Abstract formula for `metaWords U w N`. -/
def absMetaWords (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let m_bits := min (Nat.log 2 N) (3 * ll)
  let tot_micro := 2 ^ (b_bits + m_bits)
  let eff_cap := 4 * 2 ^ m_bits
  let eff_pos_bits := Nat.clog 2 (min N eff_cap + 1)
  let scale := 2 ^ ll
  let slab_bits := if b_bits = 0 then 0 else 2 * ll
  let slab_sz := 2 ^ slab_bits
  let dir_slabs := if b_bits = 0 then 0 else 4 * scale
  let tail_cap := if b_bits = 0 then 0 else 2 * slab_sz
  let max_slabs := if b_bits = 0 then 0 else N / slab_sz
  let gm_var := if b_bits = 0 then 0
    else 2 ^ b_bits * (3 + dir_slabs + 2 * tail_cap) + 4 * max_slabs
  let gm_len := 4 + gm_var
  let gm_bits := Nat.clog 2 (N + 1)
  absHashSpace U w N +
    ((gm_len * gm_bits + w - 1) / w + 2) +
    9 * ((tot_micro * eff_pos_bits + w - 1) / w + 2)

theorem absMetaWords_eq (U w N : ℕ) : absMetaWords U w N = metaWords U w N := by
  unfold absMetaWords metaWords packedWords globalMetaLen globalMetaVarLen dirSlabsPerBucket
    tailCapPerBucket maxFullSlabs slabSize slabBits slabScale numBuckets globalPtrBits
    totalMicroBuckets totalMicroBits effBucketPosBits effBucketCap numMicroPerBucket
    microBits bucketBits Dynamic.logLogFactor
  dsimp only
  rw [absHashSpace_eq]

/-- Abstract formula for `itemWords U V w N n`. -/
def absItemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let q_bits := Nat.clog 2 U - b_bits
  let v_bits := Nat.clog 2 V
  ((n * q_bits + w - 1) / w + 2) + ((n * v_bits + w - 1) / w + 2)

theorem absItemWords_eq (U V w N n : ℕ) : absItemWords U V w N n = itemWords U V w N n := rfl

/-- Abstract formula for `activeEpochWords U V w N n`. -/
def absActiveEpochWords (U V w N n : ℕ) : ℕ :=
  absMetaWords U w N + absItemWords U V w N n

theorem absActiveEpochWords_eq (U V w N n : ℕ) :
    absActiveEpochWords U V w N n = activeEpochWords U V w N n := by
  unfold absActiveEpochWords activeEpochWords
  rw [absMetaWords_eq, absItemWords_eq]

/-- Abstract formula for `Succinct.space U V w N = absActiveEpochWords U V w N N`. -/
def absEpochSpace (U V w N : ℕ) : ℕ :=
  absActiveEpochWords U V w N N

theorem absEpochSpace_eq (U V w N : ℕ) :
    absEpochSpace U V w N = Succinct.space U V w N := by
  unfold absEpochSpace
  rw [absActiveEpochWords_eq, activeEpochWords_eq_space]

/-- Abstract formula for `offCompItems U w N`. -/
def absOffCompItems (U w N : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let slab_bits := if b_bits = 0 then 0 else 2 * ll
  let slab_sz := 2 ^ slab_bits
  let tail_cap := if b_bits = 0 then 0 else 2 * slab_sz
  let max_tail := 2 ^ b_bits * tail_cap
  let gm_bits := Nat.clog 2 (N + 1)
  let tail_words := (max_tail * gm_bits + w - 1) / w + 2
  164 + absMetaWords U w N + tail_words + tail_words

theorem absOffCompItems_eq (U w N : ℕ) :
    absOffCompItems U w N = offCompItems U w N := by
  unfold absOffCompItems
  rw [absMetaWords_eq]
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM
    epochHdrWords metaWords lmSubWords packedWords maxTailItems numBuckets tailCapPerBucket
    slabSize slabBits globalPtrBits bucketBits Dynamic.logLogFactor
  dsimp only
  omega

/-- Abstract formula for `compactedItemWords U V w N n`. -/
def absCompactedItemWords (U V w N n : ℕ) : ℕ :=
  let ll := Nat.clog 2 (Nat.clog 2 (max N 4))
  let b_bits := Nat.log 2 N - 3 * ll
  let q_bits := Nat.clog 2 U - b_bits
  let v_bits := Nat.clog 2 V
  (n * (q_bits + v_bits) + w - 1) / w + 2

theorem absCompactedItemWords_eq (U V w N n : ℕ) :
    absCompactedItemWords U V w N n = compactedItemWords U V w N n := rfl

/-- Abstract formula for `compactedEpochWords U V w N n`. -/
def absCompactedEpochWords (U V w N n : ℕ) : ℕ :=
  if n = 0 then 4 else absOffCompItems U w N + absCompactedItemWords U V w N n

theorem absCompactedEpochWords_eq (U V w N n : ℕ) :
    absCompactedEpochWords U V w N n = compactedEpochWords U V w N n := by
  unfold absCompactedEpochWords compactedEpochWords
  rw [absOffCompItems_eq, absCompactedItemWords_eq]

/-- Abstract formula for `epochPeakWords U V w N`. -/
def absEpochPeakWords (U V w N : ℕ) : ℕ :=
  max (absEpochSpace U V w N) (absCompactedEpochWords U V w N N)

theorem absEpochPeakWords_eq (U V w N : ℕ) :
    absEpochPeakWords U V w N = epochPeakWords U V w N := by
  unfold absEpochPeakWords epochPeakWords
  rw [absEpochSpace_eq, absCompactedEpochWords_eq]

/-- Stepwise `n_t`-tight compacted space bound in words and bits for `n ≤ N ≤ 4 * n`. -/
theorem bridge_compactedEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    absCompactedEpochWords U V w N n ≤
      ((Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        1355 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + w - 1) / w + 380 ∧
    w * absCompactedEpochWords U V w N n ≤
      (Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        1355 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + 381 * w := by
  rw [absCompactedEpochWords_eq]
  have hnU : n ≤ U := hnN.trans hNU
  exact ⟨compactedEpochWords_le_succinctWords hw hnU hNU hU hnN hN4,
    w_mul_compactedEpochWords_le_bits hw hnU hNU hU hnN hN4⟩

/-- Conversion from `succinctWords` to bit space, showing the `(C₀ + 1) * w` additive term. -/
theorem bridge_succinctWords_mul_w_le_bits (C₁ C₀ U V w n : ℕ) :
    w * (((Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
      C₁ * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + w - 1) / w + C₀) ≤
      (Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        C₁ * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + (C₀ + 1) * w :=
  succinctWords_mul_w_le_bits C₁ C₀ U V w n

/-- Stepwise `n_t`-tight space bound for `n ≤ N ≤ 2 * n`. -/
theorem bridge_activeEpochWords_le_two_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN2 : N ≤ 2 * n) :
    absActiveEpochWords U V w N n ≤
      ((Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        312 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + w - 1) / w + 213 := by
  rw [absActiveEpochWords_eq]
  exact activeEpochWords_le_succinctWords_of_le_two_mul hw hnU hNU hU hnN hN2

/-- Stepwise `n_t`-tight space bound in words and bits for `n ≤ N ≤ 4 * n` (`EpochValid n N`). -/
theorem bridge_activeEpochWords_le_four_mul {U V w N n : ℕ}
    (hw : 0 < w) (hnU : n ≤ U) (hNU : N ≤ U) (hU : U ≤ 2 ^ w)
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    absActiveEpochWords U V w N n ≤
      ((Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        1227 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + w - 1) / w + 213 ∧
    w * absActiveEpochWords U V w N n ≤
      (Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
        1227 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + 214 * w := by
  rw [absActiveEpochWords_eq]
  have hw_le := activeEpochWords_le_succinctWords_of_le_four_mul (V := V) hw hnU hNU hU hnN hN4
  refine ⟨hw_le, ?_⟩
  have hbits :
      w * activeEpochWords U V w N n ≤
        Dynamic.optBits U V n + 1227 * n * Dynamic.logLogFactor n + 214 * w := by
    calc w * activeEpochWords U V w N n
        ≤ w * Dynamic.succinctWords 1227 213 U V w n := Nat.mul_le_mul_left w hw_le
      _ ≤ Dynamic.optBits U V n + 1227 * n * Dynamic.logLogFactor n + (213 + 1) * w :=
          succinctWords_mul_w_le_bits 1227 213 U V w n
      _ = Dynamic.optBits U V n + 1227 * n * Dynamic.logLogFactor n + 214 * w := by ring
  exact hbits

/-! ## Part 3: Polymorphic Presentation of Dynamic Dictionary Operations and Resizable RAM State -/

/-- Polymorphic signature of the self-contained dynamic dictionary operations (`insert`, `delete`,
`query`) and word-granular resizable Word-RAM state in
`ResizableSuccinctDictionaryAbstract.lean`. -/
structure DynamicDictPresentation where
  DynamicOp : ℕ → Type
  insert {U : ℕ} : Fin U → ℕ → DynamicOp U
  delete {U : ℕ} : Fin U → DynamicOp U
  query {U : ℕ} : Fin U → DynamicOp U
  dynamicOp_induction {U : ℕ} {motive : DynamicOp U → Prop} :
    (∀ u v, motive (insert u v)) → (∀ u, motive (delete u)) → (∀ u, motive (query u)) →
    ∀ o, motive o
  stepDict {U : ℕ} : (Fin U → Option ℕ) → DynamicOp U → (Fin U → Option ℕ)
  runDict {U : ℕ} : (Fin U → Option ℕ) → List (DynamicOp U) → (Fin U → Option ℕ)
  ValidDictOp {U : ℕ} : ℕ → (Fin U → Option ℕ) → DynamicOp U → Prop
  ValidDictSeq {U : ℕ} : ℕ → (Fin U → Option ℕ) → List (DynamicOp U) → Prop
  runEpochInit {U : ℕ} : ℕ → (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  maxEpochCap {U : ℕ} : ℕ → (Fin U → Option ℕ) → ℕ → List (DynamicOp U) → ℕ
  SeqOutputCorrect {r U : ℕ} :
    256 ≤ r → ℕ → (Fin U → Option ℕ) → List (DynamicOp U) → (Fin r → ℕ) → Prop
  activeEpochWords : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  compactedEpochWords : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  epochPeakWords : ℕ → ℕ → ℕ → ℕ → ℕ
  RState : ℕ → Type
  mkRState {r : ℕ} : (Fin r → ℕ) → (ℕ → ℕ) → ℕ → RState r
  rRegs {r : ℕ} : RState r → Fin r → ℕ
  rMem {r : ℕ} : RState r → ℕ → ℕ
  rFrontier {r : ℕ} : RState r → ℕ
  RBounded {r : ℕ} : ℕ → RState r → Prop

namespace DynamicDictPresentation

variable (P : DynamicDictPresentation)

/-- Empty dictionary `fun _ => none`. -/
def emptyDict (U : ℕ) : Fin U → Option ℕ :=
  fun _ => none

/-- Translate a library `Dynamic.Op U` to `P.DynamicOp U`. -/
def dynamicOpOf {U : ℕ} : Dynamic.Op U → P.DynamicOp U
  | .insert u v => P.insert u v
  | .delete u => P.delete u
  | .query u => P.query u

/-- Translate a library `RData r` state to `P.RState r`. -/
def rStateOf {r : ℕ} (x : RData r) : P.RState r :=
  P.mkRState x.regs x.mem x.frontier

/-- Translate `P.RState r` back to `RData r`. -/
def rDataOf {r : ℕ} (x : P.RState r) : RData r :=
  ⟨P.rRegs x, P.rMem x, P.rFrontier x⟩

end DynamicDictPresentation

/-- Equational specification for a `DynamicDictPresentation`. -/
structure DynamicDictLaws (P : DynamicDictPresentation) : Prop where
  stepDict_insert : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.stepDict s (P.insert u v) = Function.update s u (some v)
  stepDict_delete : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    P.stepDict s (P.delete u) = Function.update s u none
  stepDict_query : ∀ {U : ℕ} (s : Fin U → Option ℕ) (u : Fin U),
    P.stepDict s (P.query u) = s
  runDict_nil : ∀ {U : ℕ} (s : Fin U → Option ℕ),
    P.runDict s [] = s
  runDict_cons : ∀ {U : ℕ} (s : Fin U → Option ℕ) (o : P.DynamicOp U) (os : List (P.DynamicOp U)),
    P.runDict s (o :: os) = P.runDict (P.stepDict s o) os
  validDictOp_insert : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U) (v : ℕ),
    P.ValidDictOp V s (P.insert u v) ↔ v < V
  validDictOp_delete : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    P.ValidDictOp V s (P.delete u) ↔ True
  validDictOp_query : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (u : Fin U),
    P.ValidDictOp V s (P.query u) ↔ True
  validDictSeq_nil : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ),
    P.ValidDictSeq V s [] ↔ True
  validDictSeq_cons : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (o : P.DynamicOp U) (os : List (P.DynamicOp U)),
    P.ValidDictSeq V s (o :: os) ↔
      P.ValidDictOp V s o ∧ P.ValidDictSeq V (P.stepDict s o) os
  runEpochInit_nil : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (n_init : ℕ),
    P.runEpochInit V s n_init [] = n_init
  runEpochInit_cons : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (n_init : ℕ)
    (o : P.DynamicOp U) (os : List (P.DynamicOp U)),
    P.runEpochInit V s n_init (o :: os) =
      let s' := P.stepDict s o
      let n' := (Finset.univ.filter fun u => (s' u).isSome).card
      let N := min (2 * n_init) U
      let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
      P.runEpochInit V s' n_init' os
  maxEpochCap_nil : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (n_init : ℕ),
    P.maxEpochCap V s n_init [] = min (2 * n_init) U
  maxEpochCap_cons : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (n_init : ℕ)
    (o : P.DynamicOp U) (os : List (P.DynamicOp U)),
    P.maxEpochCap V s n_init (o :: os) =
      let s' := P.stepDict s o
      let n' := (Finset.univ.filter fun u => (s' u).isSome).card
      let N := min (2 * n_init) U
      let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
      max N (P.maxEpochCap V s' n_init' os)
  seqOutputCorrect_nil : ∀ {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (regs : Fin r → ℕ),
    P.SeqOutputCorrect hr V s [] regs ↔ True
  seqOutputCorrect_singleton_insert : ∀ {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (v : ℕ) (regs : Fin r → ℕ),
    P.SeqOutputCorrect hr V s [P.insert u v] regs ↔ True
  seqOutputCorrect_singleton_delete : ∀ {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (regs : Fin r → ℕ),
    P.SeqOutputCorrect hr V s [P.delete u] regs ↔ True
  seqOutputCorrect_singleton_query : ∀ {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (regs : Fin r → ℕ),
    P.SeqOutputCorrect hr V s [P.query u] regs ↔
      (if regs ⟨252, by omega⟩ = 0 then none else some (regs ⟨253, by omega⟩)) = s u
  seqOutputCorrect_cons_cons : ∀ {r U : ℕ} (hr : 256 ≤ r) (V : ℕ) (s : Fin U → Option ℕ)
    (o₁ o₂ : P.DynamicOp U) (os : List (P.DynamicOp U)) (regs : Fin r → ℕ),
    P.SeqOutputCorrect hr V s (o₁ :: o₂ :: os) regs ↔
      P.SeqOutputCorrect hr V (P.stepDict s o₁) (o₂ :: os) regs
  activeEpochWords_eq : ∀ U V w N n,
    P.activeEpochWords U V w N n = absActiveEpochWords U V w N n
  compactedEpochWords_eq : ∀ U V w N n,
    P.compactedEpochWords U V w N n = absCompactedEpochWords U V w N n
  epochPeakWords_eq : ∀ U V w N,
    P.epochPeakWords U V w N = absEpochPeakWords U V w N
  rRegs_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (frontier : ℕ),
    P.rRegs (P.mkRState regs mem frontier) = regs
  rMem_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (frontier : ℕ),
    P.rMem (P.mkRState regs mem frontier) = mem
  rFrontier_mk : ∀ {r : ℕ} (regs : Fin r → ℕ) (mem : ℕ → ℕ) (frontier : ℕ),
    P.rFrontier (P.mkRState regs mem frontier) = frontier
  rBounded_iff : ∀ {r : ℕ} (w : ℕ) (x : P.RState r),
    P.RBounded w x ↔
      ((∀ i, P.rRegs x i < 2 ^ w) ∧ (∀ a, P.rMem x a < 2 ^ w)) ∧
      P.rFrontier x < 2 ^ w ∧
      ∀ a, P.rFrontier x ≤ a → P.rMem x a = 0

/-! ### Correspondence Lemmas for `DynamicDictPresentation` -/

private theorem dynamicOpOf_surjective (P : DynamicDictPresentation) {U : ℕ}
    (o : P.DynamicOp U) : ∃ o_lib : Dynamic.Op U, P.dynamicOpOf o_lib = o :=
  P.dynamicOp_induction (motive := fun o => ∃ o_lib, P.dynamicOpOf o_lib = o)
    (fun u v => ⟨.insert u v, rfl⟩) (fun u => ⟨.delete u, rfl⟩) (fun u => ⟨.query u, rfl⟩) o

private theorem dynamicOps_surjective (P : DynamicDictPresentation) {U : ℕ}
    (ops : List (P.DynamicOp U)) :
    ∃ ops_lib : List (Dynamic.Op U), ops_lib.map P.dynamicOpOf = ops := by
  choose f hf using dynamicOpOf_surjective P (U := U)
  refine ⟨ops.map f, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ops]
  congr 1
  funext o
  exact hf o

private theorem stepDict_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (o : Dynamic.Op U) :
    P.stepDict s (P.dynamicOpOf o) = ((Dynamic.spec U V n_max).stepFn s o).1 := by
  cases o with
  | insert u v => exact hP.stepDict_insert s u v
  | delete u => exact hP.stepDict_delete s u
  | query u => exact hP.stepDict_query s u

private theorem runDict_map_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V n_max : ℕ} (s : Fin U → Option ℕ) (ops : List (Dynamic.Op U)) :
    P.runDict s (ops.map P.dynamicOpOf) = ((Dynamic.spec U V n_max).run s ops).1 := by
  induction ops generalizing s with
  | nil => exact hP.runDict_nil s
  | cons o os ih =>
    simp only [List.map_cons, hP.runDict_cons, stepDict_dynamicOpOf hP (V := V) (n_max := n_max),
      StateTransitionSpec.run_cons, ih]

private theorem validDictOp_dynamicOpOf_unbounded {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (s : Fin U → Option ℕ) (o : Dynamic.Op U) :
    P.ValidDictOp V s (P.dynamicOpOf o) ↔ (Dynamic.spec U V U).valid s o := by
  cases o with
  | insert u v =>
    rw [DynamicDictPresentation.dynamicOpOf, hP.validDictOp_insert]
    exact (Dynamic.valid_insert_iff_of_le le_rfl s u v).symm
  | delete u => exact hP.validDictOp_delete V s u
  | query u => exact hP.validDictOp_query V s u

private theorem validDictSeq_map_dynamicOpOf_unbounded {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (s : Fin U → Option ℕ) (ops : List (Dynamic.Op U)) :
    P.ValidDictSeq V s (ops.map P.dynamicOpOf) ↔ (Dynamic.spec U V U).ValidHistory s ops := by
  induction ops generalizing s with
  | nil => exact hP.validDictSeq_nil V s
  | cons o os ih =>
    simp only [List.map_cons, hP.validDictSeq_cons, validDictOp_dynamicOpOf_unbounded hP,
      stepDict_dynamicOpOf hP (V := V) (n_max := U), ih]
    rfl

private theorem runEpochInit_map_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (s : Fin U → Option ℕ) (n_init : ℕ)
    (ops : List (Dynamic.Op U)) :
    P.runEpochInit V s n_init (ops.map P.dynamicOpOf) = runEpochInit V s n_init ops := by
  induction ops generalizing s n_init with
  | nil => exact hP.runEpochInit_nil V s n_init
  | cons o os ih =>
    rw [List.map_cons, hP.runEpochInit_cons, stepDict_dynamicOpOf hP (V := V) (n_max := U)]
    exact ih _ _

private theorem maxEpochCap_map_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (s : Fin U → Option ℕ) (n_init : ℕ)
    (ops : List (Dynamic.Op U)) :
    P.maxEpochCap V s n_init (ops.map P.dynamicOpOf) = maxEpochCap V s n_init ops := by
  induction ops generalizing s n_init with
  | nil => exact hP.maxEpochCap_nil V s n_init
  | cons o os ih =>
    rw [List.map_cons, hP.maxEpochCap_cons, stepDict_dynamicOpOf hP (V := V) (n_max := U)]
    dsimp only
    rw [ih]
    rfl

private theorem hrResizable : 256 ≤ rResizable := by
  have h := Succinct.le_rSuccinct
  unfold rResizable
  omega

private theorem seqOutputCorrect_map_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (hr : 256 ≤ rResizable) (s : Fin U → Option ℕ)
    (ops : List (Dynamic.Op U)) (regs : Fin rResizable → ℕ) :
    P.SeqOutputCorrect hr V s (ops.map P.dynamicOpOf) regs ↔
      LastOpOutputCorrect V s ops regs := by
  induction ops generalizing s with
  | nil => exact hP.seqOutputCorrect_nil hr V s regs
  | cons o os ih =>
    cases os with
    | nil =>
      cases o with
      | insert u v => exact hP.seqOutputCorrect_singleton_insert hr V s u v regs
      | delete u => exact hP.seqOutputCorrect_singleton_delete hr V s u regs
      | query u =>
        have h252 : (⟨252, by omega⟩ : Fin rResizable) = resTagReg := Fin.ext rfl
        have h253 : (⟨253, by omega⟩ : Fin rResizable) = resValReg := Fin.ext rfl
        simpa only [List.map_singleton, DynamicDictPresentation.dynamicOpOf,
          LastOpOutputCorrect, h252, h253] using
          hP.seqOutputCorrect_singleton_query hr V s u regs
    | cons o₂ os' =>
      simp only [List.map_cons, hP.seqOutputCorrect_cons_cons,
        stepDict_dynamicOpOf hP (V := V) (n_max := U)]
      exact ih ((Dynamic.spec U V U).stepFn s o).1

/-- Peak epoch capacity `maxEpochCap` from the empty dictionary is at most
`min (2 * ops.length) U`. -/
theorem bridge_maxEpochCap_empty_le_targetCap_length
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) {U : ℕ} (V : ℕ)
    (ops : List (P.DynamicOp U)) :
    P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops ≤
      min (2 * ops.length) U := by
  obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
  rw [maxEpochCap_map_dynamicOpOf hP, List.length_map]
  exact maxEpochCap_empty_le_targetCap_length V ops_lib

private theorem rBounded_rDataOf {P : DynamicDictPresentation} (hP : DynamicDictLaws P)
    {r w : ℕ} {x : P.RState r} (hx : P.RBounded w x) :
    (P.rDataOf x).Bounded w := by
  rw [hP.rBounded_iff] at hx
  exact hx

private theorem rBounded_rStateOf {P : DynamicDictPresentation} (hP : DynamicDictLaws P)
    {r w : ℕ} {x : RData r} (hx : x.Bounded w) :
    P.RBounded w (P.rStateOf x) := by
  rw [hP.rBounded_iff]
  dsimp only [DynamicDictPresentation.rStateOf]
  rw [hP.rRegs_mk, hP.rMem_mk, hP.rFrontier_mk]
  exact hx

private theorem compactedOfVirt_regs (U V w N n base : ℕ) (x : Data rSuccinct) :
    (compactedOfVirt U V w N n base x).regs = x.regs := by
  unfold compactedOfVirt; split_ifs <;> rfl

/-! ## Part 4: Unbounded-Capacity Doubling/Halving Epoch Theorem & Client Reuse Transfer -/

/-- **Unbounded-capacity expected-amortized & stepwise `n_t`-tight compacted space bridge theorem:**
There exist universal `O(1)` constants `r = 9957`, `rebuildUnitCost`, `resizableChargeVal`,
`C_space = 1355`, and `C_word = 380` (quantified **outside** `U, V, w, base`) such that for every
universe `U`, value bound `V`, word width `w`, and base address `base` with `0 < w`, `U < 2 ^ w`,
and `V < 2 ^ w`, every initial machine state `x₀ : P.RState 9957` with `P.RBounded w x₀` and
`P.rFrontier x₀ = base`, and any operation sequence `ops : List (P.DynamicOp U)` satisfying
`P.ValidDictSeq V (emptyDict U) ops` whose peak epoch capacity
`P.maxEpochCap V (emptyDict U) 0 ops` (`≤ min (2 * ops.length) U`) fits in `2 ^ w`, at the
resulting state `s_final = P.runDict (emptyDict U) ops` with live key count `n_final` and epoch
capacity `N_final = min (2 * n_init_final) U`, every supported post-sequence machine state
`x_comp ∈ ν_final.support` **itself** is the live compacted dictionary state (`CompactedRep`) with
physical frontier `P.rFrontier x_comp = base + P.compactedEpochWords U V w N_final n_final`
(`≤ succinctWords 1355 380 U V w n_final` words, `≤ optBits U V n_final + 1355 * n_final *
logLogFactor n_final + 381 * w` bits, and `base + 4` when `n_final = 0`) without any post-hoc
`.shrink` that drops the representation invariant. -/
theorem bridge_unbounded_seq_expected_amortized
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ) (hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      ∀ (U V w base : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        ∀ (x₀ : P.RState r),
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          ∀ ops : List (P.DynamicOp U),
            (∀ N ≤ P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops,
              base + P.epochPeakWords U V w N < 2 ^ w) →
            P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
            let s_final := P.runDict (DynamicDictPresentation.emptyDict U) ops
            let n_final := (Finset.univ.filter fun u => (s_final u).isSome).card
            let n_init_final := P.runEpochInit V (DynamicDictPresentation.emptyDict U) 0 ops
            let N_final := min (2 * n_init_final) U
            (n_final ≤ N_final ∧ N_final ≤ 4 * n_final) ∧
            N_final ≤ U ∧
            (∀ u v, s_final u = some v → v < V) ∧
            P.compactedEpochWords U V w N_final n_final ≤
              ((Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + w - 1) / w +
                C_word ∧
            w * P.compactedEpochWords U V w N_final n_final ≤
              (Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) +
                (C_word + 1) * w ∧
            2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
              ops.length * resizableChargeVal ∧
            ∃ (ν_final : PMF (P.RState r)) (T_ops E_pot : ℝ≥0∞),
              T_ops + E_pot +
                ((2 * rebuildUnitCost *
                  ((n_final - n_init_final) + (n_init_final - n_final)) : ℕ) : ℝ≥0∞) ≤
                ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) ∧
              ∀ x_comp ∈ ν_final.support,
                P.RBounded w x_comp ∧
                P.rFrontier x_comp = base + P.compactedEpochWords U V w N_final n_final ∧
                P.rFrontier x_comp - base ≤
                  ((Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                    C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + w - 1) / w +
                    C_word ∧
                w * (P.rFrontier x_comp - base) ≤
                  (Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                    C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) +
                    (C_word + 1) * w ∧
                P.rRegs x_comp ⟨0, by omega⟩ = base ∧
                P.SeqOutputCorrect hr V (DynamicDictPresentation.emptyDict U) ops
                  (P.rRegs x_comp) ∧
                (∀ a < base, P.rMem x_comp a = P.rMem x₀ a) ∧
                (n_final = 0 → P.rFrontier x_comp = base + 4) := by
  refine ⟨rResizable, rebuildUnitCostConst, resizableChargeValConst, 1355, 380,
    hrResizable, rfl, rfl, ?_⟩
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit_abs hv_abs
  obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
  have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
    (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
      hv_abs
  have hx₀_lib : (P.rDataOf x₀).Bounded w := rBounded_rDataOf hP hx₀
  have hfr₀_lib : (P.rDataOf x₀).frontier = base := hfr₀
  have hfit_lib : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib,
      Fits w (base + epochPeakWords U V w N) := by
    intro N hN
    rw [← maxEpochCap_map_dynamicOpOf hP] at hN
    have h1 := hfit_abs N hN
    rw [hP.epochPeakWords_eq, absEpochPeakWords_eq] at h1
    exact h1
  have hmain_arith := unbounded_seq_expected_amortized (V := V) hw hU ops_lib hv_lib
  dsimp only at hmain_arith
  rw [← rebuildUnitCost_eq_const U V w, ← resizableChargeVal_eq_const U V w]
  obtain ⟨hepoch_f, hN_fU, hvb_f, _, _, hpot_f⟩ := hmain_arith
  have hmach := unbounded_seq_machine_expected_amortized hw hU hV hx₀_lib hfr₀_lib
    ops_lib hfit_lib hv_lib
  dsimp only at hmach
  obtain ⟨_, _, _, ν_lib, T_ops, _, hbound_mach, hsupp_mach⟩ := hmach
  let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops_lib).1
  let n_final := (Dynamic.dom s_final).card
  let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops_lib
  let N_final := targetCap U n_init_final
  have hn_fU : n_final ≤ U := hepoch_f.1.trans hN_fU
  have hcomp_words_f :
      compactedEpochWords U V w N_final n_final ≤
        Dynamic.succinctWords 1355 380 U V w n_final :=
    compactedEpochWords_le_succinctWords hw hn_fU hN_fU (le_of_lt hU) hepoch_f.1 hepoch_f.2
  have hcomp_bits_f :
      w * compactedEpochWords U V w N_final n_final ≤
        Dynamic.optBits U V n_final + 1355 * n_final * Dynamic.logLogFactor n_final + 381 * w :=
    w_mul_compactedEpochWords_le_bits hw hn_fU hN_fU (le_of_lt hU) hepoch_f.1 hepoch_f.2
  dsimp only
  rw [runDict_map_dynamicOpOf hP (V := V) (n_max := U),
    runEpochInit_map_dynamicOpOf hP (V := V), List.length_map,
    hP.compactedEpochWords_eq, absCompactedEpochWords_eq]
  refine ⟨hepoch_f, hN_fU, hvb_f, hcomp_words_f, hcomp_bits_f, hpot_f, ?_⟩
  let toAbsCompState : QuotHashSeed U N_final × Data rSuccinct → P.RState rResizable :=
    fun p => P.rStateOf (compactedOfVirt U V w N_final n_final base p.2)
  let E_pot : ℝ≥0∞ := ∑' q, ν_lib q * (potential U V w N_final base q.1 q.2 : ℝ≥0∞)
  rw [rebuildUnitCost_eq_const U V w, resizableChargeVal_eq_const U V w]
  refine ⟨ν_lib.map toAbsCompState, T_ops, E_pot, hbound_mach, ?_⟩
  intro x_comp hx_comp
  rw [PMF.mem_support_map_iff] at hx_comp
  obtain ⟨p, hp, rfl⟩ := hx_comp
  obtain ⟨hrep_p, _, _, _, hx_comp_bdd, hx_comp_fr, hx_comp_words,
    hx_comp_bits, hout_comp, hx_comp_caller, hx_zero_fn⟩ := hsupp_mach p hp
  refine ⟨rBounded_rStateOf hP hx_comp_bdd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_comp_fr
  · dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_comp_words
  · dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_comp_bits
  · dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rRegs_mk, compactedOfVirt_regs]
    exact hrep_p.2.2.2.1
  · dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rRegs_mk, seqOutputCorrect_map_dynamicOpOf hP hrResizable]
    exact hout_comp
  · intro a ha
    dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rMem_mk]
    exact hx_comp_caller a ha
  · intro hn0
    dsimp only [toAbsCompState, DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_zero_fn hn0

/-- **Client Subroutine Memory-Reuse Bridge Theorem (`bridge_dictionary_client_memory_reuse`):** -/
theorem bridge_dictionary_client_memory_reuse
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∃ (r : ℕ) (hr : 256 ≤ r),
      ∀ (U V w : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ (base sp₂ Δ k_client : ℕ) (x : P.RState r),
          P.RBounded w x →
          P.rFrontier x = base + sp₂ + Δ →
          1 < 2 ^ w →
          base + sp₂ + k_client < 2 ^ w →
          ∃ x_shrunk x_reused : P.RState r,
            P.RBounded w x_shrunk ∧
            P.rFrontier x_shrunk = base + sp₂ ∧
            P.RBounded w x_reused ∧
            P.rFrontier x_reused = base + sp₂ + k_client ∧
            (∀ a < base + sp₂, P.rMem x_reused a = P.rMem x a) ∧
            (∀ a, base + sp₂ ≤ a → a < base + sp₂ + k_client → P.rMem x_reused a = 0)) ∧
        (∀ (base k_client : ℕ) (x₀ : P.RState r) (ops : List (P.DynamicOp U)),
          (∀ N ≤ P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops,
            base + P.epochPeakWords U V w N < 2 ^ w) →
          base + k_client < 2 ^ w →
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
          let s_final := P.runDict (DynamicDictPresentation.emptyDict U) ops
          let n_final := (Finset.univ.filter fun u => (s_final u).isSome).card
          let N_final := min (2 * P.runEpochInit V (DynamicDictPresentation.emptyDict U) 0 ops) U
          ∃ x_dict x_dealloc x_reused : P.RState r,
            P.RBounded w x_dict ∧
            P.rFrontier x_dict = base + P.compactedEpochWords U V w N_final n_final ∧
            P.rRegs x_dict ⟨0, by omega⟩ = base ∧
            P.SeqOutputCorrect hr V (DynamicDictPresentation.emptyDict U) ops (P.rRegs x_dict) ∧
            (∀ a < base, P.rMem x_dict a = P.rMem x₀ a) ∧
            P.RBounded w x_dealloc ∧
            P.rFrontier x_dealloc = base ∧
            P.RBounded w x_reused ∧
            P.rFrontier x_reused = base + k_client ∧
            (∀ a < base, P.rMem x_reused a = P.rMem x₀ a) ∧
            (∀ a, base ≤ a → a < base + k_client → P.rMem x_reused a = 0)) := by
  refine ⟨rResizable, hrResizable, fun U V w hw hU hV => ⟨?_, ?_⟩⟩
  · intro base sp₂ Δ k_client x hx hfr h1 hfit_client
    have hx_lib : (P.rDataOf x).Bounded w := rBounded_rDataOf hP hx
    have hfr_lib : (P.rDataOf x).frontier = base + sp₂ + Δ := hfr
    obtain ⟨y_sh, _, hy_sh_bdd, hy_sh_fr, _, _, _⟩ :=
      shrinkTailWordsCode_exec (U := U) (V := V) (N := U) hx_lib (Δ := Δ) (by omega)
    have hfr2 : (P.rDataOf x).frontier - Δ = base + sp₂ := by omega
    rw [hfr2] at hy_sh_fr
    obtain ⟨x_sh, x_re, _, hx_sh_fr, _, hx_re_bdd, hx_re_fr, _, hx_re_pre, hx_re_zero⟩ :=
      shrink_and_reuse_in_place (U := U) (V := V) (N := U) hx_lib hfr_lib h1 hfit_client
    refine ⟨P.rStateOf y_sh, P.rStateOf x_re,
      rBounded_rStateOf hP hy_sh_bdd, ?_,
      rBounded_rStateOf hP hx_re_bdd, ?_, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hy_sh_fr]
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hx_re_fr]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hx_re_pre a ha
    · intro a ha1 ha2
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hx_re_zero a (by simp only [Block.mem_footprint, Block.Owns]; omega)
  · intro base k_client x₀ ops hfit_abs hfit_client hx₀ hfr₀ hv_abs
    obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
    have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
      (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
        hv_abs
    have hx₀_lib : (P.rDataOf x₀).Bounded w := rBounded_rDataOf hP hx₀
    have hfr₀_lib : (P.rDataOf x₀).frontier = base := hfr₀
    have hfit_lib : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib,
        Fits w (base + epochPeakWords U V w N) := by
      intro N hN
      rw [← maxEpochCap_map_dynamicOpOf hP] at hN
      have h1 := hfit_abs N hN
      rw [hP.epochPeakWords_eq, absEpochPeakWords_eq] at h1
      exact h1
    have hmach := unbounded_seq_machine_expected_amortized hw hU hV hx₀_lib hfr₀_lib
      ops_lib hfit_lib hv_lib
    dsimp only at hmach
    obtain ⟨_, _, _, ν_lib, _, _, _, hsupp_mach⟩ := hmach
    obtain ⟨p, hp⟩ := ν_lib.support_nonempty
    obtain ⟨hrep_dict, _, _, _, hx_comp_bdd, hx_comp_fr, _, _, hout_dict, hpre_dict, _⟩ :=
      hsupp_mach p hp
    let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops_lib).1
    let n_final := (Dynamic.dom s_final).card
    let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops_lib
    let N_final := targetCap U n_init_final
    let x_dict : RData rSuccinct := compactedOfVirt U V w N_final n_final base p.2
    have hNf_le : N_final ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib :=
      targetCap_runEpochInit_le_maxEpochCap V (Dynamic.empty U) 0 ops_lib
    have hfit_Nf : Fits w (base + Succinct.space U V w N_final) :=
      lt_of_le_of_lt (Nat.add_le_add_left (space_le_epochPeakWords U V w N_final) base)
        (hfit_lib N_final hNf_le)
    have hw2 : 2 ≤ w := two_le_w_of_fits_space hfit_Nf
    have h1 : Fits w 1 :=
      lt_of_lt_of_le (by decide : 1 < 2 ^ 2) (Nat.pow_le_pow_right two_pos hw2)
    have hfit_comp : Fits w (compactedEpochWords U V w N_final n_final) :=
      hx_comp_bdd.frontier_fits.of_le (by
        dsimp only [N_final, n_final, n_init_final, s_final]
        omega)
    have hreg_dict : x_dict.regs baseReg = base := by
      dsimp only [x_dict]
      rw [compactedOfVirt_regs]
      exact hrep_dict.2.2.2.1
    obtain ⟨y_de, _, hy_de_bdd, hy_de_fr, _, _, _, hde_caller⟩ :=
      deallocWordsCode_exec (U := U) (V := V) (N := N_final)
        hx_comp_bdd hx_comp_fr hreg_dict hfit_comp
    obtain ⟨x_reused, _, hx_re_bdd, hfr_re, _, _, hx_re_mem, hzero_re⟩ :=
      allocWordsCode_exec (U := U) (V := V) (N := N_final) hy_de_bdd hy_de_fr h1 hfit_client
    dsimp only
    rw [runDict_map_dynamicOpOf hP (V := V) (n_max := U),
      runEpochInit_map_dynamicOpOf hP (V := V)]
    refine ⟨P.rStateOf x_dict, P.rStateOf y_de, P.rStateOf x_reused,
      rBounded_rStateOf hP hx_comp_bdd,
      ?_, ?_, ?_, ?_,
      rBounded_rStateOf hP hy_de_bdd, ?_,
      rBounded_rStateOf hP hx_re_bdd,
      ?_, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf, x_dict]
      rw [hP.rFrontier_mk, hP.compactedEpochWords_eq, absCompactedEpochWords_eq]
      exact hx_comp_fr
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rRegs_mk]
      exact hreg_dict
    · dsimp only [DynamicDictPresentation.rStateOf, x_dict]
      rw [hP.rRegs_mk, seqOutputCorrect_map_dynamicOpOf hP (hr := hrResizable)]
      exact hout_dict
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf, x_dict]
      rw [hP.rMem_mk]
      exact hpre_dict a ha
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hy_de_fr]
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hfr_re]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk, hx_re_mem, hde_caller a ha]
      exact hpre_dict a ha
    · intro a ha1 ha2
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hzero_re a (by simp only [Block.mem_footprint, Block.Owns]; omega)

/-! ## Part 5: Step-by-Step Multi-Operation Execution Trace (`StepSeq`) -/

/-- Step-by-step multi-operation execution trace across `ops : List (P.DynamicOp U)` on the
word-granular Resizable Word-RAM. -/
inductive DynamicDictPresentation.StepSeq (P : DynamicDictPresentation) {r U : ℕ} (hr : 256 ≤ r)
    (V w base : ℕ) (x₀ : P.RState r) :
    (Fin U → Option ℕ) → ℕ → List (P.DynamicOp U) →
    PMF (P.RState r) → PMF (P.RState r) → ℝ≥0∞ → Prop where
  | nil (s : Fin U → Option ℕ) (n_init : ℕ) (ν : PMF (P.RState r)) :
      P.StepSeq hr V w base x₀ s n_init [] ν ν 0
  | cons {s : Fin U → Option ℕ} {n_init : ℕ} {o : P.DynamicOp U} {ops : List (P.DynamicOp U)}
      {ν ν_next ν_final : PMF (P.RState r)} {T_step T_rest : ℝ≥0∞}
      (hstep : ∀ x_post ∈ ν_next.support,
        let s' := P.stepDict s o
        let n' := (Finset.univ.filter fun u => (s' u).isSome).card
        let N := min (2 * n_init) U
        let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
        let N' := min (2 * n_init') U
        P.RBounded w x_post ∧
        P.SeqOutputCorrect hr V s [o] (P.rRegs x_post) ∧
        P.rRegs x_post ⟨0, by omega⟩ = base ∧
        (∀ a < base, P.rMem x_post a = P.rMem x₀ a) ∧
        P.rFrontier x_post = base + P.compactedEpochWords U V w N' n' ∧
        P.rFrontier x_post - base ≤
          ((Nat.clog 2 (U.choose n') + n' * Nat.clog 2 V) +
            1355 * n' * Nat.clog 2 (Nat.clog 2 (max n' 4)) + w - 1) / w + 380 ∧
        w * (P.rFrontier x_post - base) ≤
          (Nat.clog 2 (U.choose n') + n' * Nat.clog 2 V) +
            1355 * n' * Nat.clog 2 (Nat.clog 2 (max n' 4)) + 381 * w ∧
        (n' = 0 → P.rFrontier x_post = base + 4))
      (hrest :
        let s' := P.stepDict s o
        let n' := (Finset.univ.filter fun u => (s' u).isSome).card
        let N := min (2 * n_init) U
        let n_init' := if n' ≤ N ∧ N ≤ 4 * n' then n_init else n'
        P.StepSeq hr V w base x₀ s' n_init' ops ν_next ν_final T_rest) :
      P.StepSeq hr V w base x₀ s n_init (o :: ops) ν ν_final (T_step + T_rest)

private theorem stepSeq_epochValid_eq {U : ℕ} (P : DynamicDictPresentation) (hP : DynamicDictLaws P)
    {V : ℕ} (s : Fin U → Option ℕ) (n_init : ℕ) (o : Dynamic.Op U) :
    let s' := P.stepDict s (P.dynamicOpOf o)
    let n' := (Finset.univ.filter fun u => (s' u).isSome).card
    let N := min (2 * n_init) U
    (if n' ≤ N ∧ N ≤ 4 * n' then n_init else n') =
      if EpochValid (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card (targetCap U n_init)
      then n_init else (Dynamic.dom ((Dynamic.spec U V U).stepFn s o).1).card := by
  dsimp only
  rw [stepDict_dynamicOpOf hP (V := V) (n_max := U)]
  rfl

/-- **Step-by-step multi-operation execution bridge theorem
(`bridge_stepSeq_expected_amortized`):** -/
theorem bridge_stepSeq_expected_amortized
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ) (hr : 256 ≤ r),
      C_space = 1355 ∧
      C_word = 380 ∧
      ∀ (U V w base : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        ∀ (x₀ : P.RState r),
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          ∀ ops : List (P.DynamicOp U),
            (∀ N ≤ P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops,
              base + P.epochPeakWords U V w N < 2 ^ w) →
            P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
            let s_final := P.runDict (DynamicDictPresentation.emptyDict U) ops
            let n_final := (Finset.univ.filter fun u => (s_final u).isSome).card
            let n_init_final := P.runEpochInit V (DynamicDictPresentation.emptyDict U) 0 ops
            ∃ (ν_init ν_final : PMF (P.RState r)) (T_ops E_pot : ℝ≥0∞),
              (∀ x_init ∈ ν_init.support,
                P.RBounded w x_init ∧
                P.rFrontier x_init = base + P.compactedEpochWords U V w 0 0 ∧
                P.rFrontier x_init = base + 4 ∧
                P.rRegs x_init ⟨0, by omega⟩ = base ∧
                (∀ a < base, P.rMem x_init a = P.rMem x₀ a)) ∧
              P.StepSeq hr V w base x₀ (DynamicDictPresentation.emptyDict U) 0 ops
                ν_init ν_final T_ops ∧
              T_ops + E_pot +
                ((2 * rebuildUnitCost *
                  ((n_final - n_init_final) + (n_init_final - n_final)) : ℕ) : ℝ≥0∞) ≤
                ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) := by
  refine ⟨rResizable, rebuildUnitCostConst, resizableChargeValConst, 1355, 380,
    hrResizable, rfl, rfl, ?_⟩
  have hr_res : 256 ≤ rResizable := hrResizable
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit_abs hv_abs
  obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
  have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
    (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
      hv_abs
  have hx₀_lib : (P.rDataOf x₀).Bounded w := rBounded_rDataOf hP hx₀
  have hfr₀_lib : (P.rDataOf x₀).frontier = base := hfr₀
  have hfit_lib : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib,
      Fits w (base + epochPeakWords U V w N) := by
    intro N hN
    rw [← maxEpochCap_map_dynamicOpOf hP] at hN
    have h1 := hfit_abs N hN
    rw [hP.epochPeakWords_eq, absEpochPeakWords_eq] at h1
    exact h1
  let toCompState (N n : ℕ) (p : QuotHashSeed U N × Data rSuccinct) : P.RState rResizable :=
    P.rStateOf (compactedOfVirt U V w N n base p.2)
  have hstep_supp : ∀ (s : Dynamic.State U) (n_init : ℕ)
      (hvb : Dynamic.ValuesBounded V s)
      (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
      (hfit_N : Fits w (base + epochPeakWords U V w (targetCap U n_init)))
      (p : QuotHashSeed U (targetCap U n_init) × Data rSuccinct),
      ResizableRep U V w (targetCap U n_init) base p.1 s
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U n_init)⟩ →
      (∀ a < base, p.2.mem a = (P.rDataOf x₀).mem a) →
      let n := (Dynamic.dom s).card
      let N := targetCap U n_init
      let x_post := toCompState N n p
      P.RBounded w x_post ∧
      P.rRegs x_post ⟨0, by omega⟩ = base ∧
      (∀ a < base, P.rMem x_post a = P.rMem x₀ a) ∧
      P.rFrontier x_post = base + P.compactedEpochWords U V w N n ∧
      P.rFrontier x_post - base ≤
        ((Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
          1355 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + w - 1) / w + 380 ∧
      w * (P.rFrontier x_post - base) ≤
        (Nat.clog 2 (U.choose n) + n * Nat.clog 2 V) +
          1355 * n * Nat.clog 2 (Nat.clog 2 (max n 4)) + 381 * w ∧
      (n = 0 → P.rFrontier x_post = base + 4) := by
    intro s n_init hvb hepoch hfit_N p hrep_p hcaller_p n N x_post
    have hfit_comp : Fits w (base + compactedEpochWords U V w N n) :=
      hfit_N.of_le (Nat.add_le_add_left (compactedEpochWords_le_epochPeakWords hepoch.1) base)
    obtain ⟨hcomp_rep, _, hcomp_caller⟩ :=
      compactedRep_of_epochValid (n := n) hw hU hV hepoch (targetCap_le_univ U n_init)
        hfit_comp rfl hvb hrep_p.2.2
    have htoData_eq :
        ({ regs := p.2.regs, mem := p.2.mem,
           frontier := base + Succinct.space U V w (targetCap U n_init) } :
          RData rSuccinct).toData = p.2 := rfl
    rw [htoData_eq] at hcomp_rep hcomp_caller
    refine ⟨rBounded_rStateOf hP hcomp_rep.bounded, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rRegs_mk, compactedOfVirt_regs]
      exact hrep_p.2.2.2.1
    · intro a ha
      dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk, (hcomp_caller a ha).trans (hcaller_p a ha)]
      rfl
    · dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hP.compactedEpochWords_eq, absCompactedEpochWords_eq]
      exact hcomp_rep.frontier_eq
    · dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk]
      exact hcomp_rep.frontier_sub_base_le_succinctWords hw (le_of_lt hU)
    · dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk]
      exact hcomp_rep.w_mul_frontier_sub_base_le_bits hw (le_of_lt hU)
    · intro hn0
      dsimp only [x_post, toCompState, DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hcomp_rep.frontier_eq, hn0]
      simp [compactedEpochWords]
  have hgen : ∀ (l : List (Dynamic.Op U)) (s : Dynamic.State U) (n_init : ℕ)
      (hvb : Dynamic.ValuesBounded V s)
      (hepoch : EpochValid (Dynamic.dom s).card (targetCap U n_init))
      (hfit_l : ∀ N ≤ maxEpochCap V s n_init l, Fits w (base + epochPeakWords U V w N))
      (hvh_s : (Dynamic.spec U V U).ValidHistory s l)
      (ν : PMF (QuotHashSeed U (targetCap U n_init) × Data rSuccinct))
      (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
        1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U n_init))) θ)
      (hsupp : ∀ p ∈ ν.support,
        ResizableRep U V w (targetCap U n_init) base p.1 s
          ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U n_init)⟩ ∧
        ∀ a < base, p.2.mem a = (P.rDataOf x₀).mem a),
      let sf := ((Dynamic.spec U V U).run s l).1
      let nf := (Dynamic.dom sf).card
      let n_init_f := runEpochInit V s n_init l
      let Nf := targetCap U n_init_f
      ∃ (ν_f : PMF (QuotHashSeed U Nf × Data rSuccinct)) (T_ops : ℝ≥0∞),
        (∀ θ, (ν_f.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U Nf)) θ) ∧
        (∀ p ∈ ν_f.support,
          ResizableRep U V w Nf base p.1 sf ⟨p.2.regs, p.2.mem, base + Succinct.space U V w Nf⟩ ∧
          ∀ a < base, p.2.mem a = (P.rDataOf x₀).mem a) ∧
        P.StepSeq hrResizable V w base x₀ s n_init (l.map P.dynamicOpOf)
          (ν.map (toCompState (targetCap U n_init) (Dynamic.dom s).card))
          (ν_f.map (toCompState Nf nf)) T_ops ∧
        T_ops + (∑' q, ν_f q * (potential U V w Nf base q.1 q.2 : ℝ≥0∞)) +
          ((2 * rebuildUnitCost U V w * natDist nf n_init_f : ℕ) : ℝ≥0∞) ≤
          (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
            ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
              l.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
    intro l
    induction l with
    | nil =>
      intro s n_init _ _ _ _ ν hseed hsupp
      refine ⟨ν, 0, hseed, hsupp, DynamicDictPresentation.StepSeq.nil _ _ _, ?_⟩
      simp only [runEpochInit, List.length_nil, Nat.zero_mul, Nat.add_zero, zero_add]
      exact le_rfl
    | cons o os ih =>
      intro s n_init hvb hepoch hfit_l ⟨hval, hvh_os⟩ ν hseed hsupp
      have hstep_arith := unbounded_step_expected_amortized hw hU hvb o hval hepoch
      dsimp only at hstep_arith
      obtain ⟨hepoch₁, _, hvb₁, _, _, _, _⟩ := hstep_arith
      let s₁ := ((Dynamic.spec U V U).stepFn s o).1
      let n₁ := (Dynamic.dom s₁).card
      let n_init₁ := if EpochValid n₁ (targetCap U n_init) then n_init else n₁
      have hfit_N : Fits w (base + epochPeakWords U V w (targetCap U n_init)) :=
        hfit_l (targetCap U n_init) (targetCap_le_maxEpochCap V s n_init (o :: os))
      have hfit_os : ∀ N ≤ maxEpochCap V s₁ n_init₁ os, Fits w (base + epochPeakWords U V w N) :=
        fun N hN => hfit_l N (hN.trans (maxEpochCap_tail_le V s n_init o os))
      have hfit_N₁ : Fits w (base + epochPeakWords U V w (targetCap U n_init₁)) :=
        hfit_os (targetCap U n_init₁) (targetCap_le_maxEpochCap V s₁ n_init₁ os)
      obtain ⟨ν₁, T₁, hseed₁, hsupp₁, hbound₁⟩ :=
        unbounded_step_machine_aux (n_init' := n_init₁)
          hw hU hV hfit_N hfit_N₁ hx₀_lib hfr₀_lib hvb o hval hepoch rfl ν hseed hsupp
      obtain ⟨ν_f, T_rest, hseed_f, hsupp_f, hseq_rest, hbound_rest⟩ :=
        ih s₁ n_init₁ hvb₁ hepoch₁ hfit_os hvh_os ν₁ hseed₁
          (fun q hq => ⟨(hsupp₁ q hq).1, (hsupp₁ q hq).2.1⟩)
      refine ⟨ν_f, T₁ + T_rest, hseed_f, hsupp_f, ?_, ?_⟩
      · have hs₁_eq : P.stepDict s (P.dynamicOpOf o) = s₁ :=
          stepDict_dynamicOpOf hP (V := V) (n_max := U) s o
        have hn_init₁_eq := stepSeq_epochValid_eq P hP (V := V) s n_init o
        dsimp only at hn_init₁_eq
        refine DynamicDictPresentation.StepSeq.cons
          (ν_next := ν₁.map (toCompState (targetCap U n_init₁) n₁))
          (fun x_post hx_post => ?_) ?_
        · rw [PMF.mem_support_map_iff] at hx_post
          obtain ⟨q, hq, rfl⟩ := hx_post
          obtain ⟨hrep_q, hcaller_q, hout_q⟩ := hsupp₁ q hq
          have hpost := hstep_supp s₁ n_init₁ hvb₁ hepoch₁ hfit_N₁ q hrep_q hcaller_q
          dsimp only at hpost ⊢
          rw [hs₁_eq]
          change _ ∧ _ ∧ _ ∧ _ ∧
            P.rFrontier (toCompState (targetCap U n_init₁) n₁ q) =
              base + P.compactedEpochWords U V w
                (targetCap U (if EpochValid n₁ (targetCap U n_init) then n_init else n₁)) n₁ ∧ _
          have hout_abs : P.SeqOutputCorrect hrResizable V s [P.dynamicOpOf o]
              (P.rRegs (toCompState (targetCap U n_init₁) n₁ q)) := by
            dsimp only [toCompState, DynamicDictPresentation.rStateOf]
            rw [hP.rRegs_mk, compactedOfVirt_regs]
            exact (seqOutputCorrect_map_dynamicOpOf hP (hr := hrResizable)
              (V := V) s [o] q.2.regs).mpr hout_q
          exact ⟨hpost.1, hout_abs, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1,
            hpost.2.2.2.2.1, hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2⟩
        · dsimp only
          rw [hn_init₁_eq]
          change P.StepSeq hrResizable V w base x₀ (P.stepDict s (P.dynamicOpOf o)) n_init₁
            (os.map P.dynamicOpOf) _ _ T_rest
          rw [hs₁_eq]
          exact hseq_rest
      · dsimp only [runEpochInit, StateTransitionSpec.run_cons, s₁, n₁, n_init₁] at hbound_rest ⊢
        have hlen_eq :
            ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                resizableChargeVal U V w : ℕ) : ℝ≥0∞) +
              ((os.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) =
              ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                (o :: os).length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
          norm_cast
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        calc (T₁ + T_rest) +
              (∑' q, ν_f q *
                (potential U V w (targetCap U (runEpochInit V s₁ n_init₁ os))
                  base q.1 q.2 : ℝ≥0∞)) +
              ((2 * rebuildUnitCost U V w *
                natDist (Dynamic.dom ((Dynamic.spec U V U).run s₁ os).1).card
                  (runEpochInit V s₁ n_init₁ os) : ℕ) : ℝ≥0∞)
            = T₁ + (T_rest +
                (∑' q, ν_f q *
                  (potential U V w (targetCap U (runEpochInit V s₁ n_init₁ os))
                    base q.1 q.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w *
                  natDist (Dynamic.dom ((Dynamic.spec U V U).run s₁ os).1).card
                    (runEpochInit V s₁ n_init₁ os) : ℕ) : ℝ≥0∞)) := by ac_rfl
          _ ≤ T₁ + ((∑' p, ν₁ p * (potential U V w (targetCap U n_init₁) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist n₁ n_init₁ +
                  os.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞)) :=
              add_le_add le_rfl hbound_rest
          _ = (T₁ + (∑' p, ν₁ p * (potential U V w (targetCap U n_init₁) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist n₁ n_init₁ : ℕ) : ℝ≥0∞)) +
                ((os.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
              push_cast
              ac_rfl
          _ ≤ ((∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                  resizableChargeVal U V w : ℕ) : ℝ≥0∞)) +
                ((os.length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) :=
              add_le_add hbound₁ le_rfl
          _ = (∑' p, ν p * (potential U V w (targetCap U n_init) base p.1 p.2 : ℝ≥0∞)) +
                ((2 * rebuildUnitCost U V w * natDist (Dynamic.dom s).card n_init +
                  (o :: os).length * resizableChargeVal U V w : ℕ) : ℝ≥0∞) := by
              rw [add_assoc, hlen_eq]
  have hfit0 : Fits w (base + Succinct.space U V w (targetCap U 0)) :=
    (hfit_lib (targetCap U 0) (targetCap_le_maxEpochCap V (Dynamic.empty U) 0 ops_lib)).of_le
      (Nat.add_le_add_left (space_le_epochPeakWords U V w (targetCap U 0)) base)
  obtain ⟨_, ν₀_r, _, _, hseed₀_r, hsupp₀_r⟩ :=
    init_resizable_succinct hw (targetCap_le_univ U 0) hU hV hfit0 hx₀_lib hfr₀_lib
  let ν₀ : PMF (QuotHashSeed U (targetCap U 0) × Data rSuccinct) :=
    ν₀_r.map fun p => (p.1, p.2.toData)
  have hseed₀ : ∀ θ, (ν₀.map Prod.fst) θ ≤
      1 * (PMF.uniformOfFintype (QuotHashSeed U (targetCap U 0))) θ := by
    intro θ
    rw [one_mul]
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact hseed₀_r θ
  have hsupp₀ : ∀ p ∈ ν₀.support,
      ResizableRep U V w (targetCap U 0) base p.1 (Dynamic.empty U)
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w (targetCap U 0)⟩ ∧
      ∀ a < base, p.2.mem a = (P.rDataOf x₀).mem a := by
    intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hrep_q, _, hmod_q⟩ := hsupp₀_r q hq
    have hfr_q : q.2.frontier = base + Succinct.space U V w (targetCap U 0) := hrep_q.2.1
    have h_eta : (⟨q.2.toData.regs, q.2.toData.mem,
        base + Succinct.space U V w (targetCap U 0)⟩ : RData _) = q.2 := by
      ext a <;> simp [hfr_q]
    rw [h_eta]
    refine ⟨hrep_q, fun a ha => ?_⟩
    have hnot : a ∉ (Block.mk base (Succinct.space U V w (targetCap U 0))).footprint := by
      simp only [Block.mem_footprint, Block.Owns]
      omega
    exact hmod_q a hnot
  have hpot₀ : (∑' p, ν₀ p * (potential U V w (targetCap U 0) base p.1 p.2 : ℝ≥0∞)) = 0 := by
    refine tsum_eq_zero_iff.mpr fun p => ?_
    by_cases hp : p ∈ ν₀.support
    · rw [PMF.mem_support_map_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [(hsupp₀_r q hq).2.1, Nat.cast_zero, mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul]
  obtain ⟨ν_f, T_ops, _, _, hseq_f, hbound_f⟩ :=
    hgen ops_lib (Dynamic.empty U) 0 (Dictionary.valuesBounded_empty U V)
      (by simp [EpochValid, targetCap]) hfit_lib hv_lib ν₀ hseed₀ hsupp₀
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    simp [Dynamic.dom, Dynamic.empty, Dictionary.dom_empty]
  rw [hpot₀, zero_add, hdom0, natDist_self, Nat.mul_zero,
    Nat.zero_add, rebuildUnitCost_eq_const, resizableChargeVal_eq_const] at hbound_f
  let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops_lib).1
  let n_final := (Dynamic.dom s_final).card
  let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops_lib
  let N_final := targetCap U n_init_final
  let E_pot : ℝ≥0∞ := ∑' q, ν_f q * (potential U V w N_final base q.1 q.2 : ℝ≥0∞)
  dsimp only
  rw [runDict_map_dynamicOpOf hP (V := V) (n_max := U),
    runEpochInit_map_dynamicOpOf hP (V := V), List.length_map]
  refine ⟨ν₀.map (toCompState (targetCap U 0) (Dynamic.dom (Dynamic.empty U)).card),
    ν_f.map (toCompState N_final n_final), T_ops, E_pot, ?_, hseq_f, hbound_f⟩
  intro x_init hx_init
  rw [PMF.mem_support_map_iff] at hx_init
  obtain ⟨p, hp, rfl⟩ := hx_init
  obtain ⟨hrep_p, hcaller_p⟩ := hsupp₀ p hp
  have hfit_0 : Fits w (base + epochPeakWords U V w (targetCap U 0)) :=
    hfit_lib (targetCap U 0) (targetCap_le_maxEpochCap V (Dynamic.empty U) 0 ops_lib)
  have hpost0 := hstep_supp (Dynamic.empty U) 0 (Dictionary.valuesBounded_empty U V)
    (by simp [EpochValid, targetCap]) hfit_0 p hrep_p hcaller_p
  dsimp only at hpost0
  refine ⟨hpost0.1, ?_, hpost0.2.2.2.2.2.2 hdom0, hpost0.2.1, hpost0.2.2.1⟩
  exact hpost0.2.2.2.1.trans (by rw [hdom0]; rfl)

end ComplexityAbstracts.ResizableSuccinctDictionaryBridge
