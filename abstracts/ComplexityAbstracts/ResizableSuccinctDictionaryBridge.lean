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

`ResizableSuccinctDictionaryAbstract.lean` states the self-contained formal abstract for:
1. The word-granular resizable Word-RAM memory model (`DemonicGrow`, `shrinkMem`, `zeroSlice`,
   and equivalence between demonic `.grow` followed by `zeroSlice` and zero-initialized growth);
2. The Stage 1 bit-packed resizable array of `b`-bit items (`b ≤ w`) with `1 + ⌈n_t * b / w⌉`-word
   footprint (`< n_t * b + 2 * w` bits) at every step `t`;
3. The Stage 2 resizable succinct dynamic dictionary (`insert`, `delete`, `query`) with stepwise
   `n_t`-tight space `OPT(U, V, n_t) + O(n_t log log n_t) + 214 * w` bits, `O(1)` expected
   amortized operation time across unbounded-capacity sequences (`Dynamic.spec U V U`), and client
   subroutine memory reuse in `[0, L)`.

This bridge connects the self-contained definitions and theorem statements in
`ResizableSuccinctDictionaryAbstract.lean` to the library proofs in
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
  SeqOutputCorrect {U : ℕ} : ℕ → (Fin U → Option ℕ) → List (DynamicOp U) → (Fin 9957 → ℕ) → Prop
  activeEpochWords : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
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
  seqOutputCorrect_nil : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ) (regs : Fin 9957 → ℕ),
    P.SeqOutputCorrect V s [] regs ↔ True
  seqOutputCorrect_singleton_insert : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (v : ℕ) (regs : Fin 9957 → ℕ),
    P.SeqOutputCorrect V s [P.insert u v] regs ↔ True
  seqOutputCorrect_singleton_delete : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (regs : Fin 9957 → ℕ),
    P.SeqOutputCorrect V s [P.delete u] regs ↔ True
  seqOutputCorrect_singleton_query : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (u : Fin U) (regs : Fin 9957 → ℕ),
    P.SeqOutputCorrect V s [P.query u] regs ↔
      (if regs ⟨252, by decide⟩ = 0 then none else some (regs ⟨253, by decide⟩)) = s u
  seqOutputCorrect_cons_cons : ∀ {U : ℕ} (V : ℕ) (s : Fin U → Option ℕ)
    (o₁ o₂ : P.DynamicOp U) (os : List (P.DynamicOp U)) (regs : Fin 9957 → ℕ),
    P.SeqOutputCorrect V s (o₁ :: o₂ :: os) regs ↔
      P.SeqOutputCorrect V (P.stepDict s o₁) (o₂ :: os) regs
  activeEpochWords_eq : ∀ U V w N n,
    P.activeEpochWords U V w N n = absActiveEpochWords U V w N n
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

private theorem seqOutputCorrect_map_dynamicOpOf {P : DynamicDictPresentation}
    (hP : DynamicDictLaws P) {U V : ℕ} (s : Fin U → Option ℕ)
    (ops : List (Dynamic.Op U)) (regs : Fin rResizable → ℕ) :
    P.SeqOutputCorrect V s (ops.map P.dynamicOpOf) regs ↔
      LastOpOutputCorrect V s ops regs := by
  induction ops generalizing s with
  | nil => exact hP.seqOutputCorrect_nil V s regs
  | cons o os ih =>
    cases os with
    | nil =>
      cases o with
      | insert u v => exact hP.seqOutputCorrect_singleton_insert V s u v regs
      | delete u => exact hP.seqOutputCorrect_singleton_delete V s u regs
      | query u => exact hP.seqOutputCorrect_singleton_query V s u regs
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

/-! ## Part 4: Unbounded-Capacity Doubling/Halving Epoch Theorem & Client Reuse Transfer -/

/-- **Unbounded-capacity expected-amortized & stepwise `n_t`-tight space bridge theorem:**
There exist universal `O(1)` constants `r = rResizable = 9957`,
`rebuildUnitCost = rebuildUnitCostConst = 53495843`,
`resizableChargeVal = resizableChargeValConst = 160486391`, `C_space = 1227`, and `C_word = 213`
(quantified **outside** `U, V, w, base`) such that for every universe `U`, value bound `V`, word
width `w`, and base address `base` with `0 < w`, `U < 2 ^ w`, and `V < 2 ^ w`, every initial
machine state `x₀ : P.RState r` with `P.RBounded w x₀` and `P.rFrontier x₀ = base`, and any
operation sequence `ops : List (P.DynamicOp U)` satisfying
`P.ValidDictSeq V (emptyDict U) ops` (no capacity cap `n_max`) whose peak epoch capacity
`P.maxEpochCap V (emptyDict U) 0 ops` (`≤ min (2 * ops.length) U`) fits in `2 ^ w`, at the
resulting state `s_final = P.runDict (emptyDict U) ops` with live key count `n_final` and epoch
capacity `N_final = min (2 * n_init_final) U`:
1. `n_final ≤ N_final ≤ 4 * n_final` (`EpochValid`), `N_final ≤ U`, and all stored values are
   `< V`;
2. The active word footprint `P.activeEpochWords U V w N_final n_final` is at most
   `succinctWords C_space C_word U V w n_final` words, and in bits at most
   `optBits U V n_final + C_space * n_final * logLogFactor n_final + (C_word + 1) * w` bits;
3. Across the entire sequence `ops`, there exist a final machine-state distribution
   `ν_final : PMF (P.RState r)`, cumulative expected instruction time `T_ops : ℝ≥0∞`, and expected
   slot potential `E_pot : ℝ≥0∞` satisfying
   `T_ops + E_pot + 2 * rebuildUnitCost * |n_final - n_init_final| ≤`
   `ops.length * resizableChargeVal`,
   where every `x_epoch ∈ ν_final.support` has physical frontier `base + epochSpace U V w N_final`,
   `P.rRegs x_epoch ⟨0, by decide⟩ = base`,
   `P.SeqOutputCorrect V (emptyDict U) ops (P.rRegs x_epoch)`,
   preserves caller memory `< base`, and contracts in `2` instructions via `.shrink` to a resting
   machine state `x_rest : P.RState r` with physical frontier
   `P.rFrontier x_rest = base + P.activeEpochWords U V w N_final n_final` and
   `P.SeqOutputCorrect V (emptyDict U) ops (P.rRegs x_rest)`. -/
theorem bridge_unbounded_seq_expected_amortized
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∃ (r rebuildUnitCost resizableChargeVal C_space C_word : ℕ),
      r = 9957 ∧
      rebuildUnitCost = 53495843 ∧
      resizableChargeVal = 160486391 ∧
      C_space = 1227 ∧
      C_word = 213 ∧
      ∀ (U V w base : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        ∀ (x₀ : P.RState 9957),
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          ∀ ops : List (P.DynamicOp U),
            (∀ N ≤ P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops,
              base + P.activeEpochWords U V w N N < 2 ^ w) →
            P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
            let s_final := P.runDict (DynamicDictPresentation.emptyDict U) ops
            let n_final := (Finset.univ.filter fun u => (s_final u).isSome).card
            let n_init_final := P.runEpochInit V (DynamicDictPresentation.emptyDict U) 0 ops
            let N_final := min (2 * n_init_final) U
            (n_final ≤ N_final ∧ N_final ≤ 4 * n_final) ∧
            N_final ≤ U ∧
            (∀ u v, s_final u = some v → v < V) ∧
            P.activeEpochWords U V w N_final n_final ≤
              ((Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + w - 1) / w +
                C_word ∧
            w * P.activeEpochWords U V w N_final n_final ≤
              (Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) +
                (C_word + 1) * w ∧
            2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
              ops.length * resizableChargeVal ∧
            ∃ (ν_final : PMF (P.RState 9957)) (T_ops E_pot : ℝ≥0∞),
              T_ops + E_pot +
                ((2 * rebuildUnitCost *
                  ((n_final - n_init_final) + (n_init_final - n_final)) : ℕ) : ℝ≥0∞) ≤
                ((ops.length * resizableChargeVal : ℕ) : ℝ≥0∞) ∧
              ∀ x_epoch ∈ ν_final.support,
                P.RBounded w x_epoch ∧
                P.rFrontier x_epoch = base + P.activeEpochWords U V w N_final N_final ∧
                P.rRegs x_epoch ⟨0, by decide⟩ = base ∧
                P.SeqOutputCorrect V (DynamicDictPresentation.emptyDict U) ops
                  (P.rRegs x_epoch) ∧
                (∀ a < base, P.rMem x_epoch a = P.rMem x₀ a) ∧
                ∃ x_rest : P.RState 9957,
                  P.RBounded w x_rest ∧
                  P.rFrontier x_rest = base + P.activeEpochWords U V w N_final n_final ∧
                  P.rFrontier x_rest - base ≤
                    ((Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                      C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + w - 1) / w +
                      C_word ∧
                  w * (P.rFrontier x_rest - base) ≤
                    (Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
                      C_space * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) +
                      (C_word + 1) * w ∧
                  P.SeqOutputCorrect V (DynamicDictPresentation.emptyDict U) ops
                    (P.rRegs x_rest) ∧
                  (∀ a < base, P.rMem x_rest a = P.rMem x₀ a) ∧
                  (n_final = 0 →
                    ∃ x_zero : P.RState 9957,
                      P.RBounded w x_zero ∧
                      P.rFrontier x_zero = base ∧
                      ∀ a < base, P.rMem x_zero a = P.rMem x₀ a) := by
  refine ⟨rResizable, rebuildUnitCostConst, resizableChargeValConst, 1227, 213,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro U V w base hw hU hV x₀ hx₀ hfr₀ ops hfit_abs hv_abs
  obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
  have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
    (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
      hv_abs
  have hx₀_lib : (P.rDataOf x₀).Bounded w := rBounded_rDataOf hP hx₀
  have hfr₀_lib : (P.rDataOf x₀).frontier = base := hfr₀
  have hfit_lib : ∀ N ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib,
      Fits w (base + Succinct.space U V w N) := by
    intro N hN
    rw [← maxEpochCap_map_dynamicOpOf hP] at hN
    have h1 := hfit_abs N hN
    rw [hP.activeEpochWords_eq, absActiveEpochWords_eq, activeEpochWords_eq_space] at h1
    exact h1
  have hmain_arith := unbounded_seq_expected_amortized (V := V) hw hU ops_lib hv_lib
  dsimp only at hmain_arith
  rw [← rebuildUnitCost_eq_const U V w, ← resizableChargeVal_eq_const U V w]
  obtain ⟨hepoch_f, hN_fU, hvb_f, hwords_f, hbits_f, hpot_f⟩ := hmain_arith
  have hmach := unbounded_seq_machine_expected_amortized hw hU hV hx₀_lib hfr₀_lib
    ops_lib hfit_lib hv_lib
  dsimp only at hmach
  obtain ⟨_, _, _, ν_lib, T_ops, _, hbound_mach, hsupp_mach⟩ := hmach
  dsimp only
  rw [runDict_map_dynamicOpOf hP (V := V) (n_max := U),
    runEpochInit_map_dynamicOpOf hP (V := V), List.length_map,
    hP.activeEpochWords_eq, absActiveEpochWords_eq]
  refine ⟨hepoch_f, hN_fU, hvb_f, hwords_f, hbits_f, hpot_f, ?_⟩
  let s_final := ((Dynamic.spec U V U).run (Dynamic.empty U) ops_lib).1
  let n_final := (Dynamic.dom s_final).card
  let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops_lib
  let N_final := targetCap U n_init_final
  let toAbsState : QuotHashSeed U N_final × Data rSuccinct → P.RState rResizable :=
    fun p => P.rStateOf (castRData (rSuccinct_eq_const U V w N_final)
      ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩)
  let E_pot : ℝ≥0∞ := ∑' q, ν_lib q * (potential U V w N_final base q.1 q.2 : ℝ≥0∞)
  rw [rebuildUnitCost_eq_const U V w, resizableChargeVal_eq_const U V w]
  refine ⟨ν_lib.map toAbsState, T_ops, E_pot, hbound_mach, ?_⟩
  intro x_epoch hx_epoch
  rw [PMF.mem_support_map_iff] at hx_epoch
  obtain ⟨p, hp, rfl⟩ := hx_epoch
  obtain ⟨hrep_p, hcaller_p, hout_p, x_rest, _, hx_rest_bdd, hx_rest_fr, hx_rest_words,
    hx_rest_bits, hout_rest, hx_rest_caller, hx_zero_fn⟩ := hsupp_mach p hp
  have hx_epoch_bdd :
      (castRData (rSuccinct_eq_const U V w N_final)
        ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩).Bounded w :=
    castRData_bounded (rSuccinct_eq_const U V w N_final) hrep_p.1
  refine ⟨rBounded_rStateOf hP hx_epoch_bdd, ?_, ?_, ?_, ?_, P.rStateOf x_rest,
    rBounded_rStateOf hP hx_rest_bdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [toAbsState, DynamicDictPresentation.rStateOf, castRData]
    rw [hP.rFrontier_mk, hP.activeEpochWords_eq, absActiveEpochWords_eq, activeEpochWords_eq_space]
    rfl
  · dsimp only [toAbsState, DynamicDictPresentation.rStateOf, castRData]
    rw [hP.rRegs_mk]
    have h0 : (⟨0, by decide⟩ : Fin rResizable).cast (rSuccinct_eq_const U V w N_final).symm =
        baseReg := Fin.ext rfl
    rw [h0]
    exact hrep_p.2.2.2.1
  · dsimp only [toAbsState, DynamicDictPresentation.rStateOf]
    rw [hP.rRegs_mk, seqOutputCorrect_map_dynamicOpOf hP]
    exact hout_p
  · intro a ha
    dsimp only [toAbsState, DynamicDictPresentation.rStateOf, castRData]
    rw [hP.rMem_mk]
    exact hcaller_p a ha
  · dsimp only [DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_rest_fr
  · dsimp only [DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_rest_words
  · dsimp only [DynamicDictPresentation.rStateOf]
    rw [hP.rFrontier_mk]
    exact hx_rest_bits
  · dsimp only [DynamicDictPresentation.rStateOf]
    rw [hP.rRegs_mk, seqOutputCorrect_map_dynamicOpOf hP]
    exact hout_rest
  · intro a ha
    dsimp only [DynamicDictPresentation.rStateOf]
    rw [hP.rMem_mk]
    exact hx_rest_caller a ha
  · intro hn0
    obtain ⟨x_zero, _, hx_zero_bdd, hx_zero_fr, hx_zero_caller⟩ := hx_zero_fn hn0
    refine ⟨P.rStateOf x_zero, rBounded_rStateOf hP hx_zero_bdd, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk]
      exact hx_zero_fr
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hx_zero_caller a ha

/-- **Client Subroutine Memory-Reuse Bridge Theorem (`bridge_shrink_and_reuse_in_place` and
`bridge_subroutine_client_reuse_released_memory`):**
With the universal register count `r = rResizable = 9957` quantified **outside** `(U, V, w)`:
1. **Partial tail contraction and reuse (`shrink_and_reuse_in_place`):** When deletions reduce a
   dictionary's active item footprint from `base + sp₂ + Δ` by `Δ` words to `base + sp₂`, executing
   `shrinkTailWordsCode` (`2` instructions) followed by a client allocation `growTailWordsCode`
   (`4 * k_client + 8` instructions under demonic `DemonicGrow`) produces `x_shrunk, x_reused` with
   `P.rFrontier x_shrunk = base + sp₂`, `P.rFrontier x_reused = base + sp₂ + k_client` (reusing the
   released addresses `[base + sp₂, ...)`), `P.RBounded w x_reused`, preserved prefix
   `[0, base + sp₂)`, and zeroed client slice `[base + sp₂, base + sp₂ + k_client)`.
2. **Full dictionary lifecycle and memory reuse:**
   Executing the dictionary over any valid sequence `ops` whose peak epoch capacity
   `P.maxEpochCap V (emptyDict U) 0 ops` fits in `2 ^ w`, deallocating via `deallocSuccinctCode`
   (`3` instructions, `.shrink`), and allocating `k_client` words for a subsequent client via
   `allocWordsCode` (`4 * k_client + 8` instructions under demonic `DemonicGrow`) produces
   `x_dict, x_dealloc, x_reused` with
   `P.rFrontier x_dict = base + P.activeEpochWords U V w N_final N_final`,
   `P.SeqOutputCorrect V (emptyDict U) ops (P.rRegs x_dict)`,
   `P.rFrontier x_dealloc = base`, and `P.rFrontier x_reused = base + k_client`—reusing
   `[base, base + k_client)` while preserving all caller memory `< base`. -/
theorem bridge_dictionary_client_memory_reuse
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∃ r : ℕ,
      r = 9957 ∧
      ∀ (U V w : ℕ),
        0 < w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ (base sp₂ Δ k_client : ℕ) (x : P.RState 9957),
          P.RBounded w x →
          P.rFrontier x = base + sp₂ + Δ →
          1 < 2 ^ w →
          base + sp₂ + k_client < 2 ^ w →
          ∃ x_shrunk x_reused : P.RState 9957,
            P.RBounded w x_shrunk ∧
            P.rFrontier x_shrunk = base + sp₂ ∧
            P.RBounded w x_reused ∧
            P.rFrontier x_reused = base + sp₂ + k_client ∧
            (∀ a < base + sp₂, P.rMem x_reused a = P.rMem x a) ∧
            (∀ a, base + sp₂ ≤ a → a < base + sp₂ + k_client → P.rMem x_reused a = 0)) ∧
        (∀ (base k_client : ℕ) (x₀ : P.RState 9957) (ops : List (P.DynamicOp U)),
          (∀ N ≤ P.maxEpochCap V (DynamicDictPresentation.emptyDict U) 0 ops,
            base + P.activeEpochWords U V w N N < 2 ^ w) →
          base + k_client < 2 ^ w →
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
          let N_final := min (2 * P.runEpochInit V (DynamicDictPresentation.emptyDict U) 0 ops) U
          ∃ x_dict x_dealloc x_reused : P.RState 9957,
            P.RBounded w x_dict ∧
            P.rFrontier x_dict = base + P.activeEpochWords U V w N_final N_final ∧
            P.rRegs x_dict ⟨0, by decide⟩ = base ∧
            P.SeqOutputCorrect V (DynamicDictPresentation.emptyDict U) ops (P.rRegs x_dict) ∧
            (∀ a < base, P.rMem x_dict a = P.rMem x₀ a) ∧
            P.RBounded w x_dealloc ∧
            P.rFrontier x_dealloc = base ∧
            P.RBounded w x_reused ∧
            P.rFrontier x_reused = base + k_client ∧
            (∀ a < base, P.rMem x_reused a = P.rMem x₀ a) ∧
            (∀ a, base ≤ a → a < base + k_client → P.rMem x_reused a = 0)) := by
  refine ⟨rResizable, rfl, fun U V w hw hU hV => ⟨?_, ?_⟩⟩
  · intro base sp₂ Δ k_client x hx hfr h1 hfit_client
    have hx_lib0 : (P.rDataOf x).Bounded w := rBounded_rDataOf hP hx
    let x_u : RData rSuccinct :=
      castRData (rSuccinct_eq_const U V w U).symm (P.rDataOf x)
    have hx_lib : x_u.Bounded w :=
      castRData_bounded (rSuccinct_eq_const U V w U).symm hx_lib0
    have hfr_lib : x_u.frontier = base + sp₂ + Δ := hfr
    obtain ⟨y_sh, _, hy_sh_bdd, hy_sh_fr, _, _, _⟩ :=
      shrinkTailWordsCode_exec (U := U) (V := V) (N := U) hx_lib (Δ := Δ) (by omega)
    have hfr2 : x_u.frontier - Δ = base + sp₂ := by omega
    rw [hfr2] at hy_sh_fr
    obtain ⟨x_sh, x_re, _, hx_sh_fr, _, hx_re_bdd, hx_re_fr, _, hx_re_pre, hx_re_zero⟩ :=
      shrink_and_reuse_in_place (U := U) (V := V) (N := U) hx_lib hfr_lib h1 hfit_client
    let y_sh_r : RData rResizable := castRData (rSuccinct_eq_const U V w U) y_sh
    let x_re_r : RData rResizable := castRData (rSuccinct_eq_const U V w U) x_re
    refine ⟨P.rStateOf y_sh_r, P.rStateOf x_re_r,
      rBounded_rStateOf hP (castRData_bounded (rSuccinct_eq_const U V w U) hy_sh_bdd), ?_,
      rBounded_rStateOf hP (castRData_bounded (rSuccinct_eq_const U V w U) hx_re_bdd), ?_, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf, y_sh_r, castRData]
      rw [hP.rFrontier_mk, hy_sh_fr]
    · dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
      rw [hP.rFrontier_mk, hx_re_fr]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
      rw [hP.rMem_mk]
      exact hx_re_pre a ha
    · intro a ha1 ha2
      dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
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
        Fits w (base + Succinct.space U V w N) := by
      intro N hN
      rw [← maxEpochCap_map_dynamicOpOf hP] at hN
      have h1 := hfit_abs N hN
      rw [hP.activeEpochWords_eq, absActiveEpochWords_eq, activeEpochWords_eq_space] at h1
      exact h1
    have hmach := unbounded_seq_machine_expected_amortized hw hU hV hx₀_lib hfr₀_lib
      ops_lib hfit_lib hv_lib
    dsimp only at hmach
    obtain ⟨_, _, _, ν_lib, _, _, _, hsupp_mach⟩ := hmach
    obtain ⟨p, hp⟩ := ν_lib.support_nonempty
    obtain ⟨hrep_dict, hpre_dict, hout_dict, _⟩ := hsupp_mach p hp
    let n_init_final := runEpochInit V (Dynamic.empty U) 0 ops_lib
    let N_final := targetCap U n_init_final
    let x_dict : RData rSuccinct :=
      ⟨p.2.regs, p.2.mem, base + Succinct.space U V w N_final⟩
    have hNf_le : N_final ≤ maxEpochCap V (Dynamic.empty U) 0 ops_lib :=
      targetCap_runEpochInit_le_maxEpochCap V (Dynamic.empty U) 0 ops_lib
    have hfit_Nf : Fits w (base + Succinct.space U V w N_final) := hfit_lib N_final hNf_le
    have hw2 : 2 ≤ w := two_le_w_of_fits_space hfit_Nf
    have h1 : Fits w 1 :=
      lt_of_lt_of_le (by decide : 1 < 2 ^ 2) (Nat.pow_le_pow_right two_pos hw2)
    obtain ⟨y_de, _, hy_de_bdd, hy_de_fr, _, _, _, hde_caller⟩ :=
      deallocSuccinctCode_exec hrep_dict.1 rfl hrep_dict.2.2.2.1
    obtain ⟨x_reused, _, hx_re_bdd, hfr_re, _, _, hx_re_mem, hzero_re⟩ :=
      allocWordsCode_exec hy_de_bdd hy_de_fr h1 hfit_client
    let x_dict_r : RData rResizable := castRData (rSuccinct_eq_const U V w N_final) x_dict
    let y_de_r : RData rResizable := castRData (rSuccinct_eq_const U V w N_final) y_de
    let x_re_r : RData rResizable := castRData (rSuccinct_eq_const U V w N_final) x_reused
    dsimp only
    rw [runEpochInit_map_dynamicOpOf hP (V := V)]
    refine ⟨P.rStateOf x_dict_r, P.rStateOf y_de_r, P.rStateOf x_re_r,
      rBounded_rStateOf hP (castRData_bounded (rSuccinct_eq_const U V w N_final) hrep_dict.1),
      ?_, ?_, ?_, ?_,
      rBounded_rStateOf hP (castRData_bounded (rSuccinct_eq_const U V w N_final) hy_de_bdd), ?_,
      rBounded_rStateOf hP (castRData_bounded (rSuccinct_eq_const U V w N_final) hx_re_bdd),
      ?_, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf, x_dict_r, x_dict, castRData]
      rw [hP.rFrontier_mk, hP.activeEpochWords_eq, absActiveEpochWords_eq,
        activeEpochWords_eq_space]
      rfl
    · dsimp only [DynamicDictPresentation.rStateOf, x_dict_r, x_dict, castRData]
      rw [hP.rRegs_mk]
      have h0 : (⟨0, by decide⟩ : Fin rResizable).cast (rSuccinct_eq_const U V w N_final).symm =
          baseReg := Fin.ext rfl
      rw [h0]
      exact hrep_dict.2.2.2.1
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rRegs_mk, seqOutputCorrect_map_dynamicOpOf hP]
      exact hout_dict
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf, x_dict_r, x_dict, castRData]
      rw [hP.rMem_mk]
      exact hpre_dict a ha
    · dsimp only [DynamicDictPresentation.rStateOf, y_de_r, castRData]
      rw [hP.rFrontier_mk, hy_de_fr]
    · dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
      rw [hP.rFrontier_mk, hfr_re]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
      rw [hP.rMem_mk, hx_re_mem, hde_caller a ha]
      exact hpre_dict a ha
    · intro a ha1 ha2
      dsimp only [DynamicDictPresentation.rStateOf, x_re_r, castRData]
      rw [hP.rMem_mk]
      exact hzero_re a (by simp only [Block.mem_footprint, Block.Owns]; omega)

end ComplexityAbstracts.ResizableSuccinctDictionaryBridge
