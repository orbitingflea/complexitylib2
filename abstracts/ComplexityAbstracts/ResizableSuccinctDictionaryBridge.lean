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
For every universe `U`, value bound `V`, and word width `w` with `0 < w` and `U < 2 ^ w`, there
exist uniform `O(1)` constants `rebuildUnitCost, resizableChargeVal : ℕ` such that for any
operation sequence `ops : List (P.DynamicOp U)` satisfying `P.ValidDictSeq V (emptyDict U) ops`
(no capacity cap `n_max`), at the resulting state `s_final = P.runDict (emptyDict U) ops` with live
key count `n_final` and epoch capacity `N_final = min (2 * n_init_final) U`:
1. `n_final ≤ N_final ≤ 4 * n_final` (`EpochValid`), `N_final ≤ U`, and all stored values are
   `< V`;
2. The active word footprint `absActiveEpochWords U V w N_final n_final` is at most
   `succinctWords 1227 213 U V w n_final` words, and in bits at most
   `optBits U V n_final + 1227 * n_final * logLogFactor n_final + 214 * w` bits;
3. Across the entire sequence `ops`, the accumulated epoch potential is bounded by
   `ops.length * resizableChargeVal`. -/
theorem bridge_unbounded_seq_expected_amortized
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∀ (U V w : ℕ),
      0 < w →
      U < 2 ^ w →
      ∃ (rebuildUnitCost resizableChargeVal : ℕ),
        ∀ ops : List (P.DynamicOp U),
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
              1227 * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + w - 1) / w + 213 ∧
          w * P.activeEpochWords U V w N_final n_final ≤
            (Nat.clog 2 (U.choose n_final) + n_final * Nat.clog 2 V) +
              1227 * n_final * Nat.clog 2 (Nat.clog 2 (max n_final 4)) + 214 * w ∧
          2 * rebuildUnitCost * ((n_final - n_init_final) + (n_init_final - n_final)) ≤
            ops.length * resizableChargeVal := by
  intro U V w hw hU
  refine ⟨ResizableSuccinct.rebuildUnitCost U V w, ResizableSuccinct.resizableChargeVal U V w,
    fun ops hv_abs => ?_⟩
  obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
  have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
    (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
      hv_abs
  have hmain := unbounded_seq_expected_amortized (V := V) hw hU ops_lib hv_lib
  dsimp only at hmain ⊢
  rw [runDict_map_dynamicOpOf hP (V := V) (n_max := U),
    runEpochInit_map_dynamicOpOf hP (V := V), List.length_map,
    hP.activeEpochWords_eq, absActiveEpochWords_eq]
  exact hmain

/-- **Client Subroutine Memory-Reuse Bridge Theorem (`bridge_shrink_and_reuse_in_place` and
`bridge_subroutine_client_reuse_released_memory`):**
1. **Partial tail contraction and reuse (`shrink_and_reuse_in_place`):** When deletions reduce a
   dictionary's active item footprint from `base + sp₂ + Δ` by `Δ` words to `base + sp₂`, executing
   `shrinkTailWordsCode` (`2` instructions) followed by a client allocation `growTailWordsCode`
   (`4 * k_client + 8` instructions under demonic `DemonicGrow`) produces `x_shrunk, x_reused` with
   `P.rFrontier x_shrunk = base + sp₂`, `P.rFrontier x_reused = base + sp₂ + k_client` (reusing the
   released addresses `[base + sp₂, ...)`), `P.RBounded w x_reused`, preserved prefix
   `[0, base + sp₂)`, and zeroed client slice `[base + sp₂, base + sp₂ + k_client)`.
2. **Full dictionary lifecycle and memory reuse (`subroutine_client_reuse_released_memory`):**
   Executing the dictionary over any valid sequence `ops` at `[base, base + absEpochSpace U V w U)`,
   deallocating via `deallocSuccinctCode` (`3` instructions, `.shrink`), and allocating `k_client`
   words for a subsequent client via `allocWordsCode` (`4 * k_client + 8` instructions under
   demonic `DemonicGrow`) produces `x_dict, x_dealloc, x_reused` with
   `P.rFrontier x_dict = base + absEpochSpace U V w U`, `P.rFrontier x_dealloc = base`, and
   `P.rFrontier x_reused = base + k_client`—reusing `[base, base + k_client)` while preserving all
   caller memory `< base`. -/
theorem bridge_dictionary_client_memory_reuse
    (P : DynamicDictPresentation) (hP : DynamicDictLaws P) :
    ∀ (U V w : ℕ),
      0 < w →
      U < 2 ^ w →
      V < 2 ^ w →
      ∃ r : ℕ,
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
          base + P.activeEpochWords U V w U U < 2 ^ w →
          base + k_client < 2 ^ w →
          P.RBounded w x₀ →
          P.rFrontier x₀ = base →
          P.ValidDictSeq V (DynamicDictPresentation.emptyDict U) ops →
          ∃ x_dict x_dealloc x_reused : P.RState r,
            P.RBounded w x_dict ∧
            P.rFrontier x_dict = base + P.activeEpochWords U V w U U ∧
            (∀ a < base, P.rMem x_dict a = P.rMem x₀ a) ∧
            P.RBounded w x_dealloc ∧
            P.rFrontier x_dealloc = base ∧
            P.RBounded w x_reused ∧
            P.rFrontier x_reused = base + k_client ∧
            (∀ a < base, P.rMem x_reused a = P.rMem x₀ a) ∧
            (∀ a, base ≤ a → a < base + k_client → P.rMem x_reused a = 0)) := by
  intro U V w hw hU hV
  refine ⟨rSuccinct U V w U, ?_, ?_⟩
  · intro base sp₂ Δ k_client x hx hfr h1 hfit_client
    have hx_lib : (P.rDataOf x).Bounded w := rBounded_rDataOf hP hx
    have hfr_lib : (P.rDataOf x).frontier = base + sp₂ + Δ := hfr
    obtain ⟨y_sh, _, hy_sh_bdd, hy_sh_fr, _, _, _⟩ :=
      shrinkTailWordsCode_exec (U := U) (V := V) (N := U) hx_lib (Δ := Δ) (by omega)
    have hfr2 : (P.rDataOf x).frontier - Δ = base + sp₂ := by omega
    rw [hfr2] at hy_sh_fr
    obtain ⟨x_sh, x_re, _, hx_sh_fr, _, hx_re_bdd, hx_re_fr, _, hx_re_pre, hx_re_zero⟩ :=
      shrink_and_reuse_in_place (U := U) (V := V) (N := U) hx_lib hfr_lib h1 hfit_client
    refine ⟨P.rStateOf y_sh, P.rStateOf x_re, rBounded_rStateOf hP hy_sh_bdd, ?_,
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
  · intro base k_client x₀ ops hfit_dict hfit_client hx₀ hfr₀ hv_abs
    rw [hP.activeEpochWords_eq, absActiveEpochWords_eq, activeEpochWords_eq_space] at hfit_dict ⊢
    obtain ⟨ops_lib, rfl⟩ := dynamicOps_surjective P ops
    have hv_lib : (Dynamic.spec U V U).ValidHistory (Dynamic.empty U) ops_lib :=
      (validDictSeq_map_dynamicOpOf_unbounded hP (DynamicDictPresentation.emptyDict U) ops_lib).mp
        hv_abs
    have hx₀_lib : (P.rDataOf x₀).Bounded w := rBounded_rDataOf hP hx₀
    obtain ⟨x_alloc, ν₀, ν_final, T_ops, _, _, _, _, hsupp⟩ :=
      subroutine_client_reuse_released_memory hw le_rfl hU hV hfit_dict hfit_client ops_lib
        hx₀_lib hfr₀ hv_lib
    obtain ⟨p, hp⟩ := ν_final.support_nonempty
    obtain ⟨hrep_dict, hpre_dict, x_dealloc, x_reused, he_de, hfr_de, _, hx_re_bdd, hfr_re,
      hpre_re, hzero_re⟩ := hsupp p hp
    let x_dict : RData (rSuccinct U V w U) :=
      ⟨p.2.regs, p.2.mem, base + Succinct.space U V w U⟩
    obtain ⟨y_de, _, hy_de_bdd, hy_de_fr, _, _, _, _⟩ :=
      deallocSuccinctCode_exec hrep_dict.1 rfl hrep_dict.2.2.2.1
    refine ⟨P.rStateOf x_dict, P.rStateOf y_de, P.rStateOf x_reused,
      rBounded_rStateOf hP hrep_dict.1, ?_, ?_,
      rBounded_rStateOf hP hy_de_bdd, ?_,
      rBounded_rStateOf hP hx_re_bdd, ?_, ?_, ?_⟩
    · dsimp only [DynamicDictPresentation.rStateOf, x_dict]
      rw [hP.rFrontier_mk]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hpre_dict a ha
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hy_de_fr]
    · dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rFrontier_mk, hfr_re]
    · intro a ha
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hpre_re a ha
    · intro a ha1 ha2
      dsimp only [DynamicDictPresentation.rStateOf]
      rw [hP.rMem_mk]
      exact hzero_re a (by simp only [Block.mem_footprint, Block.Owns]; omega)

end ComplexityAbstracts.ResizableSuccinctDictionaryBridge
