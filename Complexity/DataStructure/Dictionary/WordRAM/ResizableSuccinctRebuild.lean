/-
Copyright (c) 2026 Representation-Cost Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Representation-Cost Contributors
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.ResizableSuccinctCompaction

/-!
# Machine-Level Active-Slot Extraction and Epoch Rebuild for the Resizable Succinct Dictionary

This module eliminates pure-Lean universe scanning (`buildOps s (List.finRange U)`) by proving that
all `n` live `(u, v)` key-value pairs of a compacted epoch (`CompactedRep`) are extracted directly
from the `n` dense active slots `d ∈ [0, n)` in machine memory `x.mem`:
1. **Direct $O(1)$ Bucket-Owner & Logical-Slot Inversion (`ownerBucketOfDense`,
   `logicalIdxOfDense`):** maps each dense slot `d < n` via `GlobalMeta` (`gmSlabOwnerBIdx`,
   `gmSlabOwnerSIdx`, `gmTailOwnerIdx`) and `DenseToTail` (`compD2TAt`) to its unique active bucket
   slot `(b, j)`.
2. **Exact Feistel Key & Value Reconstruction (`reconstructKeyAt`, `reconstructValAt`):** recovers
   `u = feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b q < U` and `v < V` at each `d < n`.
3. **Machine-Extracted Rebuild Sequence (`extractRebuildOps`, `extractRebuildOps_spec`) &
   Compaction Packing (`compactedOfVirt`, `compactedRep_of_succinctRep`):** scans `d ∈ List.range n`
   to reconstruct `s_abs` from `Dynamic.empty U` in `n` steps and packs virtual `Succinct.Rep`
   states into live `CompactedRep` states with frontier `base + compactedEpochWords U V w N n`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.Probability
open Finset

/-! ## Section 1: Direct $O(1)$ Bucket-Owner and Logical-Slot Inversion on Dense Indices -/

/-- Recover the owning Feistel bucket `b < numBuckets N` of dense index `d < S + T` from
`GlobalMeta` (`gm`) and `DenseToTail` (`d2t`). -/
@[expose]
def ownerBucketOfDense (N S : ℕ) (gm d2t : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then 0
  else if d < S then gm (gmSlabOwnerBIdx N (d / slabSize N))
  else gm (gmTailOwnerIdx N (d2t (d % maxTailItems N))) / tailCapPerBucket N

/-- Recover the logical within-bucket slot index `j < bCount N gm b` of dense index `d < S + T`. -/
@[expose]
def logicalIdxOfDense (N S : ℕ) (gm d2t : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < S then
    let p := d / slabSize N
    let rem := d % slabSize N
    gm (gmSlabOwnerSIdx N p) * slabSize N + (slabSize N - 1 - rem)
  else
    let t := d2t (d % maxTailItems N)
    let desc := gm (gmTailOwnerIdx N t)
    let b := desc / tailCapPerBucket N
    let r := desc % tailCapPerBucket N
    gm (gmQIdx b) * slabSize N + r

/-- **Forward inversion theorem (`ownerBucketOfDense_lt_and_slotOf`):**
Under `SlotStoreInv N gm` and `TailDenseBijection N S T t2d d2t`, every dense index `d < S + T`
maps via `(ownerBucketOfDense, logicalIdxOfDense)` to a valid active bucket slot `(b, j)` with
`b < numBuckets N`, `j < bCount N gm b`, and `denseOfVirt N S T t2d (slotOf N gm b j) = d`. -/
theorem ownerBucketOfDense_lt_and_slotOf {N S T : ℕ} {gm t2d d2t : ℕ → ℕ}
    (hslot : SlotStoreInv N gm)
    (hS : S = if bucketBits N = 0 then gm 0 else gm 0 * slabSize N)
    (hT : T = if bucketBits N = 0 then 0 else gm 1)
    (hbij : TailDenseBijection N S T t2d d2t)
    {d : ℕ} (hd : d < S + T) :
    let b := ownerBucketOfDense N S gm d2t d
    let j := logicalIdxOfDense N S gm d2t d
    b < numBuckets N ∧
    j < bCount N gm b ∧
    denseOfVirt N S T t2d (slotOf N gm b j) = d := by
  intro b j
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hB1 : numBuckets N = 1 := by simp [numBuckets, hb0]
    have hS0 : S = gm 0 := by simp [hS, hb0]
    have hT0 : T = 0 := by simp [hT, hb0]
    have hb_eq : b = 0 := by simp [b, ownerBucketOfDense, hb0]
    have hj_eq : j = d := by simp [j, logicalIdxOfDense, hb0]
    refine ⟨by omega, ?_, ?_⟩
    · unfold bCount
      simp only [hb0, hb_eq, hj_eq, ↓reduceIte]
      omega
    · unfold denseOfVirt slotOf
      simp [hb0, hj_eq]
  · have hb_ne : bucketBits N ≠ 0 := by omega
    have hS_eq : S = gm 0 * slabSize N := by simp [hS, hb_ne]
    have hT_eq : T = gm 1 := by simp [hT, hb_ne]
    have hK : 0 < slabSize N := slabSize_pos N
    have hslab := hslot.multi_slab hb_pos
    have htail := hslot.multi_tail hb_pos
    have htot := hslot.multi_total_le hb_pos
    have hSN : S + T ≤ N := by omega
    by_cases hdS : d < S
    · -- Dense slab index `d < S = gm 0 * slabSize N`
      have hp_lt : d / slabSize N < gm 0 := by
        rw [hS_eq] at hdS
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hrem_lt : d % slabSize N < slabSize N := Nat.mod_lt d hK
      have hvalid := hslab.owner_valid (d / slabSize N) (by rwa [← hslab.nslabs_eq])
      dsimp only at hvalid
      obtain ⟨hb_lt, hs_lt, hptr_eq⟩ := hvalid
      have hb_def : b = gm (gmSlabOwnerBIdx N (d / slabSize N)) := by
        simp [b, ownerBucketOfDense, hb_ne, hdS]
      have hj_def : j = gm (gmSlabOwnerSIdx N (d / slabSize N)) * slabSize N +
          (slabSize N - 1 - d % slabSize N) := by
        simp [j, logicalIdxOfDense, hb_ne, hdS]
      have hj_slab : j < gm (gmQIdx b) * slabSize N := by
        rw [hj_def, hb_def]
        have h1 : (gm (gmSlabOwnerSIdx N (d / slabSize N)) + 1) * slabSize N ≤
            gm (gmQIdx (gm (gmSlabOwnerBIdx N (d / slabSize N)))) * slabSize N :=
          Nat.mul_le_mul_right _ hs_lt
        rw [Nat.add_one_mul] at h1
        omega
      have hj_bc : j < bCount N gm b := by
        unfold bCount
        rw [ite_eq_right hb_ne, ite_eq_left (by omega)]
        omega
      have hj_div : j / slabSize N = gm (gmSlabOwnerSIdx N (d / slabSize N)) := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hj_mod : j % slabSize N = slabSize N - 1 - d % slabSize N := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hslot_eq : slotOf N gm b j = d := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_left hj_slab, hj_div, hj_mod]
        have hptr' : slabPtrOf N gm b (gm (gmSlabOwnerSIdx N (d / slabSize N))) =
            d / slabSize N := by
          rw [hb_def]
          exact hptr_eq
        rw [hptr']
        have hdiv_mod := Nat.div_add_mod d (slabSize N)
        have hcomm : (d / slabSize N) * slabSize N = slabSize N * (d / slabSize N) :=
          Nat.mul_comm _ _
        omega
      refine ⟨by omega, hj_bc, ?_⟩
      rw [hslot_eq, denseOfVirt_slab t2d hdS]
    · -- Dense tail index `S ≤ d < S + T`
      have hd_ge : S ≤ d := by omega
      have ht_lt_T : d2t (d % maxTailItems N) < T := hbij.d2t_lt d hd_ge hd
      have ht_lt_gm1 : d2t (d % maxTailItems N) < gm 1 := by omega
      have ht2d_eq : t2d (d2t (d % maxTailItems N)) = d := hbij.t2d_d2t d hd_ge hd
      set t := d2t (d % maxTailItems N)
      set desc := gm (gmTailOwnerIdx N t)
      have hvalid := htail.owner_valid t (by rwa [← htail.ntails_eq])
      dsimp only at hvalid
      obtain ⟨hb_lt, hr_lt, hptr_eq⟩ := hvalid
      have hb_def : b = desc / tailCapPerBucket N := by
        simp [b, ownerBucketOfDense, hb_ne, hdS, t, desc]
      have hb_lt' : b < numBuckets N := by rw [hb_def]; exact hb_lt
      have hr_lt' : desc % tailCapPerBucket N < gm (gmRIdx b) := by rw [hb_def]; exact hr_lt
      have hj_def : j = gm (gmQIdx b) * slabSize N + desc % tailCapPerBucket N := by
        simp [j, logicalIdxOfDense, hb_ne, hdS, t, desc, hb_def]
      have hj_not_slab : ¬(j < gm (gmQIdx b) * slabSize N) := by omega
      have hj_bc : j < bCount N gm b := by
        unfold bCount
        rw [ite_eq_right hb_ne, ite_eq_left hb_lt']
        omega
      have hj_sub : j - gm (gmQIdx b) * slabSize N = desc % tailCapPerBucket N := by omega
      have hdesc_eq : b * tailCapPerBucket N + desc % tailCapPerBucket N = desc := by
        rw [hb_def, Nat.mul_comm, Nat.div_add_mod]
      have hslot_eq : slotOf N gm b j = N - 1 - t := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_right hj_not_slab, hj_sub]
        unfold gmTailPtrIdx
        rw [hdesc_eq]
        change N - 1 - gm (gmTailPtrFlatIdx N (gm (gmTailOwnerIdx N t))) = N - 1 - t
        rw [hptr_eq]
      refine ⟨hb_lt', hj_bc, ?_⟩
      rw [hslot_eq, denseOfVirt_tail hb_pos hSN t2d ht_lt_T, ht2d_eq]

/-- For every active bucket slot `(b, j)` with `b < numBuckets N` and `j < bCount N gm b`,
`virtOfDense N S T d2t (denseOfVirt N S T t2d (slotOf N gm b j)) = slotOf N gm b j`. -/
theorem virtOfDense_denseOfVirt_slotOf {N S T : ℕ} {gm t2d d2t : ℕ → ℕ}
    (hslot : SlotStoreInv N gm)
    (hS : S = if bucketBits N = 0 then gm 0 else gm 0 * slabSize N)
    (hT : T = if bucketBits N = 0 then 0 else gm 1)
    (hbij : TailDenseBijection N S T t2d d2t)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    virtOfDense N S T d2t (denseOfVirt N S T t2d (slotOf N gm b j)) = slotOf N gm b j := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · simp [virtOfDense, denseOfVirt, hb0]
  · have hb_ne : bucketBits N ≠ 0 := by omega
    have hS_eq : S = gm 0 * slabSize N := by simp [hS, hb_ne]
    have hT_eq : T = gm 1 := by simp [hT, hb_ne]
    have hK : 0 < slabSize N := slabSize_pos N
    have hslab := hslot.multi_slab hb_pos
    have htail := hslot.multi_tail hb_pos
    have htot := hslot.multi_total_le hb_pos
    have hSN : S + T ≤ N := by omega
    unfold bCount at hj
    simp only [hb_ne, ↓reduceIte, hb] at hj
    by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
    · have hs_lt : j / slabSize N < gm (gmQIdx b) :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
        rw [hslab.nslabs_eq]
        exact hslab.ptr_lt b hb _ hs_lt
      have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
      have hslot_lt_S : slotOf N gm b j < S := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_left hj_slab, hS_eq]
        have h1 : (slabPtrOf N gm b (j / slabSize N) + 1) * slabSize N ≤ gm 0 * slabSize N :=
          Nat.mul_le_mul_right _ hp_lt
        rw [Nat.add_one_mul] at h1
        omega
      exact virtOfDense_denseOfVirt_slab t2d d2t hslot_lt_S
    · have hr_lt : j - gm (gmQIdx b) * slabSize N < gm (gmRIdx b) := by omega
      have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < T := by
        rw [hT_eq, htail.ntails_eq]
        exact htail.ptr_lt b hb _ hr_lt
      have hslot_eq : slotOf N gm b j =
          N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_right hj_slab]
      rw [hslot_eq]
      exact virtOfDense_denseOfVirt_tail hbij hb_pos hSN ht_lt

/-- **Reverse mapping theorem (`denseOfVirt_slotOf_lt_and_inv`):**
Under `SlotStoreInv N gm` and `TailDenseBijection N S T t2d d2t`, for every active bucket slot
`(b, j)` with `b < numBuckets N` and `j < bCount N gm b`, the dense index
`d = denseOfVirt N S T t2d (slotOf N gm b j)` satisfies `d < S + T` and
`slotOf N gm (ownerBucketOfDense N S gm d2t d) (logicalIdxOfDense N S gm d2t d) =
slotOf N gm b j`. -/
theorem denseOfVirt_slotOf_lt_and_inv {N S T : ℕ} {gm t2d d2t : ℕ → ℕ}
    (hslot : SlotStoreInv N gm)
    (hS : S = if bucketBits N = 0 then gm 0 else gm 0 * slabSize N)
    (hT : T = if bucketBits N = 0 then 0 else gm 1)
    (hbij : TailDenseBijection N S T t2d d2t)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    let d := denseOfVirt N S T t2d (slotOf N gm b j)
    d < S + T ∧
    ownerBucketOfDense N S gm d2t d = b ∧
    logicalIdxOfDense N S gm d2t d = j := by
  intro d
  have hd_lt : d < S + T := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · have hb_eq : b = 0 := by simp [numBuckets, hb0] at hb; omega
      subst hb_eq
      unfold bCount at hj
      simp only [hb0, ↓reduceIte] at hj
      simp [d, denseOfVirt, slotOf, hb0, hS, hT, hj]
    · have hb_ne : bucketBits N ≠ 0 := by omega
      have hS_eq : S = gm 0 * slabSize N := by simp [hS, hb_ne]
      have hT_eq : T = gm 1 := by simp [hT, hb_ne]
      have hK : 0 < slabSize N := slabSize_pos N
      have hslab := hslot.multi_slab hb_pos
      have htail := hslot.multi_tail hb_pos
      have htot := hslot.multi_total_le hb_pos
      have hSN : S + T ≤ N := by omega
      unfold bCount at hj
      simp only [hb_ne, ↓reduceIte, hb] at hj
      by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
      · have hs_lt : j / slabSize N < gm (gmQIdx b) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
          rw [hslab.nslabs_eq]
          exact hslab.ptr_lt b hb _ hs_lt
        have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
        have hslot_lt_S : slotOf N gm b j < S := by
          unfold slotOf
          rw [ite_eq_right hb_ne, ite_eq_left hj_slab, hS_eq]
          have h1 : (slabPtrOf N gm b (j / slabSize N) + 1) * slabSize N ≤ gm 0 * slabSize N :=
            Nat.mul_le_mul_right _ hp_lt
          rw [Nat.add_one_mul] at h1
          omega
        have hd_eq : d = slotOf N gm b j := denseOfVirt_slab t2d hslot_lt_S
        omega
      · have hr_lt : j - gm (gmQIdx b) * slabSize N < gm (gmRIdx b) := by omega
        have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < T := by
          rw [hT_eq, htail.ntails_eq]
          exact htail.ptr_lt b hb _ hr_lt
        have hslot_eq : slotOf N gm b j =
            N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
          unfold slotOf
          rw [ite_eq_right hb_ne, ite_eq_right hj_slab]
        change denseOfVirt N S T t2d (slotOf N gm b j) < S + T
        rw [hslot_eq]
        exact denseOfVirt_lt_of_tail hbij hb_pos hSN ht_lt
  obtain ⟨hb'_lt, hj'_lt, hd_round⟩ :=
    ownerBucketOfDense_lt_and_slotOf hslot hS hT hbij hd_lt
  set b' := ownerBucketOfDense N S gm d2t d
  set j' := logicalIdxOfDense N S gm d2t d
  have hvirt_eq :
      virtOfDense N S T d2t (denseOfVirt N S T t2d (slotOf N gm b' j')) =
      virtOfDense N S T d2t (denseOfVirt N S T t2d (slotOf N gm b j)) :=
    congrArg (virtOfDense N S T d2t) hd_round
  rw [virtOfDense_denseOfVirt_slotOf hslot hS hT hbij hb'_lt hj'_lt,
    virtOfDense_denseOfVirt_slotOf hslot hS hT hbij hb hj] at hvirt_eq
  have hinj := (slotOf_lt_and_injective hslot).2 b' hb'_lt j' hj'_lt b hb j hj hvirt_eq
  exact ⟨hd_lt, hinj.1, hinj.2⟩

/-- For every dense index `d < S + T`, `virtOfDense N S T d2t d` equals the virtual slot
`slotOf N gm (ownerBucketOfDense N S gm d2t d) (logicalIdxOfDense N S gm d2t d)`. -/
theorem virtOfDense_eq_slotOf_owner {N S T : ℕ} {gm t2d d2t : ℕ → ℕ}
    (hslot : SlotStoreInv N gm)
    (hS : S = if bucketBits N = 0 then gm 0 else gm 0 * slabSize N)
    (hT : T = if bucketBits N = 0 then 0 else gm 1)
    (hbij : TailDenseBijection N S T t2d d2t)
    {d : ℕ} (hd : d < S + T) :
    virtOfDense N S T d2t d =
      slotOf N gm (ownerBucketOfDense N S gm d2t d) (logicalIdxOfDense N S gm d2t d) := by
  obtain ⟨hb_lt, hj_lt, hd_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot hS hT hbij hd
  conv_lhs => rw [← hd_eq]
  exact virtOfDense_denseOfVirt_slotOf hslot hS hT hbij hb_lt hj_lt

/-! ## Section 2: Key-Value Reconstruction from Compacted Memory & Completeness over `s_abs` -/

/-- Reconstruct the key `u = feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b q` stored at
dense index `d < n` in compacted memory `mem`. -/
@[expose]
noncomputable def reconstructKeyAt (U V w N n base : ℕ) (θ : QuotHashSeed U N)
    (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  let gm := compGmAt base U w N mem
  let d2t := compD2TAt base U w N mem
  let S := if bucketBits N = 0 then gm 0 else gm 0 * slabSize N
  let b := ownerBucketOfDense N S gm d2t d
  let q := compQuotAt (base + offCompItems U w N) U V w N n mem d
  feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b q

/-- Read the value `v = compValAt (base + offCompItems U w N) U V w N n mem d` stored at dense
index `d < n` in compacted memory `mem`. -/
@[expose]
def reconstructValAt (U V w N n base : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  compValAt (base + offCompItems U w N) U V w N n mem d

/-- Under the active-epoch invariant of `CompactedRep`, every dense slot `d < n` reconstructs a
valid key `reconstructKeyAt ... d < U` and value `reconstructValAt ... d < V` present in `s_abs`,
and `reconstructKeyAt` is injective on `[0, n)` and surjective onto `Dynamic.dom s_abs`. -/
theorem reconstructKeyAt_spec {U V w N n base : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dynamic.State U} {x_virt : Memory.State} {mem : ℕ → ℕ}
    (hvals : ∀ u v, s_abs u = some v → v < V)
    (hinv : DictStateInv U V w N base θ s_abs x_virt)
    (hgm : gmAt base U V w N (hashSpace U w N) x_virt.mem = compGmAt base U w N mem)
    (hST : (if bucketBits N = 0 then compGmAt base U w N mem 0
      else compGmAt base U w N mem 0 * slabSize N) +
      (if bucketBits N = 0 then 0 else compGmAt base U w N mem 1) = n)
    (hbij : TailDenseBijection N
      (if bucketBits N = 0 then compGmAt base U w N mem 0
        else compGmAt base U w N mem 0 * slabSize N)
      (if bucketBits N = 0 then 0 else compGmAt base U w N mem 1)
      (compT2DAt base U w N mem) (compD2TAt base U w N mem))
    (hq : ∀ d < n, compQuotAt (base + offCompItems U w N) U V w N n mem d =
      quotAt base U w N (hashSpace U w N) x_virt.mem
        (virtOfDense N
          (if bucketBits N = 0 then compGmAt base U w N mem 0
            else compGmAt base U w N mem 0 * slabSize N)
          (if bucketBits N = 0 then 0 else compGmAt base U w N mem 1)
          (compD2TAt base U w N mem) d))
    (hv : ∀ d < n, compValAt (base + offCompItems U w N) U V w N n mem d =
      valAt base U V w N (hashSpace U w N) x_virt.mem
        (virtOfDense N
          (if bucketBits N = 0 then compGmAt base U w N mem 0
            else compGmAt base U w N mem 0 * slabSize N)
          (if bucketBits N = 0 then 0 else compGmAt base U w N mem 1)
          (compD2TAt base U w N mem) d))
    (hNU : N ≤ U) :
    (∀ d < n, ∃ (hu : reconstructKeyAt U V w N n base θ mem d < U),
      s_abs ⟨reconstructKeyAt U V w N n base θ mem d, hu⟩ =
        some (reconstructValAt U V w N n base mem d) ∧
      reconstructValAt U V w N n base mem d < V) ∧
    (∀ d₁ < n, ∀ d₂ < n,
      reconstructKeyAt U V w N n base θ mem d₁ =
      reconstructKeyAt U V w N n base θ mem d₂ → d₁ = d₂) ∧
    (∀ u : Fin U, (s_abs u).isSome →
      ∃ d < n, reconstructKeyAt U V w N n base θ mem d = u.val) := by
  obtain ⟨L, hbucket⟩ := hinv.hbucket
  set gm := compGmAt base U w N mem
  set t2d := compT2DAt base U w N mem
  set d2t := compD2TAt base U w N mem
  set S := if bucketBits N = 0 then gm 0 else gm 0 * slabSize N
  set T := if bucketBits N = 0 then 0 else gm 1
  have hslot : SlotStoreInv N gm := hgm ▸ hbucket.hslot
  have h1 : ∀ d < n, ∃ (hu : reconstructKeyAt U V w N n base θ mem d < U),
      s_abs ⟨reconstructKeyAt U V w N n base θ mem d, hu⟩ =
        some (reconstructValAt U V w N n base mem d) ∧
      reconstructValAt U V w N n base mem d < V := by
    intro d hd
    have hd_ST : d < S + T := by omega
    obtain ⟨hb_lt, hj_lt, _⟩ :=
      ownerBucketOfDense_lt_and_slotOf hslot rfl rfl hbij hd_ST
    have hvirt_eq := virtOfDense_eq_slotOf_owner hslot rfl rfl hbij hd_ST
    set b := ownerBucketOfDense N S gm d2t d
    set j := logicalIdxOfDense N S gm d2t d
    have hj_lt' : j < bCount N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b := by
      rwa [hgm]
    have hg_eq : slotOf N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b j =
        slotOf N gm b j := by rw [hgm]
    have hq_d : quotAt base U w N (hashSpace U w N) x_virt.mem
        (slotOf N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b j) =
        compQuotAt (base + offCompItems U w N) U V w N n mem d := by
      rw [hq d hd, hvirt_eq, hg_eq]
    have hv_d : valAt base U V w N (hashSpace U w N) x_virt.mem
        (slotOf N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b j) =
        reconstructValAt U V w N n base mem d := by
      unfold reconstructValAt
      rw [hv d hd, hvirt_eq, hg_eq]
    have hmap := hbucket.hmap_some b hb_lt j hj_lt'
    rw [hq_d, hv_d] at hmap
    unfold bucketMapOfState at hmap
    split_ifs at hmap with hcond
    exact ⟨hcond.1, hmap, hvals _ _ hmap⟩
  refine ⟨h1, ?_, ?_⟩
  · -- Injectivity on `d₁, d₂ < n`
    intro d₁ hd₁ d₂ hd₂ heq
    obtain ⟨hb₁_lt, hj₁_lt, hd₁_eq⟩ :=
      ownerBucketOfDense_lt_and_slotOf hslot rfl rfl hbij (by omega : d₁ < S + T)
    obtain ⟨hb₂_lt, hj₂_lt, hd₂_eq⟩ :=
      ownerBucketOfDense_lt_and_slotOf hslot rfl rfl hbij (by omega : d₂ < S + T)
    have hvirt₁ := virtOfDense_eq_slotOf_owner hslot rfl rfl hbij (by omega : d₁ < S + T)
    have hvirt₂ := virtOfDense_eq_slotOf_owner hslot rfl rfl hbij (by omega : d₂ < S + T)
    set b₁ := ownerBucketOfDense N S gm d2t d₁
    set j₁ := logicalIdxOfDense N S gm d2t d₁
    set b₂ := ownerBucketOfDense N S gm d2t d₂
    set j₂ := logicalIdxOfDense N S gm d2t d₂
    have hfb₁ := feistelBucket_feistelReconstruct (hValOfSeed U N θ) hb₁_lt
      (compQuotAt (base + offCompItems U w N) U V w N n mem d₁)
    have hfb₂ := feistelBucket_feistelReconstruct (hValOfSeed U N θ) hb₂_lt
      (compQuotAt (base + offCompItems U w N) U V w N n mem d₂)
    change feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b₁
        (compQuotAt (base + offCompItems U w N) U V w N n mem d₁) =
      feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b₂
        (compQuotAt (base + offCompItems U w N) U V w N n mem d₂) at heq
    have hb_eq : b₁ = b₂ := by rw [← hfb₁.1, heq, hfb₂.1]
    have hq_eq : compQuotAt (base + offCompItems U w N) U V w N n mem d₁ =
        compQuotAt (base + offCompItems U w N) U V w N n mem d₂ := by
      rw [← hfb₁.2, heq, hfb₂.2]
    have hj₁_lt' : j₁ < bCount N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b₁ := by
      rwa [hgm]
    have hj₂_lt' : j₂ < bCount N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b₁ := by
      rw [hgm, hb_eq]; exact hj₂_lt
    have hq₁ : quotAt base U w N (hashSpace U w N) x_virt.mem
        (slotOf N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b₁ j₁) =
        compQuotAt (base + offCompItems U w N) U V w N n mem d₁ := by
      rw [hq d₁ hd₁, hvirt₁, hgm]
    have hq₂ : quotAt base U w N (hashSpace U w N) x_virt.mem
        (slotOf N (gmAt base U V w N (hashSpace U w N) x_virt.mem) b₁ j₂) =
        compQuotAt (base + offCompItems U w N) U V w N n mem d₂ := by
      rw [hq d₂ hd₂, hvirt₂, hgm, hb_eq]
    have hj_eq : j₁ = j₂ :=
      hbucket.hnodup_q b₁ hb₁_lt j₁ hj₁_lt' j₂ hj₂_lt' (by rw [hq₁, hq₂, hq_eq])
    rw [← hd₁_eq, ← hd₂_eq, hb_eq, hj_eq]
  · -- Surjectivity onto `Dynamic.dom s_abs`
    intro u hu
    set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    set q := keyQuotient (bucketBits N) u.val
    have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
    have hbm_eq : bucketMapOfState U N (hValOfSeed U N θ) s_abs b q = s_abs u :=
      bucketMapOfState_feistelBucket hNU (hValOfSeed U N θ) s_abs u
    have hdom := (hbucket.hmap_dom b hb_lt q).mp (by rwa [hbm_eq])
    obtain ⟨j, hj_lt', hq_j⟩ := hdom
    have hj_lt : j < bCount N gm b := by rwa [← hgm]
    obtain ⟨hd_lt, hb_inv, _⟩ :=
      denseOfVirt_slotOf_lt_and_inv hslot rfl rfl hbij hb_lt hj_lt
    have hvirt_inv := virtOfDense_denseOfVirt_slotOf hslot rfl rfl hbij hb_lt hj_lt
    set d := denseOfVirt N S T t2d (slotOf N gm b j)
    have hd_n : d < n := by omega
    refine ⟨d, hd_n, ?_⟩
    have hq_d : compQuotAt (base + offCompItems U w N) U V w N n mem d = q := by
      rw [hq d hd_n, hvirt_inv, ← hgm, hq_j]
    unfold reconstructKeyAt
    dsimp only
    rw [hb_inv, hq_d]
    exact feistelReconstruct_feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val

/-! ## Section 3: Machine-Extracted Rebuild Sequence (`extractRebuildOps`) & Specification -/

/-- Build the list of `.insert (uFn d) (vFn d)` operations for a list of dense indices `L`. -/
@[expose]
def extractOpsAux {U : ℕ} (uFn : ℕ → Fin U) (vFn : ℕ → ℕ) : List ℕ → List (Dynamic.Op U)
  | [] => []
  | d :: ds => .insert (uFn d) (vFn d) :: extractOpsAux uFn vFn ds

@[simp]
theorem extractOpsAux_length {U : ℕ} (uFn : ℕ → Fin U) (vFn : ℕ → ℕ) (L : List ℕ) :
    (extractOpsAux uFn vFn L).length = L.length := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [extractOpsAux, ih]

/-- Agreement invariant for `extractOpsAux`: `s₀` is `none` on all keys `uFn d` for `d ∈ L`, and
agrees with `s_abs` on all keys outside `{uFn d | d ∈ L}`. -/
@[expose] def DenseRestrictOut {U : ℕ} (uFn : ℕ → Fin U) (L : List ℕ) (s₀ s_abs : Dynamic.State U) :
    Prop :=
  (∀ d ∈ L, s₀ (uFn d) = none) ∧ (∀ u : Fin U, (∀ d ∈ L, uFn d ≠ u) → s₀ u = s_abs u)

theorem extractOpsAux_spec_aux {U V N n : ℕ} {s_abs : Dynamic.State U}
    {uFn : ℕ → Fin U} {vFn : ℕ → ℕ}
    (hinj : ∀ d₁ < n, ∀ d₂ < n, uFn d₁ = uFn d₂ → d₁ = d₂)
    (hcard : (Dynamic.dom s_abs).card ≤ N) :
    ∀ (L : List ℕ) (_hnd : L.Nodup) (_hlt : ∀ d ∈ L, d < n)
      (_hspec : ∀ d ∈ L, s_abs (uFn d) = some (vFn d) ∧ vFn d < V) (s₀ : Dynamic.State U)
      (_hro : DenseRestrictOut uFn L s₀ s_abs),
      ((Dynamic.spec U V N).run s₀ (extractOpsAux uFn vFn L)).1 = s_abs ∧
      (Dynamic.spec U V N).ValidHistory s₀ (extractOpsAux uFn vFn L) ∧
      (Dynamic.dom s₀).card + L.length = (Dynamic.dom s_abs).card
  | [], _, _, _, s₀, hro => by
    have heq : s₀ = s_abs := funext fun u => hro.2 u (fun _ hd => absurd hd List.not_mem_nil)
    subst heq
    exact ⟨rfl, trivial, by simp⟩
  | d :: ds, hnd, hlt, hspec, s₀, hro => by
    obtain ⟨hd_not, hnd_ds⟩ := List.nodup_cons.mp hnd
    have hd_lt : d < n := hlt d List.mem_cons_self
    have hlt_ds : ∀ x ∈ ds, x < n := fun x hx => hlt x (List.mem_cons_of_mem d hx)
    have hspec_ds : ∀ x ∈ ds, s_abs (uFn x) = some (vFn x) ∧ vFn x < V :=
      fun x hx => hspec x (List.mem_cons_of_mem d hx)
    have hs₀_d : s₀ (uFn d) = none := hro.1 d List.mem_cons_self
    obtain ⟨hs_d, hv_d⟩ := hspec d List.mem_cons_self
    let s₁ : Dynamic.State U := Function.update s₀ (uFn d) (some (vFn d))
    have hro₁ : DenseRestrictOut uFn ds s₁ s_abs := by
      refine ⟨fun x hx => ?_, fun u hu => ?_⟩
      · have hne_u : uFn x ≠ uFn d := fun h =>
          hd_not (hinj d hd_lt x (hlt_ds x hx) h.symm ▸ hx)
        dsimp only [s₁]
        rw [Function.update_of_ne hne_u]
        exact hro.1 x (List.mem_cons_of_mem d hx)
      · by_cases hdu : u = uFn d
        · subst hdu
          simp [s₁, hs_d]
        · dsimp only [s₁]
          rw [Function.update_of_ne hdu]
          exact hro.2 u fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx_ds
            · exact Ne.symm hdu
            · exact hu x hx_ds
    have hdom₁ : (Dynamic.dom s₁).card = (Dynamic.dom s₀).card + 1 :=
      Dictionary.card_dom_insert_eq_of_eq_none hs₀_d (vFn d)
    obtain ⟨hrun, hvh, hlen⟩ :=
      extractOpsAux_spec_aux hinj hcard ds hnd_ds hlt_ds hspec_ds s₁ hro₁
    have hlt_N : (Dynamic.dom s₀).card < N := by omega
    have hval_d : (Dynamic.spec U V N).valid s₀ (.insert (uFn d) (vFn d)) := ⟨Or.inl hlt_N, hv_d⟩
    refine ⟨hrun, ⟨hval_d, hvh⟩, ?_⟩
    simp only [List.length_cons]
    omega

/-- **Machine-extracted rebuild sequence (`extractRebuildOps`):**
Scans the `n` dense slots `d ∈ List.range n` in compacted memory `mem`, reconstructing each key
`reconstructKeyAt U V w N_old n base θ mem d` via one-round Feistel inversion and reading each
value `reconstructValAt U V w N_old n base mem d`. -/
@[expose]
noncomputable def extractRebuildOps (U V w N_old n base : ℕ) (θ : QuotHashSeed U N_old)
    (mem : ℕ → ℕ) (hU : 0 < U) : List (Dynamic.Op U) :=
  extractOpsAux
    (fun d => ⟨reconstructKeyAt U V w N_old n base θ mem d % U, Nat.mod_lt _ hU⟩)
    (reconstructValAt U V w N_old n base mem)
    (List.range n)

/-- **Specification of `extractRebuildOps` (`extractRebuildOps_spec`):**
Given any machine state `x` satisfying `CompactedRep U V w N_old n base s_abs x` and any target
capacity `N ≥ n`, there exists a seed `θ : QuotHashSeed U N_old` such that the machine-extracted
operation list `extractRebuildOps U V w N_old n base θ x.mem hU`:
1. Reconstructs `s_abs` from `Dynamic.empty U`:
   `((Dynamic.spec U V N).run (Dynamic.empty U) (extractRebuildOps ...)).1 = s_abs`,
2. Is a valid operation history under `Dynamic.spec U V N`, and
3. Has exact length `n = (Dynamic.dom s_abs).card`. -/
theorem extractRebuildOps_spec {r U V w N_old N n base : ℕ}
    {s_abs : Dynamic.State U} {x : RData r}
    (hU : 0 < U)
    (hrep : CompactedRep U V w N_old n base s_abs x)
    (hnN : n ≤ N) :
    ∃ θ : QuotHashSeed U N_old,
      ((Dynamic.spec U V N).run (Dynamic.empty U)
        (extractRebuildOps U V w N_old n base θ x.mem hU)).1 = s_abs ∧
      (Dynamic.spec U V N).ValidHistory (Dynamic.empty U)
        (extractRebuildOps U V w N_old n base θ x.mem hU) ∧
      (extractRebuildOps U V w N_old n base θ x.mem hU).length = n := by
  have hcard_N : (Dynamic.dom s_abs).card ≤ N := by rw [hrep.card_eq]; exact hnN
  rcases hrep.epoch_inv with ⟨rfl, rfl⟩ | ⟨_, _, _, hNU, x_virt, θ, hinv, _, _, hgm, hST,
    hbij, hq, hv⟩
  · -- Empty epoch (`n = 0, N_old = 0`): `List.range 0 = []` and `s_abs = Dynamic.empty U`
    refine ⟨default, ?_, trivial, rfl⟩
    have hempty : Dynamic.empty U = s_abs := by
      have hdom0 : Dynamic.dom s_abs = ∅ := Finset.card_eq_zero.mp hrep.card_eq
      funext u
      rcases hsu : s_abs u with _ | v
      · rfl
      · have hu_mem : u ∈ Dynamic.dom s_abs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ u, by simp [hsu]⟩
        rw [hdom0] at hu_mem
        exact absurd hu_mem (Finset.notMem_empty u)
    exact hempty
  · -- Nonempty epoch (`1 ≤ n ≤ N_old ≤ 4 * n, N_old ≤ U`)
    refine ⟨θ, ?_⟩
    obtain ⟨h1, hinj, hsurj⟩ :=
      reconstructKeyAt_spec hrep.vals_lt hinv hgm hST hbij hq hv hNU
    let uFn : ℕ → Fin U := fun d =>
      ⟨reconstructKeyAt U V w N_old n base θ x.mem d % U, Nat.mod_lt _ hU⟩
    let vFn : ℕ → ℕ := reconstructValAt U V w N_old n base x.mem
    have huFn_val : ∀ d < n, (uFn d).val = reconstructKeyAt U V w N_old n base θ x.mem d := by
      intro d hd
      obtain ⟨hu_lt, _⟩ := h1 d hd
      exact Nat.mod_eq_of_lt hu_lt
    have hspec : ∀ d < n, s_abs (uFn d) = some (vFn d) ∧ vFn d < V := by
      intro d hd
      obtain ⟨hu_lt, hs_eq, hv_lt⟩ := h1 d hd
      have hfin : uFn d = ⟨reconstructKeyAt U V w N_old n base θ x.mem d, hu_lt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hu_lt)
      rw [hfin]
      exact ⟨hs_eq, hv_lt⟩
    have hinj' : ∀ d₁ < n, ∀ d₂ < n, uFn d₁ = uFn d₂ → d₁ = d₂ := by
      intro d₁ hd₁ d₂ hd₂ heq
      have hval := congrArg Fin.val heq
      rw [huFn_val d₁ hd₁, huFn_val d₂ hd₂] at hval
      exact hinj d₁ hd₁ d₂ hd₂ hval
    have hro : DenseRestrictOut uFn (List.range n) (Dynamic.empty U) s_abs := by
      refine ⟨fun _ _ => rfl, fun u hu => ?_⟩
      rcases hsu : s_abs u with _ | v
      · rfl
      · obtain ⟨d, hd_lt, hd_eq⟩ := hsurj u (by simp [hsu])
        have hfin : uFn d = u := Fin.ext (by rw [huFn_val d hd_lt, hd_eq])
        exact absurd hfin (hu d (List.mem_range.mpr hd_lt))
    obtain ⟨hrun, hvh, _⟩ := extractOpsAux_spec_aux hinj' hcard_N (List.range n) List.nodup_range
      (fun _ hd => List.mem_range.mp hd) (fun d hd => hspec d (List.mem_range.mp hd))
      (Dynamic.empty U) hro
    exact ⟨hrun, hvh, by simp [extractRebuildOps]⟩

/-! ## Section 4: Canonical `TailDenseBijection` & Compaction Packing from `Succinct.Rep` -/

/-- Canonical tail-to-dense map `t ↦ S + t` for `t < T` (`0` otherwise). -/
@[expose]
def canonT2D (S T t : ℕ) : ℕ :=
  if t < T then S + t else 0

/-- Canonical dense-to-tail map `r ↦ (r + maxTailItems N - S % maxTailItems N) % maxTailItems N`
for active tail offsets `< T` (`0` otherwise). -/
@[expose]
def canonD2T (N S T r : ℕ) : ℕ :=
  if T = 0 then 0
  else if r < maxTailItems N then
    let t := (r + maxTailItems N - S % maxTailItems N) % maxTailItems N
    if t < T then t else 0
  else 0

theorem canonD2T_canonT2D_mod {S M t : ℕ} (ht : t < M) :
    ((S + t) % M + M - S % M) % M = t := by
  have hM : 0 < M := by omega
  have hs_lt : S % M < M := Nat.mod_lt S hM
  have hadd_mod : (S + t) % M = (S % M + t) % M := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt ht]
  rw [hadd_mod]
  by_cases hlt : S % M + t < M
  · rw [Nat.mod_eq_of_lt hlt]
    have heq : S % M + t + M - S % M = t + M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · have hsub_lt : S % M + t - M < M := by omega
    have hmod_sub : (S % M + t) % M = S % M + t - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub_lt]
    rw [hmod_sub]
    have heq : S % M + t - M + M - S % M = t := by omega
    rw [heq, Nat.mod_eq_of_lt ht]

/-- Whenever `T ≤ maxTailItems N`, `canonT2D S T` and `canonD2T N S T` form a valid
`TailDenseBijection N S T`. -/
theorem tailDenseBijection_canon {N S T : ℕ} (hTM : T ≤ maxTailItems N) :
    TailDenseBijection N S T (canonT2D S T) (canonD2T N S T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [canonT2D, ht, ↓reduceIte]
    omega
  · intro t ht
    have hT0 : T ≠ 0 := by omega
    have htM : t < maxTailItems N := lt_of_lt_of_le ht hTM
    have hM_pos : 0 < maxTailItems N := by omega
    have hmod_lt : (S + t) % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    have hinv := canonD2T_canonT2D_mod (S := S) htM
    simp [canonT2D, canonD2T, ht, hT0, hmod_lt, hinv]
  · intro d hd1 hd2
    have hT0 : T ≠ 0 := by omega
    set t := d - S
    have ht_lt : t < T := by omega
    have hd_eq : d = S + t := by omega
    have htM : t < maxTailItems N := lt_of_lt_of_le ht_lt hTM
    have hM_pos : 0 < maxTailItems N := by omega
    have hmod_lt : d % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    have hinv :
        ((d % maxTailItems N + maxTailItems N - S % maxTailItems N) % maxTailItems N) = t := by
      rw [hd_eq]
      exact canonD2T_canonT2D_mod (S := S) htM
    simp [canonD2T, hT0, hmod_lt, hinv, ht_lt]
  · intro d hd1 hd2
    have hT0 : T ≠ 0 := by omega
    set t := d - S
    have ht_lt : t < T := by omega
    have hd_eq : d = S + t := by omega
    have htM : t < maxTailItems N := lt_of_lt_of_le ht_lt hTM
    have hM_pos : 0 < maxTailItems N := by omega
    have hmod_lt : d % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    have hinv :
        ((d % maxTailItems N + maxTailItems N - S % maxTailItems N) % maxTailItems N) = t := by
      rw [hd_eq]
      exact canonD2T_canonT2D_mod (S := S) htM
    simp only [canonD2T, hT0, ↓reduceIte, hmod_lt, hinv, ht_lt, canonT2D]
    omega

theorem canonT2D_lt_globalPtrBits {N S T : ℕ} (hST : S + T ≤ N) (t : ℕ) :
    canonT2D S T t < 2 ^ globalPtrBits N := by
  have hN := lt_two_pow_globalPtrBits N
  unfold canonT2D
  split_ifs <;> omega

theorem canonD2T_lt_globalPtrBits {N S T : ℕ} (hST : S + T ≤ N) (r : ℕ) :
    canonD2T N S T r < 2 ^ globalPtrBits N := by
  have hN := lt_two_pow_globalPtrBits N
  unfold canonD2T
  dsimp only
  split_ifs <;> omega

/-- Pack `f 0, ..., f (k - 1)` into a bit-packed array at `base_arr` with element width `b`. -/
@[expose]
def packPackedArray (base_arr b w : ℕ) (f : ℕ → ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, mem => mem
  | k + 1, mem =>
      writePacked base_arr b w (packPackedArray base_arr b w f k mem) k (f k)

theorem readPacked_packPackedArray {base_arr b w : ℕ} (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i, f i < 2 ^ b) :
    ∀ (k : ℕ) (mem : ℕ → ℕ) {idx : ℕ}, idx < k →
      readPacked base_arr b w (packPackedArray base_arr b w f k mem) idx = f idx
  | 0, _, _, hidx => absurd hidx (Nat.not_lt_zero _)
  | k + 1, mem, idx, hidx => by
      unfold packPackedArray
      by_cases heq : idx = k
      · subst heq
        exact readPacked_writePacked_self base_arr b w _ idx (hf idx)
      · rw [readPacked_writePacked_of_ne hw _ heq]
        exact readPacked_packPackedArray hw f hf k mem (by omega)

theorem packPackedArray_outside {base_arr len b w : ℕ} (hw : 0 < w) (f : ℕ → ℕ) :
    ∀ (k : ℕ), k ≤ len → ∀ (mem : ℕ → ℕ) {addr : ℕ},
      ¬(base_arr ≤ addr ∧ addr < base_arr + packedWords len b w) →
      packPackedArray base_arr b w f k mem addr = mem addr
  | 0, _, _, _, _ => rfl
  | k + 1, hk, mem, addr, haddr => by
      unfold packPackedArray
      rw [writePacked_outside hw _ (by omega : k < len) (f k) haddr]
      exact packPackedArray_outside hw f k (by omega) mem haddr

theorem packPackedArray_lt_two_pow {base_arr b w : ℕ} (hw : 0 < w) (hbw : b ≤ w) (f : ℕ → ℕ) :
    ∀ (k : ℕ) {mem : ℕ → ℕ}, (∀ addr, mem addr < 2 ^ w) →
      ∀ addr, packPackedArray base_arr b w f k mem addr < 2 ^ w
  | 0, _, hmem, addr => hmem addr
  | k + 1, mem, hmem, addr => by
      unfold packPackedArray
      exact writePacked_lt_two_pow hw hbw (packPackedArray_lt_two_pow hw hbw f k hmem) k (f k) addr

/-- `writeBitSlice` preserves `< 2 ^ w` on every memory word when `bOff < w` and `k ≤ w`. -/
theorem writeBitSlice_lt_two_pow {base wOff bOff k w : ℕ} (hb : bOff < w) (hkw : k ≤ w)
    {mem : ℕ → ℕ} (hmem : ∀ addr, mem addr < 2 ^ w) (val addr : ℕ) :
    writeBitSlice base wOff bOff k w mem val addr < 2 ^ w := by
  unfold writeBitSlice
  set k₀ := min k (w - bOff)
  set k₁ := k - k₀
  set old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  set old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hmem₁ : ∀ a, mem₁ a < 2 ^ w := by
    intro a
    dsimp only [mem₁]
    by_cases ha : a = base + wOff
    · subst ha
      rw [Function.update_self]
      refine Nat.xor_lt_two_pow (hmem _) (shiftLeft_lt_two_pow_of_lt (a := k₀) ?_ (by omega))
      refine Nat.xor_lt_two_pow ?_ ?_ <;>
      · dsimp only [old₀, val₀]
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by positivity)
    · rw [Function.update_of_ne ha]
      exact hmem a
  by_cases ha : addr = base + wOff + 1
  · subst ha
    rw [Function.update_self]
    refine Nat.xor_lt_two_pow (hmem₁ _) (shiftLeft_lt_two_pow_of_lt (a := k₁) ?_ (by omega))
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  · rw [Function.update_of_ne ha]
    exact hmem₁ addr

/-- Pack `k` interleaved `(qFn d, vFn d)` pairs into `[itemBase, itemBase + compactedItemWords)`. -/
@[expose]
def packCompItems (itemBase U V w N : ℕ) (qFn vFn : ℕ → ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, mem => mem
  | k + 1, mem =>
      writeCompVal itemBase U V w N
        (writeCompQuot itemBase U V w N (packCompItems itemBase U V w N qFn vFn k mem) k (qFn k))
        k (vFn k)

theorem compQuotAt_packCompItems {itemBase U V w N n : ℕ} (hw : 0 < w) (qFn vFn : ℕ → ℕ)
    (hq : ∀ d, qFn d < 2 ^ quotientBits U N) :
    ∀ (k : ℕ), k ≤ n → ∀ (mem : ℕ → ℕ) {d : ℕ}, d < k →
      compQuotAt itemBase U V w N n (packCompItems itemBase U V w N qFn vFn k mem) d = qFn d
  | 0, _, _, _, hd => absurd hd (Nat.not_lt_zero _)
  | k + 1, hk, mem, d, hd => by
      unfold packCompItems
      rw [compQuotAt_writeCompVal hw]
      by_cases heq : d = k
      · subst heq
        exact compQuotAt_writeCompQuot_self _ (by omega) (hq d)
      · rw [compQuotAt_writeCompQuot_of_ne hw _ heq]
        exact compQuotAt_packCompItems hw qFn vFn hq k (by omega) mem (by omega)

theorem compValAt_packCompItems {itemBase U V w N n : ℕ} (hw : 0 < w) (qFn vFn : ℕ → ℕ)
    (hv : ∀ d, vFn d < 2 ^ valBits V) :
    ∀ (k : ℕ), k ≤ n → ∀ (mem : ℕ → ℕ) {d : ℕ}, d < k →
      compValAt itemBase U V w N n (packCompItems itemBase U V w N qFn vFn k mem) d = vFn d
  | 0, _, _, _, hd => absurd hd (Nat.not_lt_zero _)
  | k + 1, hk, mem, d, hd => by
      unfold packCompItems
      by_cases heq : d = k
      · subst heq
        exact compValAt_writeCompVal_self _ (by omega) (hv d)
      · rw [compValAt_writeCompVal_of_ne hw _ heq, compValAt_writeCompQuot hw]
        exact compValAt_packCompItems hw qFn vFn hv k (by omega) mem (by omega)

theorem packCompItems_outside {itemBase U V w N n : ℕ} (hw : 0 < w) (qFn vFn : ℕ → ℕ) :
    ∀ (k : ℕ), k ≤ n → ∀ (mem : ℕ → ℕ) {addr : ℕ},
      ¬(itemBase ≤ addr ∧ addr < itemBase + compactedItemWords U V w N n) →
      packCompItems itemBase U V w N qFn vFn k mem addr = mem addr
  | 0, _, _, _, _ => rfl
  | k + 1, hk, mem, addr, haddr => by
      unfold packCompItems
      rw [writeCompVal_outside hw (by omega : k < n) _ haddr,
        writeCompQuot_outside hw (by omega : k < n) _ haddr]
      exact packCompItems_outside hw qFn vFn k (by omega) mem haddr

theorem packCompItems_lt_two_pow {itemBase U V w N : ℕ} (hw : 0 < w)
    (hqw : quotientBits U N ≤ w) (hvw : valBits V ≤ w) (qFn vFn : ℕ → ℕ) :
    ∀ (k : ℕ) {mem : ℕ → ℕ}, (∀ addr, mem addr < 2 ^ w) →
      ∀ addr, packCompItems itemBase U V w N qFn vFn k mem addr < 2 ^ w
  | 0, _, hmem, addr => hmem addr
  | k + 1, mem, hmem, addr => by
      unfold packCompItems writeCompVal writeCompQuot
      exact writeBitSlice_lt_two_pow (bOffV_lt hw) hvw
        (writeBitSlice_lt_two_pow (bOffQ_lt hw) hqw
          (packCompItems_lt_two_pow hw hqw hvw qFn vFn k hmem) (qFn k)) (vFn k) addr

/-- Shifted-base congruence for `readPacked`: if `mem₁ (base₁ + k) = mem₂ (base₂ + k)` for all
`k < packedWords len b w`, then `readPacked base₁ b w mem₁ idx = readPacked base₂ b w mem₂ idx`
for all `idx < len`. -/
theorem readPacked_shift_congr {base₁ base₂ len b w : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ k < packedWords len b w, mem₁ (base₁ + k) = mem₂ (base₂ + k))
    {idx : ℕ} (hidx : idx < len) :
    readPacked base₁ b w mem₁ idx = readPacked base₂ b w mem₂ idx := by
  unfold readPacked
  dsimp only
  have hlt1 : wordOffset b w idx + 1 < packedWords len b w :=
    wordOffset_add_one_lt_packedWords hw hidx
  have h0 : mem₁ (base₁ + wordOffset b w idx) = mem₂ (base₂ + wordOffset b w idx) :=
    h _ (by omega)
  have h1 : mem₁ (base₁ + wordOffset b w idx + 1) = mem₂ (base₂ + wordOffset b w idx + 1) := by
    have := h (wordOffset b w idx + 1) hlt1
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
  rw [h0, h1]

/-- Base memory for an active compacted epoch of capacity `N` and live count `n` at `base`:
preserves caller memory `< base`, writes `(N, n)` at `base, base + 1`, copies the hash table from
`[base, base + hashSpace U w N)` of `mem_y` to `[base + epochHdrWords, base + offCompLM U w N)`,
copies `LocalMeta` and `GlobalMeta` from `[base + offLM U V w N (hashSpace U w N), ...)` of `mem_y`
to `[base + offCompLM U w N, base + offTailToDense U w N)`, and zeroes all other words. -/
@[expose]
def compBaseMem (U V w N n base : ℕ) (mem_y : ℕ → ℕ) (addr : ℕ) : ℕ :=
  if addr < base then mem_y addr
  else if addr = base then N
  else if addr = base + 1 then n
  else if base + epochHdrWords ≤ addr ∧ addr < base + offCompLM U w N then
    mem_y (base + (addr - (base + epochHdrWords)))
  else if base + offCompLM U w N ≤ addr ∧ addr < base + offTailToDense U w N then
    mem_y (base + offLM U V w N (hashSpace U w N) + (addr - (base + offCompLM U w N)))
  else 0

theorem compBaseMem_lt_two_pow {U V w N n base : ℕ} {mem_y : ℕ → ℕ}
    (hmem : ∀ a, mem_y a < 2 ^ w) (hN : N < 2 ^ w) (hn : n < 2 ^ w) (addr : ℕ) :
    compBaseMem U V w N n base mem_y addr < 2 ^ w := by
  unfold compBaseMem
  split_ifs
  · exact hmem _
  · exact hN
  · exact hn
  · exact hmem _
  · exact hmem _
  · exact Nat.two_pow_pos w

theorem compBaseMem_above {U V w N n base : ℕ} (mem_y : ℕ → ℕ) {addr : ℕ}
    (haddr : base + offTailToDense U w N ≤ addr) :
    compBaseMem U V w N n base mem_y addr = 0 := by
  unfold compBaseMem
  have h1 : ¬(addr < base) := by omega
  have h2 : addr ≠ base := by
    unfold offTailToDense offCompGM offCompLM epochHdrWords at haddr; omega
  have h3 : addr ≠ base + 1 := by
    unfold offTailToDense offCompGM offCompLM epochHdrWords at haddr; omega
  have h4 : ¬(base + epochHdrWords ≤ addr ∧ addr < base + offCompLM U w N) := by
    unfold offTailToDense offCompGM at haddr; omega
  have h5 : ¬(base + offCompLM U w N ≤ addr ∧ addr < base + offTailToDense U w N) := by omega
  simp [h1, h2, h3, h4, h5]

theorem compBaseMem_hash {U V w N n base : ℕ} (mem_y : ℕ → ℕ) {i : ℕ}
    (hi : i < hashSpace U w N) :
    compBaseMem U V w N n base mem_y (base + epochHdrWords + i) = mem_y (base + i) := by
  unfold compBaseMem
  have h1 : ¬(base + epochHdrWords + i < base) := by omega
  have h2 : base + epochHdrWords + i ≠ base := by unfold epochHdrWords; omega
  have h3 : base + epochHdrWords + i ≠ base + 1 := by unfold epochHdrWords; omega
  have h4 : base + epochHdrWords ≤ base + epochHdrWords + i ∧
      base + epochHdrWords + i < base + offCompLM U w N := by
    unfold offCompLM; omega
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
  exact congrArg mem_y (by omega)

theorem compBaseMem_lm_gm {U V w N n base : ℕ} (mem_y : ℕ → ℕ) {j : ℕ}
    (hj : j < 9 * lmSubWords N w + packedWords (globalMetaLen N) (globalPtrBits N) w) :
    compBaseMem U V w N n base mem_y (base + offCompLM U w N + j) =
      mem_y (base + offLM U V w N (hashSpace U w N) + j) := by
  unfold compBaseMem
  have h1 : ¬(base + offCompLM U w N + j < base) := by omega
  have h2 : base + offCompLM U w N + j ≠ base := by
    unfold offCompLM epochHdrWords; omega
  have h3 : base + offCompLM U w N + j ≠ base + 1 := by
    unfold offCompLM epochHdrWords; omega
  have h4 : ¬(base + epochHdrWords ≤ base + offCompLM U w N + j ∧
      base + offCompLM U w N + j < base + offCompLM U w N) := by omega
  have h5 : base + offCompLM U w N ≤ base + offCompLM U w N + j ∧
      base + offCompLM U w N + j < base + offTailToDense U w N := by
    unfold offTailToDense offCompGM; omega
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left h5]
  exact congrArg mem_y (by omega)

/-- Full compacted memory constructed from a virtual `Succinct` memory `mem_y`. -/
@[expose]
def compactedMemOfVirt (U V w N n base : ℕ) (mem_y : ℕ → ℕ) : ℕ → ℕ :=
  let gm := gmAt base U V w N (hashSpace U w N) mem_y
  let S := if bucketBits N = 0 then gm 0 else gm 0 * slabSize N
  let T := if bucketBits N = 0 then 0 else gm 1
  let qFn := fun d =>
    quotAt base U w N (hashSpace U w N) mem_y (virtOfDense N S T (canonD2T N S T) d)
  let vFn := fun d =>
    valAt base U V w N (hashSpace U w N) mem_y (virtOfDense N S T (canonD2T N S T) d)
  let mem₀ := compBaseMem U V w N n base mem_y
  let mem₁ := packPackedArray (base + offTailToDense U w N) (globalPtrBits N) w
    (canonT2D S T) (maxTailItems N) mem₀
  let mem₂ := packPackedArray (base + offDenseToTail U w N) (globalPtrBits N) w
    (canonD2T N S T) (maxTailItems N) mem₁
  packCompItems (base + offCompItems U w N) U V w N qFn vFn n mem₂

/-- Construct the compacted machine state `RData r` with live frontier
`base + compactedEpochWords U V w N n` from a virtual `Succinct` state `y : Data r`. -/
@[expose]
def compactedOfVirt {r : ℕ} (U V w N n base : ℕ) (y : Data r) : RData r :=
  if n = 0 then
    ⟨y.regs, fun addr => if addr < base then y.mem addr else 0, base + 4⟩
  else
    ⟨y.regs, compactedMemOfVirt U V w N n base y.mem, base + compactedEpochWords U V w N n⟩

/-- When `n = 0` and `N = 0` (`s_abs = Dynamic.empty U`), `compactedOfVirt U V w 0 0 base y`
satisfies `CompactedRep U V w 0 0 base s_abs` with live frontier `base + 4`. -/
theorem compactedRep_of_zero {r U V w base : ℕ} {s_abs : Dynamic.State U} {y : Data r}
    (hy_bdd : y.Bounded w) (hfit : Fits w (base + 4))
    (hcard : (Dynamic.dom s_abs).card = 0) :
    CompactedRep U V w 0 0 base s_abs (compactedOfVirt U V w 0 0 base y) ∧
    (compactedOfVirt U V w 0 0 base y).regs = y.regs ∧
    (∀ a < base, (compactedOfVirt U V w 0 0 base y).mem a = y.mem a) := by
  have hvals : ∀ u v, s_abs u = some v → v < V := by
    intro u v hsu
    have hu_mem : u ∈ Dynamic.dom s_abs :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ u, by simp [hsu]⟩
    rw [Finset.card_eq_zero.mp hcard] at hu_mem
    exact absurd hu_mem (Finset.notMem_empty u)
  have hdef : compactedOfVirt U V w 0 0 base y =
      ⟨y.regs, fun addr => if addr < base then y.mem addr else 0, base + 4⟩ := rfl
  rw [hdef]
  refine ⟨⟨?_, ?_, ?_, ?_, hcard, hvals, Or.inl ⟨rfl, rfl⟩⟩, rfl, fun a ha => by simp [ha]⟩
  · refine ⟨⟨hy_bdd.1, fun addr => ?_⟩, hfit, fun addr haddr => ?_⟩
    · dsimp only [RData.toData]
      split_ifs
      · exact hy_bdd.2 addr
      · exact Nat.two_pow_pos w
    · dsimp only at haddr ⊢
      exact ite_eq_right (by omega)
  · simp [compactedEpochWords]
  · simp
  · simp

/-- **Compaction theorem (`compactedRep_of_succinctRep`):**
For any valid active epoch (`1 ≤ n ∧ n ≤ N ∧ N ≤ 4 * n ∧ N ≤ U`) and any virtual state
`y : Data rSuccinct` satisfying `Succinct.Rep U V w N base θ s_abs y`, the compacted state
`compactedOfVirt U V w N n base y` satisfies `CompactedRep U V w N n base s_abs`, preserves
`y.regs` and caller memory `< base`, and has live frontier
`base + compactedEpochWords U V w N n`. -/
theorem compactedRep_of_succinctRep {U V w N n base : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hN4 : N ≤ 4 * n) (hNU : N ≤ U)
    (hfit : Fits w (base + compactedEpochWords U V w N n))
    {s_abs : Dynamic.State U} (hcard : (Dynamic.dom s_abs).card = n)
    (hvals : ∀ u v, s_abs u = some v → v < V)
    {θ : QuotHashSeed U N} {y : Data rSuccinct}
    (hrep_y : Succinct.Rep U V w N base θ s_abs y) :
    CompactedRep U V w N n base s_abs (compactedOfVirt U V w N n base y) ∧
    (compactedOfVirt U V w N n base y).regs = y.regs ∧
    (∀ a < base, (compactedOfVirt U V w N n base y).mem a = y.mem a) := by
  have hn_ne : n ≠ 0 := by omega
  rcases hrep_y with ⟨hy_bdd, _, _, _, _, hdict⟩
  obtain ⟨L, hbucket⟩ := hdict.hbucket
  have hslot : SlotStoreInv N (gmAt base U V w N (hashSpace U w N) y.mem) := hbucket.hslot
  set gm_y := gmAt base U V w N (hashSpace U w N) y.mem
  set S := if bucketBits N = 0 then gm_y 0 else gm_y 0 * slabSize N
  set T := if bucketBits N = 0 then 0 else gm_y 1
  have hST_n : S + T = n := by
    have htot := hdict.htot
    unfold totalSlots at htot
    change (if bucketBits N = 0 then gm_y 0 else gm_y 0 * slabSize N + gm_y 1) =
      (Dynamic.dom s_abs).card at htot
    rw [hcard] at htot
    dsimp only [S, T]
    split_ifs at htot ⊢ <;> omega
  have hST_N : S + T ≤ N := by omega
  have hTM : T ≤ maxTailItems N := by
    dsimp only [T]
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · simp [hb0]
    · rw [ite_eq_right (by omega)]
      exact (hslot.multi_tail hb_pos).ntails_le
  set qFn := fun d =>
    quotAt base U w N (hashSpace U w N) y.mem (virtOfDense N S T (canonD2T N S T) d)
  set vFn := fun d =>
    valAt base U V w N (hashSpace U w N) y.mem (virtOfDense N S T (canonD2T N S T) d)
  set mem₀ := compBaseMem U V w N n base y.mem
  set mem₁ := packPackedArray (base + offTailToDense U w N) (globalPtrBits N) w
    (canonT2D S T) (maxTailItems N) mem₀
  set mem₂ := packPackedArray (base + offDenseToTail U w N) (globalPtrBits N) w
    (canonD2T N S T) (maxTailItems N) mem₁
  set mem₃ := packCompItems (base + offCompItems U w N) U V w N qFn vFn n mem₂
  have hN_lt : N < 2 ^ w := lt_of_le_of_lt hNU hU
  have hn_lt : n < 2 ^ w := lt_of_le_of_lt hnN hN_lt
  have hgpb_le : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hNU hU
  have hqb_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow (le_of_lt hU)
  have hvb_le : valBits V ≤ w := valBits_le_of_le_pow (le_of_lt hV)
  have hmem₀_lt : ∀ a, mem₀ a < 2 ^ w := compBaseMem_lt_two_pow hy_bdd.2 hN_lt hn_lt
  have hmem₁_lt : ∀ a, mem₁ a < 2 ^ w :=
    packPackedArray_lt_two_pow hw hgpb_le (canonT2D S T) (maxTailItems N) hmem₀_lt
  have hmem₂_lt : ∀ a, mem₂ a < 2 ^ w :=
    packPackedArray_lt_two_pow hw hgpb_le (canonD2T N S T) (maxTailItems N) hmem₁_lt
  have hmem₃_lt : ∀ a, mem₃ a < 2 ^ w :=
    packCompItems_lt_two_pow hw hqb_le hvb_le qFn vFn n hmem₂_lt
  have hmem₃_below : ∀ addr < base + offTailToDense U w N, mem₃ addr = mem₀ addr := by
    intro addr haddr
    have h3 : mem₃ addr = mem₂ addr :=
      packCompItems_outside hw qFn vFn n le_rfl mem₂
        (by unfold offCompItems offDenseToTail; omega)
    have h2 : mem₂ addr = mem₁ addr :=
      packPackedArray_outside hw (canonD2T N S T) (maxTailItems N) le_rfl mem₁
        (by unfold offDenseToTail; omega)
    have h1 : mem₁ addr = mem₀ addr :=
      packPackedArray_outside hw (canonT2D S T) (maxTailItems N) le_rfl mem₀ (by omega)
    rw [h3, h2, h1]
  have hmem₃_above : ∀ addr, base + compactedEpochWords U V w N n ≤ addr → mem₃ addr = 0 := by
    intro addr haddr
    have hcew : compactedEpochWords U V w N n =
        offCompItems U w N + compactedItemWords U V w N n := by
      simp [compactedEpochWords, hn_ne]
    rw [hcew] at haddr
    have h3 : mem₃ addr = mem₂ addr :=
      packCompItems_outside hw qFn vFn n le_rfl mem₂ (by omega)
    have h2 : mem₂ addr = mem₁ addr :=
      packPackedArray_outside hw (canonD2T N S T) (maxTailItems N) le_rfl mem₁
        (by unfold offCompItems at haddr; omega)
    have h1 : mem₁ addr = mem₀ addr :=
      packPackedArray_outside hw (canonT2D S T) (maxTailItems N) le_rfl mem₀
        (by unfold offCompItems offDenseToTail at haddr; omega)
    rw [h3, h2, h1]
    exact compBaseMem_above y.mem (by unfold offCompItems offDenseToTail at haddr; omega)
  have hcomp_eq : compactedOfVirt U V w N n base y =
      ⟨y.regs, mem₃, base + compactedEpochWords U V w N n⟩ := by
    simp [compactedOfVirt, hn_ne, compactedMemOfVirt, gm_y, S, T, qFn, vFn, mem₀, mem₁, mem₂, mem₃]
  refine ⟨?_, by simp [hcomp_eq], fun a ha => ?_⟩
  · rw [hcomp_eq]
    have h4 : 4 ≤ offTailToDense U w N := by
      unfold offTailToDense offCompGM offCompLM epochHdrWords; omega
    refine ⟨⟨⟨hy_bdd.1, hmem₃_lt⟩, hfit, hmem₃_above⟩, rfl, ?_, ?_, hcard, hvals, Or.inr ?_⟩
    · dsimp only; rw [hmem₃_below base (by omega)]; simp [mem₀, compBaseMem]
    · dsimp only; rw [hmem₃_below (base + 1) (by omega)]; simp [mem₀, compBaseMem]
    · have hgm_eq : compGmAt base U w N mem₃ = gm_y := by
        funext idx
        unfold compGmAt gm_y gmAt
        split_ifs with hidx
        · refine readPacked_shift_congr hw (fun k hk => ?_) hidx
          have hlt_t2d : base + offCompGM U w N + k < base + offTailToDense U w N := by
            unfold offTailToDense; omega
          rw [hmem₃_below _ hlt_t2d]
          have h1 : base + offCompGM U w N + k =
              base + offCompLM U w N + (9 * lmSubWords N w + k) := by
            unfold offCompGM; omega
          have h2 : base + offGM U V w N (hashSpace U w N) + k =
              base + offLM U V w N (hashSpace U w N) + (9 * lmSubWords N w + k) := by
            unfold offGM; omega
          rw [h1, h2]
          exact compBaseMem_lm_gm y.mem (by omega)
        · rfl
      refine ⟨hn1, hnN, hN4, hNU, Realization.memoryState Succinct.frontierReg y,
        θ, hdict, ?_, ?_, hgm_eq.symm, ?_⟩
      · intro i hi
        change y.mem (base + i) = mem₃ (base + epochHdrWords + i)
        rw [hmem₃_below (base + epochHdrWords + i)
          (by unfold offTailToDense offCompGM offCompLM; omega)]
        exact (compBaseMem_hash y.mem hi).symm
      · -- `lmAt = compLmAt`
        funext ⟨c, idx⟩
        unfold lmAt compLmAt
        dsimp only
        split_ifs with hp
        · symm
          refine readPacked_shift_congr hw (fun k hk => ?_) hp.2
          change k < lmSubWords N w at hk
          have hsub : (c + 1) * lmSubWords N w ≤ 9 * lmSubWords N w :=
            Nat.mul_le_mul_right _ hp.1
          rw [Nat.add_one_mul] at hsub
          have hlt_t2d : base + offCompLMSub U w N c + k < base + offTailToDense U w N := by
            unfold offTailToDense offCompGM offCompLMSub; omega
          rw [hmem₃_below _ hlt_t2d]
          have h1 : base + offCompLMSub U w N c + k =
              base + offCompLM U w N + (c * lmSubWords N w + k) := by
            unfold offCompLMSub; omega
          have h2 : base + offLMSub U V w N (hashSpace U w N) c + k =
              base + offLM U V w N (hashSpace U w N) + (c * lmSubWords N w + k) := by
            unfold offLMSub; omega
          change compBaseMem U V w N n base y.mem (base + offCompLMSub U w N c + k) =
            y.mem (base + offLMSub U V w N (hashSpace U w N) c + k)
          rw [h1, h2]
          exact compBaseMem_lm_gm y.mem (by omega)
        · rfl
      · -- `S + T = n`, `TailDenseBijection`, `hq`, `hv`
        have ht2d_eq : compT2DAt base U w N mem₃ = canonT2D S T := by
          funext t
          unfold compT2DAt
          split_ifs with ht
          · have hcongr : readPacked (base + offTailToDense U w N) (globalPtrBits N) w mem₃ t =
                readPacked (base + offTailToDense U w N) (globalPtrBits N) w mem₁ t := by
              refine readPacked_congr hw (fun addr haddr => ?_) ht
              have h3 : mem₃ addr = mem₂ addr :=
                packCompItems_outside hw qFn vFn n le_rfl mem₂
                  (by unfold offCompItems offDenseToTail; omega)
              have h2 : mem₂ addr = mem₁ addr :=
                packPackedArray_outside hw (canonD2T N S T) (maxTailItems N) le_rfl mem₁
                  (by unfold offDenseToTail; omega)
              rw [h3, h2]
            rw [hcongr]
            exact readPacked_packPackedArray hw (canonT2D S T)
              (canonT2D_lt_globalPtrBits hST_N) (maxTailItems N) mem₀ ht
          · unfold canonT2D
            exact (ite_eq_right (by omega)).symm
        have hd2t_eq : compD2TAt base U w N mem₃ = canonD2T N S T := by
          funext r
          unfold compD2TAt
          split_ifs with hr
          · have hcongr : readPacked (base + offDenseToTail U w N) (globalPtrBits N) w mem₃ r =
                readPacked (base + offDenseToTail U w N) (globalPtrBits N) w mem₂ r := by
              refine readPacked_congr hw (fun addr haddr => ?_) hr
              exact packCompItems_outside hw qFn vFn n le_rfl mem₂
                (by unfold offCompItems; omega)
            rw [hcongr]
            exact readPacked_packPackedArray hw (canonD2T N S T)
              (canonD2T_lt_globalPtrBits hST_N) (maxTailItems N) mem₁ hr
          · unfold canonD2T
            simp [hr]
        dsimp only
        rw [hgm_eq, ht2d_eq, hd2t_eq]
        change S + T = n ∧
          TailDenseBijection N S T (canonT2D S T) (canonD2T N S T) ∧
          (∀ d < n, compQuotAt (base + offCompItems U w N) U V w N n mem₃ d = qFn d) ∧
          (∀ d < n, compValAt (base + offCompItems U w N) U V w N n mem₃ d = vFn d)
        refine ⟨hST_n, tailDenseBijection_canon hTM, ?_, ?_⟩
        · intro d hd
          exact compQuotAt_packCompItems hw qFn vFn
            (fun i => quotAt_lt base U w N (hashSpace U w N) y.mem _) n le_rfl mem₂ hd
        · intro d hd
          exact compValAt_packCompItems hw qFn vFn
            (fun i => valAt_lt base U V w N (hashSpace U w N) y.mem _) n le_rfl mem₂ hd
  · rw [hcomp_eq]
    dsimp only
    rw [hmem₃_below a (by omega)]
    simp [mem₀, compBaseMem, ha]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
