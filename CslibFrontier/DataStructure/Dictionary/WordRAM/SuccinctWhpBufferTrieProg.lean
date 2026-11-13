/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Implementation of the Bounded-Depth Character Trie Buffer (`BufTrie`)

This module implements the constant-depth character trie buffer operations (`bufLookupGenProg`,
`bufEverPresentGenProg`, `bufDeleteGenProg`, `bufInsertGenProg`, `bufCheckSlotGenProg`,
`bufClearStepsGenProg`) as parameter-free `Memory.Prog` subroutines certified over `Basis.exact`
with zero local work via `realize` and `Realizes.iterate₀`.

To keep `WordEncoding` tuple widths small inside loops and multi-write branches, each entry wrapper
projects the needed scalar offsets and masks into a 14-word `BufRt` tuple once via `mkBufRtGenProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufRt`, `mkBufRt`, `mkBufRtGenProg`,
  `BufEpFrame`: compact runtime parameter tuple and disjoint-segment frame invariant for buffer
  `ep ∈ {0, 1}`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg`,
  `bufEverPresentGenProg`, `bufDeleteGenProg`, `bufInsertGenProg`, `bufCheckSlotGenProg`,
  `bufClearStepsGenProg`: parameter-free `Memory.Prog` buffer-trie operations.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufLookupGen`,
  `realizes_bufEverPresentGen`, `realizes_bufDeleteGen`, `realizes_bufInsertGen`,
  `realizes_bufCheckSlotGen`, `realizes_bufClearStepsGen`: parameter-free `Realizes .exact`
  certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufLookupGenProg_spec`,
  `bufEverPresentGenProg_spec`, `bufDeleteGenProg_spec`, `bufInsertGenProg_spec`,
  `bufCheckSlotGenProg_spec`, `bufClearStepsGenProg_spec`: exact refinement, `O_c(1)` `memoryCost`
  bounds, `ValidWhpProg`, `BufTrieMemRep` preservation, and `BufEpFrame` frame laws.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Primitive `Memory.Prog` Helpers, `BufRt`, and `BufEpFrame` -/

@[simp]
private theorem clientResult_pure_zero {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pure x) = x := rfl

@[simp]
private theorem clientState_pure_zero {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (pure x) = s := rfl

private theorem clientResult_memRead (addr : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl

private theorem clientState_memRead (addr : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.read addr) = s := rfl

private theorem memoryCost_memRead (addr : ℕ) (s : Memory.State) :
    memoryCost (Memory.read addr) s = 1 := rfl

private theorem clientState_memWrite (addr val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.write addr val) =
      { mem := Function.update s.mem addr val, frontier := s.frontier } := rfl

private theorem memoryCost_memWrite (addr val : ℕ) (s : Memory.State) :
    memoryCost (Memory.write addr val) s = 1 := rfl

private theorem clientResult_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedGenProg (((base, offset), (k, w)), idx)) =
      readPacked (base + offset) k w s.mem idx :=
  clientResult_readPackedProg _ _ _ _ _ _

private theorem clientState_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedGenProg (((base, offset), (k, w)), idx)) = s := rfl

private theorem memoryCost_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    memoryCost (readPackedGenProg (((base, offset), (k, w)), idx)) s = 2 := rfl

private theorem clientState_writePackedGen (base offset k w idx val : ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (writePackedGenProg ((((base, offset), (k, w)), idx), val)) =
      { mem := writePacked (base + offset) k w s.mem idx val,
        frontier := s.frontier } := rfl

private theorem memoryCost_writePackedGen (base offset k w idx val : ℕ)
    (s : Memory.State) :
    memoryCost (writePackedGenProg ((((base, offset), (k, w)), idx), val)) s = 4 := rfl

private theorem lt_two_pow_gBits_of_le {x n_max : ℕ} (hx : x ≤ n_max) :
    x < 2 ^ globalPtrBits n_max :=
  lt_two_pow_globalPtrBits_of_le hx

/-- Shift-offset invariance of `bufWalk`: stepping `off + 1` is identical to shifting `r` right by
`bChar` and stepping `off`. -/
private theorem bufWalk_add_off (bChar : ℕ) (child : ℕ → ℕ → ℕ) :
    ∀ rem off r cur,
      bufWalk bChar child r rem (off + 1) cur =
        bufWalk bChar child (r / 2 ^ bChar) rem off cur := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro off r cur
    dsimp only [bufWalk]
    rw [trieDigit_succ]
    split_ifs with h0
    · rfl
    · exact ih (off + 1) r _

/-- Shift-offset invariance of `bufEnsurePath`: stepping `off + 1` is identical to shifting `r`
right by `bChar` and stepping `off`. -/
private theorem bufEnsurePath_add_off (bChar : ℕ) :
    ∀ rem off r tr cur,
      bufEnsurePath bChar r rem (off + 1) tr cur =
        bufEnsurePath bChar (r / 2 ^ bChar) rem off tr cur := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro off r tr cur
    dsimp only [bufEnsurePath]
    rw [trieDigit_succ]
    split_ifs with h0
    · exact ih (off + 1) r _ _
    · exact ih (off + 1) r _ _

/-- Unique `(v, c)` decomposition of `v * 2 ^ bChar + c` when `c < 2 ^ bChar`. -/
private theorem child_idx_eq_iff {bChar v₁ c₁ v₂ c₂ : ℕ}
    (hc₁ : c₁ < 2 ^ bChar) (hc₂ : c₂ < 2 ^ bChar) :
    v₁ * 2 ^ bChar + c₁ = v₂ * 2 ^ bChar + c₂ ↔ v₁ = v₂ ∧ c₁ = c₂ := by
  constructor
  · intro heq
    have hpos : 0 < 2 ^ bChar := Nat.two_pow_pos bChar
    have hv : v₁ = v₂ := by
      have hd₁ : (v₁ * 2 ^ bChar + c₁) / 2 ^ bChar = v₁ := by
        rw [Nat.mul_comm v₁ (2 ^ bChar), Nat.mul_add_div hpos, Nat.div_eq_of_lt hc₁, Nat.add_zero]
      have hd₂ : (v₂ * 2 ^ bChar + c₂) / 2 ^ bChar = v₂ := by
        rw [Nat.mul_comm v₂ (2 ^ bChar), Nat.mul_add_div hpos, Nat.div_eq_of_lt hc₂, Nat.add_zero]
      rw [← hd₁, heq, hd₂]
    exact ⟨hv, by subst hv; omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Compact 14-word scalar runtime parameter tuple for an epoch buffer trie `ep ∈ {0, 1}`. -/
abbrev BufRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))

@[expose] def brBase (rt : BufRt) : ℕ := rt.1.1.1
@[expose] def brW (rt : BufRt) : ℕ := rt.1.1.2
@[expose] def brGBits (rt : BufRt) : ℕ := rt.1.2.1
@[expose] def brBChar (rt : BufRt) : ℕ := rt.1.2.2
@[expose] def brPowBChar (rt : BufRt) : ℕ := rt.2.1.1.1
@[expose] def brMaskBChar (rt : BufRt) : ℕ := rt.2.1.1.2
@[expose] def brCTab (rt : BufRt) : ℕ := rt.2.1.2.1
@[expose] def brQEp (rt : BufRt) : ℕ := rt.2.1.2.2
@[expose] def brMaxNodes (rt : BufRt) : ℕ := rt.2.2.1.1
@[expose] def brOffChild (rt : BufRt) : ℕ := rt.2.2.1.2
@[expose] def brOffMeta (rt : BufRt) : ℕ := rt.2.2.2.1.1
@[expose] def brOffItems (rt : BufRt) : ℕ := rt.2.2.2.1.2
@[expose] def brHdrNA (rt : BufRt) : ℕ := rt.2.2.2.2.1
@[expose] def brHdrIA (rt : BufRt) : ℕ := rt.2.2.2.2.2

/-- Pure constructor for `BufRt`. -/
@[expose] def mkBufRt (c U V w n_max base ep : ℕ) : BufRt :=
  (((base, w), (globalPtrBits n_max, bCharWhp n_max)),
   (((2 ^ bCharWhp n_max, 2 ^ bCharWhp n_max - 1), (cTabWhp c, qEpochWhp n_max)),
    ((maxTrieNodesWhp c n_max,
      if ep = 0 then offTrieChild0 c U V w n_max else offTrieChild1 c U V w n_max),
     ((if ep = 0 then offTrieMeta0 c U V w n_max else offTrieMeta1 c U V w n_max,
       if ep = 0 then offTrieItems0 c U V w n_max else offTrieItems1 c U V w n_max),
      (if ep = 0 then hdrBuf0NodeAlloc else hdrBuf1NodeAlloc,
       if ep = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc)))))

/-- Parameter-free `BufRt` envelope in the large regime. -/
@[expose] def BufRtEnvGen (w : ℕ) (rt : BufRt) : Prop :=
  ∃ c U V w₀ n_max base ep,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    rt = mkBufRt c U V w₀ n_max base ep

/-- Extract `BufRt` from `((cp, base), ep)` in zero memory operations. -/
@[expose] def mkBufRtGenProg (d : (WhpCoreParams × ℕ) × ℕ) : Memory.Prog BufRt := do
  let cp := d.1.1
  let base ← pure d.1.2
  if d.2 = 0 then
    pure (((base, wpW cp), (wpGlobalPtrBits cp, wpBChar cp)),
      (((wpPowBChar cp, wpMaskBChar cp), (wpCTab cp, wpQEpoch cp)),
       ((wpMaxTrieNodes cp, wpOffTrieChild0 cp),
        ((wpOffTrieMeta0 cp, wpOffTrieItems0 cp),
         (hdrBuf0NodeAlloc, hdrBuf0ItemAlloc)))))
  else
    pure (((base, wpW cp), (wpGlobalPtrBits cp, wpBChar cp)),
      (((wpPowBChar cp, wpMaskBChar cp), (wpCTab cp, wpQEpoch cp)),
       ((wpMaxTrieNodes cp, wpOffTrieChild1 cp),
        ((wpOffTrieMeta1 cp, wpOffTrieItems1 cp),
         (hdrBuf1NodeAlloc, hdrBuf1ItemAlloc)))))

theorem mkBufRtGenProg_spec {c U V w n_max base ep : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkBufRt c U V w n_max base ep ∧
    memoryCost prog s = 0 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkBufRtGenProg mkBufRt
  simp only [pure_bind, wp_large_w hth, wp_large_globalPtrBits hth, wp_large_bChar hth,
    wp_large_powBChar hth, wp_large_maskBChar hth, wp_large_cTab hth, wp_large_qEpoch hth,
    wp_large_maxTrieNodes hth, wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
    wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth, wp_large_offTrieItems0 hth,
    wp_large_offTrieItems1 hth]
  split_ifs with h0 <;> exact ⟨rfl, rfl, rfl, validWhpProg_pure _⟩

theorem realizes_mkBufRtGen :
    Realizes .exact mkBufRtGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := BufRt))
      (fun w d _ => WhpLargeEnvGen w d.1.1 d.1.2)
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨cp, base⟩, ep⟩
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    exact henv.fits_const (by decide)

section RtSafety

variable {c U V w₀ n_max w base ep : ℕ}

private theorem rt_child_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < trieChildEntriesWhp c n_max) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffChild rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem rt_meta_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < 6 * maxTrieNodesWhp c n_max) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffMeta rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem rt_items_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < 6 * qEpochWhp n_max + 6) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffItems rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem rt_seg_le (c U V w n_max base ep : ℕ) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
    base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
    base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
  have h32 : 32 ≤ largeSpaceWhp c U V w n_max := by
    change hdrWordsWhp ≤ largeSpaceWhp c U V w n_max; unfold largeSpaceWhp; omega
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have h13 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h15 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h16 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h17 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h18 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]
     simp only [↓reduceIte, Nat.one_ne_zero]
     exact ⟨by omega, by omega, by omega, by omega, by omega⟩)

end RtSafety

/-- Compositional frame invariant for writes confined to buffer `ep ∈ {0, 1}` (preserving all
non-buffer words, the opposite buffer `1 - ep`, and `dirtyBuckets` in `offTrieItems0`). -/
@[expose] def BufEpFrame (base c U V w n_max ep : ℕ) (mem₁ mem₂ : ℕ → ℕ) : Prop :=
  let rt := mkBufRt c U V w n_max base ep
  (∀ a,
    a ≠ base + brHdrNA rt →
    a ≠ base + brHdrIA rt →
    (a < base + brOffChild rt ∨
      base + brOffChild rt +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤ a) →
    (a < base + brOffMeta rt ∨
      base + brOffMeta rt +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a) →
    (a < base + brOffItems rt ∨
      base + brOffItems rt +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a) →
    mem₂ a = mem₁ a) ∧
  (∀ idx, 3 * qEpochWhp n_max ≤ idx → idx < 6 * qEpochWhp n_max + 6 →
    readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₂ idx =
      readPacked (base + offTrieItems0 c U V w n_max) (globalPtrBits n_max) w mem₁ idx)

theorem BufEpFrame.refl {base c U V w n_max ep : ℕ} (mem : ℕ → ℕ) :
    BufEpFrame base c U V w n_max ep mem mem :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem BufEpFrame.trans {base c U V w n_max ep : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁₂ : BufEpFrame base c U V w n_max ep m₁ m₂)
    (h₂₃ : BufEpFrame base c U V w n_max ep m₂ m₃) :
    BufEpFrame base c U V w n_max ep m₁ m₃ :=
  ⟨fun a h1 h2 h3 h4 h5 => (h₂₃.1 a h1 h2 h3 h4 h5).trans (h₁₂.1 a h1 h2 h3 h4 h5),
   fun idx h1 h2 => (h₂₃.2 idx h1 h2).trans (h₁₂.2 idx h1 h2)⟩

/-- `BufEpFrame` preserves every word before `offTrieChild0` (except `hdrNA(ep)` and `hdrIA(ep)`)
and every word at or above `base + largeSpaceWhp`. -/
theorem BufEpFrame.mem_outside {base c U V w n_max ep a : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hep : ep = 0 ∨ ep = 1) (hf : BufEpFrame base c U V w n_max ep m₁ m₂)
    (ha : (a < base + offTrieChild0 c U V w n_max ∧
            a ≠ base + brHdrNA (mkBufRt c U V w n_max base ep) ∧
            a ≠ base + brHdrIA (mkBufRt c U V w n_max base ep)) ∨
          base + largeSpaceWhp c U V w n_max ≤ a) :
    m₂ a = m₁ a := by
  have hseg := rt_seg_le c U V w n_max base ep hep
  have hc01 : offTrieChild1 c U V w n_max = offTrieChild0 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max = offTrieChild1 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max = offTrieMeta0 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max = offTrieMeta1 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi1 : offTrieItems1 c U V w n_max = offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc] at ha hseg ⊢
     simp only [↓reduceIte, Nat.one_ne_zero] at ha hseg
     exact hf.1 a
       (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega)
       (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
       (by dsimp [mkBufRt, brOffChild]; omega)
       (by dsimp [mkBufRt, brOffMeta]; omega)
       (by dsimp [mkBufRt, brOffItems]; omega))

/-- `BufEpFrame` on `ep` preserves `BufTrieMemRep` on the opposite buffer `1 - ep`. -/
theorem BufEpFrame.other_bufTrieMemRep {base c U V w n_max ep : ℕ} {tr : BufTrie}
    {m₁ m₂ : ℕ → ℕ} (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hf : BufEpFrame base c U V w n_max ep m₁ m₂)
    (hrep : BufTrieMemRep base c U V w n_max (1 - ep) tr m₁) :
    BufTrieMemRep base c U V w n_max (1 - ep) tr m₂ := by
  have hhb : offHashBkt = 32 := rfl
  have hhf : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have hq : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have hv : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hls : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have hbm : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have hfb : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  have hbp : offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
  have hba : offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
  have hps : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
  have hpo : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtm : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtk : offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
  have hbtv : offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
  have hc0 : offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
  have h32_c0 : 32 ≤ offTrieChild0 c U V w n_max := by omega
  have hc01 : offTrieChild1 c U V w n_max = offTrieChild0 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max = offTrieChild1 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max = offTrieMeta0 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max = offTrieMeta1 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi1 : offTrieItems1 c U V w n_max = offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hch, hpar, hleaf, hitems⟩ := hrep
  rcases hep with rfl | rfl
  · simp only [Nat.sub_zero, Nat.one_ne_zero, ↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hmem_c1 : ∀ a, base + offTrieChild1 c U V w n_max ≤ a →
        a < base + offTrieChild1 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_m1 : ∀ a, base + offTrieMeta1 c U V w n_max ≤ a →
        a < base + offTrieMeta1 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_i1 : ∀ a, base + offTrieItems1 c U V w n_max ≤ a →
        a < base + offTrieItems1 c U V w n_max +
          packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffItems]; omega))
    refine ⟨hna, hia,
      (hf.mem_outside (Or.inl rfl) (Or.inl ⟨by dsimp [hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc]; omega⟩)).trans hhdr_na,
      (hf.mem_outside (Or.inl rfl) (Or.inl ⟨by dsimp [hdrBuf1ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_congr_on hw hidx hmem_c1).trans (hch u hu ch hch_lt)
    · exact ⟨(readPacked_congr_on hw (show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m1).trans (hpar u hu1 hu).1,
        (readPacked_congr_on hw (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m1).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr_on hw (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m1).trans (hleaf u hu).1,
        fun hnz => (readPacked_congr_on hw (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m1).trans ((hleaf u hu).2 hnz)⟩
    · exact ⟨(readPacked_congr_on hw (show id < 6 * qEpochWhp n_max + 6 by omega) hmem_i1).trans
          (hitems id hid).1,
        (readPacked_congr_on hw (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          hmem_i1).trans (hitems id hid).2.1,
        (readPacked_congr_on hw (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          hmem_i1).trans (hitems id hid).2.2⟩
  · simp only [Nat.sub_self, ↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    have hmem_c0 : ∀ a, base + offTrieChild0 c U V w n_max ≤ a →
        a < base + offTrieChild0 c U V w n_max +
          packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inl (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_m0 : ∀ a, base + offTrieMeta0 c U V w n_max ≤ a →
        a < base + offTrieMeta0 c U V w n_max +
          packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    have hmem_i0 : ∀ a, base + offTrieItems0 c U V w n_max ≤ a →
        a < base + offTrieItems0 c U V w n_max +
          packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w → m₂ a = m₁ a :=
      fun a h1 h2 => hf.1 a
        (by dsimp [mkBufRt, brHdrNA, hdrBuf1NodeAlloc]; omega)
        (by dsimp [mkBufRt, brHdrIA, hdrBuf1ItemAlloc]; omega)
        (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))
        (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))
        (Or.inl (by dsimp [mkBufRt, brOffItems]; omega))
    refine ⟨hna, hia,
      (hf.mem_outside (Or.inr rfl) (Or.inl ⟨by dsimp [hdrBuf0NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0NodeAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_na,
      (hf.mem_outside (Or.inr rfl) (Or.inl ⟨by dsimp [hdrBuf0ItemAlloc]; omega,
        by dsimp [mkBufRt, brHdrNA, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc]; omega,
        by dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega⟩)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_congr_on hw hidx hmem_c0).trans (hch u hu ch hch_lt)
    · exact ⟨(readPacked_congr_on hw (show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m0).trans (hpar u hu1 hu).1,
        (readPacked_congr_on hw (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m0).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr_on hw (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m0).trans (hleaf u hu).1,
        fun hnz => (readPacked_congr_on hw (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          hmem_m0).trans ((hleaf u hu).2 hnz)⟩
    · exact ⟨(readPacked_congr_on hw (show id < 6 * qEpochWhp n_max + 6 by omega) hmem_i0).trans
          (hitems id hid).1,
        (readPacked_congr_on hw (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          hmem_i0).trans (hitems id hid).2.1,
        (readPacked_congr_on hw (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          hmem_i0).trans (hitems id hid).2.2⟩

private theorem offTrieItems0_ge_32 (c U V w n_max : ℕ) :
    32 ≤ offTrieItems0 c U V w n_max := by
  have hhb : offHashBkt = 32 := rfl
  have hhf : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have hq : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have hv : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hls : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have hbm : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have hfb : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  have hbp : offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
  have hba : offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
  have hps : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
  have hpo : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtm : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtk : offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
  have hbtv : offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
  have hc0 : offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
  have hc1 : offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  omega

private theorem bufEpFrame_write_hdrNA {base c U V w n_max ep val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem (Function.update mem (base + brHdrNA rt) val) := by
  have h32 := offTrieItems0_ge_32 c U V w n_max
  have hna_lt : brHdrNA (mkBufRt c U V w n_max base ep) < 32 := by
    rcases hep with rfl | rfl <;>
      (dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega)
  exact ⟨fun a h1 _ _ _ _ => Function.update_of_ne h1 _ _,
    fun idx _ h2 => readPacked_update_outside hw h2 (Or.inl (by omega))⟩

private theorem bufEpFrame_write_hdrIA {base c U V w n_max ep val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem (Function.update mem (base + brHdrIA rt) val) := by
  have h32 := offTrieItems0_ge_32 c U V w n_max
  have hia_lt : brHdrIA (mkBufRt c U V w n_max base ep) < 32 := by
    rcases hep with rfl | rfl <;>
      (dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
  exact ⟨fun a _ h2 _ _ _ => Function.update_of_ne h2 _ _,
    fun idx _ h2 => readPacked_update_outside hw h2 (Or.inl (by omega))⟩

private theorem bufEpFrame_writeChild {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < trieChildEntriesWhp c n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffChild rt) (globalPtrBits n_max) w mem idx val) := by
  have hc01 : offTrieChild1 c U V w n_max = offTrieChild0 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max = offTrieChild1 c U V w n_max +
      packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max = offTrieMeta0 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max = offTrieMeta1 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  refine ⟨fun a _ _ h3 _ _ => mem_writePacked_of_outside hw hidx h3, fun j _ hj => ?_⟩
  rcases hep with rfl | rfl <;>
    exact readPacked_writePacked_disjoint hw hj hidx
      (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))

private theorem bufEpFrame_writeMeta {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < 6 * maxTrieNodesWhp c n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffMeta rt) (globalPtrBits n_max) w mem idx val) := by
  have hm1 : offTrieMeta1 c U V w n_max = offTrieMeta0 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max = offTrieMeta1 c U V w n_max +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  refine ⟨fun a _ _ _ h4 _ => mem_writePacked_of_outside hw hidx h4, fun j _ hj => ?_⟩
  rcases hep with rfl | rfl <;>
    exact readPacked_writePacked_disjoint hw hj hidx
      (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))

private theorem bufEpFrame_writeItems_lt3q {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < 3 * qEpochWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffItems rt) (globalPtrBits n_max) w mem idx val) := by
  have hidx6 : idx < 6 * qEpochWhp n_max + 6 := by omega
  have hi1 : offTrieItems1 c U V w n_max = offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  refine ⟨fun a _ _ _ _ h5 => mem_writePacked_of_outside hw hidx6 h5, fun j hj3 hj6 => ?_⟩
  rcases hep with rfl | rfl
  · dsimp only [mkBufRt, brOffItems, ↓reduceIte]
    exact readPacked_writePacked_of_ne hw mem (by omega) val
  · simp only [mkBufRt, brOffItems, Nat.one_ne_zero, ↓reduceIte]
    exact readPacked_writePacked_disjoint hw hj6 hidx6 (Or.inl (by omega))

private theorem rt_disj_le (c U V w n_max base ep : ℕ) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    brHdrNA rt < 32 ∧
    brHdrIA rt < 32 ∧
    brHdrNA rt ≠ brHdrIA rt ∧
    32 ≤ brOffChild rt ∧
    brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
      brOffMeta rt ∧
    brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      brOffItems rt := by
  have hhb : offHashBkt = 32 := rfl
  have hhf : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have hq : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have hv : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hls : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have hbm : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have hfb : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  have hbp : offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w := rfl
  have hba : offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
  have hps : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * ellWhp n_max + 4) w := rfl
  have hpo : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtm : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w := rfl
  have hbtk : offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w := rfl
  have hbtv : offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w := rfl
  have hc0 : offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w := rfl
  have hc1 : offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm0 : offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hm1 : offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi0 : offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w := rfl
  have hi1 : offTrieItems1 c U V w n_max =
      offTrieItems0 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w := rfl
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]
     simp only [↓reduceIte, Nat.one_ne_zero]
     exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)

private theorem bufTrieMemRep_iff_rt {base c U V w n_max ep : ℕ} {tr : BufTrie} {mem : ℕ → ℕ} :
    BufTrieMemRep base c U V w n_max ep tr mem ↔
      let rt := mkBufRt c U V w n_max base ep
      tr.nodeAlloc ≤ maxTrieNodesWhp c n_max ∧
      tr.itemAlloc ≤ qEpochWhp n_max ∧
      mem (base + brHdrNA rt) = tr.nodeAlloc ∧
      mem (base + brHdrIA rt) = tr.itemAlloc ∧
      (∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w mem
          (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch) ∧
      (∀ u, 1 ≤ u → u < tr.nodeAlloc →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 0) =
          tr.nodeParent u ∧
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 1) =
          tr.nodeChar u) ∧
      (∀ u < tr.nodeAlloc,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 2) =
          tr.nodeLeafItem u ∧
        (tr.nodeLeafItem u ≠ 0 →
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 3) =
            tr.nodeActive u)) ∧
      (∀ id < tr.itemAlloc,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem id = tr.itemLeaf id ∧
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem (qEpochWhp n_max + id) =
          tr.itemBucket id ∧
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem (2 * qEpochWhp n_max + id) =
          tr.itemLoc id) :=
  Iff.rfl

/-! ## Section 2: `bufWalkLoopGenProg`, `bufEverPresentGenProg`, `bufLookupGenProg`,
and `bufDeleteGenProg` -/

/-- Precondition for one step of `bufWalk`. -/
@[expose] def BufWalkStepPre (w : ℕ) (p : BufRt × (ℕ × (ℕ × ℕ))) (_ : Memory.State) : Prop :=
  BufRtEnvGen w p.1 ∧ p.2.2.1 < brMaxNodes p.1

/-- One character-walk step on `offChild`. -/
@[expose] def bufWalkStepProg (p : BufRt × (ℕ × (ℕ × ℕ))) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := p.1
  let alive ← pure p.2.1
  let cur ← pure p.2.2.1
  let r_cur ← pure p.2.2.2
  let ch ← pure (r_cur &&& brMaskBChar rt)
  let idx ← pure (cur * brPowBChar rt + ch)
  let nxt ← readPackedGenProg (((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idx)
  let r_nxt ← pure (r_cur >>> brBChar rt)
  if alive = 0 then
    pure (0, (0, r_nxt))
  else if nxt = 0 then
    pure (0, (0, r_nxt))
  else
    pure (1, (nxt, r_nxt))

@[simp]
theorem memoryCost_bufWalkStepProg (p : BufRt × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (bufWalkStepProg p) s = 2 := by
  unfold bufWalkStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedGen]
  split_ifs <;> rfl

theorem memoryCost_bufWalkStepProg_pos (p : BufRt × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    1 ≤ memoryCost (bufWalkStepProg p) s := by simp

theorem realizes_bufWalkStep :
    Realizes .exact bufWalkStepProg
      (WordEncoding.encode (α := BufRt × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufWalkStepPre
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  realize
  all_goals
    rcases d with ⟨rt, ⟨alive, ⟨cur, r_cur⟩⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brMaskBChar, brPowBChar, brBChar, brBase, brOffChild,
      brGBits, brW] at hcur ⊢
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hch_lt : r_cur &&& (2 ^ bCharWhp n_max - 1) < 2 ^ bCharWhp n_max := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hprod_le : cur * 2 ^ bCharWhp n_max ≤ trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      exact Nat.mul_le_mul_right _ hcur.le
    have hidx_lt : cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1)) <
        trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1))
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (hidx_lt.le.trans htc_n)
    | exact rt_child_safe henv hep hidx_lt

/-- Parameter-free wrapper for `iterate bufWalkStepProg`. -/
@[expose] def bufWalkLoopGenProg
    (p : (BufRt × (ℕ × (ℕ × ℕ))) × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) :=
  iterate bufWalkStepProg p.1.1 p.2 p.1.2

theorem realizes_bufWalkLoopGen :
    Realizes .exact bufWalkLoopGenProg
      (WordEncoding.encode (α := (BufRt × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w p s => iterationSafe bufWalkStepProg BufWalkStepPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
    realizes_bufWalkStep
    memoryCost_bufWalkStepProg_pos

private theorem bufWalkLoop_spec {c U V w n_max base ep : ℕ} {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (halloc : 1 ≤ tr.nodeAlloc)
    (hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ rem alive cur r_cur,
      cur < tr.nodeAlloc →
      let prog := bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem)
      iterationSafe bufWalkStepProg BufWalkStepPre w rt rem (alive, (cur, r_cur)) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      memoryCost prog s = 2 * rem ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (alive = 0 → ((Memory.spec 0).clientResult s prog).1 = 0) ∧
      (alive = 1 →
        match bufWalk (bCharWhp n_max) tr.trieChild r_cur rem 0 cur with
        | none => ((Memory.spec 0).clientResult s prog).1 = 0
        | some leaf =>
          ((Memory.spec 0).clientResult s prog).1 = 1 ∧
          ((Memory.spec 0).clientResult s prog).2.1 = leaf ∧
          leaf < tr.nodeAlloc) := by
  intro rt rem
  have hw := henv.2.1
  have hna_max : tr.nodeAlloc ≤ maxTrieNodesWhp c n_max := hrep.1
  have hc_seg := (rt_seg_le c U V w n_max base ep hep).2.2.1
  have hrep_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
        (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch := by
    have h := hrep.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact h
  induction rem with
  | zero =>
    intro alive cur r_cur _
    refine ⟨trivial, rfl, Nat.mul_zero 2 ▸ rfl, validWhpProg_pure _,
      fun ha => ha, fun ha => ?_⟩
    dsimp only [bufWalk, bufWalkLoopGenProg, iterate]
    rw [StateTransitionSpec.clientResult_pure]
    exact ⟨ha, rfl, ‹cur < tr.nodeAlloc›⟩
  | succ rem ih =>
    intro alive cur r_cur hcur
    have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans_le hna_max
    have hpre : BufWalkStepPre w (rt, (alive, (cur, r_cur))) s :=
      ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur_max⟩
    set ch := r_cur % 2 ^ bCharWhp n_max with hch_def
    have hch_eq : r_cur &&& brMaskBChar rt = ch := by
      dsimp only [rt, mkBufRt, brMaskBChar, ch]
      exact Nat.and_two_pow_sub_one_eq_mod r_cur (bCharWhp n_max)
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    set idx := cur * 2 ^ bCharWhp n_max + ch
    have hidx_lt : idx < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
    set r_nxt := r_cur / 2 ^ bCharWhp n_max with hr_def
    have hr_eq : r_cur >>> brBChar rt = r_nxt := by
      dsimp only [rt, mkBufRt, brBChar, r_nxt]
      exact Nat.shiftRight_eq_div_pow r_cur (bCharWhp n_max)
    set stepP := bufWalkStepProg (rt, (alive, (cur, r_cur)))
    have hidx_rt : cur * brPowBChar rt + (r_cur &&& brMaskBChar rt) = idx := by
      rw [hch_eq]; rfl
    have hstep_st : (Memory.spec 0).clientState s stepP = s := by
      dsimp only [stepP, bufWalkStepProg]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
      split_ifs <;> rfl
    have hstep_vp : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
      dsimp only [stepP, bufWalkStepProg]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
      rw [clientState_readPackedGen]
      split_ifs <;> exact validWhpProg_pure _
    have hnxt_eq : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) s.mem
        (cur * brPowBChar rt + (r_cur &&& brMaskBChar rt)) = tr.trieChild cur ch := by
      rw [hch_eq]
      exact hrep_ch cur hcur_max ch hch_lt
    set stepRes :=
      if alive = 0 then (0, (0, r_nxt))
      else if tr.trieChild cur ch = 0 then (0, (0, r_nxt))
      else (1, (tr.trieChild cur ch, r_nxt))
    have hstep_res : (Memory.spec 0).clientResult s stepP = stepRes := by
      dsimp only [stepP, bufWalkStepProg, stepRes]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, hnxt_eq, hr_eq]
      by_cases ha0 : alive = 0
      · simp [ha0]
      · by_cases hn0 : tr.trieChild cur ch = 0 <;> simp [ha0, hn0]
    have hcur_nxt : stepRes.2.1 < tr.nodeAlloc := by
      dsimp only [stepRes]
      split_ifs with ha0 hn0
      · exact halloc
      · exact halloc
      · exact hchild cur ch hn0
    obtain ⟨hsafe_r, hst_r, hmc_r, hvp_r, ha0_r, ha1_r⟩ :=
      ih stepRes.1 stepRes.2.1 stepRes.2.2 hcur_nxt
    have hst_all : (Memory.spec 0).clientState s
        (bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem + 1)) = s := by
      change (Memory.spec 0).clientState s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') = s
      rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hst_r
    have hres_all : (Memory.spec 0).clientResult s
        (bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem + 1)) =
        (Memory.spec 0).clientResult s (bufWalkLoopGenProg ((rt, stepRes), rem)) := by
      change (Memory.spec 0).clientResult s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') = _
      rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_res]
      rfl
    refine ⟨⟨hpre, ?_⟩, hst_all, ?_, ?_, ?_, ?_⟩
    · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
      exact hsafe_r
    · change memoryCost (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') s = 2 * (rem + 1)
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost stepP s +
        memoryCost (bufWalkLoopGenProg
          ((rt, (Memory.spec 0).clientResult s stepP), rem))
          ((Memory.spec 0).clientState s stepP) = 2 * (rem + 1)
      rw [hstep_st, hstep_res, memoryCost_bufWalkStepProg, hmc_r]
      ring
    · change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s')
      refine validWhpProg_bind hstep_vp ?_
      change ValidWhpProg w (base + largeSpaceWhp c U V w n_max)
        ((Memory.spec 0).clientState s stepP)
        (bufWalkLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
      rw [hstep_st, hstep_res]
      exact hvp_r
    · intro ha0
      rw [hres_all]
      exact ha0_r (by dsimp [stepRes]; simp [ha0])
    · intro ha1
      rw [hres_all]
      dsimp only [bufWalk]
      rw [trieDigit_zero, ← hch_def]
      by_cases hn0 : tr.trieChild cur ch = 0
      · rw [ite_eq_left hn0]
        exact ha0_r (by dsimp [stepRes]; simp [ha1, hn0])
      · rw [ite_eq_right hn0, bufWalk_add_off, ← hr_def]
        have hsr : stepRes = (1, (tr.trieChild cur ch, r_nxt)) := by
          dsimp [stepRes]; simp [ha1, hn0]
        rw [hsr] at ha1_r ⊢
        exact ha1_r rfl

/-- Shared read/delete admissibility precondition on `(((cp, base), ep), rKey)`. -/
@[expose] def BufReadGenPre (w : ℕ) (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max tr mapFn,
    WhpLargeEnv c U V w₀ n_max w d.1.1.2 ∧
    d.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    (d.1.2 = 0 ∨ d.1.2 = 1) ∧
    BufTrieMemRep d.1.1.2 c U V w₀ n_max d.1.2 tr s.mem ∧
    ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn

/-- `BufRt` leaf helper for `bufEverPresent`. -/
@[expose] def bufEverLeafRtProg (d : BufRt × ℕ) : Memory.Prog ℕ := do
  let rt := d.1
  let idx ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx)
  if id1 = 0 then pure 0 else pure 1

theorem realizes_bufEverLeafRt :
    Realizes .exact bufEverLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hleaf
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Parameter-free `bufEverPresent` (`d = (((cp, base), ep), rKey)`), returning `1` or `0`. -/
@[expose] def bufEverPresentGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let rt ← mkBufRtGenProg d.1
  let one_v ← pure 1
  let zero_v ← pure 0
  let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, d.2))), brCTab rt)
  if wres.1 = 0 then
    pure 0
  else
    bufEverLeafRtProg (rt, wres.2.1)

theorem bufEverPresentGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufEverPresentGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if bufEverPresent (cTabWhp c) (bCharWhp n_max) tr rKey then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 2 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
    fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hw_st, hw_mc, hw_vp, _, hw_a1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
  have hw1 := hw_a1 rfl
  have hm_seg := (rt_seg_le c U V w n_max base ep hep).2.2.2.1
  have hrep_li : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u := by
    have h := hrep.2.2.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact fun u hu => (h u hu).1
  unfold bufEverPresentGenProg
  simp only [pure_bind]
  set wprog := bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c)
  set wres := (Memory.spec 0).clientResult s wprog
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientState_bind, hw_st]
    split_ifs with hz
    · rfl
    · unfold bufEverLeafRtProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
      split_ifs <;> rfl
  · rw [StateTransitionSpec.clientResult_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientResult_bind, hw_st]
    rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
    · rw [hwk] at hw1
      unfold bufEverPresent
      rw [hwk, ite_eq_left hw1]; rfl
    · rw [hwk] at hw1
      unfold bufEverPresent
      rw [hwk]
      obtain ⟨hw_one, hw_lf, hlf_lt⟩ := hw1
      rw [ite_eq_right (by omega : wres.1 ≠ 0), hw_lf]
      unfold bufEverLeafRtProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl,
        hrep_li leaf hlf_lt]
      by_cases hli : tr.nodeLeafItem leaf = 0 <;> simp [hli]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc]
    split_ifs with hz
    · change 0 + (2 * cTabWhp c + 0) ≤ _; omega
    · unfold bufEverLeafRtProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen]
      split_ifs <;> (change 0 + (2 * cTabWhp c + (2 + 0)) ≤ _; omega)
  · refine validWhpProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr_cTab]
    refine validWhpProg_bind hw_vp ?_
    rw [hw_st]
    split_ifs with hz
    · exact validWhpProg_pure _
    · rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
      · rw [hwk] at hw1; exact absurd hw1 hz
      · rw [hwk] at hw1
        obtain ⟨_, hw_lf, hlf_lt⟩ := hw1
        change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
          (bufEverLeafRtProg (rt, wres.2.1))
        rw [hw_lf]
        have hidx_lt : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by
          have := hrep.1; omega
        unfold bufEverLeafRtProg
        simp only [pure_bind]
        refine validWhpProg_bind (validWhpProg_readPacked hw hidx_lt hm_seg) ?_
        rw [clientState_readPackedGen]
        split_ifs <;> exact validWhpProg_pure _

theorem realizes_bufEverPresentGen :
    Realizes .exact bufEverPresentGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BufReadGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hel := realizes_bufEverLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
      fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, hw_st, _, _, _, hw_a1⟩ :=
      bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
    have hw1 := hw_a1 rfl
    try simp only [hrt_st, hrt_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brCTab, brMaxNodes] at *
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         exact hw1.2.1 ▸ hw1.2.2.trans_le hrep.1)

/-- `BufRt` active-item reader for `bufLookup`: given `(rt, id)` (`id < qEp`), reads
`(1, (b, loc))`. -/
@[irreducible] def bufReadItemPairRtProg (d : BufRt × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let idxB ← pure (brQEp rt + d.2)
  let idxL ← pure (2 * brQEp rt + d.2)
  let b ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB)
  let loc ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL)
  pure (1, (b, loc))

private theorem bufReadItemPairRtProg_eq (d : BufRt × ℕ) :
    bufReadItemPairRtProg d = (do
      let rt := d.1
      let idxB ← pure (brQEp rt + d.2)
      let idxL ← pure (2 * brQEp rt + d.2)
      let b ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB)
      let loc ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL)
      pure (1, (b, loc))) := by
  unfold bufReadItemPairRtProg; rfl

theorem realizes_bufReadItemPairRt :
    Realizes .exact bufReadItemPairRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brQEp d.1)
      (fun _ _ => 0) := by
  unfold bufReadItemPairRtProg
  have hrp := realizes_readPackedGen
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, id⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp] at hid ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_items_safe henv hep (by omega)

/-- `BufRt` leaf helper for `bufLookup`: checks `nodeLeafItem` and `nodeActive`, then reads
`(b, loc)`. -/
@[irreducible] def bufLookupLeafRtProg (d : BufRt × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  if id1 = 0 then
    pure (0, (0, 0))
  else
    let idxAct ← pure (4 * d.2 + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure (0, (0, 0))
    else
      let id ← pure (id1 - 1)
      bufReadItemPairRtProg (rt, id)

private theorem bufLookupLeafRtProg_eq (d : BufRt × ℕ) :
    bufLookupLeafRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      if id1 = 0 then
        pure (0, (0, 0))
      else
        let idxAct ← pure (4 * d.2 + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure (0, (0, 0))
        else
          let id ← pure (id1 - 1)
          bufReadItemPairRtProg (rt, id)) := by
  unfold bufLookupLeafRtProg; rfl

/-- Precondition for `bufLookupLeafRtProg`. -/
@[expose] def BufLookupLeafPre (w : ℕ) (d : BufRt × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max base ep tr,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    d.1 = mkBufRt c U V w₀ n_max base ep ∧
    BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
    d.2 < tr.nodeAlloc ∧
    (tr.nodeLeafItem d.2 ≠ 0 → tr.nodeLeafItem d.2 ≤ tr.itemAlloc)

theorem realizes_bufLookupLeafRt :
    Realizes .exact bufLookupLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufLookupLeafPre
      (fun _ _ => 0) := by
  unfold bufLookupLeafRtProg
  have hrp := realizes_readPackedGen
  have hrip := realizes_bufReadItemPairRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hleaf, hli_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna_max : tr.nodeAlloc ≤ maxTrieNodesWhp c n_max := hrep.1
    have hia_le : tr.itemAlloc ≤ qEpochWhp n_max := hrep.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hrep_li : readPacked (base + brOffMeta (mkBufRt c U V w n_max base ep))
        (globalPtrBits n_max) w s.mem (4 * leaf + 2) = tr.nodeLeafItem leaf := by
      have hm := hrep.2.2.2.2.2.2.1 leaf hleaf
      rcases hep with rfl | rfl <;> exact hm.1
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (simp only [brBase, brOffMeta, brGBits, brW, brQEp, mkBufRt,
         clientResult_readPackedGen] at *
       rw [hrep_li] at *
       have hnz : tr.nodeLeafItem leaf ≠ 0 := by omega
       have hle := hli_le hnz
       have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
       omega)

/-- Parameter-free `bufLookup` (`d = (((cp, base), ep), rKey)`), returning `(0, (0, 0))` on `none`
and `(1, (b, loc))` on `some (b, loc)`. -/
@[expose] def bufLookupGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt ← mkBufRtGenProg d.1
  let one_v ← pure 1
  let zero_v ← pure 0
  let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, d.2))), brCTab rt)
  if wres.1 = 0 then
    pure (0, (0, 0))
  else
    bufLookupLeafRtProg (rt, wres.2.1)

theorem bufLookupGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufLookupGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match bufLookup (cTabWhp c) (bCharWhp n_max) tr rKey with
       | none => (0, (0, 0))
       | some (b, loc) => (1, (b, loc))) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
    fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
  have hleaf_ia : ∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc :=
    fun u hu hnz => (hv.2.2.2.2.choose_spec.2.2.2 u hu hnz).2.1
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hw_st, hw_mc, hw_vp, _, hw_a1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
  have hw1 := hw_a1 rfl
  obtain ⟨_, _, _, hm_seg, hi_seg⟩ := rt_seg_le c U V w n_max base ep hep
  have hrep_meta : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u ∧
      (tr.nodeLeafItem u ≠ 0 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 3) =
          tr.nodeActive u) := by
    have hm := hrep.2.2.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact hm
  have hrep_items : ∀ id < tr.itemAlloc,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (qEpochWhp n_max + id) =
        tr.itemBucket id ∧
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (2 * qEpochWhp n_max + id) =
        tr.itemLoc id := by
    have hi := hrep.2.2.2.2.2.2.2
    rcases hep with rfl | rfl <;> exact fun id hid => (hi id hid).2
  unfold bufLookupGenProg
  simp only [pure_bind]
  set wprog := bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c)
  set wres := (Memory.spec 0).clientResult s wprog
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientState_bind, hw_st]
    split_ifs with hz
    · rfl
    · rw [bufLookupLeafRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
      split_ifs with h1
      · rfl
      · rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
        split_ifs with h2
        · rfl
        · rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
            StateTransitionSpec.clientState_bind, clientState_readPackedGen]
          rfl
  · rw [StateTransitionSpec.clientResult_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientResult_bind, hw_st]
    dsimp only [bufLookup]
    rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
    · rw [hwk] at hw1
      rw [ite_eq_left hw1]; rfl
    · rw [hwk] at hw1
      obtain ⟨hw_one, hw_lf, hlf_lt⟩ := hw1
      rw [ite_eq_right (by omega : wres.1 ≠ 0), hw_lf, bufLookupLeafRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl]
      obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
      rw [hli_eq]
      by_cases hli0 : tr.nodeLeafItem leaf = 0
      · simp [hli0]
      · rw [ite_eq_right hli0, StateTransitionSpec.clientResult_bind,
          clientState_readPackedGen, clientResult_readPackedGen, hact_eq hli0]
        by_cases hact0 : tr.nodeActive leaf = 0
        · simp [hli0, hact0]
        · rw [ite_eq_right hact0]
          simp only [hli0, hact0, false_or, ↓reduceIte]
          have hid_lt : tr.nodeLeafItem leaf - 1 < tr.itemAlloc := by
            have := hleaf_ia leaf hlf_lt hli0; omega
          obtain ⟨hb_eq, hloc_eq⟩ := hrep_items (tr.nodeLeafItem leaf - 1) hid_lt
          rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind, StateTransitionSpec.clientResult_bind,
            clientResult_readPackedGen, StateTransitionSpec.clientResult_pure]
          exact Prod.ext rfl (Prod.ext hb_eq hloc_eq)
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc]
    split_ifs with hz
    · change 0 + (2 * cTabWhp c + 0) ≤ _; omega
    · rw [bufLookupLeafRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen]
      split_ifs with h1
      · change 0 + (2 * cTabWhp c + (2 + 0)) ≤ _; omega
      · simp only [memoryCost_bind, memoryCost_readPackedGen]
        split_ifs with h2
        · change 0 + (2 * cTabWhp c + (2 + (2 + 0))) ≤ _; omega
        · rw [bufReadItemPairRtProg_eq]
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
            memoryCost_readPackedGen]
          change 0 + (2 * cTabWhp c + (2 + (2 + (2 + (2 + 0))))) ≤ _; omega
  · refine validWhpProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr_cTab]
    refine validWhpProg_bind hw_vp ?_
    rw [hw_st]
    split_ifs with hz
    · exact validWhpProg_pure _
    · rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
      · rw [hwk] at hw1; exact absurd hw1 hz
      · rw [hwk] at hw1
        obtain ⟨_, hw_lf, hlf_lt⟩ := hw1
        change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
          (bufLookupLeafRtProg (rt, wres.2.1))
        rw [hw_lf, bufLookupLeafRtProg_eq]
        have hna_max := hrep.1
        have hia_le := hrep.2.1
        simp only [pure_bind]
        refine validWhpProg_bind
          (validWhpProg_readPacked hw (show 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max by omega)
            hm_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen,
          show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
          show brW rt = w from rfl, (hrep_meta leaf hlf_lt).1]
        split_ifs with hli0
        · exact validWhpProg_pure _
        · refine validWhpProg_bind
            (validWhpProg_readPacked hw (show 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max by omega)
              hm_seg) ?_
          rw [clientState_readPackedGen]
          split_ifs with hact0
          · exact validWhpProg_pure _
          · have hid_lt : tr.nodeLeafItem leaf - 1 < tr.itemAlloc := by
              have := hleaf_ia leaf hlf_lt hli0; omega
            rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            refine validWhpProg_bind
              (validWhpProg_readPacked hw
                (show brQEp rt + (tr.nodeLeafItem leaf - 1) < 6 * qEpochWhp n_max + 6
                  by dsimp [rt, mkBufRt, brQEp]; omega) hi_seg) ?_
            rw [clientState_readPackedGen]
            exact validWhpProg_bind
              (validWhpProg_readPacked hw
                (show 2 * brQEp rt + (tr.nodeLeafItem leaf - 1) < 6 * qEpochWhp n_max + 6
                  by dsimp [rt, mkBufRt, brQEp]; omega) hi_seg)
              (validWhpProg_pure _)

theorem realizes_bufLookupGen :
    Realizes .exact bufLookupGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufReadGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hll := realizes_bufLookupLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
      fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
    have hleaf_ia : ∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc :=
      fun u hu hnz => (hv.2.2.2.2.choose_spec.2.2.2 u hu hnz).2.1
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, hw_st, _, _, _, hw_a1⟩ :=
      bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
    have hw1 := hw_a1 rfl
    try simp only [hrt_st, hrt_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | (have hbr_c : brCTab (mkBufRt c U V w n_max base ep) = cTabWhp c := rfl
       simp only [hbr_c] at *
       rw [hw_st]
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         exact ⟨c, U, V, w, n_max, base, ep, tr, henv, hep, rfl, hrep,
           hw1.2.1 ▸ hw1.2.2, fun hnz => hleaf_ia _ (hw1.2.1 ▸ hw1.2.2) hnz⟩)

/-- `BufRt` leaf helper for `bufDelete`: clears `nodeActive leaf := 0` if currently active. -/
@[irreducible] def bufDeleteLeafRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  if id1 = 0 then
    pure ()
  else
    let idxAct ← pure (4 * d.2 + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure ()
    else
      let zero_v ← pure 0
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), zero_v)

private theorem bufDeleteLeafRtProg_eq (d : BufRt × ℕ) :
    bufDeleteLeafRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      if id1 = 0 then
        pure ()
      else
        let idxAct ← pure (4 * d.2 + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure ()
        else
          let zero_v ← pure 0
          writePackedGenProg
            ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), zero_v)) := by
  unfold bufDeleteLeafRtProg; rfl

theorem realizes_bufDeleteLeafRt :
    Realizes .exact bufDeleteLeafRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufDeleteLeafRtProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hleaf
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Parameter-free `bufDelete` (`d = (((cp, base), ep), rKey)`). -/
@[expose] def bufDeleteGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let rt ← mkBufRtGenProg d.1
  let one_v ← pure 1
  let zero_v ← pure 0
  let wres ← bufWalkLoopGenProg ((rt, (one_v, (zero_v, d.2))), brCTab rt)
  if wres.1 = 0 then
    pure ()
  else
    bufDeleteLeafRtProg (rt, wres.2.1)

theorem bufDeleteGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) tr rKey
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
    fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hw_st, hw_mc, hw_vp, _, hw_a1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
  have hw1 := hw_a1 rfl
  have hm_seg : base + brOffMeta rt +
      packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := (rt_seg_le c U V w n_max base ep hep).2.2.2.1
  obtain ⟨hna32, hia32, _, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  have hrep_meta : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u ∧
      (tr.nodeLeafItem u ≠ 0 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 3) =
          tr.nodeActive u) :=
    (bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.2.2.1
  dsimp only
  unfold bufDeleteGenProg
  simp only [pure_bind]
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  set wprog := bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c)
  set wres := (Memory.spec 0).clientResult s wprog
  have hs'_pre : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
          if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) =
      (Memory.spec 0).clientState s
        (if wres.1 = 0 then pure () else bufDeleteLeafRtProg (rt, wres.2.1)) := by
    rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientState_bind, hw_st]
  rw [hs'_pre]
  dsimp only [bufDelete]
  rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
  · rw [hwk] at hw1
    rw [ite_eq_left hw1]
    have hst_pure : (Memory.spec 0).clientState s (pure ()) = s := rfl
    rw [hst_pure]
    refine ⟨rfl, ?_, ?_, hrep, BufEpFrame.refl _⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc, ite_eq_left hw1]
      change 0 + (2 * cTabWhp c + 0) ≤ _; omega
    · refine validWhpProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res, hbr_cTab]
      refine validWhpProg_bind hw_vp ?_
      rw [hw_st, ite_eq_left hw1]
      exact validWhpProg_pure _
  · rw [hwk] at hw1
    dsimp only
    obtain ⟨hw_one, hw_lf, hlf_lt⟩ := hw1
    have hna_max := hrep.1
    have hidx2 : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by omega
    have hidx3 : 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max := by omega
    obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
    have hwres_nz : wres.1 ≠ 0 := by omega
    rw [ite_eq_right hwres_nz, hw_lf]
    have hmc_all : memoryCost
        (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
          bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
            if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) s ≤
        2 * cTabWhp c + 8 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hw_st, hw_mc, ite_eq_right hwres_nz, hw_lf,
        bufDeleteLeafRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen]
      split_ifs with h1
      · change 0 + (2 * cTabWhp c + (2 + 0)) ≤ _; omega
      · simp only [memoryCost_bind, memoryCost_readPackedGen]
        split_ifs with h2
        · change 0 + (2 * cTabWhp c + (2 + (2 + 0))) ≤ _; omega
        · rw [memoryCost_writePackedGen]
          omega
    have hvp_all : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
          bufWalkLoopGenProg ((rt', (1, (0, rKey))), brCTab rt') >>= fun wr =>
            if wr.1 = 0 then pure () else bufDeleteLeafRtProg (rt', wr.2.1)) := by
      refine validWhpProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res, hbr_cTab]
      refine validWhpProg_bind hw_vp ?_
      rw [hw_st, ite_eq_right hwres_nz, hw_lf, bufDeleteLeafRtProg_eq]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen]
      split_ifs with h1
      · exact validWhpProg_pure _
      · refine validWhpProg_bind (validWhpProg_readPacked hw hidx3 hm_seg) ?_
        rw [clientState_readPackedGen]
        split_ifs with h2
        · exact validWhpProg_pure _
        · exact validWhpProg_writePacked hw hgk hidx3 hm_seg
    have hleaf_st : (Memory.spec 0).clientState s (bufDeleteLeafRtProg (rt, leaf)) =
        if tr.nodeLeafItem leaf = 0 then s
        else if tr.nodeActive leaf = 0 then s
        else
          { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * leaf + 3) 0,
            frontier := s.frontier } := by
      rw [bufDeleteLeafRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hli_eq]
      by_cases hli0 : tr.nodeLeafItem leaf = 0
      · rw [ite_eq_left hli0, ite_eq_left hli0]; rfl
      · rw [ite_eq_right hli0, ite_eq_right hli0, StateTransitionSpec.clientState_bind,
          clientState_readPackedGen, clientResult_readPackedGen, hact_eq hli0]
        by_cases hact0 : tr.nodeActive leaf = 0
        · rw [ite_eq_left hact0, ite_eq_left hact0]; rfl
        · rw [ite_eq_right hact0, ite_eq_right hact0, clientState_writePackedGen]
    rw [hleaf_st]
    by_cases hli0 : tr.nodeLeafItem leaf = 0
    · rw [ite_eq_left hli0, ite_eq_left (Or.inl hli0)]
      exact ⟨rfl, hmc_all, hvp_all, hrep, BufEpFrame.refl _⟩
    · rw [ite_eq_right hli0]
      by_cases hact0 : tr.nodeActive leaf = 0
      · rw [ite_eq_left hact0, ite_eq_left (Or.inr hact0)]
        exact ⟨rfl, hmc_all, hvp_all, hrep, BufEpFrame.refl _⟩
      · have hnot_or : ¬(tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0) :=
          fun h => h.elim hli0 hact0
        rw [ite_eq_right hact0, ite_eq_right hnot_or]
        set mem' := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem
          (4 * leaf + 3) 0
        have hfr : BufEpFrame base c U V w n_max ep s.mem mem' :=
          bufEpFrame_writeMeta hw hep hidx3
        have h0_lt : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
        refine ⟨rfl, hmc_all, hvp_all, ?_, hfr⟩
        obtain ⟨hna, hia, hhna, hhia, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
        rw [bufTrieMemRep_iff_rt]
        dsimp only
        rw [← show rt = mkBufRt c U V w n_max base ep from rfl] at hhna hhia hch hpar hlf hit ⊢
        refine ⟨hna, hia,
          (mem_writePacked_of_outside hw hidx3 (Or.inl (by omega))).trans hhna,
          (mem_writePacked_of_outside hw hidx3 (Or.inl (by omega))).trans hhia,
          fun u hu ch' hch' => ?_,
          fun u hu1 hu => ⟨(readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans
            (hpar u hu1 hu).1,
            (readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans (hpar u hu1 hu).2⟩,
          fun u hu => ⟨(readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans (hlf u hu).1,
            fun hnz => by
              by_cases hul : u = leaf
              · subst hul
                rw [Function.update_self]
                exact readPacked_writePacked_self _ _ _ s.mem (4 * u + 3) h0_lt
              · rw [Function.update_of_ne hul]
                exact (readPacked_writePacked_of_ne hw s.mem (by omega) 0).trans
                  ((hlf u hu).2 hnz)⟩,
          fun id hid => ⟨(readPacked_writePacked_disjoint hw
              (show id < 6 * qEpochWhp n_max + 6 by omega) hidx3 (Or.inr (by omega))).trans
              (hit id hid).1,
            (readPacked_writePacked_disjoint hw
              (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) hidx3
              (Or.inr (by omega))).trans (hit id hid).2.1,
            (readPacked_writePacked_disjoint hw
              (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) hidx3
              (Or.inr (by omega))).trans (hit id hid).2.2⟩⟩
        have huc_lt : u * 2 ^ bCharWhp n_max + ch' < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp
          calc u * 2 ^ bCharWhp n_max + ch'
              < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch' _
            _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
            _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
        exact (readPacked_writePacked_disjoint hw huc_lt hidx3 (Or.inl (by omega))).trans
          (hch u hu ch' hch')

theorem realizes_bufDeleteGen :
    Realizes .exact bufDeleteGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BufReadGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hwl := realizes_bufWalkLoopGen
  have hdl := realizes_bufDeleteLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, rKey⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc :=
      fun v ch hnz => ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, hw_st, _, _, _, hw_a1⟩ :=
      bufWalkLoop_spec henv hep hrep hv.1 hchild (cTabWhp c) 1 0 rKey hv.1
    have hw1 := hw_a1 rfl
    try simp only [hrt_st, hrt_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brCTab, brMaxNodes] at *
       rcases hwk : bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 with _ | leaf
       · rw [hwk] at hw1; omega
       · rw [hwk] at hw1
         exact hw1.2.1 ▸ hw1.2.2.trans_le hrep.1)

/-! ## Section 3: `bufEnsureLoopGenProg` and `bufInsertGenProg` -/

/-- Write `(nodeParent u, nodeChar u, nodeLeafItem u) := (cur, ch, 0)` for a freshly allocated
trie node `u < maxNodes` (`d = ((rt, u), (cur, ch))`). -/
@[irreducible] def bufAllocMetaRtProg (d : (BufRt × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1
  let u ← pure d.1.2
  let idx0 ← pure (4 * u)
  let idx1 ← pure (4 * u + 1)
  let idx2 ← pure (4 * u + 2)
  let zero_v ← pure 0
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx0), d.2.1)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx1), d.2.2)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idx2), zero_v)

theorem realizes_bufAllocMetaRt :
    Realizes .exact bufAllocMetaRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1 ∧ d.1.2 < brMaxNodes d.1.1)
      (fun _ _ => 0) := by
  unfold bufAllocMetaRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨rt, u⟩, ⟨cur, ch⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

private theorem bufAllocMetaRtProg_spec {c U V w n_max base ep u cur ch : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hu : u < maxTrieNodesWhp c n_max)
    (hcur : cur < maxTrieNodesWhp c n_max) (hch : ch < 2 ^ bCharWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufAllocMetaRtProg ((rt, u), (cur, ch))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 0) = cur ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 1) = ch ∧
    readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem (4 * u + 2) = 0 ∧
    (∀ idx < 6 * maxTrieNodesWhp c n_max,
      idx ≠ 4 * u → idx ≠ 4 * u + 1 → idx ≠ 4 * u + 2 →
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + brOffMeta rt ∨
      base + brOffMeta rt +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hm_seg := (rt_seg_le c U V w n_max base ep hep).2.2.2.1
  obtain ⟨_, _, _, _, _, hmt_lt, _, hpbc_lt⟩ := large_bounds_lt_n_max hth
  have hcur_g : cur < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have hch_g : ch < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have h0_g : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
  have hi0 : 4 * u < 6 * maxTrieNodesWhp c n_max := by omega
  have hi1 : 4 * u + 1 < 6 * maxTrieNodesWhp c n_max := by omega
  have hi2 : 4 * u + 2 < 6 * maxTrieNodesWhp c n_max := by omega
  set rt := mkBufRt c U V w n_max base ep
  unfold bufAllocMetaRtProg
  simp only [pure_bind]
  set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u) cur
  set m2 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w m1 (4 * u + 1) ch
  set m3 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w m2 (4 * u + 2) 0
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u), cur) >>=
        fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u + 1), ch) >>= fun _ =>
            writePackedGenProg
              ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * u + 2), 0)) =
      { mem := m3, frontier := s.frontier } := rfl
  rw [hs'_eq]
  refine ⟨rfl, rfl, ?_,
    ((bufEpFrame_writeMeta hw hep hi0).trans (bufEpFrame_writeMeta hw hep hi1)).trans
      (bufEpFrame_writeMeta hw hep hi2),
    ?_, ?_, readPacked_writePacked_self _ _ _ m2 (4 * u + 2) h0_g,
    fun idx _ hn0 hn1 hn2 => ?_, fun a ha => ?_⟩
  · refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi0 hm_seg) ?_
    rw [clientState_writePackedGen]
    refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi1 hm_seg) ?_
    rw [clientState_writePackedGen]
    exact validWhpProg_writePacked hw hgk hi2 hm_seg
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) 0).trans
      ((readPacked_writePacked_of_ne hw m1 (by omega) ch).trans
        (readPacked_writePacked_self _ _ _ s.mem (4 * u) hcur_g))
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) 0).trans
      (readPacked_writePacked_self _ _ _ m1 (4 * u + 1) hch_g)
  · exact (readPacked_writePacked_of_ne hw m2 hn2 0).trans
      ((readPacked_writePacked_of_ne hw m1 hn1 ch).trans
        (readPacked_writePacked_of_ne hw s.mem hn0 cur))
  · exact (mem_writePacked_of_outside hw hi2 ha).trans
      ((mem_writePacked_of_outside hw hi1 ha).trans (mem_writePacked_of_outside hw hi0 ha))

/-- Allocate one missing child node `u := nodeAlloc` along `(cur, ch)`
(`d = ((rt, (cur, ch)), r_nxt)`). -/
@[irreducible] def bufAllocNodeRtProg
    (d : (BufRt × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let rt := d.1.1
  let cur ← pure d.1.2.1
  let ch ← pure d.1.2.2
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let u ← Memory.read addrNA
  let u1 ← pure (u + 1)
  Memory.write addrNA u1
  let idxC ← pure (cur * brPowBChar rt + ch)
  writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), u)
  bufAllocMetaRtProg ((rt, u), (cur, ch))
  pure (u, d.2)

/-- Precondition for `bufAllocNodeRtProg`. -/
@[expose] def BufAllocNodePre (w : ℕ) (d : (BufRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  BufRtEnvGen w d.1.1 ∧
  d.1.2.1 < brMaxNodes d.1.1 ∧
  d.1.2.2 < brPowBChar d.1.1 ∧
  s.mem (brBase d.1.1 + brHdrNA d.1.1) < brMaxNodes d.1.1

theorem realizes_bufAllocNodeRt :
    Realizes .exact bufAllocNodeRtProg
      (WordEncoding.encode (α := (BufRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufAllocNodePre
      (fun _ _ => 0) := by
  unfold bufAllocNodeRtProg
  have hwp := realizes_writePackedGen
  have ham := realizes_bufAllocMetaRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, ⟨cur, ch⟩⟩, r_nxt⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur, hch, hu_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brPowBChar, brBase, brHdrNA] at hcur hch hu_lt
    have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    have hprod_le : cur * 2 ^ bCharWhp n_max ≤ trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      exact Nat.mul_le_mul_right _ hcur.le
    have hidx_lt : cur * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    try simp only [hcs_r, hcr_r] at *
    first
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_of_le_n_max (by dsimp [mkBufRt, brBase, brHdrNA, brPowBChar] at *; omega)
    | exact rt_child_safe henv hep hidx_lt
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrNA, brMaxNodes] at *; omega)

private theorem bufAllocNodeRtProg_spec {c U V w n_max base ep cur ch r_nxt : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (_halloc : 1 ≤ tr.nodeAlloc)
    (hu_lt : tr.nodeAlloc < maxTrieNodesWhp c n_max)
    (hcur : cur < tr.nodeAlloc) (hch : ch < 2 ^ bCharWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)
    let u := tr.nodeAlloc
    let tr1 : BufTrie :=
      { tr with
        nodeAlloc := u + 1
        trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
        nodeParent := Function.update tr.nodeParent u cur
        nodeChar := Function.update tr.nodeChar u ch
        nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = (u, r_nxt) ∧
    memoryCost prog s = 18 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr1 s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨hna_lt_sp, _, hc_seg, _, _⟩ :
      base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
  set u := tr.nodeAlloc
  have hmem_na : s.mem (base + brHdrNA rt) = u := (bufTrieMemRep_iff_rt.mp hrep).2.2.1
  have hu1_fit : Fits w (u + 1) := henv.fits_of_le_n_max (by omega)
  have hu_g : u < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans hu_lt
  set idxC := cur * 2 ^ bCharWhp n_max + ch
  have hidxC : idxC < trieChildEntriesWhp c n_max := by
    unfold trieChildEntriesWhp
    calc cur * 2 ^ bCharWhp n_max + ch
        < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch _
      _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
      _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
  set s1 : Memory.State :=
    { mem := Function.update s.mem (base + brHdrNA rt) (u + 1), frontier := s.frontier }
  set s2 : Memory.State :=
    { mem := writePacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem idxC u,
      frontier := s.frontier }
  have hm_spec := bufAllocMetaRtProg_spec henv hep hu_lt hcur_max hch (s := s2)
  dsimp only at hm_spec
  change _ ∧ _ ∧ _ ∧ _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    readPacked (base + brOffMeta rt) _ _ _ _ = _ ∧
    (∀ idx < 6 * maxTrieNodesWhp c n_max, _ → _ → _ →
      readPacked (base + brOffMeta rt) _ _ _ _ = readPacked (base + brOffMeta rt) _ _ _ _) ∧
    (∀ a, a < base + brOffMeta rt ∨
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤ a →
      _ = _) at hm_spec
  obtain ⟨hfr3, hmc3, hvp3, hbfr3, hm0_eq, hm1_eq, hm2_eq, hm_oth, hm_out⟩ := hm_spec
  set s3 := (Memory.spec 0).clientState s2 (bufAllocMetaRtProg ((rt, u), (cur, ch)))
  dsimp only
  unfold bufAllocNodeRtProg
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) = s3 := by
    rw [StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
      show brBase rt = base from rfl, hmem_na, StateTransitionSpec.clientState_bind,
      clientState_memWrite, StateTransitionSpec.clientState_bind, clientState_writePackedGen,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    rfl
  have hres_eq : (Memory.spec 0).clientResult s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) =
      (u, r_nxt) := by
    rw [StateTransitionSpec.clientResult_bind, clientState_memRead, clientResult_memRead,
      show brBase rt = base from rfl, hmem_na, StateTransitionSpec.clientResult_bind,
      clientState_memWrite, StateTransitionSpec.clientResult_bind, clientState_writePackedGen,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  have hmc_eq : memoryCost
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) s = 18 := by
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
      memoryCost_memRead, clientState_memWrite, memoryCost_memWrite, clientState_writePackedGen,
      memoryCost_writePackedGen]
    change 1 + (1 + (4 + (memoryCost (bufAllocMetaRtProg ((rt, u), (cur, ch))) s2 + 0))) = 18
    rw [hmc3]
  have hvp_eq : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
      (Memory.read (brBase rt + brHdrNA rt) >>= fun u' =>
        Memory.write (brBase rt + brHdrNA rt) (u' + 1) >>= fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), cur * brPowBChar rt + ch), u')
            >>= fun _ =>
            bufAllocMetaRtProg ((rt, u'), (cur, ch)) >>= fun _ => pure (u', r_nxt)) := by
    refine validWhpProg_bind (validWhpProg_read hna_lt_sp) ?_
    rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na]
    refine validWhpProg_bind (validWhpProg_write hna_lt_sp hu1_fit) ?_
    rw [clientState_memWrite]
    refine validWhpProg_bind (validWhpProg_writePacked hw hgk hidxC hc_seg) ?_
    rw [clientState_writePackedGen]
    exact validWhpProg_bind hvp3 (validWhpProg_pure _)
  rw [hs'_eq]
  have hbfr_all : BufEpFrame base c U V w n_max ep s.mem s3.mem :=
    ((bufEpFrame_write_hdrNA hw hep).trans (bufEpFrame_writeChild hw hep hidxC)).trans hbfr3
  refine ⟨hfr3, hres_eq, hmc_eq, hvp_eq, ?_, hbfr_all⟩
  -- Prove `BufTrieMemRep` for `tr1` on `s3.mem`
  have hs2_hdrNA : s2.mem (base + brHdrNA rt) = u + 1 := by
    dsimp only [s2, s1]
    rw [mem_writePacked_of_outside hw hidxC (Or.inl (by omega)), Function.update_self]
  have hs3_hdrNA : s3.mem (base + brHdrNA rt) = u + 1 :=
    (hm_out _ (Or.inl (by omega))).trans hs2_hdrNA
  have hs2_hdrIA : s2.mem (base + brHdrIA rt) = s.mem (base + brHdrIA rt) := by
    dsimp only [s2, s1]
    rw [mem_writePacked_of_outside hw hidxC (Or.inl (by omega)),
      Function.update_of_ne (by omega)]
  have hs3_hdrIA : s3.mem (base + brHdrIA rt) = s.mem (base + brHdrIA rt) :=
    (hm_out _ (Or.inl (by omega))).trans hs2_hdrIA
  have hs3_child : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s3.mem
        (v * 2 ^ bCharWhp n_max + c') =
        Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u) v c' := by
    intro v hv c' hc'
    have hvc_lt : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc v * 2 ^ bCharWhp n_max + c'
          < v * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
        _ = (v + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hv
    have hs3_s2 : readPacked (base + brOffChild rt) (globalPtrBits n_max) w s3.mem
        (v * 2 ^ bCharWhp n_max + c') =
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w s2.mem
          (v * 2 ^ bCharWhp n_max + c') :=
      readPacked_congr_on hw hvc_lt fun a ha1 ha2 => hm_out a (Or.inl (by omega))
    rw [hs3_s2]
    dsimp only [s2]
    by_cases hvc : v = cur ∧ c' = ch
    · rcases hvc with ⟨rfl, rfl⟩
      simp only [Function.update_self]
      exact readPacked_writePacked_self _ _ _ s1.mem idxC hu_g
    · have hne_idx : v * 2 ^ bCharWhp n_max + c' ≠ idxC :=
        fun heq => hvc ((child_idx_eq_iff hc' hch).mp heq)
      rw [readPacked_writePacked_of_ne hw s1.mem hne_idx u]
      dsimp only [s1]
      rw [readPacked_update_outside hw hvc_lt (Or.inl (by omega))]
      have hrep_c : readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
          (v * 2 ^ bCharWhp n_max + c') = tr.trieChild v c' := by
        have hc_r := hrep.2.2.2.2.1 v hv c' hc'
        rcases hep with rfl | rfl <;> exact hc_r
      rw [hrep_c]
      by_cases hv_eq : v = cur
      · subst hv_eq
        have hc_ne : c' ≠ ch := fun h => hvc ⟨rfl, h⟩
        simp [hc_ne]
      · simp [hv_eq]
  have hs2_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s2.mem idx =
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx := by
    intro idx hidx
    dsimp only [s2, s1]
    exact (readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
      (readPacked_update_outside hw hidx (Or.inl (by omega)))
  have hs3_items : ∀ idx < 6 * qEpochWhp n_max + 6,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s3.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem idx := by
    intro idx hidx
    have h32 : readPacked (base + brOffItems rt) (globalPtrBits n_max) w s3.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s2.mem idx :=
      readPacked_congr_on hw hidx fun a ha1 _ => hm_out a (Or.inr (by omega))
    rw [h32]
    dsimp only [s2, s1]
    exact (readPacked_writePacked_disjoint hw hidx hidxC (Or.inr (by omega))).trans
      (readPacked_update_outside hw hidx (Or.inl (by omega)))
  obtain ⟨_, hia, _, hhia, _, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
  rw [bufTrieMemRep_iff_rt]
  dsimp only
  refine ⟨by omega, hia, hs3_hdrNA, hs3_hdrIA.trans hhia, hs3_child,
    fun w' hw1 hw_lt => ?_, fun w' hw_lt => ?_, fun id hid => ?_⟩
  · by_cases hwu : w' = u
    · subst hwu
      simp only [Function.update_self]
      exact ⟨hm0_eq, hm1_eq⟩
    · have hw_u : w' < u := by omega
      simp only [Function.update_of_ne hwu]
      exact ⟨(hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hpar w' hw1 hw_u).1),
        (hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hpar w' hw1 hw_u).2)⟩
  · by_cases hwu : w' = u
    · subst hwu
      simp only [Function.update_self]
      exact ⟨hm2_eq, fun hnz => absurd rfl hnz⟩
    · have hw_u : w' < u := by omega
      simp only [Function.update_of_ne hwu]
      exact ⟨(hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans (hlf w' hw_u).1),
        fun hnz => (hm_oth _ (by omega) (by omega) (by omega) (by omega)).trans
          ((hs2_meta _ (by omega)).trans ((hlf w' hw_u).2 hnz))⟩
  · exact ⟨(hs3_items _ (by omega)).trans (hit id hid).1,
      (hs3_items _ (by omega)).trans (hit id hid).2.1,
      (hs3_items _ (by omega)).trans (hit id hid).2.2⟩

/-- Precondition for one step of `bufEnsurePath` (`p = (rt, (cur, r_cur))`). -/
@[expose] def BufEnsureStepPre (w : ℕ) (p : BufRt × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  BufRtEnvGen w p.1 ∧
  p.2.1 < brMaxNodes p.1 ∧
  s.mem (brBase p.1 + brHdrNA p.1) < brMaxNodes p.1

/-- One character-allocation step of `bufEnsurePath`. -/
@[expose] def bufEnsureStepProg (p : BufRt × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let rt := p.1
  let cur ← pure p.2.1
  let r_cur ← pure p.2.2
  let ch ← pure (r_cur &&& brMaskBChar rt)
  let idx ← pure (cur * brPowBChar rt + ch)
  let nxt ← readPackedGenProg (((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idx)
  let r_nxt ← pure (r_cur >>> brBChar rt)
  if nxt = 0 then
    bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt)
  else
    pure (nxt, r_nxt)

theorem memoryCost_bufEnsureStepProg_pos (p : BufRt × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (bufEnsureStepProg p) s := by
  unfold bufEnsureStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedGen]
  omega

theorem realizes_bufEnsureStep :
    Realizes .exact bufEnsureStepProg
      (WordEncoding.encode (α := BufRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufEnsureStepPre
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  have han := realizes_bufAllocNodeRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, ⟨cur, r_cur⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur, hna_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hcur
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hch_lt : r_cur &&& (2 ^ bCharWhp n_max - 1) < 2 ^ bCharWhp n_max := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx_lt : cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1)) <
        trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1))
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    first
    | exact rt_child_safe henv hep hidx_lt
    | (dsimp only [mkBufRt, brMaxNodes, brMaskBChar, brPowBChar, brBChar, brBase, brOffChild,
         brGBits, brW] at hna_lt ⊢
       try simp only [hcs] at *
       first
       | exact henv.fits_of_le_n_max (hidx_lt.le.trans htc_n)
       | exact ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur, hch_lt, hna_lt⟩)

/-- Parameter-free wrapper for `iterate bufEnsureStepProg`. -/
@[expose] def bufEnsureLoopGenProg
    (p : (BufRt × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) :=
  iterate bufEnsureStepProg p.1.1 p.2 p.1.2

theorem realizes_bufEnsureLoopGen :
    Realizes .exact bufEnsureLoopGenProg
      (WordEncoding.encode (α := (BufRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w p s => iterationSafe bufEnsureStepProg BufEnsureStepPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_bufEnsureStep
    memoryCost_bufEnsureStepProg_pos

private theorem bufEnsureLoop_spec {c U V w n_max base ep : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ rem (tr : BufTrie) (cur r_cur : ℕ) (s : Memory.State),
      BufTrieMemRep base c U V w n_max ep tr s.mem →
      1 ≤ tr.nodeAlloc →
      tr.nodeAlloc + rem ≤ maxTrieNodesWhp c n_max →
      cur < tr.nodeAlloc →
      (∀ v ch, tr.trieChild v ch < tr.nodeAlloc) →
      (∀ w' < tr.nodeAlloc, tr.nodeLeafItem w' ≤ tr.itemAlloc) →
      let prog := bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem)
      let pPure := bufEnsurePath (bCharWhp n_max) r_cur rem 0 tr cur
      let tr1 := pPure.1
      let leaf := pPure.2
      let s1 := (Memory.spec 0).clientState s prog
      iterationSafe bufEnsureStepProg BufEnsureStepPre w rt rem (cur, r_cur) s ∧
      s1.frontier = s.frontier ∧
      ((Memory.spec 0).clientResult s prog).1 = leaf ∧
      memoryCost prog s ≤ 20 * rem ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      BufTrieMemRep base c U V w n_max ep tr1 s1.mem ∧
      BufEpFrame base c U V w n_max ep s.mem s1.mem ∧
      leaf < tr1.nodeAlloc ∧
      tr1.itemAlloc = tr.itemAlloc ∧
      tr1.nodeLeafItem leaf ≤ tr1.itemAlloc := by
  intro rt rem
  have hw := henv.2.1
  have hc_seg := (rt_seg_le c U V w n_max base ep hep).2.2.1
  induction rem with
  | zero =>
    intro tr cur r_cur s hrep _ _ hcur _ hli_ia
    exact ⟨trivial, rfl, rfl, Nat.zero_le _, validWhpProg_pure _,
      hrep, BufEpFrame.refl _, hcur, rfl, hli_ia cur hcur⟩
  | succ rem ih =>
    intro tr cur r_cur s hrep halloc hna_rem hcur hchild_lt hli_ia
    have hu_lt : tr.nodeAlloc < maxTrieNodesWhp c n_max := by omega
    have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans hu_lt
    have hmem_na : s.mem (brBase rt + brHdrNA rt) = tr.nodeAlloc := by
      have h := hrep.2.2.1; rcases hep with rfl | rfl <;> exact h
    have hpre : BufEnsureStepPre w (rt, (cur, r_cur)) s :=
      ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur_max, hmem_na ▸ hu_lt⟩
    set ch := r_cur % 2 ^ bCharWhp n_max with hch_def
    have hch_eq : r_cur &&& brMaskBChar rt = ch := by
      dsimp only [rt, mkBufRt, brMaskBChar, ch]
      exact Nat.and_two_pow_sub_one_eq_mod r_cur (bCharWhp n_max)
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    set idx := cur * 2 ^ bCharWhp n_max + ch
    have hidx_lt : idx < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
    set r_nxt := r_cur / 2 ^ bCharWhp n_max with hr_def
    have hr_eq : r_cur >>> brBChar rt = r_nxt := by
      dsimp only [rt, mkBufRt, brBChar, r_nxt]
      exact Nat.shiftRight_eq_div_pow r_cur (bCharWhp n_max)
    have hrep_ch : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) s.mem
        (cur * brPowBChar rt + (r_cur &&& brMaskBChar rt)) = tr.trieChild cur ch := by
      rw [hch_eq]
      have hc := hrep.2.2.2.2.1 cur hcur_max ch hch_lt
      rcases hep with rfl | rfl <;> exact hc
    set stepP := bufEnsureStepProg (rt, (cur, r_cur))
    have hidx_rt : cur * brPowBChar rt + (r_cur &&& brMaskBChar rt) = idx := by
      rw [hch_eq]; rfl
    dsimp only [bufEnsurePath]
    rw [trieDigit_zero]
    by_cases hn0 : tr.trieChild cur ch = 0
    · rw [ite_eq_left hn0, bufEnsurePath_add_off]
      set u := tr.nodeAlloc
      set tr_step : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      obtain ⟨hfr_a, hres_a, hmc_a, hvp_a, hrep_a, hbfr_a⟩ :=
        bufAllocNodeRtProg_spec henv hep hrep halloc hu_lt hcur hch_lt (r_nxt := r_nxt) (s := s)
      set s_step := (Memory.spec 0).clientState s (bufAllocNodeRtProg ((rt, (cur, ch)), r_nxt))
      have hstep_st : (Memory.spec 0).clientState s stepP = s_step := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_left hn0, hch_eq, hr_eq]
      have hstep_res : (Memory.spec 0).clientResult s stepP = (u, r_nxt) := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_left hn0, hch_eq, hr_eq]
        exact hres_a
      have hstep_mc : memoryCost stepP s = 20 := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [memoryCost_readPackedGen, clientState_readPackedGen, clientResult_readPackedGen,
          hrep_ch, ite_eq_left hn0, hch_eq, hr_eq, hmc_a]
      have hstep_vp : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        refine validWhpProg_bind (validWhpProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, hrep_ch, hch_eq, hr_eq,
          ite_eq_left hn0]
        exact hvp_a
      have hchild_step : ∀ v c', tr_step.trieChild v c' < tr_step.nodeAlloc := by
        intro v c'
        dsimp only [tr_step]
        by_cases hv : v = cur
        · subst hv
          by_cases hc' : c' = ch
          · subst hc'; simp
          · simp only [Function.update_self, Function.update_of_ne hc']
            exact (hchild_lt v c').trans (Nat.lt_succ_self u)
        · simp only [Function.update_of_ne hv]
          exact (hchild_lt v c').trans (Nat.lt_succ_self u)
      have hli_step : ∀ w' < tr_step.nodeAlloc, tr_step.nodeLeafItem w' ≤ tr_step.itemAlloc := by
        intro w' hw'
        dsimp only [tr_step] at hw' ⊢
        by_cases hwu : w' = u
        · subst hwu; simp
        · rw [Function.update_of_ne hwu]
          exact hli_ia w' (by omega)
      obtain ⟨hsafe_r, hfr_r, hres_r, hmc_r, hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩ :=
        ih tr_step u r_nxt s_step hrep_a (by dsimp [tr_step]; omega)
          (by dsimp [tr_step, u]; omega) (by dsimp [tr_step]; omega) hchild_step hli_step
      have hst_all : (Memory.spec 0).clientState s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientState s_step (bufEnsureLoopGenProg ((rt, (u, r_nxt)), rem)) := by
        change (Memory.spec 0).clientState s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
        rfl
      have hres_all : (Memory.spec 0).clientResult s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientResult s_step (bufEnsureLoopGenProg ((rt, (u, r_nxt)), rem)) := by
        change (Memory.spec 0).clientResult s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_res]
        rfl
      rw [hst_all, hres_all]
      refine ⟨⟨hpre, ?_⟩, hfr_r.trans hfr_a, hres_r, ?_, ?_, hrep_r, hbfr_a.trans hbfr_r,
        hlf_lt, hia_r, hli_r⟩
      · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
        exact hsafe_r
      · change memoryCost (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') s ≤
          20 * (rem + 1)
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        change memoryCost stepP s +
          memoryCost (bufEnsureLoopGenProg
            ((rt, (Memory.spec 0).clientResult s stepP), rem))
            ((Memory.spec 0).clientState s stepP) ≤ 20 * (rem + 1)
        rw [hstep_st, hstep_res, hstep_mc]
        omega
      · change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s')
        refine validWhpProg_bind hstep_vp ?_
        change ValidWhpProg w (base + largeSpaceWhp c U V w n_max)
          ((Memory.spec 0).clientState s stepP)
          (bufEnsureLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
        rw [hstep_st, hstep_res]
        exact hvp_r
    · rw [ite_eq_right hn0, bufEnsurePath_add_off]
      set nxt := tr.trieChild cur ch
      have hstep_st : (Memory.spec 0).clientState s stepP = s := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_right hn0]
        rfl
      have hstep_res : (Memory.spec 0).clientResult s stepP = (nxt, r_nxt) := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, hrep_ch, ite_eq_right hn0, hr_eq]
        rfl
      have hstep_mc : memoryCost stepP s = 2 := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [memoryCost_readPackedGen, clientState_readPackedGen, clientResult_readPackedGen,
          hrep_ch, ite_eq_right hn0]
        rfl
      have hstep_vp : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
        dsimp only [stepP, bufEnsureStepProg]
        simp only [pure_bind]
        refine validWhpProg_bind (validWhpProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
        rw [clientState_readPackedGen, clientResult_readPackedGen, hrep_ch, ite_eq_right hn0]
        exact validWhpProg_pure _
      obtain ⟨hsafe_r, hfr_r, hres_r, hmc_r, hvp_r, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩ :=
        ih tr nxt r_nxt s hrep halloc (by omega) (hchild_lt cur ch) hchild_lt hli_ia
      have hst_all : (Memory.spec 0).clientState s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientState s (bufEnsureLoopGenProg ((rt, (nxt, r_nxt)), rem)) := by
        change (Memory.spec 0).clientState s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
        rfl
      have hres_all : (Memory.spec 0).clientResult s
          (bufEnsureLoopGenProg ((rt, (cur, r_cur)), rem + 1)) =
          (Memory.spec 0).clientResult s (bufEnsureLoopGenProg ((rt, (nxt, r_nxt)), rem)) := by
        change (Memory.spec 0).clientResult s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') = _
        rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_res]
        rfl
      rw [hst_all, hres_all]
      refine ⟨⟨hpre, ?_⟩, hfr_r, hres_r, ?_, ?_, hrep_r, hbfr_r, hlf_lt, hia_r, hli_r⟩
      · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
        exact hsafe_r
      · change memoryCost (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s') s ≤
          20 * (rem + 1)
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        change memoryCost stepP s +
          memoryCost (bufEnsureLoopGenProg
            ((rt, (Memory.spec 0).clientResult s stepP), rem))
            ((Memory.spec 0).clientState s stepP) ≤ 20 * (rem + 1)
        rw [hstep_st, hstep_res, hstep_mc]
        omega
      · change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
          (stepP >>= fun s' => iterate bufEnsureStepProg rt rem s')
        refine validWhpProg_bind hstep_vp ?_
        change ValidWhpProg w (base + largeSpaceWhp c U V w n_max)
          ((Memory.spec 0).clientState s stepP)
          (bufEnsureLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
        rw [hstep_st, hstep_res]
        exact hvp_r

/-- Write `(itemLeaf id, itemBucket id, itemLoc id) := (leaf, b, loc)` for `id < qEp`
(`d = (((rt, id), leaf), (b, loc))`). -/
@[irreducible] def bufWriteItemTripleRtProg
    (d : ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1.1
  let id ← pure d.1.1.2
  let idxB ← pure (brQEp rt + id)
  let idxL ← pure (2 * brQEp rt + id)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id), d.1.2)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB), d.2.1)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL), d.2.2)

theorem realizes_bufWriteItemTripleRt :
    Realizes .exact bufWriteItemTripleRtProg
      (WordEncoding.encode (α := ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1.1 ∧ d.1.1.2 < brQEp d.1.1.1)
      (fun _ _ => 0) := by
  unfold bufWriteItemTripleRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨rt, id⟩, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp] at hid ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_items_safe henv hep (by omega)

private theorem bufWriteItemTripleRtProg_spec {c U V w n_max base ep id leaf b loc : ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hid : id < qEpochWhp n_max)
    (hleaf : leaf < maxTrieNodesWhp c n_max)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufWriteItemTripleRtProg (((rt, id), leaf), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem id = leaf ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem
      (qEpochWhp n_max + id) = b ∧
    readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem
      (2 * qEpochWhp n_max + id) = loc ∧
    (∀ idx < 6 * qEpochWhp n_max + 6,
      idx ≠ id → idx ≠ qEpochWhp n_max + id → idx ≠ 2 * qEpochWhp n_max + id →
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + brOffItems rt ∨
      base + brOffItems rt +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hi_seg := (rt_seg_le c U V w n_max base ep hep).2.2.2.2
  obtain ⟨_, _, htl_lt, _, _, hmt_lt, _, _⟩ := large_bounds_lt_n_max hth
  have hM_le := henv.numBuckets_le_n_max
  have hlf_g : leaf < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have hb_g : b < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have hloc_g : loc < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  set qEp := qEpochWhp n_max
  have hi0 : id < 6 * qEp + 6 := by omega
  have hi1 : qEp + id < 6 * qEp + 6 := by omega
  have hi2 : 2 * qEp + id < 6 * qEp + 6 := by omega
  have hpos_q : 0 < qEp := by unfold qEp qEpochWhp; have := scaleWhp_pos n_max; positivity
  set rt := mkBufRt c U V w n_max base ep
  unfold bufWriteItemTripleRtProg
  simp only [pure_bind]
  set m1 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem id leaf
  set m2 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w m1 (qEp + id) b
  set m3 := writePacked (base + brOffItems rt) (globalPtrBits n_max) w m2 (2 * qEp + id) loc
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id), leaf) >>=
        fun _ =>
          writePackedGenProg
            ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), brQEp rt + id), b) >>= fun _ =>
            writePackedGenProg
              ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), 2 * brQEp rt + id), loc)) =
      { mem := m3, frontier := s.frontier } := rfl
  rw [hs'_eq]
  refine ⟨rfl, rfl, ?_,
    ((bufEpFrame_writeItems_lt3q hw hep (by omega)).trans
      (bufEpFrame_writeItems_lt3q hw hep (by omega))).trans
      (bufEpFrame_writeItems_lt3q hw hep (by omega)),
    ?_, ?_, readPacked_writePacked_self _ _ _ m2 (2 * qEp + id) hloc_g,
    fun idx _ hn0 hn1 hn2 => ?_, fun a ha => ?_⟩
  · refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi0 hi_seg) ?_
    rw [clientState_writePackedGen]
    refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi1 hi_seg) ?_
    rw [clientState_writePackedGen]
    exact validWhpProg_writePacked hw hgk hi2 hi_seg
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) loc).trans
      ((readPacked_writePacked_of_ne hw m1 (by omega) b).trans
        (readPacked_writePacked_self _ _ _ s.mem id hlf_g))
  · exact (readPacked_writePacked_of_ne hw m2 (by omega) loc).trans
      (readPacked_writePacked_self _ _ _ m1 (qEp + id) hb_g)
  · exact (readPacked_writePacked_of_ne hw m2 hn2 loc).trans
      ((readPacked_writePacked_of_ne hw m1 hn1 b).trans
        (readPacked_writePacked_of_ne hw s.mem hn0 leaf))
  · exact (mem_writePacked_of_outside hw hi2 ha).trans
      ((mem_writePacked_of_outside hw hi1 ha).trans (mem_writePacked_of_outside hw hi0 ha))

/-- Fresh-slot branch of `bufInsert` (`id1 = 0`, `d = ((rt, leaf), (b, loc))`). -/
@[irreducible] def bufInsertFreshRtProg
    (d : (BufRt × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1
  let leaf ← pure d.1.2
  let addrIA ← pure (brBase rt + brHdrIA rt)
  let id ← Memory.read addrIA
  let id1 ← pure (id + 1)
  Memory.write addrIA id1
  let idxLI ← pure (4 * leaf + 2)
  let idxAct ← pure (4 * leaf + 3)
  let one_v ← pure 1
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), id1)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), one_v)
  bufWriteItemTripleRtProg (((rt, id), leaf), d.2)

theorem realizes_bufInsertFreshRt :
    Realizes .exact bufInsertFreshRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d s => BufRtEnvGen w d.1.1 ∧ d.1.2 < brMaxNodes d.1.1 ∧
        s.mem (brBase d.1.1 + brHdrIA d.1.1) < brQEp d.1.1)
      (fun _ _ => 0) := by
  unfold bufInsertFreshRtProg
  have hwp := realizes_writePackedGen
  have hwt := realizes_bufWriteItemTripleRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  have hcs_w : ∀ a v s', (Memory.spec 0).clientState s' (Memory.write a v) =
      { mem := Function.update s'.mem a v, frontier := s'.frontier } := fun _ _ _ => rfl
  have hcs_wp : ∀ x s', (Memory.spec 0).clientState s' (writePackedGenProg x) =
      { mem := writePacked (x.1.1.1.1 + x.1.1.1.2) x.1.1.2.1 x.1.1.2.2 s'.mem x.1.2 x.2,
        frontier := s'.frontier } := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf, hid_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brQEp, brBase, brHdrIA] at hleaf hid_lt ⊢
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hia32 : brHdrIA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).2.1
    try simp only [hcs_r, hcr_r, hcs_w, hcs_wp] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hia32
    | exact henv.fits_of_le_n_max (by dsimp [mkBufRt, brBase, brHdrIA] at *; omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrIA, brQEp] at *; omega)

/-- Existing-slot branch of `bufInsert` (`id1 ≠ 0`, `id = id1 - 1 < qEp`,
`d = (((rt, leaf), id), (b, loc))`). -/
@[irreducible] def bufInsertUpdRtProg
    (d : ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1.1
  let leaf ← pure d.1.1.2
  let id ← pure d.1.2
  let idxAct ← pure (4 * leaf + 3)
  let idxB ← pure (brQEp rt + id)
  let idxL ← pure (2 * brQEp rt + id)
  let one_v ← pure 1
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct), one_v)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB), d.2.1)
  writePackedGenProg ((((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL), d.2.2)

theorem realizes_bufInsertUpdRt :
    Realizes .exact bufInsertUpdRtProg
      (WordEncoding.encode (α := ((BufRt × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1.1.1 ∧ d.1.1.2 < brMaxNodes d.1.1.1 ∧
        d.1.2 < brQEp d.1.1.1)
      (fun _ _ => 0) := by
  unfold bufInsertUpdRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨rt, leaf⟩, id⟩, ⟨b, loc⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hleaf, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brQEp] at hleaf hid ⊢
    obtain ⟨_, _, _, _, htm_le, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact rt_items_safe henv hep (by omega)

/-- Leaf completion helper for `bufInsert` (`d = ((rt, leaf), (b, loc))`). -/
@[irreducible] def bufInsertLeafRtProg
    (d : (BufRt × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1.1
  let leaf ← pure d.1.2
  let idxLI ← pure (4 * leaf + 2)
  let id1 ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  if id1 = 0 then
    bufInsertFreshRtProg ((rt, leaf), d.2)
  else
    let id ← pure (id1 - 1)
    bufInsertUpdRtProg (((rt, leaf), id), d.2)

/-- Precondition for `bufInsertLeafRtProg`. -/
@[expose] def BufInsertLeafPre (w : ℕ) (d : (BufRt × ℕ) × (ℕ × ℕ))
    (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max base ep tr,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    d.1.1 = mkBufRt c U V w₀ n_max base ep ∧
    BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
    d.1.2 < tr.nodeAlloc ∧
    tr.itemAlloc < qEpochWhp n_max ∧
    tr.nodeLeafItem d.1.2 ≤ tr.itemAlloc

theorem realizes_bufInsertLeafRt :
    Realizes .exact bufInsertLeafRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BufInsertLeafPre
      (fun _ _ => 0) := by
  unfold bufInsertLeafRtProg
  have hrp := realizes_readPackedGen
  have hfr := realizes_bufInsertFreshRt
  have hup := realizes_bufInsertUpdRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, leaf⟩, ⟨b, loc⟩⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hleaf, hia_lt, hli_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna_max := hrep.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    have hrep_li : readPacked (base + brOffMeta (mkBufRt c U V w n_max base ep))
        (globalPtrBits n_max) w s.mem (4 * leaf + 2) = tr.nodeLeafItem leaf := by
      have hm := hrep.2.2.2.2.2.2.1 leaf hleaf
      rcases hep with rfl | rfl <;> exact hm.1
    have hmem_ia : s.mem (base + brHdrIA (mkBufRt c U V w n_max base ep)) = tr.itemAlloc := by
      have hi := hrep.2.2.2.1
      rcases hep with rfl | rfl <;> exact hi
    first
    | exact rt_meta_safe henv hep (by omega)
    | (try simp only [hcs] at *
       simp only [mkBufRt, brBase, brOffMeta, brGBits, brW, brMaxNodes, brHdrIA, brQEp,
         clientResult_readPackedGen] at *
       try rw [hrep_li] at *
       try rw [hmem_ia] at *
       have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
       first
       | exact henv.fits_const (by decide)
       | exact henv.fits_of_le_n_max (by omega)
       | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
       | omega)

private theorem bufInsertLeafRtProg_spec {c U V w n_max base ep leaf b loc : ℕ}
    {tr1 : BufTrie} {s1 : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr1 s1.mem)
    (hlf_lt : leaf < tr1.nodeAlloc)
    (hia_lt : tr1.itemAlloc < qEpochWhp n_max)
    (hli_le : tr1.nodeLeafItem leaf ≤ tr1.itemAlloc)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufInsertLeafRtProg ((rt, leaf), (b, loc))
    let id1 := tr1.nodeLeafItem leaf
    let tr' : BufTrie :=
      if id1 = 0 then
        let id := tr1.itemAlloc
        { tr1 with
          itemAlloc := id + 1
          nodeLeafItem := Function.update tr1.nodeLeafItem leaf (id + 1)
          nodeActive := Function.update tr1.nodeActive leaf 1
          itemLeaf := Function.update tr1.itemLeaf id leaf
          itemBucket := Function.update tr1.itemBucket id b
          itemLoc := Function.update tr1.itemLoc id loc }
      else
        let id := id1 - 1
        { tr1 with
          nodeActive := Function.update tr1.nodeActive leaf 1
          itemBucket := Function.update tr1.itemBucket id b
          itemLoc := Function.update tr1.itemLoc id loc }
    let s' := (Memory.spec 0).clientState s1 prog
    s'.frontier = s1.frontier ∧
    memoryCost prog s1 ≤ 24 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s1 prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s1.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hia_lt_sp, _, hm_seg, hi_seg⟩ :
      base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  obtain ⟨hM_ge, _, htl_lt, _, _, _, hq_lt, _⟩ := large_bounds_lt_n_max hth
  have hM_le := henv.numBuckets_le_n_max
  have hna_max := hrep.1
  have hlf_max : leaf < maxTrieNodesWhp c n_max := hlf_lt.trans_le hna_max
  have hidx2 : 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max := by omega
  have hidx3 : 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max := by omega
  have h1_g : 1 < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
  have hrep_li : readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) =
      tr1.nodeLeafItem leaf := ((bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.2.2.1 leaf hlf_lt).1
  have hmem_ia : s1.mem (base + brHdrIA rt) = tr1.itemAlloc :=
    (bufTrieMemRep_iff_rt.mp hrep).2.2.2.1
  dsimp only
  unfold bufInsertLeafRtProg
  simp only [pure_bind]
  by_cases hid1 : tr1.nodeLeafItem leaf = 0
  · rw [ite_eq_left hid1]
    set id := tr1.itemAlloc
    have hid1_fit : Fits w (id + 1) := henv.fits_of_le_n_max (by omega)
    have hid1_g : id + 1 < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
    set sa : Memory.State :=
      { mem := Function.update s1.mem (base + brHdrIA rt) (id + 1), frontier := s1.frontier }
    set sb : Memory.State :=
      { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w sa.mem
          (4 * leaf + 2) (id + 1),
        frontier := s1.frontier }
    set sc : Memory.State :=
      { mem := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w sb.mem (4 * leaf + 3) 1,
        frontier := s1.frontier }
    have ht_spec := bufWriteItemTripleRtProg_spec henv hep hia_lt hlf_max hb hloc (s := sc)
    dsimp only at ht_spec
    change _ ∧ _ ∧ _ ∧ _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      readPacked (base + brOffItems rt) _ _ _ _ = _ ∧
      (∀ idx < 6 * qEpochWhp n_max + 6, _ → _ → _ →
        readPacked (base + brOffItems rt) _ _ _ _ = readPacked (base + brOffItems rt) _ _ _ _) ∧
      (∀ a, a < base + brOffItems rt ∨
        base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤ a →
        _ = _) at ht_spec
    obtain ⟨hfr_t, hmc_t, hvp_t, hbfr_t, hit0, hit1, hit2, hit_oth, hit_out⟩ := ht_spec
    set sd := (Memory.spec 0).clientState sc (bufWriteItemTripleRtProg (((rt, id), leaf), (b, loc)))
    have hs'_eq : (Memory.spec 0).clientState s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) = sd := by
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen]
      change (Memory.spec 0).clientState s1
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _) = sd
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, StateTransitionSpec.clientState_bind,
        clientState_memWrite, StateTransitionSpec.clientState_bind, clientState_writePackedGen,
        StateTransitionSpec.clientState_bind, clientState_writePackedGen]
      rfl
    have hmc_all : memoryCost
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) s1 ≤ 24 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen]
      change 2 + memoryCost
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _) s1 ≤ 24
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        memoryCost_memRead, clientState_memWrite, memoryCost_memWrite,
        clientState_writePackedGen, memoryCost_writePackedGen,
        clientState_writePackedGen, memoryCost_writePackedGen]
      change 2 + (1 + (1 + (4 + (4 + memoryCost _ sc)))) ≤ 24
      rw [hmc_t]
    have hvp_all : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) := by
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen]
      change ValidWhpProg _ _ s1
        (if readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 2) = 0
         then _ else _)
      rw [hrep_li, ite_eq_left hid1]
      unfold bufInsertFreshRtProg
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia]
      refine validWhpProg_bind (validWhpProg_write hia_lt_sp hid1_fit) ?_
      rw [clientState_memWrite]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hidx2 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hidx3 hm_seg) ?_
      rw [clientState_writePackedGen]
      exact hvp_t
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s1.mem sd.mem :=
      (((bufEpFrame_write_hdrIA hw hep).trans (bufEpFrame_writeMeta hw hep hidx2)).trans
        (bufEpFrame_writeMeta hw hep hidx3)).trans hbfr_t
    refine ⟨hfr_t, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hsd_na : sd.mem (base + brHdrNA rt) = s1.mem (base + brHdrNA rt) := by
      rw [hit_out _ (Or.inl (by omega))]
      dsimp only [sc, sb, sa]
      rw [mem_writePacked_of_outside hw hidx3 (Or.inl (by omega)),
        mem_writePacked_of_outside hw hidx2 (Or.inl (by omega)),
        Function.update_of_ne (by omega)]
    have hsd_ia : sd.mem (base + brHdrIA rt) = id + 1 := by
      rw [hit_out _ (Or.inl (by omega))]
      dsimp only [sc, sb, sa]
      rw [mem_writePacked_of_outside hw hidx3 (Or.inl (by omega)),
        mem_writePacked_of_outside hw hidx2 (Or.inl (by omega)),
        Function.update_self]
    have hsd_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w sd.mem
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem
            (u * 2 ^ bCharWhp n_max + c') := by
      intro u hu c' hc'
      have hidx_c : u * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + c'
            < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      have h_dc : readPacked (base + brOffChild rt) (globalPtrBits n_max) w sd.mem
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w sc.mem
            (u * 2 ^ bCharWhp n_max + c') :=
        readPacked_congr_on hw hidx_c fun a ha1 ha2 => hit_out a (Or.inl (by omega))
      rw [h_dc]
      dsimp only [sc, sb, sa]
      exact (readPacked_writePacked_disjoint hw hidx_c hidx3 (Or.inl (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx_c hidx2 (Or.inl (by omega))).trans
          (readPacked_update_outside hw hidx_c (Or.inl (by omega))))
    have hsd_meta_dc : ∀ idx < 6 * maxTrieNodesWhp c n_max,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w sd.mem idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w sc.mem idx :=
      fun idx hidx => readPacked_congr_on hw hidx fun a _ ha2 => hit_out a (Or.inl (by omega))
    have hsc_items : ∀ idx < 6 * qEpochWhp n_max + 6,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w sc.mem idx =
          readPacked (base + brOffItems rt) (globalPtrBits n_max) w s1.mem idx := by
      intro idx hidx
      dsimp only [sc, sb, sa]
      exact (readPacked_writePacked_disjoint hw hidx hidx3 (Or.inr (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx hidx2 (Or.inr (by omega))).trans
          (readPacked_update_outside hw hidx (Or.inl (by omega))))
    obtain ⟨hna, _, hhna, _, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨hna, by omega, hsd_na.trans hhna, hsd_ia,
      fun u hu c' hc' => (hsd_ch u hu c' hc').trans (hch u hu c' hc'),
      fun u hu1 hu => ?_, fun u hu => ?_, fun j hj => ?_⟩
    · rw [hsd_meta_dc _ (by omega), hsd_meta_dc _ (by omega)]
      dsimp only [sc, sb, sa]
      exact ⟨(readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hpar u hu1 hu).1)),
        (readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hpar u hu1 hu).2))⟩
    · rw [hsd_meta_dc _ (by omega)]
      by_cases hul : u = leaf
      · subst hul
        simp only [Function.update_self]
        dsimp only [sc, sb]
        refine ⟨(readPacked_writePacked_of_ne hw sb.mem (by omega) 1).trans
          (readPacked_writePacked_self _ _ _ sa.mem (4 * u + 2) hid1_g), fun _ => ?_⟩
        rw [hsd_meta_dc _ (by omega)]
        exact readPacked_writePacked_self _ _ _ sb.mem (4 * u + 3) h1_g
      · simp only [Function.update_of_ne hul]
        dsimp only [sc, sb, sa]
        refine ⟨(readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              (hlf u hu).1)), fun hnz => ?_⟩
        rw [hsd_meta_dc _ (by omega)]
        dsimp only [sc, sb, sa]
        exact (readPacked_writePacked_of_ne hw _ (by omega) 1).trans
          ((readPacked_writePacked_of_ne hw _ (by omega) (id + 1)).trans
            ((readPacked_update_outside hw
                (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega) (Or.inl (by omega))).trans
              ((hlf u hu).2 hnz)))
    · by_cases hji : j = id
      · subst hji
        simp only [Function.update_self]
        exact ⟨hit0, hit1, hit2⟩
      · have hj_lt : j < id := by omega
        simp only [Function.update_of_ne hji]
        exact ⟨(hit_oth _ (by omega) hji (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).1),
          (hit_oth _ (by omega) (by omega) (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).2.1),
          (hit_oth _ (by omega) (by omega) (by omega) (by omega)).trans
            ((hsc_items _ (by omega)).trans (hit j hj_lt).2.2)⟩
  · rw [ite_eq_right hid1]
    set id := tr1.nodeLeafItem leaf - 1
    have hid_ia : id < tr1.itemAlloc := by omega
    have hid_q : id < qEpochWhp n_max := hid_ia.trans hia_lt
    have hb_g : b < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
    have hloc_g : loc < 2 ^ globalPtrBits n_max := lt_two_pow_gBits_of_le (by omega)
    set qEp := qEpochWhp n_max
    have hiB : qEp + id < 6 * qEp + 6 := by omega
    have hiL : 2 * qEp + id < 6 * qEp + 6 := by omega
    set ma := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s1.mem (4 * leaf + 3) 1
    set mb := writePacked (base + brOffItems rt) (globalPtrBits n_max) w ma (qEp + id) b
    set mc := writePacked (base + brOffItems rt) (globalPtrBits n_max) w mb (2 * qEp + id) loc
    have hs'_eq : (Memory.spec 0).clientState s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) =
        { mem := mc, frontier := s1.frontier } := by
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl,
        hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_writePackedGen,
        StateTransitionSpec.clientState_bind, clientState_writePackedGen,
        clientState_writePackedGen]
      rfl
    have hmc_all : memoryCost
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) s1 ≤ 24 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen,
        show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen]
      omega
    have hvp_all : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s1
        (readPackedGenProg
          (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), 4 * leaf + 2) >>= fun v =>
          if v = 0 then bufInsertFreshRtProg ((rt, leaf), (b, loc))
          else bufInsertUpdRtProg (((rt, leaf), v - 1), (b, loc))) := by
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx2 hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen,
        show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hrep_li, ite_eq_right hid1]
      unfold bufInsertUpdRtProg
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hidx3 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hiB hi_seg) ?_
      rw [clientState_writePackedGen]
      exact validWhpProg_writePacked hw hgk hiL hi_seg
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s1.mem mc :=
      ((bufEpFrame_writeMeta hw hep hidx3).trans
        (bufEpFrame_writeItems_lt3q hw hep (by omega))).trans
        (bufEpFrame_writeItems_lt3q hw hep (by omega))
    refine ⟨rfl, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hmc_hdr : ∀ h < 32, mc (base + h) = s1.mem (base + h) := fun h hh =>
      (mem_writePacked_of_outside hw hiL (Or.inl (by omega))).trans
        ((mem_writePacked_of_outside hw hiB (Or.inl (by omega))).trans
          (mem_writePacked_of_outside hw hidx3 (Or.inl (by omega))))
    have hmc_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w mc
          (u * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s1.mem
            (u * 2 ^ bCharWhp n_max + c') := by
      intro u hu c' hc'
      have hidx_c : u * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + c'
            < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact (readPacked_writePacked_disjoint hw hidx_c hiL (Or.inl (by omega))).trans
        ((readPacked_writePacked_disjoint hw hidx_c hiB (Or.inl (by omega))).trans
          (readPacked_writePacked_disjoint hw hidx_c hidx3 (Or.inl (by omega))))
    have hmc_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mc idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w ma idx := fun idx hidx =>
      (readPacked_writePacked_disjoint hw hidx hiL (Or.inl (by omega))).trans
        (readPacked_writePacked_disjoint hw hidx hiB (Or.inl (by omega)))
    have hma_items : ∀ idx < 6 * qEp + 6,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w ma idx =
          readPacked (base + brOffItems rt) (globalPtrBits n_max) w s1.mem idx := fun idx hidx =>
      readPacked_writePacked_disjoint hw hidx hidx3 (Or.inr (by omega))
    obtain ⟨hna, hia, hhna, hhia, hch, hpar, hlf, hit⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨hna, hia,
      (hmc_hdr _ hna32).trans hhna,
      (hmc_hdr _ hia32).trans hhia,
      fun u hu c' hc' => (hmc_ch u hu c' hc').trans (hch u hu c' hc'),
      fun u hu1 hu => ?_, fun u hu => ?_, fun j hj => ?_⟩
    · rw [hmc_meta _ (by omega), hmc_meta _ (by omega)]
      exact ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hpar u hu1 hu).1,
        (readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hpar u hu1 hu).2⟩
    · rw [hmc_meta _ (by omega)]
      by_cases hul : u = leaf
      · subst hul
        simp only [Function.update_self]
        refine ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hlf u hu).1,
          fun _ => ?_⟩
        rw [hmc_meta _ (by omega)]
        exact readPacked_writePacked_self _ _ _ s1.mem (4 * u + 3) h1_g
      · simp only [Function.update_of_ne hul]
        refine ⟨(readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans (hlf u hu).1,
          fun hnz => ?_⟩
        rw [hmc_meta _ (by omega)]
        exact (readPacked_writePacked_of_ne hw s1.mem (by omega) 1).trans ((hlf u hu).2 hnz)
    · have hj0 : readPacked (base + brOffItems rt) (globalPtrBits n_max) w mc j = tr1.itemLeaf j :=
        ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
          ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
            (hma_items _ (by omega)))).trans (hit j hj).1
      by_cases hji : j = id
      · subst hji
        simp only [Function.update_self]
        exact ⟨hj0,
          (readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            (readPacked_writePacked_self _ _ _ ma (qEp + id) hb_g),
          readPacked_writePacked_self _ _ _ mb (2 * qEp + id) hloc_g⟩
      · simp only [Function.update_of_ne hji]
        exact ⟨hj0,
          ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
              (hma_items _ (by omega)))).trans (hit j hj).2.1,
          ((readPacked_writePacked_of_ne hw mb (by omega) loc).trans
            ((readPacked_writePacked_of_ne hw ma (by omega) b).trans
              (hma_items _ (by omega)))).trans (hit j hj).2.2⟩

/-- Precondition for `bufInsertGenProg` (`d = ((((cp, base), ep), rKey), (b, loc))`). -/
@[expose] def BufInsertGenPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max tr mapFn,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.2 ∧
    d.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    (d.1.1.2 = 0 ∨ d.1.1.2 = 1) ∧
    BufTrieMemRep d.1.1.1.2 c U V w₀ n_max d.1.1.2 tr s.mem ∧
    ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn ∧
    tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
    tr.itemAlloc < qEpochWhp n_max ∧
    d.2.1 < numBucketsWhp n_max ∧
    d.2.2 < totalLocalCoordsWhp n_max

/-- Parameter-free `bufInsert` (`d = ((((cp, base), ep), rKey), (b, loc))`). -/
@[expose] def bufInsertGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt ← mkBufRtGenProg d.1.1
  let zero_v ← pure 0
  let eres ← bufEnsureLoopGenProg ((rt, (zero_v, d.1.2)), brCTab rt)
  bufInsertLeafRtProg ((rt, eres.1), d.2)

theorem bufInsertGenProg_spec {c U V w n_max base ep rKey b loc : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn)
    (hna_cap : tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max)
    (hia_cap : tr.itemAlloc < qEpochWhp n_max)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := bufInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), ep), rKey), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) tr rKey b loc
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 20 * cTabWhp c + 24 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hchild_lt : ∀ v ch, tr.trieChild v ch < tr.nodeAlloc := by
    intro v ch
    by_cases hnz : tr.trieChild v ch = 0
    · rw [hnz]; exact hv.1
    · exact ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
  have hli_ia : ∀ w' < tr.nodeAlloc, tr.nodeLeafItem w' ≤ tr.itemAlloc := by
    intro w' hw'
    by_cases hnz : tr.nodeLeafItem w' = 0
    · rw [hnz]; exact Nat.zero_le _
    · exact (hv.2.2.2.2.choose_spec.2.2.2 w' hw' hnz).2.1
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hfr1, hres1, hmc1, hvp1, hrep1, hbfr1, hlf_lt1, hia_eq1, hli_le1⟩ :=
    bufEnsureLoop_spec henv hep (cTabWhp c) tr 0 rKey s hrep hv.1 hna_cap hv.1 hchild_lt hli_ia
  set pPure := bufEnsurePath (bCharWhp n_max) rKey (cTabWhp c) 0 tr 0
  set eprog := bufEnsureLoopGenProg ((rt, (0, rKey)), cTabWhp c)
  set s1 := (Memory.spec 0).clientState s eprog
  obtain ⟨hfr2, hmc2, hvp2, hrep2, hbfr2⟩ :=
    bufInsertLeafRtProg_spec henv hep hrep1 hlf_lt1 (hia_eq1 ▸ hia_cap) hli_le1 hb hloc (s1 := s1)
  have hbr_cTab : brCTab rt = cTabWhp c := rfl
  dsimp only
  unfold bufInsertGenProg
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufEnsureLoopGenProg ((rt', (0, rKey)), brCTab rt') >>= fun er =>
          bufInsertLeafRtProg ((rt', er.1), (b, loc))) =
      (Memory.spec 0).clientState s1 (bufInsertLeafRtProg ((rt, pPure.2), (b, loc))) := by
    rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res, hbr_cTab,
      StateTransitionSpec.clientState_bind, hres1]
  rw [hs'_eq]
  refine ⟨hfr2.trans hfr1, ?_, ?_, hrep2, hbfr1.trans hbfr2⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr_cTab, hres1]
    change 0 + (memoryCost eprog s + memoryCost (bufInsertLeafRtProg ((rt, pPure.2), (b, loc))) s1)
      ≤ _
    dsimp only [eprog, rt] at hmc1 hmc2 ⊢
    omega
  · refine validWhpProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr_cTab]
    refine validWhpProg_bind hvp1 ?_
    rw [hres1]
    exact hvp2

theorem realizes_bufInsertGen :
    Realizes .exact bufInsertGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BufInsertGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hel := realizes_bufEnsureLoopGen
  have hil := realizes_bufInsertLeafRt
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, ep⟩, rKey⟩, ⟨b, loc⟩⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, hv,
      hna_cap, hia_cap, _, _⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hchild_lt : ∀ v ch, tr.trieChild v ch < tr.nodeAlloc := by
      intro v ch
      by_cases hnz : tr.trieChild v ch = 0
      · rw [hnz]; exact hv.1
      · exact ((hv.2.2.2.2.choose_spec.2.2.1 v ch).mp hnz).2.1
    have hli_ia : ∀ w' < tr.nodeAlloc, tr.nodeLeafItem w' ≤ tr.itemAlloc := by
      intro w' hw'
      by_cases hnz : tr.nodeLeafItem w' = 0
      · rw [hnz]; exact Nat.zero_le _
      · exact (hv.2.2.2.2.choose_spec.2.2.2 w' hw' hnz).2.1
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, _, hres1, _, _, hrep1, _, hlf_lt1, hia_eq1, hli_le1⟩ :=
      bufEnsureLoop_spec henv hep (cTabWhp c) tr 0 rKey s hrep hv.1 hna_cap hv.1 hchild_lt hli_ia
    try simp only [hrt_st, hrt_res] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsafe
    | exact ⟨c, U, V, w, n_max, base, ep, _, henv, hep, rfl, hrep1,
        hres1 ▸ hlf_lt1, hia_eq1 ▸ hia_cap, hres1 ▸ hli_le1⟩

/-! ## Section 4: `bufCheckSlotGenProg` and `bufClearStepsGenProg` -/

/-- Leaf check helper for `bufCheckSlot` (`d = ((rt, id), leaf)` with `id < qEp`,
`leaf < maxNodes`). -/
@[irreducible] def bufCheckSlotLeafRtProg
    (d : (BufRt × ℕ) × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1.1
  let id ← pure d.1.2
  let leaf ← pure d.2
  let idxLI ← pure (4 * leaf + 2)
  let li ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
  let id1 ← pure (id + 1)
  if li = id1 then
    let idxAct ← pure (4 * leaf + 3)
    let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
    if act = 0 then
      pure (0, (0, 0))
    else
      bufReadItemPairRtProg (rt, id)
  else
    pure (0, (0, 0))

private theorem bufCheckSlotLeafRtProg_eq (d : (BufRt × ℕ) × ℕ) :
    bufCheckSlotLeafRtProg d = (do
      let rt := d.1.1
      let id ← pure d.1.2
      let leaf ← pure d.2
      let idxLI ← pure (4 * leaf + 2)
      let li ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI)
      let id1 ← pure (id + 1)
      if li = id1 then
        let idxAct ← pure (4 * leaf + 3)
        let act ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxAct)
        if act = 0 then
          pure (0, (0, 0))
        else
          bufReadItemPairRtProg (rt, id)
      else
        pure (0, (0, 0))) := by
  unfold bufCheckSlotLeafRtProg; rfl

theorem realizes_bufCheckSlotLeafRt :
    Realizes .exact bufCheckSlotLeafRtProg
      (WordEncoding.encode (α := (BufRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d _ => BufRtEnvGen w d.1.1 ∧ d.1.2 < brQEp d.1.1 ∧ d.2 < brMaxNodes d.1.1)
      (fun _ _ => 0) := by
  unfold bufCheckSlotLeafRtProg
  have hrp := realizes_readPackedGen
  have hrip := realizes_bufReadItemPairRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨rt, id⟩, leaf⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid, hleaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp, brMaxNodes] at hid hleaf ⊢
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hid

/-- In-bounds helper for `bufCheckSlot` (`d = (rt, id)` with `id < qEp`). -/
@[irreducible] def bufCheckSlotInBoundsRtProg
    (d : BufRt × ℕ) : Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let id ← pure d.2
  let leaf ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id)
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let na ← Memory.read addrNA
  if leaf < na then
    bufCheckSlotLeafRtProg ((rt, id), leaf)
  else
    pure (0, (0, 0))

private theorem bufCheckSlotInBoundsRtProg_eq (d : BufRt × ℕ) :
    bufCheckSlotInBoundsRtProg d = (do
      let rt := d.1
      let id ← pure d.2
      let leaf ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), id)
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let na ← Memory.read addrNA
      if leaf < na then
        bufCheckSlotLeafRtProg ((rt, id), leaf)
      else
        pure (0, (0, 0))) := by
  unfold bufCheckSlotInBoundsRtProg; rfl

theorem realizes_bufCheckSlotInBoundsRt :
    Realizes .exact bufCheckSlotInBoundsRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d s => BufRtEnvGen w d.1 ∧ d.2 < brQEp d.1 ∧
        s.mem (brBase d.1 + brHdrNA d.1) ≤ brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufCheckSlotInBoundsRtProg
  have hrp := realizes_readPackedGen
  have hsl := realizes_bufCheckSlotLeafRt
  have hcs_p : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, id⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid, hna_le⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp, brMaxNodes, brBase, brHdrNA] at hid hna_le ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    try simp only [hcs_p, hcs_r, hcr_r] at *
    first
    | exact henv.fits_hdr_addr hna32
    | exact rt_items_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hid
    | (dsimp only [mkBufRt, brMaxNodes, brBase, brHdrNA] at *; omega)

/-- Parameter-free `bufCheckSlot` (`d = (((cp, base), ep), id)`), returning `(0, (0, 0))` on `none`
and `(1, (b, loc))` on `some (b, loc)`. -/
@[expose] def bufCheckSlotGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt ← mkBufRtGenProg d.1
  let addrIA ← pure (brBase rt + brHdrIA rt)
  let ia ← Memory.read addrIA
  if d.2 < ia then
    bufCheckSlotInBoundsRtProg (rt, d.2)
  else
    pure (0, (0, 0))

theorem bufCheckSlotGenProg_spec {c U V w n_max base ep id : ℕ}
    {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let prog := bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), ep), id)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match bufCheckSlot tr id with
       | none => (0, (0, 0))
       | some (b, loc) => (1, (b, loc))) ∧
    memoryCost prog s ≤ 12 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨hna_lt_sp, hia_lt_sp, _, hm_seg, hi_seg⟩ := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  have hmem_na : s.mem (base + brHdrNA rt) = tr.nodeAlloc := by
    have h := hrep.2.2.1; rcases hep with rfl | rfl <;> exact h
  have hmem_ia : s.mem (base + brHdrIA rt) = tr.itemAlloc := by
    have h := hrep.2.2.2.1; rcases hep with rfl | rfl <;> exact h
  have hna_max := hrep.1
  have hia_le := hrep.2.1
  have hrep_meta : ∀ u < tr.nodeAlloc,
      readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 2) =
        tr.nodeLeafItem u ∧
      (tr.nodeLeafItem u ≠ 0 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 3) =
          tr.nodeActive u) := by
    have hm := hrep.2.2.2.2.2.2.1; rcases hep with rfl | rfl <;> exact hm
  have hrep_items : ∀ j < tr.itemAlloc,
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem j = tr.itemLeaf j ∧
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (qEpochWhp n_max + j) =
        tr.itemBucket j ∧
      readPacked (base + brOffItems rt) (globalPtrBits n_max) w s.mem (2 * qEpochWhp n_max + j) =
        tr.itemLoc j := by
    have hi := hrep.2.2.2.2.2.2.2; rcases hep with rfl | rfl <;> exact hi
  unfold bufCheckSlotGenProg
  simp only [pure_bind]
  dsimp only [bufCheckSlot]
  by_cases hid : id < tr.itemAlloc
  · obtain ⟨hlf_r, hb_r, hloc_r⟩ := hrep_items id hid
    set leaf := tr.itemLeaf id
    have hid6 : id < 6 * qEpochWhp n_max + 6 := by omega
    have hidB : brQEp rt + id < 6 * qEpochWhp n_max + 6 := by dsimp [rt, mkBufRt, brQEp]; omega
    have hidL : 2 * brQEp rt + id < 6 * qEpochWhp n_max + 6 := by dsimp [rt, mkBufRt, brQEp]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res,
        StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_left hid, bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, StateTransitionSpec.clientState_bind, clientState_memRead,
        clientResult_memRead]
      split_ifs with h1
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
        split_ifs with h2
        · rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen]
          split_ifs with h3
          · rfl
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
              StateTransitionSpec.clientState_bind, clientState_readPackedGen]
            rfl
        · rfl
      · rfl
    · rw [StateTransitionSpec.clientResult_bind, hrt_st, hrt_res,
        StateTransitionSpec.clientResult_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_left hid, ite_eq_left hid,
        bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, StateTransitionSpec.clientResult_bind, clientState_memRead,
        clientResult_memRead, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hlf_r, hmem_na]
      by_cases hlf_lt : leaf < tr.nodeAlloc
      · rw [ite_eq_left hlf_lt, bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
          clientResult_readPackedGen, show brBase rt = base from rfl,
          show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl]
        obtain ⟨hli_eq, hact_eq⟩ := hrep_meta leaf hlf_lt
        rw [hli_eq]
        by_cases hli_id : tr.nodeLeafItem leaf = id + 1
        · rw [ite_eq_left hli_id, StateTransitionSpec.clientResult_bind, clientState_readPackedGen,
            clientResult_readPackedGen, hact_eq (by omega)]
          by_cases hact0 : tr.nodeActive leaf = 0
          · simp [hli_id, hact0]
          · simp only [hli_id, hact0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
            rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind, StateTransitionSpec.clientResult_bind,
              clientResult_readPackedGen, StateTransitionSpec.clientResult_pure]
            exact Prod.ext rfl (Prod.ext hb_r hloc_r)
        · simp [hli_id]
      · rw [ite_eq_right hlf_lt]
        have hz := hv.2.1 leaf (Nat.not_lt.mp hlf_lt)
        simp [leaf, hz]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, memoryCost_memRead, ite_eq_left hid,
        bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_readPackedGen, memoryCost_memRead]
      split_ifs with h1
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
          memoryCost_readPackedGen]
        split_ifs with h2
        · simp only [memoryCost_bind, memoryCost_readPackedGen]
          split_ifs with h3
          · change 0 + (1 + (2 + (1 + (2 + (2 + 0))))) ≤ 12; omega
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
              memoryCost_readPackedGen]
            change 0 + (1 + (2 + (1 + (2 + (2 + (2 + (2 + 0))))))) ≤ 12; omega
        · change 0 + (1 + (2 + (1 + (2 + 0)))) ≤ 12; omega
      · change 0 + (1 + (2 + (1 + 0))) ≤ 12; omega
    · refine validWhpProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res]
      refine validWhpProg_bind (validWhpProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        ite_eq_left hid, bufCheckSlotInBoundsRtProg_eq]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hid6 hi_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hlf_r]
      refine validWhpProg_bind (validWhpProg_read hna_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, hmem_na]
      split_ifs with hlf_lt
      · rw [bufCheckSlotLeafRtProg_eq]
        simp only [pure_bind]
        refine validWhpProg_bind
          (validWhpProg_readPacked hw (show 4 * leaf + 2 < 6 * maxTrieNodesWhp c n_max by omega)
            hm_seg) ?_
        rw [clientState_readPackedGen]
        split_ifs with h2
        · refine validWhpProg_bind
            (validWhpProg_readPacked hw (show 4 * leaf + 3 < 6 * maxTrieNodesWhp c n_max by omega)
              hm_seg) ?_
          rw [clientState_readPackedGen]
          split_ifs with h3
          · exact validWhpProg_pure _
          · rw [bufReadItemPairRtProg_eq]
            simp only [pure_bind]
            refine validWhpProg_bind (validWhpProg_readPacked hw hidB hi_seg) ?_
            rw [clientState_readPackedGen]
            exact validWhpProg_bind (validWhpProg_readPacked hw hidL hi_seg) (validWhpProg_pure _)
        · exact validWhpProg_pure _
      · exact validWhpProg_pure _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res,
        StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_right hid]
      rfl
    · rw [StateTransitionSpec.clientResult_bind, hrt_st, hrt_res,
        StateTransitionSpec.clientResult_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, ite_eq_right hid, ite_eq_right hid]
      rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrt_st, hrt_res, hrt_mc, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_ia, memoryCost_memRead, ite_eq_right hid]
      change 0 + (1 + 0) ≤ 12; omega
    · refine validWhpProg_bind hrt_vp ?_
      rw [hrt_st, hrt_res]
      refine validWhpProg_bind (validWhpProg_read hia_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_ia,
        ite_eq_right hid]
      exact validWhpProg_pure _

theorem realizes_bufCheckSlotGen :
    Realizes .exact bufCheckSlotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufReadGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hsib := realizes_bufCheckSlotInBoundsRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, id⟩
    obtain ⟨c, U, V, w₀, n_max, tr, mapFn, henv, rfl, hep, hrep, _⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    have hia32 : brHdrIA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).2.1
    have hmem_na : s.mem (base + brHdrNA (mkBufRt c U V w n_max base ep)) = tr.nodeAlloc := by
      have hn := hrep.2.2.1; rcases hep with rfl | rfl <;> exact hn
    have hmem_ia : s.mem (base + brHdrIA (mkBufRt c U V w n_max base ep)) = tr.itemAlloc := by
      have hi := hrep.2.2.2.1; rcases hep with rfl | rfl <;> exact hi
    try simp only [hrt_st, hrt_res, hcs_r, hcr_r] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_hdr_addr hia32
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrIA, brHdrNA] at hmem_ia hmem_na
       simp only [mkBufRt, brBase, brHdrIA, brQEp, brHdrNA, brMaxNodes, hmem_na] at *
       try simp only [hmem_ia] at *
       have := hrep.1
       have := hrep.2.1
       omega)

/-- Clear `trieChild par ch := 0` when `ch < 2 ^ bChar` (`d = (rt, (par, ch))`,
`par < maxNodes`). -/
@[irreducible] def bufClearEdgeRtProg (d : BufRt × (ℕ × ℕ)) : Memory.Prog Unit := do
  let rt := d.1
  if d.2.2 < brPowBChar rt then
    let idxC ← pure (d.2.1 * brPowBChar rt + d.2.2)
    let zero_v ← pure 0
    writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), zero_v)
  else
    pure ()

private theorem bufClearEdgeRtProg_eq (d : BufRt × (ℕ × ℕ)) :
    bufClearEdgeRtProg d = (do
      let rt := d.1
      if d.2.2 < brPowBChar rt then
        let idxC ← pure (d.2.1 * brPowBChar rt + d.2.2)
        let zero_v ← pure 0
        writePackedGenProg ((((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idxC), zero_v)
      else
        pure ()) := by
  unfold bufClearEdgeRtProg; rfl

theorem realizes_bufClearEdgeRt :
    Realizes .exact bufClearEdgeRtProg
      (WordEncoding.encode (α := BufRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2.1 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearEdgeRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨rt, ⟨par, ch⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hpar⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brPowBChar] at *
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hidx_lt : ch < 2 ^ bCharWhp n_max →
        par * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := fun hch => by
      unfold trieChildEntriesWhp
      calc par * 2 ^ bCharWhp n_max + ch
          < par * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch _
        _ = (par + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hpar
    first
    | exact henv.fits_of_le_n_max ((hidx_lt (by omega)).le.trans htc_n)
    | exact rt_child_safe henv hep (hidx_lt (by omega))

/-- Tail writes of `bufClearOne` (`1 < na`, `u = na - 1`): clear `nodeLeafItem u := 0` and update
`(hdrNA, hdrIA) := (u, 0)`. -/
@[irreducible] def bufClearPopTailRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let idxLI ← pure (4 * d.2 + 2)
  let zero_v ← pure 0
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let addrIA ← pure (brBase rt + brHdrIA rt)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), zero_v)
  Memory.write addrNA d.2
  Memory.write addrIA zero_v

private theorem bufClearPopTailRtProg_eq (d : BufRt × ℕ) :
    bufClearPopTailRtProg d = (do
      let rt := d.1
      let idxLI ← pure (4 * d.2 + 2)
      let zero_v ← pure 0
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let addrIA ← pure (brBase rt + brHdrIA rt)
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxLI), zero_v)
      Memory.write addrNA d.2
      Memory.write addrIA zero_v) := by
  unfold bufClearPopTailRtProg; rfl

theorem realizes_bufClearPopTailRt :
    Realizes .exact bufClearPopTailRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearPopTailRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨rt, u⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    obtain ⟨hna32, hia32, _⟩ := rt_disj_le c U V w n_max base ep hep
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_hdr_addr hia32
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)

/-- Pop branch of `bufClearOne` (`1 < na`, `u = na - 1`). -/
@[irreducible] def bufClearPopRtProg (d : BufRt × ℕ) : Memory.Prog Unit := do
  let rt := d.1
  let u ← pure d.2
  let idxP ← pure (4 * u)
  let idxC ← pure (4 * u + 1)
  let par ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxP)
  let ch ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxC)
  bufClearEdgeRtProg (rt, (par, ch))
  bufClearPopTailRtProg (rt, u)

private theorem bufClearPopRtProg_eq (d : BufRt × ℕ) :
    bufClearPopRtProg d = (do
      let rt := d.1
      let u ← pure d.2
      let idxP ← pure (4 * u)
      let idxC ← pure (4 * u + 1)
      let par ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxP)
      let ch ← readPackedGenProg (((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), idxC)
      bufClearEdgeRtProg (rt, (par, ch))
      bufClearPopTailRtProg (rt, u)) := by
  unfold bufClearPopRtProg; rfl

theorem realizes_bufClearPopRt :
    Realizes .exact bufClearPopRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d s => BufRtEnvGen w d.1 ∧ d.2 < brMaxNodes d.1 ∧
        readPacked (brBase d.1 + brOffMeta d.1) (brGBits d.1) (brW d.1) s.mem (4 * d.2) <
          brMaxNodes d.1)
      (fun _ _ => 0) := by
  unfold bufClearPopRtProg
  have hrp := realizes_readPackedGen
  have hce := realizes_bufClearEdgeRt
  have hpt := realizes_bufClearPopTailRt
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, u⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hu, hpar_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes] at hu hpar_lt ⊢
    obtain ⟨_, _, _, _, htm_le, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
    try simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_meta_safe henv hep (by omega)
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | exact hu
    | (simp only [mkBufRt, brMaxNodes, clientResult_readPackedGen] at *; exact hpar_lt)

/-- Root branch of `bufClearOne` (`na ≤ 1`): clear `nodeLeafItem 0 := 0` and set
`(hdrNA, hdrIA) := (1, 0)`. -/
@[irreducible] def bufClearRootRtProg (rt : BufRt) : Memory.Prog Unit := do
  let two_v ← pure 2
  let one_v ← pure 1
  let zero_v ← pure 0
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let addrIA ← pure (brBase rt + brHdrIA rt)
  writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), two_v), zero_v)
  Memory.write addrNA one_v
  Memory.write addrIA zero_v

private theorem bufClearRootRtProg_eq (rt : BufRt) :
    bufClearRootRtProg rt = (do
      let two_v ← pure 2
      let one_v ← pure 1
      let zero_v ← pure 0
      let addrNA ← pure (brBase rt + brHdrNA rt)
      let addrIA ← pure (brBase rt + brHdrIA rt)
      writePackedGenProg ((((brBase rt, brOffMeta rt), (brGBits rt, brW rt)), two_v), zero_v)
      Memory.write addrNA one_v
      Memory.write addrIA zero_v) := by
  unfold bufClearRootRtProg; rfl

theorem realizes_bufClearRootRt :
    Realizes .exact bufClearRootRtProg
      (WordEncoding.encode (α := BufRt))
      (WordEncoding.encode (α := Unit))
      (fun w rt _ => BufRtEnvGen w rt)
      (fun _ _ => 0) := by
  unfold bufClearRootRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals
    obtain ⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hmt2 : 2 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    obtain ⟨hna32, hia32, _⟩ := rt_disj_le c U V w n_max base ep hep
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact henv.fits_hdr_addr hia32
    | exact rt_meta_safe henv hep (by omega)

/-- Precondition for `bufClearOneRtProg`. -/
@[expose] def BufClearOnePre (w : ℕ) (p : BufRt × Unit) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max base ep tr,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    p.1 = mkBufRt c U V w₀ n_max base ep ∧
    BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
    ClearableBufTrie tr

/-- One elementary cleanup step `bufClearOne`. -/
@[expose] def bufClearOneRtProg (p : BufRt × Unit) : Memory.Prog Unit := do
  let rt := p.1
  let addrNA ← pure (brBase rt + brHdrNA rt)
  let na ← Memory.read addrNA
  let one_v ← pure 1
  if one_v < na then
    let u ← pure (na - 1)
    bufClearPopRtProg (rt, u)
  else
    bufClearRootRtProg rt

theorem memoryCost_bufClearOneRtProg_pos (p : BufRt × Unit) (s : Memory.State) :
    1 ≤ memoryCost (bufClearOneRtProg p) s := by
  unfold bufClearOneRtProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_memRead]
  omega

theorem realizes_bufClearOneRt :
    Realizes .exact bufClearOneRtProg
      (WordEncoding.encode (α := BufRt × Unit))
      (WordEncoding.encode (α := Unit))
      BufClearOnePre
      (fun _ _ => 0) := by
  have hcp := realizes_bufClearPopRt
  have hcr := realizes_bufClearRootRt
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  have hcr_r : ∀ a s', (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, ⟨⟩⟩
    obtain ⟨c, U, V, w₀, n_max, base, ep, tr, henv, hep, rfl, hrep, hclr⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hna32 : brHdrNA (mkBufRt c U V w n_max base ep) < 32 :=
      (rt_disj_le c U V w n_max base ep hep).1
    have hmem_na : s.mem (base + brHdrNA (mkBufRt c U V w n_max base ep)) = tr.nodeAlloc := by
      have hn := hrep.2.2.1; rcases hep with rfl | rfl <;> exact hn
    try simp only [hcs_r, hcr_r] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr hna32
    | exact ⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩
    | (dsimp only [mkBufRt, brBase, brHdrNA] at hmem_na
       simp only [mkBufRt, brBase, brHdrNA, brMaxNodes, brOffMeta, brGBits, brW, hmem_na] at *
       have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
       have hna_max := hrep.1
       have hgt : 1 < tr.nodeAlloc := by omega
       set u := tr.nodeAlloc - 1
       have hu1 : 1 ≤ u := by omega
       have hu_lt : u < tr.nodeAlloc := by omega
       have hpar_u : tr.nodeParent u < u := (hclr.2.2.1 u hu1 hu_lt).1
       have hrep_par : readPacked (base + if ep = 0 then offTrieMeta0 c U V w n_max
           else offTrieMeta1 c U V w n_max) (globalPtrBits n_max) w s.mem (4 * u) =
           tr.nodeParent u := (hrep.2.2.2.2.2.1 u hu1 hu_lt).1
       try rw [hrep_par]
       omega)

private theorem bufClearOneRtProg_spec {c U V w n_max base ep : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hclr : ClearableBufTrie tr) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := bufClearOneRtProg (rt, ())
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearOne tr
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 15 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨hna_lt_sp, hia_lt_sp, hc_seg, hm_seg, _⟩ :
      base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
      base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max ∧
      base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
        base + largeSpaceWhp c U V w n_max := rt_seg_le c U V w n_max base ep hep
  obtain ⟨hna32, hia32, hna_ne_ia, h32_c, hc_le_m, hm_le_i⟩ :
      brHdrNA rt < 32 ∧ brHdrIA rt < 32 ∧ brHdrNA rt ≠ brHdrIA rt ∧ 32 ≤ brOffChild rt ∧
      brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffMeta rt ∧
      brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
        brOffItems rt := rt_disj_le c U V w n_max base ep hep
  have hmt_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.1
  have h0_g : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
  have h0_fit : Fits w 0 := Nat.two_pow_pos w
  have h1_fit : Fits w 1 := henv.fits_const (by decide)
  have hmem_na : s.mem (base + brHdrNA rt) = tr.nodeAlloc := (bufTrieMemRep_iff_rt.mp hrep).2.2.1
  have hna_max := hrep.1
  dsimp only
  unfold bufClearOneRtProg
  simp only [pure_bind]
  dsimp only [bufClearOne]
  by_cases hgt : 1 < tr.nodeAlloc
  · rw [ite_eq_left hgt]
    set u := tr.nodeAlloc - 1
    have hu1 : 1 ≤ u := by omega
    have hu_lt : u < tr.nodeAlloc := by omega
    have hu_max : u < maxTrieNodesWhp c n_max := hu_lt.trans_le hna_max
    have hu_fit : Fits w u := henv.fits_of_le_n_max (by omega)
    set par := tr.nodeParent u
    set ch := tr.nodeChar u
    have hpar_u : par < u := (hclr.2.2.1 u hu1 hu_lt).1
    have hpar_max : par < maxTrieNodesWhp c n_max := hpar_u.trans hu_max
    have hrep_par_ch :
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u) = par ∧
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem (4 * u + 1) = ch :=
      (bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.2.1 u hu1 hu_lt
    have hiP : 4 * u < 6 * maxTrieNodesWhp c n_max := by omega
    have hiC : 4 * u + 1 < 6 * maxTrieNodesWhp c n_max := by omega
    have hi2 : 4 * u + 2 < 6 * maxTrieNodesWhp c n_max := by omega
    set se := (Memory.spec 0).clientState s (bufClearEdgeRtProg (rt, (par, ch)))
    have hse_spec :
        se.frontier = s.frontier ∧
        memoryCost (bufClearEdgeRtProg (rt, (par, ch))) s ≤ 4 ∧
        ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
          (bufClearEdgeRtProg (rt, (par, ch))) ∧
        BufEpFrame base c U V w n_max ep s.mem se.mem ∧
        (∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w se.mem
            (v * 2 ^ bCharWhp n_max + c') =
            Function.update tr.trieChild par (Function.update (tr.trieChild par) ch 0) v c') ∧
        (∀ a, a < base + brOffChild rt ∨
          base + brOffChild rt +
            packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤ a →
          se.mem a = s.mem a) := by
      have hrep_c : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
            (v * 2 ^ bCharWhp n_max + c') = tr.trieChild v c' :=
        (bufTrieMemRep_iff_rt.mp hrep).2.2.2.2.1
      by_cases hch_lt : ch < 2 ^ bCharWhp n_max
      · have hch_br : ch < brPowBChar rt := hch_lt
        set idxE := par * 2 ^ bCharWhp n_max + ch
        have hidxE : idxE < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp
          calc par * 2 ^ bCharWhp n_max + ch
              < par * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
            _ = (par + 1) * 2 ^ bCharWhp n_max := by ring
            _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hpar_max
        have hse_eq : se =
            { mem := writePacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem idxE 0,
              frontier := s.frontier } := by
          dsimp only [se]
          rw [bufClearEdgeRtProg_eq, ite_eq_left hch_br]
          simp only [pure_bind]
          rw [clientState_writePackedGen]
          rfl
        rw [hse_eq]
        refine ⟨rfl, ?_, ?_, bufEpFrame_writeChild hw hep hidxE, fun v hv c' hc' => ?_,
          fun a ha => mem_writePacked_of_outside hw hidxE ha⟩
        · rw [bufClearEdgeRtProg_eq, ite_eq_left hch_br]
          simp only [pure_bind, memoryCost_writePackedGen]
          exact le_rfl
        · rw [bufClearEdgeRtProg_eq, ite_eq_left hch_br]
          simp only [pure_bind]
          exact validWhpProg_writePacked hw hgk hidxE hc_seg
        · by_cases hvc : v = par ∧ c' = ch
          · rcases hvc with ⟨rfl, rfl⟩
            simp only [Function.update_self]
            exact readPacked_writePacked_self _ _ _ s.mem idxE h0_g
          · have hne_i : v * 2 ^ bCharWhp n_max + c' ≠ idxE :=
              fun heq => hvc ((child_idx_eq_iff hc' hch_lt).mp heq)
            rw [readPacked_writePacked_of_ne hw s.mem hne_i 0, hrep_c v hv c' hc']
            by_cases hvp : v = par
            · subst hvp
              have hcc : c' ≠ ch := fun h => hvc ⟨rfl, h⟩
              simp [hcc]
            · simp [hvp]
      · have hch_br : ¬(ch < brPowBChar rt) := hch_lt
        have hse_eq : se = s := by
          dsimp only [se]
          rw [bufClearEdgeRtProg_eq, ite_eq_right hch_br, StateTransitionSpec.clientState_pure]
        rw [hse_eq]
        refine ⟨rfl, ?_, ?_, BufEpFrame.refl _, fun v hv c' hc' => ?_, fun _ _ => rfl⟩
        · rw [bufClearEdgeRtProg_eq, ite_eq_right hch_br]
          exact Nat.zero_le 4
        · rw [bufClearEdgeRtProg_eq, ite_eq_right hch_br]
          exact validWhpProg_pure _
        · rw [hrep_c v hv c' hc']
          have hcc : c' ≠ ch := by omega
          by_cases hvp : v = par
          · subst hvp; simp [hcc]
          · simp [hvp]
    obtain ⟨hse_fr, hse_mc, hse_vp, hse_bfr, hse_ch, hse_out⟩ := hse_spec
    set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w se.mem (4 * u + 2) 0
    set m2 := Function.update m1 (base + brHdrNA rt) u
    set m3 := Function.update m2 (base + brHdrIA rt) 0
    have hs'_eq : (Memory.spec 0).clientState s
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) =
        { mem := m3, frontier := s.frontier } := by
      rw [StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_na, ite_eq_left hgt, bufClearPopRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hrep_par_ch.1,
        StateTransitionSpec.clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, hrep_par_ch.2,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (bufClearEdgeRtProg (rt, (par, ch))) = se from rfl,
        bufClearPopTailRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_writePackedGen,
        StateTransitionSpec.clientState_bind, clientState_memWrite, clientState_memWrite]
      exact Memory.State.ext rfl hse_fr
    have hmc_all : memoryCost
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) s ≤ 15 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
        memoryCost_memRead, ite_eq_left hgt, bufClearPopRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen,
        show brBase rt = base from rfl, show brGBits rt = globalPtrBits n_max from rfl,
        show brW rt = w from rfl, hrep_par_ch.1,
        clientState_readPackedGen, clientResult_readPackedGen, memoryCost_readPackedGen,
        hrep_par_ch.2, bufClearPopTailRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen, memoryCost_memWrite]
      omega
    have hvp_all : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) := by
      refine validWhpProg_bind (validWhpProg_read hna_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
        ite_eq_left hgt, bufClearPopRtProg_eq]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hiP hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, show brBase rt = base from rfl,
        show brGBits rt = globalPtrBits n_max from rfl, show brW rt = w from rfl, hrep_par_ch.1]
      refine validWhpProg_bind (validWhpProg_readPacked hw hiC hm_seg) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hrep_par_ch.2]
      refine validWhpProg_bind hse_vp ?_
      rw [bufClearPopTailRtProg_eq]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi2 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validWhpProg_bind (validWhpProg_write hna_lt_sp hu_fit) ?_
      rw [clientState_memWrite]
      exact validWhpProg_write hia_lt_sp h0_fit
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s.mem m3 :=
      ((hse_bfr.trans (bufEpFrame_writeMeta hw hep hi2)).trans
        (bufEpFrame_write_hdrNA hw hep)).trans (bufEpFrame_write_hdrIA hw hep)
    refine ⟨rfl, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hm3_na : m3 (base + brHdrNA rt) = u := by
      dsimp only [m3, m2]; rw [Function.update_of_ne (by omega), Function.update_self]
    have hm3_ia : m3 (base + brHdrIA rt) = 0 := by dsimp only [m3]; simp
    have hm3_ch : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w m3
          (v * 2 ^ bCharWhp n_max + c') =
          Function.update tr.trieChild par (Function.update (tr.trieChild par) ch 0) v c' := by
      intro v hv c' hc'
      have hvc_lt : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc v * 2 ^ bCharWhp n_max + c'
            < v * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (v + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hv
      dsimp only [m3, m2, m1]
      rw [readPacked_update_outside hw hvc_lt (Or.inl (by omega)),
        readPacked_update_outside hw hvc_lt (Or.inl (by omega)),
        readPacked_writePacked_disjoint hw hvc_lt hi2 (Or.inl (by omega))]
      exact hse_ch v hv c' hc'
    have hm3_meta : ∀ idx < 6 * maxTrieNodesWhp c n_max, idx ≠ 4 * u + 2 →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w m3 idx =
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem idx := by
      intro idx hidx hne
      dsimp only [m3, m2, m1]
      rw [readPacked_update_outside hw hidx (Or.inl (by omega)),
        readPacked_update_outside hw hidx (Or.inl (by omega)),
        readPacked_writePacked_of_ne hw se.mem hne 0]
      exact readPacked_congr_on hw hidx fun a ha1 _ => hse_out a (Or.inr (by omega))
    obtain ⟨_, _, _, _, _, hpar_r, hlf_r, _⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨by omega, Nat.zero_le _, hm3_na, hm3_ia, hm3_ch,
      fun w' hw1 hw_lt => ⟨(hm3_meta _ (by omega) (by omega)).trans
          (hpar_r w' hw1 (by omega)).1,
        (hm3_meta _ (by omega) (by omega)).trans (hpar_r w' hw1 (by omega)).2⟩,
      fun w' hw_lt => ?_,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    have hwu : w' ≠ u := by omega
    simp only [Function.update_of_ne hwu]
    exact ⟨(hm3_meta _ (by omega) (by omega)).trans (hlf_r w' (by omega)).1,
      fun hnz => (hm3_meta _ (by omega) (by omega)).trans ((hlf_r w' (by omega)).2 hnz)⟩
  · rw [ite_eq_right hgt]
    have hmt2 : 2 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    have hi2_0 : 2 < 6 * maxTrieNodesWhp c n_max := by omega
    set m1 := writePacked (base + brOffMeta rt) (globalPtrBits n_max) w s.mem 2 0
    set m2 := Function.update m1 (base + brHdrNA rt) 1
    set m3 := Function.update m2 (base + brHdrIA rt) 0
    have hs'_eq : (Memory.spec 0).clientState s
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) =
        { mem := m3, frontier := s.frontier } := by
      rw [StateTransitionSpec.clientState_bind, clientState_memRead, clientResult_memRead,
        show brBase rt = base from rfl, hmem_na, ite_eq_right hgt, bufClearRootRtProg_eq]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_writePackedGen,
        StateTransitionSpec.clientState_bind, clientState_memWrite, clientState_memWrite]
      rfl
    have hmc_all : memoryCost
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) s ≤ 15 := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
        memoryCost_memRead, ite_eq_right hgt, bufClearRootRtProg_eq]
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen, memoryCost_memWrite]
      omega
    have hvp_all : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (Memory.read (brBase rt + brHdrNA rt) >>= fun na' =>
          if 1 < na' then bufClearPopRtProg (rt, na' - 1)
          else bufClearRootRtProg rt) := by
      refine validWhpProg_bind (validWhpProg_read hna_lt_sp) ?_
      rw [clientState_memRead, clientResult_memRead, show brBase rt = base from rfl, hmem_na,
        ite_eq_right hgt, bufClearRootRtProg_eq]
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_writePacked hw hgk hi2_0 hm_seg) ?_
      rw [clientState_writePackedGen]
      refine validWhpProg_bind (validWhpProg_write hna_lt_sp h1_fit) ?_
      rw [clientState_memWrite]
      exact validWhpProg_write hia_lt_sp h0_fit
    rw [hs'_eq]
    have hbfr_all : BufEpFrame base c U V w n_max ep s.mem m3 :=
      ((bufEpFrame_writeMeta hw hep hi2_0).trans (bufEpFrame_write_hdrNA hw hep)).trans
        (bufEpFrame_write_hdrIA hw hep)
    refine ⟨rfl, hmc_all, hvp_all, ?_, hbfr_all⟩
    have hm3_na : m3 (base + brHdrNA rt) = 1 := by
      dsimp only [m3, m2]; rw [Function.update_of_ne (by omega), Function.update_self]
    have hm3_ia : m3 (base + brHdrIA rt) = 0 := by dsimp only [m3]; simp
    have hm3_ch : ∀ v < maxTrieNodesWhp c n_max, ∀ c' < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w m3
          (v * 2 ^ bCharWhp n_max + c') =
          readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
            (v * 2 ^ bCharWhp n_max + c') := by
      intro v hv c' hc'
      have hvc_lt : v * 2 ^ bCharWhp n_max + c' < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc v * 2 ^ bCharWhp n_max + c'
            < v * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hc' _
          _ = (v + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hv
      dsimp only [m3, m2, m1]
      exact (readPacked_update_outside hw hvc_lt (Or.inl (by omega))).trans
        ((readPacked_update_outside hw hvc_lt (Or.inl (by omega))).trans
          (readPacked_writePacked_disjoint hw hvc_lt hi2_0 (Or.inl (by omega))))
    have hm3_m2 : readPacked (base + brOffMeta rt) (globalPtrBits n_max) w m3 2 = 0 := by
      dsimp only [m3, m2, m1]
      rw [readPacked_update_outside hw hi2_0 (Or.inl (by omega)),
        readPacked_update_outside hw hi2_0 (Or.inl (by omega))]
      exact readPacked_writePacked_self _ _ _ s.mem 2 h0_g
    obtain ⟨_, _, _, _, hch_r, _, _, _⟩ := bufTrieMemRep_iff_rt.mp hrep
    rw [bufTrieMemRep_iff_rt]
    dsimp only
    refine ⟨by omega, Nat.zero_le _, hm3_na, hm3_ia,
      fun v hv c' hc' => (hm3_ch v hv c' hc').trans (hch_r v hv c' hc'),
      fun w' hw1 hw_lt => by omega,
      fun w' hw_lt => ?_,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    have hw0 : w' = 0 := by omega
    subst hw0
    simp only [Nat.mul_zero, Nat.zero_add, Function.update_self]
    exact ⟨hm3_m2, fun hnz => absurd rfl hnz⟩

/-- Parameter-free wrapper for `iterate bufClearOneRtProg`. -/
@[expose] def bufClearLoopGenProg (p : (BufRt × Unit) × ℕ) : Memory.Prog Unit :=
  iterate bufClearOneRtProg p.1.1 p.2 p.1.2

theorem realizes_bufClearLoopGen :
    Realizes .exact bufClearLoopGenProg
      (WordEncoding.encode (α := (BufRt × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w p s => iterationSafe bufClearOneRtProg BufClearOnePre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := Unit))
    realizes_bufClearOneRt
    memoryCost_bufClearOneRtProg_pos

private theorem bufClearLoop_spec {c U V w n_max base ep : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ k (tr : BufTrie) (s : Memory.State),
      BufTrieMemRep base c U V w n_max ep tr s.mem →
      ClearableBufTrie tr →
      let prog := bufClearLoopGenProg ((rt, ()), k)
      let s' := (Memory.spec 0).clientState s prog
      let tr' := bufClearSteps k tr
      iterationSafe bufClearOneRtProg BufClearOnePre w rt k () s ∧
      s'.frontier = s.frontier ∧
      memoryCost prog s ≤ 15 * k ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
      BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  intro rt k
  induction k with
  | zero =>
    intro tr s hrep _
    exact ⟨trivial, rfl, Nat.zero_le _, validWhpProg_pure _, hrep, BufEpFrame.refl _⟩
  | succ k ih =>
    intro tr s hrep hclr
    have hpre : BufClearOnePre w (rt, ()) s :=
      ⟨c, U, V, w, n_max, base, ep, tr, henv, hep, rfl, hrep, hclr⟩
    obtain ⟨hfr1, hmc1, hvp1, hrep1, hbfr1⟩ := bufClearOneRtProg_spec henv hep hrep hclr (s := s)
    set s1 := (Memory.spec 0).clientState s (bufClearOneRtProg (rt, ()))
    have hclr1 : ClearableBufTrie (bufClearOne tr) := hclr.clearOne_step.1
    obtain ⟨hsafe_k, hfr_k, hmc_k, hvp_k, hrep_k, hbfr_k⟩ := ih (bufClearOne tr) s1 hrep1 hclr1
    have hu_eq : (Memory.spec 0).clientResult s (bufClearOneRtProg (rt, ())) = () := rfl
    dsimp only
    have hst_all : (Memory.spec 0).clientState s (bufClearLoopGenProg ((rt, ()), k + 1)) =
        (Memory.spec 0).clientState s1 (bufClearLoopGenProg ((rt, ()), k)) := by
      change (Memory.spec 0).clientState s
        (bufClearOneRtProg (rt, ()) >>= fun s' => iterate bufClearOneRtProg rt k s') = _
      rw [StateTransitionSpec.clientState_bind, hu_eq]
      rfl
    rw [hst_all]
    refine ⟨⟨hpre, ?_⟩, hfr_k.trans hfr1, ?_, ?_, hrep_k, hbfr1.trans hbfr_k⟩
    · rw [clientState_width, clientResult_width]
      exact hsafe_k
    · change memoryCost (bufClearOneRtProg (rt, ()) >>= fun s' => iterate bufClearOneRtProg rt k s')
        s ≤ 15 * (k + 1)
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost (bufClearOneRtProg (rt, ())) s +
        memoryCost (bufClearLoopGenProg ((rt, ()), k)) s1 ≤ 15 * (k + 1)
      dsimp only [rt] at hmc1 hmc_k ⊢
      omega
    · change ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (bufClearOneRtProg (rt, ()) >>= fun s' => iterate bufClearOneRtProg rt k s')
      exact validWhpProg_bind hvp1 hvp_k

/-- Precondition for `bufClearStepsGenProg` (`d = (((cp, base), ep), k)`). -/
@[expose] def BufClearStepsGenPre (w : ℕ)
    (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max tr,
    WhpLargeEnv c U V w₀ n_max w d.1.1.2 ∧
    d.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    (d.1.2 = 0 ∨ d.1.2 = 1) ∧
    BufTrieMemRep d.1.1.2 c U V w₀ n_max d.1.2 tr s.mem ∧
    ClearableBufTrie tr

/-- Parameter-free `bufClearSteps` (`d = (((cp, base), ep), k)`). -/
@[expose] def bufClearStepsGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let rt ← mkBufRtGenProg d.1
  bufClearLoopGenProg ((rt, ()), d.2)

theorem bufClearStepsGenProg_spec {c U V w n_max base ep k : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hclr : ClearableBufTrie tr) :
    let prog := bufClearStepsGenProg (((mkWhpCoreParams c U V w n_max, base), ep), k)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearSteps k tr
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 15 * k ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  have hth := henv.2.2.2.1
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hfr_l, hmc_l, hvp_l, hrep_l, hbfr_l⟩ := bufClearLoop_spec henv hep k tr s hrep hclr
  dsimp only
  unfold bufClearStepsGenProg
  have hs'_eq : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufClearLoopGenProg ((rt', ()), k)) =
      (Memory.spec 0).clientState s (bufClearLoopGenProg ((rt, ()), k)) := by
    rw [StateTransitionSpec.clientState_bind, hrt_st, hrt_res]
  rw [hs'_eq]
  refine ⟨hfr_l, ?_, ?_, hrep_l, hbfr_l⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc]
    dsimp only [rt] at hmc_l ⊢
    omega
  · refine validWhpProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res]
    exact hvp_l

theorem realizes_bufClearStepsGen :
    Realizes .exact bufClearStepsGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BufClearStepsGenPre
      (fun _ _ => 0) := by
  have hmrt := realizes_mkBufRtGen
  have hcl := realizes_bufClearLoopGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, k⟩
    obtain ⟨c, U, V, w₀, n_max, tr, henv, rfl, hep, hrep, hclr⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) hth s
    obtain ⟨hsafe, _, _, _, _, _⟩ := bufClearLoop_spec henv hep k tr s hrep hclr
    try simp only [hrt_st, hrt_res] at *
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsafe

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
