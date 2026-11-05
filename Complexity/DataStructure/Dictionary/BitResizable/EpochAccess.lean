/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Operations
public import Complexity.DataStructure.Dictionary.BitResizable.DenseItemPrimitives
import all Complexity.DataStructure.HashFamily.WordRAM.ReducedKWise

/-!
# Persistent Epoch Registers and Uniform Metadata / Dense-Item Accessors

This module defines:
1. Register-bank embeddings (`embed16`, `embed240`) into `BitRAM.Code .standard 280` and the
   persistent epoch parameter register invariant (`EpochRegs`) on registers `240..269`.
2. Parameter-free `BitRAM.Code .standard 280` accessors for bit-packed metadata arrays
   (`readGMRegCode`, `writeGMRegCode`, `readTDRegCode`, `writeTDRegCode`, `readDTRegCode`,
   `writeDTRegCode`, `readLMRegCode`, `writeLMRegCode`) and dense items (`readDenseQRegCode`,
   `readDenseVRegCode`, `writeDenseQRegCode`, `writeDenseVRegCode`, `appendDenseRegCode`,
   `popDenseRegCode`).
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability

/-! ## Section 1: Register-bank embeddings and persistent epoch register invariant (`EpochRegs`) -/

/-- Canonical embedding `Fin 16 → Fin 280`. -/
@[expose]
def embed16Map : Fin 16 → Fin 280 :=
  Fin.castLE (by decide)

theorem injective_embed16Map : Function.Injective embed16Map :=
  Fin.castLE_injective (by decide)

/-- Lift a `BitRAM.Code B 16` program into `BitRAM.Code B 280` on registers `0..15`. -/
@[expose]
def embed16 {B : Basis} (p : BitRAM.Code B 16) : BitRAM.Code B 280 :=
  p.rename embed16Map

theorem embed16_exec {B : Basis} {w : ℕ} {p : BitRAM.Code B 16}
    {x : BitRAM.Data 280} {Q : BitRAM.Data 16 → Prop} {T : ℕ}
    (h : BitRAM.DemonicExecWithin w p (x.comap embed16Map) Q T) :
    BitRAM.DemonicExecWithin w (embed16 p) x
      (fun y => Q (y.comap embed16Map) ∧ ∀ j : Fin 280, 16 ≤ j.val → y.regs j = x.regs j) T := by
  refine (h.rename injective_embed16Map).mono
    (fun y ⟨hQ, hj⟩ => ⟨hQ, fun j hj16 => hj j fun i hi => ?_⟩) le_rfl
  have : i.val = j.val := congrArg Fin.val hi
  omega

/-- Canonical embedding `Fin 240 → Fin 280`. -/
@[expose]
def embed240Map : Fin 240 → Fin 280 :=
  Fin.castLE (by decide)

theorem injective_embed240Map : Function.Injective embed240Map :=
  Fin.castLE_injective (by decide)

/-- Lift a `BitRAM.Code B 240` program into `BitRAM.Code B 280` on registers `0..239`. -/
@[expose]
def embed240 {B : Basis} (p : BitRAM.Code B 240) : BitRAM.Code B 280 :=
  p.rename embed240Map

theorem embed240_exec {B : Basis} {w : ℕ} {p : BitRAM.Code B 240}
    {x : BitRAM.Data 280} {Q : BitRAM.Data 240 → Prop} {T : ℕ}
    (h : BitRAM.DemonicExecWithin w p (x.comap embed240Map) Q T) :
    BitRAM.DemonicExecWithin w (embed240 p) x
      (fun y => Q (y.comap embed240Map) ∧ ∀ j : Fin 280, 240 ≤ j.val → y.regs j = x.regs j) T := by
  refine (h.rename injective_embed240Map).mono
    (fun y ⟨hQ, hj⟩ => ⟨hQ, fun j hj240 => hj j fun i hi => ?_⟩) le_rfl
  have : i.val = j.val := congrArg Fin.val hi
  omega

/-- Trinomial step parameter `t = reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N)
(totalMicroBits N)` for epoch capacity `N`. -/
@[expose]
def epochTrinomialStep (U N : ℕ) : ℕ :=
  reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N)

/-- Persistent epoch parameter register invariant on registers `240..269` of `BitRAM.Data 280`.
Registers `240..243` hold the global dictionary parameters `(U, V, keyBits U, valBits V)`;
register `244` holds `quotientBits U N`; and when `0 < N`, registers `245..269` hold the derived
epoch geometry, word offsets, and hash parameters for capacity `N`. -/
structure EpochRegs (U V w N : ℕ) (x : BitRAM.Data 280) : Prop where
  r240 : x.regs 240 = U
  r241 : x.regs 241 = V
  r242 : x.regs 242 = keyBits U
  r243 : x.regs 243 = valBits V
  r244 : x.regs 244 = quotientBits U N
  active : 0 < N →
    let t := epochTrinomialStep U N
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    let w₀ := Succinct.qBits U N
    let b := Succinct.hashB N
    let b' := totalMicroBits N
    x.regs 245 = bucketBits N ∧
    x.regs 246 = numBuckets N ∧
    x.regs 247 = numBuckets N - 1 ∧
    x.regs 248 = numMicroPerBucket N ∧
    x.regs 249 = b' ∧
    x.regs 250 = slabSize N ∧
    x.regs 251 = effBucketCap N ∧
    x.regs 252 = effBucketPosBits N ∧
    x.regs 253 = maxTailItems N ∧
    x.regs 254 = globalPtrBits N ∧
    x.regs 255 = Succinct.lmSubWords N w ∧
    x.regs 256 = offLM U w N ∧
    x.regs 257 = offGM U w N ∧
    x.regs 258 = offTD U w N ∧
    x.regs 259 = offDT U w N ∧
    x.regs 260 = epochMetaWords U w N ∧
    x.regs 261 = w₀ ∧
    x.regs 262 = w₀ - min w₀ (3 * b) ∧
    x.regs 263 = min t 3 ∧
    x.regs 264 = c ∧
    x.regs 265 = 2 ^ c - 1 ∧
    x.regs 266 = p ∧
    x.regs 267 = 2 ^ p - 1 ∧
    x.regs 268 = 2 ^ (2 * c) - 1 ∧
    x.regs 269 = ReducedKWise.tabBase offHash w₀ b b' 3

theorem EpochRegs.congr_regs {U V w N : ℕ} {x y : BitRAM.Data 280}
    (h : EpochRegs U V w N x)
    (heq : ∀ r : Fin 280, 240 ≤ r.val → r.val < 270 → y.regs r = x.regs r) :
    EpochRegs U V w N y where
  r240 := (heq 240 (by decide) (by decide)).trans h.r240
  r241 := (heq 241 (by decide) (by decide)).trans h.r241
  r242 := (heq 242 (by decide) (by decide)).trans h.r242
  r243 := (heq 243 (by decide) (by decide)).trans h.r243
  r244 := (heq 244 (by decide) (by decide)).trans h.r244
  active hN := by
    obtain ⟨h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255, h256, h257,
      h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269⟩ := h.active hN
    exact ⟨(heq 245 (by decide) (by decide)).trans h245,
      (heq 246 (by decide) (by decide)).trans h246,
      (heq 247 (by decide) (by decide)).trans h247,
      (heq 248 (by decide) (by decide)).trans h248,
      (heq 249 (by decide) (by decide)).trans h249,
      (heq 250 (by decide) (by decide)).trans h250,
      (heq 251 (by decide) (by decide)).trans h251,
      (heq 252 (by decide) (by decide)).trans h252,
      (heq 253 (by decide) (by decide)).trans h253,
      (heq 254 (by decide) (by decide)).trans h254,
      (heq 255 (by decide) (by decide)).trans h255,
      (heq 256 (by decide) (by decide)).trans h256,
      (heq 257 (by decide) (by decide)).trans h257,
      (heq 258 (by decide) (by decide)).trans h258,
      (heq 259 (by decide) (by decide)).trans h259,
      (heq 260 (by decide) (by decide)).trans h260,
      (heq 261 (by decide) (by decide)).trans h261,
      (heq 262 (by decide) (by decide)).trans h262,
      (heq 263 (by decide) (by decide)).trans h263,
      (heq 264 (by decide) (by decide)).trans h264,
      (heq 265 (by decide) (by decide)).trans h265,
      (heq 266 (by decide) (by decide)).trans h266,
      (heq 267 (by decide) (by decide)).trans h267,
      (heq 268 (by decide) (by decide)).trans h268,
      (heq 269 (by decide) (by decide)).trans h269⟩

theorem EpochRegs.set_of_outside {U V w N : ℕ} {x : BitRAM.Data 280}
    (h : EpochRegs U V w N x) {r : Fin 280} (hr : r.val < 240 ∨ 270 ≤ r.val) (v : ℕ) :
    EpochRegs U V w N (x.set r v) :=
  h.congr_regs fun s hs1 hs2 => by
    have hne : s ≠ r := by intro heq; subst heq; omega
    simp [BitRAM.Data.set, Function.update_of_ne hne]

theorem EpochRegs.write {U V w N : ℕ} {x : BitRAM.Data 280}
    (h : EpochRegs U V w N x) (a v : ℕ) :
    EpochRegs U V w N (x.write a v) :=
  h.congr_regs fun _ _ _ => rfl

theorem wf_comap12_280 {w : ℕ} {x : BitRAM.Data 280} (hx : x.WellFormed w) :
    (x.comap (embedFin12 (by decide))).WellFormed w :=
  ⟨fun i => hx.regs_fits (Fin.castLE (by decide) i), hx.mem_wf⟩

theorem wf_of_comap12_280 {w : ℕ} {x y : BitRAM.Data 280} (hx : x.WellFormed w)
    (hy12 : (y.comap (embedFin12 (by decide))).WellFormed w)
    (hy_hi : ∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r) :
    y.WellFormed w := by
  refine ⟨fun i => ?_, hy12.mem_wf⟩
  by_cases hi : i.val < 12
  · exact hy12.regs_fits ⟨i.val, hi⟩
  · rw [hy_hi i (by omega)]; exact hx.regs_fits i

theorem wf_comap16 {w : ℕ} {x : BitRAM.Data 280} (hx : x.WellFormed w) :
    (x.comap embed16Map).WellFormed w :=
  ⟨fun i => hx.regs_fits (embed16Map i), hx.mem_wf⟩

theorem wf_of_comap16 {w : ℕ} {x y : BitRAM.Data 280} (hx : x.WellFormed w)
    (hy16 : (y.comap embed16Map).WellFormed w)
    (hy_hi : ∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r) :
    y.WellFormed w := by
  refine ⟨fun i => ?_, hy16.mem_wf⟩
  by_cases hi : i.val < 16
  · exact hy16.regs_fits ⟨i.val, hi⟩
  · rw [hy_hi i (by omega)]; exact hx.regs_fits i

theorem wf_set {w r : ℕ} {x : BitRAM.Data r} (dst : Fin r) {v : ℕ}
    (hx : x.WellFormed w) (hv : Fits w v) : (x.set dst v).WellFormed w where
  regs_fits i := by
    by_cases h : i = dst
    · subst h; simpa [BitRAM.Data.set] using hv
    · simpa [BitRAM.Data.set, Function.update_of_ne h] using hx.regs_fits i
  mem_wf := hx.mem_wf

theorem lmSubWords_eq (N w : ℕ) :
    Succinct.lmSubWords N w = packedWords (totalMicroBuckets N) (effBucketPosBits N) w := rfl

theorem lmSubWords_pos {N w : ℕ} (_hw : 0 < w) : 0 < Succinct.lmSubWords N w := by
  rw [lmSubWords_eq]
  unfold packedWords
  positivity

/-! ## Section 2: Uniform packed-array and dense-item accessors on `BitRAM.Code .standard 280` -/

/-- General parameter-free `BitRAM.Code .standard 280` wrapper around `readPackedRegCode`:
copies `rBase` to `r0`, `rIdx` to `r1`, `rK` to `r9`, runs `readPackedRegCode` on `0..11`, and
copies `r2` to `rDst` in `45` instructions, preserving all registers `r ≥ 12` (`r ≠ rDst`). -/
@[expose]
def readPackedAtRegCode (rBase rK rIdx rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 0 rBase))
    (.seq (.op (.copy 1 rIdx))
      (.seq (.op (.copy 9 rK))
        (.seq (readPackedRegCode.embed12 (by decide))
          (.op (.copy rDst 2)))))

set_option linter.unusedSimpArgs false in
theorem readPackedAtRegCode_exec {base N k w idx : ℕ}
    {rBase rK rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (_hrBase_ge : 12 ≤ rBase.val) (hrK_ge : 12 ≤ rK.val) (hrIdx_ge : 12 ≤ rIdx.val)
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.WellFormed w)
    (hbase : x.regs rBase = base) (hrk : x.regs rK = k) (hridx : x.regs rIdx = idx)
    (hfit_end : Fits w (base + packedWords N k w))
    (hadm_end : base + packedWords N k w ≤ x.wordSize w) :
    BitRAM.DemonicExecWithin w (readPackedAtRegCode rBase rK rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = readPacked base k w x.mem idx ∧
        (∀ r : Fin 280, 12 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 45 := by
  have hne0_idx : rIdx ≠ 0 := by intro h; subst h; omega
  have hne0_k : rK ≠ 0 := by intro h; subst h; omega
  have hne1_k : rK ≠ 1 := by intro h; subst h; omega
  refine step_dExec_copy (v := base) (T := 44) hbase ?_
  refine step_dExec_copy (v := idx) (T := 43)
    (by simp [BitRAM.Data.set, Function.update_of_ne hne0_idx, hridx]) ?_
  refine step_dExec_copy (v := k) (T := 42)
    (by simp [BitRAM.Data.set, Function.update_of_ne hne1_k, Function.update_of_ne hne0_k, hrk]) ?_
  set x₁ := ((x.set 0 base).set 1 idx).set 9 k
  have hx₁_wf : (x₁.comap (embedFin12 (by decide))).WellFormed w :=
    wf_comap12_280 (wf_set 9 (wf_set 1 (wf_set 0 hx (hbase ▸ hx.regs_fits rBase))
      (hridx ▸ hx.regs_fits rIdx)) (hrk ▸ hx.regs_fits rK))
  have hread := DemonicExecWithin.embed12 (by decide)
    (readPackedRegCode_exec (base := base) (N := N) (k := k) (idx := idx) hw hkw hidx hx₁_wf
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      hfit_end hadm_end)
  refine .seq (T₁ := 41) (T₂ := 1) hread (fun y₁ ⟨⟨hmem, hsz, _, _, hy₁_2, hy₁_wf12⟩, hy₁_hi⟩ => ?_)
    (by omega)
  refine DemonicExecWithin.copy ?_
  have hy_regs : ∀ r : Fin 280, 12 ≤ r.val → y₁.regs r = x.regs r := by
    intro r hr
    have h9 : r ≠ 9 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    have h0 : r ≠ 0 := by intro h; subst h; omega
    simp [hy₁_hi r hr, x₁, BitRAM.Data.set, h9, h1, h0]
  have hy₁_wf : y₁.WellFormed w := wf_of_comap12_280 hx hy₁_wf12 hy_regs
  have hy_wf : (y₁.set rDst (y₁.regs 2)).WellFormed w := wf_set rDst hy₁_wf (hy₁_wf.regs_fits 2)
  have hst : (y₁.set rDst (y₁.regs 2)).toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact congrFun hmem a
    · exact hsz
  refine ⟨hst, hy_wf,
    by simp only [Fin.isValue, BitRAM.Data.set_regs, Function.update_self]; exact hy₁_2,
    fun r hr hne => ?_⟩
  simp [BitRAM.Data.set, hne, hy_regs r hr]

/-- General parameter-free `BitRAM.Code .standard 280` wrapper around `writePackedRegCode`:
copies `rBase` to `r0`, `rIdx` to `r1`, `rVal` to `r2`, `rK` to `r9`, and runs `writePackedRegCode`
in `56` instructions, preserving all registers `r ≥ 12`. -/
@[expose]
def writePackedAtRegCode (rBase rK rIdx rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 0 rBase))
    (.seq (.op (.copy 1 rIdx))
      (.seq (.op (.copy 2 rVal))
        (.seq (.op (.copy 9 rK))
          (writePackedRegCode.embed12 (by decide)))))

set_option linter.unusedSimpArgs false in
theorem writePackedAtRegCode_exec {base N k w idx val : ℕ}
    {rBase rK rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (_hrBase_ge : 12 ≤ rBase.val) (hrK_ge : 12 ≤ rK.val)
    (hrIdx_ge : 12 ≤ rIdx.val) (hrVal_ge : 12 ≤ rVal.val)
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.WellFormed w)
    (hbase : x.regs rBase = base) (hrk : x.regs rK = k)
    (hridx : x.regs rIdx = idx) (hrval : x.regs rVal = val)
    (hfit_end : Fits w (base + packedWords N k w))
    (hadm_bits : (base + packedWords N k w) * w ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (writePackedAtRegCode rBase rK rIdx rVal) x
      (fun y =>
        y.mem = writePacked base k w x.mem idx val ∧
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        (∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r)) 56 := by
  have hne0_idx : rIdx ≠ 0 := by intro h; subst h; omega
  have hne0_val : rVal ≠ 0 := by intro h; subst h; omega
  have hne1_val : rVal ≠ 1 := by intro h; subst h; omega
  have hne0_k : rK ≠ 0 := by intro h; subst h; omega
  have hne1_k : rK ≠ 1 := by intro h; subst h; omega
  have hne2_k : rK ≠ 2 := by intro h; subst h; omega
  refine step_dExec_copy (v := base) (T := 55) hbase ?_
  refine step_dExec_copy (v := idx) (T := 54)
    (by simp [BitRAM.Data.set, Function.update_of_ne hne0_idx, hridx]) ?_
  refine step_dExec_copy (v := val) (T := 53)
    (by simp [BitRAM.Data.set, Function.update_of_ne hne1_val, Function.update_of_ne hne0_val,
          hrval]) ?_
  refine step_dExec_copy (v := k) (T := 52)
    (by simp [BitRAM.Data.set, Function.update_of_ne hne2_k, Function.update_of_ne hne1_k,
          Function.update_of_ne hne0_k, hrk]) ?_
  set x₁ := (((x.set 0 base).set 1 idx).set 2 val).set 9 k
  have hx₁_wf : (x₁.comap (embedFin12 (by decide))).WellFormed w :=
    wf_comap12_280 (wf_set 9 (wf_set 2 (wf_set 1 (wf_set 0 hx
      (hbase ▸ hx.regs_fits rBase)) (hridx ▸ hx.regs_fits rIdx))
      (hrval ▸ hx.regs_fits rVal)) (hrk ▸ hx.regs_fits rK))
  have hwrite := DemonicExecWithin.embed12 (by decide)
    (writePackedRegCode_exec (base := base) (N := N) (k := k) (idx := idx) (val := val)
      hw hkw hidx hx₁_wf
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      (by simp +decide [x₁, BitRAM.Data.comap, embedFin12, BitRAM.Data.set])
      hfit_end hadm_bits)
  refine hwrite.mono (fun y ⟨⟨hmem, hsz, _, _, _, hy_wf12⟩, hy_hi⟩ => ?_) le_rfl
  have hy_regs : ∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    have h9 : r ≠ 9 := by intro h; subst h; omega
    have h2 : r ≠ 2 := by intro h; subst h; omega
    have h1 : r ≠ 1 := by intro h; subst h; omega
    have h0 : r ≠ 0 := by intro h; subst h; omega
    simp [hy_hi r hr, x₁, BitRAM.Data.set, h9, h2, h1, h0]
  exact ⟨hmem, hsz, wf_of_comap12_280 hx hy_wf12 hy_regs, hy_regs⟩

/-- Any memory modification confined to metadata words `< epochMetaWords U w N` preserves all
dense item quotients and values `denseQuotAt` and `denseValAt`. -/
theorem denseItem_eq_of_high_words_eq {U V w N : ℕ} (hw : 0 < w)
    {s₁ s₂ : BitMemory.State}
    (hhigh : ∀ a, epochMetaWords U w N ≤ a → s₁.mem a = s₂.mem a) (d : ℕ) :
    denseQuotAt U V w N s₁ d = denseQuotAt U V w N s₂ d ∧
    denseValAt U V w N s₁ d = denseValAt U V w N s₂ d := by
  have hfield : ∀ off b, epochMetaBits U w N ≤ off →
      s₁.getField w off b = s₂.getField w off b := by
    intro off b hoff
    have hdiv : epochMetaWords U w N ≤ off / w := by
      unfold epochMetaBits at hoff
      exact (Nat.le_div_iff_mul_le hw).mpr hoff
    unfold BitMemory.State.getField readField
    dsimp only
    rw [Nat.zero_add, hhigh (off / w) hdiv, hhigh (off / w + 1) (by omega)]
  exact ⟨hfield _ _ (by unfold itemQuotBitOff itemBitOff; omega),
    hfield _ _ (by unfold itemValBitOff itemBitOff; omega)⟩


/-- Parameter-free `BitRAM.Code .standard 280` reading `gmAtBit U w N x.mem (x.regs rIdx)` into
`rDst` (`45` instructions). -/
@[expose]
def readGMRegCode (rIdx rDst : Fin 280) : BitRAM.Code .standard 280 :=
  readPackedAtRegCode 257 254 rIdx rDst

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rVal` into `gm` at `x.regs rIdx`
(`56` instructions). -/
@[expose]
def writeGMRegCode (rIdx rVal : Fin 280) : BitRAM.Code .standard 280 :=
  writePackedAtRegCode 257 254 rIdx rVal

/-- Parameter-free `BitRAM.Code .standard 280` reading `tdAtBit U w N x.mem (x.regs rIdx)` into
`rDst` (`45` instructions). -/
@[expose]
def readTDRegCode (rIdx rDst : Fin 280) : BitRAM.Code .standard 280 :=
  readPackedAtRegCode 258 254 rIdx rDst

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rVal` into `td` at `x.regs rIdx`
(`56` instructions). -/
@[expose]
def writeTDRegCode (rIdx rVal : Fin 280) : BitRAM.Code .standard 280 :=
  writePackedAtRegCode 258 254 rIdx rVal

/-- Parameter-free `BitRAM.Code .standard 280` reading `dtAtBit U w N x.mem (x.regs rIdx)` into
`rDst` (`45` instructions). -/
@[expose]
def readDTRegCode (rIdx rDst : Fin 280) : BitRAM.Code .standard 280 :=
  readPackedAtRegCode 259 254 rIdx rDst

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rVal` into `dt` at `x.regs rIdx`
(`56` instructions). -/
@[expose]
def writeDTRegCode (rIdx rVal : Fin 280) : BitRAM.Code .standard 280 :=
  writePackedAtRegCode 259 254 rIdx rVal

/-- Parameter-free `BitRAM.Code .standard 280` reading
`lmAtBit U w N x.mem (c, x.regs rIdx)` into `rDst` (`48` instructions). -/
@[expose]
def readLMRegCode (c : ℕ) (rIdx rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 c))
    (.seq (.op (.bin .mul 12 12 255))
      (.seq (.op (.bin .add 12 256 12))
        (readPackedAtRegCode 12 252 rIdx rDst)))

/-- Parameter-free `BitRAM.Code .standard 280` writing `x.regs rVal` into `lm` at
`(c, x.regs rIdx)` (`59` instructions). -/
@[expose]
def writeLMRegCode (c : ℕ) (rIdx rVal : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 c))
    (.seq (.op (.bin .mul 12 12 255))
      (.seq (.op (.bin .add 12 256 12))
        (writePackedAtRegCode 12 252 rIdx rVal)))

theorem epochMetaWords_le_wordSize_of_bitSize {U w N : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hsz : epochMetaBits U w N ≤ x.bitSize) :
    epochMetaWords U w N ≤ x.wordSize w := by
  have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
  unfold epochMetaBits at hsz
  exact Nat.le_of_mul_le_mul_right (hsz.trans hcov) hw

theorem readGMRegCode_exec {U V w N idx : ℕ} {rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < globalMetaLen N) (hridx : x.regs rIdx = idx)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readGMRegCode rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = gmAtBit U w N x.mem idx ∧
        (∀ r : Fin 280, 12 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 45 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤
      epochMetaWords U w N := by
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT offTD
    omega
  have hadm_end : offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤
      x.wordSize w :=
    hle_meta.trans (epochMetaWords_le_wordSize_of_bitSize hw hsz)
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w) := by
    refine Fits.of_le hfit_bs ?_
    calc offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w
        ≤ epochMetaWords U w N := hle_meta
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  refine (readPackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hfit_end hadm_end).mono
    (fun y ⟨hmem, hwf, hrdst, hregs⟩ => ⟨hmem, hwf, ?_, hregs⟩) le_rfl
  unfold gmAtBit
  rw [ite_eq_left hidx, hrdst]

theorem writeGMRegCode_exec {U V w N idx val : ℕ} {rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val) (hrVal_ge : 12 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N)
    (hridx : x.regs rIdx = idx) (hrval : x.regs rVal = val)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (writeGMRegCode rIdx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        gmAtBit U w N y.mem = Function.update (gmAtBit U w N x.mem) idx val ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r)) 56 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤
      epochMetaWords U w N := by
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT offTD
    omega
  have hadm_bits :
      (offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w) * w ≤ x.bitSize :=
    (Nat.mul_le_mul_right w hle_meta).trans hsz
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w) :=
    Fits.of_le hfit_bs ((Nat.le_mul_of_pos_right _ hw).trans hadm_bits)
  refine (writePackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hrVal_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hrval hfit_end hadm_bits).mono
    (fun y ⟨hmem, hy_sz, hy_wf, hy_regs⟩ => ?_) le_rfl
  have hout : ∀ a, (a < offGM U w N ∨ offTD U w N ≤ a) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    apply writePacked_outside hw x.mem hidx val
    unfold offTD at ha
    omega
  refine ⟨hy_sz, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), ?_, ?_, ?_, ?_,
    hout, fun d => denseItem_eq_of_high_words_eq hw (fun a ha => hout a (Or.inr ?_)) d, hy_regs⟩
  · funext idx'
    unfold gmAtBit
    by_cases hidx' : idx' < globalMetaLen N
    · rw [ite_eq_left hidx', hmem]
      rcases eq_or_ne idx' idx with rfl | hne
      · rw [Function.update_self, readPacked_writePacked_self _ _ _ _ _ hval]
      · rw [Function.update_of_ne hne, ite_eq_left hidx',
          readPacked_writePacked_of_ne hw _ hne val]
    · have hne : idx' ≠ idx := by omega
      rw [ite_eq_right hidx', Function.update_of_ne hne, ite_eq_right hidx']
  · funext ⟨c, j⟩
    unfold lmAtBit
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr => hout addr (Or.inl ?_)) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have haddr_hi :
          addr < offLM U w N + c * packedWords (totalMicroBuckets N) (effBucketPosBits N) w +
            packedWords (totalMicroBuckets N) (effBucketPosBits N) w := haddr.2
      unfold offGM
      rw [lmSubWords_eq] at hmul ⊢
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  · funext t
    unfold tdAtBit
    by_cases ht : t < maxTailItems N
    · rw [ite_eq_left ht, ite_eq_left ht]
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inr (by omega))) ht
    · rw [ite_eq_right ht, ite_eq_right ht]
  · funext i
    unfold dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      have htd_le : offTD U w N ≤ offDT U w N := by unfold offDT; omega
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inr (by omega))) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · rw [← offDT_add_eq_epochMetaWords hN_pos] at ha
    unfold offDT at ha
    omega

theorem readTDRegCode_exec {U V w N idx : ℕ} {rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < maxTailItems N) (hridx : x.regs rIdx = idx)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readTDRegCode rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = tdAtBit U w N x.mem idx ∧
        (∀ r : Fin 280, 12 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 45 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      epochMetaWords U w N := by
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT
    omega
  have hadm_end : offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      x.wordSize w :=
    hle_meta.trans (epochMetaWords_le_wordSize_of_bitSize hw hsz)
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w) := by
    refine Fits.of_le hfit_bs ?_
    calc offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w
        ≤ epochMetaWords U w N := hle_meta
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  refine (readPackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hfit_end hadm_end).mono
    (fun y ⟨hmem, hwf, hrdst, hregs⟩ => ⟨hmem, hwf, ?_, hregs⟩) le_rfl
  unfold tdAtBit
  rw [ite_eq_left hidx, hrdst]

theorem writeTDRegCode_exec {U V w N idx val : ℕ} {rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val) (hrVal_ge : 12 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < maxTailItems N) (hval : val < 2 ^ globalPtrBits N)
    (hridx : x.regs rIdx = idx) (hrval : x.regs rVal = val)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (writeTDRegCode rIdx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        tdAtBit U w N y.mem = Function.update (tdAtBit U w N x.mem) idx val ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offTD U w N ∨ offDT U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r)) 56 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      epochMetaWords U w N := by
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT
    omega
  have hadm_bits :
      (offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w) * w ≤ x.bitSize :=
    (Nat.mul_le_mul_right w hle_meta).trans hsz
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w) :=
    Fits.of_le hfit_bs ((Nat.le_mul_of_pos_right _ hw).trans hadm_bits)
  refine (writePackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hrVal_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hrval hfit_end hadm_bits).mono
    (fun y ⟨hmem, hy_sz, hy_wf, hy_regs⟩ => ?_) le_rfl
  have hout : ∀ a, (a < offTD U w N ∨ offDT U w N ≤ a) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    apply writePacked_outside hw x.mem hidx val
    unfold offDT at ha
    omega
  refine ⟨hy_sz, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), ?_, ?_, ?_, ?_,
    hout, fun d => denseItem_eq_of_high_words_eq hw (fun a ha => hout a (Or.inr ?_)) d, hy_regs⟩
  · funext idx'
    unfold tdAtBit
    by_cases hidx' : idx' < maxTailItems N
    · rw [ite_eq_left hidx', hmem]
      rcases eq_or_ne idx' idx with rfl | hne
      · rw [Function.update_self, readPacked_writePacked_self _ _ _ _ _ hval]
      · rw [Function.update_of_ne hne, ite_eq_left hidx',
          readPacked_writePacked_of_ne hw _ hne val]
    · have hne : idx' ≠ idx := by omega
      rw [ite_eq_right hidx', Function.update_of_ne hne, ite_eq_right hidx']
  · funext i
    unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inl
        (by have hhi := haddr.2; unfold offTD; omega))) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext ⟨c, j⟩
    unfold lmAtBit
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr => hout addr (Or.inl ?_)) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have hhi :
          addr < offLM U w N + c * packedWords (totalMicroBuckets N) (effBucketPosBits N) w +
            packedWords (totalMicroBuckets N) (effBucketPosBits N) w := haddr.2
      unfold offTD offGM
      rw [lmSubWords_eq] at hmul ⊢
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  · funext i
    unfold dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inr (by omega))) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · rw [← offDT_add_eq_epochMetaWords hN_pos] at ha
    omega


theorem readDTRegCode_exec {U V w N idx : ℕ} {rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < maxTailItems N) (hridx : x.regs rIdx = idx)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readDTRegCode rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = dtAtBit U w N x.mem idx ∧
        (∀ r : Fin 280, 12 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 45 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      epochMetaWords U w N :=
    (offDT_add_eq_epochMetaWords hN_pos).le
  have hadm_end : offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      x.wordSize w :=
    hle_meta.trans (epochMetaWords_le_wordSize_of_bitSize hw hsz)
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w) := by
    refine Fits.of_le hfit_bs ?_
    calc offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w
        ≤ epochMetaWords U w N := hle_meta
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  refine (readPackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hfit_end hadm_end).mono
    (fun y ⟨hmem, hwf, hrdst, hregs⟩ => ⟨hmem, hwf, ?_, hregs⟩) le_rfl
  unfold dtAtBit
  rw [ite_eq_left hidx, hrdst]

theorem writeDTRegCode_exec {U V w N idx val : ℕ} {rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 12 ≤ rIdx.val) (hrVal_ge : 12 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hidx : idx < maxTailItems N) (hval : val < 2 ^ globalPtrBits N)
    (hridx : x.regs rIdx = idx) (hrval : x.regs rVal = val)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (writeDTRegCode rIdx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        dtAtBit U w N y.mem = Function.update (dtAtBit U w N x.mem) idx val ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        (∀ a, (a < offDT U w N ∨ epochMetaWords U w N ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 12 ≤ r.val → y.regs r = x.regs r)) 56 := by
  have hact := her.active hN_pos
  have hkw : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hle_meta : offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
      epochMetaWords U w N :=
    (offDT_add_eq_epochMetaWords hN_pos).le
  have hadm_bits :
      (offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w) * w ≤ x.bitSize :=
    (Nat.mul_le_mul_right w hle_meta).trans hsz
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end : Fits w (offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w) :=
    Fits.of_le hfit_bs ((Nat.le_mul_of_pos_right _ hw).trans hadm_bits)
  refine (writePackedAtRegCode_exec (by decide) (by decide) hrIdx_ge hrVal_ge hw hkw hidx hx
    hact.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2.2.2.1 hridx hrval hfit_end hadm_bits).mono
    (fun y ⟨hmem, hy_sz, hy_wf, hy_regs⟩ => ?_) le_rfl
  have hout : ∀ a, (a < offDT U w N ∨ epochMetaWords U w N ≤ a) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    apply writePacked_outside hw x.mem hidx val
    rw [← offDT_add_eq_epochMetaWords hN_pos] at ha
    omega
  refine ⟨hy_sz, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs r (by omega)), ?_, ?_, ?_, ?_,
    hout, fun d => denseItem_eq_of_high_words_eq hw (fun a ha => hout a (Or.inr ha)) d, hy_regs⟩
  · funext idx'
    unfold dtAtBit
    by_cases hidx' : idx' < maxTailItems N
    · rw [ite_eq_left hidx', hmem]
      rcases eq_or_ne idx' idx with rfl | hne
      · rw [Function.update_self, readPacked_writePacked_self _ _ _ _ _ hval]
      · rw [Function.update_of_ne hne, ite_eq_left hidx',
          readPacked_writePacked_of_ne hw _ hne val]
    · have hne : idx' ≠ idx := by omega
      rw [ite_eq_right hidx', Function.update_of_ne hne, ite_eq_right hidx']
  · funext i
    unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inl
        (by have hhi := haddr.2; unfold offDT offTD; omega))) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext ⟨c, j⟩
    unfold lmAtBit
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr => hout addr (Or.inl ?_)) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have hhi :
          addr < offLM U w N + c * packedWords (totalMicroBuckets N) (effBucketPosBits N) w +
            packedWords (totalMicroBuckets N) (effBucketPosBits N) w := haddr.2
      unfold offDT offTD offGM
      rw [lmSubWords_eq] at hmul ⊢
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  · funext i
    unfold tdAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hout addr (Or.inl
        (by have hhi := haddr.2; unfold offDT; omega))) hi
    · rw [ite_eq_right hi, ite_eq_right hi]

theorem readLMRegCode_exec {U V w N c idx : ℕ} {rIdx rDst : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 13 ≤ rIdx.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hc : c < 9) (hidx : idx < totalMicroBuckets N) (hridx : x.regs rIdx = idx)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (readLMRegCode c rIdx rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = lmAtBit U w N x.mem (c, idx) ∧
        (∀ r : Fin 280, 13 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 48 := by
  have hact := her.active hN_pos
  have hkw : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hnU hU
  have hle_gm : offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
      offGM U w N := by
    have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
      Nat.mul_le_mul_right _ hc
    unfold offGM offLMSub
    rw [lmSubWords_eq] at hmul ⊢
    rw [Nat.add_one_mul] at hmul
    omega
  have hle_meta : offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
      epochMetaWords U w N := by
    refine hle_gm.trans ?_
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT offTD
    omega
  have hadm_end : offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
      x.wordSize w :=
    hle_meta.trans (epochMetaWords_le_wordSize_of_bitSize hw hsz)
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end :
      Fits w (offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w) := by
    refine Fits.of_le hfit_bs ?_
    calc offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w
        ≤ epochMetaWords U w N := hle_meta
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  have hfit_c : Fits w c := by
    refine Fits.of_le hfit_bs ?_
    have hlm_pos : 0 < Succinct.lmSubWords N w := lmSubWords_pos hw
    have h9 : 9 ≤ epochMetaWords U w N := by
      rw [← offDT_add_eq_epochMetaWords hN_pos]
      unfold offDT offTD offGM
      omega
    calc c ≤ 9 := by omega
      _ ≤ epochMetaWords U w N := h9
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  have hle_mul :
      c * Succinct.lmSubWords N w ≤
        offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w := by
    unfold offLMSub; omega
  have hfit_mul : Fits w (c * Succinct.lmSubWords N w) := Fits.of_le hfit_end hle_mul
  have hfit_sub : Fits w (offLMSub U w N c) :=
    Fits.of_le hfit_end (by omega)
  have hne12_idx : rIdx ≠ 12 := by intro h; subst h; omega
  refine DemonicExecWithin.step_const (T := 47) hfit_c ?_
  refine step_dExec_bin (v := c * Succinct.lmSubWords N w) (T := 46)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hact.2.2.2.2.2.2.2.2.2.2.1]) hfit_mul ?_
  refine step_dExec_bin (v := offLMSub U w N c) (T := 45)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hact.2.2.2.2.2.2.2.2.2.2.2.1, offLMSub,
          lmSubWords_eq])
    hfit_sub ?_
  set x₁ := ((x.set 12 c).set 12 (c * Succinct.lmSubWords N w)).set 12 (offLMSub U w N c)
  have hx₁_wf : x₁.WellFormed w :=
    wf_set 12 (wf_set 12 (wf_set 12 hx hfit_c) hfit_mul) hfit_sub
  refine (readPackedAtRegCode_exec (by decide) (by decide) (by omega) hw hkw hidx hx₁_wf
    (by simp +decide [x₁, BitRAM.Data.set])
    (by simp +decide [x₁, BitRAM.Data.set, hact.2.2.2.2.2.2.2.1])
    (by simp [x₁, BitRAM.Data.set, hne12_idx, hridx]) hfit_end hadm_end).mono
    (fun y ⟨hmem, hwf, hrdst, hregs⟩ => ⟨hmem, hwf, ?_, fun r hr hne => ?_⟩) le_rfl
  · unfold lmAtBit
    rw [ite_eq_left ⟨hc, hidx⟩, hrdst]
    rfl
  · rw [hregs r (by omega) hne]
    have hr12 : r ≠ 12 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, hr12]

theorem writeLMRegCode_exec {U V w N c idx val : ℕ} {rIdx rVal : Fin 280} {x : BitRAM.Data 280}
    (hrIdx_ge : 13 ≤ rIdx.val) (hrVal_ge : 13 ≤ rVal.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hc : c < 9) (hidx : idx < totalMicroBuckets N) (hval : val < 2 ^ effBucketPosBits N)
    (hridx : x.regs rIdx = idx) (hrval : x.regs rVal = val)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (writeLMRegCode c rIdx rVal) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        lmAtBit U w N y.mem = Function.update (lmAtBit U w N x.mem) (c, idx) val ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        tdAtBit U w N y.mem = tdAtBit U w N x.mem ∧
        dtAtBit U w N y.mem = dtAtBit U w N x.mem ∧
        (∀ a, (a < offLMSub U w N c ∨ offLMSub U w N (c + 1) ≤ a) → y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N x.toBitMemoryState d ∧
              denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 13 ≤ r.val → y.regs r = x.regs r)) 59 := by
  have hact := her.active hN_pos
  have hkw : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hnU hU
  have hle_gm : offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
      offGM U w N := by
    have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
      Nat.mul_le_mul_right _ hc
    unfold offGM offLMSub
    rw [lmSubWords_eq] at hmul ⊢
    rw [Nat.add_one_mul] at hmul
    omega
  have hle_meta : offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
      epochMetaWords U w N := by
    refine hle_gm.trans ?_
    rw [← offDT_add_eq_epochMetaWords hN_pos]
    unfold offDT offTD
    omega
  have hadm_bits :
      (offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w) * w ≤
        x.bitSize :=
    (Nat.mul_le_mul_right w hle_meta).trans hsz
  have hfit_bs : Fits w x.bitSize := hx.mem_wf.bitSize_fits
  have hfit_end :
      Fits w (offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w) :=
    Fits.of_le hfit_bs ((Nat.le_mul_of_pos_right _ hw).trans hadm_bits)
  have hfit_c : Fits w c := by
    refine Fits.of_le hfit_bs ?_
    have hlm_pos : 0 < Succinct.lmSubWords N w := lmSubWords_pos hw
    have h9 : 9 ≤ epochMetaWords U w N := by
      rw [← offDT_add_eq_epochMetaWords hN_pos]
      unfold offDT offTD offGM
      omega
    calc c ≤ 9 := by omega
      _ ≤ epochMetaWords U w N := h9
      _ ≤ epochMetaWords U w N * w := Nat.le_mul_of_pos_right _ hw
      _ ≤ x.bitSize := hsz
  have hle_mul :
      c * Succinct.lmSubWords N w ≤
        offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w := by
    unfold offLMSub; omega
  have hfit_mul : Fits w (c * Succinct.lmSubWords N w) := Fits.of_le hfit_end hle_mul
  have hfit_sub : Fits w (offLMSub U w N c) :=
    Fits.of_le hfit_end (by omega)
  have hne12_idx : rIdx ≠ 12 := by intro h; subst h; omega
  have hne12_val : rVal ≠ 12 := by intro h; subst h; omega
  refine DemonicExecWithin.step_const (T := 58) hfit_c ?_
  refine step_dExec_bin (v := c * Succinct.lmSubWords N w) (T := 57)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hact.2.2.2.2.2.2.2.2.2.2.1]) hfit_mul ?_
  refine step_dExec_bin (v := offLMSub U w N c) (T := 56)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hact.2.2.2.2.2.2.2.2.2.2.2.1, offLMSub,
          lmSubWords_eq])
    hfit_sub ?_
  set x₁ := ((x.set 12 c).set 12 (c * Succinct.lmSubWords N w)).set 12 (offLMSub U w N c)
  have hx₁_wf : x₁.WellFormed w :=
    wf_set 12 (wf_set 12 (wf_set 12 hx hfit_c) hfit_mul) hfit_sub
  refine (writePackedAtRegCode_exec (base := offLMSub U w N c) (N := totalMicroBuckets N)
    (k := effBucketPosBits N) (idx := idx) (val := val)
    (by decide) (by decide) (by omega) (by omega) hw hkw hidx hx₁_wf
    (by simp +decide [x₁, BitRAM.Data.set])
    (by simp +decide [x₁, BitRAM.Data.set, hact.2.2.2.2.2.2.2.1])
    (by simp [x₁, BitRAM.Data.set, hne12_idx, hridx])
    (by simp [x₁, BitRAM.Data.set, hne12_val, hrval]) hfit_end hadm_bits).mono
    (fun y ⟨hmem, hy_sz, hy_wf, hy_regs⟩ => ?_) le_rfl
  have hout : ∀ a, (a < offLMSub U w N c ∨ offLMSub U w N (c + 1) ≤ a) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    apply writePacked_outside hw x.mem hidx val
    unfold offLMSub at ha ⊢
    rw [lmSubWords_eq, Nat.add_one_mul] at ha
    rw [lmSubWords_eq]
    omega
  have hout_gm : ∀ a, offGM U w N ≤ a → y.mem a = x.mem a := by
    intro a ha
    apply hout a (Or.inr ?_)
    have hsub : offLMSub U w N (c + 1) =
        offLMSub U w N c + packedWords (totalMicroBuckets N) (effBucketPosBits N) w := by
      unfold offLMSub
      rw [lmSubWords_eq, Nat.add_one_mul]
      omega
    omega
  have hy_regs13 : ∀ r : Fin 280, 13 ≤ r.val → y.regs r = x.regs r := by
    intro r hr
    rw [hy_regs r (by omega)]
    have hr12 : r ≠ 12 := by intro h; subst h; omega
    simp [x₁, BitRAM.Data.set, hr12]
  refine ⟨hy_sz, hy_wf, her.congr_regs (fun r hr1 _ => hy_regs13 r (by omega)), ?_, ?_, ?_, ?_,
    hout, fun d => denseItem_eq_of_high_words_eq hw (fun a ha => hout_gm a ?_) d, hy_regs13⟩
  · funext ⟨c', j⟩
    unfold lmAtBit
    by_cases hcj : c' < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj]
      rcases eq_or_ne c' c with rfl | hnec
      · rw [hmem]
        rcases eq_or_ne j idx with rfl | hnej
        · rw [Function.update_self, readPacked_writePacked_self _ _ _ _ _ hval]
        · have hne_p : (c', j) ≠ (c', idx) := by intro h; exact hnej (Prod.mk.inj h).2
          rw [Function.update_of_ne hne_p, ite_eq_left hcj,
            readPacked_writePacked_of_ne hw _ hnej val]
          rfl
      · have hne_p : (c', j) ≠ (c, idx) := by intro h; exact hnec (Prod.mk.inj h).1
        rw [Function.update_of_ne hne_p, ite_eq_left hcj]
        apply readPacked_congr hw (fun addr haddr => hout addr ?_) hcj.2
        rcases lt_or_gt_of_ne hnec with hlt | hgt
        · left
          have hmul : (c' + 1) * Succinct.lmSubWords N w ≤ c * Succinct.lmSubWords N w :=
            Nat.mul_le_mul_right _ hlt
          have hhi :
              addr < offLM U w N + c' * Succinct.lmSubWords N w + Succinct.lmSubWords N w :=
            haddr.2
          unfold offLMSub
          rw [Nat.add_one_mul] at hmul
          omega
        · right
          have hmul : (c + 1) * Succinct.lmSubWords N w ≤ c' * Succinct.lmSubWords N w :=
            Nat.mul_le_mul_right _ hgt
          have hlo : offLM U w N + c' * Succinct.lmSubWords N w ≤ addr := haddr.1
          unfold offLMSub
          omega
    · have hne_p : (c', j) ≠ (c, idx) := by
        intro h
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        exact hcj ⟨hc, hidx⟩
      rw [ite_eq_right hcj, Function.update_of_ne hne_p, ite_eq_right hcj]
  · funext i
    unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr => hout_gm addr (by omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext i
    unfold tdAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      have hgm_td : offGM U w N ≤ offTD U w N := by unfold offTD; omega
      exact readPacked_congr hw (fun addr haddr => hout_gm addr (by omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · funext i
    unfold dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      have hgm_dt : offGM U w N ≤ offDT U w N := by unfold offDT offTD; omega
      exact readPacked_congr hw (fun addr haddr => hout_gm addr (by omega)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  · rw [← offDT_add_eq_epochMetaWords hN_pos] at ha
    unfold offDT offTD at ha
    omega

end Cslib.DataStructure.Dictionary.BitResizable
