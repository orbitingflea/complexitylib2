/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Computability.WordRAM.Width

/-!
# `Memory.Prog` Bit-Packed Array Primitives and Uniform `Realizes` Certificates

This module wraps the overflow-free bit-packed array operations (`readPacked`, `writePacked`) from
`CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray` as `Memory.Prog` operations
(`readPackedProg`, `writePackedProg`) together with their `Memory.spec` functional, admissibility,
and cost lemmas and uniform parameter-free `Realizes .exact` certificates (`realizes_readPackedGen`,
`realizes_writePackedGen`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.writePackedProg`: `Memory.Prog` wrappers
  for bit-packed array reads and writes at `base + offset`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPackedGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.writePackedGenProg`: parameter-free
  `Memory.Prog` wrappers for `Realizes .exact`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.clientResult_readPackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.clientState_readPackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.memoryCost_readPackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.validHistory_readPackedProg`: `Memory.spec`
  characterization and admissibility of `readPackedProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.clientResult_writePackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.clientState_writePackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.memoryCost_writePackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.validHistory_writePackedProg`:
  `Memory.spec` characterization and admissibility of `writePackedProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPackedCode_not_readsWidth`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.writePackedCode_not_readsWidth`:
  width-opcode freedom (`¬ReadsWidth`) of `readPackedCode` and `writePackedCode`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.realizes_readPackedGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.realizes_writePackedGen`: uniform
  parameter-free `Realizes .exact` certificates for `readPackedGenProg` and `writePackedGenProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory

/-- `Memory.Prog` operation reading the `k`-bit entry at index `idx` from a bit-packed array at
`base + offset` on a `w`-bit machine. -/
@[expose] def readPackedProg (base offset k w idx : ℕ) : Memory.Prog ℕ := do
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let word₀ ← Memory.read (base + offset + wOff)
  let word₁ ← Memory.read (base + offset + wOff + 1)
  let low := (word₀ >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (word₁ >>> 0) &&& (2 ^ k₁ - 1)
  pure (low ^^^ (high <<< k₀))

/-- `Memory.Prog` operation writing `val` (`< 2 ^ k`) into the `k`-bit entry at index `idx` of a
bit-packed array at `base + offset` on a `w`-bit machine. -/
@[expose] def writePackedProg (base offset k w idx val : ℕ) : Memory.Prog Unit := do
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let word₀ ← Memory.read (base + offset + wOff)
  let old₀ := (word₀ >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  Memory.write (base + offset + wOff) (word₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let word₁ ← Memory.read (base + offset + wOff + 1)
  let old₁ := (word₁ >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Memory.write (base + offset + wOff + 1) (word₁ ^^^ ((old₁ ^^^ val₁) <<< 0))

@[simp]
theorem clientResult_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedProg base offset k w idx) =
      readPacked (base + offset) k w s.mem idx :=
  rfl

theorem clientState_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedProg base offset k w idx) = s :=
  rfl

@[simp]
theorem memoryCost_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    memoryCost (readPackedProg base offset k w idx) s = 2 :=
  rfl

@[simp]
theorem clientResult_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writePackedProg base offset k w idx val) = () :=
  rfl

theorem clientState_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (writePackedProg base offset k w idx val) =
      { mem := writePacked (base + offset) k w s.mem idx val, frontier := s.frontier } :=
  rfl

@[simp]
theorem memoryCost_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    memoryCost (writePackedProg base offset k w idx val) s = 4 :=
  rfl

theorem validHistory_readPackedProg {w base offset N k idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N)
    (ha : base + offset + packedWords N k w ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readPackedProg base offset k w idx)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  change base + offset + wordOffset k w idx < s.frontier ∧
    base + offset + wordOffset k w idx + 1 < s.frontier ∧ True
  exact ⟨by omega, by omega, trivial⟩

theorem validHistory_writePackedProg {w base offset N k idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hwf : Memory.WellFormed w s)
    (ha : base + offset + packedWords N k w ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writePackedProg base offset k w idx val)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set old₀ := (s.mem (base + offset + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  have hδ0_lt : old₀ ^^^ val₀ < 2 ^ k₀ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₀, val₀]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh0_lt : (old₀ ^^^ val₀) <<< bOff < 2 ^ w := by
    refine shiftLeft_lt_two_pow_of_lt hδ0_lt ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hw0 : Fits w (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff)) :=
    Nat.xor_lt_two_pow (hwf.2 _) hsh0_lt
  let mem₁ := Function.update s.mem (base + offset + wOff)
    (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  have hm1 : Fits w (mem₁ (base + offset + wOff + 1)) := by
    dsimp only [mem₁]
    rw [Function.update_of_ne (by omega)]
    exact hwf.2 _
  set old₁ := (mem₁ (base + offset + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hδ1_lt : old₁ ^^^ val₁ < 2 ^ k₁ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh1_lt : (old₁ ^^^ val₁) <<< 0 < 2 ^ w :=
    hδ1_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hw1 : Fits w (mem₁ (base + offset + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) :=
    Nat.xor_lt_two_pow hm1 hsh1_lt
  change base + offset + wOff < s.frontier ∧
    ((base + offset + wOff < s.frontier ∧
      Fits w (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))) ∧
    base + offset + wOff + 1 < s.frontier ∧
    (base + offset + wOff + 1 < s.frontier ∧
      Fits w (mem₁ (base + offset + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))) ∧ True)
  exact ⟨by omega, ⟨by omega, hw0⟩, by omega, ⟨by omega, hw1⟩, trivial⟩

/-- `readPackedCode` does not invoke `Op.width`. -/
theorem readPackedCode_not_readsWidth :
    ¬readPackedCode.ReadsWidth := by
  simp [readPackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, readPackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- `writePackedCode` does not invoke `Op.width`. -/
theorem writePackedCode_not_readsWidth :
    ¬writePackedCode.ReadsWidth := by
  simp [writePackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, writePackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- Parameter-free `Memory.Prog` wrapper for `readPackedProg` taking
`(((base, offset), (k, w)), idx)`. -/
@[expose] def readPackedGenProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | (((base, offset), (k, w)), idx) => readPackedProg base offset k w idx

/-- Parameter-free `Memory.Prog` wrapper for `writePackedProg` taking
`((((base, offset), (k, w)), idx), val)`. -/
@[expose] def writePackedGenProg : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | ((((base, offset), (k, w)), idx), val) => writePackedProg base offset k w idx val

/-- Uniform parameter-free `Realizes .exact` certificate for `readPackedGenProg`. -/
theorem realizes_readPackedGen :
    Realizes .exact readPackedGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w (((base, offset), (k, w')), idx) _ => ∃ N, w = w' ∧ 0 < w ∧ k ≤ w ∧ idx < N ∧
        Fits w (base + offset + packedWords N k w))
      (fun _ _ => 0) := by
  let perm : Fin 10 ≃ Fin 10 := Equiv.swap 0 2
  refine ⟨8, 38, fun _ src tmp =>
    .seq (.op (.exactBin .add (tmp 2) (src 0) (src 1)))
      (.seq (.op (.copy (tmp 1) (src 4)))
        (.seq (.op (.copy (tmp 8) (src 3)))
          (.seq (.op (.copy (tmp 9) (src 2)))
            (readPackedCode.rename (tmp ∘ perm))))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hperm_inj : Function.Injective (tmp ∘ perm) := hi.comp perm.injective
  refine ⟨?_, ?_⟩
  · simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Code.readsWidth_rename,
      readPackedCode_not_readsWidth]
  · intro w ⟨⟨⟨base, offset⟩, ⟨k, w'⟩⟩, idx⟩ x hx hin ⟨N, heq, hw, hkw, hidx, hfit⟩ _
    have hsrc0 : x.regs (src 0) = base := congrFun hin 0
    have hsrc1 : x.regs (src 1) = offset := congrFun hin 1
    have hsrc2 : x.regs (src 2) = k := congrFun hin 2
    have hsrc3 : x.regs (src 3) = w' := congrFun hin 3
    have hsrc4 : x.regs (src 4) = idx := congrFun hin 4
    refine WP.exists_execWithin ?_
    wram_exec [hsrc0, hsrc1]
    · refine WP.name fun x₄ hx₄ => ?_
      have hx₄b : x₄.Bounded w := by rw [hx₄]; wram_bounded; exact hfit.of_le (by omega)
      have hreg (a : Fin 10) (b : Fin 10) (h : perm a = b) :
          (x₄.comap (tmp ∘ perm)).regs a = x₄.regs (tmp b) := by rw [← h]; rfl
      obtain ⟨y_core, hex_core, hymem, _, _, hy2⟩ := readPackedCode_execWithin hw hkw hidx
        (hx₄b.comap (tmp ∘ perm)) (by rw [hreg 0 2 (by decide), hx₄]; wram_simp)
        (by rw [hreg 1 1 (by decide), hx₄]; wram_simp [hsrc4])
        (by rw [hreg 8 8 (by decide), hx₄]; wram_simp [hsrc3, heq])
        (by rw [hreg 9 9 (by decide), hx₄]; wram_simp [hsrc2]) hfit
      refine WP.of_execWithin (hex_core.rename hperm_inj) ⟨?_, ?_, ?_, ?_⟩
      · change 34 + 1 + 1 + 1 + 1 ≤ 38 * (2 + 0 + 1); omega
      · apply Memory.State.ext
        · change y_core.mem = x.mem
          rw [hymem, hx₄]
          rfl
        · change Function.extend (tmp ∘ perm) y_core.regs x₄.regs frontier = x.regs frontier
          rw [Function.extend_apply' (f := tmp ∘ perm) _ _ _ fun ⟨j, hj⟩ => hf (perm j) hj, hx₄]
          wram_simp
      · intro i
        have hi0 : i = 0 := Fin.eq_zero i
        subst hi0
        rw [clientResult_width]
        change (y_core.extend (tmp ∘ perm) x₄).regs (tmp 0) =
          readPacked (base + offset) k w' x.mem idx
        have hp2 : tmp 0 = (tmp ∘ perm) 2 := by congr 1
        rw [hp2]
        change ((y_core.extend (tmp ∘ perm) x₄).comap (tmp ∘ perm)).regs 2 = _
        rw [Data.comap_extend hperm_inj, hy2, ← heq, hx₄]
        rfl
      · intro i _ htmp
        change Function.extend (tmp ∘ perm) y_core.regs x₄.regs i = x.regs i
        rw [Function.extend_apply' (f := tmp ∘ perm) _ _ _ fun ⟨j, hj⟩ => htmp (perm j) hj, hx₄]
        wram_simp

/-- Uniform parameter-free `Realizes .exact` certificate for `writePackedGenProg`. -/
theorem realizes_writePackedGen :
    Realizes .exact writePackedGenProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w ((((base, offset), (k, w')), idx), _val) _ => ∃ N, w = w' ∧ 0 < w ∧ k ≤ w ∧ idx < N ∧
        Fits w (base + offset + packedWords N k w))
      (fun _ _ => 0) := by
  refine ⟨9, 50, fun _ src tmp =>
    .seq (.op (.exactBin .add (tmp 0) (src 0) (src 1)))
      (.seq (.op (.copy (tmp 1) (src 4)))
        (.seq (.op (.copy (tmp 2) (src 5)))
          (.seq (.op (.copy (tmp 8) (src 3)))
            (.seq (.op (.copy (tmp 9) (src 2)))
              (writePackedCode.rename tmp))))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨?_, ?_⟩
  · simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Code.readsWidth_rename,
      writePackedCode_not_readsWidth]
  · intro w ⟨⟨⟨⟨base, offset⟩, ⟨k, w'⟩⟩, idx⟩, val⟩ x hx hin ⟨N, heq, hw, hkw, hidx, hfit⟩ _
    have hsrc0 : x.regs (src 0) = base := congrFun hin 0
    have hsrc1 : x.regs (src 1) = offset := congrFun hin 1
    have hsrc2 : x.regs (src 2) = k := congrFun hin 2
    have hsrc3 : x.regs (src 3) = w' := congrFun hin 3
    have hsrc4 : x.regs (src 4) = idx := congrFun hin 4
    have hsrc5 : x.regs (src 5) = val := congrFun hin 5
    refine WP.exists_execWithin ?_
    wram_exec [hsrc0, hsrc1]
    · refine WP.name fun x₅ hx₅ => ?_
      have hx₅b : x₅.Bounded w := by rw [hx₅]; wram_bounded; exact hfit.of_le (by omega)
      obtain ⟨y_core, hex_core, hymem, _, _, _⟩ := writePackedCode_execWithin (val := val) hw hkw
        hidx (hx₅b.comap tmp) (by rw [Data.comap_regs, hx₅]; wram_simp)
        (by rw [Data.comap_regs, hx₅]; wram_simp [hsrc4])
        (by rw [Data.comap_regs, hx₅]; wram_simp [hsrc5])
        (by rw [Data.comap_regs, hx₅]; wram_simp [hsrc3, heq])
        (by rw [Data.comap_regs, hx₅]; wram_simp [hsrc2]) hfit
      refine WP.of_execWithin (hex_core.rename hi) ⟨?_, ?_, ?_, ?_⟩
      · change 45 + 1 + 1 + 1 + 1 + 1 ≤ 50 * (4 + 0 + 1); omega
      · apply Memory.State.ext
        · change y_core.mem =
            writePacked (base + offset) k w' x.mem idx val
          rw [hymem, ← heq, hx₅]
          rfl
        · change Function.extend tmp y_core.regs x₅.regs frontier = x.regs frontier
          rw [Function.extend_apply' (f := tmp) _ _ _ fun ⟨j, hj⟩ => hf j hj, hx₅]
          wram_simp
      · intro i
        exact Fin.elim0 i
      · intro i _ htmp
        change Function.extend tmp y_core.regs x₅.regs i = x.regs i
        rw [Function.extend_apply' (f := tmp) _ _ _ fun ⟨j, hj⟩ => htmp j hj, hx₅]
        wram_simp

end Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

end
