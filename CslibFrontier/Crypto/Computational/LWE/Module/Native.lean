/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Module
public import CslibFrontier.Crypto.Computational.SIS.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native decoding of Module-LWE sample words

A Module-LWE sample `(A, b)` is encoded by `ModuleLWE.encodeSample` as the rows of the expanded
matrix `expandModuleMatrix A` and the flattened residues of `b`. This module reads the residue lists
of the polynomials back from these words with total list functions that have plain
polynomial-time certificates in unary dimensions: `ModuleLWE.entryResidues` reads the entries of
`A` from column `0` of each rotation block (`entryResidues_encodeMatrix`), and
`ModuleLWE.chunkResidues` splits the residues of `b` into polynomials
(`chunkResidues_flattenPolyVec`). Reductions that receive a sample word and build words of their
own from it use them. This is original supporting representation algebra; it makes no security
claim.

## Main definitions

* `Cslib.Crypto.ModuleLWE.entryResidues`, `Cslib.Crypto.ModuleLWE.chunkResidues`: reading residue
  lists from expanded rows and from flattened residues.
* `Cslib.Crypto.ModuleLWE.sampleDecoder`: the decoder of sample words.

## Main results

* `Cslib.Crypto.ModuleLWE.entryResidues_encodeMatrix`,
  `Cslib.Crypto.ModuleLWE.chunkResidues_flattenPolyVec`: the list functions read the residues of
  the encoded polynomials.
* `Turing.MultiTapeTM.ComputableInPolyTime.entryResidues`,
  `Turing.MultiTapeTM.ComputableInPolyTime.chunkResidues`: their certificates.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

namespace ModuleLWE

/-- The residue lists of the polynomial entries of a `d × k` module matrix, read from the rows of
its expansion `expandModuleMatrix`: coefficient `t` of entry `(i, j)` is the entry in row
`t + n * i` and column `n * j`. -/
def entryResidues (d k n : ℕ) (rows : List (List ℕ)) : List (List (List ℕ)) :=
  (List.range d).map fun i => (List.range k).map fun j => (List.range n).map fun t =>
    (rows.getD (t + n * i) []).getD (n * j) 0

/-- Split a flattened residue list into `k` residue lists of `n` coefficients: coefficient `t` of
polynomial `j` is entry `t + n * j`, the layout of `flattenPolyVec`. -/
def chunkResidues (k n : ℕ) (flat : List ℕ) : List (List ℕ) :=
  (List.range k).map fun j => (List.range n).map fun t => flat.getD (t + n * j) 0

/-- The decoder of sample words `encodeSample (A, b)`: the expanded rows of `A` and the flattened
residues of `b`. -/
def sampleDecoder : Decoder (encPair encBits (encList encNat)) :=
  Decoder.pair Decoder.bits (Decoder.list Decoder.nat)

/-- Reading the entries of the expanded rows of an encoded module matrix gives the residue lists of
its entries. -/
theorem entryResidues_encodeMatrix {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) :
    entryResidues d k n ((Decoder.list (Decoder.list Decoder.nat)).decode
      (ModuleSIS.encodeMatrix A)) = List.ofFn fun i => polyVecResidues (A i) := by
  rw [ModuleSIS.encodeMatrix, SIS.encodeMatrix, Decoder.decode_enc]
  apply List.ext_getElem (by simp [entryResidues])
  intro i h₁ h₂
  have hi : i < d := by simpa [entryResidues] using h₁
  apply List.ext_getElem (by simp [entryResidues, polyVecResidues])
  intro j h₃ h₄
  have hj : j < k := by simpa [entryResidues] using h₃
  apply List.ext_getElem (by simp [entryResidues, polyVecResidues, polyResidues])
  intro t h₅ h₆
  have ht : t < n := by simpa [entryResidues] using h₅
  have hrow : t + n * i < d * n := by nlinarith
  have hcol : n * j < k * n := by nlinarith
  simp only [entryResidues, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    polyVecResidues, polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hrow]
  simp only [dite_true, Option.getD_some, List.getElem?_ofFn, hcol]
  have hr : (⟨t + n * i, hrow⟩ : Fin (d * n)) = finProdFinEquiv (⟨i, hi⟩, ⟨t, ht⟩) :=
    Fin.ext (by simp [finProdFinEquiv_apply_val])
  have hc : (⟨n * j, hcol⟩ : Fin (k * n)) = finProdFinEquiv (⟨j, hj⟩, ⟨0, by omega⟩) :=
    Fin.ext (by simp [finProdFinEquiv_apply_val])
  simp only [hr, hc, expandModuleMatrix_apply]
  simp [rotMatrix]

/-- Chunking the flattened residues of a polynomial vector recovers its residue lists. -/
theorem chunkResidues_flattenPolyVec {k n q : ℕ} (v : Fin k → Fin n → ZMod q) :
    chunkResidues k n (List.ofFn fun c => (flattenPolyVec v c).val) = polyVecResidues v := by
  apply List.ext_getElem (by simp [chunkResidues, polyVecResidues])
  intro j h₁ h₂
  have hj : j < k := by simpa [chunkResidues] using h₁
  apply List.ext_getElem (by simp [chunkResidues, polyVecResidues, polyResidues])
  intro t h₃ h₄
  have ht : t < n := by simpa [chunkResidues] using h₃
  have hidx : t + n * j < k * n := by nlinarith
  have hc : (⟨t + n * j, hidx⟩ : Fin (k * n)) = finProdFinEquiv (⟨j, hj⟩, ⟨t, ht⟩) :=
    Fin.ext (by simp [finProdFinEquiv_apply_val])
  simp only [chunkResidues, List.getElem_map, List.getElem_range, polyVecResidues, polyResidues,
    List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hidx, dite_true,
    Option.getD_some, hc, flattenPolyVec, Function.comp_apply, Equiv.symm_apply_apply,
    Function.uncurry_apply_pair]

end ModuleLWE

end Cslib.Crypto

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Reading the entries of a module matrix from expanded rows, with computed unary dimensions. -/
@[fun_prop]
theorem entryResidues {d k n : α → ℕ} {rows : α → List (List ℕ)}
    (hd : ComputableInPolyTime d input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hrows : ComputableInPolyTime rows input Cslib.Crypto.encPolyVecResidues) :
    ComputableInPolyTime (fun x => Cslib.Crypto.ModuleLWE.entryResidues (d x) (k x) (n x) (rows x))
      input (encList Cslib.Crypto.encPolyVecResidues) := by
  unfold Cslib.Crypto.ModuleLWE.entryResidues
  let I := encPair (encPair input encUnary) encUnary
  have hcoeff : ComputableInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ =>
      ((rows p.1.1.1).getD (p.2 + n p.1.1.1 * p.1.1.2) []).getD (n p.1.1.1 * p.1.2) 0)
      (encPair I encUnary) encNat := by
    have hr : ComputableInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => rows p.1.1.1)
        (encPair I encUnary) Cslib.Crypto.encPolyVecResidues := hrows.comp (by fun_prop)
    have hn' : ComputableInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => n p.1.1.1)
        (encPair I encUnary) encUnary := hn.comp (by fun_prop)
    have hi : ComputableInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => p.2 + n p.1.1.1 * p.1.1.2)
        (encPair I encUnary) encUnary :=
      unary_add' (by fun_prop) (unary_mul' hn' (by fun_prop))
    have hj : ComputableInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => n p.1.1.1 * p.1.2)
        (encPair I encUnary) encUnary := unary_mul' hn' (by fun_prop)
    exact listGetDWithInput (listGetDWithInput hr hi []) hj 0
  have hpoly : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => (List.range (n p.1.1)).map fun t =>
      ((rows p.1.1).getD (t + n p.1.1 * p.1.2) []).getD (n p.1.1 * p.2) 0) I (encList encNat) :=
    mapWithInput (range.comp (hn.comp (by fun_prop))) hcoeff
  have hrow : ComputableInPolyTime (fun p : α × ℕ => (List.range (k p.1)).map fun j =>
      (List.range (n p.1)).map fun t => ((rows p.1).getD (t + n p.1 * p.2) []).getD (n p.1 * j) 0)
      (encPair input encUnary) Cslib.Crypto.encPolyVecResidues :=
    mapWithInput (range.comp (hk.comp (by fun_prop))) hpoly
  exact mapWithInput (range.comp hd) hrow

/-- Chunking a flattened residue list, with computed unary dimensions. -/
@[fun_prop]
theorem chunkResidues {k n : α → ℕ} {flat : α → List ℕ}
    (hk : ComputableInPolyTime k input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hflat : ComputableInPolyTime flat input (encList encNat)) :
    ComputableInPolyTime (fun x => Cslib.Crypto.ModuleLWE.chunkResidues (k x) (n x) (flat x))
      input Cslib.Crypto.encPolyVecResidues := by
  unfold Cslib.Crypto.ModuleLWE.chunkResidues
  have hcoeff : ComputableInPolyTime
      (fun p : (α × ℕ) × ℕ => (flat p.1.1).getD (p.2 + n p.1.1 * p.1.2) 0)
      (encPair (encPair input encUnary) encUnary) encNat :=
    listGetDWithInput (hflat.comp (by fun_prop))
      (unary_add' (by fun_prop) (unary_mul' (hn.comp (by fun_prop)) (by fun_prop))) 0
  have hpoly : ComputableInPolyTime (fun p : α × ℕ => (List.range (n p.1)).map fun t =>
      (flat p.1).getD (t + n p.1 * p.2) 0) (encPair input encUnary) (encList encNat) :=
    mapWithInput (range.comp (hn.comp (by fun_prop))) hcoeff
  exact mapWithInput (range.comp hk) hpoly

end Turing.MultiTapeTM.ComputableInPolyTime
