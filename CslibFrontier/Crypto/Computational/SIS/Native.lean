/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Polynomial.Coefficients
public import CslibFrontier.Computability.PolyTime.Int.Negacyclic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv

/-!
# Native coefficient arithmetic for the existing Module-SIS ring

Polynomials of `ℤ_q[X] / (X^n + 1)` in coefficient form `Fin n → ZMod q` are represented natively
by the list of their canonical residues (`polyResidues`), and vectors of polynomials by lists of
such lists (`polyVecResidues`). The total list operations `negacyclicMulResidues`, `addResidues`
and `negacyclicInnerResidues` are identified with `negacyclicMul`, polynomial addition and
`innerPoly`, including degree zero and positive composite coefficient moduli, and have plain
polynomial-time certificates with a unary degree and a binary modulus. This is original supporting
representation algebra; it supplies neither a new encryption algorithm nor a security claim.

## Main definitions

* `Cslib.Crypto.polyResidues`, `Cslib.Crypto.polyVecResidues`: residue lists of a polynomial and of
  a vector of polynomials, and `Cslib.Crypto.encPolyVecResidues`, the words of the latter.
* `Cslib.Crypto.addResidues`, `Cslib.Crypto.subResidues`, `Cslib.Crypto.negacyclicInnerResidues`:
  coefficientwise addition and subtraction, and the inner product `∑ⱼ aⱼ · rⱼ`, on residue lists.

## Main results

* `negacyclicMulResidues_ofFn`: exact canonical coefficients for positive moduli.
* `addResidues_polyResidues`, `negacyclicInnerResidues_polyVecResidues`: the list operations
  compute polynomial addition and `innerPoly`.
* `Turing.MultiTapeTM.ComputableInPolyTime.addResidues`,
  `Turing.MultiTapeTM.ComputableInPolyTime.negacyclicInnerResidues`: their certificates.
-/

public section

namespace Cslib.Crypto

open Polynomial Turing.MultiTapeTM

/-- The native list product returns precisely the canonical coefficients of the existing
negacyclic multiplication. Positive composite moduli and modulus one are allowed. -/
theorem negacyclicMulResidues_ofFn {n q : ℕ} (hq : 0 < q)
    (a b : Fin n → ZMod q) :
    negacyclicMulResidues n q (List.ofFn fun i => (a i).val)
      (List.ofFn fun i => (b i).val) =
        List.ofFn fun i => (negacyclicMul a b i).val := by
  let : NeZero q := ⟨by omega⟩
  let ai : Fin n → ℤ := fun i => (a i).val
  let bi : Fin n → ℤ := fun i => (b i).val
  have hcast (i : Fin n) : ((negacyclicMul ai bi i : ℤ) : ZMod q) = negacyclicMul a b i := by
    have h := congrFun (map_negacyclicMul (Int.castRingHom (ZMod q)) ai bi) i
    simpa [ai, bi, Function.comp_def] using h
  have haTake : (List.ofFn fun i => (a i).val).take n = List.ofFn fun i => (a i).val :=
    List.take_of_length_le (by simp)
  have hbTake : (List.ofFn fun i => (b i).val).take n = List.ofFn fun i => (b i).val :=
    List.take_of_length_le (by simp)
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hin : i < n := by simpa using hi
  simp only [negacyclicMulResidues, haTake, hbTake, List.map_ofFn,
    List.getElem_map, List.getElem_range, List.getElem_ofFn]
  change (((mulZJet (2 * n) (List.ofFn ai) (List.ofFn bi)).getD i 0 -
    (mulZJet (2 * n) (List.ofFn ai) (List.ofFn bi)).getD (n + i) 0) % (q : ℤ)).toNat = _
  rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet (by omega),
    ← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet (by omega),
    ← negacyclicMul_eq_coeff_mul ai bi ⟨i, hin⟩, ← ZMod.val_intCast]
  simpa only [Int.toNat_natCast] using congrArg ZMod.val (hcast ⟨i, hin⟩)

/-- The canonical residues `f₀.val, …, f_{n-1}.val` of a polynomial in coefficient form. -/
@[expose] def polyResidues {n m : ℕ} (f : Fin n → ZMod m) : List ℕ :=
  List.ofFn fun i => (f i).val

/-- The residue lists of the polynomials of a vector, in order. -/
@[expose] def polyVecResidues {k n m : ℕ} (v : Fin k → Fin n → ZMod m) : List (List ℕ) :=
  List.ofFn fun j => polyResidues (v j)

/-- The words of residue lists of polynomial vectors: the framed list of the framed residue lists
of the polynomials, each residue in binary. -/
abbrev encPolyVecResidues : List (List ℕ) ↪ List Bool :=
  encList (encList encNat)

/-- Coefficientwise addition modulo `q` of two residue lists, truncated to the shorter one. -/
@[expose] def addResidues (q : ℕ) (a b : List ℕ) : List ℕ :=
  (a.zip b).map fun x => (x.1 + x.2) % q

/-- Coefficientwise subtraction modulo `q` of two residue lists, truncated to the shorter one. -/
@[expose] def subResidues (q : ℕ) (a b : List ℕ) : List ℕ :=
  (a.zip b).map fun x => (((x.1 : ℤ) - x.2) % (q : ℤ)).toNat

/-- The inner product `∑ⱼ aⱼ · rⱼ` in `ℤ_q[X] / (X^n + 1)` of two vectors of residue lists, with
`n` output coefficients. Products are taken over the shorter vector. -/
@[expose] def negacyclicInnerResidues (n q : ℕ) (a r : List (List ℕ)) : List ℕ :=
  let products := (a.zip r).map fun x => negacyclicMulResidues n q x.1 x.2
  (List.range n).map fun i => (products.map fun p => p.getD i 0).sum % q

/-- Native addition computes polynomial addition. -/
theorem addResidues_polyResidues {n q : ℕ} [NeZero q] (f g : Fin n → ZMod q) :
    addResidues q (polyResidues f) (polyResidues g) = polyResidues (f + g) := by
  apply List.ext_getElem (by simp [addResidues, polyResidues])
  intro i h₁ h₂
  simp [addResidues, polyResidues, ZMod.val_add]

/-- Native subtraction computes polynomial subtraction. -/
theorem subResidues_polyResidues {n q : ℕ} [NeZero q] (f g : Fin n → ZMod q) :
    subResidues q (polyResidues f) (polyResidues g) = polyResidues (f - g) := by
  apply List.ext_getElem (by simp [subResidues, polyResidues])
  intro i h₁ h₂
  simp only [subResidues, polyResidues, List.getElem_map, List.getElem_zip, List.getElem_ofFn,
    Pi.sub_apply]
  rw [← ZMod.val_intCast, Int.toNat_natCast]
  congr 1
  push_cast
  simp

/-- The native inner product computes `innerPoly`. -/
theorem negacyclicInnerResidues_polyVecResidues {k n q : ℕ} [NeZero q]
    (a r : Fin k → Fin n → ZMod q) :
    negacyclicInnerResidues n q (polyVecResidues a) (polyVecResidues r) =
      polyResidues (innerPoly a r) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hproducts : ((polyVecResidues a).zip (polyVecResidues r)).map
      (fun x => negacyclicMulResidues n q x.1 x.2) =
      List.ofFn fun j => polyResidues (negacyclicMul (a j) (r j)) := by
    apply List.ext_getElem (by simp [polyVecResidues])
    intro j h₁ h₂
    simp only [polyVecResidues, List.getElem_map, List.getElem_zip, List.getElem_ofFn,
      polyResidues]
    exact negacyclicMulResidues_ofFn hq _ _
  rw [negacyclicInnerResidues, hproducts]
  apply List.ext_getElem (by simp [polyResidues])
  intro i h₁ h₂
  have hi : i < n := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, polyResidues, List.getElem_ofFn, innerPoly,
    Finset.sum_apply, List.map_ofFn, Function.comp_def, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, List.sum_ofFn]
  rw [← ZMod.val_natCast, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [hi]

end Cslib.Crypto

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Coefficientwise addition of computed residue lists modulo a computed binary modulus. -/
@[fun_prop]
theorem addResidues {q : α → ℕ} {a b : α → List ℕ} (hq : ComputableInPolyTime q input encNat)
    (ha : ComputableInPolyTime a input (encList encNat))
    (hb : ComputableInPolyTime b input (encList encNat)) :
    ComputableInPolyTime (fun x => Cslib.Crypto.addResidues (q x) (a x) (b x)) input
      (encList encNat) := by
  unfold Cslib.Crypto.addResidues
  apply mapWithInput ((zip encNat encNat).comp (ha.prod hb))
  exact binary_mod' (binary_add' ((fst encNat encNat).comp (snd input _))
    ((snd encNat encNat).comp (snd input _))) (hq.comp (fst input _))

/-- Coefficientwise subtraction of computed residue lists modulo a computed binary modulus. -/
@[fun_prop]
theorem subResidues {q : α → ℕ} {a b : α → List ℕ} (hq : ComputableInPolyTime q input encNat)
    (ha : ComputableInPolyTime a input (encList encNat))
    (hb : ComputableInPolyTime b input (encList encNat)) :
    ComputableInPolyTime (fun x => Cslib.Crypto.subResidues (q x) (a x) (b x)) input
      (encList encNat) := by
  unfold Cslib.Crypto.subResidues
  apply mapWithInput ((zip encNat encNat).comp (ha.prod hb))
  exact intBin_emodNat' (intBin_sub' (intBin_natCast.comp ((fst encNat encNat).comp (snd input _)))
    (intBin_natCast.comp ((snd encNat encNat).comp (snd input _)))) (hq.comp (fst input _))

/-- The native inner product with a computed unary degree and binary modulus. -/
@[fun_prop]
theorem negacyclicInnerResidues {n q : α → ℕ} {a r : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encUnary) (hq : ComputableInPolyTime q input encNat)
    (ha : ComputableInPolyTime a input Cslib.Crypto.encPolyVecResidues)
    (hr : ComputableInPolyTime r input Cslib.Crypto.encPolyVecResidues) :
    ComputableInPolyTime (fun x => Cslib.Crypto.negacyclicInnerResidues (n x) (q x) (a x) (r x))
      input (encList encNat) := by
  unfold Cslib.Crypto.negacyclicInnerResidues
  have hzip := (zip (encList encNat) (encList encNat)).comp (ha.prod hr)
  have hfst := fst input (encPair (encList encNat) (encList encNat))
  have hsnd := snd input (encPair (encList encNat) (encList encNat))
  have hmul := Cslib.computableInPolyTime_negacyclicMulResidues.comp
    (((hn.comp hfst).prod (hq.comp hfst)).prod hsnd)
  simp only [Function.comp_def] at hmul hzip
  have hproducts := mapWithInput
    (f := fun (x : α) (y : List ℕ × List ℕ) => Cslib.negacyclicMulResidues (n x) (q x) y.1 y.2)
    hzip hmul
  have hfst' := fst input encUnary
  have hget := (listGetD (encA := encNat) 0).comp
    ((snd (encPair input encUnary) (encList encNat)).prod
      ((snd input encUnary).comp (fst (encPair input encUnary) (encList encNat))))
  have hcolumn := mapWithInput (f := fun (y : α × ℕ) (p : List ℕ) => p.getD y.2 0)
    (hproducts.comp hfst') hget
  have hsum := binary_mod' (binary_sum.comp hcolumn) (hq.comp hfst')
  have hrange := range.comp hn
  simp only [Function.comp_def] at hsum hrange
  exact mapWithInput hrange hsum

end Turing.MultiTapeTM.ComputableInPolyTime
