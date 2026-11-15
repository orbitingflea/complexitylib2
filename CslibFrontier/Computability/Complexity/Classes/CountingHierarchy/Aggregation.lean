/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Oracle.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Counting and summation over short indices

A uniform F_a evaluator on an instance and a bitstring can be counted or summed in F_(a+1).
The index width is computed in unary in polynomial time; its domain can therefore have
exponentially many elements. Natural and signed summands have polynomial encoded length by
their function-level certificate. No enumeration of the domain is performed by the deterministic
program, and its oracle is fixed for every instance and index.

Inputs have a certified total decoder, as do words and the usual structured encodings.
Restrictions can be included in the evaluator using zero outside the domain. Quantification
uses the same count oracle, including the empty bitstring when the width is zero.

## Main results

* `Cslib.Complexity.CountingFunction.count_bits`: exact short-index counting.
* `Cslib.Complexity.CountingFunction.sum_bits`, `.sum_bits_int`: nonnegative and signed sums.
* `Cslib.Complexity.CountingFunction.exists_bits`, `.forall_bits`: bounded quantification.
* `Cslib.Complexity.CountingFunction.sum_bits_restrict`: uniform restricted sums.

## References

* [OpenAI, *Existential--universal real sentences in the counting hierarchy*]
  [OpenAI2026CountingHierarchy], Section 2, Counting and summation lemma. Unary polynomial-time
  widths express its polynomially bounded computable index lengths; the summand's strict
  certificate supplies its polynomial encoded-length bound. Signed sums are included as well.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Recover a signed relativized count by recovering its two nonnegative counts and subtracting.
The two threshold oracles are combined at the same level. -/
theorem GapPWithOracle.mem_CountingFunction {α : Type} {enc : α ↪ List Bool}
    {A : Set (List Bool)} {a : ℕ} (D : Decoder enc) (hA : A ∈ CountingLevel a encBits)
    {f : α → ℤ} (hf : f ∈ GapPWithOracle A enc) :
    f ∈ CountingFunction (a + 1) enc encIntBin := by
  obtain ⟨f₁, h₁, f₂, h₂, hf⟩ := hf
  have h := CountingFunction.map (CountingFunction.prod
    (SharpPWithOracle.mem_CountingFunction D hA h₁)
    (SharpPWithOracle.mem_CountingFunction D hA h₂))
      (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)) (by fun_prop)
  simpa only [← hf] using h

namespace CountingFunction

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- Count all accepted bitstrings of a polynomial-time unary width using one uniform evaluator. -/
theorem count_bits (D : Decoder enc) {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => acceptCount V x (r x)) ∈ CountingFunction (a + 1) enc encNat := by
  obtain ⟨A, hA, hV⟩ := hV
  exact SharpPWithOracle.mem_CountingFunction D hA
    (mem_SharpPWithOracle_of_polyTime_length hV hr)

/-- Sum polynomial-bit nonnegative values over exponentially many short indices. The summand
certificate supplies a uniform output bound on all instance/index pairs. -/
theorem sum_bits (D : Decoder enc) {f : α × List Bool → ℕ} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => ∑ w : Fin (r x) → Bool, f (x, List.ofFn w)) ∈
      CountingFunction (a + 1) enc encNat := by
  obtain ⟨A, hA, hf⟩ := hf
  exact SharpPWithOracle.mem_CountingFunction D hA
    (SharpPWithOracle.sum_bits_mem (mem_SharpPWithOracle_of_polyTime hf) hr)

/-- Signed polynomial-bit summands have the same one-level summation cost. -/
theorem sum_bits_int (D : Decoder enc) {f : α × List Bool → ℤ} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encIntBin)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => ∑ w : Fin (r x) → Bool, f (x, List.ofFn w)) ∈
      CountingFunction (a + 1) enc encIntBin := by
  obtain ⟨A, hA, hf⟩ := hf
  exact GapPWithOracle.mem_CountingFunction D hA
    (GapPWithOracle.sum_bits_mem (mem_GapPWithOracle_of_polyTime hf) hr)

open Classical in
/-- Existential quantification over bitstrings of a polynomial-time unary width costs one level. -/
theorem exists_bits (D : Decoder enc) {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => decide (∃ w : List Bool, w.length = r x ∧ V (x, w) = true)) ∈
      CountingFunction (a + 1) enc encBool := by
  have h := map (count_bits D hV hr) (g := fun n : ℕ => decide (0 < n)) (by fun_prop)
  simpa only [acceptCount_pos_iff] using h

open Classical in
/-- Universal quantification counts rejecting indices and tests whether that count is zero. -/
theorem forall_bits (D : Decoder enc) {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => decide (∀ w : Fin (r x) → Bool, V (x, List.ofFn w) = true)) ∈
      CountingFunction (a + 1) enc encBool := by
  have hnot := map hV ComputableInPolyTime.bool_not
  have h := map (count_bits D hnot hr) (g := fun n : ℕ => decide (n = 0)) (by fun_prop)
  simpa only [acceptCount_eq_zero_iff, Bool.not_eq_false'] using h

/-- A same-level uniform restriction can mask summands by zero, with no extra counting level. -/
theorem sum_bits_restrict (D : Decoder enc) {f : α × List Bool → ℕ}
    {V : α × List Bool → Bool} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => ∑ w : Fin (r x) → Bool,
      if V (x, List.ofFn w) then f (x, List.ofFn w) else 0) ∈
      CountingFunction (a + 1) enc encNat :=
  sum_bits D (ite hV hf (of_polyTime (ComputableInPolyTime.const 0))) hr

/-- A uniform same-level restriction also preserves the signed summation bound. -/
theorem sum_bits_int_restrict (D : Decoder enc) {f : α × List Bool → ℤ}
    {V : α × List Bool → Bool} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encIntBin)
    (hV : V ∈ CountingFunction a (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => ∑ w : Fin (r x) → Bool,
      if V (x, List.ofFn w) then f (x, List.ofFn w) else 0) ∈
      CountingFunction (a + 1) enc encIntBin :=
  sum_bits_int D (ite hV hf (of_polyTime (ComputableInPolyTime.const 0))) hr

/-- Reduction of a short-index sum modulo a uniformly accessible short modulus has the same
level. Natural remainder is total, with n % 0 = n; positive moduli have the usual residue bound. -/
theorem sum_bits_mod (D : Decoder enc) {f : α × List Bool → ℕ} {r modulus : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encBits) encNat)
    (hr : ComputableInPolyTime r enc encUnary)
    (hm : modulus ∈ CountingFunction a enc encNat) :
    (fun x => (∑ w : Fin (r x) → Bool, f (x, List.ofFn w)) % modulus x) ∈
      CountingFunction (a + 1) enc encNat :=
  map (prod (sum_bits D hf hr) (mono (Nat.le_succ a) hm)) ComputableInPolyTime.binary_mod

end CountingFunction
end Cslib.Complexity
