/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Oracle
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Uniform counting closure relative to a language oracle

A single fixed oracle verifier can count outputs of deterministic polynomial-time oracle
functions and aggregate a uniform counting family over all words of a polynomial unary length.
The same padding and witness-splitting identities used by ordinary #P apply without changing
counts. The ordinary counting rules specialize these constructions to the empty oracle,
retaining the original proofs by Samuel Schlesinger. No characterization by nondeterministic
oracle machines is asserted.

## Main results

* `mem_SharpPWithOracle_of_polyTime`: binary natural oracle functions are relativized counts.
* `mem_GapPWithOracle_of_polyTime`: binary integer oracle functions are relativized gaps.
* `mem_SharpPWithOracle_of_polyTime_length`: unary witness lengths can be padded exactly.
* `SharpPWithOracle.comp_mem`, `GapPWithOracle.comp_mem`: ordinary polynomial preprocessing.
* `SharpPWithOracle.sum_bits_mem`, `GapPWithOracle.sum_bits_mem`: short-index aggregation.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-- Binary natural outputs of polynomial-time oracle computations are relativized #P functions.
The verifier compares the guessed binary value with the computed output; the output-length
bound supplies a polynomial witness width. -/
theorem mem_SharpPWithOracle_of_polyTime {f : α → ℕ}
    (hf : ComputableInPolyTimeWithOracle A f enc encNat) :
    f ∈ SharpPWithOracle A enc := by
  obtain ⟨p, hb⟩ := hf.polyBounded_length.exists_polynomial
  refine ⟨p, fun x => decide (BitString.binaryValue x.2 < f x.1), ?_, fun a => ?_⟩
  · exact (hf.preprocess (ComputableInPolyTime.fst enc encBits)).map_with
      (g := fun x value => decide (BitString.binaryValue x.2 < value)) (by fun_prop)
  · symm
    unfold acceptCount
    simp only [decide_eq_true_eq]
    apply BitString.card_filter_binaryValue_lt
    have hsize : (f a).size ≤ p.eval (enc a).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using hb a
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by lia) hsize)

/-- Binary integer outputs of polynomial-time oracle computations are relativized GapP functions.
Positive and negative parts are computed by the same fixed oracle. -/
theorem mem_GapPWithOracle_of_polyTime {f : α → ℤ}
    (hf : ComputableInPolyTimeWithOracle A f enc encIntBin) :
    f ∈ GapPWithOracle A enc := by
  have hp := mem_SharpPWithOracle_of_polyTime (hf.map ComputableInPolyTime.intBin_toNat)
  have hn := mem_SharpPWithOracle_of_polyTime
    (hf.map (g := fun value : ℤ => (0 - value).toNat) (by fun_prop))
  exact ⟨_, hp, _, hn, fun a => by simp only [zero_sub]; lia⟩

/-- A polynomial-time unary witness length can be padded without changing the relativized count.
The evaluator is uniform in the instance and the witness. -/
theorem mem_SharpPWithOracle_of_polyTime_length {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => acceptCount V a (r a)) ∈ SharpPWithOracle A enc := by
  obtain ⟨p, hle⟩ := hr.polyBounded.exists_polynomial
  exact ⟨p, padVerifier r V, computableInPolyTimeWithOracle_padVerifier hr hV, fun a =>
    (acceptCount_padVerifier_of_le r V (hle a)).symm⟩

/-- Ordinary polynomial-time preprocessing preserves the exact relativized count. -/
theorem SharpPWithOracle.comp_mem {β : Type} {encB : β ↪ List Bool}
    {f : β → ℕ} {g : α → β} (hf : f ∈ SharpPWithOracle A encB)
    (hg : ComputableInPolyTime g enc encB) :
    f ∘ g ∈ SharpPWithOracle A enc := by
  obtain ⟨q, W, hW, hWB⟩ := hf
  have h := mem_SharpPWithOracle_of_polyTime_length
    (V := fun x => W (g x.1, x.2))
    (r := fun a => q.eval (encB (g a)).length)
    (hW.preprocess (g := fun x : α × List Bool => (g x.1, x.2)) (by fun_prop))
    (by fun_prop)
  change (fun a => acceptCount W (g a) (q.eval (encB (g a)).length)) ∈
    SharpPWithOracle A enc at h
  simpa only [← hWB, Function.comp_def] using h

/-- Ordinary polynomial-time preprocessing preserves relativized GapP. -/
theorem GapPWithOracle.comp_mem {β : Type} {encB : β ↪ List Bool}
    {f : β → ℤ} {g : α → β} (hf : f ∈ GapPWithOracle A encB)
    (hg : ComputableInPolyTime g enc encB) :
    f ∘ g ∈ GapPWithOracle A enc := by
  obtain ⟨f₁, h₁, f₂, h₂, h⟩ := hf
  exact ⟨f₁ ∘ g, SharpPWithOracle.comp_mem h₁ hg,
    f₂ ∘ g, SharpPWithOracle.comp_mem h₂ hg, fun a => h (g a)⟩

/-- A relativized count has at most an exponential number of accepting witnesses. -/
theorem SharpPWithOracle.exists_le_two_pow {f : α → ℕ}
    (hf : f ∈ SharpPWithOracle A enc) :
    ∃ p : Polynomial ℕ, ∀ a, f a ≤ 2 ^ p.eval (enc a).length := by
  obtain ⟨p, V, hV, hf⟩ := hf
  exact ⟨p, fun a => (hf a).trans_le acceptCount_le_two_pow⟩

/-- Summing one uniform relativized #P family over all words of a polynomial-time unary length
preserves relativized #P. The index and the verifier certificate share one guessed word. -/
theorem SharpPWithOracle.sum_bits_mem {f : α × List Bool → ℕ} {r : α → ℕ}
    (hf : f ∈ SharpPWithOracle A (encPair enc encBits))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∑ w : Fin (r a) → Bool, f (a, List.ofFn w)) ∈ SharpPWithOracle A enc := by
  obtain ⟨p, V, hV, hf⟩ := hf
  let q : α → ℕ := fun a => p.eval (2 * (enc a).length + 1 + r a)
  let W : α × List Bool → Bool := fun x => V ((x.1, x.2.take (r x.1)), x.2.drop (r x.1))
  have hq : ComputableInPolyTime q enc encUnary := by dsimp [q]; fun_prop
  have hW : ComputableInPolyTimeWithOracle A W (encPair enc encBits) encBool :=
    hV.preprocess (g := fun x : α × List Bool =>
      ((x.1, x.2.take (r x.1)), x.2.drop (r x.1))) (by fun_prop)
  convert mem_SharpPWithOracle_of_polyTime_length hW
    (ComputableInPolyTime.unary_add.comp (hr.prod hq)) using 1
  ext a
  change _ = acceptCount W a (r a + q a)
  rw [acceptCount_add]
  apply Finset.sum_congr rfl
  intro w _
  rw [hf]
  simp only [length_encPair, encBits_apply, List.length_ofFn]
  simp only [acceptCount, W, List.take_left' List.length_ofFn,
    List.drop_left' List.length_ofFn, q]

/-- A uniform relativized GapP family may be summed over exponentially many short indices. -/
theorem GapPWithOracle.sum_bits_mem {g : α × List Bool → ℤ} {r : α → ℕ}
    (hg : g ∈ GapPWithOracle A (encPair enc encBits))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∑ w : Fin (r a) → Bool, g (a, List.ofFn w)) ∈ GapPWithOracle A enc := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  refine ⟨_, SharpPWithOracle.sum_bits_mem h₁ hr,
    _, SharpPWithOracle.sum_bits_mem h₂ hr, fun a => ?_⟩
  simp only [hg, Finset.sum_sub_distrib, Nat.cast_sum]

end Cslib.Complexity
