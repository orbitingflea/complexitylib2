/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP.Oracle
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.OutputLength
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Elementary closure of relativized majority verifiers

Deterministic oracle decision, polynomial-time preprocessing, reductions of the oracle, and
selection between a fixed pair of raw-word languages preserve the fixed-length relativized
majority class. The tagged union construction pads the random input and ignores the extra bits;
it does not use intersection closure of PP.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set (List Bool)}

/-- A deterministic oracle decider is a majority verifier with no random bits. -/
theorem PWithOracle_subset_PPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ PPWithOracle A enc := by
  rintro L ⟨f, hf, hL⟩
  refine ⟨0, fun x => f x.1, hf.preprocess (.fst enc encBits), fun a => ?_⟩
  rw [hL a]
  simp only [Polynomial.eval_zero, acceptCount_zero]
  cases f a <;> simp

/-- Ignoring a suffix of random bits preserves the strict-majority condition. -/
private theorem majority_take_iff {V : β × List Bool → Bool}
    {V' : α × List Bool → Bool} {a : α} {b : β} {k K : ℕ} (hk : k ≤ K)
    (hV : ∀ w, V' (a, w) = V (b, w.take k)) :
    (2 ^ K < 2 * acceptCount V' a K) ↔ (2 ^ k < 2 * acceptCount V b k) := by
  rw [acceptCount_eq_two_pow_mul_of_take hk hV, ← pow_sub_mul_pow 2 hk, mul_left_comm 2]
  exact Nat.mul_lt_mul_left (by positivity)

/-- Relativized PP is closed under polynomial-time many-one reductions. The verifier reads
only the prefix of its random input required by the reduced instance. -/
theorem PolyTimeReducible.mem_PPWithOracle {L : Set α} {L' : Set β}
    (h : PolyTimeReducible enc encB L L') (hL' : L' ∈ PPWithOracle A encB) :
    L ∈ PPWithOracle A enc := by
  obtain ⟨f, hf, hLL'⟩ := h
  obtain ⟨p, V, hV, hVL'⟩ := hL'
  obtain ⟨q, hpq⟩ := hf.exists_polynomial_eval_length_le p
  let W : α × List Bool → Bool := fun x =>
    V (f x.1, x.2.take (p.eval (encB (f x.1)).length))
  have hW : ComputableInPolyTimeWithOracle A W (encPair enc encBits) encBool :=
    hV.preprocess (g := fun x : α × List Bool =>
      (f x.1, x.2.take (p.eval (encB (f x.1)).length))) (by fun_prop)
  refine ⟨q, W, hW, fun a => ?_⟩
  rw [hLL' a, hVL' (f a)]
  exact (majority_take_iff (hpq a) (fun _ => rfl)).symm

/-- Reducing the oracle preserves relativized PP, including the uniform resource certificate
of its verifier. -/
theorem PolyTimeReducible.PPWithOracle_subset {A B : Set (List Bool)}
    (hAB : PolyTimeReducible encBits encBits A B) (enc : α ↪ List Bool) :
    PPWithOracle A enc ⊆ PPWithOracle B enc :=
  fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.of_polyTimeReducible hAB, hL⟩

/-- A leading Boolean tag chooses between two languages. The empty word takes the false branch
on the empty tail, so the definition is total on raw words. -/
@[expose] def taggedUnion (L₀ L₁ : Set (List Bool)) : Set (List Bool) :=
  {w | if w.headD false then w.tail ∈ L₁ else w.tail ∈ L₀}

/-- Two relativized PP languages with the same fixed oracle have a relativized PP tagged union.
A common polynomial random length is shortened to the length required by the selected branch. -/
theorem taggedUnion_mem_PPWithOracle {L₀ L₁ : Set (List Bool)}
    (h₀ : L₀ ∈ PPWithOracle A encBits) (h₁ : L₁ ∈ PPWithOracle A encBits) :
    taggedUnion L₀ L₁ ∈ PPWithOracle A encBits := by
  obtain ⟨p₀, V₀, hV₀, h₀⟩ := h₀
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := h₁
  let W₀ : List Bool × List Bool → Bool := fun x =>
    V₀ (x.1.tail, x.2.take (p₀.eval x.1.tail.length))
  let W₁ : List Bool × List Bool → Bool := fun x =>
    V₁ (x.1.tail, x.2.take (p₁.eval x.1.tail.length))
  let W : List Bool × List Bool → Bool := fun x =>
    if x.1.headD false then W₁ x else W₀ x
  have hW₀ : ComputableInPolyTimeWithOracle A W₀ (encPair encBits encBits) encBool :=
    hV₀.preprocess (g := fun x : List Bool × List Bool =>
      (x.1.tail, x.2.take (p₀.eval x.1.tail.length))) (by fun_prop)
  have hW₁ : ComputableInPolyTimeWithOracle A W₁ (encPair encBits encBits) encBool :=
    hV₁.preprocess (g := fun x : List Bool × List Bool =>
      (x.1.tail, x.2.take (p₁.eval x.1.tail.length))) (by fun_prop)
  have hselect : ComputableInPolyTime
      (fun pair : (List Bool × List Bool) × (Bool × Bool) =>
        if pair.1.1.headD false then pair.2.2 else pair.2.1)
      (encPair (encPair encBits encBits) (encPair encBool encBool)) encBool :=
    ComputableInPolyTime.ite'
      (show ComputableInPolyTime (fun pair : (List Bool × List Bool) × (Bool × Bool) =>
        pair.1.1.headD false)
        (encPair (encPair encBits encBits) (encPair encBool encBool)) encBool by fun_prop)
      (by fun_prop) (by fun_prop)
  have hW : ComputableInPolyTimeWithOracle A W (encPair encBits encBits) encBool :=
    (hW₀.prod hW₁).map_with (output := encBool)
      (g := fun x b => if x.1.headD false then b.2 else b.1) hselect
  refine ⟨p₀ + p₁, W, hW, fun w => ?_⟩
  have htail : w.tail.length ≤ w.length := by simp only [List.length_tail]; omega
  have hp₀ : p₀.eval w.tail.length ≤ (p₀ + p₁).eval (encBits w).length := by
    simp only [encBits_apply, Polynomial.eval_add]
    exact (Polynomial.eval_mono p₀ htail).trans (Nat.le_add_right _ _)
  have hp₁ : p₁.eval w.tail.length ≤ (p₀ + p₁).eval (encBits w).length := by
    simp only [encBits_apply, Polynomial.eval_add]
    exact (Polynomial.eval_mono p₁ htail).trans (Nat.le_add_left _ _)
  cases ht : w.headD false
  · have hc : acceptCount W w ((p₀ + p₁).eval (encBits w).length) =
        acceptCount W₀ w ((p₀ + p₁).eval (encBits w).length) :=
      acceptCount_congr (fun r => by simp only [W, ht, Bool.false_eq_true, ↓reduceIte]) _
    change (if w.headD false then w.tail ∈ L₁ else w.tail ∈ L₀) ↔ _
    simp only [ht, Bool.false_eq_true, ↓reduceIte]
    rw [hc, h₀ w.tail]
    simp only [encBits_apply]
    exact (majority_take_iff hp₀ (fun _ => rfl)).symm
  · have hc : acceptCount W w ((p₀ + p₁).eval (encBits w).length) =
        acceptCount W₁ w ((p₀ + p₁).eval (encBits w).length) :=
      acceptCount_congr (fun r => by simp only [W, ht, ↓reduceIte]) _
    change (if w.headD false then w.tail ∈ L₁ else w.tail ∈ L₀) ↔ _
    simp only [ht, ↓reduceIte]
    rw [hc, h₁ w.tail]
    simp only [encBits_apply]
    exact (majority_take_iff hp₁ (fun _ => rfl)).symm

end Cslib.Complexity
