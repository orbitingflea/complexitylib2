/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Oracle.Closure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.Classes.Oracle.BinarySearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Recovering relativized counts by majority queries

Compare a relativized count with a binary threshold using the positive-gap characterization,
then recover the entire count with the existing certified binary search. Threshold requests
are total on raw words through a supplied polynomial-time decoder. Thus an arbitrary encoding
is never assumed to have efficient range recognition.

## Main results

* `Cslib.Complexity.setOf_le_mem_PPWithOracle`: comparison with a relativized count.
* `Cslib.Complexity.SharpPWithOracle.mem_CountingFunction`: a count relative to C_a P is in
  F_(a+1), for inputs with a certified total decoder.
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-- Comparison with a relativized count is strict-majority decidable: the gap is f(x)+1-k. -/
theorem setOf_le_mem_PPWithOracle {f : α → ℕ} (hf : f ∈ SharpPWithOracle A enc) :
    {x : α × ℕ | x.2 ≤ f x.1} ∈ PPWithOracle A (encPair enc encNat) := by
  have hfst := SharpPWithOracle.comp_mem hf (ComputableInPolyTime.fst enc encNat)
  have hone : (fun _ : α × ℕ => 1) ∈ SharpPWithOracle A (encPair enc encNat) :=
    mem_SharpPWithOracle_of_polyTime
      ((ComputableInPolyTime.const 1).computableInPolyTimeWithOracle A)
  refine mem_PPWithOracle_iff_exists_GapPWithOracle.mpr
    ⟨fun x => ((f x.1 + 1 : ℕ) : ℤ) - (x.2 : ℤ),
      ⟨_, SharpPWithOracle.add_mem hfst hone, _,
        mem_SharpPWithOracle_of_polyTime
          ((ComputableInPolyTime.snd enc encNat).computableInPolyTimeWithOracle A),
        fun _ => rfl⟩, fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, sub_pos, Nat.cast_lt]
  omega

/-- A relativized count can be recovered one level above its fixed oracle. The decoder makes
the threshold oracle a language on all raw words; its values off valid codes are fixed by the
decoder. The search uses one more bit than the witness bound, including the endpoint 2^b. -/
theorem SharpPWithOracle.mem_CountingFunction {a : ℕ} (D : Decoder enc)
    (hA : A ∈ CountingLevel a encBits) {f : α → ℕ} (hf : f ∈ SharpPWithOracle A enc) :
    f ∈ CountingFunction (a + 1) enc encNat := by
  obtain ⟨p, hp⟩ := SharpPWithOracle.exists_le_two_pow hf
  let E := Decoder.pair D Decoder.nat
  let B : Set (List Bool) := {q | (E.decode q).2 ≤ f (E.decode q).1}
  have hB : B ∈ PPWithOracle A encBits :=
    (show PolyTimeReducible encBits (encPair enc encNat) B
      {x : α × ℕ | x.2 ≤ f x.1} from
        ⟨E.decode, E.computableInPolyTime, fun _ => Iff.rfl⟩).mem_PPWithOracle
          (setOf_le_mem_PPWithOracle hf)
  refine ⟨B, ⟨A, hA, hB⟩,
    fun x => BinarySearch.search (enc x) (p.eval (enc x).length + 1), ?_, fun x => ?_⟩
  · exact BinarySearch.isOraclePPTOn_search
      (ComputableInPolyTime.encoding_comp ComputableInPolyTime.id') (by fun_prop)
  · apply BinarySearch.interpret_id_search
    · intro k
      change (E.decode (encPair enc encNat (x, k))).2 ≤
        f (E.decode (encPair enc encNat (x, k))).1 ↔ _
      rw [E.decode_enc]
    · exact (hp x).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))

end Cslib.Complexity
