/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Uniform

/-!
# Independent blocks of uniform bit lists

Reading a uniform list of `count * width` bits as fixed-width rows gives exactly `count`
independent uniform bit strings. This includes zero-width rows and zero rows. Conversely,
concatenating prefixes of independent uniform strings, for example of the values of a uniform
function at distinct inputs, gives a uniform list.

## Main results

* `Cslib.BitString.uniformList_ofList`: a uniform list gives a uniform finite bit string.
* `Cslib.BitString.uniformList_blocks`: fixed-width blocks are jointly uniform.
* `Cslib.BitString.uniformList_listRows`: the same law for the ordinary list-of-lists program.
* `Cslib.BitString.uniformList_map_listRow_equiv`: rows read at enumerated positions form a
  uniform function.
* `Cslib.BitString.uniformList_replaceRow`: replacing one row with an independent uniform row
  preserves uniformity.
* `Cslib.BitString.uniformList_map_listXor`,
  `Cslib.BitString.uniformList_map_listXor_length`,
  `Cslib.BitString.uniformList_map_zipWith_xor`,
  `Cslib.BitString.uniformList_map_take_zipWith_xor`: XOR with a fixed word preserves uniformity
  (both in `listXor m [y, r]` and direct `List.zipWith Bool.xor y r` forms).
* `Cslib.BitString.uniformOfFintype_map_flatten_take`,
  `Cslib.BitString.uniformOfFintype_map_readPrefixes`: prefixes of independent uniform strings,
  or of the values of a uniform function at distinct inputs, form a uniform word.

## References

Adapted from Probability/WordBits.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared block representation.
-/

public section

namespace Cslib.BitString

open Probability

/-- A uniform list gives exactly a uniform finite bit string. -/
theorem uniformList_ofList (n : ℕ) :
    (uniformList n).map (ofList n) = PMF.uniformOfFintype (BitString n) := by
  simp only [uniformList, PMF.map_comp, Function.comp_def, ofList_ofFn]
  exact PMF.map_id _

/-- Disjoint fixed-width blocks of a uniform list are jointly uniform. -/
theorem uniformList_blocks (count width : ℕ) :
    (uniformList (count * width)).map (fun word => block (ofList (count * width) word)) =
      PMF.uniformOfFintype (Fin count → BitString width) := by
  change (uniformList (count * width)).map (blocksEquiv ∘ ofList (count * width)) = _
  rw [← PMF.map_comp, uniformList_ofList]
  exact PMF.uniformOfFintype_map_equiv blocksEquiv

/-- Extracting fixed-width rows realizes the joint law of independent uniform seeds. -/
theorem uniformList_listRows (count width : ℕ) :
    (uniformList (count * width)).map (listRows count width) =
      (PMF.uniformOfFintype (Fin count → BitString width)).map
        (fun rows => List.ofFn (fun i => List.ofFn (rows i))) := by
  rw [← uniformList_blocks count width, PMF.map_comp]
  congr 1 with word : 1
  exact listRows_eq_ofFn count width word

/-- Reading the fixed-width rows of a uniform list at the positions given by an enumeration `e`
gives a uniform function. -/
theorem uniformList_map_listRow_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] {count : ℕ}
    (e : ι ≃ Fin count) (width : ℕ) :
    (uniformList (count * width)).map (fun word i => ofList width (listRow width (e i) word)) =
      PMF.uniformOfFintype (ι → BitString width) := by
  have h : (fun word i => ofList width (listRow width (e i) word)) =
      ((e.arrowCongr (Equiv.refl (BitString width))).symm : _ → _) ∘
        fun word => block (ofList (count * width) word) := by
    funext word i
    simp [listRow_eq_ofFn width (e i) word, Equiv.arrowCongr]
  rw [h, ← PMF.map_comp, uniformList_blocks]
  exact PMF.uniformOfFintype_map_equiv _

/-- XORing a uniform `m`-bit word with any word `r` preserves the uniform distribution; see
`uniformList_map_zipWith_xor` and `uniformList_map_take_zipWith_xor` for the direct
`List.zipWith Bool.xor y r` form alongside `listXor m [y, r]`. -/
theorem uniformList_map_listXor (m : ℕ) (r : List Bool) :
    (uniformList m).map (fun y => listXor m [y, r]) = uniformList m := by
  unfold uniformList
  rw [PMF.map_comp]
  have hfun : (fun y => listXor m [y, r]) ∘ List.ofFn =
      List.ofFn ∘ Equiv.addRight (ofList m r) := by
    funext x
    simp [listXor_pair]
  rw [hfun, ← PMF.map_comp, Probability.PMF.uniformOfFintype_map_equiv]

/-- Pointwise `List.zipWith Bool.xor` of a uniform `msg.length`-bit word with a fixed word `msg`
preserves `uniformList msg.length` (the direct `List.zipWith Bool.xor y r` counterpart to
`uniformList_map_listXor`'s `listXor m [y, r]`). -/
theorem uniformList_map_zipWith_xor (msg : List Bool) :
    (uniformList msg.length).map (fun pad => List.zipWith Bool.xor pad msg) =
      uniformList msg.length := by
  unfold uniformList
  rw [PMF.map_comp]
  have hfun : (fun pad => List.zipWith Bool.xor pad msg) ∘ List.ofFn =
      List.ofFn ∘ Equiv.addRight (ofList msg.length msg) := by
    funext x
    simp [ofFn_add, ofFn_ofList rfl]
  rw [hfun, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]

/-- Pointwise `List.zipWith Bool.xor` of `pad.take n` for a uniform `n`-bit word `pad` with an
`n`-bit word `msg` preserves `uniformList n`. -/
theorem uniformList_map_take_zipWith_xor {n : ℕ} {msg : List Bool} (hmsg : msg.length = n) :
    (uniformList n).map (fun pad => List.zipWith Bool.xor (pad.take n) msg) =
      uniformList n := by
  have hcongr :
      (uniformList n).map (fun pad => List.zipWith Bool.xor (pad.take n) msg) =
        (uniformList n).map (fun pad => List.zipWith Bool.xor pad msg) := by
    rw [PMF.map, PMF.map]
    refine PMF.bind_congr_on_support _ _ _ fun pad hpad => ?_
    dsimp only [Function.comp_def]
    rw [List.take_of_length_le (length_of_mem_support_uniformList hpad).le]
  rw [hcongr, ← hmsg, uniformList_map_zipWith_xor]

/-- XORing a uniform `m`-bit word `pad` with any word `r` at width `pad.length` preserves the
uniform distribution `uniformList m`. -/
theorem uniformList_map_listXor_length (m : ℕ) (r : List Bool) :
    (uniformList m).map (fun pad => listXor pad.length [pad, r]) = uniformList m := by
  have hcomp :
      (fun pad : List Bool => listXor pad.length [pad, r]) ∘ List.ofFn =
        (fun pad : List Bool => listXor m [pad, r]) ∘ (List.ofFn : BitString m → List Bool) := by
    funext x
    simp
  calc
    (uniformList m).map (fun pad => listXor pad.length [pad, r])
      = (PMF.uniformOfFintype (BitString m)).map
          ((fun pad : List Bool => listXor pad.length [pad, r]) ∘ List.ofFn) := by
        rw [uniformList, PMF.map_comp]
    _ = (PMF.uniformOfFintype (BitString m)).map
          ((fun pad : List Bool => listXor m [pad, r]) ∘ List.ofFn) := by
        rw [hcomp]
    _ = (uniformList m).map (fun pad => listXor m [pad, r]) := by
        rw [uniformList, PMF.map_comp]
    _ = uniformList m :=
        uniformList_map_listXor m r

/-- Replacing row `j < count` of a uniform `count * width`-bit string with an independent uniform
`width`-bit string preserves the uniform distribution `uniformList (count * width)`. -/
theorem uniformList_replaceRow (width count : ℕ) (j : Fin count) :
    (uniformList width).bind (fun x =>
      (uniformList (count * width)).map (replaceRow width count j.val x)) =
      uniformList (count * width) := by
  classical
  have hrep (x : BitString width) (Z : List Bool) :
      replaceRow width count j.val (List.ofFn x) Z =
        List.ofFn (blocksEquiv.symm
          (Function.update (block (ofList (count * width) Z)) j x)) := by
    rw [ofFn_blocksEquiv_symm, replaceRow, List.flatMap_def]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    by_cases hij : (⟨i, by simpa using hi⟩ : Fin count) = j
    · have hval : i = j.val := congrArg Fin.val hij
      simp [hval]
    · have hval : i ≠ j.val := fun h => hij (Fin.ext h)
      simp [hij, hval, listRow_eq_ofFn width ⟨i, by simpa using hi⟩ Z]
  have hblocks :
      (PMF.uniformOfFintype (Fin count → BitString width)).map
        (fun rows => List.ofFn (blocksEquiv.symm rows)) =
      uniformList (count * width) := by
    have h := congrArg (PMF.map List.ofFn)
      (PMF.uniformOfFintype_map_equiv
        (blocksEquiv : BitString (count * width) ≃ (Fin count → BitString width)).symm)
    simpa only [PMF.map_comp, Function.comp_def, uniformList] using h
  have hupd := congrArg
    (PMF.map (fun rows : Fin count → BitString width => List.ofFn (blocksEquiv.symm rows)))
    (PMF.uniformOfFintype_update (γ := BitString width) j)
  conv_rhs => rw [← hblocks, ← hupd]
  simp only [uniformList, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1 with x : 1
  have hZ := congrArg
    (PMF.map (fun rows : Fin count → BitString width =>
      List.ofFn (blocksEquiv.symm (Function.update rows j x))))
    (uniformList_blocks count width)
  simpa only [uniformList, PMF.map_comp, Function.comp_def, hrep] using hZ

/-- **Prefixes of independent uniform strings form a uniform word.** Keeping the first `ℓ i ≤ w`
bits of each of `m` independent uniform `w`-bit strings and concatenating them gives a uniform word
of `∑ ℓ i` bits. -/
theorem uniformOfFintype_map_flatten_take {m w : ℕ} (ℓ : Fin m → ℕ) (hℓ : ∀ i, ℓ i ≤ w) :
    (PMF.uniformOfFintype (Fin m → BitString w)).map
        (fun values => (List.ofFn fun i => (List.ofFn (values i)).take (ℓ i)).flatten) =
      uniformList (∑ i, ℓ i) := by
  induction m with
  | zero =>
    have h : (fun values : Fin 0 → BitString w =>
        (List.ofFn fun i => (List.ofFn (values i)).take (ℓ i)).flatten) = fun _ => [] := by
      funext values
      simp
    rw [h, Finset.univ_eq_empty, Finset.sum_empty, uniformList_zero]
    exact PMF.map_const _ _
  | succ m ih =>
    have hhead : (PMF.uniformOfFintype (BitString w)).map
        (fun value => (List.ofFn value).take (ℓ 0)) = uniformList (ℓ 0) := by
      rw [← uniformList_take (hℓ 0), uniformList, PMF.map_comp]
      rfl
    have htail := ih (fun i => ℓ i.succ) fun i => hℓ i.succ
    rw [← PMF.uniformOfFintype_map_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => BitString w)),
      PMF.map_comp, ← PMF.uniformOfFintype_prod, Fin.sum_univ_succ, uniformList_add, ← hhead,
      ← htail]
    simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, Fin.consEquiv,
      List.ofFn_succ]

/-- **A uniform function read at distinct inputs gives a uniform word.** Reading a uniform
function from `a`-bit to `w`-bit strings at the distinct inputs `x 0, …, x (m - 1)`, keeping the
first `ℓ i ≤ w` bits of the value at `x i` and concatenating them gives a uniform word of
`∑ ℓ i` bits. -/
theorem uniformOfFintype_map_readPrefixes {a w m : ℕ} (x : Fin m ↪ BitString a)
    (ℓ : Fin m → ℕ) (hℓ : ∀ i, ℓ i ≤ w) :
    (PMF.uniformOfFintype (BitString a → BitString w)).map
        (fun table => (List.ofFn fun i => (List.ofFn (table (x i))).take (ℓ i)).flatten) =
      uniformList (∑ i, ℓ i) := by
  rw [show (fun table : BitString a → BitString w =>
      (List.ofFn fun i => (List.ofFn (table (x i))).take (ℓ i)).flatten) =
      (fun values : Fin m → BitString w =>
        (List.ofFn fun i => (List.ofFn (values i)).take (ℓ i)).flatten) ∘
        (fun table i => table (x i)) from rfl, ← PMF.map_comp,
    PMF.uniformOfFintype_pi_map_comp_embedding x]
  exact uniformOfFintype_map_flatten_take ℓ hℓ

end Cslib.BitString
