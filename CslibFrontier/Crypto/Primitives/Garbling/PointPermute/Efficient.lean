/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Point-and-permute garbling is efficient

`PointPermute.scheme family` of `CslibFrontier.Crypto.Primitives.Garbling.PointPermute` is an
efficient garbling scheme (`Scheme.IsEfficient`) whenever the word family `family` is computed in
polynomial time, as `PseudorandomFunction.polyTime` provides: `PointPermute.scheme_isEfficient`.
Circuits are encoded by `encValidCircuit` (`n`, `m` in unary, wire numbers in binary). Privacy of
the scheme, with a polynomial-time simulator and certified reductions, is open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293).

The garbler writes each gate's block from the gate list of the encoded circuit; wire numbers read
from that list are capped at the length of the coins, which changes nothing since a wire beyond
the coins reads the all-zero key and permutation bit either way. The evaluator is a fold over the
gates whose state grows by one label per gate, and the semantics `ev` a fold over the gates whose
state grows by one bit per gate. The certificates for the keyed function on words, tweaks, keys,
permutation bits and labels are stated compositionally for reuse.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.scheme_isEfficient`: point-and-permute garbling is
  efficient.
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Turing.MultiTapeTM

variable {family : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
    (encPair encBits encBits) encBits)

include hf in
/-- The keyed function on words is computed in polynomial time. -/
theorem labelWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    {key t : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hkey : ComputableInPolyTime key encIn encBits) (ht : ComputableInPolyTime t encIn encBits) :
    ComputableInPolyTime (fun a => labelWord family (k a) (key a) (t a)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      labelWord family p.1 p.2.1 p.2.2) (encPair encUnary (encPair encBits encBits)) encBits := by
    polytime [labelWord]
  exact h.comp (hk.prod (hkey.prod ht))

/-- Tweaks are computed in polynomial time. -/
theorem tweak_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g i a : γ → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun x => tweak (k x) (g x) (i x) (a x)) encIn encBits := by
  unfold tweak
  polytime

/-- The width of wire numbers is computed in polynomial time. -/
theorem wireWidth_polyTime {γ : Type} {encIn : γ ↪ List Bool} {n q : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hq : ComputableInPolyTime q encIn encUnary) :
    ComputableInPolyTime (fun a => wireWidth (n a) (q a)) encIn encUnary :=
  ComputableInPolyTime.binary_size.comp
    (ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime.comp (by fun_prop))

/-- Permutation bits are read in polynomial time. -/
theorem permOf_polyTime {γ : Type} {encIn : γ ↪ List Bool} {coins : γ → List Bool} {v : γ → ℕ}
    (hcoins : ComputableInPolyTime coins encIn encBits)
      (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun a => permOf (coins a) (v a)) encIn encBool := by
  unfold permOf
  polytime

/-- Keys are read in polynomial time. -/
theorem keyOf_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k wires v : γ → ℕ}
    {coins : γ → List Bool} {c : γ → Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hwires : ComputableInPolyTime wires encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits) (hv : ComputableInPolyTime v encIn encUnary)
    (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun a => keyOf (k a) (wires a) (coins a) (v a) (c a)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × ℕ × Bool =>
      keyOf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encBits
        (encPair encUnary encBool)))) encBits := by
    polytime [keyOf, BitString.listRow]
  exact h.comp (hk.prod (hwires.prod (hcoins.prod (hv.prod hc))))

/-- Labels are read in polynomial time. -/
theorem labelOf_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k wires v : γ → ℕ}
    {coins : γ → List Bool} {c : γ → Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hwires : ComputableInPolyTime wires encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits) (hv : ComputableInPolyTime v encIn encUnary)
    (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun a => labelOf (k a) (wires a) (coins a) (v a) (c a)) encIn encBits :=
  ComputableInPolyTime.bitsAppend (keyOf_polyTime hk hwires hcoins hv hc) (by polytime)

attribute [local fun_prop] labelWord_polyTime tweak_polyTime wireWidth_polyTime permOf_polyTime
  keyOf_polyTime labelOf_polyTime

/-- `De` runs in polynomial time. -/
private theorem decodeWord_polyTime :
    ComputableInPolyTime (fun (d, Y) => decodeWord d Y) (encPair encBits encBits)
      (encOption encBits) := by
  polytime [decodeWord]

/-- `En` runs in polynomial time. -/
private theorem encodeWord_polyTime :
    ComputableInPolyTime (fun (e, x) => encodeWord e x) (encPair encBits encBits) encBits := by
  polytime [encodeWord, BitString.listRow]

include hf in
private theorem evalGate_step :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × List Bool) × List (List Bool)) × ℕ =>
        evalGate family p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encPair encUnary encBits)) (encList encBits)) encUnary)
      (encList encBits) := by
  polytime [evalGate]

private theorem length_evalGate_le (k w : ℕ) (body : List Bool) (labels : List (List Bool))
    (g : ℕ) : (encList encBits (evalGate family k w body labels g)).length ≤
      (encList encBits labels).length + (2 * (k + 2) + 1) := by
  simp only [evalGate, length_encList, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, encBits_apply]
  rw [List.length_zipWith, BitString.length_listRow]
  omega

include hf in
/-- `Ev` runs in polynomial time. -/
private theorem evalWord_polyTime :
    ComputableInPolyTime (fun (F, X) => evalWord family F X) (encPair encBits encBits)
      encBits := by
  have hdec : ComputableInPolyTime (fun p : List Bool × List Bool => fnDecoder.decode p.1)
      (encPair encBits encBits) encFn :=
    fnDecoder.computableInPolyTime.comp (ComputableInPolyTime.fst _ _)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary (encPair encUnary encBits)) (encL := encList encUnary)
    (encB := encList encBits) (encA := encUnary) (encIn := encPair encBits encBits)
    (step := fun par labels g => evalGate family par.1 par.2.1 par.2.2 labels g)
    (par := fun p : List Bool × List Bool => ((fnDecoder.decode p.1).1.1,
      wireWidth (fnDecoder.decode p.1).1.2.1 (fnDecoder.decode p.1).1.2.2.2,
        (fnDecoder.decode p.1).2))
    (list := fun p => List.range (fnDecoder.decode p.1).1.2.2.2)
    (init := fun p => BitString.listRows (fnDecoder.decode p.1).1.2.1
      ((fnDecoder.decode p.1).1.1 + 2) p.2)
    (by polytime) (by polytime)
    (by polytime [BitString.listRows, BitString.listRow])
    (evalGate_step hf) (growth := fun p => 2 * ((fnDecoder.decode p.1).1.1 + 2) + 1)
    (by
      refine (hdec.polyBounded_length.add (PolyBounded.const 5)).mono fun p => ?_
      simp only [encFn, encHeader, length_encPair, encUnary_apply, List.length_replicate]
      omega)
    (fun p labels g _ => length_evalGate_le _ _ _ _ _)
  have heq : (fun (F, X) => evalWord family F X) = fun p : List Bool × List Bool =>
      ((List.range (fnDecoder.decode p.1).1.2.2.2).foldl
        (fun labels g => evalGate family (fnDecoder.decode p.1).1.1
          (wireWidth (fnDecoder.decode p.1).1.2.1 (fnDecoder.decode p.1).1.2.2.2)
          (fnDecoder.decode p.1).2 labels g)
        (BitString.listRows (fnDecoder.decode p.1).1.2.1 ((fnDecoder.decode p.1).1.1 + 2)
          p.2)).drop ((fnDecoder.decode p.1).1.2.1 + (fnDecoder.decode p.1).1.2.2.2 -
            (fnDecoder.decode p.1).1.2.2.1) |>.flatten := rfl
  rw [heq]
  have hc : ComputableInPolyTime (fun p : List Bool × List Bool =>
      (fnDecoder.decode p.1).1.2.1 + (fnDecoder.decode p.1).1.2.2.2 -
        (fnDecoder.decode p.1).1.2.2.1) (encPair encBits encBits) encUnary := by
    polytime
  have hfin : ComputableInPolyTime (fun p : List (List Bool) × ℕ => (p.1.drop p.2).flatten)
      (encPair (encList encBits) encUnary) encBits :=
    (ComputableTidilyInPolyTime.bitsFlatten (ComputableTidilyInPolyTime.listDropWithInput
      (ComputableTidilyInPolyTime.fst _ _)
        (ComputableTidilyInPolyTime.snd _ _))).computableInPolyTime
  exact hfin.comp (hfold.prod hc)

/-! ### Garbling -/

/-- The truth table of a gate read from its four bits. -/
private theorem getD_table (G : Bool → Bool → Bool) (x y : Bool) :
    [G false false, G false true, G true false, G true true].getD
      ((if x then 2 else 0) + (if y then 1 else 0)) false = G x y := by
  cases x <;> cases y <;> rfl

/-- Row `i` of gate `g` from the gate's data: argument wires `A`, `B` and truth table `t`. -/
private def rowData (k n q : ℕ) (coins : List Bool) (A B : ℕ) (t : List Bool) (g i : ℕ) :
    List Bool :=
  let bit := t.getD ((if i.testBit 1 ^^ permOf coins (A - 1) then 2 else 0) +
    (if i.testBit 0 ^^ permOf coins (B - 1) then 1 else 0)) false
  List.zipWith xor (labelOf k (n + q) coins (n + g) (bit ^^ permOf coins (n + g)))
    (List.zipWith xor (labelWord family k (keyOf k (n + q) coins (A - 1) (i.testBit 1))
        (tweak k g i 0))
      (labelWord family k (keyOf k (n + q) coins (B - 1) (i.testBit 0)) (tweak k g i 1)))

/-- The body of the garbled function from the gate list. -/
private def bodyData (k n q : ℕ) (gates : List (ℕ × ℕ × List Bool)) (coins : List Bool) :
    List Bool :=
  ((List.range q).map fun g =>
    BitString.lowBits (wireWidth n q) (gates.getD g (0, 0, [])).1 ++
      BitString.lowBits (wireWidth n q) (gates.getD g (0, 0, [])).2.1 ++
      ((List.range 4).map fun i => rowData (family := family) k n q coins
        (gates.getD g (0, 0, [])).1 (gates.getD g (0, 0, [])).2.1
        (gates.getD g (0, 0, [])).2.2 g i).flatten).flatten

private theorem fnWord_eq (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    fnWord family k f coins =
      encFn ((k, f.n, f.m, f.gateList.length),
        bodyData (family := family) k f.n f.gateList.length f.gateList coins) := by
  simp only [fnWord, bodyData, ConventionalCircuit.length_gateList]
  congr 3
  apply List.ext_getElem (by simp)
  intro g h₁ h₂
  have hg : g < f.q := by simpa using h₁
  have hgate : f.gateList.getD g (0, 0, []) = (f.A ⟨g, hg⟩, f.B ⟨g, hg⟩,
      [f.G ⟨g, hg⟩ false false, f.G ⟨g, hg⟩ false true, f.G ⟨g, hg⟩ true false,
        f.G ⟨g, hg⟩ true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD, hg]
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, hgate]
  congr 2
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, rowWord, rowData, getD_table]

/-- A wire number beyond the coins reads the same permutation bit as the length of the coins. -/
private theorem permOf_min (coins : List Bool) (v : ℕ) :
    permOf coins (min coins.length v) = permOf coins v := by
  rcases le_total coins.length v with h | h
  · simp [permOf, min_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  · rw [min_eq_right h]

/-- A wire number beyond the coins reads the same key as the length of the coins. -/
private theorem keyOf_min (k wires : ℕ) (coins : List Bool) (v : ℕ) (c : Bool) :
    keyOf k wires coins (min coins.length v) c = keyOf k wires coins v c := by
  rcases le_total coins.length v with h | h
  · rw [min_eq_left h]
    have hbeyond (u : ℕ) (hu : coins.length ≤ u) : keyOf k wires coins u c =
        List.replicate (k + 1) false := by
      simp only [keyOf, BitString.listRow]
      rw [List.drop_eq_nil_of_le (by simp; split <;> nlinarith), List.nil_append,
        List.take_of_length_le (by simp)]
    rw [hbeyond _ le_rfl, hbeyond _ h]
  · rw [min_eq_right h]

/-- Row `i` of gate `g`, reading the 0-indexed argument wires `a` and `b`. -/
private def rowCapped (k n q : ℕ) (coins : List Bool) (a b : ℕ) (t : List Bool) (g i : ℕ) :
    List Bool :=
  let bit := t.getD ((if i.testBit 1 ^^ permOf coins a then 2 else 0) +
    (if i.testBit 0 ^^ permOf coins b then 1 else 0)) false
  List.zipWith xor (labelOf k (n + q) coins (n + g) (bit ^^ permOf coins (n + g)))
    (List.zipWith xor (labelWord family k (keyOf k (n + q) coins a (i.testBit 1))
        (tweak k g i 0))
      (labelWord family k (keyOf k (n + q) coins b (i.testBit 0)) (tweak k g i 1)))

private theorem rowData_eq (k n q : ℕ) (coins : List Bool) (A B : ℕ) (t : List Bool) (g i : ℕ) :
    rowData (family := family) k n q coins A B t g i =
      rowCapped (family := family) k n q coins (min (coins.length + 1) A - 1)
        (min (coins.length + 1) B - 1) t g i := by
  have hcap (V : ℕ) : min (coins.length + 1) V - 1 = min coins.length (V - 1) := by omega
  simp only [rowData, rowCapped, hcap, permOf_min, keyOf_min]

/-- The input `(k, n, q, gates, coins)` of the garbler's body. -/
private abbrev encBodyInput : (ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary
    (encPair (encList (encPair encNat (encPair encNat encBits))) encBits)))

include hf in
private theorem rowCapped_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q a b g i : γ → ℕ}
    {coins t : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary) (hq : ComputableInPolyTime q encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => rowCapped (family := family) (k x) (n x) (q x) (coins x) (a x)
      (b x) (t x) (g x) (i x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List Bool) × (ℕ × ℕ × List Bool) × ℕ × ℕ =>
        rowCapped (family := family) p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1.1 p.2.1.2.1
          p.2.1.2.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary encBits)))
        (encPair (encPair encUnary (encPair encUnary encBits)) (encPair encUnary encUnary)))
      encBits := by
    polytime [rowCapped, labelOf]
  exact h.comp ((hk.prod (hn.prod (hq.prod hcoins))).prod ((ha.prod (hb.prod ht)).prod
    (hg.prod hi)))

attribute [local fun_prop] rowCapped_polyTime

/-- The four rows of gate `g`, reading the 0-indexed argument wires `a` and `b`. -/
private def rowsBlock (k n q : ℕ) (coins : List Bool) (a b : ℕ) (t : List Bool) (g : ℕ) :
    List Bool :=
  ((List.range 4).map fun i => rowCapped (family := family) k n q coins a b t g i).flatten

include hf in
private theorem rowsBlock_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q a b g : γ → ℕ}
    {coins t : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary) (hq : ComputableInPolyTime q encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime (fun x => rowsBlock (family := family) (k x) (n x) (q x) (coins x) (a x)
      (b x) (t x) (g x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List Bool) × (ℕ × ℕ × List Bool) × ℕ =>
        rowsBlock (family := family) p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1.1 p.2.1.2.1
          p.2.1.2.2 p.2.2)
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary encBits)))
        (encPair (encPair encUnary (encPair encUnary encBits)) encUnary)) encBits := by
    polytime [rowsBlock]
  exact h.comp ((hk.prod (hn.prod (hq.prod hcoins))).prod ((ha.prod (hb.prod ht)).prod hg))

attribute [local fun_prop] rowsBlock_polyTime

/-- Gate `g` of the garbler's body, with capped wire numbers. -/
private def gateBlock (x : ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) (g : ℕ) :
    List Bool :=
  BitString.lowBits (wireWidth x.2.1 x.2.2.1) (x.2.2.2.1.getD g (0, 0, [])).1 ++
    BitString.lowBits (wireWidth x.2.1 x.2.2.1) (x.2.2.2.1.getD g (0, 0, [])).2.1 ++
    rowsBlock (family := family) x.1 x.2.1 x.2.2.1 x.2.2.2.2
      (min (x.2.2.2.2.length + 1) (x.2.2.2.1.getD g (0, 0, [])).1 - 1)
      (min (x.2.2.2.2.length + 1) (x.2.2.2.1.getD g (0, 0, [])).2.1 - 1)
      (x.2.2.2.1.getD g (0, 0, [])).2.2 g

include hf in
private theorem gateBlock_polyTime :
    ComputableInPolyTime (fun p => gateBlock (family := family) p.1 p.2)
      (encPair encBodyInput encUnary) encBits := by
  have hgate : ComputableInPolyTime
      (fun p : (ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) × ℕ =>
        p.1.2.2.2.1.getD p.2 (0, 0, [])) (encPair encBodyInput encUnary)
      (encPair encNat (encPair encNat encBits)) := by
    polytime
  have hA := hgate.fst'
  have hB := hgate.snd'.fst'
  have ht := hgate.snd'.snd'
  have hw : ComputableInPolyTime
      (fun p : (ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) × ℕ =>
        wireWidth p.1.2.1 p.1.2.2.1) (encPair encBodyInput encUnary) encUnary := by
    polytime
  have hcap (V : (ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) × ℕ → ℕ)
      (hV : ComputableInPolyTime V (encPair encBodyInput encUnary) encNat) :
      ComputableInPolyTime (fun p => min (p.1.2.2.2.2.length + 1) (V p) - 1)
        (encPair encBodyInput encUnary) encUnary := by
    polytime
  unfold gateBlock
  refine ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend ?_ ?_)
    (rowsBlock_polyTime hf (by polytime) (by polytime) (by polytime) (by polytime)
      (hcap _ hA) (hcap _ hB) ht (by polytime))
  · polytime
  · polytime

include hf in
private theorem bodyData_polyTime :
    ComputableInPolyTime (fun (k, n, q, gates, coins) => bodyData
      (family := family) k n q gates coins)
      encBodyInput encBits := by
  have hblock := gateBlock_polyTime hf
  have heq : (fun (x : ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) =>
      bodyData (family := family) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) =
      fun x => ((List.range x.2.2.1).map (gateBlock (family := family) x)).flatten := by
    funext x
    simp only [bodyData, rowData_eq]
    rfl
  refine (show ComputableInPolyTime (fun (x : ℕ × ℕ × ℕ × List (ℕ × ℕ × List Bool) × List Bool) =>
      bodyData (family := family) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) encBodyInput encBits
    from ?_)
  rw [heq]
  polytime


/-- The input `(1^k, f, r)` of the garbler. -/
private abbrev encGbInput : (ℕ × ValidCircuit × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encValidCircuit encBits)

private theorem data_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (x.2.1.1.n, x.2.1.1.m, x.2.1.1.gateList)) encGbInput encCircuitData :=
  circuitData_polyTime.comp (ComputableInPolyTime.snd _ _).fst'

private theorem q_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.gateList.length)
      encGbInput encUnary := by
  have hg : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.gateList)
      encGbInput (encList (encPair encNat (encPair encNat encBits))) := data_polyTime.snd'.snd'
  exact (ComputableTidilyInPolyTime.length_list _).computableInPolyTime.comp hg

private theorem q'_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.q) encGbInput encUnary :=
  by simpa only [ConventionalCircuit.length_gateList] using q_polyTime

private theorem n_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.n) encGbInput encUnary :=
  data_polyTime.fst'

private theorem m_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.m) encGbInput encUnary :=
  data_polyTime.snd'.fst'

include hf in
private theorem fnWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => fnWord family x.1 x.2.1.1 x.2.2)
      encGbInput encBits := by
  have hd := data_polyTime
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hg := hd.snd'.snd'
  have hbody := (bodyData_polyTime hf).comp ((ComputableInPolyTime.fst _ _).prod
    (hn.prod (q_polyTime.prod (hg.prod (ComputableInPolyTime.snd _ _).snd'))))
  have hhead : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (x.1, x.2.1.1.n, x.2.1.1.m, x.2.1.1.gateList.length)) encGbInput encHeader :=
    (ComputableInPolyTime.fst _ _).prod (hn.prod (hm.prod q_polyTime))
  have henc : ComputableInPolyTime (fun y : (ℕ × ℕ × ℕ × ℕ) × List Bool => encFn y) encFn
      encBits := .of_eq fun _ => rfl
  simp only [fnWord_eq]
  exact henc.comp (hhead.prod hbody)

private theorem encInfoWord_eq (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    encInfoWord k f coins = ((List.range (2 * f.n)).map fun j =>
      labelOf k (f.n + f.gateList.length) coins (j / 2) (j.testBit 0 ^^ permOf coins
        (j / 2))).flatten := by
  rw [encInfoWord, ConventionalCircuit.length_gateList, List.map_range_eq_ofFn]

private theorem decInfoWord_eq (f : ConventionalCircuit) (coins : List Bool) :
    decInfoWord f coins = (List.range f.m).map fun o =>
      permOf coins (f.n + f.gateList.length - f.m + o) := by
  rw [decInfoWord, ConventionalCircuit.length_gateList, List.map_range_eq_ofFn]

private theorem encRange_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List Bool =>
      ((List.range (2 * p.2.1)).map fun j => labelOf p.1 (p.2.1 + p.2.2.1) p.2.2.2 (j / 2)
        (j.testBit 0 ^^ permOf p.2.2.2 (j / 2))).flatten)
      (encPair encUnary (encPair encUnary (encPair encUnary encBits))) encBits := by
  polytime

private theorem decRange_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List Bool =>
      (List.range p.2.2.1).map fun o => permOf p.2.2.2 (p.1 + p.2.1 - p.2.2.1 + o))
      (encPair encUnary (encPair encUnary (encPair encUnary encBits))) encBits := by
  polytime

include hf in
/-- The garbler runs in polynomial time. -/
private theorem gb_polyTime :
    ComputableInPolyTime (fun (k, f, coins) => (scheme family).gb k f coins)
      (encPair encUnary (encPair encValidCircuit encBits)) Scheme.encGarbled := by
  have hcoins := (ComputableInPolyTime.snd (encUnary) (encPair encValidCircuit encBits)).snd'
  have hq' := q'_polyTime
  have hn' := n_polyTime
  have hm' := m_polyTime
  have he₀ := encRange_polyTime
  have he : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      encInfoWord x.1 x.2.1.1 x.2.2) encGbInput encBits := by
    simp only [encInfoWord_eq, ConventionalCircuit.length_gateList]
    exact he₀.comp ((ComputableInPolyTime.fst _ _).prod (hn'.prod (hq'.prod hcoins)))
  have hd₀ := decRange_polyTime
  have hdec : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      decInfoWord x.2.1.1 x.2.2) encGbInput encBits := by
    simp only [decInfoWord_eq, ConventionalCircuit.length_gateList]
    exact hd₀.comp (hn'.prod (hq'.prod (hm'.prod hcoins)))
  have hcomp := Scheme.encGarbled_mk_polyTime (fnWord_polyTime hf) he hdec
  have heq : (fun x : ℕ × ValidCircuit × List Bool => (⟨fnWord family x.1 x.2.1.1 x.2.2,
      encInfoWord x.1 x.2.1.1 x.2.2, decInfoWord x.2.1.1 x.2.2⟩ : Scheme.Garbled)) =
      fun (k, f, coins) => (scheme family).gb k f coins := by
    funext x
    obtain ⟨k, f, coins⟩ := x
    simp only [scheme]
  exact heq ▸ hcomp

/-! ### Coins and semantics -/

/-- The number of coins is computed in polynomial time. -/
private theorem coins_polyTime :
    ComputableInPolyTime (fun (k, f) => (scheme family).coins k f)
      (encPair encUnary encValidCircuit) encUnary := by
  have hd : ComputableInPolyTime (fun x : ℕ × ValidCircuit =>
      (x.2.1.n, x.2.1.m, x.2.1.gateList)) (encPair encUnary encValidCircuit) encCircuitData :=
    circuitData_polyTime.comp (ComputableInPolyTime.snd _ _)
  have hn := hd.fst'
  have hg : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.gateList)
      (encPair encUnary encValidCircuit) (encList (encPair encNat (encPair encNat encBits))) :=
    hd.snd'.snd'
  have hq : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.q)
      (encPair encUnary encValidCircuit) encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableTidilyInPolyTime.length_list _).computableInPolyTime.comp hg
  have hn' : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.n)
      (encPair encUnary encValidCircuit) encUnary := hn
  have heq : (fun (k, f) => (scheme family).coins k f) = fun x : ℕ × ValidCircuit =>
      (x.2.1.n + x.2.1.q) * (2 * (x.1 + 1) + 1) := by
    funext x
    obtain ⟨k, f⟩ := x
    simp [scheme, Scheme.coins]
  rw [heq]
  polytime

/-- One gate of the plaintext evaluation, from the gate's data. -/
private def wireStep (ws : List Bool) (gate : ℕ × ℕ × List Bool) : List Bool :=
  ws ++ [gate.2.2.getD ((if ws.getD (min (ws.length + 1) gate.1 - 1) false then 2 else 0) +
    (if ws.getD (min (ws.length + 1) gate.2.1 - 1) false then 1 else 0)) false]

private theorem getD_min (ws : List Bool) (V : ℕ) :
    ws.getD (min (ws.length + 1) V - 1) false = ws.getD (V - 1) false := by
  rcases le_total (ws.length + 1) V with h | h
  · rw [min_eq_left h, Nat.add_sub_cancel]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ws.length ≤ V - 1 by omega)]
  · rw [min_eq_right h]

private theorem wires_eq_foldl (f : ConventionalCircuit) (x : List Bool) {s : ℕ} (hs : s ≤ f.q) :
    f.wires x s = (f.gateList.take s).foldl wireStep
      (x.take f.n ++ List.replicate (f.n - x.length) false) := by
  induction s with
  | zero => simp [ConventionalCircuit.wires]
  | succ s ih =>
    have hsq : s < f.q := hs
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, ConventionalCircuit.wires,
      dite_eq_left hsq]
    have hget : f.gateList[s]? = some (f.A ⟨s, hsq⟩, f.B ⟨s, hsq⟩,
        [f.G ⟨s, hsq⟩ false false, f.G ⟨s, hsq⟩ false true, f.G ⟨s, hsq⟩ true false,
          f.G ⟨s, hsq⟩ true true]) := by
      simp [ConventionalCircuit.gateList, hsq]
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, wireStep, getD_min,
      getD_table, ConventionalCircuit.wireVal, ← List.getD_eq_getElem?_getD]

private theorem wireStep_polyTime :
    ComputableInPolyTime (fun p : (Unit × List Bool) × (ℕ × ℕ × List Bool) => wireStep p.1.2 p.2)
      (encPair (encPair encUnit encBits) (encPair encNat (encPair encNat encBits))) encBits := by
  polytime [wireStep]

/-- The semantics `ev` is computed in polynomial time. -/
private theorem ev_polyTime :
    ComputableInPolyTime (fun (f, x) => (scheme family).ev f x) (encPair encValidCircuit encBits)
      encBits := by
  have hd : ComputableInPolyTime (fun p : ValidCircuit × List Bool =>
      (p.1.1.n, p.1.1.m, p.1.1.gateList)) (encPair encValidCircuit encBits) encCircuitData :=
    circuitData_polyTime.comp (ComputableInPolyTime.fst _ _)
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hg : ComputableInPolyTime (fun p : ValidCircuit × List Bool => p.1.1.gateList)
      (encPair encValidCircuit encBits) (encList (encPair encNat (encPair encNat encBits))) :=
    hd.snd'.snd'
  have hq := (ComputableTidilyInPolyTime.length_list _).computableInPolyTime.comp hg
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encUnit) (encL := encList (encPair encNat (encPair encNat encBits)))
    (encB := encBits) (encA := encPair encNat (encPair encNat encBits))
    (encIn := encPair encValidCircuit encBits)
    (step := fun (_ : Unit) ws gate => wireStep ws gate) (par := fun _ => ())
    (list := fun p => p.1.1.gateList)
    (init := fun p => p.2.take p.1.1.n ++ List.replicate (p.1.1.n - p.2.length) false)
    (by polytime) hg (by polytime) wireStep_polyTime (growth := fun _ => 1)
    (PolyBounded.const 1) (fun _ ws gate _ => by
      change (wireStep ws gate).length ≤ ws.length + 1
      simp [wireStep])
  have heq : (fun (f, x) => (scheme family).ev f x) = fun p : ValidCircuit × List Bool =>
      (p.1.1.gateList.foldl wireStep (p.2.take p.1.1.n ++
        List.replicate (p.1.1.n - p.2.length) false)).drop
          (p.1.1.n + p.1.1.gateList.length - p.1.1.m) := by
    funext p
    obtain ⟨f, x⟩ := p
    simp only [scheme, ConventionalCircuit.evalCirc, ConventionalCircuit.length_gateList]
    rw [wires_eq_foldl _ _ le_rfl,
      List.take_of_length_le (show f.1.gateList.length ≤ f.1.q by simp)]
  rw [heq]
  have hn' : ComputableInPolyTime (fun p : ValidCircuit × List Bool => p.1.1.n)
      (encPair encValidCircuit encBits) encUnary := hn
  have hm' : ComputableInPolyTime (fun p : ValidCircuit × List Bool => p.1.1.m)
      (encPair encValidCircuit encBits) encUnary := hm
  have hc : ComputableInPolyTime (fun p : ValidCircuit × List Bool =>
      p.1.1.n + p.1.1.gateList.length - p.1.1.m) (encPair encValidCircuit encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_sub.computableInPolyTime.comp
      ((ComputableTidilyInPolyTime.unary_add.computableInPolyTime.comp (hn'.prod hq)).prod hm')
  have hdrop : ComputableInPolyTime (fun p : List Bool × ℕ => p.1.drop p.2)
      (encPair encBits encUnary) encBits := by
    polytime
  exact hdrop.comp (hfold.prod hc)

include hf in
/-- **Point-and-permute garbling is efficient** for every family computed in polynomial time
(`PseudorandomFunction.polyTime` supplies `hf`): the length readers `n` and `m`, the number of
coins and the garbler on `(1^k, f, r)`, and `En`, `Ev`, `De` and `ev` on their encoded arguments,
run in polynomial time, for valid circuits encoded by `encValidCircuit`. -/
theorem scheme_isEfficient : (scheme family).IsEfficient encValidCircuit where
  inLen := circuitData_polyTime.fst'
  outLen := circuitData_polyTime.snd'.fst'
  coins := coins_polyTime
  gb := gb_polyTime hf
  encode := encodeWord_polyTime
  evalGarbled := evalWord_polyTime hf
  decode := decodeWord_polyTime
  ev := ev_polyTime

end Cslib.Crypto.Garbling.PointPermute
