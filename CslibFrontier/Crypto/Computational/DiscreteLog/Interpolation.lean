/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
public import Mathlib.LinearAlgebra.Lagrange
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Computational.DiscreteLog.Extract
import CslibFrontier.Crypto.Computational.DiffieHellman.EncodingBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Lagrange interpolation, and interpolation in the exponent, in polynomial time

Lemma 22.1 of [BonehShoup2023] says that the value at a point `j*` of a polynomial of degree less
than `t` over `Z_q` is a fixed combination `∑ λ_j ω(j)` of its values at `t` distinct nodes, and
that the coefficients `λ_j` are efficiently computable from the nodes and `j*`. Corollary 22.2
says that in a group of prime order `q` the element `h^{ω(j*)}` can be efficiently computed from
the nodes, `j*` and the elements `h^{ω(j)}`. This file proves both efficiency clauses, for
functions that are tied to the identities.

* `lagrangeWeightNat q nodes j x` computes the coefficient `λ_j` at the point `x` on natural
  numbers modulo `q`, as a product of the factors `(j - j')⁻¹ (x - j')` from `extractNat`. Modulo
  a prime it is the value at `x` of the Lagrange basis polynomial of `j`
  (`lagrangeWeightNat_cast_eq_eval_basis`), so Lemma 22.1 holds with these coefficients
  (`eval_eq_sum_lagrangeWeightNat_mul_eval`). With `q` the order of a group of a prime-order group
  family, it is computable in polynomial time (`computableInPolyTime_lagrangeWeightNat`).
* `lagrangeCombine d x shares` combines the group elements of a list of pairs `(j, h_j)` with
  those coefficients. On the elements `f(j) • h` it gives `f(x) • h`
  (`lagrangeCombine_eval_smul`, Corollary 22.2 written additively), and its encoding is
  computable in polynomial time from the encoded pairs
  (`computableInPolyTime_encode_lagrangeCombine`).

The identities over an arbitrary field, without cost statements, are
`Lagrange.eval_eq_sum_eval_basis_mul_eval` and `Lagrange.eval_smul_eq_sum_eval_basis_smul`.

Differences from the book:

* The prime is the order `F.order d` of a group of a `PrimeOrderGroupFamily`, because the
  certified inverse modulo a prime, `computableInPolyTime_extractNat`, is stated for it. The
  identities `lagrangeWeightNat_cast_eq_eval_basis` and `eval_eq_sum_lagrangeWeightNat_mul_eval`
  hold for every prime `q`.
* The node set `J ⊆ Z_q` is a list of natural numbers whose residues modulo the order are
  distinct, and the point `j*` is any natural number. The computed coefficient needs no hypothesis
  on the nodes: it skips the nodes equal to `j` modulo the order.
* The group is written additively, as in the library's Diffie–Hellman modules.
* The combination's certificate takes the encodings of group elements, not arbitrary words: the
  input is the list of pairs `(j, F.encode d h_j)`. For words that are not encodings, no
  polynomial bound on the intermediate results of the combination is available.
* `lagrangeCombine` recomputes every coefficient with its own fold, so it performs quadratically
  many modular exponentiations in the number of nodes. The certificates claim polynomial time
  and no sharper bound.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.lagrangeWeightNat`: the Lagrange coefficient modulo `q` on
  natural numbers.
* `Cslib.Crypto.PrimeOrderGroupFamily.lagrangeCombine`: the combination of group elements with
  those coefficients.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.lagrangeWeightNat_cast_eq_eval_basis`: the computed
  coefficient is the value of a Lagrange basis polynomial.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_eq_sum_lagrangeWeightNat_mul_eval`: Lemma 22.1 of
  [BonehShoup2023] with the computed coefficients.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_lagrangeWeightNat`: the efficiency
  clause of Lemma 22.1.
* `Cslib.Crypto.PrimeOrderGroupFamily.lagrangeCombine_eval_smul`: Corollary 22.2 for the computed
  combination.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encode_lagrangeCombine`: the efficiency
  clause of Corollary 22.2.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 22.1.1, Lemma 22.1 (p. 928) and Corollary 22.2 (p. 929).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Turing.MultiTapeTM Polynomial

/-! ### The interpolation coefficient on natural numbers -/

/-- The Lagrange interpolation coefficient at the point `x` of the node `j` among `nodes`, computed
modulo `q` on natural numbers: the product of `(j - j')⁻¹ (x - j')` over the nodes `j'` that differ
from `j` modulo `q`, each factor computed by `extractNat`. -/
def lagrangeWeightNat (q : ℕ) (nodes : List ℕ) (j x : ℕ) : ℕ :=
  nodes.foldl
    (fun acc j' => if j' % q = j % q then acc else acc * extractNat q j x j' j' % q) 1

private theorem foldl_lagrangeStep_cast {q : ℕ} [Fact q.Prime] (nodes : List ℕ) (j x acc : ℕ) :
    ((nodes.foldl
        (fun acc j' => if j' % q = j % q then acc else acc * extractNat q j x j' j' % q)
        acc : ℕ) : ZMod q) =
      acc * (nodes.map fun j' : ℕ =>
        if (j' : ZMod q) = j then 1 else ((x : ZMod q) - j') / ((j : ZMod q) - j')).prod := by
  induction nodes generalizing acc with
  | nil => simp
  | cons j' nodes ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    congr 1
    have hiff : j' % q = j % q ↔ (j' : ZMod q) = j := (ZMod.natCast_eq_natCast_iff' j' j q).symm
    by_cases h : (j' : ZMod q) = j
    · simp only [hiff.mpr h, h, ↓reduceIte, mul_one]
    · simp only [mt hiff.mp h, h, ↓reduceIte]
      rw [ZMod.natCast_mod, Nat.cast_mul, extractNat_cast (Ne.symm h), div_eq_inv_mul]

/-- Modulo a prime `q`, `lagrangeWeightNat` is the product of the quotients `(x - j') / (j - j')`
over the nodes `j'` that differ from `j` modulo `q`. No hypothesis on the nodes is needed. -/
theorem lagrangeWeightNat_cast {q : ℕ} [Fact q.Prime] (nodes : List ℕ) (j x : ℕ) :
    (lagrangeWeightNat q nodes j x : ZMod q) =
      (nodes.map fun j' : ℕ =>
        if (j' : ZMod q) = j then 1 else ((x : ZMod q) - j') / ((j : ZMod q) - j')).prod := by
  rw [lagrangeWeightNat, foldl_lagrangeStep_cast, Nat.cast_one, one_mul]

/-- Modulo a prime `q`, for nodes that are distinct modulo `q` and a node `j` among them,
`lagrangeWeightNat` is the value at `x` of the Lagrange basis polynomial of `j`: the coefficient of
`Lagrange.eval_basis`. Both hypotheses are needed. -/
theorem lagrangeWeightNat_cast_eq_eval_basis {q : ℕ} [Fact q.Prime] {nodes : List ℕ}
    (hnodes : (nodes.map (Nat.cast : ℕ → ZMod q)).Nodup) {j : ℕ} (hj : j ∈ nodes) (x : ℕ) :
    (lagrangeWeightNat q nodes j x : ZMod q) =
      (Lagrange.basis nodes.toFinset (Nat.cast : ℕ → ZMod q) j).eval (x : ZMod q) := by
  rw [lagrangeWeightNat_cast, Lagrange.eval_basis, ← List.prod_toFinset _ hnodes.of_map,
    ← Finset.mul_prod_erase _ _ (List.mem_toFinset.mpr hj)]
  simp only [↓reduceIte, one_mul]
  refine Finset.prod_congr rfl fun j' hj' => ?_
  rw [Finset.mem_erase, List.mem_toFinset] at hj'
  have hne : (j' : ZMod q) ≠ j := fun h => hj'.1 (List.inj_on_of_nodup_map hnodes hj'.2 hj h)
  simp only [hne, ↓reduceIte]

/-- **Lemma 22.1** of [BonehShoup2023] for the computed coefficients: for a prime `q`, nodes that
are distinct modulo `q` and a polynomial `f` over `ZMod q` of degree less than the number of
nodes, the value of `f` at any point `x` is the combination of its values at the nodes with the
coefficients `lagrangeWeightNat q nodes j x`. These coefficients are computable in polynomial time
when `q` is the order of a group of a family (`computableInPolyTime_lagrangeWeightNat`). -/
theorem eval_eq_sum_lagrangeWeightNat_mul_eval {q : ℕ} [Fact q.Prime] {nodes : List ℕ}
    (hnodes : (nodes.map (Nat.cast : ℕ → ZMod q)).Nodup) {f : (ZMod q)[X]}
    (hf : f.degree < nodes.length) (x : ℕ) :
    f.eval (x : ZMod q) =
      (nodes.map fun j => (lagrangeWeightNat q nodes j x : ZMod q) * f.eval (j : ZMod q)).sum := by
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod q) nodes.toFinset := fun a ha b hb h =>
    List.inj_on_of_nodup_map hnodes (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) h
  rw [Lagrange.eval_eq_sum_eval_basis_mul_eval hinj
    (by rwa [List.toFinset_card_of_nodup hnodes.of_map]) (x : ZMod q),
    List.sum_toFinset _ hnodes.of_map]
  exact congrArg List.sum (List.map_congr_left fun j hj => by
    rw [lagrangeWeightNat_cast_eq_eval_basis hnodes hj])

variable {F : PrimeOrderGroupFamily}

/-- **The efficiency clause of Lemma 22.1** of [BonehShoup2023]: the coefficient
`lagrangeWeightNat` modulo the group order is computable in polynomial time from the group
description, the list of nodes, the node and the point, all computed from the input. No hypothesis
on the nodes is needed. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeWeightNat {α : Type} {input : α ↪ List Bool}
    {d : α → F.Desc} {nodes : α → List ℕ} {j x : α → ℕ}
    (hd : ComputableInPolyTime d input F.encDesc)
    (hnodes : ComputableInPolyTime nodes input (encList encNat))
    (hj : ComputableInPolyTime j input encNat) (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime
      (fun a => lagrangeWeightNat (F.order (d a)) (nodes a) (j a) (x a)) input encNat := by
  have hq : ComputableInPolyTime (fun a => F.order (d a)) input encNat :=
    F.computableInPolyTime_order.comp hd
  unfold lagrangeWeightNat
  -- A fold over the nodes with the parameter `(d, j, x)`; each step returns the accumulator or a
  -- residue below the order, so the accumulator grows by at most the length of the order.
  refine ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encNat) (encL := encList encNat) (encB := encNat)
    (encP := encPair F.encDesc (encPair encNat encNat))
    (par := fun a => (d a, j a, x a)) (list := nodes) (init := fun _ => 1)
    (step := fun p acc j' =>
      if j' % F.order p.1 = p.2.1 % F.order p.1 then acc
      else acc * extractNat (F.order p.1) p.2.1 p.2.2 j' j' % F.order p.1)
    (hd.prod (hj.prod hx)) hnodes (.const 1) ?_
    (growth := fun a => (encNat (F.order (d a))).length)
    hq.polyBounded_length ?_
  · let E := encPair (encPair (encPair F.encDesc (encPair encNat encNat)) encNat) encNat
    have hd' : ComputableInPolyTime (fun p : ((F.Desc × ℕ × ℕ) × ℕ) × ℕ => p.1.1.1) E
        F.encDesc := by fun_prop
    have hj' : ComputableInPolyTime (fun p : ((F.Desc × ℕ × ℕ) × ℕ) × ℕ => p.1.1.2.1) E
        encNat := by fun_prop
    have hx' : ComputableInPolyTime (fun p : ((F.Desc × ℕ × ℕ) × ℕ) × ℕ => p.1.1.2.2) E
        encNat := by fun_prop
    have hacc : ComputableInPolyTime (fun p : ((F.Desc × ℕ × ℕ) × ℕ) × ℕ => p.1.2) E
        encNat := by fun_prop
    have hv : ComputableInPolyTime (fun p : ((F.Desc × ℕ × ℕ) × ℕ) × ℕ => p.2) E
        encNat := by fun_prop
    have hq' := F.computableInPolyTime_order.comp hd'
    have hex := computableInPolyTime_extractNat hd' hj' hx' hv hv
    exact (ComputableTidilyInPolyTime.ite_decide
      (ComputableTidilyInPolyTime.decide_eq' (hv.binary_mod' hq').tidy (hj'.binary_mod' hq').tidy)
      hacc.tidy ((hacc.binary_mul' hex).binary_mod' hq').tidy).computableInPolyTime
  · intro a state value _
    split_ifs
    · exact Nat.le_add_right _ _
    · have hlt := Nat.mod_lt (state * extractNat (F.order (d a)) (j a) (x a) value value)
        (F.prime_order (d a)).pos
      simp only [encNat_apply, Nat.size_eq_bits_len] at *
      exact (Nat.size_le_size hlt.le).trans (Nat.le_add_left _ _)

/-! ### Interpolation in the exponent -/

variable (F) in
/-- The combination `∑ λ_j • h_j` of the group elements `h_j` of the pairs `(j, h_j)`, with the
coefficients `λ_j = lagrangeWeightNat` of their nodes at the point `x` modulo the group order.
This is the book's `∏ (h^{ω(j)})^{λ_j}` ([BonehShoup2023], Corollary 22.2), written
additively. -/
@[expose] def lagrangeCombine (d : F.Desc) (x : ℕ) (shares : List (ℕ × F.Carrier d)) :
    F.Carrier d :=
  (shares.map fun s =>
    (lagrangeWeightNat (F.order d) (shares.map Prod.fst) s.1 x : ZMod (F.order d)) • s.2).sum

/-- **Corollary 22.2** of [BonehShoup2023] for the computed combination, written additively: from
the elements `f(j) • h` at nodes that are distinct modulo the group order, `lagrangeCombine` gives
`f(x) • h`, for a polynomial `f` of degree less than the number of nodes. Its encoding is
computable in polynomial time (`computableInPolyTime_encode_lagrangeCombine`). -/
theorem lagrangeCombine_eval_smul (d : F.Desc) {nodes : List ℕ}
    (hnodes : (nodes.map (Nat.cast : ℕ → ZMod (F.order d))).Nodup) {f : (ZMod (F.order d))[X]}
    (hf : f.degree < nodes.length) (x : ℕ) (h : F.Carrier d) :
    F.lagrangeCombine d x (nodes.map fun j : ℕ => (j, f.eval (j : ZMod (F.order d)) • h)) =
      f.eval (x : ZMod (F.order d)) • h := by
  have hfst :
      (nodes.map fun j : ℕ => (j, f.eval (j : ZMod (F.order d)) • h)).map Prod.fst = nodes := by
    simp [List.map_map, Function.comp_def]
  rw [lagrangeCombine, hfst, List.map_map, eval_eq_sum_lagrangeWeightNat_mul_eval hnodes hf x,
    List.sum_smul, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun j _ => by simp [mul_smul])

/-- The fold that the machine runs, on encoded elements, computes the encoding of the
combination, started from any group element. -/
private theorem foldl_combine_encode (d : F.Desc) (w : ℕ → ℕ) (shares : List (ℕ × F.Carrier d))
    (g : F.Carrier d) :
    (shares.map fun s => (s.1, F.encode d s.2)).foldl
        (fun acc s => F.add (d, acc, F.smul (d, w s.1, s.2))) (F.encode d g) =
      F.encode d (g + (shares.map fun s => (w s.1 : ZMod (F.order d)) • s.2).sum) := by
  induction shares generalizing g with
  | nil => simp
  | cons s shares ih =>
    rw [List.map_cons, List.foldl_cons, F.smul_encode, F.add_encode, ih, List.map_cons,
      List.sum_cons, add_assoc]

/-- **The efficiency clause of Corollary 22.2** of [BonehShoup2023]: the encoding of
`lagrangeCombine` is computable in polynomial time from the group description, the point and the
list of pairs `(j, F.encode d h_j)` of nodes and encoded group elements, all computed from the
input. The elements must be group elements: the input is their encodings, not arbitrary words. -/
theorem computableInPolyTime_encode_lagrangeCombine {α : Type} {input : α ↪ List Bool}
    {d : α → F.Desc} {x : α → ℕ} {shares : (a : α) → List (ℕ × F.Carrier (d a))}
    (hd : ComputableInPolyTime d input F.encDesc) (hx : ComputableInPolyTime x input encNat)
    (hshares : ComputableInPolyTime
      (fun a => (shares a).map fun s => (s.1, F.encode (d a) s.2)) input
      (encList (encPair encNat encBits))) :
    ComputableInPolyTime
      (fun a => F.encode (d a) (F.lagrangeCombine (d a) (x a) (shares a))) input encBits := by
  obtain ⟨c, k, hlen⟩ := F.exists_length_encode_le
  let words : α → List (ℕ × List Bool) := fun a =>
    (shares a).map fun s => (s.1, F.encode (d a) s.2)
  have hnodes : ComputableInPolyTime (fun a => (words a).map Prod.fst) input (encList encNat) := by
    fun_prop
  -- The components of the input of a fold step: parameter `(d, x, nodes)`, accumulator, entry.
  let E := encPair (encPair (encPair F.encDesc (encPair encNat (encList encNat))) encBits)
    (encPair encNat encBits)
  have hd' : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.1.1.1) E F.encDesc := by
    fun_prop
  have hx' : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.1.1.2.1) E encNat := by
    fun_prop
  have hns : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.1.1.2.2) E
      (encList encNat) := by
    fun_prop
  have hacc : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.1.2) E encBits := by
    fun_prop
  have hj : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.2.1) E encNat := by
    fun_prop
  have hw : ComputableInPolyTime
      (fun p : ((F.Desc × ℕ × List ℕ) × List Bool) × ℕ × List Bool => p.2.2) E encBits := by
    fun_prop
  have hstep := F.computableInPolyTime_add.comp (hd'.prod (hacc.prod
    (F.computableInPolyTime_smul.comp (hd'.prod
      ((computableInPolyTime_lagrangeWeightNat hd' hns hj hx').prod hw)))))
  -- Invariant: the accumulator encodes a group element, so its length is bounded polynomially.
  have hfold := (ComputableInPolyTime.foldlWith_spec
    (encP := encPair F.encDesc (encPair encNat (encList encNat)))
    (encA := encPair encNat encBits) (encL := encList (encPair encNat encBits)) (encB := encBits)
    (par := fun a => (d a, x a, (words a).map Prod.fst)) (list := words)
    (init := fun a => F.encode (d a) 0)
    (step := fun p acc s =>
      F.add (p.1, acc, F.smul (p.1, lagrangeWeightNat (F.order p.1) p.2.2 s.1 p.2.1, s.2)))
    (hd.prod (hx.prod hnodes)) hshares (computableInPolyTime_encode_zero hd) hstep
    (fun a _ state => state ∈ Set.range (F.encode (d a)))
    (fun a => ⟨0, rfl⟩) ?_
    (size := fun a => c * ((F.encDesc (d a)).length + 1) ^ k)
    ((PolyBounded.const c).mul ((hd.polyBounded_length.add (.const 1)).pow k)) ?_).1
  · refine hfold.of_enc_eq fun a => ?_
    have hfst : (words a).map Prod.fst = (shares a).map Prod.fst := by
      simp [words, List.map_map, Function.comp_def]
    have key := foldl_combine_encode (d a)
      (fun j => lagrangeWeightNat (F.order (d a)) ((shares a).map Prod.fst) j (x a)) (shares a) 0
    rw [zero_add] at key
    simp only [encBits_apply, hfst]
    exact key.symm
  · rintro a consumed _ value hprefix ⟨g, rfl⟩
    have hmem : value ∈ words a :=
      hprefix.subset (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hmem
    refine ⟨g + ((lagrangeWeightNat (F.order (d a)) ((words a).map Prod.fst) s.1 (x a) : ℕ) :
      ZMod (F.order (d a))) • s.2, ?_⟩
    simp only [F.smul_encode, F.add_encode]
  · rintro a _ _ _ ⟨g, rfl⟩
    simpa using hlen (d a) g

end Cslib.Crypto.PrimeOrderGroupFamily
