/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Data.List.GetD

/-!
# Logarithmic-randomness PCP is contained in NP

Enumerating all random words gives polynomially many queries, even when their binary addresses
are large. The NP certificate records the bits at those addresses. Looking up an address's first
occurrence makes repeated queries consistent. A possibly long PCP proof is reconstructed only
in the soundness argument, never by the polynomial-time verifier.

## Main definitions

* `PCPVerifier.queryTable`: the complete list of binary proof addresses.
* `PCPVerifier.tableVerifier`: an exhaustive checker with consistent first-occurrence lookup.
* `PCPVerifier.proofOfTable`: finite proof reconstructed from a query table by first-occurrence
  lookup.

## Main results

* `PCPVerifier.isPolyTime_enumList_of_le_mul_log`, `PCPVerifier.isPolyTime_enumCoins`:
  enumerating logarithmically bounded bit-string tables in polynomial time.
* `PCPVerifier.isPolyTime_queryTable`: the complete address table is computable in polynomial
  time under the logarithmic coin bound.
* `PCPVerifier.isPolyTime_tableWordVerdict`, `PCPVerifier.isPolyTime_tableVerifier`: uniform
  efficiency, including malformed tables.
* `PCPVerifier.mem_queryTable`: the table records every address queried on a valid random word.
* `PCPVerifier.verdict_answers_queryTable_append`, `PCPVerifier.accepts_proofOfTable`,
  `PCPVerifier.tableVerifier_complete`, `PCPVerifier.tableVerifier_sound`: exact proof transfer.
* `PCPVerifier.mem_NP_of_tableCheck`: shared polynomial-length table padding criterion for `NP`
  membership.
* `Cslib.Complexity.IsPCPVerifier.mem_iff_exists_tableVerifier`: the tables accepted by the
  exhaustive check characterize the problem.
* `Cslib.Complexity.PCP_log_subset_NP`: logarithmic-randomness PCP is contained in NP.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
-/

@[expose] public section

open Turing.MultiTapeTM

namespace Cslib.Complexity.PCPVerifier

variable {α : Type} (V : PCPVerifier α)

/-- All proof addresses queried on all valid random words, retaining repeated occurrences. -/
def queryTable (a : α) : List ℕ :=
  (BitString.enumList (V.coins a)).flatMap fun word => V.queries (a, word)

/-- Exhaustively check the random words using the bit at each address's first table occurrence. -/
def tableVerifier (input : α × List Bool) : Bool :=
  let addresses := V.queryTable input.1
  (BitString.enumList (V.coins input.1)).all fun word =>
    V.verdict ((input.1, word), (V.queries (input.1, word)).map fun address =>
      input.2.getD (addresses.idxOf address) false)

variable {V} {enc : α ↪ List Bool} {c : ℕ}

/-- Enumerating all bit strings of length `f a` is polynomial-time whenever `f` is computable in
polynomial time into `encUnary` and bounded by `c * (Nat.log 2 (enc a).length + 1)`. -/
theorem isPolyTime_enumList_of_le_mul_log {f : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary)
    (hle : ∀ a, f a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime (fun a => BitString.enumList (f a)) enc (encList encBits) := by
  apply ComputableInPolyTime.bitsEnumList hf
    (size := fun n => 2 ^ (c * (Nat.log 2 n + 1)) * (2 * (c * (Nat.log 2 n + 1)) + 1))
  · have hpow := polynomiallyBounded_two_pow_mul_log c
    fun_prop
  · intro a
    have ha := hle a
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ha) (by lia)

private theorem coins_unary (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.coins enc encUnary :=
  .binary_to_unary_bounded hV.coins (by fun_prop) hcoins

/-- Enumerating all `V.coins a`-bit random words is polynomial-time under a logarithmic coin
bound. -/
theorem isPolyTime_enumCoins (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime (fun a => BitString.enumList (V.coins a))
      enc (encList encBits) :=
  isPolyTime_enumList_of_le_mul_log (coins_unary hV hcoins) hcoins

/-- The complete address table charges every enumerated word and binary address. -/
theorem isPolyTime_queryTable (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.queryTable enc (encList encNat) := by
  have he := isPolyTime_enumCoins hV hcoins
  have hq := hV.queries
  unfold queryTable
  fun_prop

/-- Evaluating `V.verdict` on a candidate table `(a, table)` and a random word `word` using
first-occurrence lookup in `V.queryTable a` is polynomial-time under a logarithmic coin bound. -/
theorem isPolyTime_tableWordVerdict (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun x : (α × List Bool) × List Bool =>
        V.verdict ((x.1.1, x.2), (V.queries (x.1.1, x.2)).map fun address =>
          x.1.2.getD ((V.queryTable x.1.1).idxOf address) false))
      (encPair (encPair enc encBits) encBits) encBool := by
  have hq := hV.queries
  have hv := hV.verdict
  have ht := isPolyTime_queryTable hV hcoins
  have hinput := ComputableInPolyTime.fst (encPair enc encBits) encBits
  have hword := ComputableInPolyTime.snd (encPair enc encBits) encBits
  have hqueries := hq.comp (hinput.fst'.prod hword)
  have htable := ht.comp hinput.fst'
  have hproof := hinput.snd'
  have houter := ComputableInPolyTime.fst (encPair (encPair enc encBits) encBits) encNat
  have haddress := ComputableInPolyTime.snd (encPair (encPair enc encBits) encBits) encNat
  have hlookup := (ComputableInPolyTime.bitsGetD false).comp
    ((hproof.comp houter).prod ((ComputableInPolyTime.idxOf encNat).comp
      ((htable.comp houter).prod haddress)))
  have hanswers := ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.mapWithInput
      (f := fun input address => input.1.2.getD (List.idxOf address (V.queryTable input.1.1)) false)
      hqueries (by simpa only [Function.comp_def] using hlookup))
  exact hv.comp ((hinput.fst'.prod hword).prod hanswers)

/-- Exhaustive verification is polynomial time for every table, including short inputs. -/
theorem isPolyTime_tableVerifier (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.tableVerifier (encPair enc encBits) encBool :=
  ComputableInPolyTime.allWithInput
    ((isPolyTime_enumCoins hV hcoins).comp (ComputableInPolyTime.fst enc encBits))
    (isPolyTime_tableWordVerdict hV hcoins)

/-- Every address queried on a random word of the right length occurs in the address table. -/
theorem mem_queryTable {a : α} {word : List Bool} {address : ℕ}
    (hword : word.length = V.coins a) (haddress : address ∈ V.queries (a, word)) :
    address ∈ V.queryTable a :=
  List.mem_flatMap.mpr ⟨word, BitString.mem_enumList.mpr hword, haddress⟩

/-- On any random word of length `V.coins a`, first-occurrence lookup in
`answers proof (V.queryTable a) ++ padding` gives the same verdict as `V.accepts a proof word`. -/
theorem verdict_answers_queryTable_append (a : α) (proof padding word : List Bool)
    (hword : word.length = V.coins a) :
    V.verdict ((a, word), (V.queries (a, word)).map fun address =>
      (answers proof (V.queryTable a) ++ padding).getD ((V.queryTable a).idxOf address) false) =
      V.accepts a proof word := by
  unfold accepts answers
  congr 2
  refine List.map_congr_left fun address haddress => ?_
  have hmem := mem_queryTable hword haddress
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, List.idxOf_lt_length_iff.2 hmem]

/-- A genuine proof supplies a consistent table; trailing padding is never read. -/
theorem tableVerifier_complete (a : α) (proof padding : List Bool)
    (h : ∀ word, word.length = V.coins a → V.accepts a proof word = true) :
    V.tableVerifier (a, answers proof (V.queryTable a) ++ padding) = true :=
  List.all_eq_true.mpr fun word hword => by
    rw [verdict_answers_queryTable_append a proof padding word (BitString.mem_enumList.mp hword)]
    exact h word (BitString.mem_enumList.mp hword)

variable (V) in
/-- Expand a bit table indexed by `V.queryTable a` into a full proof string by looking up each
address's first occurrence in `V.queryTable a`. -/
def proofOfTable (a : α) (table : List Bool) : List Bool :=
  (List.range ((V.queryTable a).sum + 1)).map fun address =>
    table.getD ((V.queryTable a).idxOf address) false

/-- On any random word of length `V.coins a`, `V.proofOfTable a table` gives the exact same verdict
as first-occurrence lookup in `table`. -/
theorem accepts_proofOfTable (a : α) (table word : List Bool)
    (hword : word.length = V.coins a) :
    V.accepts a (V.proofOfTable a table) word =
      V.verdict ((a, word), (V.queries (a, word)).map fun address =>
        table.getD ((V.queryTable a).idxOf address) false) := by
  unfold accepts answers
  congr 2
  refine List.map_congr_left fun address haddress => ?_
  have hmem := mem_queryTable hword haddress
  have hbound : address < (V.queryTable a).sum + 1 := Nat.lt_succ_of_le (List.le_sum_of_mem hmem)
  simp [proofOfTable, List.getD_eq_getElem?_getD, hbound]

/-- Every table, including malformed or short certificates, is the restriction of a finite proof.
The expanded proof is only a mathematical witness; its length need not be polynomial. -/
theorem tableVerifier_sound (a : α) (table : List Bool)
    (h : V.tableVerifier (a, table) = true) :
    ∃ proof, ∀ word, word.length = V.coins a → V.accepts a proof word = true :=
  ⟨V.proofOfTable a table, fun word hword => by
    rw [accepts_proofOfTable a table word hword]
    exact List.all_eq_true.mp h word (BitString.mem_enumList.mpr hword)⟩

/-- Any polynomial-time table predicate `check : α × List Bool → Bool` that accepts padded query
tables `answers proof (V.queryTable a) ++ padding` on members of `A` and rejects all tables on
non-members witnesses `A ∈ NP enc` under a logarithmic coin bound. -/
theorem mem_NP_of_tableCheck {A : Set α} {check : α × List Bool → Bool}
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hcheck : ComputableInPolyTime check (encPair enc encBits) encBool)
    (hcomplete : ∀ a ∈ A, ∃ proof, ∀ padding,
      check (a, answers proof (V.queryTable a) ++ padding) = true)
    (hsound : ∀ a table, check (a, table) = true → a ∈ A) :
    A ∈ NP enc := by
  obtain ⟨p, hlength⟩ :=
    (isPolyTime_queryTable hV hcoins).polyBounded_length.exists_polynomial
  have hbound (a : α) : (V.queryTable a).length ≤ p.eval (enc a).length :=
    (length_le_length_encList encNat (V.queryTable a)).trans (hlength a)
  refine ⟨p, check, hcheck, fun a => ?_⟩
  constructor
  · intro ha
    obtain ⟨proof, hproof⟩ := hcomplete a ha
    let table := answers proof (V.queryTable a)
    refine ⟨table ++ List.replicate (p.eval (enc a).length - table.length) false, ?_, hproof _⟩
    have htable : table.length ≤ p.eval (enc a).length := by
      simpa [table, answers] using hbound a
    simp only [List.length_append, List.length_replicate]
    lia
  · rintro ⟨table, _, htable⟩
    exact hsound a table htable

end Cslib.Complexity.PCPVerifier

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- For a PCP verifier of `A`, the instances some table makes the exhaustive table check accept
are exactly the members of `A`. -/
theorem IsPCPVerifier.mem_iff_exists_tableVerifier {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (h : IsPCPVerifier enc r q V A) (a : α) :
    a ∈ A ↔ ∃ table, V.tableVerifier (a, table) = true := by
  refine ⟨fun ha => ?_, fun ⟨table, htable⟩ => ?_⟩
  · obtain ⟨proof, hproof⟩ := h.complete a ha
    exact ⟨_, by simpa using PCPVerifier.tableVerifier_complete a proof [] hproof⟩
  · by_contra ha
    obtain ⟨proof, hproof⟩ := PCPVerifier.tableVerifier_sound a table htable
    have hs := h.sound a ha proof
    have hc : acceptCount (fun x => V.accepts x.1 proof x.2) a (V.coins a) = 2 ^ V.coins a := by
      simp [acceptCount, hproof]
    rw [hc] at hs
    have hp : 0 < 2 ^ V.coins a := Nat.two_pow_pos _
    lia

/-- Logarithmically many random bits can be checked exhaustively in NP, regardless of the query
bound. Binary proof addresses are represented by a polynomial-length table of queried bits. -/
theorem PCP_log_subset_NP (q : ℕ → ℕ) :
    PCP (fun n => Nat.log 2 n + 1) q enc ⊆ NP enc := by
  rintro A ⟨V, c, d, hV, hpcp⟩
  exact PCPVerifier.mem_NP_of_tableCheck hV hpcp.coins_le
    (PCPVerifier.isPolyTime_tableVerifier hV hpcp.coins_le)
    (fun a ha =>
      let ⟨proof, hproof⟩ := hpcp.complete a ha
      ⟨proof, fun padding => PCPVerifier.tableVerifier_complete a proof padding hproof⟩)
    (fun a table htable => (hpcp.mem_iff_exists_tableVerifier a).2 ⟨table, htable⟩)

end Cslib.Complexity
