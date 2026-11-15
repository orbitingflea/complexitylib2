/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Label
public import CslibFrontier.Crypto.Primitives.Garbling.CircularCorrelationRobust

/-!
# Circular correlation robust hash families

The finite notion `Cslib.Crypto.Garbling.CCR.advantage` measures how well one adversary tells a
circular oracle from a random function, for one hash on finite types. This module states the
asymptotic assumption on a hash family given on words, `hash : List Bool → List Bool → List Bool`,
in the form of Definition 1 of Zahur, Rosulek and Evans [ZahurRosulekEvans2015] (§4.1, p. 10 of
ePrint 2014/756, version of March 16, 2015): for a uniform `R` with least significant bit `1`, the
oracle `Circ_R(x, i, b) = H(x ⊕ R, i) ⊕ bR` must be indistinguishable from a random function by
polynomial-time adversaries that never query one `(x, i)` with both values of `b`.

At level `k` a label is a `(k + 1)`-bit key and a colour bit, `(k + 2)` bits in all, and a tweak
has `k` bits. `CCR.atLevel hash k` hashes the label's word (the key bits, then the colour) with the
tweak's bits, and reads the first `k + 2` bits of the answer as a label, padding with `false`. The
offset `CCR.offset R = (R, true)` has colour `true`: the colour is the least significant bit that
Definition 1 fixes to `1`. A word distinguisher `W : OracleDistinguisher` sends a query
`(x, t, b)` as the request of the `k + 2` bits of `x`, the `k` bits of `t` and the bit `b`, and
reads a label as its `k + 2` bits (`CCR.codec k`).

`CircularCorrelationRobust hash` asks that the hash be computable in polynomial time and that
every uniform strict oracle-PPT word distinguisher that never repeats a tweak, at any level, have
negligible advantage. Its level-`k` advantage is, by definition, the finite advantage
`CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset ((CCR.codec k).adapt (W k []))`, so the
finite theorems about `CCR.advantage` apply at every level without a bridge. The lemma
`CircularCorrelationRobust.negligible_advantage` is this finite-advantage reading of the assumption,
not a separate result. Legality is required at every level, as in the
source; a reduction that would need more than the `2 ^ k` tweaks of level `k` stays legal by making
no queries there.

## Relation to the sources

The assumption has two parts. Its security condition `secure` is Definition 1 of
[ZahurRosulekEvans2015] with the differences below, each of which admits fewer adversaries or fixes
a parametrization. So for a hash family that is evaluated in polynomial time, Definition 1 implies
`secure`. The evaluation premise `polyTime` is separate: Definition 1 does not supply it.

* **Legality.** An adversary must ask at most one query per tweak on every run
  (`CCR.IsTweakUnique`), at every level. Definition 1 forbids only asking one `(x, i)` with both
  bits. Guo, Katz, Wang and Yu [GuoKatzWangYu2020] name non-repeating tweaks as a weaker notion
  that may suffice (locator not verified).
* **Tweaks** are `k`-bit strings at level `k`; Definition 1 takes them from `ℤ`
  (`H : {0, 1}^k × ℤ → {0, 1}^k`, p. 8).
* **Lengths.** Labels have `k + 2` bits at level `k`, where Definition 1 has `k`.
* **Adversaries** are uniform strict oracle-PPT word programs; Definition 1 says "polynomial-time
  adversaries", and Choi, Katz, Kumaresan and Zhou [ChoiKatzKumaresanZhou2012] admit non-uniform
  ones.
* **Evaluation.** `polyTime` asks that one deterministic machine evaluate the hash in polynomial
  time on all words. Definition 1 gives the adversary unrestricted access to `H` but asks nothing
  of its running time. The premise is kept because the garbling schemes built on the hash must be
  efficient.

Definition 3 of [GuoKatzWangYu2020] (tccr; locator not verified) is the concrete form of the same
notion, with repeatable tweaks and every key law of min-entropy at least `ρ`. Definition 4 of
[ChoiKatzKumaresanZhou2012] (locator not verified) is the dual-key notion from which circular
correlation robustness originates. Definition 3 of [ZahurRosulekEvans2015] (p. 11), robustness for
naturally derived keys, restricts the adversary further; Theorem 1 there (p. 12), privacy of
half-gates garbling, assumes only that weaker notion.

## Main definitions

* `Cslib.Crypto.Garbling.CCR.atLevel`: the hash of a word family at level `k`.
* `Cslib.Crypto.Garbling.CCR.codec`: circular-oracle queries and labels on the word channel.
* `Cslib.Crypto.CircularCorrelationRobust`: the asymptotic assumption.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Garbling

namespace Garbling.CCR

/-- The hash of the word family `hash` at level `k`: the label `(key, colour)` and the tweak `t`
are hashed as the word of the `k + 1` bits of `key` followed by `colour`, and the word of the `k`
bits of `t`; the first `k + 1` bits of the answer are the key of the result and bit `k + 1` its
colour, padding with `false`. -/
@[expose] def atLevel (hash : List Bool → List Bool → List Bool) (k : ℕ) :
    BitString (k + 1) × Bool → BitString k → BitString (k + 1) × Bool
  | (key, colour), t =>
    let word := hash (List.ofFn key ++ [colour]) (List.ofFn t)
    (BitString.ofList (k + 1) word, word.getD (k + 1) false)

/-- Circular-oracle queries at level `k` on the single word channel. The query `(x, t, b)`, with
`x = (key, colour)`, is the request of the `k + 1` bits of `key`, then `colour`, then the `k` bits
of `t`, then `b`, `2 k + 3` bits in all; a request carries a query exactly when it has `2 k + 3`
bits. A label reply is the bits of its key followed by its colour, the reply of `labelCodec k`. -/
@[expose] def codec (k : ℕ) :
    OracleCodec Unit (Query (BitString (k + 1) × Bool) (BitString k))
      fun _ => BitString (k + 1) × Bool where
  encodeQuery
    | ⟨(key, colour), t, b⟩ => ((), List.ofFn key ++ colour :: (List.ofFn t ++ [b]))
  decodeQuery
    | ((), word) =>
      if word.length = 2 * k + 3 then
        some ⟨(BitString.ofList (k + 1) word, word.getD (k + 1) false),
          BitString.ofList k (word.drop (k + 2)), word.getD (2 * k + 2) false⟩
      else none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, word⟩ ⟨⟨key, colour⟩, t, b⟩
    by_cases hlen : word.length = 2 * k + 3
    · simp only [hlen, ↓reduceIte, Option.some.injEq, Query.mk.injEq, Prod.mk.injEq, true_and]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, rfl, rfl⟩
        have hkey : List.ofFn (BitString.ofList (k + 1) word) = word.take (k + 1) := by
          rw [BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by omega)]
        have htweak : List.ofFn (BitString.ofList k (word.drop (k + 2))) =
            (word.drop (k + 2)).take k := by
          rw [BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by simp; omega)]
        rw [hkey, htweak]
        refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
        simp only [List.getElem_append, List.getElem_cons, List.getElem_take, List.getElem_drop,
          List.length_take, List.length_drop, List.getD_eq_getElem?_getD, hlen]
        split_ifs <;> first
          | rfl
          | (exfalso; omega)
          | (congr 1; omega)
          | (rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1; omega)
      · rintro rfl
        refine ⟨⟨BitString.ofList_ofFn_append _ _, ?_⟩, ?_, ?_⟩
        · simp [List.getD_eq_getElem?_getD]
        · rw [← List.singleton_append, ← List.append_assoc,
            List.drop_left' (by simp), BitString.ofList_ofFn_append]
        · have hprefix : (List.ofFn key ++ colour :: List.ofFn t).length = 2 * k + 2 := by
            simp; omega
          rw [show List.ofFn key ++ colour :: (List.ofFn t ++ [b]) =
              (List.ofFn key ++ colour :: List.ofFn t) ++ [b] by simp,
            List.getD_eq_getElem?_getD, List.getElem?_append_right hprefix.le, hprefix,
            Nat.sub_self]
          rfl
    · simp only [hlen, ↓reduceIte, reduceCtorEq, false_iff, Prod.mk.injEq, true_and]
      rintro rfl
      simp at hlen
      omega
  encodeReply q := (labelCodec k).encodeReply q.tweak

end Garbling.CCR

/-- **Circular correlation robustness** of a hash family on words: the hash is evaluated in
polynomial time, a premise that the source does not impose, and its security condition is
[ZahurRosulekEvans2015] Definition 1 (§4.1, p. 10) read with `k`-bit tweaks, `(k + 2)`-bit labels
and tweak-unique uniform adversaries (module documentation). At every level `k` no uniform strict
oracle-PPT word distinguisher that asks each tweak at most once, at every level, tells the circular
oracle `(x, t, b) ↦ H(x + Δ, t) + bΔ` with `H = CCR.atLevel hash k` and `Δ = CCR.offset R` for a
uniform `(k + 1)`-bit `R` from a uniform random function, except with negligible advantage. -/
structure CircularCorrelationRobust (hash : List Bool → List Bool → List Bool) : Prop where
  /-- One deterministic machine evaluates the hash on the encoded label and tweak words. -/
  polyTime : ComputableInPolyTime (fun (label, tweak) => hash label tweak)
    (encPair encBits encBits) encBits
  /-- At level `k`, the keyed circular oracle under a uniform offset key and a uniform random
  function, both read through `CCR.codec k`, are indistinguishable for every uniform strict
  oracle-PPT word distinguisher that never repeats a tweak at any level. -/
  secure : Game.Indistinguishable
    (fun W k => ProbComp.eval (PRF.realExperiment
      (CCR.keyed (CCR.atLevel hash k) CCR.offset CCR.offset) ((CCR.codec k).adapt (W k []))))
    (fun W k => ProbComp.eval (PRF.idealExperiment ((CCR.codec k).adapt (W k []))))
    (fun W : OracleDistinguisher => IsOraclePPT encBool W ∧
      ∀ k, CCR.IsTweakUnique ((CCR.codec k).adapt (W k [])))

/-- **The assumption at the finite advantage.** Under circular correlation robustness, every
uniform strict oracle-PPT word distinguisher that never repeats a tweak has negligible finite
advantage `CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset` at level `k`: the level-`k`
advantage of the assumption's games is that finite advantage. -/
theorem CircularCorrelationRobust.negligible_advantage {hash : List Bool → List Bool → List Bool}
    (h : CircularCorrelationRobust hash) {W : OracleDistinguisher} (hW : IsOraclePPT encBool W)
    (hunique : ∀ k, CCR.IsTweakUnique ((CCR.codec k).adapt (W k []))) :
    Negligible fun k =>
      CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset ((CCR.codec k).adapt (W k [])) :=
  h.secure W ⟨hW, hunique⟩

end Cslib.Crypto
