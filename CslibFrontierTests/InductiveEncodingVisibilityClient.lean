/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (inductive-encoding visibility regression tests)

public import CslibFrontierTests.InductiveEncodingVisibility

/-! Import-side semantics, scoped automation and export guards for `enc_inductive`. -/

open Turing.MultiTapeTM CslibFrontierTests.InductiveEncodingVisibility

-- Independent field bounds are retained after import.
example {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} {g : α → List Bool} {h : α → Bool} {S₀ S₁ S₂ : α → ℕ}
    (hf : ComputableInSpace f enc encUnary S₀)
    (hg : ComputableInSpace g enc encBits S₁)
    (hh : ComputableInSpace h enc encBool S₂) :
    ComputableInSpace (fun a => Message.triple (f a) (g a) (h a)) enc eMessage
      (fun a => S₀ a + (S₁ a + S₂ a)) := by
  fun_prop

example {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} {g : α → List Bool} {h : α → Bool}
    (hf : ComputableInPolyTime f enc encUnary)
    (hg : ComputableInPolyTime g enc encBits)
    (hh : ComputableInPolyTime h enc encBool) :
    ComputableInPolyTime (fun a => Message.triple (f a) (g a) (h a)) enc eMessage := by
  fun_prop

example : ComputableInDegree eMessage_triple_matches eMessage encBool 1 0 := by fun_prop
example : ComputableInDegree eMessage_triple_payload? eMessage
    (encOption (encPair encUnary (encPair encBits encBool))) 1 1 := by fun_prop
example : ComputableInDegree eMessage_triple_field0? eMessage (encOption encUnary) 1 1 := by
  fun_prop
example : ComputableInDegree eMessage_triple_field1? eMessage (encOption encBits) 1 1 := by
  fun_prop
-- Field 2 requires two dropFrame operations, unlike the two-field regression.
example : ComputableInDegree eMessage_triple_field2? eMessage (encOption encBool) 1 1 := by
  fun_prop
example : ComputableInPolyTime (fun p : Unit × Message => eMessage_triple_field2? p.2)
    (encPair encUnit eMessage) (encOption encBool) :=
  eMessage_triple_field2?_polyTime.comp
    (ComputableInDegree.snd encUnit eMessage).computableInPolyTime

-- Both output-degree zero matchers and optional projections use the shared linear lift.
example : ComputableInSpace eMessage_triple_matches eMessage encBool
    (fun v => (eMessage v).length) := by fun_prop
example : ComputableInO eMessage_triple_field2? eMessage (encOption encBool)
    (fun v => (eMessage v).length) (fun v => (eMessage v).length) := by fun_prop
example : ComputableInPolyTime eMessage_triple_matches eMessage encBool := by fun_prop

-- Unknown inputs use the semantic API, with no unfolding or constructor case split.
example (v : Message) (n : ℕ) (bits : List Bool) (b : Bool) :
    eMessage_triple_payload? v = some (n, bits, b) ↔ v = .triple n bits b :=
  eMessage_triple_payload?_eq_some_iff v (n, bits, b)
example (v : Message) :
    eMessage_triple_matches v = true ↔
      ∃ a : ℕ × List Bool × Bool, v = .triple a.1 a.2.1 a.2.2 :=
  eMessage_triple_matches_iff v
example (v : Message) (h : eMessage_triple_matches v = true) :
    ∃ a, eMessage_triple_payload? v = some a :=
  (eMessage_triple_payload?_range v).mpr h
example (v : Message) : eMessage_idle_payload? v = some () ↔ v = .idle :=
  eMessage_idle_payload?_eq_some_iff v ()
example (v : Message) (bits : List Bool) :
    eMessage_word_payload? v = some bits ↔ v = .word bits :=
  eMessage_word_payload?_eq_some_iff v bits
example : eMessage_word_payload? (.word []) = some [] := rfl
example : eMessage_word_payload? .idle = none := rfl
example (n : ℕ) (bits : List Bool) (b : Bool) :
    eMessage_triple_field2? (.triple n bits b) = some b := rfl

-- Branch clocks/degrees are unrelated; the elimination rule is explicitly applied.
example {π ε : Type} {encP : π ↪ List Bool} {encE : ε ↪ List Bool}
    {f : π × Unit → ε} {g : π × List Bool → ε}
    {h : π × (ℕ × List Bool × Bool) → ε}
    (hf : ComputableInPolyTime f (encPair encP encUnit) encE)
    (hg : ComputableInPolyTime g (encPair encP encBits) encE)
    (hh : ComputableInPolyTime h
      (encPair encP (encPair encUnary (encPair encBits encBool))) encE) :
    ComputableInPolyTime (fun p : π × Message =>
      eMessage_elim p.2 (fun a => f (p.1, a)) (fun a => g (p.1, a)) (fun a => h (p.1, a)))
      (encPair encP eMessage) encE := eMessage_elim_polyTime hf hg hh

-- An actual imported environment lookup guards the complete exported family.
run_cmd do
  let env ← Lean.getEnv
  let mut suffixes := ["", "Payload", "_apply", "_toSum", "_toSum_deg", "_elim",
    "_elim_inO", "_elim_inSpace", "_elim_polyTime"]
  for c in ["idle", "word", "triple"] do
    suffixes := suffixes ++ ["_inO", "_inSpace", "_polyTime"].map ("_" ++ c ++ ·)
    suffixes := suffixes ++ ["_matches_iff", "_payload?_eq_some_iff", "_payload?_range"].map
      ("_" ++ c ++ ·)
    let projections := ["_matches", "_payload?"] ++
      (if c == "triple" then ["_field0?", "_field1?", "_field2?"]
       else if c == "word" then ["_field0?"] else [])
    for p in projections do
      suffixes := suffixes ++ ["", "_deg", "_inO", "_inSpace", "_polyTime"].map
        ("_" ++ c ++ p ++ ·)
      if p != "_matches" then
        suffixes := suffixes ++ ["_" ++ c ++ p ++ "_isSome"]
  for suffix in suffixes do
    let name := (`CslibFrontierTests.InductiveEncodingVisibility.eMessage).appendAfter suffix
    unless env.contains name do
      throwError "enc_inductive did not export {name}"
