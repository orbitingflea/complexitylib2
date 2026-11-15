/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Primitives.PRF.RandomOracleModel
public import CslibFrontier.Probability.PMF.UniformExtend
import CslibFrontier.Probability.PMF.Map

/-!
# Pseudorandom functions in the random-oracle model: checked instances

An ordinary `module` client of `CslibFrontier.Crypto.Primitives.PRF.RandomOracleModel`
([BonehShoup2023], Section 8.10.2, Attack Game 8.4 and Theorem 8.9) and of
`CslibFrontier.Probability.PMF.UniformExtend`.

* The budget counts random-oracle queries only: a program with one `F`-query and one oracle query
  has budget `1`.
* Injectivity of `encode` in the input is needed: with one key and `encode` constant in the input,
  an adversary that compares `F` at two inputs makes no random-oracle query and has advantage
  exactly `1 / 2`, where the bound of Theorem 8.9 would be `0 / 1`.
* Separation of the keys by `encode` is needed: when every key is sent to the one oracle point,
  one `F`-query and one oracle query give advantage exactly `1 / 2` for every key type, and the
  conclusion `≤ 1 / 3` is false for three keys.
* A large key space is needed: with one key the same pairing is injective, the theorem gives the
  bound `1 / 1`, and the advantage is `1 / 2`.
* With `Bool` keys and `Prod.mk`, the advantage is `0` without random-oracle queries, however many
  `F`-queries the adversary makes, and at most `1 / 2` with one; with two-bit keys and `keyAppend`
  it is at most `1 / 4` with one. `keyAppend 2 1` appends the word `[true]` to the key
  `[true, false]`, and the asymptotic statement applies to `n`-bit keys and adversaries that make
  no query.
* The game restricts to Attack Game 4.2, and a budget on all queries bounds the random-oracle
  queries.
* Resampling along a map, at an injective and at a non-injective map.
-/

public section

namespace CslibFrontierTests.Crypto.RandomOraclePRF

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PRF
open Cslib.Probability.PMF (uniformOfFintype)
open scoped NNReal ENNReal

/-! ### The budget counts random-oracle queries only -/

/-- One `F`-query and one `O`-query: one random-oracle query. -/
example {X Y M T : Type} (x : X) (m : M) (g : Y → T → Bool) :
    ROAdversary.IsOracleQueryBounded (X := X) (Y := Y) (M := M) (T := T)
      (do
        let y ← ProbOracleComp.query (spec := ROSpec X Y M T) (Sum.inl x)
        let t ← ProbOracleComp.query (spec := ROSpec X Y M T) (Sum.inr m)
        pure (g y t) : ProbOracleComp (ROSpec X Y M T) Bool) 1 := by
  have h := (ProbOracleComp.isCostBounded_query (spec := ROSpec X Y M T)
    (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl x)).bind fun y =>
      (ProbOracleComp.isCostBounded_query (spec := ROSpec X Y M T)
        (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inr m)).bind fun t =>
          OracleComp.IsCostBounded.pure (g y t) 0
  simpa using h

/-! ### Injectivity of `encode` in the input is needed -/

/-- Ask for `F` at both inputs and compare. -/
def collisionTest : ProbOracleComp (ROSpec Bool Bool Unit Bool) Bool := do
  let a ← ProbOracleComp.query (Sum.inl false)
  let b ← ProbOracleComp.query (Sum.inl true)
  pure (a == b)

/-- `collisionTest` makes no random-oracle query. -/
theorem collisionTest_isOracleQueryBounded :
    ROAdversary.IsOracleQueryBounded collisionTest 0 := by
  have h := (ProbOracleComp.isCostBounded_query (spec := ROSpec Bool Bool Unit Bool)
    (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl false)).bind fun a =>
      (ProbOracleComp.isCostBounded_query (spec := ROSpec Bool Bool Unit Bool)
        (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl true)).bind fun b =>
          OracleComp.IsCostBounded.pure (a == b) 0
  simpa [collisionTest] using h

/-- With one key and `encode` constant in the input, an adversary making no random-oracle query has
advantage `1 / 2`, above the bound `0 / 1` that Theorem 8.9 would give. -/
theorem roAdvantage_collisionTest :
    (roAdvantage (Key := Unit) (prependKey fun _ _ => ()) collisionTest : ℝ) = 1 / 2 := by
  have hreal : ProbComp.eval (roRealExperiment (Key := Unit) (prependKey fun _ _ => ())
      collisionTest) = PMF.pure true := by
    rw [eval_roRealExperiment]
    simp [collisionTest, ProbOracleComp.query]
  have hideal : ProbComp.eval (roIdealExperiment collisionTest) =
      (uniformOfFintype (Bool → Bool)).map fun f => f false == f true := by
    rw [eval_roIdealExperiment]
    simp [collisionTest, ProbOracleComp.query, PMF.map, Function.comp_def]
  have hcard : Nat.card {f : Bool → Bool // (f false == f true) = true} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [roAdvantage, hreal, hideal, Game.coe_advantage_pure_true_left,
    PMF.uniformOfFintype_map_apply, hcard]
  simp
  norm_num

/-! ### Separation of the keys by `encode` is needed -/

/-- Ask for `F` and for the oracle at the only points and compare. -/
def sharedPointTest : ProbOracleComp (ROSpec Unit Bool Unit Bool) Bool := do
  let a ← ProbOracleComp.query (Sum.inl ())
  let b ← ProbOracleComp.query (Sum.inr ())
  pure (a == b)

/-- `sharedPointTest` makes one random-oracle query. -/
theorem sharedPointTest_isOracleQueryBounded :
    ROAdversary.IsOracleQueryBounded sharedPointTest 1 := by
  have h := (ProbOracleComp.isCostBounded_query (spec := ROSpec Unit Bool Unit Bool)
    (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl ())).bind fun a =>
      (ProbOracleComp.isCostBounded_query (spec := ROSpec Unit Bool Unit Bool)
        (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inr ())).bind fun b =>
          OracleComp.IsCostBounded.pure (a == b) 0
  simpa [sharedPointTest] using h

/-- When all keys share the one oracle point, one random-oracle query gives advantage `1 / 2`,
however many keys there are. -/
theorem roAdvantage_sharedPointTest (Key : Type) [Fintype Key] [Nonempty Key] :
    (roAdvantage (Key := Key) (prependKey fun _ _ => ()) sharedPointTest : ℝ) = 1 / 2 := by
  have hreal : ProbComp.eval (roRealExperiment (Key := Key) (prependKey fun _ _ => ())
      sharedPointTest) = PMF.pure true := by
    rw [eval_roRealExperiment]
    simp [sharedPointTest, ProbOracleComp.query]
  have hideal : ProbComp.eval (roIdealExperiment sharedPointTest) =
      (uniformOfFintype ((Unit → Bool) × (Unit → Bool))).map fun p => p.2 () == p.1 () := by
    rw [eval_roIdealExperiment]
    have h := PMF.uniformOfFintype_bind_bind_fst_equiv
      (Equiv.prodPUnit _ : ((Unit → Bool) × (Unit → Bool)) × Unit ≃ _).symm
      fun p : (Unit → Bool) × (Unit → Bool) => PMF.pure (p.2 () == p.1 ())
    simpa [sharedPointTest, ProbOracleComp.query, PMF.map, Function.comp_def] using h
  have hcard : Nat.card {p : (Unit → Bool) × (Unit → Bool) // (p.2 () == p.1 ()) = true} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [roAdvantage, hreal, hideal, Game.coe_advantage_pure_true_left,
    PMF.uniformOfFintype_map_apply, hcard]
  simp
  norm_num

/-- With three keys the conclusion of Theorem 8.9 is false for this adversary: `1 / 2` is above
`1 / 3`. -/
example : ¬ ((roAdvantage (Key := Fin 3) (prependKey fun _ _ => ()) sharedPointTest : ℝ) ≤
    (1 : ℕ) / Fintype.card (Fin 3)) := by
  rw [roAdvantage_sharedPointTest]
  norm_num

/-! ### A large key space is needed -/

/-- With one key the pairing is injective and Theorem 8.9 applies, with bound `1 / 1`. -/
example : (roAdvantage (Key := Unit) (prependKey fun _ _ => ()) sharedPointTest : ℝ) ≤
    (1 : ℕ) / Fintype.card Unit :=
  roAdvantage_prependKey_le (fun _ _ _ _ _ => ⟨rfl, rfl⟩) sharedPointTest_isOracleQueryBounded

/-- The advantage is then `1 / 2` with one random-oracle query: no bound independent of the number
of keys holds. -/
example : (roAdvantage (Key := Unit) (prependKey fun _ _ => ()) sharedPointTest : ℝ) = 1 / 2 :=
  roAdvantage_sharedPointTest Unit

/-! ### The theorem at small instances -/

/-- Without random-oracle queries the two experiments have the same law, however many `F`-queries
the adversary makes. -/
example {A : ROAdversary Bool Bool (Bool × Bool) Bool} (hA : A.IsOracleQueryBounded 0) :
    roAdvantage (Key := Bool) (prependKey Prod.mk) A = 0 := by
  have h := roAdvantage_prependKey_le (encode := Prod.mk) (fun _ _ _ _ h => Prod.mk.inj h) hA
  rw [Nat.cast_zero, zero_div] at h
  exact le_antisymm (NNReal.coe_le_coe.mp h) zero_le

/-- With one random-oracle query and two keys the advantage is at most `1 / 2`. -/
example {A : ROAdversary Bool Bool (Bool × Bool) Bool} (hA : A.IsOracleQueryBounded 1) :
    (roAdvantage (Key := Bool) (prependKey Prod.mk) A : ℝ) ≤ 1 / 2 := by
  have h := roAdvantage_prependKey_le (encode := Prod.mk) (fun _ _ _ _ h => Prod.mk.inj h) hA
  simpa using h

/-! ### The book's bit strings -/

open Cslib.BitString in
/-- The key `[true, false]` followed by the word `[true]`. -/
example : (keyAppend 2 1 ![true, false] ⟨[true], mem_shortWords.mpr (by simp)⟩).1 =
    [true, false, true] := by
  simp

open Cslib.BitString in
/-- Two-bit keys: one random-oracle query gives advantage at most `1 / 4`. -/
example {A : ROAdversary (shortWords 1) Bool (shortWords (2 + 1)) Bool}
    (hA : A.IsOracleQueryBounded 1) :
    (roAdvantage (prependKey (keyAppend 2 1)) A : ℝ) ≤ 1 / 4 :=
  (roAdvantage_prependKey_keyAppend_le 2 1 hA).trans_eq (by norm_num)

open Cslib.BitString in
/-- The hypotheses of the asymptotic statement can be met: `n`-bit keys and adversaries that make
no query. -/
example : Negligible fun n => roAdvantage (T := Bool) (prependKey (keyAppend n 1))
    (pure true : ProbOracleComp (ROSpec (shortWords 1) Bool (shortWords (n + 1)) Bool) Bool) :=
  negligible_roAdvantage_prependKey_keyAppend (fun _ => le_rfl) (fun _ => 1)
    (Q := fun _ => 0) ⟨0, Filter.Eventually.of_forall fun _ => Nat.zero_le _⟩
    fun _ => OracleComp.IsCostBounded.pure true 0

/-! ### Relation to the game without a random oracle, and to the total budget -/

/-- A keyed function that ignores the oracle has its ordinary PRF advantage. -/
example (F : Bool → Bool → Bool) (A : Adversary Bool Bool) :
    roAdvantage (M := Unit) (T := Bool) (fun _ => F)
      (ProbOracleComp.simulate (fun x => ProbOracleComp.query (Sum.inl x)) A) = advantage F A :=
  roAdvantage_const_simulate F A

/-- Three queries in all are at most three random-oracle queries. -/
example {A : ROAdversary Bool Bool Unit Bool} (h : ProbOracleComp.IsQueryBounded A 3) :
    A.IsOracleQueryBounded 3 :=
  .of_isQueryBounded h

/-! ### Resampling along a map -/

/-- Overwrite the value at `true` by a fresh uniform bit. -/
example (g : (Bool → Bool) → PMF Bool) :
    ((uniformOfFintype (Bool → Bool)).bind fun f =>
      (uniformOfFintype (Unit → Bool)).bind fun t =>
        g (Function.extend (fun _ : Unit => true) t f)) = (uniformOfFintype (Bool → Bool)).bind g :=
  PMF.uniformOfFintype_bind_bind_extend _ g

/-- The map need not be injective. -/
example (g : (Unit → Bool) → PMF Bool) :
    ((uniformOfFintype (Unit → Bool)).bind fun f =>
      (uniformOfFintype (Bool → Bool)).bind fun t =>
        g (Function.extend (fun _ : Bool => ()) t f)) = (uniformOfFintype (Unit → Bool)).bind g :=
  PMF.uniformOfFintype_bind_bind_extend _ g

end CslibFrontierTests.Crypto.RandomOraclePRF
