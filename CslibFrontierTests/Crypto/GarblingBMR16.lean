/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.BMR16
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-! # BMR16 garbling of mixed-modulus circuits: checked instances

Clients of the BMR16 API under module encapsulation, with ordinary imports. A two-gate circuit
with a projection `ℤ₂ → ℤ₃` followed by an addition modulo `3`, evaluated by computation; the
number of ciphertexts of a projection gate; correctness, simulator correctness, legality of the
reduction, the privacy equality instantiated with injective tweaks and the algebraic helper
`advantage_realGame_simGame_le_of_mixedModulusCCR_of_reduction_mem` applied to it; the
mixed-modulus CCR games on an adversary that makes no query; and a legal one-query adversary
showing that the constant zero hash is not mixed-modulus CCR for any bound below `1 / 2`. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.GarblingBMR16

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Garbling.MixedModulus
  Cslib.Crypto.Garbling.BMR16

/-- Two sorts, of moduli `2` and `3`. -/
def μ : Fin 2 → ℕ := ![2, 3]

instance (i : Fin 2) : NeZero (μ i) := ⟨by fin_cases i <;> simp [μ]⟩

/-- One key coordinate per label. -/
def ℓ : Fin 2 → ℕ := fun _ => 1

/-- `y = x₀ + x₁ mod 3` for `x₀ ∈ ℤ₂` and `x₁ ∈ ℤ₃`: a projection `ℤ₂ → ℤ₃` lifts `x₀`, then an
addition modulo `3`. -/
def crossC : MixedModulusCircuit μ (Projection μ) [0, 1] [1] :=
  .proj (i := 0) (j := 1) .here (fun x => (x.val : ZMod (μ 1))) <|
    .add [.here, .there (.there .here)] <|
      .output (Env.cons .here PUnit.unit)

/-- The input `(x₀, x₁)`. -/
def input (x₀ : ZMod (μ 0)) (x₁ : ZMod (μ 1)) : Env (Residue μ) [0, 1] :=
  Env.cons x₀ (Env.cons x₁ PUnit.unit)

/-- The output `y`. -/
def output (y : ZMod (μ 1)) : Env (Residue μ) [1] := Env.cons y PUnit.unit

-- The circuit adds its inputs modulo `3`.
example : crossC.eval (input 1 1) = output 2 := rfl

example : crossC.eval (input 1 2) = output 0 := rfl

example : crossC.eval (input 0 2) = output 2 := rfl

example : crossC.size = 2 := rfl

-- The garbled tables of the circuit: one label of sort `1` per non-zero colour of the projection's
-- input in `ℤ₂`, so `2 - 1 = 1` ciphertext; the addition gate has none.
example : Tables ℓ crossC = (({c : ZMod (μ 0) // c ≠ 0} → Label μ ℓ 1) × PUnit) := rfl

example : Fintype.card {c : ZMod (μ 0) // c ≠ 0} = 1 := by decide

/-- A toy tweakable hash. It is not correlation robust; it only makes the statements concrete. -/
def toyH : MixedModulusHash (Fin 2) μ ℓ := fun t _ W j =>
  (fun _ => ((W.2.val + t.val : ℕ) : ZMod (μ j)), ((2 * W.2.val + t.val + 1 : ℕ) : ZMod (μ j)))

/-- Gate `k` has tweak `k mod 2`. -/
def tw (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by decide)⟩

theorem tw_injOn : Set.InjOn tw (Set.Iio crossC.size) := by
  intro a ha b hb h
  change a < 2 at ha
  change b < 2 at hb
  have h' := congrArg Fin.val h
  simp only [tw, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact h'

-- Correctness and simulator correctness use neither choice nor any other axiom beyond these two.
/--
info: 'Cslib.Crypto.Garbling.BMR16.Garbled.run_ofKeys' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Garbled.run_ofKeys

/--
info: 'Cslib.Crypto.Garbling.BMR16.View.run_simulateWith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms View.run_simulateWith

-- Correctness, for every offset and zero labels.
example (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (E : Env (Label μ ℓ) [0, 1])
    (x : Env (Residue μ) [0, 1]) :
    (Garbled.ofKeys toyH tw δ crossC E).run toyH tw x = crossC.eval x :=
  Garbled.run_ofKeys toyH tw δ crossC E x

-- Simulated views decode to the requested output.
example (y : Env (Residue μ) [1]) (A : Env (Label μ ℓ) [0, 1]) (R : Tables ℓ crossC) :
    (simulateWith toyH tw crossC y A R).run toyH tw = y :=
  View.run_simulateWith toyH tw crossC y A R

-- The reduction is a legal mixed-modulus CCR adversary.
example (x : Env (Residue μ) [0, 1]) (D : View ℓ crossC → ProbComp Bool) :
    (reduction toyH tw crossC x D).IsLegal :=
  reduction_isLegal toyH tw crossC x D tw_injOn

-- The privacy theorem applies to the circuit with injective tweaks, for every distinguisher; with
-- the toy hash the right side is not small.
example (x : Env (Residue μ) [0, 1]) (D : View ℓ crossC → ProbComp Bool) :
    Game.advantage (realGame toyH tw crossC x D) (simGame toyH tw crossC x D) =
      ccrAdvantage toyH (reduction toyH tw crossC x D) :=
  advantage_realGame_simGame toyH tw crossC x D tw_injOn

-- The algebraic helper: for every hash, a `MixedModulusCCR` bound `ε` against a class containing
-- the reduction bounds the advantage of the distinguisher by `ε`.
example (H : MixedModulusHash (Fin 2) μ ℓ) (x : Env (Residue μ) [0, 1])
    (D : View ℓ crossC → ProbComp Bool) {𝒟 : Set (CCRAdversary (Fin 2) μ ℓ)} {ε : NNReal}
    (hH : MixedModulusCCR H 𝒟 ε) (hD : reduction H tw crossC x D ∈ 𝒟) :
    Game.advantage (realGame H tw crossC x D) (simGame H tw crossC x D) ≤ ε :=
  advantage_realGame_simGame_le_of_mixedModulusCCR_of_reduction_mem H tw crossC x D tw_injOn hH hD

-- An adversary that makes no query is legal and has advantage zero, so `MixedModulusCCR` with
-- bound `0` is satisfiable for that class.
example (b : Bool) : CCRAdversary.IsLegal (pure b : CCRAdversary (Fin 2) μ ℓ) := by
  rintro requests b' ⟨rfl, -⟩
  simp [CCRLegal]

example (b : Bool) : MixedModulusCCR toyH {pure b} 0 := by
  rintro B rfl -
  have h₁ : ccrRealGame toyH (pure b : CCRAdversary (Fin 2) μ ℓ) = PMF.pure b := by
    simp only [ccrRealGame, OracleComp.interpret_pure, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_const]
  have h₂ : ccrIdealGame (pure b : CCRAdversary (Fin 2) μ ℓ) = PMF.pure b := by
    simp only [ccrIdealGame, OracleComp.interpret_pure, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_const]
  rw [ccrAdvantage, h₁, h₂, Game.advantage_self]

/-- An adversary asking a query with multiplier `a = 0`. -/
def zeroQuery : CCRAdversary (Fin 2) μ ℓ := do
  let _ ← ProbOracleComp.query (spec := ccrSpec (Fin 2) μ ℓ) (0, ⟨0, 0, 0, 0, 0⟩)
  pure true

-- It is not legal.
example : ¬ zeroQuery.IsLegal := fun h =>
  (h [.inr (0, ⟨0, 0, 0, 0, 0⟩)] true ⟨0, [], rfl, rfl, rfl⟩).1 (0, ⟨0, 0, 0, 0, 0⟩) (by simp) rfl

/-- An adversary that asks two queries differing only in `b` when two private coins differ. -/
def twoCoins : CCRAdversary (Fin 2) μ ℓ := do
  let r₁ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let r₂ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  if r₁ = r₂ then pure true else do
    let _ ← ProbOracleComp.query (spec := ccrSpec (Fin 2) μ ℓ) (0, ⟨0, 0, 0, 1, 0⟩)
    let _ ← ProbOracleComp.query (spec := ccrSpec (Fin 2) μ ℓ) (0, ⟨0, 0, 0, 1, 1⟩)
    pure true

-- It is not legal: along the run whose coins differ, two calls with the same coin request get
-- different replies.
example : ¬ twoCoins.IsLegal := by
  intro h
  have hrun : IsRun twoCoins [.inl 1, .inl 1, .inr (0, ⟨0, 0, 0, 1, 0⟩), .inr (0, ⟨0, 0, 0, 1, 1⟩)]
      true := ⟨0, _, rfl, 1, _, rfl, 0, _, rfl, 0, _, rfl, rfl, rfl⟩
  have heq := (h _ _ hrun).2 (0, ⟨0, 0, 0, 1, 0⟩) (by simp) (0, ⟨0, 0, 0, 1, 1⟩) (by simp) rfl
  revert heq
  decide

/-! ### The zero hash is not mixed-modulus CCR

The real oracle answers `(g, X, a, b)` with `H(g, X + a Δ_i) + b Δ_j`. For the zero hash and
`b = 0` this is `0`, whatever the offsets, while the ideal oracle's answer has a uniform colour. -/

/-- The hash that ignores its tweak and label and returns the zero label. -/
def zeroH : MixedModulusHash (Fin 2) μ ℓ := fun _ _ _ _ => 0

/-- The query `(g, X, a, b) = (0, 0, 1, 0)` from sort `0` to sort `0`. -/
private abbrev colourQuery : Fin 2 × CCRInput μ ℓ := (0, ⟨0, 0, 0, 1, 0⟩)

/-- Ask `colourQuery` once and accept when the colour of the reply is `0`. -/
def colourTest : CCRAdversary (Fin 2) μ ℓ := do
  let reply ← ProbOracleComp.query (spec := ccrSpec (Fin 2) μ ℓ) colourQuery
  pure (decide (reply.2 = 0))

/-- One query with `a = 1` is legal. -/
private theorem colourTest_isLegal : colourTest.IsLegal := by
  rintro requests b ⟨r, rest, rfl, rfl, -⟩
  exact ⟨by decide, by simp⟩

/-- Against the zero hash the real reply is `0`, so `colourTest` always accepts. -/
private theorem ccrRealGame_zeroH_colourTest :
    ccrRealGame zeroH colourTest = PMF.pure true := by
  simp only [ccrRealGame, ccrOracle, zeroH, CCRInput.b, zero_add, colourTest, Fin.isValue,
    bind_pure_comp, OracleComp.interpret_map, ProbOracleComp.interpret_query, zero_smul, map_pure,
    Prod.snd_zero, decide_true, ProbComp.eval_map, ProbComp.eval_uniform]
  exact PMF.map_const _ _

/-- The ideal reply is uniform, so its colour is `0` with probability `1 / 2`. -/
private theorem ccrIdealGame_colourTest :
    ccrIdealGame colourTest = Probability.PMF.uniformOfFintype Bool := by
  simp only [ccrIdealGame, colourTest, Fin.isValue, bind_pure_comp, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, map_pure, ProbComp.eval_map, ProbComp.eval_uniform]
  have h0 : (Probability.PMF.uniformOfFintype (Fin 2 → CCRTable μ ℓ)).map (fun f => f 0) =
      Probability.PMF.uniformOfFintype (CCRTable μ ℓ) := by
    rw [← @Probability.PMF.pi_uniformOfFintype (Fin 2) _ (fun _ => CCRTable μ ℓ) _ _
      (fun _ => inferInstance) _]
    exact Probability.PMF.pi_map_eval _ _
  have h1 : (Probability.PMF.uniformOfFintype (CCRTable μ ℓ)).map (fun t => t colourQuery.2) =
      Probability.PMF.uniformOfFintype (Label μ ℓ 0) := by
    rw [← Probability.PMF.pi_uniformOfFintype (α := fun r : CCRInput μ ℓ => Label μ ℓ r.target)]
    exact Probability.PMF.pi_map_eval _ _
  have h2 : (Probability.PMF.uniformOfFintype (ZMod (μ 0))).map (fun c => decide (c = 0)) =
      Probability.PMF.uniformOfFintype Bool :=
    Probability.PMF.uniformOfFintype_map_equiv
      (⟨fun c => decide (c = 0), fun b => if b then 0 else 1, fun c => by revert c; decide,
        fun b => by revert b; decide⟩ : ZMod (μ 0) ≃ Bool)
  rw [show (fun f : Fin 2 → CCRTable μ ℓ => decide ((f 0 colourQuery.2).2 = 0)) =
      (fun c => decide (c = 0)) ∘ Prod.snd ∘ (fun t : CCRTable μ ℓ => t colourQuery.2) ∘
        (fun f => f 0) from rfl, ← PMF.map_comp, ← PMF.map_comp, ← PMF.map_comp, h0, h1,
    Probability.PMF.uniformOfFintype_prod_map_snd, h2]

/-- **`MixedModulusCCR` is not vacuous**: the zero hash is not mixed-modulus CCR with any bound
below `1 / 2` for a class containing the legal one-query adversary `colourTest`. -/
theorem not_mixedModulusCCR_zeroH {𝒟 : Set (CCRAdversary (Fin 2) μ ℓ)} (hD : colourTest ∈ 𝒟)
    {ε : NNReal} (hε : ε < 2⁻¹) : ¬ MixedModulusCCR zeroH 𝒟 ε := by
  intro h
  have hadv := h colourTest hD colourTest_isLegal
  rw [ccrAdvantage, ccrRealGame_zeroH_colourTest, ccrIdealGame_colourTest,
    Game.advantage_pure_true_left] at hadv
  refine hε.not_ge (le_of_eq_of_le ?_ hadv)
  simp [Game.failProbability, Probability.PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat]

end CslibFrontierTests.GarblingBMR16
