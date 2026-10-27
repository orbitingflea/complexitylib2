/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Subexponential model counting for bounded-width CNF formulas

For every fixed clause width `k`, one native machine computes the number of satisfying
assignments `CNF.modelCount φ` of every formula `φ` with clauses of at most `k` literals. It
runs in time `2 ^ (A * interpolationScale n)` times a polynomial in the encoding length, where
`n = φ.numVars`, and in space polynomial in the encoding length.

This restates `CountingNativeEndpoint.exists_declaredCounter` on the plain formula: the machine
relabels the variables densely, declares their number, and runs the declared counter. The
resource bounds are folded into `ComputableInO`.

## Main results

* `CountingNativeEndpoint.exists_modelCounter`: the bounded-width model counter.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Proposition 6.4.
-/

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- Dense relabeling followed by declaring the number of variables. -/
private theorem computableInPolyTime_declareDense :
    ComputableInPolyTime (fun φ : CNF ℕ => (φ.denseRelabel.numVars, φ.denseRelabel)) encCNF
      (encPair encUnary encCNF) := by
  have h : ComputableInPolyTime (fun ψ : CNF ℕ => (ψ.numVars, ψ)) encCNF
      (encPair encUnary encCNF) := by fun_prop
  exact h.comp SAT.computableInPolyTime_denseRelabel

/-- **Subexponential bounded-width model counting.** For each width `k`, one machine computes
`φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in time
`2 ^ (A * interpolationScale φ.numVars)` times a polynomial in the encoding length, and in
polynomial space. -/
public theorem exists_modelCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ := exists_declaredCounter k
  set g : CNF ℕ → ℕ × CNF ℕ := fun φ => (φ.denseRelabel.numVars, φ.denseRelabel)
  obtain ⟨d, _, hd⟩ :=
    ComputableTidilyInPolyTime.exists_degree computableInPolyTime_declareDense.tidy
  obtain ⟨p, q, hp⟩ := computableInPolyTime_declareDense.polyBounded_length.exists_le
  refine ⟨fun φ => count (g φ), A, q * e + d, q * b + d, fun φ hφ => ?_,
    (hcount.comp (ComputableInO.of_tidy hd.inO)).mono
      (c * (p + 1) ^ e + 1 + c + a * (p + 1) ^ b + 1) (fun φ => ?_) (fun φ => ?_)⟩
  · have hw : ∀ cl ∈ φ.denseRelabel, cl.length ≤ k :=
      (CNF.all_length_le_denseRelabel φ).mpr hφ
    have hv : CNF.validDeclaredInput k φ.denseRelabel.numVars φ.denseRelabel = true :=
      CNF.validDeclaredInput_eq_true_iff.mpr
        ⟨hw, by rw [CNF.vars_denseRelabel_toFinset, CNF.numVars_denseRelabel]⟩
    simp only [g]
    rw [hspec, hv]
    simp only [↓reduceIte, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel]
  all_goals
    set Y := (encCNF φ).length + 1 with hY
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g φ)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g φ)).length ≤ p * Y ^ q := hp φ
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
  · -- time
    set X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars) with hX
    set N := ⌈X⌉₊
    have hXN : X ≤ N := Nat.le_ceil X
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ e ≤ (p + 1) ^ e * Y ^ (q * e) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ e := Nat.pow_le_pow_left hlen e
        _ = _ := by rw [mul_pow, pow_mul]
    have hTg : T (g φ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by
      have h : (T (g φ) : ℝ) ≤
          c * (X * (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e) + c := by
        have h := hT (g φ)
        rwa [show (g φ).1 = φ.numVars from CNF.numVars_denseRelabel φ] at h
      have hpowR : (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e ≤
          (p + 1) ^ e * Y ^ (q * e) := by exact_mod_cast hpow
      have h1 := mul_le_mul hXN hpowR (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
      have : (T (g φ) : ℝ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by nlinarith
      exact_mod_cast this
    have hqe : Y ^ (q * e) ≤ Y ^ (q * e + d) := Nat.pow_le_pow_right hY1 (by omega)
    have hd' : Y ^ d ≤ N * Y ^ (q * e + d) :=
      (Nat.pow_le_pow_right hY1 (by omega)).trans (Nat.le_mul_of_pos_left _ hN1)
    have hmul := Nat.mul_le_mul_left (c * (p + 1) ^ e) (Nat.mul_le_mul_left N hqe)
    change Y ^ d + T (g φ) ≤ _ * (N * Y ^ (q * e + d) + 1)
    generalize N * Y ^ (q * e + d) = Z at hd' hmul ⊢
    generalize c * (p + 1) ^ e = u at hTg hmul ⊢
    generalize a * (p + 1) ^ b = v
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]
  · -- space
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ b ≤ (p + 1) ^ b * Y ^ (q * b) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ b := Nat.pow_le_pow_left hlen b
        _ = _ := by rw [mul_pow, pow_mul]
    have hSg : S (g φ) ≤ a * (p + 1) ^ b * Y ^ (q * b + d) :=
      (hS (g φ)).trans (by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left a (hpow.trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hY1 (by omega)))))
    have hd' : Y ^ d ≤ Y ^ (q * b + d) := Nat.pow_le_pow_right hY1 (by omega)
    change Y ^ d + S (g φ) ≤ _ * (Y ^ (q * b + d) + 1)
    generalize Y ^ (q * b + d) = Z at hSg hd' ⊢
    generalize a * (p + 1) ^ b = v at hSg ⊢
    generalize c * (p + 1) ^ e = u
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]

end Cslib.Complexity.CountingNativeEndpoint
