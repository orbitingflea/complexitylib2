/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.OPRF.DiffieHellman
public import Mathlib.Algebra.Field.ZMod

/-!
# Diffie–Hellman oblivious pseudorandom functions: checked instances and hypothesis probes

An ordinary `module` client of `CslibFrontier.Crypto.Protocols.OPRF.DiffieHellman`
([BonehShoup2023], Section 11.6.3, pp. 454–456):

* In `ZMod 3` with generator `1`, the nonzero hashed inputs `2` and `1` induce the same `OPRF1`
  message distribution (`uniformOfFintype_bind_units_smul_of_ne_zero`).
* In `ZMod 5` with generator `1`, `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero` applies with
  `d v = 2`.
* `h ≠ 0` is required in `uniformOfFintype_bind_units_smul_of_ne_zero`: in `ZMod 3`, `ρ • 0` is
  always `0`, which `ρ • 1` never is.
* Primality of `q` is required in `uniformOfFintype_bind_units_smul_of_ne_zero`: in `ZMod 4` with
  generator `1`, the input `2` is nonzero yet `ρ • 2 = 2` for every unit `ρ`, whereas `ρ • 1` can
  be `1`.
* `g` generating the group is required in `uniformOfFintype_bind_maskedBlind`: in `ZMod 2` with
  `g = 0`, `maskedBlind 0 1 τ 1` is always `1`, whereas `τ • 0` is always `0`.
* `d v ≠ 0` is required in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in `ZMod 3`, an
  honest sender (`d = 0`) makes the receiver compute `k • h`, which `k • h + ρ • g` never is.
* Primality of `q` is required in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in
  `ZMod 4` with `g = 1`, `d _ = 2`, and `k = h = 0`, the receiver always computes `2`, whereas
  `0 • 0 + ρ • 1` is never `2`.
-/

public section

namespace CslibFrontierTests.Crypto.OPRF

open Cslib Cslib.Probability Cslib.Crypto.Protocols.OPRF

/-- The hypotheses of `uniformOfFintype_bind_units_smul_of_ne_zero` hold in `ZMod 3` with generator
`1`: the nonzero inputs `2` and `1` give the sender of `OPRF1` the same view. -/
example (f : ZMod 3 → PMF Bool) :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => f (ρ • (2 : ZMod 3))) =
      (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => f (ρ • (1 : ZMod 3)) :=
  uniformOfFintype_bind_units_smul_of_ne_zero (g := (1 : ZMod 3)) (h := (2 : ZMod 3))
    (fun c => ⟨c, by simp⟩) (by decide) f

/-- The hypotheses of `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero` hold in `ZMod 5` with
generator `1` and deviating offset `d v = 2`. -/
example (f : ZMod 5 → ZMod 5 → PMF Bool) :
    ((PMF.uniformOfFintype (ZMod 5)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 5)).bind fun τ =>
        f (maskedBlind (1 : ZMod 5) ρ τ (3 : ZMod 5))
          (maskedUnblind ((2 : ZMod 5) • (1 : ZMod 5)) ρ τ
            ((2 : ZMod 5) • maskedBlind (1 : ZMod 5) ρ τ (3 : ZMod 5) + 2))) =
      (PMF.uniformOfFintype (ZMod 5)).bind fun τ => (PMF.uniformOfFintype (ZMod 5)ˣ).bind fun ρ =>
        f (τ • (1 : ZMod 5)) ((2 : ZMod 5) • (3 : ZMod 5) + ρ • (1 : ZMod 5)) := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact uniformOfFintype_bind_maskedUnblind_add_of_ne_zero (g := (1 : ZMod 5))
    (fun c => ⟨c, by simp⟩) 2 3 (fun _ => 2) (fun _ => h2) f

/-- `h ≠ 0` is needed in `uniformOfFintype_bind_units_smul_of_ne_zero`: the hashed input `0` is
always sent as `0`, which no nonzero input in `ZMod 3` is. -/
example :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (ρ • (0 : ZMod 3))) ≠
      (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (ρ • (1 : ZMod 3)) := by
  intro h
  have hmem : (0 : ZMod 3) ∈
      ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (ρ • (0 : ZMod 3))).support := by
    simp
  rw [h] at hmem
  simp [Units.smul_def] at hmem

/-- Primality of `q` is needed in `uniformOfFintype_bind_units_smul_of_ne_zero`: in `ZMod 4` with
generator `1`, the input `2` is nonzero and is always sent as `2`, which the input `1` never is. -/
example : (2 : ZMod 4) ≠ 0 ∧ (Function.Surjective fun c : ZMod 4 => c • (1 : ZMod 4)) ∧
    ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (ρ • (2 : ZMod 4))) ≠
      (PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (ρ • (1 : ZMod 4)) := by
  refine ⟨by decide, fun c => ⟨c, by simp⟩, fun h => ?_⟩
  have key : ∀ x : ZMod 4, x * 2 ≠ 1 := by decide
  have hmem : (1 : ZMod 4) ∈
      ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (ρ • (1 : ZMod 4))).support := by
    simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff]
    exact ⟨1, by simp, by simp⟩
  rw [← h] at hmem
  simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff, Units.smul_def,
    smul_eq_mul] at hmem
  obtain ⟨ρ, -, hρ⟩ := hmem
  exact key _ hρ.symm

/-- `g` must generate the group in `uniformOfFintype_bind_maskedBlind`: with `g = 0` in `ZMod 2`,
the message of `OPRF2` equals the blinded input rather than `τ • 0`. -/
example :
    ((PMF.uniformOfFintype (ZMod 2)).bind fun τ => PMF.pure (maskedBlind (0 : ZMod 2) 1 τ 1)) ≠
      (PMF.uniformOfFintype (ZMod 2)).bind fun τ => PMF.pure (τ • (0 : ZMod 2)) := by
  intro h
  have hmem : (1 : ZMod 2) ∈ ((PMF.uniformOfFintype (ZMod 2)).bind fun τ =>
      PMF.pure (maskedBlind (0 : ZMod 2) 1 τ 1)).support := by
    simp [maskedBlind]
  rw [h] at hmem
  simp at hmem

/-- `d v ≠ 0` is needed in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in `ZMod 3`, an
honest sender (`d = 0`) makes the receiver compute `k • h`, which `k • h + ρ • g` never is. -/
example :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 3)).bind fun τ =>
        PMF.pure (maskedUnblind ((2 : ZMod 3) • (1 : ZMod 3)) ρ τ
          ((2 : ZMod 3) • maskedBlind (1 : ZMod 3) ρ τ (1 : ZMod 3) + 0))) ≠
      (PMF.uniformOfFintype (ZMod 3)).bind fun _ => (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ =>
        PMF.pure ((2 : ZMod 3) • (1 : ZMod 3) + ρ • (1 : ZMod 3)) := by
  intro h
  have hmem : (2 : ZMod 3) • (1 : ZMod 3) ∈
      ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 3)).bind fun τ =>
        PMF.pure (maskedUnblind ((2 : ZMod 3) • (1 : ZMod 3)) ρ τ
          ((2 : ZMod 3) • maskedBlind (1 : ZMod 3) ρ τ (1 : ZMod 3) + 0))).support := by
    simp only [add_zero, maskedUnblind_smul_maskedBlind]
    simp
  rw [h] at hmem
  simp [Units.smul_def] at hmem

/-- Primality of `q` is needed in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in
`ZMod 4` with generator `1`, `d _ = 2` is nonzero yet the receiver always computes `2`, which
`0 • 0 + ρ • 1` never is. -/
example :
    (Function.Surjective fun c : ZMod 4 => c • (1 : ZMod 4)) ∧
      (∀ _ : ZMod 4, (2 : ZMod 4) ≠ 0) ∧
      ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ =>
          (PMF.uniformOfFintype (ZMod 4)).bind fun τ =>
            PMF.pure (maskedUnblind ((0 : ZMod 4) • (1 : ZMod 4)) ρ τ
              ((0 : ZMod 4) • maskedBlind (1 : ZMod 4) ρ τ (0 : ZMod 4) + 2))) ≠
        (PMF.uniformOfFintype (ZMod 4)).bind fun _ =>
          (PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ =>
            PMF.pure ((0 : ZMod 4) • (0 : ZMod 4) + ρ • (1 : ZMod 4)) := by
  refine ⟨fun c => ⟨c, by simp⟩, fun _ => by decide, fun h => ?_⟩
  have hunit2 : ∀ u : (ZMod 4)ˣ, (u : ZMod 4) * 2 = 2 := by decide
  have hunitne2 : ∀ u : (ZMod 4)ˣ, (u : ZMod 4) ≠ 2 := by decide
  have hmem : (2 : ZMod 4) ∈
      ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 4)).bind fun τ =>
        PMF.pure (maskedUnblind ((0 : ZMod 4) • (1 : ZMod 4)) ρ τ
          ((0 : ZMod 4) • maskedBlind (1 : ZMod 4) ρ τ (0 : ZMod 4) + 2))).support := by
    simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff, maskedUnblind,
      smul_eq_mul, zero_mul, mul_zero, zero_add, sub_zero, Units.smul_def]
    exact ⟨1, by simp, 0, by simp, (hunit2 _).symm⟩
  rw [h] at hmem
  simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff, smul_eq_mul,
    zero_mul, zero_add, Units.smul_def, mul_one] at hmem
  obtain ⟨_, -, ρ, -, hρ⟩ := hmem
  exact hunitne2 ρ hρ.symm

end CslibFrontierTests.Crypto.OPRF
