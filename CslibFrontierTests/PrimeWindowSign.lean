/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Foundations.NumberTheory.PrimeWindowSign
import Mathlib.Tactic.NormNum

/-!
# Prime-window sign correctness through ordinary imports

The clients extract opposite sides of one half for coefficients of `1` and `-1`, use the
zero theorem without any coefficient assumptions, and check the excluded-prime endpoint.
The nonzero clients deliberately accept the supplied coefficient component's congruences;
computing that component and its resource bound belongs to the computational layer.
-/

set_option linter.privateModule false

open Cslib Cslib.PrimeWindowSign

example : cutoff 0 16 = 131072 := by norm_num [cutoff]

example : 17 ∈ primes 0 16 := by
  apply Nat.mem_primesLE_sdiff_primesLE_iff.mpr
  exact ⟨by decide, by decide, by norm_num [cutoff]⟩

example : 2 ∉ primes 0 16 := by
  intro h
  have := Nat.mem_primesLE_sdiff_primesLE_iff.mp h
  omega

-- Zero coefficients give a nonvacuous, unconditional zero instance at every input bound.
example (m L : ℕ) :
    ¬ CircleFlag (1 / 8)
      (crtCircleApprox (modulus m L) ((cutoff m L).size + 10) (fun _ => 0)) := by
  apply not_flag_zero_of_coefficients
  intro p
  simp

-- The positive client removes the sign iff after checking the integer magnitude bound.
example (L : ℕ) (c : ℕ → primes 0 L → ℤ)
    (hc : ∀ k ≤ cutoff 0 L * (cutoff 0 L).size + 1, ∀ p,
      c k p * crtCofactor (modulus 0 L) p ≡ (2 : ℤ) ^ k [ZMOD modulus 0 L p]) :
    ∃ k ≤ cutoff 0 L * (cutoff 0 L).size + 1,
      FirstCircleFlag (1 / 8)
        (fun j => crtCircleApprox (modulus 0 L) ((cutoff 0 L).size + 10) (c j)) k ∧
      crtCircleApprox (modulus 0 L) ((cutoff 0 L).size + 10) (c k) < 1 / 2 := by
  have hc' : ∀ k ≤ cutoff 0 L * (cutoff 0 L).size + 1, ∀ p,
      c k p * crtCofactor (modulus 0 L) p ≡ (2 : ℤ) ^ k * 1 [ZMOD modulus 0 L p] := by
    simpa only [mul_one] using hc
  obtain ⟨k, hk, hf, hs, _⟩ :=
    firstCircleFlag_sign_of_coefficients 0 L c 1 (by norm_num) (by norm_num) hc'
  exact ⟨k, hk, hf, hs.mp (by norm_num)⟩

-- The same precision and cutoff handle a negative integer, without a positive representative.
example (L : ℕ) (c : ℕ → primes 0 L → ℤ)
    (hc : ∀ k ≤ cutoff 0 L * (cutoff 0 L).size + 1, ∀ p,
      c k p * crtCofactor (modulus 0 L) p ≡ (2 : ℤ) ^ k * (-1) [ZMOD modulus 0 L p]) :
    ∃ k ≤ cutoff 0 L * (cutoff 0 L).size + 1,
      FirstCircleFlag (1 / 8)
        (fun j => crtCircleApprox (modulus 0 L) ((cutoff 0 L).size + 10) (c j)) k ∧
      1 / 2 < crtCircleApprox (modulus 0 L) ((cutoff 0 L).size + 10) (c k) := by
  obtain ⟨k, hk, hf, _, hs⟩ :=
    firstCircleFlag_sign_of_coefficients 0 L c (-1) (by norm_num) (by norm_num) hc
  exact ⟨k, hk, hf, hs.mp (by norm_num)⟩
