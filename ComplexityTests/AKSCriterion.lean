/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.AKS.Criterion

/-! The AKS identity on a prime and a composite, the binomial divisibility, the AKS tests on a
prime, and axiom guards. -/

namespace ComplexityTests.AKSCriterion

open Polynomial Cslib.AKS

-- The identity holds for the prime `7`.
example : (X + C (1 : ZMod 7)) ^ 7 = X ^ 7 + C 1 := add_pow_eq_of_prime (by decide) 1

-- It fails for the composite `4`, with the unit `1`.
example : (X + C (1 : ZMod 4)) ^ 4 ≠ X ^ 4 + C 1 := fun h =>
  absurd ((prime_iff_add_pow_eq (by norm_num) isUnit_one).mpr h) (by decide)

-- `4 ∤ C(4, 2) = 6`.
example : ¬ 4 ∣ Nat.choose 4 2 := not_dvd_choose_of_prime_dvd Nat.prime_two (by norm_num)
  (by norm_num)

-- The prime `7` passes the AKS tests for every `r`.
example (r : ℕ) : Passes 7 r := passes_of_prime (by decide) r

-- `8 = 2³` is a perfect power, so it fails step 1.
example : ¬ Passes 8 3 := fun h => h.1 ⟨2, 3, by norm_num, by norm_num⟩

/--
info: 'Cslib.AKS.prime_iff_add_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prime_iff_add_pow_eq

/--
info: 'Cslib.AKS.passes_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms passes_of_prime

end ComplexityTests.AKSCriterion
