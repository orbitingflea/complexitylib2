/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Probability.Entropy.BitString

/-!
# Tests for `Complexity.Probability.Entropy.BitString`

Concrete instantiations of the bit-string Shannon entropy and statistical distance lemmas:
`entropy_ge_of_dist_uniform`, `entropy_ge_of_dist_uniform_le`,
`sum_filter_mass_le_ge_of_entropy_ge`, `entropy_ofList_take_ge`, and `entropy_append_uniform`.
-/

@[expose] public section

namespace Cslib.Probability.PMF.BitStringEntropyTests

open Cslib Probability Probability.PMF BitString
open scoped ENNReal

/-- Lemma 2.2 (`entropy_ge_of_dist_uniform_le`) instantiated on the uniform distribution on
`BitString 5`: since $\mathsf{SD}(U_5, U_5) = 0 \le 1 / 25$, the bound yields $H(U_5) \ge 3$. -/
theorem three_le_entropy_uniform_five :
    3 ≤ PMF.entropy (PMF.uniformOfFintype (BitString 5)) := by
  have h := entropy_ge_of_dist_uniform_le (n := 5) (PMF.uniformOfFintype (BitString 5)) (by simp)
  have h5 : ((5 : ℕ) : ℝ) - 2 = 3 := by norm_num
  linarith

/-- Low-point-mass subset bound (`sum_filter_mass_le_ge_of_entropy_ge`) instantiated on
`PMF.uniformOfFintype (BitString 5)` with $B = 3$. -/
example :
    (1 : ℝ) / 5 ≤
      ∑ y ∈ Finset.univ.filter (fun y : BitString 5 =>
        (PMF.uniformOfFintype (BitString 5) y).toReal ≤ (2 : ℝ) ^ (-(0 : ℝ))),
        (PMF.uniformOfFintype (BitString 5) y).toReal := by
  simpa using sum_filter_mass_le_ge_of_entropy_ge (by omega : 1 ≤ 5)
    (PMF.uniformOfFintype (BitString 5)) (B := 3) le_rfl three_le_entropy_uniform_five

/-- `entropy_ofList_take_ge` instantiated on a distribution over `BitString 5` with $H(p) \ge 4$
and prefix length $k = 4$: truncating to $4$ bits leaves entropy at least $3$. -/
example (p : PMF (BitString 5)) (hp : 4 ≤ PMF.entropy p) :
    3 ≤ PMF.entropy (p.map fun x => BitString.ofList 4 ((List.ofFn x).take 4)) := by
  have h := entropy_ofList_take_ge (m := 5) (k := 4) (by omega) p
  have hsub : ((5 - 4 : ℕ) : ℝ) = 1 := by norm_num
  linarith

/-- `entropy_append_uniform` instantiated with $H(p) \ge 3$ on `BitString 4` and $k = 2$
independent uniform padding bits: the padded distribution on `BitString 6` has entropy
$H(p) + 2 \ge 5$. -/
example (p : PMF (BitString 4)) (hp : 3 ≤ PMF.entropy p) :
    5 ≤ PMF.entropy (p.bind fun x =>
      (PMF.uniformOfFintype (BitString 2)).map fun z =>
        BitString.ofList (4 + 2) (List.ofFn x ++ List.ofFn z)) := by
  have h := entropy_append_uniform (m := 4) (k := 2) p
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  linarith

end Cslib.Probability.PMF.BitStringEntropyTests
