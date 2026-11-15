/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Game.StatisticalIndistinguishability

/-!
# From statistical to computational indistinguishability

Statistically indistinguishable word ensembles are computationally indistinguishable
([BonehShoup2023], Corollary 3.12, p. 85). Neither ensemble is required to be efficiently
samplable.

## Main results

* `Cslib.Crypto.StatisticallyIndistinguishable.computationallyIndistinguishable`: statistical
  indistinguishability of `ℕ → PMF (List Bool)` ensembles implies
  `ComputationallyIndistinguishable`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 3.11 (Corollary 3.12, p. 85).
-/

public section

namespace Cslib.Crypto

/-- **Statistical indistinguishability implies computational indistinguishability**
([BonehShoup2023], Corollary 3.12, p. 85). -/
theorem StatisticallyIndistinguishable.computationallyIndistinguishable
    {X Y : ℕ → PMF (List Bool)} (h : StatisticallyIndistinguishable X Y) :
    ComputationallyIndistinguishable X Y :=
  fun adversary _ => h.indistinguishable (fun n word => ProbComp.eval (adversary n word)) trivial

end Cslib.Crypto
