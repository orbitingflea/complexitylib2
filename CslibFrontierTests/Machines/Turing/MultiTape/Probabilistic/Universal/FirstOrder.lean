/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder

/-! Checked source-level clients for first-order universal oracle-machine storage. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder

open _root_.Turing MultiTapeTM MultiTapePTM.Universal

/-- Halted first-order storage remains local and unchanged. -/
example (r : ℕ) (d : Desc) (input : List ℕ) (cfg : ICfg) (coin : Bool)
    (hhalted : cfg.control = none) : cfg.commandAt r d input coin = .local cfg := by
  simp [ICfg.commandAt, hhalted]

/-- An out-of-range operation tag cannot escape as a typed query. -/
example (r : ℕ) (d : Desc) (input : List ℕ) (cfg : ICfg)
    (operation next : ℕ) (hop : ¬ operation < r) :
    cfg.command r d input (.query operation next) = .local cfg.halt := by
  simp [ICfg.command, hop]

/-- An invalid initial state still has a well-shaped explicit trap configuration. -/
example (d : Desc) (input : List ℕ) : (ICfg.init d).Valid d input :=
  ICfg.valid_init d input

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder
