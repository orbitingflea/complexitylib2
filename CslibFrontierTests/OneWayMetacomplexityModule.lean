/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Crypto.Computational.OneWay.BPP
import CslibFrontier.Crypto.Computational.OneWay.MCSP
import CslibFrontier.Crypto.Computational.OneWay.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Ordinary-module clients of the one-way metacomplexity certificates

The deterministic search captures its original input, the randomized search accepts a zero-coin
schedule, and the truth-table construction accepts a computed parameter at arity zero.
These certificate clients assert no one-wayness or complexity-class separation.
-/

public section

namespace CslibFrontierTests.OneWayMetacomplexityModule

open Turing.MultiTapeTM Cslib Cslib.Crypto

-- The decider reads the captured original word uniformly throughout the prefix search.
example : ComputableInPolyTime
    (fun y : List Bool => (preimageSearch (fun _ => y.isEmpty) (y.length, y)).isEmpty)
    encBits encBool := by
  have hsearch : ComputableInPolyTime
      (fun y : List Bool => preimageSearch (fun _ => y.isEmpty) (y.length, y))
      encBits encBits :=
    computableInPolyTime_preimageSearch_of_input
      (ComputableInPolyTime.bitsIsEmpty.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.length_bits.prod ComputableInPolyTime.id')
  exact ComputableInPolyTime.bitsIsEmpty.comp hsearch

-- The verifier inspects the supplied coin word; the zero schedule supplies the empty word.
example : Cslib.Probability.IsPPT encBits
    (randomizedPreimageSearch 0 (fun p => p.2.isEmpty)) :=
  isPPT_randomizedPreimageSearch
    (ComputableInPolyTime.bitsIsEmpty.comp (ComputableInPolyTime.snd _ _))

-- Compose the zero-arity table construction with an input-dependent length and then count rows.
example : ComputableInPolyTime
    (fun y : List Bool =>
      (KabanetsCai.tableQueries y.length (KabanetsCai.tableArity 0 y.length)).length)
    encBits encUnary :=
  (ComputableInPolyTime.length_list encBits).comp
    ((KabanetsCai.computableInPolyTime_tableQueries 0).comp
      (ComputableInPolyTime.length_bits.prod ComputableInPolyTime.id'))

example : preimageSearch (fun _ => true) (0, []) = [] := rfl

example : preimageSearch (fun _ => true) (2, [true, false]) = [false, false] :=
  by decide +kernel

example : searchCoinLength 0 (0, []) = 0 := by simp [searchCoinLength]

example : KabanetsCai.tableQueries 0 (KabanetsCai.tableArity 0 0) = [[]] :=
  by decide +kernel

end CslibFrontierTests.OneWayMetacomplexityModule
