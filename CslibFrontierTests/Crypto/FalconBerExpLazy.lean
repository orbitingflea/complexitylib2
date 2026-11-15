/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.BerExpLazy
public meta import CslibFrontier.Crypto.Computational.Falcon.BerExpLazy

/-!
# Tests for the Falcon v1.2 BerExp lazy-byte trace

These clients cover stopping on either side of the first mismatch, continuing after equal bytes,
the eight-byte boundary, all-equal rejection, the fixed-threshold bridge and the exact continuation
mass. They also exercise the shared byte encoding and exact source-resource fields. They do not
test floating-point threshold construction, a PRNG buffer or Gaussian sampling.
-/

-- This module checks the exported Falcon API and exports no test fixtures.
set_option linter.privateModule false

public section

namespace CslibFrontierTests.Crypto.FalconBerExpLazy

open Cslib Cslib.Crypto Cslib.Crypto.Falcon Probability

set_option linter.hashCommand false

#guard (berExpLazyTrace [16, 32] [15, 255]).accepted
#guard (berExpLazyTrace [16, 32] [15, 255]).bytesRead == 1

#guard !(berExpLazyTrace [16, 32] [17, 0]).accepted
#guard (berExpLazyTrace [16, 32] [17, 0]).bytesRead == 1

#guard (berExpLazyTrace [16, 32] [16, 31]).accepted
#guard (berExpLazyTrace [16, 32] [16, 31]).bytesRead == 2

#guard (berExpLazyTrace [1, 2, 3, 4, 5, 6, 7, 8]
  [1, 2, 3, 4, 5, 6, 7, 7]).accepted
#guard (berExpLazyTrace [1, 2, 3, 4, 5, 6, 7, 8]
  [1, 2, 3, 4, 5, 6, 7, 7]).bytesRead == 8

#guard !(berExpLazyTrace [1, 2, 3, 4, 5, 6, 7, 8]
  [1, 2, 3, 4, 5, 6, 7, 8]).accepted
#guard (berExpLazyTrace [1, 2, 3, 4, 5, 6, 7, 8]
  [1, 2, 3, 4, 5, 6, 7, 8]).bytesRead == 8

#guard (berExpLazyTrace [16, 32] [16, 31]).resources ==
  { byteDrawCount := 2, byteSubtractionCount := 2, byteComparisonCount := 2,
    randomBits := 16, oracleQueries := 0, handlerCalls := 0 }

private abbrev threshold256 : BerExpThreshold := ⟨256, by norm_num⟩
private abbrev sample255 : BerExpThreshold := ⟨255, by norm_num⟩

example : (berExpLazyTrace (natToFixedBytesBE 8 threshold256.val).toList
    (natToFixedBytesBE 8 sample255.val).toList).accepted = true := by
  rw [berExpLazyTrace64_accepted]
  decide

example : ((ProbComp.eval (berExpLazyCoin threshold256)).map
    (fun result => decide (1 < result.bytesRead))) true = (1 : ENNReal) / 2 ^ 8 := by
  exact eval_berExpLazyCoin_bytesRead_gt_one threshold256

example : ((ProbComp.eval (berExpLazyCoin threshold256)).map
    BerExpLazyResult.accepted) true = (256 : ENNReal) / 2 ^ 64 := by
  exact eval_berExpLazyCoin_accepted_true threshold256

example {result : BerExpLazyResult}
    (hresult : result ∈ (ProbComp.eval (berExpLazyCoin threshold256)).support) :
    result.resources.byteDrawCount = result.bytesRead ∧
      result.resources.byteSubtractionCount = result.bytesRead ∧
      result.resources.byteComparisonCount = result.bytesRead ∧
      result.resources.randomBits = 8 * result.bytesRead ∧
      result.resources.oracleQueries = 0 ∧
      result.resources.handlerCalls = 0 :=
  mem_support_berExpLazyCoin_resources hresult

end CslibFrontierTests.Crypto.FalconBerExpLazy
