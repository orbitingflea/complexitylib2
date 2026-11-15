/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.PseudorandomFunction.Label

/-!
# Tests for the finite view of word PRFs and for garbling labels

Clients of `CslibFrontier.Crypto.Computational.PseudorandomFunction.Finite` and
`CslibFrontier.Crypto.Computational.PseudorandomFunction.Label` under module encapsulation.

The key-masking word family XORs the key into a valid query. At parameter `2` its keyed function
`PRF.atLevel` and the label function `PRF.label` built from it are evaluated on concrete bits, and
`labelCodec` carries a label as the key bits followed by the colour bit. A word label distinguisher
that sends one tweak and checks the reply word, run through `labelCodec` against a label table,
receives exactly that word; a malformed tweak receives the empty word without a call.

The bridge `PRF.advantage_atLevel_adapt` is applied to the key-echo family, whose length hypothesis
holds by `rfl`: its word PRF advantage is the finite advantage against the keyed function that
ignores its input.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PRFLabel

open Cslib Cslib.Probability Cslib.Crypto

/-- The key-masking word family: a query is XORed with the key. It preserves length but is not
pseudorandom. -/
def xorFamily (key query : List Bool) : List Bool := List.zipWith xor key query

/-! ### Keyed functions and labels on concrete bits -/

-- At parameter `2`, the key `10` masks the input `01` to `11`.
example : PRF.atLevel xorFamily 2 ![true, false] ![false, true] = ![true, true] := by decide

-- The label of the tweak `1` under the key `10` is `(10 ⊕ 01, first bit of 10 ⊕ 11) = (11, 0)`.
example : PRF.label (PRF.atLevel xorFamily 2) ![true, false] ![true] = (![true, true], false) := by
  decide

-- `labelCodec 1` carries the label `(11, 0)` as the key bits followed by the colour bit.
example : (labelCodec 1).encodeReply ![true] (![true, true], false) = [true, true, false] := rfl

-- A one-bit request carries a tweak; a request of any other length carries none.
example : (labelCodec 1).decodeQuery ((), [true]) = some ![true] := by decide
example : (labelCodec 1).decodeQuery ((), [true, false]) = none := by decide

/-! ### Runs of a label distinguisher -/

/-- A word label distinguisher that sends `tweak` and accepts when the reply word is `expected`. -/
def checkReply (tweak expected : List Bool) : OracleDistinguisher := fun _ _ => do
  let reply ← ProbOracleComp.query ((), tweak)
  return reply == expected

-- Against any label table `g`, the reply to the word of a tweak `t` with label
-- `g t = (key, colour)` is the word `List.ofFn key ++ [colour]`.
example (n : ℕ) (g : BitString n → BitString (n + 1) × Bool) (t : BitString n)
    (key : BitString (n + 1)) (colour : Bool) (hg : g t = (key, colour)) :
    ((labelCodec n).adapt (checkReply (List.ofFn t) (List.ofFn key ++ [colour]) n [])).run
      (fun t => pure (g t)) = pure true := by
  simp [checkReply, OracleCodec.wordOracle, labelCodec, OracleCodec.bitString, hg]

-- Against the label table of the key-masking family under the key `10`, the reply to the tweak
-- `1` is `[true, true, false]`, the word of the label `(11, 0)`.
example :
    ((labelCodec 1).adapt (checkReply [true] [true, true, false] 1 [])).run
      (fun t => pure (PRF.label (PRF.atLevel xorFamily 2) ![true, false] t)) = pure true := by
  rfl

-- A malformed tweak is answered by the empty word without consulting the table.
example (g : BitString 1 → BitString 2 × Bool) :
    ((labelCodec 1).adapt (checkReply [true, false] [] 1 [])).run (fun t => pure (g t)) =
      pure true := by
  simp [checkReply, OracleCodec.wordOracle, labelCodec, OracleCodec.bitString]

/-! ### The bridge at a concrete family -/

-- The key-echo family is length-preserving by `rfl`, and at parameter `n` its keyed function
-- ignores the input. So its word PRF advantage is the finite advantage against `fun key _ => key`.
example (A : OracleDistinguisher) (n : ℕ) :
    Game.advantage (ProbComp.eval (prfRealGame (fun key _ => key) A n))
        (ProbComp.eval (prfIdealGame A n)) =
      PRF.advantage (fun (key _ : BitString n) => key)
        ((OracleCodec.bitString n).adapt (A n [])) := by
  have hecho : PRF.atLevel (fun key _ => key) n = fun key _ => key := by
    funext key x
    simp [PRF.atLevel]
  rw [← PRF.advantage_atLevel_adapt (fun _ _ _ => rfl), hecho]

end CslibFrontierTests.Crypto.PRFLabel
