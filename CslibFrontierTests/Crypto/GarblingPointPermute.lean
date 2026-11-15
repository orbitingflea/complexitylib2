/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.PointPermute

/-!
# Tests for point-and-permute garbling

A client of `CslibFrontier.Crypto.Primitives.Garbling.PointPermute` under module encapsulation.

One AND gate is garbled by `PointPermute.scheme` at `k = 2`, with a family that XORs copies of
the key into the tweak and with fixed coins. Encoding, evaluating and decoding gives the AND of
the two input bits on all four inputs, by computation. `scheme_isValid` gives the same answer for
every outcome of the randomized garbler at every `k > 0`, and `ConventionalCircuit.eval_toCircuit`
shows that the gate's translation to a circuit computes AND.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingPointPermute

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling

/-! ### A run on one AND gate -/

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ConventionalCircuit := ⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩

/-- The AND gate is a valid conventional circuit. -/
def validAndGate : ValidCircuit := ⟨andGate, by decide⟩

/-- A keyed family on words: the tweak XORed with copies of the key. -/
def xorFamily (key t : List Bool) : List Bool := List.zipWith xor (key ++ key) (t ++ t ++ t)

/-- Fixed coins for `k = 2`: three permutation bits, then six 3-bit keys. -/
def coins : List Bool := List.ofFn fun i : Fin 21 => decide (i.val % 3 = 1)

/-- The AND gate garbled at `k = 2` on these coins. -/
def garbled : Scheme.Garbled := (PointPermute.scheme xorFamily).gb 2 validAndGate coins

/-- The coins have the length that `Gb` samples, so `garbled` is an outcome of `garble`. -/
example :
    garbled ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).garble 2 validAndGate)).support :=
  (PointPermute.scheme xorFamily).mem_support_eval_garble_iff.mpr ⟨coins, by decide, rfl⟩

/-- The garbled function has 49 bits: the header `(2, 2, 1, 1)` and one gate's two 2-bit wire
numbers and four 4-bit rows. -/
example : garbled.fn.length = 49 := by decide

/-- Garbling, encoding, evaluating and decoding computes AND on every input. `Ev` reads the header
through `PointPermute.fnDecoder`, whose body is not exposed; its inverse law `decode_enc` is. -/
example : ∀ x₀ x₁ : Bool,
    (PointPermute.scheme xorFamily).decode garbled.decInfo
      ((PointPermute.scheme xorFamily).evalGarbled garbled.fn
        ((PointPermute.scheme xorFamily).encode garbled.encInfo [x₀, x₁])) =
      some [x₀ && x₁] := by
  simp only [garbled, PointPermute.scheme, PointPermute.fnWord, PointPermute.evalWord,
    PointPermute.fnDecoder.decode_enc]
  decide

/-! ### Correctness from `scheme_isValid` -/

/-- Every outcome of the randomized garbler, at every `k > 0`, decodes the AND of the inputs. -/
example (k : ℕ) (hk : 0 < k) (x₀ x₁ : Bool) (g : Scheme.Garbled)
    (hg : g ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).garble k validAndGate)).support) :
    (PointPermute.scheme xorFamily).decode g.decInfo
      ((PointPermute.scheme xorFamily).evalGarbled g.fn
        ((PointPermute.scheme xorFamily).encode g.encInfo [x₀, x₁])) =
      some [x₀ && x₁] := by
  rw [(PointPermute.scheme_isValid xorFamily).correct k hk validAndGate [x₀, x₁] rfl g hg]
  cases x₀ <;> cases x₁ <;> rfl

/-- The AND gate as a circuit over the full binary basis computes AND. -/
example (x : Fin 2 → Bool) :
    List.ofFn ((ConventionalCircuit.toCircuit validAndGate).eval fullInterpretation x) =
      [x 0 && x 1] := by
  refine (ConventionalCircuit.eval_toCircuit validAndGate x).trans ?_
  revert x
  decide

end CslibFrontierTests.Crypto.GarblingPointPermute
