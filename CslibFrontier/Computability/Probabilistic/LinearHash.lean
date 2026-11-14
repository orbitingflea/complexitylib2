/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.LinearHash
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-time binary linear hashing

Matrix hashing uses the shared row parser and inner-product certificate. Both certificates allow
computed
input and output lengths, arbitrary input encodings, and short matrix seeds padded with zero.
The full extractor charges sampling, hashing and copying its complete public seed and digest.

## Main results

* `Cslib.BitString.LinearHash.computableInPolyTime_wordHash`: deterministic hashing.
* `Cslib.BitString.LinearHash.isPPTOn_extract`: the complete seeded sampler.

## References

Adapted from Computability/Probabilistic/LinearHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The certificates compose the plain
row, inner-product and sampling APIs.
-/

public section

namespace Cslib.BitString.LinearHash

open Probability Turing.MultiTapeTM

/-- Hash plain polynomial-time words, retaining unary output dimensions and the full input. -/
@[fun_prop]
theorem computableInPolyTime_wordHash {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hseed : ComputableInPolyTime seed encode encBits)
    (hinput : ComputableInPolyTime input encode encBits) :
    ComputableInPolyTime (fun a => wordHash (count a) (seed a) (input a))
      encode encBits := by
  unfold wordHash
  fun_prop

/-- The complete extractor is uniformly strict PPT, including the revealed matrix seed. -/
@[program_certificate]
theorem isPPTOn_extract {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hinput : ComputableInPolyTime input encode encBits) :
    IsPPTOn encode encBits (fun a => extract (count a) (input a)) := by
  have hwidth := ComputableInPolyTime.unary_mul.comp
    (hcount.prod (ComputableInPolyTime.length_bits.comp hinput))
  have hsample := ComputableInPolyTime.sampleList hwidth
  have hc := hcount.comp (ComputableInPolyTime.fst encode encBits)
  have hi := hinput.comp (ComputableInPolyTime.fst encode encBits)
  have hs := ComputableInPolyTime.snd encode encBits
  have hcallback := ComputableInPolyTime.bitsAppend hs
    (computableInPolyTime_wordHash hc hs hi)
  simpa only [extract, bind_pure_comp, Function.comp_def] using hsample.map_with hcallback

end Cslib.BitString.LinearHash
