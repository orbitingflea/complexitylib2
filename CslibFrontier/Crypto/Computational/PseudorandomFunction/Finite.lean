/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec

/-!
# Word-level pseudorandom functions as finite ones

At security parameter `n`, a word family `family : List Bool → List Bool → List Bool` is a keyed
function `PRF.atLevel family n` on `n`-bit strings, and a word distinguisher `A` is a finite PRF
adversary `(OracleCodec.bitString n).adapt (A n [])`: it reads `n`-bit requests as strings and
answers other requests with the empty word without a call, which is the convention of the word
games. The two views have the same games (`PRF.advantage_atLevel_adapt`): the finite PRF
advantage of the adapted adversary against `PRF.atLevel family n` is the advantage of `A` between
`prfRealGame family A n` and `prfIdealGame A n`, for every length-preserving family.

So a `PseudorandomFunction` makes the finite advantage of every adapted oracle-PPT distinguisher
negligible in `n`, and an argument about finite PRF adversaries (a hybrid step, a switching lemma,
a derived keyed function) transfers to the word notion by exhibiting its finite adversary as an
adapted word program.

## Main definitions

* `Cslib.Crypto.PRF.atLevel`: the finite keyed function of a word family at one parameter.

## Main results

* `Cslib.Crypto.PRF.advantage_atLevel_adapt`: the finite PRF advantage of an adapted word
  distinguisher is its word-level PRF advantage.
-/

public section

namespace Cslib.Crypto

open Probability

/-- A table on `n`-bit strings presents `randomFunctionOracle n f` on the word channel: through
`OracleCodec.bitString n`, an `n`-bit request is answered by the bits of the table's value and any
other request by the empty word. -/
theorem wordOracle_bitString {m : Type → Type*} [Monad m] [LawfulMonad m] (n : ℕ)
    (f : BitString n → BitString n) :
    (OracleCodec.bitString n).wordOracle (fun x => (pure (f x) : m (BitString n))) =
      fun request => pure (randomFunctionOracle n f request.2) := by
  funext ⟨⟨⟩, word⟩
  by_cases hword : word.length = n <;>
    simp [OracleCodec.wordOracle, OracleCodec.bitString, randomFunctionOracle, hword]

namespace PRF

/-- The keyed function of the word family `family` at parameter `n`: an `n`-bit key and an `n`-bit
query give the first `n` bits of `family key query`, padded with `false`. For a length-preserving
family no padding happens. -/
@[expose] def atLevel (family : List Bool → List Bool → List Bool) (n : ℕ) (key x : BitString n) :
    BitString n :=
  BitString.ofList n (family (List.ofFn key) (List.ofFn x))

/-- For a length-preserving family, the table `PRF.atLevel family n key` presents the keyed word
oracle `prfOracle family n key`. -/
private theorem randomFunctionOracle_atLevel {family : List Bool → List Bool → List Bool}
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) (key : BitString n) (query : List Bool) :
    randomFunctionOracle n (atLevel family n key) query =
      prfOracle family n (List.ofFn key) query := by
  unfold randomFunctionOracle prfOracle atLevel
  split_ifs with hquery
  · rw [BitString.ofFn_ofList hquery, BitString.ofFn_ofList]
    rw [hlength _ _ (by rw [List.length_ofFn, hquery]), List.length_ofFn]
  · rfl

/-- **Finite and word PRF games agree.** For a length-preserving family, the finite PRF advantage
of the adapted word distinguisher against `PRF.atLevel family n` is the advantage of `A` between
the word games `prfRealGame family A n` and `prfIdealGame A n`. -/
theorem advantage_atLevel_adapt {family : List Bool → List Bool → List Bool}
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (A : OracleDistinguisher) (n : ℕ) :
    advantage (atLevel family n) ((OracleCodec.bitString n).adapt (A n [])) =
      Game.advantage (ProbComp.eval (prfRealGame family A n))
        (ProbComp.eval (prfIdealGame A n)) := by
  have hreal : ProbComp.eval (realExperiment (atLevel family n)
      ((OracleCodec.bitString n).adapt (A n []))) = ProbComp.eval (prfRealGame family A n) := by
    simp only [realExperiment, prfRealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, OracleCodec.run_adapt,
      wordOracle_bitString, Function.comp_def, randomFunctionOracle_atLevel hlength]
  have hideal : idealExperiment ((OracleCodec.bitString n).adapt (A n [])) = prfIdealGame A n := by
    simp only [idealExperiment, prfIdealGame, OracleCodec.run_adapt, wordOracle_bitString]
  rw [advantage, hreal, hideal]

end PRF

end Cslib.Crypto
