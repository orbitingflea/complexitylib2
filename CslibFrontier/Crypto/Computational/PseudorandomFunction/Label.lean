/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.Uniform

/-!
# Garbling labels from a length-preserving pseudorandom function

The point-and-permute garbling of `CslibFrontier.Crypto.Primitives.Garbling.Basic` masks its
tables with a keyed function `F : K → T → K × Bool` that sends a wire key and a tweak to a
*label*, a key together with a colour bit. A length-preserving PRF has one bit too few for this.
`PRF.label F` builds such a function from a keyed function `F` on `(n + 1)`-bit strings with two
calls: the label of an `n`-bit tweak `t` under key `k` is `F k (0 ‖ t)` together with the first
bit of `F k (1 ‖ t)`.

It is exactly as secure as `F` (`PRF.advantage_label`): an adversary against `PRF.label F` has the
same finite PRF advantage as the adversary against `F` that answers each of its label queries with
the two calls. On the ideal side, reading a uniform function on `(n + 1)`-bit strings at `0 ‖ t`
and the first bit at `1 ‖ t` gives a uniform function from tweaks to labels, because this reading
is a surjective additive map.

On words, a label distinguisher is an `OracleDistinguisher` that sends `n`-bit tweaks and reads
`(n + 2)`-bit replies, a key's bits followed by the colour bit (`labelCodec n`). The reduction
`labelReduction W` runs `W` at parameter `n` against a PRF oracle at parameter `n + 1` and answers
each tweak with the two calls. It is oracle PPT whenever `W` is (`isOraclePPT_labelReduction`), and
its word PRF advantage at `n + 1` is `W`'s label advantage at `n` (`advantage_label_atLevel`). So
the label function of a `PseudorandomFunction` is pseudorandom against every oracle-PPT label
distinguisher (`PseudorandomFunction.indistinguishable_label`).

The two-call construction is the standard way to lengthen the output of a PRF; the statements and
proofs are this library's.

## Main definitions

* `Cslib.Crypto.PRF.label`, `Cslib.Crypto.PRF.labelQuery`: the label function of a keyed function
  on `(n + 1)`-bit strings, and the two calls that answer one label query.
* `Cslib.Crypto.labelCodec`: labels on the word channel.
* `Cslib.Crypto.labelReduction`: the PRF distinguisher built from a label distinguisher.

## Main results

* `Cslib.Crypto.PRF.advantage_label`: the label function is exactly as secure as the keyed
  function.
* `Cslib.Crypto.isOraclePPT_labelReduction`: the reduction is uniform strict oracle PPT.
* `Cslib.Crypto.advantage_label_atLevel`: the reduction's word PRF advantage is the label
  advantage of the label distinguisher.
* `Cslib.Crypto.PseudorandomFunction.indistinguishable_label`: the label function of a PRF is
  pseudorandom.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace PRF

variable {Key : Type} {n : ℕ}

/-- The label function of a keyed function `F` on `(n + 1)`-bit strings: the label of an `n`-bit
tweak `t` under `key` is `F key (0 ‖ t)` together with the first bit of `F key (1 ‖ t)`. -/
@[expose] def label (F : Key → BitString (n + 1) → BitString (n + 1)) (key : Key)
    (t : BitString n) : BitString (n + 1) × Bool :=
  (F key (Fin.cons false t), F key (Fin.cons true t) 0)

/-- The two calls to a function on `(n + 1)`-bit strings that answer the label query `t`. -/
@[expose] def labelQuery (t : BitString n) :
    ProbOracleComp (fun _ : BitString (n + 1) => BitString (n + 1))
      (BitString (n + 1) × Bool) := do
  let value ← ProbOracleComp.query (Fin.cons false t)
  let colour ← ProbOracleComp.query (Fin.cons true t)
  return (value, colour 0)

/-- Against the table `f`, the two calls return the label of `t` under `f`. -/
private theorem run_labelQuery (f : BitString (n + 1) → BitString (n + 1)) (t : BitString n) :
    (labelQuery t).run (fun x => pure (f x)) = pure (label (fun (_ : Unit) => f) () t) := by
  simp [labelQuery, label]

/-- Reading the labels of a function on `(n + 1)`-bit strings is an additive map. -/
private def labelHom (n : ℕ) :
    (BitString (n + 1) → BitString (n + 1)) →+ (BitString n → BitString (n + 1) × Bool) where
  toFun f := label (fun (_ : Unit) => f) ()
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every label table is read from some function on `(n + 1)`-bit strings. -/
private theorem labelHom_surjective (n : ℕ) : Function.Surjective (labelHom n) := by
  intro g
  let f : BitString (n + 1) → BitString (n + 1) := fun x =>
    if x 0 then Pi.single 0 (g (Fin.tail x)).2 else (g (Fin.tail x)).1
  refine ⟨f, funext fun t => ?_⟩
  change label (fun (_ : Unit) => f) () t = g t
  simp [label, f]

/-- **The label function is exactly as secure as the keyed function.** The finite PRF advantage of
`A` against `PRF.label F` is the advantage against `F` of `A` with each label query answered by
the two calls `labelQuery`. -/
theorem advantage_label [Fintype Key] [Nonempty Key]
    (F : Key → BitString (n + 1) → BitString (n + 1))
    (A : Adversary (BitString n) (BitString (n + 1) × Bool)) :
    advantage (label F) A = advantage F (ProbOracleComp.simulate labelQuery A) := by
  have hreal :
      realExperiment (label F) A = realExperiment F (ProbOracleComp.simulate labelQuery A) := by
    simp only [realExperiment, ProbOracleComp.run_simulate, run_labelQuery]
    rfl
  have hideal : ProbComp.eval (idealExperiment A) =
      ProbComp.eval (idealExperiment (ProbOracleComp.simulate labelQuery A)) := by
    simp only [idealExperiment, ProbOracleComp.run_simulate, run_labelQuery, ProbComp.eval_bind,
      ProbComp.eval_uniform]
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_addHom (labelHom n) (labelHom_surjective n),
      PMF.bind_map]
    rfl
  rw [advantage, advantage, hreal, hideal]

end PRF

/-! ### Labels on words -/

/-- Labels on the single word channel: an `n`-bit tweak is the request of its bits, and the label
`(k, c)` is the reply of the `n + 1` bits of `k` followed by `c`. -/
@[expose] def labelCodec (n : ℕ) :
    OracleCodec Unit (BitString n) fun _ => BitString (n + 1) × Bool where
  encodeQuery := (OracleCodec.bitString n).encodeQuery
  decodeQuery := (OracleCodec.bitString n).decodeQuery
  decodeQuery_eq_some_iff := (OracleCodec.bitString n).decodeQuery_eq_some_iff
  encodeReply _ := ⟨fun (key, colour) => List.ofFn key ++ [colour], by
    rintro ⟨key, colour⟩ ⟨key', colour'⟩ h
    obtain ⟨hkey, hcolour⟩ := List.append_inj h (by simp)
    rw [List.ofFn_injective hkey, List.singleton_inj.mp hcolour]⟩

/-- The reduction's answer to one request of a label distinguisher run at parameter `m - 1`: an
`(m - 1)`-bit tweak `t` is answered by the first `m` bits of the reply to `0 ‖ t` followed by the
first bit of the reply to `1 ‖ t`; any other request by the empty word, without a query. -/
private def labelHandler (m : ℕ) (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  if request.2.length + 1 = m then do
    let value ← List.take m <$> ProbOracleComp.query ((), false :: request.2)
    (value ++ ·) <$> (List.take 1 <$> ProbOracleComp.query ((), true :: request.2))
  else pure []

/-- The PRF distinguisher built from a label distinguisher `W`: at parameter `m` it runs `W` at
parameter `m - 1` and answers each `(m - 1)`-bit tweak `t` with two calls to its own oracle, the
first `m` bits of the reply to `0 ‖ t` followed by the first bit of the reply to `1 ‖ t`. Any other
request of `W` is answered by the empty word, without a query. -/
def labelReduction (W : OracleDistinguisher) : OracleDistinguisher :=
  fun m _ => ProbOracleComp.simulate (labelHandler m) (W (m - 1) [])

/-! ### Efficiency -/

/-- The handler is uniformly strict oracle PPT in the parameter, the auxiliary word and the
request. -/
private theorem isOraclePPTOn_labelHandler :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)) encBits
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) => labelHandler pair.1.1 pair.2) := by
  unfold labelHandler
  fun_prop

/-- Every answer of the handler has at most `m + 1` bits. -/
private theorem length_le_of_mem_support_labelHandler {m : ℕ} {request : Unit × List Bool}
    {reply : List Bool} (hreply : reply ∈ OracleComp.support (labelHandler m request)) :
    reply.length ≤ m + 1 := by
  unfold labelHandler at hreply
  split at hreply
  · obtain ⟨value, hvalue, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
    obtain ⟨value, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hvalue
    obtain ⟨colour, hcolour, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    obtain ⟨colour, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcolour
    simp only [List.length_append, List.length_take]
    omega
  · simp [OracleComp.eq_of_mem_supportWith_pure hreply]

/-- **Efficiency of the reduction.** For every uniform strict oracle-PPT label distinguisher `W`,
`labelReduction W` is uniform strict oracle PPT. -/
theorem isOraclePPT_labelReduction {W : OracleDistinguisher} (hW : IsOraclePPT encBool W) :
    IsOraclePPT encBool (labelReduction W) :=
  (IsOraclePPTOn.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × List Bool => labelHandler caller.1)
    (prepare := fun caller : ℕ × List Bool => (caller.1 - 1, ([] : List Bool)))
    (resources := fun caller _ => caller.1 + 1)
    hW (by fun_prop) isOraclePPTOn_labelHandler (by fun_prop)
    fun _ _ _ hreply => length_le_of_mem_support_labelHandler hreply).isOraclePPT

/-! ### Security -/

/-- Against a table `f` on `(n + 1)`-bit strings, the reduction at parameter `n + 1`, read through
`OracleCodec.bitString (n + 1)`, runs like the label distinguisher at parameter `n`, read through
`labelCodec n`, with each label query answered by the two calls. -/
private theorem run_adapt_labelReduction (W : OracleDistinguisher) (n : ℕ)
    (f : BitString (n + 1) → BitString (n + 1)) :
    ((OracleCodec.bitString (n + 1)).adapt (labelReduction W (n + 1) [])).run
        (fun x => pure (f x)) =
      (ProbOracleComp.simulate PRF.labelQuery ((labelCodec n).adapt (W n []))).run
        (fun x => pure (f x)) := by
  simp only [labelReduction, OracleCodec.run_adapt, wordOracle_bitString,
    ProbOracleComp.run_simulate, PRF.run_labelQuery, Nat.add_sub_cancel]
  congr 1
  funext ⟨⟨⟩, word⟩
  by_cases hword : word.length = n
  · have hvalue (bit : Bool) : randomFunctionOracle (n + 1) f (bit :: word) =
        List.ofFn (f (Fin.cons bit (BitString.ofList n word))) := by
      have hcons :
          BitString.ofList (n + 1) (bit :: word) = Fin.cons bit (BitString.ofList n word) :=
        funext fun i =>
          Fin.cases (by simp [BitString.ofList]) (fun _ => by simp [BitString.ofList]) i
      rw [randomFunctionOracle, ite_eq_left (by rw [List.length_cons, hword]), hcons]
    simp only [labelHandler, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_map,
      ProbOracleComp.run_query, hvalue, map_pure, pure_bind, List.take_of_length_le
        (List.length_ofFn (f := f (Fin.cons false (BitString.ofList n word)))).le,
      labelCodec, OracleCodec.wordOracle, OracleCodec.bitString, hword, PRF.label]
    simp [List.ofFn_succ]
  · simp [labelHandler, labelCodec, OracleCodec.wordOracle, OracleCodec.bitString, hword]

/-- **The reduction's advantage is the label advantage.** For a length-preserving family, the word
PRF advantage of `labelReduction W` at parameter `n + 1` is the finite PRF advantage of the label
distinguisher `W`, read through `labelCodec n`, against the label function of `family` at
parameter `n + 1`. -/
theorem advantage_label_atLevel {family : List Bool → List Bool → List Bool}
    (hlength : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (W : OracleDistinguisher) (n : ℕ) :
    PRF.advantage (PRF.label (PRF.atLevel family (n + 1))) ((labelCodec n).adapt (W n [])) =
      Game.advantage (ProbComp.eval (prfRealGame family (labelReduction W) (n + 1)))
        (ProbComp.eval (prfIdealGame (labelReduction W) (n + 1))) := by
  rw [PRF.advantage_label, ← PRF.advantage_atLevel_adapt hlength]
  simp only [PRF.advantage, PRF.realExperiment, PRF.idealExperiment, run_adapt_labelReduction]

/-- **The label function of a pseudorandom function is pseudorandom.** For every uniform strict
oracle-PPT label distinguisher `W`, its finite PRF advantage at parameter `n`, read through
`labelCodec n`, against the label function of `family` at parameter `n + 1` is negligible. -/
theorem PseudorandomFunction.indistinguishable_label {family : List Bool → List Bool → List Bool}
    (h : PseudorandomFunction family) :
    Game.Indistinguishable
      (fun W n => ProbComp.eval (PRF.realExperiment (PRF.label (PRF.atLevel family (n + 1)))
        ((labelCodec n).adapt (W n []))))
      (fun W n => ProbComp.eval (PRF.idealExperiment ((labelCodec n).adapt (W n []))))
      (IsOraclePPT encBool) := by
  intro W hW
  convert (h.secure (labelReduction W) (isOraclePPT_labelReduction hW)).shift 1 using 1
  funext n
  exact advantage_label_atLevel h.length_eq W n

end Cslib.Crypto
