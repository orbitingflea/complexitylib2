/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Module

/-!
# Two blinded Diffie–Hellman problems in a fixed group

[BonehShoup2023], Section 21.11.5, Lemmas 21.7 and 21.8 (pp. 910–911), state two problems that are
hard under CDH. With `[X, Y]` the Diffie–Hellman value of `X` and `Y` (Section 21.11.4), given
random `a, b, u, v`, Lemma 21.7's adversary must find `γ` and `w = [u / a ^ γ, v / b ^ γ]`; given
random `a, b, u`, Lemma 21.8's adversary must find `γ₁ ≠ γ₂`, any `v` and both values
`wᵢ = [u / a ^ γᵢ, v / b ^ γᵢ]`. The book names neither problem: "blinded CDH" and
"two-point blinded CDH", and the names of all declarations here, are this library's names.

This module states both problems in one group, as `Cslib.Crypto.cdhExperiment` does for CDH, and
analyses exactly the book's reductions, which turn an adversary for each problem into a CDH
adversary. The efficient reductions over a prime-order group family, and the conclusions under the
CDH assumption, are in `CslibFrontier/Crypto/Computational/DiffieHellman/BlindedFamily.lean`.

Differences from the book:

* Groups are written additively and the experiments draw exponents: `a = α • g`, `b = β • g`,
  `u = x • g`, `v = y • g`. The target is written through the exponents of `u` and `a` only,
  `blindedDH α x γ b v = (x - γ * α) • (v - γ • b)`, which is the book's `[u / a ^ γ, v / b ^ γ]`
  because `[X, Y]` is the discrete logarithm of `X` times `Y`. No discrete-logarithm function on
  group elements is introduced, and in Lemma 21.8 the adversary's `v` needs no exponent.
* The statements are exact and in one group. With exactly uniform blinding exponents, Lemma 21.7
  is an equality of success probabilities (`cdhAdvantage_blindedCDHToCDH`) for every nonzero
  modulus `q`, every `ZMod q`-module `G` and every `g`. Lemma 21.8
  (`blindedCDHPairAdvantage_le_cdhAdvantage`) is an inequality and needs `q` prime: when the
  adversary loses, the reduction's output can still be right, and for composite `q` the difference
  `γ₁ - γ₂` need not be invertible.
* The win conditions are decided, so the experiments take `[DecidableEq G]`, as
  `Cslib.Crypto.cdhExperiment` does.

## Main definitions

* `Cslib.Crypto.blindedDH`: the target value `[u / a ^ γ, v / b ^ γ]` in additive notation.
* `Cslib.Crypto.BlindedCDHAnswer`, `Cslib.Crypto.BlindedCDHPairAnswer`: the adversaries' answers.
* `Cslib.Crypto.blindedCDHExperiment`, `Cslib.Crypto.blindedCDHAdvantage`: the problem of
  Lemma 21.7 and its success probability.
* `Cslib.Crypto.blindedCDHPairExperiment`, `Cslib.Crypto.blindedCDHPairAdvantage`: the problem of
  Lemma 21.8 and its success probability.
* `Cslib.Crypto.blindedCDHToCDH`, `Cslib.Crypto.blindedCDHPairToCDH`: the book's reductions, which
  turn an adversary for each problem into a CDH adversary, with the blinding exponents drawn
  uniformly; `Cslib.Crypto.blindedCDHToCDHWith` and `Cslib.Crypto.blindedCDHPairToCDHWith` fix
  them.

## Main results

* `Cslib.Crypto.BlindedCDHAnswer.solve_eq_iff`, `Cslib.Crypto.BlindedCDHPairAnswer.solve_eq`: the
  book's equations (21.10) and (21.11), solved for the Diffie–Hellman value.
* `Cslib.Crypto.cdhAdvantage_blindedCDHToCDH`: Lemma 21.7 in one group, an equality.
* `Cslib.Crypto.blindedCDHPairAdvantage_le_cdhAdvantage`: Lemma 21.8 in one group of prime order.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 21.11.5, Lemmas 21.7 and 21.8 with equations (21.10) and
  (21.11), pp. 910–911.
-/

public section

namespace Cslib.Crypto

open Probability
open scoped NNReal

section Algebra

variable {G : Type} [AddCommGroup G] {q : ℕ} [Module (ZMod q) G]

/-- The book's `[u / a ^ γ, v / b ^ γ]` ([BonehShoup2023], Lemma 21.7) for `u = x • g` and
`a = α • g`, written through the exponents of `u` and `a`: since `[X, Y]` is the discrete logarithm
of `X` times `Y`, it is `(x - γ * α) • (v - γ • b)`. No discrete logarithm of `b` or `v` is needed.
The name is this library's. -/
@[expose] def blindedDH (α x γ : ZMod q) (b v : G) : G :=
  (x - γ * α) • (v - γ • b)

/-- When `b = β • g` and `v = y • g`, `blindedDH` is the product of the two blinded exponents
times `g`. -/
theorem blindedDH_smul_smul (g : G) (α β x y γ : ZMod q) :
    blindedDH α x γ (β • g) (y • g) = ((x - γ * α) * (y - γ * β)) • g := by
  rw [blindedDH, smul_smul, ← sub_smul, smul_smul]

/-- An adversary's answer in `blindedCDHExperiment`: the exponent `γ` and the claimed value
`w = [u / a ^ γ, v / b ^ γ]` of [BonehShoup2023], Lemma 21.7. -/
structure BlindedCDHAnswer (q : ℕ) (G : Type) where
  /-- The exponent `γ` chosen by the adversary. -/
  exponent : ZMod q
  /-- The claimed value of `blindedDH` at `γ`. -/
  value : G

/-- An adversary's answer in `blindedCDHPairExperiment`: two exponents `γ₁, γ₂`, an element `v`
and the claimed values `wᵢ = [u / a ^ γᵢ, v / b ^ γᵢ]` of [BonehShoup2023], Lemma 21.8. -/
structure BlindedCDHPairAnswer (q : ℕ) (G : Type) where
  /-- The first exponent `γ₁`. -/
  exponent₁ : ZMod q
  /-- The second exponent `γ₂`. -/
  exponent₂ : ZMod q
  /-- The element `v` chosen by the adversary. -/
  right : G
  /-- The claimed value of `blindedDH` at `γ₁`. -/
  value₁ : G
  /-- The claimed value of `blindedDH` at `γ₂`. -/
  value₂ : G

/-- The output of the reduction of [BonehShoup2023], Lemma 21.7, on the CDH instance `(s, t)`
with blinding exponents `μ`, `ν` (so `a = μ • g` and `b = ν • g`): equation (21.10) solved for
`[s, t]`, `w + (γ * ν) • s + (γ * μ) • t - (γ ^ 2 * μ * ν) • g`. -/
@[expose] def BlindedCDHAnswer.solve (out : BlindedCDHAnswer q G) (g : G) (μ ν : ZMod q)
    (s t : G) : G :=
  out.value + (out.exponent * ν) • s + (out.exponent * μ) • t -
    (out.exponent ^ 2 * μ * ν) • g

/-- The output of the reduction of [BonehShoup2023], Lemma 21.8, on a CDH instance whose first
element is `s`, with blinding exponent `μ` (so `a = μ • g` and `b = s`): equation (21.11) solved
for `[u, b]`, `(γ₁ - γ₂)⁻¹ • (w₂ - w₁) - μ • v + ((γ₁ + γ₂) * μ) • s`. -/
@[expose] def BlindedCDHPairAnswer.solve (out : BlindedCDHPairAnswer q G) (μ : ZMod q) (s : G) :
    G :=
  (out.exponent₁ - out.exponent₂)⁻¹ • (out.value₂ - out.value₁) - μ • out.right +
    ((out.exponent₁ + out.exponent₂) * μ) • s

/-- The algebra of [BonehShoup2023], Lemma 21.7: the reduction's output is the Diffie–Hellman
element exactly when the adversary's value is the blinded one. No hypothesis on `G`, `q` or
`g`. -/
theorem BlindedCDHAnswer.solve_eq_iff (out : BlindedCDHAnswer q G) (g : G) (μ ν x y : ZMod q) :
    out.solve g μ ν (x • g) (y • g) = (x * y) • g ↔
      out.value = blindedDH μ x out.exponent (ν • g) (y • g) := by
  have h : blindedDH μ x out.exponent (ν • g) (y • g) =
      (x * y) • g - (out.exponent * ν) • x • g - (out.exponent * μ) • y • g +
        (out.exponent ^ 2 * μ * ν) • g := by
    rw [blindedDH]
    module
  rw [h, BlindedCDHAnswer.solve]
  constructor
  · intro h'
    rw [← h']
    abel
  · intro h'
    rw [h']
    abel

/-- The algebra of [BonehShoup2023], Lemma 21.8: for prime `q`, from the two blinded values at
distinct exponents the reduction's output is the Diffie–Hellman element of `β • g` and `x • g`.
The adversary's `v` is any element of `G`. -/
theorem BlindedCDHPairAnswer.solve_eq [Fact q.Prime] (out : BlindedCDHPairAnswer q G) (g : G)
    (μ β x : ZMod q) (hne : out.exponent₁ ≠ out.exponent₂)
    (h₁ : out.value₁ = blindedDH μ x out.exponent₁ (β • g) out.right)
    (h₂ : out.value₂ = blindedDH μ x out.exponent₂ (β • g) out.right) :
    out.solve μ (β • g) = (β * x) • g := by
  have h : out.value₂ - out.value₁ = (out.exponent₁ - out.exponent₂) •
      (μ • out.right + (x * β - (out.exponent₁ + out.exponent₂) * μ * β) • g) := by
    rw [h₁, h₂]
    simp only [blindedDH]
    module
  rw [BlindedCDHPairAnswer.solve, h, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
  module

end Algebra

section Experiments

variable {G : Type} [AddCommGroup G] (q : ℕ) [Module (ZMod q) G] (g : G)

/-- The reduction of [BonehShoup2023], Lemma 21.7, with its blinding exponents `μ`, `ν` fixed: on
the CDH instance `(s, t)`, run the adversary on `a = μ • g`, `b = ν • g`, `u = s`, `v = t` and
return `BlindedCDHAnswer.solve`. -/
@[expose] def blindedCDHToCDHWith (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G))
    (μ ν : ZMod q) (s t : G) : ProbComp G := do
  let out ← A (μ • g) (ν • g) s t
  return out.solve g μ ν s t

/-- The reduction of [BonehShoup2023], Lemma 21.8, with its blinding exponent `μ` fixed: on the
CDH instance `(s, t)`, run the adversary on `a = μ • g`, `b = s`, `u = t` and return
`BlindedCDHPairAnswer.solve`. -/
@[expose] def blindedCDHPairToCDHWith (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G))
    (μ : ZMod q) (s t : G) : ProbComp G := do
  let out ← A (μ • g) s t
  return out.solve μ s

variable [NeZero q]

/-- The reduction of [BonehShoup2023], Lemma 21.7, with exactly uniform blinding exponents. -/
noncomputable def blindedCDHToCDH
    (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) (s t : G) : ProbComp G := do
  let μ ← $ᵗ ZMod q
  let ν ← $ᵗ ZMod q
  blindedCDHToCDHWith q g A μ ν s t

/-- The reduction of [BonehShoup2023], Lemma 21.8, with an exactly uniform blinding exponent. Its
bound, `blindedCDHPairAdvantage_le_cdhAdvantage`, needs `q` prime. It is an `abbrev`, so that the
program it runs after the draw is visibly `blindedCDHPairToCDHWith`, whose efficiency over a group
family is `PrimeOrderGroupFamily.isPPTOn_blindedCDHPairToCDHWith`. The exactly uniform draw is
outside that certificate: a strict fair-coin machine outputs each value with a dyadic probability,
so it can make the draw only when `q` is a power of two. The efficient reduction is
`PrimeOrderGroupFamily.blindedCDHPairToCDHAdversary` (certified by
`PrimeOrderGroupFamily.isPPT_blindedCDHPairToCDHAdversary`), which draws with
`PrimeOrderGroupFamily.sampleExp` and loses `1 / 2 ^ n`
(`PrimeOrderGroupFamily.succProbability_blindedCDHPairGame_le`). -/
noncomputable abbrev blindedCDHPairToCDH
    (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G)) (s t : G) : ProbComp G := do
  let μ ← $ᵗ ZMod q
  blindedCDHPairToCDHWith q g A μ s t

variable [DecidableEq G]

/-- The problem of [BonehShoup2023], Lemma 21.7, in the group generated by `g`: the challenger
draws uniform exponents and gives the adversary `a = α • g`, `b = β • g`, `u = x • g`, `v = y • g`;
the adversary wins when its value is `blindedDH` at its exponent. The name is this library's. -/
@[expose] noncomputable def blindedCDHExperiment
    (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) : Experiment := do
  let α ← $ᵗ ZMod q
  let β ← $ᵗ ZMod q
  let x ← $ᵗ ZMod q
  let y ← $ᵗ ZMod q
  let out ← A (α • g) (β • g) (x • g) (y • g)
  return out.value = blindedDH α x out.exponent (β • g) (y • g)

/-- The success probability of `A` in `blindedCDHExperiment`. -/
@[expose] noncomputable def blindedCDHAdvantage
    (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) : ℝ≥0 :=
  Experiment.succProbability (blindedCDHExperiment q g A)

/-- The problem of [BonehShoup2023], Lemma 21.8, in the group generated by `g`: the challenger
draws uniform exponents and gives the adversary `a = α • g`, `b = β • g`, `u = x • g`; the
adversary wins when its two exponents differ and both values are `blindedDH` at its `v`. The name
is this library's. -/
@[expose] noncomputable def blindedCDHPairExperiment
    (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G)) : Experiment := do
  let α ← $ᵗ ZMod q
  let β ← $ᵗ ZMod q
  let x ← $ᵗ ZMod q
  let out ← A (α • g) (β • g) (x • g)
  return out.exponent₁ ≠ out.exponent₂ ∧
    out.value₁ = blindedDH α x out.exponent₁ (β • g) out.right ∧
    out.value₂ = blindedDH α x out.exponent₂ (β • g) out.right

/-- The success probability of `A` in `blindedCDHPairExperiment`. -/
@[expose] noncomputable def blindedCDHPairAdvantage
    (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G)) : ℝ≥0 :=
  Experiment.succProbability (blindedCDHPairExperiment q g A)

/-- A CDH solver that first draws `r` from `R` and then runs `B r` has, in the CDH experiment, the
average over `r` of the laws for `B r`. -/
theorem eval_cdhExperiment_bind {ρ : Type} (R : ProbComp ρ) (B : ρ → G → G → ProbComp G) :
    ProbComp.eval (cdhExperiment q g fun s t => R >>= fun r => B r s t) =
      (ProbComp.eval R).bind fun r => ProbComp.eval (cdhExperiment q g (B r)) := by
  simp only [cdhExperiment, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind]
  exact (congrArg (PMF.bind _) (funext fun a => PMF.bind_comm _ _ _)).trans (PMF.bind_comm _ _ _)

/-- The law of `blindedCDHExperiment` is the law of the CDH experiment for
`blindedCDHToCDHWith`, averaged over uniform blinding exponents. -/
theorem eval_blindedCDHExperiment (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) :
    ProbComp.eval (blindedCDHExperiment q g A) =
      (PMF.uniformOfFintype (ZMod q)).bind fun μ => (PMF.uniformOfFintype (ZMod q)).bind fun ν =>
        ProbComp.eval (cdhExperiment q g (blindedCDHToCDHWith q g A μ ν)) := by
  simp only [blindedCDHExperiment, cdhExperiment, blindedCDHToCDHWith, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind,
    BlindedCDHAnswer.solve_eq_iff]

/-- With exactly uniform blinding exponents, the reduction of [BonehShoup2023], Lemma 21.7, has
in the CDH experiment the law of the adversary in `blindedCDHExperiment`. -/
theorem eval_cdhExperiment_blindedCDHToCDH
    (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) :
    ProbComp.eval (cdhExperiment q g (blindedCDHToCDH q g A)) =
      ProbComp.eval (blindedCDHExperiment q g A) := by
  rw [eval_blindedCDHExperiment]
  refine (eval_cdhExperiment_bind q g ($ᵗ ZMod q) fun μ s t => do
    let ν ← $ᵗ ZMod q
    blindedCDHToCDHWith q g A μ ν s t).trans ?_
  rw [ProbComp.eval_uniform]
  refine congrArg (PMF.bind _) (funext fun μ => ?_)
  refine (eval_cdhExperiment_bind q g ($ᵗ ZMod q) fun ν => blindedCDHToCDHWith q g A μ ν).trans ?_
  rw [ProbComp.eval_uniform]

/-- **[BonehShoup2023], Lemma 21.7, in one group, with exactly uniform blinding**: the reduction
solves its CDH instance with exactly the adversary's success probability in
`blindedCDHExperiment`. Beyond `NeZero q`, which the uniform draws need, there is no hypothesis on
`q` or `g`: `q` need not be prime and `g` need not generate `G`. -/
theorem cdhAdvantage_blindedCDHToCDH (A : G → G → G → G → ProbComp (BlindedCDHAnswer q G)) :
    cdhAdvantage q g (blindedCDHToCDH q g A) = blindedCDHAdvantage q g A := by
  unfold cdhAdvantage blindedCDHAdvantage Experiment.succProbability
  rw [eval_cdhExperiment_blindedCDHToCDH]

/-- For prime `q`, `blindedCDHPairExperiment` accepts with probability at most that of the CDH
experiment for `blindedCDHPairToCDHWith`, averaged over a uniform blinding exponent. -/
theorem eval_blindedCDHPairExperiment_true_le [Fact q.Prime]
    (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G)) :
    ProbComp.eval (blindedCDHPairExperiment q g A) true ≤
      ((PMF.uniformOfFintype (ZMod q)).bind fun μ =>
        ProbComp.eval (cdhExperiment q g (blindedCDHPairToCDHWith q g A μ))) true := by
  simp only [cdhExperiment, blindedCDHPairExperiment, blindedCDHPairToCDHWith,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_apply_mono_on_support _ _ fun μ _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun β _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun x _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun out _ => ?_
  by_cases h : out.exponent₁ ≠ out.exponent₂ ∧
      out.value₁ = blindedDH μ x out.exponent₁ (β • g) out.right ∧
      out.value₂ = blindedDH μ x out.exponent₂ (β • g) out.right
  · refine le_of_le_of_eq (PMF.coe_le_one _ _) ?_
    simp [out.solve_eq g μ β x h.1 h.2.1 h.2.2]
  · simp [h]

/-- **[BonehShoup2023], Lemma 21.8, in one group of prime order, with exactly uniform
blinding**: whenever the adversary wins `blindedCDHPairExperiment`, the reduction solves its CDH
instance. The inequality can be strict, since the reduction can also be right when the adversary
loses. -/
theorem blindedCDHPairAdvantage_le_cdhAdvantage [Fact q.Prime]
    (A : G → G → G → ProbComp (BlindedCDHPairAnswer q G)) :
    blindedCDHPairAdvantage q g A ≤ cdhAdvantage q g (blindedCDHPairToCDH q g A) := by
  refine Game.succProbability_mono ?_
  refine (eval_blindedCDHPairExperiment_true_le q g A).trans_eq ?_
  refine congrFun (congrArg DFunLike.coe ?_) true
  refine ((eval_cdhExperiment_bind q g ($ᵗ ZMod q) fun μ =>
    blindedCDHPairToCDHWith q g A μ).trans ?_).symm
  rw [ProbComp.eval_uniform]

end Experiments

end Cslib.Crypto
