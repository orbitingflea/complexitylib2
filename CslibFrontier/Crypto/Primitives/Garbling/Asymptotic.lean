/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Negligible.Basic

/-!
# Asymptotic simulation privacy of garbling schemes

`Scheme.PrvSimSecure G Φ encFn encΛ` is simulation privacy (`prv.sim`) in the sense of Bellare,
Hoang and Rogaway [BellareHoangRogaway2012], §3.4 (p. 9): for every polynomial-time adversary `B`
there is a polynomial-time simulator `S` whose advantage in the game `PrvSim` (Fig. 5, p. 8) is
negligible in the security parameter. The quantifiers are those of the source, `∀ B ∃ S`.

The library's form differs from the source in the following ways, none of which strengthens or
weakens the notion beyond the change of formal setting:
* An adversary is a uniform strict PPT two-stage program (`TwoStage.IsPPT`): its first stage
  chooses the single `Garble` query `(f, x)` and a state of any type, encoded by any `encσ`; its
  second stage guesses from the state and the answer `(F, X, d)`, or `⊥` on an invalid query.
* The advantage is the two-world advantage `prvSimAdvantage`, the distance between the
  probabilities of answering `true` with the real and the simulated view; it is the absolute value
  of the source's `2 Pr[PrvSim] - 1`.
* Functions and side information are typed, `Fn` and `Λ`, and enter the efficiency predicates
  through the encodings `encFn` and `encΛ`. The simulator runs in time polynomial in all of its
  inputs `(1^k, y, φ)`, as the source's convention (§2.1, p. 4) requires.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.PrvSimSecure`: asymptotic simulation privacy.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM Probability

variable {Fn Λ : Type}

/-- **Simulation privacy** `prv.sim` of [BellareHoangRogaway2012], §3.4 (p. 9), with side
information `Φ`: for every uniform strict PPT adversary `B` there is a simulator `S`, uniform
strict PPT on `(1^k, y, φ)`, whose `prv.sim` advantage against `B` is negligible. Queries are
encoded by `encQuery Fn encFn`, side information by `encΛ`; the module documentation lists the
differences from the source's formal setting. -/
@[expose] def Scheme.PrvSimSecure (G : Scheme Fn) (Φ : SideInfo Fn Λ) (encFn : Fn ↪ List Bool)
    (encΛ : Λ ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → PrvSimAdversary Fn σ),
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B →
      ∃ S : ℕ → PrvSimulator Λ,
        IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView
          (fun (k, y, φ) => S k y φ) ∧
        Negligible fun k => prvSimAdvantage G Φ k (S k) (B k)

end Cslib.Crypto.Garbling
