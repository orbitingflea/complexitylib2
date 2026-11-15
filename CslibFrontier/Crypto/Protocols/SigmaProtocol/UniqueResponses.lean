/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear

/-!
# Unique Responses and Strong Special Soundness for Sigma Protocols

Formalizes unique responses and strong special soundness for `SigmaProtocol`
([BonehShoup2023], Exercises 19.14(a)–(c) and 19.15(a), pp. 813–814).

Unique responses at a statement `y` (`UniqueResponsesAt P y`) ask that an accepting commitment
and challenge determine the response uniquely; `UniqueResponses P` asks for this at every
statement. `StrongSpecialSoundness P R extract` strengthens `SpecialSoundness` so the extractor
succeeds on any two accepting conversations with the same commitment whose `(c, z)` pairs differ,
not only when `c ≠ c'`.

For the generic linear protocol `linear ψ u ι`, `linear_uniqueResponsesAt_iff` characterizes
unique responses at `y` as injectivity of `ψ y` when `C` is nonempty, giving specializations for
`schnorr`, `chaumPedersen`, and `linearSystem` (where the homogeneous system has only the zero
solution), together with `schnorr_strongSpecialSoundness` for prime `q` and `g ≠ 0`. Exercises
19.14(d), 19.15(b), and 19.16 (computational strong special soundness) are outside the scope of
this module.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.UniqueResponsesAt`: unique responses at one statement.
* `Cslib.Crypto.Protocols.SigmaProtocol.UniqueResponses`: unique responses at every statement.
* `Cslib.Crypto.Protocols.SigmaProtocol.StrongSpecialSoundness`: witness extraction from any two
  accepting transcripts sharing a commitment with distinct `(c, z)`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.SpecialSoundness.strong`: special soundness and unique
  responses yield strong special soundness with the same extractor (Exercise 19.15(a)).
* `Cslib.Crypto.Protocols.SigmaProtocol.StrongSpecialSoundness.specialSoundness`: strong special
  soundness implies special soundness.
* `Cslib.Crypto.Protocols.SigmaProtocol.linear_uniqueResponsesAt_iff`,
  `Cslib.Crypto.Protocols.SigmaProtocol.linearSystem_uniqueResponsesAt_iff`: equivalence with
  injectivity / trivial homogeneous kernel (Exercise 19.14(c)).
* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_uniqueResponses`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chaumPedersen_uniqueResponses`: unique responses when
  `r ↦ r • g` is injective (Exercise 19.14(a)–(b)).
* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_strongSpecialSoundness`: strong special soundness
  of Schnorr's protocol with `linearExtract`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Exercises
  19.14(a)–(c) and 19.15(a), pp. 813–814.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

universe u

section Defs

variable {X Y T C Z : Type u} (P : SigmaProtocol X Y T C Z)

/-- Unique responses at one statement ([BonehShoup2023], Exercise 19.14): two accepting
conversations for `y` with the same commitment and the same challenge have the same response. -/
@[expose] def UniqueResponsesAt (y : Y) : Prop :=
  ∀ t c z z', P.Accepts y t c z → P.Accepts y t c z' → z = z'

/-- Unique responses ([BonehShoup2023], Exercise 19.14): unique responses at every statement. -/
@[expose] def UniqueResponses : Prop := ∀ y, P.UniqueResponsesAt y

/-- Strong special soundness ([BonehShoup2023], Exercise 19.15): the extractor returns a witness
from two accepting conversations with the same commitment that differ in the challenge or in the
response. -/
@[expose] def StrongSpecialSoundness {W : Type*} (R : W → Y → Prop)
    (extract : Y → T → C → Z → C → Z → W) : Prop :=
  ∀ y t c z c' z', (c, z) ≠ (c', z') → P.Accepts y t c z → P.Accepts y t c' z' →
    R (extract y t c z c' z') y

variable {P} {W : Type*} {R : W → Y → Prop} {extract : Y → T → C → Z → C → Z → W}

/-- With unique responses at `y`, two accepting conversations with the same commitment and
distinct `(c, z)` pairs must differ in the challenge. -/
theorem UniqueResponsesAt.challenge_ne {y : Y} (hu : P.UniqueResponsesAt y) {t : T} {c c' : C}
    {z z' : Z} (hne : (c, z) ≠ (c', z')) (hz : P.Accepts y t c z) (hz' : P.Accepts y t c' z') :
    c ≠ c' := by
  rintro rfl
  exact hne (Prod.ext rfl (hu t c z z' hz hz'))

/-- Strong special soundness implies special soundness, with the same extractor. -/
theorem StrongSpecialSoundness.specialSoundness (h : P.StrongSpecialSoundness R extract) :
    P.SpecialSoundness R extract :=
  fun y t c z c' z' hc => h y t c z c' z' fun h' => hc (congrArg Prod.fst h')

/-- **Exercise 19.15(a)** ([BonehShoup2023], p. 814): special soundness and unique responses give
strong special soundness, with the same extractor. -/
theorem SpecialSoundness.strong (h : P.SpecialSoundness R extract) (hu : P.UniqueResponses) :
    P.StrongSpecialSoundness R extract :=
  fun y t c z c' z' hne hz hz' => h y t c z c' z' ((hu y).challenge_ne hne hz hz') hz hz'

end Defs

section Linear

variable {q : ℕ} {M N Y C : Type u} [AddCommGroup M] [Module (ZMod q) M] [Fintype M]
  [AddCommGroup N] [Module (ZMod q) N] [DecidableEq N]
  (ψ : Y → M →ₗ[ZMod q] N) (u : Y → N) (ι : C ↪ ZMod q)

/-- The sufficient direction of `linear_uniqueResponsesAt_iff`, kept separately because it needs
no `[Nonempty C]` hypothesis. -/
theorem linear_uniqueResponsesAt {y : Y} (h : Function.Injective (ψ y)) :
    (linear ψ u ι).UniqueResponsesAt y := by
  intro t c z z' hz hz'
  rw [linear_accepts_iff] at hz hz'
  exact h (hz.trans hz'.symm)

/-- **Exercise 19.14(c)** ([BonehShoup2023], p. 814): when `C` is nonempty, the linear protocol has
unique responses at `y` exactly when `ψ y` is injective (its homogeneous system has only the trivial
solution). The exercise asks for the sufficient direction; `linearSystem_uniqueResponsesAt_iff`
states it for the book's systems. -/
theorem linear_uniqueResponsesAt_iff [Nonempty C] {y : Y} :
    (linear ψ u ι).UniqueResponsesAt y ↔ Function.Injective (ψ y) := by
  refine ⟨fun h z z' hzz' => ?_, linear_uniqueResponsesAt ψ u ι⟩
  obtain ⟨c⟩ := ‹Nonempty C›
  refine h (ψ y z - ι c • u y) c z z' ?_ ?_
  · rw [linear_accepts_iff, sub_add_cancel]
  · rw [linear_accepts_iff, sub_add_cancel, hzz']

end Linear

section Instances

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  {ι : C ↪ ZMod q} {g : G}

/-- **Exercise 19.14(a)** ([BonehShoup2023], p. 813): Schnorr's protocol has unique responses when
`r ↦ r • g` is injective. -/
theorem schnorr_uniqueResponses (hg : Function.Injective fun r : ZMod q => r • g) :
    (schnorr ι g).UniqueResponses :=
  fun _ => linear_uniqueResponsesAt _ _ _ hg

/-- With at least one challenge, unique responses of Schnorr's protocol at any single statement
force `r ↦ r • g` to be injective. -/
theorem schnorr_uniqueResponsesAt_iff [Nonempty C] {u : G} :
    (schnorr ι g).UniqueResponsesAt u ↔ Function.Injective fun r : ZMod q => r • g :=
  linear_uniqueResponsesAt_iff _ _ _

/-- **Exercise 19.14(b)** ([BonehShoup2023], p. 813): the Chaum–Pedersen protocol has unique
responses when `r ↦ r • g` is injective, at every statement (Diffie–Hellman triple or not). -/
theorem chaumPedersen_uniqueResponses (hg : Function.Injective fun r : ZMod q => r • g) :
    (chaumPedersen ι g).UniqueResponses := by
  intro s
  refine linear_uniqueResponsesAt _ _ _ fun z z' h => hg ?_
  exact congrArg Prod.fst h

/-- **Exercise 19.14(c)** ([BonehShoup2023], p. 814) for `linearSystem`: when `C` is nonempty,
unique responses hold at the system `s` exactly when its homogenized form has only the trivial
solution. The exercise asks for the sufficient direction and prints the unique solution as
`α_j = 1`; the trivial solution, which is what this condition states, has every `α_j = 0`. -/
theorem linearSystem_uniqueResponsesAt_iff [Nonempty C] {m n : ℕ}
    {s : (Fin m → Fin n → G) × (Fin m → G)} :
    (linearSystem ι m n).UniqueResponsesAt s ↔
      ∀ α : Fin n → ZMod q, (∀ i, ∑ j, α j • s.1 i j = 0) → α = 0 := by
  rw [linearSystem, linear_uniqueResponsesAt_iff, injective_iff_map_eq_zero]
  simp only [funext_iff, LinearMap.pi_apply, Fintype.linearCombination_apply, Pi.zero_apply]

/-- Schnorr's protocol has strong special soundness ([BonehShoup2023], Exercises 19.14(a) and
19.15(a), pp. 813–814) with `linearExtract`. Exercise 19.17(a) ([BonehShoup2023], p. 815) derives
strongly secure Fiat–Shamir signatures from special soundness and unique responses; the library
does not yet prove it. -/
theorem schnorr_strongSpecialSoundness [Fact q.Prime] (hg : g ≠ 0) :
    (schnorr ι g).StrongSpecialSoundness (fun α u => α • g = u) (linearExtract ι) :=
  schnorr_specialSoundness.strong (schnorr_uniqueResponses (smul_left_injective (ZMod q) hg))

end Instances

end Cslib.Crypto.Protocols.SigmaProtocol
