/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Privacy
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Coalition Recognition and Unauthorized Guessing Bounds for Secret Sharing

This module formalizes the coalition-recognition observation of [BonehShoup2023], Section 22.5
(pp. 975–976), together with the impossibility of perfectly correct secret sharing when the empty
coalition is authorized:

1. **Coalition recognition (`AccessScheme.recognizeCoalitionDist`):** given a scheme over a finite
   nonempty secret space `Secret` with decidable equality and a key distribution `P : PMF Key`,
   sample `secret ← uniformOfFintype Secret`, generate coalition `s`'s view under `P`, and accept
   (`true`) iff `scheme.reconstruct s v = secret`.
   - On any authorized coalition `s`, `recognizeCoalitionDist` equals `PMF.pure true` for every key
     distribution `P` (`AccessScheme.recognizeCoalitionDist_eq_pure_true_of_authorized`).
   - On any unauthorized coalition `s` under an allowed source `P ∈ scheme.sources`, *every*
     deterministic guessing function `guess : ((i : s) → Share i.1) → Secret` recovers a uniform
     secret with probability `(Fintype.card Secret : ℝ≥0∞)⁻¹`
     (`AccessScheme.bind_viewDist_map_decide_eq_true_of_not_authorized`), and in particular
     `recognizeCoalitionDist` accepts with probability `(Fintype.card Secret : ℝ≥0∞)⁻¹` (`1 / |Z|`,
     `AccessScheme.recognizeCoalitionDist_true_of_not_authorized`).
   - When `[Nontrivial Secret]` (the book's `|Z| ≥ 2`) and `P ∈ scheme.sources`, acceptance with
     probability `1` characterizes authorized coalitions
     (`AccessScheme.recognizeCoalitionDist_true_eq_one_iff`).
2. **Impossibility when `∅` is authorized (`not_perfectlyCorrect_of_authorized_empty`):** over any
   nontrivial secret space and nonempty key type, no sharing and reconstruction maps can be
   perfectly correct for an access structure that authorizes `∅`, because the empty coalition's view
   is independent of the secret.

Model notes: `AccessScheme` models information-theoretic correctness and privacy without machine
encodings or running-time bounds, so `recognizeCoalitionDist` is the output distribution `PMF Bool`
of the recognition test rather than a complexity-bounded algorithm. Unlike [BonehShoup2023],
Definition 22.19 (which specifies the combiner `C` only on authorized coalitions while invoking it
on arbitrary coalitions in the recognition test), `AccessScheme.reconstruct` is total on all
coalitions `s : Finset Party`.

## Main definitions

* `AccessScheme.recognizeCoalitionDist`: output distribution of the coalition-recognition test on
  coalition `s` under key source `P`.

## Main results

* `AccessScheme.recognizeCoalitionDist_eq_pure_true_of_authorized`: authorized coalitions are
  accepted with probability `1` (`PMF.pure true`).
* `AccessScheme.bind_viewDist_map_decide_eq_true_of_not_authorized`: any deterministic guesser
  applied to an unauthorized coalition's view recovers a uniform secret with probability
  `(Fintype.card Secret : ℝ≥0∞)⁻¹`.
* `AccessScheme.recognizeCoalitionDist_true_of_not_authorized`: unauthorized coalitions are
  accepted by `recognizeCoalitionDist` with probability `(Fintype.card Secret : ℝ≥0∞)⁻¹`.
* `AccessScheme.recognizeCoalitionDist_true_eq_one_iff`: for `[Nontrivial Secret]`, acceptance
  probability `1` characterizes authorized coalitions.
* `not_perfectlyCorrect_of_authorized_empty`: no scheme over a nontrivial secret space and nonempty
  key space is perfectly correct when `A.authorized ∅`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Version 0.6,
  Section 22.5, pp. 975–976.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

namespace AccessScheme

variable {Secret Key Party : Type*} {Share : Party → Type*}

/-- The coalition-recognition experiment of [BonehShoup2023], Section 22.5 (pp. 975–976): sample a
uniform secret `secret ← uniformOfFintype Secret`, generate coalition `s`'s view under key source
`P`, and accept (`true`) iff `scheme.reconstruct s v = secret`. -/
noncomputable def recognizeCoalitionDist [Fintype Secret] [Nonempty Secret]
    [DecidableEq Secret] (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) (s : Finset Party) : PMF Bool :=
  (uniformOfFintype Secret).bind fun secret =>
    (scheme.viewDist P s secret).map fun v => decide (scheme.reconstruct s v = secret)

/-- On an authorized coalition, `recognizeCoalitionDist` is `PMF.pure true` for every key
distribution `P` ([BonehShoup2023], Section 22.5, p. 976). -/
theorem recognizeCoalitionDist_eq_pure_true_of_authorized [Fintype Secret] [Nonempty Secret]
    [DecidableEq Secret] (scheme : AccessScheme Secret Key Party Share)
    (P : PMF Key) {s : Finset Party} (hs : scheme.access.authorized s) :
    scheme.recognizeCoalitionDist P s = PMF.pure true := by
  have hview (secret : Secret) :
      (scheme.viewDist P s secret).map (fun v => decide (scheme.reconstruct s v = secret)) =
        PMF.pure true := by
    rw [viewDist, AccessStructure.viewDistOf, PMF.map_comp]
    have hconst :
        ((fun v => decide (scheme.reconstruct s v = secret)) ∘
          fun k i => scheme.share k secret i.1) =
          Function.const Key true := by
      funext k
      simp [scheme.correct k secret s hs]
    rw [hconst, PMF.map_const]
  simp [recognizeCoalitionDist, hview]

/-- Any deterministic guesser `guess` applied to an unauthorized coalition's view recovers a
uniformly chosen secret with probability `(Fintype.card Secret : ℝ≥0∞)⁻¹` (`1 / |Z|`,
[BonehShoup2023], Section 22.5, p. 976). -/
theorem bind_viewDist_map_decide_eq_true_of_not_authorized [Fintype Secret] [Nonempty Secret]
    [DecidableEq Secret] (scheme : AccessScheme Secret Key Party Share)
    {P : PMF Key} (hP : P ∈ scheme.sources) {s : Finset Party}
    (hs : ¬ scheme.access.authorized s) (guess : ((i : s) → Share i.1) → Secret) :
    ((uniformOfFintype Secret).bind fun secret =>
      (scheme.viewDist P s secret).map fun v => decide (guess v = secret)) true =
      (Fintype.card Secret : ℝ≥0∞)⁻¹ := by
  obtain ⟨m₀⟩ := ‹Nonempty Secret›
  have hind (secret : Secret) : scheme.viewDist P s secret = scheme.viewDist P s m₀ :=
    scheme.viewDist_eq_of_not_authorized hP hs secret m₀
  simp only [hind, ← PMF.bind_pure_comp, Function.comp_def]
  rw [PMF.bind_comm, PMF.bind_apply]
  simp_rw [uniformOfFintype_bind_decide_eq_apply_true]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- On an unauthorized coalition `s` under any allowed key source `P ∈ scheme.sources`,
`recognizeCoalitionDist` accepts with probability `(Fintype.card Secret : ℝ≥0∞)⁻¹` (`1 / |Z|`,
[BonehShoup2023], Section 22.5, p. 976). -/
theorem recognizeCoalitionDist_true_of_not_authorized [Fintype Secret] [Nonempty Secret]
    [DecidableEq Secret] (scheme : AccessScheme Secret Key Party Share)
    {P : PMF Key} (hP : P ∈ scheme.sources) {s : Finset Party}
    (hs : ¬ scheme.access.authorized s) :
    scheme.recognizeCoalitionDist P s true = (Fintype.card Secret : ℝ≥0∞)⁻¹ :=
  scheme.bind_viewDist_map_decide_eq_true_of_not_authorized hP hs (scheme.reconstruct s)

/-- When the secret space has at least two elements (`[Nontrivial Secret]`, the book's
`|Z| ≥ 2`), `recognizeCoalitionDist` accepts with probability `1` if and only if the coalition is
authorized ([BonehShoup2023], Section 22.5, p. 976). -/
theorem recognizeCoalitionDist_true_eq_one_iff [Fintype Secret] [Nontrivial Secret]
    [DecidableEq Secret] (scheme : AccessScheme Secret Key Party Share)
    {P : PMF Key} (hP : P ∈ scheme.sources) (s : Finset Party) :
    scheme.recognizeCoalitionDist P s true = 1 ↔ scheme.access.authorized s := by
  constructor
  · intro h1
    by_contra hs
    rw [scheme.recognizeCoalitionDist_true_of_not_authorized hP hs] at h1
    have hcard : 1 < Fintype.card Secret := Fintype.one_lt_card
    have hne : (Fintype.card Secret : ℝ≥0∞) ≠ 1 := by
      exact_mod_cast ne_of_gt hcard
    exact hne (ENNReal.inv_eq_one.mp h1)
  · intro hs
    rw [scheme.recognizeCoalitionDist_eq_pure_true_of_authorized P hs, PMF.pure_apply_self]

end AccessScheme

/-- No secret-sharing scheme over a nontrivial secret space and nonempty key type can be perfectly
correct for an access structure that authorizes `∅`: the empty view is independent of the secret. -/
theorem not_perfectlyCorrect_of_authorized_empty {Secret Key Party : Type*} {Share : Party → Type*}
    [Nontrivial Secret] [Nonempty Key] {A : AccessStructure Party} (hempty : A.authorized ∅)
    (share : Key → Secret → (i : Party) → Share i)
    (reconstruct : (s : Finset Party) → ((i : s) → Share i.1) → Secret) :
    ¬ PerfectlyCorrect A share reconstruct := by
  intro hcorr
  obtain ⟨k⟩ := ‹Nonempty Key›
  obtain ⟨m₀, m₁, hne⟩ := exists_pair_ne Secret
  have hview : (fun i : (∅ : Finset Party) => share k m₀ i.1) =
      fun i : (∅ : Finset Party) => share k m₁ i.1 := by
    ext ⟨_, hi⟩
    exact False.elim (Finset.notMem_empty _ hi)
  have h0 := hcorr k m₀ ∅ hempty
  have h1 := hcorr k m₁ ∅ hempty
  rw [hview, h1] at h0
  exact hne h0.symm

end Cslib.Crypto.Protocols.SecretSharing
