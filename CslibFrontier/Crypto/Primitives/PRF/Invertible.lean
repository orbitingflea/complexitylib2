/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Invertible pseudorandom functions

An invertible pseudorandom function (iPRF) from domain `D` to range `R` with keyspace `Key`
([Hoover, Patel, Persiano and Yeo, Section 4, Definition 4.1][HooverPatelPersianoYeo2025]) consists
of a randomized key generation algorithm `gen : ProbComp Key`, a deterministic forward evaluation
function `eval : Key → D → R`, and a deterministic inverse function `inv : Key → R → Finset D`
returning the preimage set of a range element `y : R` under `eval k`.

* **Inversion correctness** (`InvertiblePRF.IsCorrectKey`, `InvertiblePRF.IsCorrect`,
  `InvertiblePRF.IsCorrectOnGen`): for a key `k`, `iF.IsCorrectKey k` states that
  `x ∈ iF.inv k y ↔ iF.eval k x = y` for all `x : D` and `y : R` (equivalently,
  `iF.inv k y = Finset.univ.filter (fun x => iF.eval k x = y)` when `D` is finite).
* **Ideal random-function iPRF** (`idealInvertiblePRF`): samples a uniformly random function
  `f : D → R` as key, evaluates `f x` in the forward direction, and returns the exact preimage
  `Finset.univ.filter (fun x => f x = y)` in the inverse direction.
* **Composition of a permutation and an invertible function / multinomial sampler**
  (`InvertiblePRF.compose`, `InvertiblePRF.composePerm`,
  [Hoover, Patel, Persiano and Yeo, Section 4.2, Theorem 4.4 &
  Corollary 4.5][HooverPatelPersianoYeo2025]):
  composing a keyed bijection `(P k₁, Pinv k₁)` on `D` with an invertible function `S` from `D` to
  `R` via `eval (k₁, k₂) x = S.eval k₂ (P k₁ x)` and
  `inv (k₁, k₂) y = (S.inv k₂ y).image (Pinv k₁)` yields a correct iPRF.

## What is not proved

* No security notion for iPRFs is defined, and no security statement is proved. In particular,
  the forward-only security that Plinko needs (Section 5.2, p. 23), the bidirectional security
  half of Theorem 4.4 (p. 12), and the pseudorandom multinomial sampler (PMNS) construction
  (Definitions 4.2–4.3, Figure 4, Lemma 4.6, and Theorem 4.7) are not formalized.

## References

* [A. Hoover, S. Patel, G. Persiano, K. Yeo, *Plinko: Single-Server PIR with Efficient Updates via
  Invertible PRFs*][HooverPatelPersianoYeo2025], Section 4 (Definition 4.1, p. 10; Theorem 4.4,
  p. 12; Corollary 4.5, p. 13; locators follow IACR ePrint 2024/318).
-/

public section

namespace Cslib.Crypto.PRF

open Probability
open scoped NNReal

/-- An invertible pseudorandom function (iPRF) from domain `D` to range `R` with keyspace `Key`
([Hoover, Patel, Persiano and Yeo, Section 4, Definition 4.1][HooverPatelPersianoYeo2025]). -/
structure InvertiblePRF (Key D R : Type) where
  /-- Randomized key generation algorithm `Gen`. -/
  gen : ProbComp Key
  /-- Deterministic forward evaluation `F : Key → D → R`. -/
  eval : Key → D → R
  /-- Deterministic inverse evaluation `F⁻¹ : Key → R → Finset D`. -/
  inv : Key → R → Finset D

namespace InvertiblePRF

variable {Key Key₁ Key₂ D R : Type}

/-! ### Inversion correctness (Definition 4.1) -/

/-- Exact inversion correctness for a fixed key `k : Key`: `x ∈ iF.inv k y` holds if and only if
`iF.eval k x = y` ([Hoover, Patel, Persiano and Yeo, Definition 4.1 &
Corollary 4.5][HooverPatelPersianoYeo2025]). -/
@[expose] def IsCorrectKey (iF : InvertiblePRF Key D R) (k : Key) : Prop :=
  ∀ (x : D) (y : R), x ∈ iF.inv k y ↔ iF.eval k x = y

/-- Unconditional inversion correctness across all keys `k : Key`. -/
@[expose] def IsCorrect (iF : InvertiblePRF Key D R) : Prop :=
  ∀ k : Key, iF.IsCorrectKey k

/-- Inversion correctness on all keys in the support of `iF.gen` (the probability-one form of
[Hoover, Patel, Persiano and Yeo, Definition 4.1][HooverPatelPersianoYeo2025]). -/
@[expose] def IsCorrectOnGen (iF : InvertiblePRF Key D R) : Prop :=
  ∀ k ∈ (ProbComp.eval iF.gen).support, iF.IsCorrectKey k

theorem IsCorrect.isCorrectOnGen {iF : InvertiblePRF Key D R} (h : iF.IsCorrect) :
    iF.IsCorrectOnGen :=
  fun k _ => h k

/-- On a finite domain `D`, `iF.IsCorrectKey k` holds if and only if `iF.inv k y` equals the
exact preimage filter `{x ∈ D | iF.eval k x = y}` for every `y : R`
([Hoover, Patel, Persiano and Yeo, Definition 4.1][HooverPatelPersianoYeo2025]). -/
theorem isCorrectKey_iff_inv_eq [Fintype D] [DecidableEq R] (iF : InvertiblePRF Key D R)
    (k : Key) :
    iF.IsCorrectKey k ↔ ∀ y : R, iF.inv k y = Finset.univ.filter (fun x => iF.eval k x = y) := by
  rw [IsCorrectKey]
  constructor
  · intro hk y
    ext x
    simp [hk x y]
  · intro h x y
    simp [h y]

theorem IsCorrectKey.inv_eq_filter [Fintype D] [DecidableEq R] {iF : InvertiblePRF Key D R}
    {k : Key} (hk : iF.IsCorrectKey k) (y : R) :
    iF.inv k y = Finset.univ.filter (fun x => iF.eval k x = y) :=
  (iF.isCorrectKey_iff_inv_eq k).mp hk y

/-! ### Ideal random-function iPRF -/

/-- The ideal random-function instantiation of an iPRF on finite types `D` and `R`: keys are
functions `f : D → R` sampled uniformly, forward evaluation is function application `f x`, and
inverse evaluation returns the exact preimage set `Finset.univ.filter (fun x => f x = y)`. -/
@[expose] noncomputable def _root_.Cslib.Crypto.PRF.idealInvertiblePRF (D R : Type) [Fintype D]
    [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R] : InvertiblePRF (D → R) D R where
  gen := ProbComp.uniform (D → R)
  eval f x := f x
  inv f y := Finset.univ.filter (fun x => f x = y)

theorem _root_.Cslib.Crypto.PRF.isCorrectKey_idealInvertiblePRF [Fintype D] [DecidableEq D]
    [Fintype R] [DecidableEq R] [Nonempty R] (f : D → R) :
    (idealInvertiblePRF D R).IsCorrectKey f := by
  intro x y
  simp [idealInvertiblePRF]

theorem _root_.Cslib.Crypto.PRF.isCorrect_idealInvertiblePRF [Fintype D] [DecidableEq D]
    [Fintype R] [DecidableEq R] [Nonempty R] :
    (idealInvertiblePRF D R).IsCorrect :=
  isCorrectKey_idealInvertiblePRF

theorem _root_.Cslib.Crypto.PRF.isCorrectOnGen_idealInvertiblePRF [Fintype D] [DecidableEq D]
    [Fintype R] [DecidableEq R] [Nonempty R] :
    (idealInvertiblePRF D R).IsCorrectOnGen :=
  isCorrect_idealInvertiblePRF.isCorrectOnGen

/-! ### Composition with a keyed permutation (Theorem 4.4 and Corollary 4.5) -/

/-- **Theorem 4.4 / Corollary 4.5 composition**
([Hoover, Patel, Persiano and Yeo, Section 4.2][HooverPatelPersianoYeo2025]): composes a keyed
permutation `(genP, P, Pinv)` on domain `D` with an invertible function / multinomial sampler
`S : InvertiblePRF Key₂ D R` via

* `gen = (genP, S.gen)`
* `eval (k₁, k₂) x = S.eval k₂ (P k₁ x)`
* `inv (k₁, k₂) y = {Pinv k₁ z | z ∈ S.inv k₂ y}`. -/
@[expose] def compose [DecidableEq D] (genP : ProbComp Key₁) (P : Key₁ → D → D)
    (Pinv : Key₁ → D → D) (S : InvertiblePRF Key₂ D R) : InvertiblePRF (Key₁ × Key₂) D R where
  gen := do
    let k₁ ← genP
    let k₂ ← S.gen
    pure (k₁, k₂)
  eval k x := S.eval k.2 (P k.1 x)
  inv k y := (S.inv k.2 y).image (Pinv k.1)

/-- **Inversion correctness of the Theorem 4.4 composition (per-key form)**: if `P k₁` and
`Pinv k₁` are mutual inverses on `D` and `S` is correct at `k₂`, then `S.compose genP P Pinv` is
correct at `(k₁, k₂)`. -/
theorem isCorrectKey_compose [DecidableEq D] {genP : ProbComp Key₁} {P : Key₁ → D → D}
    {Pinv : Key₁ → D → D} {S : InvertiblePRF Key₂ D R} {k₁ : Key₁} {k₂ : Key₂}
    (hleft : Function.LeftInverse (Pinv k₁) (P k₁))
    (hright : Function.RightInverse (Pinv k₁) (P k₁))
    (hS : S.IsCorrectKey k₂) :
    (S.compose genP P Pinv).IsCorrectKey (k₁, k₂) := by
  intro x y
  simp only [compose, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hright z, ← hS z y]
    exact hz
  · intro heval
    exact ⟨P k₁ x, (hS (P k₁ x) y).mpr heval, hleft x⟩

/-- **Inversion correctness of the Theorem 4.4 composition (all-key form)**: if `P k₁` and
`Pinv k₁` are mutual inverses for every key `k₁` and `S.IsCorrect` holds, then
`(S.compose genP P Pinv).IsCorrect` holds. -/
theorem isCorrect_compose [DecidableEq D] {genP : ProbComp Key₁} {P : Key₁ → D → D}
    {Pinv : Key₁ → D → D} {S : InvertiblePRF Key₂ D R}
    (hP : ∀ k₁ : Key₁, Function.LeftInverse (Pinv k₁) (P k₁) ∧
      Function.RightInverse (Pinv k₁) (P k₁))
    (hS : S.IsCorrect) :
    (S.compose genP P Pinv).IsCorrect :=
  fun ⟨k₁, k₂⟩ => isCorrectKey_compose (hP k₁).1 (hP k₁).2 (hS k₂)

/-- **Inversion correctness of the Theorem 4.4 composition (`gen`-support form)**: if `P k₁` and
`Pinv k₁` are mutual inverses on the support of `genP` and `S.IsCorrectOnGen` holds, then
`(S.compose genP P Pinv).IsCorrectOnGen` holds. -/
theorem isCorrectOnGen_compose [DecidableEq D] {genP : ProbComp Key₁} {P : Key₁ → D → D}
    {Pinv : Key₁ → D → D} {S : InvertiblePRF Key₂ D R}
    (hP : ∀ k₁ ∈ (ProbComp.eval genP).support,
      Function.LeftInverse (Pinv k₁) (P k₁) ∧ Function.RightInverse (Pinv k₁) (P k₁))
    (hS : S.IsCorrectOnGen) :
    (S.compose genP P Pinv).IsCorrectOnGen := by
  rintro ⟨k₁, k₂⟩ hmem
  simp only [compose, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
  obtain ⟨k₁', hk₁', k₂', hk₂', rfl, rfl⟩ := hmem
  exact isCorrectKey_compose (hP k₁ hk₁').1 (hP k₁ hk₁').2 (hS k₂ hk₂')

/-- Specialization of `InvertiblePRF.compose` to a keyed permutation family
`E : Key₁ → Equiv.Perm D` (matching `Cslib.Crypto.PRP`). -/
@[expose] def composePerm [DecidableEq D] (genP : ProbComp Key₁) (E : Key₁ → Equiv.Perm D)
    (S : InvertiblePRF Key₂ D R) : InvertiblePRF (Key₁ × Key₂) D R :=
  S.compose genP (fun k₁ => ⇑(E k₁)) (fun k₁ => ⇑(E k₁).symm)

theorem isCorrectKey_composePerm [DecidableEq D] (genP : ProbComp Key₁) (E : Key₁ → Equiv.Perm D)
    {S : InvertiblePRF Key₂ D R} (k₁ : Key₁) {k₂ : Key₂} (hS : S.IsCorrectKey k₂) :
    (S.composePerm genP E).IsCorrectKey (k₁, k₂) :=
  isCorrectKey_compose (E k₁).left_inv (E k₁).right_inv hS

theorem isCorrect_composePerm [DecidableEq D] (genP : ProbComp Key₁) (E : Key₁ → Equiv.Perm D)
    {S : InvertiblePRF Key₂ D R} (hS : S.IsCorrect) :
    (S.composePerm genP E).IsCorrect :=
  fun ⟨k₁, k₂⟩ => isCorrectKey_composePerm genP E k₁ (hS k₂)

end InvertiblePRF

end Cslib.Crypto.PRF

end
