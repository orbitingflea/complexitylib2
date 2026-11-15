/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant.Birthday
public import CslibFrontier.Crypto.Computational.MerkleDamgard
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Probability.IID.FunctionCollision
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.TotalProbability

/-!
# Joux multicollisions of Merkle–Damgård chains, with their cost

Joux's attack ([BonehShoup2023], §8.4.1, printed pp. 298–299) finds many messages with one digest
for an iterated hash at little more than the cost of one collision. If `b` pairs of different
blocks `(m_i, m_i')` satisfy `h(t_i, m_i) = h(t_i, m_i')`, where `t_{i+1} = h(t_i, m_i)`, then each
of the `2 ^ b` messages that take one block from each pair reaches the same chaining value.

This module proves that structural fact for any iterated function (`IsCollisionChain`,
`IsCollisionChain.isMulticollision`), and builds and analyses oracle programs that find such
chains with the birthday finder of `CslibFrontier.Crypto.Computational.CollisionResistant.Birthday`.
Each program has a bound on its oracle calls that holds on every path, and a lower bound on its
success probability that holds for every compression function meeting a length condition.

* `jouxFinder` runs the stages against any step program. It shares a budget of `f` birthday
  attempts among the `b` stages: an attempt that finds a collision records it and moves on from the
  chaining value it reaches; an attempt that finds none is repeated from the same value; when the
  budget is spent the program returns `none`. It makes at most `f * (s * c)` oracle calls when each
  step costs `c` (`isQueryBounded_jouxFinder`), and returns a collision chain of length `b` except
  with probability `2 ^ b * ((1 + ε) / 2) ^ f / 2`, where `ε` bounds the probability that one
  attempt finds no collision (`jouxFinder_success`).
* `merkleDamgardJouxFinder` is the book's setting: a chain `merkleDamgardChain` with `ℓ`-bit blocks
  and `n`-bit chaining values. With `ℓ ≥ n + 7`, `s = ⌈2 √(2 ^ n)⌉ + 1` samples per attempt and
  `3 b` attempts, it makes at most `3 b s` compression calls, and with probability at least `1/2`
  it outputs `b` pairs such that, for every common list of blocks `tail`, their `2 ^ b` selections,
  each followed by `tail`, are a `2 ^ b`-collision
  (`isQueryBounded_merkleDamgardJouxFinder`, `merkleDamgardJouxFinder_success_half`).
* `merkleDamgardBitJouxFinder` does the same for the library's `merkleDamgard`, which spends one
  compression call per message bit. It treats `g` consecutive bits as one candidate, so its count
  `1 + 3 b s g` carries a factor `g ≥ n + 7` that the book's count does not
  (`isQueryBounded_merkleDamgardBitJouxFinder`, `merkleDamgardBitJouxFinder_success_half`).

**The cost measure.** The certificates are `ProbOracleComp.IsQueryBounded`, with the compression
function as the oracle. They count evaluations of the compression function on every path,
whatever the samples and the replies; that is the cost measure of §8.3. They are not running-time
bounds: sampling, the search for a colliding pair and the bookkeeping are not counted, and no
machine model is involved. They are worst-case counts, not expected costs. The programs reach the
compression function only through the oracle, and the success theorems run them against
`fun x => pure (h k x)`, so each certificate and its success theorem are about the same program.

## Differences from [BonehShoup2023]

* **Cost.** The book uses the birthday attack `log₂ s` times, spending `2 ^ (n/2)` on each, and
  concludes that it found a `2 ^ b`-collision "in time `O(b 2 ^ (n/2))`". It states no success
  probability and does not say what happens when an attack finds no collision. Here a budget of
  `f` attempts serves the `b` stages; with `f = 3 b` and the sample count of Lemma 8.2 the finder
  makes at most `3 b (⌈2 √(2 ^ n)⌉ + 1)` compression evaluations and succeeds with probability at
  least `1/2`. The constant `3` and the probability `1/2` are this library's choices;
  `merkleDamgardJouxFinder_success` has the general trade-off.
* **Cost measure.** §8.4.1 says "time". The certificates count compression evaluations only.
* **Block length.** §8.4.1 states no condition on the blocks. Lemma 8.2, which it applies to
  `h(t, ·)`, needs `|Y| ≥ 100 |X|`; the statements here assume `ℓ ≥ n + 7`, since `2 ^ 7 ≥ 100`.
  Without such a condition the claim is false: a compression function that is injective in the
  block has no block collision.
* **`s`-collision.** An `s`-collision is a `Finset` of `s` messages with one digest
  (`IsMulticollision`), so the messages are distinct, as [BonehShoup2023], Exercise 8.7 (printed
  p. 349) makes explicit; §8.4.1 says "a set of messages". The programs output the `b` pairs, not
  the `2 ^ b` messages.
* **Blocks.** Blocks are bit strings with a length hypothesis on `h`, in place of
  `h : X × Y → X`. The existing development in `CslibFrontier.Crypto.Computational.MerkleDamgard`
  takes blocks as long as chaining values; `merkleDamgardChain` itself does not, and the statements
  for `merkleDamgardJouxFinder` are about it with longer blocks.

## Main definitions

* `Cslib.Crypto.IsCollisionChain`: `b` pairs of different messages, each colliding at the value
  reached through the pairs before it.
* `Cslib.Crypto.jouxMessage`: the message that takes one message from each pair.
* `Cslib.Crypto.IsMulticollision`: `s` distinct points with one value.
* `Cslib.Crypto.jouxFinder`, `Cslib.Crypto.merkleDamgardJouxFinder`,
  `Cslib.Crypto.merkleDamgardBitJouxFinder`: the finders.
* `Cslib.Crypto.multicollisionOutputs`, `Cslib.Crypto.bitMulticollisionOutputs`: the success
  events of the last two, unfolded by `Cslib.Crypto.mem_multicollisionOutputs` and
  `Cslib.Crypto.mem_bitMulticollisionOutputs`.

## Main results

* `Cslib.Crypto.IsCollisionChain.isMulticollision`: a collision chain of length `b` gives a
  `2 ^ b`-collision of the iterated function, also after a common suffix.
* `Cslib.Crypto.isMulticollision_merkleDamgardChain`,
  `Cslib.Crypto.isMulticollision_merkleDamgard_of_chain`: the same for `merkleDamgardChain` and for
  `merkleDamgard`.
* `Cslib.Crypto.isQueryBounded_jouxFinder`, `Cslib.Crypto.jouxFinder_success`: cost and success of
  the generic finder.
* `Cslib.Crypto.isQueryBounded_merkleDamgardJouxFinder`,
  `Cslib.Crypto.merkleDamgardJouxFinder_success`,
  `Cslib.Crypto.merkleDamgardJouxFinder_success_half`: Joux's attack on `merkleDamgardChain`.
* `Cslib.Crypto.isQueryBounded_merkleDamgardBitJouxFinder`,
  `Cslib.Crypto.merkleDamgardBitJouxFinder_success`,
  `Cslib.Crypto.merkleDamgardBitJouxFinder_success_half`: the same for `merkleDamgard`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §8.4.1 (printed pp. 298–299); §8.3, Lemma 8.2 (printed p. 294);
  Exercise 8.7 (printed p. 349).
-/

public section

namespace Cslib.Crypto

/-! ### Collision chains of an iterated function -/

section Chain

variable {T M : Type}

/-- `pairs` is a chain of collisions of `step` from `t`: the two messages of the first pair
differ and collide at `t`, and the rest is a chain from their common next value. -/
@[expose] def IsCollisionChain (step : T → M → T) : T → List (M × M) → Prop
  | _, [] => True
  | t, p :: rest => p.1 ≠ p.2 ∧ step t p.2 = step t p.1 ∧ IsCollisionChain step (step t p.1) rest

/-- The message that takes the second message of pair `i` exactly when `σ i` is set. -/
@[expose] def jouxMessage (pairs : List (M × M)) (σ : BitString pairs.length) : List M :=
  List.ofFn fun i => if σ i then pairs[i].2 else pairs[i].1

/-- The two messages of each pair of a collision chain differ. -/
theorem IsCollisionChain.fst_ne_snd {step : T → M → T} :
    ∀ {t : T} {pairs : List (M × M)}, IsCollisionChain step t pairs → ∀ p ∈ pairs, p.1 ≠ p.2
  | _, [], _, _, hp => by simp at hp
  | _, _ :: _, ⟨hne, _, hrest⟩, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hne
    · exact hrest.fst_ne_snd p hp

/-- **Joux's observation** ([BonehShoup2023], §8.4.1, printed p. 299): every choice of one message
from each pair of a collision chain reaches the same value as the first messages. -/
theorem IsCollisionChain.foldl_jouxMessage {step : T → M → T} :
    ∀ {t : T} {pairs : List (M × M)}, IsCollisionChain step t pairs →
      ∀ σ : BitString pairs.length,
        (jouxMessage pairs σ).foldl step t = (pairs.map Prod.fst).foldl step t
  | _, [], _, _ => by simp [jouxMessage]
  | t, p :: rest, ⟨_, hcol, hrest⟩, σ => by
    have ih := hrest.foldl_jouxMessage fun i => σ i.succ
    simp only [jouxMessage] at ih ⊢
    simp only [List.length_cons, List.ofFn_succ, List.foldl_cons, List.map_cons]
    by_cases h0 : σ 0
    · simpa [h0, hcol] using ih
    · simpa [h0] using ih

/-- Different selections from a collision chain are different messages. -/
theorem IsCollisionChain.jouxMessage_injective {step : T → M → T} {t : T}
    {pairs : List (M × M)} (hc : IsCollisionChain step t pairs) :
    Function.Injective (jouxMessage pairs) := by
  intro σ τ hστ
  funext i
  have hi := congrFun (List.ofFn_injective hστ) i
  have hne := hc.fst_ne_snd pairs[i] (List.getElem_mem _)
  by_cases hσ : σ i <;> by_cases hτ : τ i <;> simp_all

/-- `S` is an `s`-collision of `f`: `s` distinct points with one common value (the sense of
[BonehShoup2023], §8.4.1 and Exercise 8.7). -/
@[expose] def IsMulticollision {α β : Type*} (f : α → β) (s : ℕ) (S : Finset α) : Prop :=
  S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, f x = f y

/-- **Joux multicollisions** ([BonehShoup2023], §8.4.1, printed p. 299): a collision chain of
length `b` gives a `2 ^ b`-collision of the iterated function, also after any common suffix. -/
theorem IsCollisionChain.isMulticollision [DecidableEq M] {step : T → M → T} {t : T}
    {pairs : List (M × M)} (hc : IsCollisionChain step t pairs) (tail : List M) :
    IsMulticollision (fun ms => (ms ++ tail).foldl step t) (2 ^ pairs.length)
      (Finset.univ.image (jouxMessage pairs)) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hc.jouxMessage_injective, Finset.card_univ,
      BitString.card]
  · intro x hx y hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hy
    simp only [List.foldl_append, hc.foldl_jouxMessage]

/-- Two different valid members of a multicollision of `H key` are a collision in the sense of the
collision-resistance game (`isCollision`). -/
theorem isCollision_of_isMulticollision {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {n s : ℕ} {key : List Bool} {S : Finset (List Bool)}
    (hS : IsMulticollision (H key) s S) {m₁ m₂ : List Bool} (h₁ : m₁ ∈ S) (h₂ : m₂ ∈ S)
    (hne : m₁ ≠ m₂) (hv₁ : valid n m₁ = true) (hv₂ : valid n m₂ = true) :
    isCollision H valid n key m₁ m₂ = true :=
  isCollision_eq_true_iff.mpr ⟨hv₁, hv₂, hne, hS.2 m₁ h₁ m₂ h₂⟩

end Chain

/-! ### The Joux finder for any step program -/

section Joux

variable {Query M T : Type} {spec : Query → Type} [DecidableEq M] [DecidableEq T]

/-- Joux's finder with a budget of `f` birthday attempts for `b` stages, from the chaining value
`t`. Each attempt runs `birthdayFinder` with the step program `stage t` from the current value. A
collision is recorded and the search goes on from the value it reaches; an attempt that finds no
collision is repeated from the same value. Returns the `b` pairs, or `none` when the budget runs
out first. -/
@[expose] def jouxFinder (stage : T → M → ProbOracleComp spec T) (sampler : ProbComp M) (s : ℕ) :
    ℕ → ℕ → T → ProbOracleComp spec (Option (List (M × M)))
  | _, 0, _ => pure (some [])
  | 0, _ + 1, _ => pure none
  | f + 1, b + 1, t =>
    birthdayFinder (stage t) sampler s >>= fun r =>
      match r with
      | none => jouxFinder stage sampler s f (b + 1) t
      | some (m, m', t') => Option.map ((m, m') :: ·) <$> jouxFinder stage sampler s f b t'

/-- **Cost of the Joux finder.** `f` attempts of `s` steps of at most `c` oracle calls each make
at most `f * (s * c)` oracle calls on every path, whatever the number of stages. This counts oracle
calls only; it is not a running time. -/
theorem isQueryBounded_jouxFinder {stage : T → M → ProbOracleComp spec T} {c : ℕ}
    (hstage : ∀ t m, ProbOracleComp.IsQueryBounded (stage t m) c) (sampler : ProbComp M) (s : ℕ) :
    ∀ (f b : ℕ) (t : T),
      ProbOracleComp.IsQueryBounded (jouxFinder stage sampler s f b t) (f * (s * c))
  | 0, 0, _ => by rw [jouxFinder]; exact OracleComp.IsCostBounded.pure _ _
  | 0, _ + 1, _ => by rw [jouxFinder]; exact OracleComp.IsCostBounded.pure _ _
  | _ + 1, 0, _ => by rw [jouxFinder]; exact OracleComp.IsCostBounded.pure _ _
  | f + 1, b + 1, t => by
    rw [jouxFinder]
    refine ((isQueryBounded_birthdayFinder (hstage t) sampler s).bind (m := f * (s * c))
      fun r => ?_).mono (by rw [Nat.succ_mul, Nat.add_comm])
    match r with
    | none => exact isQueryBounded_jouxFinder hstage sampler s f (b + 1) t
    | some (m, m', t') =>
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (isQueryBounded_jouxFinder hstage sampler s f b t')

/-- The successful outputs of the Joux finder: `b` pairs forming a collision chain of `step`
from `t`. -/
@[expose] def jouxSuccess (step : T → M → T) (b : ℕ) (t : T) : Set (Option (List (M × M))) :=
  {o | ∃ pairs, o = some pairs ∧ pairs.length = b ∧ IsCollisionChain step t pairs}

/-- The arithmetic of one step of the budget induction: `x B + y (2 B) ≤ (1 + ε) B` when
`x + y = 1` and `x ≥ 1 - ε`. -/
private theorem budget_step {x y ε B : ℝ} (hadd : x + y = 1) (hx : 1 - ε ≤ x) (hB : 0 ≤ B) :
    x * B + y * (2 * B) ≤ (1 + ε) * B := by
  have h1 : y * B ≤ ε * B := mul_le_mul_of_nonneg_right (by linarith) hB
  have h2 : x * B + y * B = B := by rw [← add_mul, hadd, one_mul]
  linarith

variable [Fintype M] [Nonempty M]

/-- From every value in `D`, `jouxFinder` misses `jouxSuccess` with probability at most
`2 ^ b * ((1 + ε) / 2) ^ f / 2`. The induction follows the recursion of `jouxFinder`; it is
Markov's inequality for `2 ^ (-X)`, where `X` counts the attempts that find a collision. -/
private theorem jouxFinder_failure_le {stage : T → M → ProbOracleComp spec T}
    (O : (q : Query) → spec q) (step : T → M → T)
    (hstage : ∀ t m, (stage t m).run (fun x => pure (O x)) = pure (step t m))
    (D : Finset T) (hD : ∀ t ∈ D, ∀ m, step t m ∈ D) (s : ℕ) {ε : ℝ}
    (hε : Real.exp (-(s * (s - 1) / (2 * D.card))) + s.choose 2 * (Fintype.card M : ℝ)⁻¹ ≤ ε) :
    ∀ (f b : ℕ) (t : T), t ∈ D →
      ((ProbComp.eval ((jouxFinder stage (ProbComp.uniform M) s f b t).run
        fun x => pure (O x))).toOuterMeasure (jouxSuccess step b t)ᶜ).toReal ≤
        2 ^ b * ((1 + ε) / 2) ^ f / 2
  | f, 0, t, _ => by
    have hε0 : 0 ≤ ε := le_trans (by positivity) hε
    have hmem : (some [] : Option (List (M × M))) ∈ jouxSuccess step 0 t :=
      ⟨[], rfl, rfl, trivial⟩
    have h0 : (ProbComp.eval ((jouxFinder stage (ProbComp.uniform M) s f 0 t).run
        fun x => pure (O x))).toOuterMeasure (jouxSuccess step 0 t)ᶜ = 0 := by
      simp [jouxFinder, PMF.toOuterMeasure_pure_apply, hmem]
    rw [h0, ENNReal.toReal_zero]
    positivity
  | 0, b + 1, t, _ => by
    have h1 := (ENNReal.toReal_mono ENNReal.one_ne_top (Probability.PMF.toOuterMeasure_le_one
      (ProbComp.eval ((jouxFinder stage (ProbComp.uniform M) s 0 (b + 1) t).run
        fun x => pure (O x))) (jouxSuccess step (b + 1) t)ᶜ)).trans_eq ENNReal.toReal_one
    have h2 : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
    rw [pow_zero, mul_one, pow_succ]
    linarith
  | f + 1, b + 1, t, ht => by
    have hε0 : 0 ≤ ε := le_trans (by positivity) hε
    have hB0 : 0 ≤ (2 : ℝ) ^ b * ((1 + ε) / 2) ^ f / 2 := by positivity
    have hsucc := birthdayFinder_success O (step t) (hstage t) D (hD t ht) s
    have hadd := Probability.PMF.toOuterMeasure_toReal_add_compl
      (ProbComp.eval ((birthdayFinder (stage t) (ProbComp.uniform M) s).run fun x => pure (O x)))
      (collisionOutputs (step t))
    have e : (2 : ℝ) ^ (b + 1) * ((1 + ε) / 2) ^ (f + 1) / 2 =
        (1 + ε) * (2 ^ b * ((1 + ε) / 2) ^ f / 2) := by ring
    rw [jouxFinder, ProbOracleComp.run_bind, ProbComp.eval_bind, e]
    refine (Probability.PMF.toOuterMeasure_bind_toReal_le_mul_add_mul _ _
      (collisionOutputs (step t)) _
      (a₁ := 2 ^ b * ((1 + ε) / 2) ^ f / 2) (a₂ := 2 * (2 ^ b * ((1 + ε) / 2) ^ f / 2))
      hB0 (by positivity) ?_ ?_).trans (budget_step hadd (by linarith) hB0)
    · rintro _ - ⟨m, m', hne, hcol, rfl⟩
      simp only [ProbOracleComp.run_map, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
      refine (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
        (MeasureTheory.measure_mono ?_)).trans
          (jouxFinder_failure_le O step hstage D hD s hε f b (step t m) (hD t ht m))
      intro o ho hmem
      obtain ⟨pairs, rfl, hlen, hchain⟩ := hmem
      exact ho ⟨(m, m') :: pairs, rfl, by simp [hlen], hne, hcol, hchain⟩
    · intro a ha hna
      have ha' : a = none := by
        by_contra hsome
        exact hna (birthdayFinder_sound O (step t) (hstage t) _ s ha hsome)
      subst ha'
      exact (jouxFinder_failure_le O step hstage D hD s hε f (b + 1) t ht).trans_eq (by ring)

/-- **Success probability of the Joux finder.** Run against a deterministic oracle `O` under which
the step program `stage t m` returns `step t m`, from a value `t` in a finite set `D` closed under
`step`: if one birthday attempt with `s` uniform messages finds no collision with probability at
most `ε` (in the form that `birthdayFinder_success` proves, with `|D|` values), then `f` attempts
complete the `b` stages, returning a collision chain of length `b`, except with probability at
most `2 ^ b * ((1 + ε) / 2) ^ f / 2`. -/
theorem jouxFinder_success {stage : T → M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (step : T → M → T) (hstage : ∀ t m, (stage t m).run (fun x => pure (O x)) = pure (step t m))
    (D : Finset T) (hD : ∀ t ∈ D, ∀ m, step t m ∈ D) (s : ℕ) {ε : ℝ}
    (hε : Real.exp (-(s * (s - 1) / (2 * D.card))) + s.choose 2 * (Fintype.card M : ℝ)⁻¹ ≤ ε)
    (f b : ℕ) {t : T} (ht : t ∈ D) :
    1 - 2 ^ b * ((1 + ε) / 2) ^ f / 2 ≤
      ((ProbComp.eval ((jouxFinder stage (ProbComp.uniform M) s f b t).run
        fun x => pure (O x))).toOuterMeasure (jouxSuccess step b t)).toReal := by
  have h := jouxFinder_failure_le O step hstage D hD s hε f b t ht
  have hadd := Probability.PMF.toOuterMeasure_toReal_add_compl
    (ProbComp.eval ((jouxFinder stage (ProbComp.uniform M) s f b t).run fun x => pure (O x)))
    (jouxSuccess step b t)
  linarith

/-- With attempts that find no collision with probability at most `1/2`, a budget of `3 b`
attempts leaves success probability at least `1/2`: the bound is `(27/32) ^ b / 2`. -/
private theorem half_le_one_sub_budget_bound (b : ℕ) :
    (1 / 2 : ℝ) ≤ 1 - 2 ^ b * ((1 + 1 / 2) / 2) ^ (3 * b) / 2 := by
  have h2 : (2 : ℝ) ^ b * ((1 + 1 / 2) / 2) ^ (3 * b) = (27 / 32) ^ b := by
    rw [pow_mul, ← mul_pow]
    norm_num
  have h3 : ((27 : ℝ) / 32) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- The sample count `⌈2 √(2 ^ n)⌉ + 1` of Lemma 8.2 with messages at least seven bits longer than
digests: one attempt finds no collision with probability at most `1/2`. -/
private theorem birthday_failure_le_half {n ℓ : ℕ} (hℓ : n + 7 ≤ ℓ) :
    Real.exp (-(((⌈2 * Real.sqrt ((2 ^ n : ℕ) : ℝ)⌉₊ + 1 : ℕ) : ℝ) *
        (((⌈2 * Real.sqrt ((2 ^ n : ℕ) : ℝ)⌉₊ + 1 : ℕ) : ℝ) - 1) / (2 * 2 ^ n))) +
      (⌈2 * Real.sqrt ((2 ^ n : ℕ) : ℝ)⌉₊ + 1).choose 2 * ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 / 2 := by
  have hK : 100 * 2 ^ n ≤ 2 ^ ℓ := by
    calc 100 * 2 ^ n ≤ 2 ^ 7 * 2 ^ n := by norm_num
      _ = 2 ^ (n + 7) := by rw [pow_add, Nat.mul_comm]
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hq := Probability.PMF.half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le (N := 2 ^ n)
    (K := 2 ^ ℓ) (by positivity) hK
  push_cast at hq ⊢
  linarith

end Joux

/-! ### Merkle–Damgård chains with `ℓ`-bit blocks -/

section MerkleDamgard

variable {h : List Bool → List Bool → List Bool} {k : List Bool}

/-- The `n`-bit strings, as lists. -/
private noncomputable def digests (n : ℕ) : Finset (List Bool) :=
  (List.finite_length_eq Bool n).toFinset

private theorem mem_digests {n : ℕ} {t : List Bool} : t ∈ digests n ↔ t.length = n := by
  simp [digests]

private theorem card_digests (n : ℕ) : (digests n).card = 2 ^ n := by
  have h := (List.finite_length_eq Bool n).encard_eq_coe_toFinset_card
  rw [BitString.encard_setOf_length_eq] at h
  exact_mod_cast h.symm

/-- Joux's finder for a Merkle–Damgård chain with `ℓ`-bit blocks from `iv`, against the
compression function as an oracle: at most `f` attempts of `s` uniform blocks for `b` stages, one
compression call per block. -/
@[expose] noncomputable def merkleDamgardJouxFinder (ℓ s f b : ℕ) (iv : List Bool) :
    ProbOracleComp (fun _ : List Bool => List Bool)
      (Option (List (BitString ℓ × BitString ℓ))) :=
  jouxFinder (fun t (m : BitString ℓ) => ProbOracleComp.query (t ++ List.ofFn m))
    (ProbComp.uniform (BitString ℓ)) s f b iv

/-- **Cost of Joux's attack on a chain.** `merkleDamgardJouxFinder ℓ s f b iv` makes at most
`f * s` evaluations of the compression function on every path. This counts oracle calls only; it
is not a running time. -/
theorem isQueryBounded_merkleDamgardJouxFinder (ℓ s f b : ℕ) (iv : List Bool) :
    ProbOracleComp.IsQueryBounded (merkleDamgardJouxFinder ℓ s f b iv) (f * s) := by
  simpa [merkleDamgardJouxFinder] using
    isQueryBounded_jouxFinder (c := 1)
      (stage := fun t (m : BitString ℓ) =>
        ProbOracleComp.query (spec := fun _ : List Bool => List Bool) (t ++ List.ofFn m))
      (fun t m => ProbOracleComp.IsQueryBounded.query _) (ProbComp.uniform (BitString ℓ)) s f b iv

private theorem foldl_blockStep {ℓ : ℕ} (t : List Bool) (ms : List (BitString ℓ)) :
    ms.foldl (fun t m => h k (t ++ List.ofFn m)) t =
      merkleDamgardChain h k t (ms.map List.ofFn) := by
  simp [merkleDamgardChain, List.foldl_map]

/-- A collision chain of `ℓ`-bit blocks gives a `2 ^ b`-collision of the chain from `iv`, after
any common suffix of blocks ([BonehShoup2023], §8.4.1, printed p. 299). -/
theorem isMulticollision_merkleDamgardChain {ℓ : ℕ} {iv : List Bool}
    {pairs : List (BitString ℓ × BitString ℓ)}
    (hc : IsCollisionChain (fun t (m : BitString ℓ) => h k (t ++ List.ofFn m)) iv pairs)
    (tail : List (List Bool)) :
    IsMulticollision (fun bs => merkleDamgardChain h k iv (bs ++ tail)) (2 ^ pairs.length)
      ((Finset.univ.image (jouxMessage pairs)).image (List.map List.ofFn)) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (List.map_injective_iff.mpr List.ofFn_injective),
      Finset.card_image_of_injective _ hc.jouxMessage_injective, Finset.card_univ,
      BitString.card]
  · intro x hx y hy
    obtain ⟨_, hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hy'
    simp only [merkleDamgardChain_append, ← foldl_blockStep, hc.foldl_jouxMessage]

/-- The outputs of `merkleDamgardJouxFinder` that are `b` pairs whose `2 ^ b` selections, each
followed by any common list of blocks `tail`, are a `2 ^ b`-collision of the chain from `iv`. One
output serves every `tail`. `mem_multicollisionOutputs` unfolds membership. -/
def multicollisionOutputs (h : List Bool → List Bool → List Bool) (k : List Bool) (ℓ b : ℕ)
    (iv : List Bool) : Set (Option (List (BitString ℓ × BitString ℓ))) :=
  {o | ∃ pairs, o = some pairs ∧ pairs.length = b ∧ ∀ tail : List (List Bool),
    IsMulticollision (fun bs => merkleDamgardChain h k iv (bs ++ tail)) (2 ^ b)
      ((Finset.univ.image (jouxMessage pairs)).image (List.map List.ofFn))}

/-- Membership in `multicollisionOutputs`: `b` pairs whose selections, each followed by any common
list of blocks, are a `2 ^ b`-collision of the chain from `iv`. -/
theorem mem_multicollisionOutputs {ℓ b : ℕ} {iv : List Bool}
    {o : Option (List (BitString ℓ × BitString ℓ))} :
    o ∈ multicollisionOutputs h k ℓ b iv ↔
      ∃ pairs, o = some pairs ∧ pairs.length = b ∧ ∀ tail : List (List Bool),
        IsMulticollision (fun bs => merkleDamgardChain h k iv (bs ++ tail)) (2 ^ b)
          ((Finset.univ.image (jouxMessage pairs)).image (List.map List.ofFn)) :=
  Iff.rfl

private theorem jouxSuccess_subset_multicollisionOutputs (ℓ b : ℕ) (iv : List Bool) :
    jouxSuccess (fun t (m : BitString ℓ) => h k (t ++ List.ofFn m)) b iv ⊆
      multicollisionOutputs h k ℓ b iv := by
  rintro _ ⟨pairs, rfl, rfl, hc⟩
  exact ⟨pairs, rfl, rfl, isMulticollision_merkleDamgardChain hc⟩

/-- **Joux's attack on a chain, with its cost.** Let `h k` map `n + ℓ`-bit inputs to `n`-bit
outputs and let `iv` have `n` bits. With at most `f * s` compression evaluations
(`isQueryBounded_merkleDamgardJouxFinder`), `merkleDamgardJouxFinder` outputs `b` pairs such that,
for every common list of blocks `tail`, their `2 ^ b` selections, each followed by `tail`, are a
`2 ^ b`-collision of the chain, except with probability at most `2 ^ b * ((1 + ε) / 2) ^ f / 2`,
where `ε` bounds `exp (-s (s - 1) / 2 ^ (n + 1)) + C(s, 2) / 2 ^ ℓ`, the bound of Lemma 8.2 on the
probability that one attempt finds no collision. -/
theorem merkleDamgardJouxFinder_success {n ℓ : ℕ}
    (hlen : ∀ x, x.length = n + ℓ → (h k x).length = n)
    {iv : List Bool} (hiv : iv.length = n) (s : ℕ) {ε : ℝ}
    (hε : Real.exp (-(s * (s - 1) / (2 * 2 ^ n))) + s.choose 2 * ((2 : ℝ) ^ ℓ)⁻¹ ≤ ε)
    (f b : ℕ) :
    1 - 2 ^ b * ((1 + ε) / 2) ^ f / 2 ≤
      ((ProbComp.eval ((merkleDamgardJouxFinder ℓ s f b iv).run
        fun x => pure (h k x))).toOuterMeasure
          (multicollisionOutputs h k ℓ b iv)).toReal := by
  have key := jouxFinder_success (spec := fun _ : List Bool => List Bool)
    (stage := fun t (m : BitString ℓ) => ProbOracleComp.query (t ++ List.ofFn m))
    (h k) (fun t (m : BitString ℓ) => h k (t ++ List.ofFn m))
    (fun t m => ProbOracleComp.run_query _ _) (digests n)
    (fun t ht m => mem_digests.mpr (hlen _ (by simp [mem_digests.mp ht]))) s (ε := ε)
    (by rw [card_digests, BitString.card]; push_cast; exact hε) f b (mem_digests.mpr hiv)
  exact key.trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono (jouxSuccess_subset_multicollisionOutputs ℓ b iv)))

/-- **Joux's attack on a chain with `O(b 2 ^ (n/2))` compression evaluations**
([BonehShoup2023], §8.4.1, printed p. 299). Let `h k` map `n + ℓ`-bit inputs to `n`-bit outputs,
let `iv` have `n` bits, and let blocks be at least seven bits longer than chaining values
(`n + 7 ≤ ℓ`). With the sample count `s = ⌈2 √(2 ^ n)⌉ + 1` of Lemma 8.2 per attempt and a budget
of `3 b` attempts, `merkleDamgardJouxFinder` makes at most `3 b s` compression evaluations
(`isQueryBounded_merkleDamgardJouxFinder`), and with probability at least `1/2` it outputs `b`
pairs such that, for every common list of blocks `tail`, their `2 ^ b` selections, each followed by
`tail`, are a `2 ^ b`-collision. The book states "time `O(b 2 ^ (n/2))`" and no success
probability; the count here is of compression evaluations only, not a running time. -/
theorem merkleDamgardJouxFinder_success_half {n ℓ : ℕ}
    (hlen : ∀ x, x.length = n + ℓ → (h k x).length = n)
    {iv : List Bool} (hiv : iv.length = n) (hℓ : n + 7 ≤ ℓ) (b : ℕ) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardJouxFinder ℓ (⌈2 * Real.sqrt ((2 ^ n : ℕ) : ℝ)⌉₊ + 1)
        (3 * b) b iv).run fun x => pure (h k x))).toOuterMeasure
          (multicollisionOutputs h k ℓ b iv)).toReal :=
  (half_le_one_sub_budget_bound b).trans
    (merkleDamgardJouxFinder_success hlen hiv _ (birthday_failure_le_half hℓ) (3 * b) b)

end MerkleDamgard

/-! ### The library's one-bit-per-block `merkleDamgard` -/

section Library

variable {h : List Bool → List Bool → List Bool} {k : List Bool}

/-- Absorb the bits of `m` from the chaining value `t` as `merkleDamgard` does, one data block and
one compression call per bit. -/
def absorbBits (n : ℕ) (t m : List Bool) :
    ProbOracleComp (fun _ : List Bool => List Bool) (List Bool) :=
  m.foldlM (fun acc b => ProbOracleComp.query (acc ++ mdDataBlock n b)) t

/-- Against `h k`, `absorbBits n t m` continues the chain from `t` over the data blocks of `m`. -/
theorem run_absorbBits (n : ℕ) (t m : List Bool) :
    (absorbBits n t m).run (fun x => pure (h k x)) =
      pure (merkleDamgardChain h k t (m.map (mdDataBlock n))) := by
  induction m generalizing t with
  | nil => simp [absorbBits, ProbOracleComp.run_pure]
  | cons b m ih =>
    have := ih (h k (t ++ mdDataBlock n b))
    simp only [absorbBits] at this
    simp [absorbBits, List.foldlM_cons, ProbOracleComp.run_bind, ProbOracleComp.run_query, this]

/-- `absorbBits n t m` makes at most `m.length` compression calls. -/
theorem isQueryBounded_absorbBits (n : ℕ) (t m : List Bool) :
    ProbOracleComp.IsQueryBounded (absorbBits n t m) m.length := by
  induction m generalizing t with
  | nil => exact OracleComp.IsCostBounded.pure _ _
  | cons b m ih =>
    rw [absorbBits, List.foldlM_cons]
    refine OracleComp.IsCostBounded.mono (n := 1 + m.length) ?_ (by simp [Nat.add_comm])
    exact (ProbOracleComp.IsQueryBounded.query _).bind fun acc => ih acc

/-- Hashing a concatenation of `g`-bit groups with `merkleDamgard` continues the chain group by
group from the value after the marker block. -/
private theorem merkleDamgard_flatMap_ofFn {g : ℕ} (ms : List (BitString g)) :
    merkleDamgard h k (ms.flatMap List.ofFn) =
      ms.foldl (fun t m => merkleDamgardChain h k t ((List.ofFn m).map (mdDataBlock k.length)))
        (h k (List.replicate k.length false ++ mdEndBlock k.length)) := by
  simp only [merkleDamgard, mdBlocks, merkleDamgardChain_cons]
  generalize h k (List.replicate k.length false ++ mdEndBlock k.length) = t
  induction ms generalizing t with
  | nil => simp
  | cons m ms ih => simp [List.flatMap_cons, ih]

/-- Lists of `g`-bit groups of the same length with the same concatenation are equal. -/
private theorem flatMap_ofFn_inj {g : ℕ} {ms ms' : List (BitString g)}
    (hl : ms.length = ms'.length) (he : ms.flatMap List.ofFn = ms'.flatMap List.ofFn) :
    ms = ms' := by
  refine List.map_injective_iff.mpr List.ofFn_injective (List.eq_iff_flatten_eq.mpr ⟨?_, ?_⟩)
  · simpa [List.flatMap_def] using he
  · simp [Function.comp_def, hl]

/-- A collision chain of `g`-bit groups, from the value after the marker block, gives a
`2 ^ b`-collision of `merkleDamgard h k` among messages of `b * g` bits. -/
theorem isMulticollision_merkleDamgard_of_chain {g : ℕ}
    {pairs : List (BitString g × BitString g)}
    (hc : IsCollisionChain
      (fun t (m : BitString g) =>
        merkleDamgardChain h k t ((List.ofFn m).map (mdDataBlock k.length)))
      (h k (List.replicate k.length false ++ mdEndBlock k.length)) pairs) :
    IsMulticollision (merkleDamgard h k) (2 ^ pairs.length)
      (Finset.univ.image fun σ => (jouxMessage pairs σ).flatMap List.ofFn) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injective, Finset.card_univ, BitString.card]
    intro σ τ hστ
    exact hc.jouxMessage_injective (flatMap_ofFn_inj (by simp [jouxMessage]) hστ)
  · intro x hx y hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hy
    simp only [merkleDamgard_flatMap_ofFn, hc.foldl_jouxMessage]

/-- Joux's finder for the library's `merkleDamgard` with `n`-bit digests: one compression call for
the marker block, then at most `f` attempts of `s` uniform `g`-bit groups for `b` stages, `g`
compression calls per group. -/
noncomputable def merkleDamgardBitJouxFinder (n g s f b : ℕ) :
    ProbOracleComp (fun _ : List Bool => List Bool)
      (Option (List (BitString g × BitString g))) :=
  ProbOracleComp.query (List.replicate n false ++ mdEndBlock n) >>= fun t₀ =>
    jouxFinder (fun t (m : BitString g) => absorbBits n t (List.ofFn m))
      (ProbComp.uniform (BitString g)) s f b t₀

/-- **Cost of Joux's attack on `merkleDamgard`.** `merkleDamgardBitJouxFinder n g s f b` makes at
most `1 + f * (s * g)` evaluations of the compression function on every path. This counts oracle
calls only; it is not a running time. -/
theorem isQueryBounded_merkleDamgardBitJouxFinder (n g s f b : ℕ) :
    ProbOracleComp.IsQueryBounded (merkleDamgardBitJouxFinder n g s f b) (1 + f * (s * g)) :=
  (ProbOracleComp.IsQueryBounded.query _).bind fun t₀ =>
    isQueryBounded_jouxFinder (c := g)
      (fun t (m : BitString g) => by
        simpa using isQueryBounded_absorbBits n t (List.ofFn m))
      (ProbComp.uniform (BitString g)) s f b t₀

/-- The outputs of `merkleDamgardBitJouxFinder` that are `b` pairs whose `2 ^ b` selections are a
`2 ^ b`-collision of `merkleDamgard h k`. `mem_bitMulticollisionOutputs` unfolds membership. -/
def bitMulticollisionOutputs (h : List Bool → List Bool → List Bool) (k : List Bool) (g b : ℕ) :
    Set (Option (List (BitString g × BitString g))) :=
  {o | ∃ pairs, o = some pairs ∧ pairs.length = b ∧
    IsMulticollision (merkleDamgard h k) (2 ^ b)
      (Finset.univ.image fun σ => (jouxMessage pairs σ).flatMap List.ofFn)}

/-- Membership in `bitMulticollisionOutputs`: `b` pairs of `g`-bit groups whose selections are a
`2 ^ b`-collision of `merkleDamgard h k`. -/
theorem mem_bitMulticollisionOutputs {g b : ℕ} {o : Option (List (BitString g × BitString g))} :
    o ∈ bitMulticollisionOutputs h k g b ↔
      ∃ pairs, o = some pairs ∧ pairs.length = b ∧
        IsMulticollision (merkleDamgard h k) (2 ^ b)
          (Finset.univ.image fun σ => (jouxMessage pairs σ).flatMap List.ofFn) :=
  Iff.rfl

/-- **Joux's attack on `merkleDamgard`, with its cost.** Let `h k` map `2 n`-bit inputs to `n`-bit
outputs, where `n = k.length`. With at most `1 + f * (s * g)` compression evaluations
(`isQueryBounded_merkleDamgardBitJouxFinder`), `merkleDamgardBitJouxFinder` outputs `b` pairs of
`g`-bit groups whose `2 ^ b` selections are a `2 ^ b`-collision of `merkleDamgard h k` except with
probability at most `2 ^ b * ((1 + ε) / 2) ^ f / 2`, where `ε` bounds
`exp (-s (s - 1) / 2 ^ (n + 1)) + C(s, 2) / 2 ^ g`. -/
theorem merkleDamgardBitJouxFinder_success
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length) (g s : ℕ) {ε : ℝ}
    (hε : Real.exp (-(s * (s - 1) / (2 * 2 ^ k.length))) + s.choose 2 * ((2 : ℝ) ^ g)⁻¹ ≤ ε)
    (f b : ℕ) :
    1 - 2 ^ b * ((1 + ε) / 2) ^ f / 2 ≤
      ((ProbComp.eval ((merkleDamgardBitJouxFinder k.length g s f b).run
        fun x => pure (h k x))).toOuterMeasure (bitMulticollisionOutputs h k g b)).toReal := by
  have hD : ∀ t ∈ digests k.length, ∀ m : BitString g,
      merkleDamgardChain h k t ((List.ofFn m).map (mdDataBlock k.length)) ∈ digests k.length :=
    fun t ht m => mem_digests.mpr (length_merkleDamgardChain hlen (mem_digests.mp ht)
      (by simp))
  have ht₀ : h k (List.replicate k.length false ++ mdEndBlock k.length) ∈ digests k.length :=
    mem_digests.mpr (hlen _ (by simp; ring))
  have key := jouxFinder_success (spec := fun _ : List Bool => List Bool)
    (stage := fun t (m : BitString g) => absorbBits k.length t (List.ofFn m))
    (h k) (fun t (m : BitString g) =>
      merkleDamgardChain h k t ((List.ofFn m).map (mdDataBlock k.length)))
    (fun t m => run_absorbBits k.length t (List.ofFn m)) (digests k.length) hD s (ε := ε)
    (by rw [card_digests, BitString.card]; push_cast; exact hε) f b ht₀
  rw [merkleDamgardBitJouxFinder, ProbOracleComp.run_bind, ProbOracleComp.run_query, pure_bind]
  refine key.trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono ?_))
  rintro _ ⟨pairs, rfl, rfl, hc⟩
  exact ⟨pairs, rfl, rfl, isMulticollision_merkleDamgard_of_chain hc⟩

/-- **Joux's attack on `merkleDamgard` with the sample count of Lemma 8.2.** Let `h k` map
`2 n`-bit inputs to `n`-bit outputs, where `n = k.length`, and let groups have `g` bits, at least
seven more than a digest (`n + 7 ≤ g`). With `s = ⌈2 √(2 ^ n)⌉ + 1` samples per attempt and a
budget of `3 b` attempts, `merkleDamgardBitJouxFinder` makes at most `1 + 3 b s g` compression
evaluations (`isQueryBounded_merkleDamgardBitJouxFinder`) and outputs a `2 ^ b`-collision of
`merkleDamgard h k` with probability at least `1/2`. The factor `g ≥ n + 7` is the price of one
compression call per message bit, so this count is not the book's `O(b 2 ^ (n/2))`. -/
theorem merkleDamgardBitJouxFinder_success_half
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length) {g : ℕ}
    (hg : k.length + 7 ≤ g) (b : ℕ) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardBitJouxFinder k.length g
        (⌈2 * Real.sqrt ((2 ^ k.length : ℕ) : ℝ)⌉₊ + 1) (3 * b) b).run
          fun x => pure (h k x))).toOuterMeasure (bitMulticollisionOutputs h k g b)).toReal :=
  (half_le_one_sub_budget_bound b).trans
    (merkleDamgardBitJouxFinder_success hlen g _ (birthday_failure_le_half hg) (3 * b) b)

end Library

end Cslib.Crypto
