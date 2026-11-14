/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Replay
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.EncLen

/-!
# Saved coins independent of a generated auxiliary input

A polynomial bound on the length of the public inputs, substituted into an oracle machine's
clock, gives one polynomial coin budget depending only on the security parameter. A strict-PPT
generator supplies such a bound for its supported public inputs. Replay still truncates the
supplied tape at the original input-dependent clock. This padding preserves the joint output and
external state, without fixing the randomness of the handler.

## Main definitions

* `Cslib.Probability.savedCoinBudget`: one polynomial budget for a polynomial clock
  `c * (|(1ⁿ, pk)| + 1) ^ d` on every input `pk` of length at most `keyC * (n + 1) ^ keyD`.

## Main results

* `Cslib.Probability.polynomiallyBounded_savedCoinBudget`,
  `Cslib.Probability.computableInPolyTime_savedCoinBudget`,
  `Cslib.Probability.clock_le_savedCoinBudget`: polynomial growth, unary polynomial-time
  computability and the clock bound for `savedCoinBudget`.
* `Cslib.Probability.IsOraclePPT.exists_savedCoins_of_length_le`: key-independent padding for
  every public input within a given polynomial length bound, with the original efficient
  full-input replay.
* `Cslib.Probability.IsOraclePPT.exists_savedCoins_of_keyGen`: the same padding, with the bound
  derived from an actual strict-PPT key generator.

## References

Original padding consequence of `IsOraclePPTOn.exists_savedCoins` and `IsPPTOn.length_le`.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-- One polynomial budget for a polynomial clock `c * (|(1ⁿ, pk)| + 1) ^ d` on every input `pk` of
length at most `keyC * (n + 1) ^ keyD`. -/
@[expose] def savedCoinBudget (c d keyC keyD n : ℕ) : ℕ :=
  c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d

/-- The saved-coin budget is polynomial in the security parameter. -/
@[fun_prop] theorem polynomiallyBounded_savedCoinBudget (c d keyC keyD : ℕ) :
    PolynomiallyBounded (savedCoinBudget c d keyC keyD) := by
  unfold savedCoinBudget
  fun_prop

/-- The saved-coin budget is computable in polynomial time in unary. -/
@[fun_prop] theorem computableInPolyTime_savedCoinBudget (c d keyC keyD : ℕ) :
    ComputableInPolyTime (savedCoinBudget c d keyC keyD) encUnary encUnary := by
  unfold savedCoinBudget
  fun_prop

/-- On any input `pk` of length at most `keyC * (n + 1) ^ keyD`, the polynomial clock
`c * (|(1ⁿ, pk)| + 1) ^ d` is at most `savedCoinBudget c d keyC keyD n`. -/
theorem clock_le_savedCoinBudget (c d keyC keyD n : ℕ) {pk : List Bool}
    (hpk : pk.length ≤ keyC * (n + 1) ^ keyD) :
    c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d ≤
      savedCoinBudget c d keyC keyD n := by
  apply Nat.mul_le_mul_left c
  apply Nat.pow_le_pow_left
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  omega

/-- Bound the public input by `keyC * (n + 1) ^ keyD`, then use a coin law independent of that
input. The prefix cutoff remains the original machine clock. The replay equality holds for every
public input within the bound and every stateful handler. -/
theorem IsOraclePPT.exists_savedCoins_of_length_le {Operation β : Type}
    [DecidableEq Operation] {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPT output program) (keyC keyD : ℕ) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
      IsOraclePPTOn (encPair encBits encBits) encBits
        (fun p : List Bool × List Bool =>
          machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) ∧
      (∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d ≤
          savedCoinBudget c d keyC keyD n) ∧
      ∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        ∀ (Store : Type) (oracle : Operation × List Bool → StateT Store PMF (List Bool)) s,
        ProbOracleComp.runWith oracle (output <$> program n pk) s =
          (BitString.uniformList (savedCoinBudget c d keyC keyD n)).bind
            (fun coins => ProbOracleComp.runWith oracle
                (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
                  (coins.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
                  (encPair encUnary encBits (n, pk))) s) := by
  obtain ⟨k, Control, hfinite, machine, c, d, hefficient, hrun⟩ := h.on.exists_savedCoins
  refine ⟨k, Control, hfinite, machine, c, d, hefficient,
    fun n _ hpk => clock_le_savedCoinBudget c d keyC keyD n hpk, ?_⟩
  intro n pk hpk Store oracle s
  rw [hrun (n, pk) Store oracle s,
    ← BitString.uniformList_take (clock_le_savedCoinBudget c d keyC keyD n hpk), PMF.bind_map]
  rfl

/-- Generate the auxiliary word by an actual strict-PPT program, then use a coin law independent
of that word. The prefix cutoff remains the original machine clock. The replay equality holds
for every key satisfying the derived size bound and every stateful handler. -/
theorem IsOraclePPT.exists_savedCoins_of_keyGen {Operation Key β : Type}
    [DecidableEq Operation] {keyEncoding : Key ↪ List Bool} {output : β ↪ List Bool}
    {gen : ℕ → ProbComp (List Bool × Key)}
    (hgen : IsPPTOn encUnary (encPair encBits keyEncoding) gen)
    {program : ℕ → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPT output program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d keyC keyD : ℕ),
      (∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
        keys.1.length ≤ keyC * (n + 1) ^ keyD) ∧
      IsOraclePPTOn (encPair encBits encBits) encBits
        (fun p : List Bool × List Bool =>
          machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) ∧
      (∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d ≤
          savedCoinBudget c d keyC keyD n) ∧
      ∀ n pk, pk.length ≤ keyC * (n + 1) ^ keyD →
        ∀ (Store : Type) (oracle : Operation × List Bool → StateT Store PMF (List Bool)) s,
        ProbOracleComp.runWith oracle (output <$> program n pk) s =
          (BitString.uniformList (savedCoinBudget c d keyC keyD n)).bind
            (fun coins => ProbOracleComp.runWith oracle
                (machine.runCoins (fun op word => ProbOracleComp.query (op, word))
                  (coins.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
                  (encPair encUnary encBits (n, pk))) s) := by
  obtain ⟨keyC, keyD, hkeys⟩ := hgen.length_le
  obtain ⟨k, Control, hfinite, machine, c, d, hefficient, hbound, hrun⟩ :=
    h.exists_savedCoins_of_length_le keyC keyD
  refine ⟨k, Control, hfinite, machine, c, d, keyC, keyD, fun n keys hkeys' => ?_, hefficient,
    hbound, hrun⟩
  have hk := hkeys n keys hkeys'
  simp only [encUnary_apply, List.length_replicate] at hk
  exact (length_le_encPair_left encBits keyEncoding keys).trans hk

end Cslib.Probability
