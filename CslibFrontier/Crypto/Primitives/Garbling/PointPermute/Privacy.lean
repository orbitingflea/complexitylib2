/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Reduction
public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime

/-!
# Point-and-permute garbling is simulation private

The point-and-permute scheme `PointPermute.scheme family`, with masks from the label function of
a pseudorandom function `family`, is `prv.sim` secure with topology side information (`phiTopo`):
`PseudorandomFunction.prvSim_pointPermute`. The simulator is `PointPermute.simWord`, which does not
depend on the adversary, so the proof gives more than the definition asks
(`PseudorandomFunction.negligible_prvSimAdvantage_simWord`): one PPT simulator whose advantage
against every uniform strict PPT adversary is negligible.

The proof bounds the adversary's chosen circuits by a polynomial `P k` in the parameter, read from
the length bound of its choice stage. At every parameter with `8 P k ≤ 2 ^ k`, which holds from
some parameter on, the advantage is exactly `dyadicSize (P k)` times the label advantage of the
certified reduction `prvSimReduction` (`prvSimAdvantage_simWord_eq`), which is negligible by
`PseudorandomFunction.indistinguishable_label`.

This is this library's theorem about its variant of `Garble1` of [BellareHoangRogaway2012]; see
`CslibFrontier.Crypto.Primitives.Garbling.PointPermute` for the differences of the scheme. That
paper proves `prv.ind` over `Φ_topo` for `Garble1` under a secure dual-key cipher (Theorem 10,
§5.3, p. 21), with a dual-key cipher from a PRF in §5.5 (Theorem 11, p. 27); the statement and
proof here are a direct simulation proof, not a formalization of those theorems.

## Main results

* `Cslib.Crypto.PseudorandomFunction.negligible_prvSimAdvantage_simWord`: the advantage of every
  uniform strict PPT adversary against the simulator `simWord` is negligible.
* `Cslib.Crypto.PseudorandomFunction.prvSim_pointPermute`: point-and-permute garbling is `prv.sim`
  secure over `phiTopo`.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto

open Garbling Garbling.PointPermute Turing.MultiTapeTM Probability Filter

variable {family : List Bool → List Bool → List Bool}

/-- **One simulator serves every adversary.** For a pseudorandom function `family` and every
uniform strict PPT `prv.sim` adversary `B`, the `prv.sim` advantage of `B` against the simulator
`simWord family` for point-and-permute garbling with topology side information is negligible. -/
theorem PseudorandomFunction.negligible_prvSimAdvantage_simWord
    (h : PseudorandomFunction family) {σ : Type} {encσ : σ ↪ List Bool}
    {B : ℕ → PrvSimAdversary ValidCircuit σ}
    (hB : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) (encOption encPrvView)
      encBool encσ B) :
    Negligible fun k =>
      prvSimAdvantage (PointPermute.scheme family) phiTopo k (simWord family k) (B k) := by
  obtain ⟨c, d, hlen⟩ := hB.choose.length_le
  let P : ℕ → ℕ := fun k => c * (4 * (k + 1)) ^ d
  have hPpoly : ComputableInPolyTime P encUnary encUnary := by
    simp only [P]
    polytime
  have hP : ∀ k query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ P k := by
    intro k query state hmem _
    have h₁ := hlen (k, ()) (query, state) hmem
    have h₂ := n_add_q_le_length_encValidCircuit query.fn
    have h₃ : (encValidCircuit query.fn).length ≤
        (encPair (encQuery ValidCircuit encValidCircuit) encσ (query, state)).length := by
      simp only [length_encPair, encQuery_apply]
      omega
    have h₄ : (encPair encUnary encUnit (k, ())).length + 1 ≤ 4 * (k + 1) := by
      have hu : (encUnit ()).length = 0 := rfl
      simp only [length_encPair, encUnary_apply, List.length_replicate, hu]
      omega
    calc query.fn.1.n + query.fn.1.q
        ≤ c * ((encPair encUnary encUnit (k, ())).length + 1) ^ d := by omega
      _ ≤ P k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₄ _)
  have hW := isOraclePPT_prvSimReduction h.polyTime hB hPpoly
  have hneg := h.indistinguishable_label _ hW
  have hbound : ∀ k, (4 * (k + 1)) ^ d = 4 ^ d * (k + 1) ^ d := fun k => mul_pow _ _ _
  have hcap : PolynomiallyBounded fun k => dyadicSize (P k) := by
    refine polynomiallyBounded_iff_le.mpr ⟨2 * c * 4 ^ d + 2, d, fun k => ?_⟩
    have h₁ := dyadicSize_le (P k)
    have h₂ : 1 ≤ (k + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos k)
    simp only [P, hbound] at h₁ ⊢
    nlinarith
  have hsmall : PolynomiallyBounded fun k => 8 * P k := by
    refine polynomiallyBounded_iff_le.mpr ⟨8 * c * 4 ^ d, d, fun k => ?_⟩
    simp only [P, hbound]
    ring_nf
    exact le_rfl
  have hev : ∀ᶠ k in atTop, 8 * P k ≤ 2 ^ k :=
    hsmall.eventually_lt_two_pow.mono fun _ hk => hk.le
  refine negligible_of_eventually_le (hneg.polynomiallyBounded_mul hcap) ?_
  filter_upwards [hev] with k hk
  rw [prvSimAdvantage_simWord_eq family B P k (hP k) hk]

/-- **Point-and-permute garbling is `prv.sim` secure with topology side information**, for every
pseudorandom function `family`: for every uniform strict PPT adversary there is a PPT simulator,
on `(1^k, y, Φ_topo(f))` with topologies encoded by `encValidTopo`, whose advantage is negligible.
The simulator `simWord family` is the same for every adversary
(`PseudorandomFunction.negligible_prvSimAdvantage_simWord`). The model is the standard model with
uniform adversaries and a single `Garble` query, as in `Scheme.PrvSimSecure`. -/
theorem PseudorandomFunction.prvSim_pointPermute (h : PseudorandomFunction family) :
    (PointPermute.scheme family).PrvSimSecure phiTopo encValidCircuit encValidTopo :=
  fun _ _ _ hB => ⟨simWord family, isPPTOn_simWord h.polyTime,
    h.negligible_prvSimAdvantage_simWord hB⟩

end Cslib.Crypto
