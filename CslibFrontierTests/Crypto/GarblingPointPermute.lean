/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Privacy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.OutputLength
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for point-and-permute garbling

A client of `CslibFrontier.Crypto.Primitives.Garbling.PointPermute` and its modules `Efficient`,
`Simulator` and `Privacy`, and of `CslibFrontier.Crypto.Primitives.Garbling.Efficient`, under
module encapsulation.

One AND gate is garbled by `PointPermute.scheme` at `k = 2`, with a family `xorFamily` that XORs
copies of the key into the tweak and with fixed coins. Encoding, evaluating and decoding gives the
AND of the two input bits on all four inputs, by computation. `scheme_isValid` gives the same
answer for every outcome of the randomized garbler at every `k > 0`, and
`ConventionalCircuit.eval_toCircuit` shows that the gate's translation to a circuit computes AND.

`Scheme.encGarbled`, declared with `enc_structure`, writes the same words as the former tuple
encoding `encPair encBits (encPair encBits encBits)` of `(F, e, d)`. `xorFamily` is computed in
polynomial time, so `scheme_isEfficient` applies to it, and its certificate for `Gb` bounds the
garbled AND gate by a polynomial in `k` for every outcome of the garbler; at `k = 2` the bound
covers the 49 bits computed above. For the same family the simulator `PointPermute.simWord` is
PPT. Run on the AND gate's topology at `k = 2` with fixed coins, it writes a view of the real
view's lengths whose garbled function and input do not depend on the output, and which evaluates
and decodes to the output it was given.

A pseudorandom family makes the scheme `prv.sim` secure. A concrete adversary chooses the AND gate
on the input `(true, false)`, saves a bit, and guesses from the saved bit and the decoding
information of the view. It is certified PPT, its guess takes both values on real views of its
query and on simulated views of its output, and the theorem gives it a PPT simulator with
negligible advantage.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingPointPermute

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling

/-! ### A run on one AND gate -/

/-- One AND gate on two inputs: `n = 2`, `m = 1`, `q = 1`, reading wires `1` and `2`. -/
def andGate : ConventionalCircuit := ⟨2, 1, 1, fun _ => 1, fun _ => 2, fun _ => (· && ·)⟩

/-- The AND gate is a valid conventional circuit. -/
def validAndGate : ValidCircuit := ⟨andGate, by decide⟩

/-- A keyed family on words: the tweak XORed with copies of the key. -/
def xorFamily (key t : List Bool) : List Bool := List.zipWith xor (key ++ key) (t ++ t ++ t)

/-- Fixed coins for `k = 2`: three permutation bits, then six 3-bit keys. -/
def coins : List Bool := List.ofFn fun i : Fin 21 => decide (i.val % 3 = 1)

/-- The AND gate garbled at `k = 2` on these coins. -/
def garbled : Scheme.Garbled := (PointPermute.scheme xorFamily).gb 2 validAndGate coins

/-- The coins have the length that `Gb` samples, so `garbled` is an outcome of `garble`. -/
example :
    garbled ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).garble 2 validAndGate)).support :=
  (PointPermute.scheme xorFamily).mem_support_eval_garble_iff.mpr ⟨coins, by decide, rfl⟩

/-- The garbled function has 49 bits: the header `(2, 2, 1, 1)` and one gate's two 2-bit wire
numbers and four 4-bit rows. -/
example : garbled.fn.length = 49 := by decide

/-- Garbling, encoding, evaluating and decoding computes AND on every input. `Ev` reads the header
through `PointPermute.fnDecoder`, whose body is not exposed; its inverse law `decode_enc` is. -/
example : ∀ x₀ x₁ : Bool,
    (PointPermute.scheme xorFamily).decode garbled.decInfo
      ((PointPermute.scheme xorFamily).evalGarbled garbled.fn
        ((PointPermute.scheme xorFamily).encode garbled.encInfo [x₀, x₁])) =
      some [x₀ && x₁] := by
  simp only [garbled, PointPermute.scheme, PointPermute.fnWord, PointPermute.evalWord,
    PointPermute.fnDecoder.decode_enc]
  decide

/-! ### Correctness from `scheme_isValid` -/

/-- Every outcome of the randomized garbler, at every `k > 0`, decodes the AND of the inputs. -/
example (k : ℕ) (hk : 0 < k) (x₀ x₁ : Bool) (g : Scheme.Garbled)
    (hg : g ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).garble k validAndGate)).support) :
    (PointPermute.scheme xorFamily).decode g.decInfo
      ((PointPermute.scheme xorFamily).evalGarbled g.fn
        ((PointPermute.scheme xorFamily).encode g.encInfo [x₀, x₁])) =
      some [x₀ && x₁] := by
  rw [(PointPermute.scheme_isValid xorFamily).correct k hk validAndGate [x₀, x₁] rfl g hg]
  cases x₀ <;> cases x₁ <;> rfl

/-- The AND gate as a circuit over the full binary basis computes AND. -/
example (x : Fin 2 → Bool) :
    List.ofFn ((ConventionalCircuit.toCircuit validAndGate).eval fullInterpretation x) =
      [x 0 && x 1] := by
  refine (ConventionalCircuit.eval_toCircuit validAndGate x).trans ?_
  revert x
  decide

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM Polynomial

/-- The encoded words of a garbled triple are unchanged by the `enc_structure` declaration. -/
example (g : Scheme.Garbled) :
    Scheme.encGarbled g = encPair encBits (encPair encBits encBits) (g.fn, g.encInfo, g.decInfo) :=
  rfl

/-- The family `xorFamily` is computed in polynomial time. -/
theorem xorFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorFamily p.1 p.2)
      (encPair encBits encBits) encBits := by
  polytime [xorFamily]

/-- **The efficiency certificate bounds the garbled AND gate.** The certificate for `Gb` in
`scheme_isEfficient` bounds the word of `Gb(1^k, f, r)` by a polynomial of the word of
`(1^k, f, r)`. For the AND gate the coins that `Gb` samples have `3 (2 k + 3)` bits, so the garbled
function of every outcome of the garbler is polynomially long in `k`; at `k = 2` the bound covers
the 49 bits of `garbled`. -/
example : ∃ P : Polynomial ℕ,
    (∀ k, ∀ g ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).garble k validAndGate)).support,
      g.fn.length ≤ P.eval k) ∧ 49 ≤ P.eval 2 := by
  obtain ⟨P, hP⟩ := (PointPermute.scheme_isEfficient xorFamily_polyTime).gb
    |>.exists_polynomial_eval_length_le X
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℕ, ∀ k r,
      r.length = (PointPermute.scheme xorFamily).coins k validAndGate →
      ((PointPermute.scheme xorFamily).gb k validAndGate r).fn.length ≤ Q.eval k := by
    refine ⟨P.comp (C 8 * X + C (2 * (encValidCircuit validAndGate).length + 11)),
      fun k r hr => ?_⟩
    have h := hP (k, validAndGate, r)
    have hr' : r.length = 3 * (2 * k + 3) := by
      rw [hr]
      simp only [Scheme.coins, PointPermute.scheme, validAndGate, andGate]
      ring
    simp only [eval_X, Scheme.encGarbled_apply, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate, hr'] at h
    have hlen : 8 * k + (2 * (encValidCircuit validAndGate).length + 11) =
        2 * k + 1 + (2 * (encValidCircuit validAndGate).length + 1 + 3 * (2 * k + 3)) := by
      ring
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, hlen]
    omega
  refine ⟨Q, fun k g hg => ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := (PointPermute.scheme xorFamily).mem_support_eval_garble_iff.mp hg
    exact hQ k r hr
  · exact (show 49 = garbled.fn.length by decide).trans_le (hQ 2 coins (by decide))

/-- The simulator of point-and-permute garbling keyed by `xorFamily` is PPT. -/
example : Cslib.Probability.IsPPTOn (encPair encUnary (encPair encBits encValidTopo)) encPrvView
    (fun (k, y, t) => PointPermute.simWord xorFamily k y t) :=
  PointPermute.isPPTOn_simWord xorFamily_polyTime

end Efficiency

/-! ### A run of the simulator on the AND gate's topology -/

/-- Coins for the simulator on the AND gate's topology at `k = 2`: seven 4-bit labels, one for each
of the three wires and four filler rows. -/
def simCoins : List Bool := List.ofFn fun i : Fin 28 => decide (i.val % 3 = 1)

/-- The simulated view at `k = 2` for the output `[y]` and the AND gate's topology on the coins
`r`. -/
def simView (r : List Bool) (y : Bool) : PrvView :=
  PointPermute.simViewWord xorFamily 2 [y] (phiTopo.phi validAndGate).1 r

/-- The coins have the length that the simulator samples. -/
example : simCoins.length = PointPermute.simCoinLen 2 validAndGate.1.n validAndGate.1.q := by
  decide

/-- A simulated view has the lengths of the real view: a garbled function as long as the 49 bits of
`garbled`, two 4-bit input labels and one decoding bit. Only the decoding bit depends on the
output. -/
example : (simView simCoins false).fn.length = garbled.fn.length ∧
    (simView simCoins false).input.length = 8 ∧ (simView simCoins false).decInfo.length = 1 ∧
    (simView simCoins true).fn = (simView simCoins false).fn ∧
    (simView simCoins true).input = (simView simCoins false).input ∧
    (simView simCoins true).decInfo ≠ (simView simCoins false).decInfo := by
  decide

/-- Evaluating a simulated view with `Ev` and decoding it with `De` gives the output it was
simulated for. -/
example : ∀ y : Bool,
    (PointPermute.scheme xorFamily).decode (simView simCoins y).decInfo
      ((PointPermute.scheme xorFamily).evalGarbled (simView simCoins y).fn
        (simView simCoins y).input) =
      some [y] := by
  simp only [simView, PointPermute.simViewWord, PointPermute.scheme, PointPermute.evalWord,
    PointPermute.fnDecoder.decode_enc]
  decide

/-! ### Privacy -/

/-- The guess of `andAdversary`: on a view, the conjunction of the saved bit and the view's first
decoding bit; on `⊥`, `false`. -/
def andGuess (state : Bool) (view : Option PrvView) : Bool :=
  view.elim false fun v => state && v.decInfo.headD false

/-- A concrete `prv.sim` adversary with a saved state: it chooses the AND gate on the input
`(true, false)`, saves the bit `true`, and guesses `andGuess` from the saved bit and the view. -/
def andAdversary : ℕ → PrvSimAdversary ValidCircuit Bool :=
  fun _ => ⟨fun _ => pure (⟨validAndGate, [true, false]⟩, true),
    fun state view => pure (andGuess state view)⟩

open Turing.MultiTapeTM in
/-- The adversary is uniform strict PPT, with its saved bit encoded by `encBool`; its guess reads
the decoding information of the encoded view. -/
theorem isPPT_andAdversary : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit)
    (encOption encPrvView) encBool encBool andAdversary where
  choose := ComputableInPolyTime.isPPTOn (ComputableInPolyTime.const _)
  guess := ComputableInPolyTime.isPPTOn
    (f := fun ((_, state, view) : ℕ × Bool × Option PrvView) => andGuess state view)
    (by polytime [andGuess])

/-- The real view of the adversary's query `(AND, (true, false))` at `k = 2` on the coins `r`. -/
def realView (r : List Bool) : PrvView :=
  let g := (PointPermute.scheme xorFamily).gb 2 validAndGate r
  ⟨g.fn, (PointPermute.scheme xorFamily).encode g.encInfo [true, false], g.decInfo⟩

/-- The real view on the garbler's coins `r` is an outcome of the real game's view. -/
example {r : List Bool} (hr : r.length = 21) :
    realView r ∈ (ProbComp.eval ((PointPermute.scheme xorFamily).prvView 2
      ⟨validAndGate, [true, false]⟩)).support := by
  simp only [Scheme.prvView, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff]
  exact ⟨_, (PointPermute.scheme xorFamily).mem_support_eval_garble_iff.mpr ⟨r, hr, rfl⟩, rfl⟩

/-- **The guess depends on the view and on the saved bit.** With the saved bit `true`, it guesses
`false` on the real view of its query from `coins` and `true` on the real view from the all-ones
coins, and likewise `false` and `true` on the simulated views of the query's output `[false]` from
`simCoins` and from the all-ones coins: neither world fixes its guess. With the saved bit `false`
it guesses `false`, and on `⊥` it guesses `false`. -/
example : andGuess true (some (realView coins)) = false ∧
    andGuess true (some (realView (List.replicate 21 true))) = true ∧
    andGuess true (some (simView simCoins false)) = false ∧
    andGuess true (some (simView (List.replicate 28 true) false)) = true ∧
    andGuess false (some (realView (List.replicate 21 true))) = false ∧
    andGuess true none = false := by
  decide

open Turing.MultiTapeTM in
/-- For a pseudorandom family, `prv.sim` security gives this adversary a PPT simulator whose
advantage is negligible. -/
example {family : List Bool → List Bool → List Bool}
    (h : Cslib.Crypto.PseudorandomFunction family) :
    ∃ S : ℕ → PrvSimulator ValidTopo,
      Cslib.Probability.IsPPTOn (encPair encUnary (encPair encBits encValidTopo)) encPrvView
        (fun (k, y, t) => S k y t) ∧
      Negligible fun k => prvSimAdvantage (PointPermute.scheme family) phiTopo k (S k)
        (andAdversary k) :=
  h.prvSim_pointPermute Bool encBool andAdversary isPPT_andAdversary

end CslibFrontierTests.Crypto.GarblingPointPermute
