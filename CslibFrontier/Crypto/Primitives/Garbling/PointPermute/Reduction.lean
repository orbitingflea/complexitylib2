/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The PRF reduction for the privacy of point-and-permute garbling

The `prv.sim` advantage of an adversary `B` against the simulator `simWord` of
`PointPermute.scheme family`, with topology side information, is exactly a step range times the
label advantage of an explicit, certified reduction (`prvSimAdvantage_simWord_eq`).

The proof is a hybrid over the wires. The garbler's coins give uniform keys and permutation bits,
so the real view of a query `(f, x)` is the typed real view of `toCircuit f` written as words; the
simulated view is the typed simulated view (`eval_simWord`). Hybrid view `j` on words is the typed
hybrid view `j` of `Privacy.lean`, and global hybrid `i` runs `B`'s choice and then hybrid `i` of
its circuit.

The reduction `prvSimReduction family B P` runs `B`'s choice of `(f, x)`, draws a step `j` below
`dyadicSize (P k)`, the garbler's coins and filler labels, asks its label oracle at the tweaks of
all `8 q` argument slots, and runs `B`'s guess on hybrid view `j` with the answers in the target
slots. Against any table it runs the typed reductions of `Privacy.lean`
(`eval_run_prvSimReduction`), so against the keyed label function it plays a uniform global hybrid
`j`, and against a random function global hybrid `j + 1` when distinct slots have distinct tweaks,
which holds while `8 q ≤ 2 ^ k`. When `P k` bounds the wires of every circuit `B` chooses, the
hybrids telescope (`Game.advantage_hybrid_average`). The reduction is uniform strict oracle PPT for
every adversary certified by `TwoStage.IsPPT` and every polynomial-time family
(`isOraclePPT_prvSimReduction`); the body of its hybrid view is written by `bodyWith`, whose
certificate it shares with the garbler and the simulator.

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.prvSimReduction`: the PRF reduction.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.prvSimAdvantage_simWord_eq`: the `prv.sim` advantage is the
  step range times the reduction's label advantage.
* `Cslib.Crypto.Garbling.PointPermute.isOraclePPT_prvSimReduction`: the reduction is oracle PPT.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Cslib.Circuits Probability ConventionalCircuit

variable {n m s : ℕ}

/-! ### The garbler's coins -/

/-- The position of the key of colour `c` of wire `w` among the keys of the garbler's coins. -/
private def keyIndex (w : Wire n s) (c : Bool) : Fin ((n + s) * 2) :=
  ⟨2 * w.toNat + (if c then 1 else 0), by have := w.toNat_lt; split <;> omega⟩

private theorem keyIndex_bijective :
    Function.Bijective (fun p : Wire n s × Bool => keyIndex p.1 p.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨w, c⟩ ⟨w', c'⟩ h
    have h' : 2 * w.toNat + (if c then 1 else 0) = 2 * w'.toNat + (if c' then 1 else 0) :=
      congrArg Fin.val h
    have hc : c = c' := by cases c <;> cases c' <;> simp at h' ⊢ <;> omega
    subst hc
    have hw : w.toNat = w'.toNat := by cases c <;> simp at h' <;> omega
    rw [Wire.toNat_injective hw]
  · rw [Fintype.card_prod, Fintype.card_congr (Wire.equivFin n s), Fintype.card_fin,
      Fintype.card_bool, Fintype.card_fin]

/-- **The garbler's coins are uniform keys and permutation bits.** Reading the permutation bit of
each wire and the key of each colour of each wire from uniform coins of the scheme's length gives
uniform and independent keys and permutation bits. -/
private theorem uniformList_map_keyFn_permFn (k n s : ℕ) :
    (BitString.uniformList ((n + s) * (2 * (k + 1) + 1))).map
        (fun coins => ((keyFn k coins : Wire n s × Bool → BitString (k + 1)),
          (permFn coins : Wire n s → Bool))) =
      PMF.uniformOfFintype ((Wire n s × Bool → BitString (k + 1)) × (Wire n s → Bool)) := by
  let keys : List Bool → Wire n s × Bool → BitString (k + 1) := fun back p =>
    BitString.ofList (k + 1) (BitString.listRow (k + 1) (keyIndex p.1 p.2) back)
  let perms : List Bool → Wire n s → Bool := fun front w =>
    BitString.ofList 1 (BitString.listRow 1 w.toNat front) 0
  have hkeys : (BitString.uniformList ((n + s) * 2 * (k + 1))).map keys =
      PMF.uniformOfFintype (Wire n s × Bool → BitString (k + 1)) :=
    BitString.uniformList_map_listRow_equiv (Equiv.ofBijective _ keyIndex_bijective) (k + 1)
  have hperms : (BitString.uniformList (n + s)).map perms =
      PMF.uniformOfFintype (Wire n s → Bool) := by
    have h := BitString.uniformList_map_listRow_equiv (Wire.equivFin n s) 1
    rw [mul_one] at h
    have hcomp : perms = ((Equiv.arrowCongr (Equiv.refl (Wire n s))
        (Equiv.funUnique (Fin 1) Bool)) : _ → _) ∘
          fun word i => BitString.ofList 1 (BitString.listRow 1 (Wire.equivFin n s i) word) := by
      funext front w
      rfl
    rw [hcomp, ← PMF.map_comp, h, PMF.uniformOfFintype_map_equiv]
  have hsplit : ∀ front, front.length = n + s → ∀ back : List Bool,
      ((keyFn k (front ++ back) : Wire n s × Bool → BitString (k + 1)),
        (permFn (front ++ back) : Wire n s → Bool)) = (keys back, perms front) := by
    intro front hfront back
    refine Prod.ext (funext fun ⟨w, c⟩ => ?_) (funext fun w => ?_)
    · simp only [keyFn, keyOf, keys, keyIndex, ← hfront, List.drop_left]
      congr 2
      cases c <;> simp
    · have hw := w.toNat_lt
      simp only [permFn, permOf, perms, BitString.ofList]
      rw [BitString.getD_listRow (by omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      simp
  rw [show (n + s) * (2 * (k + 1) + 1) = (n + s) + (n + s) * 2 * (k + 1) by ring,
    BitString.uniformList_add, PMF.map_bind]
  calc _ = (BitString.uniformList (n + s)).bind (fun front =>
          (BitString.uniformList ((n + s) * 2 * (k + 1))).map fun back =>
            (keys back, perms front)) := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
        rw [PMF.map_comp]
        congr 1
        funext back
        exact hsplit front (BitString.length_of_mem_support_uniformList hfront) back
    _ = ((PMF.uniformOfFintype (Wire n s → Bool)).bind fun perm =>
          (PMF.uniformOfFintype (Wire n s × Bool → BitString (k + 1))).map fun key =>
            (key, perm)) := by
        rw [← hperms, ← hkeys, PMF.bind_map]
        simp only [PMF.map_comp, Function.comp_def]
    _ = _ := by
        rw [← PMF.uniformOfFintype_map_equiv (Equiv.prodComm (Wire n s → Bool)
          (Wire n s × Bool → BitString (k + 1))), ← Cslib.Probability.PMF.uniformOfFintype_prod,
          PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk]

variable (family : List Bool → List Bool → List Bool)

/-- The real view on given coins is the typed view of the typed garbling with the keys and
permutation bits read from the coins. -/
private theorem prvViewWord_gb (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.1.n) (coins : List Bool) :
    (⟨((scheme family).gb k f coins).fn,
      (scheme family).encode ((scheme family).gb k f coins).encInfo x,
      ((scheme family).gb k f coins).decInfo⟩ : PrvView) =
      viewWord k _ ((garbleWith (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins)
        (permFn coins)).view (BitString.ofList f.1.n x)) := by
  rw [gb_eq_encodeGarbled]
  simp only [viewWord, encodeGarbled, garbleWith, Garbled.view, PrvView.mk.injEq, true_and,
    and_true]
  exact encodeWord_encInfo (n := f.1.n) _ hx

/-- **The real view is the typed real view.** For a valid circuit `f` and an input `x` of `f.n`
bits, the real view `(F, X, d)` of the query `(f, x)` at parameter `k` is the typed view of the
typed garbling of `toCircuit f`, with the keyed function and tweaks of the scheme, written as
words. -/
private theorem eval_prvView (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n) :
    ProbComp.eval ((scheme family).prvView k ⟨f, x⟩) =
      (ProbComp.eval (garble (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k))).map
          fun G => viewWord k _ (G.view (BitString.ofList f.1.n x)) := by
  have hcoins : (scheme family).coins k f = (f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1) := by
    rw [size_toCircuit]
    rfl
  simp only [Scheme.prvView, garble, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    Scheme.eval_garble, ProbComp.eval_uniform, hcoins, PMF.map_comp]
  have hfun : ((fun a : Scheme.Garbled => (⟨a.fn, (scheme family).encode a.encInfo x, a.decInfo⟩ :
      PrvView)) ∘ (scheme family).gb k f) =
      (fun p : (Wire f.1.n (toCircuit f).size × Bool → BitString (k + 1)) ×
          (Wire f.1.n (toCircuit f).size → Bool) => viewWord k _ ((garbleWith (toCircuit f)
        fullInterpretation (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) p.1
          p.2).view (BitString.ofList f.1.n x))) ∘
        (fun coins => ((keyFn k coins : Wire f.1.n (toCircuit f).size × Bool → _),
          (permFn coins : Wire f.1.n (toCircuit f).size → Bool))) :=
    funext fun coins => prvViewWord_gb family k f hx coins
  rw [hfun, ← PMF.map_comp, uniformList_map_keyFn_permFn,
    ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-! ### Tweaks -/

/-- **Distinct slots have distinct tweaks** while `8 q ≤ 2 ^ k`: slot `a` of row `ρ` of gate `g`
has the tweak `8 g + 2 rowIndex ρ + a`, which is below `2 ^ k`. -/
private theorem slotTweak_injective (k : ℕ) (f : ValidCircuit) (hk : 8 * f.1.q ≤ 2 ^ k) :
    Function.Injective (slotTweak (toCircuit f).topology k) := by
  have hbound : ∀ p : Slot (toCircuit f).topology,
      8 * p.1.1 + 2 * rowIndex p.1.2 + p.2 < 2 ^ k := by
    rintro ⟨⟨g, ρ⟩, a⟩
    have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
    have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
    have ha : a.val < 2 := a.isLt.trans_eq (arity_topology_toCircuit f g)
    dsimp only
    omega
  rintro ⟨⟨g, ρ⟩, a⟩ ⟨⟨g', ρ'⟩, a'⟩ h
  have h' := congrArg List.ofFn h
  simp only [slotTweak, tweak] at h'
  rw [BitString.ofFn_ofList (BitString.length_lowBits _ _),
    BitString.ofFn_ofList (BitString.length_lowBits _ _)] at h'
  have heq := BitString.lowBits_injective_of_lt (hbound ⟨⟨g, ρ⟩, a⟩) (hbound ⟨⟨g', ρ'⟩, a'⟩) h'
  dsimp only at heq
  have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
  have hρ' := rowIndex_lt_four (arity_topology_toCircuit f g') ρ'
  have ha : a.val < 2 := a.isLt.trans_eq (arity_topology_toCircuit f g)
  have ha' : a'.val < 2 := a'.isLt.trans_eq (arity_topology_toCircuit f g')
  have hgv : g.val = g'.val := by omega
  have hg : g = g' := Fin.ext hgv
  subst hg
  have hi : rowIndex ρ = rowIndex ρ' := by omega
  have hρeq : ρ = ρ' := by
    rw [← testBit_rowIndex_of_eq_two (arity_topology_toCircuit f g) ρ,
      ← testBit_rowIndex_of_eq_two (arity_topology_toCircuit f g) ρ', hi]
  subst hρeq
  have haeq : a = a' := Fin.ext (by omega)
  subst haeq
  rfl

/-! ### Hybrid views on words -/

/-- The value of wire `v`, numbered from `0`, in the plaintext evaluation of `f` on `x`. -/
private def wireBit (f : ConventionalCircuit) (x : List Bool) (v : ℕ) : Bool :=
  (f.wires x f.q).getD v false

/-- Row `i` of gate `g` of hybrid view `j` on words, at parameter `k`, from the garbler's coins
`kc`, the filler labels `sc` and the oracle's answers `rs`: a row that reads an inactive colour on
a wire numbered below `j` holds its filler label; any other row holds the gate's label for the
bits its colours encode, masked by the keyed function at its argument keys, except that the mask
of an argument slot reading the inactive colour of wire `j` is the answer to that slot's tweak,
the answer numbered `8 g + 2 i + a` for slot `a`. -/
private def hybRow (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) (g : Fin f.q) (i : ℕ) : List Bool :=
  let a := f.A g - 1
  let b := f.B g - 1
  let actA := wireBit f x a ^^ permOf kc a
  let actB := wireBit f x b ^^ permOf kc b
  if (i.testBit 1 ≠ actA ∧ a < j) ∨ (i.testBit 0 ≠ actB ∧ b < j) then
    simLabel k sc (f.n + f.q + 4 * g + i)
  else
    let bit := f.G g (i.testBit 1 ^^ permOf kc a) (i.testBit 0 ^^ permOf kc b)
    List.zipWith xor (labelOf k (f.n + f.q) kc (f.n + g) (bit ^^ permOf kc (f.n + g)))
      (List.zipWith xor
        (if i.testBit 1 ≠ actA ∧ a = j then rs.getD (8 * g + 2 * i) [] else
          labelWord family k (keyOf k (f.n + f.q) kc a (i.testBit 1)) (tweak k g i 0))
        (if i.testBit 0 ≠ actB ∧ b = j then rs.getD (8 * g + 2 * i + 1) [] else
          labelWord family k (keyOf k (f.n + f.q) kc b (i.testBit 0)) (tweak k g i 1)))

/-- Hybrid view `j` on words: the garbled function of the rows `hybRow`, the labels encoding `x`
and the permutation bits of the output wires. -/
private def hybViewWord (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) : PrvView where
  fn := encFn ((k, f.n, f.m, f.q), (List.ofFn fun g : Fin f.q =>
    BitString.lowBits (wireWidth f.n f.q) (f.A g) ++
      BitString.lowBits (wireWidth f.n f.q) (f.B g) ++
      (List.ofFn fun i : Fin 4 => hybRow family k f x j kc sc rs g i).flatten).flatten)
  input := (List.ofFn fun i : Fin f.n =>
    labelOf k (f.n + f.q) kc i (x.getD i false ^^ permOf kc i)).flatten
  decInfo := List.ofFn fun o : Fin f.m => permOf kc (f.n + f.q - f.m + o)

/-- The answers `rs` to the tweaks of the slots, as an oracle on slots: slot `a` of row `ρ` of gate
`g` reads answer number `8 g + 2 rowIndex ρ + a`, the number of its tweak. -/
private def replyOracle (k : ℕ) {τ : Circuit.Topology n m s} (rs : List (List Bool)) :
    Slot τ → BitString (k + 1) × Bool
  | ⟨⟨g, ρ⟩, a⟩ => labelOfWord k (rs.getD (8 * g + 2 * rowIndex ρ + a) [])

/-- An existential over the two arguments of a binary gate. -/
private theorem exists_fin_of_eq_two {r : ℕ} (hr : r = 2) (P : Fin r → Prop) :
    (∃ a, P a) ↔ P ⟨0, by omega⟩ ∨ P ⟨1, by omega⟩ := by
  subst hr
  exact Fin.exists_fin_two

/-- The plaintext of row `i < 4` of gate `g` of `toCircuit f`, with keys and permutation bits
read from the coins, as a word. -/
private theorem labelBits_plainRow (k : ℕ) (f : ValidCircuit) (kc : List Bool)
    (g : Fin (toCircuit f).size) (i : ℕ) :
    labelBits (plainRow (toCircuit f) fullInterpretation (keyFn k kc) (permFn kc)
        ⟨g, fun a => i.testBit ((toCircuit f).topology.arity g - 1 - a)⟩) =
      labelOf k (f.1.n + f.1.q) kc (f.1.n + g)
        (f.1.G (g.cast (size_toCircuit f)) (i.testBit 1 ^^ permOf kc (f.1.A (g.cast
          (size_toCircuit f)) - 1)) (i.testBit 0 ^^ permOf kc (f.1.B (g.cast
            (size_toCircuit f)) - 1)) ^^ permOf kc (f.1.n + g)) := by
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  simp only [plainRow, Circuit.topology]
  rw [lines_toCircuit f g]
  simp only [fullSignature, fullInterpretation, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, labelBits_keyFn, Wire.toNat_gate, Wire.toNat_ofNat, permFn, hq,
    Bool.add_eq_xor]
  rfl

/-- The value of wire `w` of `toCircuit f` on the input `x`. -/
private theorem trace_wires (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n)
    (w : Wire f.1.n (toCircuit f).size) :
    (toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x) w =
      wireBit f.1 x w.toNat := by
  rw [trace_toCircuit, BitString.ofFn_ofList hx, wireBit]

/-- Row `i` of gate `g` of hybrid view `j`, with the keys, permutation bits and filler labels read
from the coins and the answers `rs` in the target slots, as a word, is `hybRow`. -/
private theorem labelBits_hybridView (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.1.n) (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)}
    (hrs : ∀ w ∈ rs, w.length = k + 2) (hlen : 8 * f.1.q ≤ rs.length)
    (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.1.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) =
      hybRow family k f.1 x j kc sc rs (g.cast (size_toCircuit f)) i := by
  have harity := arity_topology_toCircuit f g
  have hw₀ : ((toCircuit f).topology.wires g ⟨0, by omega⟩).toNat =
      f.1.A (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hw₁ : ((toCircuit f).topology.wires g ⟨1, by omega⟩).toNat =
      f.1.B (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
  have hreply : ∀ a < 2, labelBits (labelOfWord k (rs.getD (8 * g + 2 * i + a) [])) =
      rs.getD (8 * g + 2 * i + a) [] := by
    intro a ha
    have hlt : 8 * g + 2 * i + a < rs.length := by omega
    apply labelBits_labelOfWord
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact hrs _ (List.getElem_mem hlt)
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have htb₀ : i.testBit ((toCircuit f).topology.arity g - 1 - 0) = i.testBit 1 := by
    rw [harity]
  have htb₁ : i.testBit ((toCircuit f).topology.arity g - 1 - 1) = i.testBit 0 := by
    rw [harity]
  simp only [hybridView, rowOf, simFillerRows]
  simp only [rowIndex_testBit_of_eq_two harity hi]
  rw [apply_ite labelBits]
  unfold hybRow
  refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
  · simp only [IsHidden, exists_fin_of_eq_two harity, htb₀, htb₁, activeColour, trace_wires f hx,
      permFn, hw₀, hw₁, Bool.add_eq_xor]
  · rw [labelBits_labelOfWord (length_simLabel _ _ _), hq]
    rfl
  · rw [labelBits_add, labelBits_plainRow k f kc g i, ← Fin.sum_congr' _ harity.symm,
      Fin.sum_univ_two, labelBits_add, hc₀, hc₁]
    congr 2
    · rw [apply_ite labelBits]
      refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
      · simp only [IsTarget, htb₀, activeColour, trace_wires f hx, permFn, hw₀, Bool.add_eq_xor]
      · simp only [replyOracle, rowIndex_testBit_of_eq_two harity hi, add_zero]
        exact hreply 0 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₀]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, htb₀, hq,
          Fin.val_cast]
    · rw [apply_ite labelBits]
      refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
      · simp only [IsTarget, htb₁, activeColour, trace_wires f hx, permFn, hw₁, Bool.add_eq_xor]
      · simp only [replyOracle, rowIndex_testBit_of_eq_two harity hi]
        exact hreply 1 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₁]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, htb₁, hq,
          Fin.val_cast]

/-- **The hybrid view on words is the typed hybrid view.** For a valid circuit `f`, an input `x`
of `f.n` bits and answers `rs` of `k + 2` bits to the tweaks of all slots, hybrid view `j` on words
is the words of the typed hybrid view `j` of `toCircuit f`, with the keys, permutation bits and
filler labels read from the coins and the answers in the target slots. -/
private theorem hybViewWord_eq (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n)
    (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)} (hrs : ∀ w ∈ rs, w.length = k + 2)
    (hlen : 8 * f.1.q ≤ rs.length) :
    hybViewWord family k f.1 x j kc sc rs = viewWord k (toCircuit f).topology
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.n x) j (keyFn k kc) (permFn kc)
        (simFillerRows k _ sc) (replyOracle k rs)) := by
  have hrow : ∀ (g : Fin (toCircuit f).size) (i : Fin 4),
      labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.1.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) = hybRow family k f.1 x j kc sc rs (g.cast (size_toCircuit f)) i :=
    fun g i => labelBits_hybridView family k f hx j kc sc hrs hlen g i.isLt
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  simp only [hybViewWord, viewWord, encodeFn, encodeBody, PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [gateWord_toCircuit, hrow]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [hybridView, encode, inputEncoding, labelBits_keyFn, Wire.toNat_input, hq, permFn,
      BitString.ofList, Bool.add_eq_xor]
  · congr 1
    funext o
    simp only [hybridView, outputDecoding, permFn, toNat_outputs_toCircuit]

/-! ### The reduction -/

/-- One step of collecting the oracle's answers at label parameter `k`: ask the tweak numbered by
the answers collected so far, `lowBits k` of that number, and keep the first `k + 2` bits of the
reply. Answer `8 g + 2 i + a` is then the answer to the tweak of slot `a` of row `i` of gate `g`. -/
private def replyStep (k : ℕ) (rs : List (List Bool)) :
    WordOracleComp Unit (List (List Bool)) :=
  (fun reply => rs ++ [reply]) <$> (List.take (k + 2) <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), BitString.lowBits k rs.length))

/-- **The PRF reduction** for a `prv.sim` adversary `B`, at label parameter `k`, with step range
`dyadicSize (P k)`: run `B`'s choice of a query `(f, x)`; when `x` has `f.n` bits, draw a step `j`,
the garbler's coins and filler labels, ask the oracle at the tweaks of the `8 q` slots, and run
`B`'s guess on hybrid view `j`; otherwise run `B`'s guess on `⊥`. -/
noncomputable def prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) : OracleDistinguisher :=
  fun k _ => do
    let (query, state) ← ProbOracleComp.sample ((B k).choose ())
    if query.input.length = query.fn.1.n then do
      let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (P k))
      let kc ← ProbOracleComp.sample
        (BitString.sampleList ((query.fn.1.n + query.fn.1.q) * (2 * (k + 1) + 1)))
      let sc ← ProbOracleComp.sample (BitString.sampleList (simCoinLen k query.fn.1.n query.fn.1.q))
      let rs ← OracleComp.iterate (8 * query.fn.1.q) (replyStep k) []
      ProbOracleComp.sample ((B k).guess state
        (some (hybViewWord family k query.fn.1 query.input j kc sc rs)))
    else ProbOracleComp.sample ((B k).guess state none)

/-- Against a label table `T`, the word oracle of `labelCodec k` answers a `k`-bit request with the
word of `T` at that tweak, and any other request with the empty word. -/
private theorem wordOracle_labelCodec (k : ℕ) (T : BitString k → BitString (k + 1) × Bool)
    (request : Unit × List Bool) :
    (labelCodec k).wordOracle (fun t => (pure (T t) : ProbComp _)) request =
      pure (if request.2.length = k then labelBits (T (BitString.ofList k request.2)) else []) := by
  obtain ⟨⟨⟩, word⟩ := request
  by_cases hword : word.length = k <;>
    simp [OracleCodec.wordOracle, labelCodec, OracleCodec.bitString, hword, labelBits]

/-- Against a label table `T`, collecting `c` answers gives the words of `T` at the tweaks
`lowBits k 0`, ..., `lowBits k (c - 1)`. -/
private theorem run_iterate_replyStep (k : ℕ) (T : BitString k → BitString (k + 1) × Bool)
    (c : ℕ) :
    ProbOracleComp.run (OracleComp.iterate c (replyStep k) [])
        ((labelCodec k).wordOracle fun t => pure (T t)) =
      pure ((List.range c).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih, pure_bind]
    simp only [replyStep, ProbOracleComp.run_map, ProbOracleComp.run_query, wordOracle_labelCodec,
      BitString.length_lowBits, ite_true, map_pure, List.length_map, List.length_range,
      List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.take_of_length_le (le_of_eq (length_labelBits _))]

/-- The answers collected from a label table, read as an oracle on the slots of `toCircuit f`,
are the table at the slots' tweaks. -/
private theorem replyOracle_table (k : ℕ) (f : ValidCircuit)
    (T : BitString k → BitString (k + 1) × Bool) (p : Slot (toCircuit f).topology) :
    replyOracle k ((List.range (8 * f.1.q)).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) p =
      T (slotTweak _ k p) := by
  obtain ⟨⟨g, ρ⟩, a⟩ := p
  have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
  have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
  have ha : a.val < 2 := a.isLt.trans_eq (arity_topology_toCircuit f g)
  have hlt : 8 * g + 2 * rowIndex ρ + a < 8 * f.1.q := by omega
  simp only [replyOracle, slotTweak, tweak, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some]
  apply ((labelCodec k).encodeReply 0).injective
  change labelBits _ = labelBits _
  rw [labelBits_labelOfWord (length_labelBits _)]

/-- **The word reduction runs the typed reductions.** Against every label table `T`, the reduction
for `B` at label parameter `k` runs `B`'s choice of `(f, x)` and, when `x` has `f.n` bits, the
typed reduction for a uniform step `j` below `dyadicSize (P k)` on `toCircuit f` with `B`'s guess
on the words of the view; otherwise `B`'s guess on `⊥`. -/
theorem eval_run_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ)
    (k : ℕ) (T : BitString k → BitString (k + 1) × Bool) :
    ProbComp.eval (((labelCodec k).adapt (prvSimReduction family B P k [])).run
        fun t => pure (T t)) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n then
          (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
            ProbComp.eval ((reduction (toCircuit query.fn) fullInterpretation
              (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
              (BitString.ofList query.fn.1.n query.input)
              (fun V => (B k).guess state (some (viewWord k _ V))) j).run
                fun t => pure (T t))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [prvSimReduction, OracleCodec.run_adapt, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hx
  swap
  · simp only [ProbOracleComp.run_sample]
  set f := query.fn
  set x := query.input
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  have hrs : ∀ w ∈ (List.range (8 * f.1.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))), w.length = k + 2 := by
    intro w hw
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
    exact length_labelBits _
  have hlen : 8 * f.1.q ≤ ((List.range (8 * f.1.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx))))).length := by simp
  have hfill : (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).map
      (simFillerRows k (toCircuit f).topology) =
        PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool) := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_prod_map_snd (α := Wire f.1.n (toCircuit f).size →
      BitString (k + 1) × Bool), ← uniformList_map_simCoins k _ (arity_topology_toCircuit f),
      PMF.map_comp]
    rfl
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, run_iterate_replyStep,
    ProbComp.eval_bind, pure_bind, ProbComp.eval_sampleDyadicIndex,
    BitString.eval_sampleList, PMF.bind_map, Function.comp_def,
    hybViewWord_eq family k f hx _ _ _ hrs hlen, eval_run_reduction]
  refine congrArg _ (funext fun j => ?_)
  rw [show simCoinLen k f.1.n f.1.q = simCoinLen k f.1.n (toCircuit f).size by rw [size_toCircuit],
    show (f.1.n + f.1.q) * (2 * (k + 1) + 1) = (f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1) by
      rw [size_toCircuit]]
  have hreply : (replyOracle k ((List.range (8 * f.1.q)).map fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) :
        Slot (toCircuit f).topology → BitString (k + 1) × Bool) =
      fun p => T (slotTweak _ k p) :=
    funext (replyOracle_table k f T)
  rw [hreply]
  set G : (Wire f.1.n (toCircuit f).size × Bool → BitString (k + 1)) →
      (Wire f.1.n (toCircuit f).size → Bool) →
        (Row (toCircuit f).topology → BitString (k + 1) × Bool) → PMF Bool :=
    fun key perm R => ProbComp.eval ((B k).guess state (some (viewWord k _
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.n x) j key perm R
          fun p => T (slotTweak _ k p))))) with hG
  have hinner : ∀ key perm, (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).bind
      (fun sc => G key perm (simFillerRows k _ sc)) =
        (PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool)).bind
          (G key perm) := by
    intro key perm
    rw [← hfill, PMF.bind_map]
    rfl
  calc _ = (BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).bind
          (fun kc => (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).bind
            fun sc => G (keyFn k kc) (permFn kc) (simFillerRows k _ sc)) := rfl
    _ = (BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).bind
          (fun kc => (PMF.uniformOfFintype (Row (toCircuit f).topology →
            BitString (k + 1) × Bool)).bind (G (keyFn k kc) (permFn kc))) := by
        simp only [hinner]
    _ = ((BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).map
          (fun kc => ((keyFn k kc : Wire f.1.n (toCircuit f).size × Bool → _),
            (permFn kc : Wire f.1.n (toCircuit f).size → Bool)))).bind
          (fun p => (PMF.uniformOfFintype (Row (toCircuit f).topology →
            BitString (k + 1) × Bool)).bind (G p.1 p.2)) := by
        rw [PMF.bind_map]
        rfl
    _ = _ := by
        rw [uniformList_map_keyFn_permFn, ← Cslib.Probability.PMF.uniformOfFintype_prod]
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
        rfl

/-! ### The exact bound -/

/-- Global hybrid `i` for `B` at parameter `k`: `B`'s choice of `(f, x)`, then, when `x` has `f.n`
bits, hybrid experiment `i` of `toCircuit f` with `B`'s guess on the words of the view; otherwise
`B`'s guess on `⊥`. -/
private noncomputable def prvSimHybrid {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k i : ℕ) : Game :=
  (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
    if query.input.length = query.fn.1.n then
      hybridGame (toCircuit query.fn) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList query.fn.1.n query.input)
        (fun V => (B k).guess state (some (viewWord k _ V))) i
    else ProbComp.eval ((B k).guess state none)

/-- The real `prv.sim` experiment is global hybrid `0`. -/
private theorem eval_prvSimExperiment_true {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ) (S : PrvSimulator ValidTopo) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k S (B k) true) =
      prvSimHybrid family B k 0 := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  have hin : (scheme family).inLen query.fn = query.fn.1.n := rfl
  dsimp only
  rw [hin]
  split_ifs with hx
  · rw [hybridGame_zero]
    simp only [ProbComp.eval_bind, realGame]
    rw [eval_prvView family k query.fn hx, PMF.bind_map]
    rfl
  · rfl

/-- The simulated `prv.sim` experiment is every global hybrid from the largest number of wires
on. -/
private theorem eval_prvSimExperiment_false {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k c : ℕ)
    (hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ c) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k (simWord family k) (B k) false) =
      prvSimHybrid family B k c := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨query, state⟩ hmem => ?_
  have hin : (scheme family).inLen query.fn = query.fn.1.n := rfl
  have hev : (scheme family).ev query.fn query.input = query.fn.1.evalCirc query.input := rfl
  dsimp only
  simp only [hin, hev, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hx
  · rw [hybridGame_of_le _ _ _ _ _ _ (by rw [size_toCircuit]; exact hc query state hmem hx)]
    simp only [ProbComp.eval_bind, simGame]
    have hy : BitString.ofList query.fn.1.m (query.fn.1.evalCirc query.input) =
        (toCircuit query.fn).eval fullInterpretation
          (BitString.ofList query.fn.1.n query.input) := by
      have h := eval_toCircuit query.fn (BitString.ofList query.fn.1.n query.input)
      rw [BitString.ofFn_ofList hx] at h
      rw [← h, BitString.ofList_ofFn]
    rw [eval_simWord, hy, PMF.bind_map]
    rfl
  · rfl

/-- Against the keyed label function, the reduction plays a uniform global hybrid below
`dyadicSize (P k)`. -/
private theorem eval_realExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ) (k : ℕ) :
    ProbComp.eval (PRF.realExperiment (PRF.label (PRF.atLevel family (k + 1)))
        ((labelCodec k).adapt (prvSimReduction family B P k []))) =
      (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
        prvSimHybrid family B k j := by
  simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction, prvSimHybrid]
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (Fin _))]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hx
  · rw [PMF.bind_comm]
    refine congrArg _ (funext fun j => ?_)
    rw [← eval_realExperiment_reduction]
    simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const, PMF.bind_const]

/-- Against a uniform random function, the reduction plays the next global hybrid, when every
valid query `B k` can choose has at most `P k` wires and `8 P k ≤ 2 ^ k`. -/
private theorem eval_idealExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ P k)
    (hk : 8 * P k ≤ 2 ^ k) :
    ProbComp.eval (PRF.idealExperiment ((labelCodec k).adapt (prvSimReduction family B P k []))) =
      (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
        prvSimHybrid family B k (j + 1) := by
  simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction, prvSimHybrid]
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (Fin _))]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨query, state⟩ hmem => ?_
  dsimp only
  split_ifs with hx
  · have htw := slotTweak_injective k query.fn (by
      have := hP query state hmem hx
      omega)
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun j => ?_)
    rw [← eval_idealExperiment_reduction _ _ _ _ htw]
    simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const, PMF.bind_const]

/-- **The `prv.sim` advantage against the simulator is the reduction's label advantage, times the
step range.** At parameter `k`, if every valid query `B k` can choose has at most `P k` wires and
`8 P k ≤ 2 ^ k`, the `prv.sim` advantage of `B k` against `simWord` is `dyadicSize (P k)` times
the finite PRF advantage of `prvSimReduction family B P` at label parameter `k`, read through
`labelCodec k`, against the label function of `family` at parameter `k + 1`. -/
theorem prvSimAdvantage_simWord_eq {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ P k)
    (hk : 8 * P k ≤ 2 ^ k) :
    prvSimAdvantage (scheme family) phiTopo k (simWord family k) (B k) =
      Probability.dyadicSize (P k) * PRF.advantage (PRF.label (PRF.atLevel family (k + 1)))
        ((labelCodec k).adapt (prvSimReduction family B P k [])) := by
  have hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n →
        query.fn.1.n + query.fn.1.q ≤ Probability.dyadicSize (P k) :=
    fun query state hmem hx => (hP query state hmem hx).trans (Probability.lt_dyadicSize _).le
  rw [prvSimAdvantage, Experiment.advantage, eval_prvSimExperiment_false family B k _ hc,
    eval_prvSimExperiment_true, Game.advantage_comm,
    Game.advantage_hybrid_average (prvSimHybrid family B k) _ _ le_rfl, PRF.advantage,
    eval_realExperiment_prvSimReduction, eval_idealExperiment_prvSimReduction family B P k hP hk]
  simp only [Fin.is_lt, ↓reduceIte]

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

variable {family}

/-- The active colour of wire `v`: its plaintext value plus its permutation bit. -/
private def actBit (ws kc : List Bool) (v : ℕ) : Bool := permOf ws v ^^ permOf kc v

/-- Whether the colour `c` of wire `v` is inactive and the wire is numbered below `j`. -/
private def hiddenBit (ws kc : List Bool) (j v : ℕ) (c : Bool) : Bool :=
  c != actBit ws kc v && decide (v < j)

/-- Whether the colour `c` of wire `v` is inactive and the wire is wire `j`. -/
private def targetBit (ws kc : List Bool) (j v : ℕ) (c : Bool) : Bool :=
  c != actBit ws kc v && decide (v = j)

/-- The mask term of slot `slot` of row `i` of gate `g` reading wire `v` with colour `c`: the
answer to its tweak when it is a target, the keyed function at its key otherwise. -/
private def maskWord (k n q j : ℕ) (ws kc : List Bool) (rs : List (List Bool)) (v : ℕ) (c : Bool)
    (g i slot : ℕ) : List Bool :=
  if targetBit ws kc j v c then rs.getD (8 * g + 2 * i + slot) [] else
    labelWord family k (keyOf k (n + q) kc v c) (tweak k g i slot)

/-- The plaintext word of row `i` of gate `g`, from its 0-indexed argument wires and truth table. -/
private def plainWord (k n q : ℕ) (kc : List Bool) (a b : ℕ) (t : List Bool) (g i : ℕ) :
    List Bool :=
  labelOf k (n + q) kc (n + g)
    (t.getD ((if i.testBit 1 ^^ permOf kc a then 2 else 0) +
      (if i.testBit 0 ^^ permOf kc b then 1 else 0)) false ^^ permOf kc (n + g))

/-- Row `i` of gate `g` of hybrid view `j`, from the plaintext wire values `ws`, the 0-indexed
argument wires `a` and `b` and the truth table `t` of the gate. -/
private def hybRowData (k n q j : ℕ) (ws kc sc : List Bool) (rs : List (List Bool)) (a b : ℕ)
    (t : List Bool) (g i : ℕ) : List Bool :=
  if hiddenBit ws kc j a (i.testBit 1) || hiddenBit ws kc j b (i.testBit 0) then
    simLabel k sc (n + q + 4 * g + i)
  else List.zipWith xor (plainWord k n q kc a b t g i)
    (List.zipWith xor (maskWord (family := family) k n q j ws kc rs a (i.testBit 1) g i 0)
      (maskWord (family := family) k n q j ws kc rs b (i.testBit 0) g i 1))

/-- Hybrid view `j` on words from the data of the circuit and its plaintext wire values: the body
is `bodyWith` of the gate list, with the rows `hybRowData` on argument wires capped at the number of
wire values. -/
private theorem hybViewWord_eq_data (k : ℕ) (f : ValidCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) :
    hybViewWord family k f.1 x j kc sc rs =
      ⟨encFn ((k, f.1.n, f.1.m, f.1.gateList.length),
          bodyWith f.1.n f.1.gateList.length ((f.1.wires x f.1.q).length + 1)
            (fun g => (f.1.gateList.getD g (0, 0, [])).1)
            (fun g => (f.1.gateList.getD g (0, 0, [])).2.1)
            (fun g a b i => hybRowData (family := family) k f.1.n f.1.gateList.length j
              (f.1.wires x f.1.q) kc sc rs a b (f.1.gateList.getD g (0, 0, [])).2.2 g i)),
        ((List.range f.1.n).map fun i =>
          labelOf k (f.1.n + f.1.gateList.length) kc i (permOf x i ^^ permOf kc i)).flatten,
        decInfoWord f.1 kc⟩ := by
  have hws : (f.1.wires x f.1.q).length = f.1.n + f.1.q := f.1.length_wires x le_rfl
  have hgate (g : Fin f.1.q) : f.1.gateList.getD g (0, 0, []) = (f.1.A g, f.1.B g,
      [f.1.G g false false, f.1.G g false true, f.1.G g true false, f.1.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  have hrow (g : Fin f.1.q) (i : Fin 4) :
      hybRowData (family := family) k f.1.n f.1.q j (f.1.wires x f.1.q) kc sc rs
        (min ((f.1.wires x f.1.q).length + 1) (f.1.A g) - 1)
        (min ((f.1.wires x f.1.q).length + 1) (f.1.B g) - 1)
        (f.1.gateList.getD g (0, 0, [])).2.2 g i = hybRow family k f.1 x j kc sc rs g i := by
    have hA := f.2.one_le_A g
    have hAB := f.2.A_lt_B g
    have hBg := f.2.B_lt_gate g
    simp only [topo] at hA hAB hBg
    have hcapA : min ((f.1.wires x f.1.q).length + 1) (f.1.A g) - 1 = f.1.A g - 1 := by
      rw [hws]; omega
    have hcapB : min ((f.1.wires x f.1.q).length + 1) (f.1.B g) - 1 = f.1.B g - 1 := by
      rw [hws]; omega
    simp only [hcapA, hcapB, hgate, hybRowData, hybRow, hiddenBit, targetBit, actBit, maskWord,
      plainWord, getD_table, add_zero]
    simp only [wireBit, permOf, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    rfl
  simp only [hybViewWord, ConventionalCircuit.length_gateList, List.map_range_eq_ofFn]
  rw [bodyWith_eq_ofFn f.1.A f.1.B (hybRow family k f.1 x j kc sc rs) (fun g => by rw [hgate])
    (fun g => by rw [hgate]) hrow]
  rfl

variable (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
  (encPair encBits encBits) encBits)

attribute [local fun_prop] labelWord_polyTime tweak_polyTime wireWidth_polyTime permOf_polyTime
  keyOf_polyTime labelOf_polyTime simLabel_polyTime

private theorem actBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {v : γ → ℕ} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => actBit (ws x) (kc x) (v x)) encIn encBool := by
  unfold actBit
  polytime

attribute [local fun_prop] actBit_polyTime

private theorem hiddenBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {j v : γ → ℕ} {c : γ → Bool} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hj : ComputableInPolyTime j encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun x => hiddenBit (ws x) (kc x) (j x) (v x) (c x)) encIn encBool := by
  unfold hiddenBit
  polytime

private theorem targetBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {j v : γ → ℕ} {c : γ → Bool} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hj : ComputableInPolyTime j encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun x => targetBit (ws x) (kc x) (j x) (v x) (c x)) encIn encBool := by
  unfold targetBit
  polytime

attribute [local fun_prop] hiddenBit_polyTime targetBit_polyTime

include hf in
private theorem maskWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q j v g i slot : γ → ℕ}
    {ws kc : γ → List Bool} {rs : γ → List (List Bool)} {c : γ → Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary)
    (hws : ComputableInPolyTime ws encIn encBits) (hkc : ComputableInPolyTime kc encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool)
    (hg : ComputableInPolyTime g encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary) :
    ComputableInPolyTime (fun x => maskWord (family := family) (k x) (n x) (q x) (j x) (ws x)
      (kc x) (rs x) (v x) (c x) (g x) (i x) (slot x)) encIn encBits := by
  unfold maskWord
  polytime

attribute [local fun_prop] maskWord_polyTime

private theorem plainWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q a b g i : γ → ℕ}
    {kc t : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hkc : ComputableInPolyTime kc encIn encBits)
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => plainWord (k x) (n x) (q x) (kc x) (a x) (b x) (t x) (g x)
      (i x)) encIn encBits := by
  unfold plainWord
  polytime

attribute [local fun_prop] plainWord_polyTime

include hf in
private theorem hybRowData_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q j a b g i : γ → ℕ}
    {ws kc sc t : γ → List Bool} {rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary)
    (hws : ComputableInPolyTime ws encIn encBits) (hkc : ComputableInPolyTime kc encIn encBits)
    (hsc : ComputableInPolyTime sc encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => hybRowData (family := family) (k x) (n x) (q x) (j x) (ws x)
      (kc x) (sc x) (rs x) (a x) (b x) (t x) (g x) (i x)) encIn encBits := by
  unfold hybRowData
  polytime

private theorem hybInput_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List Bool × List Bool =>
      ((List.range p.2.1).map fun i => labelOf p.1 (p.2.1 + p.2.2.1) p.2.2.2.2 i
        (permOf p.2.2.2.1 i ^^ permOf p.2.2.2.2 i)).flatten)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encBits encBits))))
      encBits := by
  polytime

/-- The input `(1^k, f, x, j, kc, sc, rs)` of the hybrid view. -/
private abbrev encHybInput :
    (ℕ × ValidCircuit × List Bool × ℕ × List Bool × List Bool × List (List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encValidCircuit (encPair encBits (encPair encUnary (encPair encBits
    (encPair encBits (encList encBits))))))

include hf in
/-- Hybrid view `j` on words is computed in polynomial time. -/
private theorem hybViewWord_polyTime :
    ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool × List Bool ×
        List (List Bool) =>
      hybViewWord family p.1 p.2.1.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2)
      encHybInput encPrvView := by
  let E := encHybInput
  have hk : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.1) E encUnary := ComputableInPolyTime.fst _ _
  have hf' : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.1) E encValidCircuit :=
    (ComputableInPolyTime.snd _ _).fst'
  have hx : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.2.1) E encBits :=
    (ComputableInPolyTime.snd _ _).snd'.fst'
  have hj : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.2.2.1) E encUnary :=
    (ComputableInPolyTime.snd _ _).snd'.snd'.fst'
  have hkc : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.2.2.2.1) E encBits :=
    (ComputableInPolyTime.snd _ _).snd'.snd'.snd'.fst'
  have hsc : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.2.2.2.2.1) E encBits :=
    (ComputableInPolyTime.snd _ _).snd'.snd'.snd'.snd'.fst'
  have hrs : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.2.2.2.2.2) E (encList encBits) :=
    (ComputableInPolyTime.snd _ _).snd'.snd'.snd'.snd'.snd'
  have hd := circuitData_polyTime.comp hf'
  have hn : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.1.1.n) E encUnary := hd.fst'
  have hm : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.1.1.m) E encUnary := hd.snd'.fst'
  have hg : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.1.1.gateList) E
      (encList (encPair encNat (encPair encNat encBits))) := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hg
  have hws : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool ×
      List Bool × List (List Bool) => p.2.1.1.wires p.2.2.1 p.2.1.1.q) E encBits :=
    wires_polyTime.comp (hf'.prod hx)
  have hp := ComputableInPolyTime.fst E (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hr := ComputableInPolyTime.snd E (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have ht := (ComputableInPolyTime.listGetDWithInput (hg.comp hp) hr.fst' (0, 0, [])).snd'.snd'
  have hrow := hybRowData_polyTime hf (hk.comp hp) (hn.comp hp) (hq.comp hp) (hj.comp hp)
    (hws.comp hp) (hkc.comp hp) (hsc.comp hp) (hrs.comp hp) hr.snd'.fst' hr.snd'.snd'.fst' ht
    hr.fst' hr.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hg.comp (ComputableInPolyTime.fst E encUnary)) (ComputableInPolyTime.snd _ _) (0, 0, [])
  have hbody := bodyWith_polyTime
    (n := fun p : ℕ × ValidCircuit × List Bool × ℕ × List Bool × List Bool × List (List Bool) =>
      p.2.1.1.n)
    (cap := fun p => (p.2.1.1.wires p.2.2.1 p.2.1.1.q).length + 1)
    (A := fun p g => (p.2.1.1.gateList.getD g (0, 0, [])).1)
    (B := fun p g => (p.2.1.1.gateList.getD g (0, 0, [])).2.1)
    (row := fun p g a b i => hybRowData (family := family) p.1 p.2.1.1.n p.2.1.1.gateList.length
      p.2.2.2.1 (p.2.1.1.wires p.2.2.1 p.2.1.1.q) p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 a b
      (p.2.1.1.gateList.getD g (0, 0, [])).2.2 g i)
    hn hq (by polytime) hgate.fst' hgate.snd'.fst' hrow
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => encFn z) encFn
      encBits := .of_eq fun _ => rfl
  have hfn := henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody)
  have hinput := hybInput_polyTime.comp (hk.prod (hn.prod (hq.prod (hx.prod hkc))))
  have hdec := decInfoWord_polyTime.comp (hf'.prod hkc)
  simp only [hybViewWord_eq_data]
  exact encPrvView_mk_polyTime hfn hinput hdec

/-- One reply step is strict oracle PPT, for a parameter computed in unary from the input. -/
private theorem isOraclePPTOn_replyStep {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary) :
    IsOraclePPTOn (encPair encIn (encList encBits)) (encList encBits)
      (fun p : γ × List (List Bool) => replyStep (k p.1) p.2) := by
  unfold replyStep
  exact IsOraclePPTOn.map_with' (IsOraclePPTOn.query_take' () (by polytime) (by polytime))
    (by polytime)

/-- A reply step appends one word of at most `k + 2` bits. -/
private theorem length_le_of_mem_support_replyStep {k : ℕ} {rs next : List (List Bool)}
    (hnext : next ∈ OracleComp.support (replyStep k rs)) :
    (encList encBits next).length ≤ (encList encBits rs).length + (2 * (k + 2) + 2) := by
  unfold replyStep at hnext
  obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, encBits_apply, List.length_take]
  omega

variable {σ : Type} {encσ : σ ↪ List Bool} {B : ℕ → PrvSimAdversary ValidCircuit σ}
  (hB : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) (encOption encPrvView)
    encBool encσ B)

/-- The state after `B`'s choice: the caller's input `(k, aux)` and the query and state. -/
private abbrev encChosen (encσ : σ ↪ List Bool) :
    ((ℕ × List Bool) × (Query ValidCircuit × σ)) ↪ List Bool :=
  encPair (encPair encUnary encBits) (encPair (encQuery ValidCircuit encValidCircuit) encσ)

/-- The state before the replies: the chosen state, the step, the garbler's coins and the filler
labels. -/
private abbrev encDrawn (encσ : σ ↪ List Bool) :
    ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair (encPair (encChosen encσ) encUnary) encBits) encBits

include hf hB in
/-- The valid branch of the reduction after the draws: collect the answers and run `B`'s guess on
the hybrid view. -/
private theorem isOraclePPTOn_prvSimGuess :
    IsOraclePPTOn (encDrawn encσ) encBool
      (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) × List Bool) × List Bool => do
        let rs ← OracleComp.iterate (8 * p.1.1.1.2.1.fn.1.q) (replyStep p.1.1.1.1.1) []
        ProbOracleComp.sample ((B p.1.1.1.1.1).guess p.1.1.1.2.2
          (some (hybViewWord family p.1.1.1.1.1 p.1.1.1.2.1.fn.1 p.1.1.1.2.1.input p.1.1.2 p.1.2
            p.2 rs)))) := by
  let E := encDrawn encσ
  have hk : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) ×
      List Bool) × List Bool => p.1.1.1.1.1) E encUnary := by polytime
  have hquery : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => p.1.1.1.2.1) E (encQuery ValidCircuit encValidCircuit) := by
    polytime
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hgates := (circuitData_polyTime.comp hfn).snd'.snd'
  have hq : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) ×
      List Bool) × List Bool => p.1.1.1.2.1.fn.1.q) E encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hgates
  have hcount : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => 8 * p.1.1.1.2.1.fn.1.q) E encUnary := by polytime
  have hrs := IsOraclePPTOn.iterateWith_of_bounded_growth' (Operation := Unit)
    (stateEncoding := encList encBits) hcount (ComputableInPolyTime.const (encIn := E) [])
    (isOraclePPTOn_replyStep hk) (growth := fun p => 2 * (p.1.1.1.1.1 + 2) + 2)
    (by
      refine ((hk.polyBounded_length.add hk.polyBounded_length).add (PolyBounded.const 6)).mono
        fun p => ?_
      simp only [encUnary_apply, List.length_replicate]
      omega)
    (fun p rs next hnext => length_le_of_mem_support_replyStep hnext)
  have hfst := ComputableInPolyTime.fst E (encList encBits)
  have hk' := hk.comp hfst
  have hquery' := hquery.comp hfst
  have hstate : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => p.1.1.1.2.2) E encσ :=
    (((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _))).snd').snd'
  have hj : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => p.1.1.2) E encUnary :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).snd'
  have hkc : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => p.1.2) E encBits := (ComputableInPolyTime.fst _ _).snd'
  have hsc : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      ℕ) × List Bool) × List Bool => p.2) E encBits := ComputableInPolyTime.snd _ _
  have hview := (hybViewWord_polyTime hf).comp (hk'.prod ((encQuery_fn_polyTime _ _ hquery').prod
    ((encQuery_input_polyTime _ _ hquery').prod ((hj.comp hfst).prod ((hkc.comp hfst).prod
      ((hsc.comp hfst).prod (ComputableInPolyTime.snd E (encList encBits))))))))
  have hprep := hk'.prod ((hstate.comp hfst).prod
    ((ComputableInPolyTime.optionSome encPrvView).comp hview))
  exact hrs.bind_with (hB.guess.preprocess hprep).isOraclePPTOn

include hf hB in
/-- The reduction after `B`'s choice: on a valid query draw the step, the garbler's coins and the
filler labels, collect the answers and run the guess on the hybrid view; otherwise run the guess
on `⊥`. -/
private theorem isOraclePPTOn_prvSimBranch {P : ℕ → ℕ}
    (hP : ComputableInPolyTime P encUnary encUnary) :
    IsOraclePPTOn (encChosen encσ) encBool
      (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) =>
        if p.2.1.input.length = p.2.1.fn.1.n then do
          let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (P p.1.1))
          let kc ← ProbOracleComp.sample
            (BitString.sampleList ((p.2.1.fn.1.n + p.2.1.fn.1.q) * (2 * (p.1.1 + 1) + 1)))
          let sc ← ProbOracleComp.sample
            (BitString.sampleList (simCoinLen p.1.1 p.2.1.fn.1.n p.2.1.fn.1.q))
          let rs ← OracleComp.iterate (8 * p.2.1.fn.1.q) (replyStep p.1.1) []
          ProbOracleComp.sample ((B p.1.1).guess p.2.2
            (some (hybViewWord family p.1.1 p.2.1.fn.1 p.2.1.input j kc sc rs)))
        else ProbOracleComp.sample ((B p.1.1).guess p.2.2 none)) := by
  let E := encChosen encσ
  have hk : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) => p.1.1) E
      encUnary := (ComputableInPolyTime.fst _ _).fst'
  have hquery : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) => p.2.1)
      E (encQuery ValidCircuit encValidCircuit) := (ComputableInPolyTime.snd _ _).fst'
  have hstate : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) => p.2.2)
      E encσ := (ComputableInPolyTime.snd _ _).snd'
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hd := circuitData_polyTime.comp hfn
  have hn : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) =>
      p.2.1.fn.1.n) E encUnary := hd.fst'
  have hq : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) =>
      p.2.1.fn.1.q) E encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hcond : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) =>
      decide (p.2.1.input.length = p.2.1.fn.1.n)) E encBool :=
    (ComputableTidilyInPolyTime.decide_eq' (ComputableInPolyTime.length_bits_comp hx).tidy
      hn.tidy).computableInPolyTime
  have hnone := (hB.guess.preprocess (hk.prod (hstate.prod
    (ComputableInPolyTime.const (encIn := E) (encOut := encOption encPrvView) none)))).isOraclePPTOn
    (Operation := Unit)
  have hj := (isPPTOn_sampleDyadicIndex (hP.comp hk)).isOraclePPTOn (Operation := Unit)
  have hlen : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ =>
      (p.1.2.1.fn.1.n + p.1.2.1.fn.1.q) * (2 * (p.1.1.1 + 1) + 1)) (encPair E encUnary)
      encUnary := by
    have hn' := hn.comp (ComputableInPolyTime.fst E encUnary)
    have hq' := hq.comp (ComputableInPolyTime.fst E encUnary)
    have hk' := hk.comp (ComputableInPolyTime.fst E encUnary)
    polytime
  have hkc := (isPPTOn_sampleList.preprocess hlen).isOraclePPTOn (Operation := Unit)
  have hsimLen : ComputableInPolyTime (fun p : (((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) ×
      List Bool => simCoinLen p.1.1.1.1 p.1.1.2.1.fn.1.n p.1.1.2.1.fn.1.q)
      (encPair (encPair E encUnary) encBits) encUnary := by
    have hf2 := (ComputableInPolyTime.fst E encUnary).comp
      (ComputableInPolyTime.fst (encPair E encUnary) encBits)
    have hn' := hn.comp hf2
    have hq' := hq.comp hf2
    have hk' := hk.comp hf2
    unfold simCoinLen
    polytime
  have hsc := (isPPTOn_sampleList.preprocess hsimLen).isOraclePPTOn (Operation := Unit)
  refine IsOraclePPTOn.ite' hcond ?_ hnone
  refine hj.bind_with ?_
  refine hkc.bind_with ?_
  refine hsc.bind_with ?_
  exact isOraclePPTOn_prvSimGuess hf hB

include hf hB in
/-- **Efficiency of the reduction.** For every family computed in polynomial time, every uniform
strict PPT `prv.sim` adversary `B` and every step range `P` computed in polynomial time in unary,
`prvSimReduction family B P` is uniform strict oracle PPT. -/
theorem isOraclePPT_prvSimReduction {P : ℕ → ℕ}
    (hP : ComputableInPolyTime P encUnary encUnary) :
    IsOraclePPT encBool (prvSimReduction family B P) := by
  have hchoose := (hB.choose.preprocess (prepare := fun a : ℕ × List Bool => (a.1, ()))
    ((ComputableInPolyTime.fst encUnary encBits).prod
      (ComputableInPolyTime.const ()))).isOraclePPTOn (Operation := Unit)
  exact hchoose.bind_with (isOraclePPTOn_prvSimBranch hf hB hP)

end Efficiency

end Cslib.Crypto.Garbling.PointPermute
