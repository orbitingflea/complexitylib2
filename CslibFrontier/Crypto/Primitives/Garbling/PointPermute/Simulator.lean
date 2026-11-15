/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
public import CslibFrontier.Crypto.Primitives.Garbling.Privacy
public import CslibFrontier.Crypto.Primitives.Garbling.Games
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The simulator of point-and-permute garbling

The privacy simulator of `CslibFrontier.Crypto.Primitives.Garbling.Privacy` written on words, for
the point-and-permute scheme `PointPermute.scheme family` with topology side information
(`phiTopo`). The simulator `simWord family k y t` sees the parameter `k`, the output `y` and the
topology `t = (n, m, q, A, B)`. It samples one `(k + 2)`-bit label for each of the `n + q` wires
and four filler labels for each gate, and writes the view `(F, X, d)` (`simViewWord`): in each
gate's table, the row named by the colours of its argument wires' labels holds the gate's label
masked under their keys, and every other row holds a filler label; `X` lists the input wires'
labels, and `d` makes the output wires' colours decode to `y` when `y` has `m` bits.

The words written are those of the typed simulator `simulateWith` on `toCircuit f`, for every
valid circuit `f` of topology `t`, with the labels read from the coins (`simViewWord_eq`), and the
coins give uniform wire labels and filler rows (`uniformList_map_simCoins`). So the simulator's
output law is the typed simulator's (`eval_simWord`). Every view it writes for an output of `m`
bits, `m` the topology's output count, decodes to that output (`decodeWord_evalWord_simViewWord`).

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.viewWord`: the words `(F, X, d)` of a typed view.
* `Cslib.Crypto.Garbling.PointPermute.simViewWord`, `Cslib.Crypto.Garbling.PointPermute.simWord`:
  the simulated view on given coins, and the simulator.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.eval_simWord`: the simulator samples the words of the
  typed simulator's view.
* `Cslib.Crypto.Garbling.PointPermute.decodeWord_evalWord_simViewWord`: every view the simulator
  writes for an output of `m` bits, `m` the topology's output count, decodes to that output.
* `Cslib.Crypto.Garbling.PointPermute.isPPTOn_simWord`: the simulator is PPT.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Cslib.Circuits Probability ConventionalCircuit

/-! ### Labels as bit strings -/

/-- A label as a `(k + 2)`-bit string: the `k + 1` bits of its key, then its colour. -/
@[expose] def labelEquiv (k : ℕ) : BitString (k + 2) ≃ BitString (k + 1) × Bool where
  toFun bits := (Fin.init bits, bits (Fin.last _))
  invFun label := Fin.snoc label.1 label.2
  left_inv bits := Fin.snoc_init_self bits
  right_inv label := by simp

/-- The word of the label of a bit string is the bit string. -/
private theorem labelBits_labelEquiv {k : ℕ} (bits : BitString (k + 2)) :
    labelBits (labelEquiv k bits) = List.ofFn bits := by
  simp only [labelBits_apply, labelEquiv, Equiv.coe_fn_mk]
  rw [List.ofFn_succ' bits, List.concat_eq_append]
  rfl

/-- The label of a `(k + 2)`-bit word. -/
@[expose] def labelOfWord (k : ℕ) (word : List Bool) : BitString (k + 1) × Bool :=
  labelEquiv k (BitString.ofList (k + 2) word)

/-- The label of a `(k + 2)`-bit word has that word. -/
theorem labelBits_labelOfWord {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    labelBits (labelOfWord k word) = word := by
  rw [labelOfWord, labelBits_labelEquiv, BitString.ofFn_ofList hword]

/-- The key of the label of a `(k + 2)`-bit word is its first `k + 1` bits. -/
theorem ofFn_labelOfWord_fst {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    List.ofFn (labelOfWord k word).1 = word.take (k + 1) := by
  rw [← take_labelBits, labelBits_labelOfWord hword]

/-- The colour of the label of a word is its bit `k + 1`. -/
theorem labelOfWord_snd (k : ℕ) (word : List Bool) :
    (labelOfWord k word).2 = word.getD (k + 1) false := rfl

/-! ### The simulator's coins -/

/-- The number of coins of the simulator at parameter `k` for `n` inputs and `q` gates: one label
for each of the `n + q` wires, then four filler labels for each gate. -/
@[expose] def simCoinLen (k n q : ℕ) : ℕ := (n + q + q * 4) * (k + 2)

/-- Label `v` of the simulator's coins, their `(k + 2)`-bit block `v`. Wire `v` has label `v`;
row `i` of gate `g` has filler label `n + q + 4 g + i`. -/
@[expose] def simLabel (k : ℕ) (coins : List Bool) (v : ℕ) : List Bool :=
  BitString.listRow (k + 2) v coins

theorem length_simLabel (k : ℕ) (coins : List Bool) (v : ℕ) :
    (simLabel k coins v).length = k + 2 :=
  BitString.length_listRow _ _ _

variable {n m s : ℕ}

/-- The wire labels read from the simulator's coins: wire `w` has label number `w`. -/
@[expose] def simWireLabels (k : ℕ) (coins : List Bool) (w : Wire n s) :
    BitString (k + 1) × Bool :=
  labelOfWord k (simLabel k coins w.toNat)

/-- The filler rows read from the simulator's coins: row `ρ` of gate `g` has label number
`n + s + 4 g + rowIndex ρ`. -/
@[expose] def simFillerRows (k : ℕ) (τ : Circuit.Topology n m s) (coins : List Bool)
    (r : Row τ) : BitString (k + 1) × Bool :=
  labelOfWord k (simLabel k coins (n + s + 4 * r.1 + rowIndex r.2))

/-- A row of a binary gate has number below `4`. -/
theorem rowIndex_lt_four {r : ℕ} (hr : r = 2) (colours : Fin r → Bool) : rowIndex colours < 4 := by
  rw [rowIndex_of_eq_two hr]
  split_ifs <;> omega

/-- The position of each wire's label and each row's filler label among the simulator's coins. -/
private def simIndex (τ : Circuit.Topology n m s) (hτ : ∀ g, τ.arity g = 2) :
    Wire n s ⊕ Row τ → Fin (n + s + s * 4)
  | .inl w => ⟨w.toNat, by have := w.toNat_lt; omega⟩
  | .inr r => ⟨n + s + 4 * r.1 + rowIndex r.2, by
      have := rowIndex_lt_four (hτ r.1) r.2
      have := r.1.isLt
      omega⟩

private theorem simIndex_bijective (τ : Circuit.Topology n m s) (hτ : ∀ g, τ.arity g = 2) :
    Function.Bijective (simIndex τ hτ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro (w | ⟨g, ρ⟩) (w' | ⟨g', ρ'⟩) h <;> simp only [simIndex, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Wire.toNat_injective h)
    · have := w.toNat_lt; omega
    · have := w'.toNat_lt; omega
    · have hi := rowIndex_lt_four (hτ g) ρ
      have hi' := rowIndex_lt_four (hτ g') ρ'
      have hg : g = g' := Fin.ext (by omega)
      subst hg
      have hρ : rowIndex ρ = rowIndex ρ' := by omega
      have : ρ = ρ' := by
        rw [← testBit_rowIndex_of_eq_two (hτ g) ρ, ← testBit_rowIndex_of_eq_two (hτ g) ρ', hρ]
      subst this
      rfl
  · rw [Fintype.card_sum, Fintype.card_congr (Wire.equivFin n s), Fintype.card_fin,
      Fintype.card_sigma]
    simp [hτ, Finset.sum_const, Finset.card_univ]

/-- **The simulator's coins are uniform labels.** For a topology of binary gates, the wire labels
and filler rows read from uniform coins are uniform and independent. -/
theorem uniformList_map_simCoins (k : ℕ) (τ : Circuit.Topology n m s)
    (hτ : ∀ g, τ.arity g = 2) :
    (BitString.uniformList (simCoinLen k n s)).map
        (fun coins => ((simWireLabels k coins : Wire n s → _), simFillerRows k τ coins)) =
      PMF.uniformOfFintype
        ((Wire n s → BitString (k + 1) × Bool) × (Row τ → BitString (k + 1) × Bool)) := by
  let e := Equiv.ofBijective _ (simIndex_bijective τ hτ)
  let E : (Wire n s ⊕ Row τ → BitString (k + 2)) ≃
      (Wire n s → BitString (k + 1) × Bool) × (Row τ → BitString (k + 1) × Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k))
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k)))
  have h : (fun coins => ((simWireLabels k coins : Wire n s → _), simFillerRows k τ coins)) =
      (E : _ → _) ∘
        fun coins i => BitString.ofList (k + 2) (BitString.listRow (k + 2) (e i) coins) := by
    funext coins
    rfl
  rw [h, ← PMF.map_comp, simCoinLen, BitString.uniformList_map_listRow_equiv e (k + 2)]
  exact PMF.uniformOfFintype_map_equiv E

/-! ### The simulated view -/

variable (family : List Bool → List Bool → List Bool)

/-- Row `i` of gate `g` of the simulated garbled function at parameter `k` for the topology `t`:
the row named by the colours of the labels of the gate's argument wires holds the gate's label
masked by the keyed function at their keys; every other row holds its filler label. -/
@[expose] def simRow (k : ℕ) (t : Topo) (coins : List Bool) (g : Fin t.q) (i : ℕ) : List Bool :=
  let la := simLabel k coins (t.A g - 1)
  let lb := simLabel k coins (t.B g - 1)
  if i = (if la.getD (k + 1) false then 2 else 0) + (if lb.getD (k + 1) false then 1 else 0) then
    List.zipWith xor (simLabel k coins (t.n + g))
      (List.zipWith xor (labelWord family k (la.take (k + 1)) (tweak k g i 0))
        (labelWord family k (lb.take (k + 1)) (tweak k g i 1)))
  else simLabel k coins (t.n + t.q + 4 * g + i)

/-- The simulated view `(F, X, d)` at parameter `k` for the output `y` and the topology `t`, on the
simulator's coins: the garbled function with the header and wire numbers of `t` and the rows
`simRow`, the labels of the input wires, and the decoding bits that make the colours of the output
wires' labels decode to `y` when `y` has `t.m` bits. -/
@[expose] def simViewWord (k : ℕ) (y : List Bool) (t : Topo) (coins : List Bool) : PrvView where
  fn := encFn ((k, t.n, t.m, t.q), (List.ofFn fun g : Fin t.q =>
    BitString.lowBits (wireWidth t.n t.q) (t.A g) ++
      BitString.lowBits (wireWidth t.n t.q) (t.B g) ++
      (List.ofFn fun i : Fin 4 => simRow family k t coins g i).flatten).flatten)
  input := (List.ofFn fun i : Fin t.n => simLabel k coins i).flatten
  decInfo := List.ofFn fun o : Fin t.m =>
    (simLabel k coins (t.n + t.q - t.m + o)).getD (k + 1) false ^^ y.getD o false

/-- **The simulator** `S(1^k, y, φ)` of point-and-permute garbling with topology side information:
sample the coins and write the simulated view. -/
noncomputable def simWord (k : ℕ) (y : List Bool) (t : ValidTopo) : ProbComp PrvView := do
  let coins ← BitString.sampleList (simCoinLen k t.1.n t.1.q)
  return simViewWord family k y t.1 coins

/-- The words `(F, X, d)` of a typed view at parameter `k`: the garbled function of its table, the
words of its input labels in order, and its decoding bits. -/
@[expose] def viewWord (k : ℕ) (τ : Circuit.Topology n m s) (V : View τ (BitString (k + 1))) :
    PrvView where
  fn := encodeFn k τ V.table
  input := (List.ofFn fun i => labelBits (V.input i)).flatten
  decInfo := List.ofFn V.decoding

/-! ### The simulated view is the typed simulator's -/

/-- Row `i < 4` of a binary gate has number `i`. -/
theorem rowIndex_testBit_of_eq_two {r i : ℕ} (hr : r = 2) (hi : i < 4) :
    rowIndex (fun a : Fin r => i.testBit (r - 1 - a)) = i := by
  subst hr
  exact rowIndex_testBit hi

/-- Row `i < 4` of a binary gate has the colours `colours` exactly when `i` is their number. -/
private theorem testBit_eq_iff_of_eq_two {r i : ℕ} (hr : r = 2) (hi : i < 4)
    (colours : Fin r → Bool) :
    (fun a : Fin r => i.testBit (r - 1 - a)) = colours ↔ i = rowIndex colours := by
  constructor
  · rintro rfl
    exact (rowIndex_testBit_of_eq_two hr hi).symm
  · rintro rfl
    exact testBit_rowIndex_of_eq_two hr colours

/-- Row `i` of gate `g` of the typed simulated table, as a word, is `simRow`. -/
private theorem labelBits_simulateWith (k : ℕ) (f : ValidCircuit) (y : Fin f.1.m → Bool)
    (coins : List Bool) (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits ((simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) y (simWireLabels k coins) (simFillerRows k _ coins)).table
          (rowOf _ g i)) =
      simRow family k f.1.topo coins (g.cast (size_toCircuit f)) i := by
  have harity := arity_topology_toCircuit f g
  have hw₀ : ((toCircuit f).topology.wires g ⟨0, by omega⟩).toNat =
      f.1.A (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hw₁ : ((toCircuit f).topology.wires g ⟨1, by omega⟩).toNat =
      f.1.B (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  simp only [simulateWith, rowOf, simFillerRows, slotTweak]
  simp only [rowIndex_testBit_of_eq_two harity hi]
  simp only [testBit_eq_iff_of_eq_two harity hi, rowIndex_of_eq_two harity]
  rw [← Fin.sum_congr' _ harity.symm, Fin.sum_univ_two]
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  simp only [hc₀, hc₁, simRow, topo, simWireLabels, labelOfWord_snd, hw₀, hw₁, Wire.toNat_gate,
    Fin.val_cast]
  rw [apply_ite labelBits]
  refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
  · rw [labelBits_add, labelBits_add, ← labelWord_ofFn, ← labelWord_ofFn, ofFn_ofList_tweak,
      ofFn_ofList_tweak, labelBits_labelOfWord (length_simLabel _ _ _),
      ofFn_labelOfWord_fst (length_simLabel _ _ _), ofFn_labelOfWord_fst (length_simLabel _ _ _)]
  · have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
    rw [labelBits_labelOfWord (length_simLabel _ _ _), hq]

/-- **The simulated view is the typed simulator's.** For every valid circuit `f`, the simulated
view for the topology of `f` and the output `y` is the words of the typed simulated view of
`toCircuit f`, with the wire labels and filler rows read from the coins. -/
theorem simViewWord_eq (k : ℕ) (f : ValidCircuit) (y coins : List Bool) :
    simViewWord family k y f.1.topo coins = viewWord k (toCircuit f).topology
      (simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y) (simWireLabels k coins)
        (simFillerRows k _ coins)) := by
  have hrow : ∀ (g : Fin (toCircuit f).size) (i : Fin 4),
      labelBits ((simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y) (simWireLabels k coins)
        (simFillerRows k _ coins)).table (rowOf _ g i)) =
      simRow family k f.1.topo coins (g.cast (size_toCircuit f)) i :=
    fun g i => labelBits_simulateWith family k f _ coins g i.isLt
  simp only [simViewWord, viewWord, encodeFn, encodeBody, PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [gateWord_toCircuit, hrow]
    congr 2
    · simp only [topo, size_toCircuit]
    · simp only [topo]
      rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [simulateWith, simWireLabels, labelBits_labelOfWord (length_simLabel _ _ _),
      Wire.toNat_input, topo]
  · apply List.ext_getElem (by simp [topo])
    intro o h₁ h₂
    have ho := toNat_outputs_toCircuit f ⟨o, by simpa using h₂⟩
    simp only [List.getElem_ofFn, simulateWith, simWireLabels, labelOfWord_snd, Circuit.topology,
      ho, BitString.ofList, Bool.add_eq_xor, topo]

/-- **The simulator samples the typed simulator's view.** For every valid circuit `f` and output
`y`, the simulator on the topology of `f` samples the words of the typed simulator's view of
`toCircuit f`. -/
theorem eval_simWord (k : ℕ) (f : ValidCircuit) (y : List Bool) :
    ProbComp.eval (simWord family k y (phiTopo.phi f)) =
      (ProbComp.eval (simulate (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y))).map (viewWord k _) := by
  have hcoins : simCoinLen k f.1.n f.1.q = simCoinLen k f.1.n (toCircuit f).size := by
    rw [size_toCircuit]
  have hsim := uniformList_map_simCoins k (toCircuit f).topology (arity_topology_toCircuit f)
  have hview : simViewWord family k y f.1.topo =
      (fun p : (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) ×
          (Row (toCircuit f).topology → BitString (k + 1) × Bool) =>
        viewWord k _ (simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
          (slotTweak _ k) (BitString.ofList f.1.m y) p.1 p.2)) ∘
        (fun coins => (simWireLabels k coins, simFillerRows k _ coins)) :=
    funext fun coins => simViewWord_eq family k f y coins
  change ProbComp.eval (do
      let coins ← BitString.sampleList (simCoinLen k f.1.n f.1.q)
      return simViewWord family k y f.1.topo coins) = _
  simp only [simulate, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_uniform, BitString.eval_sampleList, hcoins]
  rw [hview, ← PMF.map_comp, hsim, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **Simulated views decode to the output.** For every valid topology `t`, every output `y` of
`t.m` bits and all coins, decoding the evaluation of the simulated garbled input gives `y`. -/
theorem decodeWord_evalWord_simViewWord (k : ℕ) (t : ValidTopo) {y : List Bool}
    (hy : y.length = t.1.m) (coins : List Bool) :
    decodeWord (simViewWord family k y t.1 coins).decInfo
      (evalWord family (simViewWord family k y t.1 coins).fn
        (simViewWord family k y t.1 coins).input) = some y := by
  have ht : (mTopoInv t).1.topo = t.1 := rfl
  rw [← ht, simViewWord_eq]
  simp only [viewWord]
  rw [evalWord_encodeFn family k (mTopoInv t) _ _ _ (evalStep_simulateWith _ _ _ _ _ _),
    decodeWord_ofFn]
  congr 1
  have hdec : decode (simulateWith (toCircuit (mTopoInv t)).topology
      (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
      (BitString.ofList (mTopoInv t).1.m y) (simWireLabels k coins)
      (simFillerRows k _ coins)).decoding
      (fun o => simWireLabels k coins ((toCircuit (mTopoInv t)).outputs o)) =
      BitString.ofList (mTopoInv t).1.m y := by
    funext o
    have ho : (toCircuit (mTopoInv t)).topology.outputs o = (toCircuit (mTopoInv t)).outputs o :=
      rfl
    simp only [decode, simulateWith, ho]
    rw [← add_assoc, BooleanRing.add_self, zero_add]
  rw [hdec, BitString.ofFn_ofList (n := (mTopoInv t).1.m) hy]

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

variable {family}

/-- A label read at or beyond the end of the coins is the all-`false` word, wherever it is read. -/
private theorem simLabel_min (k : ℕ) (coins : List Bool) (v : ℕ) :
    simLabel k coins (min coins.length v) = simLabel k coins v := by
  rcases le_total coins.length v with h | h
  · rw [min_eq_left h]
    have hbeyond (u : ℕ) (hu : coins.length ≤ u) :
        simLabel k coins u = List.replicate (k + 2) false := by
      simp only [simLabel, BitString.listRow]
      rw [List.drop_eq_nil_of_le (by nlinarith), List.nil_append,
        List.take_of_length_le (by simp)]
    rw [hbeyond _ le_rfl, hbeyond _ h]
  · rw [min_eq_right h]

/-- Row `i` of gate `g` of the simulated table, from the 0-indexed argument wires `a` and `b`. -/
private def simRowData (k n q : ℕ) (coins : List Bool) (a b g i : ℕ) : List Bool :=
  let la := simLabel k coins a
  let lb := simLabel k coins b
  if i = (if la.getD (k + 1) false then 2 else 0) + (if lb.getD (k + 1) false then 1 else 0) then
    List.zipWith xor (simLabel k coins (n + g))
      (List.zipWith xor (labelWord family k (la.take (k + 1)) (tweak k g i 0))
        (labelWord family k (lb.take (k + 1)) (tweak k g i 1)))
  else simLabel k coins (n + q + 4 * g + i)

/-- The simulated view from the data of the topology: the body is `bodyWith` of the gate list,
with the rows `simRowData` on argument wires capped at the length of the coins. -/
private theorem simViewWord_eq_data (k : ℕ) (y : List Bool) (t : Topo) (coins : List Bool) :
    simViewWord family k y t coins =
      ⟨encFn ((k, t.n, t.m, t.gateList.length), bodyWith t.n t.gateList.length (coins.length + 1)
          (fun g => (t.gateList.getD g (0, 0)).1) (fun g => (t.gateList.getD g (0, 0)).2)
          (fun g a b i => simRowData (family := family) k t.n t.gateList.length coins a b g i)),
        ((List.range t.n).map (simLabel k coins)).flatten,
        (List.range t.m).map fun o =>
          permOf (simLabel k coins (t.n + t.gateList.length - t.m + o)) (k + 1) ^^ permOf y o⟩ := by
  have hgate (g : Fin t.q) : t.gateList.getD g (0, 0) = (t.A g, t.B g) := by
    simp [Topo.gateList, List.getD_eq_getElem?_getD]
  have hcap (V : ℕ) : min (coins.length + 1) V - 1 = min coins.length (V - 1) := by omega
  simp only [simViewWord, Topo.length_gateList, List.map_range_eq_ofFn]
  rw [bodyWith_eq_ofFn t.A t.B (simRow family k t coins) (fun g => by rw [hgate])
    (fun g => by rw [hgate]) (fun g i => by simp only [simRow, simRowData, hcap, simLabel_min])]
  rfl

variable (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
  (encPair encBits encBits) encBits)

attribute [local fun_prop] labelWord_polyTime tweak_polyTime wireWidth_polyTime permOf_polyTime

/-- Labels of the simulator's coins are read in polynomial time. -/
theorem simLabel_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k v : γ → ℕ}
    {coins : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => simLabel (k x) (coins x) (v x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ => simLabel p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encUnary)) encBits := by
    polytime [simLabel, BitString.listRow]
  exact h.comp (hk.prod (hcoins.prod hv))

attribute [local fun_prop] simLabel_polyTime

include hf in
private theorem simRowData_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q a b g i : γ → ℕ}
    {coins : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary) (hq : ComputableInPolyTime q encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => simRowData (family := family) (k x) (n x) (q x) (coins x)
      (a x) (b x) (g x) (i x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List Bool) × (ℕ × ℕ) × ℕ × ℕ =>
        simRowData (family := family) p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1.1 p.2.1.2
          p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary encBits)))
        (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) encBits := by
    polytime [simRowData]
  exact h.comp ((hk.prod (hn.prod (hq.prod hcoins))).prod ((ha.prod hb).prod (hg.prod hi)))

attribute [local fun_prop] simRowData_polyTime

private theorem simInput_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool =>
      ((List.range p.2.1).map (simLabel p.1 p.2.2)).flatten)
      (encPair encUnary (encPair encUnary encBits)) encBits := by
  polytime

private theorem simDecInfo_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ × ℕ × List Bool =>
      (List.range p.2.2.2.1).map fun o =>
        permOf (simLabel p.1 p.2.2.2.2.2 (p.2.2.1 + p.2.2.2.2.1 - p.2.2.2.1 + o)) (p.1 + 1) ^^
          permOf p.2.1 o)
      (encPair encUnary (encPair encBits (encPair encUnary (encPair encUnary
        (encPair encUnary encBits))))) encBits := by
  polytime

/-- The input `(1^k, y, t)` of the simulator. -/
private abbrev encSimInput : (ℕ × List Bool × ValidTopo) ↪ List Bool :=
  encPair encUnary (encPair encBits encValidTopo)

private theorem simTopoData_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × ValidTopo =>
      (x.2.2.1.n, x.2.2.1.m, x.2.2.1.gateList)) encSimInput encTopoData :=
  topoData_polyTime.comp (ComputableInPolyTime.snd _ _).snd'

private theorem simGateCount_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × ValidTopo => x.2.2.1.gateList.length)
      encSimInput encUnary :=
  (ComputableInPolyTime.length_list _).comp
    simTopoData_polyTime.snd'.snd'

private theorem simCoinLen_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × ValidTopo =>
      simCoinLen x.1 x.2.2.1.n x.2.2.1.gateList.length) encSimInput encUnary := by
  have hk : ComputableInPolyTime (fun x : ℕ × List Bool × ValidTopo => x.1) encSimInput
      encUnary := ComputableInPolyTime.fst _ _
  have hn : ComputableInPolyTime (fun x : ℕ × List Bool × ValidTopo => x.2.2.1.n) encSimInput
      encUnary := simTopoData_polyTime.fst'
  have hq := simGateCount_polyTime
  unfold simCoinLen
  polytime

include hf in
private theorem simViewWord_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool =>
      simViewWord family p.1.1 p.1.2.1 p.1.2.2.1 p.2) (encPair encSimInput encBits)
      encPrvView := by
  let E' := encPair encSimInput encBits
  have hfst : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool => p.1) E'
      encSimInput := ComputableInPolyTime.fst _ _
  have hk' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool => p.1.1) E'
      encUnary := (ComputableInPolyTime.fst _ _).comp hfst
  have hy' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool => p.1.2.1) E'
      encBits := (ComputableInPolyTime.snd _ _).fst'.comp hfst
  have hn' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool =>
      p.1.2.2.1.n) E' encUnary := simTopoData_polyTime.fst'.comp hfst
  have hm' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool =>
      p.1.2.2.1.m) E' encUnary := simTopoData_polyTime.snd'.fst'.comp hfst
  have hg' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool =>
      p.1.2.2.1.gateList) E' (encList (encPair encNat encNat)) :=
    simTopoData_polyTime.snd'.snd'.comp hfst
  have hq' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool =>
      p.1.2.2.1.gateList.length) E' encUnary := simGateCount_polyTime.comp hfst
  have hc' : ComputableInPolyTime (fun p : (ℕ × List Bool × ValidTopo) × List Bool => p.2) E'
      encBits := ComputableInPolyTime.snd _ _
  have hx := ComputableInPolyTime.fst E' (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd E' (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hrow := simRowData_polyTime hf (hk'.comp hx) (hn'.comp hx) (hq'.comp hx) (hc'.comp hx)
    hrest.snd'.fst' hrest.snd'.snd'.fst' hrest.fst' hrest.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hg'.comp (ComputableInPolyTime.fst E' encUnary)) (ComputableInPolyTime.snd _ _) (0, 0)
  have hbody := bodyWith_polyTime
    (n := fun p : (ℕ × List Bool × ValidTopo) × List Bool => p.1.2.2.1.n)
    (cap := fun p => p.2.length + 1)
    (A := fun p g => (p.1.2.2.1.gateList.getD g (0, 0)).1)
    (B := fun p g => (p.1.2.2.1.gateList.getD g (0, 0)).2)
    (row := fun p g a b i => simRowData (family := family) p.1.1 p.1.2.2.1.n
      p.1.2.2.1.gateList.length p.2 a b g i)
    hn' hq' (by polytime) hgate.fst' hgate.snd' hrow
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => encFn z) encFn
      encBits := .of_eq fun _ => rfl
  have hfn := henc.comp ((hk'.prod (hn'.prod (hm'.prod hq'))).prod hbody)
  have hinput := simInput_polyTime.comp (hk'.prod (hn'.prod hc'))
  have hdec := simDecInfo_polyTime.comp (hk'.prod (hy'.prod (hn'.prod (hm'.prod (hq'.prod hc')))))
  simp only [simViewWord_eq_data]
  exact encPrvView_mk_polyTime hfn hinput hdec

include hf in
/-- **The simulator is PPT.** For every family computed in polynomial time, the simulator runs in
uniform strict probabilistic polynomial time on the parameter in unary, the output and the encoded
topology. -/
theorem isPPTOn_simWord :
    IsPPTOn (encPair encUnary (encPair encBits encValidTopo)) encPrvView
      (fun (k, y, t) => simWord family k y t) := by
  have h : IsPPTOn encSimInput encPrvView (fun x : ℕ × List Bool × ValidTopo => do
      let coins ← BitString.sampleList (simCoinLen x.1 x.2.2.1.n x.2.2.1.gateList.length)
      pure (simViewWord family x.1 x.2.1 x.2.2.1 coins)) :=
    (isPPTOn_sampleList.preprocess simCoinLen_polyTime).bind_with
      (simViewWord_polyTime hf).isPPTOn
  refine h.congr ?_
  rintro ⟨k, y, t⟩
  simp only [simWord, Topo.length_gateList]

end Efficiency

end Cslib.Crypto.Garbling.PointPermute
