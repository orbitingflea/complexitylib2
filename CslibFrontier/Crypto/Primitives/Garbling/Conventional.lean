/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Crypto.Primitives.Garbling.CircuitInverters
public import CslibFrontier.Computability.Circuit.Topology
import CslibFrontier.Computability.Circuit.Encoding.Evaluation

/-!
# Conventional circuits as circuits

A conventional circuit `f = (n, m, q, A, B, G)` of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012] (`ConventionalCircuit`), numbers its wires from `1`, reads
its gates' arguments from the 1-indexed wires `A g` and `B g`, and outputs its last `m` wires. A
valid one is a circuit `ConventionalCircuit.toCircuit f : Circuit (fullSignature 2 Bool) n m` over
the full binary basis: gate `g` applies the truth table `G g` to the 0-indexed wires `A g - 1` and
`B g - 1`, and output `o` is wire `n + q - m + o`. It is decoded with `Circuit.ofCode` from this
gate list (`ConventionalCircuit.code_toCircuit`), so the garbling and privacy results stated for
`Circuit` apply to conventional circuits. Both semantics agree
(`ConventionalCircuit.eval_toCircuit`): on an `n`-bit input the circuit's outputs are
`ConventionalCircuit.evalCirc`.

## Main definitions

* `Cslib.Crypto.Garbling.ConventionalCircuit.gateCode`,
  `Cslib.Crypto.Garbling.ConventionalCircuit.outputCode`: a conventional circuit as circuit code.
* `Cslib.Crypto.Garbling.ConventionalCircuit.toCircuit`: a valid conventional circuit as a circuit.

## Main results

* `Cslib.Crypto.Garbling.ConventionalCircuit.eval_toCircuit`: it computes `evalCirc`.

Since `toCircuit` is not exposed, its gates, their binary operations and argument wires, and its
output wires are read through interface lemmas (`ConventionalCircuit.size_toCircuit`,
`ConventionalCircuit.lines_toCircuit`, `ConventionalCircuit.arity_topology_toCircuit`,
`ConventionalCircuit.ofFn_toNat_wires_toCircuit`, `ConventionalCircuit.toNat_outputs_toCircuit`).

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Cslib.Circuits

namespace ConventionalCircuit

/-- The gates of a conventional circuit as circuit code over the full binary basis: gate `i`
applies its truth table to the 0-indexed wires `A i - 1` and `B i - 1`. -/
@[expose] def gateCode (f : ConventionalCircuit) : List ((fullSignature 2 Bool).Op × List ℕ) :=
  List.ofFn fun i => (.fn fun a => f.G i (a 0) (a 1), [f.A i - 1, f.B i - 1])

/-- The output wires of a conventional circuit as circuit code: output `o` is the 0-indexed wire
`n + q - m + o`, one of the last `m` wires. -/
@[expose] def outputCode (f : ConventionalCircuit) : List ℕ :=
  List.ofFn fun o : Fin f.m => f.n + f.q - f.m + o

/-- The code of a valid conventional circuit decodes. -/
private theorem isSome_ofCode (f : ValidCircuit) :
    (Circuit.ofCode f.1.n f.1.m (gateCode f.1, outputCode f.1) :
      Option (Circuit (fullSignature 2 Bool) f.1.n f.1.m)).isSome := by
  obtain ⟨f, hf⟩ := f
  refine Circuit.isSome_ofCode_iff.mpr ⟨Program.isCodeFrom_of_getElem fun j hj => ?_, ?_, ?_⟩
  · simp only [gateCode, List.length_ofFn] at hj
    have hA := hf.A_lt_B ⟨j, hj⟩
    have hB := hf.B_lt_gate ⟨j, hj⟩
    have hA₁ := hf.one_le_A ⟨j, hj⟩
    simp only [topo] at hA hB hA₁
    simp only [gateCode, List.getElem_ofFn, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    refine ⟨rfl, ?_⟩
    rintro i (rfl | rfl) <;> omega
  · simp [outputCode]
  · have hm := hf.m_le_q
    simp only [topo] at hm
    simp only [outputCode, gateCode, List.mem_ofFn, List.length_ofFn]
    rintro _ ⟨o, rfl⟩
    omega

/-- A valid conventional circuit as a circuit over the full binary basis, decoded from its
gate list. -/
noncomputable def toCircuit (f : ValidCircuit) : Circuit (fullSignature 2 Bool) f.1.n f.1.m :=
  (Circuit.ofCode f.1.n f.1.m (gateCode f.1, outputCode f.1)).get (isSome_ofCode f)

/-- The code of `toCircuit f` is the gate list of `f` with its last `m` wires as outputs. -/
theorem code_toCircuit (f : ValidCircuit) :
    (toCircuit f).code = (gateCode f.1, outputCode f.1) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- `toCircuit f` has the `q` gates of `f`. -/
theorem size_toCircuit (f : ValidCircuit) : (toCircuit f).size = f.1.q := by
  have h := congrArg (fun code => code.1.length) (code_toCircuit f)
  simpa [Circuit.code, gateCode] using h

/-- The code of line `g` of `toCircuit f`: the truth table `G g` on the 0-indexed wires `A g - 1`
and `B g - 1`. -/
private theorem code_lines_toCircuit (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    ((toCircuit f).program.lines g).code =
      (.fn fun a => f.1.G (g.cast (size_toCircuit f)) (a 0) (a 1),
        [f.1.A (g.cast (size_toCircuit f)) - 1, f.1.B (g.cast (size_toCircuit f)) - 1]) := by
  rw [← Program.getD_code _ _ (FullOp.con false, [])]
  have h := congrArg Prod.fst (code_toCircuit f)
  simp only [Circuit.code] at h
  have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [gateCode] using hg)]
  simp only [gateCode, List.getElem_ofFn, Option.getD_some]
  rfl

/-- Every gate of `toCircuit f` is binary. -/
theorem arity_topology_toCircuit (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    (toCircuit f).topology.arity g = 2 := by
  have h := congrArg (fun code => code.2.length) (code_lines_toCircuit f g)
  simp only [Line.length_code_snd, List.length_cons, List.length_nil] at h
  exact h

/-- The argument wires of gate `g` of `toCircuit f` are the 0-indexed wires `A g - 1` and
`B g - 1`. -/
theorem ofFn_toNat_wires_toCircuit (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    List.ofFn (fun a => ((toCircuit f).topology.wires g a).toNat) =
      [f.1.A (g.cast (size_toCircuit f)) - 1, f.1.B (g.cast (size_toCircuit f)) - 1] :=
  congrArg Prod.snd (code_lines_toCircuit f g)

/-- The lines of `toCircuit f`: gate `g` applies the truth table `G g` to the 0-indexed wires
`A g - 1` and `B g - 1`. -/
theorem lines_toCircuit (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    (toCircuit f).program.lines g =
      ⟨.fn fun a => f.1.G (g.cast (size_toCircuit f)) (a 0) (a 1),
        ![Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) (by
            have := f.2.A_lt_B (g.cast (size_toCircuit f))
            have := f.2.B_lt_gate (g.cast (size_toCircuit f))
            simp only [topo, Fin.val_cast] at *
            omega),
          Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by
            have := f.2.B_lt_gate (g.cast (size_toCircuit f))
            simp only [topo, Fin.val_cast] at *
            omega)]⟩ := by
  have h := Line.ofCode_code ((toCircuit f).program.lines g)
  rw [code_lines_toCircuit f g] at h
  rw [Line.ofCode, dite_eq_left (by
    refine ⟨rfl, ?_⟩
    have hA := f.2.A_lt_B (g.cast (size_toCircuit f))
    have hB := f.2.B_lt_gate (g.cast (size_toCircuit f))
    simp only [topo, Fin.val_cast] at hA hB
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)] at h
  rw [← Option.some_inj.mp h]
  congr 1
  funext a
  match a with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Output `o` of `toCircuit f` is the 0-indexed wire `n + q - m + o`. -/
theorem toNat_outputs_toCircuit (f : ValidCircuit) (o : Fin f.1.m) :
    ((toCircuit f).outputs o).toNat = f.1.n + f.1.q - f.1.m + o := by
  have h := congrArg (fun code => code.2[o.val]?) (code_toCircuit f)
  simpa [Circuit.code, outputCode] using h

/-- Evaluating the first `s` gates of the code on an `n`-bit input lists the first `n + s` wire
values of the conventional evaluation. -/
private theorem evalCode_take_gateCode (f : ConventionalCircuit) {x : List Bool}
    (hx : x.length = f.n) {s : ℕ} (hs : s ≤ f.q) :
    evalCode fullInterpretation false x ((gateCode f).take s) = f.wires x s := by
  induction s with
  | zero => simp [wires, ← hx]
  | succ s ih =>
    have hsq : s < f.q := hs
    have htake : (gateCode f).take (s + 1) =
        (gateCode f).take s ++ [(.fn fun a => f.G ⟨s, hsq⟩ (a 0) (a 1),
          [f.A ⟨s, hsq⟩ - 1, f.B ⟨s, hsq⟩ - 1])] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [gateCode] using hsq)]
      simp [gateCode]
    rw [htake, evalCode_append_singleton, ih hsq.le]
    simp [wires, hsq, fullInterpretation, wireVal, List.getD_eq_getElem?_getD]

/-- **The translation computes the conventional semantics.** On every `n`-bit input, the outputs
of `toCircuit f` are `evalCirc f`. -/
theorem eval_toCircuit (f : ValidCircuit) (x : Fin f.1.n → Bool) :
    List.ofFn ((toCircuit f).eval fullInterpretation x) = f.1.evalCirc (List.ofFn x) := by
  have hwires := evalCode_take_gateCode f.1 (x := List.ofFn x) (by simp) le_rfl
  rw [show (gateCode f.1).take f.1.q = gateCode f.1 by simp [gateCode]] at hwires
  have hlen := f.1.length_wires (List.ofFn x) (le_refl f.1.q)
  have hm := f.2.m_le_q
  simp only [topo] at hm
  apply List.ext_getElem (by simp [evalCirc, hlen]; omega)
  intro o ho _
  have hom : o < f.1.m := by simpa using ho
  simp only [List.getElem_ofFn, evalCirc, List.getElem_drop]
  rw [Circuit.eval_eq_getD _ _ false, code_toCircuit, hwires]
  rw [toNat_outputs_toCircuit f ⟨o, hom⟩, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

end ConventionalCircuit

end Cslib.Crypto.Garbling
