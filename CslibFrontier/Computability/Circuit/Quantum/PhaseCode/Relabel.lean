/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode

/-!
# Relabelling phase-gate-code wires

`PhaseGateCode.relabel` applies a total map of natural-numbered wire labels to the target and
controls of a phase gate code. When that map agrees on the source register with an embedding into
a larger register, decoding the relabelled codes gives exactly the original circuit mapped along
the embedding (`Circuit.ofPhaseCodes_map_relabel`). This permits non-contiguous register layouts;
the existing `GateCode.shift` covers only contiguous blocks.

## Main definitions

* `Cslib.Quantum.PhaseGateCode.relabel`: relabel every wire named by a phase gate code.

## Main results

* `Cslib.Quantum.PhaseGateCode.toPlacedGate?_relabel`: decoding one well-formed relabelled code
  maps its placed gate along the embedding.
* `Cslib.Quantum.Circuit.ofPhaseCodes_map_relabel`: decoding a well-formed relabelled code list
  maps the decoded circuit along the embedding.
-/

public section

namespace Cslib.Quantum

variable {m N : ℕ}

namespace PhaseGateCode

/-- Relabel every target and control wire of a phase gate code by the total map `ρ`. -/
@[expose] def relabel (ρ : ℕ → ℕ) : PhaseGateCode → PhaseGateCode
  | (phase, kind, target, controls) => (phase, kind, ρ target, controls.map ρ)

/-- Decoding a well-formed relabelled phase gate code maps the original placed gate along the
embedding with which the total relabelling agrees on the source register. -/
theorem toPlacedGate?_relabel (e : Fin m ↪ Fin N) (ρ : ℕ → ℕ)
    (hρ : ∀ i : Fin m, ρ i = (e i : ℕ)) {c : PhaseGateCode} (hc : c.WellFormed m) :
    toPlacedGate? N (c.relabel ρ) = (toPlacedGate? m c).map (PlacedGate.mapWires e) := by
  have hlt {i : ℕ} (hi : i < m) : ρ i < N := by
    rw [hρ ⟨i, hi⟩]
    exact (e ⟨i, hi⟩).isLt
  have hinj {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) : ρ i ≠ ρ j := by
    intro h
    apply hij
    have he : e ⟨i, hi⟩ = e ⟨j, hj⟩ := Fin.ext ((hρ ⟨i, hi⟩).symm.trans (h.trans (hρ ⟨j, hj⟩)))
    exact congrArg Fin.val (e.injective he)
  have key {k : ℕ} (U : Gate k) (A : Fin k ↪ Fin m) (A' : Fin k ↪ Fin N)
      (hA : ∀ i, A' i = e (A i)) :
      (⟨k, U, A'⟩ : PlacedGate N) = PlacedGate.mapWires e ⟨k, U, A⟩ := by
    simp only [PlacedGate.mapWires, PlacedGate.mk.injEq, heq_eq_eq, true_and]
    exact Function.Embedding.ext hA
  match c, hc with
  | (false, true, t, []), hc =>
    have ht : t < m := hc.1
    simp only [relabel, toPlacedGate?, GateCode.toPlacedGate?, ht, hlt ht, ↓reduceDIte,
      List.map_nil, Option.map_some, Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i; exact Fin.ext (hρ ⟨t, ht⟩)
  | (false, true, t, _ :: _), hc => exact absurd hc.2 (List.cons_ne_nil _ _)
  | (false, false, t, []), hc =>
    have ht : t < m := hc.2.2 t (List.mem_cons_self ..)
    simp only [relabel, toPlacedGate?, GateCode.toPlacedGate?, ht, hlt ht, ↓reduceDIte,
      List.map_nil, Option.map_some, Option.some.injEq]
    exact key _ _ _ fun i => by fin_cases i; exact Fin.ext (hρ ⟨t, ht⟩)
  | (false, false, t, [c]), hc =>
    obtain ⟨-, hnd, hw⟩ := hc
    have ht : t < m := hw t (by simp)
    have hcontrol : c < m := hw c (by simp)
    have hct : c ≠ t := by simp at hnd; omega
    simp only [relabel, toPlacedGate?, GateCode.toPlacedGate?, List.map_cons, List.map_nil,
      dite_eq_left (show c < m ∧ t < m ∧ c ≠ t from ⟨hcontrol, ht, hct⟩),
      dite_eq_left (show ρ c < N ∧ ρ t < N ∧ ρ c ≠ ρ t from
        ⟨hlt hcontrol, hlt ht, hinj hcontrol ht hct⟩), Option.map_some, Option.some.injEq]
    exact key _ _ _ fun i => by
      fin_cases i
      · exact Fin.ext (hρ ⟨c, hcontrol⟩)
      · exact Fin.ext (hρ ⟨t, ht⟩)
  | (false, false, t, [c₁, c₂]), hc =>
    obtain ⟨-, hnd, hw⟩ := hc
    have ht : t < m := hw t (by simp)
    have hc₁ : c₁ < m := hw c₁ (by simp)
    have hc₂ : c₂ < m := hw c₂ (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true] at hnd
    simp only [relabel, toPlacedGate?, GateCode.toPlacedGate?, List.map_cons, List.map_nil,
      dite_eq_left (show c₁ < m ∧ c₂ < m ∧ t < m ∧ c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t by
        omega),
      dite_eq_left (show ρ c₁ < N ∧ ρ c₂ < N ∧ ρ t < N ∧ ρ c₁ ≠ ρ c₂ ∧ ρ c₁ ≠ ρ t ∧
        ρ c₂ ≠ ρ t by
          exact ⟨hlt hc₁, hlt hc₂, hlt ht, hinj hc₁ hc₂ (by omega),
            hinj hc₁ ht (by omega), hinj hc₂ ht (by omega)⟩),
      Option.map_some, Option.some.injEq]
    exact key _ _ _ fun i => by
      fin_cases i
      · exact Fin.ext (hρ ⟨c₁, hc₁⟩)
      · exact Fin.ext (hρ ⟨c₂, hc₂⟩)
      · exact Fin.ext (hρ ⟨t, ht⟩)
  | (false, false, _, _ :: _ :: _ :: _), hc => exact absurd hc.1 (by simp)
  | (true, inv, t, []), hc =>
    have ht : t < m := hc.2.2 t (List.mem_cons_self ..)
    simp only [relabel, toPlacedGate?, ht, hlt ht, ↓reduceDIte, List.map_nil, Option.map_some,
      Option.some.injEq, PlacedGate.mapWires_ctrlPhase]
    apply congrArg (fun A : Fin 1 ↪ Fin N => PlacedGate.ctrlPhase inv A)
    exact Function.Embedding.ext fun i => by fin_cases i; exact Fin.ext (hρ ⟨t, ht⟩)
  | (true, inv, t, [c]), hc =>
    obtain ⟨-, hnd, hw⟩ := hc
    have ht : t < m := hw t (by simp)
    have hcontrol : c < m := hw c (by simp)
    have hct : c ≠ t := by simp at hnd; omega
    simp only [relabel, toPlacedGate?, List.map_cons, List.map_nil,
      dite_eq_left (show c < m ∧ t < m ∧ c ≠ t from ⟨hcontrol, ht, hct⟩),
      dite_eq_left (show ρ c < N ∧ ρ t < N ∧ ρ c ≠ ρ t from
        ⟨hlt hcontrol, hlt ht, hinj hcontrol ht hct⟩), Option.map_some, Option.some.injEq,
      PlacedGate.mapWires_ctrlPhase]
    apply congrArg (fun A : Fin 2 ↪ Fin N => PlacedGate.ctrlPhase inv A)
    exact Function.Embedding.ext fun i => by
      fin_cases i
      · exact Fin.ext (hρ ⟨c, hcontrol⟩)
      · exact Fin.ext (hρ ⟨t, ht⟩)
  | (true, _, _, _ :: _ :: _), hc => exact absurd hc.1 (by simp)

end PhaseGateCode

/-- Decoding well-formed phase gate codes after relabelling their wire numbers maps the decoded
circuit along the embedding with which the total relabelling agrees on the source register. -/
theorem Circuit.ofPhaseCodes_map_relabel (e : Fin m ↪ Fin N) (ρ : ℕ → ℕ)
    (hρ : ∀ i : Fin m, ρ i = (e i : ℕ)) {codes : List PhaseGateCode}
    (hcodes : ∀ c ∈ codes, c.WellFormed m) :
    Circuit.ofPhaseCodes N (codes.map (PhaseGateCode.relabel ρ)) =
      (Circuit.ofPhaseCodes m codes).mapWires e := by
  simp only [Circuit.ofPhaseCodes, Circuit.mapWires, List.filterMap_map, List.map_filterMap]
  exact List.filterMap_congr fun c hc =>
    PhaseGateCode.toPlacedGate?_relabel e ρ hρ (hcodes c hc)

end Cslib.Quantum
