/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Program

/-!
# Dijkstra's algorithm on the word RAM: the relaxation scan

This file proves what one run of `Cslib.Algorithms.WordRAM.Dijkstra.relax` does: in `O(n)`
instructions it applies `Cslib.Algorithms.WordRAM.Dijkstra.relaxWord` to every distance word,
with the matrix row of vertex `bv`, and writes no other memory.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.relax_spec`: the relaxation scan.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM Reg

/-- The loop body of the relaxation scan. -/
private def relaxBody : Code .exact 17 := ram_exact[
  tmp ← row + j;
  c ← *tmp;
  if c = zero then [ tmp ← tmp ] else [
    cand ← best + c;
    cand ← cand - one;
    tmp ← dbase + j;
    dj ← *tmp;
    if dj = zero then [ *tmp ← cand ] else [
      if cand < dj then [ *tmp ← cand ] else [ tmp ← tmp ] ] ];
  j ← j + one ]

/-- One iteration updates its distance word and advances the index. -/
private theorem relaxBody_spec {w R J Db B : ℕ} {y : Data 17}
    (hzero : y.regs zero = 0) (hone : y.regs one = 1) (hr : y.regs row = R)
    (hj : y.regs j = J) (hdb : y.regs dbase = Db) (hb : y.regs best = B)
    (hfitR : Fits w (R + J)) (hfitD : Fits w (Db + J))
    (hfitC : Fits w (B + y.mem (R + J))) (hfitJ : Fits w (J + 1)) :
    ∃ z, ExecWithin w relaxBody y z 18 ∧ z.regs j = J + 1 ∧
      ∀ a, z.mem a = if a = Db + J then
        relaxWord B (y.mem (R + J)) (y.mem (Db + J)) else y.mem a := by
  have hsub : Fits w (B + y.mem (R + J) - 1) := hfitC.of_le (Nat.sub_le _ _)
  let y₁ := (y.set tmp (R + J)).set c (y.mem (R + J))
  let y₂ := (((y₁.set cand (B + y.mem (R + J))).set cand
    (B + y.mem (R + J) - 1)).set tmp (Db + J)).set dj (y.mem (Db + J))
  by_cases hc : y.mem (R + J) = 0
  · refine ⟨((y₁.set tmp (R + J)).set j (J + 1)), ?_, ?_, ?_⟩
    · ram_exact_eval [relaxBody, y₁, y₂, hzero, hone, hr, hj, hdb, hb, hfitR, hfitD, hfitC,
        hfitJ, hc, hsub]
    · simp +decide
    · intro a
      simp only [y₁, Data.set_mem, relaxWord, hc, ↓reduceIte]
      split <;> simp_all
  · have hle : 1 ≤ B + y.mem (R + J) := by omega
    by_cases hd : y.mem (Db + J) = 0
    · refine ⟨(y₂.write (Db + J) (B + y.mem (R + J) - 1)).set j (J + 1),
        ?_, ?_, ?_⟩
      · ram_exact_eval [relaxBody, y₁, y₂, hzero, hone, hr, hj, hdb, hb, hfitR, hfitD, hfitC,
          hfitJ, hc, hd, hle, hsub]
      · simp +decide
      · intro a
        simp +decide [y₂, y₁, relaxWord, hc, hd, Function.update_apply]
    · by_cases hl : B + y.mem (R + J) - 1 < y.mem (Db + J)
      · refine ⟨(y₂.write (Db + J) (B + y.mem (R + J) - 1)).set j (J + 1),
          ?_, ?_, ?_⟩
        · ram_exact_eval [relaxBody, y₁, y₂, hzero, hone, hr, hj, hdb, hb, hfitR, hfitD, hfitC,
            hfitJ, hc, hd, hl, hle, hsub]
        · simp +decide
        · intro a
          simp +decide [y₂, y₁, relaxWord, hc, hd, hl, Function.update_apply]
      · refine ⟨(y₂.set tmp (Db + J)).set j (J + 1), ?_, ?_, ?_⟩
        · ram_exact_eval [relaxBody, y₁, y₂, hzero, hone, hr, hj, hdb, hb, hfitR, hfitD, hfitC,
            hfitJ, hc, hd, hl, hle, hsub]
        · simp +decide
        · intro a
          simp only [y₂, y₁, Data.set_mem, relaxWord, hc, hd, hl, ↓reduceIte]
          split <;> simp_all

/-- The processed prefix contains relaxed distances; other memory is unchanged. -/
private structure RelaxInvariant (x : Data 17) (N Db U B : ℕ) (y : Data 17) : Prop where
  /-- Registers outside the scratch registers retain their initial values. -/
  frame : ∀ i ∉ [row, j, tmp, c, cand, dj], y.regs i = x.regs i
  /-- The row address is fixed throughout the scan. -/
  row_eq : y.regs row = U * N + 3
  /-- The index does not pass the end of the distance array. -/
  index_le : y.regs j ≤ N
  /-- Exactly the prefix below the index has been relaxed. -/
  distance : ∀ v < N, y.mem (Db + v) = if v < y.regs j then
    relaxWord B (x.mem (U * N + 3 + v)) (x.mem (Db + v)) else x.mem (Db + v)
  /-- Memory outside the distance array retains its initial values. -/
  outside : ∀ a, a < Db ∨ Db + N ≤ a → y.mem a = x.mem a

/-- **The relaxation scan.** With the matrix row of vertex `U` at `U N + 3 + v` and the distance
words at `Db + v`, past that row, the scan runs within `20 N + 10` instructions, writes only the
registers `row`, `j`, `tmp`, `c`, `cand`, `dj`, and replaces every distance word `x.mem (Db + v)`
for `v < N` by its relaxation through the edge from `U` to `v`, leaving all other memory as it
was. -/
theorem relax_spec {w N Db U B : ℕ} {x : Data 17} (hzero : x.regs zero = 0)
    (hone : x.regs one = 1) (hthree : x.regs three = 3) (hn : x.regs n = N)
    (hdb : x.regs dbase = Db) (hbv : x.regs bv = U) (hbest : x.regs best = B)
    (hrow : U * N + 3 + N ≤ Db) (hfitD : Fits w (Db + N))
    (hcand : ∀ v < N, Fits w (B + x.mem (U * N + 3 + v))) :
    ∃ y, ExecWithin w relax x y (20 * N + 10) ∧
      (∀ i ∉ [row, j, tmp, c, cand, dj], y.regs i = x.regs i) ∧
      (∀ v < N, y.mem (Db + v) = relaxWord B (x.mem (U * N + 3 + v)) (x.mem (Db + v))) ∧
      (∀ a, a < Db ∨ Db + N ≤ a → y.mem a = x.mem a) := by
  have hfitM : Fits w (U * N) := hfitD.of_le (by omega)
  have hfitR : Fits w (U * N + 3) := hfitD.of_le (by omega)
  let y₀ := ((x.set row (U * N)).set row (U * N + 3)).set j 0
  have hI₀ : RelaxInvariant x N Db U B y₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, not_or] at hi
      simp [y₀, hi.1, hi.2.1]
    · simp +decide [y₀]
    · simp [y₀]
    · intro v hv
      simp [y₀]
    · intro a ha
      rfl
  have hbody : ∀ y, RelaxInvariant x N Db U B y → (Cond.lt j n).Holds y →
      ∃ z, ExecWithin w relaxBody y z 18 ∧ RelaxInvariant x N Db U B z ∧
        N - z.regs j < N - y.regs j := by
    intro y hy hcond
    have hz := (hy.frame zero (by decide)).trans hzero
    have ho := (hy.frame one (by decide)).trans hone
    have hn' := (hy.frame n (by decide)).trans hn
    have hd := (hy.frame dbase (by decide)).trans hdb
    have hb := (hy.frame best (by decide)).trans hbest
    have hj : y.regs j < N := by simpa only [Cond.holds_lt, hn'] using hcond
    have hmatrix : y.mem (U * N + 3 + y.regs j) = x.mem (U * N + 3 + y.regs j) :=
      hy.outside _ (Or.inl (by omega))
    have hdist : y.mem (Db + y.regs j) = x.mem (Db + y.regs j) := by
      simpa using hy.distance (y.regs j) hj
    obtain ⟨z, he, hjz, hm⟩ := relaxBody_spec hz ho hy.row_eq rfl hd hb
      (hfitD.of_le (by omega)) (hfitD.of_le (by omega))
      (by rw [hmatrix]; exact hcand _ hj) (hfitD.of_le (by omega))
    have hframe : ∀ i ∉ [j, tmp, c, cand, dj], z.regs i = y.regs i := by
      intro i hi
      apply he.regs_eq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [relaxBody, Code.Preserves, Op.dest, Op.exactBin, ne_comm,
        hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2]
    refine ⟨z, he, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      exact (hframe i (fun h => hi (List.mem_cons_of_mem row h))).trans (hy.frame i hi)
    · exact (hframe row (by decide)).trans hy.row_eq
    · omega
    · intro v hv
      rw [hm, hjz]
      by_cases heq : v = y.regs j
      · subst v
        simp [hmatrix, hdist]
      · have haddr : Db + v ≠ Db + y.regs j := by omega
        have hlt : (v < y.regs j + 1) = (v < y.regs j) := propext (by omega)
        simp only [haddr, ↓reduceIte, hy.distance v hv, hlt]
    · intro a ha
      rw [hm, ite_eq_right (by omega)]
      exact hy.outside a ha
    · omega
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant
    (cond := .lt j n) (body := relaxBody) (RelaxInvariant x N Db U B)
    (fun y => N - y.regs j) hbody hI₀
  have hn' := (hy.frame n (by decide)).trans hn
  have hj : y.regs j = N := by
    have := hy.index_le
    simp only [Cond.holds_lt, hn'] at hexit
    omega
  refine ⟨y, ?_, hy.frame, ?_, hy.outside⟩
  · have e₁ : ExecWithin w ram_exact[row ← bv * n] x (x.set row (U * N)) 1 := by
      ram_exact_eval [hbv, hn, hfitM]
    have e₂ : ExecWithin w ram_exact[row ← row + three] (x.set row (U * N))
        ((x.set row (U * N)).set row (U * N + 3)) 1 := by
      ram_exact_eval [hthree, hfitR]
    have e₃ : ExecWithin (B := .exact) w ram_exact[j ← zero]
        ((x.set row (U * N)).set row (U * N + 3)) y₀ 1 := by
      ram_exact_eval [y₀, hzero]
    exact (e₁.seq (e₂.seq (e₃.seq he))).mono (by
      simp only [y₀, Data.set_regs, Function.update_self, Nat.sub_zero]
      omega)
  · intro v hv
    simpa only [hj, hv, ↓reduceIte] using hy.distance v hv

end Cslib.Algorithms.WordRAM.Dijkstra

end
