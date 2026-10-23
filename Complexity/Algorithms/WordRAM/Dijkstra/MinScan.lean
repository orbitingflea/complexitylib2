/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Program

/-!
# Dijkstra's algorithm on the word RAM: the minimum scan

This file proves what one run of `Cslib.Algorithms.WordRAM.Dijkstra.minScan` does: it reads
memory without changing it and, in `O(n)` instructions, finds an unvisited vertex of least
nonzero distance word, or reports that every unvisited vertex has distance word `0`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.minScan_spec`: the minimum scan.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM Reg

/-- The minimum recorded after inspecting the vertices below `t`. -/
private def ScanPrefix (mem : ℕ → ℕ) (Db Vb t b v : ℕ) : Prop :=
  (b = 0 → ∀ u < t, mem (Vb + u) = 0 → mem (Db + u) = 0) ∧
  (b ≠ 0 → v < t ∧ mem (Vb + v) = 0 ∧ mem (Db + v) = b ∧
    ∀ u < t, mem (Vb + u) = 0 → mem (Db + u) ≠ 0 → b ≤ mem (Db + u))

/-- Skipping a visited vertex or a zero distance preserves the recorded minimum. -/
private theorem ScanPrefix.skip {mem : ℕ → ℕ} {Db Vb t b v : ℕ}
    (h : ScanPrefix mem Db Vb t b v)
    (ht : mem (Vb + t) ≠ 0 ∨ mem (Db + t) = 0) :
    ScanPrefix mem Db Vb (t + 1) b v := by
  refine ⟨?_, ?_⟩
  · intro hb u hu hf
    by_cases hut : u < t
    · exact h.1 hb u hut hf
    · have he : u = t := by omega
      subst u
      exact ht.resolve_left (not_not_intro hf)
  · intro hb
    obtain ⟨hv, hf, hd, hmin⟩ := h.2 hb
    refine ⟨by omega, hf, hd, ?_⟩
    intro u hu hfu hdu
    have hut : u < t := by
      by_contra hn
      have he : u = t := by omega
      subst u
      exact ht.elim (fun h => h hfu) hdu
    exact hmin u hut hfu hdu

/-- A newly found positive distance replaces an absent or larger minimum. -/
private theorem ScanPrefix.replace {mem : ℕ → ℕ} {Db Vb t b v : ℕ}
    (h : ScanPrefix mem Db Vb t b v) (hf : mem (Vb + t) = 0)
    (hd : mem (Db + t) ≠ 0) (hb : b = 0 ∨ mem (Db + t) < b) :
    ScanPrefix mem Db Vb (t + 1) (mem (Db + t)) t := by
  refine ⟨fun hz => (hd hz).elim, fun _ => ⟨by omega, hf, rfl, ?_⟩⟩
  intro u hu hfu hdu
  by_cases hut : u < t
  · rcases hb with hb | hb
    · exact (hdu (h.1 hb u hut hfu)).elim
    · have hbn : b ≠ 0 := by omega
      exact Nat.le_trans (Nat.le_of_lt hb) ((h.2 hbn).2.2.2 u hut hfu hdu)
  · have he : u = t := by omega
    subst u
    exact le_rfl

/-- A distance no smaller than the recorded positive minimum leaves it unchanged. -/
private theorem ScanPrefix.keep {mem : ℕ → ℕ} {Db Vb t b v : ℕ}
    (h : ScanPrefix mem Db Vb t b v) (hb : b ≠ 0) (hd : b ≤ mem (Db + t)) :
    ScanPrefix mem Db Vb (t + 1) b v := by
  refine ⟨fun hz => (hb hz).elim, fun _ => ?_⟩
  obtain ⟨hv, hf, he, hmin⟩ := h.2 hb
  refine ⟨by omega, hf, he, ?_⟩
  intro u hu hfu hdu
  by_cases hut : u < t
  · exact hmin u hut hfu hdu
  · have he : u = t := by omega
    simpa [he] using hd

/-- The scan preserves its inputs and records the minimum of its processed prefix. -/
private structure ScanInvariant (mem : ℕ → ℕ) (N Db Vb : ℕ) (y : Data 17) : Prop where
  /-- The zero register remains zero. -/
  zero_eq : y.regs zero = 0
  /-- The increment remains one. -/
  one_eq : y.regs one = 1
  /-- The vertex count remains fixed. -/
  n_eq : y.regs n = N
  /-- The distance base remains fixed. -/
  dbase_eq : y.regs dbase = Db
  /-- The flag base remains fixed. -/
  vbase_eq : y.regs vbase = Vb
  /-- No memory is changed. -/
  mem_eq : y.mem = mem
  /-- The scan index does not exceed the vertex count. -/
  j_le : y.regs j ≤ N
  /-- The answer describes exactly the processed prefix. -/
  result : ScanPrefix mem Db Vb (y.regs j) (y.regs best) (y.regs bv)

/-- The loop body of the minimum scan. -/
private def scanBody : Code .standard 17 := ram[
  tmp ← vbase + j;
  f ← *tmp;
  if f = zero then [
    tmp ← dbase + j;
    dj ← *tmp;
    if dj = zero then [ tmp ← tmp ] else [
      if best = zero then [ best ← dj; bv ← j ] else [
        if dj < best then [ best ← dj; bv ← j ] else [ tmp ← tmp ] ] ] ]
  else [ tmp ← tmp ];
  j ← j + one ]

/-- One scan iteration preserves the invariant and advances the index, within 18 steps. -/
private theorem scanBody_spec {w N Db Vb : ℕ} {mem : ℕ → ℕ} {y : Data 17}
    (hy : ScanInvariant mem N Db Vb y) (hc : (Cond.lt j n).Holds y)
    (hfitD : Fits w (Db + N)) (hfitV : Fits w (Vb + N)) :
    ∃ z, ExecWithin w scanBody y z 18 ∧ ScanInvariant mem N Db Vb z ∧
      N - z.regs j < N - y.regs j := by
  have hz := hy.zero_eq
  have ho := hy.one_eq
  have hn := hy.n_eq
  have hdb := hy.dbase_eq
  have hvb := hy.vbase_eq
  have hm := hy.mem_eq
  have hj : y.regs j < N := by simpa [hn] using hc
  have hfd : Fits w (Db + y.regs j) := hfitD.of_le (by omega)
  have hfv : Fits w (Vb + y.regs j) := hfitV.of_le (by omega)
  have hfj : Fits w (y.regs j + 1) := hfitD.of_le (by omega)
  have finish (z : Data 17) (he : ExecWithin w scanBody y z 18)
      (hmz : z.mem = mem) (hjz : z.regs j = y.regs j + 1)
      (hp : ScanPrefix mem Db Vb (y.regs j + 1) (z.regs best) (z.regs bv)) :
      ExecWithin w scanBody y z 18 ∧ ScanInvariant mem N Db Vb z ∧
        N - z.regs j < N - y.regs j := by
    refine ⟨he, ⟨?_, ?_, ?_, ?_, ?_, hmz, ?_, ?_⟩, ?_⟩
    · exact (he.regs_eq (by decide)).trans hz
    · exact (he.regs_eq (by decide)).trans ho
    · exact (he.regs_eq (by decide)).trans hn
    · exact (he.regs_eq (by decide)).trans hdb
    · exact (he.regs_eq (by decide)).trans hvb
    · omega
    · simpa only [hjz] using hp
    · omega
  let y₁ := (y.set tmp (Vb + y.regs j)).set f (mem (Vb + y.regs j))
  let y₂ := (y₁.set tmp (Db + y.regs j)).set dj (mem (Db + y.regs j))
  by_cases hf : mem (Vb + y.regs j) = 0
  · by_cases hd : mem (Db + y.regs j) = 0
    · let z := (y₂.set tmp (Db + y.regs j)).set j (y.regs j + 1)
      refine ⟨z, finish z ?_ (by simp [z, y₂, y₁, hm])
        (by simp [z]) ?_⟩
      · ram_eval [scanBody, z, y₂, y₁, hz, ho, hdb, hvb, hm, hfd, hfv, hfj, hf, hd]
      · simpa +decide [z, y₂, y₁] using hy.result.skip (Or.inr hd)
    · by_cases hb : y.regs best = 0
      · let z := ((y₂.set best (mem (Db + y.regs j))).set bv (y.regs j)).set j
          (y.regs j + 1)
        refine ⟨z, finish z ?_ (by simp [z, y₂, y₁, hm])
          (by simp [z]) ?_⟩
        · ram_eval [scanBody, z, y₂, y₁, hz, ho, hdb, hvb, hm, hfd, hfv, hfj, hf, hd, hb]
        · simpa +decide [z] using hy.result.replace hf hd (Or.inl hb)
      · by_cases hlt : mem (Db + y.regs j) < y.regs best
        · let z := ((y₂.set best (mem (Db + y.regs j))).set bv (y.regs j)).set j
            (y.regs j + 1)
          refine ⟨z, finish z ?_ (by simp [z, y₂, y₁, hm])
            (by simp [z]) ?_⟩
          · ram_eval [scanBody, z, y₂, y₁, hz, ho, hdb, hvb, hm, hfd, hfv, hfj,
              hf, hd, hb, hlt]
          · simpa +decide [z] using hy.result.replace hf hd (Or.inr hlt)
        · let z := (y₂.set tmp (Db + y.regs j)).set j (y.regs j + 1)
          refine ⟨z, finish z ?_ (by simp [z, y₂, y₁, hm])
            (by simp [z]) ?_⟩
          · ram_eval [scanBody, z, y₂, y₁, hz, ho, hdb, hvb, hm, hfd, hfv, hfj,
              hf, hd, hb, hlt]
          · simpa +decide [z, y₂, y₁] using hy.result.keep hb (Nat.le_of_not_gt hlt)
  · let z := (y₁.set tmp (Vb + y.regs j)).set j (y.regs j + 1)
    refine ⟨z, finish z ?_ (by simp [z, y₁, hm]) (by simp [z]) ?_⟩
    · ram_eval [scanBody, z, y₁, hz, ho, hvb, hm, hfv, hfj, hf]
    · simpa +decide [z, y₁] using hy.result.skip (Or.inl hf)

/-- **The minimum scan.** With the distance words of the vertices `v < N` at `Db + v` and their
visited flags at `Vb + v`, the scan runs within `20 N + 10` instructions, writes no memory and
only the registers `j`, `tmp`, `f`, `dj`, `best`, `bv`. If `best` ends at `0`, every unvisited
vertex has distance word `0`; otherwise `bv` is an unvisited vertex whose distance word is
`best`, the least nonzero distance word of an unvisited vertex. -/
theorem minScan_spec {w N Db Vb : ℕ} {x : Data 17} (hzero : x.regs zero = 0)
    (hone : x.regs one = 1) (hn : x.regs n = N) (hdb : x.regs dbase = Db)
    (hvb : x.regs vbase = Vb) (hfitD : Fits w (Db + N)) (hfitV : Fits w (Vb + N)) :
    ∃ y, ExecWithin w minScan x y (20 * N + 10) ∧ y.mem = x.mem ∧
      (∀ i ∉ [j, tmp, f, dj, best, bv], y.regs i = x.regs i) ∧
      (y.regs best = 0 → ∀ v < N, x.mem (Vb + v) = 0 → x.mem (Db + v) = 0) ∧
      (y.regs best ≠ 0 → y.regs bv < N ∧ x.mem (Vb + y.regs bv) = 0 ∧
        x.mem (Db + y.regs bv) = y.regs best ∧
        ∀ v < N, x.mem (Vb + v) = 0 → x.mem (Db + v) ≠ 0 → y.regs best ≤ x.mem (Db + v)) := by
  let x₀ := (x.set best 0).set j 0
  have hinit : ScanInvariant x.mem N Db Vb x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa +decide [x₀] using hzero
    · simpa +decide [x₀] using hone
    · simpa +decide [x₀] using hn
    · simpa +decide [x₀] using hdb
    · simpa +decide [x₀] using hvb
    · rfl
    · simp [x₀]
    · simp +decide [ScanPrefix, x₀]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant
    (ScanInvariant x.mem N Db Vb) (fun z => N - z.regs j)
    (fun z hz hc => scanBody_spec hz hc hfitD hfitV) hinit
  have hj : y.regs j = N := by
    have hn' := hy.n_eq
    have hj' := hy.j_le
    simp only [Cond.holds_lt, hn'] at hc
    omega
  have e : ExecWithin w minScan x y (20 * N + 10) := by
    change ExecWithin w (.seq (.op (.copy best zero))
      (.seq (.op (.copy j zero)) (.loop (.lt j n) scanBody))) x y _
    have e₁ := ExecWithin.copy (B := .standard) (w := w) (x := x)
      (d := best) (s := zero)
    have e₂ := ExecWithin.copy (B := .standard) (w := w)
      (x := x.set best (x.regs zero)) (d := j) (s := zero)
    have he' := e₁.seq (e₂.seq (by simpa +decide [x₀, hzero] using he))
    exact he'.mono (by omega)
  refine ⟨y, e, hy.mem_eq, ?_, ?_, ?_⟩
  · intro i hi
    apply e.regs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [minScan, Code.Preserves, Op.bin, Op.dest, eq_comm, hi.1, hi.2.1, hi.2.2.1,
      hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2]
  · simpa only [hj] using hy.result.1
  · simpa only [hj] using hy.result.2

end Cslib.Algorithms.WordRAM.Dijkstra

end
