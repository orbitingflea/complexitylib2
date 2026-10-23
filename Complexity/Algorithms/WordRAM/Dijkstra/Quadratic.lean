/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Invariant
public import Complexity.Algorithms.WordRAM.Dijkstra.MinScan
public import Complexity.Algorithms.WordRAM.Dijkstra.Relax

/-!
# Dijkstra's algorithm on the word RAM in quadratic time

This file proves that the program `Cslib.Algorithms.WordRAM.Dijkstra.dijkstra` computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices within
`125 n²` instructions, the final `halt` included [Dijkstra][Dijkstra1959]
[Cormen et al., Section 24.3][CLRS2009].

The memory of the program determines a visited set and tentative distances
(`Cslib.Algorithms.WordRAM.Dijkstra.visitedOf`, `Cslib.Algorithms.WordRAM.Dijkstra.distOf`); the
loop invariant `Cslib.Algorithms.WordRAM.Dijkstra.OuterInv` asks that they satisfy the invariant
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv` of Dijkstra's algorithm and that the round
counter counts the visited vertices, or has jumped to `n` once no unvisited vertex is reachable.
Each round keeps it by `Cslib.Algorithms.WordRAM.Dijkstra.minScan_spec`,
`Cslib.Algorithms.WordRAM.Dijkstra.relax_spec` and
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv.step`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.OuterInv`: the invariant of the rounds.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.dijkstra_spec`: the structured program leaves the encoded
  distances in the output cells within `125 n² - 1` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.quadraticSpec`: the compiled program meets
  `Cslib.Algorithms.WordRAM.Dijkstra.QuadraticSpec` with `K = 125`.
* `Cslib.Algorithms.WordRAM.Dijkstra.quadraticStatement`: the phase-1 main theorem.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM Reg

/-- The address of the visited flag of vertex `v`, just past the output cells. -/
def visAddr (I : Instance) (v : Fin I.n) : ℕ := I.n * I.n + 3 + I.n + v

/-- The tentative distances held in the output cells of `y`. -/
noncomputable def distOf (I : Instance) (y : Data 17) (v : Fin I.n) : ℕ∞ :=
  decodeDist (y.mem (I.outAddr v))

/-- The vertices whose visited flag in `y` is nonzero. -/
def visitedOf (I : Instance) (y : Data 17) : Finset (Fin I.n) :=
  Finset.univ.filter fun v => y.mem (visAddr I v) ≠ 0

/-- **The invariant of the rounds.** The constant registers hold their values, the weight matrix
is intact, the memory satisfies the invariant of Dijkstra's algorithm, and the round counter is
the number of visited vertices, or `n` once every unvisited vertex is unreachable so far. -/
structure OuterInv (I : Instance) (y : Data 17) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  three_eq : y.regs three = 3
  n_eq : y.regs n = I.n
  dbase_eq : y.regs dbase = I.n * I.n + 3
  vbase_eq : y.regs vbase = I.n * I.n + 3 + I.n
  k_le : y.regs k ≤ I.n
  matrix : ∀ u v : Fin I.n, y.mem (u * I.n + 3 + v) = Instance.encodeWeight (I.weight u v)
  inv : I.Inv (visitedOf I y) (distOf I y)
  count : y.regs k = (visitedOf I y).card ∨
    (y.regs k = I.n ∧ ∀ v ∉ visitedOf I y, distOf I y v = ⊤)

variable {I : Instance} {w : ℕ}

/-- Indexing a concatenation of rows of equal length. -/
private theorem getD_flatMap_rows {α : Type*} (l : List α) (f : α → List ℕ)
    (N : ℕ) (hf : ∀ a ∈ l, (f a).length = N) (i j : ℕ) (hi : i < l.length)
    (hj : j < N) : (l.flatMap f).getD (i * N + j) 0 = (f l[i]).getD j 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have ha := hf a (by simp)
    have hl : ∀ a ∈ l, (f a).length = N := fun b hb => hf b (by simp [hb])
    cases i with
    | zero =>
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, ha, hj]
    | succ i =>
      have he : (i + 1) * N + j - N = i * N + j := by rw [Nat.add_mul]; omega
      have hn : ¬(i + 1) * N + j < N := by rw [Nat.add_mul]; omega
      simpa only [List.flatMap_cons, List.getD_eq_getElem?_getD,
        List.getElem?_append, ha, hn,
        ite_false, he, List.getElem_cons_succ] using ih hl i (by simpa using hi)

/-- The encoded matrix has one word per entry, after its two header words. -/
private theorem encode_length (I : Instance) : I.encode.length = I.n * I.n + 2 := by
  simp [Instance.encode, List.length_flatMap, List.sum_replicate,
    Nat.add_comm, Nat.add_left_comm]

/-- Initial memory contains the encoded matrix at its specified addresses. -/
private theorem init_matrix (I : Instance) (u v : Fin I.n) :
    (Data.init I.encode : Data 17).mem (u * I.n + 3 + v) =
      Instance.encodeWeight (I.weight u v) := by
  have he : (u : ℕ) * I.n + 3 + v = ((u : ℕ) * I.n + v + 2) + 1 := by omega
  rw [he, Data.init_mem_succ, Instance.encode]
  rw [show (u : ℕ) * I.n + v + 2 = ((u : ℕ) * I.n + v + 1) + 1 by omega]
  rw [List.getD_cons_succ, List.getD_cons_succ]
  rw [getD_flatMap_rows _ _ I.n (by simp) u v (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

/-- Memory past the encoded input initially contains zero. -/
private theorem init_past (I : Instance) {a : ℕ} (ha : I.n * I.n + 3 ≤ a) :
    (Data.init I.encode : Data 17).mem a = 0 := by
  have hz : a ≠ 0 := by omega
  have hl : I.encode.length ≤ a - 1 := by rw [encode_length]; omega
  simp [Data.init, hz, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]

/-- The allowed word size holds all array addresses. -/
private theorem fits_arrays (hw : Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2))) :
    Fits w (I.n * I.n + 3 + I.n + I.n) := by
  apply hw.of_le
  nlinarith [Nat.zero_le I.maxWeight]

/-- The setup establishes the invariant of the rounds. -/
theorem setup_spec (hw : Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2))) :
    ∃ y, ExecWithin w setup (.init I.encode) y 20 ∧ OuterInv I y := by
  have hf := fits_arrays hw
  have h1 : Fits w 1 := hf.of_le (by omega)
  have h2 : Fits w 2 := hf.of_le (by omega)
  have h3 : Fits w 3 := hf.of_le (by omega)
  have hnn : Fits w (I.n * I.n) := hf.of_le (by omega)
  have hd : Fits w (I.n * I.n + 3) := hf.of_le (by omega)
  have hv : Fits w (I.n * I.n + 3 + I.n) := hf.of_le (by omega)
  have hs : Fits w (I.n * I.n + 3 + I.source) := hf.of_le (by
    have := I.source.isLt; omega)
  have hnmem : (Data.init I.encode : Data 17).mem 1 = I.n := rfl
  have hsmem : (Data.init I.encode : Data 17).mem 2 = I.source := rfl
  let y := (((((((((((Data.init I.encode : Data 17).set one 1).set three 3).set n
    I.n).set tmp 2).set src I.source).set dbase (I.n * I.n)).set dbase
    (I.n * I.n + 3)).set vbase (I.n * I.n + 3 + I.n)).set tmp
    (I.n * I.n + 3 + I.source)).write (I.n * I.n + 3 + I.source) 1).set k 0
  have he : ExecWithin w setup (.init I.encode) y 20 := by
    ram_eval [setup, y, Data.init_regs, hnmem, hsmem, h1, h2, h3, hnn, hd, hv, hs]
  have hm (a : ℕ) : y.mem a =
      Function.update (Data.init I.encode : Data 17).mem (I.outAddr I.source) 1 a := rfl
  have hdist : distOf I y = Function.update (fun _ => ⊤) I.source 0 := by
    funext v
    simp only [distOf, hm]
    by_cases h : v = I.source
    · subst v
      simp [decodeDist]
    · have hne : I.outAddr v ≠ I.outAddr I.source := by
        intro heq
        apply h
        apply Fin.ext
        simp only [Instance.outAddr] at heq
        omega
      simp [Function.update_of_ne hne, Function.update_of_ne h,
        init_past I (a := I.outAddr v) (by simp [Instance.outAddr]), decodeDist]
  have hvis : visitedOf I y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v
    have hne : visAddr I v ≠ I.outAddr I.source := by
      have := I.source.isLt
      simp only [visAddr, Instance.outAddr]
      omega
    simp [visitedOf, hm, Function.update_of_ne hne,
      init_past I (a := visAddr I v) (by unfold visAddr; omega)]
  refine ⟨y, he, ⟨by simp +decide [y], by simp +decide [y], by simp +decide [y],
    by simp +decide [y], by simp +decide [y], by simp +decide [y],
    by simp +decide [y], ?_, ?_, ?_⟩⟩
  · intro u v
    have hrow : (u : ℕ) * I.n + 3 + v < I.n * I.n + 3 := by
      have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt u.isLt)
      have := v.isLt
      nlinarith
    rw [hm, Function.update_of_ne (by simp only [Instance.outAddr]; omega)]
    exact init_matrix I u v
  · rw [hvis, hdist]
    exact Instance.Inv.init I
  · left
    simp +decide [y, hvis]

/-- Word relaxation decodes to relaxation of tentative distances. -/
private theorem decode_relaxWord {b : ℕ} (hb : b ≠ 0) (c : Option ℕ) (d : ℕ) :
    decodeDist (relaxWord b (Instance.encodeWeight c) d) =
      match c with
      | none => decodeDist d
      | some c => min (decodeDist d) (decodeDist b + c) := by
  cases c with
  | none => simp [relaxWord, Instance.encodeWeight]
  | some c =>
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    have he : b.succ + (c + 1) - 1 = (b + c) + 1 := by omega
    cases d with
    | zero => simp [relaxWord, Instance.encodeWeight, he, decodeDist]
    | succ d =>
      simp only [Instance.encodeWeight, relaxWord, Nat.succ_ne_zero, ite_false, he]
      by_cases h : b + c < d
      · have hc : (b : ℕ∞) + c ≤ d := by exact_mod_cast h.le
        simp [h, decodeDist, min_eq_right hc]
      · have hc : (d : ℕ∞) ≤ (b : ℕ∞) + c := by exact_mod_cast Nat.le_of_not_gt h
        simp [h, decodeDist, min_eq_left hc]

/-- States with the same memory and invariant registers have the same outer invariant. -/
private theorem outerInv_congr {x y : Data 17} (hy : OuterInv I y) (hm : x.mem = y.mem)
    (hr : ∀ i ∈ [zero, one, three, n, dbase, vbase, k], x.regs i = y.regs i) :
    OuterInv I x := by
  have hd : distOf I x = distOf I y := by funext v; simp [distOf, hm]
  have hv : visitedOf I x = visitedOf I y := by simp [visitedOf, hm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr zero (by simp), hy.zero_eq]
  · rw [hr one (by simp), hy.one_eq]
  · rw [hr three (by simp), hy.three_eq]
  · rw [hr n (by simp), hy.n_eq]
  · rw [hr dbase (by simp), hy.dbase_eq]
  · rw [hr vbase (by simp), hy.vbase_eq]
  · rw [hr k (by simp)]; exact hy.k_le
  · simpa only [hm] using hy.matrix
  · simpa only [hd, hv] using hy.inv
  · simpa only [hr k (by simp), hd, hv] using hy.count

/-- Membership in the visited set is exactly a nonzero flag. -/
private theorem mem_visitedOf (I : Instance) (y : Data 17) (v : Fin I.n) :
    v ∈ visitedOf I y ↔ y.mem (visAddr I v) ≠ 0 := by
  simp [visitedOf]

/-- One round keeps the invariant of the rounds and advances the round counter. -/
theorem round_spec (hw : Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2))) {y : Data 17}
    (hy : OuterInv I y) (hk : (Cond.lt k n).Holds y) :
    ∃ y', ExecWithin w round y y' (50 * I.n + 50) ∧ OuterInv I y' ∧
      I.n - y'.regs k < I.n - y.regs k := by
  have hfV := fits_arrays hw
  have hfD : Fits w (I.n * I.n + 3 + I.n) := hfV.of_le (by omega)
  have hkn : y.regs k < I.n := by simpa only [Cond.holds_lt, hy.n_eq] using hk
  have hcount : y.regs k = (visitedOf I y).card := by
    rcases hy.count with h | h
    · exact h
    · omega
  obtain ⟨x, ex, hmem, hregs, hnone, hsome⟩ :=
    minScan_spec hy.zero_eq hy.one_eq hy.n_eq hy.dbase_eq hy.vbase_eq hfD hfV
  have hx : OuterInv I x := outerInv_congr hy hmem (by
    intro i hi
    apply hregs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hxk : x.regs k = y.regs k := hregs k (by decide)
  by_cases hb : x.regs best = 0
  · let z := x.set k I.n
    have ez : ExecWithin (B := .standard) w (.op (.copy k n)) x z 1 := by
      simpa only [hx.n_eq] using (ExecWithin.copy (w := w) (B := .standard)
        (x := x) (d := k) (s := n))
    have hd : ∀ v ∉ visitedOf I z, distOf I z v = ⊤ := by
      intro v hv
      have hv0 : y.mem (I.n * I.n + 3 + I.n + v) = 0 := by
        simpa only [mem_visitedOf, z, Data.set_mem, hmem, visAddr, not_not] using hv
      have hvd := hnone hb v v.isLt hv0
      simp [distOf, z, hmem, Instance.outAddr, hvd, decodeDist]
    refine ⟨z, ?_, ?_, ?_⟩
    · exact (ex.seq (ez.branch_pos (by simp [Cond.holds_eq, hb, hx.zero_eq]))).mono
        (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨?_, hd⟩⟩
      · simpa +decide [z] using hx.zero_eq
      · simpa +decide [z] using hx.one_eq
      · simpa +decide [z] using hx.three_eq
      · simpa +decide [z] using hx.n_eq
      · simpa +decide [z] using hx.dbase_eq
      · simpa +decide [z] using hx.vbase_eq
      · simp [z]
      · exact hx.matrix
      · exact hx.inv
      · simp [z]
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  · obtain ⟨huN, hu0, hub, hleast⟩ := hsome hb
    let u : Fin I.n := ⟨x.regs bv, huN⟩
    have hu : u ∉ visitedOf I y := by
      simpa only [mem_visitedOf, visAddr, u, not_not] using hu0
    have hdu : distOf I y u = decodeDist (x.regs best) := by
      simp only [distOf, Instance.outAddr, u, hub]
    have hfin : distOf I y u ≠ ⊤ := by rw [hdu]; exact decodeDist_ne_top hb
    have hmin : ∀ v ∉ visitedOf I y, distOf I y u ≤ distOf I y v := by
      intro v hv
      have hv0 : y.mem (I.n * I.n + 3 + I.n + v) = 0 := by
        simpa only [mem_visitedOf, visAddr, not_not] using hv
      rw [hdu]
      by_cases hd : y.mem (I.outAddr v) = 0
      · simp [distOf, hd, decodeDist]
      · exact decodeDist_le hb hd (hleast v v.isLt hv0 hd)
    have hbound : x.regs best ≤ (visitedOf I y).card * I.maxWeight + 1 := by
      have hh := hy.inv.bound u hfin
      rw [hdu] at hh
      simp only [decodeDist, hb, ite_false] at hh
      have hh' : x.regs best - 1 ≤ (visitedOf I y).card * I.maxWeight := by
        exact_mod_cast hh
      omega
    have hrow : (u : ℕ) * I.n + 3 + I.n ≤ I.n * I.n + 3 := by
      have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt u.isLt)
      nlinarith
    let a := I.n * I.n + 3 + I.n + (u : ℕ)
    let z := (x.set tmp a).write a 1
    have ea : ExecWithin w (.op (.bin .add tmp vbase bv)) x (x.set tmp a) 1 := by
      have hh : Fits w (x.regs vbase + x.regs bv) := by
        rw [hx.vbase_eq]
        exact hfV.of_le (by omega)
      simpa only [BinOp.eval, hx.vbase_eq, a, u] using
        (ExecWithin.bin (f := .add) (d := tmp) (i := vbase) (j := bv) hh)
    have ez : ExecWithin (B := .standard) w (.op (.store tmp one)) (x.set tmp a) z 1 := by
      simpa +decide [hx.one_eq] using (ExecWithin.store (w := w) (B := .standard)
        (x := x.set tmp a) (a := tmp) (s := one))
    have zm (b : ℕ) (hne : b ≠ a) : z.mem b = y.mem b := by
      simp [z, Function.update_of_ne hne, hmem]
    have zd (v : Fin I.n) : z.mem (I.outAddr v) = y.mem (I.outAddr v) := by
      apply zm
      have := v.isLt
      simp only [Instance.outAddr, a]
      omega
    have zw (p q : Fin I.n) : z.mem (p * I.n + 3 + q) =
        Instance.encodeWeight (I.weight p q) := by
      rw [zm, hy.matrix]
      have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt p.isLt)
      have := q.isLt
      dsimp only [a]
      nlinarith
    have zv : visitedOf I z = insert u (visitedOf I y) := by
      ext v
      by_cases hv : v = u
      · subst v
        simp [mem_visitedOf, z, a, visAddr]
      · have hne : visAddr I v ≠ a := by
          intro hh
          apply hv
          apply Fin.ext
          simp only [visAddr, a] at hh
          omega
        simp [mem_visitedOf, hv, zm _ hne]
    have hcand : ∀ v < I.n, Fits w (x.regs best + z.mem (u * I.n + 3 + v)) := by
      intro v hv
      rw [zw u ⟨v, hv⟩]
      apply hw.of_le
      have he := I.encodeWeight_le u ⟨v, hv⟩
      have hc : (visitedOf I y).card + 1 ≤ I.n := by omega
      have hbnd := Nat.mul_le_mul_right I.maxWeight hc
      nlinarith [Nat.zero_le I.maxWeight]
    obtain ⟨t, et, tr, td, tm⟩ := relax_spec
      (x := z) (N := I.n) (Db := I.n * I.n + 3) (U := u) (B := x.regs best)
      (by simpa +decide [z] using hx.zero_eq)
      (by simpa +decide [z] using hx.one_eq)
      (by simpa +decide [z] using hx.three_eq)
      (by simpa +decide [z] using hx.n_eq)
      (by simpa +decide [z] using hx.dbase_eq)
      (by simp +decide [z, u]) (by simp +decide [z]) hrow hfD hcand
    have treg (i : Fin 17) (hi : i ∈ [zero, one, three, n, dbase, vbase, k]) :
        t.regs i = x.regs i := by
      rw [tr i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [z]
    have tv : visitedOf I t = insert u (visitedOf I y) := by
      rw [← zv]
      ext v
      simp only [mem_visitedOf, tm (visAddr I v) (Or.inr (by unfold visAddr; omega))]
    have tdist : distOf I t = I.relax (distOf I y) u := by
      funext v
      change decodeDist (t.mem (I.n * I.n + 3 + v)) = _
      rw [td v v.isLt, zw u v, show z.mem (I.n * I.n + 3 + v) =
        y.mem (I.n * I.n + 3 + v) from zd v, decode_relaxWord hb]
      rw [Instance.relax, hdu]
      cases I.weight u v <;> rfl
    have tw (p q : Fin I.n) : t.mem (p * I.n + 3 + q) =
        Instance.encodeWeight (I.weight p q) := by
      rw [tm, zw]
      left
      have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt p.isLt)
      have := q.isLt
      nlinarith
    have tk : t.regs k = y.regs k := (treg k (by simp)).trans hxk
    have tone : t.regs one = 1 := (treg one (by simp)).trans hx.one_eq
    let r := t.set k (y.regs k + 1)
    have er : ExecWithin w (.op (.bin .add k k one)) t r 1 := by
      have hh : Fits w (t.regs k + t.regs one) := by
        rw [tk, tone]
        exact hfV.of_le (by omega)
      simpa only [BinOp.eval, tk, tone] using (ExecWithin.bin (f := .add)
        (d := k) (i := k) (j := one) hh)
    refine ⟨r, ?_, ?_, ?_⟩
    · exact (ex.seq ((ea.seq (ez.seq (et.seq er))).branch_neg
        (by simpa only [Cond.holds_eq, hx.zero_eq] using hb))).mono (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, tw, ?_, ?_⟩
      · simpa +decide [r] using (treg zero (by simp)).trans hx.zero_eq
      · simpa +decide [r] using tone
      · simpa +decide [r] using (treg three (by simp)).trans hx.three_eq
      · simpa +decide [r] using (treg n (by simp)).trans hx.n_eq
      · simpa +decide [r] using (treg dbase (by simp)).trans hx.dbase_eq
      · simpa +decide [r] using (treg vbase (by simp)).trans hx.vbase_eq
      · simpa only [r, Data.set_regs, Function.update_self] using Nat.succ_le_of_lt hkn
      · change I.Inv (visitedOf I t) (distOf I t)
        rw [tv, tdist]
        exact Instance.Inv.step I hy.inv hu hmin hfin
      · left
        change y.regs k + 1 = (visitedOf I t).card
        rw [tv, Finset.card_insert_of_notMem hu, hcount]
    · simp only [r, Data.set_regs, Function.update_self]
      omega

/-- When the rounds stop, the output cells hold the encoded distances. -/
theorem exit_spec {y : Data 17} (hy : OuterInv I y) (hk : ¬(Cond.lt k n).Holds y)
    (v : Fin I.n) : y.mem (I.outAddr v) = encodeDist (I.dist I.source v) := by
  have hkn : y.regs k = I.n := by
    have := hy.n_eq
    have := hy.k_le
    simp only [Cond.holds_lt] at hk
    omega
  have hd : ∀ v ∉ visitedOf I y, distOf I y v = ⊤ := by
    rcases hy.count with hc | hc
    · have hs : visitedOf I y = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa only [Fintype.card_fin] using hc.symm.trans hkn
      simp [hs]
    · exact hc.2
  rw [← Instance.Inv.eq_dist I hy.inv hd v]
  exact (encodeDist_decodeDist _).symm

/-- **Correctness and running time of the structured program.** -/
theorem dijkstra_spec (hw : Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2))) :
    ∃ y, ExecWithin w dijkstra (.init I.encode) y (125 * I.n ^ 2 - 1) ∧
      ∀ v : Fin I.n, y.mem (I.outAddr v) = encodeDist (I.dist I.source v) := by
  obtain ⟨x, hx, hix⟩ := setup_spec hw
  obtain ⟨y, he, hi, hc⟩ := ExecWithin.loop_invariant (OuterInv I)
    (fun z => I.n - z.regs k) (fun _ h => round_spec hw h) hix
  refine ⟨y, (hx.seq he).mono ?_, fun v => exit_spec hi hc v⟩
  have hn : 1 ≤ I.n := by have := I.source.isLt; omega
  have hm : I.n - x.regs k ≤ I.n := Nat.sub_le _ _
  have ht := Nat.mul_le_mul_right (50 * I.n + 50 + 2) hm
  have hs : I.n ≤ I.n ^ 2 := by nlinarith
  have hb : 20 + ((I.n - x.regs k) * (50 * I.n + 50 + 2) + 2) + 1 ≤
      125 * I.n ^ 2 := by nlinarith
  omega

/-- **Dijkstra's algorithm in quadratic time.** The compiled program meets the specification
`Cslib.Algorithms.WordRAM.Dijkstra.QuadraticSpec` with `K = 125`. -/
theorem quadraticSpec : QuadraticSpec (dijkstra.program zero) 125 := by
  intro I w hw
  obtain ⟨y, ⟨m, hm, he⟩, hd⟩ := dijkstra_spec hw
  have hr := he.runs (pc := 0) (p := dijkstra.program zero)
    (Program.Contains.self _).append_left
  refine ⟨⟨dijkstra.size, y⟩, m, hr, ⟨y.regs zero, ?_⟩, ?_, hd⟩
  · exact step_halt (by simp [Code.program])
  · have hn : 1 ≤ I.n := by have := I.source.isLt; omega
    have : 1 ≤ 125 * I.n ^ 2 := by nlinarith
    omega

/-- **Phase 1 main theorem.** Some word-RAM program over the standard basis computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices within
`O(n²)` instructions. -/
theorem quadraticStatement : QuadraticStatement :=
  ⟨17, _, 125, quadraticSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra

end
