/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import Complexity.Algorithms.WordRAM.Dijkstra.LogLinear

/-!
# Bridge for the Dijkstra formal abstract

`DijkstraAbstract.lean` defines the distance of a graph given by adjacency lists as the least
weight of a walk, a list of edges each of which leaves the target of the one before. The library
defines it (`Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.dist`) as the least weight of a
`Quiver.Path` in the weight-matrix instance that keeps the lightest of the parallel edges. This
file proves that the two agree, for every walk predicate `W` that satisfies `WalkLaws`, and
transfers `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement` to the walk distance.

## Main results

* `walkDist_eq`: the walk distance is the library's distance.
* `logLinear`: the library's main theorem, over unfolded adjacency lists and the walk distance.
-/

namespace ComplexityAbstracts.DijkstraBridge

open Cslib.WordRAM Cslib.Algorithms.WordRAM.Dijkstra

/-- The defining equations of a walk predicate: `W G u l v` says that the list `l` of edges
`(target, weight)` is a walk from `u` to `v` in the graph with adjacency lists `G`. -/
structure WalkLaws
    (W : ∀ {n : ℕ}, (Fin n → List (Fin n × ℕ)) → Fin n → List (Fin n × ℕ) → Fin n → Prop) :
    Prop where
  nil : ∀ {n : ℕ} (G : Fin n → List (Fin n × ℕ)) (u v : Fin n), W G u [] v ↔ u = v
  cons : ∀ {n : ℕ} (G : Fin n → List (Fin n × ℕ)) (u : Fin n) (e : Fin n × ℕ)
    (l : List (Fin n × ℕ)) (v : Fin n), W G u (e :: l) v ↔ e ∈ G u ∧ W G e.1 l v

variable {W : ∀ {n : ℕ}, (Fin n → List (Fin n × ℕ)) → Fin n → List (Fin n × ℕ) → Fin n → Prop}

/-- The least weight of a walk from `u` to `v`, and `⊤` when there is none. -/
noncomputable def walkDist {n : ℕ} (W : (Fin n → List (Fin n × ℕ)) → Fin n →
    List (Fin n × ℕ) → Fin n → Prop) (G : Fin n → List (Fin n × ℕ)) (u v : Fin n) : ℕ∞ :=
  ⨅ (l : List (Fin n × ℕ)) (_ : W G u l v), ((l.map Prod.snd).sum : ℕ∞)

namespace ListInstance

variable (hW : WalkLaws W) (G : ListInstance)
include hW

/-- A walk followed by an edge out of its end is a walk. -/
theorem walk_append {u b : Fin G.n} {l : List (Fin G.n × ℕ)} (hl : W G.adj u l b)
    {e : Fin G.n × ℕ} (he : e ∈ G.adj b) : W G.adj u (l ++ [e]) e.1 := by
  induction l generalizing u with
  | nil =>
    rw [hW.nil] at hl
    subst hl
    exact (hW.cons _ _ _ _ _).2 ⟨he, (hW.nil _ _ _).2 rfl⟩
  | cons e' l ih =>
    rw [hW.cons] at hl
    exact (hW.cons _ _ _ _ _).2 ⟨hl.1, ih hl.2⟩

/-- Every path of the weight-matrix instance is a walk of the same weight. -/
theorem exists_walk {u v : G.toInstance.Vertex} (p : Quiver.Path u v) :
    ∃ l, W G.adj u l v ∧
      ((l.map Prod.snd).sum : ℕ∞) = p.addWeight G.toInstance.arrowWeight := by
  induction p with
  | nil =>
    refine ⟨[], (hW.nil _ _ _).2 rfl, ?_⟩
    rw [Quiver.Path.addWeight_nil]
    simp
  | @cons b c p e ih =>
    obtain ⟨l, hl, hw⟩ := ih
    have he : ((show Fin G.n from c), e.1) ∈ G.adj b := (G.lightest_eq_some_iff.1 e.2).1
    refine ⟨l ++ [((show Fin G.n from c), e.1)], walk_append hW G hl he, ?_⟩
    rw [Quiver.Path.addWeight_cons, ← hw]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, Nat.cast_add]
    rfl

/-- Every walk gives a path of the weight-matrix instance of at most the same weight: each edge
is replaced by the lightest edge between its endpoints. -/
theorem exists_path {v : G.toInstance.Vertex} (l : List (Fin G.n × ℕ)) {u : G.toInstance.Vertex}
    (hl : W G.adj u l v) :
    ∃ p : Quiver.Path u v,
      p.addWeight G.toInstance.arrowWeight ≤ ((l.map Prod.snd).sum : ℕ∞) := by
  induction l generalizing u with
  | nil =>
    obtain rfl : u = v := (hW.nil _ _ _).1 hl
    refine ⟨.nil, ?_⟩
    rw [Quiver.Path.addWeight_nil]
    exact zero_le
  | cons e l ih =>
    replace hl := (hW.cons _ _ _ _ _).1 hl
    obtain ⟨q, hq⟩ := ih hl.2
    obtain ⟨c, hc⟩ : ∃ c, G.lightest u e.1 = some c := by
      cases h : G.lightest u e.1 with
      | none => exact absurd hl.1 (G.lightest_eq_none_iff.1 h e.2)
      | some c => exact ⟨c, rfl⟩
    have hce : c ≤ e.2 := (G.lightest_eq_some_iff.1 hc).2 e.2 hl.1
    let x : G.toInstance.Vertex := e.1
    let a : u ⟶ x := ⟨c, hc⟩
    let q' : Quiver.Path x v := q
    refine ⟨(Quiver.Path.nil.cons a).comp q', ?_⟩
    rw [Quiver.Path.addWeight_comp, Quiver.Path.addWeight_cons, Quiver.Path.addWeight_nil,
      zero_add]
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add (show ((c : ℕ) : ℕ∞) ≤ e.2 by exact_mod_cast hce) hq

end ListInstance

/-- The walk distance is the library's distance. -/
theorem walkDist_eq (hW : WalkLaws W) (G : ListInstance) (u v : Fin G.n) :
    walkDist W G.adj u v = G.dist u v := by
  apply le_antisymm
  · refine le_iInf fun p => ?_
    obtain ⟨l, hl, hw⟩ := ListInstance.exists_walk hW G p
    exact (iInf₂_le l hl).trans hw.le
  · refine le_iInf₂ fun l hl => ?_
    obtain ⟨p, hp⟩ := ListInstance.exists_path hW G l hl
    exact (iInf_le _ p).trans hp

/-- **Transfer of the main theorem.** `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement`,
for the instance `⟨n, G, s⟩` and with the distance given by walks. -/
theorem logLinear (hW : WalkLaws W) :
    ∃ r, ∃ p : Program .standard r, ∃ K, ∀ (n : ℕ) (G : Fin n → List (Fin n × ℕ)) (s : Fin n)
      (w : ℕ), Fits w (8 * (n + (ListInstance.mk n G s).m + 2) *
        ((ListInstance.mk n G s).maxWeight + 2)) →
      ∃ t steps, Runs w p (.init (ListInstance.mk n G s).encode) t steps ∧
        (∃ v, step w p t = .halt v) ∧
        steps + 1 ≤ K * ((ListInstance.mk n G s).m + 1) * (Nat.log 2 n + 1) ∧
        ∀ v : Fin n, t.data.mem (n + 2 * (ListInstance.mk n G s).m + 4 + v) =
          encodeDist (walkDist W G s v) := by
  obtain ⟨r, p, K, h⟩ := logLinearStatement
  refine ⟨r, p, K, fun n G s w hw => ?_⟩
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := h ⟨n, G, s⟩ w hw
  exact ⟨t, steps, hr, hh, hle, fun v => by
    rw [walkDist_eq hW ⟨n, G, s⟩]
    exact hd v⟩

end ComplexityAbstracts.DijkstraBridge
