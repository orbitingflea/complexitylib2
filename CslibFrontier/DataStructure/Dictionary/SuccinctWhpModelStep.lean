/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shadow-Rebuild and Deletion Invariants for the Pure WHP Succinct Dynamic Dictionary

This module establishes the map-correspondence combinators (`SliceMapRel`, `BufMapRel`),
core/pre-tick invariants (`CoreFastInv`, `OvermarsBucketInv`, `PreOvermarsBucketInv`,
`ValidEpochStagePreTick`), and step preservation for `overmarsStep` and `fastDelete` in
`SuccinctWhpModel` for **every** static seed `θ` and capacity `n_max ≤ U`
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]). Insertion, global epoch ticks, and
full sequence refinement are proved in `SuccinctWhpModelTick`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.overmarsStep_spec`: background per-bucket shadow
  rebuild preserves `CoreFastInv`, `OvermarsBucketInv`, and `ValidEpochStage` /
  `ValidEpochStagePreTick`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastDelete_spec`: fast-mode deletion
  refines `Dynamic.step dict (.delete u)` and preserves `CoreFastInv`, `OvermarsBucketInv`, and
  `ValidEpochStagePreTick`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: Generic `SliceMapRel`, `BufMapRel`, and role-permutation helpers -/

theorem sliceIdx_inj {b₁ r₁ b₂ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (heq : 3 * b₁ + r₁ = 3 * b₂ + r₂) : b₁ = b₂ ∧ r₁ = r₂ :=
  ⟨by omega, by omega⟩

theorem rebRole_props {r₁ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3) (hne : r₁ ≠ r₂) :
    3 - r₁ - r₂ < 3 ∧ 3 - r₁ - r₂ ≠ r₁ ∧ 3 - r₁ - r₂ ≠ r₂ :=
  ⟨by omega, by omega, by omega⟩

theorem SliceMapRel.congr {f f' : ℕ → ℕ} {P P' : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P X m)
    (hf : ∀ loc < X, f' loc = f loc)
    (hP : ∀ loc < X, P' loc ↔ P loc) :
    SliceMapRel f' P' X m := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · rw [hrel.1 fp]
    exact ⟨fun h loc hlt hp' => hf loc hlt ▸ h loc hlt ((hP loc hlt).mp hp'),
      fun h loc hlt hp => hf loc hlt ▸ h loc hlt ((hP loc hlt).mpr hp)⟩
  · rw [hrel.2 fp loc]
    exact ⟨fun ⟨hlt, hp, heq⟩ => ⟨hlt, (hP loc hlt).mpr hp, (hf loc hlt).trans heq⟩,
      fun ⟨hlt, hp', heq⟩ => ⟨hlt, (hP loc hlt).mp hp', (hf loc hlt).symm.trans heq⟩⟩

theorem SliceMapRel.step_true {f : ℕ → ℕ} {P : ℕ → Prop} {cur : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m) (hp : P cur)
    (hfresh : ∀ loc < cur, P loc → f loc ≠ f cur) :
    SliceMapRel f P (cur + 1) (Function.update m (f cur) (some cur)) := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · by_cases hfp : fp = f cur
    · subst hfp
      simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
      exact ⟨cur, Nat.lt_succ_self cur, hp, rfl⟩
    · rw [Function.update_of_ne hfp, hrel.1 fp]
      refine ⟨fun hall loc hlt hpl => ?_, fun hall loc hlt hpl =>
        hall loc (Nat.lt_succ_of_lt hlt) hpl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact hall loc hlt' hpl
      · exact Ne.symm hfp
  · by_cases hfp : fp = f cur
    · subst hfp
      simp only [Function.update_self, Option.some.injEq]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact ⟨Nat.lt_succ_self cur, hp, rfl⟩
      · rintro ⟨hlt, hpl, heq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
        · exact absurd heq (hfresh loc hlt' hpl)
        · rfl
    · rw [Function.update_of_ne hfp, hrel.2 fp loc]
      refine ⟨fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩, ?_⟩
      rintro ⟨hlt, hpl, heq⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact ⟨hlt', hpl, heq⟩
      · exact absurd heq.symm hfp

theorem SliceMapRel.step_false {f : ℕ → ℕ} {P : ℕ → Prop} {cur : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m) (hnp : ¬P cur) :
    SliceMapRel f P (cur + 1) m := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · rw [hrel.1 fp]
    refine ⟨fun hall loc hlt hpl => ?_, fun hall loc hlt hpl =>
      hall loc (Nat.lt_succ_of_lt hlt) hpl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact hall loc hlt' hpl
    · exact absurd hpl hnp
  · rw [hrel.2 fp loc]
    refine ⟨fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩, ?_⟩
    rintro ⟨hlt, hpl, heq⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact ⟨hlt', hpl, heq⟩
    · exact absurd hpl hnp

theorem SliceMapRel.delete_last {f : ℕ → ℕ} {P : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (X + 1) m) (hp : P X)
    (hinj : ∀ loc < X, P loc → f loc ≠ f X) :
    SliceMapRel f P X (Function.update m (f X) none) := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · by_cases hfp : fp = f X
    · subst hfp
      simp only [Function.update_self, true_iff]
      exact hinj
    · rw [Function.update_of_ne hfp, hrel.1 fp]
      refine ⟨fun hall loc hlt hpl => hall loc (Nat.lt_succ_of_lt hlt) hpl,
        fun hall loc hlt hpl => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact hall loc hlt' hpl
      · exact Ne.symm hfp
  · by_cases hfp : fp = f X
    · subst hfp
      simp only [Function.update_self, reduceCtorEq, false_iff]
      rintro ⟨hlt, hpl, heq⟩
      exact hinj loc hlt hpl heq
    · rw [Function.update_of_ne hfp, hrel.2 fp loc]
      exact ⟨fun ⟨hlt, hpl, heq⟩ =>
        ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun h => hfp (h ▸ heq.symm)), hpl, heq⟩,
        fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩⟩

theorem SliceMapRel.skip_last {f : ℕ → ℕ} {P : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (X + 1) m) (hnp : ¬P X) :
    SliceMapRel f P X m := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · rw [hrel.1 fp]
    refine ⟨fun hall loc hlt hpl => hall loc (Nat.lt_succ_of_lt hlt) hpl,
      fun hall loc hlt hpl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact hall loc hlt' hpl
    · exact absurd hpl hnp
  · rw [hrel.2 fp loc]
    exact ⟨fun ⟨hlt, hpl, heq⟩ =>
      ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun h => hnp (h ▸ hpl)), hpl, heq⟩,
      fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩⟩

/-- Relocating `loc_last` into `loc_del < loc_last` across a full slice `0 .. loc_last` (`loc_last +
1 → loc_last`). -/
theorem SliceMapRel.relocate_full {f f' : ℕ → ℕ} {P P' : ℕ → Prop} [DecidablePred P]
    {loc_del loc_last : ℕ} {m0 : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (loc_last + 1) m0)
    (hlt_del : loc_del < loc_last)
    (hinj : ∀ l₁ < loc_last + 1, ∀ l₂ < loc_last + 1, P l₁ → P l₂ → f l₁ = f l₂ → l₁ = l₂)
    (hf_pres : ∀ loc < loc_last, loc ≠ loc_del → f' loc = f loc)
    (hf_del : f' loc_del = f loc_last)
    (hP_pres : ∀ loc < loc_last, loc ≠ loc_del → (P' loc ↔ P loc))
    (hP_del : P' loc_del ↔ P loc_last) :
    let m1 := if P loc_del then Function.update m0 (f loc_del) none else m0
    (P loc_last → (m1 (f loc_last)).isSome = true) ∧
    SliceMapRel f' P' loc_last
      (if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1) := by
  intro m1
  have hm1_last : P loc_last → (m1 (f loc_last)).isSome = true := by
    intro hpl
    have h0_last : m0 (f loc_last) = some loc_last :=
      (hrel.2 (f loc_last) loc_last).mpr ⟨Nat.lt_succ_self _, hpl, rfl⟩
    dsimp only [m1]
    split_ifs with hpd
    · have hne : f loc_last ≠ f loc_del := fun heq =>
        Nat.ne_of_gt hlt_del
          (hinj loc_last (Nat.lt_succ_self _) loc_del (by omega) hpl hpd heq)
      rw [Function.update_of_ne hne, h0_last]; rfl
    · rw [h0_last]; rfl
  refine ⟨hm1_last, ?_⟩
  -- Characterize `m2 fp = some loc` directly via injectivity!
  let m2 := if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1
  have hm2_some : ∀ fp loc, m2 fp = some loc ↔ loc < loc_last ∧ P' loc ∧ f' loc = fp := by
    intro fp loc
    constructor
    · intro hs
      dsimp only [m2] at hs
      by_cases hpl : P loc_last
      · rw [ite_eq_left hpl] at hs
        by_cases hfp_l : fp = f loc_last
        · subst hfp_l
          rw [Function.update_self, Option.some.injEq] at hs
          subst hs
          exact ⟨hlt_del, hP_del.mpr hpl, hf_del⟩
        · rw [Function.update_of_ne hfp_l] at hs
          dsimp only [m1] at hs
          have h0s : m0 fp = some loc ∧ ¬(P loc_del ∧ fp = f loc_del) := by
            split_ifs at hs with hpd
            · by_cases hfp_d : fp = f loc_del
              · rw [hfp_d, Function.update_self] at hs; cases hs
              · rw [Function.update_of_ne hfp_d] at hs
                exact ⟨hs, fun ⟨_, h⟩ => hfp_d h⟩
            · exact ⟨hs, fun ⟨hp, _⟩ => hpd hp⟩
          obtain ⟨hlt1, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s.1
          have hne_last : loc ≠ loc_last := fun h => hfp_l (h ▸ hfl_eq.symm)
          have hlt_ll : loc < loc_last := by omega
          have hne_del : loc ≠ loc_del := fun h => h0s.2 ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
          exact ⟨hlt_ll, (hP_pres loc hlt_ll hne_del).mpr hpl_loc,
            (hf_pres loc hlt_ll hne_del).trans hfl_eq⟩
      · rw [ite_eq_right hpl] at hs
        dsimp only [m1] at hs
        have h0s : m0 fp = some loc ∧ ¬(P loc_del ∧ fp = f loc_del) := by
          split_ifs at hs with hpd
          · by_cases hfp_d : fp = f loc_del
            · rw [hfp_d, Function.update_self] at hs; cases hs
            · rw [Function.update_of_ne hfp_d] at hs
              exact ⟨hs, fun ⟨_, h⟩ => hfp_d h⟩
          · exact ⟨hs, fun ⟨hp, _⟩ => hpd hp⟩
        obtain ⟨hlt1, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s.1
        have hne_last : loc ≠ loc_last := fun h => hpl (h ▸ hpl_loc)
        have hlt_ll : loc < loc_last := by omega
        have hne_del : loc ≠ loc_del := fun h => h0s.2 ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
        exact ⟨hlt_ll, (hP_pres loc hlt_ll hne_del).mpr hpl_loc,
          (hf_pres loc hlt_ll hne_del).trans hfl_eq⟩
    · rintro ⟨hlt_ll, hp', hf'_eq⟩
      by_cases hld : loc = loc_del
      · subst hld
        have hpl : P loc_last := hP_del.mp hp'
        have hfp_l : fp = f loc_last := hf'_eq.symm.trans hf_del
        subst hfp_l
        dsimp only [m2]
        rw [ite_eq_left hpl, Function.update_self]
      · have hpl_loc : P loc := (hP_pres loc hlt_ll hld).mp hp'
        have hfl_eq : f loc = fp := (hf_pres loc hlt_ll hld).symm.trans hf'_eq
        have h0s : m0 fp = some loc := (hrel.2 fp loc).mpr ⟨by omega, hpl_loc, hfl_eq⟩
        have hm1s : m1 fp = some loc := by
          dsimp only [m1]
          split_ifs with hpd
          · have hne_d : fp ≠ f loc_del := fun heq =>
              hld (hinj loc (by omega) loc_del (by omega) hpl_loc hpd (hfl_eq.trans heq))
            rwa [Function.update_of_ne hne_d]
          · exact h0s
        dsimp only [m2]
        split_ifs with hpl
        · have hne_l : fp ≠ f loc_last := fun heq =>
            Nat.ne_of_lt hlt_ll
              (hinj loc (by omega) loc_last (Nat.lt_succ_self _) hpl_loc hpl (hfl_eq.trans heq))
          rwa [Function.update_of_ne hne_l]
        · exact hm1s
  refine ⟨fun fp => ?_, hm2_some⟩
  rw [Option.eq_none_iff_forall_not_mem]
  refine ⟨fun hall loc hlt hp' heq => hall loc ((hm2_some fp loc).mpr ⟨hlt, hp', heq⟩),
    fun hall loc hmem => ?_⟩
  obtain ⟨hlt, hp', heq⟩ := (hm2_some fp loc).mp hmem
  exact hall loc hlt hp' heq

/-- Relocating `loc_last` into `loc_del < cur ≤ loc_last` across a prefix `0 .. cur - 1`, assuming
no collision between `f loc_last` and any remaining active item `< cur \ {loc_del}`. -/
theorem SliceMapRel.relocate_prefix {f f' : ℕ → ℕ} {P P' : ℕ → Prop} [DecidablePred P]
    {loc_del cur loc_last : ℕ} {m0 : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m0)
    (hlt_cur : loc_del < cur)
    (hinj_cur : ∀ l₁ < cur, ∀ l₂ < cur, P l₁ → P l₂ → f l₁ = f l₂ → l₁ = l₂)
    (hno_coll : P loc_last → ∀ l < cur, l ≠ loc_del → P l → f l ≠ f loc_last)
    (hf_pres : ∀ loc < cur, loc ≠ loc_del → f' loc = f loc)
    (hf_del : f' loc_del = f loc_last)
    (hP_pres : ∀ loc < cur, loc ≠ loc_del → (P' loc ↔ P loc))
    (hP_del : P' loc_del ↔ P loc_last) :
    let m1 := if P loc_del then Function.update m0 (f loc_del) none else m0
    SliceMapRel f' P' cur
      (if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1) := by
  intro m1
  let m2 := if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1
  have hm2_some : ∀ fp loc, m2 fp = some loc ↔ loc < cur ∧ P' loc ∧ f' loc = fp := by
    intro fp loc
    constructor
    · intro hs
      dsimp only [m2] at hs
      by_cases hpl : P loc_last
      · rw [ite_eq_left hpl] at hs
        by_cases hfp_l : fp = f loc_last
        · subst hfp_l
          rw [Function.update_self, Option.some.injEq] at hs
          subst hs
          exact ⟨hlt_cur, hP_del.mpr hpl, hf_del⟩
        · rw [Function.update_of_ne hfp_l] at hs
          dsimp only [m1] at hs
          have h0s : m0 fp = some loc ∧ ¬(P loc_del ∧ fp = f loc_del) := by
            split_ifs at hs with hpd
            · by_cases hfp_d : fp = f loc_del
              · rw [hfp_d, Function.update_self] at hs; cases hs
              · rw [Function.update_of_ne hfp_d] at hs
                exact ⟨hs, fun ⟨_, h⟩ => hfp_d h⟩
            · exact ⟨hs, fun ⟨hp, _⟩ => hpd hp⟩
          obtain ⟨hlt_c, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s.1
          have hne_del : loc ≠ loc_del := fun h => h0s.2 ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
          exact ⟨hlt_c, (hP_pres loc hlt_c hne_del).mpr hpl_loc,
            (hf_pres loc hlt_c hne_del).trans hfl_eq⟩
      · rw [ite_eq_right hpl] at hs
        dsimp only [m1] at hs
        have h0s : m0 fp = some loc ∧ ¬(P loc_del ∧ fp = f loc_del) := by
          split_ifs at hs with hpd
          · by_cases hfp_d : fp = f loc_del
            · rw [hfp_d, Function.update_self] at hs; cases hs
            · rw [Function.update_of_ne hfp_d] at hs
              exact ⟨hs, fun ⟨_, h⟩ => hfp_d h⟩
          · exact ⟨hs, fun ⟨hp, _⟩ => hpd hp⟩
        obtain ⟨hlt_c, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s.1
        have hne_del : loc ≠ loc_del := fun h => h0s.2 ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
        exact ⟨hlt_c, (hP_pres loc hlt_c hne_del).mpr hpl_loc,
          (hf_pres loc hlt_c hne_del).trans hfl_eq⟩
    · rintro ⟨hlt_c, hp', hf'_eq⟩
      by_cases hld : loc = loc_del
      · subst hld
        have hpl : P loc_last := hP_del.mp hp'
        have hfp_l : fp = f loc_last := hf'_eq.symm.trans hf_del
        subst hfp_l
        dsimp only [m2]
        rw [ite_eq_left hpl, Function.update_self]
      · have hpl_loc : P loc := (hP_pres loc hlt_c hld).mp hp'
        have hfl_eq : f loc = fp := (hf_pres loc hlt_c hld).symm.trans hf'_eq
        have h0s : m0 fp = some loc := (hrel.2 fp loc).mpr ⟨hlt_c, hpl_loc, hfl_eq⟩
        have hm1s : m1 fp = some loc := by
          dsimp only [m1]
          split_ifs with hpd
          · have hne_d : fp ≠ f loc_del := fun heq =>
              hld (hinj_cur loc hlt_c loc_del hlt_cur hpl_loc hpd (hfl_eq.trans heq))
            rwa [Function.update_of_ne hne_d]
          · exact h0s
        dsimp only [m2]
        split_ifs with hpl
        · have hne_l : fp ≠ f loc_last := fun heq =>
            hno_coll hpl loc hlt_c hld hpl_loc (hfl_eq.trans heq)
          rwa [Function.update_of_ne hne_l]
        · exact hm1s
  refine ⟨fun fp => ?_, hm2_some⟩
  rw [Option.eq_none_iff_forall_not_mem]
  refine ⟨fun hall loc hlt hp' heq => hall loc ((hm2_some fp loc).mpr ⟨hlt, hp', heq⟩),
    fun hall loc hmem => ?_⟩
  obtain ⟨hlt, hp', heq⟩ := (hm2_some fp loc).mp hmem
  exact hall loc hlt hp' heq

/-- Helper producing a full `BufMapRel` from its `some`-characterization. -/
theorem BufMapRel.of_some_iff {M tag : ℕ} {bktCnt : ℕ → ℕ} {locSt rKeyOf : ℕ → ℕ → ℕ}
    {m : ℕ → Option (ℕ × ℕ)}
    (hsome : ∀ rk b loc, m rk = some (b, loc) ↔
      b < M ∧ loc < bktCnt b ∧ locSt b loc = tag ∧ rKeyOf b loc = rk) :
    BufMapRel M tag bktCnt locSt rKeyOf m := by
  refine ⟨fun rk => ?_, hsome⟩
  rw [Option.eq_none_iff_forall_not_mem]
  refine ⟨fun hall b hb loc hloc hst heq =>
    hall (b, loc) ((hsome rk b loc).mpr ⟨hb, hloc, hst, heq⟩),
    fun hall p hmem => ?_⟩
  rcases p with ⟨b, loc⟩
  obtain ⟨hb, hloc, hst, heq⟩ := (hsome rk b loc).mp hmem
  exact hall b hb loc hloc hst heq

theorem BufMapRel.congr {M tag : ℕ} {bktCnt bktCnt' : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hcnt : ∀ b < M, bktCnt' b = bktCnt b)
    (hst : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = tag ↔ locSt b loc = tag)
    (hrk : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag bktCnt' locSt' rKeyOf' m := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  rw [hrel.2 rk b loc]
  refine ⟨fun ⟨hb, hloc, hst0, hrk0⟩ =>
    ⟨hb, hcnt b hb ▸ hloc, (hst b hb loc hloc).mpr hst0, (hrk b hb loc hloc).trans hrk0⟩,
    fun ⟨hb, hloc', hst', hrk'⟩ => ?_⟩
  have hloc : loc < bktCnt b := hcnt b hb ▸ hloc'
  exact ⟨hb, hloc, (hst b hb loc hloc).mp hst', (hrk b hb loc hloc).symm.trans hrk'⟩

/-- Inserting a fresh item at `(b₀, bktCnt b₀)` into `BufMapRel`. -/
theorem BufMapRel.insert_fresh {M tag b₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hb₀ : b₀ < M)
    (hst_new : locSt' b₀ (bktCnt b₀) = tag)
    (hst_pres : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc)
    (hno_coll : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag →
      rKeyOf b loc ≠ rKeyOf' b₀ (bktCnt b₀)) :
    BufMapRel M tag (Function.update bktCnt b₀ (bktCnt b₀ + 1)) locSt' rKeyOf'
      (Function.update m (rKeyOf' b₀ (bktCnt b₀)) (some (b₀, bktCnt b₀))) := by
  set X₀ := bktCnt b₀
  set rk₀ := rKeyOf' b₀ X₀
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  by_cases hrk_eq : rk = rk₀
  · subst hrk_eq
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      simp [hb₀, hst_new, rk₀]
    · rintro ⟨hb, hloc_upd, hst', hrk'⟩
      by_cases hb_eq : b = b₀
      · subst hb_eq
        rw [Function.update_self] at hloc_upd
        rcases Nat.lt_succ_iff_lt_or_eq.mp hloc_upd with hlt | rfl
        · rw [hst_pres b hb loc hlt] at hst'
          rw [hrk_pres b hb loc hlt] at hrk'
          exact absurd hrk' (hno_coll b hb loc hlt hst')
        · exact ⟨rfl, rfl⟩
      · rw [Function.update_of_ne hb_eq] at hloc_upd
        rw [hst_pres b hb loc hloc_upd] at hst'
        rw [hrk_pres b hb loc hloc_upd] at hrk'
        exact absurd hrk' (hno_coll b hb loc hloc_upd hst')
  · rw [Function.update_of_ne hrk_eq, hrel.2 rk b loc]
    refine ⟨fun ⟨hb, hloc, hst0, hrk0⟩ => ?_, fun ⟨hb, hloc_upd, hst', hrk'⟩ => ?_⟩
    · refine ⟨hb, ?_, ?_, (hrk_pres b hb loc hloc).trans hrk0⟩
      · by_cases hb_eq : b = b₀
        · subst hb_eq; rw [Function.update_self]; exact Nat.lt_succ_of_lt hloc
        · rwa [Function.update_of_ne hb_eq]
      · rw [hst_pres b hb loc hloc]; exact hst0
    · by_cases hb_eq : b = b₀
      · subst hb_eq
        rw [Function.update_self] at hloc_upd
        rcases Nat.lt_succ_iff_lt_or_eq.mp hloc_upd with hlt | rfl
        · exact ⟨hb, hlt, (hst_pres b hb loc hlt).symm.trans hst',
            (hrk_pres b hb loc hlt).symm.trans hrk'⟩
        · exact absurd hrk'.symm hrk_eq
      · rw [Function.update_of_ne hb_eq] at hloc_upd
        exact ⟨hb, hloc_upd, (hst_pres b hb loc hloc_upd).symm.trans hst',
          (hrk_pres b hb loc hloc_upd).symm.trans hrk'⟩

/-- Deleting `loc_last` when `bktCnt b₀ = loc_last + 1` shrinks to `loc_last` (case `loc_del =
loc_last`). -/
theorem BufMapRel.delete_last {M tag b₀ loc_last : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m0 : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m0)
    (hb₀ : b₀ < M) (hcnt₀ : bktCnt b₀ = loc_last + 1)
    (hinj : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag → locSt b₀ loc_last = tag →
      rKeyOf b loc = rKeyOf b₀ loc_last → b = b₀ ∧ loc = loc_last)
    (hst_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag (Function.update bktCnt b₀ loc_last) locSt' rKeyOf'
      (if locSt b₀ loc_last = tag then Function.update m0 (rKeyOf b₀ loc_last) none else m0) := by
  let bktCnt' := Function.update bktCnt b₀ loc_last
  have hlt_orig : ∀ b < M, ∀ loc < bktCnt' b, loc < bktCnt b ∧ ¬(b = b₀ ∧ loc = loc_last) := by
    intro b _ loc hlt
    dsimp only [bktCnt'] at hlt
    by_cases hb_eq : b = b₀
    · subst hb_eq; rw [Function.update_self] at hlt
      exact ⟨by omega, fun ⟨_, h⟩ => by omega⟩
    · rw [Function.update_of_ne hb_eq] at hlt
      exact ⟨hlt, fun ⟨h, _⟩ => hb_eq h⟩
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  constructor
  · intro hs
    have h0s : m0 rk = some (b, loc) ∧ ¬(locSt b₀ loc_last = tag ∧ rk = rKeyOf b₀ loc_last) := by
      split_ifs at hs with htl
      · by_cases hrk_l : rk = rKeyOf b₀ loc_last
        · rw [hrk_l, Function.update_self] at hs; cases hs
        · rw [Function.update_of_ne hrk_l] at hs
          exact ⟨hs, fun ⟨_, h⟩ => hrk_l h⟩
      · exact ⟨hs, fun ⟨h, _⟩ => htl h⟩
    obtain ⟨hb, hloc, hst0, hrk0⟩ := (hrel.2 rk b loc).mp h0s.1
    have hne : ¬(b = b₀ ∧ loc = loc_last) := fun ⟨h1, h2⟩ =>
      h0s.2 ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩
    have hloc' : loc < bktCnt' b := by
      dsimp only [bktCnt']
      by_cases hb_eq : b = b₀
      · subst hb_eq; rw [Function.update_self]
        have : loc ≠ loc_last := fun h => hne ⟨rfl, h⟩
        omega
      · rwa [Function.update_of_ne hb_eq]
    exact ⟨hb, hloc', (hst_pres b hb loc hloc').trans hst0,
      (hrk_pres b hb loc hloc').trans hrk0⟩
  · rintro ⟨hb, hloc', hst', hrk'⟩
    obtain ⟨hloc, hne⟩ := hlt_orig b hb loc hloc'
    have hst0 : locSt b loc = tag := (hst_pres b hb loc hloc').symm.trans hst'
    have hrk0 : rKeyOf b loc = rk := (hrk_pres b hb loc hloc').symm.trans hrk'
    have h0s : m0 rk = some (b, loc) := (hrel.2 rk b loc).mpr ⟨hb, hloc, hst0, hrk0⟩
    split_ifs with htl
    · have hrk_ne : rk ≠ rKeyOf b₀ loc_last := fun heq =>
        hne (hinj b hb loc hloc hst0 htl (hrk0.trans heq))
      rwa [Function.update_of_ne hrk_ne]
    · exact h0s

/-- Relocating `(b₀, loc_last)` into `(b₀, loc_del)` (`loc_del < loc_last`) in `BufMapRel`. -/
theorem BufMapRel.relocate_last {M tag b₀ loc_del loc_last : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m0 : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m0)
    (hb₀ : b₀ < M) (hcnt₀ : bktCnt b₀ = loc_last + 1) (hlt_del : loc_del < loc_last)
    (hinj : ∀ b₁ < M, ∀ l₁ < bktCnt b₁, ∀ b₂ < M, ∀ l₂ < bktCnt b₂,
      locSt b₁ l₁ = tag → locSt b₂ l₂ = tag → rKeyOf b₁ l₁ = rKeyOf b₂ l₂ → b₁ = b₂ ∧ l₁ = l₂)
    (hst_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      ¬(b = b₀ ∧ loc = loc_del) → locSt' b loc = locSt b loc)
    (hst_del : locSt' b₀ loc_del = locSt b₀ loc_last)
    (hrk_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      ¬(b = b₀ ∧ loc = loc_del) → rKeyOf' b loc = rKeyOf b loc)
    (hrk_del : rKeyOf' b₀ loc_del = rKeyOf b₀ loc_last) :
    let m1 := if locSt b₀ loc_del = tag then Function.update m0 (rKeyOf b₀ loc_del) none else m0
    (locSt b₀ loc_last = tag → m1 (rKeyOf b₀ loc_last) = some (b₀, loc_last)) ∧
    BufMapRel M tag (Function.update bktCnt b₀ loc_last) locSt' rKeyOf'
      (if locSt b₀ loc_last = tag then
        Function.update m1 (rKeyOf b₀ loc_last) (some (b₀, loc_del))
      else m1) := by
  intro m1
  let bktCnt' := Function.update bktCnt b₀ loc_last
  have hll_lt : loc_last < bktCnt b₀ := by omega
  have hld_lt : loc_del < bktCnt b₀ := by omega
  have hm1_last : locSt b₀ loc_last = tag → m1 (rKeyOf b₀ loc_last) = some (b₀, loc_last) := by
    intro htl
    have h0s : m0 (rKeyOf b₀ loc_last) = some (b₀, loc_last) :=
      (hrel.2 _ b₀ loc_last).mpr ⟨hb₀, hll_lt, htl, rfl⟩
    dsimp only [m1]
    split_ifs with htd
    · have hne : rKeyOf b₀ loc_last ≠ rKeyOf b₀ loc_del := fun heq =>
        Nat.ne_of_gt hlt_del ((hinj b₀ hb₀ loc_last hll_lt b₀ hb₀ loc_del hld_lt htl htd heq).2)
      rwa [Function.update_of_ne hne]
    · exact h0s
  refine ⟨hm1_last, BufMapRel.of_some_iff fun rk b loc => ?_⟩
  let m2 := if locSt b₀ loc_last = tag then
    Function.update m1 (rKeyOf b₀ loc_last) (some (b₀, loc_del)) else m1
  change m2 rk = some (b, loc) ↔ b < M ∧ loc < bktCnt' b ∧ locSt' b loc = tag ∧ rKeyOf' b loc = rk
  have hlt_orig : ∀ b < M, ∀ loc < bktCnt' b, loc < bktCnt b ∧ ¬(b = b₀ ∧ loc = loc_last) := by
    intro b _ loc hlt
    dsimp only [bktCnt'] at hlt
    by_cases hb_eq : b = b₀
    · subst hb_eq; rw [Function.update_self] at hlt
      exact ⟨by omega, fun ⟨_, h⟩ => by omega⟩
    · rw [Function.update_of_ne hb_eq] at hlt
      exact ⟨hlt, fun ⟨h, _⟩ => hb_eq h⟩
  constructor
  · intro hs
    dsimp only [m2] at hs
    by_cases htl : locSt b₀ loc_last = tag
    · rw [ite_eq_left htl] at hs
      by_cases hrk_l : rk = rKeyOf b₀ loc_last
      · subst hrk_l
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        refine ⟨hb₀, ?_, hst_del.trans htl, hrk_del⟩
        dsimp only [bktCnt']; rw [Function.update_self]; exact hlt_del
      · rw [Function.update_of_ne hrk_l] at hs
        dsimp only [m1] at hs
        have h0s : m0 rk = some (b, loc) ∧ ¬(locSt b₀ loc_del = tag ∧ rk = rKeyOf b₀ loc_del) := by
          split_ifs at hs with htd
          · by_cases hrk_d : rk = rKeyOf b₀ loc_del
            · rw [hrk_d, Function.update_self] at hs; cases hs
            · rw [Function.update_of_ne hrk_d] at hs
              exact ⟨hs, fun ⟨_, h⟩ => hrk_d h⟩
          · exact ⟨hs, fun ⟨h, _⟩ => htd h⟩
        obtain ⟨hb, hloc, hst0, hrk0⟩ := (hrel.2 rk b loc).mp h0s.1
        have hne_last : ¬(b = b₀ ∧ loc = loc_last) := fun ⟨h1, h2⟩ =>
          hrk_l (h1 ▸ h2 ▸ hrk0.symm)
        have hne_del : ¬(b = b₀ ∧ loc = loc_del) := fun ⟨h1, h2⟩ =>
          h0s.2 ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩
        have hloc' : loc < bktCnt' b := by
          dsimp only [bktCnt']
          by_cases hb_eq : b = b₀
          · subst hb_eq; rw [Function.update_self]
            have : loc ≠ loc_last := fun h => hne_last ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hb_eq]
        exact ⟨hb, hloc', (hst_pres b hb loc hloc' hne_del).trans hst0,
          (hrk_pres b hb loc hloc' hne_del).trans hrk0⟩
    · rw [ite_eq_right htl] at hs
      dsimp only [m1] at hs
      have h0s : m0 rk = some (b, loc) ∧ ¬(locSt b₀ loc_del = tag ∧ rk = rKeyOf b₀ loc_del) := by
        split_ifs at hs with htd
        · by_cases hrk_d : rk = rKeyOf b₀ loc_del
          · rw [hrk_d, Function.update_self] at hs; cases hs
          · rw [Function.update_of_ne hrk_d] at hs
            exact ⟨hs, fun ⟨_, h⟩ => hrk_d h⟩
        · exact ⟨hs, fun ⟨h, _⟩ => htd h⟩
      obtain ⟨hb, hloc, hst0, hrk0⟩ := (hrel.2 rk b loc).mp h0s.1
      have hne_last : ¬(b = b₀ ∧ loc = loc_last) := fun ⟨h1, h2⟩ => htl (h1 ▸ h2 ▸ hst0)
      have hne_del : ¬(b = b₀ ∧ loc = loc_del) := fun ⟨h1, h2⟩ =>
        h0s.2 ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩
      have hloc' : loc < bktCnt' b := by
        dsimp only [bktCnt']
        by_cases hb_eq : b = b₀
        · subst hb_eq; rw [Function.update_self]
          have : loc ≠ loc_last := fun h => hne_last ⟨rfl, h⟩
          omega
        · rwa [Function.update_of_ne hb_eq]
      exact ⟨hb, hloc', (hst_pres b hb loc hloc' hne_del).trans hst0,
        (hrk_pres b hb loc hloc' hne_del).trans hrk0⟩
  · rintro ⟨hb, hloc', hst', hrk'⟩
    by_cases hbd : b = b₀ ∧ loc = loc_del
    · rcases hbd with ⟨rfl, rfl⟩
      have htl : locSt b loc_last = tag := hst_del.symm.trans hst'
      have hrk_l : rk = rKeyOf b loc_last := hrk'.symm.trans hrk_del
      subst hrk_l
      dsimp only [m2]
      rw [ite_eq_left htl, Function.update_self]
    · obtain ⟨hloc, hne_last⟩ := hlt_orig b hb loc hloc'
      have hst0 : locSt b loc = tag := (hst_pres b hb loc hloc' hbd).symm.trans hst'
      have hrk0 : rKeyOf b loc = rk := (hrk_pres b hb loc hloc' hbd).symm.trans hrk'
      have h0s : m0 rk = some (b, loc) := (hrel.2 rk b loc).mpr ⟨hb, hloc, hst0, hrk0⟩
      have hm1s : m1 rk = some (b, loc) := by
        dsimp only [m1]
        split_ifs with htd
        · have hne_d : rk ≠ rKeyOf b₀ loc_del := fun heq =>
            hbd (hinj b hb loc hloc b₀ hb₀ loc_del hld_lt hst0 htd (hrk0.trans heq))
          rwa [Function.update_of_ne hne_d]
        · exact h0s
      dsimp only [m2]
      split_ifs with htl
      · have hne_l : rk ≠ rKeyOf b₀ loc_last := fun heq =>
          hne_last (hinj b hb loc hloc b₀ hb₀ loc_last hll_lt hst0 htl (hrk0.trans heq))
        rwa [Function.update_of_ne hne_l]
      · exact hm1s

/-! ## Section 2: `CoreFastInv`, `ValidEpochStagePreTick`, and `overmarsStep_spec` -/

/-- Core fast-state invariant (all fields of `ValidFastState` except `overmars_valid` and
`stage_valid`), shared across intermediate pre-`overmarsStep` and pre-`epochTick` states. -/
structure CoreFastInv (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (dict : State U) : Prop where
  hth : whpThreshold c ≤ n_max
  curEp_or : fs.curEp = 0 ∨ fs.curEp = 1
  epochClock_lt : fs.epochClock < qEpochWhp n_max
  rebStage_le : fs.rebStage ≤ 5
  rebCollision_zero : fs.rebCollision = 0
  qv_global : ∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max ∧ fs.valArr p < max V 1
  bktCount_le : ∀ b < numBucketsWhp n_max, fs.bktCount b ≤ totalLocalCoordsWhp n_max
  bktCount_ge_zero : ∀ b, numBucketsWhp n_max ≤ b → fs.bktCount b = 0
  locState_active : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
    1 ≤ fs.locState b loc ∧ fs.locState b loc ≤ 3
  locState_inactive : ∀ b loc, ¬(b < numBucketsWhp n_max ∧ loc < fs.bktCount b) →
    fs.locState b loc = 0
  active_item : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
    let kv := fs.keyValAt c U n_max θ.1 b loc
    kv < U ∧
    feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) kv = b ∧
    keyQuotient (bWhp n_max) kv = fs.quotArr (fs.physSlot n_max b loc) ∧
    fs.valArr (fs.physSlot n_max b loc) < V
  quot_inj : ∀ b < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
    fs.quotArr (fs.physSlot n_max b l₁) = fs.quotArr (fs.physSlot n_max b l₂) → l₁ = l₂
  dict_map : ∀ u : Fin U,
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q := keyQuotient (bWhp n_max) u.val
    (dict u = none ↔ ∀ loc < fs.bktCount b, fs.quotArr (fs.physSlot n_max b loc) ≠ q) ∧
    (∀ v, dict u = some v ↔
      ∃ loc < fs.bktCount b,
        fs.quotArr (fs.physSlot n_max b loc) = q ∧
        fs.valArr (fs.physSlot n_max b loc) = v)
  poolFreeTop_le : fs.poolFreeTop ≤ poolSizeWhp n_max
  backPtr_valid : ∀ b < numBucketsWhp n_max, ∀ k < fs.bktCount b - capFrontWhp n_max,
    fs.backPtr b k < poolSizeWhp n_max ∧
    fs.poolOwner (fs.backPtr b k) = b * capBackWhp n_max + k
  freeStack_lt : ∀ j < fs.poolFreeTop, fs.poolFreeStack j < poolSizeWhp n_max
  backPtr_inj : ∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs.bktCount b₁ - capFrontWhp n_max,
    ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs.bktCount b₂ - capFrontWhp n_max,
      fs.backPtr b₁ k₁ = fs.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂
  freeStack_inj : ∀ j₁ < fs.poolFreeTop, ∀ j₂ < fs.poolFreeTop,
    fs.poolFreeStack j₁ = fs.poolFreeStack j₂ → j₁ = j₂
  back_free_disj : ∀ b < numBucketsWhp n_max, ∀ k < fs.bktCount b - capFrontWhp n_max,
    ∀ j < fs.poolFreeTop, fs.backPtr b k ≠ fs.poolFreeStack j
  pool_conservation : fs.poolFreeTop +
    ∑ b ∈ range (numBucketsWhp n_max), (fs.bktCount b - capFrontWhp n_max) = poolSizeWhp n_max
  roles_valid : ∀ b < numBucketsWhp n_max,
    fs.liveRole b < 3 ∧ fs.overmarsRole b < 3 ∧ fs.liveRole b ≠ fs.overmarsRole b
  bktSalt_lt : ∀ b < numBucketsWhp n_max, fs.bktSalt b < sMaxWhp c n_max
  live_fp_inj : ∀ b < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
    inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₁) = true →
    inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₂) = true →
    fs.fpAt c U n_max θ (fs.bktSalt b) b l₁ = fs.fpAt c U n_max θ (fs.bktSalt b) b l₂ →
    l₁ = l₂
  live_valid : ∀ b < numBucketsWhp n_max,
    ∃ liveMap,
      ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) liveMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (fs.bktCount b) liveMap
  rKey_buf_inj : ∀ b₁ < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b₁,
    ∀ b₂ < numBucketsWhp n_max, ∀ l₂ < fs.bktCount b₂,
      2 ≤ fs.locState b₁ l₁ → 2 ≤ fs.locState b₂ l₂ →
      fs.rKeyAt c U n_max θ b₁ l₁ = fs.rKeyAt c U n_max θ b₂ l₂ →
      b₁ = b₂ ∧ l₁ = l₂
  bufCur_valid :
    (fs.buf fs.curEp).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
    (fs.buf fs.curEp).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf fs.curEp).itemAlloc ∧
    ∃ curMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap ∧
      BufMapRel (numBucketsWhp n_max) (2 + fs.curEp) fs.bktCount fs.locState
        (fs.rKeyAt c U n_max θ) curMap
  bufOld_valid :
    if fs.rebStage ≤ 3 then
      (fs.buf fs.oldEp).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
      (fs.buf fs.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf fs.oldEp).itemAlloc ∧
      ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap ∧
        BufMapRel (numBucketsWhp n_max) (2 + fs.oldEp) fs.bktCount fs.locState
          (fs.rKeyAt c U n_max θ) oldMap
    else if fs.rebStage = 4 then
      (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
      ClearableBufTrie (fs.buf fs.oldEp) ∧
      (fs.buf fs.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * rIndepWhp c n_max)
    else
      (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) (fun _ => none) ∧
      (fs.buf fs.oldEp).nodeAlloc = 1 ∧
      (fs.buf fs.oldEp).itemAlloc = 0

/-- Per-bucket Overmars invariant in `ValidFastState`. -/
@[expose] def OvermarsBucketInv (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (b : ℕ) : Prop :=
  (fs.overmarsActive b = 0 ∧ fs.liveInsCount b < 5 * (scaleWhp n_max) ^ 12) ∨
  (fs.overmarsActive b = 1 ∧
    16 ≤ fs.overmarsCursor b ∧
    fs.overmarsCursor b < fs.bktCount b ∧
    16 * (fs.liveInsCount b - 5 * (scaleWhp n_max) ^ 12) ≤ fs.overmarsCursor b ∧
    16 * fs.overmarsInsCount b + 16 ≤ 17 * fs.overmarsCursor b ∧
    ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (fs.overmarsCursor b) omMap)

/-- Relaxed per-bucket Overmars invariant immediately prior to `overmarsStep` on bucket `b`. -/
@[expose] def PreOvermarsBucketInv (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (b : ℕ) : Prop :=
  (fs.overmarsActive b = 0 ∧ fs.liveInsCount b ≤ 5 * (scaleWhp n_max) ^ 12) ∨
  (fs.overmarsActive b = 1 ∧
    16 ≤ fs.overmarsCursor b ∧
    fs.overmarsCursor b ≤ fs.bktCount b ∧
    16 * (fs.liveInsCount b - 5 * (scaleWhp n_max) ^ 12) ≤ fs.overmarsCursor b + 16 ∧
    16 * fs.overmarsInsCount b ≤ 17 * fs.overmarsCursor b ∧
    ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) (fs.overmarsCursor b)) omMap)

/-- Stage invariant between `fastDelete` and `epochTick` (relaxing `rebScanCursor < bktCount b_cur`
to `≤` and removing the `+ 16` slack in `16 * rebInsCount ≤ 17 * rebScanCursor` until `epochTick`
scans the next `16` slots). -/
@[expose] def ValidEpochStagePreTick (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) : Prop :=
  let M := numBucketsWhp n_max
  let oldEp := fs.oldEp
  let oldTr := fs.buf oldEp
  if fs.rebStage = 0 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    ∀ id < fs.stageCursor, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        fs.rebQueued b = 0 ∧ fs.rebDoneFlag b = 0
  else if fs.rebStage = 1 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    fs.dirtyCount ≤ fs.stageCursor ∧
    (∀ j < fs.dirtyCount,
      fs.dirtyBuckets j < M ∧
      fs.rebQueued (fs.dirtyBuckets j) = 1 ∧
      fs.rebDoneFlag (fs.dirtyBuckets j) = 0) ∧
    (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
      fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
    (∀ id < oldTr.itemAlloc, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        (fs.rebQueued b = 0 ∧ fs.rebDoneFlag b = 0) ∨
        ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b) ∧
    (∀ id < fs.stageCursor, ∀ b loc,
      bufCheckSlot oldTr id = some (b, loc) →
        ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b)
  else if fs.rebStage = 2 then
    fs.dirtyCount ≤ 2 * rIndepWhp c n_max ∧
    fs.dirtyIdx < fs.dirtyCount ∧
    (∀ j < fs.dirtyCount, fs.dirtyBuckets j < M) ∧
    (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
      fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
    (∀ j < fs.dirtyCount,
      (j < fs.dirtyIdx → fs.rebDoneFlag (fs.dirtyBuckets j) = 1) ∧
      (fs.dirtyIdx ≤ j → fs.rebDoneFlag (fs.dirtyBuckets j) = 0)) ∧
    (∀ b < M, ∀ loc < fs.bktCount b, fs.locState b loc = 2 + oldEp →
      ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b) ∧
    (fs.rebCandSalt < sMaxWhp c n_max →
      let b_cur := fs.dirtyBuckets fs.dirtyIdx
      ((fs.rebScanCursor = 0 ∧ fs.rebInsCount = 0) ∨
       (16 ≤ fs.rebScanCursor ∧ fs.rebScanCursor ≤ fs.bktCount b_cur ∧
        16 * fs.rebInsCount ≤ 17 * fs.rebScanCursor)) ∧
      (∀ l₁ < min (fs.bktCount b_cur) fs.rebScanCursor,
       ∀ l₂ < min (fs.bktCount b_cur) fs.rebScanCursor,
        (fs.locState b_cur l₁ = 1 ∨ fs.locState b_cur l₁ = 2 + oldEp) →
        (fs.locState b_cur l₂ = 1 ∨ fs.locState b_cur l₂ = 2 + oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b_cur l₁ =
          fs.fpAt c U n_max θ fs.rebCandSalt b_cur l₂ →
        l₁ = l₂) ∧
      ∃ rebMap,
        ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b_cur)) rebMap ∧
        SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b_cur)
          (fun loc => fs.locState b_cur loc = 1 ∨ fs.locState b_cur loc = 2 + oldEp)
          (min (fs.bktCount b_cur) fs.rebScanCursor) rebMap)
  else if fs.rebStage = 3 then
    fs.stageCursor ≤ oldTr.itemAlloc ∧
    (∀ id < fs.stageCursor, bufCheckSlot oldTr id = none)
  else
    True

theorem ValidFastState.toCore {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) :
    CoreFastInv c U V n_max θ fs dict :=
  { hth := hv.hth, curEp_or := hv.curEp_or, epochClock_lt := hv.epochClock_lt,
    rebStage_le := hv.rebStage_le, rebCollision_zero := hv.rebCollision_zero,
    qv_global := hv.qv_global, bktCount_le := hv.bktCount_le,
    bktCount_ge_zero := hv.bktCount_ge_zero, locState_active := hv.locState_active,
    locState_inactive := hv.locState_inactive, active_item := hv.active_item,
    quot_inj := hv.quot_inj, dict_map := hv.dict_map, poolFreeTop_le := hv.poolFreeTop_le,
    backPtr_valid := hv.backPtr_valid, freeStack_lt := hv.freeStack_lt,
    backPtr_inj := hv.backPtr_inj, freeStack_inj := hv.freeStack_inj,
    back_free_disj := hv.back_free_disj, pool_conservation := hv.pool_conservation,
    roles_valid := hv.roles_valid, bktSalt_lt := hv.bktSalt_lt,
    live_fp_inj := hv.live_fp_inj, live_valid := hv.live_valid,
    rKey_buf_inj := hv.rKey_buf_inj, bufCur_valid := hv.bufCur_valid,
    bufOld_valid := hv.bufOld_valid }

theorem CoreFastInv.toValidFastState {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hst : ValidEpochStage c U n_max θ fs) :
    ValidFastState c U V n_max θ fs dict :=
  { hth := hc.hth, curEp_or := hc.curEp_or, epochClock_lt := hc.epochClock_lt,
    rebStage_le := hc.rebStage_le, rebCollision_zero := hc.rebCollision_zero,
    qv_global := hc.qv_global, bktCount_le := hc.bktCount_le,
    bktCount_ge_zero := hc.bktCount_ge_zero, locState_active := hc.locState_active,
    locState_inactive := hc.locState_inactive, active_item := hc.active_item,
    quot_inj := hc.quot_inj, dict_map := hc.dict_map, poolFreeTop_le := hc.poolFreeTop_le,
    backPtr_valid := hc.backPtr_valid, freeStack_lt := hc.freeStack_lt,
    backPtr_inj := hc.backPtr_inj, freeStack_inj := hc.freeStack_inj,
    back_free_disj := hc.back_free_disj, pool_conservation := hc.pool_conservation,
    roles_valid := hc.roles_valid, bktSalt_lt := hc.bktSalt_lt,
    live_fp_inj := hc.live_fp_inj, live_valid := hc.live_valid,
    overmars_valid := hom, rKey_buf_inj := hc.rKey_buf_inj,
    bufCur_valid := hc.bufCur_valid, bufOld_valid := hc.bufOld_valid,
    stage_valid := hst }

theorem OvermarsBucketInv.toPre {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {b : ℕ} (h : OvermarsBucketInv c U n_max θ fs b) :
    PreOvermarsBucketInv c U n_max θ fs b := by
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨h0, hlt.le⟩
  · refine Or.inr ⟨h1, h16, hcur.le, by omega, by omega, omMap, hv, ?_⟩
    rwa [Nat.min_eq_right hcur.le]

theorem ValidEpochStage.toPreTick {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs : FastState}
    (h : ValidEpochStage c U n_max θ fs) : ValidEpochStagePreTick c U n_max θ fs := by
  dsimp only [ValidEpochStage, ValidEpochStagePreTick] at h ⊢
  split_ifs at h ⊢ with h0 h1 h2 h3
  · exact h
  · exact h
  · rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hs⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
    obtain ⟨hcur, hinj, hmap⟩ := hs hlt
    refine ⟨?_, hinj, hmap⟩
    rcases hcur with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins⟩
    · exact Or.inl ⟨hc0, hi0⟩
    · exact Or.inr ⟨h16, hc_lt.le, by omega⟩
  · exact h

private theorem fpAt_lt {c U n_max : ℕ} (θ : SeedWhp c U n_max) (fs : FastState)
    (salt b loc : ℕ) : fs.fpAt c U n_max θ salt b loc < 2 ^ fpBitsWhp n_max := by
  dsimp only [FastState.fpAt]
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨_, hu⟩
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

theorem keyValAt_eq_of_fields {c U n_max : ℕ} {θ₁ : BktSeed c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) :
    fs₁.keyValAt c U n_max θ₁ = fs₂.keyValAt c U n_max θ₁ := by
  funext b loc
  dsimp only [FastState.keyValAt, FastState.physSlot]
  rw [hq, hbp]

theorem fpAt_eq_of_fields {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) (salt b : ℕ) :
    fs₁.fpAt c U n_max θ salt b = fs₂.fpAt c U n_max θ salt b := by
  funext loc
  dsimp only [FastState.fpAt]
  rw [keyValAt_eq_of_fields hq hbp]

theorem rKeyAt_eq_of_fields {c U n_max : ℕ} {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState}
    (hq : fs₁.quotArr = fs₂.quotArr) (hbp : fs₁.backPtr = fs₂.backPtr) :
    fs₁.rKeyAt c U n_max θ = fs₂.rKeyAt c U n_max θ := by
  funext b loc
  dsimp only [FastState.rKeyAt]
  rw [keyValAt_eq_of_fields hq hbp]

theorem OvermarsBucketInv.of_eq_on {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {b : ℕ}
    (h : OvermarsBucketInv c U n_max θ fs b)
    (hfp : fs'.fpAt c U n_max θ (fs'.bktSalt b) b = fs.fpAt c U n_max θ (fs.bktSalt b) b)
    (hst : fs'.rebStage = fs.rebStage)
    (hep : fs'.curEp = fs.curEp)
    (hdn : fs'.rebDoneFlag b = fs.rebDoneFlag b)
    (hls : fs'.locState b = fs.locState b)
    (hcnt : fs'.bktCount b = fs.bktCount b)
    (hlic : fs'.liveInsCount b = fs.liveInsCount b)
    (hoa : fs'.overmarsActive b = fs.overmarsActive b)
    (hoc : fs'.overmarsCursor b = fs.overmarsCursor b)
    (hoi : fs'.overmarsInsCount b = fs.overmarsInsCount b)
    (hsl : fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b)) :
    OvermarsBucketInv c U n_max θ fs' b := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨hoa.trans h0, hlic.symm ▸ hlt⟩
  · refine Or.inr ⟨hoa.trans h1, hoc.symm ▸ h16, by omega, by omega, by omega,
      omMap, ?_, ?_⟩
    · rw [hoi, hsl]; exact hv
    · rw [hfp, hst, hold, hdn, hls, hoc]; exact hrel

theorem OvermarsBucketInv.of_eq_lt {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {b : ℕ}
    (h : OvermarsBucketInv c U n_max θ fs b)
    (hsalt : fs'.bktSalt b = fs.bktSalt b)
    (hfp : ∀ loc < fs.bktCount b,
      fs'.fpAt c U n_max θ (fs.bktSalt b) b loc = fs.fpAt c U n_max θ (fs.bktSalt b) b loc)
    (hst : fs'.rebStage = fs.rebStage)
    (hep : fs'.curEp = fs.curEp)
    (hdn : fs'.rebDoneFlag b = fs.rebDoneFlag b)
    (hls : ∀ loc < fs.bktCount b, fs'.locState b loc = fs.locState b loc)
    (hcnt : fs.bktCount b ≤ fs'.bktCount b)
    (hlic : fs'.liveInsCount b = fs.liveInsCount b)
    (hoa : fs'.overmarsActive b = fs.overmarsActive b)
    (hoc : fs'.overmarsCursor b = fs.overmarsCursor b)
    (hoi : fs'.overmarsInsCount b = fs.overmarsInsCount b)
    (hsl : fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b)) :
    OvermarsBucketInv c U n_max θ fs' b := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  rcases h with ⟨h0, hlt⟩ | ⟨h1, h16, hcur, hlin, hins, omMap, hv, hrel⟩
  · exact Or.inl ⟨hoa.trans h0, hlic.symm ▸ hlt⟩
  · refine Or.inr ⟨hoa.trans h1, hoc.symm ▸ h16, by omega, by omega, by omega,
      omMap, ?_, ?_⟩
    · rw [hoi, hsl]; exact hv
    · rw [hsalt, hst, hold, hdn, hoc]
      exact hrel.congr (fun loc hlt => hfp loc (hlt.trans hcur))
        (fun loc hlt => by rw [hls loc (hlt.trans hcur)])

theorem ValidEpochStage.of_rebSlice_eq {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState}
    (h : ValidEpochStage c U n_max θ fs)
    (hq : fs'.quotArr = fs.quotArr) (hbp : fs'.backPtr = fs.backPtr)
    (hcnt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hep : fs'.curEp = fs.curEp) (hst : fs'.rebStage = fs.rebStage)
    (hsc : fs'.stageCursor = fs.stageCursor) (hdc : fs'.dirtyCount = fs.dirtyCount)
    (hdb : fs'.dirtyBuckets = fs.dirtyBuckets) (hdi : fs'.dirtyIdx = fs.dirtyIdx)
    (hdn : fs'.rebDoneFlag = fs.rebDoneFlag) (hrq : fs'.rebQueued = fs.rebQueued)
    (hcs : fs'.rebCandSalt = fs.rebCandSalt) (hrc : fs'.rebScanCursor = fs.rebScanCursor)
    (hri : fs'.rebInsCount = fs.rebInsCount) (hbuf : fs'.buf = fs.buf)
    (hsl : ∀ bc < numBucketsWhp n_max,
      fs'.slices (fs'.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc)) :
    ValidEpochStage c U n_max θ fs' := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  dsimp only [ValidEpochStage] at h ⊢
  rw [hst, hold, hbuf, hsc, hdc, hdb, hdi, hdn, hrq, hcnt, hls, hcs, hrc, hri]
  split_ifs at h ⊢ with hs0 hs1 hs2 hs3
  · exact h
  · exact h
  · rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
    obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt
    have hbc : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
    rw [fpAt_eq_of_fields hq hbp fs.rebCandSalt (fs.dirtyBuckets fs.dirtyIdx)]
    refine ⟨hcur_r, hinj_r, rm, ?_, hrr⟩
    rwa [hsl _ hbc]
  · exact h

theorem ValidEpochStagePreTick.of_rebSlice_eq {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState}
    (h : ValidEpochStagePreTick c U n_max θ fs)
    (hq : fs'.quotArr = fs.quotArr) (hbp : fs'.backPtr = fs.backPtr)
    (hcnt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hep : fs'.curEp = fs.curEp) (hst : fs'.rebStage = fs.rebStage)
    (hsc : fs'.stageCursor = fs.stageCursor) (hdc : fs'.dirtyCount = fs.dirtyCount)
    (hdb : fs'.dirtyBuckets = fs.dirtyBuckets) (hdi : fs'.dirtyIdx = fs.dirtyIdx)
    (hdn : fs'.rebDoneFlag = fs.rebDoneFlag) (hrq : fs'.rebQueued = fs.rebQueued)
    (hcs : fs'.rebCandSalt = fs.rebCandSalt) (hrc : fs'.rebScanCursor = fs.rebScanCursor)
    (hri : fs'.rebInsCount = fs.rebInsCount) (hbuf : fs'.buf = fs.buf)
    (hsl : ∀ bc < numBucketsWhp n_max,
      fs'.slices (fs'.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc)) :
    ValidEpochStagePreTick c U n_max θ fs' := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  dsimp only [ValidEpochStagePreTick] at h ⊢
  rw [hst, hold, hbuf, hsc, hdc, hdb, hdi, hdn, hrq, hcnt, hls, hcs, hrc, hri]
  split_ifs at h ⊢ with hs0 hs1 hs2 hs3
  · exact h
  · exact h
  · rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
    obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt
    have hbc : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
    rw [fpAt_eq_of_fields hq hbp fs.rebCandSalt (fs.dirtyBuckets fs.dirtyIdx)]
    refine ⟨hcur_r, hinj_r, rm, ?_, hrr⟩
    rwa [hsl _ hbc]
  · exact h

private theorem upd_idem {α : Type*} {β : α → Sort*} [DecidableEq α]
    (f : (a : α) → β a) (a : α) (v w : β a) :
    Function.update (Function.update f a v) a w = Function.update f a w := by
  funext x
  by_cases hx : x = a
  · subst hx; simp
  · simp [hx]

private theorem overmarsScanSteps_spec {c U n_max b : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcnt_le : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12)
    (hinj : ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₁) = true →
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₂) = true →
      fs.fpAt c U n_max θ (fs.bktSalt b) b l₁ = fs.fpAt c U n_max θ (fs.bktSalt b) b l₂ →
      l₁ = l₂)
    (hins_ub : fs.overmarsInsCount b + rem ≤ 8 * (scaleWhp n_max) ^ 12)
    (hom : ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) (fs.overmarsCursor b)) omMap) :
    ∃ sl' cur' ins' omMap',
      overmarsScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl'
          overmarsCursor := Function.update fs.overmarsCursor b cur'
          overmarsInsCount := Function.update fs.overmarsInsCount b ins' } ∧
      cur' = fs.overmarsCursor b + rem ∧
      ins' ≤ fs.overmarsInsCount b + rem ∧
      ValidWhpSlice n_max ins' sl' omMap' ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) cur') omMap' := by
  induction rem generalizing fs with
  | zero =>
    obtain ⟨omMap, hv, hrel⟩ := hom
    refine ⟨fs.slices (fs.overmarsSliceIdx b), fs.overmarsCursor b, fs.overmarsInsCount b, omMap,
      ?_, by omega, by omega, hv, hrel⟩
    cases fs
    simp [overmarsScanSteps, Function.update_eq_self]
  | succ rem ih =>
    obtain ⟨omMap, hv, hrel⟩ := hom
    dsimp only [overmarsScanSteps]
    set cur := fs.overmarsCursor b
    set omIdx := fs.overmarsSliceIdx b
    by_cases hcond : cur < fs.bktCount b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true
    · rw [ite_eq_left hcond]
      obtain ⟨hcur_lt, hlive_cur⟩ := hcond
      have hmin_eq : min (fs.bktCount b) cur = cur := Nat.min_eq_right hcur_lt.le
      rw [hmin_eq] at hrel
      have hfp_lt : fs.fpAt c U n_max θ (fs.bktSalt b) b cur < 2 ^ fpBitsWhp n_max :=
        fpAt_lt θ fs (fs.bktSalt b) b cur
      have hval_lt : cur < 2 ^ valLaneBitsWhp n_max := by
        rw [valLane_pow_eq]; omega
      have hins1 := hv.insert_spec hth (by omega) hfp_lt hval_lt
      have hfresh : ∀ loc < cur,
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true →
          fs.fpAt c U n_max θ (fs.bktSalt b) b loc ≠
            fs.fpAt c U n_max θ (fs.bktSalt b) b cur :=
        fun loc hlt hpl heq =>
          Nat.ne_of_lt hlt (hinj loc (hlt.trans hcur_lt) cur hcur_lt hpl hlive_cur heq)
      have hrel1 := hrel.step_true hlive_cur hfresh
      have hmin1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
        Nat.min_eq_right (Nat.succ_le_of_lt hcur_lt)
      set sl1 := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices omIdx) (fs.fpAt c U n_max θ (fs.bktSalt b) b cur) cur
      let fs1 : FastState :=
        { fs with
          slices := Function.update fs.slices omIdx sl1
          overmarsCursor := Function.update fs.overmarsCursor b (cur + 1)
          overmarsInsCount := Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) }
      have hfs1_om : ∃ omMap1,
          ValidWhpSlice n_max (fs1.overmarsInsCount b) (fs1.slices (fs1.overmarsSliceIdx b))
            omMap1 ∧
          SliceMapRel (fs1.fpAt c U n_max θ (fs1.bktSalt b) b)
            (fun loc =>
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) (fs1.locState b loc) = true)
            (min (fs1.bktCount b) (fs1.overmarsCursor b)) omMap1 := by
        refine ⟨Function.update omMap (fs.fpAt c U n_max θ (fs.bktSalt b) b cur) (some cur),
          ?_, ?_⟩
        · dsimp only [fs1, FastState.overmarsSliceIdx, omIdx]
          simpa only [Function.update_self] using hins1.2
        · rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl]
          have hold_eq : fs1.oldEp = fs.oldEp := rfl
          rw [hold_eq]
          dsimp only [fs1]
          simpa only [Function.update_self, hmin1] using hrel1
      obtain ⟨sl', cur', ins', omMap', heq', hcur', hins', hv', hrel'⟩ :=
        ih fs1 hcnt_le hinj
          (by dsimp only [fs1]; rw [Function.update_self]; omega) hfs1_om
      have hfp1 : fs1.fpAt c U n_max θ (fs1.bktSalt b) b =
          fs.fpAt c U n_max θ (fs.bktSalt b) b := fpAt_eq_of_fields rfl rfl _ _
      have hold1 : fs1.oldEp = fs.oldEp := rfl
      rw [hfp1, hold1] at hrel'
      dsimp only [fs1, FastState.overmarsSliceIdx] at heq' hcur' hins' hrel'
      rw [Function.update_self] at hcur' hins'
      refine ⟨sl', cur', ins', omMap', ?_, by omega, by omega, hv', hrel'⟩
      rw [heq']
      dsimp only [omIdx, FastState.overmarsSliceIdx]
      rw [upd_idem, upd_idem, upd_idem]
    · rw [ite_eq_right hcond]
      let fs1 : FastState :=
        { fs with overmarsCursor := Function.update fs.overmarsCursor b (cur + 1) }
      have hrel1 : SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
          (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
          (min (fs.bktCount b) (cur + 1)) omMap := by
        by_cases hcur_lt : cur < fs.bktCount b
        · have hnot_live : ¬(inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
              (fs.locState b cur) = true) := fun hl => hcond ⟨hcur_lt, hl⟩
          rw [Nat.min_eq_right hcur_lt.le] at hrel
          rw [Nat.min_eq_right (Nat.succ_le_of_lt hcur_lt)]
          exact hrel.step_false hnot_live
        · have hge : fs.bktCount b ≤ cur := Nat.not_lt.mp hcur_lt
          rw [Nat.min_eq_left hge] at hrel
          rw [Nat.min_eq_left (hge.trans (Nat.le_succ cur))]
          exact hrel
      have hfs1_om : ∃ omMap1,
          ValidWhpSlice n_max (fs1.overmarsInsCount b) (fs1.slices (fs1.overmarsSliceIdx b))
            omMap1 ∧
          SliceMapRel (fs1.fpAt c U n_max θ (fs1.bktSalt b) b)
            (fun loc =>
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) (fs1.locState b loc) = true)
            (min (fs1.bktCount b) (fs1.overmarsCursor b)) omMap1 := by
        refine ⟨omMap, hv, ?_⟩
        rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl]
        have hold_eq : fs1.oldEp = fs.oldEp := rfl
        rw [hold_eq]
        dsimp only [fs1]
        simpa only [Function.update_self] using hrel1
      obtain ⟨sl', cur', ins', omMap', heq', hcur', hins', hv', hrel'⟩ :=
        ih fs1 hcnt_le hinj (by dsimp only [fs1]; omega) hfs1_om
      have hfp1 : fs1.fpAt c U n_max θ (fs1.bktSalt b) b =
          fs.fpAt c U n_max θ (fs.bktSalt b) b := fpAt_eq_of_fields rfl rfl _ _
      have hold1 : fs1.oldEp = fs.oldEp := rfl
      rw [hfp1, hold1] at hrel'
      dsimp only [fs1, FastState.overmarsSliceIdx] at heq' hcur' hins' hrel'
      rw [Function.update_self] at hcur'
      refine ⟨sl', cur', ins', omMap', ?_, by omega, by omega, hv', hrel'⟩
      rw [heq']
      dsimp only [omIdx, FastState.overmarsSliceIdx]
      rw [upd_idem]

/-- `overmarsStep` on bucket `b < numBucketsWhp n_max` restores `OvermarsBucketInv` on `b` while
preserving `CoreFastInv`, `OvermarsBucketInv` on all `b' ≠ b`, `ValidEpochStage`, and
`ValidEpochStagePreTick`. -/
theorem overmarsStep_spec {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hom_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fs b')
    (hom_b : PreOvermarsBucketInv c U n_max θ fs b) :
    let fs' := overmarsStep c U n_max θ b fs
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    (ValidEpochStage c U n_max θ fs → ValidEpochStage c U n_max θ fs') ∧
    (ValidEpochStagePreTick c U n_max θ fs → ValidEpochStagePreTick c U n_max θ fs') ∧
    fs'.curEp = fs.curEp ∧
    fs'.epochClock = fs.epochClock ∧
    fs'.rebStage = fs.rebStage ∧
    fs'.buf = fs.buf := by
  have hL2 : 2 ≤ scaleWhp n_max := two_le_scaleWhp n_max
  have hL12 : 4096 ≤ (scaleWhp n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_3L : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  obtain ⟨hlr_lt, hor_lt, hro_ne⟩ := hc.roles_valid b hb
  -- Helper: any update confined to `(liveRole b, overmarsRole b)` as a swap (or identity) and
  -- `slices` at `overmarsSliceIdx b` leaves `rebSliceIdx b'` and `slices (rebSliceIdx b')`
  -- untouched for EVERY `b'`!
  dsimp only [overmarsStep]
  -- Case split on whether `overmarsStep` is completely idle (`overmarsActive b = 0 ∧ liveInsCount b
  -- < 5 * L ^ 12`) vs active after `fs0`!
  rcases hom_b with ⟨ha0, hlic_le⟩ | ⟨ha1, h16, hcur_le, hlin, hins_le, omMap0, hv0, hrel0⟩
  · by_cases htrig : 5 * (scaleWhp n_max) ^ 12 ≤ fs.liveInsCount b
    · -- Triggers activation: `fs0` resets `overmarsSliceIdx b` and sets `overmarsActive b = 1`!
      have hcond0 : fs.overmarsActive b = 0 ∧ 5 * (scaleWhp n_max) ^ 12 ≤ fs.liveInsCount b :=
        ⟨ha0, htrig⟩
      rw [ite_eq_left hcond0]
      set fs0 : FastState :=
        { fs with
          overmarsActive := Function.update fs.overmarsActive b 1
          overmarsCursor := Function.update fs.overmarsCursor b 0
          overmarsInsCount := Function.update fs.overmarsInsCount b 0
          slices := Function.update fs.slices (fs.overmarsSliceIdx b)
            (resetBTreeSlice (fs.slices (fs.overmarsSliceIdx b))) }
      have ha0_1 : fs0.overmarsActive b = 1 := by dsimp only [fs0]; simp
      rw [ite_eq_left ha0_1]
      have hom0 : ∃ omMap,
          ValidWhpSlice n_max (fs0.overmarsInsCount b) (fs0.slices (fs0.overmarsSliceIdx b))
            omMap ∧
          SliceMapRel (fs0.fpAt c U n_max θ (fs0.bktSalt b) b)
            (fun loc =>
              inLiveTree fs0.rebStage fs0.oldEp (fs0.rebDoneFlag b) (fs0.locState b loc) = true)
            (min (fs0.bktCount b) (fs0.overmarsCursor b)) omMap := by
        refine ⟨fun _ => none, ?_, ?_⟩
        · dsimp only [fs0, FastState.overmarsSliceIdx]
          rw [Function.update_self, Function.update_self]
          exact validSlice_zero _ _ _ 0 _
        · dsimp only [fs0]
          rw [Function.update_self, Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)
      obtain ⟨sl1, cur1, ins1, omMap1, hscan_eq, hcur1, hins1, hv1, hrel1⟩ :=
        overmarsScanSteps_spec hc.hth θ 16 fs0 hcnt_3L (hc.live_fp_inj b hb)
          (by dsimp only [fs0]; rw [Function.update_self]; omega) hom0
      rw [hscan_eq]
      have hfp0 : fs0.fpAt c U n_max θ (fs0.bktSalt b) b =
          fs.fpAt c U n_max θ (fs.bktSalt b) b := fpAt_eq_of_fields rfl rfl _ _
      have hold0 : fs0.oldEp = fs.oldEp := rfl
      rw [hfp0, hold0] at hrel1
      dsimp only [fs0] at hcur1 hins1 hrel1
      rw [Function.update_self] at hcur1 hins1
      -- Simplify stacked `Function.update`s in `fs1`
      let fs1 : FastState :=
        { fs with
          overmarsActive := Function.update fs.overmarsActive b 1
          overmarsCursor := Function.update fs.overmarsCursor b cur1
          overmarsInsCount := Function.update fs.overmarsInsCount b ins1
          slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1 }
      have hfs1_eq :
          ({ fs0 with
              slices := Function.update fs0.slices (fs0.overmarsSliceIdx b) sl1
              overmarsCursor := Function.update fs0.overmarsCursor b cur1
              overmarsInsCount := Function.update fs0.overmarsInsCount b ins1 } : FastState) =
            fs1 := by
        dsimp only [fs0, fs1, FastState.overmarsSliceIdx]
        rw [upd_idem, upd_idem, upd_idem]
      rw [hfs1_eq]
      have hne_lo : fs.overmarsSliceIdx b ≠ fs.liveSliceIdx b := by
        dsimp only [FastState.overmarsSliceIdx, FastState.liveSliceIdx]; omega
      have hne_reb_all : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b ≠ fs.rebSliceIdx b' := by
        intro b' hb'
        obtain ⟨hlr', hor', hne'⟩ := hc.roles_valid b' hb'
        dsimp only [FastState.overmarsSliceIdx, FastState.rebSliceIdx, FastState.rebRole]
        by_cases hbb : b' = b
        · subst hbb; omega
        · intro heq
          have hrr : 3 - fs.liveRole b' - fs.overmarsRole b' < 3 := by omega
          exact hbb (sliceIdx_inj hor_lt hrr heq).1.symm
      by_cases hdone : fs1.bktCount b ≤ fs1.overmarsCursor b
      · rw [ite_eq_left hdone]
        dsimp only [fs1] at hdone
        rw [Function.update_self] at hdone
        have hmin_eq : min (fs.bktCount b) cur1 = fs.bktCount b := Nat.min_eq_left hdone
        rw [hmin_eq] at hrel1
        have hreb_eq : ∀ bc < numBucketsWhp n_max,
            ({ fs1 with
                liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
                overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
                liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
                overmarsActive := Function.update fs1.overmarsActive b 0
                overmarsCursor := Function.update fs1.overmarsCursor b 0
                overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
                FastState).slices
              (({ fs1 with
                  liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
                  overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
                  liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
                  overmarsActive := Function.update fs1.overmarsActive b 0
                  overmarsCursor := Function.update fs1.overmarsCursor b 0
                  overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
                  FastState).rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
          intro bc hbc
          have hridx_eq : ({ fs1 with
              liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
              overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
              liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
              overmarsActive := Function.update fs1.overmarsActive b 0
              overmarsCursor := Function.update fs1.overmarsCursor b 0
              overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
              FastState).rebSliceIdx bc = fs.rebSliceIdx bc := by
            dsimp only [FastState.rebSliceIdx, FastState.rebRole, fs1]
            by_cases hbb : bc = b
            · subst hbb; simp only [Function.update_self]; omega
            · simp [hbb]
          rw [hridx_eq]
          dsimp only [fs1]
          exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
        refine ⟨?_, ?_,
          fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl hreb_eq,
          fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl hreb_eq,
          rfl, rfl, rfl, rfl⟩
        · refine { hc with
            roles_valid := fun b' hb' => by
              by_cases hbb : b' = b
              · subst hbb; dsimp only [fs1]; simp [hor_lt, hlr_lt, Ne.symm hro_ne]
              · dsimp only [fs1]; simp [hbb, hc.roles_valid b' hb']
            live_valid := fun b' hb' => by
              by_cases hbb : b' = b
              · subst hbb
                refine ⟨omMap1, ?_, hrel1⟩
                dsimp only [FastState.liveSliceIdx, fs1, FastState.overmarsSliceIdx]
                simp only [Function.update_self]
                exact hv1
              · obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
                refine ⟨lm, ?_, hrl⟩
                have hne_s : 3 * b' + fs.liveRole b' ≠ fs.overmarsSliceIdx b := by
                  dsimp only [FastState.overmarsSliceIdx]
                  intro heq
                  exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_lt heq).1
                dsimp only [FastState.liveSliceIdx, fs1]
                simp only [Function.update_of_ne hbb, Function.update_of_ne hne_s]
                exact hvl }
        · intro b' hb'
          by_cases hbb : b' = b
          · subst hbb
            left
            dsimp only [fs1]
            simp only [Function.update_self]
            exact ⟨trivial, by omega⟩
          · have hne_om : 3 * b' + fs.overmarsRole b' ≠ fs.overmarsSliceIdx b := by
              dsimp only [FastState.overmarsSliceIdx]
              intro heq
              exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_lt heq).1
            refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
              rfl ?_ ?_ ?_ ?_ ?_
            · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
            · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
            · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
            · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
            · dsimp only [FastState.overmarsSliceIdx, fs1] at hne_om ⊢
              simp only [Function.update_of_ne hbb]
              exact Function.update_of_ne hne_om _ _
      · rw [ite_eq_right hdone]
        dsimp only [fs1] at hdone
        rw [Function.update_self] at hdone
        have hcur_lt_b : cur1 < fs.bktCount b := Nat.lt_of_not_le hdone
        rw [Nat.min_eq_right hcur_lt_b.le] at hrel1
        have hreb_eq : ∀ bc < numBucketsWhp n_max,
            fs1.slices (fs1.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
          intro bc hbc
          dsimp only [fs1, FastState.rebSliceIdx, FastState.rebRole]
          exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
        refine ⟨?_, ?_,
          fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl hreb_eq,
          fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl hreb_eq,
          rfl, rfl, rfl, rfl⟩
        · refine { hc with
            live_valid := fun b' hb' => by
              obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
              refine ⟨lm, ?_, hrl⟩
              have hne_s : fs.liveSliceIdx b' ≠ fs.overmarsSliceIdx b := by
                by_cases hbb : b' = b
                · subst hbb; exact hne_lo.symm
                · dsimp only [FastState.liveSliceIdx, FastState.overmarsSliceIdx]
                  intro heq
                  exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_lt heq).1
              dsimp only [fs1, FastState.liveSliceIdx] at hne_s ⊢
              rwa [Function.update_of_ne hne_s] }
        · intro b' hb'
          by_cases hbb : b' = b
          · subst hbb
            right
            dsimp only [fs1, FastState.overmarsSliceIdx]
            simp only [Function.update_self]
            exact ⟨trivial, by omega, hcur_lt_b, by omega, by omega, omMap1, hv1, hrel1⟩
          · have hne_om : 3 * b' + fs.overmarsRole b' ≠ fs.overmarsSliceIdx b := by
              dsimp only [FastState.overmarsSliceIdx]
              intro heq
              exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_lt heq).1
            refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
              rfl rfl ?_ ?_ ?_ ?_
            · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
            · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
            · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
            · dsimp only [FastState.overmarsSliceIdx, fs1]
              exact Function.update_of_ne hne_om _ _
    · -- Stays completely inactive (`fs' = fs`)!
      have hncond0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (scaleWhp n_max) ^ 12 ≤ fs.liveInsCount b) :=
        fun ⟨_, h⟩ => htrig h
      rw [ite_eq_right hncond0, ite_eq_right (by omega : ¬(fs.overmarsActive b = 1))]
      refine ⟨hc, fun b' hb' => ?_, id, id, rfl, rfl, rfl, rfl⟩
      by_cases hbb : b' = b
      · subst hbb; exact Or.inl ⟨ha0, Nat.lt_of_not_le htrig⟩
      · exact hom_other b' hb' hbb
  · -- Already active (`overmarsActive b = 1`)!
    have hncond0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (scaleWhp n_max) ^ 12 ≤ fs.liveInsCount b) :=
      by omega
    rw [ite_eq_right hncond0, ite_eq_left ha1]
    have hins_ub : fs.overmarsInsCount b + 16 ≤ 8 * (scaleWhp n_max) ^ 12 := by omega
    obtain ⟨sl1, cur1, ins1, omMap1, hscan_eq, hcur1, hins1, hv1, hrel1⟩ :=
      overmarsScanSteps_spec hc.hth θ 16 fs hcnt_3L (hc.live_fp_inj b hb) hins_ub
        ⟨omMap0, hv0, hrel0⟩
    rw [hscan_eq]
    set fs1 : FastState :=
      { fs with
        slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1
        overmarsCursor := Function.update fs.overmarsCursor b cur1
        overmarsInsCount := Function.update fs.overmarsInsCount b ins1 }
    have hne_lo : fs.overmarsSliceIdx b ≠ fs.liveSliceIdx b := by
      dsimp only [FastState.overmarsSliceIdx, FastState.liveSliceIdx]; omega
    have hne_reb_all : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b ≠ fs.rebSliceIdx b' := by
      intro b' hb'
      obtain ⟨hlr', hor', hne'⟩ := hc.roles_valid b' hb'
      dsimp only [FastState.overmarsSliceIdx, FastState.rebSliceIdx, FastState.rebRole]
      by_cases hbb : b' = b
      · subst hbb; omega
      · intro heq
        have hrr : 3 - fs.liveRole b' - fs.overmarsRole b' < 3 := by omega
        exact hbb (sliceIdx_inj hor_lt hrr heq).1.symm
    by_cases hdone : fs1.bktCount b ≤ fs1.overmarsCursor b
    · rw [ite_eq_left hdone]
      dsimp only [fs1] at hdone
      rw [Function.update_self] at hdone
      rw [Nat.min_eq_left hdone] at hrel1
      have hreb_eq : ∀ bc < numBucketsWhp n_max,
          ({ fs1 with
              liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
              overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
              liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
              overmarsActive := Function.update fs1.overmarsActive b 0
              overmarsCursor := Function.update fs1.overmarsCursor b 0
              overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
              FastState).slices
            (({ fs1 with
                liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
                overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
                liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
                overmarsActive := Function.update fs1.overmarsActive b 0
                overmarsCursor := Function.update fs1.overmarsCursor b 0
                overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
                FastState).rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
        intro bc hbc
        have hridx_eq : ({ fs1 with
            liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
            overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
            liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
            overmarsActive := Function.update fs1.overmarsActive b 0
            overmarsCursor := Function.update fs1.overmarsCursor b 0
            overmarsInsCount := Function.update fs1.overmarsInsCount b 0 } :
            FastState).rebSliceIdx bc = fs.rebSliceIdx bc := by
          dsimp only [FastState.rebSliceIdx, FastState.rebRole, fs1]
          by_cases hbb : bc = b
          · subst hbb; simp only [Function.update_self]; omega
          · simp [hbb]
        rw [hridx_eq]
        dsimp only [fs1]
        exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
      refine ⟨?_, ?_,
        fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hreb_eq,
        fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hreb_eq,
        rfl, rfl, rfl, rfl⟩
      · refine { hc with
          roles_valid := fun b' hb' => by
            by_cases hbb : b' = b
            · subst hbb; dsimp only [fs1]; simp [hor_lt, hlr_lt, Ne.symm hro_ne]
            · dsimp only [fs1]; simp [hbb, hc.roles_valid b' hb']
          live_valid := fun b' hb' => by
            by_cases hbb : b' = b
            · subst hbb
              refine ⟨omMap1, ?_, hrel1⟩
              dsimp only [FastState.liveSliceIdx, fs1, FastState.overmarsSliceIdx]
              simp only [Function.update_self]
              exact hv1
            · obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
              refine ⟨lm, ?_, hrl⟩
              have hne_s : 3 * b' + fs.liveRole b' ≠ fs.overmarsSliceIdx b := by
                dsimp only [FastState.overmarsSliceIdx]
                intro heq
                exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_lt heq).1
              dsimp only [FastState.liveSliceIdx, fs1]
              simp only [Function.update_of_ne hbb, Function.update_of_ne hne_s]
              exact hvl }
      · intro b' hb'
        by_cases hbb : b' = b
        · subst hbb
          left
          dsimp only [fs1]
          simp only [Function.update_self]
          exact ⟨trivial, by omega⟩
        · have hne_om : 3 * b' + fs.overmarsRole b' ≠ fs.overmarsSliceIdx b := by
            dsimp only [FastState.overmarsSliceIdx]
            intro heq
            exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_lt heq).1
          refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
            rfl ?_ ?_ ?_ ?_ ?_
          · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
          · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
          · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
          · dsimp only [fs1]; simp only [Function.update_of_ne hbb]
          · dsimp only [FastState.overmarsSliceIdx, fs1] at hne_om ⊢
            simp only [Function.update_of_ne hbb]
            exact Function.update_of_ne hne_om _ _
    · rw [ite_eq_right hdone]
      dsimp only [fs1] at hdone
      rw [Function.update_self] at hdone
      have hcur_lt_b : cur1 < fs.bktCount b := Nat.lt_of_not_le hdone
      rw [Nat.min_eq_right hcur_lt_b.le] at hrel1
      have hreb_eq : ∀ bc < numBucketsWhp n_max,
          fs1.slices (fs1.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
        intro bc hbc
        dsimp only [fs1, FastState.rebSliceIdx, FastState.rebRole]
        exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
      refine ⟨?_, ?_,
        fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hreb_eq,
        fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl hreb_eq,
        rfl, rfl, rfl, rfl⟩
      · refine { hc with
          live_valid := fun b' hb' => by
            obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
            refine ⟨lm, ?_, hrl⟩
            have hne_s : fs.liveSliceIdx b' ≠ fs.overmarsSliceIdx b := by
              by_cases hbb : b' = b
              · subst hbb; exact hne_lo.symm
              · dsimp only [FastState.liveSliceIdx, FastState.overmarsSliceIdx]
                intro heq
                exact hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_lt heq).1
            dsimp only [fs1, FastState.liveSliceIdx] at hne_s ⊢
            rwa [Function.update_of_ne hne_s] }
      · intro b' hb'
        by_cases hbb : b' = b
        · subst hbb
          right
          dsimp only [fs1, FastState.overmarsSliceIdx]
          simp only [Function.update_self]
          exact ⟨ha1, by omega, hcur_lt_b, by omega, by omega, omMap1, hv1, hrel1⟩
        · have hne_om : 3 * b' + fs.overmarsRole b' ≠ fs.overmarsSliceIdx b := by
            dsimp only [FastState.overmarsSliceIdx]
            intro heq
            exact hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_lt heq).1
          refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
            rfl rfl rfl ?_ ?_ ?_
          · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
          · dsimp only [fs1]; exact Function.update_of_ne hbb _ _
          · dsimp only [FastState.overmarsSliceIdx, fs1]
            exact Function.update_of_ne hne_om _ _

/-! ## Section 3: Fast-mode deletion (`ValidFastState.fastDelete_spec`) -/

private theorem buf_del_at_ep {c n_max st rKey ep : ℕ} (buf : ℕ → BufTrie)
    (hep : ep = 0 ∨ ep = 1) :
    (if st = 2 then
        Function.update buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (buf 0) rKey)
      else if st = 3 then
        Function.update buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (buf 1) rKey)
      else buf) ep =
      if st = 2 + ep then bufDelete (cTabWhp c) (bCharWhp n_max) (buf ep) rKey else buf ep := by
  rcases hep with rfl | rfl
  · by_cases h2 : st = 2
    · simp [h2]
    · by_cases h3 : st = 3
      · simp [h3]
      · simp [h2, h3]
  · by_cases h3 : st = 3
    · simp [h3]
    · by_cases h2 : st = 2
      · simp [h2]
      · simp [h2, h3]

private theorem buf_ins_at_ep {c n_max st rKey b loc ep : ℕ} (buf : ℕ → BufTrie)
    (hep : ep = 0 ∨ ep = 1) :
    (if st = 2 then
        Function.update buf 0 (bufInsert (cTabWhp c) (bCharWhp n_max) (buf 0) rKey b loc)
      else if st = 3 then
        Function.update buf 1 (bufInsert (cTabWhp c) (bCharWhp n_max) (buf 1) rKey b loc)
      else buf) ep =
      if st = 2 + ep then bufInsert (cTabWhp c) (bCharWhp n_max) (buf ep) rKey b loc
      else buf ep := by
  rcases hep with rfl | rfl
  · by_cases h2 : st = 2
    · simp [h2]
    · by_cases h3 : st = 3
      · simp [h3]
      · simp [h2, h3]
  · by_cases h3 : st = 3
    · simp [h3]
    · by_cases h2 : st = 2
      · simp [h2]
      · simp [h2, h3]

private theorem oldEp_or {fs : FastState} (h : fs.curEp = 0 ∨ fs.curEp = 1) :
    fs.oldEp = 0 ∨ fs.oldEp = 1 := by
  rcases h with hc | hc <;> simp [FastState.oldEp, hc]

/-- Releasing `loc_last` (`fs.bktCount b = loc_last + 1`) preserves all backyard-pool invariants. -/
private theorem pool_release_last {c U V n_max b loc_last : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hbp' : fs'.backPtr = fs.backPtr)
    (hown' : fs'.poolOwner = fs.poolOwner)
    (htop' : fs'.poolFreeTop =
      if capFrontWhp n_max ≤ loc_last then fs.poolFreeTop + 1 else fs.poolFreeTop)
    (hstk' : fs'.poolFreeStack =
      if capFrontWhp n_max ≤ loc_last then
        Function.update fs.poolFreeStack fs.poolFreeTop
          (fs.backPtr b (loc_last - capFrontWhp n_max))
      else fs.poolFreeStack) :
    fs'.poolFreeTop ≤ poolSizeWhp n_max ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
      fs'.backPtr b' k < poolSizeWhp n_max ∧
      fs'.poolOwner (fs'.backPtr b' k) = b' * capBackWhp n_max + k) ∧
    (∀ j < fs'.poolFreeTop, fs'.poolFreeStack j < poolSizeWhp n_max) ∧
    (∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs'.bktCount b₁ - capFrontWhp n_max,
     ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs'.bktCount b₂ - capFrontWhp n_max,
       fs'.backPtr b₁ k₁ = fs'.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂) ∧
    (∀ j₁ < fs'.poolFreeTop, ∀ j₂ < fs'.poolFreeTop,
      fs'.poolFreeStack j₁ = fs'.poolFreeStack j₂ → j₁ = j₂) ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
     ∀ j < fs'.poolFreeTop, fs'.backPtr b' k ≠ fs'.poolFreeStack j) ∧
    fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
  have hsub_le : ∀ b' < numBucketsWhp n_max,
      fs'.bktCount b' - capFrontWhp n_max ≤ fs.bktCount b' - capFrontWhp n_max := by
    intro b' _
    rw [hbkt']
    by_cases hbb : b' = b
    · subst hbb; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hbb]
  have hsum_split_old := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs.bktCount b' - capFrontWhp n_max) (Finset.mem_range.mpr hb)
  have hsum_split_new := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs'.bktCount b' - capFrontWhp n_max) (Finset.mem_range.mpr hb)
  have herase_eq :
      ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs'.bktCount x - capFrontWhp n_max) =
        ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs.bktCount x - capFrontWhp n_max) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hbkt', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have hcons : fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
    have hpc := hc.pool_conservation
    rw [← hsum_split_old, hcnt] at hpc
    rw [← hsum_split_new, herase_eq, hbkt', Function.update_self, htop']
    split_ifs with hcf <;> omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, hcons⟩
  · intro b' hb' k hk
    rw [hbp', hown']
    exact hc.backPtr_valid b' hb' k (hk.trans_le (hsub_le b' hb'))
  · intro j hj
    rw [htop'] at hj
    rw [hstk']
    split_ifs with hcf
    · rw [ite_eq_left hcf] at hj
      by_cases hjeq : j = fs.poolFreeTop
      · subst hjeq; rw [Function.update_self]
        exact (hc.backPtr_valid b hb (loc_last - capFrontWhp n_max) (by omega)).1
      · rw [Function.update_of_ne hjeq]
        exact hc.freeStack_lt j (by omega)
    · rw [ite_eq_right hcf] at hj
      exact hc.freeStack_lt j hj
  · intro b₁ hb₁ k₁ hk₁ b₂ hb₂ k₂ hk₂ heq
    rw [hbp'] at heq
    exact hc.backPtr_inj b₁ hb₁ k₁ (hk₁.trans_le (hsub_le b₁ hb₁))
      b₂ hb₂ k₂ (hk₂.trans_le (hsub_le b₂ hb₂)) heq
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [htop'] at hj₁ hj₂
    rw [hstk'] at heq
    split_ifs at hj₁ hj₂ heq with hcf
    · by_cases h1 : j₁ = fs.poolFreeTop <;> by_cases h2 : j₂ = fs.poolFreeTop
      · omega
      · subst h1
        rw [Function.update_self, Function.update_of_ne h2] at heq
        exact absurd heq
          (hc.back_free_disj b hb (loc_last - capFrontWhp n_max) (by omega) j₂ (by omega))
      · subst h2
        rw [Function.update_of_ne h1, Function.update_self] at heq
        exact absurd heq.symm
          (hc.back_free_disj b hb (loc_last - capFrontWhp n_max) (by omega) j₁ (by omega))
      · rw [Function.update_of_ne h1, Function.update_of_ne h2] at heq
        exact hc.freeStack_inj j₁ (by omega) j₂ (by omega) heq
    · exact hc.freeStack_inj j₁ hj₁ j₂ hj₂ heq
  · intro b' hb' k hk j hj
    rw [htop'] at hj
    rw [hbp', hstk']
    split_ifs at hj ⊢ with hcf
    · by_cases hjeq : j = fs.poolFreeTop
      · subst hjeq
        rw [Function.update_self]
        intro heq
        obtain ⟨rfl, hkeq⟩ := hc.backPtr_inj b' hb' k (hk.trans_le (hsub_le b' hb'))
          b hb (loc_last - capFrontWhp n_max) (by omega) heq
        rw [hbkt', Function.update_self] at hk
        omega
      · rw [Function.update_of_ne hjeq]
        exact hc.back_free_disj b' hb' k (hk.trans_le (hsub_le b' hb')) j (by omega)
    · exact hc.back_free_disj b' hb' k (hk.trans_le (hsub_le b' hb')) j hj

/-- Abstract dictionary-map and quotient-injectivity preservation under deleting `(b, loc_del)` and
relocating `(b, loc_last)` (when `loc_del < loc_last`). -/
private theorem dict_map_after_delete {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {u : Fin U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb_eq : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hq_del : fs.quotArr (fs.physSlot n_max b loc_del) = keyQuotient (bWhp n_max) u.val)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hother : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ loc < fs.bktCount b',
      fs'.quotArr (fs'.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
      fs'.valArr (fs'.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc))
    (hfwd : ∀ loc' < loc_last, ∃ loc < loc_last + 1, loc ≠ loc_del ∧
      fs'.quotArr (fs'.physSlot n_max b loc') = fs.quotArr (fs.physSlot n_max b loc) ∧
      fs'.valArr (fs'.physSlot n_max b loc') = fs.valArr (fs.physSlot n_max b loc) ∧
      (∀ l₂ < loc_last,
        fs'.quotArr (fs'.physSlot n_max b loc') = fs'.quotArr (fs'.physSlot n_max b l₂) →
        loc' = l₂))
    (hbwd : ∀ loc < loc_last + 1, loc ≠ loc_del → ∃ loc' < loc_last,
      fs'.quotArr (fs'.physSlot n_max b loc') = fs.quotArr (fs.physSlot n_max b loc) ∧
      fs'.valArr (fs'.physSlot n_max b loc') = fs.valArr (fs.physSlot n_max b loc)) :
    (∀ b' < numBucketsWhp n_max, ∀ l₁ < fs'.bktCount b', ∀ l₂ < fs'.bktCount b',
      fs'.quotArr (fs'.physSlot n_max b' l₁) = fs'.quotArr (fs'.physSlot n_max b' l₂) →
      l₁ = l₂) ∧
    (∀ u' : Fin U,
      let b' := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val
      let q' := keyQuotient (bWhp n_max) u'.val
      ((Function.update dict u none) u' = none ↔
        ∀ loc < fs'.bktCount b', fs'.quotArr (fs'.physSlot n_max b' loc) ≠ q') ∧
      (∀ v, (Function.update dict u none) u' = some v ↔
        ∃ loc < fs'.bktCount b',
          fs'.quotArr (fs'.physSlot n_max b' loc) = q' ∧
          fs'.valArr (fs'.physSlot n_max b' loc) = v)) := by
  have hb : b < numBucketsWhp n_max := hb_eq ▸ feistelBucket_lt _ _ _
  refine ⟨fun b' hb' l₁ hl₁ l₂ hl₂ heq => ?_, fun u' => ?_⟩
  · rw [hbkt'] at hl₁ hl₂
    by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self] at hl₁ hl₂
      obtain ⟨_, _, _, _, _, hinj⟩ := hfwd l₁ hl₁
      exact hinj l₂ hl₂ heq
    · rw [Function.update_of_ne hbb] at hl₁ hl₂
      rw [(hother b' hb' hbb l₁ hl₁).1, (hother b' hb' hbb l₂ hl₂).1] at heq
      exact hc.quot_inj b' hb' l₁ hl₁ l₂ hl₂ heq
  · dsimp only
    set b' := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val
    set q' := keyQuotient (bWhp n_max) u'.val
    have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
    by_cases hu_eq : u' = u
    · subst hu_eq
      have hb'_eq : b' = b := hb_eq
      simp only [Function.update_self, hbkt', hb'_eq, true_iff, reduceCtorEq, false_iff,
        not_exists, not_and]
      refine ⟨fun loc' hloc' hq' => ?_, fun v loc' hloc' hq' _ => ?_⟩
      · obtain ⟨loc, hloc, hne_d, hqe, _⟩ := hfwd loc' hloc'
        have h1 : fs.quotArr (fs.physSlot n_max b loc) = fs.quotArr (fs.physSlot n_max b loc_del) :=
          hqe.symm.trans (hq'.trans hq_del.symm)
        exact hne_d (hc.quot_inj b hb loc (hcnt ▸ hloc) loc_del (hcnt ▸ hld_lt) h1)
      · obtain ⟨loc, hloc, hne_d, hqe, _⟩ := hfwd loc' hloc'
        have h1 : fs.quotArr (fs.physSlot n_max b loc) = fs.quotArr (fs.physSlot n_max b loc_del) :=
          hqe.symm.trans (hq'.trans hq_del.symm)
        exact hne_d (hc.quot_inj b hb loc (hcnt ▸ hloc) loc_del (hcnt ▸ hld_lt) h1)
    · rw [Function.update_of_ne hu_eq]
      obtain ⟨hnone_iff, hsome_iff⟩ := hc.dict_map u'
      by_cases hbb : b' = b
      · have hq_ne : q' ≠ keyQuotient (bWhp n_max) u.val := by
          intro hqe
          apply hu_eq
          apply Fin.ext
          rw [← feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val,
            ← feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val]
          change feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b' q' =
            feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
              (keyQuotient (bWhp n_max) u.val)
          rw [hbb, hb_eq, hqe]
        have hbb_raw : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val = b := hbb
        rw [hbkt', hbb, Function.update_self]
        refine ⟨?_, fun v => ?_⟩
        · rw [hnone_iff, hbb_raw, hcnt]
          refine ⟨fun hall loc' hloc' hqe' => ?_, fun hall loc hloc hqe => ?_⟩
          · obtain ⟨loc, hloc, _, hq1, _⟩ := hfwd loc' hloc'
            exact hall loc hloc (hq1.symm.trans hqe')
          · have hne_d : loc ≠ loc_del := fun h => hq_ne (hqe.symm.trans (h ▸ hq_del))
            obtain ⟨loc', hloc', hq1, _⟩ := hbwd loc hloc hne_d
            exact hall loc' hloc' (hq1.trans hqe)
        · rw [hsome_iff v, hbb_raw, hcnt]
          refine ⟨fun ⟨loc, hloc, hqe, hve⟩ => ?_, fun ⟨loc', hloc', hqe', hve'⟩ => ?_⟩
          · have hne_d : loc ≠ loc_del := fun h => hq_ne (hqe.symm.trans (h ▸ hq_del))
            obtain ⟨loc', hloc', hq1, hv1⟩ := hbwd loc hloc hne_d
            exact ⟨loc', hloc', hq1.trans hqe, hv1.trans hve⟩
          · obtain ⟨loc, hloc, _, hq1, hv1, _⟩ := hfwd loc' hloc'
            exact ⟨loc, hloc, hq1.symm.trans hqe', hv1.symm.trans hve'⟩
      · rw [hbkt', Function.update_of_ne hbb]
        refine ⟨?_, fun v => ?_⟩
        · rw [hnone_iff]
          exact ⟨fun hall loc hloc => (hother b' hb' hbb loc hloc).1.symm ▸ hall loc hloc,
            fun hall loc hloc => (hother b' hb' hbb loc hloc).1 ▸ hall loc hloc⟩
        · rw [hsome_iff v]
          refine ⟨fun ⟨loc, hloc, hqe, hve⟩ =>
            ⟨loc, hloc, (hother b' hb' hbb loc hloc).1.trans hqe,
              (hother b' hb' hbb loc hloc).2.trans hve⟩,
            fun ⟨loc, hloc, hqe, hve⟩ =>
            ⟨loc, hloc, (hother b' hb' hbb loc hloc).1.symm.trans hqe,
              (hother b' hb' hbb loc hloc).2.symm.trans hve⟩⟩

private theorem rKeyAt_lt {c U n_max : ℕ} (θ : SeedWhp c U n_max) (fs : FastState)
    (b loc : ℕ) : fs.rKeyAt c U n_max θ b loc < 2 ^ (cTabWhp c * bCharWhp n_max) := by
  dsimp only [FastState.rKeyAt]
  split_ifs with h
  · exact fpReducedKey_lt c U n_max θ.2 ⟨_, h⟩
  · exact Nat.two_pow_pos _

/-- Parametric epoch-buffer preservation across `fastDelete` (applicable to both `curEp` and
`oldEp` when `rebStage ≤ 3`). -/
private theorem buf_valid_after_delete {c U V n_max b loc_del loc_last ep : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {rKey_u : ℕ}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u)
    (hbuf0 :
      (fs.buf ep).itemAlloc ≤ 2 * rIndepWhp c n_max ∧
      (fs.buf ep).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf ep).itemAlloc ∧
      ∃ m0,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) m0 ∧
        BufMapRel (numBucketsWhp n_max) (2 + ep) fs.bktCount fs.locState
          (fs.rKeyAt c U n_max θ) m0)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hpres_eq : loc_del = loc_last →
      ∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b',
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc)
    (hpres_lt : loc_del < loc_last →
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', ¬(b' = b ∧ loc = loc_del) →
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc) ∧
      fs'.locState b loc_del = fs.locState b loc_last ∧
      fs'.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last) :
    let tr1 :=
      if fs.locState b loc_del = 2 + ep then
        bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey_u
      else fs.buf ep
    let tr' :=
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + ep then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1 (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1
    tr'.itemAlloc = (fs.buf ep).itemAlloc ∧
    tr'.nodeAlloc = (fs.buf ep).nodeAlloc ∧
    (∃ m',
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr' m' ∧
      BufMapRel (numBucketsWhp n_max) (2 + ep) fs'.bktCount fs'.locState
        (fs'.rKeyAt c U n_max θ) m') ∧
    (∀ id, bufCheckSlot (fs.buf ep) id = none → bufCheckSlot tr' id = none) ∧
    (∀ id b' loc', bufCheckSlot tr' id = some (b', loc') →
      ∃ loc₀, bufCheckSlot (fs.buf ep) id = some (b', loc₀)) := by
  intro tr1 tr'
  obtain ⟨hia_le, hna_le, m0, hv0, hrel0⟩ := hbuf0
  have hrk_u_lt : rKey_u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    hrk_del ▸ rKeyAt_lt θ fs b loc_del
  have hrk_l_lt : fs.rKeyAt c U n_max θ b loc_last < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    rKeyAt_lt θ fs b loc_last
  let m1 :=
    if fs.locState b loc_del = 2 + ep then
      Function.update m0 (fs.rKeyAt c U n_max θ b loc_del) none
    else m0
  have htr1 : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr1 m1 ∧
      tr1.nodeAlloc = (fs.buf ep).nodeAlloc ∧
      tr1.itemAlloc = (fs.buf ep).itemAlloc ∧
      (∀ id, bufCheckSlot (fs.buf ep) id = none → bufCheckSlot tr1 id = none) ∧
      (∀ id b' loc', bufCheckSlot tr1 id = some (b', loc') →
        bufCheckSlot (fs.buf ep) id = some (b', loc')) := by
    dsimp only [tr1, m1]
    split_ifs with htd
    · rw [hrk_del]
      obtain ⟨hv1, hna1, hia1, _, hnone1⟩ := hv0.delete_spec hrk_u_lt
      exact ⟨hv1, hna1, hia1, hnone1, fun _ _ _ h => bufDelete_checkSlot_some h⟩
    · exact ⟨hv0, rfl, rfl, fun _ h => h, fun _ _ _ h => h⟩
  obtain ⟨hv1, hna1, hia1, hnone1, hsome1⟩ := htr1
  have hinj_ep : ∀ b₁ < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b₁,
      ∀ b₂ < numBucketsWhp n_max, ∀ l₂ < fs.bktCount b₂,
        fs.locState b₁ l₁ = 2 + ep → fs.locState b₂ l₂ = 2 + ep →
        fs.rKeyAt c U n_max θ b₁ l₁ = fs.rKeyAt c U n_max θ b₂ l₂ → b₁ = b₂ ∧ l₁ = l₂ :=
    fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h1 h2 =>
      hc.rKey_buf_inj b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ (by omega) (by omega)
  by_cases hlt : loc_del < loc_last
  · dsimp only [tr']
    rw [ite_eq_left hlt]
    obtain ⟨hpres, hst_d, hrk_d⟩ := hpres_lt hlt
    obtain ⟨hm1_last, hrel2⟩ := hrel0.relocate_last hb hcnt hlt hinj_ep
      (fun b' hb' loc hloc hne => (hpres b' hb' loc (hbkt' ▸ hloc) hne).1) hst_d
      (fun b' hb' loc hloc hne => (hpres b' hb' loc (hbkt' ▸ hloc) hne).2) hrk_d
    rw [← hbkt'] at hrel2
    split_ifs with htl
    · rw [ite_eq_left htl] at hrel2
      have hm1_some : m1 (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) := hm1_last htl
      have hm1_ne : m1 (fs.rKeyAt c U n_max θ b loc_last) ≠ none := by rw [hm1_some]; simp
      have hins := hv1.insert_spec (b := b) (loc := loc_del) hrk_l_lt
      obtain ⟨hna2, hia2, hnone2⟩ := hins.2.2.2.2.2.2.2 hm1_ne
      refine ⟨hia2.trans hia1, hna2.trans hna1, ⟨_, hins.1, hrel2⟩,
        fun id h => hnone2 id (hnone1 id h), fun id b' loc' hchk => ?_⟩
      obtain ⟨loc₁, hchk1⟩ := hv1.insert_same_bucket_checkSlot_some hrk_l_lt hm1_some hchk
      exact ⟨loc₁, hsome1 id b' loc₁ hchk1⟩
    · rw [ite_eq_right htl] at hrel2
      exact ⟨hia1, hna1, ⟨m1, hv1, hrel2⟩, hnone1, fun id b' loc' h => ⟨loc', hsome1 id b' loc' h⟩⟩
  · have heq_ll : loc_del = loc_last := by omega
    dsimp only [tr']
    rw [ite_eq_right hlt]
    subst heq_ll
    have hpres := hpres_eq rfl
    have hrel2 := hrel0.delete_last hb hcnt
      (fun b' hb' loc hloc h1 h2 =>
        hinj_ep b' hb' loc hloc b hb loc_del (by omega) h1 h2)
      (fun b' hb' loc hloc => (hpres b' hb' loc (hbkt' ▸ hloc)).1)
      (fun b' hb' loc hloc => (hpres b' hb' loc (hbkt' ▸ hloc)).2)
    rw [← hbkt'] at hrel2
    exact ⟨hia1, hna1, ⟨m1, hv1, hrel2⟩, hnone1, fun id b' loc' h => ⟨loc', hsome1 id b' loc' h⟩⟩

/-- Intermediate `fsAfterDel` invariant when `fastFindLoc` finds `loc_del = loc_last`. -/
private theorem fastDelete_afterDel_last_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {loc_del : ℕ}
    (hld_lt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr
      (fs.physSlot n_max (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val)
    (hnot_lt : ¬(loc_del <
      fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) - 1)) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let fs1 := fastDeleteErase c U n_max θ fs u b loc_del
    let fsA := fastDeleteShrink n_max b loc_last fs1
    CoreFastInv c U V n_max θ fsA (Function.update dict u none) ∧
    (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsA b') ∧
    PreOvermarsBucketInv c U n_max θ fsA b ∧
    ValidEpochStagePreTick c U n_max θ fsA := by
  intro b loc_last
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set lIdx := fs.liveSliceIdx b
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices lIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices lIdx) fp_live_u)
    else fs.slices
  set omIdx := fs.overmarsSliceIdx b
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 omIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 omIdx) fp_live_u)
    else slices1
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rIdx := fs.rebSliceIdx b
  set slices3 :=
    if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
      Function.update slices2 rIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices2 rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
    else slices2
  set fs1_loc : FastState := { fs with buf := buf1, slices := slices3 }
  have hfs1_eq : fastDeleteErase c U n_max θ fs u b loc_del = fs1_loc := rfl
  set cf := capFrontWhp n_max
  set freePair :=
    if cf ≤ loc_last then
      (fs.poolFreeTop + 1,
       Function.update fs.poolFreeStack fs.poolFreeTop (fs.backPtr b (loc_last - cf)))
    else (fs.poolFreeTop, fs.poolFreeStack)
  set fsA : FastState :=
    { fs with
      buf := buf1
      slices := slices3
      locState := Function.update fs.locState b (Function.update (fs.locState b) loc_last 0)
      bktCount := Function.update fs.bktCount b loc_last
      poolFreeTop := freePair.1
      poolFreeStack := freePair.2 }
  have hfsA_eq : fastDeleteShrink n_max b loc_last fs1_loc = fsA := rfl
  dsimp only
  rw [hfs1_eq, hfsA_eq]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hcnt : fs.bktCount b = loc_last + 1 := by
    dsimp only [b, loc_last] at hld_lt ⊢; omega
  have heq_ll : loc_del = loc_last := by
    dsimp only [b, loc_last] at hld_lt hnot_lt ⊢; omega
  have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
    dsimp only [FastState.keyValAt, b]
    rw [hq_del]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u := by
    dsimp only [FastState.rKeyAt, rKey_u]; simp [hkv_del, u.isLt]
  have hs_b : fs.bktSalt b < sMaxWhp c n_max := hv.bktSalt_lt b hb
  have hfp_live_del : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del = fp_live_u := by
    dsimp only [FastState.fpAt, fp_live_u, fpOfSalt]; simp [hs_b, hkv_del, u.isLt]
  -- Neither `omIdx` nor `rIdx` can be `< cursor` at `loc_last`!
  have hsl2_eq : slices2 = slices1 := by
    dsimp only [slices2]
    refine ite_eq_right fun ⟨ha1, hlt_c, _⟩ => ?_
    rcases hv.overmars_valid b hb with ⟨h0, _⟩ | ⟨_, _, hcur_lt, _⟩
    · omega
    · omega
  have hsl3_eq : slices3 = slices1 := by
    dsimp only [slices3]
    rw [hsl2_eq]
    refine ite_eq_right fun hcond => ?_
    simp only [rebActiveB, Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨hs2, hdi, hdb, hcs, _⟩, hlt_r, _⟩ := hcond
    have hstg := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg
    simp only [hs2, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hstg
    obtain ⟨hcur_or, _⟩ := hstg.2.2.2.2.2.2 hcs
    rw [hdb] at hcur_or
    rcases hcur_or with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
  obtain ⟨hlr_b, hor_b, hro_ne⟩ := hv.roles_valid b hb
  have hrr_b := rebRole_props hlr_b hor_b hro_ne
  have hl_ne_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3, 3 * b' + r ≠ lIdx := by
    intro b' _ hbb r hr heq
    exact hbb (sliceIdx_inj hr hlr_b heq).1
  have hphys_eq : fsA.physSlot n_max = fs.physSlot n_max := rfl
  have hfp_eq : ∀ salt b', fsA.fpAt c U n_max θ salt b' = fs.fpAt c U n_max θ salt b' :=
    fun salt b' => fpAt_eq_of_fields rfl rfl salt b'
  have hrk_eq : fsA.rKeyAt c U n_max θ = fs.rKeyAt c U n_max θ := rKeyAt_eq_of_fields rfl rfl
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      fsA.locState b' loc = fs.locState b' loc := by
    intro b' _ loc hloc
    dsimp only [fsA] at hloc ⊢
    by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self] at hloc ⊢
      exact Function.update_of_ne (Nat.ne_of_lt hloc) _ _
    · simp [hbb]
  have hpool := pool_release_last (fs' := fsA) hv.toCore hb hcnt rfl rfl rfl
    (by dsimp only [fsA, freePair]; split_ifs <;> rfl)
    (by dsimp only [fsA, freePair]; split_ifs <;> rfl)
  obtain ⟨hq_inj, hdict_map⟩ := dict_map_after_delete (fs' := fsA) hv.toCore rfl hcnt
    (hcnt ▸ hld_lt) hq_del rfl
    (fun _ _ _ _ _ => ⟨rfl, rfl⟩)
    (fun loc' hloc' => ⟨loc', by omega, by omega, rfl, rfl,
      fun l₂ hl₂ heq => hv.quot_inj b hb loc' (by omega) l₂ (by omega) heq⟩)
    (fun loc hloc hne => ⟨loc, by omega, rfl, rfl⟩)
  have hbuf_cur := buf_valid_after_delete (ep := fs.curEp) (fs' := fsA) hv.toCore hb hcnt
    (hcnt ▸ hld_lt) hrk_del hv.bufCur_valid rfl
    (fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc, congrFun (congrFun hrk_eq b') loc⟩)
    (fun hlt => absurd hlt hnot_lt)
  -- Live slice preservation on bucket `b`
  have hlive_b : ∃ liveMap',
      ValidWhpSlice n_max (fsA.liveInsCount b) (fsA.slices (fsA.liveSliceIdx b)) liveMap' ∧
      SliceMapRel (fsA.fpAt c U n_max θ (fsA.bktSalt b) b)
        (fun loc => inLiveTree fsA.rebStage fsA.oldEp (fsA.rebDoneFlag b) (fsA.locState b loc) =
          true)
        (fsA.bktCount b) liveMap' := by
    obtain ⟨lm0, hvl0, hrl0⟩ := hv.live_valid b hb
    rw [hcnt] at hrl0
    rw [hfp_eq]
    dsimp only [fsA, FastState.liveSliceIdx, FastState.oldEp]
    rw [hsl3_eq]
    simp only [Function.update_self]
    by_cases hinL : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
    · dsimp only [slices1, lIdx, FastState.liveSliceIdx]
      rw [ite_eq_left hinL, Function.update_self]
      have hfp_lt : fp_live_u < 2 ^ fpBitsWhp n_max :=
        hfp_live_del ▸ fpAt_lt θ fs (fs.bktSalt b) b loc_del
      have hvd := hvl0.delete_spec hv.hth (hv.liveInsCount_le hb) hfp_lt
      have hinL_ll : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fs.locState b loc_last) = true := heq_ll ▸ hinL
      have hfp_ll : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last = fp_live_u :=
        heq_ll ▸ hfp_live_del
      have hrld := hrl0.delete_last hinL_ll fun loc hlt hpl heq =>
        Nat.ne_of_lt hlt (hv.live_fp_inj b hb loc (by omega) loc_last (by omega) hpl hinL_ll heq)
      rw [hfp_ll] at hrld
      refine ⟨_, hvd, hrld.congr (fun _ _ => rfl) fun loc hlt => ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]; exact Iff.rfl
    · dsimp only [slices1, lIdx, FastState.liveSliceIdx]
      rw [ite_eq_right hinL]
      have hninL_ll : ¬(inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fs.locState b loc_last) = true) := heq_ll ▸ hinL
      have hrls := hrl0.skip_last hninL_ll
      refine ⟨lm0, hvl0, hrls.congr (fun _ _ => rfl) fun loc hlt => ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]; exact Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := hv.qv_global
        bktCount_le := fun b' hb' => by
          dsimp only [fsA]
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self]
            exact Nat.le_of_lt ((heq_ll ▸ hld_lt).trans_le (hv.bktCount_le b hb))
          · rw [Function.update_of_ne hbb]; exact hv.bktCount_le b' hb'
        bktCount_ge_zero := fun b' hge => by
          dsimp only [fsA]
          rw [Function.update_of_ne (by omega)]; exact hv.bktCount_ge_zero b' hge
        locState_active := fun b' hb' loc hloc => by
          rw [hls_pres b' hb' loc hloc]
          exact hv.locState_active b' hb' loc (by
            dsimp only [fsA] at hloc
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hloc; omega
            · rwa [Function.update_of_ne hbb] at hloc)
        locState_inactive := fun b' loc hna => by
          dsimp only [fsA] at hna ⊢
          by_cases hbb : b' = b
          · subst hbb
            rw [Function.update_self] at hna ⊢
            by_cases hll : loc = loc_last
            · subst hll; simp
            · rw [Function.update_of_ne hll]
              exact hv.locState_inactive b loc fun ⟨_, hlt⟩ => hna ⟨hb, by omega⟩
          · simp only [Function.update_of_ne hbb] at hna ⊢
            exact hv.locState_inactive b' loc hna
        active_item := fun b' hb' loc hloc => by
          refine hv.active_item b' hb' loc ?_
          dsimp only [fsA] at hloc
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hloc; omega
          · rwa [Function.update_of_ne hbb] at hloc
        quot_inj := hq_inj
        dict_map := hdict_map
        poolFreeTop_le := hpool.1
        backPtr_valid := hpool.2.1
        freeStack_lt := hpool.2.2.1
        backPtr_inj := hpool.2.2.2.1
        freeStack_inj := hpool.2.2.2.2.1
        back_free_disj := hpool.2.2.2.2.2.1
        pool_conservation := hpool.2.2.2.2.2.2
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          rw [hls_pres b' hb' l₁ hl₁] at hin₁
          rw [hls_pres b' hb' l₂ hl₂] at hin₂
          rw [hfp_eq] at hfeq
          have hl₁' : l₁ < fs.bktCount b' := by
            dsimp only [fsA] at hl₁
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl₁; omega
            · rwa [Function.update_of_ne hbb] at hl₁
          have hl₂' : l₂ < fs.bktCount b' := by
            dsimp only [fsA] at hl₂
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hl₂; omega
            · rwa [Function.update_of_ne hbb] at hl₂
          exact hv.live_fp_inj b' hb' l₁ hl₁' l₂ hl₂' hin₁ hin₂ hfeq
        live_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · subst hbb; exact hlive_b
          · obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
            refine ⟨lm, ?_, ?_⟩
            · dsimp only [fsA, FastState.liveSliceIdx]
              rw [hsl3_eq]
              dsimp only [slices1]
              split_ifs with hinL
              · rw [Function.update_of_ne (hl_ne_other b' hb' hbb _ (hv.roles_valid b' hb').1)]
                exact hvl
              · exact hvl
            · rw [hfp_eq]
              dsimp only [fsA, FastState.oldEp]
              simp only [Function.update_of_ne hbb]
              exact hrl
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ hst₁ hst₂ hrkeq => by
          rw [hls_pres b₁ hb₁ l₁ hl₁] at hst₁
          rw [hls_pres b₂ hb₂ l₂ hl₂] at hst₂
          rw [hrk_eq] at hrkeq
          have hl₁' : l₁ < fs.bktCount b₁ := by
            dsimp only [fsA] at hl₁
            by_cases hbb : b₁ = b
            · subst hbb; rw [Function.update_self] at hl₁; omega
            · rwa [Function.update_of_ne hbb] at hl₁
          have hl₂' : l₂ < fs.bktCount b₂ := by
            dsimp only [fsA] at hl₂
            by_cases hbb : b₂ = b
            · subst hbb; rw [Function.update_self] at hl₂; omega
            · rwa [Function.update_of_ne hbb] at hl₂
          exact hv.rKey_buf_inj b₁ hb₁ l₁ hl₁' b₂ hb₂ l₂ hl₂' hst₁ hst₂ hrkeq
        bufCur_valid := by
          have hb1 : fsA.buf fsA.curEp =
              if st_del = 2 + fs.curEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey_u
              else fs.buf fs.curEp := buf_del_at_ep fs.buf hv.curEp_or
          have htr_eq : (if loc_del < loc_last then
              if fs.locState b loc_last = 2 + fs.curEp then
                bufInsert (cTabWhp c) (bCharWhp n_max) (fsA.buf fsA.curEp)
                  (fs.rKeyAt c U n_max θ b loc_last) b loc_del
              else fsA.buf fsA.curEp
            else fsA.buf fsA.curEp) = fsA.buf fsA.curEp := ite_eq_right hnot_lt
          obtain ⟨hia_eq, hna_eq, hmap_cur, _⟩ := hbuf_cur
          dsimp only [st_del] at hb1
          rw [← hb1, htr_eq] at hia_eq hna_eq hmap_cur
          exact ⟨hia_eq ▸ hv.bufCur_valid.1,
            hna_eq ▸ hia_eq ▸ hv.bufCur_valid.2.1, hmap_cur⟩
        bufOld_valid := by
          have hb_old : fsA.buf fs.oldEp =
              if st_del = 2 + fs.oldEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
              else fs.buf fs.oldEp := buf_del_at_ep fs.buf (oldEp_or hv.curEp_or)
          have hbo := hv.bufOld_valid
          have ho_eq : fsA.oldEp = fs.oldEp := rfl
          have hrs_eq : fsA.rebStage = fs.rebStage := rfl
          rw [ho_eq, hrs_eq]
          split_ifs at hbo ⊢ with hs3 hs4
          · have hbuf_old := buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
              (hcnt ▸ hld_lt) hrk_del hbo rfl
              (fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc,
                congrFun (congrFun hrk_eq b') loc⟩)
              (fun hlt => absurd hlt hnot_lt)
            obtain ⟨hia_eq, hna_eq, hmap_old, _⟩ := hbuf_old
            dsimp only [st_del] at hb_old
            rw [ite_eq_right hnot_lt, ← hb_old] at hia_eq hna_eq hmap_old
            exact ⟨hia_eq ▸ hbo.1, hna_eq ▸ hia_eq ▸ hbo.2.1, hmap_old⟩
          · have hst_ne : st_del ≠ 2 + fs.oldEp := hbo.1 b hb loc_del hld_lt
            rw [ite_eq_right hst_ne] at hb_old
            rw [hb_old]
            refine ⟨fun b' hb' loc hloc => ?_, hbo.2.1, hbo.2.2⟩
            rw [hls_pres b' hb' loc hloc]
            exact hbo.1 b' hb' loc (by
              dsimp only [fsA] at hloc
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hloc; omega
              · rwa [Function.update_of_ne hbb] at hloc)
          · have hst_ne : st_del ≠ 2 + fs.oldEp := hbo.1 b hb loc_del hld_lt
            rw [ite_eq_right hst_ne] at hb_old
            rw [hb_old]
            refine ⟨fun b' hb' loc hloc => ?_, hbo.2.1, hbo.2.2.1, hbo.2.2.2⟩
            rw [hls_pres b' hb' loc hloc]
            exact hbo.1 b' hb' loc (by
              dsimp only [fsA] at hloc
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hloc; omega
              · rwa [Function.update_of_ne hbb] at hloc) }
  · intro b' hb' hbb
    refine OvermarsBucketInv.of_eq_on (hv.overmars_valid b' hb') (hfp_eq _ _) rfl rfl rfl ?_ ?_
      rfl rfl rfl rfl ?_
    · dsimp only [fsA]; exact Function.update_of_ne hbb _ _
    · dsimp only [fsA]; exact Function.update_of_ne hbb _ _
    · dsimp only [fsA, FastState.overmarsSliceIdx]
      rw [hsl3_eq]
      dsimp only [slices1]
      split_ifs with hinL
      · exact Function.update_of_ne (hl_ne_other b' hb' hbb _ (hv.roles_valid b' hb').2.1) _ _
      · rfl
  · rcases hv.overmars_valid b hb with
      ⟨ha0, hlic⟩ | ⟨ha1, h16, hcur_lt, hlin, hins, omM, hv_om, hr_om⟩
    · exact Or.inl ⟨ha0, hlic.le⟩
    · have hcur_le : fs.overmarsCursor b ≤ loc_last := by omega
      dsimp only [PreOvermarsBucketInv]
      have hoa_eq : fsA.overmarsActive b = fs.overmarsActive b := rfl
      have hoc_eq : fsA.overmarsCursor b = fs.overmarsCursor b := rfl
      have hlic_eq : fsA.liveInsCount b = fs.liveInsCount b := rfl
      have hoi_eq : fsA.overmarsInsCount b = fs.overmarsInsCount b := rfl
      rw [hoa_eq, hoc_eq, hlic_eq, hoi_eq]
      refine Or.inr ⟨ha1, h16, ?_, by omega, by omega, omM, ?_, ?_⟩
      · dsimp only [fsA]; rw [Function.update_self]; exact hcur_le
      · dsimp only [fsA, FastState.overmarsSliceIdx]
        rw [hsl3_eq]
        dsimp only [slices1, lIdx, FastState.liveSliceIdx]
        split_ifs with hinL
        · rw [Function.update_of_ne (by omega : 3 * b + fs.overmarsRole b ≠ 3 * b + fs.liveRole b)]
          exact hv_om
        · exact hv_om
      · rw [hfp_eq]
        dsimp only [fsA, FastState.oldEp]
        simp only [Function.update_self, Nat.min_eq_right hcur_le]
        refine hr_om.congr (fun _ _ => rfl) fun loc hlt => ?_
        rw [Function.update_of_ne (by omega : loc ≠ loc_last)]
        exact Iff.rfl
  · have hstg := hv.stage_valid.toPreTick
    have hb_old : fsA.buf fs.oldEp =
        if st_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp := buf_del_at_ep fs.buf (oldEp_or hv.curEp_or)
    have hreb_st : fsA.rebStage = fs.rebStage := rfl
    have hold_ep : fsA.oldEp = fs.oldEp := rfl
    dsimp only [ValidEpochStagePreTick] at hstg ⊢
    rw [hreb_st, hold_ep]
    split_ifs at hstg ⊢ with hs0 hs1 hs2 hs3
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, _, hsome_old⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt) hrk_del hbo_v rfl
          (fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc,
            congrFun (congrFun hrk_eq b') loc⟩)
          (fun hlt => absurd hlt hnot_lt)
      dsimp only [st_del] at hb_old
      rw [ite_eq_right hnot_lt, ← hb_old] at hia_eq hsome_old
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        ∀ id < fs.stageCursor, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0
      rw [hia_eq]
      refine ⟨hstg.1, fun id hid b' loc' hchk => ?_⟩
      obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
      exact hstg.2 id hid b' loc₀ hchk0
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, _, hsome_old⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt) hrk_del hbo_v rfl
          (fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc,
            congrFun (congrFun hrk_eq b') loc⟩)
          (fun hlt => absurd hlt hnot_lt)
      dsimp only [st_del] at hb_old
      rw [ite_eq_right hnot_lt, ← hb_old] at hia_eq hsome_old
      rcases hstg with ⟨hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6⟩
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        fs.dirtyCount ≤ fs.stageCursor ∧
        (∀ j < fs.dirtyCount,
          fs.dirtyBuckets j < numBucketsWhp n_max ∧
          fs.rebQueued (fs.dirtyBuckets j) = 1 ∧
          fs.rebDoneFlag (fs.dirtyBuckets j) = 0) ∧
        (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
          fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
        (∀ id < (fsA.buf fs.oldEp).itemAlloc, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            (fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0) ∨
            ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b') ∧
        (∀ id < fs.stageCursor, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b')
      rw [hia_eq]
      refine ⟨hs1_1, hs1_2, hs1_3, hs1_4, fun id hid b' loc' hchk => ?_,
        fun id hid b' loc' hchk => ?_⟩
      · obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
        exact hs1_5 id hid b' loc₀ hchk0
      · obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
        exact hs1_6 id hid b' loc₀ hchk0
    · -- Stage 2!
      have hstg_full := hv.stage_valid
      dsimp only [ValidEpochStage] at hstg_full
      simp only [hs2, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hstg_full
      rcases hstg_full with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
      refine ⟨hd1, hd2, hd3, hd4, hd5, fun b' hb' loc hloc hst_old => ?_, fun hcs => ?_⟩
      · rw [hls_pres b' hb' loc hloc] at hst_old
        have hloc0 : loc < fs.bktCount b' := by
          dsimp only [fsA] at hloc
          by_cases hbb : b' = b
          · subst hbb; rw [Function.update_self] at hloc; omega
          · rwa [Function.update_of_ne hbb] at hloc
        exact hd6 b' hb' loc hloc0 hst_old
      · obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hcs
        set bc := fs.dirtyBuckets fs.dirtyIdx
        have hbc : bc < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
        have hne_rl : 3 * bc + (3 - fs.liveRole bc - fs.overmarsRole bc) ≠ lIdx := by
          by_cases hbb : bc = b
          · rw [hbb]; dsimp only [lIdx, FastState.liveSliceIdx]; omega
          · exact hl_ne_other bc hbc hbb _
              (rebRole_props (hv.roles_valid bc hbc).1 (hv.roles_valid bc hbc).2.1
                (hv.roles_valid bc hbc).2.2).1
        have hsl_bc : fsA.slices (fsA.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
          dsimp only [fsA, FastState.rebSliceIdx, FastState.rebRole]
          rw [hsl3_eq]
          dsimp only [slices1]
          split_ifs with hinL
          · exact Function.update_of_ne hne_rl _ _
          · rfl
        have hfp_bc : FastState.fpAt c U n_max θ fsA fs.rebCandSalt bc =
            fs.fpAt c U n_max θ fs.rebCandSalt bc := hfp_eq _ _
        have hrc_eq : fsA.rebScanCursor = fs.rebScanCursor := rfl
        have hri_eq : fsA.rebInsCount = fs.rebInsCount := rfl
        have hcs_eq : fsA.rebCandSalt = fs.rebCandSalt := rfl
        rw [hrc_eq, hri_eq, hcs_eq, hsl_bc, hfp_bc]
        by_cases hbb : bc = b
        · rw [hbb] at hcur_r hinj_r hvr hrr ⊢
          have hcntA_b : fsA.bktCount b = loc_last := by
            dsimp only [fsA]; exact Function.update_self _ _ _
          rw [hcntA_b]
          have hcur_le_ll : fs.rebScanCursor ≤ loc_last := by
            rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
          have hmin_old : min (fs.bktCount b) fs.rebScanCursor = fs.rebScanCursor :=
            Nat.min_eq_right (by omega)
          have hmin_new : min loc_last fs.rebScanCursor = fs.rebScanCursor :=
            Nat.min_eq_right hcur_le_ll
          rw [hmin_old] at hinj_r hrr
          rw [hmin_new]
          refine ⟨?_, ?_, rm, hvr, ?_⟩
          · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, _, hins⟩
            · exact Or.inl ⟨hc0, hi0⟩
            · exact Or.inr ⟨h16, hcur_le_ll, by omega⟩
          · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            rw [hls_pres b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)] at hp₁
            rw [hls_pres b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)] at hp₂
            exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          · refine hrr.congr (fun _ _ => rfl) fun loc hlt => ?_
            rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll)]
        · have hcntA_bc : fsA.bktCount bc = fs.bktCount bc := by
            dsimp only [fsA]; exact Function.update_of_ne hbb _ _
          rw [hcntA_bc]
          refine ⟨?_, ?_, rm, hvr, ?_⟩
          · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins⟩
            · exact Or.inl ⟨hc0, hi0⟩
            · exact Or.inr ⟨h16, hc_lt.le, by omega⟩
          · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            rw [hls_pres bc hbc l₁ (hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hl₁)] at hp₁
            rw [hls_pres bc hbc l₂ (hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hl₂)] at hp₂
            exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          · refine hrr.congr (fun _ _ => rfl) fun loc hlt => ?_
            rw [hls_pres bc hbc loc (hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hlt)]
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, hnone_old, _⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt) hrk_del hbo_v rfl
          (fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc,
            congrFun (congrFun hrk_eq b') loc⟩)
          (fun hlt => absurd hlt hnot_lt)
      dsimp only [st_del] at hb_old
      rw [ite_eq_right hnot_lt, ← hb_old] at hia_eq hnone_old
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        ∀ id < fs.stageCursor, bufCheckSlot (fsA.buf fs.oldEp) id = none
      rw [hia_eq]
      exact ⟨hstg.1, fun id hid => hnone_old id (hstg.2 id hid)⟩

/-- Intermediate `fsAfterDel` invariant when `fastFindLoc` finds `loc_del < loc_last`. -/
private theorem fastDelete_afterDel_reloc_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {loc_del : ℕ}
    (hld_lt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr
      (fs.physSlot n_max (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val)
    (hlt_ll : loc_del <
      fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) - 1) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let fs1 := fastDeleteErase c U n_max θ fs u b loc_del
    let fs2 := fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
    let fsA := fastDeleteShrink n_max b loc_last fs2
    CoreFastInv c U V n_max θ fsA (Function.update dict u none) ∧
    (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsA b') ∧
    PreOvermarsBucketInv c U n_max θ fsA b ∧
    ValidEpochStagePreTick c U n_max θ fsA := by
  intro b loc_last rebActiveB
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set lIdx := fs.liveSliceIdx b
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices lIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices lIdx) fp_live_u)
    else fs.slices
  set omIdx := fs.overmarsSliceIdx b
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 omIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 omIdx) fp_live_u)
    else slices1
  set rIdx := fs.rebSliceIdx b
  set slices3 :=
    if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
      Function.update slices2 rIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices2 rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
    else slices2
  set fs1 : FastState := { fs with buf := buf1, slices := slices3 }
  have hfs1_eq : fastDeleteErase c U n_max θ fs u b loc_del = fs1 := rfl
  set p_last := fs1.physSlot n_max b loc_last
  set p_del := fs1.physSlot n_max b loc_del
  set st_last := fs1.locState b loc_last
  set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
  set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
  set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
  set qArr' := Function.update fs1.quotArr p_del (fs1.quotArr p_last)
  set vArr' := Function.update fs1.valArr p_del (fs1.valArr p_last)
  set buf2 :=
    if st_last = 2 then
      Function.update fs1.buf 0
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
    else if st_last = 3 then
      Function.update fs1.buf 1
        (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
    else fs1.buf
  set sl_live' :=
    if inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last then
      Function.update fs1.slices lIdx
        (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs1.slices lIdx) fp_live_last loc_del)
    else fs1.slices
  set omPair :=
    if fs1.overmarsActive b = 1 ∧
        inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last then
      if loc_last < fs1.overmarsCursor b then
        (Function.update sl_live' omIdx
          (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_live' omIdx) fp_live_last loc_del),
         fs1.overmarsInsCount)
      else if loc_del < fs1.overmarsCursor b then
        (Function.update sl_live' omIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_live' omIdx) fp_live_last loc_del),
         Function.update fs1.overmarsInsCount b (fs1.overmarsInsCount b + 1))
      else (sl_live', fs1.overmarsInsCount)
    else (sl_live', fs1.overmarsInsCount)
  set sl_om' := omPair.1
  set omIns' := omPair.2
  set rebQuad :=
    if rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp) then
      if loc_last < fs1.rebScanCursor then
        (Function.update sl_om' rIdx
          (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_om' rIdx) fp_cand_last loc_del),
         (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
      else if loc_del < fs1.rebScanCursor then
        match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (sl_om' rIdx) fp_cand_last with
        | some _ =>
          (Function.update sl_om' rIdx (resetBTreeSlice (sl_om' rIdx)),
           (fs1.rebCandSalt + 1, (0, 0)))
        | none =>
          (Function.update sl_om' rIdx
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (sl_om' rIdx) fp_cand_last loc_del),
           (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount + 1)))
      else (sl_om', (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
    else (sl_om', (fs1.rebCandSalt, (fs1.rebScanCursor, fs1.rebInsCount)))
  set fs2 : FastState :=
    { fs1 with
      quotArr := qArr'
      valArr := vArr'
      locState := Function.update fs1.locState b
        (Function.update (fs1.locState b) loc_del st_last)
      buf := buf2
      slices := rebQuad.1
      overmarsInsCount := omIns'
      rebCandSalt := rebQuad.2.1
      rebScanCursor := rebQuad.2.2.1
      rebInsCount := rebQuad.2.2.2 }
  have hfs2_eq :
      fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1 = fs2 := rfl
  set cf := capFrontWhp n_max
  set freePair :=
    if cf ≤ loc_last then
      (fs2.poolFreeTop + 1,
       Function.update fs2.poolFreeStack fs2.poolFreeTop (fs2.backPtr b (loc_last - cf)))
    else (fs2.poolFreeTop, fs2.poolFreeStack)
  set fsA : FastState :=
    { fs2 with
      locState := Function.update fs2.locState b (Function.update (fs2.locState b) loc_last 0)
      bktCount := Function.update fs2.bktCount b loc_last
      poolFreeTop := freePair.1
      poolFreeStack := freePair.2 }
  have hfsA_eq : fastDeleteShrink n_max b loc_last fs2 = fsA := rfl
  dsimp only
  rw [hfs1_eq, hfs2_eq, hfsA_eq]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hld_lt_b : loc_del < fs.bktCount b := hld_lt
  have hlt_ll_b : loc_del < loc_last := hlt_ll
  have hcnt : fs.bktCount b = loc_last + 1 := by
    dsimp only [loc_last] at hlt_ll_b ⊢; omega
  have hll_lt : loc_last < fs.bktCount b := by omega
  have hL2 : 2 ≤ scaleWhp n_max := two_le_scaleWhp n_max
  have hL12 : 4096 ≤ (scaleWhp n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (scaleWhp n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_3L : fs.bktCount b ≤ 3 * (scaleWhp n_max) ^ 12 :=
    (hv.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
    dsimp only [FastState.keyValAt, b]
    rw [hq_del]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u := by
    dsimp only [FastState.rKeyAt, rKey_u]; simp [hkv_del, u.isLt]
  have hs_b : fs.bktSalt b < sMaxWhp c n_max := hv.bktSalt_lt b hb
  have hfp_live_del : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del = fp_live_u := by
    dsimp only [FastState.fpAt, fp_live_u, fpOfSalt]; simp [hs_b, hkv_del, u.isLt]
  have hfp_cand_del : fs.fpAt c U n_max θ fs.rebCandSalt b loc_del =
      fpOfSalt c U n_max θ.2 fs.rebCandSalt u := by
    dsimp only [FastState.fpAt, fpOfSalt]
    by_cases hs : fs.rebCandSalt < sMaxWhp c n_max
    · simp [hs, hkv_del, u.isLt]
    · simp [hs]
  have hrk1_last : rKey_last = fs.rKeyAt c U n_max θ b loc_last :=
    congrFun (congrFun (rKeyAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl) b) loc_last
  have hfp1_live : fp_live_last = fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last :=
    congrFun (fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl (fs.bktSalt b) b) loc_last
  have hfp1_cand : fp_cand_last = fs.fpAt c U n_max θ fs.rebCandSalt b loc_last :=
    congrFun (fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl fs.rebCandSalt b) loc_last
  obtain ⟨hlr_b, hor_b, hro_ne⟩ := hv.roles_valid b hb
  have hrr_b := rebRole_props hlr_b hor_b hro_ne
  have hl_ne_om : lIdx ≠ omIdx := by
    dsimp only [lIdx, omIdx, FastState.liveSliceIdx, FastState.overmarsSliceIdx]; omega
  have hl_ne_r : lIdx ≠ rIdx := by
    dsimp only [lIdx, rIdx, FastState.liveSliceIdx, FastState.rebSliceIdx, FastState.rebRole]; omega
  have hom_ne_r : omIdx ≠ rIdx := by
    dsimp only [omIdx, rIdx, FastState.overmarsSliceIdx, FastState.rebSliceIdx, FastState.rebRole]
    omega
  have hslice_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3,
      3 * b' + r ≠ lIdx ∧ 3 * b' + r ≠ omIdx ∧ 3 * b' + r ≠ rIdx := by
    intro b' _ hbb r hr
    refine ⟨fun h => hbb (sliceIdx_inj hr hlr_b h).1,
      fun h => hbb (sliceIdx_inj hr hor_b h).1,
      fun h => hbb (sliceIdx_inj hr hrr_b.1 h).1⟩
  -- Physical-slot & coordinate transport
  obtain ⟨_, hphys_inj⟩ := hv.physSlot_lt_and_inj
  have hphys_eq : fsA.physSlot n_max = fs.physSlot n_max := rfl
  have hqv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.quotArr (fs.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
      fsA.valArr (fs.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc) := by
    intro b' hb' loc hloc hne
    have hloc0 : loc < fs.bktCount b' := by
      dsimp only [fsA, fs2, fs1] at hloc
      by_cases hbb : b' = b
      · subst hbb; rw [Function.update_self] at hloc; omega
      · rwa [Function.update_of_ne hbb] at hloc
    have hp_ne : fs.physSlot n_max b' loc ≠ p_del := fun heq =>
      hne (hphys_inj b' hb' loc hloc0 b hb loc_del hld_lt_b heq)
    exact ⟨Function.update_of_ne hp_ne _ _, Function.update_of_ne hp_ne _ _⟩
  have hqv_at_del :
      fsA.quotArr (fs.physSlot n_max b loc_del) = fs.quotArr (fs.physSlot n_max b loc_last) ∧
      fsA.valArr (fs.physSlot n_max b loc_del) = fs.valArr (fs.physSlot n_max b loc_last) := by
    dsimp only [fsA, fs2, qArr', vArr', fs1]
    exact ⟨Function.update_self _ _ _, Function.update_self _ _ _⟩
  have hkv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.keyValAt c U n_max θ.1 b' loc = fs.keyValAt c U n_max θ.1 b' loc := by
    intro b' hb' loc hloc hne
    dsimp only [FastState.keyValAt]
    rw [hphys_eq, (hqv_pres b' hb' loc hloc hne).1]
  have hkv_at_del :
      fsA.keyValAt c U n_max θ.1 b loc_del = fs.keyValAt c U n_max θ.1 b loc_last := by
    dsimp only [FastState.keyValAt]
    rw [hphys_eq, hqv_at_del.1]
  have hfp_pres : ∀ salt b', b' < numBucketsWhp n_max → ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      FastState.fpAt c U n_max θ fsA salt b' loc = FastState.fpAt c U n_max θ fs salt b' loc := by
    intro salt b' hb' loc hloc hne
    dsimp only [FastState.fpAt]
    rw [hkv_pres b' hb' loc hloc hne]
  have hfp_at_del : ∀ salt,
      FastState.fpAt c U n_max θ fsA salt b loc_del =
        FastState.fpAt c U n_max θ fs salt b loc_last := by
    intro salt; dsimp only [FastState.fpAt]; rw [hkv_at_del]
  have hrk_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) →
      fsA.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc := by
    intro b' hb' loc hloc hne
    dsimp only [FastState.rKeyAt]; rw [hkv_pres b' hb' loc hloc hne]
  have hrk_at_del : fsA.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last := by
    dsimp only [FastState.rKeyAt]; rw [hkv_at_del]
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      ¬(b' = b ∧ loc = loc_del) → fsA.locState b' loc = fs.locState b' loc := by
    intro b' _ loc hloc hne
    dsimp only [fsA, fs2, fs1] at hloc ⊢
    by_cases hbb : b' = b
    · rw [hbb] at hloc hne ⊢
      rw [Function.update_self] at hloc ⊢
      have hne_d : loc ≠ loc_del := fun h => hne ⟨rfl, h⟩
      rw [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hloc),
        Function.update_of_ne hne_d]
    · simp [hbb]
  have hls_at_del : fsA.locState b loc_del = fs.locState b loc_last := by
    dsimp only [fsA, fs2, fs1, st_last]
    rw [Function.update_self, Function.update_self,
      Function.update_of_ne (Nat.ne_of_lt hlt_ll_b), Function.update_self]
  -- Slice isolation: `lIdx`, `omIdx`, `rIdx`, and `3 * b' + r` (`b' ≠ b`) never interfere!
  have hsl2_l : slices2 lIdx = slices1 lIdx := by
    dsimp only [slices2]
    split_ifs
    · exact Function.update_of_ne hl_ne_om _ _
    · rfl
  have hsl3_l : slices3 lIdx = slices1 lIdx := by
    dsimp only [slices3]
    split_ifs
    · exact (Function.update_of_ne hl_ne_r _ _).trans hsl2_l
    · exact hsl2_l
  have hsl3_om : slices3 omIdx = slices2 omIdx := by
    dsimp only [slices3]
    split_ifs
    · exact Function.update_of_ne hom_ne_r _ _
    · rfl
  have hsl1_om : slices1 omIdx = fs.slices omIdx := by
    dsimp only [slices1]
    split_ifs
    · exact Function.update_of_ne hl_ne_om.symm _ _
    · rfl
  have hsl1_r : slices1 rIdx = fs.slices rIdx := by
    dsimp only [slices1]
    split_ifs
    · exact Function.update_of_ne hl_ne_r.symm _ _
    · rfl
  have hsl2_r : slices2 rIdx = fs.slices rIdx := by
    dsimp only [slices2]
    split_ifs
    · exact (Function.update_of_ne hom_ne_r.symm _ _).trans hsl1_r
    · exact hsl1_r
  have hreb_l : rebQuad.1 lIdx = sl_live' lIdx := by
    have hom_l : sl_om' lIdx = sl_live' lIdx := by
      dsimp only [sl_om', omPair]
      by_cases h1 : fs1.overmarsActive b = 1 ∧
          inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true
      · rw [ite_eq_left h1]
        by_cases h2 : loc_last < fs1.overmarsCursor b
        · rw [ite_eq_left h2]; exact Function.update_of_ne hl_ne_om _ _
        · rw [ite_eq_right h2]
          by_cases h3 : loc_del < fs1.overmarsCursor b
          · rw [ite_eq_left h3]; exact Function.update_of_ne hl_ne_om _ _
          · rw [ite_eq_right h3]
      · rw [ite_eq_right h1]
    dsimp only [rebQuad]
    by_cases h1 : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true
    · rw [ite_eq_left h1]
      by_cases h2 : loc_last < fs1.rebScanCursor
      · rw [ite_eq_left h2]; exact (Function.update_of_ne hl_ne_r _ _).trans hom_l
      · rw [ite_eq_right h2]
        by_cases h3 : loc_del < fs1.rebScanCursor
        · rw [ite_eq_left h3]
          cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) (sl_om' rIdx)
            fp_cand_last <;> exact (Function.update_of_ne hl_ne_r _ _).trans hom_l
        · rw [ite_eq_right h3]; exact hom_l
    · rw [ite_eq_right h1]; exact hom_l
  have hreb_om : rebQuad.1 omIdx = sl_om' omIdx := by
    dsimp only [rebQuad]
    by_cases h1 : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true
    · rw [ite_eq_left h1]
      by_cases h2 : loc_last < fs1.rebScanCursor
      · rw [ite_eq_left h2]; exact Function.update_of_ne hom_ne_r _ _
      · rw [ite_eq_right h2]
        by_cases h3 : loc_del < fs1.rebScanCursor
        · rw [ite_eq_left h3]
          cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) (sl_om' rIdx)
            fp_cand_last <;> exact Function.update_of_ne hom_ne_r _ _
        · rw [ite_eq_right h3]
    · rw [ite_eq_right h1]
  have hsll_om : sl_live' omIdx = slices2 omIdx := by
    dsimp only [sl_live', fs1]
    split_ifs
    · exact (Function.update_of_ne hl_ne_om.symm _ _).trans hsl3_om
    · exact hsl3_om
  have hslom_r : sl_om' rIdx = slices3 rIdx := by
    have hsll_r : sl_live' rIdx = slices3 rIdx := by
      dsimp only [sl_live', fs1]
      split_ifs
      · exact Function.update_of_ne hl_ne_r.symm _ _
      · rfl
    dsimp only [sl_om', omPair]
    by_cases h1 : fs1.overmarsActive b = 1 ∧
        inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true
    · rw [ite_eq_left h1]
      by_cases h2 : loc_last < fs1.overmarsCursor b
      · rw [ite_eq_left h2]; exact (Function.update_of_ne hom_ne_r.symm _ _).trans hsll_r
      · rw [ite_eq_right h2]
        by_cases h3 : loc_del < fs1.overmarsCursor b
        · rw [ite_eq_left h3]; exact (Function.update_of_ne hom_ne_r.symm _ _).trans hsll_r
        · rw [ite_eq_right h3]; exact hsll_r
    · rw [ite_eq_right h1]; exact hsll_r
  have hreb_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3,
      rebQuad.1 (3 * b' + r) = fs.slices (3 * b' + r) := by
    intro b' hb' hbb r hr
    obtain ⟨hne1, hne2, hne3⟩ := hslice_other b' hb' hbb r hr
    have hs1 : slices1 (3 * b' + r) = fs.slices (3 * b' + r) := by
      dsimp only [slices1]
      split_ifs
      · exact Function.update_of_ne hne1 _ _
      · rfl
    have hs2 : slices2 (3 * b' + r) = fs.slices (3 * b' + r) := by
      dsimp only [slices2]
      split_ifs
      · exact (Function.update_of_ne hne2 _ _).trans hs1
      · exact hs1
    have hs3 : slices3 (3 * b' + r) = fs.slices (3 * b' + r) := by
      dsimp only [slices3]
      split_ifs
      · exact (Function.update_of_ne hne3 _ _).trans hs2
      · exact hs2
    have hsll : sl_live' (3 * b' + r) = fs.slices (3 * b' + r) := by
      dsimp only [sl_live', fs1]
      split_ifs
      · exact (Function.update_of_ne hne1 _ _).trans hs3
      · exact hs3
    have hslom : sl_om' (3 * b' + r) = fs.slices (3 * b' + r) := by
      dsimp only [sl_om', omPair]
      by_cases h1 : fs1.overmarsActive b = 1 ∧
          inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true
      · rw [ite_eq_left h1]
        by_cases h2 : loc_last < fs1.overmarsCursor b
        · rw [ite_eq_left h2]; exact (Function.update_of_ne hne2 _ _).trans hsll
        · rw [ite_eq_right h2]
          by_cases h3 : loc_del < fs1.overmarsCursor b
          · rw [ite_eq_left h3]; exact (Function.update_of_ne hne2 _ _).trans hsll
          · rw [ite_eq_right h3]; exact hsll
      · rw [ite_eq_right h1]; exact hsll
    dsimp only [rebQuad]
    by_cases h1 : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true
    · rw [ite_eq_left h1]
      by_cases h2 : loc_last < fs1.rebScanCursor
      · rw [ite_eq_left h2]; exact (Function.update_of_ne hne3 _ _).trans hslom
      · rw [ite_eq_right h2]
        by_cases h3 : loc_del < fs1.rebScanCursor
        · rw [ite_eq_left h3]
          cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) (sl_om' rIdx)
            fp_cand_last <;> exact (Function.update_of_ne hne3 _ _).trans hslom
        · rw [ite_eq_right h3]; exact hslom
    · rw [ite_eq_right h1]; exact hslom
  have hpool := pool_release_last (fs' := fsA) hv.toCore hb hcnt rfl rfl rfl
    (by dsimp only [fsA, freePair, fs2, fs1]; split_ifs <;> rfl)
    (by dsimp only [fsA, freePair, fs2, fs1]; split_ifs <;> rfl)
  obtain ⟨hq_inj, hdict_map⟩ := dict_map_after_delete (fs' := fsA) hv.toCore rfl hcnt
    (by omega) hq_del rfl
    (fun b' hb' hbb loc hloc =>
      hqv_pres b' hb' loc (by dsimp only [fsA, fs2, fs1]; rwa [Function.update_of_ne hbb])
        (fun ⟨h, _⟩ => hbb h))
    (fun loc' hloc' => by
      by_cases hld : loc' = loc_del
      · rw [hld]
        refine ⟨loc_last, by omega, by omega, hqv_at_del.1, hqv_at_del.2, fun l₂ hl₂ heq => ?_⟩
        by_cases h2 : l₂ = loc_del
        · exact h2.symm
        · have hp2 := (hqv_pres b hb l₂ (by dsimp [fsA, fs2, fs1]; simp [hl₂])
            (fun ⟨_, h⟩ => h2 h)).1
          rw [hphys_eq, hqv_at_del.1, hp2] at heq
          have := hv.quot_inj b hb loc_last hll_lt l₂ (by omega) heq
          omega
      · have hp1 := hqv_pres b hb loc' (by dsimp [fsA, fs2, fs1]; simp [hloc'])
          (fun ⟨_, h⟩ => hld h)
        refine ⟨loc', by omega, hld, hp1.1, hp1.2, fun l₂ hl₂ heq => ?_⟩
        by_cases h2 : l₂ = loc_del
        · rw [h2, hphys_eq, hp1.1, hqv_at_del.1] at heq
          have := hv.quot_inj b hb loc' (by omega) loc_last hll_lt heq
          omega
        · have hp2 := (hqv_pres b hb l₂ (by dsimp [fsA, fs2, fs1]; simp [hl₂])
            (fun ⟨_, h⟩ => h2 h)).1
          rw [hphys_eq, hp1.1, hp2] at heq
          exact hv.quot_inj b hb loc' (by omega) l₂ (by omega) heq)
    (fun loc hloc hne => by
      by_cases hll : loc = loc_last
      · rw [hll]; exact ⟨loc_del, hlt_ll_b, hqv_at_del.1, hqv_at_del.2⟩
      · have hlt' : loc < loc_last := by omega
        have hp := hqv_pres b hb loc (by dsimp [fsA, fs2, fs1]; simp [hlt']) (fun ⟨_, h⟩ => hne h)
        exact ⟨loc, hlt', hp.1, hp.2⟩)
  -- Live slice preservation on bucket `b` via `SliceMapRel.relocate_full`
  have hlive_b : ∃ liveMap',
      ValidWhpSlice n_max (fsA.liveInsCount b) (fsA.slices (fsA.liveSliceIdx b)) liveMap' ∧
      SliceMapRel (fsA.fpAt c U n_max θ (fsA.bktSalt b) b)
        (fun loc => inLiveTree fsA.rebStage fsA.oldEp (fsA.rebDoneFlag b) (fsA.locState b loc) =
          true)
        (fsA.bktCount b) liveMap' := by
    obtain ⟨lm0, hvl0, hrl0⟩ := hv.live_valid b hb
    rw [hcnt] at hrl0
    obtain ⟨hm1_some, hrel_full⟩ := hrl0.relocate_full (f' := fsA.fpAt c U n_max θ (fs.bktSalt b) b)
      (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fsA.locState b loc) =
        true)
      hlt_ll_b (fun l₁ hl₁ l₂ hl₂ => hv.live_fp_inj b hb l₁ (hcnt ▸ hl₁) l₂ (hcnt ▸ hl₂))
      (fun loc hlt hne => hfp_pres _ b hb loc (by dsimp [fsA, fs2, fs1]; simp [hlt])
        (fun ⟨_, h⟩ => hne h))
      (hfp_at_del _)
      (fun loc hlt hne => by
        rw [hls_pres b hb loc (by dsimp [fsA, fs2, fs1]; simp [hlt]) (fun ⟨_, h⟩ => hne h)])
      (by rw [hls_at_del])
    have hlic_le := hv.liveInsCount_le hb
    let m1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true then
        Function.update lm0 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del) none
      else lm0
    have hv_s1 : ValidWhpSlice n_max (fs.liveInsCount b) (slices1 lIdx) m1 := by
      dsimp only [slices1, m1]
      split_ifs with hin_d
      · rw [Function.update_self, ← hfp_live_del]
        exact hvl0.delete_spec hv.hth hlic_le (fpAt_lt θ fs (fs.bktSalt b) b loc_del)
      · exact hvl0
    have hv_s2 : ValidWhpSlice n_max (fs.liveInsCount b) (sl_live' lIdx)
        (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true then
          Function.update m1 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) (some loc_del)
        else m1) := by
      by_cases hin_l :
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true
      · have hsll_eq : sl_live' lIdx =
            btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (slices1 lIdx) (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) loc_del := by
          dsimp only [sl_live']
          have hin_l1 : inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true :=
            hin_l
          rw [ite_eq_left hin_l1, Function.update_self]
          dsimp only [fs1]; rw [hsl3_l, hfp1_live]
        rw [hsll_eq, ite_eq_left hin_l]
        have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by rw [valLane_pow_eq]; omega
        have hupd := hv_s1.update_spec hv.hth hlic_le
          (fpAt_lt θ fs (fs.bktSalt b) b loc_last) hloc_val
        rwa [ite_eq_left (hm1_some hin_l)] at hupd
      · have hsll_eq : sl_live' lIdx = slices1 lIdx := by
          dsimp only [sl_live']
          have hnin_l1 : ¬(inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true) :=
            hin_l
          rw [ite_eq_right hnin_l1]
          exact hsl3_l
        rw [hsll_eq, ite_eq_right hin_l]
        exact hv_s1
    let m2 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true then
        Function.update m1 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) (some loc_del)
      else m1
    refine ⟨m2, ?_, ?_⟩
    · change ValidWhpSlice n_max (fs.liveInsCount b) (rebQuad.1 lIdx) m2
      rw [hreb_l]; exact hv_s2
    · change SliceMapRel (fsA.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fsA.locState b loc) = true)
        (Function.update fs.bktCount b loc_last b) m2
      rw [Function.update_self]
      exact hrel_full
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := fun p => by
          dsimp only [fsA, fs2, qArr', vArr', fs1]
          by_cases hp : p = p_del
          · rw [hp]; simp [hv.qv_global p_last]
          · simp [hp, hv.qv_global p]
        bktCount_le := fun b' hb' => by
          dsimp only [fsA, fs2, fs1]
          by_cases hbb : b' = b
          · rw [hbb, Function.update_self]
            have := hv.bktCount_le b hb; omega
          · rw [Function.update_of_ne hbb]; exact hv.bktCount_le b' hb'
        bktCount_ge_zero := fun b' hge => by
          dsimp only [fsA, fs2, fs1]
          rw [Function.update_of_ne (by omega)]; exact hv.bktCount_ge_zero b' hge
        locState_active := fun b' hb' loc hloc => by
          by_cases hbd : b' = b ∧ loc = loc_del
          · rcases hbd with ⟨hb_eq, hl_eq⟩
            rw [hb_eq, hl_eq, hls_at_del]
            exact hv.locState_active b hb loc_last hll_lt
          · rw [hls_pres b' hb' loc hloc hbd]
            refine hv.locState_active b' hb' loc ?_
            dsimp only [fsA, fs2, fs1] at hloc
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hloc; omega
            · rwa [Function.update_of_ne hbb] at hloc
        locState_inactive := fun b' loc hna => by
          dsimp only [fsA, fs2, fs1] at hna ⊢
          by_cases hbb : b' = b
          · rw [hbb] at hna ⊢
            rw [Function.update_self] at hna ⊢
            rw [Function.update_self]
            by_cases hll : loc = loc_last
            · rw [hll]; simp
            · have hne_d : loc ≠ loc_del := fun hd => hna ⟨hb, hd ▸ hlt_ll_b⟩
              rw [Function.update_of_ne hll, Function.update_of_ne hne_d]
              exact hv.locState_inactive b loc fun ⟨_, hlt⟩ => hna ⟨hb, by omega⟩
          · simp only [Function.update_of_ne hbb] at hna ⊢
            exact hv.locState_inactive b' loc hna
        active_item := fun b' hb' loc hloc => by
          by_cases hbd : b' = b ∧ loc = loc_del
          · rcases hbd with ⟨hb_eq, hl_eq⟩
            dsimp only
            rw [hb_eq, hl_eq, hkv_at_del, hphys_eq, hqv_at_del.1, hqv_at_del.2]
            exact hv.active_item b hb loc_last hll_lt
          · dsimp only
            rw [hkv_pres b' hb' loc hloc hbd, hphys_eq, (hqv_pres b' hb' loc hloc hbd).1,
              (hqv_pres b' hb' loc hloc hbd).2]
            refine hv.active_item b' hb' loc ?_
            dsimp only [fsA, fs2, fs1] at hloc
            by_cases hbb : b' = b
            · subst hbb; rw [Function.update_self] at hloc; omega
            · rwa [Function.update_of_ne hbb] at hloc
        quot_inj := hq_inj
        dict_map := hdict_map
        poolFreeTop_le := hpool.1
        backPtr_valid := hpool.2.1
        freeStack_lt := hpool.2.2.1
        backPtr_inj := hpool.2.2.2.1
        freeStack_inj := hpool.2.2.2.2.1
        back_free_disj := hpool.2.2.2.2.2.1
        pool_conservation := hpool.2.2.2.2.2.2
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          have mapL : ∀ l < fsA.bktCount b', ∃ l₀ < fs.bktCount b',
              fsA.locState b' l = fs.locState b' l₀ ∧
              FastState.fpAt c U n_max θ fsA (fs.bktSalt b') b' l =
                FastState.fpAt c U n_max θ fs (fs.bktSalt b') b' l₀ ∧
              (b' = b → (l = loc_del ↔ l₀ = loc_last) ∧ (l ≠ loc_del → l₀ = l)) ∧
              (b' ≠ b → l₀ = l) := by
            intro l hl
            by_cases hbd : b' = b ∧ l = loc_del
            · rcases hbd with ⟨hb_eq, hl_eq⟩
              rw [hb_eq, hl_eq]
              exact ⟨loc_last, hll_lt, hls_at_del, hfp_at_del _,
                fun _ => ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun h => absurd rfl h⟩,
                fun h => absurd rfl h⟩
            · have hl0 : l < fs.bktCount b' := by
                dsimp only [fsA, fs2, fs1] at hl
                by_cases hbb : b' = b
                · subst hbb; rw [Function.update_self] at hl; omega
                · rwa [Function.update_of_ne hbb] at hl
              refine ⟨l, hl0, hls_pres b' hb' l hl hbd, hfp_pres _ b' hb' l hl hbd,
                fun hbb => ⟨⟨fun hd => absurd ⟨hbb, hd⟩ hbd, fun hll => ?_⟩, fun _ => rfl⟩,
                fun _ => rfl⟩
              rw [hbb, hll] at hl
              dsimp only [fsA, fs2, fs1] at hl; rw [Function.update_self] at hl; omega
          obtain ⟨l₁₀, hl₁₀, hls₁, hfp₁, hb₁_iff, hnb₁⟩ := mapL l₁ hl₁
          obtain ⟨l₂₀, hl₂₀, hls₂, hfp₂, hb₂_iff, hnb₂⟩ := mapL l₂ hl₂
          rw [hls₁] at hin₁; rw [hls₂] at hin₂
          change FastState.fpAt c U n_max θ fsA (fs.bktSalt b') b' l₁ =
            FastState.fpAt c U n_max θ fsA (fs.bktSalt b') b' l₂ at hfeq
          rw [hfp₁, hfp₂] at hfeq
          have heq0 := hv.live_fp_inj b' hb' l₁₀ hl₁₀ l₂₀ hl₂₀ hin₁ hin₂ hfeq
          by_cases hbb : b' = b
          · by_cases hd1 : l₁ = loc_del <;> by_cases hd2 : l₂ = loc_del
            · exact hd1.trans hd2.symm
            · have := (hb₁_iff hbb).1.mp hd1
              have := (hb₂_iff hbb).2 hd2
              have : l₂ < loc_last := by
                rw [hbb] at hl₂; dsimp only [fsA, fs2, fs1] at hl₂
                rwa [Function.update_self] at hl₂
              omega
            · have := (hb₂_iff hbb).1.mp hd2
              have := (hb₁_iff hbb).2 hd1
              have : l₁ < loc_last := by
                rw [hbb] at hl₁; dsimp only [fsA, fs2, fs1] at hl₁
                rwa [Function.update_self] at hl₁
              omega
            · rw [← (hb₁_iff hbb).2 hd1, heq0, (hb₂_iff hbb).2 hd2]
          · rw [← hnb₁ hbb, heq0, hnb₂ hbb]
        live_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · rw [hbb]; exact hlive_b
          · obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
            refine ⟨lm, ?_, ?_⟩
            · dsimp only [fsA, fs2, FastState.liveSliceIdx, fs1]
              rw [hreb_other b' hb' hbb _ (hv.roles_valid b' hb').1]
              exact hvl
            · have hcnt_eq : fsA.bktCount b' = fs.bktCount b' := by
                dsimp only [fsA, fs2, fs1]; exact Function.update_of_ne hbb _ _
              rw [hcnt_eq]
              refine hrl.congr
                (fun loc hloc => hfp_pres _ b' hb' loc (hcnt_eq ▸ hloc) (fun ⟨h, _⟩ => hbb h))
                (fun loc hloc => ?_)
              dsimp only [fsA, fs2, fs1, FastState.oldEp]
              simp only [Function.update_of_ne hbb]
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ hst₁ hst₂ hrkeq => by
          let orig (b' : ℕ) (l : ℕ) : ℕ :=
            if b' = b ∧ l = loc_del then loc_last else l
          have horig_props : ∀ b' < numBucketsWhp n_max, ∀ l < fsA.bktCount b',
              orig b' l < fs.bktCount b' ∧
              fsA.locState b' l = fs.locState b' (orig b' l) ∧
              fsA.rKeyAt c U n_max θ b' l = fs.rKeyAt c U n_max θ b' (orig b' l) := by
            intro b' hb' l hl
            dsimp only [orig]
            split_ifs with hbd
            · rcases hbd with ⟨hb_eq, hl_eq⟩
              rw [hb_eq, hl_eq]
              exact ⟨hll_lt, hls_at_del, hrk_at_del⟩
            · refine ⟨?_, hls_pres b' hb' l hl hbd, hrk_pres b' hb' l hl hbd⟩
              dsimp only [fsA, fs2, fs1] at hl
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hl; omega
              · rwa [Function.update_of_ne hbb] at hl
          obtain ⟨ho₁, hs₁, hr₁⟩ := horig_props b₁ hb₁ l₁ hl₁
          obtain ⟨ho₂, hs₂, hr₂⟩ := horig_props b₂ hb₂ l₂ hl₂
          rw [hs₁] at hst₁; rw [hs₂] at hst₂; rw [hr₁, hr₂] at hrkeq
          obtain ⟨rfl, heq_o⟩ := hv.rKey_buf_inj b₁ hb₁ _ ho₁ b₂ hb₂ _ ho₂ hst₁ hst₂ hrkeq
          refine ⟨rfl, ?_⟩
          dsimp only [orig] at heq_o
          by_cases hbb : b₁ = b
          · rw [hbb] at hl₁ hl₂ heq_o
            dsimp only [fsA, fs2, fs1] at hl₁ hl₂
            rw [Function.update_self] at hl₁ hl₂
            split_ifs at heq_o with hd1 hd2 <;> omega
          · simp only [hbb, false_and, ↓reduceIte] at heq_o; exact heq_o
        bufCur_valid := by
          have hb1 : buf1 fs.curEp =
              if st_del = 2 + fs.curEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey_u
              else fs.buf fs.curEp := buf_del_at_ep fs.buf hv.curEp_or
          have hb2 : buf2 fs.curEp =
              if fs.locState b loc_last = 2 + fs.curEp then
                bufInsert (cTabWhp c) (bCharWhp n_max) (buf1 fs.curEp)
                  (fs.rKeyAt c U n_max θ b loc_last) b loc_del
              else buf1 fs.curEp := by
            rw [← hrk1_last]
            exact buf_ins_at_ep buf1 hv.curEp_or
          obtain ⟨hia_eq, hna_eq, hmap_cur, _⟩ :=
            buf_valid_after_delete (ep := fs.curEp) (fs' := fsA) hv.toCore hb hcnt
              (hcnt ▸ hld_lt_b) hrk_del hv.bufCur_valid rfl
              (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b))
              (fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
                hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩)
          dsimp only [st_del] at hb1
          rw [ite_eq_left hlt_ll_b, ← hb1, ← hb2] at hia_eq hna_eq hmap_cur
          exact ⟨hia_eq ▸ hv.bufCur_valid.1,
            hna_eq ▸ hia_eq ▸ hv.bufCur_valid.2.1, hmap_cur⟩
        bufOld_valid := by
          have hb1_old : buf1 fs.oldEp =
              if st_del = 2 + fs.oldEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
              else fs.buf fs.oldEp := buf_del_at_ep fs.buf (oldEp_or hv.curEp_or)
          have hb2_old : fsA.buf fs.oldEp =
              if fs.locState b loc_last = 2 + fs.oldEp then
                bufInsert (cTabWhp c) (bCharWhp n_max) (buf1 fs.oldEp)
                  (fs.rKeyAt c U n_max θ b loc_last) b loc_del
              else buf1 fs.oldEp := by
            rw [← hrk1_last]
            exact buf_ins_at_ep buf1 (oldEp_or hv.curEp_or)
          have hbo := hv.bufOld_valid
          have ho_eq : fsA.oldEp = fs.oldEp := rfl
          have hrs_eq : fsA.rebStage = fs.rebStage := rfl
          rw [ho_eq, hrs_eq]
          split_ifs at hbo ⊢ with hs3 hs4
          · obtain ⟨hia_eq, hna_eq, hmap_old, _⟩ :=
              buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
                (hcnt ▸ hld_lt_b) hrk_del hbo rfl
                (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b))
                (fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
                  hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩)
            dsimp only [st_del] at hb1_old
            rw [ite_eq_left hlt_ll_b, ← hb1_old, ← hb2_old] at hia_eq hna_eq hmap_old
            exact ⟨hia_eq ▸ hbo.1, hna_eq ▸ hia_eq ▸ hbo.2.1, hmap_old⟩
          · have hne_d : st_del ≠ 2 + fs.oldEp := hbo.1 b hb loc_del hld_lt_b
            have hne_l : fs.locState b loc_last ≠ 2 + fs.oldEp := hbo.1 b hb loc_last hll_lt
            rw [ite_eq_right hne_d] at hb1_old
            rw [ite_eq_right hne_l, hb1_old] at hb2_old
            rw [hb2_old]
            refine ⟨fun b' hb' loc hloc => ?_, hbo.2.1, hbo.2.2⟩
            by_cases hbd : b' = b ∧ loc = loc_del
            · rcases hbd with ⟨hb_eq, hl_eq⟩; rw [hb_eq, hl_eq, hls_at_del]; exact hne_l
            · rw [hls_pres b' hb' loc hloc hbd]
              refine hbo.1 b' hb' loc ?_
              dsimp only [fsA, fs2, fs1] at hloc
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hloc; omega
              · rwa [Function.update_of_ne hbb] at hloc
          · have hne_d : st_del ≠ 2 + fs.oldEp := hbo.1 b hb loc_del hld_lt_b
            have hne_l : fs.locState b loc_last ≠ 2 + fs.oldEp := hbo.1 b hb loc_last hll_lt
            rw [ite_eq_right hne_d] at hb1_old
            rw [ite_eq_right hne_l, hb1_old] at hb2_old
            rw [hb2_old]
            refine ⟨fun b' hb' loc hloc => ?_, hbo.2.1, hbo.2.2.1, hbo.2.2.2⟩
            by_cases hbd : b' = b ∧ loc = loc_del
            · rcases hbd with ⟨hb_eq, hl_eq⟩; rw [hb_eq, hl_eq, hls_at_del]; exact hne_l
            · rw [hls_pres b' hb' loc hloc hbd]
              refine hbo.1 b' hb' loc ?_
              dsimp only [fsA, fs2, fs1] at hloc
              by_cases hbb : b' = b
              · subst hbb; rw [Function.update_self] at hloc; omega
              · rwa [Function.update_of_ne hbb] at hloc }
  · -- `OvermarsBucketInv` on `b' ≠ b`
    intro b' hb' hbb
    have hcnt_b' : fsA.bktCount b' = fs.bktCount b' := by
      dsimp only [fsA, fs2, fs1]; exact Function.update_of_ne hbb _ _
    refine OvermarsBucketInv.of_eq_lt (hv.overmars_valid b' hb') rfl
      (fun loc hloc => hfp_pres _ b' hb' loc (hcnt_b' ▸ hloc) (fun ⟨h, _⟩ => hbb h))
      rfl rfl rfl
      (fun loc hloc => hls_pres b' hb' loc (hcnt_b' ▸ hloc) (fun ⟨h, _⟩ => hbb h))
      (by omega) rfl rfl rfl ?_ ?_
    · dsimp only [fsA, fs2, omIns', omPair]
      by_cases h1 : fs1.overmarsActive b = 1 ∧
          inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true
      · rw [ite_eq_left h1]
        by_cases h2 : loc_last < fs1.overmarsCursor b
        · rw [ite_eq_left h2]
        · rw [ite_eq_right h2]
          by_cases h3 : loc_del < fs1.overmarsCursor b
          · rw [ite_eq_left h3]; exact Function.update_of_ne hbb _ _
          · rw [ite_eq_right h3]
      · rw [ite_eq_right h1]
    · dsimp only [fsA, fs2, FastState.overmarsSliceIdx, fs1]
      exact hreb_other b' hb' hbb _ (hv.roles_valid b' hb').2.1
  · -- `PreOvermarsBucketInv` on `b`
    have hcntA_b : fsA.bktCount b = loc_last := by
      dsimp only [fsA]; exact Function.update_self _ _ _
    rcases hv.overmars_valid b hb with
      ⟨ha0, hlic⟩ | ⟨ha1, h16, hcur_lt, hlin, hins, omM, hv_om, hr_om⟩
    · exact Or.inl ⟨ha0, hlic.le⟩
    · dsimp only [PreOvermarsBucketInv]
      right
      have hcur_le : fs.overmarsCursor b ≤ loc_last := by omega
      have hnll_cur : ¬(loc_last < fs.overmarsCursor b) := by omega
      have hoi_ub : fs.overmarsInsCount b ≤ 8 * (scaleWhp n_max) ^ 12 := by omega
      have hoa_eq : fsA.overmarsActive b = fs.overmarsActive b := rfl
      have hlic_eq : fsA.liveInsCount b = fs.liveInsCount b := rfl
      have hreb_eq : fsA.rebStage = fs.rebStage := rfl
      have hold_eq : fsA.oldEp = fs.oldEp := rfl
      have hdone_eq : fsA.rebDoneFlag b = fs.rebDoneFlag b := rfl
      have hsalt_eq : fsA.bktSalt b = fs.bktSalt b := rfl
      have hoc_eq : fsA.overmarsCursor b = fs.overmarsCursor b := rfl
      rw [hoa_eq, hoc_eq, hlic_eq, hcntA_b, Nat.min_eq_right hcur_le,
        hsalt_eq, hreb_eq, hold_eq, hdone_eq]
      by_cases hld_cur : loc_del < fs.overmarsCursor b
      · let m1 :=
          if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true then
            Function.update omM (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del) none
          else omM
        have hv_om1 : ValidWhpSlice n_max (fs.overmarsInsCount b) (slices2 omIdx) m1 := by
          dsimp only [slices2, m1, st_del]
          by_cases hin_d :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left ⟨ha1, hld_cur, hin_d⟩, ite_eq_left hin_d, Function.update_self,
              hsl1_om, ← hfp_live_del]
            exact hv_om.delete_spec hv.hth hoi_ub (fpAt_lt θ fs (fs.bktSalt b) b loc_del)
          · rw [ite_eq_right (fun ⟨_, _, h⟩ => hin_d h), ite_eq_right hin_d, hsl1_om]
            exact hv_om
        have hrel_pre := hr_om.relocate_prefix (f' := fsA.fpAt c U n_max θ (fs.bktSalt b) b)
          (P' := fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
            (fsA.locState b loc) = true)
          (loc_last := loc_last)
          hld_cur
          (fun l₁ hl₁ l₂ hl₂ => hv.live_fp_inj b hb l₁ (hl₁.trans hcur_lt) l₂ (hl₂.trans hcur_lt))
          (fun hpl l hl hne hpl_l heq =>
            Nat.ne_of_lt (hl.trans_le hcur_le)
              (hv.live_fp_inj b hb l (hl.trans hcur_lt) loc_last hll_lt hpl_l hpl heq))
          (fun loc hlt hne => hfp_pres _ b hb loc
            (by rw [hcntA_b]; exact hlt.trans_le hcur_le) (fun ⟨_, h⟩ => hne h))
          (hfp_at_del _)
          (fun loc hlt hne => by
            rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le)
              (fun ⟨_, h⟩ => hne h)])
          (by rw [hls_at_del])
        dsimp only at hrel_pre
        by_cases hin_l :
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_last) = true
        · have hcond_om : fs1.overmarsActive b = 1 ∧
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true :=
            ⟨ha1, hin_l⟩
          have homPair_eq : omPair =
              (Function.update sl_live' omIdx
                (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                  (sl_live' omIdx) fp_live_last loc_del),
               Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1)) := by
            dsimp only [omPair]
            rw [ite_eq_left hcond_om, ite_eq_right hnll_cur, ite_eq_left hld_cur]
          have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by rw [valLane_pow_eq]; omega
          have hins_om := hv_om1.insert_spec hv.hth hoi_ub
            (fpAt_lt θ fs (fs.bktSalt b) b loc_last) hloc_val
          let m_om2 :=
            Function.update m1 (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last) (some loc_del)
          refine ⟨ha1, h16, hcur_le, by omega, ?_, m_om2, ?_, ?_⟩
          · dsimp only [fsA, fs2, omIns']; rw [homPair_eq]; dsimp only
            rw [Function.update_self]; omega
          · dsimp only [fsA, fs2, omIns', sl_om', FastState.overmarsSliceIdx, fs1]
            change ValidWhpSlice n_max (omPair.2 b) (rebQuad.1 omIdx) m_om2
            rw [hreb_om]
            change ValidWhpSlice n_max (omPair.2 b) (omPair.1 omIdx) m_om2
            rw [homPair_eq]; dsimp only
            rw [Function.update_self, Function.update_self, hsll_om, hfp1_live]
            exact hins_om.2
          · rwa [ite_eq_left hin_l] at hrel_pre
        · have hncond_om : ¬(fs1.overmarsActive b = 1 ∧
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true) :=
            fun ⟨_, h⟩ => hin_l h
          have homPair_eq : omPair = (sl_live', fs.overmarsInsCount) := by
            dsimp only [omPair]; rw [ite_eq_right hncond_om]
          refine ⟨ha1, h16, hcur_le, by omega, ?_, m1, ?_, ?_⟩
          · dsimp only [fsA, fs2, omIns']; rw [homPair_eq]; dsimp only; omega
          · dsimp only [fsA, fs2, omIns', sl_om', FastState.overmarsSliceIdx, fs1]
            change ValidWhpSlice n_max (omPair.2 b) (rebQuad.1 omIdx) m1
            rw [hreb_om]
            change ValidWhpSlice n_max (omPair.2 b) (omPair.1 omIdx) m1
            rw [homPair_eq]; dsimp only; rw [hsll_om]
            exact hv_om1
          · rwa [ite_eq_right hin_l] at hrel_pre
      · have homPair_eq : omPair = (sl_live', fs.overmarsInsCount) := by
          dsimp only [omPair]
          by_cases h1 : fs1.overmarsActive b = 1 ∧
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) st_last = true
          · rw [ite_eq_left h1, ite_eq_right hnll_cur, ite_eq_right hld_cur]
          · rw [ite_eq_right h1]
        have hsl2_om : slices2 omIdx = fs.slices omIdx := by
          dsimp only [slices2]
          rw [ite_eq_right (fun ⟨_, h, _⟩ => hld_cur h), hsl1_om]
        refine ⟨ha1, h16, hcur_le, by omega, ?_, omM, ?_, ?_⟩
        · dsimp only [fsA, fs2, omIns']; rw [homPair_eq]; dsimp only; omega
        · dsimp only [fsA, fs2, omIns', sl_om', FastState.overmarsSliceIdx, fs1]
          change ValidWhpSlice n_max (omPair.2 b) (rebQuad.1 omIdx) omM
          rw [hreb_om]
          change ValidWhpSlice n_max (omPair.2 b) (omPair.1 omIdx) omM
          rw [homPair_eq]; dsimp only; rw [hsll_om, hsl2_om]
          exact hv_om
        · exact hr_om.congr
            (fun loc hlt => hfp_pres _ b hb loc
              (by rw [hcntA_b]; exact hlt.trans_le hcur_le)
              (fun ⟨_, h⟩ => hld_cur (h ▸ hlt)))
            (fun loc hlt => by
              rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le)
                (fun ⟨_, h⟩ => hld_cur (h ▸ hlt))])
  · -- `ValidEpochStagePreTick` on `fsA`
    have hcntA_b : fsA.bktCount b = loc_last := by
      dsimp only [fsA]; exact Function.update_self _ _ _
    have hstg := hv.stage_valid.toPreTick
    have hb1_old : buf1 fs.oldEp =
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp := buf_del_at_ep fs.buf (oldEp_or hv.curEp_or)
    have hb2_old : fsA.buf fs.oldEp =
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) (buf1 fs.oldEp)
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else buf1 fs.oldEp := by
      rw [← hrk1_last]
      exact buf_ins_at_ep buf1 (oldEp_or hv.curEp_or)
    have hreb_st : fsA.rebStage = fs.rebStage := rfl
    have hold_ep : fsA.oldEp = fs.oldEp := rfl
    dsimp only [ValidEpochStagePreTick] at hstg ⊢
    rw [hreb_st, hold_ep]
    split_ifs at hstg ⊢ with hs0 hs1 hs2 hs3
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, _, hsome_old⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt_b) hrk_del hbo_v rfl
          (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b))
          (fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
            hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩)
      rw [ite_eq_left hlt_ll_b, ← hb1_old, ← hb2_old] at hia_eq hsome_old
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        ∀ id < fs.stageCursor, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0
      rw [hia_eq]
      refine ⟨hstg.1, fun id hid b' loc' hchk => ?_⟩
      obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
      exact hstg.2 id hid b' loc₀ hchk0
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, _, hsome_old⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt_b) hrk_del hbo_v rfl
          (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b))
          (fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
            hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩)
      rw [ite_eq_left hlt_ll_b, ← hb1_old, ← hb2_old] at hia_eq hsome_old
      rcases hstg with ⟨hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6⟩
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        fs.dirtyCount ≤ fs.stageCursor ∧
        (∀ j < fs.dirtyCount,
          fs.dirtyBuckets j < numBucketsWhp n_max ∧
          fs.rebQueued (fs.dirtyBuckets j) = 1 ∧
          fs.rebDoneFlag (fs.dirtyBuckets j) = 0) ∧
        (∀ j₁ < fs.dirtyCount, ∀ j₂ < fs.dirtyCount,
          fs.dirtyBuckets j₁ = fs.dirtyBuckets j₂ → j₁ = j₂) ∧
        (∀ id < (fsA.buf fs.oldEp).itemAlloc, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            (fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0) ∨
            ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b') ∧
        (∀ id < fs.stageCursor, ∀ b' loc',
          bufCheckSlot (fsA.buf fs.oldEp) id = some (b', loc') →
            ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b')
      rw [hia_eq]
      refine ⟨hs1_1, hs1_2, hs1_3, hs1_4, fun id hid b' loc' hchk => ?_,
        fun id hid b' loc' hchk => ?_⟩
      · obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
        exact hs1_5 id hid b' loc₀ hchk0
      · obtain ⟨loc₀, hchk0⟩ := hsome_old id b' loc' hchk
        exact hs1_6 id hid b' loc₀ hchk0
    · -- Stage 2!
      have hstg_full := hv.stage_valid
      dsimp only [ValidEpochStage] at hstg_full
      simp only [hs2, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hstg_full
      rcases hstg_full with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
      refine ⟨hd1, hd2, hd3, hd4, hd5, fun b' hb' loc hloc hst_old => ?_, ?_⟩
      · by_cases hbd : b' = b ∧ loc = loc_del
        · rcases hbd with ⟨hb_eq, hl_eq⟩
          rw [hb_eq, hl_eq, hls_at_del] at hst_old
          rw [hb_eq]
          exact hd6 b hb loc_last hll_lt hst_old
        · rw [hls_pres b' hb' loc hloc hbd] at hst_old
          have hloc0 : loc < fs.bktCount b' := by
            by_cases hbb : b' = b
            · rw [hbb, hcntA_b] at hloc; rw [hbb]; omega
            · have hc_eq : fsA.bktCount b' = fs.bktCount b' := by
                dsimp only [fsA, fs2, fs1]; exact Function.update_of_ne hbb _ _
              rwa [hc_eq] at hloc
          exact hd6 b' hb' loc hloc0 hst_old
      · set bc := fs.dirtyBuckets fs.dirtyIdx
        have hbc : bc < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
        change rebQuad.2.1 < sMaxWhp c n_max →
          ((rebQuad.2.2.1 = 0 ∧ rebQuad.2.2.2 = 0) ∨
           (16 ≤ rebQuad.2.2.1 ∧ rebQuad.2.2.1 ≤ fsA.bktCount bc ∧
            16 * rebQuad.2.2.2 ≤ 17 * rebQuad.2.2.1)) ∧
          (∀ l₁ < min (fsA.bktCount bc) rebQuad.2.2.1,
           ∀ l₂ < min (fsA.bktCount bc) rebQuad.2.2.1,
            (fsA.locState bc l₁ = 1 ∨ fsA.locState bc l₁ = 2 + fs.oldEp) →
            (fsA.locState bc l₂ = 1 ∨ fsA.locState bc l₂ = 2 + fs.oldEp) →
            fsA.fpAt c U n_max θ rebQuad.2.1 bc l₁ =
              fsA.fpAt c U n_max θ rebQuad.2.1 bc l₂ →
            l₁ = l₂) ∧
          ∃ rebMap,
            ValidWhpSlice n_max rebQuad.2.2.2 (rebQuad.1 (fs.rebSliceIdx bc)) rebMap ∧
            SliceMapRel (fsA.fpAt c U n_max θ rebQuad.2.1 bc)
              (fun loc => fsA.locState bc loc = 1 ∨ fsA.locState bc loc = 2 + fs.oldEp)
              (min (fsA.bktCount bc) rebQuad.2.2.1) rebMap
        intro hcs_new
        by_cases hbb : bc = b
        · -- Active rebuild bucket `bc = b`!
          have hcs0 : fs.rebCandSalt < sMaxWhp c n_max := by
            by_contra hge
            have hrbf : rebActiveB = false :=
              decide_eq_false (fun ⟨_, _, _, h, _⟩ => hge h)
            have hcs_eq : rebQuad.2.1 = fs.rebCandSalt := by
              dsimp only [rebQuad, fs1]; rw [hrbf]; rfl
            omega
          have hrbt : rebActiveB = true :=
            decide_eq_true ⟨hs2, hd2, hbb, hcs0, hv.rebCollision_zero⟩
          obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs0
          rw [hbb] at hcur_r hinj_r hvr0 hrr0 ⊢
          change _ ∧ _ ∧ ∃ rebMap,
            ValidWhpSlice n_max rebQuad.2.2.2 (rebQuad.1 rIdx) rebMap ∧ _
          rw [hcntA_b]
          have hcur_le_ll : fs.rebScanCursor ≤ loc_last := by
            rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
          have hnll_r : ¬(loc_last < fs.rebScanCursor) := by omega
          have hmin_old : min (fs.bktCount b) fs.rebScanCursor = fs.rebScanCursor :=
            Nat.min_eq_right (by omega)
          rw [hmin_old] at hinj_r hrr0
          have hri_ub : fs.rebInsCount ≤ 8 * (scaleWhp n_max) ^ 12 := by
            rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins⟩ <;> omega
          by_cases hld_r : loc_del < fs.rebScanCursor
          · have hcur_pos :
                16 ≤ fs.rebScanCursor ∧ 16 * fs.rebInsCount + 16 ≤ 17 * fs.rebScanCursor := by
              rcases hcur_r with ⟨hc0, _⟩ | ⟨h16, _, hins⟩
              · omega
              · exact ⟨h16, hins⟩
            let P_r (st : ℕ → ℕ) (loc : ℕ) : Prop :=
              st loc = 1 ∨ st loc = 2 + fs.oldEp
            let mr1 :=
              if P_r (fs.locState b) loc_del then
                Function.update rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_del) none
              else rm0
            have hv_r1 : ValidWhpSlice n_max fs.rebInsCount (slices3 rIdx) mr1 := by
              dsimp only [slices3, mr1, P_r, st_del]
              rw [hrbt, Bool.true_and]
              by_cases hpd : fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp
              · have hd_true : decide (loc_del < fs.rebScanCursor ∧
                    (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp)) = true :=
                  decide_eq_true ⟨hld_r, hpd⟩
                rw [hd_true, ite_eq_left rfl, ite_eq_left hpd, Function.update_self, hsl2_r,
                  ← hfp_cand_del]
                exact hvr0.delete_spec hv.hth hri_ub (fpAt_lt θ fs fs.rebCandSalt b loc_del)
              · have hd_fls : decide (loc_del < fs.rebScanCursor ∧
                    (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp)) = false :=
                  decide_eq_false (fun ⟨_, h⟩ => hpd h)
                rw [hd_fls]
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [ite_eq_right hpd, hsl2_r]
                exact hvr0
            by_cases hpl_r : fs.locState b loc_last = 1 ∨ fs.locState b loc_last = 2 + fs.oldEp
            · have hcond_q :
                  (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true := by
                rw [hrbt, Bool.true_and]
                exact decide_eq_true hpl_r
              have hrebQ_branch : rebQuad =
                  match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                      (sl_om' rIdx) fp_cand_last with
                  | some _ =>
                    (Function.update sl_om' rIdx (resetBTreeSlice (sl_om' rIdx)),
                     (fs.rebCandSalt + 1, (0, 0)))
                  | none =>
                    (Function.update sl_om' rIdx
                      (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                        (sl_om' rIdx) fp_cand_last loc_del),
                     (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount + 1))) := by
                dsimp only [rebQuad, fs1]
                rw [hcond_q, ite_eq_left rfl, ite_eq_right hnll_r, ite_eq_left hld_r]
              rw [hrebQ_branch]
              have hlk_eq :
                  btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                    (sl_om' rIdx) fp_cand_last = mr1 fp_cand_last := by
                rw [hslom_r, hfp1_cand]
                exact hv_r1.lookup_eq hv.hth hri_ub (fpAt_lt θ fs fs.rebCandSalt b loc_last)
              cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                  (sl_om' rIdx) fp_cand_last with
              | some v_coll =>
                dsimp only
                rw [Nat.min_zero, Function.update_self]
                exact ⟨Or.inl ⟨rfl, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
                  fun _ => none, validSlice_zero _ _ _ 0 _,
                  SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩
              | none =>
                have hmr1_none : mr1 (fs.fpAt c U n_max θ fs.rebCandSalt b loc_last) = none := by
                  rw [← hfp1_cand, ← hlk_eq, hlk]
                have hno_coll_r : ∀ l < fs.rebScanCursor, l ≠ loc_del →
                    P_r (fs.locState b) l →
                    fs.fpAt c U n_max θ fs.rebCandSalt b l ≠
                      fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := by
                  intro l hl hne hpl_l heq
                  have h0_some : rm0 (fs.fpAt c U n_max θ fs.rebCandSalt b l) = some l :=
                    (hrr0.2 _ l).mpr ⟨hl, hpl_l, rfl⟩
                  have hmr1_some : mr1 (fs.fpAt c U n_max θ fs.rebCandSalt b l) = some l := by
                    dsimp only [mr1]
                    split_ifs with hpd
                    · have hne_fp : fs.fpAt c U n_max θ fs.rebCandSalt b l ≠
                          fs.fpAt c U n_max θ fs.rebCandSalt b loc_del := fun hfe =>
                        hne (hinj_r l hl loc_del hld_r hpl_l hpd hfe)
                      rwa [Function.update_of_ne hne_fp]
                    · exact h0_some
                  rw [heq, hmr1_none] at hmr1_some
                  cases hmr1_some
                dsimp only
                rw [Nat.min_eq_right hcur_le_ll, Function.update_self, hslom_r, hfp1_cand]
                have hloc_val : loc_del < 2 ^ valLaneBitsWhp n_max := by rw [valLane_pow_eq]; omega
                have hins_r := hv_r1.insert_spec hv.hth hri_ub
                  (fpAt_lt θ fs fs.rebCandSalt b loc_last) hloc_val
                have hrel_r := hrr0.relocate_prefix (f' := fsA.fpAt c U n_max θ fs.rebCandSalt b)
                  (P' := P_r (fsA.locState b)) (loc_last := loc_last)
                  hld_r hinj_r (fun _ => hno_coll_r)
                  (fun loc hlt hne => hfp_pres _ b hb loc
                    (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll) (fun ⟨_, h⟩ => hne h))
                  (hfp_at_del _)
                  (fun loc hlt hne => by
                    dsimp only [P_r]
                    rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll)
                      (fun ⟨_, h⟩ => hne h)])
                  (by dsimp only [P_r]; rw [hls_at_del])
                dsimp only at hrel_r
                rw [ite_eq_left hpl_r] at hrel_r
                refine ⟨Or.inr ⟨hcur_pos.1, hcur_le_ll, by omega⟩, ?_, _, hins_r.2, hrel_r⟩
                intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
                by_cases hd1 : l₁ = loc_del <;> by_cases hd2 : l₂ = loc_del
                · exact hd1.trans hd2.symm
                · rw [hd1, hfp_at_del, hfp_pres _ b hb l₂
                    (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd2 h)] at hfeq
                  rw [hls_pres b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd2 h)] at hp₂
                  exact absurd hfeq.symm (hno_coll_r l₂ hl₂ hd2 hp₂)
                · rw [hd2, hfp_pres _ b hb l₁
                    (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd1 h), hfp_at_del] at hfeq
                  rw [hls_pres b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd1 h)] at hp₁
                  exact absurd hfeq (hno_coll_r l₁ hl₁ hd1 hp₁)
                · rw [hfp_pres _ b hb l₁
                    (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd1 h),
                    hfp_pres _ b hb l₂
                    (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd2 h)] at hfeq
                  rw [hls_pres b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd1 h)] at hp₁
                  rw [hls_pres b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hd2 h)] at hp₂
                  exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            · have hcond_q :
                  (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = false := by
                rw [Bool.and_eq_false_iff]
                exact Or.inr (decide_eq_false hpl_r)
              have hrebQ_eq :
                  rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
                dsimp only [rebQuad, fs1]; rw [hcond_q]; rfl
              rw [hrebQ_eq]
              dsimp only
              rw [Nat.min_eq_right hcur_le_ll, hslom_r]
              have hrel_r := hrr0.relocate_prefix (f' := fsA.fpAt c U n_max θ fs.rebCandSalt b)
                (P' := P_r (fsA.locState b)) (loc_last := loc_last)
                hld_r hinj_r (fun h => absurd h hpl_r)
                (fun loc hlt hne => hfp_pres _ b hb loc
                  (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll) (fun ⟨_, h⟩ => hne h))
                (hfp_at_del _)
                (fun loc hlt hne => by
                  dsimp only [P_r]
                  rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll)
                    (fun ⟨_, h⟩ => hne h)])
                (by dsimp only [P_r]; rw [hls_at_del])
              dsimp only at hrel_r
              rw [ite_eq_right hpl_r] at hrel_r
              refine ⟨Or.inr ⟨hcur_pos.1, hcur_le_ll, by omega⟩, ?_, mr1, hv_r1, hrel_r⟩
              intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
              have hne1 : l₁ ≠ loc_del := fun h => by
                rw [h, hls_at_del] at hp₁; exact hpl_r hp₁
              have hne2 : l₂ ≠ loc_del := fun h => by
                rw [h, hls_at_del] at hp₂; exact hpl_r hp₂
              rw [hls_pres b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                (fun ⟨_, h⟩ => hne1 h)] at hp₁
              rw [hls_pres b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                (fun ⟨_, h⟩ => hne2 h)] at hp₂
              rw [hfp_pres _ b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                  (fun ⟨_, h⟩ => hne1 h),
                hfp_pres _ b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                  (fun ⟨_, h⟩ => hne2 h)] at hfeq
              exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          · -- `fs.rebScanCursor ≤ loc_del`: neither `loc_del` nor `loc_last` is `< rebScanCursor`!
            have hrebQ_eq :
                rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
              dsimp only [rebQuad]
              by_cases h1 : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1.oldEp)) = true
              · rw [ite_eq_left h1, ite_eq_right hnll_r, ite_eq_right hld_r]
              · rw [ite_eq_right h1]
            have hsl3_r : slices3 rIdx = fs.slices rIdx := by
              dsimp only [slices3]
              have hd_fls : (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
                  (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = false := by
                rw [Bool.and_eq_false_iff]
                exact Or.inr (decide_eq_false (fun ⟨h, _⟩ => hld_r h))
              rw [hd_fls]; exact hsl2_r
            rw [hrebQ_eq]
            dsimp only
            rw [Nat.min_eq_right hcur_le_ll, hslom_r, hsl3_r]
            refine ⟨?_, ?_, rm0, hvr0, ?_⟩
            · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, _, hins⟩
              · exact Or.inl ⟨hc0, hi0⟩
              · exact Or.inr ⟨h16, hcur_le_ll, by omega⟩
            · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
              have hne1 : l₁ ≠ loc_del := fun h => hld_r (h ▸ hl₁)
              have hne2 : l₂ ≠ loc_del := fun h => hld_r (h ▸ hl₂)
              rw [hls_pres b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                (fun ⟨_, h⟩ => hne1 h)] at hp₁
              rw [hls_pres b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                (fun ⟨_, h⟩ => hne2 h)] at hp₂
              rw [hfp_pres _ b hb l₁ (by rw [hcntA_b]; exact hl₁.trans_le hcur_le_ll)
                  (fun ⟨_, h⟩ => hne1 h),
                hfp_pres _ b hb l₂ (by rw [hcntA_b]; exact hl₂.trans_le hcur_le_ll)
                  (fun ⟨_, h⟩ => hne2 h)] at hfeq
              exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            · exact hrr0.congr
                (fun loc hlt => hfp_pres _ b hb loc
                  (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll)
                  (fun ⟨_, heq⟩ => hld_r (heq ▸ hlt)))
                (fun loc hlt => by
                  rw [hls_pres b hb loc (by rw [hcntA_b]; exact hlt.trans_le hcur_le_ll)
                    (fun ⟨_, heq⟩ => hld_r (heq ▸ hlt))])
        · -- `bc ≠ b`: `rebActiveB = false`!
          have hrbf : rebActiveB = false :=
            decide_eq_false (fun ⟨_, _, h, _, _⟩ => hbb h)
          have hrebQ_eq :
              rebQuad = (sl_om', (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount))) := by
            dsimp only [rebQuad, fs1]; rw [hrbf]; rfl
          rw [hrebQ_eq] at hcs_new ⊢
          dsimp only at hcs_new ⊢
          obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs_new
          have hcntA_bc : fsA.bktCount bc = fs.bktCount bc := by
            dsimp only [fsA, fs2, fs1]; exact Function.update_of_ne hbb _ _
          rw [hcntA_bc]
          have hsl_bc : sl_om' (fs.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
            have hr_lt := (rebRole_props (hv.roles_valid bc hbc).1
              (hv.roles_valid bc hbc).2.1 (hv.roles_valid bc hbc).2.2).1
            have hsl_eq := hreb_other bc hbc hbb (fs.rebRole bc) hr_lt
            rw [hrebQ_eq] at hsl_eq
            exact hsl_eq
          rw [hsl_bc]
          refine ⟨?_, ?_, rm0, hvr0, ?_⟩
          · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, hc_lt, hins⟩
            · exact Or.inl ⟨hc0, hi0⟩
            · exact Or.inr ⟨h16, hc_lt.le, by omega⟩
          · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
            have hl₁_b : l₁ < fsA.bktCount bc :=
              hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hl₁
            have hl₂_b : l₂ < fsA.bktCount bc :=
              hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hl₂
            rw [hls_pres bc hbc l₁ hl₁_b (fun ⟨h, _⟩ => hbb h)] at hp₁
            rw [hls_pres bc hbc l₂ hl₂_b (fun ⟨h, _⟩ => hbb h)] at hp₂
            rw [hfp_pres _ bc hbc l₁ hl₁_b (fun ⟨h, _⟩ => hbb h),
              hfp_pres _ bc hbc l₂ hl₂_b (fun ⟨h, _⟩ => hbb h)] at hfeq
            exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          · exact hrr0.congr
              (fun loc hlt => hfp_pres _ bc hbc loc
                (hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hlt) (fun ⟨h, _⟩ => hbb h))
              (fun loc hlt => by
                rw [hls_pres bc hbc loc
                  (hcntA_bc ▸ (Nat.min_le_left _ _).trans_lt' hlt) (fun ⟨h, _⟩ => hbb h)])
    · have hbo : fs.rebStage ≤ 3 := by omega
      have hbo_v := hv.bufOld_valid
      simp only [hbo, ↓reduceIte] at hbo_v
      obtain ⟨hia_eq, _, _, hnone_old, _⟩ :=
        buf_valid_after_delete (ep := fs.oldEp) (fs' := fsA) hv.toCore hb hcnt
          (hcnt ▸ hld_lt_b) hrk_del hbo_v rfl
          (fun heq => absurd heq (Nat.ne_of_lt hlt_ll_b))
          (fun _ => ⟨fun b' hb' loc hloc hne => ⟨hls_pres b' hb' loc hloc hne,
            hrk_pres b' hb' loc hloc hne⟩, hls_at_del, hrk_at_del⟩)
      rw [ite_eq_left hlt_ll_b, ← hb1_old, ← hb2_old] at hia_eq hnone_old
      change fs.stageCursor ≤ (fsA.buf fs.oldEp).itemAlloc ∧
        ∀ id < fs.stageCursor, bufCheckSlot (fsA.buf fs.oldEp) id = none
      rw [hia_eq]
      exact ⟨hstg.1, fun id hid => hnone_old id (hstg.2 id hid)⟩

/-- `fastDelete` refines `Dynamic.step dict (.delete u)` and yields `CoreFastInv`,
`OvermarsBucketInv` on all buckets, and `ValidEpochStagePreTick` (ready for `epochTick`). -/
theorem ValidFastState.fastDelete_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    let fs' := fastDelete c U n_max θ fs u
    CoreFastInv c U V n_max θ fs' (Dynamic.step dict (.delete u)).1 ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    ValidEpochStagePreTick c U n_max θ fs' ∧
    fs'.epochClock = fs.epochClock := by
  have hfl := hv.fastFindLoc_spec u
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  dsimp only [fastDelete, Dynamic.step]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl
    have hdict_eq : Function.update dict u none = dict := by
      funext x; by_cases hx : x = u <;> simp [hx, hfl]
    rw [hdict_eq]
    dsimp only
    obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ :=
      overmarsStep_spec hv.toCore hb (fun b' hb' _ => hv.overmars_valid b' hb')
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb))
    exact ⟨hc', hom', hpre' hv.stage_valid.toPreTick, hclk'⟩
  | some loc_del =>
    rw [hfind] at hfl
    dsimp only
    by_cases hlt : loc_del < fs.bktCount b - 1
    · rw [ite_eq_left hlt]
      obtain ⟨hcA, homA_other, homA_b, hpreA⟩ :=
        fastDelete_afterDel_reloc_spec hv u hfl.1 hfl.2 hlt
      obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ :=
        overmarsStep_spec hcA hb homA_other homA_b
      exact ⟨hc', hom', hpre' hpreA, hclk'⟩
    · rw [ite_eq_right hlt]
      obtain ⟨hcA, homA_other, homA_b, hpreA⟩ :=
        fastDelete_afterDel_last_spec hv u hfl.1 hfl.2 hlt
      obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ :=
        overmarsStep_spec hcA hb homA_other homA_b
      exact ⟨hc', hom', hpre' hpreA, hclk'⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
