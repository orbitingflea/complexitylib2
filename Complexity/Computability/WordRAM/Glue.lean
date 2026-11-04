/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Glue.Basic

/-!
# Compositional certificates and `fun_prop` automation for register-word glue

This module re-exports `Complexity.Computability.WordRAM.Glue.Basic` and provides the staged
comparison-operand selection combinators (`GlueComputes.stage_pair`, `GlueComputes.ite_eq_staged`,
`GlueComputes.ite_lt_staged`) together with the `@[fun_prop]` closure rules on `GlueComputable`.

## Main results

* `GlueComputes.stage_pair`, `GlueComputes.ite_eq_staged`, `GlueComputes.ite_lt_staged`:
  staged-operand selection with explicit guard and branch costs.
* `GlueComputable.proj`, `GlueComputable.const`, `GlueComputable.comp`, `GlueComputable.comp_many`:
  register projections, constants, and scalar/vector composition.
* `GlueComputable.ite_eq`, `GlueComputable.ite_lt`: lazy branch selection on equality and `<`
  between input registers, which stages nothing and so imposes no envelope obligation on them.
* `GlueComputable.ite_eq_staged`, `GlueComputable.ite_lt_staged`: lazy branch selection on
  equality and `<` between arbitrary certified computed operands.
* `GlueComputable.add`, `GlueComputable.sub`, `GlueComputable.mul`, `GlueComputable.div`,
  `GlueComputable.mod`, `GlueComputable.and`, `GlueComputable.or`, `GlueComputable.xor`,
  `GlueComputable.shiftLeft`, `GlueComputable.shiftRight` (and `*_standard`): exact- and
  standard-basis binary closure rules.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {k : ℕ}

namespace GlueComputes

variable {P : (Fin k → ℕ) → Prop} {bound : (Fin k → ℕ) → ℕ}

private def stageRest {a b c : ℕ} (j : Fin (c + 1)) : Fin (a + b + c + 3) :=
  ⟨j.val, by omega⟩

private def stageLeft {a b c : ℕ} (j : Fin (a + 1)) : Fin (a + b + c + 3) :=
  ⟨j.val + c + 1, by omega⟩

private def stageRight {a b c : ℕ} (j : Fin (b + 1)) : Fin (a + b + c + 3) :=
  ⟨j.val + c + a + 2, by omega⟩

private theorem stageRest_injective {a b c : ℕ} : Function.Injective (@stageRest a b c) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [stageRest] at this
  omega

private theorem stageLeft_injective {a b c : ℕ} : Function.Injective (@stageLeft a b c) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [stageLeft] at this
  omega

private theorem stageRight_injective {a b c : ℕ} : Function.Injective (@stageRight a b c) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [stageRight] at this
  omega

private theorem stageLeft_ne_stageRight {a b c : ℕ} (i : Fin (a + 1)) (j : Fin (b + 1)) :
    stageLeft (c := c) i ≠ stageRight (c := c) j := by
  intro h
  have := congrArg Fin.val h
  simp only [stageLeft, stageRight] at this
  omega

private theorem stageLeft_ne_stageRest {a b c : ℕ} (i : Fin (a + 1)) (j : Fin (c + 1)) :
    stageLeft (b := b) i ≠ stageRest (a := a) (b := b) j := by
  intro h
  have := congrArg Fin.val h
  simp only [stageLeft, stageRest] at this
  omega

private theorem stageRight_ne_stageRest {a b c : ℕ} (i : Fin (b + 1)) (j : Fin (c + 1)) :
    stageRight (a := a) i ≠ stageRest (a := a) (b := b) j := by
  intro h
  have := congrArg Fin.val h
  simp only [stageRight, stageRest] at this
  omega

/-- Stage two computed words into fresh scratch slots and run a `(k + 2)`-input computation over
the original `k` input registers together with the two staged words, without copying the original
input registers. -/
theorem stage_pair {lhs rhs : (Fin k → ℕ) → ℕ} {Q : (Fin (k + 2) → ℕ) → Prop}
    {h : (Fin (k + 2) → ℕ) → ℕ} {tl tr tc : ℕ}
    (hl : GlueComputes B P lhs bound tl) (hr : GlueComputes B P rhs bound tr)
    (hc : GlueComputes B Q h (fun v' => bound (v' ∘ Fin.castAdd 2)) tc)
    (hQ : ∀ v, P v → Q (Fin.addCases v ![lhs v, rhs v])) :
    GlueComputes B P (fun v => h (Fin.addCases v ![lhs v, rhs v])) bound (tl + tr + tc) := by
  obtain ⟨_, a, el, hl⟩ := hl
  obtain ⟨_, b, er, hr⟩ := hr
  obtain ⟨hco, c, ec, hc⟩ := hc
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (a + b + c + 2 + 1) → Fin r) → Code B r :=
    fun src tmp => .seq (el src (tmp ∘ stageLeft))
      (.seq (er src (tmp ∘ stageRight))
        (ec (Fin.addCases src ![tmp (stageLeft 0), tmp (stageRight 0)]) (tmp ∘ stageRest)))
  refine ⟨fun v hv => ?_, a + b + c + 2, emit, ?_⟩
  · have hcast : Fin.addCases v ![lhs v, rhs v] ∘ Fin.castAdd 2 = v :=
      funext fun i => by simp
    simpa only [hcast] using hco (Fin.addCases v ![lhs v, rhs v]) (hQ v hv)
  intro r src tmp hi hd
  obtain ⟨hgl, hrl⟩ := hl src (tmp ∘ stageLeft) (hi.comp stageLeft_injective)
    (fun i j => hd i (stageLeft j))
  obtain ⟨hgr, hrr⟩ := hr src (tmp ∘ stageRight) (hi.comp stageRight_injective)
    (fun i j => hd i (stageRight j))
  have hdc (i : Fin (k + 2)) (j : Fin (c + 1)) :
      Fin.addCases src ![tmp (stageLeft 0), tmp (stageRight 0)] i ≠ tmp (stageRest j) := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.addCases_left] using hd i (stageRest j)
    · rw [Fin.addCases_right]
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i
      · exact fun h => stageLeft_ne_stageRest 0 j (hi h)
      · exact fun h => stageRight_ne_stageRest 0 j (hi h)
  obtain ⟨hgc, hrc⟩ := hc (Fin.addCases src ![tmp (stageLeft 0), tmp (stageRight 0)])
    (tmp ∘ stageRest) (hi.comp stageRest_injective) hdc
  refine ⟨⟨hgl, hgr, hgc⟩, ?_⟩
  intro w x hx hw
  obtain ⟨y, hy, hyo, hym, hyf⟩ := hrl w x hx hw
  have hys : y.regs ∘ src = x.regs ∘ src :=
    funext fun i => hyf (src i) (fun j => (hd i (stageLeft j)).symm)
  obtain ⟨z, hz, hzo, hzm, hzf⟩ := hrr w y (hys.symm ▸ hx) (hys.symm ▸ hw)
  have hzs : z.regs ∘ src = x.regs ∘ src :=
    funext fun i => (hzf (src i) (fun j => (hd i (stageRight j)).symm)).trans (congrFun hys i)
  have hleft : z.regs (tmp (stageLeft 0)) = lhs (x.regs ∘ src) :=
    (hzf _ (fun j h => stageLeft_ne_stageRight (0 : Fin (a + 1)) j (hi h).symm)).trans hyo
  have hright : z.regs (tmp (stageRight 0)) = rhs (x.regs ∘ src) := by
    change z.regs (tmp (stageRight 0)) = rhs (y.regs ∘ src) at hzo
    exact hys ▸ hzo
  have hsrc' : z.regs ∘ Fin.addCases src ![tmp (stageLeft 0), tmp (stageRight 0)] =
      Fin.addCases (x.regs ∘ src) ![lhs (x.regs ∘ src), rhs (x.regs ∘ src)] := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Function.comp_apply, Fin.addCases_left]
      exact congrFun hzs i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i <;>
        simp [hleft, hright]
  have hcast : Fin.addCases (x.regs ∘ src) ![lhs (x.regs ∘ src), rhs (x.regs ∘ src)] ∘
      Fin.castAdd 2 = x.regs ∘ src :=
    funext fun i => by simp
  obtain ⟨u, hu, huo, hum, huf⟩ := hrc w z (hsrc'.symm ▸ hQ _ hx)
    (by simpa only [hsrc', hcast] using hw)
  have hzero : stageRest (a := a) (b := b) (0 : Fin (c + 1)) = 0 := by ext; rfl
  refine ⟨u, (hy.seq (hz.seq hu)).mono (by omega),
    by simpa only [Function.comp_apply, hzero, hsrc'] using huo,
    hum.trans (hzm.trans hym), ?_⟩
  intro i hne
  exact (huf i (fun j => hne (stageRest j))).trans
    ((hzf i (fun j => hne (stageRight j))).trans (hyf i (fun j => hne (stageLeft j))))

/-- Select between two computations by equality of two computed words. Both guard operands are
staged once before the branch, and only the selected branch is executed. -/
theorem ite_eq_staged {lhs rhs f g : (Fin k → ℕ) → ℕ} {tl tr tf tg : ℕ}
    (hl : GlueComputes B P lhs bound tl) (hr : GlueComputes B P rhs bound tr)
    (hf : GlueComputes B (fun v => P v ∧ lhs v = rhs v) f bound tf)
    (hg : GlueComputes B (fun v => P v ∧ ¬lhs v = rhs v) g bound tg) :
    GlueComputes B P (fun v => if lhs v = rhs v then f v else g v)
      bound (tl + tr + (max tf tg + 3)) := by
  let Q : (Fin (k + 2) → ℕ) → Prop := fun v' =>
    P (v' ∘ Fin.castAdd 2) ∧
      v' (Fin.natAdd k 0) = lhs (v' ∘ Fin.castAdd 2) ∧
      v' (Fin.natAdd k 1) = rhs (v' ∘ Fin.castAdd 2)
  let cond : Cond (k + 2) := .eq (Fin.natAdd k 0) (Fin.natAdd k 1)
  have hf' : GlueComputes B (fun v' => Q v' ∧ cond.Holds ⟨v', fun _ => 0⟩)
      (fun v' => f (v' ∘ Fin.castAdd 2)) (fun v' => bound (v' ∘ Fin.castAdd 2)) tf :=
    hf.reindex (Fin.castAdd 2)
      (fun v' ⟨⟨hp, hl', hr'⟩, hc⟩ => ⟨hp, by simpa only [cond, Cond.Holds, hl', hr'] using hc⟩)
      (fun _ _ => le_rfl)
  have hg' : GlueComputes B (fun v' => Q v' ∧ ¬cond.Holds ⟨v', fun _ => 0⟩)
      (fun v' => g (v' ∘ Fin.castAdd 2)) (fun v' => bound (v' ∘ Fin.castAdd 2)) tg :=
    hg.reindex (Fin.castAdd 2)
      (fun v' ⟨⟨hp, hl', hr'⟩, hc⟩ => ⟨hp, by simpa only [cond, Cond.Holds, hl', hr'] using hc⟩)
      (fun _ _ => le_rfl)
  have hsel := select cond hf' hg'
  have hst := stage_pair hl hr hsel (fun v hp => by
    have hcast : Fin.addCases v ![lhs v, rhs v] ∘ Fin.castAdd 2 = v :=
      funext fun i => by simp
    refine ⟨hcast.symm ▸ hp, ?_, ?_⟩ <;> simp [hcast])
  convert hst using 2 with v
  have hcast : Fin.addCases v ![lhs v, rhs v] ∘ Fin.castAdd 2 = v :=
    funext fun i => by simp
  simp [cond, Cond.Holds, hcast]

/-- Select between two computations by unsigned comparison of two computed words. Both guard
operands are staged once before the branch, and only the selected branch is executed. -/
theorem ite_lt_staged {lhs rhs f g : (Fin k → ℕ) → ℕ} {tl tr tf tg : ℕ}
    (hl : GlueComputes B P lhs bound tl) (hr : GlueComputes B P rhs bound tr)
    (hf : GlueComputes B (fun v => P v ∧ lhs v < rhs v) f bound tf)
    (hg : GlueComputes B (fun v => P v ∧ ¬lhs v < rhs v) g bound tg) :
    GlueComputes B P (fun v => if lhs v < rhs v then f v else g v)
      bound (tl + tr + (max tf tg + 3)) := by
  let Q : (Fin (k + 2) → ℕ) → Prop := fun v' =>
    P (v' ∘ Fin.castAdd 2) ∧
      v' (Fin.natAdd k 0) = lhs (v' ∘ Fin.castAdd 2) ∧
      v' (Fin.natAdd k 1) = rhs (v' ∘ Fin.castAdd 2)
  let cond : Cond (k + 2) := .lt (Fin.natAdd k 0) (Fin.natAdd k 1)
  have hf' : GlueComputes B (fun v' => Q v' ∧ cond.Holds ⟨v', fun _ => 0⟩)
      (fun v' => f (v' ∘ Fin.castAdd 2)) (fun v' => bound (v' ∘ Fin.castAdd 2)) tf :=
    hf.reindex (Fin.castAdd 2)
      (fun v' ⟨⟨hp, hl', hr'⟩, hc⟩ => ⟨hp, by simpa only [cond, Cond.Holds, hl', hr'] using hc⟩)
      (fun _ _ => le_rfl)
  have hg' : GlueComputes B (fun v' => Q v' ∧ ¬cond.Holds ⟨v', fun _ => 0⟩)
      (fun v' => g (v' ∘ Fin.castAdd 2)) (fun v' => bound (v' ∘ Fin.castAdd 2)) tg :=
    hg.reindex (Fin.castAdd 2)
      (fun v' ⟨⟨hp, hl', hr'⟩, hc⟩ => ⟨hp, by simpa only [cond, Cond.Holds, hl', hr'] using hc⟩)
      (fun _ _ => le_rfl)
  have hsel := select cond hf' hg'
  have hst := stage_pair hl hr hsel (fun v hp => by
    have hcast : Fin.addCases v ![lhs v, rhs v] ∘ Fin.castAdd 2 = v :=
      funext fun i => by simp
    refine ⟨hcast.symm ▸ hp, ?_, ?_⟩ <;> simp [hcast])
  convert hst using 2 with v
  have hcast : Fin.addCases v ![lhs v, rhs v] ∘ Fin.castAdd 2 = v :=
    funext fun i => by simp
  simp [cond, Cond.Holds, hcast]

end GlueComputes

namespace GlueComputable

variable {P : (Fin k → ℕ) → Prop} {bound : (Fin k → ℕ) → ℕ}

/-- Register projections are found without searching for a budget. -/
@[fun_prop]
theorem proj (i : Fin k) (hb : ∀ v, P v → v i ≤ bound v) :
    GlueComputable B (fun v => v i) P bound := (GlueComputes.proj i hb).computable

/-- Constants are found without searching for a budget. -/
@[fun_prop]
theorem const (z : ℕ) (hb : ∀ v, P v → z ≤ bound v) :
    GlueComputable B (fun _ => z) P bound := (GlueComputes.const z hb).computable

variable {f g : (Fin k → ℕ) → ℕ}

/-- Reuse a named scalar computation after another computation, with explicit domain and
envelope implications. This rule searches for the two functions, never for a budget. -/
@[fun_prop]
theorem comp {h : ℕ → ℕ} {b : (Fin 1 → ℕ) → ℕ} {Q : (Fin 1 → ℕ) → Prop}
    (hf : GlueComputable B f P bound)
    (hh : GlueComputable B (fun v => h (v 0)) Q b)
    (hQ : ∀ v, P v → Q (fun _ => f v))
    (hb : ∀ v, P v → b (fun _ => f v) ≤ bound v) :
    GlueComputable B (fun v => h (f v)) P bound := by
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨th, hh⟩ := hh
  exact (hf.comp hh hQ hb).computable

/-- Apply an opaque routine to any finite vector of computed local words. The component
budgets are chosen uniformly, before the input/width quantifiers, and then summed explicitly. -/
@[fun_prop]
theorem comp_many {m : ℕ} {Q : (Fin m → ℕ) → Prop} {h b : (Fin m → ℕ) → ℕ}
    {g : (Fin k → ℕ) → Fin m → ℕ}
    (hh : GlueComputable B h Q b)
    (hg : ∀ i, GlueComputable B (fun v => g v i) P bound)
    (hQ : ∀ v, P v → Q (g v)) (hb : ∀ v, P v → b (g v) ≤ bound v) :
    GlueComputable B (fun v => h (g v)) P bound := by
  classical
  obtain ⟨tf, hf⟩ := hh
  choose t ht using hg
  exact (hf.comp_many ht hQ hb).computable

/-- Indexing a finite tuple is compile-time routing, so it adds no runtime instruction. -/
@[fun_prop]
theorem vec_cons {m : ℕ} {g : (Fin k → ℕ) → Fin m → ℕ}
    (hf : GlueComputable B f P bound)
    (hg : ∀ i, GlueComputable B (fun v => g v i) P bound) (i : Fin (m + 1)) :
    GlueComputable B (fun v => Matrix.vecCons (f v) (g v) i) P bound := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact hg j

/-- A singleton tuple has just its computed head; there is no empty-tail obligation. -/
@[fun_prop]
theorem vec_single (hf : GlueComputable B f P bound) (i : Fin 1) :
    GlueComputable B (fun v => ![f v] i) P bound := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hf

/-- Register-condition selection retains branch-specific domains. -/
theorem select (cond : Cond k)
    (hf : GlueComputable B f (fun v => P v ∧ cond.Holds ⟨v, fun _ => 0⟩) bound)
    (hg : GlueComputable B g (fun v => P v ∧ ¬cond.Holds ⟨v, fun _ => 0⟩) bound) :
    GlueComputable B (fun v => if cond.Holds ⟨v, fun _ => 0⟩ then f v else g v) P bound := by
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨tg, hg⟩ := hg
  exact (GlueComputes.select cond hf hg).computable

/-- Select by equality of input words, without evaluating the unchosen computation. The guard
compares the input registers directly, so the operands need not fit the result envelope. -/
@[fun_prop]
theorem ite_eq (i j : Fin k)
    (hf : GlueComputable B f (fun v => P v ∧ v i = v j) bound)
    (hg : GlueComputable B g (fun v => P v ∧ ¬v i = v j) bound) :
    GlueComputable B (fun v => if v i = v j then f v else g v) P bound :=
  select (.eq i j) hf hg

/-- Select by unsigned comparison of input words. The guard compares the input registers
directly, so the operands need not fit the result envelope. -/
@[fun_prop]
theorem ite_lt (i j : Fin k)
    (hf : GlueComputable B f (fun v => P v ∧ v i < v j) bound)
    (hg : GlueComputable B g (fun v => P v ∧ ¬v i < v j) bound) :
    GlueComputable B (fun v => if v i < v j then f v else g v) P bound :=
  select (.lt i j) hf hg

/-- Select by equality of computed words, without evaluating the unchosen computation. Both
operands are staged, so each must be certified within the result envelope; `ite_eq` handles
direct input-register comparisons without that obligation. -/
@[fun_prop]
theorem ite_eq_staged {lhs rhs : (Fin k → ℕ) → ℕ}
    (hl : GlueComputable B lhs P bound)
    (hr : GlueComputable B rhs P bound)
    (hf : GlueComputable B f (fun v => P v ∧ lhs v = rhs v) bound)
    (hg : GlueComputable B g (fun v => P v ∧ ¬lhs v = rhs v) bound) :
    GlueComputable B (fun v => if lhs v = rhs v then f v else g v) P bound := by
  obtain ⟨tl, hl⟩ := hl
  obtain ⟨tr, hr⟩ := hr
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨tg, hg⟩ := hg
  exact (GlueComputes.ite_eq_staged hl hr hf hg).computable

/-- Select by unsigned comparison of computed words, without evaluating the unchosen
computation. Both operands are staged, so each must be certified within the result envelope;
`ite_lt` handles direct input-register comparisons without that obligation. -/
@[fun_prop]
theorem ite_lt_staged {lhs rhs : (Fin k → ℕ) → ℕ}
    (hl : GlueComputable B lhs P bound)
    (hr : GlueComputable B rhs P bound)
    (hf : GlueComputable B f (fun v => P v ∧ lhs v < rhs v) bound)
    (hg : GlueComputable B g (fun v => P v ∧ ¬lhs v < rhs v) bound) :
    GlueComputable B (fun v => if lhs v < rhs v then f v else g v) P bound := by
  obtain ⟨tl, hl⟩ := hl
  obtain ⟨tr, hr⟩ := hr
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨tg, hg⟩ := hg
  exact (GlueComputes.ite_lt_staged hl hr hf hg).computable

/-- The standard basis's binary operation rule. -/
theorem bin_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound) (op : BinOp)
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputable .standard (fun v => op.eval (f v) (g v)) P bound := by
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨tg, hg⟩ := hg
  exact (hf.bin_standard hg op hb).computable

/-- The exact basis's binary operation rule keeps its domain premise explicit. -/
theorem bin_exact (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound) (op : BinOp)
    (hv : ∀ v, P v → op.evalExact (f v) (g v) = some (op.eval (f v) (g v)))
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputable .exact (fun v => op.eval (f v) (g v)) P bound := by
  obtain ⟨tf, hf⟩ := hf
  obtain ⟨tg, hg⟩ := hg
  exact (hf.bin_exact hg op hv hb).computable

/-- Closure under exact-basis `add`; the common envelope also bounds this result. -/
@[fun_prop]
theorem add (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v + g v ≤ bound v) :
    GlueComputable .exact (fun v => f v + g v) P bound :=
  bin_exact hf hg .add (fun _ _ => rfl) hb

/-- Closure under exact-basis `sub`; the common envelope also bounds this result. -/
@[fun_prop]
theorem sub (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hv : ∀ v, P v → g v ≤ f v)
    (hb : ∀ v, P v → f v - g v ≤ bound v) :
    GlueComputable .exact (fun v => f v - g v) P bound :=
  bin_exact hf hg .sub (fun v hp => by simp [hv v hp]) hb

/-- Closure under exact-basis `mul`; the common envelope also bounds this result. -/
@[fun_prop]
theorem mul (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v * g v ≤ bound v) :
    GlueComputable .exact (fun v => f v * g v) P bound :=
  bin_exact hf hg .mul (fun _ _ => rfl) hb

/-- Closure under exact-basis `div`; the common envelope also bounds this result. -/
@[fun_prop]
theorem div (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hv : ∀ v, P v → g v ≠ 0)
    (hb : ∀ v, P v → f v / g v ≤ bound v) :
    GlueComputable .exact (fun v => f v / g v) P bound :=
  bin_exact hf hg .div (fun v hp => by simp [hv v hp]) hb

/-- Closure under exact-basis `mod`; the common envelope also bounds this result. -/
@[fun_prop]
theorem mod (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hv : ∀ v, P v → g v ≠ 0)
    (hb : ∀ v, P v → f v % g v ≤ bound v) :
    GlueComputable .exact (fun v => f v % g v) P bound :=
  bin_exact hf hg .mod (fun v hp => by simp [hv v hp]) hb

/-- Closure under exact-basis `and`; the common envelope also bounds this result. -/
@[fun_prop]
theorem and (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v &&& g v ≤ bound v) :
    GlueComputable .exact (fun v => f v &&& g v) P bound :=
  bin_exact hf hg .and (fun _ _ => rfl) hb

/-- Closure under exact-basis `or`; the common envelope also bounds this result. -/
@[fun_prop]
theorem or (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v ||| g v ≤ bound v) :
    GlueComputable .exact (fun v => f v ||| g v) P bound :=
  bin_exact hf hg .or (fun _ _ => rfl) hb

/-- Closure under exact-basis `xor`; the common envelope also bounds this result. -/
@[fun_prop]
theorem xor (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v ^^^ g v ≤ bound v) :
    GlueComputable .exact (fun v => f v ^^^ g v) P bound :=
  bin_exact hf hg .xor (fun _ _ => rfl) hb

/-- Closure under exact-basis `shiftLeft`; the common envelope also bounds this result. -/
@[fun_prop]
theorem shiftLeft (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v <<< g v ≤ bound v) :
    GlueComputable .exact (fun v => f v <<< g v) P bound :=
  bin_exact hf hg .shiftLeft (fun _ _ => rfl) hb

/-- Closure under exact-basis `shiftRight`; the common envelope also bounds this result. -/
@[fun_prop]
theorem shiftRight (hf : GlueComputable .exact f P bound)
    (hg : GlueComputable .exact g P bound)
    (hb : ∀ v, P v → f v >>> g v ≤ bound v) :
    GlueComputable .exact (fun v => f v >>> g v) P bound :=
  bin_exact hf hg .shiftRight (fun _ _ => rfl) hb

/-- Closure under standard-basis `add`; the common envelope also bounds this result. -/
@[fun_prop]
theorem add_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v + g v ≤ bound v) :
    GlueComputable .standard (fun v => f v + g v) P bound :=
  bin_standard hf hg .add hb

/-- Closure under standard-basis `sub`; the common envelope also bounds this result. -/
@[fun_prop]
theorem sub_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v - g v ≤ bound v) :
    GlueComputable .standard (fun v => f v - g v) P bound :=
  bin_standard hf hg .sub hb

/-- Closure under standard-basis `mul`; the common envelope also bounds this result. -/
@[fun_prop]
theorem mul_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v * g v ≤ bound v) :
    GlueComputable .standard (fun v => f v * g v) P bound :=
  bin_standard hf hg .mul hb

/-- Closure under standard-basis `div`; the common envelope also bounds this result. -/
@[fun_prop]
theorem div_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v / g v ≤ bound v) :
    GlueComputable .standard (fun v => f v / g v) P bound :=
  bin_standard hf hg .div hb

/-- Closure under standard-basis `mod`; the common envelope also bounds this result. -/
@[fun_prop]
theorem mod_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v % g v ≤ bound v) :
    GlueComputable .standard (fun v => f v % g v) P bound :=
  bin_standard hf hg .mod hb

/-- Closure under standard-basis `and`; the common envelope also bounds this result. -/
@[fun_prop]
theorem and_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v &&& g v ≤ bound v) :
    GlueComputable .standard (fun v => f v &&& g v) P bound :=
  bin_standard hf hg .and hb

/-- Closure under standard-basis `or`; the common envelope also bounds this result. -/
@[fun_prop]
theorem or_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v ||| g v ≤ bound v) :
    GlueComputable .standard (fun v => f v ||| g v) P bound :=
  bin_standard hf hg .or hb

/-- Closure under standard-basis `xor`; the common envelope also bounds this result. -/
@[fun_prop]
theorem xor_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v ^^^ g v ≤ bound v) :
    GlueComputable .standard (fun v => f v ^^^ g v) P bound :=
  bin_standard hf hg .xor hb

/-- Closure under standard-basis `shiftLeft`; the common envelope also bounds this result. -/
@[fun_prop]
theorem shiftLeft_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v <<< g v ≤ bound v) :
    GlueComputable .standard (fun v => f v <<< g v) P bound :=
  bin_standard hf hg .shiftLeft hb

/-- Closure under standard-basis `shiftRight`; the common envelope also bounds this result. -/
@[fun_prop]
theorem shiftRight_standard (hf : GlueComputable .standard f P bound)
    (hg : GlueComputable .standard g P bound)
    (hb : ∀ v, P v → f v >>> g v ≤ bound v) :
    GlueComputable .standard (fun v => f v >>> g v) P bound :=
  bin_standard hf hg .shiftRight hb

end GlueComputable

/-- Graded register-word glue certificate with an explicit upper bound `time` on the instruction
budget and `2 * time` on the auxiliary register count. -/
@[expose]
def GlueComputableAt (time : ℕ) (B : Basis) (f : (Fin k → ℕ) → ℕ) (P : (Fin k → ℕ) → Prop)
    (bound : (Fin k → ℕ) → ℕ) : Prop :=
  (∀ v, P v → f v ≤ bound v) ∧
  ∃ n₀ ≤ 2 * time, ∃ t₀ ≤ time,
    ∃ emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (n₀ + 1) → Fin r) → Code B r,
      ∀ {r : ℕ} (src : Fin k → Fin r) (tmp : Fin (n₀ + 1) → Fin r),
        Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
        (emit src tmp).IsGlue ∧
        ∀ (w : ℕ) (x : Data r), P (x.regs ∘ src) → Fits w (bound (x.regs ∘ src)) →
          ∃ y, ExecWithin w (emit src tmp) x y t₀ ∧
            y.regs (tmp 0) = f (x.regs ∘ src) ∧ y.mem = x.mem ∧
            ∀ i, (∀ j, tmp j ≠ i) → y.regs i = x.regs i

namespace GlueComputableAt

variable {t₁ : ℕ} {P : (Fin k → ℕ) → Prop} {bound : (Fin k → ℕ) → ℕ}
  {f g : (Fin k → ℕ) → ℕ} {tf tg t₂ : ℕ}

/-- Monotonicity of `GlueComputableAt` in the instruction budget `time`. -/
theorem mono (ht : t₁ ≤ t₂) (h : GlueComputableAt t₁ B f P bound) :
    GlueComputableAt t₂ B f P bound := by
  obtain ⟨hb, n₀, hn₀, t₀, ht₀, emit, he⟩ := h
  exact ⟨hb, n₀, hn₀.trans (by omega), t₀, ht₀.trans ht, emit, he⟩

/-- Forget the explicit budget bound to `GlueComputable`. -/
theorem toGlueComputable (h : GlueComputableAt t₁ B f P bound) :
    GlueComputable B f P bound := by
  obtain ⟨hb, n₀, _, t₀, _, emit, he⟩ := h
  exact ⟨t₀, hb, n₀, emit, he⟩

/-- Register projections use `0` auxiliary registers and `1` instruction. -/
theorem proj (i : Fin k) (hb : ∀ v, P v → v i ≤ bound v) :
    GlueComputableAt 1 B (fun v => v i) P bound := by
  refine ⟨hb, 0, by omega, 1, le_rfl, fun src tmp => .op (.copy (tmp 0) (src i)), ?_⟩
  intro r src tmp _ _
  refine ⟨trivial, fun w x _ _ => ⟨x.set (tmp 0) (x.regs (src i)), ExecWithin.copy, ?_, rfl, ?_⟩⟩
  · simp [Data.set]
  · intro j hj
    exact Function.update_of_ne (hj 0).symm _ _

/-- Constants use `0` auxiliary registers and `1` instruction. -/
theorem const (z : ℕ) (hb : ∀ v, P v → z ≤ bound v) :
    GlueComputableAt 1 B (fun _ => z) P bound := by
  refine ⟨hb, 0, by omega, 1, le_rfl, fun _ tmp => .op (.const (tmp 0) z), ?_⟩
  intro r src tmp _ _
  refine ⟨trivial, fun w x hx hw => ⟨x.set (tmp 0) z,
    ExecWithin.const (hw.of_le (hb _ hx)), ?_, rfl, ?_⟩⟩
  · simp [Data.set]
  · intro j hj
    exact Function.update_of_ne (hj 0).symm _ _

/-- Indexing a finite tuple at a uniform budget `t₁`. -/
theorem vec_cons {m : ℕ} {g : (Fin k → ℕ) → Fin m → ℕ}
    (hf : GlueComputableAt t₁ B f P bound)
    (hg : ∀ i, GlueComputableAt t₁ B (fun v => g v i) P bound) (i : Fin (m + 1)) :
    GlueComputableAt t₁ B (fun v => Matrix.vecCons (f v) (g v) i) P bound := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact hg j

/-- A singleton tuple at budget `t₁`. -/
theorem vec_single (hf : GlueComputableAt t₁ B f P bound) (i : Fin 1) :
    GlueComputableAt t₁ B (fun v => ![f v] i) P bound := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hf

private def left {a b : ℕ} (j : Fin (a + 1)) : Fin (a + b + 3) :=
  ⟨j.val + 1, by omega⟩

private def right {a b : ℕ} (j : Fin (b + 1)) : Fin (a + b + 3) :=
  ⟨j.val + a + 2, by omega⟩

private theorem left_injective {a b : ℕ} : Function.Injective (@left a b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [left] at this
  omega

private theorem right_injective {a b : ℕ} : Function.Injective (@right a b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [right] at this
  omega

private theorem left_ne_right {a b : ℕ} (i : Fin (a + 1)) (j : Fin (b + 1)) :
    left i ≠ right j := by
  intro h
  have := congrArg Fin.val h
  simp only [left, right] at this
  omega

/-- Apply a basis operation to two graded computed words. -/
theorem binary {h : (Fin k → ℕ) → ℕ}
    (hf : GlueComputableAt tf B f P bound) (hg : GlueComputableAt tg B g P bound)
    (op : B.Op) (args : Fin (B.Arity op) → Fin 2) (hop : ¬B.ReadsWidth op)
    (heval : ∀ v, P v → ∀ w, B.interp w op (fun i => ![f v, g v] (args i)) = some (h v))
    (hb : ∀ v, P v → h v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) B h P bound := by
  obtain ⟨_, a, ha, tfa, htfa, ea, hea⟩ := hf
  obtain ⟨_, b, hb', tgb, htgb, eb, heb⟩ := hg
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (a + b + 2 + 1) → Fin r) → Code B r :=
    fun src tmp => .seq (ea src (tmp ∘ left))
      (.seq (eb src (tmp ∘ right))
        (.op (.alu op (tmp 0)
          (fun i => if args i = 0 then tmp (left 0) else tmp (right 0)))))
  refine ⟨hb, a + b + 2, by omega, tfa + tgb + 1, by omega, emit, ?_⟩
  intro r src tmp hi hd
  obtain ⟨hga, hra⟩ := hea src (tmp ∘ left)
    (hi.comp left_injective) (fun i j => hd i (left j))
  obtain ⟨hgb, hrb⟩ := heb src (tmp ∘ right)
    (hi.comp right_injective) (fun i j => hd i (right j))
  refine ⟨⟨hga, hgb, hop⟩, ?_⟩
  intro w x hx hw
  obtain ⟨y, hy, hyo, hym, hyf⟩ := hra w x hx hw
  have hys : y.regs ∘ src = x.regs ∘ src := by
    funext i
    exact hyf (src i) (fun j => (hd i (left j)).symm)
  obtain ⟨z, hz, hzo, hzm, hzf⟩ := hrb w y (hys.symm ▸ hx) (hys.symm ▸ hw)
  have hleft : z.regs (tmp (left 0)) = f (x.regs ∘ src) :=
    (hzf _ (fun j h => left_ne_right (0 : Fin (a + 1)) j (hi h).symm)).trans hyo
  have hright : z.regs (tmp (right 0)) = g (x.regs ∘ src) := by
    change z.regs (tmp (right 0)) = g (y.regs ∘ src) at hzo
    exact hys ▸ hzo
  have hargs : (z.regs ∘ (fun i =>
      if args i = 0 then tmp (left 0) else tmp (right 0))) =
      (fun i => ![f (x.regs ∘ src), g (x.regs ∘ src)] (args i)) := by
    funext i
    by_cases h : args i = 0
    · simp [h, hleft]
    · have h' : args i = 1 := by apply Fin.ext; have := (args i).isLt; omega
      simp [h', hright]
  have he : ExecWithin w (.op (.alu op (tmp 0)
      (fun i => if args i = 0 then tmp (left 0) else tmp (right 0)))) z
      (z.set (tmp 0) (h (x.regs ∘ src))) 1 := by
    apply ExecWithin.alu _ (hw.of_le (hb _ hx))
    rw [hargs]
    exact heval _ hx w
  refine ⟨z.set (tmp 0) (h (x.regs ∘ src)), hy.seq (hz.seq he), ?_, hzm.trans hym, ?_⟩
  · simp [Data.set]
  · intro i hne
    change Function.update z.regs (tmp 0) (h (x.regs ∘ src)) i = x.regs i
    rw [Function.update_of_ne (hne 0).symm]
    exact (hzf i (fun j => hne (right j))).trans
      (hyf i (fun j => hne (left j)))

/-- Select between two graded computations by an existing register condition. -/
theorem select (cond : Cond k)
    (hf : GlueComputableAt tf B f (fun v => P v ∧ cond.Holds ⟨v, fun _ => 0⟩) bound)
    (hg : GlueComputableAt tg B g (fun v => P v ∧ ¬cond.Holds ⟨v, fun _ => 0⟩) bound) :
    GlueComputableAt (tf + tg + 3) B
      (fun v => if cond.Holds ⟨v, fun _ => 0⟩ then f v else g v) P bound := by
  obtain ⟨hfo, a, ha, tfa, htfa, ea, hea⟩ := hf
  obtain ⟨hgo, b, hb', tgb, htgb, eb, heb⟩ := hg
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (a + b + 2 + 1) → Fin r) → Code B r :=
    fun src tmp => .branch (cond.rename src)
      (.seq (ea src (tmp ∘ left)) (.op (.copy (tmp 0) (tmp (left 0)))))
      (.seq (eb src (tmp ∘ right)) (.op (.copy (tmp 0) (tmp (right 0)))))
  refine ⟨?_, a + b + 2, by omega, max tfa tgb + 3, by omega, emit, ?_⟩
  · intro v hv
    dsimp only
    split
    · exact hfo v ⟨hv, by assumption⟩
    · exact hgo v ⟨hv, by assumption⟩
  intro r src tmp hi hd
  obtain ⟨hga, hra⟩ := hea src (tmp ∘ left)
    (hi.comp left_injective) (fun i j => hd i (left j))
  obtain ⟨hgb, hrb⟩ := heb src (tmp ∘ right)
    (hi.comp right_injective) (fun i j => hd i (right j))
  refine ⟨⟨⟨hga, trivial⟩, hgb, trivial⟩, ?_⟩
  intro w x hx hw
  have hc : (cond.rename src).Holds x ↔ cond.Holds ⟨x.regs ∘ src, fun _ => 0⟩ := by
    cases cond <;> rfl
  by_cases h : cond.Holds ⟨x.regs ∘ src, fun _ => 0⟩
  · obtain ⟨y, hy, hyo, hym, hyf⟩ := hra w x ⟨hx, h⟩ hw
    refine ⟨y.set (tmp 0) (y.regs (tmp (left 0))),
      ((hy.seq ExecWithin.copy).branch_pos (hc.mpr h)).mono (by omega), ?_, hym, ?_⟩
    · simpa [Data.set, h] using hyo
    · intro i hne
      change Function.update y.regs (tmp 0) _ i = x.regs i
      rw [Function.update_of_ne (hne 0).symm]
      exact hyf i (fun j => hne (left j))
  · obtain ⟨y, hy, hyo, hym, hyf⟩ := hrb w x ⟨hx, h⟩ hw
    refine ⟨y.set (tmp 0) (y.regs (tmp (right 0))),
      ((hy.seq ExecWithin.copy).branch_neg (fun h' => h (hc.mp h'))).mono (by omega),
      ?_, hym, ?_⟩
    · simpa [Data.set, h] using hyo
    · intro i hne
      change Function.update y.regs (tmp 0) _ i = x.regs i
      rw [Function.update_of_ne (hne 0).symm]
      exact hyf i (fun j => hne (right j))

theorem ite_eq (i j : Fin k)
    (hf : GlueComputableAt tf B f (fun v => P v ∧ v i = v j) bound)
    (hg : GlueComputableAt tg B g (fun v => P v ∧ ¬v i = v j) bound) :
    GlueComputableAt (tf + tg + 3) B (fun v => if v i = v j then f v else g v) P bound :=
  select (.eq i j) hf hg

theorem ite_lt (i j : Fin k)
    (hf : GlueComputableAt tf B f (fun v => P v ∧ v i < v j) bound)
    (hg : GlueComputableAt tg B g (fun v => P v ∧ ¬v i < v j) bound) :
    GlueComputableAt (tf + tg + 3) B (fun v => if v i < v j then f v else g v) P bound :=
  select (.lt i j) hf hg

/-- Standard-basis binary operation with explicit budget `tf + tg + 1`. -/
theorem bin_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound) (op : BinOp)
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => op.eval (f v) (g v)) P bound :=
  binary hf hg (.bin op) id (by simp) (fun _ _ _ => rfl) hb

/-- Exact-basis binary operation with explicit budget `tf + tg + 1`. -/
theorem bin_exact (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound) (op : BinOp)
    (hv : ∀ v, P v → op.evalExact (f v) (g v) = some (op.eval (f v) (g v)))
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => op.eval (f v) (g v)) P bound :=
  binary hf hg (.bin op) id (by simp) (fun v hp _ => hv v hp) hb

theorem add (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v + g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v + g v) P bound :=
  bin_exact hf hg .add (fun _ _ => rfl) hb

theorem sub (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hv : ∀ v, P v → g v ≤ f v)
    (hb : ∀ v, P v → f v - g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v - g v) P bound :=
  bin_exact hf hg .sub (fun v hp => by simp [hv v hp]) hb

theorem mul (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v * g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v * g v) P bound :=
  bin_exact hf hg .mul (fun _ _ => rfl) hb

theorem div (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hv : ∀ v, P v → g v ≠ 0)
    (hb : ∀ v, P v → f v / g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v / g v) P bound :=
  bin_exact hf hg .div (fun v hp => by simp [hv v hp]) hb

theorem mod (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hv : ∀ v, P v → g v ≠ 0)
    (hb : ∀ v, P v → f v % g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v % g v) P bound :=
  bin_exact hf hg .mod (fun v hp => by simp [hv v hp]) hb

theorem and (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v &&& g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v &&& g v) P bound :=
  bin_exact hf hg .and (fun _ _ => rfl) hb

theorem or (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v ||| g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v ||| g v) P bound :=
  bin_exact hf hg .or (fun _ _ => rfl) hb

theorem xor (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v ^^^ g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v ^^^ g v) P bound :=
  bin_exact hf hg .xor (fun _ _ => rfl) hb

theorem shiftLeft (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v <<< g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v <<< g v) P bound :=
  bin_exact hf hg .shiftLeft (fun _ _ => rfl) hb

theorem shiftRight (hf : GlueComputableAt tf .exact f P bound)
    (hg : GlueComputableAt tg .exact g P bound)
    (hb : ∀ v, P v → f v >>> g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .exact (fun v => f v >>> g v) P bound :=
  bin_exact hf hg .shiftRight (fun _ _ => rfl) hb

theorem add_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v + g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v + g v) P bound :=
  bin_standard hf hg .add hb

theorem sub_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v - g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v - g v) P bound :=
  bin_standard hf hg .sub hb

theorem mul_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v * g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v * g v) P bound :=
  bin_standard hf hg .mul hb

theorem div_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v / g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v / g v) P bound :=
  bin_standard hf hg .div hb

theorem mod_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v % g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v % g v) P bound :=
  bin_standard hf hg .mod hb

theorem and_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v &&& g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v &&& g v) P bound :=
  bin_standard hf hg .and hb

theorem or_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v ||| g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v ||| g v) P bound :=
  bin_standard hf hg .or hb

theorem xor_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v ^^^ g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v ^^^ g v) P bound :=
  bin_standard hf hg .xor hb

theorem shiftLeft_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v <<< g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v <<< g v) P bound :=
  bin_standard hf hg .shiftLeft hb

theorem shiftRight_standard (hf : GlueComputableAt tf .standard f P bound)
    (hg : GlueComputableAt tg .standard g P bound)
    (hb : ∀ v, P v → f v >>> g v ≤ bound v) :
    GlueComputableAt (tf + tg + 1) .standard (fun v => f v >>> g v) P bound :=
  bin_standard hf hg .shiftRight hb

end GlueComputableAt

end Cslib.WordRAM
