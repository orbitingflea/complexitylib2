/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Smolensky.Approximation
public import CslibFrontier.Foundations.Combinatorics.CentralBinomial
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeParity
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Razborov–Smolensky lower bound

**`MOD_p` is not in AC⁰[q]** for any two distinct primes `p ≠ q` (`modGate_notMem_AC0Mod`,
`compl_modGate_notMem_AC0Mod`): constant-depth, polynomial-size circuits of negations, unbounded
fan-in conjunctions and disjunctions, and `MOD_q` gates do not compute `MOD_p` [Razborov1987],
[Smolensky1987]. The library's `modGate p m x` accepts when the number of `true` inputs is not
divisible by `p` (`mem_ofSlices_modGate_iff`); the complement `(Language.ofSlices (modGate p))ᶜ`
is the textbook convention rejecting when the count is nonzero mod `p`
(`mem_compl_ofSlices_modGate_iff`). Since `modGate 2 = parity`, the `p = 2` special case is
`parity_notMem_AC0Mod`.

For the general finite tradeoff (`two_mul_two_pow_le_size_of_computes_modGate`), an AC⁰[q] circuit
of depth `d` computing `modGate p` on `n` bits is approximated in degree
`D = ((q - 1) ℓ) ^ d` over the algebraic closure `F` of `ZMod q` with error rate `size / 2 ^ ℓ`
(`exists_lowDegree_approx`). Fixing a primitive `p`-th root of unity `ω ∈ F` and padding
`r ∈ [1, p)` additional `true` bits onto `m = n - (p - 1)` inputs turns the approximator into a
degree-`D` polynomial agreeing with `ω ^ weight x` whenever all `p - 1` shifted evaluations
agree, yielding `2 · 2 ^ ℓ ≤ 5 (p - 1) 2 ^ (p - 1) · size` when
`100 (D + 1)² + (p - 1) ≤ n + 1` via `BitString.card_agree_phaseChar_le` and
`ten_mul_card_filter_card_le_le`. For parity against an odd prime
(`two_mul_two_pow_le_size_of_computes_parity`), working directly over `ZMod p` preserves the sharper
constant `2 · 2 ^ ℓ ≤ 5 · size` under `100 (D + 1)² ≤ n + 1`.

## Main definitions

* `Cslib.Circuits.Boolean.Smolensky.invertibleTwo`: `2` is invertible in `ZMod p` for an odd prime
  `p`.

## Main results

* `Cslib.Circuits.Boolean.Smolensky.mem_ofSlices_modGate_iff`,
  `Cslib.Circuits.Boolean.Smolensky.mem_compl_ofSlices_modGate_iff`: characterization of
  `Language.ofSlices (modGate p)` and its complement in terms of `List.count true % p`.
* `Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_modGate`: the finite
  size–depth tradeoff for `modGate p` against AC⁰[q] circuits for distinct primes `p ≠ q`.
* `Cslib.Circuits.Boolean.Smolensky.modGate_notMem_AC0Mod`,
  `Cslib.Circuits.Boolean.Smolensky.compl_modGate_notMem_AC0Mod`: `MOD_p` and its complement are
  not in AC⁰[q] for any distinct primes `p ≠ q`.
* `Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity`,
  `Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod`: the parity size–depth tradeoff and
  membership separation for odd primes `p`.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString

section Conventions

private theorem modGate_eq_decide_weight (p m : ℕ) (x : BitString m) :
    modGate p m x = decide (weight x % p ≠ 0) :=
  rfl

/-- `Language.ofSlices (modGate p)` accepts bit strings whose number of `true` entries is not
divisible by `p`. -/
theorem mem_ofSlices_modGate_iff (p : ℕ) (w : List Bool) :
    w ∈ Language.ofSlices (modGate p) ↔ w.count true % p ≠ 0 := by
  rw [Language.mem_ofSlices, modGate_eq_decide_weight, ← count_true_ofFn, decide_eq_true_iff]
  have hof : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  rw [hof]

/-- The complement `(Language.ofSlices (modGate p))ᶜ` accepts bit strings whose number of `true`
entries is divisible by `p`, matching the `MOD_p` convention where multiples of `p` are accepted. -/
theorem mem_compl_ofSlices_modGate_iff (p : ℕ) (w : List Bool) :
    w ∈ (Language.ofSlices (modGate p))ᶜ ↔ w.count true % p = 0 :=
  (not_congr (mem_ofSlices_modGate_iff p w)).trans not_not

end Conventions

section LowerBounds

/-! ### Padding helpers and shared counting bound -/

/-- A `k`-bit suffix of weight `r` (when `r ≤ k`): its first `r` bits are `true`. -/
private def padVec (k r : ℕ) : BitString k :=
  fun j => decide (j.1 < r)

/-- Appending `padVec (n - m) r` to `x : BitString m` produces an `n`-bit string when `m ≤ n`. -/
private def padBits {m n : ℕ} (hmn : m ≤ n) (r : ℕ) (x : BitString m) : BitString n :=
  fun i => Fin.append x (padVec (n - m) r) (Fin.cast (Nat.add_sub_cancel' hmn).symm i)

private theorem weight_padVec {k r : ℕ} (hr : r ≤ k) : weight (padVec k r) = r := by
  rw [weight]
  refine (card_bij (s := univ.filter fun j : Fin k => padVec k r j = true)
      (t := (univ : Finset (Fin r)))
      (fun j hj => ⟨j.1, of_decide_eq_true (mem_filter.1 hj).2⟩)
      (fun _ _ => mem_univ _)
      (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val (n := r)) h))
      (fun j _ => ⟨Fin.castLE hr j, mem_filter.2 ⟨mem_univ _, decide_eq_true j.2⟩, rfl⟩)).trans
    (by simp)

private theorem padBits_injective {m n : ℕ} (hmn : m ≤ n) (r : ℕ) :
    Function.Injective (padBits hmn r) := by
  intro x y hxy
  funext i
  have h := congrFun hxy (Fin.cast (Nat.add_sub_cancel' hmn) (Fin.castAdd (n - m) i))
  rw [padBits, padBits, Fin.cast_cast, Fin.cast_refl, id_eq,
    Fin.append_left, Fin.append_left] at h
  exact h

private theorem weight_padBits {m n : ℕ} (hmn : m ≤ n) {r : ℕ} (hr : r ≤ n - m)
    (x : BitString m) : weight (padBits hmn r x) = weight x + r := by
  simp only [weight_eq_sum_toNat, padBits]
  rw [← (finCongr (Nat.add_sub_cancel' hmn)).sum_comp]
  simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, ← weight_eq_sum_toNat, weight_padVec hr]

private theorem bitVal_padBits_mem_lowDegree {R : Type*} [CommRing R] {m n : ℕ} (hmn : m ≤ n)
    (r : ℕ) (i : Fin n) :
    (fun x : BitString m => bitVal R (padBits hmn r x i)) ∈ lowDegree R (Fin m) 1 := by
  change (fun x : BitString m => bitVal R
      (Fin.append x (padVec (n - m) r) (Fin.cast (Nat.add_sub_cancel' hmn).symm i))) ∈
    lowDegree R (Fin m) 1
  refine Fin.addCases (motive := fun idx =>
      (fun x : BitString m => bitVal R (Fin.append x (padVec (n - m) r) idx)) ∈
        lowDegree R (Fin m) 1)
    (fun j => ?_) (fun k => ?_) (Fin.cast (Nat.add_sub_cancel' hmn).symm i)
  · simp only [Fin.append_left]
    exact bitVal_mem_lowDegree j
  · simp only [Fin.append_right]
    have hconst : (fun _ : BitString m => bitVal R (padVec (n - m) r k)) =
        bitVal R (padVec (n - m) r k) • (1 : BitString m → R) := by
      funext _
      simp
    rw [hconst]
    exact Submodule.smul_mem _ _ (one_mem_lowDegree 1)

/-- Shared arithmetic step from an agreement bound `10 * #A ≤ 6 * 2 ^ m` and error bound
`2 ^ m ≤ #A + k * #E`, `#E * 2 ^ ℓ ≤ C.size * 2 ^ n` to `2 * 2 ^ ℓ ≤ 5 * k * 2 ^ (n - m) * C.size`.
-/
private theorem two_mul_two_pow_le_size_of_agreement_bound {m n ℓ k : ℕ} (hmn : m ≤ n)
    {C : Circuit Unbounded.extSignature n 1}
    {A : Finset (BitString m)} {E : Finset (BitString n)}
    (hA : 10 * #A ≤ 6 * 2 ^ m)
    (hmiss : 2 ^ m ≤ #A + k * #E)
    (herr : #E * 2 ^ ℓ ≤ C.size * 2 ^ n) :
    2 * 2 ^ ℓ ≤ 5 * k * 2 ^ (n - m) * C.size := by
  have hE : 4 * 2 ^ m ≤ 10 * (k * #E) := by omega
  have h : 2 * 2 ^ n * (2 * 2 ^ ℓ) ≤ 2 * 2 ^ n * (5 * k * 2 ^ (n - m) * C.size) := by
    calc 2 * 2 ^ n * (2 * 2 ^ ℓ)
        = 4 * 2 ^ (m + (n - m)) * 2 ^ ℓ := by rw [Nat.add_sub_of_le hmn]; ring
      _ = 4 * 2 ^ m * 2 ^ (n - m) * 2 ^ ℓ := by rw [pow_add]; ring
      _ ≤ 10 * (k * #E) * 2 ^ (n - m) * 2 ^ ℓ := by gcongr
      _ = 10 * k * (#E * 2 ^ ℓ) * 2 ^ (n - m) := by ring
      _ ≤ 10 * k * (C.size * 2 ^ n) * 2 ^ (n - m) := by gcongr
      _ = 2 * 2 ^ n * (5 * k * 2 ^ (n - m) * C.size) := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-! ### Finite size–depth tradeoffs and separation theorems -/

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {n : ℕ}

/-- `2` is invertible in `ZMod p` for an odd prime `p`. -/
@[instance_reducible] def invertibleTwo (hp2 : p ≠ 2) : Invertible (2 : ZMod p) :=
  invertibleOfNonzero fun h => hp2 <| (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h))

/-- **The general Razborov–Smolensky size–depth tradeoff.** A circuit of the AC⁰[q] basis of
depth `d` computing `modGate p` on `n` bits, for distinct primes `p ≠ q`, has size at least
`2 * 2 ^ ℓ / (5 * (p - 1) * 2 ^ (p - 1))` whenever `100 (((q - 1) ℓ) ^ d + 1)² + (p - 1) ≤ n + 1`.
-/
theorem two_mul_two_pow_le_size_of_computes_modGate (hpq : p ≠ q)
    {C : Circuit Unbounded.extSignature n 1}
    (hC : C.Computes (Unbounded.extInterpretation (modGate q)) (single (modGate p n))) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ)
    (hn : 100 * (((q - 1) * ℓ) ^ C.depth + 1) ^ 2 + (p - 1) ≤ n + 1) :
    2 * 2 ^ ℓ ≤ 5 * (p - 1) * 2 ^ (p - 1) * C.size := by
  classical
  let F := AlgebraicClosure (ZMod q)
  have _hpZ : NeZero (p : ZMod q) :=
    ⟨fun h => hpq.symm
      ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 ((ZMod.natCast_eq_zero_iff p q).1 h))⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p
  have hω0 : ω ≠ 0 := hω.ne_zero hp.out.ne_zero
  have hω1 : ω ≠ 1 := hω.ne_one hp.out.one_lt
  obtain ⟨Q, hQ, herr⟩ := exists_lowDegree_approx (R := F) hℓ C
  have heval : ∀ z, C.eval (Unbounded.extInterpretation (modGate q)) z 0 = modGate p n z :=
    fun z => congrFun (hC z) 0
  simp only [heval] at herr
  have hpow : 1 ≤ (((q - 1) * ℓ) ^ C.depth + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  let m := n - (p - 1)
  have hmn : m ≤ n := Nat.sub_le _ _
  have hm : 100 * (((q - 1) * ℓ) ^ C.depth + 1) ^ 2 ≤ m + 1 := by omega
  have hnm : n - m = p - 1 := by omega
  -- interpolate `x ↦ ω ^ weight x` from the `p - 1` padded evaluations `Q (padBits hmn r x)`
  let R : BitString m → F :=
    fun x => 1 + ∑ r ∈ Ico 1 p, (ω ^ (p - r) - 1) * (1 - Q (padBits hmn r x))
  have hR : R ∈ lowDegree F (Fin m) (((q - 1) * ℓ) ^ C.depth) := by
    have hR_eq : R = 1 + ∑ r ∈ Ico 1 p,
        (ω ^ (p - r) - 1) • (1 - fun x : BitString m => Q (padBits hmn r x)) := by
      funext x
      simp only [R, Pi.add_apply, Pi.one_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
    rw [hR_eq]
    refine Submodule.add_mem _ (one_mem_lowDegree _) (Submodule.sum_mem _ fun r _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (one_mem_lowDegree _)
      (comp_mem_lowDegree (bitVal_padBits_mem_lowDegree hmn r) hQ))
  set E := univ.filter fun z => Q z ≠ bitVal F (modGate p n z)
  have hagree : ∀ x : BitString m, (∀ r ∈ Ico 1 p, padBits hmn r x ∉ E) → R x = ω ^ weight x := by
    intro x hx
    have hQeq : ∀ r ∈ Ico 1 p, Q (padBits hmn r x) = bitVal F (modGate p n (padBits hmn r x)) := by
      intro r hr
      by_contra hne
      exact hx r hr (mem_filter.2 ⟨mem_univ _, hne⟩)
    set k := weight x % p
    have hk_lt : k < p := Nat.mod_lt _ hp.out.pos
    have hpow_w : ω ^ weight x = ω ^ k := by
      rw [← Nat.div_add_mod (weight x) p, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
    have hmod : ∀ r ∈ Ico 1 p,
        1 - Q (padBits hmn r x) = if (k + r) % p = 0 then 1 else 0 := by
      intro r hr
      have hr_le : r ≤ n - m := by
        have := (mem_Ico.1 hr).2
        omega
      rw [hQeq r hr, modGate_eq_decide_weight, weight_padBits hmn hr_le]
      have hdiv : (weight x + r) % p = (k + r) % p := by
        rw [Nat.add_mod, Nat.add_mod k r, Nat.mod_mod]
      rw [hdiv]
      split_ifs with h0
      · simp [h0]
      · simp [h0]
    rcases Nat.eq_zero_or_pos k with hk0 | _hk_pos
    · have hsum0 : ∑ r ∈ Ico 1 p, (ω ^ (p - r) - 1) * (1 - Q (padBits hmn r x)) = 0 :=
        sum_eq_zero fun r hr => by
          rw [hmod r hr]
          have hkr : (k + r) % p ≠ 0 := by
            rw [hk0, zero_add, Nat.mod_eq_of_lt (mem_Ico.1 hr).2]
            exact Nat.ne_of_gt (mem_Ico.1 hr).1
          rw [ite_eq_right_iff.2 fun h => (hkr h).elim, mul_zero]
      rw [show R x = 1 + _ from rfl, hsum0, add_zero, hpow_w, hk0, pow_zero]
    · have hr0 : p - k ∈ Ico 1 p := mem_Ico.2 ⟨by omega, by omega⟩
      have hsum : ∑ r ∈ Ico 1 p, (ω ^ (p - r) - 1) * (1 - Q (padBits hmn r x)) = ω ^ k - 1 := by
        rw [sum_eq_single (p - k)]
        · have hk0' : (k + (p - k)) % p = 0 := by
            rw [Nat.add_sub_of_le hk_lt.le, Nat.mod_self]
          rw [hmod (p - k) hr0, ite_eq_left_iff.2 fun h => (h hk0').elim, mul_one,
            Nat.sub_sub_self hk_lt.le]
        · intro r hr hne
          rw [hmod r hr]
          have hkr : (k + r) % p ≠ 0 := by
            intro h0
            obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h0
            have h1 := (mem_Ico.1 hr).1
            have h2 := (mem_Ico.1 hr).2
            by_cases ht1 : t = 1
            · subst ht1
              rw [mul_one] at ht
              omega
            · have ht0 : t ≠ 0 := fun h => by subst h; omega
              have hge : 2 * p ≤ p * t := (mul_comm 2 p) ▸ Nat.mul_le_mul_left p (by omega)
              omega
          rw [ite_eq_right_iff.2 fun h => (hkr h).elim, mul_zero]
        · exact fun abs => (abs hr0).elim
      rw [show R x = 1 + _ from rfl, hsum, add_sub_cancel, hpow_w]
  set A := univ.filter fun x : BitString m => R x = ω ^ weight x
  set B := univ.filter fun x : BitString m => R x ≠ ω ^ weight x
  have htotal : #A + #B = 2 ^ m := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hB : #B ≤ (p - 1) * #E := by
    have hsub : B ⊆ (Ico 1 p).biUnion fun r => univ.filter fun x => padBits hmn r x ∈ E := by
      intro x hx
      by_contra hnot
      simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and] at hnot
      exact (mem_filter.1 hx).2 (hagree x hnot)
    calc #B ≤ #((Ico 1 p).biUnion fun r => univ.filter fun x => padBits hmn r x ∈ E) :=
          card_le_card hsub
      _ ≤ ∑ r ∈ Ico 1 p, #(univ.filter fun x => padBits hmn r x ∈ E) := card_biUnion_le
      _ ≤ ∑ _ ∈ Ico 1 p, #E := sum_le_sum fun r _ =>
          card_le_card_of_injOn (padBits hmn r) (fun _ hx => (mem_filter.1 hx).2)
            (padBits_injective hmn r).injOn
      _ = (p - 1) * #E := by rw [sum_const, Nat.card_Ico, smul_eq_mul]
  have hA : 10 * #A ≤ 6 * 2 ^ m :=
    (Nat.mul_le_mul_left 10 (card_agree_phaseChar_le hω0 hω1 hR)).trans
      (ten_mul_card_filter_card_le_le m _ hm)
  simpa [hnm] using two_mul_two_pow_le_size_of_agreement_bound hmn hA (by omega) herr

/-- **`MOD_p` is not in AC⁰[q]** for any two distinct primes `p ≠ q` (Razborov–Smolensky). -/
theorem modGate_notMem_AC0Mod (hpq : p ≠ q) : Language.ofSlices (modGate p) ∉ AC0Mod q := by
  intro h
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  have hq1 := hq.out.two_le
  -- the size bound at lengths `100 (((q - 1) ℓ) ^ d + 1)² + (p - 1)` is a polynomial in `ℓ`
  have hpoly : PolynomiallyBounded fun ℓ =>
      5 * (p - 1) * 2 ^ (p - 1) * size (100 * (((q - 1) * ℓ) ^ d + 1) ^ 2 + (p - 1)) :=
    PolynomiallyBounded.mul (by fun_prop) (hsize.comp (by fun_prop))
  obtain ⟨ℓ, hlt, hℓ⟩ := (hpoly.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨C, hCc, hCd, hCs⟩ := hC (100 * (((q - 1) * ℓ) ^ d + 1) ^ 2 + (p - 1))
  rw [Language.slice_ofSlices] at hCc
  have hbase : 1 ≤ (q - 1) * ℓ :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hbound := two_mul_two_pow_le_size_of_computes_modGate hpq hCc hℓ (by
    have := Nat.pow_le_pow_right hbase hCd
    have := Nat.pow_le_pow_left (Nat.add_le_add_right this 1) 2
    omega)
  have : 5 * (p - 1) * 2 ^ (p - 1) * C.size ≤
      5 * (p - 1) * 2 ^ (p - 1) * size (100 * (((q - 1) * ℓ) ^ d + 1) ^ 2 + (p - 1)) :=
    Nat.mul_le_mul_left _ hCs
  omega

/-- The complement `(Language.ofSlices (modGate p))ᶜ` (accepting counts divisible by `p`) is
not in AC⁰[q] for any two distinct primes `p ≠ q`. -/
theorem compl_modGate_notMem_AC0Mod (hpq : p ≠ q) :
    (Language.ofSlices (modGate p))ᶜ ∉ AC0Mod q := fun h =>
  modGate_notMem_AC0Mod hpq
    (by simpa [AC0Mod, compl_compl] using ConstDepth.compl Unbounded.toExt h)

/-- **The Razborov–Smolensky size–depth tradeoff for parity.** A circuit of the AC⁰[p] basis of
depth `d` computing the parity of `n` bits, for an odd prime `p`, has size at least `2 ^ ℓ · 2 / 5`
whenever `100 (((p - 1) ℓ) ^ d + 1)² ≤ n + 1`. -/
theorem two_mul_two_pow_le_size_of_computes_parity (hp2 : p ≠ 2)
    {C : Circuit Unbounded.extSignature n 1}
    (hC : C.Computes (Unbounded.extInterpretation (modGate p)) (single (parity n))) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ)
    (hn : 100 * (((p - 1) * ℓ) ^ C.depth + 1) ^ 2 ≤ n + 1) : 2 * 2 ^ ℓ ≤ 5 * C.size := by
  classical
  let _ := invertibleTwo hp2
  obtain ⟨Q, hQ, herr⟩ := exists_lowDegree_approx (R := ZMod p) hℓ C
  have heval : ∀ x, C.eval (Unbounded.extInterpretation (modGate p)) x 0 = parity n x := fun x =>
    congrFun (hC x) 0
  simp only [heval] at herr
  set A := univ.filter fun x => Q x = bitVal (ZMod p) (parity n x)
  set E := univ.filter fun x => Q x ≠ bitVal (ZMod p) (parity n x)
  have htotal : #A + #E = 2 ^ n := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hA : 10 * #A ≤ 6 * 2 ^ n :=
    (Nat.mul_le_mul_left 10 (card_agree_parity_le hQ)).trans (ten_mul_card_filter_card_le_le n _ hn)
  simpa using two_mul_two_pow_le_size_of_agreement_bound (k := 1) le_rfl hA (by omega) herr

/-- **Parity is not in AC⁰[p]** for an odd prime `p` (Razborov–Smolensky), as the `q = 2` case
of `modGate_notMem_AC0Mod`. -/
theorem parity_notMem_AC0Mod (hp2 : p ≠ 2) : Language.ofSlices parity ∉ AC0Mod p := by
  have hpar : Language.ofSlices parity = Language.ofSlices (modGate 2) :=
    congrArg Language.ofSlices (funext modGate_two_eq_parity).symm
  rw [hpar]
  exact modGate_notMem_AC0Mod (p := 2) (q := p) hp2.symm

end LowerBounds

end Cslib.Circuits.Boolean.Smolensky
