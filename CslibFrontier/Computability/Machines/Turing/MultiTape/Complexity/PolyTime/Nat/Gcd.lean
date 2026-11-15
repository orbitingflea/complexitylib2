/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time greatest common divisor and modular inverse on binary naturals

Euclid's algorithm on the binary encoding `Turing.MultiTapeTM.encNat`. Each step
`Turing.MultiTapeTM.BinaryGcd.gcdStep` replaces `(a, b)` by `(b, a % b)` when `b ≠ 0` and fixes
`(a, 0)`. After the first step the state satisfies `b ≤ a`, and every subsequent step with `0 < b`
at least halves the product `a * b` (`BinaryGcd.gcd_product_halving`). Because
`a * b < 2 ^ (a.size + b.size)`, iterating `gcdStep` for
`BinaryGcd.gcdCount (a, b) = a.bits.length + b.bits.length + 1` steps reaches `(Nat.gcd a b, 0)`
(`BinaryGcd.iterate_gcdStep_eq`). At every intermediate step both components are at most
`max a b`, so the encoded pair length never exceeds a linear bound in the input length.

Tracking the unsigned Bézout coefficients modulo `m` alongside `(r₀, r₁)` yields the polynomial-time
modular inverse `Turing.MultiTapeTM.BinaryGcd.modInv`: each step `BinaryGcd.modInvStep m` updates
`(t₀, t₁)` in `{0, …, m - 1}` so that `a * t₀ ≡ r₀ [MOD m]` and `a * t₁ ≡ r₁ [MOD m]`. After
`gcdCount (m, a)` steps, `a * modInv a m ≡ Nat.gcd m a [MOD m]`, giving `a * modInv a m ≡ 1 [MOD m]`
whenever `Nat.Coprime a m`.

## Main definitions

* `Turing.MultiTapeTM.BinaryGcd.gcdStep`: one Euclidean remainder step on `ℕ × ℕ`.
* `Turing.MultiTapeTM.BinaryGcd.gcdCount`: the fuel `a.bits.length + b.bits.length + 1` sufficient
  to reach a zero remainder.
* `Turing.MultiTapeTM.BinaryGcd.modInv`: unsigned extended-Euclidean modular inverse modulo `m`.

## Main results

* `Turing.MultiTapeTM.BinaryGcd.gcd_product_halving`: when `0 < a ≤ b`, `2 * (a * (b % a)) ≤ a * b`.
* `Turing.MultiTapeTM.BinaryGcd.iterate_gcdStep_eq`: iterating `gcdStep` for `gcdCount p` steps
  produces `(Nat.gcd p.1 p.2, 0)`.
* `Turing.MultiTapeTM.BinaryGcd.mul_modInv_modEq_gcd`,
  `Turing.MultiTapeTM.BinaryGcd.mul_modInv_modEq_one`, `Turing.MultiTapeTM.BinaryGcd.modInv_lt`,
  `Turing.MultiTapeTM.BinaryGcd.modInv_eq_zmod_inv_val`:
  correctness, range bounds, and `ZMod` inverse bridge for `BinaryGcd.modInv`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd`, `.binary_gcd'`,
  `Turing.MultiTapeTM.ComputableInPolyTime.binary_modInv`, `.binary_modInv'`: polynomial-time
  certificates for `Nat.gcd` and `BinaryGcd.modInv` on `encNat`.

## References

* `gcd_product_halving` is adapted from OpenAI's formalization [OpenAI2026RationalHitting] at
  revision adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/BinaryFactorial.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Turing.MultiTapeTM.BinaryGcd

/-- Euclid's product is halved at every ordered step. -/
theorem gcd_product_halving {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (a * (b % a)) ≤ a * b := by
  have hr := Nat.mod_lt b ha
  have hq : 1 ≤ b / a := (Nat.one_le_div_iff ha).mpr hab
  have hid := Nat.mod_add_div b a
  have hmul := Nat.mul_le_mul_left a hq
  have hhalf : 2 * (b % a) ≤ b := by lia
  nlinarith

/-- One step of Euclid's algorithm: replace `(a, b)` by `(b, a % b)` while `b ≠ 0`. -/
def gcdStep (state : ℕ × ℕ) : ℕ × ℕ :=
  if state.2 = 0 then state else (state.2, state.1 % state.2)

/-- Number of Euclidean steps sufficient to reduce `(p.1, p.2)` to `(Nat.gcd p.1 p.2, 0)`. -/
def gcdCount (p : ℕ × ℕ) : ℕ :=
  p.1.bits.length + p.2.bits.length + 1

lemma gcd_gcdStep (s : ℕ × ℕ) : Nat.gcd (gcdStep s).1 (gcdStep s).2 = Nat.gcd s.1 s.2 := by
  unfold gcdStep
  split_ifs with h
  · rfl
  · calc Nat.gcd s.2 (s.1 % s.2)
        = Nat.gcd (s.1 % s.2) s.2 := Nat.gcd_comm _ _
      _ = Nat.gcd s.2 s.1 := (Nat.gcd_rec s.2 s.1).symm
      _ = Nat.gcd s.1 s.2 := Nat.gcd_comm _ _

lemma gcd_iterate_gcdStep (s : ℕ × ℕ) (i : ℕ) :
    Nat.gcd (gcdStep^[i] s).1 (gcdStep^[i] s).2 = Nat.gcd s.1 s.2 := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, gcd_gcdStep]

lemma max_gcdStep_le (s : ℕ × ℕ) : max (gcdStep s).1 (gcdStep s).2 ≤ max s.1 s.2 := by
  unfold gcdStep
  split_ifs with h
  · exact le_rfl
  · exact max_le (le_max_right s.1 s.2) ((Nat.mod_le s.1 s.2).trans (le_max_left s.1 s.2))

lemma max_iterate_gcdStep_le (s : ℕ × ℕ) (i : ℕ) :
    max (gcdStep^[i] s).1 (gcdStep^[i] s).2 ≤ max s.1 s.2 := by
  induction i generalizing s with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (gcdStep s)).trans (max_gcdStep_le s)

lemma snd_gcdStep_le_fst (s : ℕ × ℕ) : (gcdStep s).2 ≤ (gcdStep s).1 := by
  unfold gcdStep
  split_ifs with h
  · lia
  · exact (Nat.mod_lt s.1 (Nat.pos_of_ne_zero h)).le

lemma mul_gcdStep_le (s : ℕ × ℕ) : (gcdStep s).1 * (gcdStep s).2 ≤ s.1 * s.2 := by
  unfold gcdStep
  split_ifs with h
  · exact le_rfl
  · rw [Nat.mul_comm s.1 s.2]
    exact Nat.mul_le_mul_left s.2 (Nat.mod_le s.1 s.2)

lemma mul_gcdStep_two_le (s : ℕ × ℕ) (hs : s.2 ≤ s.1) :
    2 * ((gcdStep s).1 * (gcdStep s).2) ≤ s.1 * s.2 := by
  unfold gcdStep
  split_ifs with h
  · rw [h]
    simp
  · calc 2 * (s.2 * (s.1 % s.2))
        ≤ s.2 * s.1 := gcd_product_halving (Nat.pos_of_ne_zero h) hs
      _ = s.1 * s.2 := Nat.mul_comm s.2 s.1

lemma iterate_gcdStep_product_le (s : ℕ × ℕ) (hs : s.2 ≤ s.1) (k : ℕ) :
    (gcdStep^[k] s).2 ≤ (gcdStep^[k] s).1 ∧
      2 ^ k * ((gcdStep^[k] s).1 * (gcdStep^[k] s).2) ≤ s.1 * s.2 := by
  induction k generalizing s with
  | zero => simp [hs]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hord, hprod⟩ := ih (gcdStep s) (snd_gcdStep_le_fst s)
    refine ⟨hord, ?_⟩
    calc 2 ^ (k + 1) * ((gcdStep^[k] (gcdStep s)).1 * (gcdStep^[k] (gcdStep s)).2)
        = 2 * (2 ^ k * ((gcdStep^[k] (gcdStep s)).1 * (gcdStep^[k] (gcdStep s)).2)) := by ring
      _ ≤ 2 * ((gcdStep s).1 * (gcdStep s).2) := Nat.mul_le_mul_left 2 hprod
      _ ≤ s.1 * s.2 := mul_gcdStep_two_le s hs

lemma snd_iterate_gcdStep_gcdCount (p : ℕ × ℕ) :
    (gcdStep^[gcdCount p] p).2 = 0 := by
  unfold gcdCount
  rw [Function.iterate_add_apply, Function.iterate_one]
  set k := p.1.bits.length + p.2.bits.length
  obtain ⟨hord, hprod⟩ := iterate_gcdStep_product_le (gcdStep p) (snd_gcdStep_le_fst p) k
  have hmul : (gcdStep p).1 * (gcdStep p).2 < 2 ^ k := by
    refine (mul_gcdStep_le p).trans_lt ?_
    have h₁ : p.1 < 2 ^ p.1.bits.length :=
      Nat.size_eq_bits_len p.1 ▸ Nat.lt_size_self p.1
    have h₂ : p.2 < 2 ^ p.2.bits.length :=
      Nat.size_eq_bits_len p.2 ▸ Nat.lt_size_self p.2
    rw [show k = p.1.bits.length + p.2.bits.length from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul'' h₁ h₂
  by_contra hne
  have hpos : 1 ≤ (gcdStep^[k] (gcdStep p)).1 * (gcdStep^[k] (gcdStep p)).2 := by
    have : 1 ≤ (gcdStep^[k] (gcdStep p)).2 := Nat.pos_of_ne_zero hne
    nlinarith
  have hge : 2 ^ k ≤ 2 ^ k * ((gcdStep^[k] (gcdStep p)).1 * (gcdStep^[k] (gcdStep p)).2) :=
    Nat.le_mul_of_pos_right (2 ^ k) hpos
  lia

/-- Iterating `gcdStep` for `gcdCount p` steps reaches `(Nat.gcd p.1 p.2, 0)`. -/
theorem iterate_gcdStep_eq (p : ℕ × ℕ) :
    gcdStep^[gcdCount p] p = (Nat.gcd p.1 p.2, 0) := by
  have hsnd := snd_iterate_gcdStep_gcdCount p
  have hgcd := gcd_iterate_gcdStep p (gcdCount p)
  rw [hsnd, Nat.gcd_zero_right] at hgcd
  exact Prod.ext hgcd hsnd

/-- At every Euclidean step, the encoded pair has length at most
`3 * (encPair encNat encNat p).length`. -/
theorem length_encPair_iterate_gcdStep_le (p : ℕ × ℕ) (i : ℕ) :
    (encPair encNat encNat (gcdStep^[i] p)).length ≤ 3 * (encPair encNat encNat p).length := by
  have hmax := max_iterate_gcdStep_le p i
  have h₁ : (gcdStep^[i] p).1 ≤ max p.1 p.2 := (le_max_left _ _).trans hmax
  have h₂ : (gcdStep^[i] p).2 ≤ max p.1 p.2 := (le_max_right _ _).trans hmax
  have hm : (max p.1 p.2).size ≤ p.1.size + p.2.size := by grind
  have hs₁ : ((gcdStep^[i] p).1).size ≤ p.1.size + p.2.size := (Nat.size_le_size h₁).trans hm
  have hs₂ : ((gcdStep^[i] p).2).size ≤ p.1.size + p.2.size := (Nat.size_le_size h₂).trans hm
  simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len] at hs₁ hs₂ ⊢
  lia

/-- Initial state `((m, a), (0, if m ≤ 1 then 0 else 1))` for the unsigned extended-Euclidean
modular-inverse loop. -/
def modInvInit (a m : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((m, a), (0, if m ≤ 1 then 0 else 1))

/-- Next unsigned Bézout coefficient `(t₀ + m - (q * t₁) % m) % m` modulo `m`. -/
def modInvNext (m q t₀ t₁ : ℕ) : ℕ :=
  (t₀ + m - (q * t₁) % m) % m

/-- One step of the unsigned extended-Euclidean loop modulo `m`: advance the remainder pair
`(r₀, r₁)` by `gcdStep` and update `(t₀, t₁)` to `(t₁, modInvNext m (r₀ / r₁) t₀ t₁)`
while `r₁ ≠ 0`. -/
def modInvStep (m : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let r := s.1
  let t := s.2
  if r.2 = 0 then s
  else ((r.2, r.1 % r.2), (t.2, modInvNext m (r.1 / r.2) t.1 t.2))

/-- Unsigned modular inverse of `a` modulo `m`, computed by the extended Euclidean algorithm.
When `0 < m`, `a * modInv a m ≡ Nat.gcd m a [MOD m]` and `modInv a m < m`; when
`Nat.Coprime a m`, `a * modInv a m ≡ 1 [MOD m]`. -/
def modInv (a m : ℕ) : ℕ :=
  let t := ((modInvStep m)^[gcdCount (m, a)] (modInvInit a m)).2
  t.1

private lemma fst_modInvStep (m : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) :
    (modInvStep m s).1 = gcdStep s.1 := by
  dsimp only [modInvStep, gcdStep]
  split_ifs <;> rfl

private lemma fst_iterate_modInvStep (m : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) (i : ℕ) :
    ((modInvStep m)^[i] s).1 = gcdStep^[i] s.1 := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, fst_modInvStep]

private lemma snd_modInvStep_le (m : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) (h₁ : s.2.1 ≤ m) (h₂ : s.2.2 ≤ m) :
    (modInvStep m s).2.1 ≤ m ∧ (modInvStep m s).2.2 ≤ m := by
  dsimp only [modInvStep, modInvNext]
  split_ifs with hr
  · exact ⟨h₁, h₂⟩
  · refine ⟨h₂, ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hs₁ : s.2.1 = 0 := by lia
      have hs₂ : s.2.2 = 0 := by lia
      simp [hs₁, hs₂]
    · exact (Nat.mod_lt _ hm).le

private lemma snd_iterate_modInvStep_le (m : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁ : s.2.1 ≤ m) (h₂ : s.2.2 ≤ m) (i : ℕ) :
    ((modInvStep m)^[i] s).2.1 ≤ m ∧ ((modInvStep m)^[i] s).2.2 ≤ m := by
  induction i generalizing s with
  | zero => exact ⟨h₁, h₂⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h₁', h₂'⟩ := snd_modInvStep_le m s h₁ h₂
    exact ih (modInvStep m s) h₁' h₂'

private lemma snd_modInvInit_le (a m : ℕ) :
    (modInvInit a m).2.1 ≤ m ∧ (modInvInit a m).2.2 ≤ m := by
  unfold modInvInit
  split_ifs <;> lia

private lemma snd_modInvStep_lt {m : ℕ} (hm : 0 < m) (s : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁ : s.2.1 < m) (h₂ : s.2.2 < m) :
    (modInvStep m s).2.1 < m ∧ (modInvStep m s).2.2 < m := by
  dsimp only [modInvStep, modInvNext]
  split_ifs with hr
  · exact ⟨h₁, h₂⟩
  · exact ⟨h₂, Nat.mod_lt _ hm⟩

private lemma snd_iterate_modInvStep_lt {m : ℕ} (hm : 0 < m) (s : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁ : s.2.1 < m) (h₂ : s.2.2 < m) (i : ℕ) :
    ((modInvStep m)^[i] s).2.1 < m ∧ ((modInvStep m)^[i] s).2.2 < m := by
  induction i generalizing s with
  | zero => exact ⟨h₁, h₂⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h₁', h₂'⟩ := snd_modInvStep_lt hm s h₁ h₂
    exact ih (modInvStep m s) h₁' h₂'

/-- When `0 < m`, `modInv a m < m`. -/
theorem modInv_lt {a m : ℕ} (hm : 0 < m) : modInv a m < m := by
  have hinit : (modInvInit a m).2.1 < m ∧ (modInvInit a m).2.2 < m := by
    unfold modInvInit
    split_ifs <;> lia
  exact (snd_iterate_modInvStep_lt hm (modInvInit a m) hinit.1 hinit.2 (gcdCount (m, a))).1

/-- For every `a` and `m`, `modInv a m ≤ m`. -/
theorem modInv_le (a m : ℕ) : modInv a m ≤ m := by
  obtain ⟨h₁, h₂⟩ := snd_modInvInit_le a m
  exact (snd_iterate_modInvStep_le m (modInvInit a m) h₁ h₂ (gcdCount (m, a))).1

private lemma modEq_modInvStep {a m : ℕ} (hm : 0 < m) (s : (ℕ × ℕ) × (ℕ × ℕ))
    (hm₁ : a * s.2.1 ≡ s.1.1 [MOD m]) (hm₂ : a * s.2.2 ≡ s.1.2 [MOD m]) :
    a * (modInvStep m s).2.1 ≡ (modInvStep m s).1.1 [MOD m] ∧
      a * (modInvStep m s).2.2 ≡ (modInvStep m s).1.2 [MOD m] := by
  dsimp only [modInvStep, modInvNext]
  split_ifs with hr
  · exact ⟨hm₁, hm₂⟩
  · refine ⟨hm₂, ?_⟩
    set q := s.1.1 / s.1.2
    set u := (q * s.2.2) % m
    set t' := (s.2.1 + m - u) % m
    have hu_lt : u < m := Nat.mod_lt _ hm
    have hsub : (s.2.1 + m - u) + u = s.2.1 + m := Nat.sub_add_cancel (by lia)
    have ht' : t' ≡ s.2.1 + m - u [MOD m] := Nat.mod_modEq _ m
    have hu : u ≡ q * s.2.2 [MOD m] := Nat.mod_modEq _ m
    have hsum : a * t' + a * (q * s.2.2) ≡ a * (s.2.1 + m) [MOD m] := by
      calc a * t' + a * (q * s.2.2)
          ≡ a * (s.2.1 + m - u) + a * u [MOD m] :=
            (ht'.mul_left a).add (hu.symm.mul_left a)
        _ = a * ((s.2.1 + m - u) + u) := (Nat.mul_add a _ _).symm
        _ = a * (s.2.1 + m) := by rw [hsub]
    have hmul_q : a * (q * s.2.2) ≡ s.1.2 * q [MOD m] := by
      calc a * (q * s.2.2)
          = q * (a * s.2.2) := by ring
        _ ≡ q * s.1.2 [MOD m] := hm₂.mul_left q
        _ = s.1.2 * q := Nat.mul_comm q s.1.2
    have hrhs : a * (s.2.1 + m) ≡ s.1.1 % s.1.2 + s.1.2 * q [MOD m] := by
      have ham : a * m ≡ 0 [MOD m] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left m a)
      calc a * (s.2.1 + m)
          = a * s.2.1 + a * m := Nat.mul_add a s.2.1 m
        _ ≡ s.1.1 + 0 [MOD m] := hm₁.add ham
        _ = s.1.1 := Nat.add_zero s.1.1
        _ = s.1.1 % s.1.2 + s.1.2 * q := (Nat.mod_add_div s.1.1 s.1.2).symm
    have hboth : a * t' + s.1.2 * q ≡ s.1.1 % s.1.2 + s.1.2 * q [MOD m] := by
      calc a * t' + s.1.2 * q
          ≡ a * t' + a * (q * s.2.2) [MOD m] :=
            (Nat.ModEq.refl (a * t')).add hmul_q.symm
        _ ≡ a * (s.2.1 + m) [MOD m] := hsum
        _ ≡ s.1.1 % s.1.2 + s.1.2 * q [MOD m] := hrhs
    exact Nat.ModEq.add_right_cancel' (s.1.2 * q) hboth

private lemma modEq_iterate_modInvStep {a m : ℕ} (hm : 0 < m) (s : (ℕ × ℕ) × (ℕ × ℕ))
    (hm₁ : a * s.2.1 ≡ s.1.1 [MOD m]) (hm₂ : a * s.2.2 ≡ s.1.2 [MOD m]) (i : ℕ) :
    a * ((modInvStep m)^[i] s).2.1 ≡ ((modInvStep m)^[i] s).1.1 [MOD m] ∧
      a * ((modInvStep m)^[i] s).2.2 ≡ ((modInvStep m)^[i] s).1.2 [MOD m] := by
  induction i generalizing s with
  | zero => exact ⟨hm₁, hm₂⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hm₁', hm₂'⟩ := modEq_modInvStep hm s hm₁ hm₂
    exact ih (modInvStep m s) hm₁' hm₂'

/-- Extended Euclidean correctness modulo `m`: `a * modInv a m ≡ Nat.gcd m a [MOD m]`. -/
theorem mul_modInv_modEq_gcd (a : ℕ) {m : ℕ} (hm : 0 < m) :
    a * modInv a m ≡ Nat.gcd m a [MOD m] := by
  have hm₁ : a * (modInvInit a m).2.1 ≡ (modInvInit a m).1.1 [MOD m] := by
    change a * 0 ≡ m [MOD m]
    rw [Nat.mul_zero]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m)).symm
  have hm₂ : a * (modInvInit a m).2.2 ≡ (modInvInit a m).1.2 [MOD m] := by
    change a * (if m ≤ 1 then 0 else 1) ≡ a [MOD m]
    split_ifs with hle
    · have hm1 : m = 1 := by lia
      subst hm1
      exact Nat.modEq_one
    · rw [Nat.mul_one]
  have hiter := (modEq_iterate_modInvStep hm (modInvInit a m) hm₁ hm₂ (gcdCount (m, a))).1
  have hfst : ((modInvStep m)^[gcdCount (m, a)] (modInvInit a m)).1.1 = Nat.gcd m a := by
    rw [fst_iterate_modInvStep]
    change (gcdStep^[gcdCount (m, a)] (m, a)).1 = Nat.gcd m a
    rw [iterate_gcdStep_eq]
  simpa [modInv, hfst] using hiter

/-- Modular inverse correctness: when `Nat.Coprime a m`, `a * modInv a m ≡ 1 [MOD m]`. -/
theorem mul_modInv_modEq_one {a m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m) :
    a * modInv a m ≡ 1 [MOD m] := by
  have hgcd : Nat.gcd m a = 1 := by
    rw [Nat.gcd_comm]
    exact hcop
  simpa [hgcd] using mul_modInv_modEq_gcd a hm

/-- When `0 < m` and `Nat.Coprime a m`, `modInv a m` equals the canonical natural-number
representative `((a : ZMod m)⁻¹).val` of the modular inverse in `ZMod m`. -/
theorem modInv_eq_zmod_inv_val {a m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m) :
    modInv a m = ((a : ZMod m)⁻¹).val := by
  rcases m with _ | _ | m
  · exact absurd hm (Nat.lt_irrefl 0)
  · have hlt := modInv_lt (a := a) zero_lt_one
    have hval := ZMod.val_lt ((a : ZMod 1)⁻¹)
    lia
  · have hm1 : 1 < m + 2 := by lia
    have : Fact (1 < m + 2) := ⟨hm1⟩
    have hmul : (a : ZMod (m + 2)) * (modInv a (m + 2) : ZMod (m + 2)) = 1 := by
      have hmod := (ZMod.natCast_eq_natCast_iff (a * modInv a (m + 2)) 1 (m + 2)).mpr
        (mul_modInv_modEq_one (by lia) hcop)
      simpa using hmod
    have hinv := ZMod.inv_eq_of_mul_eq_one (m + 2) (a : ZMod (m + 2))
      (modInv a (m + 2) : ZMod (m + 2)) hmul
    rw [hinv, ZMod.val_natCast_of_lt (modInv_lt (by lia))]

/-- At every extended-Euclidean step, the encoded state has length at most
`9 * (encPair encNat encNat (a, m)).length`. -/
private theorem length_encPair_iterate_modInvStep_le (a m i : ℕ) :
    (encPair (encPair encNat encNat) (encPair encNat encNat)
      ((modInvStep m)^[i] (modInvInit a m))).length ≤
      9 * (encPair encNat encNat (a, m)).length := by
  set s := (modInvStep m)^[i] (modInvInit a m)
  have hfst : s.1 = gcdStep^[i] (m, a) := fst_iterate_modInvStep m (modInvInit a m) i
  have hmax := max_iterate_gcdStep_le (m, a) i
  have hr₁ : s.1.1 ≤ max m a := by rw [hfst]; exact (le_max_left _ _).trans hmax
  have hr₂ : s.1.2 ≤ max m a := by rw [hfst]; exact (le_max_right _ _).trans hmax
  have hm : (max m a).size ≤ m.size + a.size := by grind
  have hsr₁ : s.1.1.size ≤ m.size + a.size := (Nat.size_le_size hr₁).trans hm
  have hsr₂ : s.1.2.size ≤ m.size + a.size := (Nat.size_le_size hr₂).trans hm
  obtain ⟨hinit₁, hinit₂⟩ := snd_modInvInit_le a m
  obtain ⟨ht₁, ht₂⟩ := snd_iterate_modInvStep_le m (modInvInit a m) hinit₁ hinit₂ i
  have hst₁ : s.2.1.size ≤ m.size := Nat.size_le_size ht₁
  have hst₂ : s.2.2.size ≤ m.size := Nat.size_le_size ht₂
  simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len] at hsr₁ hsr₂ hst₁ hst₂ ⊢
  lia

attribute [irreducible] modInv

end Turing.MultiTapeTM.BinaryGcd

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Greatest common divisor of binary naturals via Euclid's algorithm. -/
@[fun_prop, program_certificate]
theorem binary_gcd : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)
    (encPair encNat encNat) encNat := by
  have hcount : ComputableInPolyTime BinaryGcd.gcdCount
      (encPair encNat encNat) encUnary := by
    unfold BinaryGcd.gcdCount
    fun_prop
  have hinit : ComputableInPolyTime (fun p => p)
      (encPair encNat encNat) (encPair encNat encNat) := by
    fun_prop
  have hstep : ComputableInPolyTime BinaryGcd.gcdStep
      (encPair encNat encNat) (encPair encNat encNat) := by
    unfold BinaryGcd.gcdStep
    fun_prop
  have hiter := iterate hcount hinit hstep
    (bound := fun p => 3 * (encPair encNat encNat p).length)
    ((PolyBounded.const 3).mul .self)
    (fun p i _ => BinaryGcd.length_encPair_iterate_gcdStep_le p i)
  have hfst := hiter.fst'
  simpa only [BinaryGcd.iterate_gcdStep_eq] using hfst

/-- Greatest common divisor of computed binary values, fixing their intermediate encodings for
proof search. -/
@[fun_prop, program_certificate]
theorem binary_gcd' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => Nat.gcd (left a) (right a)) input encNat :=
  binary_gcd.comp (hleft.prod hright)

private theorem computableInPolyTime_modInvNext {α : Type} {enc : α ↪ List Bool}
    {m q t₀ t₁ : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat)
    (hq : ComputableInPolyTime q enc encNat)
    (ht₀ : ComputableInPolyTime t₀ enc encNat)
    (ht₁ : ComputableInPolyTime t₁ enc encNat) :
    ComputableInPolyTime (fun x => BinaryGcd.modInvNext (m x) (q x) (t₀ x) (t₁ x)) enc encNat := by
  unfold BinaryGcd.modInvNext
  fun_prop

/-- Unsigned modular inverse of binary naturals via the extended Euclidean algorithm. -/
@[fun_prop, program_certificate]
theorem binary_modInv : ComputableInPolyTime (fun p : ℕ × ℕ => BinaryGcd.modInv p.1 p.2)
    (encPair encNat encNat) encNat := by
  have hnext := @computableInPolyTime_modInvNext
  have hpar : ComputableInPolyTime (fun p : ℕ × ℕ => p.2)
      (encPair encNat encNat) encNat := by
    fun_prop
  have hcount : ComputableInPolyTime (fun p : ℕ × ℕ => BinaryGcd.gcdCount (p.2, p.1))
      (encPair encNat encNat) encUnary := by
    unfold BinaryGcd.gcdCount
    fun_prop
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ => BinaryGcd.modInvInit p.1 p.2)
      (encPair encNat encNat) (encPair (encPair encNat encNat) (encPair encNat encNat)) := by
    unfold BinaryGcd.modInvInit
    fun_prop
  have hstep : ComputableInPolyTime
      (fun q : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) => BinaryGcd.modInvStep q.1 q.2)
      (encPair encNat (encPair (encPair encNat encNat) (encPair encNat encNat)))
      (encPair (encPair encNat encNat) (encPair encNat encNat)) := by
    unfold BinaryGcd.modInvStep
    fun_prop
  have hiter := iterateWith hpar hcount hinit hstep
    (bound := fun p => 9 * (encPair encNat encNat p).length)
    ((PolyBounded.const 9).mul .self)
    (fun p i _ => BinaryGcd.length_encPair_iterate_modInvStep_le p.1 p.2 i)
  unfold BinaryGcd.modInv
  exact hiter.snd'.fst'

/-- Unsigned modular inverse of computed binary values, fixing their intermediate encodings for
proof search. -/
@[fun_prop, program_certificate]
theorem binary_modInv' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => BinaryGcd.modInv (left a) (right a)) input encNat :=
  binary_modInv.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime

