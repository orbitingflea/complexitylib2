/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.MINKT
import Complexity.Computability.Kolmogorov.TimeBounded

/-!
Regression clients for time-bounded Kolmogorov complexity (`K^t`), Levin's `Kt`, the universal
multi-tape description method `universalTM`, `MINKT ∈ NP`, `MINKTAt ∈ NP`, and `GapMINKT`
(#798 M1a, #884 Item 1).
-/

namespace ComplexityTests.KolmogorovTimeBounded

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### Clock-preserving simulation of binary multi-tape machines -/

example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, Nonempty (Simulation (ofMultiTapeTM tm) universalTM c fun _ t => t) :=
  exists_simulation_ofMultiTapeTM tm

example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ (t : ℕ) (x : List Bool),
      universalTM.etimeBoundedComplexity t x ≤
        (ofMultiTapeTM tm).etimeBoundedComplexity t x + c :=
  exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM tm

/-! ### Basic properties of `K^t` and `Kt` -/

-- Antitonicity in the step bound `t` and time function `t`.
example (x : List Bool) : Antitone (timeBoundedAt · x) :=
  timeBoundedAt_antitone x

example (x : List Bool) : Antitone (timeBounded · x) :=
  timeBounded_antitone x

-- Trivial upper bound `K^t(x) ≤ |x| + copyOverhead` for `t(n) ≥ n + 1` (LP20 Fact 2.1).
example (x : List Bool) :
    timeBounded (fun n => n + 1) x ≤ (x.length + copyOverhead : ℕ) :=
  timeBounded_le (fun _ => le_rfl) x

-- `K(x) ≤ K^t(x)` for plain complexity under `universalTM` and `Partrec.universal`.
example (t : ℕ → ℕ) (x : List Bool) : plain x ≤ timeBounded t x :=
  plain_le_timeBounded t x

example : ∃ c : ℕ, ∀ (t : ℕ → ℕ) (n : ℕ),
    universal.ecomplexity n ≤ timeBounded t n.bits + c :=
  exists_ecomplexity_universal_le_timeBounded_bits

-- Bridge between `ℕ∞` and the `ℕ` infimum when a witness exists.
example (x : List Bool) :
    timeBoundedNat (fun n => n + 1) x =
      sInf {k : ℕ | ∃ p : List Bool, p.length = k ∧
        x ∈ (universalTM.run p).runFor (x.length + 1)} :=
  timeBoundedNat_eq_sInf (timeBounded_ne_top (t := fun n => n + 1) le_rfl)

-- Counting and incompressibility for `K^t`.
example (t : ℕ → ℕ) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ timeBounded t x :=
  exists_length_eq_le_timeBounded t n

example (t : ℕ → ℕ) (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ timeBounded t x}.ncard +
      2 ^ (n - c) :=
  two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add t n c

-- Levin's `Kt` on a concrete 4-bit string (`|[1, 0, 1, 0]| = 4`, `⌈log₂ 5⌉ = 3`).
example : levinKt [true, false, true, false] ≤ (4 + copyOverhead + 3 : ℕ) :=
  levinKt_le_length_add [true, false, true, false]

example : levinKtNat [true, false, true, false] ≤ 4 + copyOverhead + 3 :=
  levinKtNat_le_iff.mpr (levinKt_le_length_add [true, false, true, false])

example (x : List Bool) (k : ℕ) :
    levinKtNat x ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k :=
  levinKtNat_le_iff.trans levinKt_le_natCast_iff

/-! ### Non-vacuous `MINKT`, `MINKTAt`, and `GapMINKT` instances -/

-- Concrete `MINKT` yes-instance `⟨x, |x| + 1, |x| + copyOverhead⟩`.
example (x : List Bool) :
    (⟨x, x.length + 1, x.length + copyOverhead⟩ : MINKT.Instance) ∈ MINKT :=
  MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl)

example : (⟨[true, false, true], 4, 3 + copyOverhead⟩ : MINKT.Instance) ∈ MINKT :=
  MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl)

-- Every string belongs to `MINKTAt (n ↦ n + 1) (n ↦ n + copyOverhead)`.
example (x : List Bool) :
    x ∈ MINKTAt (fun n => n + 1) (fun n => n + copyOverhead) :=
  timeBounded_le (fun _ => le_rfl) x

-- Concrete `MINKT` no-instance from an incompressible string of length `s + 1`.
example (t s : ℕ) :
    ∃ x : List Bool, x.length = s + 1 ∧ (⟨x, t, s⟩ : MINKT.Instance) ∉ MINKT := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded (s + 1)
  refine ⟨x, hx, ?_⟩
  rw [MINKT.mk_mem_iff, not_le]
  have hle : ((s + 1 : ℕ) : ℕ∞) ≤ timeBoundedAt t x := hall (fun _ => t)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self s)).trans_le hle

-- Non-trivial `GapMINKT` with strict gap `σ(n, s) = 2 * s + 1` and `τ(n, t) = 2 * t + 2`:
-- exhibits both a concrete yes-instance and a no-instance of length `2 * s + 2`.
example :
    let P := GapMINKT (fun _ s => 2 * s + 1) (fun _ t => 2 * t + 2)
    (⟨[true, false], 3, 2 + copyOverhead⟩ : MINKT.Instance) ∈ P.yes ∧
      ∀ t s : ℕ, ∃ x : List Bool, x.length = 2 * s + 2 ∧
        (⟨x, t, s⟩ : MINKT.Instance) ∈ P.no := by
  intro P
  have hno_eq : P.no = GapMINKT.no (fun _ s => 2 * s + 1) (fun _ t => 2 * t + 2) :=
    GapMINKT.no_eq (fun _ s => by omega) (fun _ t => by omega)
  refine ⟨MINKT.mk_mem_iff.mpr (timeBoundedAt_le_length_add le_rfl), fun t s => ?_⟩
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded (2 * s + 2)
  refine ⟨x, hx, ?_⟩
  rw [hno_eq, GapMINKT.mem_no_iff]
  dsimp only
  have hle : ((2 * s + 2 : ℕ) : ℕ∞) ≤ timeBoundedAt (2 * t + 2) x :=
    hall (fun _ => 2 * t + 2)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (2 * s + 1))).trans_le hle

example : MINKT ∈ NP MINKT.enc :=
  MINKT.mem_NP

example (p q : Polynomial ℕ) : MINKTAt p.eval q.eval ∈ NP encBits :=
  MINKTAt.mem_NP_polynomial₂ p q

example : GapMINKT (fun _ s => s) (fun _ t => t) = PromiseProblem.ofSet MINKT :=
  GapMINKT.id_eq

/-! ### Axiom guards -/

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_simulation_ofMultiTapeTM' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_simulation_ofMultiTapeTM

/--
info: 'Cslib.Kolmogorov.timeBounded_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms timeBounded_le

/--
info: 'Cslib.Kolmogorov.exists_ecomplexity_universal_le_timeBounded' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_ecomplexity_universal_le_timeBounded

/--
info: 'Cslib.Kolmogorov.MINKT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MINKT.mem_NP

/--
info: 'Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MINKTAt.mem_NP_polynomial₂

end ComplexityTests.KolmogorovTimeBounded
