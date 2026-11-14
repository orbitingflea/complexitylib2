/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.DataStructure.BallsToSlots.KickTree
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.KickTree.Facility
public import CslibFrontier.DataStructure.Dictionary.KickTree.Metadata
public import CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.Foundations.Data.Nat.IterLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Word-RAM Memory Layout for the `k`-Kick Tree Dynamic Dictionary

This module defines the word-level memory layout and pure array extraction functions for the
fixed-capacity STOC 2022 `k`-kick tree dynamic dictionary of Bender, Farach-Colton, J. Kuszmaul,
W. Kuszmaul, and Liu ([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`,
Sections 3–5):
- `KickTreeParams`: word width `w`, capacity bound `n_max`, universe `U ≤ 2 ^ w`, value bound
  `V ≤ 2 ^ w`, parameter `k ≥ 1`, and bounded kick limit.
- Memory offsets: `offSeeds`, `offQuot`, `offVal`, `offFourRussians`, `offFreeSlotTree`,
  `offFacility`, and `totalSpace`.
- Master space bound `totalSpace_le_kickTreeWords`: total memory footprint is bounded by the
  succinct word bound `kickTreeWords 8 2080 U V w k n_max`, which matches the optimal
  $\text{OPT} + O(n_{\max} \log^{(k)} n_{\max})$ bit-redundancy bound.
- Pure extraction functions for memory blocks (`quotAt`, `valAt`, `fourRussiansAt`, `freeSlotAt`,
  `cubbyAt`) with bit-width bounds and zero-initialization properties.

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 3.1 (printed pp. 8–10 / PDF pp. 9–11): $k$-kick tree hierarchy, kick limit $k + 1$,
    and priority kicks.
  - Section 4.1 (printed p. 24 / PDF p. 25): Method of Four Russians lookup tables on machine words.
  - Section 4.2–4.3 (printed pp. 24–26 / PDF pp. 25–27): mini-arrays and local query routers.
  - Section 5.1 (printed pp. 27–28 / PDF pp. 28–29): free-slot bitmap tree.
  - Section 5.2 (printed pp. 30–32 / PDF pp. 31–33): multi-tier cubbies and tail replacement.
  - Section 5.3 (printed pp. 34–36 / PDF pp. 33–35): quotienting and space bounds.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.KickTreeParams`: configuration parameters.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.offSeeds`, `offQuot`, `offVal`,
  `offFourRussians`, `offFreeSlotTree`, `offFacility`, `totalSpace`:
  word offsets and total footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.kickTreeWords`: succinct word space bound.
* `Cslib.DataStructure.Dictionary.WordRAM.KickTree.quotAt`, `valAt`, `fourRussiansAt`, `freeSlotAt`,
  `cubbyAt`: pure extraction functions for the memory blocks.

## Main results

* `totalSpace_le_kickTreeWords`: `totalSpace` is bounded by `kickTreeWords 8 2080 U V w k n_max`.
* `kickTreeWords_le_succinctWords`: specialization at $k = 2$ connects to `Dynamic.succinctWords`.
* `quotAt_lt`, `valAt_lt`, `fourRussiansAt_lt`, `freeSlotAt_lt`, `cubbyAt_lt`: bit-width bounds.
* `quotAt_zero_of_init`, `valAt_zero_of_init`, `fourRussiansAt_zero_of_init`,
  `freeSlotAt_zero_of_init`, `cubbyAt_zero_of_init`: extracted arrays are identically zero on
  zero-initialized memory.
* `arrays_congr_of_eq_on`: extracted arrays depend only on words in `[base, base + totalSpace)`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, M. Liu,
  *Dynamic Dictionaries with Worst-Case Optimal Operations and Space*]
  [BenderFarachColtonKuszmaulKuszmaulLiu2022], arXiv:2111.00602.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.KickTree

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.FeistelQuotient

/-! ### 1. Parameter record and memory offsets -/

/-- Word-RAM configuration parameters for the `k`-kick tree dynamic dictionary
([BenderFarachColtonKuszmaulKuszmaulLiu2022] Section 3.1, pp. 8–10 / PDF pp. 9–11). -/
structure KickTreeParams where
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Maximum dictionary capacity `n_max`. -/
  n_max : ℕ
  /-- Key universe size `U ≤ 2 ^ w`. -/
  U : ℕ
  /-- Value range bound `V ≤ 2 ^ w`. -/
  V : ℕ
  /-- Kick parameter `k ≥ 1`. -/
  k : ℕ
  /-- Worst-case kick limit (bounded by `k + 1` steps per Lemma 1 / Theorem 2). -/
  kickLimit : ℕ
deriving Repr, DecidableEq

/-- Default kick limit `k + 1` from Lemma 1 / Theorem 2 switching cost. -/
@[expose] def defaultKickLimit (k : ℕ) : ℕ := k + 1

/-- Canonical constructor for `KickTreeParams` from dimensions `w`, `n_max`, `U`, `V`, `k`. -/
@[expose] def mkKickTreeParams (w n_max U V k : ℕ) : KickTreeParams where
  w := w
  n_max := n_max
  U := U
  V := V
  k := k
  kickLimit := defaultKickLimit k

/-- 6-word encoding embedding for `KickTreeParams`. -/
def kickTreeParamsWords : KickTreeParams ↪ (Fin 6 → ℕ) where
  toFun p := ![p.w, p.n_max, p.U, p.V, p.k, p.kickLimit]
  inj' := by
    intro p₁ p₂ h
    have h0 := congrFun h ⟨0, by decide⟩
    have h1 := congrFun h ⟨1, by decide⟩
    have h2 := congrFun h ⟨2, by decide⟩
    have h3 := congrFun h ⟨3, by decide⟩
    have h4 := congrFun h ⟨4, by decide⟩
    have h5 := congrFun h ⟨5, by decide⟩
    cases p₁; cases p₂; dsimp at h0 h1 h2 h3 h4 h5
    rw [h0, h1, h2, h3, h4, h5]

instance : WordEncoding KickTreeParams := ⟨6, kickTreeParamsWords⟩

/-- Number of machine words reserved for hash seed storage. -/
@[expose] def seedWords : ℕ := 16

/-- Word offset of hash seeds relative to `base`. -/
@[expose] def offSeeds : ℕ := 0

/-- Word offset of `Quotients` array relative to `base`. -/
@[expose] def offQuot : ℕ := offSeeds + seedWords

/-- Word size of the bit-packed `Quotients` array. -/
@[expose] def quotWords (p : KickTreeParams) : ℕ :=
  packedWords p.n_max (fullQuotBits p.U p.n_max) p.w

/-- Word offset of `Values` array relative to `base`. -/
@[expose] def offVal (p : KickTreeParams) : ℕ :=
  offQuot + quotWords p

/-- Word size of the bit-packed `Values` array. -/
@[expose] def valWords (p : KickTreeParams) : ℕ :=
  packedWords p.n_max (valBits p.V) p.w

/-- Word offset of `FourRussians` lookup tables relative to `base`. -/
@[expose] def offFourRussians (p : KickTreeParams) : ℕ :=
  offVal p + valWords p

/-- Word size of the precomputed Four-Russians lookup tables (for 8-bit characters). -/
@[expose] def fourRussiansWords (p : KickTreeParams) : ℕ :=
  packedWords 256 8 p.w

/-- Word offset of `FreeSlotTree` bitmap relative to `base`. -/
@[expose] def offFreeSlotTree (p : KickTreeParams) : ℕ :=
  offFourRussians p + fourRussiansWords p

/-- Word size of the free-slot tree bitmap for `2 * n_max + 1` nodes. -/
@[expose] def freeSlotWords (p : KickTreeParams) : ℕ :=
  packedWords (2 * p.n_max + 1) 1 p.w

/-- Word offset of `Facility` multi-tier cubbies relative to `base`. -/
@[expose] def offFacility (p : KickTreeParams) : ℕ :=
  offFreeSlotTree p + freeSlotWords p

/-- Word size of the multi-tier facility cubby metadata block. -/
@[expose] def facilityWords (p : KickTreeParams) : ℕ :=
  packedWords (p.n_max + 1) (max (Nat.iterLog p.k p.n_max) 1) p.w

/-- Total word footprint of the `k`-kick tree dynamic dictionary starting at `base`. -/
@[expose] def totalSpace (p : KickTreeParams) : ℕ :=
  offFacility p + facilityWords p

/-! ### 2. Space bound theorems -/

/-- Total space decomposition identity. -/
theorem totalSpace_eq (p : KickTreeParams) :
    totalSpace p = seedWords + quotWords p + valWords p + fourRussiansWords p +
      freeSlotWords p + facilityWords p := by
  unfold totalSpace offFacility offFreeSlotTree offFourRussians offVal offQuot offSeeds seedWords
  omega

/-- The quotient block ends before the total space footprint. -/
theorem quot_end_le_totalSpace (p : KickTreeParams) :
    offQuot + quotWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offQuot offSeeds seedWords; omega

/-- The value block ends before the total space footprint. -/
theorem val_end_le_totalSpace (p : KickTreeParams) :
    offVal p + valWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offVal offQuot offSeeds seedWords; omega

/-- The Four-Russians block ends before the total space footprint. -/
theorem fourRussians_end_le_totalSpace (p : KickTreeParams) :
    offFourRussians p + fourRussiansWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offFourRussians offVal offQuot offSeeds seedWords; omega

/-- The free-slot tree block ends before the total space footprint. -/
theorem freeSlot_end_le_totalSpace (p : KickTreeParams) :
    offFreeSlotTree p + freeSlotWords p ≤ totalSpace p := by
  rw [totalSpace_eq]
  unfold offFreeSlotTree offFourRussians offVal offQuot offSeeds seedWords
  omega

/-- The facility block ends before the total space footprint. -/
theorem facility_end_le_totalSpace (p : KickTreeParams) :
    offFacility p + facilityWords p ≤ totalSpace p := by
  rw [totalSpace_eq]; unfold offFacility offFreeSlotTree offFourRussians offVal offQuot offSeeds
    seedWords; omega

/-- Succinct word-space bound for the `k`-kick tree dynamic dictionary:
`⌈(OPT(U, V, n_max) + C * n_max * max (Nat.iterLog k n_max) 1) / w⌉ + C₀`. -/
@[expose] def kickTreeWords (C C₀ U V w k n_max : ℕ) : ℕ :=
  (Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog k n_max) 1 + w - 1) / w + C₀

/-- Four-Russians table words are bounded by 2050 whenever `0 < w`. -/
theorem fourRussiansWords_le (p : KickTreeParams) (hw : 0 < p.w) :
    fourRussiansWords p ≤ 2050 := by
  unfold fourRussiansWords packedWords
  have : 2048 * 1 ≤ p.w * 2048 := by
    calc 2048 * 1 = 1 * 2048 := by ring
    _ ≤ p.w * 2048 := Nat.mul_le_mul_right 2048 hw
  have hle : 256 * 8 + p.w - 1 < p.w * 2049 := by omega
  have hlt : (256 * 8 + p.w - 1) / p.w < 2049 := Nat.div_lt_of_lt_mul hle
  omega

/-- Specialization: for `k = 2`, `kickTreeWords` is bounded by `Dynamic.succinctWords`
via `max_iterLog_two_le_logLogFactor`. -/
theorem kickTreeWords_le_succinctWords (C C₀ U V w n_max : ℕ) :
    kickTreeWords C C₀ U V w 2 n_max ≤ Dynamic.succinctWords C C₀ U V w n_max := by
  unfold kickTreeWords Dynamic.succinctWords
  have hle := BallsToSlots.max_iterLog_two_le_logLogFactor n_max
  have hmul : C * n_max * max (Nat.iterLog 2 n_max) 1 ≤
      C * n_max * Dynamic.logLogFactor n_max :=
    Nat.mul_le_mul_left _ hle
  have hadd : Dynamic.optBits U V n_max + C * n_max * max (Nat.iterLog 2 n_max) 1 + w - 1 ≤
      Dynamic.optBits U V n_max + C * n_max * Dynamic.logLogFactor n_max + w - 1 := by
    omega
  exact Nat.add_le_add_right (Nat.div_le_div_right hadd) _

/-- Master deterministic word-space bound: total memory footprint `totalSpace p` is at most
`kickTreeWords 8 2080 p.U p.V p.w p.k p.n_max` for all `0 < p.w`. -/
theorem totalSpace_le_kickTreeWords (p : KickTreeParams) (hw : 0 < p.w) :
    totalSpace p ≤ kickTreeWords 8 2080 p.U p.V p.w p.k p.n_max := by
  rw [totalSpace_eq]
  have h12 := packedWords_add_le p.n_max (fullQuotBits p.U p.n_max)
    p.n_max (valBits p.V) p.w
  have h123 := div_add_packedWords_le
    (p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V) 5
    (2 * p.n_max + 1) 1 p.w
  have h1234 := div_add_packedWords_le
    (p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V +
      (2 * p.n_max + 1) * 1) 8
    (p.n_max + 1) (max (Nat.iterLog p.k p.n_max) 1) p.w
  have hopt := mul_fullQuotBits_add_valBits_le_optBits p.U p.V p.n_max
  have h4R := fourRussiansWords_le p hw
  have hchain : packedWords p.n_max (fullQuotBits p.U p.n_max) p.w +
      packedWords p.n_max (valBits p.V) p.w +
      packedWords (2 * p.n_max + 1) 1 p.w +
      packedWords (p.n_max + 1) (max (Nat.iterLog p.k p.n_max) 1) p.w ≤
      (p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V +
        (2 * p.n_max + 1) * 1 + (p.n_max + 1) * (max (Nat.iterLog p.k p.n_max) 1) +
        p.w - 1) / p.w + 11 := by
    omega
  have hdiv_le :
      (p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V +
        (2 * p.n_max + 1) * 1 + (p.n_max + 1) * (max (Nat.iterLog p.k p.n_max) 1) +
        p.w - 1) / p.w ≤
      (Dynamic.optBits p.U p.V p.n_max +
        8 * p.n_max * max (Nat.iterLog p.k p.n_max) 1 + p.w - 1) / p.w + 2 := by
    by_cases hn : p.n_max = 0
    · obtain ⟨w, n_max, U, V, k, kickLimit⟩ := p
      dsimp only at *
      subst hn
      have hiter : Nat.iterLog k 0 = 0 := Nat.iterLog_zero_right k
      have hL1 : max (Nat.iterLog k 0) 1 = 1 := by rw [hiter]; rfl
      have hnum : 0 * fullQuotBits U 0 + 0 * valBits V +
          (2 * 0 + 1) * 1 + (0 + 1) * max (Nat.iterLog k 0) 1 + w - 1 = w + 1 := by
        rw [hL1]; omega
      rw [hnum]
      have hlt : (w + 1) / w < 3 := by
        have : w + 1 < w * 3 := by omega
        exact Nat.div_lt_of_lt_mul this
      have : (w + 1) / w ≤ 2 := by omega
      have hzero : Dynamic.optBits U V 0 + 8 * 0 * max (Nat.iterLog k 0) 1 + w - 1 =
          Dynamic.optBits U V 0 + w - 1 := by simp
      rw [hzero]
      exact le_trans (by omega) (Nat.le_add_left 2 _)
    · have hn1 : 1 ≤ p.n_max := Nat.pos_of_ne_zero hn
      set M := max (Nat.iterLog p.k p.n_max) 1
      have hM : 1 ≤ M := le_max_right _ _
      have hterm1 : p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V ≤
          Dynamic.optBits p.U p.V p.n_max + 2 * p.n_max := by
        rw [← Nat.mul_add]; exact hopt
      have h5M : 5 * p.n_max ≤ 5 * p.n_max * M := by
        have := Nat.mul_le_mul_left (5 * p.n_max) hM
        simpa using this
      have h2M : (p.n_max + 1) * M ≤ 2 * p.n_max * M := by
        have : p.n_max + 1 ≤ 2 * p.n_max := by omega
        exact Nat.mul_le_mul_right M this
      have hsum52 : 5 * p.n_max + (p.n_max + 1) * M ≤ 7 * p.n_max * M := by
        calc 5 * p.n_max + (p.n_max + 1) * M
          _ ≤ 5 * p.n_max * M + 2 * p.n_max * M := Nat.add_le_add h5M h2M
          _ = 7 * p.n_max * M := by ring
      have h78 : 7 * p.n_max * M ≤ 8 * p.n_max * M :=
        Nat.mul_le_mul_right M (by omega)
      have hle_num : p.n_max * fullQuotBits p.U p.n_max +
          p.n_max * valBits p.V +
          (2 * p.n_max + 1) * 1 + (p.n_max + 1) * M ≤
          Dynamic.optBits p.U p.V p.n_max + 8 * p.n_max * M := by
        calc p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V +
              (2 * p.n_max + 1) * 1 + (p.n_max + 1) * M
          _ ≤ Dynamic.optBits p.U p.V p.n_max + 2 * p.n_max + (2 * p.n_max + 1) +
              (p.n_max + 1) * M := by
            linarith [hterm1]
          _ = Dynamic.optBits p.U p.V p.n_max + (4 * p.n_max + 1) + (p.n_max + 1) * M := by ring
          _ ≤ Dynamic.optBits p.U p.V p.n_max + 5 * p.n_max + (p.n_max + 1) * M := by omega
          _ ≤ Dynamic.optBits p.U p.V p.n_max + 7 * p.n_max * M := by
            linarith [hsum52]
          _ ≤ Dynamic.optBits p.U p.V p.n_max + 8 * p.n_max * M := by
            linarith [h78]
      have hnum_le : p.n_max * fullQuotBits p.U p.n_max + p.n_max * valBits p.V +
          (2 * p.n_max + 1) * 1 + (p.n_max + 1) * M + p.w - 1 ≤
          Dynamic.optBits p.U p.V p.n_max + 8 * p.n_max * M + p.w - 1 := by omega
      have hdiv := Nat.div_le_div_right hnum_le (c := p.w)
      exact le_trans hdiv (Nat.le_add_right _ 2)
  unfold kickTreeWords quotWords valWords freeSlotWords facilityWords seedWords
  omega

/-! ### 3. Pure extraction functions -/

/-- Pure extraction function for `Quotients[idx]` (`0` for `idx ≥ p.n_max`). -/
@[expose] def quotAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.n_max then
    readPacked (base + offQuot) (fullQuotBits p.U p.n_max) p.w mem idx
  else 0

/-- Pure extraction function for `Values[idx]` (`0` for `idx ≥ p.n_max`). -/
@[expose] def valAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.n_max then
    readPacked (base + offVal p) (valBits p.V) p.w mem idx
  else 0

/-- Pure extraction function for `FourRussians` table entry `idx < 256` (`0` out of bounds). -/
@[expose] def fourRussiansAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < 256 then
    readPacked (base + offFourRussians p) 8 p.w mem idx
  else 0

/-- Pure extraction function for `FreeSlotTree` bitmap bit `idx < 2 * p.n_max + 1`. -/
@[expose] def freeSlotAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < 2 * p.n_max + 1 then
    readPacked (base + offFreeSlotTree p) 1 p.w mem idx
  else 0

/-- Pure extraction function for `Facility` cubby metadata entry `idx < p.n_max + 1`. -/
@[expose] def cubbyAt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < p.n_max + 1 then
    readPacked (base + offFacility p) (max (Nat.iterLog p.k p.n_max) 1) p.w mem idx
  else 0

/-! ### 4. Value range theorems -/

/-- Value range invariant for `quotAt`: every entry is `< 2 ^ fullQuotBits p.U p.n_max`. -/
theorem quotAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt base p mem idx < 2 ^ fullQuotBits p.U p.n_max := by
  unfold quotAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `valAt`: every entry is `< 2 ^ valBits p.V`. -/
theorem valAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    valAt base p mem idx < 2 ^ valBits p.V := by
  unfold valAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `fourRussiansAt`: every entry is `< 2 ^ 8`. -/
theorem fourRussiansAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    fourRussiansAt base p mem idx < 2 ^ 8 := by
  unfold fourRussiansAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `freeSlotAt`: every entry is `< 2 ^ 1`. -/
theorem freeSlotAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    freeSlotAt base p mem idx < 2 ^ 1 := by
  unfold freeSlotAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `cubbyAt`: every entry is `< 2 ^ max (Nat.iterLog p.k p.n_max) 1`. -/
theorem cubbyAt_lt (base : ℕ) (p : KickTreeParams) (mem : ℕ → ℕ) (idx : ℕ) :
    cubbyAt base p mem idx < 2 ^ max (Nat.iterLog p.k p.n_max) 1 := by
  unfold cubbyAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-! ### 5. Zero-initialization theorems -/

/-- On zero-initialized table memory `[base, base + totalSpace p)`, `quotAt` is identically zero. -/
theorem quotAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base ≤ a → a < base + totalSpace p → mem a = 0) :
    quotAt base p mem = fun _ => 0 := by
  funext idx
  unfold quotAt
  split_ifs with hidx
  · have hlt1 : wordOffset (fullQuotBits p.U p.n_max) p.w idx + 1 < quotWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := quot_end_le_totalSpace p
    exact readPacked_zero
      (hzero _ (by omega) (by omega))
      (hzero _ (by omega) (by omega))
  · rfl

/-- On zero-initialized table memory `[base, base + totalSpace p)`, `valAt` is identically zero. -/
theorem valAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base ≤ a → a < base + totalSpace p → mem a = 0) :
    valAt base p mem = fun _ => 0 := by
  funext idx
  unfold valAt
  split_ifs with hidx
  · have hlt1 : wordOffset (valBits p.V) p.w idx + 1 < valWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := val_end_le_totalSpace p
    exact readPacked_zero
      (hzero _ (by omega) (by omega))
      (hzero _ (by omega) (by omega))
  · rfl

/-- On zero-initialized table memory `[base, base + totalSpace p)`, `fourRussiansAt` is identically
zero. -/
theorem fourRussiansAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base ≤ a → a < base + totalSpace p → mem a = 0) :
    fourRussiansAt base p mem = fun _ => 0 := by
  funext idx
  unfold fourRussiansAt
  split_ifs with hidx
  · have hlt1 : wordOffset 8 p.w idx + 1 < fourRussiansWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := fourRussians_end_le_totalSpace p
    exact readPacked_zero
      (hzero _ (by omega) (by omega))
      (hzero _ (by omega) (by omega))
  · rfl

/-- On zero-initialized table memory `[base, base + totalSpace p)`, `freeSlotAt` is identically
zero. -/
theorem freeSlotAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base ≤ a → a < base + totalSpace p → mem a = 0) :
    freeSlotAt base p mem = fun _ => 0 := by
  funext idx
  unfold freeSlotAt
  split_ifs with hidx
  · have hlt1 : wordOffset 1 p.w idx + 1 < freeSlotWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := freeSlot_end_le_totalSpace p
    exact readPacked_zero
      (hzero _ (by omega) (by omega))
      (hzero _ (by omega) (by omega))
  · rfl

/-- On zero-initialized table memory `[base, base + totalSpace p)`, `cubbyAt` is identically
zero. -/
theorem cubbyAt_zero_of_init {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base ≤ a → a < base + totalSpace p → mem a = 0) :
    cubbyAt base p mem = fun _ => 0 := by
  funext idx
  unfold cubbyAt
  split_ifs with hidx
  · have hlt1 : wordOffset (max (Nat.iterLog p.k p.n_max) 1) p.w idx + 1 < facilityWords p :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hbound := facility_end_le_totalSpace p
    exact readPacked_zero
      (hzero _ (by omega) (by omega))
      (hzero _ (by omega) (by omega))
  · rfl

/-! ### 6. Memory congruence theorem -/

/-- If two memories agree on `[base, base + totalSpace p)`, they yield identical extraction
results for all five sub-arrays. -/
theorem arrays_congr_of_eq_on {base : ℕ} (p : KickTreeParams) (hw : 0 < p.w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + totalSpace p → mem₁ a = mem₂ a) :
    quotAt base p mem₁ = quotAt base p mem₂ ∧
      valAt base p mem₁ = valAt base p mem₂ ∧
      fourRussiansAt base p mem₁ = fourRussiansAt base p mem₂ ∧
      freeSlotAt base p mem₁ = freeSlotAt base p mem₂ ∧
      cubbyAt base p mem₁ = cubbyAt base p mem₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext idx; unfold quotAt; split_ifs with hidx
    · have hbound := quot_end_le_totalSpace p
      exact readPacked_congr (N := p.n_max) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [quotWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold valAt; split_ifs with hidx
    · have hbound := val_end_le_totalSpace p
      exact readPacked_congr (N := p.n_max) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [valWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold fourRussiansAt; split_ifs with hidx
    · have hbound := fourRussians_end_le_totalSpace p
      exact readPacked_congr (N := 256) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [fourRussiansWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold freeSlotAt; split_ifs with hidx
    · have hbound := freeSlot_end_le_totalSpace p
      exact readPacked_congr (N := 2 * p.n_max + 1) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [freeSlotWords] at hbound; omega)) hidx
    · rfl
  · funext idx; unfold cubbyAt; split_ifs with hidx
    · have hbound := facility_end_le_totalSpace p
      exact readPacked_congr (N := p.n_max + 1) hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by omega) (by dsimp [facilityWords] at hbound; omega)) hidx
    · rfl

end Cslib.DataStructure.Dictionary.WordRAM.KickTree
