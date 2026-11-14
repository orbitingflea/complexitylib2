/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpHashProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Subroutines for the Small Regime and CSR Fallback Operations

This module builds parameter-free `Memory.Prog` subroutines certified over `Basis.exact` (via
`realize` and `Realizes.iterate₀`) for:

1. **Small regime (`n_max < whpThreshold c`)**: `smallStepOpGenProg`, executing `smallQuery`,
   `smallInsert`, and `smallDelete` in `≤ 4 * whpThreshold c + 16` (`O_c(1)`) worst-case memory
   operations while preserving `SmallMemRep` and leaving memory outside
   `[base, base + smallSpaceWhp U V w n_max)` untouched.
2. **CSR fallback operations (`whpThreshold c ≤ n_max`)**: `csrStepOpGenProg`, executing
   `csrStepOp c U n_max θ.1 csr op` (`csrQuery`, `csrInsert`, `csrDelete`) fault-free for **every**
   seed `θ : SeedWhp c U n_max` while preserving `CsrMemRep` and `SeedWhpMemRep`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.encodeOpWhp`, `encodeOptRes`: canonical word
  encodings of `Dynamic.Op U` and `Option ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.smallStepOpGenProg`, `smallOpCostWhp`:
  certified small-regime `Memory.Prog` operation dispatcher and `c`-only cost bound.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.csrStepOpGenProg`: certified CSR fallback
  `Memory.Prog` operation dispatcher.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_smallStepOpGen`,
  `smallStepOpGenProg_spec`: `Realizes .exact` certificate and exact `SmallMemRep` specification.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_csrStepOpGen`,
  `csrStepOpGenProg_spec`: `Realizes .exact` certificate and exact `CsrMemRep` specification.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Canonical Operation / Result Word Encodings and Packed Helpers -/

/-- Canonical `(opTag, (u_val, v_val))` tuple for `op : Dynamic.Op U`
(`0` = `query`, `1` = `insert`, `2` = `delete`). -/
@[expose] def encodeOpWhp {U : ℕ} : Dynamic.Op U → ℕ × (ℕ × ℕ)
  | .query u => (0, (u.val, 0))
  | .insert u v => (1, (u.val, v))
  | .delete u => (2, (u.val, 0))

/-- Canonical `(resTag, resVal)` pair for `Option ℕ` (`(0, 0)` = `none`, `(1, v)` = `some v`). -/
@[expose] def encodeOptRes : Option ℕ → ℕ × ℕ
  | none => (0, 0)
  | some v => (1, v)

/-- `c`-only worst-case `memoryCost` bound for any small-regime operation
(`n_max < whpThreshold c`). -/
@[expose] def smallOpCostWhp (c : ℕ) : ℕ :=
  4 * whpThreshold c + 16

@[simp]
private theorem runClient_pure_prog {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).runClient s (pure x : Memory.Prog α) = (x, s, []) := rfl

@[simp]
private theorem clientResult_pure_prog {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pure x : Memory.Prog α) = x := rfl

@[simp]
private theorem clientState_pure_prog {α : Type} (x : α) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pure x : Memory.Prog α)).2.1 = s := rfl

private theorem clientState_pure_rw {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (pure x : Memory.Prog α) = s := rfl

private theorem clientState_bind_prog {α β : Type} (p : Memory.Prog α) (k : α → Memory.Prog β)
    (s : Memory.State) :
    ((Memory.spec 0).runClient s (p >>= k)).2.1 =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) :=
  StateTransitionSpec.fst_snd_runClient_bind (D := Memory.spec 0) p k s

private theorem clientState_bind_rw {α β : Type} (p : Memory.Prog α) (k : α → Memory.Prog β)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (p >>= k) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) :=
  StateTransitionSpec.clientState_bind (D := Memory.spec 0) p k s

private theorem clientResult_bind_prog {α β : Type} (p : Memory.Prog α) (k : α → Memory.Prog β)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (p >>= k) =
      (Memory.spec 0).clientResult ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) :=
  StateTransitionSpec.clientResult_bind (D := Memory.spec 0) p k s

private theorem clientResult_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedGenProg (((base, offset), (k, w)), idx)) =
      readPacked (base + offset) k w s.mem idx :=
  clientResult_readPackedProg _ _ _ _ _ _

private theorem clientState_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (readPackedGenProg (((base, offset), (k, w)), idx))).2.1 = s :=
  rfl

private theorem clientState_readPackedGen_rw (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedGenProg (((base, offset), (k, w)), idx)) = s :=
  rfl

private theorem memoryCost_readPackedGen (base offset k w idx : ℕ) (s : Memory.State) :
    memoryCost (readPackedGenProg (((base, offset), (k, w)), idx)) s = 2 := rfl

private theorem clientState_writePackedGen (base offset k w idx val : ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (writePackedGenProg ((((base, offset), (k, w)), idx), val))).2.1 =
      { mem := writePacked (base + offset) k w s.mem idx val,
        frontier := s.frontier } := rfl

private theorem memoryCost_writePackedGen (base offset k w idx val : ℕ) (s : Memory.State) :
    memoryCost (writePackedGenProg ((((base, offset), (k, w)), idx), val)) s = 4 := rfl

private theorem val_lt_two_pow_valBits {V v : ℕ} (hv : v < V) : v < 2 ^ valBits V :=
  hv.trans_le (Nat.le_pow_clog Nat.one_lt_two V)

private theorem key_lt_two_pow_keyBits {U u : ℕ} (hu : u < U) : u < 2 ^ keyBits U :=
  hu.trans_le (Nat.le_pow_clog Nat.one_lt_two U)

private theorem quot_lt_two_pow_quotBits {U n_max u : ℕ} (hnU : n_max ≤ U) (hu : u < U) :
    keyQuotient (bWhp n_max) u < 2 ^ quotBitsWhp U n_max := by
  unfold keyQuotient
  refine Nat.div_lt_of_lt_mul ?_
  rw [mul_comm, ← Nat.pow_add, quotBitsWhp_add_bWhp hnU]
  exact key_lt_two_pow_keyBits hu

/-! ## Section 2: Small-Regime `Memory.Prog` Subroutines (`n_max < whpThreshold c`) -/

/-- Compact 8-word runtime parameter bundle for the small regime:
`(((base, w), (n_max, keyBits)), ((valBits, offPres), (offKeys, offVals)))`. -/
abbrev SmallRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))

@[expose] def srBase (srt : SmallRt) : ℕ := srt.1.1.1
@[expose] def srW (srt : SmallRt) : ℕ := srt.1.1.2
@[expose] def srNMax (srt : SmallRt) : ℕ := srt.1.2.1
@[expose] def srKeyBits (srt : SmallRt) : ℕ := srt.1.2.2
@[expose] def srValBits (srt : SmallRt) : ℕ := srt.2.1.1
@[expose] def srOffPres (srt : SmallRt) : ℕ := srt.2.1.2
@[expose] def srOffKeys (srt : SmallRt) : ℕ := srt.2.2.1
@[expose] def srOffVals (srt : SmallRt) : ℕ := srt.2.2.2

/-- Pure constructor for `SmallRt`. -/
@[expose] def mkSmallRt (U V w n_max base : ℕ) : SmallRt :=
  (((base, w), (n_max, keyBits U)),
   ((valBits V, offSmallPres), (offSmallKeys U w n_max, offSmallVals U w n_max)))

@[simp] private theorem srBase_mk (U V w n_max base : ℕ) :
    srBase (mkSmallRt U V w n_max base) = base := rfl
@[simp] private theorem srW_mk (U V w n_max base : ℕ) :
    srW (mkSmallRt U V w n_max base) = w := rfl
@[simp] private theorem srNMax_mk (U V w n_max base : ℕ) :
    srNMax (mkSmallRt U V w n_max base) = n_max := rfl
@[simp] private theorem srKeyBits_mk (U V w n_max base : ℕ) :
    srKeyBits (mkSmallRt U V w n_max base) = keyBits U := rfl
@[simp] private theorem srValBits_mk (U V w n_max base : ℕ) :
    srValBits (mkSmallRt U V w n_max base) = valBits V := rfl
@[simp] private theorem srOffPres_mk (U V w n_max base : ℕ) :
    srOffPres (mkSmallRt U V w n_max base) = offSmallPres := rfl
@[simp] private theorem srOffKeys_mk (U V w n_max base : ℕ) :
    srOffKeys (mkSmallRt U V w n_max base) = offSmallKeys U w n_max := rfl
@[simp] private theorem srOffVals_mk (U V w n_max base : ℕ) :
    srOffVals (mkSmallRt U V w n_max base) = offSmallVals U w n_max := rfl

/-- Parameter-free small-regime `SmallRt` envelope. -/
@[expose] def SmallRtEnvGen (w : ℕ) (srt : SmallRt) : Prop :=
  ∃ c U V w₀ n_max,
    WhpSmallEnv c U V w₀ n_max w (srBase srt) ∧
    srt = mkSmallRt U V w₀ n_max (srBase srt)

/-- Extract `SmallRt` from `(cp, base)` in 0 memory operations. -/
@[irreducible] def extractSmallRtGenProg (d : WhpCoreParams × ℕ) : Memory.Prog SmallRt := do
  let cp := d.1
  let base ← pure d.2
  pure (((base, wpW cp), (wpNMax cp, wpKeyBits cp)),
    ((wpValBits cp, wpOffSmallPres cp), (wpOffSmallKeys cp, wpOffSmallVals cp)))

theorem realizes_extractSmallRtGen :
    Realizes .exact extractSmallRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := SmallRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold extractSmallRtGenProg
  realize

theorem extractSmallRtGenProg_spec {c U V w n_max base : ℕ} (hsm : n_max < whpThreshold c)
    (s : Memory.State) :
    let prog := extractSmallRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkSmallRt U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidWhpProg w (base + smallSpaceWhp U V w n_max) s prog := by
  dsimp only
  unfold extractSmallRtGenProg mkSmallRt
  simp only [pure_bind, wp_small_w hsm, wp_small_nMax hsm, wp_small_keyBits hsm,
    wp_small_valBits hsm, wp_small_offPres hsm, wp_small_offKeys hsm, wp_small_offVals hsm]
  exact ⟨rfl, rfl, rfl, validWhpProg_pure _⟩

section SmallSafety

private theorem small_seg_bounds (U V w n_max : ℕ) :
    offSmallPres + packedWords n_max 1 w ≤ smallSpaceWhp U V w n_max ∧
    offSmallKeys U w n_max + packedWords n_max (keyBits U) w ≤ smallSpaceWhp U V w n_max ∧
    offSmallVals U w n_max + packedWords n_max (valBits V) w ≤ smallSpaceWhp U V w n_max ∧
    hdrMode < offSmallPres ∧
    offSmallPres + packedWords n_max 1 w ≤ offSmallKeys U w n_max ∧
    offSmallKeys U w n_max + packedWords n_max (keyBits U) w ≤ offSmallVals U w n_max := by
  have hend := smallOffsets_eq U V w n_max
  have h1 : offSmallPres = 32 := rfl
  have h2 : offSmallKeys U w n_max = offSmallPres + packedWords n_max 1 w := rfl
  have h3 : offSmallVals U w n_max = offSmallKeys U w n_max + packedWords n_max (keyBits U) w :=
    rfl
  dsimp only [hdrMode]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem small_pres_safe {c U V w n_max base idx : ℕ}
    (henv : WhpSmallEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ 1 ≤ w ∧ idx < N ∧
      Fits w (base + offSmallPres + packedWords N 1 w) := by
  rcases henv with ⟨_, hw, _, hsm, _, _, _, hfit⟩
  rw [whpSpace, ite_eq_left hsm] at hfit
  have hb := (small_seg_bounds U V w n_max).1
  exact ⟨n_max, rfl, hw, hw, hidx, hfit.of_le (by omega)⟩

private theorem small_keys_safe {c U V w n_max base idx : ℕ}
    (henv : WhpSmallEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ keyBits U ≤ w ∧ idx < N ∧
      Fits w (base + offSmallKeys U w n_max + packedWords N (keyBits U) w) := by
  rcases henv with ⟨_, hw, _, hsm, _, hU, _, hfit⟩
  rw [whpSpace, ite_eq_left hsm] at hfit
  have hb := (small_seg_bounds U V w n_max).2.1
  exact ⟨n_max, rfl, hw, keyBits_le_w hU, hidx, hfit.of_le (by omega)⟩

private theorem small_vals_safe' {c U V w n_max base idx : ℕ}
    (henv : WhpSmallEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ valBits V ≤ w ∧ idx < N ∧
      Fits w (base + offSmallVals U w n_max + packedWords N (valBits V) w) := by
  rcases henv with ⟨_, hw, _, hsm, _, _, hV, hfit⟩
  rw [whpSpace, ite_eq_left hsm] at hfit
  have hb := (small_seg_bounds U V w n_max).2.2.1
  exact ⟨n_max, rfl, hw, valBits_le_w hV, hidx, hfit.of_le (by omega)⟩

private theorem to_true_exists {w : ℕ} {P : ℕ → Prop} (h : ∃ N, w = w ∧ P N) :
    ∃ N, True ∧ P N :=
  let ⟨N, _, hP⟩ := h
  ⟨N, trivial, hP⟩

private theorem small_seg_base_bounds (base U V w n_max : ℕ) :
    base + offSmallPres + packedWords n_max 1 w ≤ base + smallSpaceWhp U V w n_max ∧
    base + offSmallKeys U w n_max + packedWords n_max (keyBits U) w ≤
      base + smallSpaceWhp U V w n_max ∧
    base + offSmallVals U w n_max + packedWords n_max (valBits V) w ≤
      base + smallSpaceWhp U V w n_max := by
  have hb := small_seg_bounds U V w n_max
  exact ⟨by omega, by omega, by omega⟩

end SmallSafety

/-- Single iteration of `smallScan` (`d = ((srt, u_val), (i, (f1, free1)))`). -/
@[irreducible] def smallScanStepProg (d : (SmallRt × ℕ) × (ℕ × (ℕ × ℕ))) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let srt := d.1.1
  let u_val ← pure d.1.2
  let i ← pure d.2.1
  let f1 ← pure d.2.2.1
  let free1 ← pure d.2.2.2
  let one_v ← pure 1
  let zero_v ← pure 0
  let p ← readPackedGenProg (((srBase srt, srOffPres srt), (one_v, srW srt)), i)
  let ki ← readPackedGenProg (((srBase srt, srOffKeys srt), (srKeyBits srt, srW srt)), i)
  let i1 ← pure (i + one_v)
  if p = zero_v then
    if free1 = zero_v then
      pure (i1, (f1, i1))
    else
      pure (i1, (f1, free1))
  else
    if ki = u_val then
      if f1 = zero_v then
        pure (i1, (i1, free1))
      else
        pure (i1, (f1, free1))
    else
      pure (i1, (f1, free1))

/-- Precondition for `smallScanStepProg`. -/
@[expose] def SmallScanStepPre (w : ℕ) (d : (SmallRt × ℕ) × (ℕ × (ℕ × ℕ)))
    (_s : Memory.State) : Prop :=
  SmallRtEnvGen w d.1.1 ∧
  d.2.1 < srNMax d.1.1 ∧
  d.2.2.1 ≤ srNMax d.1.1 ∧
  d.2.2.2 ≤ srNMax d.1.1

private theorem memoryCost_smallScanStepProg (d : (SmallRt × ℕ) × (ℕ × (ℕ × ℕ)))
    (s : Memory.State) :
    memoryCost (smallScanStepProg d) s = 4 := by
  unfold smallScanStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedGen]
  split_ifs <;> rfl

private theorem memoryCost_smallScanStepProg_pos (d : (SmallRt × ℕ) × (ℕ × (ℕ × ℕ)))
    (s : Memory.State) :
    1 ≤ memoryCost (smallScanStepProg d) s := by
  rw [memoryCost_smallScanStepProg]; decide

theorem realizes_smallScanStep :
    Realizes .exact smallScanStepProg
      (WordEncoding.encode (α := (SmallRt × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      SmallScanStepPre
      (fun _ _ => 0) := by
  unfold smallScanStepProg
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨srt, u_val⟩, i, f1, free1⟩
    try clear hwords hmem
    dsimp only [SmallScanStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_srt⟩, hi_lt, hf1_le, hfr1_le⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hN_eq : srNMax srt = n_max := by rw [heq_srt]; rfl
    have hW_eq : srW srt = w := by rw [heq_srt]; rfl
    have hKB_eq : srKeyBits srt = keyBits U := by rw [heq_srt]; rfl
    have hOP_eq : srOffPres srt = offSmallPres := by rw [heq_srt]; rfl
    have hOK_eq : srOffKeys srt = offSmallKeys U w n_max := by rw [heq_srt]; rfl
    rw [hN_eq] at hi_lt hf1_le hfr1_le
    dsimp only [srBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact (by omega : i + 1 ≤ n_max).trans_lt hn_lt
    | (rw [hW_eq, hOP_eq]; exact small_pres_safe henv hi_lt)
    | (rw [hW_eq, hKB_eq, hOK_eq]; exact small_keys_safe henv hi_lt)
  )

/-- Loop wrapper for `iterate smallScanStepProg`. -/
@[expose] def smallScanLoopProg (d : ((SmallRt × ℕ) × (ℕ × (ℕ × ℕ))) × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) :=
  iterate smallScanStepProg d.1.1 d.2 d.1.2

private theorem smallScanLoopProg_zero (env : SmallRt × ℕ) (acc : ℕ × (ℕ × ℕ)) :
    smallScanLoopProg ((env, acc), 0) = pure acc := rfl

private theorem smallScanLoopProg_succ (env : SmallRt × ℕ) (acc : ℕ × (ℕ × ℕ)) (m : ℕ) :
    smallScanLoopProg ((env, acc), m + 1) =
      (smallScanStepProg (env, acc) >>= fun acc' => smallScanLoopProg ((env, acc'), m)) := rfl

theorem realizes_smallScanLoop :
    Realizes .exact smallScanLoopProg
      (WordEncoding.encode (α := ((SmallRt × ℕ) × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d s => iterationSafe smallScanStepProg SmallScanStepPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := SmallRt × ℕ))
    (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
    realizes_smallScanStep
    memoryCost_smallScanStepProg_pos

private theorem smallScanStepProg_step {U V w n_max base u_val i f1 free1 : ℕ}
    {s : Memory.State} :
    let srt := mkSmallRt U V w n_max base
    let prog := smallScanStepProg ((srt, u_val), (i, (f1, free1)))
    let p := readPacked (base + offSmallPres) 1 w s.mem i
    let ki := readPacked (base + offSmallKeys U w n_max) (keyBits U) w s.mem i
    let nxt : ℕ × ℕ :=
      if p != 0 then
        if ki == u_val && f1 == 0 then (i + 1, free1) else (f1, free1)
      else
        if free1 == 0 then (f1, i + 1) else (f1, free1)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (i + 1, nxt) := by
  intro srt prog p ki nxt
  dsimp only [prog]
  unfold smallScanStepProg
  simp only [pure_bind]
  have h1 : (Memory.spec 0).clientState s
      (readPackedGenProg (((srBase srt, srOffPres srt), (1, srW srt)), i)) = s := rfl
  have h1r : (Memory.spec 0).clientResult s
      (readPackedGenProg (((srBase srt, srOffPres srt), (1, srW srt)), i)) = p :=
    clientResult_readPackedProg _ _ _ _ _ _
  have h2 : (Memory.spec 0).clientState s
      (readPackedGenProg (((srBase srt, srOffKeys srt), (srKeyBits srt, srW srt)), i)) = s := rfl
  have h2r : (Memory.spec 0).clientResult s
      (readPackedGenProg (((srBase srt, srOffKeys srt), (srKeyBits srt, srW srt)), i)) = ki :=
    clientResult_readPackedProg _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, h1, StateTransitionSpec.clientState_bind, h2]
    split_ifs <;> rfl
  · rw [StateTransitionSpec.clientResult_bind, h1, h1r,
      StateTransitionSpec.clientResult_bind, h2, h2r]
    dsimp only [nxt]
    by_cases hp0 : p = 0
    · simp [hp0]
      by_cases hfr0 : free1 = 0 <;> simp [hfr0]
    · simp [hp0]
      by_cases hk : ki = u_val
      · simp [hk]
        by_cases hf0 : f1 = 0 <;> simp [hf0]
      · simp [hk]

private theorem smallScanLoop_invariant {c U V w n_max base u_val : ℕ}
    (henv : WhpSmallEnv c U V w n_max w base) (s : Memory.State) :
    let srt := mkSmallRt U V w n_max base
    ∀ m i f1 free1, i + m ≤ n_max → f1 ≤ n_max → free1 ≤ n_max →
      iterationSafe smallScanStepProg SmallScanStepPre w (srt, u_val) m (i, (f1, free1)) s ∧
      (Memory.spec 0).clientState s (smallScanLoopProg (((srt, u_val), (i, (f1, free1))), m)) = s ∧
      ((Memory.spec 0).clientResult s
        (smallScanLoopProg (((srt, u_val), (i, (f1, free1))), m))).2.1 ≤ n_max ∧
      ((Memory.spec 0).clientResult s
        (smallScanLoopProg (((srt, u_val), (i, (f1, free1))), m))).2.2 ≤ n_max ∧
      memoryCost (smallScanLoopProg (((srt, u_val), (i, (f1, free1))), m)) s = 4 * m ∧
      ValidWhpProg w (base + smallSpaceWhp U V w n_max) s
        (smallScanLoopProg (((srt, u_val), (i, (f1, free1))), m)) := by
  intro srt m
  have hw := henv.2.1
  have hsegb := small_seg_base_bounds base U V w n_max
  induction m with
  | zero =>
    intro i f1 free1 _ hf1 hfr1
    exact ⟨trivial, rfl, hf1, hfr1, rfl, validWhpProg_pure _⟩
  | succ m ih =>
    intro i f1 free1 him hf1 hfr1
    have hi_lt : i < n_max := by omega
    have hpre : SmallScanStepPre w ((srt, u_val), (i, (f1, free1))) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hi_lt, hf1, hfr1⟩
    set p := readPacked (base + offSmallPres) 1 w s.mem i
    set ki := readPacked (base + offSmallKeys U w n_max) (keyBits U) w s.mem i
    set nxt : ℕ × ℕ :=
      if p != 0 then
        if ki == u_val && f1 == 0 then (i + 1, free1) else (f1, free1)
      else
        if free1 == 0 then (f1, i + 1) else (f1, free1)
    obtain ⟨hst1, hres1⟩ :
        (Memory.spec 0).clientState s (smallScanStepProg ((srt, u_val), (i, (f1, free1)))) = s ∧
        (Memory.spec 0).clientResult s (smallScanStepProg ((srt, u_val), (i, (f1, free1)))) =
          (i + 1, nxt) :=
      smallScanStepProg_step
    have hnxt_le : nxt.1 ≤ n_max ∧ nxt.2 ≤ n_max := by
      dsimp only [nxt]
      split_ifs <;> exact ⟨by omega, by omega⟩
    have hvp1 : ValidWhpProg w (base + smallSpaceWhp U V w n_max) s
        (smallScanStepProg ((srt, u_val), (i, (f1, free1)))) := by
      unfold smallScanStepProg
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hi_lt hsegb.1) ?_
      refine validWhpProg_bind (validWhpProg_readPacked hw hi_lt hsegb.2.1) ?_
      split_ifs <;> exact validWhpProg_pure _
    obtain ⟨hsafe_m, hst_m, hr1_m, hr2_m, hmc_m, hvp_m⟩ :=
      ih (i + 1) nxt.1 nxt.2 (by omega) hnxt_le.1 hnxt_le.2
    rw [Prod.mk.eta] at hsafe_m hst_m hr1_m hr2_m hmc_m hvp_m
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [clientResult_width, clientState_width, hst1, hres1]; exact hsafe_m
    · rw [smallScanLoopProg_succ, StateTransitionSpec.clientState_bind, hst1, hres1]
      exact hst_m
    · rw [smallScanLoopProg_succ, StateTransitionSpec.clientResult_bind, hst1, hres1]
      exact hr1_m
    · rw [smallScanLoopProg_succ, StateTransitionSpec.clientResult_bind, hst1, hres1]
      exact hr2_m
    · rw [smallScanLoopProg_succ, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_smallScanStepProg, hst1, hres1, hmc_m]
      ring
    · rw [smallScanLoopProg_succ]
      refine validWhpProg_bind hvp1 ?_
      rw [hst1, hres1]; exact hvp_m

private theorem smallScanLoop_result_eq {U V w n_max base u_val : ℕ} {sm : SmallDictState}
    {s : Memory.State} (hrep : SmallMemRep base U V w n_max sm s.mem) :
    ∀ m i, i + m ≤ n_max →
      (Memory.spec 0).clientResult s
        (smallScanLoopProg (((mkSmallRt U V w n_max base, u_val),
          (i, smallScan sm u_val i)), m)) =
        (i + m, smallScan sm u_val (i + m)) := by
  intro m
  induction m with
  | zero =>
    intro i _
    rw [smallScanLoopProg_zero, clientResult_pure_prog, Nat.add_zero]
  | succ m ih =>
    intro i him
    have hi_lt : i < n_max := by omega
    obtain ⟨hst1, hres1⟩ := smallScanStepProg_step (U := U) (V := V) (w := w) (n_max := n_max)
      (base := base) (u_val := u_val) (i := i)
      (f1 := (smallScan sm u_val i).1) (free1 := (smallScan sm u_val i).2) (s := s)
    rw [(hrep.2 i hi_lt).1, (hrep.2 i hi_lt).2.1] at hres1
    have hstep_eq : (Memory.spec 0).clientResult s
        (smallScanStepProg ((mkSmallRt U V w n_max base, u_val),
          (i, smallScan sm u_val i))) =
        (i + 1, smallScan sm u_val (i + 1)) := by
      rw [Prod.mk.eta] at hres1
      exact hres1
    rw [smallScanLoopProg_succ, StateTransitionSpec.clientResult_bind, hst1, hstep_eq]
    have hrec := ih (i + 1) (by omega)
    have hadd : i + 1 + m = i + (m + 1) := by omega
    rwa [hadd] at hrec

/-- Small-regime operation dispatcher (`d = (((cp, base), opTag), (u_val, v_val))`). -/
@[irreducible] def smallStepOpGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) :
    Memory.Prog (ℕ × ℕ) := do
  let srt ← extractSmallRtGenProg d.1.1
  let opTag ← pure d.1.2
  let u_val ← pure d.2.1
  let v_val ← pure d.2.2
  let zero_v ← pure 0
  let one_v ← pure 1
  let scanRes ← smallScanLoopProg (((srt, u_val), (zero_v, (zero_v, zero_v))), srNMax srt)
  let f1 ← pure scanRes.2.1
  let free1 ← pure scanRes.2.2
  if opTag = zero_v then
    if f1 = zero_v then
      pure (zero_v, zero_v)
    else
      let idx ← pure (f1 - one_v)
      let val ← readPackedGenProg (((srBase srt, srOffVals srt), (srValBits srt, srW srt)), idx)
      pure (one_v, val)
  else if opTag = one_v then
    if f1 = zero_v then
      if free1 = zero_v then
        pure (zero_v, zero_v)
      else
        let idx ← pure (free1 - one_v)
        writePackedGenProg
          ((((srBase srt, srOffPres srt), (one_v, srW srt)), idx), one_v)
        writePackedGenProg
          ((((srBase srt, srOffKeys srt), (srKeyBits srt, srW srt)), idx), u_val)
        writePackedGenProg
          ((((srBase srt, srOffVals srt), (srValBits srt, srW srt)), idx), v_val)
        pure (zero_v, zero_v)
    else
      let idx ← pure (f1 - one_v)
      writePackedGenProg
        ((((srBase srt, srOffVals srt), (srValBits srt, srW srt)), idx), v_val)
      pure (zero_v, zero_v)
  else
    if f1 = zero_v then
      pure (zero_v, zero_v)
    else
      let idx ← pure (f1 - one_v)
      writePackedGenProg
        ((((srBase srt, srOffPres srt), (one_v, srW srt)), idx), zero_v)
      pure (zero_v, zero_v)

theorem realizes_smallStepOpGen :
    Realizes .exact smallStepOpGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => WhpSmallEnvGen w d.1.1.1 d.1.1.2)
      (fun _ _ => 0) := by
  unfold smallStepOpGenProg
  have hex := realizes_extractSmallRtGen
  have hsl := realizes_smallScanLoop
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, opTag⟩, u_val, v_val⟩
    try clear hwords hmem
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hsm := henv.2.2.2.1
    try simp only [
      (extractSmallRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hsm s).1,
      (extractSmallRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hsm s).2.1,
      srBase_mk, srW_mk, srNMax_mk, srKeyBits_mk, srValBits_mk, srOffPres_mk, srOffKeys_mk,
      srOffVals_mk] at *
    have hinv := smallScanLoop_invariant (u_val := u_val) henv s n_max 0 0 0
      (Nat.zero_add n_max).le (Nat.zero_le _) (Nat.zero_le _)
    let scanP := smallScanLoopProg (((mkSmallRt U V w n_max base, u_val), (0, (0, 0))), n_max)
    set scanOut := (Memory.spec 0).clientResult s scanP
    have hf1_le : scanOut.2.1 ≤ n_max := hinv.2.2.1
    have hfr1_le : scanOut.2.2 ≤ n_max := hinv.2.2.2.1
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact hinv.1
    | omega
    | (apply to_true_exists (w := w); refine small_vals_safe' henv ?_; omega)
    | (apply to_true_exists (w := w); refine small_pres_safe henv ?_; omega)
    | (apply to_true_exists (w := w); refine small_keys_safe henv ?_; omega)
  )

theorem smallStepOpGenProg_spec {c U V w n_max base : ℕ} {sm : SmallDictState}
    {dict : Dictionary.State U} {s : Memory.State}
    (henv : WhpSmallEnv c U V w n_max w base)
    (hrep : SmallMemRep base U V w n_max sm s.mem)
    (_hv : ValidSmallState U V n_max sm dict)
    (op : Dynamic.Op U) (hvalid : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := smallStepOpGenProg (((mkWhpCoreParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := match op with
      | .query u => (sm, smallQuery n_max sm u.val)
      | .delete u => (smallDelete n_max sm u.val, none)
      | .insert u v => (smallInsert n_max sm u.val v, none)
    SmallMemRep base U V w n_max pureOut.1 s'.mem ∧
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    memoryCost prog s ≤ smallOpCostWhp c ∧
    ValidWhpProg w (base + smallSpaceWhp U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + smallSpaceWhp U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hsm := henv.2.2.2.1
  have hseg := small_seg_bounds U V w n_max
  have hsegb := small_seg_base_bounds base U V w n_max
  obtain ⟨hex_st, hex_res, hex_mc, hex_vp⟩ := extractSmallRtGenProg_spec
    (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hsm s
  dsimp only
  cases op with
  | query u =>
    have hinv := smallScanLoop_invariant (u_val := u.val) henv s n_max 0 0 0
      (Nat.zero_add n_max).le (Nat.zero_le _) (Nat.zero_le _)
    have hscan_res := smallScanLoop_result_eq (u_val := u.val) hrep n_max 0
      (Nat.zero_add n_max).le
    rw [Nat.zero_add] at hscan_res
    change (Memory.spec 0).clientResult s
      (smallScanLoopProg (((mkSmallRt U V w n_max base, u.val), (0, (0, 0))), n_max)) =
      (n_max, smallScan sm u.val n_max) at hscan_res
    set sc := smallScan sm u.val n_max
    unfold smallStepOpGenProg
    dsimp only [encodeOpWhp]
    simp only [pure_bind]
    have hsrN : srNMax (mkSmallRt U V w n_max base) = n_max := rfl
    by_cases hf0 : sc.1 = 0
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, clientState_pure_prog]
        exact hrep
      · rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp [hf0]
      · rw [StateTransitionSpec.clientResult_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientResult_bind, hinv.2.1, hscan_res]
        simp [smallQuery, sc, hf0, encodeOptRes]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res, hex_mc, hsrN]
        rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, memoryCost_pure, smallOpCostWhp]
        omega
      · refine validWhpProg_bind hex_vp ?_
        rw [hex_st, hex_res, hsrN]
        refine validWhpProg_bind hinv.2.2.2.2.2 ?_
        rw [hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0]
        exact validWhpProg_pure _
      · intro a _
        rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp [hf0]
    · have hidx_lt : sc.1 - 1 < n_max := by
        have := hinv.2.2.1; rw [hscan_res] at this; dsimp only at this; omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, clientState_bind_prog, clientState_readPackedGen,
          clientState_pure_prog]
        exact hrep
      · rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, clientState_bind_prog, clientState_readPackedGen,
          clientState_pure_prog]
      · rw [StateTransitionSpec.clientResult_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientResult_bind, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, clientResult_bind_prog, clientState_readPackedGen,
          clientResult_pure_prog]
        change (1, readPacked (base + offSmallVals U w n_max) (valBits V) w s.mem (sc.1 - 1)) =
          encodeOptRes (smallQuery n_max sm u.val)
        rw [(hrep.2 (sc.1 - 1) hidx_lt).2.2]
        simp [smallQuery, sc, hf0, encodeOptRes]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res, hex_mc, hsrN]
        rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, memoryCost_bind,
          memoryCost_readPackedGen, memoryCost_pure, smallOpCostWhp]
        omega
      · refine validWhpProg_bind hex_vp ?_
        rw [hex_st, hex_res, hsrN]
        refine validWhpProg_bind hinv.2.2.2.2.2 ?_
        rw [hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0]
        refine validWhpProg_bind (validWhpProg_readPacked hw hidx_lt hsegb.2.2) ?_
        exact validWhpProg_pure _
      · intro a _
        rw [StateTransitionSpec.clientState_bind, hex_st, hex_res, hsrN,
          StateTransitionSpec.clientState_bind, hinv.2.1, hscan_res]
        simp only [↓reduceIte, hf0, clientState_bind_prog, clientState_readPackedGen,
          clientState_pure_prog]
  | insert u v =>
    have hv_lt : v < V := hvalid.2
    have hinv := smallScanLoop_invariant (u_val := u.val) henv s n_max 0 0 0
      (Nat.zero_add n_max).le (Nat.zero_le _) (Nat.zero_le _)
    have hscan_res := smallScanLoop_result_eq (u_val := u.val) hrep n_max 0
      (Nat.zero_add n_max).le
    rw [Nat.zero_add] at hscan_res
    change (Memory.spec 0).clientResult s
      (smallScanLoopProg (((mkSmallRt U V w n_max base, u.val), (0, (0, 0))), n_max)) =
      (n_max, smallScan sm u.val n_max) at hscan_res
    set sc := smallScan sm u.val n_max
    dsimp only [encodeOpWhp]
    have hsrN : srNMax (mkSmallRt U V w n_max base) = n_max := rfl
    have h10 : ¬(1 = 0) := Nat.one_ne_zero
    by_cases hf0 : sc.1 = 0
    · by_cases hfr0 : sc.2 = 0
      · unfold smallStepOpGenProg
        simp only [pure_bind]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [clientState_bind_rw, hex_st, hex_res, hsrN,
            clientState_bind_rw, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, clientState_pure_prog]
          unfold smallInsert
          dsimp only [sc] at hf0 hfr0
          simp only [hf0, hfr0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          exact hrep
        · rw [clientState_bind_rw, hex_st, hex_res, hsrN,
            clientState_bind_rw, hinv.2.1, hscan_res]
          simp [h10, hf0, hfr0]
        · rw [clientResult_bind_prog, hex_st, hex_res, hsrN,
            clientResult_bind_prog, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, clientResult_pure_prog, encodeOptRes]
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res, hex_mc, hsrN]
          rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, memoryCost_pure, smallOpCostWhp]
          omega
        · refine validWhpProg_bind hex_vp ?_
          rw [hex_st, hex_res, hsrN]
          refine validWhpProg_bind hinv.2.2.2.2.2 ?_
          rw [hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0]
          exact validWhpProg_pure _
        · intro a _
          rw [clientState_bind_rw, hex_st, hex_res, hsrN,
            clientState_bind_rw, hinv.2.1, hscan_res]
          simp [h10, hf0, hfr0]
      · have hidx_lt : sc.2 - 1 < n_max := by
          have := hinv.2.2.2.1; rw [hscan_res] at this; dsimp only at this; omega
        set idx := sc.2 - 1
        set m1 := writePacked (base + offSmallPres) 1 w s.mem idx 1
        set m2 := writePacked (base + offSmallKeys U w n_max) (keyBits U) w m1 idx u.val
        set m3 := writePacked (base + offSmallVals U w n_max) (valBits V) w m2 idx v
        have hst_eq : (Memory.spec 0).clientState s
            (smallStepOpGenProg (((mkWhpCoreParams c U V w n_max, base), 1), (u.val, v))) =
            { mem := m3, frontier := s.frontier } := by
          unfold smallStepOpGenProg
          simp only [pure_bind]
          rw [clientState_bind_rw, hex_st, hex_res, hsrN,
            clientState_bind_rw, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, clientState_bind_prog,
            clientState_writePackedGen, clientState_pure_prog]
          rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hst_eq]
          have hsm_eq : smallInsert n_max sm u.val v =
              { present := Function.update sm.present idx 1
                keys := Function.update sm.keys idx u.val
                vals := Function.update sm.vals idx v } := by
            unfold smallInsert; simp [sc, hf0, hfr0, idx]
          rw [hsm_eq]
          refine ⟨?_, fun i hi => ⟨?_, ?_, ?_⟩⟩
          · dsimp only [m3, m2, m1]
            rw [mem_writePacked_of_outside hw hidx_lt (by omega),
              mem_writePacked_of_outside hw hidx_lt (by omega),
              mem_writePacked_of_outside hw hidx_lt (by omega)]
            exact hrep.1
          · dsimp only [m3, m2, m1]
            rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega),
              readPacked_writePacked_disjoint hw hi hidx_lt (by omega)]
            by_cases heq : i = idx
            · subst heq
              rw [readPacked_writePacked_self _ _ _ _ _ (by decide : 1 < 2 ^ 1),
                Function.update_self]
            · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
                (hrep.2 i hi).1]
          · dsimp only [m3, m2, m1]
            rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega)]
            by_cases heq : i = idx
            · subst heq
              rw [readPacked_writePacked_self _ _ _ _ _ (key_lt_two_pow_keyBits u.isLt),
                Function.update_self]
            · rw [readPacked_writePacked_of_ne hw _ heq,
                readPacked_writePacked_disjoint hw hi hidx_lt (by omega),
                Function.update_of_ne heq, (hrep.2 i hi).2.1]
          · dsimp only [m3]
            by_cases heq : i = idx
            · subst heq
              rw [readPacked_writePacked_self _ _ _ _ _ (val_lt_two_pow_valBits hv_lt),
                Function.update_self]
            · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq]
              dsimp only [m2, m1]
              rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega),
                readPacked_writePacked_disjoint hw hi hidx_lt (by omega),
                (hrep.2 i hi).2.2]
        · rw [hst_eq]
        · unfold smallStepOpGenProg
          simp only [pure_bind]
          rw [clientResult_bind_prog, hex_st, hex_res, hsrN,
            clientResult_bind_prog, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, clientResult_bind_prog,
            clientResult_pure_prog, encodeOptRes]
        · unfold smallStepOpGenProg
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res,
            hex_mc, hsrN]
          rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0, memoryCost_bind]
          change 0 + (4 * n_max + (4 + (4 + (4 + 0)))) ≤ 4 * whpThreshold c + 16
          omega
        · unfold smallStepOpGenProg
          simp only [pure_bind]
          refine validWhpProg_bind hex_vp ?_
          rw [hex_st, hex_res, hsrN]
          refine validWhpProg_bind hinv.2.2.2.2.2 ?_
          rw [hinv.2.1, hscan_res]
          simp only [h10, ↓reduceIte, hf0, hfr0]
          refine validWhpProg_bind
            (validWhpProg_writePacked hw hw hidx_lt hsegb.1) ?_
          refine validWhpProg_bind
            (validWhpProg_writePacked hw (keyBits_le_w henv.2.2.2.2.2.1) hidx_lt hsegb.2.1) ?_
          refine validWhpProg_bind
            (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hidx_lt hsegb.2.2) ?_
          exact validWhpProg_pure _
        · intro a ha
          rw [hst_eq]; dsimp only [m3, m2, m1]
          rw [mem_writePacked_of_outside hw hidx_lt (by omega),
            mem_writePacked_of_outside hw hidx_lt (by omega),
            mem_writePacked_of_outside hw hidx_lt (by omega)]
    · have hidx_lt : sc.1 - 1 < n_max := by
        have := hinv.2.2.1; rw [hscan_res] at this; dsimp only at this; omega
      set idx := sc.1 - 1
      set m1 := writePacked (base + offSmallVals U w n_max) (valBits V) w s.mem idx v
      have hst_eq : (Memory.spec 0).clientState s
          (smallStepOpGenProg (((mkWhpCoreParams c U V w n_max, base), 1), (u.val, v))) =
          { mem := m1, frontier := s.frontier } := by
        unfold smallStepOpGenProg
        simp only [pure_bind]
        rw [clientState_bind_rw, hex_st, hex_res, hsrN,
          clientState_bind_rw, hinv.2.1, hscan_res]
        simp only [h10, ↓reduceIte, hf0, clientState_bind_prog,
          clientState_writePackedGen, clientState_pure_prog]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]
        have hsm_eq : smallInsert n_max sm u.val v =
            { sm with vals := Function.update sm.vals idx v } := by
          unfold smallInsert; simp [sc, hf0, idx]
        rw [hsm_eq]
        refine ⟨?_, fun i hi => ⟨?_, ?_, ?_⟩⟩
        · dsimp only [m1]
          rw [mem_writePacked_of_outside hw hidx_lt (by omega)]
          exact hrep.1
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega), (hrep.2 i hi).1]
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega), (hrep.2 i hi).2.1]
        · dsimp only [m1]
          by_cases heq : i = idx
          · subst heq
            rw [readPacked_writePacked_self _ _ _ _ _ (val_lt_two_pow_valBits hv_lt),
              Function.update_self]
          · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
              (hrep.2 i hi).2.2]
      · rw [hst_eq]
      · unfold smallStepOpGenProg
        simp only [pure_bind]
        rw [clientResult_bind_prog, hex_st, hex_res, hsrN,
          clientResult_bind_prog, hinv.2.1, hscan_res]
        simp only [h10, ↓reduceIte, hf0, clientResult_bind_prog,
          clientResult_pure_prog, encodeOptRes]
      · unfold smallStepOpGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res,
          hex_mc, hsrN]
        rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
        simp only [h10, ↓reduceIte, hf0, memoryCost_bind]
        change 0 + (4 * n_max + (4 + 0)) ≤ 4 * whpThreshold c + 16
        omega
      · unfold smallStepOpGenProg
        simp only [pure_bind]
        refine validWhpProg_bind hex_vp ?_
        rw [hex_st, hex_res, hsrN]
        refine validWhpProg_bind hinv.2.2.2.2.2 ?_
        rw [hinv.2.1, hscan_res]
        simp only [h10, ↓reduceIte, hf0]
        refine validWhpProg_bind
          (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hidx_lt hsegb.2.2) ?_
        exact validWhpProg_pure _
      · intro a ha
        rw [hst_eq]; dsimp only [m1]
        rw [mem_writePacked_of_outside hw hidx_lt (by omega)]
  | delete u =>
    have hinv := smallScanLoop_invariant (u_val := u.val) henv s n_max 0 0 0
      (Nat.zero_add n_max).le (Nat.zero_le _) (Nat.zero_le _)
    have hscan_res := smallScanLoop_result_eq (u_val := u.val) hrep n_max 0
      (Nat.zero_add n_max).le
    rw [Nat.zero_add] at hscan_res
    change (Memory.spec 0).clientResult s
      (smallScanLoopProg (((mkSmallRt U V w n_max base, u.val), (0, (0, 0))), n_max)) =
      (n_max, smallScan sm u.val n_max) at hscan_res
    set sc := smallScan sm u.val n_max
    dsimp only [encodeOpWhp]
    have hsrN : srNMax (mkSmallRt U V w n_max base) = n_max := rfl
    have h20 : ¬(2 = 0) := by decide
    have h21 : ¬(2 = 1) := by decide
    by_cases hf0 : sc.1 = 0
    · unfold smallStepOpGenProg
      simp only [pure_bind]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [clientState_bind_rw, hex_st, hex_res, hsrN,
          clientState_bind_rw, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, clientState_pure_prog]
        unfold smallDelete
        dsimp only [sc] at hf0
        simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact hrep
      · rw [clientState_bind_rw, hex_st, hex_res, hsrN,
          clientState_bind_rw, hinv.2.1, hscan_res]
        simp [h20, h21, hf0]
      · rw [clientResult_bind_prog, hex_st, hex_res, hsrN,
          clientResult_bind_prog, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, clientResult_pure_prog, encodeOptRes]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res, hex_mc, hsrN]
        rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, memoryCost_pure, smallOpCostWhp]
        omega
      · refine validWhpProg_bind hex_vp ?_
        rw [hex_st, hex_res, hsrN]
        refine validWhpProg_bind hinv.2.2.2.2.2 ?_
        rw [hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0]
        exact validWhpProg_pure _
      · intro a _
        rw [clientState_bind_rw, hex_st, hex_res, hsrN,
          clientState_bind_rw, hinv.2.1, hscan_res]
        simp [h20, h21, hf0]
    · have hidx_lt : sc.1 - 1 < n_max := by
        have := hinv.2.2.1; rw [hscan_res] at this; dsimp only at this; omega
      set idx := sc.1 - 1
      set m1 := writePacked (base + offSmallPres) 1 w s.mem idx 0
      have hst_eq : (Memory.spec 0).clientState s
          (smallStepOpGenProg (((mkWhpCoreParams c U V w n_max, base), 2), (u.val, 0))) =
          { mem := m1, frontier := s.frontier } := by
        unfold smallStepOpGenProg
        simp only [pure_bind]
        rw [clientState_bind_rw, hex_st, hex_res, hsrN,
          clientState_bind_rw, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, clientState_bind_prog,
          clientState_writePackedGen, clientState_pure_prog]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]
        have hsm_eq : smallDelete n_max sm u.val =
            { sm with present := Function.update sm.present idx 0 } := by
          unfold smallDelete; simp [sc, hf0, idx]
        rw [hsm_eq]
        refine ⟨?_, fun i hi => ⟨?_, ?_, ?_⟩⟩
        · dsimp only [m1]
          rw [mem_writePacked_of_outside hw hidx_lt (by omega)]
          exact hrep.1
        · dsimp only [m1]
          by_cases heq : i = idx
          · subst heq
            rw [readPacked_writePacked_self _ _ _ _ _ (by decide : 0 < 2 ^ 1),
              Function.update_self]
          · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
              (hrep.2 i hi).1]
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega), (hrep.2 i hi).2.1]
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw hi hidx_lt (by omega), (hrep.2 i hi).2.2]
      · rw [hst_eq]
      · unfold smallStepOpGenProg
        simp only [pure_bind]
        rw [clientResult_bind_prog, hex_st, hex_res, hsrN,
          clientResult_bind_prog, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, clientResult_bind_prog, clientResult_pure_prog,
          encodeOptRes]
      · unfold smallStepOpGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hex_st, hex_res,
          hex_mc, hsrN]
        rw [hinv.2.2.2.2.1, hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0, memoryCost_bind]
        change 0 + (4 * n_max + (4 + 0)) ≤ 4 * whpThreshold c + 16
        omega
      · unfold smallStepOpGenProg
        simp only [pure_bind]
        refine validWhpProg_bind hex_vp ?_
        rw [hex_st, hex_res, hsrN]
        refine validWhpProg_bind hinv.2.2.2.2.2 ?_
        rw [hinv.2.1, hscan_res]
        simp only [h20, h21, ↓reduceIte, hf0]
        refine validWhpProg_bind (validWhpProg_writePacked hw hw hidx_lt hsegb.1) ?_
        exact validWhpProg_pure _
      · intro a ha
        rw [hst_eq]; dsimp only [m1]
        rw [mem_writePacked_of_outside hw hidx_lt (by omega)]

/-! ## Section 3: CSR Fallback `Memory.Prog` Subroutines (`whpThreshold c ≤ n_max`) -/

/-- Compact 10-word runtime parameter bundle for CSR operations:
`(((base, w), (n_max, M)), (((gBits, quotBits), (valBits, offFb)), (offQuot, offVal)))`. -/
abbrev CsrRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ))

@[expose] def crBase (crt : CsrRt) : ℕ := crt.1.1.1
@[expose] def crW (crt : CsrRt) : ℕ := crt.1.1.2
@[expose] def crNMax (crt : CsrRt) : ℕ := crt.1.2.1
@[expose] def crM (crt : CsrRt) : ℕ := crt.1.2.2
@[expose] def crGBits (crt : CsrRt) : ℕ := crt.2.1.1.1
@[expose] def crQuotBits (crt : CsrRt) : ℕ := crt.2.1.1.2
@[expose] def crValBits (crt : CsrRt) : ℕ := crt.2.1.2.1
@[expose] def crOffFb (crt : CsrRt) : ℕ := crt.2.1.2.2
@[expose] def crOffQuot (crt : CsrRt) : ℕ := crt.2.2.1
@[expose] def crOffVal (crt : CsrRt) : ℕ := crt.2.2.2

/-- Pure constructor for `CsrRt`. -/
@[expose] def mkCsrRt (c U V w n_max base : ℕ) : CsrRt :=
  (((base, w), (n_max, numBucketsWhp n_max)),
   (((globalPtrBits n_max, quotBitsWhp U n_max),
     (valBits V, offFbStart c U V w n_max)),
    (offQuotWhp c w n_max, offValWhp c U w n_max)))

@[simp] private theorem crBase_mk (c U V w n_max base : ℕ) :
    crBase (mkCsrRt c U V w n_max base) = base := rfl
@[simp] private theorem crW_mk (c U V w n_max base : ℕ) :
    crW (mkCsrRt c U V w n_max base) = w := rfl
@[simp] private theorem crNMax_mk (c U V w n_max base : ℕ) :
    crNMax (mkCsrRt c U V w n_max base) = n_max := rfl
@[simp] private theorem crM_mk (c U V w n_max base : ℕ) :
    crM (mkCsrRt c U V w n_max base) = numBucketsWhp n_max := rfl
@[simp] private theorem crGBits_mk (c U V w n_max base : ℕ) :
    crGBits (mkCsrRt c U V w n_max base) = globalPtrBits n_max := rfl
@[simp] private theorem crQuotBits_mk (c U V w n_max base : ℕ) :
    crQuotBits (mkCsrRt c U V w n_max base) = quotBitsWhp U n_max := rfl
@[simp] private theorem crValBits_mk (c U V w n_max base : ℕ) :
    crValBits (mkCsrRt c U V w n_max base) = valBits V := rfl
@[simp] private theorem crOffFb_mk (c U V w n_max base : ℕ) :
    crOffFb (mkCsrRt c U V w n_max base) = offFbStart c U V w n_max := rfl
@[simp] private theorem crOffQuot_mk (c U V w n_max base : ℕ) :
    crOffQuot (mkCsrRt c U V w n_max base) = offQuotWhp c w n_max := rfl
@[simp] private theorem crOffVal_mk (c U V w n_max base : ℕ) :
    crOffVal (mkCsrRt c U V w n_max base) = offValWhp c U w n_max := rfl

/-- Parameter-free large-regime `CsrRt` envelope. -/
@[expose] def CsrRtEnvGen (w : ℕ) (crt : CsrRt) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (crBase crt) ∧
    crt = mkCsrRt c U V w₀ n_max (crBase crt)

/-- Extract `CsrRt` from `(cp, base)` in 0 memory operations. -/
@[irreducible] def mkCsrRtGenProg (d : WhpCoreParams × ℕ) : Memory.Prog CsrRt := do
  let cp := d.1
  let base ← pure d.2
  pure (((base, wpW cp), (wpNMax cp, wpM cp)),
    (((wpGlobalPtrBits cp, wpQuotBits cp),
      (wpValBits cp, wpOffFbStart cp)),
     (wpOffQuot cp, wpOffVal cp)))

theorem realizes_mkCsrRtGen :
    Realizes .exact mkCsrRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := CsrRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkCsrRtGenProg
  realize

theorem mkCsrRtGenProg_spec {c U V w n_max base : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkCsrRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkCsrRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold mkCsrRtGenProg mkCsrRt
  simp only [pure_bind, wp_large_w hth, wp_large_nMax hth, wp_large_M hth,
    wp_large_globalPtrBits hth, wp_large_quotBits hth, wp_large_valBits hth,
    wp_large_offFbStart hth, wp_large_offQuot hth, wp_large_offVal hth]
  exact ⟨rfl, rfl, rfl, validWhpProg_pure _⟩

section CsrSafety

private theorem csr_seg_disjoint (c U V w n_max : ℕ) :
    offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      largeSpaceWhp c U V w n_max ∧
    offValWhp c U w n_max + packedWords n_max (valBits V) w ≤
      largeSpaceWhp c U V w n_max ∧
    offFbStart c U V w n_max + packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ≤
      largeSpaceWhp c U V w n_max ∧
    offHashBkt + bktHashWords c w n_max + fpHashWords c w n_max ≤ offQuotWhp c w n_max ∧
    32 ≤ offQuotWhp c w n_max ∧
    offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      offValWhp c U w n_max ∧
    offValWhp c U w n_max + packedWords n_max (valBits V) w ≤
      offFbStart c U V w n_max := by
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have h0 : offHashBkt = 32 := rfl
  have h1 : offHashFp c w n_max = offHashBkt + bktHashWords c w n_max := rfl
  have h2 : offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max := rfl
  have h3 : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have h4 : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have h5 : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * ellWhp n_max + 4) w := rfl
  have h6 : offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w := rfl
  have h7 : offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w := rfl
  exact ⟨hseg.1, hseg.2.1, hseg.2.2.2.2.2.1, by omega, by omega, by omega, by omega⟩

private theorem csr_quot_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ quotBitsWhp U n_max ≤ w ∧ idx < N ∧
      Fits w (base + offQuotWhp c w n_max + packedWords N (quotBitsWhp U n_max) w) := by
  have hqk : quotBitsWhp U n_max ≤ w :=
    (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  exact henv.packed_safe_of_le hqk hidx (WhpLargeEnv.seg_end_le c U V w n_max).1

private theorem csr_val_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, w = w ∧ 0 < w ∧ valBits V ≤ w ∧ idx < N ∧
      Fits w (base + offValWhp c U w n_max + packedWords N (valBits V) w) :=
  henv.packed_safe_of_le (valBits_le_w henv.2.2.2.2.2.2.1) hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.1

private theorem csr_fb_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < numBucketsWhp n_max + 1) :
    ∃ N, w = w ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offFbStart c U V w n_max + packedWords N (globalPtrBits n_max) w) :=
  henv.packed_safe_of_le (globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1) hidx
    (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1

private theorem numBuckets_lt_n_max {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    numBucketsWhp n_max < n_max := by
  have h16 := sixteen_mul_numBuckets_le_n_max henv.2.2.2.1
  have hM := (large_bounds_lt_n_max henv.2.2.2.1).1
  omega

private theorem csr_seg_base_bounds (base c U V w n_max : ℕ) :
    base + offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offValWhp c U w n_max + packedWords n_max (valBits V) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offFbStart c U V w n_max +
      packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
  have hs := csr_seg_disjoint c U V w n_max
  exact ⟨by omega, by omega, by omega⟩

end CsrSafety

/-! ### Loop 1: `csrScanRange` -/

/-- Single step of `csrScanRange` (`d = ((crt, (lo, q_val)), (k, f1))`). -/
@[irreducible] def csrScanStepProg (d : (CsrRt × (ℕ × ℕ)) × (ℕ × ℕ)) :
    Memory.Prog (ℕ × ℕ) := do
  let crt := d.1.1
  let lo ← pure d.1.2.1
  let q_val ← pure d.1.2.2
  let k ← pure d.2.1
  let f1 ← pure d.2.2
  let zero_v ← pure 0
  let one_v ← pure 1
  let pos ← pure (lo + k)
  let qk ← readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), pos)
  let k1 ← pure (k + one_v)
  if f1 = zero_v then
    if qk = q_val then
      let p1 ← pure (pos + one_v)
      pure (k1, p1)
    else
      pure (k1, zero_v)
  else
    pure (k1, f1)

/-- Precondition for `csrScanStepProg`. -/
@[expose] def CsrScanStepPre (w : ℕ) (d : (CsrRt × (ℕ × ℕ)) × (ℕ × ℕ))
    (_s : Memory.State) : Prop :=
  CsrRtEnvGen w d.1.1 ∧
  d.1.2.1 + d.2.1 < crNMax d.1.1 ∧
  d.2.2 ≤ crNMax d.1.1

private theorem memoryCost_csrScanStepProg (d : (CsrRt × (ℕ × ℕ)) × (ℕ × ℕ))
    (s : Memory.State) :
    memoryCost (csrScanStepProg d) s = 2 := by
  unfold csrScanStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 2 + _ = 2
  split_ifs <;> rfl

private theorem memoryCost_csrScanStepProg_pos (d : (CsrRt × (ℕ × ℕ)) × (ℕ × ℕ))
    (s : Memory.State) :
    1 ≤ memoryCost (csrScanStepProg d) s := by
  rw [memoryCost_csrScanStepProg]; decide

theorem realizes_csrScanStep :
    Realizes .exact csrScanStepProg
      (WordEncoding.encode (α := (CsrRt × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CsrScanStepPre
      (fun _ _ => 0) := by
  unfold csrScanStepProg
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨crt, lo, q_val⟩, k, f1⟩
    try clear hwords hmem
    dsimp only [CsrScanStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hpos_lt, hf1_le⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hN_eq : crNMax crt = n_max := by rw [heq_crt]; rfl
    have hW_eq : crW crt = w := by rw [heq_crt]; rfl
    have hQB_eq : crQuotBits crt = quotBitsWhp U n_max := by rw [heq_crt]; rfl
    have hOQ_eq : crOffQuot crt = offQuotWhp c w n_max := by rw [heq_crt]; rfl
    rw [hN_eq] at hpos_lt hf1_le
    dsimp only [crBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact (by omega : lo + k < n_max).trans hn_lt
    | exact (by omega : k + 1 ≤ n_max).trans_lt hn_lt
    | exact (by omega : lo + k + 1 ≤ n_max).trans_lt hn_lt
    | (rw [hW_eq, hQB_eq, hOQ_eq]; exact csr_quot_safe henv hpos_lt)
  )

/-- Loop wrapper for `iterate csrScanStepProg`. -/
@[expose] def csrScanLoopProg (d : ((CsrRt × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) :
    Memory.Prog (ℕ × ℕ) :=
  iterate csrScanStepProg d.1.1 d.2 d.1.2

private theorem csrScanLoopProg_zero (env : CsrRt × (ℕ × ℕ)) (acc : ℕ × ℕ) :
    csrScanLoopProg ((env, acc), 0) = pure acc := rfl

private theorem csrScanLoopProg_succ (env : CsrRt × (ℕ × ℕ)) (acc : ℕ × ℕ) (m : ℕ) :
    csrScanLoopProg ((env, acc), m + 1) =
      (csrScanStepProg (env, acc) >>= fun acc' => csrScanLoopProg ((env, acc'), m)) := rfl

theorem realizes_csrScanLoop :
    Realizes .exact csrScanLoopProg
      (WordEncoding.encode (α := ((CsrRt × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s => iterationSafe csrScanStepProg CsrScanStepPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := CsrRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_csrScanStep
    memoryCost_csrScanStepProg_pos

private theorem csrScanLoop_spec {c U V w n_max base lo q_val : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (s : Memory.State) :
    let crt := mkCsrRt c U V w n_max base
    let qMem : ℕ → ℕ := fun i => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
      s.mem i
    ∀ m k f1, lo + k + m ≤ n_max → f1 ≤ n_max →
      iterationSafe csrScanStepProg CsrScanStepPre w (crt, (lo, q_val)) m (k, f1) s ∧
      (Memory.spec 0).clientState s (csrScanLoopProg (((crt, (lo, q_val)), (k, f1)), m)) = s ∧
      ((Memory.spec 0).clientResult s
        (csrScanLoopProg (((crt, (lo, q_val)), (k, f1)), m))).2 ≤ n_max ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (csrScanLoopProg (((crt, (lo, q_val)), (k, f1)), m)) ∧
      (f1 = csrScanRange qMem lo q_val k →
        (Memory.spec 0).clientResult s (csrScanLoopProg (((crt, (lo, q_val)), (k, f1)), m)) =
          (k + m, csrScanRange qMem lo q_val (k + m))) := by
  intro crt qMem m
  have hw := henv.2.1
  have hsegb := csr_seg_base_bounds base c U V w n_max
  induction m with
  | zero =>
    intro k f1 _ hf1
    refine ⟨trivial, rfl, hf1, validWhpProg_pure _, fun heq => ?_⟩
    rw [csrScanLoopProg_zero, clientResult_pure_prog, Nat.add_zero, heq]
  | succ m ih =>
    intro k f1 hkm hf1
    have hpos : lo + k < n_max := by omega
    have hpre : CsrScanStepPre w ((crt, (lo, q_val)), (k, f1)) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hpos, hf1⟩
    have hst1 : (Memory.spec 0).clientState s
        (csrScanStepProg ((crt, (lo, q_val)), (k, f1))) = s := by
      unfold csrScanStepProg
      simp only [pure_bind, clientState_bind_prog, clientState_readPackedGen]
      split_ifs <;> rfl
    set nxt := if f1 != 0 then f1 else if qMem (lo + k) == q_val then (lo + k) + 1 else 0
    have hres1 : (Memory.spec 0).clientResult s
        (csrScanStepProg ((crt, (lo, q_val)), (k, f1))) = (k + 1, nxt) := by
      unfold csrScanStepProg
      simp only [pure_bind, clientResult_bind_prog, clientState_readPackedGen]
      have hrp : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), lo + k)) =
          qMem (lo + k) := clientResult_readPackedProg _ _ _ _ _ _
      rw [hrp]
      dsimp only [nxt]
      by_cases hf0 : f1 = 0
      · simp [hf0]; by_cases hq : qMem (lo + k) = q_val <;> simp [hq]
      · simp [hf0]
    have hnxt_le : nxt ≤ n_max := by dsimp only [nxt]; split_ifs <;> omega
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (csrScanStepProg ((crt, (lo, q_val)), (k, f1))) := by
      unfold csrScanStepProg
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hpos hsegb.1) ?_
      split_ifs <;> exact validWhpProg_pure _
    obtain ⟨hsafe_m, hst_m, hr_m, hvp_m, heq_m⟩ := ih (k + 1) nxt (by omega) hnxt_le
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, fun hf_eq => ?_⟩
    · rw [clientResult_width, clientState_width, hst1, hres1]; exact hsafe_m
    · rw [csrScanLoopProg_succ, StateTransitionSpec.clientState_bind, hst1, hres1]
      exact hst_m
    · rw [csrScanLoopProg_succ, StateTransitionSpec.clientResult_bind, hst1, hres1]
      exact hr_m
    · rw [csrScanLoopProg_succ]
      refine validWhpProg_bind hvp1 ?_
      rw [hst1, hres1]; exact hvp_m
    · rw [csrScanLoopProg_succ, StateTransitionSpec.clientResult_bind, hst1, hres1]
      have hnxt_eq : nxt = csrScanRange qMem lo q_val (k + 1) := by
        dsimp only [nxt, csrScanRange]; rw [hf_eq]
      have hrec := heq_m hnxt_eq
      have hadd : k + 1 + m = k + (m + 1) := by omega
      rwa [hadd] at hrec

/-! ### Loop 2: `csrShiftDown` -/

/-- Single step of `csrShiftDown` (`d = ((crt, i₀), k)`). -/
@[irreducible] def csrShiftDownStepProg (d : (CsrRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let crt := d.1.1
  let i₀ ← pure d.1.2
  let k ← pure d.2
  let one_v ← pure 1
  let pos ← pure (i₀ + k)
  let pos1 ← pure (pos + one_v)
  let qn ← readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), pos1)
  let vn ← readPackedGenProg (((crBase crt, crOffVal crt), (crValBits crt, crW crt)), pos1)
  writePackedGenProg ((((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), pos), qn)
  writePackedGenProg ((((crBase crt, crOffVal crt), (crValBits crt, crW crt)), pos), vn)
  pure (k + one_v)

/-- Precondition for `csrShiftDownStepProg`. -/
@[expose] def CsrShiftDownStepPre (w : ℕ) (d : (CsrRt × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  CsrRtEnvGen w d.1.1 ∧
  d.1.2 + d.2 + 1 < crNMax d.1.1

private theorem memoryCost_csrShiftDownStepProg_pos (d : (CsrRt × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (csrShiftDownStepProg d) s := by
  unfold csrShiftDownStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 2 + _ ≥ 1
  omega

theorem realizes_csrShiftDownStep :
    Realizes .exact csrShiftDownStepProg
      (WordEncoding.encode (α := (CsrRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrShiftDownStepPre
      (fun _ _ => 0) := by
  unfold csrShiftDownStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨crt, i₀⟩, k⟩
    dsimp only [CsrShiftDownStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hpos1_lt⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hN_eq : crNMax crt = n_max := by rw [heq_crt]; rfl
    have hW_eq : crW crt = w := by rw [heq_crt]; rfl
    have hQB_eq : crQuotBits crt = quotBitsWhp U n_max := by rw [heq_crt]; rfl
    have hVB_eq : crValBits crt = valBits V := by rw [heq_crt]; rfl
    have hOQ_eq : crOffQuot crt = offQuotWhp c w n_max := by rw [heq_crt]; rfl
    have hOV_eq : crOffVal crt = offValWhp c U w n_max := by rw [heq_crt]; rfl
    rw [hN_eq] at hpos1_lt
    dsimp only [crBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact (by omega : i₀ + k < n_max).trans hn_lt
    | exact hpos1_lt.trans hn_lt
    | exact (by omega : k + 1 < n_max).trans hn_lt
    | (rw [hW_eq, hQB_eq, hOQ_eq]; exact csr_quot_safe henv (by omega))
    | (rw [hW_eq, hVB_eq, hOV_eq]; exact csr_val_safe henv (by omega))
  )

/-- Loop wrapper for `iterate csrShiftDownStepProg`. -/
@[expose] def csrShiftDownLoopProg (d : ((CsrRt × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate csrShiftDownStepProg d.1.1 d.2 d.1.2

private theorem csrShiftDownLoopProg_zero (env : CsrRt × ℕ) (acc : ℕ) :
    csrShiftDownLoopProg ((env, acc), 0) = pure acc := rfl

private theorem csrShiftDownLoopProg_succ (env : CsrRt × ℕ) (acc m : ℕ) :
    csrShiftDownLoopProg ((env, acc), m + 1) =
      (csrShiftDownStepProg (env, acc) >>= fun acc' => csrShiftDownLoopProg ((env, acc'), m)) := rfl

theorem realizes_csrShiftDownLoop :
    Realizes .exact csrShiftDownLoopProg
      (WordEncoding.encode (α := ((CsrRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => iterationSafe csrShiftDownStepProg CsrShiftDownStepPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := CsrRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_csrShiftDownStep
    memoryCost_csrShiftDownStepProg_pos

private theorem csrShiftDownLoop_spec {c U V w n_max base i₀ : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let crt := mkCsrRt c U V w n_max base
    ∀ m k (q₀ v₀ : ℕ → ℕ) (s : Memory.State),
      i₀ + k + m ≤ n_max →
      (m > 0 → i₀ + k + m < n_max) →
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i =
          (csrShiftDown i₀ k (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w s.mem i =
          (csrShiftDown i₀ k (q₀, v₀)).2 i) →
      let prog := csrShiftDownLoopProg (((crt, i₀), k), m)
      let s' := (Memory.spec 0).clientState s prog
      iterationSafe csrShiftDownStepProg CsrShiftDownStepPre w (crt, i₀) m k s ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s'.mem i =
          (csrShiftDown i₀ (k + m) (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w s'.mem i =
          (csrShiftDown i₀ (k + m) (q₀, v₀)).2 i) ∧
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offPermAct c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro crt m
  have hw := henv.2.1
  have hseg := csr_seg_disjoint c U V w n_max
  have hsegb := csr_seg_base_bounds base c U V w n_max
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  induction m with
  | zero =>
    intro k q₀ v₀ s _ _ hqv
    dsimp only
    rw [csrShiftDownLoopProg_zero, clientState_pure_rw, Nat.add_zero]
    exact ⟨trivial, rfl, validWhpProg_pure _, hqv, fun _ _ => rfl⟩
  | succ m ih =>
    intro k q₀ v₀ s _ hlt_pos hqv
    dsimp only
    have hpos1 : i₀ + k + 1 < n_max := by have := hlt_pos (Nat.succ_pos m); omega
    have hpos : i₀ + k < n_max := by omega
    have hpre : CsrShiftDownStepPre w ((crt, i₀), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hpos1⟩
    set qk := (csrShiftDown i₀ k (q₀, v₀)).1
    set vk := (csrShiftDown i₀ k (q₀, v₀)).2
    have hqn_lt : qk (i₀ + k + 1) < 2 ^ quotBitsWhp U n_max := by
      rw [← (hqv (i₀ + k + 1) hpos1).1]; exact readPacked_lt _ _ _ _ _
    have hvn_lt : vk (i₀ + k + 1) < 2 ^ valBits V := by
      rw [← (hqv (i₀ + k + 1) hpos1).2]; exact readPacked_lt _ _ _ _ _
    set m1 := writePacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem
      (i₀ + k) (qk (i₀ + k + 1))
    set m2 := writePacked (base + offValWhp c U w n_max) (valBits V) w m1
      (i₀ + k) (vk (i₀ + k + 1))
    have hstep_st : (Memory.spec 0).clientState s (csrShiftDownStepProg ((crt, i₀), k)) =
        { mem := m2, frontier := s.frontier } := by
      unfold csrShiftDownStepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
      have hr1 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)),
            i₀ + k + 1)) = qk (i₀ + k + 1) :=
        (clientResult_readPackedProg _ _ _ _ _ _).trans (hqv (i₀ + k + 1) hpos1).1
      change (Memory.spec 0).clientState s _ = _
      rw [hr1, StateTransitionSpec.clientState_bind]
      have hr2 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffVal crt), (crValBits crt, crW crt)),
            i₀ + k + 1)) = vk (i₀ + k + 1) :=
        (clientResult_readPackedProg _ _ _ _ _ _).trans (hqv (i₀ + k + 1) hpos1).2
      change (Memory.spec 0).clientState s _ = _
      rw [hr2, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      rfl
    have hstep_res : (Memory.spec 0).clientResult s (csrShiftDownStepProg ((crt, i₀), k)) =
        k + 1 := by
      unfold csrShiftDownStepProg
      simp only [pure_bind, clientResult_bind_prog, clientResult_pure_prog]
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (csrShiftDownStepProg ((crt, i₀), k)) := by
      unfold csrShiftDownStepProg
      simp only [pure_bind]
      have hqk_w : quotBitsWhp U n_max ≤ w :=
        (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
      refine validWhpProg_bind (validWhpProg_readPacked hw hpos1 hsegb.1) ?_
      refine validWhpProg_bind (validWhpProg_readPacked hw hpos1 hsegb.2.1) ?_
      refine validWhpProg_bind (validWhpProg_writePacked hw hqk_w hpos hsegb.1) ?_
      refine validWhpProg_bind
        (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hpos hsegb.2.1) ?_
      exact validWhpProg_pure _
    have hqv_nxt : ∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w m2 i =
          (csrShiftDown i₀ (k + 1) (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w m2 i =
          (csrShiftDown i₀ (k + 1) (q₀, v₀)).2 i := by
      intro i hi
      dsimp only [csrShiftDown, m2, m1]
      rw [readPacked_writePacked_disjoint hw hi hpos (by omega)]
      refine ⟨?_, ?_⟩
      · by_cases heq : i = i₀ + k
        · subst heq
          rw [readPacked_writePacked_self _ _ _ _ _ hqn_lt, Function.update_self]
        · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq, (hqv i hi).1]
      · by_cases heq : i = i₀ + k
        · subst heq
          rw [readPacked_writePacked_self _ _ _ _ _ hvn_lt, Function.update_self]
        · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
            readPacked_writePacked_disjoint hw hi hpos (by omega), (hqv i hi).2]
    have hlt_m := hlt_pos (Nat.succ_pos m)
    obtain ⟨hsafe_m, hfr_m, hvp_m, hqv_m, hout_m⟩ := ih (k + 1) q₀ v₀
      { mem := m2, frontier := s.frontier } (by omega) (fun _ => by omega) hqv_nxt
    have hadd : k + 1 + m = k + (m + 1) := by omega
    rw [hadd] at hqv_m
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientResult_width, clientState_width, hstep_st, hstep_res]; exact hsafe_m
    · rw [csrShiftDownLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hfr_m
    · rw [csrShiftDownLoopProg_succ]
      refine validWhpProg_bind hvp1 ?_
      rw [hstep_st, hstep_res]; exact hvp_m
    · intro i hi
      rw [csrShiftDownLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hqv_m i hi
    · rw [csrShiftDownLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
        hout_m a ha]
      dsimp only [m2, m1]
      rw [mem_writePacked_of_outside hw hpos (by omega),
        mem_writePacked_of_outside hw hpos (by omega)]

/-! ### Loop 3: `csrShiftUp` -/

/-- Single step of `csrShiftUp` (`d = ((crt, N), k)`). -/
@[irreducible] def csrShiftUpStepProg (d : (CsrRt × ℕ) × ℕ) : Memory.Prog ℕ := do
  let crt := d.1.1
  let N ← pure d.1.2
  let k ← pure d.2
  let one_v ← pure 1
  let idx ← pure (N - k)
  let src ← pure (idx - one_v)
  let qp ← readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), src)
  let vp ← readPackedGenProg (((crBase crt, crOffVal crt), (crValBits crt, crW crt)), src)
  writePackedGenProg ((((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), idx), qp)
  writePackedGenProg ((((crBase crt, crOffVal crt), (crValBits crt, crW crt)), idx), vp)
  pure (k + one_v)

/-- Precondition for `csrShiftUpStepProg`. -/
@[expose] def CsrShiftUpStepPre (w : ℕ) (d : (CsrRt × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  CsrRtEnvGen w d.1.1 ∧
  d.2 < d.1.2 ∧
  d.1.2 < crNMax d.1.1

private theorem memoryCost_csrShiftUpStepProg_pos (d : (CsrRt × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (csrShiftUpStepProg d) s := by
  unfold csrShiftUpStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 2 + _ ≥ 1
  omega

theorem realizes_csrShiftUpStep :
    Realizes .exact csrShiftUpStepProg
      (WordEncoding.encode (α := (CsrRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrShiftUpStepPre
      (fun _ _ => 0) := by
  unfold csrShiftUpStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨crt, N⟩, k⟩
    dsimp only [CsrShiftUpStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hk_lt, hN_lt⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hN_eq : crNMax crt = n_max := by rw [heq_crt]; rfl
    have hW_eq : crW crt = w := by rw [heq_crt]; rfl
    have hQB_eq : crQuotBits crt = quotBitsWhp U n_max := by rw [heq_crt]; rfl
    have hVB_eq : crValBits crt = valBits V := by rw [heq_crt]; rfl
    have hOQ_eq : crOffQuot crt = offQuotWhp c w n_max := by rw [heq_crt]; rfl
    have hOV_eq : crOffVal crt = offValWhp c U w n_max := by rw [heq_crt]; rfl
    rw [hN_eq] at hN_lt
    dsimp only [crBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | omega
    | exact (by omega : k + 1 ≤ N).trans_lt (hN_lt.trans hn_lt)
    | (rw [hW_eq, hQB_eq, hOQ_eq]; exact csr_quot_safe henv (by omega))
    | (rw [hW_eq, hVB_eq, hOV_eq]; exact csr_val_safe henv (by omega))
  )

/-- Loop wrapper for `iterate csrShiftUpStepProg`. -/
@[expose] def csrShiftUpLoopProg (d : ((CsrRt × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate csrShiftUpStepProg d.1.1 d.2 d.1.2

private theorem csrShiftUpLoopProg_zero (env : CsrRt × ℕ) (acc : ℕ) :
    csrShiftUpLoopProg ((env, acc), 0) = pure acc := rfl

private theorem csrShiftUpLoopProg_succ (env : CsrRt × ℕ) (acc m : ℕ) :
    csrShiftUpLoopProg ((env, acc), m + 1) =
      (csrShiftUpStepProg (env, acc) >>= fun acc' => csrShiftUpLoopProg ((env, acc'), m)) := rfl

theorem realizes_csrShiftUpLoop :
    Realizes .exact csrShiftUpLoopProg
      (WordEncoding.encode (α := ((CsrRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => iterationSafe csrShiftUpStepProg CsrShiftUpStepPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := CsrRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_csrShiftUpStep
    memoryCost_csrShiftUpStepProg_pos

private theorem csrShiftUpLoop_spec {c U V w n_max base N : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hN_lt : N < n_max) :
    let crt := mkCsrRt c U V w n_max base
    ∀ m k (q₀ v₀ : ℕ → ℕ) (s : Memory.State),
      k + m ≤ N →
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i =
          (csrShiftUp N k (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w s.mem i =
          (csrShiftUp N k (q₀, v₀)).2 i) →
      let prog := csrShiftUpLoopProg (((crt, N), k), m)
      let s' := (Memory.spec 0).clientState s prog
      iterationSafe csrShiftUpStepProg CsrShiftUpStepPre w (crt, N) m k s ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s'.mem i =
          (csrShiftUp N (k + m) (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w s'.mem i =
          (csrShiftUp N (k + m) (q₀, v₀)).2 i) ∧
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offPermAct c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro crt m
  have hw := henv.2.1
  have hseg := csr_seg_disjoint c U V w n_max
  have hsegb := csr_seg_base_bounds base c U V w n_max
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  induction m with
  | zero =>
    intro k q₀ v₀ s _ hqv
    dsimp only
    rw [csrShiftUpLoopProg_zero, clientState_pure_rw, Nat.add_zero]
    exact ⟨trivial, rfl, validWhpProg_pure _, hqv, fun _ _ => rfl⟩
  | succ m ih =>
    intro k q₀ v₀ s hkm hqv
    dsimp only
    have hk_lt : k < N := by omega
    have hidx : N - k < n_max := by omega
    have hsrc : N - k - 1 < n_max := by omega
    have hpre : CsrShiftUpStepPre w ((crt, N), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hk_lt, hN_lt⟩
    set qk := (csrShiftUp N k (q₀, v₀)).1
    set vk := (csrShiftUp N k (q₀, v₀)).2
    have hqp_lt : qk (N - k - 1) < 2 ^ quotBitsWhp U n_max := by
      rw [← (hqv (N - k - 1) hsrc).1]; exact readPacked_lt _ _ _ _ _
    have hvp_lt : vk (N - k - 1) < 2 ^ valBits V := by
      rw [← (hqv (N - k - 1) hsrc).2]; exact readPacked_lt _ _ _ _ _
    set m1 := writePacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem
      (N - k) (qk (N - k - 1))
    set m2 := writePacked (base + offValWhp c U w n_max) (valBits V) w m1
      (N - k) (vk (N - k - 1))
    have hstep_st : (Memory.spec 0).clientState s (csrShiftUpStepProg ((crt, N), k)) =
        { mem := m2, frontier := s.frontier } := by
      unfold csrShiftUpStepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
      have hr1 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)),
            N - k - 1)) = qk (N - k - 1) :=
        (clientResult_readPackedProg _ _ _ _ _ _).trans (hqv (N - k - 1) hsrc).1
      change (Memory.spec 0).clientState s _ = _
      rw [hr1, StateTransitionSpec.clientState_bind]
      have hr2 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffVal crt), (crValBits crt, crW crt)),
            N - k - 1)) = vk (N - k - 1) :=
        (clientResult_readPackedProg _ _ _ _ _ _).trans (hqv (N - k - 1) hsrc).2
      change (Memory.spec 0).clientState s _ = _
      rw [hr2, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      rfl
    have hstep_res : (Memory.spec 0).clientResult s (csrShiftUpStepProg ((crt, N), k)) =
        k + 1 := by
      unfold csrShiftUpStepProg
      simp only [pure_bind, clientResult_bind_prog, clientResult_pure_prog]
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (csrShiftUpStepProg ((crt, N), k)) := by
      unfold csrShiftUpStepProg
      simp only [pure_bind]
      have hqk_w : quotBitsWhp U n_max ≤ w :=
        (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
      refine validWhpProg_bind (validWhpProg_readPacked hw hsrc hsegb.1) ?_
      refine validWhpProg_bind (validWhpProg_readPacked hw hsrc hsegb.2.1) ?_
      refine validWhpProg_bind (validWhpProg_writePacked hw hqk_w hidx hsegb.1) ?_
      refine validWhpProg_bind
        (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hidx hsegb.2.1) ?_
      exact validWhpProg_pure _
    have hqv_nxt : ∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w m2 i =
          (csrShiftUp N (k + 1) (q₀, v₀)).1 i ∧
        readPacked (base + offValWhp c U w n_max) (valBits V) w m2 i =
          (csrShiftUp N (k + 1) (q₀, v₀)).2 i := by
      intro i hi
      dsimp only [csrShiftUp, m2, m1]
      rw [readPacked_writePacked_disjoint hw hi hidx (by omega)]
      refine ⟨?_, ?_⟩
      · by_cases heq : i = N - k
        · subst heq
          rw [readPacked_writePacked_self _ _ _ _ _ hqp_lt, Function.update_self]
        · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq, (hqv i hi).1]
      · by_cases heq : i = N - k
        · subst heq
          rw [readPacked_writePacked_self _ _ _ _ _ hvp_lt, Function.update_self]
        · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
            readPacked_writePacked_disjoint hw hi hidx (by omega), (hqv i hi).2]
    obtain ⟨hsafe_m, hfr_m, hvp_m, hqv_m, hout_m⟩ := ih (k + 1) q₀ v₀
      { mem := m2, frontier := s.frontier } (by omega) hqv_nxt
    have hadd : k + 1 + m = k + (m + 1) := by omega
    rw [hadd] at hqv_m
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientResult_width, clientState_width, hstep_st, hstep_res]; exact hsafe_m
    · rw [csrShiftUpLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hfr_m
    · rw [csrShiftUpLoopProg_succ]
      refine validWhpProg_bind hvp1 ?_
      rw [hstep_st, hstep_res]; exact hvp_m
    · intro i hi
      rw [csrShiftUpLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hqv_m i hi
    · rw [csrShiftUpLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
        hout_m a ha]
      dsimp only [m2, m1]
      rw [mem_writePacked_of_outside hw hidx (by omega),
        mem_writePacked_of_outside hw hidx (by omega)]

/-! ### Loop 4: `csrAdjustStarts` -/

/-- Single step of `csrAdjustStarts` (`d = ((crt, (b, decTag)), k)`). -/
@[irreducible] def csrAdjustStepProg (d : (CsrRt × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let crt := d.1.1
  let b ← pure d.1.2.1
  let decTag ← pure d.1.2.2
  let k ← pure d.2
  let zero_v ← pure 0
  let one_v ← pure 1
  let idx ← pure (b + one_v + k)
  let cur ← readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), idx)
  let nxt ←
    if decTag = one_v then
      if zero_v < cur then
        pure (cur - one_v)
      else
        pure zero_v
    else
      if cur < crNMax crt then
        pure (cur + one_v)
      else
        pure cur
  writePackedGenProg ((((crBase crt, crOffFb crt), (crGBits crt, crW crt)), idx), nxt)
  pure (k + one_v)

/-- Precondition for `csrAdjustStepProg`. -/
@[expose] def CsrAdjustStepPre (w : ℕ) (d : (CsrRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  CsrRtEnvGen w d.1.1 ∧
  d.1.2.1 + 1 + d.2 ≤ crM d.1.1

private theorem memoryCost_csrAdjustStepProg_pos (d : (CsrRt × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) :
    1 ≤ memoryCost (csrAdjustStepProg d) s := by
  unfold csrAdjustStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readPackedGen]
  omega

theorem realizes_csrAdjustStep :
    Realizes .exact csrAdjustStepProg
      (WordEncoding.encode (α := (CsrRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrAdjustStepPre
      (fun _ _ => 0) := by
  unfold csrAdjustStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨crt, b, decTag⟩, k⟩
    try clear hwords hmem
    dsimp only [CsrAdjustStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hidx_le⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hM_lt_n : numBucketsWhp n_max < n_max := numBuckets_lt_n_max henv
    have hM_eq : crM crt = numBucketsWhp n_max := by rw [heq_crt]; rfl
    have hN_eq : crNMax crt = n_max := by rw [heq_crt]; rfl
    have hW_eq : crW crt = w := by rw [heq_crt]; rfl
    have hGB_eq : crGBits crt = globalPtrBits n_max := by rw [heq_crt]; rfl
    have hOF_eq : crOffFb crt = offFbStart c U V w n_max := by rw [heq_crt]; rfl
    rw [hM_eq] at hidx_le
    try simp only [hN_eq] at *
    dsimp only [crBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | omega
    | exact (by omega : b + 1 + k ≤ n_max).trans_lt hn_lt
    | exact (by omega : k + 1 ≤ n_max).trans_lt hn_lt
    | (rw [hW_eq, hGB_eq, hOF_eq]; exact csr_fb_safe henv (by omega))
    | (have h1 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crt.1.1.1, crOffFb crt), (crGBits crt, crW crt)),
            b + 1 + k)) + 1 ≤ n_max := by omega
       exact h1.trans_lt hn_lt)
  )

/-- Loop wrapper for `iterate csrAdjustStepProg`. -/
@[expose] def csrAdjustLoopProg (d : ((CsrRt × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate csrAdjustStepProg d.1.1 d.2 d.1.2

private theorem csrAdjustLoopProg_zero (env : CsrRt × (ℕ × ℕ)) (acc : ℕ) :
    csrAdjustLoopProg ((env, acc), 0) = pure acc := rfl

private theorem csrAdjustLoopProg_succ (env : CsrRt × (ℕ × ℕ)) (acc m : ℕ) :
    csrAdjustLoopProg ((env, acc), m + 1) =
      (csrAdjustStepProg (env, acc) >>= fun acc' => csrAdjustLoopProg ((env, acc'), m)) := rfl

theorem realizes_csrAdjustLoop :
    Realizes .exact csrAdjustLoopProg
      (WordEncoding.encode (α := ((CsrRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => iterationSafe csrAdjustStepProg CsrAdjustStepPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := CsrRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_csrAdjustStep
    memoryCost_csrAdjustStepProg_pos

private theorem csrAdjustStarts_unchanged_ge (b : ℕ) (dec : Bool) :
    ∀ k (f : ℕ → ℕ) x, b + 1 + k ≤ x → csrAdjustStarts b dec k f x = f x := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro f x hx
    dsimp only [csrAdjustStarts]
    rw [Function.update_of_ne (by omega)]
    exact ih f x (by omega)

private theorem csrAdjustLoop_spec {c U V w n_max base b : ℕ} {dec : Bool}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let crt := mkCsrRt c U V w n_max base
    let decTag := if dec then 1 else 0
    ∀ m k (f₀ : ℕ → ℕ) (s : Memory.State),
      b + 1 + k + m ≤ numBucketsWhp n_max + 1 →
      (∀ x ≤ numBucketsWhp n_max,
        (dec = true → f₀ x ≤ n_max) ∧ (dec = false → f₀ x < n_max)) →
      (∀ x ≤ numBucketsWhp n_max,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x =
          csrAdjustStarts b dec k f₀ x) →
      let prog := csrAdjustLoopProg (((crt, (b, decTag)), k), m)
      let s' := (Memory.spec 0).clientState s prog
      iterationSafe csrAdjustStepProg CsrAdjustStepPre w (crt, (b, decTag)) m k s ∧
      s'.frontier = s.frontier ∧
      ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ x ≤ numBucketsWhp n_max,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s'.mem x =
          csrAdjustStarts b dec (k + m) f₀ x) ∧
      (∀ a, (a < base + offFbStart c U V w n_max ∨
          base + offFbStart c U V w n_max +
            packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ≤ a) →
        s'.mem a = s.mem a) := by
  intro crt decTag m
  have hw := henv.2.1
  have hsegb := csr_seg_base_bounds base c U V w n_max
  have hg_le := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  induction m with
  | zero =>
    intro k f₀ s _ _ hfb
    dsimp only
    rw [csrAdjustLoopProg_zero, clientState_pure_rw, Nat.add_zero]
    exact ⟨trivial, rfl, validWhpProg_pure _, hfb, fun _ _ => rfl⟩
  | succ m ih =>
    intro k f₀ s hbkm hbnd hfb
    dsimp only
    set idx := b + 1 + k
    have hidx_le_M : idx ≤ numBucketsWhp n_max := by omega
    have hidx_lt : idx < numBucketsWhp n_max + 1 := by omega
    have hpre : CsrAdjustStepPre w ((crt, (b, decTag)), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hidx_le_M⟩
    set fk := csrAdjustStarts b dec k f₀
    have hfk_idx : fk idx = f₀ idx := csrAdjustStarts_unchanged_ge b dec k f₀ idx le_rfl
    set nxtVal := if dec then fk idx - 1 else fk idx + 1
    have hnxt_le : nxtVal ≤ n_max := by
      dsimp only [nxtVal]; rw [hfk_idx]
      cases dec
      · have := (hbnd idx hidx_le_M).2 rfl
        simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · have := (hbnd idx hidx_le_M).1 rfl
        simp only [↓reduceIte]; omega
    set m1 := writePacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
      idx nxtVal
    have hstep_st : (Memory.spec 0).clientState s (csrAdjustStepProg ((crt, (b, decTag)), k)) =
        { mem := m1, frontier := s.frontier } := by
      unfold csrAdjustStepProg
      simp only [pure_bind, clientState_bind_prog, clientState_readPackedGen]
      have hr1 : (Memory.spec 0).clientResult s
          (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b + 1 + k)) =
          fk idx :=
        (clientResult_readPackedProg _ _ _ _ _ _).trans (hfb idx hidx_le_M)
      rw [hr1]
      have hcrN : crNMax crt = n_max := rfl
      cases dec
      · have hfk_lt : fk idx < n_max := by rw [hfk_idx]; exact (hbnd idx hidx_le_M).2 rfl
        dsimp only [decTag, nxtVal]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one, hcrN, hfk_lt,
          clientState_bind_prog, clientState_writePackedGen, clientState_pure_prog]
        rfl
      · dsimp only [decTag, nxtVal]
        simp only [↓reduceIte]
        by_cases hpos_fk : 0 < fk idx
        · simp only [hpos_fk, ↓reduceIte, clientState_bind_prog,
            clientState_writePackedGen, clientState_pure_prog]
          rfl
        · have hfk0 : fk idx = 0 := by omega
          simp only [hpos_fk, ↓reduceIte,
            clientState_bind_prog, clientState_writePackedGen, clientState_pure_prog]
          dsimp only [m1, nxtVal]
          simp only [↓reduceIte, hfk0, Nat.zero_sub]
          rfl
    have hstep_res : (Memory.spec 0).clientResult s (csrAdjustStepProg ((crt, (b, decTag)), k)) =
        k + 1 := by
      unfold csrAdjustStepProg
      simp only [pure_bind, clientResult_bind_prog, clientState_readPackedGen]
      split_ifs <;> simp only [clientResult_bind_prog, clientResult_pure_prog]
    have hvp1 : ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s
        (csrAdjustStepProg ((crt, (b, decTag)), k)) := by
      unfold csrAdjustStepProg
      simp only [pure_bind]
      refine validWhpProg_bind (validWhpProg_readPacked hw hidx_lt hsegb.2.2) ?_
      rw [clientState_readPackedGen_rw]
      split_ifs <;>
        exact validWhpProg_bind (validWhpProg_writePacked hw hg_le hidx_lt hsegb.2.2)
          (validWhpProg_pure _)
    have hfb_nxt : ∀ x ≤ numBucketsWhp n_max,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w m1 x =
          csrAdjustStarts b dec (k + 1) f₀ x := by
      intro x hx
      dsimp only [csrAdjustStarts, m1]
      by_cases heq : x = idx
      · subst heq
        rw [readPacked_writePacked_self _ _ _ _ _ (lt_two_pow_globalPtrBits_of_le hnxt_le),
          Function.update_self]
      · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq, hfb x hx]
    obtain ⟨hsafe_m, hfr_m, hvp_m, hfb_m, hout_m⟩ := ih (k + 1) f₀
      { mem := m1, frontier := s.frontier } (by omega) hbnd hfb_nxt
    have hadd : k + 1 + m = k + (m + 1) := by omega
    rw [hadd] at hfb_m
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientResult_width, clientState_width, hstep_st, hstep_res]; exact hsafe_m
    · rw [csrAdjustLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hfr_m
    · rw [csrAdjustLoopProg_succ]
      refine validWhpProg_bind hvp1 ?_
      rw [hstep_st, hstep_res]; exact hvp_m
    · intro x hx
      rw [csrAdjustLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      exact hfb_m x hx
    · rw [csrAdjustLoopProg_succ, StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
        hout_m a ha]
      exact mem_writePacked_of_outside hw hidx_lt (by omega)

/-! ### Top-Level `csrPrefixGenProg` and `csrStepOpGenProg` -/

private theorem csrAdjustLoop_safe {c U V w n_max base b decTag : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let crt := mkCsrRt c U V w n_max base
    ∀ m k (s : Memory.State), b + 1 + k + m ≤ numBucketsWhp n_max + 1 →
      iterationSafe csrAdjustStepProg CsrAdjustStepPre w (crt, (b, decTag)) m k s := by
  intro crt m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro k s hbkm
    have hidx_le : b + 1 + k ≤ crM crt := by change b + 1 + k ≤ numBucketsWhp n_max; omega
    have hpre : CsrAdjustStepPre w ((crt, (b, decTag)), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hidx_le⟩
    have hres : (Memory.spec 0).clientResult s (csrAdjustStepProg ((crt, (b, decTag)), k)) =
        k + 1 := by
      unfold csrAdjustStepProg
      simp only [pure_bind, clientResult_bind_prog, clientState_readPackedGen]
      split_ifs <;> simp only [clientResult_bind_prog, clientResult_pure_prog]
    refine ⟨hpre, ?_⟩
    rw [clientResult_width, hres]
    exact ih (k + 1) _ (by omega)

private theorem csrShiftUpLoop_safe {c U V w n_max base N : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hN_lt : N < n_max) :
    let crt := mkCsrRt c U V w n_max base
    ∀ m k (s : Memory.State), k + m ≤ N →
      iterationSafe csrShiftUpStepProg CsrShiftUpStepPre w (crt, N) m k s := by
  intro crt m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro k s hkm
    have hk_lt : k < N := by omega
    have hpre : CsrShiftUpStepPre w ((crt, N), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hk_lt, hN_lt⟩
    have hres : (Memory.spec 0).clientResult s (csrShiftUpStepProg ((crt, N), k)) = k + 1 := by
      unfold csrShiftUpStepProg
      simp only [pure_bind, clientResult_bind_prog, clientResult_pure_prog]
    refine ⟨hpre, ?_⟩
    rw [clientResult_width, hres]
    exact ih (k + 1) _ (by omega)

private theorem csrShiftDownLoop_safe {c U V w n_max base i₀ : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let crt := mkCsrRt c U V w n_max base
    ∀ m k (s : Memory.State), (m > 0 → i₀ + k + m < n_max) →
      iterationSafe csrShiftDownStepProg CsrShiftDownStepPre w (crt, i₀) m k s := by
  intro crt m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro k s hlt
    have hpos1 : i₀ + k + 1 < n_max := by have := hlt (Nat.succ_pos m); omega
    have hpre : CsrShiftDownStepPre w ((crt, i₀), k) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hpos1⟩
    have hres : (Memory.spec 0).clientResult s (csrShiftDownStepProg ((crt, i₀), k)) = k + 1 := by
      unfold csrShiftDownStepProg
      simp only [pure_bind, clientResult_bind_prog, clientResult_pure_prog]
    refine ⟨hpre, ?_⟩
    rw [clientResult_width, hres]
    have hm := hlt (Nat.succ_pos m)
    exact ih (k + 1) _ (fun _ => by omega)

/-- Return tuple of `csrPrefixGenProg`: `(((crt, ok), (b, q_val)), ((lo, hi), (N, f1)))`. -/
abbrev CsrPrefixOut : Type :=
  ((CsrRt × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))

/-- Precondition for `csrPrefixGenProg` (`d = ((wp, base), u_val)`). -/
@[expose] def CsrPrefixPre (w : ℕ) (d : (WhpParams × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w d.1.2 ∧
    d.1.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.1.2 c U w₀ n_max θ s.mem

/-- Stage 1 of `csrPrefixGenProg`: extracts `(crt, (b, q_val))` in 3 subroutine calls. -/
@[irreducible] def csrSplitAndBoundsProg (d : (WhpParams × ℕ) × ℕ) :
    Memory.Prog (CsrRt × (ℕ × ℕ)) := do
  let hrt ← mkHashRtGenProg d.1
  let crt ← mkCsrRtGenProg (d.1.1.1, d.1.2)
  let bq ← feistelSplitRtProg (hrt, d.2)
  pure (crt, bq)

theorem realizes_csrSplitAndBounds :
    Realizes .exact csrSplitAndBoundsProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := CsrRt × (ℕ × ℕ)))
      CsrPrefixPre
      (fun _ _ => 0) := by
  unfold csrSplitAndBoundsProg
  have hmh := realizes_mkHashRtGen
  have hmc := realizes_mkCsrRtGen
  have hfs := realizes_feistelSplitRt
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    try clear hwords hmem
    dsimp only [CsrPrefixPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, hseed⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hth := henv.2.2.2.1
    try simp only [
      (mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hth s).1,
      (mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hth s).2.1] at *
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
    try simp only [hwp1,
      (mkCsrRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hth s).1] at *
    exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

/-- Stage 2 of `csrPrefixGenProg` (`d = (crt, (b, q_val))`, 12 words): reads `(lo, hi, N)` and
scans `lo .. hi - 1`. -/
@[irreducible] def csrReadAndScanProg (d : CsrRt × (ℕ × ℕ)) : Memory.Prog CsrPrefixOut := do
  let crt := d.1
  let b ← pure d.2.1
  let q_val ← pure d.2.2
  let zero_v ← pure 0
  let one_v ← pure 1
  let M ← pure (crM crt)
  let nMax ← pure (crNMax crt)
  if b < M then
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b)
    let hi ← readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b1)
    let N ← readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), M)
    if hi < lo then
      pure (((crt, zero_v), (b, q_val)), ((zero_v, zero_v), (zero_v, zero_v)))
    else if N < hi then
      pure (((crt, zero_v), (b, q_val)), ((zero_v, zero_v), (zero_v, zero_v)))
    else if nMax < N then
      pure (((crt, zero_v), (b, q_val)), ((zero_v, zero_v), (zero_v, zero_v)))
    else
      let len ← pure (hi - lo)
      let scanOut ← csrScanLoopProg (((crt, (lo, q_val)), (zero_v, zero_v)), len)
      pure (((crt, one_v), (b, q_val)), ((lo, hi), (N, scanOut.2)))
  else
    pure (((crt, zero_v), (b, q_val)), ((zero_v, zero_v), (zero_v, zero_v)))

theorem realizes_csrReadAndScan :
    Realizes .exact csrReadAndScanProg
      (WordEncoding.encode (α := CsrRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := CsrPrefixOut))
      (fun w d _ => CsrRtEnvGen w d.1)
      (fun _ _ => 0) := by
  unfold csrReadAndScanProg
  have hrp := realizes_readPackedGen
  have hsl := realizes_csrScanLoop
  realize
  all_goals (
    rcases d with ⟨crt, b, q_val⟩
    try clear hwords hmem
    dsimp only [CsrRtEnvGen] at h
    obtain ⟨c, U, V, w₀, n_max, henv, heq_crt⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hM_lt_n : numBucketsWhp n_max < n_max := numBuckets_lt_n_max henv
    have hB_eq : crBase crt = crt.1.1.1 := rfl
    have hW_eq : crW crt = w := by rw [heq_crt]; rfl
    have hN_eq : crNMax crt = n_max := by rw [heq_crt]; rfl
    have hM_eq : crM crt = numBucketsWhp n_max := by rw [heq_crt]; rfl
    have hG_eq : crGBits crt = globalPtrBits n_max := by rw [heq_crt]; rfl
    have hOF_eq : crOffFb crt = offFbStart c U V w n_max := by rw [heq_crt]; rfl
    try simp only [hW_eq, hN_eq, hM_eq, hG_eq, hOF_eq,
      clientState_readPackedGen, clientResult_readPackedGen] at *
    dsimp only [crBase] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact (by omega : b + 1 ≤ numBucketsWhp n_max).trans_lt (hM_lt_n.trans hn_lt)
    | (apply to_true_exists (w := w); refine csr_fb_safe henv ?_; omega)
    | omega
    | (rw [heq_crt]
       dsimp only [mkCsrRt] at *
       refine (csrScanLoop_spec henv _ _ 0 0 ?_ (Nat.zero_le _)).1
       omega)
  )

/-- Shared CSR prefix: splits `u_val` into `(b, q_val)`, reads `(lo, hi, N)`, and scans
`lo .. hi - 1`. -/
@[irreducible] def csrPrefixGenProg (d : (WhpParams × ℕ) × ℕ) : Memory.Prog CsrPrefixOut := do
  let cbq ← csrSplitAndBoundsProg d
  csrReadAndScanProg cbq

private theorem csrSplitAndBoundsProg_spec {c U V w n_max base u_val : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := csrSplitAndBoundsProg ((mkWhpParams c U V w n_max, base), u_val)
    let h1 := bktHash c U n_max θ.1
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (mkCsrRt c U V w n_max base,
        (feistelBucket (bWhp n_max) h1 u_val, keyQuotient (bWhp n_max) u_val)) ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, _, hmh_vp⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
  obtain ⟨hmc_st, hmc_res, _, hmc_vp⟩ := mkCsrRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, _, hfs_vp⟩ := feistelSplitRtProg_spec (V := V) (u_val := u_val) henv
    hseed (s := s)
  dsimp only
  unfold csrSplitAndBoundsProg
  simp only [hwp1]
  refine ⟨?_, ?_, ?_⟩
  · simp only [clientState_bind_prog, clientState_pure_prog, hmh_st, hmh_res, hmc_st, hfs_st]
  · simp only [clientResult_bind_prog, clientResult_pure_prog, hmh_st, hmh_res, hmc_st, hmc_res,
      hfs_st, hfs_res]
  · refine validWhpProg_bind hmh_vp ?_
    rw [hmh_st, hmh_res]
    refine validWhpProg_bind hmc_vp ?_
    rw [hmc_st, hmc_res]
    refine validWhpProg_bind hfs_vp ?_
    rw [hfs_st]
    exact validWhpProg_pure _

theorem realizes_csrPrefixGen :
    Realizes .exact csrPrefixGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := CsrPrefixOut))
      CsrPrefixPre
      (fun _ _ => 0) := by
  unfold csrPrefixGenProg
  have hsb := realizes_csrSplitAndBounds
  have hrs := realizes_csrReadAndScan
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    try clear hwords hmem
    dsimp only [CsrPrefixPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, hseed⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | (rw [(csrSplitAndBoundsProg_spec (V := V) (u_val := u_val) henv hseed (s := s)).2.1]
       exact ⟨c, U, V, w, n_max, henv, rfl⟩)
  )

private theorem csrPrefixGenProg_invariant {c U V w n_max base u_val : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := csrPrefixGenProg ((mkWhpParams c U V w n_max, base), u_val)
    let out := (Memory.spec 0).clientResult s prog
    (Memory.spec 0).clientState s prog = s ∧
    out.1.1.1 = mkCsrRt c U V w n_max base ∧
    (out.1.1.2 = 1 →
      out.1.2.1 < numBucketsWhp n_max ∧
      out.2.1.1 ≤ out.2.1.2 ∧
      out.2.1.2 ≤ out.2.2.1 ∧
      out.2.2.1 ≤ n_max ∧
      out.2.2.2 ≤ n_max) := by
  obtain ⟨hsb_st, hsb_res, _⟩ := csrSplitAndBoundsProg_spec (V := V) (u_val := u_val) henv hseed
    (s := s)
  dsimp only
  unfold csrPrefixGenProg
  set crt := mkCsrRt c U V w n_max base
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val
  set q_val := keyQuotient (bWhp n_max) u_val
  set lo := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b
  set hi := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem (b + 1)
  set N := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
    (numBucketsWhp n_max)
  have hr_b : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b)) = lo :=
    clientResult_readPackedProg _ _ _ _ _ _
  have hr_b1 : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b + 1)) = hi :=
    clientResult_readPackedProg _ _ _ _ _ _
  have hr_M : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), crM crt)) = N :=
    clientResult_readPackedProg _ _ _ _ _ _
  have hb_lt : b < crM crt := feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u_val
  have hcrN : crNMax crt = n_max := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind_rw, hsb_st, hsb_res]
    unfold csrReadAndScanProg
    simp only [pure_bind, hb_lt, ↓reduceIte, clientState_bind_prog, clientState_readPackedGen]
    rw [hr_b, hr_b1, hr_M, hcrN]
    by_cases h1 : hi < lo
    · simp only [h1, ↓reduceIte, clientState_pure_prog]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : N < hi
      · simp only [h2, ↓reduceIte, clientState_pure_prog]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : n_max < N
        · simp only [h3, ↓reduceIte, clientState_pure_prog]
        · simp only [h3, ↓reduceIte, clientState_bind_prog, clientState_pure_prog]
          exact (csrScanLoop_spec (lo := lo) (q_val := q_val) henv s (hi - lo) 0 0
            (by omega) (Nat.zero_le _)).2.1
  · rw [clientResult_bind_prog, hsb_st, hsb_res]
    unfold csrReadAndScanProg
    simp only [pure_bind, hb_lt, ↓reduceIte, clientResult_bind_prog, clientState_readPackedGen]
    rw [hr_b, hr_b1, hr_M, hcrN]
    split_ifs <;> simp only [clientResult_bind_prog, clientResult_pure_prog]
  · rw [clientResult_bind_prog, hsb_st, hsb_res]
    unfold csrReadAndScanProg
    simp only [pure_bind, hb_lt, ↓reduceIte, clientResult_bind_prog, clientState_readPackedGen]
    rw [hr_b, hr_b1, hr_M, hcrN]
    by_cases h1 : hi < lo
    · simp only [h1, ↓reduceIte, clientResult_pure_prog, Nat.zero_ne_one, IsEmpty.forall_iff]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : N < hi
      · simp only [h2, ↓reduceIte, clientResult_pure_prog, Nat.zero_ne_one, IsEmpty.forall_iff]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : n_max < N
        · simp only [h3, ↓reduceIte, clientResult_pure_prog, Nat.zero_ne_one, IsEmpty.forall_iff]
        · simp only [h3, ↓reduceIte, clientResult_bind_prog, clientResult_pure_prog]
          intro _
          have hsc := csrScanLoop_spec (lo := lo) (q_val := q_val) henv s (hi - lo) 0 0
            (by omega) (Nat.zero_le _)
          exact ⟨hb_lt, by omega, by omega, by omega, hsc.2.2.1⟩

private theorem fbStart_le_of_adj_aux {M : ℕ} {fb : ℕ → ℕ} (hadj : ∀ b < M, fb b ≤ fb (b + 1)) :
    ∀ x y, x ≤ y → y ≤ M → fb x ≤ fb y := by
  intro x y hxy hyM
  induction y with
  | zero =>
    have : x = 0 := by omega
    subst this; exact le_rfl
  | succ y ih =>
    rcases Nat.eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hadj y (by omega))

private theorem csrScanRange_congr {q1 q2 : ℕ → ℕ} {lo q_val : ℕ} :
    ∀ len, (∀ k < len, q1 (lo + k) = q2 (lo + k)) →
      csrScanRange q1 lo q_val len = csrScanRange q2 lo q_val len := by
  intro len
  induction len with
  | zero => intros; rfl
  | succ len ih =>
    intro h
    dsimp only [csrScanRange]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h len (Nat.lt_succ_self len)]

private theorem csrScanRange_lt_of_ne_zero {qArr : ℕ → ℕ} {lo q_val : ℕ} :
    ∀ len, csrScanRange qArr lo q_val len ≠ 0 →
      lo ≤ csrScanRange qArr lo q_val len - 1 ∧
      csrScanRange qArr lo q_val len - 1 < lo + len := by
  intro len
  induction len with
  | zero => intro h; exact absurd rfl h
  | succ len ih =>
    intro hne
    dsimp only [csrScanRange] at hne ⊢
    set prev := csrScanRange qArr lo q_val len
    by_cases hp : prev != 0
    · have hp_ne : prev ≠ 0 := by simpa using hp
      simp only [hp, ↓reduceIte]
      obtain ⟨h1, h2⟩ := ih hp_ne
      exact ⟨h1, by omega⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hne ⊢
      by_cases hq : qArr (lo + len) == q_val
      · simp only [hq, ↓reduceIte]
        exact ⟨by omega, by omega⟩
      · simp [hq] at hne

private theorem csrPrefixGenProg_spec {c U V w n_max base u_val : ℕ} {θ : SeedWhp c U n_max}
    {csr : CsrState} {dict : Dictionary.State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hv : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict) :
    let prog := csrPrefixGenProg ((mkWhpParams c U V w n_max, base), u_val)
    let h1 := bktHash c U n_max θ.1
    let b := feistelBucket (bWhp n_max) h1 u_val
    let q_val := keyQuotient (bWhp n_max) u_val
    let lo := csr.fbStart b
    let hi := csr.fbStart (b + 1)
    let N := csr.fbStart (numBucketsWhp n_max)
    let f1 := csrScanRange csr.qArr lo q_val (hi - lo)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (((mkCsrRt c U V w n_max base, 1), (b, q_val)), ((lo, hi), (N, f1))) ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hsegb := csr_seg_base_bounds base c U V w n_max
  obtain ⟨hsb_st, hsb_res, hsb_vp⟩ := csrSplitAndBoundsProg_spec (V := V) (u_val := u_val)
    henv hseed (s := s)
  set M := numBucketsWhp n_max
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u_val
  set q_val := keyQuotient (bWhp n_max) u_val
  set crt := mkCsrRt c U V w n_max base
  have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u_val
  have hmono := fbStart_le_of_adj_aux hv.2.1
  have hlo_hi : csr.fbStart b ≤ csr.fbStart (b + 1) := hv.2.1 b hb_lt
  have hhi_N : csr.fbStart (b + 1) ≤ csr.fbStart M := hmono (b + 1) M (by omega) le_rfl
  have hN_le : csr.fbStart M ≤ n_max := hv.2.2.1
  have hnot1 : ¬(csr.fbStart (b + 1) < csr.fbStart b) := Nat.not_lt.mpr hlo_hi
  have hnot2 : ¬(csr.fbStart M < csr.fbStart (b + 1)) := Nat.not_lt.mpr hhi_N
  have hnot3 : ¬(n_max < csr.fbStart M) := Nat.not_lt.mpr hN_le
  set len := csr.fbStart (b + 1) - csr.fbStart b
  have hscan := csrScanLoop_spec (lo := csr.fbStart b) (q_val := q_val) henv s
    len 0 0 (by omega) (Nat.zero_le _)
  have hq_congr : csrScanRange
      (fun i => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i)
      (csr.fbStart b) q_val len =
      csrScanRange csr.qArr (csr.fbStart b) q_val len :=
    csrScanRange_congr len fun k hk => (hrep.2.2 (csr.fbStart b + k) (by omega)).1
  have hscan_res : (Memory.spec 0).clientResult s
      (csrScanLoopProg (((crt, (csr.fbStart b, q_val)), (0, 0)), len)) =
      (len, csrScanRange csr.qArr (csr.fbStart b) q_val len) := by
    have hr := hscan.2.2.2.2 rfl
    rw [Nat.zero_add] at hr
    rwa [hq_congr] at hr
  have hr_b : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b)) =
      csr.fbStart b :=
    (clientResult_readPackedProg _ _ _ _ _ _).trans (hrep.2.1 b hb_lt.le)
  have hr_b1 : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), b + 1)) =
      csr.fbStart (b + 1) :=
    (clientResult_readPackedProg _ _ _ _ _ _).trans (hrep.2.1 (b + 1) hb_lt)
  have hr_M : (Memory.spec 0).clientResult s
      (readPackedGenProg (((crBase crt, crOffFb crt), (crGBits crt, crW crt)), M)) =
      csr.fbStart M :=
    (clientResult_readPackedProg _ _ _ _ _ _).trans (hrep.2.1 M le_rfl)
  have hcrM : crM crt = M := rfl
  have hcrN : crNMax crt = n_max := rfl
  have hst_all := (csrPrefixGenProg_invariant (V := V) (u_val := u_val) henv hseed).1
  dsimp only
  refine ⟨hst_all, ?_, ?_⟩
  · unfold csrPrefixGenProg
    rw [clientResult_bind_prog, hsb_st, hsb_res]
    unfold csrReadAndScanProg
    simp only [pure_bind, hcrM, hb_lt, ↓reduceIte, clientResult_bind_prog,
      clientState_readPackedGen]
    rw [hr_b, hr_b1, hr_M, hcrN]
    simp only [hnot1, hnot2, hnot3, ↓reduceIte, clientResult_bind_prog, clientResult_pure_prog]
    dsimp only [crt, len, b] at hscan_res ⊢
    rw [hscan_res]
  · unfold csrPrefixGenProg
    refine validWhpProg_bind hsb_vp ?_
    rw [hsb_st, hsb_res]
    unfold csrReadAndScanProg
    simp only [pure_bind, hcrM, hb_lt, ↓reduceIte]
    refine validWhpProg_bind
      (validWhpProg_readPacked hw (by omega : b < M + 1) hsegb.2.2) ?_
    rw [clientState_readPackedGen_rw, hr_b]
    refine validWhpProg_bind
      (validWhpProg_readPacked hw (by omega : b + 1 < M + 1) hsegb.2.2) ?_
    rw [clientState_readPackedGen_rw, hr_b1]
    refine validWhpProg_bind
      (validWhpProg_readPacked hw (Nat.lt_succ_self M) hsegb.2.2) ?_
    rw [clientState_readPackedGen_rw, hr_M, hcrN]
    simp only [hnot1, hnot2, hnot3, ↓reduceIte]
    refine validWhpProg_bind hscan.2.2.2.1 ?_
    exact validWhpProg_pure _

/-- Precondition for `csrStepBodyProg` (`d = ((pre, opTag), v_val)`, 18 words). -/
@[expose] def CsrStepBodyPre (w : ℕ) (d : (CsrPrefixOut × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  let out := d.1.1
  CsrRtEnvGen w out.1.1.1 ∧
  (out.1.1.2 = 1 →
    out.1.2.1 < crM out.1.1.1 ∧
    out.2.1.1 ≤ out.2.1.2 ∧
    out.2.1.2 ≤ out.2.2.1 ∧
    out.2.2.1 ≤ crNMax out.1.1.1 ∧
    out.2.2.2 ≤ crNMax out.1.1.1)

/-- 18-word body of `csrStepOpGenProg` (`d = ((pre, opTag), v_val)`), avoiding `WhpParams` in
the live environment across branches. -/
@[irreducible] def csrStepBodyProg (d : (CsrPrefixOut × ℕ) × ℕ) :
    Memory.Prog (ℕ × ℕ) := do
  let pre := d.1.1
  let crt := pre.1.1.1
  let ok ← pure pre.1.1.2
  let b ← pure pre.1.2.1
  let q_val ← pure pre.1.2.2
  let hi ← pure pre.2.1.2
  let N ← pure pre.2.2.1
  let f1 ← pure pre.2.2.2
  let opTag ← pure d.1.2
  let v_val ← pure d.2
  let zero_v ← pure 0
  let one_v ← pure 1
  if ok = one_v then
    let M ← pure (crM crt)
    let nMax ← pure (crNMax crt)
    if opTag = zero_v then
      if f1 = zero_v then
        pure (zero_v, zero_v)
      else
        let idx ← pure (f1 - one_v)
        let val ← readPackedGenProg
          (((crBase crt, crOffVal crt), (crValBits crt, crW crt)), idx)
        pure (one_v, val)
    else if opTag = one_v then
      if f1 = zero_v then
        if N < nMax then
          let shCnt ← pure (N - hi)
          let _ ← csrShiftUpLoopProg (((crt, N), zero_v), shCnt)
          writePackedGenProg
            ((((crBase crt, crOffQuot crt), (crQuotBits crt, crW crt)), hi), q_val)
          writePackedGenProg
            ((((crBase crt, crOffVal crt), (crValBits crt, crW crt)), hi), v_val)
          let adjCnt ← pure (M - b)
          let _ ← csrAdjustLoopProg (((crt, (b, zero_v)), zero_v), adjCnt)
          pure (zero_v, zero_v)
        else
          pure (zero_v, zero_v)
      else
        let idx ← pure (f1 - one_v)
        writePackedGenProg
          ((((crBase crt, crOffVal crt), (crValBits crt, crW crt)), idx), v_val)
        pure (zero_v, zero_v)
    else
      if f1 = zero_v then
        pure (zero_v, zero_v)
      else
        let i₀ ← pure (f1 - one_v)
        if i₀ < N then
          let shCnt ← pure (N - one_v - i₀)
          let _ ← csrShiftDownLoopProg (((crt, i₀), zero_v), shCnt)
          let adjCnt ← pure (M - b)
          let _ ← csrAdjustLoopProg (((crt, (b, one_v)), zero_v), adjCnt)
          pure (zero_v, zero_v)
        else
          pure (zero_v, zero_v)
  else
    pure (zero_v, zero_v)

theorem realizes_csrStepBody :
    Realizes .exact csrStepBodyProg
      (WordEncoding.encode (α := (CsrPrefixOut × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CsrStepBodyPre
      (fun _ _ => 0) := by
  unfold csrStepBodyProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hsu := realizes_csrShiftUpLoop
  have hsd := realizes_csrShiftDownLoop
  have had := realizes_csrAdjustLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨crt, ok⟩, b, q_val⟩, ⟨lo, hi⟩, N, f1⟩, opTag⟩, v_val⟩
    try clear hwords hmem
    dsimp only [CsrStepBodyPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hpre_ok⟩ := h
    have hw := henv.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hn_lt : n_max < 2 ^ w := henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1
    have hM_lt_n : numBucketsWhp n_max < n_max := numBuckets_lt_n_max henv
    dsimp only [crBase, crW, crNMax, crM, crQuotBits, crValBits, crOffQuot, crOffVal] at *
    have hW_eq : crt.1.1.2 = w := congrArg crW heq_crt
    have hN_eq : crt.1.2.1 = n_max := congrArg crNMax heq_crt
    have hM_eq : crt.1.2.2 = numBucketsWhp n_max := congrArg crM heq_crt
    have hQB_eq : crt.2.1.1.2 = quotBitsWhp U n_max := congrArg crQuotBits heq_crt
    have hVB_eq : crt.2.1.2.1 = valBits V := congrArg crValBits heq_crt
    have hOQ_eq : crt.2.2.1 = offQuotWhp c w n_max := congrArg crOffQuot heq_crt
    have hOV_eq : crt.2.2.2 = offValWhp c U w n_max := congrArg crOffVal heq_crt
    try simp only [hW_eq, hN_eq, hM_eq, hQB_eq, hVB_eq, hOQ_eq, hOV_eq] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | (obtain ⟨hb_lt, hlo_hi, hhi_N, hN_le, hf1_le⟩ := hpre_ok (by assumption)
       first
       | omega
       | (apply to_true_exists (w := w); refine csr_val_safe henv ?_; omega)
       | (apply to_true_exists (w := w); refine csr_quot_safe henv ?_; omega)
       | (rw [heq_crt]; refine csrShiftUpLoop_safe henv (by assumption) _ 0 _ ?_; omega)
       | (rw [heq_crt]; refine csrShiftDownLoop_safe henv _ 0 _ (fun _ => ?_); omega)
       | (rw [heq_crt]; refine csrAdjustLoop_safe henv _ 0 _ ?_; omega))
  )

/-- Precondition for `csrStepOpGenProg` (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[expose] def CsrStepOpPre (w : ℕ) (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) : Prop :=
  CsrPrefixPre w (d.1.1, d.2.1) s

/-- CSR fallback operation dispatcher (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[irreducible] def csrStepOpGenProg (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) :
    Memory.Prog (ℕ × ℕ) := do
  let pre ← csrPrefixGenProg (d.1.1, d.2.1)
  csrStepBodyProg ((pre, d.1.2), d.2.2)

theorem realizes_csrStepOpGen :
    Realizes .exact csrStepOpGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      CsrStepOpPre
      (fun _ _ => 0) := by
  unfold csrStepOpGenProg
  have hpr := realizes_csrPrefixGen
  have hbd := realizes_csrStepBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, opTag⟩, u_val, v_val⟩
    try clear hwords hmem
    dsimp only [CsrStepOpPre, CsrPrefixPre, CsrStepBodyPre] at h ⊢
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, hseed⟩ := h
    have hw_eq := henv.2.2.1
    subst hw_eq
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | (obtain ⟨_, hcrt, hok⟩ :=
         csrPrefixGenProg_invariant (V := V) (u_val := u_val) henv hseed (s := s)
       have hB :
           ((Memory.spec 0).clientResult s
             (csrPrefixGenProg ((mkWhpParams c U V w n_max, base), u_val))).1.1.1.1.1.1 = base :=
         congrArg crBase hcrt
       have hM :
           ((Memory.spec 0).clientResult s
             (csrPrefixGenProg ((mkWhpParams c U V w n_max, base), u_val))).1.1.1.1.2.2 =
             numBucketsWhp n_max :=
         congrArg crM hcrt
       have hN :
           ((Memory.spec 0).clientResult s
             (csrPrefixGenProg ((mkWhpParams c U V w n_max, base), u_val))).1.1.1.1.2.1 = n_max :=
         congrArg crNMax hcrt
       dsimp only [crBase, crM, crNMax]
       refine ⟨⟨c, U, V, w, n_max, ?_, ?_⟩, ?_⟩
       · rw [hB]; exact henv
       · dsimp only [crBase]; exact hcrt.trans (by rw [hB])
       · rw [hM, hN]; exact hok)
  )

theorem csrStepOpGenProg_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {csr : CsrState} {dict : Dictionary.State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hv : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (op : Dynamic.Op U) (hvalid : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := csrStepOpGenProg (((mkWhpParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := csrStepOp c U n_max θ.1 csr op
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    CsrMemRep base c U V w n_max pureOut.1 s'.mem ∧
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    ValidWhpProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hnU := henv.2.2.2.2.1
  have hseg := csr_seg_disjoint c U V w n_max
  have hsegb := csr_seg_base_bounds base c U V w n_max
  have hpa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hpa_le_fb : offPermAct c U V w n_max ≤ offFbStart c U V w n_max := hseg.2.2.2.2.2.2
  set M := numBucketsWhp n_max
  set h1 := bktHash c U n_max θ.1
  set crt := mkCsrRt c U V w n_max base
  have hmono := fbStart_le_of_adj_aux hv.2.1
  have hN_le : csr.fbStart M ≤ n_max := hv.2.2.1
  have hcrM : crM (mkCsrRt c U V w n_max base) = M := rfl
  have hcrN : crNMax (mkCsrRt c U V w n_max base) = n_max := rfl
  dsimp only
  cases op with
  | query u =>
    obtain ⟨hpre_st, hpre_res, hpre_vp⟩ :=
      csrPrefixGenProg_spec (u_val := u.val) henv hseed hrep hv
    set b := feistelBucket (bWhp n_max) h1 u.val
    set q_val := keyQuotient (bWhp n_max) u.val
    have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
    have hlo_hi : csr.fbStart b ≤ csr.fbStart (b + 1) := hv.2.1 b hb_lt
    have hhi_N : csr.fbStart (b + 1) ≤ csr.fbStart M := hmono (b + 1) M (by omega) le_rfl
    set f1 := csrScanRange csr.qArr (csr.fbStart b) q_val (csr.fbStart (b + 1) - csr.fbStart b)
    dsimp only [encodeOpWhp, csrStepOp]
    by_cases hf0 : f1 = 0
    · have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 0), (u.val, 0))) = s := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0, clientState_pure_prog]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]; exact hseed
      · rw [hst_eq]; exact hrep
      · rw [hst_eq]
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0, clientResult_pure_prog]
        change (0, 0) = encodeOptRes (if f1 = 0 then none else some (csr.vArr (f1 - 1)))
        simp [hf0, encodeOptRes]
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0]
        exact validWhpProg_pure _
      · intro a _; rw [hst_eq]
    · obtain ⟨_, hlt_hi⟩ := csrScanRange_lt_of_ne_zero _ hf0
      have hidx_lt : f1 - 1 < n_max := by omega
      have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 0), (u.val, 0))) = s := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0, clientState_bind_prog, clientState_readPackedGen,
          clientState_pure_prog]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]; exact hseed
      · rw [hst_eq]; exact hrep
      · rw [hst_eq]
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0, clientResult_bind_prog, clientState_readPackedGen,
          clientResult_pure_prog]
        change (1, readPacked (base + offValWhp c U w n_max) (valBits V) w s.mem (f1 - 1)) =
          encodeOptRes (if f1 = 0 then none else some (csr.vArr (f1 - 1)))
        rw [(hrep.2.2 (f1 - 1) hidx_lt).2, ite_eq_right hf0]
        rfl
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, hf0]
        refine validWhpProg_bind (validWhpProg_readPacked hw hidx_lt hsegb.2.1) ?_
        exact validWhpProg_pure _
      · intro a _; rw [hst_eq]
  | insert u v =>
    have hv_lt : v < V := hvalid.2
    obtain ⟨hpre_st, hpre_res, hpre_vp⟩ :=
      csrPrefixGenProg_spec (u_val := u.val) henv hseed hrep hv
    set b := feistelBucket (bWhp n_max) h1 u.val
    set q_val := keyQuotient (bWhp n_max) u.val
    have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
    have hlo_hi : csr.fbStart b ≤ csr.fbStart (b + 1) := hv.2.1 b hb_lt
    set hi := csr.fbStart (b + 1)
    set N := csr.fbStart M
    have hhi_N : hi ≤ N := hmono (b + 1) M (by omega) le_rfl
    set f1 := csrScanRange csr.qArr (csr.fbStart b) q_val (hi - csr.fbStart b)
    have h10 : ¬(1 = 0) := Nat.one_ne_zero
    dsimp only [encodeOpWhp, csrStepOp]
    by_cases hf0 : f1 = 0
    · have hdict_none : dict u = none := by
        rw [← csrQuery_spec hv u]
        change (if f1 = 0 then none else some (csr.vArr (f1 - 1))) = none
        exact ite_eq_left hf0
      have hN_lt : N < n_max := by
        rcases hvalid.1 with hlt_card | hsome
        · rwa [hv.bucket_and_dom_card.2] at hlt_card
        · rw [hdict_none] at hsome; cases hsome
      have hhi_lt : hi < n_max := hhi_N.trans_lt hN_lt
      have hsu := csrShiftUpLoop_spec henv hN_lt (N - hi) 0 csr.qArr csr.vArr s
        (by omega) hrep.2.2
      rw [Nat.zero_add] at hsu
      set s_su := (Memory.spec 0).clientState s (csrShiftUpLoopProg (((crt, N), 0), N - hi))
      set s_wq : Memory.State :=
        { mem := writePacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s_su.mem
            hi q_val
          frontier := s_su.frontier }
      set s_wv : Memory.State :=
        { mem := writePacked (base + offValWhp c U w n_max) (valBits V) w s_wq.mem hi v
          frontier := s_wq.frontier }
      have hfb_wv : ∀ x ≤ M,
          readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s_wv.mem x =
            csr.fbStart x := by
        intro x hx
        have hx_lt : x < M + 1 := by omega
        dsimp only [s_wv, s_wq]
        rw [readPacked_writePacked_disjoint hw hx_lt hhi_lt (by omega),
          readPacked_writePacked_disjoint hw hx_lt hhi_lt (by omega),
          readPacked_congr_on hw hx_lt
            (fun a ha1 ha2 => hsu.2.2.2.2 a (Or.inr (by omega))),
          hrep.2.1 x hx]
      have hbnd_ins : ∀ x ≤ M,
          (false = true → csr.fbStart x ≤ n_max) ∧ (false = false → csr.fbStart x < n_max) :=
        fun x hx => ⟨fun h => Bool.noConfusion h, fun _ => (hmono x M hx le_rfl).trans_lt hN_lt⟩
      have hadj := csrAdjustLoop_spec (b := b) (dec := false) henv (M - b) 0 csr.fbStart s_wv
        (by omega) hbnd_ins hfb_wv
      simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at hadj
      set s_fin := (Memory.spec 0).clientState s_wv (csrAdjustLoopProg (((crt, (b, 0)), 0), M - b))
      have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 1), (u.val, v))) = s_fin := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0]
        rw [hcrN, hcrM]
        simp only [hN_lt, ↓reduceIte, clientState_bind_prog, clientState_writePackedGen,
          clientState_pure_prog]
        rfl
      have hmem_before_quot : ∀ a, a < base + offQuotWhp c w n_max → s_fin.mem a = s.mem a := by
        intro a ha
        rw [hadj.2.2.2.2 a (Or.inl (by omega))]
        dsimp only [s_wv, s_wq]
        rw [mem_writePacked_of_outside hw hhi_lt (Or.inl (by omega)),
          mem_writePacked_of_outside hw hhi_lt (Or.inl ha),
          hsu.2.2.2.2 a (Or.inl ha)]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]
        exact SeedWhpMemRep.congr_hash hw
          (fun a _ ha2 => (hmem_before_quot a ha2).symm) hseed
      · rw [hst_eq]
        have hcsr_eq : csrInsert M csr b q_val v =
            ⟨csrAdjustStarts b false (M - b) csr.fbStart,
             Function.update (csrShiftUp N (N - hi) (csr.qArr, csr.vArr)).1 hi q_val,
             Function.update (csrShiftUp N (N - hi) (csr.qArr, csr.vArr)).2 hi v⟩ := by
          unfold csrInsert; simp [hi, N, f1, hf0]
        rw [hcsr_eq]
        refine ⟨?_, hadj.2.2.2.1, fun i hi_n => ⟨?_, ?_⟩⟩
        · rw [hmem_before_quot (base + hdrMode) (by dsimp only [hdrMode]; omega)]
          exact hrep.1
        · rw [readPacked_congr_on hw hi_n
            (fun a ha1 ha2 => hadj.2.2.2.2 a (Or.inl (by omega)))]
          dsimp only [s_wv, s_wq]
          rw [readPacked_writePacked_disjoint hw hi_n hhi_lt (by omega)]
          by_cases heq : i = hi
          · subst heq
            rw [readPacked_writePacked_self _ _ _ _ _ (quot_lt_two_pow_quotBits hnU u.isLt),
              Function.update_self]
          · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
              (hsu.2.2.2.1 i hi_n).1]
        · rw [readPacked_congr_on hw hi_n
            (fun a ha1 ha2 => hadj.2.2.2.2 a (Or.inl (by omega)))]
          dsimp only [s_wv]
          by_cases heq : i = hi
          · subst heq
            rw [readPacked_writePacked_self _ _ _ _ _ (val_lt_two_pow_valBits hv_lt),
              Function.update_self]
          · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq]
            dsimp only [s_wq]
            rw [readPacked_writePacked_disjoint hw hi_n hhi_lt (by omega),
              (hsu.2.2.2.1 i hi_n).2]
      · rw [hst_eq, hadj.2.1]
        exact hsu.2.1
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0]
        rw [hcrN, hcrM]
        simp only [hN_lt, ↓reduceIte, clientResult_bind_prog, clientResult_pure_prog,
          encodeOptRes]
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0]
        rw [hcrN, hcrM]
        simp only [hN_lt, ↓reduceIte]
        have hqk_w : quotBitsWhp U n_max ≤ w :=
          (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
        refine validWhpProg_bind hsu.2.2.1 ?_
        refine validWhpProg_bind (validWhpProg_writePacked hw hqk_w hhi_lt hsegb.1) ?_
        refine validWhpProg_bind
          (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hhi_lt hsegb.2.1) ?_
        refine validWhpProg_bind hadj.2.2.1 ?_
        exact validWhpProg_pure _
      · intro a ha
        rw [hst_eq]
        rcases ha with ha_lo | ha_hi
        · exact hmem_before_quot a (by omega)
        · have hfb_end := hsegb.2.2
          dsimp only [M] at hfb_end
          rw [hadj.2.2.2.2 a (Or.inr (by omega))]
          dsimp only [s_wv, s_wq]
          rw [mem_writePacked_of_outside hw hhi_lt (Or.inr (by omega)),
            mem_writePacked_of_outside hw hhi_lt (Or.inr (by omega)),
            hsu.2.2.2.2 a (Or.inr (by omega))]
    · obtain ⟨_, hlt_hi⟩ := csrScanRange_lt_of_ne_zero _ hf0
      have hidx_lt : f1 - 1 < n_max := by omega
      set idx := f1 - 1
      set m1 := writePacked (base + offValWhp c U w n_max) (valBits V) w s.mem idx v
      have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 1), (u.val, v))) =
          { mem := m1, frontier := s.frontier } := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0, clientState_bind_prog,
          clientState_writePackedGen, clientState_pure_prog]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]
        exact SeedWhpMemRep.congr_hash hw
          (fun a _ ha2 => (mem_writePacked_of_outside hw hidx_lt (Or.inl (by omega))).symm) hseed
      · rw [hst_eq]
        have hcsr_eq : csrInsert M csr b q_val v =
            { csr with vArr := Function.update csr.vArr idx v } := by
          unfold csrInsert; simp [hi, f1, hf0, idx]
        rw [hcsr_eq]
        refine ⟨?_, fun x hx => ?_, fun i hi_n => ⟨?_, ?_⟩⟩
        · dsimp only [m1]
          rw [mem_writePacked_of_outside hw hidx_lt (Or.inl (by dsimp only [hdrMode]; omega))]
          exact hrep.1
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw (by omega : x < M + 1) hidx_lt (by omega),
            hrep.2.1 x hx]
        · dsimp only [m1]
          rw [readPacked_writePacked_disjoint hw hi_n hidx_lt (by omega), (hrep.2.2 i hi_n).1]
        · dsimp only [m1]
          by_cases heq : i = idx
          · subst heq
            rw [readPacked_writePacked_self _ _ _ _ _ (val_lt_two_pow_valBits hv_lt),
              Function.update_self]
          · rw [readPacked_writePacked_of_ne hw _ heq, Function.update_of_ne heq,
              (hrep.2.2 i hi_n).2]
      · rw [hst_eq]
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0, clientResult_bind_prog, clientResult_pure_prog,
          encodeOptRes]
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h10, hf0]
        refine validWhpProg_bind
          (validWhpProg_writePacked hw (valBits_le_w henv.2.2.2.2.2.2.1) hidx_lt hsegb.2.1) ?_
        exact validWhpProg_pure _
      · intro a ha
        rw [hst_eq]; dsimp only [m1]
        exact mem_writePacked_of_outside hw hidx_lt (by omega)
  | delete u =>
    obtain ⟨hpre_st, hpre_res, hpre_vp⟩ :=
      csrPrefixGenProg_spec (u_val := u.val) henv hseed hrep hv
    set b := feistelBucket (bWhp n_max) h1 u.val
    set q_val := keyQuotient (bWhp n_max) u.val
    have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
    have hlo_hi : csr.fbStart b ≤ csr.fbStart (b + 1) := hv.2.1 b hb_lt
    set hi := csr.fbStart (b + 1)
    set N := csr.fbStart M
    have hhi_N : hi ≤ N := hmono (b + 1) M (by omega) le_rfl
    set f1 := csrScanRange csr.qArr (csr.fbStart b) q_val (hi - csr.fbStart b)
    have h20 : ¬(2 = 0) := by decide
    have h21 : ¬(2 = 1) := by decide
    dsimp only [encodeOpWhp, csrStepOp]
    by_cases hf0 : f1 = 0
    · have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 2), (u.val, 0))) = s := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0, clientState_pure_prog]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]; exact hseed
      · rw [hst_eq]
        unfold csrDelete
        dsimp only [f1, hi, b, q_val, h1] at hf0 ⊢
        simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact hrep
      · rw [hst_eq]
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0, clientResult_pure_prog, encodeOptRes]
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0]
        exact validWhpProg_pure _
      · intro a _; rw [hst_eq]
    · obtain ⟨_, hlt_hi⟩ := csrScanRange_lt_of_ne_zero _ hf0
      set i₀ := f1 - 1
      have hi₀_lt_N : i₀ < N := by omega
      have hsd := csrShiftDownLoop_spec (i₀ := i₀) henv (N - 1 - i₀) 0 csr.qArr csr.vArr s
        (by omega) (fun _ => by omega) hrep.2.2
      rw [Nat.zero_add] at hsd
      set s_sd := (Memory.spec 0).clientState s (csrShiftDownLoopProg (((crt, i₀), 0), N - 1 - i₀))
      have hfb_sd : ∀ x ≤ M,
          readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s_sd.mem x =
            csr.fbStart x := by
        intro x hx
        have hx_lt : x < M + 1 := by omega
        rw [readPacked_congr_on hw hx_lt
          (fun a ha1 ha2 => hsd.2.2.2.2 a (Or.inr (by omega))),
          hrep.2.1 x hx]
      have hbnd_del : ∀ x ≤ M,
          (true = true → csr.fbStart x ≤ n_max) ∧ (true = false → csr.fbStart x < n_max) :=
        fun x hx => ⟨fun _ => (hmono x M hx le_rfl).trans hN_le, fun h => Bool.noConfusion h⟩
      have hadj := csrAdjustLoop_spec (b := b) (dec := true) henv (M - b) 0 csr.fbStart s_sd
        (by omega) hbnd_del hfb_sd
      simp only [Nat.zero_add, ↓reduceIte] at hadj
      set s_fin := (Memory.spec 0).clientState s_sd (csrAdjustLoopProg (((crt, (b, 1)), 0), M - b))
      have hst_eq : (Memory.spec 0).clientState s
          (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), 2), (u.val, 0))) = s_fin := by
        unfold csrStepOpGenProg csrStepBodyProg
        rw [clientState_bind_rw, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0]
        change (Memory.spec 0).clientState s (if i₀ < N then _ else _) = s_fin
        rw [hcrM]
        simp only [hi₀_lt_N, ↓reduceIte, clientState_bind_prog, clientState_pure_prog]
        rfl
      have hmem_before_quot : ∀ a, a < base + offQuotWhp c w n_max → s_fin.mem a = s.mem a := by
        intro a ha
        rw [hadj.2.2.2.2 a (Or.inl (by omega)), hsd.2.2.2.2 a (Or.inl ha)]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq]
        exact SeedWhpMemRep.congr_hash hw
          (fun a _ ha2 => (hmem_before_quot a ha2).symm) hseed
      · rw [hst_eq]
        have hcsr_eq : csrDelete (numBucketsWhp n_max) csr
            (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
            (keyQuotient (bWhp n_max) u.val) =
            ⟨csrAdjustStarts b true (M - b) csr.fbStart,
             (csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)).1,
             (csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)).2⟩ := by
          unfold csrDelete
          dsimp only [i₀, f1, hi, N, M, b, q_val, h1] at hf0 ⊢
          simp only [bne_iff_ne, ne_eq, hf0, not_false_eq_true, ↓reduceIte]
        rw [hcsr_eq]
        refine ⟨?_, hadj.2.2.2.1, fun i hi_n => ⟨?_, ?_⟩⟩
        · rw [hmem_before_quot (base + hdrMode) (by dsimp only [hdrMode]; omega)]
          exact hrep.1
        · rw [readPacked_congr_on hw hi_n
            (fun a ha1 ha2 => hadj.2.2.2.2 a (Or.inl (by omega)))]
          exact (hsd.2.2.2.1 i hi_n).1
        · rw [readPacked_congr_on hw hi_n
            (fun a ha1 ha2 => hadj.2.2.2.2 a (Or.inl (by omega)))]
          exact (hsd.2.2.2.1 i hi_n).2
      · rw [hst_eq, hadj.2.1]
        exact hsd.2.1
      · unfold csrStepOpGenProg csrStepBodyProg
        rw [clientResult_bind_prog, hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0]
        change (Memory.spec 0).clientResult s (if i₀ < N then _ else _) = _
        rw [hcrM]
        simp only [hi₀_lt_N, ↓reduceIte, clientResult_bind_prog, clientResult_pure_prog,
          encodeOptRes]
      · unfold csrStepOpGenProg csrStepBodyProg
        refine validWhpProg_bind hpre_vp ?_
        rw [hpre_st, hpre_res]
        simp only [pure_bind, ↓reduceIte, h20, h21, hf0]
        change ValidWhpProg _ _ s (if i₀ < N then _ else _)
        rw [hcrM]
        simp only [hi₀_lt_N, ↓reduceIte]
        refine validWhpProg_bind hsd.2.2.1 ?_
        refine validWhpProg_bind hadj.2.2.1 ?_
        exact validWhpProg_pure _
      · intro a ha
        rw [hst_eq]
        rcases ha with ha_lo | ha_hi
        · exact hmem_before_quot a (by omega)
        · have hfb_end := hsegb.2.2
          dsimp only [M] at hfb_end
          rw [hadj.2.2.2.2 a (Or.inr (by omega)), hsd.2.2.2.2 a (Or.inr (by omega))]

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end


