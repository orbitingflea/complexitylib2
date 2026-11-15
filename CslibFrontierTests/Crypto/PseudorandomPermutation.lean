/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.PseudorandomPermutation
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Crypto.Primitives.PRP.Finite
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.Nat.Choose.Cast

/-!
# Tests for block ciphers and pseudorandom permutations

The key-masking cipher `xorCipher` (encryption and decryption both XOR the key into the block)
satisfies every structural law of `BlockCipher`, so the bundled length, inversion and
polynomial-time hypotheses are satisfiable. Its induced permutation and its oracles are evaluated
on concrete words, including the rejection of malformed queries and the decryption channel.

Fixing the private coins of a program that flips a coin and then queries one of two points turns
it into the deterministic query selected by the fixed coin, without changing its query budget.

For the finite experiments, a one-query adversary run against a deterministic oracle returns the
oracle's reply. The switching lemma gives it no advantage between a uniform permutation and a
uniform function, so its PRF and PRP advantages coincide up to zero. Lifted to the bidirectional
interface it asks the forward direction.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PseudorandomPermutation

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The key-masking cipher on `n`-bit keys and blocks. It is a permutation for every key but is
not pseudorandom: XORing two ciphertexts cancels the key. -/
def xorCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ key block := List.zipWith Bool.xor key block
  decrypt _ key block := List.zipWith Bool.xor key block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  length_decrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  decrypt_encrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])
  encrypt_decrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])

-- The key `[true, false]` flips the first bit of a two-bit block.
example : xorCipher.permEquiv 2 [true, false] rfl ![false, true] = ![true, true] := by
  funext i
  fin_cases i <;> rfl
example : (xorCipher.permEquiv 2 [true, false] rfl).symm ![true, true] = ![false, true] := by
  funext i
  fin_cases i <;> rfl

-- Valid encryption and decryption queries, and a malformed query of the wrong length.
example : xorCipher.prpOracle 2 [true, false] [false, true] = [true, true] := by decide
example : xorCipher.prpOracle 2 [true, false] [false] = [] := by decide
example : xorCipher.strongPRPOracle 2 [true, true] (true, [false, true]) = [true, false] := by
  decide

-- The ideal oracles read the sampled permutation and reject malformed words in the same way.
example : randomPermOracle 1 (Equiv.swap ![false] ![true]) [false] = [true] := by decide
example : randomPermOracle 1 (Equiv.swap ![false] ![true]) [false, false] = [] := by decide
example : strongRandomPermOracle 1 (Equiv.swap ![false] ![true]) (true, [true]) = [false] := by
  decide

-- A valid key answers as its induced permutation.
example : xorCipher.prpOracle 2 [true, false] [false, true] =
    randomPermOracle 2 (xorCipher.permEquiv 2 [true, false] rfl) [false, true] :=
  xorCipher.prpOracle_eq_randomPermOracle (n := 2) (key := [true, false]) rfl _

/-- Flip a fair coin, then query `0` or `1` and return the reply. -/
def coinThenQuery : ProbOracleComp (fun _ : Fin 2 => Bool) Bool := do
  let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
  ProbOracleComp.query (if c = 0 then 0 else 1)

-- Fixing the coin to `1` leaves the deterministic query of the point `1`.
example (ω : ProbOracleComp.Coins coinThenQuery) (hω : ω.1 = 1) :
    ProbOracleComp.fixCoins coinThenQuery ω =
      OracleComp.query (spec := fun _ : Fin 2 => Bool) 1 := by
  obtain ⟨c, ω'⟩ := ω
  subst hω
  rfl

-- Fixing coins keeps the one-query budget.
example (ω : ProbOracleComp.Coins coinThenQuery) :
    (ProbOracleComp.fixCoins coinThenQuery ω).IsQueryBounded 1 := by
  refine ProbOracleComp.isQueryBounded_fixCoins ?_ ω
  unfold coinThenQuery
  simpa using (ProbOracleComp.IsQueryBounded.sample _).bind fun c =>
    ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin 2 => Bool) (if c = 0 then 0 else 1)

/-! ### Finite experiments -/

/-- Ask the oracle at `false` and return the reply. -/
def queryFalse : PRF.Adversary Bool Bool := ProbOracleComp.query false

private theorem isQueryBounded_queryFalse : queryFalse.IsQueryBounded 1 :=
  ProbOracleComp.IsQueryBounded.query false

-- Running against a deterministic oracle returns its reply.
example (f : Bool → Bool) : queryFalse.run (fun x => pure (f x)) = pure (f false) :=
  ProbOracleComp.run_query false _

-- One query cannot tell a uniform permutation from a uniform function.
example :
    Game.advantage (ProbComp.eval (PRP.idealExperiment queryFalse))
      (ProbComp.eval (PRF.idealExperiment queryFalse)) = 0 := by
  have h := PRP.advantage_idealExperiment_prfIdealExperiment_le isQueryBounded_queryFalse
  rw [show Nat.choose 1 2 = 0 by decide, Nat.cast_zero, zero_div] at h
  exact_mod_cast le_antisymm h (NNReal.coe_nonneg _)

-- Hence its PRF advantage against a block cipher is at most its PRP advantage.
example (E : Bool → Equiv.Perm Bool) :
    (PRF.advantage (fun key => ⇑(E key)) queryFalse : ℝ) ≤ PRP.advantage E queryFalse := by
  simpa using PRP.prfAdvantage_le_advantage_add E isQueryBounded_queryFalse

-- The two-sided finite switching bound also gives equality of advantages on one query.
example (E : Bool → Equiv.Perm Bool) :
    |(PRP.advantage E queryFalse : ℝ) - PRF.advantage (fun key => ⇑(E key)) queryFalse| = 0 := by
  have h := PRP.abs_advantage_sub_prfAdvantage_le E isQueryBounded_queryFalse
  rw [show Nat.choose 1 2 = 0 by decide, Nat.cast_zero, zero_div] at h
  exact le_antisymm h (abs_nonneg _)

-- Theorem 4.4's `Q ^ 2 / (2 * |D|)` bound follows from `PRP.abs_advantage_sub_prfAdvantage_le`.
example {Key D : Type} [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Nonempty D]
    (E : Key → Equiv.Perm D) {A : PRF.Adversary D D} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    |(PRP.advantage E A : ℝ) - PRF.advantage (fun key => ⇑(E key)) A| ≤
      (Q : ℝ) ^ 2 / (2 * Fintype.card D) := by
  refine (PRP.abs_advantage_sub_prfAdvantage_le E hQ).trans ?_
  have hc : (Q.choose 2 : ℝ) ≤ (Q : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have := Nat.cast_nonneg (α := ℝ) Q
    nlinarith
  calc (Q.choose 2 : ℝ) / Fintype.card D ≤ ((Q : ℝ) ^ 2 / 2) / Fintype.card D := by gcongr
    _ = (Q : ℝ) ^ 2 / (2 * Fintype.card D) := by ring

-- Length-preserving Corollary 4.5 follows from `BlockCipher.prp_iff_pseudorandomFunctionOver`.
example {E : BlockCipher} (hkey : E.keyLen = id) (hblock : E.blockLen = id) :
    E.PRP ↔ PseudorandomFunction (fun key query => E.encrypt key.length key query) := by
  have hiff := BlockCipher.prp_iff_pseudorandomFunctionOver hkey
    (by rw [hblock]; exact negligible_inv_two_pow)
  rw [hblock] at hiff
  exact hiff

-- The lifted adversary asks the forward direction of the bidirectional oracle.
example (π : Equiv.Perm Bool) :
    (PRP.StrongAdversary.ofForward queryFalse).run
      (fun q => pure (RandomPermutation.evalPerm π q)) = pure (π false) := by
  simp only [PRP.StrongAdversary.run_ofForward, RandomPermutation.evalPerm_forward, queryFalse,
    ProbOracleComp.run_query]

/-! ### Necessity of super-polynomial block size in Corollary 4.5 -/

section OneBitCipher

open Cslib.Probability

private noncomputable def oneBitCipher : BlockCipher where
  keyLen := id
  blockLen := fun _ => 1
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.const 1
  encrypt _ key block := List.zipWith Bool.xor (key ++ [false]) block
  decrypt _ key block := List.zipWith Bool.xor (key ++ [false]) block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ key block _ hblock := by
    simp [List.length_zipWith, hblock]
  length_decrypt _ key block _ hblock := by
    simp [List.length_zipWith, hblock]
  decrypt_encrypt _ key block _ hblock := by
    rcases block with _ | ⟨b, bs⟩
    · simp at hblock
    · have hbs : bs = [] := by simpa using hblock
      subst hbs
      rcases key with _ | ⟨k, ks⟩ <;> cases b <;> simp [List.zipWith]
  encrypt_decrypt _ key block _ hblock := by
    rcases block with _ | ⟨b, bs⟩
    · simp at hblock
    · have hbs : bs = [] := by simpa using hblock
      subst hbs
      rcases key with _ | ⟨k, ks⟩ <;> cases b <;> simp [List.zipWith]

private lemma oneBitCipher_encrypt_eq_take_one (n : ℕ) (key block : List Bool)
    (hk : 1 ≤ key.length) (hb : block.length = 1) :
    oneBitCipher.encrypt n key block = List.zipWith Bool.xor (key.take 1) block := by
  rcases key with _ | ⟨k, ks⟩
  · simp at hk
  · rcases block with _ | ⟨b, bs⟩
    · simp at hb
    · have hbs : bs = [] := by simpa using hb
      subst hbs
      simp [oneBitCipher, List.zipWith]

private def permEquivBitStringOne : BitString 1 ≃ Equiv.Perm (BitString 1) where
  toFun k :=
    { toFun := fun x i => Bool.xor (k i) (x i)
      invFun := fun x i => Bool.xor (k i) (x i)
      left_inv := fun x => by ext i; cases hk : k i <;> cases hx : x i <;> simp [hk, hx]
      right_inv := fun x => by ext i; cases hk : k i <;> cases hx : x i <;> simp [hk, hx] }
  invFun π := fun _ => Bool.xor (π (fun _ => false) 0) false
  left_inv k := by
    ext i
    rw [Fin.eq_zero i]
    cases h : k 0 <;> simp [h]
  right_inv π := by
    ext x i
    rw [Fin.eq_zero i]
    have hx : x = (fun _ => false) ∨ x = (fun _ => true) := by
      by_cases h0 : x 0
      · right; ext j; rw [Fin.eq_zero j]; exact h0
      · left; ext j; rw [Fin.eq_zero j]; simp [h0]
    have hinj : π (fun _ => false) ≠ π (fun _ => true) :=
      π.injective.ne (fun h => Bool.false_ne_true (congr_fun h 0))
    have hneq : π (fun _ => false) 0 ≠ π (fun _ => true) 0 := by
      intro heq
      apply hinj
      ext j
      rw [Fin.eq_zero j]
      exact heq
    rcases hx with rfl | rfl
    · simp
    · cases h0 : π (fun _ => false) 0 <;> cases h1 : π (fun _ => true) 0 <;> simp_all

private theorem oneBitCipher_prp : oneBitCipher.PRP := by
  intro adversary _
  have heq : ∀ n, ProbComp.eval (oneBitCipher.prpRealGame adversary (n + 1)) =
      ProbComp.eval (prpIdealGame (fun _ => 1) adversary (n + 1)) := by
    intro n
    simp only [BlockCipher.prpRealGame, prpIdealGame, ProbComp.eval_bind,
      BitString.eval_sampleList, ProbComp.eval_uniform]
    have htake : (BitString.uniformList (oneBitCipher.keyLen (n + 1))).bind
        (fun key => (ProbOracleComp.run (adversary (n + 1) [])
          (fun request => pure (oneBitCipher.prpOracle (n + 1) key request.2))).eval) =
        (BitString.uniformList 1).bind
          (fun key₁ => (ProbOracleComp.run (adversary (n + 1) [])
            (fun request => pure (if request.2.length = 1 then
              List.zipWith Bool.xor key₁ request.2 else []))).eval) := by
      change (BitString.uniformList (n + 1)).bind _ = _
      rw [← BitString.uniformList_take (k := 1) (n := n + 1) (by omega), PMF.bind_map]
      refine Probability.PMF.bind_congr_on_support (BitString.uniformList (n + 1)) _ _
        fun key hk => ?_
      have hlen : key.length = n + 1 := BitString.length_of_mem_support_uniformList hk
      congr 2
      funext request
      change pure (if request.2.length = 1 then
        oneBitCipher.encrypt (n + 1) key request.2 else []) = _
      split_ifs with hreq
      · exact congrArg pure (oneBitCipher_encrypt_eq_take_one (n + 1) key request.2 (by omega) hreq)
      · rfl
    rw [htake]
    have hbit : BitString.uniformList 1 =
        (PMF.uniformOfFintype (BitString 1)).map List.ofFn := rfl
    rw [hbit, PMF.bind_map, ← Probability.PMF.uniformOfFintype_map_equiv permEquivBitStringOne,
      PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support (PMF.uniformOfFintype (BitString 1)) _ _
      fun k _ => ?_
    refine congrArg (fun oracle => (ProbOracleComp.run (adversary (n + 1) []) oracle).eval) ?_
    funext request
    simp only [randomPermOracle, randomFunctionOracle]
    split_ifs with hreq
    · rcases request with ⟨_, q⟩
      rcases q with _ | ⟨b, bs⟩
      · simp at hreq
      · have hbs : bs = [] := by simpa using hreq
        subst hbs
        simp only [permEquivBitStringOne, Equiv.coe_fn_mk, List.ofFn_succ,
          Fin.isValue, List.ofFn_zero, List.zipWith_cons_cons,
          List.zipWith_nil_right]
        congr 2
    · rfl
  intro c
  refine (negligible_zero c).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (oneBitCipher.blockLen : ℕ → ℕ) = fun _ => 1 := rfl
  simp only [h1]
  rw [heq m]
  simp [Game.advantage]

private noncomputable def distinctOneBitQuery : OracleDistinguisher := fun _ _ => do
  let y₀ ← List.take 1 <$> ProbOracleComp.query ((), [false])
  let y₁ ← List.take 1 <$> ProbOracleComp.query ((), [true])
  return (decide (y₀ = y₁))

private theorem distinctOneBitQuery_isOraclePPT : IsOraclePPT encBool distinctOneBitQuery := by
  have hq₀ : ComputableInPolyTime (fun _ : ℕ × List Bool => [false])
      (encPair encUnary encBits) encBits := by polytime
  have hq₁ : ComputableInPolyTime (fun _ : (ℕ × List Bool) × List Bool => [true])
      (encPair (encPair encUnary encBits) encBits) encBits := by polytime
  have hlim₀ : ComputableInPolyTime (fun _ : ℕ × List Bool => (1 : ℕ))
      (encPair encUnary encBits) encUnary := by polytime
  have hlim₁ : ComputableInPolyTime (fun _ : (ℕ × List Bool) × List Bool => (1 : ℕ))
      (encPair (encPair encUnary encBits) encBits) encUnary := by polytime
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool => decide (p.1.2 = p.2))
      (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBool := by
    polytime
  unfold distinctOneBitQuery
  exact ((IsOraclePPTOn.query_take' () hq₀ hlim₀).bind_with
    ((IsOraclePPTOn.query_take' () hq₁ hlim₁).bind_with hout.isOraclePPTOn)).isOraclePPT

private def funOneBitEquiv : (BitString 1 → BitString 1) ≃ Bool × Bool where
  toFun t := (t (BitString.ofList 1 [false]) 0, t (BitString.ofList 1 [true]) 0)
  invFun p x _ := if x 0 = false then p.1 else p.2
  left_inv t := by
    ext x i
    rw [Fin.eq_zero i]
    by_cases hx : x 0 = false
    · have hxf : BitString.ofList 1 [false] = x := by
        ext j; rw [Fin.eq_zero j]; simpa [BitString.ofList] using hx.symm
      simp [hx, hxf]
    · have hxt : BitString.ofList 1 [true] = x := by
        ext j; rw [Fin.eq_zero j]
        cases h0 : x 0
        · exact False.elim (hx h0)
        · rfl
      simp [hx, hxt]
  right_inv p := by ext <;> simp [BitString.ofList]

private theorem not_pseudorandomFunctionOver_oneBitCipher :
    ¬ PseudorandomFunctionOver (fun _ => 1) (fun _ => 1)
      (fun key query => oneBitCipher.encrypt key.length key query) := by
  intro h
  have hneg := h.secure distinctOneBitQuery distinctOneBitQuery_isOraclePPT
  have hreal : ∀ n, ProbComp.eval
      (prfRealGame (fun _ => 1) (fun key query => oneBitCipher.encrypt key.length key query)
        distinctOneBitQuery (n + 1)) = PMF.pure false := by
    intro n
    simp only [prfRealGame, ProbOracleComp.run, distinctOneBitQuery, oneBitCipher, prfOracle,
      List.length_singleton, ↓reduceIte, bind_pure_comp, Functor.map_map,
      OracleComp.interpret_bind, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, map_pure, ProbComp.eval_map, BitString.eval_sampleList]
    have hconst : ∀ key ∈ (BitString.uniformList (n + 1)).support,
        decide (List.take 1 (List.zipWith Bool.xor (key ++ [false]) [false]) =
          List.take 1 (List.zipWith Bool.xor (key ++ [false]) [true])) = false := by
      intro key hk
      have hlen : key.length = n + 1 := BitString.length_of_mem_support_uniformList hk
      rcases key with _ | ⟨k, ks⟩
      · simp at hlen
      · cases k <;> simp
    rw [Probability.PMF.map_congr_on_support (BitString.uniformList (n + 1)) _ (fun _ => false)
      hconst]
    exact PMF.map_const (BitString.uniformList (n + 1)) false
  have hideal : ∀ n, ProbComp.eval
      (prfIdealGame (fun _ => 1) (fun _ => 1) distinctOneBitQuery (n + 1)) =
      PMF.uniformOfFintype Bool := by
    intro n
    simp only [prfIdealGame, ProbOracleComp.run, distinctOneBitQuery, randomFunctionOracle,
      List.length_singleton, ↓reduceIte, bind_pure_comp, Functor.map_map,
      OracleComp.interpret_bind, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, map_pure, ProbComp.eval_map, ProbComp.eval_uniform]
    rw [← Probability.PMF.uniformOfFintype_map_equiv funOneBitEquiv.symm, PMF.map_comp]
    ext b
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type]
    have hne : BitString.ofList 1 [false] 0 ≠ BitString.ofList 1 [true] 0 := by decide
    have hsum : (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = 2⁻¹ := by
      rw [show (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = 2 * (4 : ENNReal)⁻¹ from (two_mul _).symm,
        show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    cases b <;>
      simpa [funOneBitEquiv, List.ofFn_succ, hne] using hsum
  have hshift := hneg.shift 1
  simp only [hreal, hideal] at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

-- `oneBitCipher` satisfies `PRP` without being a `PseudorandomFunctionOver` on 1-bit blocks.
example :
    ¬ (oneBitCipher.PRP ↔
      PseudorandomFunctionOver oneBitCipher.blockLen oneBitCipher.blockLen
        (fun key query => oneBitCipher.encrypt key.length key query)) := by
  intro hiff
  exact not_pseudorandomFunctionOver_oneBitCipher (hiff.mp oneBitCipher_prp)

end OneBitCipher

end CslibFrontierTests.Crypto.PseudorandomPermutation
