/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.GoldwasserMicali
public import CslibFrontier.Crypto.Computational.Paillier
import CslibFrontier.Crypto.Computational.GoldwasserMicali.Malleability
import CslibFrontier.Crypto.Computational.Paillier.Malleability
import CslibFrontier.Crypto.Computational.Paillier.Security
import Mathlib.Tactic.NormNum.Prime

/-! Clients of the Goldwasser–Micali and Paillier CCA-insecurity API under module encapsulation:
each scheme is IND-CPA under its assumption yet not CCA secure; concrete instances on the Blum
modulus `21 = 3 * 7` and the balanced modulus `143 = 11 * 13` with advantage exactly `1`; and
concrete mauled decryptions. The API under test is imported ordinarily; only the scheme modules
are imported publicly, for the fixtures. -/

public section

namespace CslibFrontierTests.Crypto.CCAMalleability

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM

/-! ### Goldwasser–Micali -/

section GoldwasserMicali

open GoldwasserMicali

/-- The Blum modulus `21 = 3 * 7`. -/
@[expose] def d21 : ModulusDesc := ⟨3, 7, by norm_num, by norm_num, by decide, by decide, by decide⟩

/-- The constant generator of the Blum modulus `21`. -/
noncomputable def constBlumGen : ℕ → ProbComp ModulusDesc := fun _ => pure d21

theorem isBlum_constBlumGen (n : ℕ) :
    ∀ d ∈ (ProbComp.eval (constBlumGen n)).support, IsBlumModulus d.p d.q := by
  intro d hd
  simp only [constBlumGen, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hd
  have h37 : IsBlumModulus 3 7 := ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩
  exact hd ▸ h37

-- Under quadratic residuosity, Blum Goldwasser–Micali is IND-CPA, yet it is neither 1CCA nor
-- interleaved-CCA secure.
example {gen : ℕ → ProbComp ModulusDesc}
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    INDCPA (blumKeyGen gen) encrypt ∧ ¬ INDCCA2 (blumKeyGen gen) encrypt decryptOpt ∧
      ¬ INDCCA2Interleaved (blumKeyGen gen) encrypt decryptOpt :=
  ⟨indcpa_blumGoldwasserMicali hblum hsize hQR, not_indcca2_blumGoldwasserMicali hblum,
    not_indcca2Interleaved_blumGoldwasserMicali hblum⟩

-- The Blum hypothesis holds for the constant generator of `21`, where `flipAdversary` has
-- advantage exactly `1` at every parameter.
example : ¬ INDCCA2 (blumKeyGen constBlumGen) encrypt decryptOpt :=
  not_indcca2_blumGoldwasserMicali isBlum_constBlumGen

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2Game encBool (blumKeyGen constBlumGen) encrypt decryptOpt
        flipAdversary false n))
      (ProbComp.eval (cca2Game encBool (blumKeyGen constBlumGen) encrypt decryptOpt
        flipAdversary true n)) = 1 :=
  advantage_cca2Game_blum_flipAdversary (isBlum_constBlumGen n)

example : flipAdversary.IsPPT := isPPT_flipAdversary

-- Over any generator of valid key descriptions, Goldwasser–Micali is not 1CCA secure.
example (gen : ℕ → ProbComp KeyDesc) : ¬ INDCCA2 (keyGen gen) encrypt decryptOpt :=
  not_indcca2_goldwasserMicali gen

-- A concrete flip modulo `21` with public nonresidue `20 = -1`: the ciphertexts of both bits with
-- randomness `2` flip to ciphertexts of the negated bits.
example : ∀ b : Bool,
    decrypt (encPair encNat encNat (3, 7))
      (flipCiphertext (encPair encNat encNat (21, 20)) (encNat (ciphertext 21 20 b 2))) = !b := by
  decide

end GoldwasserMicali

/-! ### Paillier -/

section Paillier

open Paillier

/-- Four-bit numbers have `Nat.size` four. -/
theorem size_eq_four {m : ℕ} (h₁ : 2 ^ 3 ≤ m) (h₂ : m < 2 ^ 4) : m.size = 4 :=
  le_antisymm (Nat.size_le.mpr h₂) (Nat.lt_size.mpr h₁)

/-- The balanced modulus `143 = 11 * 13`. -/
@[expose] def d143 : BalancedModulus.Desc :=
  ⟨(11, 13), ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num,
    (size_eq_four (by norm_num) (by norm_num)).trans
      (size_eq_four (by norm_num) (by norm_num)).symm⟩⟩

/-- The constant generator of the balanced modulus `143`. -/
noncomputable def constGen : ℕ → ProbComp BalancedModulus.Desc := fun _ => pure d143

-- Under DCR, Paillier is IND-CPA, yet it is neither 1CCA nor interleaved-CCA secure, for every
-- modulus generator.
example {gen : ℕ → ProbComp BalancedModulus.Desc}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hDCR : DCR fun n => ProbComp.eval (gen n)) :
    INDCPAOn validMessages encNat (keyGen gen) encrypt ∧
      ¬ INDCCA2On validMessages encNat encBits (keyGen gen) encrypt decryptOpt ∧
      ¬ INDCCA2InterleavedOn validMessages encNat encBits (keyGen gen) encrypt decryptOpt :=
  ⟨DCR.indcpaOn_paillier hsize hDCR, not_indcca2On_paillier gen,
    not_indcca2InterleavedOn_paillier gen⟩

-- At the constant modulus `143`, `incrementAdversary` is strict oracle PPT and has advantage
-- exactly `1` at every parameter.
example : incrementAdversary.IsPPT encNat := isPPT_incrementAdversary

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2GameOn validMessages encBits (keyGen constGen) encrypt decryptOpt
        incrementAdversary false n))
      (ProbComp.eval (cca2GameOn validMessages encBits (keyGen constGen) encrypt decryptOpt
        incrementAdversary true n)) = 1 :=
  advantage_cca2GameOn_incrementAdversary constGen n

-- A concrete increment modulo `143 ^ 2`: the encryption of `5` with randomness `2` increments to
-- a ciphertext that decrypts to `6` under the secret key `⟨143, φ(143) = 120⟩`.
example :
    decrypt (encPair encNat encNat (143, 120))
      (incrementCiphertext (encNat 143) (encNat (ciphertext 143 5 2))) = encNat 6 := by
  decide

end Paillier

end CslibFrontierTests.Crypto.CCAMalleability
