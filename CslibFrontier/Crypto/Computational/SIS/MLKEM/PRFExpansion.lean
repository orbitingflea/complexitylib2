/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Family
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# K-PKE with PRF seed expansion

Kyber v3.02 expands every centered-binomial noise polynomial of K-PKE from a 32-byte seed with a
pseudorandom function `PRF : B^32 × B → B^*` ([AvanziEtAl2021], p. 5), reading `64η` bytes with
`CBD_η` (Algorithm 2, p. 7). Key generation computes `s[i], e[i] := CBD_η₁(PRF(σ, N))` for the
counters `N = 0, …, 2k − 1`, where `σ` is half of `G(d)` (Algorithm 4, p. 8). Encryption with
coins `r ∈ B^32` computes `r[i] := CBD_η₁(PRF(r, N))`, `e₁[i] := CBD_η₂(PRF(r, N))` and
`e₂ := CBD_η₂(PRF(r, N))` for `N = 0, …, 2k` (Algorithm 5, p. 9).

`kpkePRF P F` is the word-level K-PKE family `kpke P` of
`CslibFrontier.Crypto.Computational.SIS.MLKEM.Family` with this expansion by a keyed function `F`
on words, in place of fair coins. At security parameter `κ`:

* the encryption coins are a `κ`-bit seed `r`, expanded to `encNoise (P κ) F r`: for each counter
  `N ≤ 2k`, the first `n · 2η` bits of `F r (nonceWord N)`, with `η = η₁` for `N < k` and
  `η = η₂` otherwise (`encWidth`). These are exactly the bits from which `encDetWord` decodes the
  `N`-th noise polynomial by `SamplePolyCBD_η`, so it decodes `CBD_η(F(r, N))` (`cbd_encNoise`);
* key generation draws the matrix as `keyGenWord` does, and a uniform `κ`-bit seed `σ`, and decodes
  `s` and `e` from `keyNoise (P κ) F σ`, the first `n · 2η₁` bits of `F σ (nonceWord N)` for
  `N < 2k`, so it decodes `CBD_η₁(F(σ, N))` (`cbd_keyNoise`);
* decryption is `decWord`.

The counter `N` is written in binary in `nonceLen = (2k).size` bits, so the `2k + 1` counters have
distinct words for every rank `k` (`nonceWord_injOn`). The PRF's outputs are meant to have
`prfLen = n · 2 · max(η₁, η₂)` bits, of which each counter reads a prefix.

The family is efficient whenever its parameters are computable in polynomial time and `F` is
evaluated in polynomial time (`kpkePRF_isEfficient`), and its ciphertexts fit the ciphertext space
(`kpkePRF_ciphertextFits`). This module makes no security claim.

## Model differences from Kyber v3.02 and FIPS 203

* The public key carries an approximately uniform matrix, drawn coefficientwise, in place of the
  seed `ρ` from which Kyber re-derives it with `XOF`, and the seed `σ` is sampled directly rather
  than taken from `G(d)`. Neither the scheme nor the adversary has an `XOF` or `G` oracle, so the
  random-oracle model of Kyber v3.02 Theorem 1 (§4.3.1, p. 20) is not formalized here; relating
  this full-matrix family to it is open under #5293.
* Seeds have `κ` bits rather than 32 bytes, and counters `(2k).size` bits rather than one byte,
  since an asymptotic family scales the rank `k`.
* `F` is any keyed function on words. Kyber's `PRF` has outputs of any length and FIPS 203 fixes
  it to SHAKE-256 (`prf` of `CslibFrontier.Crypto.Computational.SIS.MLKEM.SeedExpansion`), whose
  outputs of different lengths are prefixes of one another (`prf_two_eq_take_three`).
* Polynomials are in coefficient form rather than the NTT domain, and keys and ciphertexts are
  words of residue lists rather than `ByteEncode` outputs.

## Main definitions

* `Cslib.Crypto.MLKEM.nonceLen`, `Cslib.Crypto.MLKEM.nonceWord`, `Cslib.Crypto.MLKEM.prfLen`: the
  counter words and the PRF output length.
* `Cslib.Crypto.MLKEM.expandNoise`, `Cslib.Crypto.MLKEM.keyNoise`, `Cslib.Crypto.MLKEM.encWidth`,
  `Cslib.Crypto.MLKEM.encNoise`: seed expansion.
* `Cslib.Crypto.MLKEM.keyGenPRFWord`: key generation with seed expansion.
* `Cslib.Crypto.MLKEM.kpkePRF`: the word-level K-PKE family with seed expansion.

## Main results

* `Cslib.Crypto.MLKEM.nonceWord_injOn`: the counters of key generation and encryption have
  distinct words.
* `Cslib.Crypto.MLKEM.cbd_keyNoise`, `Cslib.Crypto.MLKEM.cbd_encNoise`: key generation and
  encryption decode `CBD_η(F(σ, N))` and `CBD_η(F(r, N))`.
* `Cslib.Crypto.MLKEM.kpkePRF_isEfficient`: the family is efficient for a polynomial-time
  parameter family and a polynomial-time `F`.
* `Cslib.Crypto.MLKEM.kpkePRF_ciphertextFits`: ciphertexts fit their ciphertext space.

## References

* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, p. 5, Algorithms 2, 4 and 5 (pp. 7–9) and
  §4.3.1 (p. 20)
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.FujisakiOkamoto

/-! ### Counters and seed expansion -/

/-- The number of bits of a PRF counter word: the length of the binary representation of `2k`, so
that the counters `0, …, 2k` of key generation and encryption have distinct words. -/
def nonceLen (P : Params) : ℕ := (2 * P.k).size

/-- The word of the PRF counter `N`: its `nonceLen P` low-order bits, least significant first. -/
def nonceWord (P : Params) (N : ℕ) : List Bool := BitString.lowBits (nonceLen P) N

/-- The output length of the PRF, `n · 2 · max(η₁, η₂)` bits: `SamplePolyCBD_η` reads the first
`n · 2η` of them at either width. -/
def prfLen (P : Params) : ℕ := P.n * (2 * max P.η₁ P.η₂)

/-- Seed expansion: for each counter `N < count`, the first `width N` bits of `F seed` at the word
of `N`, concatenated. -/
def expandNoise (P : Params) (F : List Bool → List Bool → List Bool) (seed : List Bool)
    (count : ℕ) (width : ℕ → ℕ) : List Bool :=
  (List.range count).flatMap fun N => (F seed (nonceWord P N)).take (width N)

/-- The noise bits of key generation from the seed `σ`: `n · 2η₁` bits from each of the counters
`0, …, 2k − 1`, those of `s` and then those of `e`. -/
def keyNoise (P : Params) (F : List Bool → List Bool → List Bool) (σ : List Bool) : List Bool :=
  expandNoise P F σ (2 * P.k) fun _ => P.n * (2 * P.η₁)

/-- The number of noise bits that encryption reads from counter `N`: `n · 2η₁` for the `k`
polynomials of `r`, and `n · 2η₂` for the `k` polynomials of `e₁` and for `e₂`. -/
def encWidth (P : Params) (N : ℕ) : ℕ :=
  if N < P.k then P.n * (2 * P.η₁) else P.n * (2 * P.η₂)

/-- The coins of encryption from the seed `r`: the noise bits of the counters `0, …, 2k`. -/
def encNoise (P : Params) (F : List Bool → List Bool → List Bool) (r : List Bool) : List Bool :=
  expandNoise P F r (2 * P.k + 1) (encWidth P)

@[simp] theorem length_nonceWord (P : Params) (N : ℕ) : (nonceWord P N).length = nonceLen P :=
  BitString.length_lowBits _ _

/-- **The counters have distinct words.** The words of the counters `0, …, 2k` are distinct. -/
theorem nonceWord_injOn (P : Params) : Set.InjOn (nonceWord P) (Set.Iic (2 * P.k)) := by
  intro N hN M hM h
  have hlt (x : ℕ) (hx : x ≤ 2 * P.k) : x < 2 ^ nonceLen P :=
    lt_of_le_of_lt hx (Nat.lt_size_self _)
  exact BitString.lowBits_injective_of_lt (hlt N hN) (hlt M hM) h

/-! ### The noise that encryption decodes -/

/-- `SamplePolyCBD_η` reads only the first `n · 2η` bits of its input. -/
private theorem cbdResidues_take (n q η : ℕ) (bits : List Bool) :
    cbdResidues n q η (bits.take (n * (2 * η))) = cbdResidues n q η bits := by
  rw [cbdResidues, cbdResidues, BitString.listRows_eq_ofFn, BitString.listRows_eq_ofFn,
    BitString.ofList_take]

/-- Prefixes of one width `w` of the words `blocks`, concatenated, have `blocks.length * w` bits
when every word has at least `w` bits. -/
private theorem length_flatten_map_take {w : ℕ} (blocks : List (List Bool))
    (hblocks : ∀ block ∈ blocks, w ≤ block.length) :
    (blocks.map (List.take w)).flatten.length = blocks.length * w := by
  rw [List.length_flatten, List.map_map,
    List.map_congr_left (g := fun _ => w) fun b hb => by simp [hblocks b hb]]
  simp

/-- `SamplePolyCBD_η` of each of `k` prefixes of `n · 2η` bits, from their concatenation. -/
private theorem cbdVecResidues_flatten_map_take {k n q η : ℕ} (blocks : List (List Bool))
    (hk : blocks.length = k) (hblocks : ∀ block ∈ blocks, n * (2 * η) ≤ block.length) :
    cbdVecResidues k n q η (blocks.map (List.take (n * (2 * η)))).flatten =
      blocks.map (cbdResidues n q η) := by
  unfold cbdVecResidues
  subst hk
  rw [show blocks.length = (blocks.map (List.take (n * (2 * η)))).length by simp,
    BitString.listRows_flatten _ fun block hblock => ?_]
  · simp only [List.map_map, Function.comp_def, cbdResidues_take]
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hblock
    simpa using hblocks b hb

/-- **Key generation decodes `CBD_η₁(F(σ, N))`.** If `F σ` has at least `prfLen P` bits at the
word of each counter `N < 2k`, the polynomials that key generation decodes from `keyNoise P F σ`
are `SamplePolyCBD` of `F σ` at the counters, as in Kyber v3.02 Algorithm 4 (p. 8): `s` from the
counters `0, …, k − 1` and `e` from `k, …, 2k − 1`, at width `η₁`. -/
theorem cbd_keyNoise (P : Params) (F : List Bool → List Bool → List Bool) (σ : List Bool)
    (hF : ∀ N < 2 * P.k, prfLen P ≤ (F σ (nonceWord P N)).length) :
    cbdVecResidues P.k P.n P.q P.η₁ ((keyNoise P F σ).take (P.k * (P.n * (2 * P.η₁)))) =
        (List.range P.k).map (fun N => cbdResidues P.n P.q P.η₁ (F σ (nonceWord P N))) ∧
      cbdVecResidues P.k P.n P.q P.η₁ ((keyNoise P F σ).drop (P.k * (P.n * (2 * P.η₁)))) =
        (List.range P.k).map (fun i => cbdResidues P.n P.q P.η₁ (F σ (nonceWord P (P.k + i)))) := by
  set w := P.n * (2 * P.η₁)
  set S := (List.range P.k).map fun N => F σ (nonceWord P N)
  set E := (List.range P.k).map fun i => F σ (nonceWord P (P.k + i))
  have hw : w ≤ prfLen P := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_left _ _))
  have hS : ∀ block ∈ S, w ≤ block.length := by
    intro block hblock
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hblock
    exact hw.trans (hF N (by have := List.mem_range.mp hN; omega))
  have hE : ∀ block ∈ E, w ≤ block.length := by
    intro block hblock
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hblock
    exact hw.trans (hF _ (by have := List.mem_range.mp hi; omega))
  have hsplit :
      keyNoise P F σ = (S.map (List.take w)).flatten ++ (E.map (List.take w)).flatten := by
    unfold keyNoise expandNoise
    rw [show 2 * P.k = P.k + P.k by omega, List.range_add, List.flatMap_append, List.flatMap_def,
      List.flatMap_def]
    simp only [S, E, List.map_map, Function.comp_def, w]
  have hlen : (S.map (List.take w)).flatten.length = P.k * w := by
    rw [length_flatten_map_take _ hS]
    simp [S]
  refine ⟨?_, ?_⟩
  · rw [hsplit, List.take_left' hlen, cbdVecResidues_flatten_map_take _ (by simp [S]) hS]
    simp [S]
  · rw [hsplit, List.drop_left' hlen, cbdVecResidues_flatten_map_take _ (by simp [E]) hE]
    simp [E]

/-- **Encryption decodes `CBD_η(F(r, N))`.** If `F r` has at least `prfLen P` bits at the word of
each counter `N ≤ 2k`, the polynomials that `encDetWord` decodes from the coins `encNoise P F r`
are `SamplePolyCBD` of `F r` at the counters, as in Kyber v3.02 Algorithm 5 (p. 9): `r` from the
counters `0, …, k − 1` at width `η₁`, `e₁` from `k, …, 2k − 1` and `e₂` from `2k` at width `η₂`. -/
theorem cbd_encNoise (P : Params) (F : List Bool → List Bool → List Bool) (r : List Bool)
    (hF : ∀ N ≤ 2 * P.k, prfLen P ≤ (F r (nonceWord P N)).length) :
    cbdVecResidues P.k P.n P.q P.η₁ ((encNoise P F r).take (P.k * (P.n * (2 * P.η₁)))) =
        (List.range P.k).map (fun N => cbdResidues P.n P.q P.η₁ (F r (nonceWord P N))) ∧
      cbdVecResidues P.k P.n P.q P.η₂ (((encNoise P F r).drop (P.k * (P.n * (2 * P.η₁)))).take
          (P.k * (P.n * (2 * P.η₂)))) =
        (List.range P.k).map (fun i => cbdResidues P.n P.q P.η₂ (F r (nonceWord P (P.k + i)))) ∧
      cbdResidues P.n P.q P.η₂ ((encNoise P F r).drop
          (P.k * (P.n * (2 * P.η₁)) + P.k * (P.n * (2 * P.η₂)))) =
        cbdResidues P.n P.q P.η₂ (F r (nonceWord P (2 * P.k))) := by
  set w₁ := P.n * (2 * P.η₁)
  set w₂ := P.n * (2 * P.η₂)
  set B₁ := (List.range P.k).map fun N => F r (nonceWord P N)
  set B₂ := (List.range P.k).map fun i => F r (nonceWord P (P.k + i))
  have h₁ : ∀ block ∈ B₁, w₁ ≤ block.length := by
    intro block hblock
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hblock
    exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_left _ _))).trans
      (hF N (by have := List.mem_range.mp hN; omega))
  have h₂ : ∀ block ∈ B₂, w₂ ≤ block.length := by
    intro block hblock
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hblock
    exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_max_right _ _))).trans
      (hF _ (by have := List.mem_range.mp hi; omega))
  have hsplit : encNoise P F r = (B₁.map (List.take w₁)).flatten ++
      ((B₂.map (List.take w₂)).flatten ++ (F r (nonceWord P (2 * P.k))).take w₂) := by
    unfold encNoise expandNoise
    rw [show 2 * P.k + 1 = P.k + P.k + 1 by omega, List.range_succ, List.range_add,
      List.flatMap_append, List.flatMap_append, List.append_assoc, List.flatMap_singleton]
    refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_)
    · rw [List.flatMap_def]
      simp only [B₁, List.map_map]
      exact congrArg _ (List.map_congr_left fun N hN => by
        simp [encWidth, List.mem_range.mp hN, w₁])
    · rw [List.flatMap_def]
      simp only [B₂, List.map_map]
      exact congrArg _ (List.map_congr_left fun i _ => by simp [encWidth, w₂])
    · simp [encWidth, w₂, two_mul]
  have hlen₁ : (B₁.map (List.take w₁)).flatten.length = P.k * w₁ := by
    rw [length_flatten_map_take _ h₁]
    simp [B₁]
  have hlen₂ : (B₂.map (List.take w₂)).flatten.length = P.k * w₂ := by
    rw [length_flatten_map_take _ h₂]
    simp [B₂]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, List.take_left' hlen₁, cbdVecResidues_flatten_map_take _ (by simp [B₁]) h₁]
    simp [B₁]
  · rw [hsplit, List.drop_left' hlen₁, List.take_left' hlen₂,
      cbdVecResidues_flatten_map_take _ (by simp [B₂]) h₂]
    simp [B₂]
  · rw [hsplit, ← List.drop_drop, List.drop_left' hlen₁, List.drop_left' hlen₂, cbdResidues_take]

/-! ### Key generation and the family -/

/-- K-PKE key generation on words with PRF seed expansion: draw the matrix as `keyGenWord` does at
precision `κ` and a uniform `κ`-bit seed `σ`, and decode `s` and `e` from `keyNoise P F σ`. -/
noncomputable def keyGenPRFWord (P : Params) (F : List Bool → List Bool → List Bool) (κ : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let A ← sampleMatrixResidues P κ
  let σ ← BitString.sampleList κ
  return keyWords P A ((keyNoise P F σ).take (P.k * (P.n * (2 * P.η₁))))
    ((keyNoise P F σ).drop (P.k * (P.n * (2 * P.η₁))))

/-- **The full-matrix K-PKE family with PRF seed expansion, as a word-level public-key encryption
family.** At security parameter `κ`, the scheme uses the parameters `P κ` and the keyed function
`F`: key generation is `keyGenPRFWord`, whose public key carries the sampled matrix in place of the
seed `ρ`, encryption coins are `κ`-bit seeds expanded by `encNoise`, and messages, ciphertexts and
decryption are those of `kpke P`. No algorithm calls `XOF` or `G`. -/
noncomputable def kpkePRF (P : ℕ → Params) (F : List Bool → List Bool → List Bool) : WordPKE where
  msgLen κ := (P κ).n
  coinLen κ := κ
  ctLen κ := ctLength (P κ)
  keyGen κ := keyGenPRFWord (P κ) F κ
  encDet κ pk m r := encDetWord (P κ) pk m (encNoise (P κ) F r)
  dec κ := decWord (P κ)

/-- **K-PKE ciphertexts with seed expansion fit their ciphertext space.** -/
theorem kpkePRF_ciphertextFits (P : ℕ → Params) (F : List Bool → List Bool → List Bool) :
    (kpkePRF P F).CiphertextFits :=
  fun κ pk _ _ m r _ _ => length_encDetWord_le (P κ) pk m (encNoise (P κ) F r)

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The word of a computed counter, with computed parameters. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.nonceWord {P : α → Params} {N : α → ℕ}
    (hP : ComputableInPolyTime P input encParams) (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun a => nonceWord (P a) (N a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.nonceWord Cslib.Crypto.MLKEM.nonceLen
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have hsize : ComputableInPolyTime (fun a => (2 * (P a).k).size) input encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hk)))
  exact ComputableInPolyTime.bitsLow hsize (ComputableInPolyTime.unary_to_binary.comp hN)

/-- Seed expansion with computed parameters, seed, count and widths, for a keyed function
evaluated in polynomial time. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.expandNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {seed : α → List Bool} {count : α → ℕ}
    {width : α → ℕ → ℕ} (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hseed : ComputableInPolyTime seed input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime (fun p : α × ℕ => width p.1 p.2) (encPair input encUnary)
      encUnary) :
    ComputableInPolyTime (fun a => expandNoise (P a) F (seed a) (count a) (width a)) input
      encBits := by
  unfold Cslib.Crypto.MLKEM.expandNoise
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hvalue := hF.comp ((hseed.comp hfst).prod
    (ComputableInPolyTime.nonceWord (hP.comp hfst) hsnd))
  exact ComputableInPolyTime.flatMapToBitsWithInput (enc := encUnary)
    (ComputableInPolyTime.range.comp hcount)
    (ComputableInPolyTime.bitsTakeWithInput hvalue hwidth)

/-- The noise widths of encryption, with computed parameters and counter. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encWidth {P : α → Params} {N : α → ℕ}
    (hP : ComputableInPolyTime P input encParams) (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun a => encWidth (P a) (N a)) input encUnary := by
  unfold Cslib.Crypto.MLKEM.encWidth
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have h₁ : ComputableInPolyTime (fun a => (P a).n * (2 * (P a).η₁)) input encUnary := by fun_prop
  have h₂ : ComputableInPolyTime (fun a => (P a).n * (2 * (P a).η₂)) input encUnary := by fun_prop
  simpa only [decide_eq_true_eq] using ComputableInPolyTime.ite' (hN.unary_lt' hk) h₁ h₂

/-- Key-generation noise with computed parameters and seed. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.keyNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {σ : α → List Bool}
    (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hσ : ComputableInPolyTime σ input encBits) :
    ComputableInPolyTime (fun a => keyNoise (P a) F (σ a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.keyNoise
  exact ComputableInPolyTime.expandNoise hP hF hσ (by fun_prop) (by fun_prop)

/-- Encryption coins with computed parameters and seed. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {r : α → List Bool}
    (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => encNoise (P a) F (r a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.encNoise
  exact ComputableInPolyTime.expandNoise hP hF hr (by fun_prop)
    (ComputableInPolyTime.encWidth (hP.comp (ComputableInPolyTime.fst input encUnary))
      (ComputableInPolyTime.snd input encUnary))

end PolyTime

/-- **K-PKE with seed expansion is an efficient word-level family** whenever its parameters are
computable in polynomial time from the unary security parameter and `F` is evaluated in
polynomial time. -/
theorem kpkePRF_isEfficient {P : ℕ → Params} {F : List Bool → List Bool → List Bool}
    (hP : ComputableInPolyTime P encUnary encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    (kpkePRF P F).IsEfficient where
  msgLen := (kpke_isEfficient hP).msgLen
  coinLen := ComputableInPolyTime.id'
  ctLen := (kpke_isEfficient hP).ctLen
  keyGen := by
    change IsPPTOn encUnary (encPair encBits encBits) fun κ => keyGenPRFWord (P κ) F κ
    unfold keyGenPRFWord
    have hA := isPPTOn_sampleMatrixResidues.preprocess (hP.prod ComputableInPolyTime.id')
    refine hA.bind_with ((isPPTOn_sampleList.preprocess
      (ComputableInPolyTime.fst encUnary encMatrixResidues)).bind_with ?_)
    let E := encPair (encPair encUnary encMatrixResidues) encBits
    have hP' : ComputableInPolyTime (fun y : (ℕ × List (List (List ℕ))) × List Bool => P y.1.1) E
        encParams := hP.comp (by fun_prop)
    have hnoise := ComputableInPolyTime.keyNoise hP' hF
      (by fun_prop : ComputableInPolyTime
        (fun y : (ℕ × List (List (List ℕ))) × List Bool => y.2) E encBits)
    have hL : ComputableInPolyTime
        (fun y : (ℕ × List (List (List ℕ))) × List Bool =>
          (P y.1.1).k * ((P y.1.1).n * (2 * (P y.1.1).η₁))) E encUnary := by fun_prop
    exact (ComputableInPolyTime.keyWords hP' (by fun_prop)
      (ComputableInPolyTime.bitsTakeWithInput hnoise hL)
      (ComputableInPolyTime.bitsDropWithInput hnoise hL)).isPPTOn
  encDet := by
    change ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool =>
      encDetWord (P x.1) x.2.1 x.2.2.1 (encNoise (P x.1) F x.2.2.2)) encEncDetInput encBits
    have hPx : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool => P x.1)
        encEncDetInput encParams := hP.comp (by fun_prop)
    exact ComputableInPolyTime.encDetWord hPx (by fun_prop) (by fun_prop)
      (ComputableInPolyTime.encNoise hPx hF (by fun_prop))
  dec := (kpke_isEfficient hP).dec

end Cslib.Crypto.MLKEM
