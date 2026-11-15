/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE
public import CslibFrontier.Computability.PolyTime.Int.Negacyclic
public import CslibFrontier.Computability.PolyTime.ZMod.ModulusSwitch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Crypto.Computational.SIS.Native
import CslibFrontier.Probability.PMF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Native K-PKE on residue lists

K-PKE ([NIST, Section 5, Algorithms 13–15][NISTFIPS203]) is defined in
`CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE` over typed polynomials `Fin n → ZMod q`. This
module gives its algorithms as total functions on residue lists (`polyResidues`,
`polyVecResidues`), with plain polynomial-time certificates in which the ring degree, module rank,
centered-binomial widths and compression widths are unary and the modulus is binary
(`encParams`). Each list function is proved to compute the typed operation:

* `compressResidues` and `decompressResidues` compute `compressPoly` and `decompressPoly`
  ([NIST, Section 4.2.1][NISTFIPS203]) through the integer modulus-switching implementation
  `ZMod.modulusSwitchResidue`; `messageResidues` computes `messagePoly`.
* `cbdResidues` is `SamplePolyCBD_η` ([NIST, Section 4.2.2, Algorithm 8][NISTFIPS203]) on a word
  of fair bits: decoding `n * (2 * η)` uniform bits gives exactly the law of the residues of
  `samplePolyCBD n q η` (`uniformList_map_cbdResidues`), and likewise for vectors
  (`uniformList_map_cbdVecResidues`).
* `encryptResidues`, `decryptResidues` and `publicKeyResidues` compute `encrypt`, `decrypt` and the
  public vector `A s + e` of `moduleLWEKeyGen` (`encryptResidues_eq`, `decryptResidues_eq`,
  `publicKeyResidues_eq`).

These are the natives for the certified asymptotic IND-CPA theorem for K-PKE
([#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6888265804)):
the word-level K-PKE family and the efficiency certificates of the theorem's reductions are built
from them. They make no security claim.

## Main definitions

* `Cslib.Crypto.MLKEM.compressResidues`, `Cslib.Crypto.MLKEM.decompressResidues`,
  `Cslib.Crypto.MLKEM.messageResidues`: compression, decompression and the message polynomial.
* `Cslib.Crypto.MLKEM.cbdValue`, `Cslib.Crypto.MLKEM.cbdResidues`,
  `Cslib.Crypto.MLKEM.cbdVecResidues`: centered-binomial sampling from fair bits.
* `Cslib.Crypto.MLKEM.encParams`: the encoding of K-PKE parameters.
* `Cslib.Crypto.MLKEM.matrixResidues`, `Cslib.Crypto.MLKEM.encMatrixResidues`,
  `Cslib.Crypto.MLKEM.encCiphertextResidues`: residue rows of a module matrix and the layouts of
  their words and of ciphertext words.
* `Cslib.Crypto.MLKEM.encryptResidues`, `Cslib.Crypto.MLKEM.decryptResidues`,
  `Cslib.Crypto.MLKEM.publicKeyResidues`: K-PKE encryption, decryption and public-key
  computation on residue lists.

## Main results

* `Cslib.Crypto.MLKEM.uniformList_map_cbdResidues`,
  `Cslib.Crypto.MLKEM.uniformList_map_cbdVecResidues`: the laws of centered-binomial sampling from
  fair bits.
* `Cslib.Crypto.MLKEM.encryptResidues_eq`, `Cslib.Crypto.MLKEM.decryptResidues_eq`,
  `Cslib.Crypto.MLKEM.publicKeyResidues_eq`: the list algorithms compute K-PKE.
* `Turing.MultiTapeTM.ComputableInPolyTime.encryptResidues`,
  `Turing.MultiTapeTM.ComputableInPolyTime.decryptResidues`,
  `Turing.MultiTapeTM.ComputableInPolyTime.publicKeyResidues` and the certificates of the
  operations above.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM

/-- Coefficientwise `Compress_d` on residues modulo `q`: `⌈(2^d / q) · x⌋ mod 2^d`, computed by
integer modulus switching. -/
def compressResidues (q d : ℕ) (a : List ℕ) : List ℕ :=
  a.map fun x : ℕ => ZMod.modulusSwitchResidue q (2 ^ d) x

/-- Coefficientwise `Decompress_d` on `d`-bit residues: `⌈(q / 2^d) · y⌋`, computed by integer
modulus switching. -/
def decompressResidues (q d : ℕ) (a : List ℕ) : List ℕ :=
  a.map fun y : ℕ => ZMod.modulusSwitchResidue (2 ^ d) q y

/-- The residues of the message polynomial `Decompress_1(m)` of the first `n` bits of `m`, read
as `false` beyond the end of `m`. -/
def messageResidues (n q : ℕ) (m : List Bool) : List ℕ :=
  decompressResidues q 1 ((List.range n).map fun i => if m.getD i false then 1 else 0)

/-- The centered-binomial value of a word of `2 * η` bits ([NIST, Section 4.2.2,
Algorithm 8][NISTFIPS203]): the number of `true` bits among the first `η` minus the number among
the rest. -/
def cbdValue (η : ℕ) (bits : List Bool) : ℤ :=
  ((bits.take η).count true : ℤ) - (bits.drop η).count true

/-- `SamplePolyCBD_η` on a word of `n * (2 * η)` fair bits: one centered-binomial coefficient
from each block of `2 * η` bits, reduced modulo `q`. -/
def cbdResidues (n q η : ℕ) (bits : List Bool) : List ℕ :=
  (BitString.listRows n (2 * η) bits).map fun row => (cbdValue η row % (q : ℤ)).toNat

/-- A vector of `k` polynomials from `cbdResidues`, one from each block of `n * (2 * η)` bits. -/
def cbdVecResidues (k n q η : ℕ) (bits : List Bool) : List (List ℕ) :=
  (BitString.listRows k (n * (2 * η)) bits).map (cbdResidues n q η)

/-! ### K-PKE on residue lists -/

/-- The encoding of K-PKE parameters: the ring degree `n` in unary, the modulus `q` in binary,
and the module rank `k`, the centered-binomial widths `η₁`, `η₂` and the compression widths
`d_u`, `d_v` in unary. -/
enc_structure encParams : Params where
  n : encUnary, q : encNat, k : encUnary, η₁ : encUnary, η₂ : encUnary, du : encUnary,
  dv : encUnary

/-- The residue rows of a module matrix: row `i` is the list of residue lists of `A i`. -/
def matrixResidues {k n q : ℕ} (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q)) :
    List (List (List ℕ)) :=
  List.ofFn fun i => polyVecResidues (A i)

/-- The words of the residue rows of a module matrix: the framed list of the rows, each in
`encPolyVecResidues`. -/
abbrev encMatrixResidues : List (List (List ℕ)) ↪ List Bool := encList encPolyVecResidues

/-- The layout of ciphertext words: the residue lists of `c₁`, framed, then the residues of
`c₂`. -/
abbrev encCiphertextResidues : List (List ℕ) × List ℕ ↪ List Bool :=
  encPair encPolyVecResidues (encList encNat)

/-- Native K-PKE encryption on residue lists: `u = Aᵀ r + e₁` and
`v = bᵀ r + e₂ + Decompress_1(m)`, compressed to `d_u` and `d_v` bits. -/
def encryptResidues (P : Params) (A : List (List (List ℕ))) (b : List (List ℕ)) (m : List Bool)
    (r e₁ : List (List ℕ)) (e₂ : List ℕ) : List (List ℕ) × List ℕ :=
  let u := (List.range P.k).map fun i =>
    addResidues P.q (negacyclicInnerResidues P.n P.q (A.map fun row => row.getD i []) r)
      (e₁.getD i [])
  let v := addResidues P.q (addResidues P.q (negacyclicInnerResidues P.n P.q b r) e₂)
    (messageResidues P.n P.q m)
  (u.map (compressResidues P.q P.du), compressResidues P.q P.dv v)

/-- Native K-PKE decryption on residue lists: decompress `(c₁, c₂)` to `(u', v')` and read bit `i`
as `Compress_1` of coefficient `i` of `v' - sᵀ u'`. -/
def decryptResidues (P : Params) (s c₁ : List (List ℕ)) (c₂ : List ℕ) : List Bool :=
  (compressResidues P.q 1 (subResidues P.q (decompressResidues P.q P.dv c₂)
    (negacyclicInnerResidues P.n P.q (c₁.map (decompressResidues P.q P.du)) s))).map (· == 1)

/-- Native K-PKE public-key computation on residue lists: `b = A s + e`. -/
def publicKeyResidues (P : Params) (A : List (List (List ℕ))) (s e : List (List ℕ)) :
    List (List ℕ) :=
  (List.range P.k).map fun i =>
    addResidues P.q (negacyclicInnerResidues P.n P.q (A.getD i []) s) (e.getD i [])

/-! ### Agreement with the typed operations -/

section Agreement

/-- On a natural representative, the integer modulus-switching implementation is rounded
division `⌈p x / q⌋` reduced modulo `p`. -/
theorem modulusSwitchResidue_natCast (q p x : ℕ) :
    ZMod.modulusSwitchResidue q p (x : ℤ) = roundDiv (p * x) q % p := by
  have h : (2 * (p : ℤ) * x + q) / (2 * (q : ℤ)) = ((roundDiv (p * x) q : ℕ) : ℤ) := by
    rw [roundDiv]
    push_cast
    ring_nf
  rw [ZMod.modulusSwitchResidue, h, ← Int.natCast_mod, Int.toNat_natCast]

/-- Native compression computes `compressPoly`. -/
theorem compressResidues_polyResidues {n q : ℕ} (d : ℕ) (f : Fin n → ZMod q) :
    compressResidues q d (polyResidues f) = polyResidues (compressPoly q d f) := by
  simp [compressResidues, polyResidues, compress, modulusSwitchResidue_natCast, ZMod.val_natCast,
    Function.comp_def]

/-- Native decompression computes `decompressPoly`. -/
theorem decompressResidues_polyResidues {n : ℕ} (q d : ℕ) (f : Fin n → ZMod (2 ^ d)) :
    decompressResidues q d (polyResidues f) = polyResidues (decompressPoly q d f) := by
  simp [decompressResidues, polyResidues, decompress, modulusSwitchResidue_natCast,
    ZMod.val_natCast, Function.comp_def]

/-- The native message polynomial of a word `m` is `messagePoly` of its first `n` bits. -/
theorem messageResidues_eq (P : Params) (m : List Bool) :
    messageResidues P.n P.q m = polyResidues (messagePoly P fun i => m.getD i false) := by
  rw [messagePoly, ← decompressResidues_polyResidues, messageResidues]
  congr 1
  apply List.ext_getElem (by simp [polyResidues])
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, polyResidues, List.getElem_ofFn]
  cases m.getD i false <;> rfl

private theorem toNat_emod_eq_val {q : ℕ} [NeZero q] (z : ℤ) :
    (z % (q : ℤ)).toNat = (z : ZMod q).val := by
  rw [← ZMod.val_intCast, Int.toNat_natCast]

/-- `SamplePolyCBD_η` from fair bits: decoding `n * (2 * η)` uniform bits with `cbdResidues` gives
the law of the polyResidues of `samplePolyCBD n q η`. -/
theorem uniformList_map_cbdResidues (n q η : ℕ) [NeZero q] :
    (BitString.uniformList (n * (2 * η))).map (cbdResidues n q η) =
      (ProbComp.eval (samplePolyCBD n q η)).map polyResidues := by
  have hlaw := ProbComp.eval_replicate_of_uniformList n (2 * η) (ProbComp.sampleCenteredBinomial η)
    (cbdValue η) (ProbComp.eval_sampleCenteredBinomial_eq_map η)
  rw [← OracleComp.map_ofFn_replicateFin, ProbComp.eval_map] at hlaw
  have hmap := congrArg (PMF.map (List.map fun z : ℤ => (z % (q : ℤ)).toNat)) hlaw
  simp only [PMF.map_comp, Function.comp_def, List.map_map] at hmap
  rw [show cbdResidues n q η = fun tape =>
      (BitString.listRows n (2 * η) tape).map fun row => (cbdValue η row % (q : ℤ)).toNat from rfl,
    ← hmap, samplePolyCBD, ProbComp.eval_bind]
  simp only [ProbComp.eval_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    List.map_ofFn, polyResidues, toNat_emod_eq_val]

/-- A vector of `k` independent `SamplePolyCBD_η` polynomials from `k * (n * (2 * η))` fair
bits. -/
theorem uniformList_map_cbdVecResidues (k n q η : ℕ) [NeZero q] :
    (BitString.uniformList (k * (n * (2 * η)))).map (cbdVecResidues k n q η) =
      (ProbComp.eval (sampleVecCBD k n q η)).map polyVecResidues := by
  have hpoly := uniformList_map_cbdResidues n q η
  have hlaw := ProbComp.eval_replicate_of_uniformList k (n * (2 * η))
    (polyResidues <$> samplePolyCBD n q η) (cbdResidues n q η)
    (by rw [ProbComp.eval_map, hpoly])
  rw [ProbComp.eval_replicate_map (ProbComp.eval_map _ _) k, ← OracleComp.map_ofFn_replicateFin,
    ProbComp.eval_map, PMF.map_comp] at hlaw
  rw [show cbdVecResidues k n q η = fun tape =>
      (BitString.listRows k (n * (2 * η)) tape).map (cbdResidues n q η) from rfl, ← hlaw,
    sampleVecCBD]
  simp only [Function.comp_def, List.map_ofFn]
  rfl

end Agreement

section SchemeAgreement

variable (P : Params) [NeZero P.q]

omit [NeZero P.q] in
private theorem column_matrixResidues (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    {i : ℕ} (hi : i < P.k) :
    (matrixResidues A).map (fun row => row.getD i []) = polyVecResidues fun j => A j ⟨i, hi⟩ := by
  simp [matrixResidues, polyVecResidues, List.map_ofFn, Function.comp_def, hi]

private theorem getD_polyVecResidues {k n m : ℕ} (v : Fin k → Fin n → ZMod m) {i : ℕ}
    (hi : i < k) : (polyVecResidues v).getD i [] = polyResidues (v ⟨i, hi⟩) := by
  simp [polyVecResidues, hi]

/-- Native encryption computes the residues of `encrypt`. -/
theorem encryptResidues_eq (pk : PublicKey P) (m : List Bool)
    (r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) :
    encryptResidues P (matrixResidues pk.1) (polyVecResidues pk.2) m (polyVecResidues r)
        (polyVecResidues e₁) (polyResidues e₂) =
      (polyVecResidues (encrypt P pk (fun i => m.getD i false) (r, e₁, e₂)).1,
        polyResidues (encrypt P pk (fun i => m.getD i false) (r, e₁, e₂)).2) := by
  obtain ⟨A, b⟩ := pk
  simp only [encryptResidues, encrypt, compressCiphertext, encryptRaw]
  congr 1
  · apply List.ext_getElem (by simp [polyVecResidues])
    intro i h₁ h₂
    have hi : i < P.k := by simpa using h₁
    simp only [List.getElem_map, List.getElem_range]
    rw [column_matrixResidues P A hi, getD_polyVecResidues e₁ hi,
      negacyclicInnerResidues_polyVecResidues,
      addResidues_polyResidues, compressResidues_polyResidues]
    simp [polyVecResidues, moduleSISMap, innerPoly]
  · rw [negacyclicInnerResidues_polyVecResidues, addResidues_polyResidues, messageResidues_eq,
      addResidues_polyResidues, compressResidues_polyResidues]

/-- Native decryption computes `decrypt`. -/
theorem decryptResidues_eq (s : SecretKey P) (ct : Ciphertext P) :
    decryptResidues P (polyVecResidues s) (polyVecResidues ct.1) (polyResidues ct.2) =
      List.ofFn (decrypt P s ct) := by
  have hu : (polyVecResidues ct.1).map (decompressResidues P.q P.du) =
      polyVecResidues (decompressCiphertext P ct).1 := by
    simp only [polyVecResidues, List.map_ofFn, Function.comp_def, decompressResidues_polyResidues]
    rfl
  rw [decryptResidues, hu, negacyclicInnerResidues_polyVecResidues,
    decompressResidues_polyResidues, show decompressPoly P.q P.dv ct.2 =
      (decompressCiphertext P ct).2 from rfl, subResidues_polyResidues,
    compressResidues_polyResidues]
  simp only [polyResidues, List.map_ofFn, Function.comp_def, compressPoly_apply]
  rfl

/-- Native public-key computation computes `moduleSISMap A s + e`. -/
theorem publicKeyResidues_eq (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e : Fin P.k → Fin P.n → ZMod P.q) :
    publicKeyResidues P (matrixResidues A) (polyVecResidues s) (polyVecResidues e) =
      polyVecResidues (moduleSISMap A s + e) := by
  apply List.ext_getElem (by simp [publicKeyResidues, polyVecResidues])
  intro i h₁ h₂
  have hi : i < P.k := by simpa [publicKeyResidues] using h₁
  simp only [publicKeyResidues, List.getElem_map, List.getElem_range]
  rw [show (matrixResidues A).getD i [] = polyVecResidues (A ⟨i, hi⟩) by
      simp [matrixResidues, hi],
    getD_polyVecResidues e hi, negacyclicInnerResidues_polyVecResidues,
    addResidues_polyResidues]
  simp [polyVecResidues, moduleSISMap, innerPoly]

end SchemeAgreement

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Nearest-integer modulus switching of a natural residue, with both moduli computed. -/
private theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.modulusSwitchResidue_natCast
    {q p x : α → ℕ} (hq : ComputableInPolyTime q input encNat)
    (hp : ComputableInPolyTime p input encNat) (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => ZMod.modulusSwitchResidue (q a) (p a) (x a : ℤ)) input
      encNat := by
  have h := ComputableInPolyTime.modulusSwitchResidue.comp
    ((hq.prod hp).prod (ComputableInPolyTime.intBin_natCast.comp hx))
  exact h

/-- Compression of a computed residue list, with a computed binary modulus and unary width. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.compressResidues {q d : α → ℕ}
    {a : α → List ℕ} (hq : ComputableInPolyTime q input encNat)
    (hd : ComputableInPolyTime d input encUnary)
    (ha : ComputableInPolyTime a input (encList encNat)) :
    ComputableInPolyTime (fun x => compressResidues (q x) (d x) (a x)) input (encList encNat) := by
  unfold Cslib.Crypto.MLKEM.compressResidues
  have hfst := ComputableInPolyTime.fst input encNat
  have h := ComputableInPolyTime.modulusSwitchResidue_natCast (hq.comp hfst)
    (ComputableInPolyTime.binary_two_pow.comp (hd.comp hfst))
    (ComputableInPolyTime.snd input encNat)
  exact ComputableInPolyTime.mapWithInput ha h

/-- Decompression of a computed residue list, with a computed binary modulus and unary width. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.decompressResidues {q d : α → ℕ}
    {a : α → List ℕ} (hq : ComputableInPolyTime q input encNat)
    (hd : ComputableInPolyTime d input encUnary)
    (ha : ComputableInPolyTime a input (encList encNat)) :
    ComputableInPolyTime (fun x => decompressResidues (q x) (d x) (a x)) input
      (encList encNat) := by
  unfold Cslib.Crypto.MLKEM.decompressResidues
  have hfst := ComputableInPolyTime.fst input encNat
  have h := ComputableInPolyTime.modulusSwitchResidue_natCast
    (ComputableInPolyTime.binary_two_pow.comp (hd.comp hfst)) (hq.comp hfst)
    (ComputableInPolyTime.snd input encNat)
  exact ComputableInPolyTime.mapWithInput ha h

/-- The message polynomial of a computed word, with a computed unary degree and binary modulus. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.messageResidues {n q : α → ℕ}
    {m : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hq : ComputableInPolyTime q input encNat) (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun x => messageResidues (n x) (q x) (m x)) input (encList encNat) := by
  unfold Cslib.Crypto.MLKEM.messageResidues
  have hfst := ComputableInPolyTime.fst input encUnary
  have hbit := ComputableInPolyTime.bitsGetDWithInput (hm.comp hfst)
    (ComputableInPolyTime.snd input encUnary) false
  have hite := ComputableInPolyTime.ite' (encMid := encNat) hbit (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 0)
  have hrange := ComputableInPolyTime.range.comp hn
  simp only [Function.comp_def] at hite hrange
  exact ComputableInPolyTime.decompressResidues hq (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.mapWithInput hrange hite)

/-- The centered-binomial value of a computed word, with a computed unary width. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.cbdValue {η : α → ℕ}
    {bits : α → List Bool} (hη : ComputableInPolyTime η input encUnary)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun x => cbdValue (η x) (bits x)) input encIntBin := by
  unfold Cslib.Crypto.MLKEM.cbdValue
  have hcount (word : α → List Bool) (hword : ComputableInPolyTime word input encBits) :
      ComputableInPolyTime (fun x => ((word x).count true : ℤ)) input encIntBin := by
    have h := ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.bitsCountWithInput hword (ComputableInPolyTime.const true)))
    simpa only [Function.comp_def] using h
  exact ComputableInPolyTime.intBin_sub'
    (hcount _ (ComputableInPolyTime.bitsTakeWithInput hbits hη))
    (hcount _ (ComputableInPolyTime.bitsDropWithInput hbits hη))

/-- `SamplePolyCBD_η` on a computed word, with computed unary degree and width and binary
modulus. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.cbdResidues {n q η : α → ℕ}
    {bits : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hq : ComputableInPolyTime q input encNat) (hη : ComputableInPolyTime η input encUnary)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun x => cbdResidues (n x) (q x) (η x) (bits x)) input
      (encList encNat) := by
  unfold Cslib.Crypto.MLKEM.cbdResidues
  have hwidth := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hη)
  have hrows := ComputableInPolyTime.bitsRowsWithInput hn hwidth hbits
  have hfst := ComputableInPolyTime.fst input encBits
  have hentry := ComputableInPolyTime.intBin_emodNat'
    (ComputableInPolyTime.cbdValue (hη.comp hfst) (ComputableInPolyTime.snd input encBits))
    (hq.comp hfst)
  simp only [Function.comp_def] at hrows hentry
  exact ComputableInPolyTime.mapWithInput hrows hentry

/-- Vectors of `SamplePolyCBD_η` polynomials on a computed word, with computed unary dimensions and
width and binary modulus. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.cbdVecResidues {k n q η : α → ℕ}
    {bits : α → List Bool} (hk : ComputableInPolyTime k input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hq : ComputableInPolyTime q input encNat)
    (hη : ComputableInPolyTime η input encUnary)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun x => cbdVecResidues (k x) (n x) (q x) (η x) (bits x)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLKEM.cbdVecResidues
  have hwidth := ComputableInPolyTime.unary_mul.comp (hn.prod
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hη)))
  have hrows := ComputableInPolyTime.bitsRowsWithInput hk hwidth hbits
  have hfst := ComputableInPolyTime.fst input encBits
  have hentry := ComputableInPolyTime.cbdResidues (hn.comp hfst) (hq.comp hfst) (hη.comp hfst)
    (ComputableInPolyTime.snd input encBits)
  simp only [Function.comp_def] at hrows hentry
  exact ComputableInPolyTime.mapWithInput hrows hentry

/-- Native encryption on residue lists, with computed parameters and inputs. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encryptResidues {P : α → Params}
    {A : α → List (List (List ℕ))} {b r e₁ : α → List (List ℕ)} {m : α → List Bool}
    {e₂ : α → List ℕ} (hP : ComputableInPolyTime P input encParams)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (hb : ComputableInPolyTime b input encPolyVecResidues)
    (hm : ComputableInPolyTime m input encBits)
    (hr : ComputableInPolyTime r input encPolyVecResidues)
    (he₁ : ComputableInPolyTime e₁ input encPolyVecResidues)
    (he₂ : ComputableInPolyTime e₂ input (encList encNat)) :
    ComputableInPolyTime (fun x => encryptResidues (P x) (A x) (b x) (m x) (r x) (e₁ x) (e₂ x))
      input encCiphertextResidues := by
  unfold Cslib.Crypto.MLKEM.encryptResidues
  dsimp only
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x => (P x).q) input encNat := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hdu : ComputableInPolyTime (fun x => (P x).du) input encUnary := by fun_prop
  have hdv : ComputableInPolyTime (fun x => (P x).dv) input encUnary := by fun_prop
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hcol := ComputableInPolyTime.mapWithInput
    (f := fun (p : α × ℕ) (row : List (List ℕ)) => row.getD p.2 []) (hA.comp hfst)
    ((ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
      ((ComputableInPolyTime.snd (encPair input encUnary) encPolyVecResidues).prod
        (hsnd.comp (ComputableInPolyTime.fst (encPair input encUnary) encPolyVecResidues))))
  have he₁i := (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
    ((he₁.comp hfst).prod hsnd)
  simp only [Function.comp_def] at hcol he₁i
  have hui := ComputableInPolyTime.addResidues (hq.comp hfst)
    (ComputableInPolyTime.negacyclicInnerResidues (hn.comp hfst) (hq.comp hfst) hcol (hr.comp hfst))
    he₁i
  have hrange := ComputableInPolyTime.range.comp hk
  simp only [Function.comp_def] at hui hrange
  have hu : ComputableInPolyTime (fun x => (List.range (P x).k).map fun i =>
      addResidues (P x).q (negacyclicInnerResidues (P x).n (P x).q
        ((A x).map fun row => row.getD i []) (r x)) ((e₁ x).getD i []))
      input encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput hrange hui
  have hcu : ComputableInPolyTime (fun x => ((List.range (P x).k).map fun i =>
      addResidues (P x).q (negacyclicInnerResidues (P x).n (P x).q
        ((A x).map fun row => row.getD i []) (r x)) ((e₁ x).getD i [])).map
          (compressResidues (P x).q (P x).du)) input encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput hu
      (ComputableInPolyTime.compressResidues
        (hq.comp (ComputableInPolyTime.fst input (encList encNat)))
        (hdu.comp (ComputableInPolyTime.fst input (encList encNat)))
        (ComputableInPolyTime.snd input (encList encNat)))
  have hv := ComputableInPolyTime.compressResidues hq hdv
    (ComputableInPolyTime.addResidues hq
      (ComputableInPolyTime.addResidues hq
        (ComputableInPolyTime.negacyclicInnerResidues hn hq hb hr) he₂)
      (ComputableInPolyTime.messageResidues hn hq hm))
  exact hcu.prod hv

/-- Native decryption on residue lists, with computed parameters and inputs. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.decryptResidues {P : α → Params}
    {s c₁ : α → List (List ℕ)} {c₂ : α → List ℕ} (hP : ComputableInPolyTime P input encParams)
    (hs : ComputableInPolyTime s input encPolyVecResidues)
    (hc₁ : ComputableInPolyTime c₁ input encPolyVecResidues)
    (hc₂ : ComputableInPolyTime c₂ input (encList encNat)) :
    ComputableInPolyTime (fun x => decryptResidues (P x) (s x) (c₁ x) (c₂ x)) input encBits := by
  unfold Cslib.Crypto.MLKEM.decryptResidues
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x => (P x).q) input encNat := by fun_prop
  have hdu : ComputableInPolyTime (fun x => (P x).du) input encUnary := by fun_prop
  have hdv : ComputableInPolyTime (fun x => (P x).dv) input encUnary := by fun_prop
  have hu := ComputableInPolyTime.mapWithInput
    (f := fun (x : α) (c : List ℕ) => decompressResidues (P x).q (P x).du c) hc₁
    (ComputableInPolyTime.decompressResidues
      (hq.comp (ComputableInPolyTime.fst input (encList encNat)))
      (hdu.comp (ComputableInPolyTime.fst input (encList encNat)))
      (ComputableInPolyTime.snd input (encList encNat)))
  have hw := ComputableInPolyTime.compressResidues hq (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.subResidues hq (ComputableInPolyTime.decompressResidues hq hdv hc₂)
      (ComputableInPolyTime.negacyclicInnerResidues hn hq hu hs))
  have hbit : ComputableInPolyTime (fun p : α × ℕ => p.2 == 1) (encPair input encNat) encBool := by
    fun_prop
  exact ComputableInPolyTime.mapToBitsWithInput (f := fun (_ : α) (y : ℕ) => y == 1) hw hbit

/-- Native public-key computation on residue lists, with computed parameters and inputs. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.publicKeyResidues {P : α → Params}
    {A : α → List (List (List ℕ))} {s e : α → List (List ℕ)}
    (hP : ComputableInPolyTime P input encParams)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (hs : ComputableInPolyTime s input encPolyVecResidues)
    (he : ComputableInPolyTime e input encPolyVecResidues) :
    ComputableInPolyTime (fun x => publicKeyResidues (P x) (A x) (s x) (e x)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLKEM.publicKeyResidues
  have hn : ComputableInPolyTime (fun x => (P x).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun x => (P x).q) input encNat := by fun_prop
  have hk : ComputableInPolyTime (fun x => (P x).k) input encUnary := by fun_prop
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hAi := (ComputableInPolyTime.listGetD (encA := encPolyVecResidues) []).comp
    ((hA.comp hfst).prod hsnd)
  have hei := (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
    ((he.comp hfst).prod hsnd)
  simp only [Function.comp_def] at hAi hei
  have hbi := ComputableInPolyTime.addResidues (hq.comp hfst)
    (ComputableInPolyTime.negacyclicInnerResidues (hn.comp hfst) (hq.comp hfst) hAi (hs.comp hfst))
    hei
  have hrange := ComputableInPolyTime.range.comp hk
  simp only [Function.comp_def] at hbi hrange
  exact ComputableInPolyTime.mapWithInput hrange hbi

end PolyTime

end Cslib.Crypto.MLKEM
