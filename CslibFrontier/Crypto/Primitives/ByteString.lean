/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Init
public import Mathlib.Data.Fin.Tuple.Take
import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder
import CslibFrontier.Foundations.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Byte strings

This module supplies the byte boundary shared by executable cryptographic primitives. A byte is an
unsigned integer below 256, and `FixedBytes n` records a byte-string length in its type. The
big-endian bit conversion follows the byte convention used by FIPS 180-4 and FIPS 205; primitives
with a different within-byte convention, such as FIPS 202's Keccak, keep that conversion explicit.

## Main definitions

* `Cslib.Crypto.Byte`: one unsigned byte.
* `Cslib.Crypto.FixedBytes`: a byte string whose length is part of its type.
* `Cslib.Crypto.bytesToBitsBE`: big-endian serialization of a list of bytes.
* `Cslib.Crypto.bitsToFixedBytesBE`: split a bit list into typed big-endian bytes.

## Main results

* `Cslib.Crypto.length_bytesToBitsBE`: byte serialization has eight bits per byte.
* `Cslib.Crypto.byteOfBitsBE_byteBitsBE`, `Cslib.Crypto.byteBitsBE_byteOfBitsBE`: converting one
  byte to bits and back is exact in either direction.
* `Cslib.Crypto.bytesToBitsBE_bitsToFixedBytesBE`: an exact-length bit string round-trips through
  typed bytes.
* `Cslib.Crypto.bytesToBitsBE_natToFixedBytesBE`: natural-number serialization retains exactly
  its low `8n` bits.
* `Cslib.Crypto.bytesToBitsBE_lt_iff_lt`: equal-length byte strings and their big-endian bit
  serializations have the same lexicographic order.
-/

public section

namespace Cslib.Crypto

open Cslib.BitString

/-- One byte, represented by its unsigned integer value. -/
abbrev Byte := Fin (2 ^ 8)

/-- A byte string whose byte length is part of its type. -/
abbrev FixedBytes (n : ℕ) := Fin n → Byte

namespace FixedBytes

/-- The list view of a fixed-length byte string. -/
def toList {n : ℕ} (X : FixedBytes n) : List Byte := List.ofFn X

/-- The list view has the byte length recorded in the type. -/
@[simp] theorem length_toList {n : ℕ} (X : FixedBytes n) : X.toList.length = n := by
  simp [toList]

end FixedBytes

/-- The eight big-endian bits of a byte. -/
@[expose]
def byteBitsBE (x : Byte) : List Bool := binaryWord 8 x

/-- The bits of a byte list in big-endian order within each byte. -/
@[expose]
def bytesToBitsBE : List Byte → List Bool
  | [] => []
  | x :: X => byteBitsBE x ++ bytesToBitsBE X

/-- A byte list has eight serialized bits per byte. -/
@[simp] theorem length_bytesToBitsBE (X : List Byte) :
    (bytesToBitsBE X).length = 8 * X.length := by
  induction X with
  | nil => simp [bytesToBitsBE]
  | cons x X ih =>
    simp only [bytesToBitsBE, byteBitsBE, List.length_append, ih, List.length_cons]
    rw [length_binaryWord x.isLt]
    omega

/-- One byte and its eight-bit big-endian serialization have the same strict order. -/
private theorem byteBitsBE_lt_iff_lt (x y : Byte) :
    byteBitsBE x < byteBitsBE y ↔ x < y := by
  have hlength : (byteBitsBE x).length = (byteBitsBE y).length := by
    change (binaryWord 8 x).length = (binaryWord 8 y).length
    rw [length_binaryWord x.isLt, length_binaryWord y.isLt]
  rw [← BitString.binaryValue_lt_iff_lt hlength]
  simp [byteBitsBE]

/-- Equal-length byte strings and their big-endian bit serializations have the same strict
lexicographic order. -/
theorem bytesToBitsBE_lt_iff_lt {X Y : List Byte} (hlength : X.length = Y.length) :
    bytesToBitsBE X < bytesToBitsBE Y ↔ X < Y := by
  induction X generalizing Y with
  | nil =>
      obtain rfl : Y = [] := List.length_eq_zero_iff.mp hlength.symm
      simp [bytesToBitsBE]
  | cons x X ih =>
      obtain ⟨y, Y, rfl⟩ := List.exists_cons_of_length_eq_add_one hlength.symm
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength
      have byteBitsLength (z : Byte) : (byteBitsBE z).length = 8 := by
        change (binaryWord 8 z).length = 8
        exact length_binaryWord z.isLt
      rcases lt_trichotomy x y with hlt | heq | hgt
      · have hbits := (byteBitsBE_lt_iff_lt x y).2 hlt
        have happend := List.append_lt_append_of_lt_of_length_eq hbits
          ((byteBitsLength x).trans (byteBitsLength y).symm)
          (bytesToBitsBE X) (bytesToBitsBE Y)
        exact iff_of_true (by simpa [bytesToBitsBE] using happend)
          (by exact List.Lex.rel hlt)
      · subst y
        have prefixCancel : ∀ s : List Bool,
            s ++ bytesToBitsBE X < s ++ bytesToBitsBE Y ↔
              bytesToBitsBE X < bytesToBitsBE Y := by
          intro s
          induction s with
          | nil => rfl
          | cons bit tail ihprefix =>
              exact List.lex_cons_iff.trans ihprefix
        simp only [bytesToBitsBE]
        rw [prefixCancel (byteBitsBE x), ih hlength]
        exact List.lex_cons_iff.symm
      · have hbits := (byteBitsBE_lt_iff_lt y x).2 hgt
        have happend := List.append_lt_append_of_lt_of_length_eq hbits
          ((byteBitsLength y).trans (byteBitsLength x).symm)
          (bytesToBitsBE Y) (bytesToBitsBE X)
        have hnotBits : ¬ (bytesToBitsBE (x :: X) < bytesToBitsBE (y :: Y)) :=
          not_lt_of_gt (by simpa [bytesToBitsBE] using happend)
        have hnotBytes : ¬ (x :: X < y :: Y) :=
          not_lt_of_gt (show y :: Y < x :: X from List.Lex.rel hgt)
        exact iff_of_false hnotBits hnotBytes

/-- Read at most eight big-endian bits as one byte. Missing low-order bits are not added; callers
that require a full byte should supply an eight-bit chunk. -/
def byteOfBitsBE (bits : List Bool) : Byte :=
  ⟨binaryValue (bits.take 8), by
    exact Nat.lt_of_lt_of_le (binaryValue_lt_two_pow (bits.take 8))
      (Nat.pow_le_pow_right (by decide) (List.length_take_le 8 bits))⟩

/-- Serializing one byte to eight big-endian bits and reading it back recovers the byte. -/
@[simp] theorem byteOfBitsBE_byteBitsBE (x : Byte) : byteOfBitsBE (byteBitsBE x) = x := by
  apply Fin.ext
  change binaryValue ((binaryWord 8 x).take 8) = x
  have hlength : (binaryWord 8 x).length = 8 := length_binaryWord x.isLt
  rw [List.take_of_length_le (Nat.le_of_eq hlength)]
  exact binaryValue_binaryWord 8 x

/-- Reading an eight-bit word as a byte and serializing it recovers the word. -/
@[simp] theorem byteBitsBE_byteOfBitsBE (bits : List Bool) (h : bits.length = 8) :
    byteBitsBE (byteOfBitsBE bits) = bits := by
  apply binaryValue_injective_of_length_eq
  · simpa [byteBitsBE, h] using (length_binaryWord (byteOfBitsBE bits).isLt)
  · simp only [byteBitsBE, binaryValue_binaryWord, byteOfBitsBE]
    rw [List.take_of_length_le (by omega)]

/-- Split a bit list into `n` consecutive big-endian bytes. An incomplete or absent final chunk is
read using `byteOfBitsBE`; exact-length clients avoid that fallback by construction. -/
def bitsToFixedBytesBE (n : ℕ) (bits : List Bool) : FixedBytes n := fun i =>
  byteOfBitsBE ((bits.drop (8 * i.val)).take 8)

/-- An exact `8 * n`-bit word round-trips through its `n` typed big-endian bytes. -/
@[simp] theorem bytesToBitsBE_bitsToFixedBytesBE (n : ℕ) (bits : List Bool)
    (h : bits.length = 8 * n) :
    bytesToBitsBE ((bitsToFixedBytesBE n bits).toList) = bits := by
  induction n generalizing bits with
  | zero =>
      simp only [Nat.mul_zero] at h
      rw [List.length_eq_zero_iff.mp h]
      simp [FixedBytes.toList, bytesToBitsBE]
  | succ n ih =>
      have hlength : 8 ≤ bits.length := by omega
      have htake : (bits.take 8).length = 8 := by simp [Nat.min_eq_left hlength]
      have hdrop : (bits.drop 8).length = 8 * n := by simp; omega
      rw [show (bitsToFixedBytesBE (n + 1) bits).toList =
          byteOfBitsBE (bits.take 8) :: (bitsToFixedBytesBE n (bits.drop 8)).toList by
        simp only [bitsToFixedBytesBE, FixedBytes.toList, List.ofFn_succ]
        congr 1
        apply List.ofFn_inj.mpr
        funext i
        simp [bitsToFixedBytesBE, List.drop_drop, Nat.mul_add, Nat.add_comm]]
      simp only [bytesToBitsBE]
      rw [byteBitsBE_byteOfBitsBE (bits.take 8) htake, ih (bits.drop 8) hdrop,
        List.take_append_drop]

/-- Encode a natural number as exactly `n` big-endian bytes, retaining its low `8n` bits. -/
def natToFixedBytesBE (n value : ℕ) : FixedBytes n := fun i =>
  ⟨value / 2 ^ (8 * (n - 1 - i.val)) % 256, Nat.mod_lt _ (by decide)⟩

private theorem natToFixedBytesBE_toList_succ (n value : ℕ) :
    (natToFixedBytesBE (n + 1) value).toList =
      ⟨value / 2 ^ (8 * n) % 256, Nat.mod_lt _ (by decide)⟩ ::
        (natToFixedBytesBE n value).toList := by
  simp only [natToFixedBytesBE, FixedBytes.toList, List.ofFn_succ]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  apply Fin.ext
  dsimp only
  rw [Fin.val_succ]
  congr 3
  omega

/-- Serializing a natural number as `n` bytes produces its low `8n` bits in big-endian order. -/
theorem bytesToBitsBE_natToFixedBytesBE (n value : ℕ) :
    bytesToBitsBE (natToFixedBytesBE n value).toList =
      binaryWord (8 * n) (value % 2 ^ (8 * n)) := by
  induction n with
  | zero =>
      change [] = binaryWord 0 (value % 1)
      rw [Nat.mod_one]
      rfl
  | succ n ih =>
      rw [natToFixedBytesBE_toList_succ]
      simp only [bytesToBitsBE, byteBitsBE, ih]
      apply binaryValue_injective_of_length_eq
      · rw [List.length_append,
          length_binaryWord (Nat.mod_lt _ (by decide)),
          length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _)),
          length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _))]
        omega
      · rw [binaryValue_append, binaryValue_binaryWord, binaryValue_binaryWord,
          binaryValue_binaryWord, length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _))]
        rw [show 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 by
          rw [show 8 * (n + 1) = 8 * n + 8 by omega]
          simp only [Nat.pow_succ]
          omega]
        calc
          _ = value % (2 ^ (8 * n) * 256) / 2 ^ (8 * n) * 2 ^ (8 * n) +
              value % 2 ^ (8 * n) := by rw [Nat.mod_mul_right_div_self]
          _ = value % (2 ^ (8 * n) * 256) / 2 ^ (8 * n) * 2 ^ (8 * n) +
              value % (2 ^ (8 * n) * 256) % 2 ^ (8 * n) := by
                rw [Nat.mod_mul_right_mod]
          _ = _ := Nat.div_add_mod' _ _

end Cslib.Crypto
