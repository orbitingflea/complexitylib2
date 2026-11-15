/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Cyclic group families of arbitrary order

A `CyclicGroupFamily` is a family of finite cyclic groups whose orders need not be prime, with the
encodings and polynomial-time operations of a `PrimeOrderGroupFamily`. It differs from
`PrimeOrderGroupFamily` in two fields: `order_ne_zero` replaces `prime_order`, and
`smul_generator_injective`, the injectivity of `α ↦ α • g` on `ZMod q`, replaces
`generator_ne_zero`. With `card_carrier` the injectivity says that `g` generates its group of
order `q`. `PrimeOrderGroupFamily.toCyclicGroupFamily` maps every prime-order family to a cyclic
one, with the injectivity from `PrimeOrderGroupFamily.smul_generator_injective`.

Families of composite order are the setting of [BonehShoup2023], Exercise 10.24 (p. 431), which
drops the restriction that the order is prime from the DDH attack game.

## Main definitions

* `Cslib.Crypto.CyclicGroupFamily`: cyclic groups of nonzero order with polynomial-time operations
  on encoded elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.toCyclicGroupFamily`: a prime-order family as a cyclic one.

## Main results

* `Cslib.Crypto.CyclicGroupFamily.computableInPolyTime_order_comp`,
  `Cslib.Crypto.CyclicGroupFamily.computableInPolyTime_encode_generator`,
  `Cslib.Crypto.CyclicGroupFamily.computableInPolyTime_encode_zero`,
  `Cslib.Crypto.CyclicGroupFamily.computableInPolyTime_encode_natCast_smul`: `fun_prop` rules for
  the order, the encoded generator, the encoded identity and the encoded multiple by a natural
  number, on computed group parameters.

## Implementation notes

`PrimeOrderGroupFamily` does not extend `CyclicGroupFamily`: the two structures repeat their
common fields, and `toCyclicGroupFamily` copies them. The DDH vocabulary over this structure, and
its agreement with the prime-order one under `toCyclicGroupFamily`, are in
`CslibFrontier/Crypto/Computational/DiffieHellman/CyclicGroupFamily.lean`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 10.5 and Exercise 10.24 (p. 431).
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- A family of finite cyclic groups of nonzero order, indexed by public group parameters, with
polynomial-time operations on encoded elements. It is `PrimeOrderGroupFamily` with
`order_ne_zero` in place of `prime_order` and `smul_generator_injective` in place of
`generator_ne_zero`, so the order need not be prime. -/
structure CyclicGroupFamily where
  /-- Public group parameters: `d` selects `Carrier d`, `order d` and `generator d`. -/
  Desc : Type
  /-- The bit-string encoding of the public group parameters given to algorithms. -/
  encDesc : Desc ↪ List Bool
  /-- The order of each group. -/
  order : Desc → ℕ
  /-- Every order is nonzero. -/
  order_ne_zero : ∀ d, order d ≠ 0
  /-- The groups, written additively. -/
  Carrier : Desc → Type
  /-- Each group is commutative. -/
  [addCommGroup : ∀ d, AddCommGroup (Carrier d)]
  /-- Each group is a `ZMod q`-module, where `q` is its order. -/
  [module : ∀ d, Module (ZMod (order d)) (Carrier d)]
  /-- The generator of each group. -/
  generator : ∀ d, Carrier d
  /-- Each group has `q` elements. -/
  card_carrier : ∀ d, Nat.card (Carrier d) = order d
  /-- The generator has order `q`: `α ↦ α • g` is injective on `ZMod q`. With `card_carrier`,
  the generator generates the group. -/
  smul_generator_injective : ∀ d, Function.Injective fun α : ZMod (order d) => α • generator d
  /-- Group elements as words. -/
  encode : ∀ d, Carrier d → List Bool
  /-- Distinct elements have distinct encodings. -/
  encode_injective : ∀ d, Function.Injective (encode d)
  /-- Addition of encoded elements. -/
  add : Desc × List Bool × List Bool → List Bool
  /-- `add` adds encoded elements. -/
  add_encode : ∀ d x y, add (d, encode d x, encode d y) = encode d (x + y)
  /-- Multiplication of an encoded element by a natural number. -/
  smul : Desc × ℕ × List Bool → List Bool
  /-- `smul` multiplies encoded elements by natural numbers. -/
  smul_encode : ∀ d (a : ℕ) x, smul (d, a, encode d x) = encode d ((a : ZMod (order d)) • x)
  /-- The order is computable in polynomial time from the public group parameters. -/
  computableInPolyTime_order : ComputableInPolyTime order encDesc encNat
  /-- The encoded generator is computable in polynomial time from the public group parameters. -/
  computableInPolyTime_generator :
    ComputableInPolyTime (fun d => encode d (generator d)) encDesc encBits
  /-- Addition is computable in polynomial time. -/
  computableInPolyTime_add :
    ComputableInPolyTime add (encPair encDesc (encPair encBits encBits)) encBits
  /-- Multiplication by a binary natural number is computable in polynomial time. -/
  computableInPolyTime_smul :
    ComputableInPolyTime smul (encPair encDesc (encPair encNat encBits)) encBits

/-- A prime-order family as a cyclic group family: a prime is nonzero, and
`PrimeOrderGroupFamily.smul_generator_injective` supplies the injectivity. The other fields are
copied. -/
@[expose] def PrimeOrderGroupFamily.toCyclicGroupFamily (F : PrimeOrderGroupFamily) :
    CyclicGroupFamily where
  Desc := F.Desc
  encDesc := F.encDesc
  order := F.order
  order_ne_zero d := (F.prime_order d).ne_zero
  Carrier := F.Carrier
  generator := F.generator
  card_carrier := F.card_carrier
  smul_generator_injective := F.smul_generator_injective
  encode := F.encode
  encode_injective := F.encode_injective
  add := F.add
  add_encode := F.add_encode
  smul := F.smul
  smul_encode := F.smul_encode
  computableInPolyTime_order := F.computableInPolyTime_order
  computableInPolyTime_generator := F.computableInPolyTime_generator
  computableInPolyTime_add := F.computableInPolyTime_add
  computableInPolyTime_smul := F.computableInPolyTime_smul

namespace CyclicGroupFamily

variable (F : CyclicGroupFamily)

attribute [instance] addCommGroup module

instance (d : F.Desc) : NeZero (F.order d) := ⟨F.order_ne_zero d⟩

/-- Equality of group elements, decided on their injective encodings. -/
instance (d : F.Desc) : DecidableEq (F.Carrier d) := fun x y =>
  decidable_of_iff (F.encode d x = F.encode d y) (F.encode_injective d).eq_iff

variable {F} in
/-- The order of computed group parameters. -/
@[fun_prop] theorem computableInPolyTime_order_comp {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => F.order (d a)) enc encNat :=
  F.computableInPolyTime_order.comp hd

variable {F} in
/-- The encoded generator of computed group parameters. -/
@[fun_prop] theorem computableInPolyTime_encode_generator {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => F.encode (d a) (F.generator (d a))) enc encBits :=
  F.computableInPolyTime_generator.comp hd

variable {F} in
/-- The encoded identity of computed group parameters, computed as `0 • g`. -/
@[fun_prop] theorem computableInPolyTime_encode_zero {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => F.encode (d a) 0) enc encBits :=
  .of_enc_eq (F.computableInPolyTime_smul.comp
      (hd.prod ((ComputableInPolyTime.const 0).prod (computableInPolyTime_encode_generator hd))))
    fun a => by simp [F.smul_encode]

variable {F} in
/-- The encoded multiple of a computed element by a computed natural number. -/
@[fun_prop] theorem computableInPolyTime_encode_natCast_smul {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} {k : α → ℕ} {x : (a : α) → F.Carrier (d a)}
    (hd : ComputableInPolyTime d enc F.encDesc) (hk : ComputableInPolyTime k enc encNat)
    (hx : ComputableInPolyTime (fun a => F.encode (d a) (x a)) enc encBits) :
    ComputableInPolyTime (fun a => F.encode (d a) ((k a : ZMod (F.order (d a))) • x a)) enc
      encBits :=
  .of_enc_eq (F.computableInPolyTime_smul.comp (hd.prod (hk.prod hx))) fun a => by
    simp [F.smul_encode]

end CyclicGroupFamily

end Cslib.Crypto
