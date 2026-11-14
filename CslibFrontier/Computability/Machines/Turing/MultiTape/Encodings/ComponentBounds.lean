/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ComponentBounds.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi

/-!
# Component bounds without unfolding encodings

Use `simp only [enc_component]` for finite-table entries and syntactic pair projections.
For a list element supply its membership proof, as in `simp only [enc_component, hm]`.
The element rule uses `SizedListEncoding`, so it also applies to readable encodings other than
`encList`. The set is opt-in and does not expand words or replace nonlinear arithmetic.

Simp matching does not in general recover a pair from a reduced concrete projection: use
`length_le_encPair_left ea eb (a, b)` (or the right-hand provider) for concrete pairs.
List counts and suffixes require an explicit element encoding, which is absent from their goals.
Use `SizedListEncoding.length_le (encA := ea) (encL := el) xs` and
`SizedListEncoding.length_drop_le (encA := ea) (encL := el) xs i` directly.
These two class fields are deliberately not registered in the collection.

The sparse CNF compiler uses these rules to obtain element bounds before transporting them
through its enclosing pair and polynomial growth estimates.
-/

attribute [enc_component] Turing.MultiTapeTM.length_le_encPair_left
  Turing.MultiTapeTM.length_le_encPair_right
  Turing.MultiTapeTM.SizedListEncoding.length_elem_le

attribute [enc_component] Turing.MultiTapeTM.length_le_encPi
