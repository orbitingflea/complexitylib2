/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Conventional
public import CslibFrontier.Crypto.Primitives.Garbling.Basic
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Label
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.BitString.Neg

/-!
# Point-and-permute garbling as a garbling scheme

The point-and-permute garbling of `CslibFrontier.Crypto.Primitives.Garbling.Basic` as a garbling
scheme in the sense of Bellare, Hoang and Rogaway [BellareHoangRogaway2012] (`Garbling.Scheme`),
over valid conventional circuits (`ValidCircuit`): `PointPermute.scheme family`, whose masks are
keyed by a word family `family`. This module gives the definitions and their correctness only.
Polynomial running times are proved in
`CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient`. Privacy (`prv.sim` with the
topology as side information) is open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293).

The scheme is a variant of `Garble1` of [BellareHoangRogaway2012] (§5.1, Fig. 7) with the
PRF-based dual-key cipher of §5.5, not `Garble1` itself. In `Garble1` the type of an output wire's
token is its semantics and `d` is empty, and both keys of a row are used at the one tweak
`g ‖ a ‖ b`. Here output wires are permuted too, `d` holds their permutation bits, and each
argument slot of a row has its own tweak.

At security parameter `k`, a wire key has `k + 1` bits and a label is the `(k + 2)`-bit word of a
key followed by its colour bit. The masks come from the keyed function
`PRF.label (PRF.atLevel family (k + 1))`, which sends a key and a `k`-bit tweak to a label
(`PointPermute.labelWord` on words). Argument slot `a` of row `i` of gate `g` has the tweak
`8 g + 2 i + a`, reduced modulo `2 ^ k` (`PointPermute.tweak`); rows are numbered by the colours of
the two arguments, the first argument most significant. Correctness holds for every family and
every tweak.

The coins are the `n + q` permutation bits followed by two keys for each wire, colour `0` first.
`Gb` writes the garbled function `F` as the header `(k, n, m, q)`, in unary, followed for each gate
by its two argument wires `A g` and `B g` as `w`-bit numbers, `w` the bit length of `n + q`, and
its four rows. So `F` carries the topology, which the evaluator `Ev(F, X)` reads, and its length
depends only on `k` and `(n, m, q)`, as the length condition requires. The encoding information
`e` lists the two labels of each input wire, for bit `0` and bit `1`; the decoding information `d`
lists the permutation bits of the `m` output wires. `De(d, Y)` reads the colour bit of each of the
`m` labels of `Y` and adds the decoding bit; it fails only when `|Y|` is not a multiple of `m`.

The garbler and the evaluator are list programs. The garbler writes the typed garbling `garbleWith`
of `ConventionalCircuit.toCircuit f` (`PointPermute.gb_eq_encodeGarbled`), and the evaluator
follows every fixed point of the typed evaluation round (`PointPermute.evalWord_encodeFn`), so
correctness follows from `Garbled.run_garbleWith` and `ConventionalCircuit.eval_toCircuit`.

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.scheme`: point-and-permute garbling as a garbling scheme.
* `Cslib.Crypto.Garbling.PointPermute.encodeFn`, `Cslib.Crypto.Garbling.PointPermute.encodeGarbled`:
  the words of a typed garbled table and of a typed garbled circuit.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.gb_eq_encodeGarbled`: the garbler computes `garbleWith`.
* `Cslib.Crypto.Garbling.PointPermute.evalWord_encodeFn`: the evaluator computes the typed
  evaluation.
* `Cslib.Crypto.Garbling.PointPermute.scheme_isValid`: it is a valid garbling scheme.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [D. Beaver, S. Micali, P. Rogaway, *The Round Complexity of Secure
  Protocols*][BeaverMicaliRogaway1990]
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Cslib.Circuits Turing.MultiTapeTM

/-! ### Words -/

/-- The tweak of argument slot `a` of row `i` of gate `g` at parameter `k`: the `k` low bits of
`8 g + 2 i + a`, least significant first. -/
@[expose] def tweak (k g i a : ℕ) : List Bool := BitString.lowBits k (8 * g + 2 * i + a)

variable (family : List Bool → List Bool → List Bool)

/-- The keyed function on words at parameter `k`: the label of the key word `key` at the tweak
word `t` is the first `k + 1` bits of `family key (0 ‖ t)`, padded with `false`, followed by the
first bit of `family key (1 ‖ t)`. On a `(k + 1)`-bit key and a `k`-bit tweak it is the label of
`PRF.label (PRF.atLevel family (k + 1))` (`labelWord_ofFn`). -/
@[expose] def labelWord (k : ℕ) (key t : List Bool) : List Bool :=
  (family key (false :: t) ++ List.replicate (k + 1) false).take (k + 1) ++
    [(family key (true :: t)).getD 0 false]

/-- The permutation bit of wire `v`, numbered from `0`: bit `v` of the coins. -/
@[expose] def permOf (coins : List Bool) (v : ℕ) : Bool := coins.getD v false

/-- The key of colour `c` of wire `v` among `wires` wires: key number `2 v + c` of `k + 1` bits,
after the `wires` permutation bits. -/
@[expose] def keyOf (k wires : ℕ) (coins : List Bool) (v : ℕ) (c : Bool) : List Bool :=
  BitString.listRow (k + 1) (if c then 2 * v + 1 else 2 * v) (coins.drop wires)

/-- The label of colour `c` of wire `v`: its key followed by `c`. -/
@[expose] def labelOf (k wires : ℕ) (coins : List Bool) (v : ℕ) (c : Bool) : List Bool :=
  keyOf k wires coins v c ++ [c]

/-- The bit length of the wire numbers of a circuit with `n` inputs and `q` gates. -/
@[expose] def wireWidth (n q : ℕ) : ℕ := (n + q).size

/-- Row `i` of gate `g` of the garbling of `f` at parameter `k` with coins `coins`: the label of
the gate's output for the bits that the row's colours encode, masked by the keyed function at the
two argument keys of those colours. -/
@[expose] def rowWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) (g : Fin f.q)
    (i : ℕ) : List Bool :=
  let wires := f.n + f.q
  let a := f.A g - 1
  let b := f.B g - 1
  let v := f.n + g
  let bit := f.G g (i.testBit 1 ^^ permOf coins a) (i.testBit 0 ^^ permOf coins b)
  List.zipWith xor (labelOf k wires coins v (bit ^^ permOf coins v))
    (List.zipWith xor (labelWord family k (keyOf k wires coins a (i.testBit 1)) (tweak k g i 0))
      (labelWord family k (keyOf k wires coins b (i.testBit 0)) (tweak k g i 1)))

/-- The header `(k, n, m, q)` of a garbled function, four unary numbers. -/
abbrev encHeader : (ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encUnary))

/-- A garbled function: its header framed, then its body. -/
abbrev encFn : ((ℕ × ℕ × ℕ × ℕ) × List Bool) ↪ List Bool := encPair encHeader encBits

/-- The decoder of garbled functions. -/
def fnDecoder : Decoder encFn :=
  .pair (.pair .unary (.pair .unary (.pair .unary .unary))) .bits

/-- The garbled function of `f`: the header `(k, n, m, q)`, then for each gate its argument
wires as `w`-bit numbers and its four rows. -/
@[expose] def fnWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  encFn ((k, f.n, f.m, f.q), (List.ofFn fun g : Fin f.q =>
    BitString.lowBits (wireWidth f.n f.q) (f.A g) ++
      BitString.lowBits (wireWidth f.n f.q) (f.B g) ++
      (List.ofFn fun i : Fin 4 => rowWord family k f coins g i).flatten).flatten)

/-- The encoding information of `f`: for each input wire, the labels encoding `0` and `1`; label
`j` encodes bit `j mod 2` of input `j / 2`. -/
@[expose] def encInfoWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (2 * f.n) =>
    labelOf k (f.n + f.q) coins (j / 2) (j.val.testBit 0 ^^ permOf coins (j / 2))).flatten

/-- The decoding information of `f`: the permutation bits of its last `m` wires. -/
@[expose] def decInfoWord (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  List.ofFn fun o : Fin f.m => permOf coins (f.n + f.q - f.m + o)

/-- `En(e, x)`: the label of each bit of `x`, read from `e` as two labels per input of
`|e| / (2 |x|)` bits each. -/
@[expose] def encodeWord (e x : List Bool) : List Bool :=
  ((List.range x.length).map fun i => BitString.listRow (e.length / (2 * x.length))
    (if x.getD i false then 2 * i + 1 else 2 * i) e).flatten

/-- One gate of `Ev`: read the gate's argument wires and their labels, select the row named by
their colours, and remove the masks with their keys. -/
@[expose] def evalGate (k w : ℕ) (body : List Bool) (labels : List (List Bool)) (g : ℕ) :
    List (List Bool) :=
  let gate := BitString.listRow (2 * w + 4 * (k + 2)) g body
  let la := labels.getD (BitString.boundedBinaryValue labels.length (gate.take w).reverse - 1) []
  let lb := labels.getD
    (BitString.boundedBinaryValue labels.length ((gate.drop w).take w).reverse - 1) []
  let i := (if la.getD (k + 1) false then 2 else 0) + (if lb.getD (k + 1) false then 1 else 0)
  labels ++ [List.zipWith xor (BitString.listRow (k + 2) i (gate.drop (2 * w)))
    (List.zipWith xor (labelWord family k (la.take (k + 1)) (tweak k g i 0))
      (labelWord family k (lb.take (k + 1)) (tweak k g i 1)))]

/-- `Ev(F, X)`: read the header `(k, n, m, q)` of `F`, start from the `n` labels of `X`, evaluate
the gates in order, and return the labels of the last `m` wires. -/
@[expose] def evalWord (F X : List Bool) : List Bool :=
  let ((k, n, m, q), body) := fnDecoder.decode F
  let labels := (List.range q).foldl (evalGate family k (wireWidth n q) body)
    (BitString.listRows n (k + 2) X)
  (labels.drop (n + q - m)).flatten

/-- `De(d, Y)`: when `Y` splits into `|d|` labels of equal width, output the colour bit of each
plus its decoding bit; otherwise fail. -/
@[expose] def decodeWord (d Y : List Bool) : Option (List Bool) :=
  if Y.length % d.length = 0 then
    some ((List.range d.length).map fun o =>
      Y.getD ((o + 1) * (Y.length / d.length) - 1) false ^^ d.getD o false)
  else none

/-- **Point-and-permute garbling** as a garbling scheme over valid conventional circuits, with
masks keyed by `family`. -/
@[expose] def scheme : Scheme ValidCircuit where
  inLen f := f.1.n
  outLen f := f.1.m
  size f := f.1.q
  ev f x := f.1.evalCirc x
  coinLen k n _ q := (n + q) * (2 * (k + 1) + 1)
  gb k f coins := ⟨fnWord family k f.1 coins, encInfoWord k f.1 coins, decInfoWord f.1 coins⟩
  encode := encodeWord
  evalGarbled := evalWord family
  decode := decodeWord

/-- Its length readers are `(n, m, q)` and its semantics is `ConventionalCircuit.evalCirc`. -/
theorem scheme_isCircuitScheme : (scheme family).IsCircuitScheme :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-! ### The typed garbling -/

/-- The word of a label: the bits of its key, then its colour. It is the reply of `labelCodec k`,
through which a label oracle answers on words; that reply does not depend on the tweak, so
`labelBits label = (labelCodec k).encodeReply t label` by `rfl` for every tweak `t`. -/
@[expose] def labelBits {k : ℕ} (label : BitString (k + 1) × Bool) : List Bool :=
  (labelCodec k).encodeReply 0 label

/-- A label word is the bits of its key followed by its colour. -/
theorem labelBits_apply {k : ℕ} (label : BitString (k + 1) × Bool) :
    labelBits label = List.ofFn label.1 ++ [label.2] :=
  rfl

/-- A label word has `k + 2` bits. -/
@[simp] theorem length_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).length = k + 2 := by
  simp [labelBits_apply]

/-- The word of a sum of labels is the XOR of their words. -/
theorem labelBits_add {k : ℕ} (x y : BitString (k + 1) × Bool) :
    labelBits (x + y) = List.zipWith xor (labelBits x) (labelBits y) := by
  simp only [labelBits_apply, Prod.fst_add, Prod.snd_add, BitString.ofFn_add]
  rw [List.zipWith_append (by simp)]
  simp [Bool.add_eq_xor]

/-- On a `(k + 1)`-bit key and a `k`-bit tweak, `labelWord` is the label of
`PRF.label (PRF.atLevel family (k + 1))`. -/
theorem labelWord_ofFn (k : ℕ) (key : BitString (k + 1)) (t : BitString k) :
    labelWord family k (List.ofFn key) (List.ofFn t) =
      labelBits (PRF.label (PRF.atLevel family (k + 1)) key t) := by
  simp [labelWord, labelBits_apply, PRF.label, PRF.atLevel, List.ofFn_succ, BitString.ofList,
    ← BitString.ofFn_ofList_eq_take]

variable {n m s : ℕ}

/-- The row of gate `g` whose colours are the binary digits of `i`, the first argument most
significant. -/
@[expose] def rowOf (τ : Circuit.Topology n m s) (g : Fin s) (i : ℕ) : Row τ :=
  ⟨g, fun a => i.testBit (τ.arity g - 1 - a)⟩

/-- The number of a row: its colours read in binary, the first argument most significant. -/
@[expose] def rowIndex {r : ℕ} (colours : Fin r → Bool) : ℕ :=
  BitString.binaryValue (List.ofFn colours)

/-- The tweak of an argument slot at parameter `k`: slot `a` of row `ρ` of gate `g` gets
`tweak k g (rowIndex ρ) a`. -/
@[expose] def slotTweak (τ : Circuit.Topology n m s) (k : ℕ) : Slot τ → BitString k
  | ⟨⟨g, colours⟩, a⟩ => BitString.ofList k (tweak k g (rowIndex colours) a)

/-- The keys read from the coins: the key of colour `c` of wire `w`. -/
@[expose] def keyFn (k : ℕ) (coins : List Bool) : Wire n s × Bool → BitString (k + 1)
  | (w, c) => BitString.ofList (k + 1) (keyOf k (n + s) coins w.toNat c)

/-- The permutation bits read from the coins. -/
@[expose] def permFn (coins : List Bool) (w : Wire n s) : Bool := permOf coins w.toNat

/-- The body of a garbled function over the topology `τ`: for each gate the numbers of its
argument wires, from `1`, as `w`-bit numbers, and its rows in the order of `rowOf`. -/
@[expose] def encodeBody (k : ℕ) (τ : Circuit.Topology n m s)
    (table : Row τ → BitString (k + 1) × Bool) : List Bool :=
  (List.ofFn fun g : Fin s =>
    (List.ofFn fun a => BitString.lowBits (wireWidth n s) ((τ.wires g a).toNat + 1)).flatten ++
      (List.ofFn fun i : Fin (2 ^ τ.arity g) => labelBits (table (rowOf τ g i))).flatten).flatten

/-- The garbled function of a table over the topology `τ` at parameter `k`: the header
`(k, n, m, s)`, then for each gate the numbers of its argument wires, from `1`, as `w`-bit numbers,
and its rows in the order of `rowOf`. -/
@[expose] def encodeFn (k : ℕ) (τ : Circuit.Topology n m s)
    (table : Row τ → BitString (k + 1) × Bool) : List Bool :=
  encFn ((k, n, m, s), encodeBody k τ table)

open ConventionalCircuit in
/-- The words `(F, e, d)` of a typed garbling of `toCircuit f` at parameter `k`. -/
@[expose] noncomputable def encodeGarbled (k : ℕ) (f : ValidCircuit)
    (G : Garbled (toCircuit f).topology (BitString (k + 1))) : Scheme.Garbled where
  fn := encodeFn k (toCircuit f).topology G.table
  encInfo := (List.ofFn fun j : Fin (2 * f.1.n) =>
    labelBits (G.encoding ⟨j / 2, by omega⟩ (j.val.testBit 0))).flatten
  decInfo := List.ofFn G.decoding

/-! ### The garbler computes the typed garbling -/

/-- The bits of a key read from the coins are `keyOf`. -/
theorem ofFn_keyFn (k : ℕ) (coins : List Bool) (w : Wire n s) (c : Bool) :
    List.ofFn (keyFn k coins (w, c)) = keyOf k (n + s) coins w.toNat c :=
  BitString.ofFn_ofList (by simp [keyOf])

/-- The word of a label read from the coins is `labelOf`. -/
theorem labelBits_keyFn (k : ℕ) (coins : List Bool) (w : Wire n s) (c : Bool) :
    labelBits (keyFn k coins (w, c), c) = labelOf k (n + s) coins w.toNat c := by
  rw [labelBits_apply, ofFn_keyFn, labelOf]

/-- A tweak word has `k` bits. -/
@[simp] theorem ofFn_ofList_tweak (k g i a : ℕ) :
    List.ofFn (BitString.ofList k (tweak k g i a)) = tweak k g i a :=
  BitString.ofFn_ofList (by simp [tweak])

/-- The colours of row `i < 4` of a binary gate read back as `i`. -/
private theorem rowIndex_testBit {i : ℕ} (hi : i < 4) :
    rowIndex (fun a : Fin 2 => i.testBit (2 - 1 - a)) = i := by
  interval_cases i <;> rfl

open ConventionalCircuit in
/-- Row `i` of gate `g` of the typed garbling, as a word, is `rowWord`. -/
private theorem labelBits_garbleTable (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits (garbleTable (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
        (rowOf _ g i)) =
      rowWord family k f.1 coins (g.cast (size_toCircuit f)) i := by
  simp only [garbleTable, plainRow, rowMask]
  rw [← Fin.sum_ofFn]
  simp only [rowOf, Circuit.topology, slotTweak]
  rw [lines_toCircuit f g]
  simp only [fullSignature, fullInterpretation, List.ofFn_succ, List.ofFn_zero, List.sum_cons,
    List.sum_nil, add_zero, labelBits_add, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Fin.succ_zero_eq_one]
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  simp only [← labelWord_ofFn, ofFn_keyFn, labelBits_keyFn, ofFn_ofList_tweak, Wire.toNat_gate,
    Wire.toNat_ofNat, permFn, rowIndex_testBit hi, hq, Bool.add_eq_xor, rowWord, Fin.val_cast]

open ConventionalCircuit in
/-- Gate `g` of the typed garbled function, as a word: its argument wires and its four rows. -/
private theorem gateWord_garbleTable (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) :
    ((List.ofFn fun a => BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
        (((toCircuit f).topology.wires g a).toNat + 1)).flatten ++
      (List.ofFn fun i : Fin (2 ^ (toCircuit f).topology.arity g) =>
        labelBits (garbleTable (toCircuit f) fullInterpretation
          (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
          (rowOf _ g i))).flatten) =
      BitString.lowBits (wireWidth f.1.n f.1.q) (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (wireWidth f.1.n f.1.q) (f.1.B (g.cast (size_toCircuit f))) ++
        (List.ofFn fun i : Fin 4 =>
          rowWord family k f.1 coins (g.cast (size_toCircuit f)) i).flatten := by
  have hrow (i : Fin (2 ^ (toCircuit f).topology.arity g)) := labelBits_garbleTable family k f coins
    g (i := i) (by simpa only [arity_topology_toCircuit f g, Nat.reducePow] using i.isLt)
  simp only [hrow]
  have hA := f.2.one_le_A (g.cast (size_toCircuit f))
  have hB := f.2.A_lt_B (g.cast (size_toCircuit f))
  simp only [topo] at hA hB
  simp only [Circuit.topology, size_toCircuit]
  rw [lines_toCircuit f g]
  simp only [fullSignature, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    Wire.toNat_ofNat, Nat.sub_add_cancel hA, Nat.sub_add_cancel (hA.trans hB.le), List.append_assoc]

open ConventionalCircuit in
/-- **The garbler computes the typed garbling.** At parameter `k`, `Gb` on any coins writes the
words of the typed point-and-permute garbling `garbleWith` of `toCircuit f`, with the keyed
function `PRF.label (PRF.atLevel family (k + 1))`, the tweaks `slotTweak` and the keys and
permutation bits read from the coins. -/
theorem gb_eq_encodeGarbled (k : ℕ) (f : ValidCircuit) (coins : List Bool) :
    (scheme family).gb k f coins = encodeGarbled k f
      (garbleWith (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (keyFn k coins) (permFn coins)) := by
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  simp only [scheme, encodeGarbled, garbleWith, Scheme.Garbled.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [fnWord, encodeFn, encodeBody, gateWord_garbleTable]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [encInfoWord, inputEncoding, labelBits_keyFn, Wire.toNat_input, hq, permFn,
      Bool.add_eq_xor]
  · simp only [decInfoWord]
    congr 1
    funext o
    simp only [outputDecoding, permFn, toNat_outputs_toCircuit]

/-! ### Encoding, evaluation and decoding on words -/

/-- A list of `c` words of width `L`, flattened, has `c * L` bits. -/
private theorem length_flatten_ofFn {c L : ℕ} (word : Fin c → List Bool)
    (hword : ∀ j, (word j).length = L) : (List.ofFn word).flatten.length = c * L := by
  simp [List.length_flatten, List.sum_ofFn, hword]

/-- The colour of a label word is its last bit. -/
theorem getD_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).getD (k + 1) false = label.2 := by
  simp [labelBits_apply, List.getD_eq_getElem?_getD]

/-- The key of a label word is its first `k + 1` bits. -/
@[simp] theorem take_labelBits {k : ℕ} (label : BitString (k + 1) × Bool) :
    (labelBits label).take (k + 1) = List.ofFn label.1 := by
  simp [labelBits_apply]

/-- `En` on the words of a typed input encoding writes the label of each bit. -/
theorem encodeWord_encInfo {k : ℕ} (e : Fin n → Bool → BitString (k + 1) × Bool)
    {x : List Bool} (hx : x.length = n) :
    encodeWord (List.ofFn fun j : Fin (2 * n) =>
        labelBits (e ⟨j / 2, by omega⟩ (j.val.testBit 0))).flatten x =
      (List.ofFn fun i => labelBits (e i (BitString.ofList n x i))).flatten := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [List.length_eq_zero_iff.mp hx]
    simp [encodeWord]
  subst hx
  have hL : (List.ofFn fun j : Fin (2 * x.length) =>
      labelBits (e ⟨j / 2, by omega⟩ (j.val.testBit 0))).flatten.length / (2 * x.length) =
        k + 2 := by
    rw [length_flatten_ofFn _ fun _ => length_labelBits _]
    exact Nat.mul_div_cancel_left _ (by omega)
  simp only [encodeWord, hL]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₁, Option.getD_some, BitString.ofList]
  cases hxi : x[i]
  · rw [ite_eq_right (by simp), show 2 * i = (⟨2 * i, by omega⟩ : Fin (2 * x.length)).val from rfl,
      BitString.listRow_flatten_ofFn _ fun _ => length_labelBits _]
    simp [Nat.mul_div_cancel_left i (show 0 < 2 by omega)]
  · rw [ite_eq_left rfl, show 2 * i + 1 = (⟨2 * i + 1, by omega⟩ : Fin (2 * x.length)).val from rfl,
      BitString.listRow_flatten_ofFn _ fun _ => length_labelBits _]
    simp only [Nat.testBit_zero]
    congr 2
    · ext; simp only; omega
    · simp

/-- `De` on the decoding bits and output labels of a typed garbling decodes them. -/
theorem decodeWord_ofFn {k : ℕ} (d : Fin m → Bool) (Y : Fin m → BitString (k + 1) × Bool) :
    decodeWord (List.ofFn d) (List.ofFn fun o => labelBits (Y o)).flatten =
      some (List.ofFn (decode d Y)) := by
  have hlen := length_flatten_ofFn (fun o => labelBits (Y o)) fun _ => length_labelBits _
  rw [decodeWord, ite_eq_left (by simp [hlen])]
  congr 1
  apply List.ext_getElem (by simp)
  intro o h₁ h₂
  simp only [List.length_map, List.length_range, List.length_ofFn] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, decode, hlen,
    List.length_ofFn, Nat.mul_div_cancel_left _ (show 0 < m by omega), List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, h₁]
  have hrow := BitString.listRow_flatten_ofFn (fun o => labelBits (Y o))
    (fun _ => length_labelBits _) ⟨o, h₁⟩
  have hbit := BitString.getD_listRow (width := k + 2) (row := o)
    (word := (List.ofFn fun o => labelBits (Y o)).flatten) (i := k + 1) (by omega)
  rw [hrow, getD_labelBits] at hbit
  rw [show (o + 1) * (k + 2) - 1 = o * (k + 2) + (k + 1) by rw [Nat.add_mul]; omega,
    ← List.getD_eq_getElem?_getD, ← hbit]
  simp [Bool.add_eq_xor]

/-! ### Evaluation -/

/-- A sum over the two arguments of a binary gate. -/
private theorem sum_fin_of_eq_two {M : Type*} [AddCommMonoid M] {r : ℕ} (hr : r = 2)
    (h : Fin r → M) : ∑ a, h a = h ⟨0, by omega⟩ + h ⟨1, by omega⟩ := by
  subst hr
  exact Fin.sum_univ_two h

/-- The number of a row of a binary gate. -/
private theorem rowIndex_of_eq_two {r : ℕ} (hr : r = 2) (colours : Fin r → Bool) :
    rowIndex colours =
      (if colours ⟨0, by omega⟩ then 2 else 0) + (if colours ⟨1, by omega⟩ then 1 else 0) := by
  subst hr
  have h (b₀ b₁ : Bool) :
      2 * (2 * 0 + b₀.toNat) + b₁.toNat = (if b₀ then 2 else 0) + (if b₁ then 1 else 0) := by
    cases b₀ <;> cases b₁ <;> rfl
  simp only [rowIndex, BitString.binaryValue, List.ofFn_succ, List.ofFn_zero, List.foldl_cons,
    List.foldl_nil]
  exact h _ _

/-- The row of a binary gate named by the number of its colours is the row of those colours. -/
private theorem testBit_rowIndex_of_eq_two {r : ℕ} (hr : r = 2) (colours : Fin r → Bool) :
    (fun a : Fin r => (rowIndex colours).testBit (r - 1 - a)) = colours := by
  subst hr
  have h₁ (b₀ b₁ : Bool) : ((if b₀ then 2 else 0) + (if b₁ then 1 else 0)).testBit 1 = b₀ := by
    cases b₀ <;> cases b₁ <;> rfl
  have h₀ (b₀ b₁ : Bool) : ((if b₀ then 2 else 0) + (if b₁ then 1 else 0)).testBit 0 = b₁ := by
    cases b₀ <;> cases b₁ <;> rfl
  funext a
  rw [rowIndex_of_eq_two rfl]
  match a with
  | ⟨0, _⟩ => exact h₁ _ _
  | ⟨1, _⟩ => exact h₀ _ _

open ConventionalCircuit in
private theorem toNat_wires_toCircuit (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (a : Fin ((toCircuit f).topology.arity g)) :
    ((toCircuit f).topology.wires g a).toNat =
      [f.1.A (g.cast (size_toCircuit f)) - 1, f.1.B (g.cast (size_toCircuit f)) - 1].getD a 0 := by
  have h := congrArg (fun l => l.getD a.val 0) (ofFn_toNat_wires_toCircuit f g)
  simpa [List.getD_eq_getElem?_getD] using h

/-- The parts of a gate word: its two wire numbers and its rows. -/
private theorem gate_parts {w : ℕ} {a b rows : List Bool} (ha : a.length = w)
    (hb : b.length = w) :
    ((a ++ b) ++ rows).take w = a ∧ (((a ++ b) ++ rows).drop w).take w = b ∧
      ((a ++ b) ++ rows).drop (2 * w) = rows := by
  subst ha
  refine ⟨by simp, by simp [hb], ?_⟩
  rw [two_mul, ← List.drop_drop, List.append_assoc, List.drop_left, ← hb, List.drop_left]

/-- An entry of a prefix of the labels of a labelling. -/
private theorem getD_take_labels {k : ℕ} (A : Wire n s → BitString (k + 1) × Bool) {j i : ℕ}
    (hij : i < j) (hj : j ≤ n + s) :
    ((List.ofFn fun v : Fin (n + s) => labelBits (A (Wire.ofNat v v.isLt))).take j).getD i [] =
      labelBits (A (Wire.ofNat i (by omega))) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hij, List.getElem?_ofFn]
  simp [show i < n + s by omega]

open ConventionalCircuit in
/-- One gate of `Ev` on the labels of the earlier wires of a fixed point of an evaluation round
appends the label of the gate. -/
private theorem evalGate_take (k : ℕ) (f : ValidCircuit)
    (table : Row (toCircuit f).topology → BitString (k + 1) × Bool)
    (X : Fin f.1.n → BitString (k + 1) × Bool)
    (A : Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, Garbling.evalStep (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
      (slotTweak _ k) table X A w = A w)
    (g : Fin (toCircuit f).size) :
    evalGate family k (wireWidth f.1.n (toCircuit f).size)
        (encodeBody k (toCircuit f).topology table)
        ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g)) g =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g + 1) := by
  have harity := arity_topology_toCircuit f g
  have hA₁ := f.2.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.2.A_lt_B (g.cast (size_toCircuit f))
  have hBg := f.2.B_lt_gate (g.cast (size_toCircuit f))
  simp only [topo, Fin.val_cast] at hA₁ hAB hBg
  have hblock (g₀ : Fin (toCircuit f).size) :
      ((List.ofFn fun a => BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
          (((toCircuit f).topology.wires g₀ a).toNat + 1)).flatten ++
        (List.ofFn fun i : Fin (2 ^ (toCircuit f).topology.arity g₀) =>
          labelBits (table (rowOf _ g₀ i))).flatten).length =
        2 * wireWidth f.1.n (toCircuit f).size + 4 * (k + 2) := by
    rw [List.length_append, length_flatten_ofFn _ fun _ => BitString.length_lowBits _ _,
      length_flatten_ofFn _ fun _ => length_labelBits _, arity_topology_toCircuit f g₀]
    norm_num
  have hgate := BitString.listRow_flatten_ofFn _ hblock g
  have hwires : (List.ofFn fun a => BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
      (((toCircuit f).topology.wires g a).toNat + 1)).flatten =
      BitString.lowBits (wireWidth f.1.n (toCircuit f).size) (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
          (f.1.B (g.cast (size_toCircuit f))) := by
    rw [show (List.ofFn fun a => BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
        (((toCircuit f).topology.wires g a).toNat + 1)) =
      (List.ofFn fun a => ((toCircuit f).topology.wires g a).toNat).map
        (fun v => BitString.lowBits (wireWidth f.1.n (toCircuit f).size) (v + 1)) by
        rw [List.map_ofFn]; rfl, ofFn_toNat_wires_toCircuit]
    simp [Nat.sub_add_cancel hA₁, Nat.sub_add_cancel (hA₁.trans hAB.le)]
  rw [hwires] at hgate
  rw [evalGate, encodeBody, hgate]
  obtain ⟨hp₁, hp₂, hp₃⟩ := gate_parts
    (rows := (List.ofFn fun i : Fin (2 ^ (toCircuit f).topology.arity g) =>
      labelBits (table (rowOf _ g i))).flatten)
    (BitString.length_lowBits _ (f.1.A (g.cast (size_toCircuit f))))
    (BitString.length_lowBits _ (f.1.B (g.cast (size_toCircuit f))))
  have hsize : (f.1.n + (toCircuit f).size) < 2 ^ wireWidth f.1.n (toCircuit f).size :=
    Nat.lt_size_self _
  have hgs := g.isLt
  have hval (a : ℕ) (ha : a ≤ f.1.n + g) (hw : a < 2 ^ wireWidth f.1.n (toCircuit f).size) :
      BitString.boundedBinaryValue
        ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g)).length
        (BitString.lowBits (wireWidth f.1.n (toCircuit f).size) a).reverse = a := by
    rw [BitString.boundedBinaryValue_eq, ← ofBits_reverse, List.reverse_reverse,
      ofBits_lowBits hw, List.length_take, List.length_ofFn]
    omega
  rw [hp₁, hp₂, hp₃, hval _ (by omega) (by omega), hval _ (by omega) (by omega),
    getD_take_labels A (by omega) (by omega), getD_take_labels A (by omega) (by omega)]
  simp only [getD_labelBits, take_labelBits]
  have hwa : (toCircuit f).topology.wires g ⟨0, by omega⟩ =
      Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) (by omega) :=
    Wire.toNat_injective (by rw [toNat_wires_toCircuit, Wire.toNat_ofNat]; rfl)
  have hwb : (toCircuit f).topology.wires g ⟨1, by omega⟩ =
      Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by omega) :=
    Wire.toNat_injective (by rw [toNat_wires_toCircuit, Wire.toNat_ofNat]; rfl)
  have hindex : rowIndex (fun a => (A ((toCircuit f).topology.wires g a)).2) =
      (if (A (Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) (by omega))).2 then 2 else 0) +
        (if (A (Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1)
            (by omega))).2 then 1 else 0) := by
    rw [rowIndex_of_eq_two harity, hwa, hwb]
  have hrowOf : rowOf (toCircuit f).topology g
      (rowIndex (fun a => (A ((toCircuit f).topology.wires g a)).2)) =
        ⟨g, fun a => (A ((toCircuit f).topology.wires g a)).2⟩ :=
    Sigma.ext rfl (heq_of_eq (testBit_rowIndex_of_eq_two harity _))
  have hgateA := hA (.gate g)
  simp only [Garbling.evalStep] at hgateA
  rw [sum_fin_of_eq_two harity, show ∀ x y : BitString (k + 1) × Bool, x - y = x + y from
    fun x y => Prod.ext (BitString.sub_eq_add _ _) (BooleanRing.sub_eq_add _ _)] at hgateA
  simp only [slotTweak, hwa, hwb, hindex] at hgateA
  have hi : (if (A (Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1)
      (by omega))).2 then 2 else 0) +
      (if (A (Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by omega))).2 then 1 else 0) <
        2 ^ (toCircuit f).topology.arity g := by
    rw [harity]
    cases (A (Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) (by omega))).2 <;>
      cases (A (Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by omega))).2 <;> simp
  rw [show (if (A (Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1)
      (by omega))).2 then 2 else 0) +
      (if (A (Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by omega))).2 then 1 else 0) =
        (⟨_, hi⟩ : Fin (2 ^ (toCircuit f).topology.arity g)).val from rfl,
    BitString.listRow_flatten_ofFn _ fun _ => length_labelBits _]
  simp only
  rw [← hindex, hrowOf, ← ofFn_ofList_tweak k g _ 0, ← ofFn_ofList_tweak k g _ 1,
    labelWord_ofFn, labelWord_ofFn, ← labelBits_add, ← labelBits_add, hindex, hgateA,
    List.take_add_one, List.getElem?_ofFn]
  have hgate : (Wire.ofNat (f.1.n + g) (by omega) : Wire f.1.n (toCircuit f).size) = .gate g :=
    Wire.toNat_injective (by simp)
  simp [show f.1.n + g < f.1.n + (toCircuit f).size by omega, hgate]

open ConventionalCircuit in
/-- **`Ev` follows a fixed point of an evaluation round.** If the labelling `A` of the wires of
`toCircuit f` is left unchanged by one round of the typed evaluation of `table` on the input
labels `X`, then `Ev` on the garbled function of `table` and the words of `X` returns the labels
`A` of the output wires. -/
theorem evalWord_encodeFn (k : ℕ) (f : ValidCircuit)
    (table : Row (toCircuit f).topology → BitString (k + 1) × Bool)
    (X : Fin f.1.n → BitString (k + 1) × Bool)
    (A : Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, Garbling.evalStep (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
      (slotTweak _ k) table X A w = A w) :
    evalWord family (encodeFn k (toCircuit f).topology table)
        (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun o => labelBits (A ((toCircuit f).outputs o))).flatten := by
  have hinit : BitString.listRows f.1.n (k + 2) (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (A (Wire.ofNat v v.isLt))).take f.1.n := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [BitString.length_listRows] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.1.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [BitString.listRows, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_ofFn, hin, ← hA (.input ⟨i, h₁⟩), Garbling.evalStep]
    exact BitString.listRow_flatten_ofFn (fun i => labelBits (X i)) (fun _ => length_labelBits _)
      ⟨i, h₁⟩
  have hfold : ∀ g ≤ (toCircuit f).size,
      (List.range g).foldl (evalGate family k (wireWidth f.1.n (toCircuit f).size)
          (encodeBody k (toCircuit f).topology table))
        (BitString.listRows f.1.n (k + 2) (List.ofFn fun i => labelBits (X i)).flatten) =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g) := by
    intro g hg
    induction g with
    | zero => exact hinit
    | succ g ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      exact evalGate_take family k f table X A hA ⟨g, by omega⟩
  simp only [evalWord, encodeFn, fnDecoder.decode_enc]
  rw [hfold _ le_rfl, List.take_of_length_le (by simp)]
  congr 1
  apply List.ext_getElem (by
    have := f.2.m_le_q
    have := size_toCircuit f
    simp only [topo] at *
    simp
    omega)
  intro o h₁ h₂
  simp only [List.length_ofFn] at h₂
  have hout : (Wire.ofNat (f.1.n + (toCircuit f).size - f.1.m + o) (by
      have := f.2.m_le_q; simp only [topo] at this; rw [size_toCircuit]; omega) :
        Wire f.1.n (toCircuit f).size) = (toCircuit f).outputs ⟨o, h₂⟩ :=
    Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit, size_toCircuit])
  simp only [List.getElem_drop, List.getElem_ofFn, hout]

/-! ### Validity -/

open ConventionalCircuit in
/-- **Correctness**: decoding the evaluation of an encoded input gives the circuit's output, for
every family. -/
private theorem scheme_correct : (scheme family).Correct := by
  intro k _ f x hx g hg
  obtain ⟨coins, -, rfl⟩ := (scheme family).mem_support_eval_garble_iff.mp hg
  have hev := evaluate_eq_of_evalStep (toCircuit f).isOrdered_topology
    (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
    (garbleTable (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
      (slotTweak _ k) (keyFn k coins) (permFn coins))
    (encode (inputEncoding (keyFn k coins) (permFn coins)) (BitString.ofList f.1.n x))
    _ (evalStep_activeLabel (toCircuit f) fullInterpretation
      (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
      (BitString.ofList f.1.n x))
  have hrun := Garbled.run_garbleWith (toCircuit f) fullInterpretation
    (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
    (BitString.ofList f.1.n x)
  simp only [Garbled.run, garbleWith, hev] at hrun
  rw [gb_eq_encodeGarbled]
  simp only [scheme, encodeGarbled, garbleWith]
  rw [encodeWord_encInfo (n := f.1.n) _ hx, evalWord_encodeFn family k f _
    (fun i => inputEncoding (keyFn k coins) (permFn coins) i (BitString.ofList f.1.n x i)) _
    (evalStep_activeLabel (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
      (slotTweak _ k) (keyFn k coins) (permFn coins) (BitString.ofList f.1.n x)), decodeWord_ofFn]
  have h := congrArg List.ofFn hrun
  rw [eval_toCircuit, BitString.ofFn_ofList (n := f.1.n) hx] at h
  exact congrArg some h

/-- A label read from the coins has `k + 2` bits. -/
@[simp] theorem length_labelOf (k wires : ℕ) (coins : List Bool) (v : ℕ) (c : Bool) :
    (labelOf k wires coins v c).length = k + 2 := by
  simp [labelOf, keyOf]

/-- A label of the keyed function has `k + 2` bits. -/
@[simp] theorem length_labelWord (k : ℕ) (key t : List Bool) :
    (labelWord family k key t).length = k + 2 := by
  simp [labelWord]

/-- A row has `k + 2` bits. -/
@[simp] theorem length_rowWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool)
    (g : Fin f.q) (i : ℕ) : (rowWord family k f coins g i).length = k + 2 := by
  simp [rowWord]

/-- The garbled function has a length fixed by `k` and the shape `(n, m, q)`. -/
theorem length_fnWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    (fnWord family k f coins).length =
      2 * (encHeader (k, f.n, f.m, f.q)).length + 1 +
        f.q * (2 * wireWidth f.n f.q + 4 * (k + 2)) := by
  rw [fnWord, length_encPair]
  congr 1
  rw [encBits_apply, length_flatten_ofFn _ fun g => by
    rw [List.length_append, List.length_append, BitString.length_lowBits,
      BitString.length_lowBits, length_flatten_ofFn _ fun _ => length_rowWord family _ _ _ _ _]]
  ring

/-- The encoding information has `2 n` labels. -/
theorem length_encInfoWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    (encInfoWord k f coins).length = 2 * f.n * (k + 2) :=
  length_flatten_ofFn _ fun _ => length_labelOf _ _ _ _ _

/-- The length condition: the lengths of `F`, `e` and `d` depend only on `k` and the shape. -/
private theorem scheme_lengthCondition : (scheme family).LengthCondition := by
  rintro k - f f' ⟨hn, hm, hq⟩ g hg g' hg'
  obtain ⟨coins, -, rfl⟩ := (scheme family).mem_support_eval_garble_iff.mp hg
  obtain ⟨coins', -, rfl⟩ := (scheme family).mem_support_eval_garble_iff.mp hg'
  simp only [scheme] at hn hm hq ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [length_fnWord, length_fnWord, hn, hm, hq]
  · rw [length_encInfoWord, length_encInfoWord, hn]
  · simp [decInfoWord, hm]

/-- Non-degeneracy: the encoding and decoding information depend only on the coins and the
shape. -/
private theorem scheme_nonDegenerate : (scheme family).NonDegenerate := by
  rintro k - ⟨⟨n, m, q, A, B, G⟩, hf⟩ ⟨⟨n', m', q', A', B', G'⟩, hf'⟩ ⟨hn, hm, hq⟩ coins -
  simp only [scheme] at hn hm hq ⊢
  subst hn hm hq
  exact ⟨rfl, rfl⟩

/-- **Point-and-permute garbling is a valid garbling scheme**: the length condition,
non-degeneracy and correctness of `Scheme.IsValid`, for every family. -/
theorem scheme_isValid : (scheme family).IsValid :=
  ⟨scheme_lengthCondition family, scheme_nonDegenerate family, scheme_correct family⟩

end Cslib.Crypto.Garbling.PointPermute
