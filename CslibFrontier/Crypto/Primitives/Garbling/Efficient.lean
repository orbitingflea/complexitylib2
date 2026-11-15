/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.CircuitInverters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Primitives.Garbling.Games
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Efficient garbling schemes

The algorithms of a garbling scheme in the sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012] are meant to be efficient. `Scheme.IsEfficient G encFn` states this for
a scheme `G` whose function descriptions are encoded by `encFn`: the length readers `f.n` and
`f.m`, the number of coins, the deterministic core `gb` of the garbling algorithm, encoding,
evaluation, decoding and the semantics `ev` are computed in polynomial time, on the security
parameter in unary and the encoded arguments.

For circuit garbling, `encConventionalCircuit` encodes a conventional circuit by `n` and `m` in
unary followed by its gates, each the binary numbers of its two argument wires and its truth table
as four bits; `encValidCircuit` restricts it to valid circuits. `encValidTopo` encodes the
topology `(n, m, q, A, B)` revealed by `phiTopo` in the same layout without the truth tables, and
`encPrvView` encodes the view `(F, X, d)` of a privacy adversary.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.encGarbled`: the encoding of a garbled triple `(F, e, d)`.
* `Cslib.Crypto.Garbling.Scheme.IsEfficient`: polynomial-time algorithms.
* `Cslib.Crypto.Garbling.ConventionalCircuit.gateList`,
  `Cslib.Crypto.Garbling.encConventionalCircuit`, `Cslib.Crypto.Garbling.encValidCircuit`:
  conventional circuits as data.
* `Cslib.Crypto.Garbling.Topo.gateList`, `Cslib.Crypto.Garbling.encTopo`,
  `Cslib.Crypto.Garbling.encValidTopo`: topologies, the side information of `phiTopo`, as data.
* `Cslib.Crypto.Garbling.encPrvView`, `Cslib.Crypto.Garbling.encQuery`: the encodings of a
  privacy view `(F, X, d)` and of a query `(f, x)`.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM

namespace Scheme

/-- The encoding of a garbled triple `(F, e, d)`: `F` and `e` framed, then `d`
(`encGarbled_apply`). -/
enc_structure encGarbled : Garbled where
  fn : encBits, encInfo : encBits, decInfo : encBits

variable {Fn : Type}

/-- A garbling scheme is **efficient** for the encoding `encFn` of its function descriptions when
its algorithms run in polynomial time: the length readers `f.n` and `f.m` on the encoded function,
the number of coins and the deterministic core `gb` of `Gb` on the parameter in unary and the
encoded function (and coins), and `En`, `Ev`, `De` and `ev` on their encoded arguments.
[BellareHoangRogaway2012], §3.1, fixes linear-time algorithms for `f.n` and `f.m`; here they are
only required to run in polynomial time. -/
structure IsEfficient (G : Scheme Fn) (encFn : Fn ↪ List Bool) : Prop where
  /-- The input length `f.n` is read from `f` in polynomial time, in unary. -/
  inLen : ComputableInPolyTime G.inLen encFn encUnary
  /-- The output length `f.m` is read from `f` in polynomial time, in unary. -/
  outLen : ComputableInPolyTime G.outLen encFn encUnary
  /-- The number of coins is polynomial-time computable in unary. -/
  coins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary
  /-- The deterministic core of garbling is polynomial-time on `(1^k, f, r)`. -/
  gb : ComputableInPolyTime (fun (k, f, coins) => G.gb k f coins)
    (encPair encUnary (encPair encFn encBits)) encGarbled
  /-- Encoding is polynomial-time on `(e, x)`. -/
  encode : ComputableInPolyTime (fun (e, x) => G.encode e x) (encPair encBits encBits) encBits
  /-- Evaluation is polynomial-time on `(F, X)`. -/
  evalGarbled : ComputableInPolyTime (fun (F, X) => G.evalGarbled F X) (encPair encBits encBits)
    encBits
  /-- Decoding is polynomial-time on `(d, Y)`. -/
  decode : ComputableInPolyTime (fun (d, Y) => G.decode d Y) (encPair encBits encBits)
    (encOption encBits)
  /-- The semantics is polynomial-time on `(f, x)`. -/
  ev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits

end Scheme

namespace ConventionalCircuit

/-- The gates of a conventional circuit as data: for each gate its argument wires `A g` and `B g`
and its truth table as the four bits `G g 0 0`, `G g 0 1`, `G g 1 0`, `G g 1 1`. -/
@[expose] def gateList (f : ConventionalCircuit) : List (ℕ × ℕ × List Bool) :=
  List.ofFn fun g => (f.A g, f.B g,
    [f.G g false false, f.G g false true, f.G g true false, f.G g true true])

@[simp] theorem length_gateList (f : ConventionalCircuit) : f.gateList.length = f.q := by
  simp [gateList]

/-- A conventional circuit is determined by `n`, `m` and its gates. -/
theorem gateList_injective {f f' : ConventionalCircuit} (hn : f.n = f'.n) (hm : f.m = f'.m)
    (h : f.gateList = f'.gateList) : f = f' := by
  obtain ⟨n, m, q, A, B, G⟩ := f
  obtain ⟨n', m', q', A', B', G'⟩ := f'
  simp only at hn hm
  subst hn hm
  obtain ⟨rfl, hfun⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp h)
  have hfun := eq_of_heq hfun
  have hA : A = A' := funext fun g => congrArg Prod.fst (congrFun hfun g)
  have hB : B = B' := funext fun g => congrArg (fun p => p.2.1) (congrFun hfun g)
  have hG : G = G' := funext fun g => funext fun x => funext fun y => by
    have ht := congrArg (fun p => p.2.2) (congrFun hfun g)
    simp only [List.cons.injEq, and_true] at ht
    obtain ⟨h₀, h₁, h₂, h₃⟩ := ht
    cases x <;> cases y <;> assumption
  subst hA hB hG
  rfl

end ConventionalCircuit

/-- The data of a conventional circuit: `n` and `m` in unary, then its gates, each the binary
numbers of its two argument wires followed by its truth table as four bits. -/
abbrev encCircuitData : (ℕ × ℕ × List (ℕ × ℕ × List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair encNat (encPair encNat encBits))))

/-- **Conventional circuits as words**: `n` and `m` in unary, then the gates in order, each the
binary numbers of its argument wires `A g` and `B g` and its truth table as four bits
(`encCircuitData` of `(n, m, gateList f)`). -/
def encConventionalCircuit : ConventionalCircuit ↪ List Bool :=
  ⟨fun f => encCircuitData (f.n, f.m, f.gateList), fun f f' h => by
    obtain ⟨hn, hrest⟩ := Prod.ext_iff.mp (encCircuitData.injective h)
    obtain ⟨hm, hg⟩ := Prod.ext_iff.mp hrest
    exact ConventionalCircuit.gateList_injective hn hm hg⟩

/-- Valid conventional circuits as words, by `encConventionalCircuit`. -/
def encValidCircuit : ValidCircuit ↪ List Bool :=
  (Function.Embedding.subtype _).trans encConventionalCircuit

/-- A valid circuit's word has at least `n + q` bits: `n` in unary and at least one bit per
gate. -/
theorem n_add_q_le_length_encValidCircuit (f : ValidCircuit) :
    f.1.n + f.1.q ≤ (encValidCircuit f).length := by
  change f.1.n + f.1.q ≤ (encCircuitData (f.1.n, f.1.m, f.1.gateList)).length
  have h := length_le_length_encList (encPair encNat (encPair encNat encBits)) f.1.gateList
  simp only [ConventionalCircuit.length_gateList] at h
  simp only [encCircuitData, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The data of a valid circuit is read from its word in polynomial time. -/
theorem circuitData_polyTime :
    ComputableInPolyTime (fun f : ValidCircuit => (f.1.n, f.1.m, f.1.gateList)) encValidCircuit
      encCircuitData :=
  .of_eq fun _ => rfl

namespace Topo

/-- The gates of a topology as data: for each gate its argument wires `A g` and `B g`. -/
@[expose] def gateList (t : Topo) : List (ℕ × ℕ) := List.ofFn fun g => (t.A g, t.B g)

@[simp] theorem length_gateList (t : Topo) : t.gateList.length = t.q := by
  simp [gateList]

/-- A topology is determined by `n`, `m` and its gates. -/
theorem gateList_injective {t t' : Topo} (hn : t.n = t'.n) (hm : t.m = t'.m)
    (h : t.gateList = t'.gateList) : t = t' := by
  obtain ⟨n, m, q, A, B⟩ := t
  obtain ⟨n', m', q', A', B'⟩ := t'
  simp only at hn hm
  subst hn hm
  obtain ⟨rfl, hfun⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp h)
  have hfun := eq_of_heq hfun
  have hA : A = A' := funext fun g => congrArg Prod.fst (congrFun hfun g)
  have hB : B = B' := funext fun g => congrArg Prod.snd (congrFun hfun g)
  subst hA hB
  rfl

end Topo

/-- The data of a topology: `n` and `m` in unary, then each gate's argument wires in binary. -/
abbrev encTopoData : (ℕ × ℕ × List (ℕ × ℕ)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair encNat encNat)))

/-- **Topologies as words**: `n` and `m` in unary, then the gates in order, each the binary numbers
of its argument wires `A g` and `B g` (`encTopoData` of `(n, m, gateList t)`). This is the layout
of `encConventionalCircuit` without the truth tables. -/
def encTopo : Topo ↪ List Bool :=
  ⟨fun t => encTopoData (t.n, t.m, t.gateList), fun t t' h => by
    obtain ⟨hn, hrest⟩ := Prod.ext_iff.mp (encTopoData.injective h)
    obtain ⟨hm, hg⟩ := Prod.ext_iff.mp hrest
    exact Topo.gateList_injective hn hm hg⟩

/-- Valid topologies, the side information of `phiTopo`, as words by `encTopo`. -/
def encValidTopo : ValidTopo ↪ List Bool :=
  (Function.Embedding.subtype _).trans encTopo

/-- The data of a valid topology is read from its word in polynomial time. -/
theorem topoData_polyTime :
    ComputableInPolyTime (fun t : ValidTopo => (t.1.n, t.1.m, t.1.gateList)) encValidTopo
      encTopoData :=
  .of_eq fun _ => rfl

/-- The encoding of a privacy view `(F, X, d)`: `F` and `X` framed, then `d`. -/
enc_structure encPrvView : PrvView where
  fn : encBits, input : encBits, decInfo : encBits

/-- The encoding of a query `(f, x)`: `f` by `encFn`, framed, then `x`. -/
enc_structure encQuery (Fn : Type) (encFn : Fn ↪ List Bool) : Query Fn where
  fn : encFn, input : encBits

end Cslib.Crypto.Garbling
