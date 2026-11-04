/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.WhileAbsorb
public import Complexity.Computability.WordRAM.Realization.Reindex

/-!
# Word-glue metaprogramming helpers for the `realize` tactic

Shared environment, expression analysis, envelope construction, and `GlueComputable` /
`GlueComputableAt` certificate builders used by `Complexity/Tactic/Realize.lean`.

## Main definitions

* `Cslib.Tactic.Realize.Env`, `Cslib.Tactic.Realize.Out`, `Cslib.Tactic.Realize.Ctx`: tactic state
  structures.
* `Cslib.Tactic.Realize.analyze`, `Cslib.Tactic.Realize.annotate`,
  `Cslib.Tactic.Realize.glueProof`: syntax-directed word-glue certificate assembly.
-/

public meta section

namespace Cslib.Tactic.Realize

open Lean Meta Elab Tactic Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- The live words of a realization environment. -/
structure Env where
  /-- The environment type. -/
  ty : Expr
  /-- The number of live words. -/
  k : Nat
  /-- The encoding `ty ↪ (Fin k → ℕ)`. -/
  input : Expr
  /-- `atoms[i]` is `fun d => input d i` in weak-head normal form. -/
  atoms : Array Expr

/-- A certificate built by `realize`. -/
structure Out where
  /-- Scratch register bound `n` (used when `ctx.graded` is true). -/
  n : Nat := 0
  /-- Exchange factor bound `c` (used when `ctx.graded` is true). -/
  c : Nat := 0
  /-- A proof of `Realizes B prog input output safe 0` or
  `RealizesAt n c B prog input output safe 0`. -/
  proof : Expr
  /-- The output encoding. -/
  output : Expr
  /-- The domain `fun w d s => …`, in the client's terms, definitionally equal to the proof's. -/
  safe : Expr

/-- The basis of the goal and whether the goal is graded (`RealizesAt`). -/
structure Ctx where
  /-- The basis. -/
  basis : Expr
  /-- Whether the basis is `.exact`. -/
  exact : Bool
  /-- Whether the basis is `.standard`. -/
  standard : Bool
  /-- Whether the goal is `RealizesAt` (`true`) or `Realizes` (`false`). -/
  graded : Bool := false

/-- `(i : Fin n)` as a numeral. -/
def finLit (n i : Nat) : MetaM Expr :=
  mkNumeral (mkApp (mkConst ``Fin) (mkNatLit n)) i

/-- Prove `a ≤ b` for two natural-number literals using `Nat.le_of_ble_eq_true`. -/
def natLeProof (a b : Nat) : MetaM Expr := do
  unless a ≤ b do
    throwError "realize: graded bound `{a}` exceeds target `{b}`"
  let eqTy ← mkEq (← mkAppM ``Nat.ble #[mkNatLit a, mkNatLit b]) (mkConst ``true)
  let hble ← mkExpectedTypeHint (← mkEqRefl (mkConst ``true)) eqTy
  mkAppOptM ``Nat.le_of_ble_eq_true #[mkNatLit a, mkNatLit b, hble]

/-- The number of words of an encoding `α ↪ (Fin l → ℕ)`. -/
def encodingWidth (enc : Expr) : MetaM Nat := do
  let ty ← instantiateMVars (← inferType enc)
  let some (_, tgt) := ty.app2? ``Function.Embedding
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let n ← instantiateMVars tgt.bindingDomain!.appArg!
  if let some l ← (evalNat n).run then return l
  let some l ← (evalNat (← whnf n)).run
    | throwError "realize: the encoding width is not a numeral in{indentExpr ty}"
  return l

/-- The atoms of `enc x`, for `x` an expression in the environment variable. -/
def encodingAtoms (enc x : Expr) (l : Nat) : MetaM (Array Expr) :=
  (Array.range l).mapM fun j => do
    whnf (mkApp (← mkAppM ``DFunLike.coe #[enc, x]) (← finLit l j))

/-- Locate an expression among the live words: syntactically after `whnf`, as the live words are
themselves in weak-head normal form, and otherwise by definitional equality. -/
def findAtom (atoms : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  if let some i := atoms.findIdx? (· == e') then return some i
  for h : i in [0:atoms.size] do
    if ← withNewMCtxDepth (isDefEq e' atoms[i]) then return some i
  return none

/-- Reduce `(a, b).1` and `(a, b).2` everywhere. -/
def reducePairs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Prod.fst 3 then
      if let some (_, _, a, _) := e.appArg!.app4? ``Prod.mk then return .done a
    if e.isAppOfArity ``Prod.snd 3 then
      if let some (_, _, _, b) := e.appArg!.app4? ``Prod.mk then return .done b
    if let .proj ``Prod i s := e then
      if let some (_, _, a, b) := s.app4? ``Prod.mk then return .done (if i == 0 then a else b)
    return .continue)

/-- `φ₀ ∧ (φ₁ ∧ … φₙ)`, or `True`. -/
def conj : List Expr → Expr
  | [] => mkConst ``True
  | [f] => f
  | f :: fs => mkAnd f (conj fs)

/-- Project the conjunct at `pos` out of a proof of `conj` of `size` facts. -/
def conjunct (h : Expr) (size pos : Nat) : MetaM Expr := do
  let mut h := h
  for _ in [0:pos] do h ← mkAppM ``And.right #[h]
  if pos + 1 == size then return h
  mkAppM ``And.left #[h]

/-! ### Word glue -/

/-- The supported glue operations. -/
inductive GOp
  | add | sub | mul | div | mod | and | or | xor | shiftLeft | shiftRight

/-- The glue rule name for an operation in the exact or standard basis. -/
def GOp.rule (graded exact : Bool) : GOp → Name
  | .add =>
    if graded then (if exact then ``GlueComputableAt.add else ``GlueComputableAt.add_standard)
    else (if exact then ``GlueComputable.add else ``GlueComputable.add_standard)
  | .sub =>
    if graded then (if exact then ``GlueComputableAt.sub else ``GlueComputableAt.sub_standard)
    else (if exact then ``GlueComputable.sub else ``GlueComputable.sub_standard)
  | .mul =>
    if graded then (if exact then ``GlueComputableAt.mul else ``GlueComputableAt.mul_standard)
    else (if exact then ``GlueComputable.mul else ``GlueComputable.mul_standard)
  | .div =>
    if graded then (if exact then ``GlueComputableAt.div else ``GlueComputableAt.div_standard)
    else (if exact then ``GlueComputable.div else ``GlueComputable.div_standard)
  | .mod =>
    if graded then (if exact then ``GlueComputableAt.mod else ``GlueComputableAt.mod_standard)
    else (if exact then ``GlueComputable.mod else ``GlueComputable.mod_standard)
  | .and =>
    if graded then (if exact then ``GlueComputableAt.and else ``GlueComputableAt.and_standard)
    else (if exact then ``GlueComputable.and else ``GlueComputable.and_standard)
  | .or =>
    if graded then (if exact then ``GlueComputableAt.or else ``GlueComputableAt.or_standard)
    else (if exact then ``GlueComputable.or else ``GlueComputable.or_standard)
  | .xor =>
    if graded then (if exact then ``GlueComputableAt.xor else ``GlueComputableAt.xor_standard)
    else (if exact then ``GlueComputable.xor else ``GlueComputable.xor_standard)
  | .shiftLeft =>
    if graded then
      (if exact then ``GlueComputableAt.shiftLeft else ``GlueComputableAt.shiftLeft_standard)
    else
      (if exact then ``GlueComputable.shiftLeft else ``GlueComputable.shiftLeft_standard)
  | .shiftRight =>
    if graded then
      (if exact then ``GlueComputableAt.shiftRight else ``GlueComputableAt.shiftRight_standard)
    else
      (if exact then ``GlueComputable.shiftRight else ``GlueComputable.shiftRight_standard)

/-- The operator's heterogeneous-operation function. -/
def GOp.fn : GOp → Name
  | .add => ``HAdd.hAdd | .sub => ``HSub.hSub | .mul => ``HMul.hMul | .div => ``HDiv.hDiv
  | .mod => ``HMod.hMod | .and => ``HAnd.hAnd | .or => ``HOr.hOr | .xor => ``HXor.hXor
  | .shiftLeft => ``HShiftLeft.hShiftLeft | .shiftRight => ``HShiftRight.hShiftRight

/-- Whether the result is at most the left operand. -/
def GOp.belowLeft : GOp → Bool
  | .sub | .div | .mod | .and | .shiftRight => true
  | _ => false

/-- A glue expression over the live words. -/
inductive GNode
  /-- A live word. -/
  | reg (i : Nat) (user : Expr)
  /-- A value independent of the environment. -/
  | const (c : Expr) (zero : Bool)
  /-- A binary operation. -/
  | bin (op : GOp) (user : Expr) (a b : GNode)

/-- The expression in the client's terms. -/
def GNode.user : GNode → Expr
  | .reg _ u | .const u _ | .bin _ u _ _ => u

/-- Recognize a binary operation on natural numbers. -/
def binOp? (e : Expr) : Option (GOp × Expr × Expr) :=
  [GOp.add, .sub, .mul, .div, .mod, .and, .or, .xor, .shiftLeft, .shiftRight].findSome? fun op =>
    if e.isAppOfArity op.fn 6 && (e.getArg! 0).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5)
    else none

/-- Parse a word-valued expression over the live words. -/
partial def analyze (atoms : Array Expr) (d : Expr) (e : Expr) : MetaM GNode := do
  if let some i ← findAtom atoms e then return .reg i e
  if !e.containsFVar d.fvarId! then
    return .const e (← withNewMCtxDepth (isDefEq e (mkNatLit 0)))
  if let some (op, a, b) := binOp? e then
    return .bin op e (← analyze atoms d a) (← analyze atoms d b)
  let e' ← whnfR e
  if e' != e then return ← analyze atoms d e'
  throwError "realize: cannot compute{indentExpr e}\nfrom the live words{indentD
    (MessageData.joinSep (atoms.toList.map fun a => m!"{a}") ", ")}"

/-- A glue node numbered in depth-first order, with its value over the word vector. -/
inductive ANode
  /-- A live word. -/
  | reg (idx : Nat) (val : Expr) (i : Nat)
  /-- A constant. -/
  | const (idx : Nat) (val : Expr) (zero : Bool)
  /-- A binary operation; `dom` numbers its definedness condition, if any. -/
  | bin (idx : Nat) (val : Expr) (op : GOp) (dom : Option Nat) (a b : ANode)

/-- The value over the word vector. -/
def ANode.val : ANode → Expr
  | .reg _ v _ | .const _ v _ | .bin _ v .. => v

/-- The values of all nodes in depth-first order and the definedness conditions, over the word
vector and in the client's terms. -/
structure Annot where
  /-- Node values over the word vector. -/
  vals : Array Expr := #[]
  /-- Definedness conditions over the word vector. -/
  domV : Array Expr := #[]
  /-- Definedness conditions in the client's terms. -/
  domU : Array Expr := #[]

/-- Number the nodes and compute their values over the word vector `v`. -/
partial def annotate (exact : Bool) (k : Nat) (v : Expr) : GNode → StateT Annot MetaM ANode
  | .reg i _ => do
    let val := mkApp v (← finLit k i)
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push val }
    return .reg idx val i
  | .const c zero => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push c }
    return .const idx c zero
  | .bin op _ a b => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push default }
    let a' ← annotate exact k v a
    let b' ← annotate exact k v b
    let val ← mkAppM op.fn #[a'.val, b'.val]
    modify fun st => { st with vals := st.vals.set! idx val }
    let dom? ← if exact then
        match op with
        | .sub => pure (some (← mkAppM ``LE.le #[b'.val, a'.val],
            ← mkAppM ``LE.le #[b.user, a.user]))
        | .div | .mod => pure (some (← mkAppM ``Ne #[b'.val, mkNatLit 0],
            ← mkAppM ``Ne #[b.user, mkNatLit 0]))
        | _ => pure none
      else pure none
    let dom ← match dom? with
      | some (fv, fu) => do
        let n := (← get).domV.size
        modify fun st => { st with domV := st.domV.push fv, domU := st.domU.push fu }
        pure (some n)
      | none => pure none
    return .bin idx val op dom a' b'

/-- The node's value in the client's terms, by depth-first number. -/
partial def userVals (g : GNode) (acc : Array Expr := #[]) : Array Expr :=
  match g with
  | .reg _ u => acc.push u
  | .const c _ => acc.push c
  | .bin _ u a b => userVals b (userVals a (acc.push u))

/-- The nodes whose fit is a visible condition: `covered` says that a dominating value fits. -/
partial def needNodes (exact : Bool) (n : ANode) (covered : Bool)
    (acc : Array Nat := #[]) : Array Nat :=
  match n with
  | .reg .. => acc
  | .const idx _ zero => if zero || covered then acc else acc.push idx
  | .bin idx _ op _ a b =>
    let acc := if op.belowLeft || covered then acc else acc.push idx
    match op with
    | .add | .or =>
      needNodes exact b true (needNodes exact a true acc)
    | .shiftLeft => needNodes exact b false (needNodes exact a true acc)
    | .sub => needNodes exact b exact (needNodes exact a false acc)
    | _ => needNodes exact b false (needNodes exact a false acc)

/-- Fit proofs of all nodes, indexed by depth-first number, mirroring `needNodes`. `self?` is the
node's fit from a dominating value. -/
partial def fitProofs (exact : Bool) (k : Nat) (w hregs hdom hneed : Expr) (ndom : Nat)
    (needIdx : Array Nat) (n : ANode) (self? : Option Expr) :
    StateT (Array Expr) MetaM Expr := do
  let fitNeed (idx : Nat) : MetaM Expr := do
    let some pos := needIdx.findIdx? (· == idx) | throwError "realize: internal fit error"
    conjunct hneed needIdx.size pos
  let fitLe (p h : Expr) : MetaM Expr := mkAppM ``Cslib.WordRAM.Fits.of_le #[p, h]
  let record (idx : Nat) (p : Expr) : StateT (Array Expr) MetaM Expr := do
    modify fun acc => acc.set! idx p
    return p
  match n with
  | .reg idx _ i => record idx (mkApp hregs (← finLit k i))
  | .const idx _ zero =>
    if zero then
      record idx (← mkAppM ``Cslib.WordRAM.fits_zero #[w])
    else match self? with
      | some p => record idx p
      | none => record idx (← fitNeed idx)
  | .bin idx _ op dom a b =>
    if op.belowLeft then
      let pa ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
      let pbDom ← match op, dom with
        | .sub, some di => pure (some (← fitLe pa (← conjunct hdom ndom di)))
        | _, _ => pure none
      let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b pbDom
      let le ← match op with
        | .sub => mkAppM ``Nat.sub_le #[a.val, b.val]
        | .div => mkAppM ``Nat.div_le_self #[a.val, b.val]
        | .mod => mkAppM ``Nat.mod_le #[a.val, b.val]
        | .and => mkAppOptM ``Nat.and_le_left #[a.val, b.val]
        | _ => mkAppM ``Nat.shiftRight_le #[a.val, b.val]
      record idx (← fitLe pa le)
    else
      let self ← match self? with
        | some p => pure p
        | none => fitNeed idx
      match op with
      | .add =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppM ``Nat.le_add_right #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppM ``Nat.le_add_left #[b.val, a.val])))
      | .or =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.left_le_or #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppOptM ``Nat.right_le_or #[a.val, b.val])))
      | .shiftLeft =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.le_shiftLeft #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      | _ =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      record idx self

/-- `max` on natural numbers through the linear order, as in `le_max_left` and `max_lt`. -/
def natMax : MetaM Expr := do
  let nat := mkConst ``Nat
  mkAppOptM ``Max.max #[nat, ← mkAppOptM ``LinearOrder.toMax #[nat, none]]

/-- `max n₀ (max n₁ … nₘ)` from position `i`. -/
partial def maxChain (maxFn : Expr) (vals : Array Expr) (i : Nat := 0) : Expr :=
  if i + 1 ≥ vals.size then vals[i]! else mkApp2 maxFn vals[i]! (maxChain maxFn vals (i + 1))

/-- `vals[pos] ≤ maxChain vals i`. -/
partial def memProof (maxFn : Expr) (vals : Array Expr) (pos : Nat) (i : Nat := 0) :
    MetaM Expr := do
  if i + 1 ≥ vals.size then return ← mkAppM ``le_refl #[vals[i]!]
  if pos == i then return ← mkAppM ``le_max_left #[vals[i]!, maxChain maxFn vals (i + 1)]
  mkAppOptM ``le_max_of_le_right #[none, none, none, vals[i]!, none,
    ← memProof maxFn vals pos (i + 1)]

/-- `Fits w (maxChain vals i)` from the fit of every value. -/
partial def fitChain (fits : Array Expr) (i : Nat := 0) : MetaM Expr := do
  if i + 1 ≥ fits.size then return fits[i]!
  mkAppM ``max_lt #[fits[i]!, ← fitChain fits (i + 1)]

/-- The `GlueComputable` / `GlueComputableAt` certificate of a node, one closure rule per form. -/
partial def glueProof (graded exact : Bool) (B kE P bound : Expr) (k : Nat)
    (hb : Nat → MetaM Expr) (hd : Nat → MetaM Expr) : ANode → MetaM (Nat × Expr)
  | .reg idx _ i => do
    let fn := if graded then ``GlueComputableAt.proj else ``GlueComputable.proj
    return (1, ← mkAppOptM fn #[B, kE, P, bound, ← finLit k i, ← hb idx])
  | .const idx c _ => do
    let fn := if graded then ``GlueComputableAt.const else ``GlueComputable.const
    return (1, ← mkAppOptM fn #[B, kE, P, bound, c, ← hb idx])
  | .bin idx _ op dom a b => do
    let (ta, ga) ← glueProof graded exact B kE P bound k hb hd a
    let (tb, gb) ← glueProof graded exact B kE P bound k hb hd b
    let pf ← match dom with
      | some di => mkAppM (op.rule graded exact) #[ga, gb, ← hd di, ← hb idx]
      | none => mkAppM (op.rule graded exact) #[ga, gb, ← hb idx]
    return (ta + tb + 1, pf)

/-- `![x₀, …, xₙ]`. -/
def vecOf (xs : List Expr) : MetaM Expr := do
  match xs with
  | [] => mkAppOptM ``Matrix.vecEmpty #[mkConst ``Nat]
  | x :: xs => mkAppM ``Matrix.vecCons #[x, ← vecOf xs]

/-- `∀ i, GlueComputable[At T] B (fun v => ![f₀ v, …] i) P bound` from coordinate certificates. -/
partial def vecCoords (graded : Bool) (tE B kE P bound v : Expr) (vals proofs : Array Expr)
    (j : Nat) : MetaM Expr := do
  let l := vals.size
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit (l - j))) fun i => do
    let f ← mkLambdaFVars #[v] vals[j]!
    if j + 1 == l then
      let single ← if graded then
          mkAppOptM ``GlueComputableAt.vec_single #[B, kE, tE, P, bound, f, proofs[j]!, i]
        else
          mkAppOptM ``GlueComputable.vec_single #[B, kE, P, bound, f, proofs[j]!, i]
      return ← mkLambdaFVars #[i] single
    let g ← mkLambdaFVars #[v] (← vecOf (vals.toList.drop (j + 1)))
    let tail ← vecCoords graded tE B kE P bound v vals proofs (j + 1)
    let cons ← if graded then
        mkAppOptM ``GlueComputableAt.vec_cons
          #[B, kE, tE, P, bound, f, mkNatLit (l - j - 1), g, proofs[j]!, tail, i]
      else
        mkAppOptM ``GlueComputable.vec_cons
          #[B, kE, P, bound, f, mkNatLit (l - j - 1), g, proofs[j]!, tail, i]
    mkLambdaFVars #[i] cons

/-- Replace the maximal non-constructor subterms of `e` by local variables, then continue with
the skeleton and the pairs (variable, replaced subterm). -/
partial def withSkeleton {β : Type} (e : Expr) (acc : Array (Expr × Expr))
    (k : Expr → Array (Expr × Expr) → MetaM β) : MetaM β := do
  let e' ← whnfR e
  if let .const c _ := e'.getAppFn then
    if let some (.ctorInfo info) := (← getEnv).find? c then
      if info.induct != ``Nat then
        let args := e'.getAppArgs
        let rec go (j : Nat) (newArgs : Array Expr) (acc : Array (Expr × Expr)) : MetaM β :=
          if h : j < args.size then
            if j < info.numParams then go (j + 1) (newArgs.push args[j]) acc
            else withSkeleton args[j] acc fun a' acc' => go (j + 1) (newArgs.push a') acc'
          else k (mkAppN e'.getAppFn newArgs) acc
        return ← go 0 #[] acc
  withLocalDeclD `z (← inferType e) fun z => k z (acc.push (z, e))

/-- The coordinates of `enc a` in the client's terms. Constructor applications are kept as a
skeleton so that the encoding reduces without unfolding the client's arithmetic. -/
def coordinates (enc a : Expr) (l : Nat) : MetaM (Array Expr) :=
  withSkeleton a #[] fun skel holes => do
    let cs ← encodingAtoms enc skel l
    return cs.map fun c => c.replaceFVars (holes.map (·.1)) (holes.map (·.2))

/-- `fun _ _ => 0`. -/
def zeroWork (δ : Expr) : MetaM Expr :=
  withLocalDeclD `d δ fun d => withLocalDeclD `s (mkConst ``Memory.State) fun s =>
    mkLambdaFVars #[d, s] (mkNatLit 0)

/-- `fun _ _ _ => True`. -/
def trueSafe (δ : Expr) : MetaM Expr :=
  withLocalDeclD `w (mkConst ``Nat) fun w => withLocalDeclD `d δ fun d =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => mkLambdaFVars #[w, d, s] (mkConst ``True)

end Cslib.Tactic.Realize
