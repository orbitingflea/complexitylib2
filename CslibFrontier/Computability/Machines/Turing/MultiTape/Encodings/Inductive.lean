/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeLifts
public meta import Lean.Elab.Command

/-!
# Encodings of non-recursive inductive types

`enc_inductive eT : T where | c₁ : e₁₁, e₁₂ | c₂ | …` declares the encoding of an inductive type
whose constructors take explicit, non-recursive fields. A value is mapped to a right-nested sum
with one summand per constructor, and the sum is encoded by `encSum`. The summand of a constructor
is the framed tuple of its fields, encoded as in `enc_structure`: the field encoding itself for
one field, `encUnit` for none. Constructor `i` of `n` is therefore tagged by `i` leading `true`
bits, followed by a `false` bit unless it is the last.

The command declares:

* `eTPayload`, the encoding of the sum, and `eT_toSum`, the map from `T` to the sum;
* `eT`, the encoding of `T`, and `eT_apply`, unfolding `eT x` to `eTPayload (eT_toSum x)`;
* `eT_toSum_deg`, the linear map to the sum;
* for each constructor `c`, the rule `eT_c_inO`, which adds up the bounds of its arguments,
  `eT_c_inSpace`, retaining their independent workspace bounds, and `eT_c_polyTime`;
* `eT_elim`, case analysis by constructor on the payloads, and its rule `eT_elim_inO`, which
  charges only the case taken, together with `eT_elim_inSpace` at the same workspace bound
  and `eT_elim_polyTime`;
* for each constructor `c`, `eT_c_matches`, `eT_c_payload?`, and `eT_c_fieldJ?` for each
  zero-based field index `J`, with `_deg`, `_inO`, `_inSpace` and `_polyTime` certificates.
  Matchers have cost degree one and output degree zero; projections have degrees one/one.
* `eT_c_matches_iff` characterizes the constructor range; `eT_c_payload?_eq_some_iff`
  reconstructs the constructor from its payload, and `eT_c_payload?_range` characterizes
  payload existence. These public facts apply to unknown input values without unfolding matches.

The generated matcher and projection definitions retain the encoding/constructor prefix naming
convention above, with a declaration-specific `defsWithUnderscore` exemption.

The `toSum` and constructor rules are `scoped` `fun_prop` rules, as for `enc_structure`. The case
rule is stated for an input paired with the value, as `ComputableInO.sumElimSnd` is.

The command does not inspect the declaration for recursion, and it derives no recursive
encodings: each field encoding must already be available as an ordinary term, and the generated
certificates are relative to those encodings. A recursive field is accepted only when such an
encoding is supplied, for example `encUnary` for the field of `Nat.succ`. Fields that are
propositions, indices or implicit arguments are not supported.

Before declaring anything, the command checks that `T` is an inductive type without parameters or
indices, that every constructor is listed once in declaration order, and that each has no
implicit field and one encoding per field, of the field's type. A wrong type or constructor list
is reported at `T`, with the expected list; a wrong field is reported at its constructor or
encoding.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command Term Meta

/-- `enc_inductive eT : T where | c₁ : e₁, e₂ | c₂` declares the encoding `eT` of the inductive
type `T`: constructor `c₁` with fields encoded by `e₁` and `e₂`, and constructor `c₂` without
fields. Constructors are listed in declaration order. -/
syntax (name := encInductive) (docComment)? "enc_inductive " ident " : " ident " where"
  (" | " ident (" : " term:max,+)?)+ : command

private def app (base : Name) (suffix : String) : Ident :=
  mkIdent (base.appendAfter suffix)

/-- Check the constructor list of `enc_inductive` against the inductive type `T` before anything
is declared: every constructor once, in declaration order, with one encoding of the right type
per explicit field. -/
private def checkConstructors (T : Ident) (cs : Array Ident) (encss : Array (Array Term)) :
    CommandElabM Unit := do
  let ty ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo T
  let tyName := MessageData.ofConstName ty
  let .inductInfo info ← getConstInfo ty |
    throwErrorAt T "enc_inductive: `{tyName}` is not an inductive type"
  unless info.numParams == 0 && info.numIndices == 0 do
    throwErrorAt T "enc_inductive: `{tyName}` has parameters or indices, which are not supported"
  let expected := info.ctors.map (·.replacePrefix ty .anonymous)
  unless cs.toList.map (·.getId) == expected do
    throwErrorAt T "enc_inductive: list every constructor of `{tyName}` once, in declaration \
      order:{indentD (" ".intercalate (expected.map fun c => s!"| {c}"))}"
  for c in cs, ctor in info.ctors, encs in encss do
    let ctorName := MessageData.ofConstName ctor
    -- the explicit fields' types, `none` for a type that depends on an earlier field
    let fields ← liftTermElabM <| forallTelescopeReducing (← getConstInfo ctor).type fun xs _ => do
      unless ← xs.allM fun x => return (← x.fvarId!.getBinderInfo).isExplicit do
        throwErrorAt c "enc_inductive: `{ctorName}` has an implicit or instance field, which is \
          not supported"
      xs.mapM fun x => do
        let τ ← inferType x
        return if τ.hasFVar then none else some τ
    unless fields.size == encs.size do
      throwErrorAt c "enc_inductive: `{ctorName}` has {fields.size} explicit field(s), but \
        {encs.size} encoding(s) are listed; give one encoding per field, in order"
    -- Each encoding must have the type of its field; a dependent field is left to elaboration.
    liftTermElabM do
      for τ? in fields, enc in encs do
        let some τ := τ? | continue
        let embedding ← mkAppM ``Function.Embedding #[τ, ← mkAppM ``List #[mkConst ``Bool]]
        discard <| Term.withoutErrToSorry <| Term.elabTermEnsuringType enc embedding
      Term.synthesizeSyntheticMVarsNoPostponing

/-- The right-nested tuple of `ts`, or `()` for none. -/
private def tuple (ts : Array Term) : MacroM Term := do
  if ts.isEmpty then return ← `(())
  let mut r := ts.back!
  for t in ts.pop.reverse do
    r ← `(($t, $r))
  return r

/-- The right-nested `encPair` of `es`, or `encUnit` for none. -/
private def tupleEnc (es : Array Term) : MacroM Term := do
  if es.isEmpty then return ← `(encUnit)
  let mut r := es.back!
  for e in es.pop.reverse do
    r ← `(encPair $e $r)
  return r

/-- Inject `t` as summand `i` of a right-nested sum of `n` summands. -/
private def inject (t : Term) (i n : Nat) : MacroM Term := do
  let mut r := t
  if i + 1 < n then r ← `(Sum.inl $r)
  for _ in [0:i] do
    r ← `(Sum.inr $r)
  return r

/-- The summands of a right-nested sum type with `n` summands. -/
private partial def summands (t : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | 1 => return #[t]
  | n + 1 => do
    let t ← whnfR t
    let some (a, b) := t.app2? ``Sum |
      throwError "enc_inductive: expected a sum type, got{indentExpr t}"
    return #[a] ++ (← summands b n)

/-- Expose the three predicate views of a canonical linear degree certificate. -/
private def linearViews (fn encIn encOut : Term) (base : Name) : CommandElabM Unit := do
  let deg := app base "_deg"
  let rule := app base "_inO"
  let (linear, space, polynomial) ← liftMacroM <| Internal.linearDegreeViews deg
  elabCommand (← `(@[scoped fun_prop] public theorem $rule:ident :
    ComputableInO $fn $encIn $encOut (fun x => ($encIn x).length)
      (fun x => ($encIn x).length) := $linear))
  elabCommand (← `(@[scoped fun_prop] public theorem $(app base "_inSpace"):ident :
    ComputableInSpace $fn $encIn $encOut (fun x => ($encIn x).length) :=
      $space))
  elabCommand (← `(@[scoped fun_prop] public theorem $(app base "_polyTime"):ident :
    ComputableInPolyTime $fn $encIn $encOut := $polynomial))

/-- Elaborate `enc_inductive`. -/
@[command_elab encInductive] def elabEncInductive : CommandElab := fun stx => do
  let `($[$doc:docComment]? enc_inductive $eT:ident : $T:ident where
      $[ | $cs:ident $[: $ess,*]?]*) := stx | throwUnsupportedSyntax
  let name := eT.getId
  let n := cs.size
  let encss : Array (Array Term) := ess.map fun o => (o.map (·.getElems)).getD #[]
  checkConstructors T cs encss
  let payloads ← liftMacroM <| encss.mapM tupleEnc
  -- the encoding of the sum of the payloads
  let mut sumEnc : Term := payloads.back!
  for p in payloads.pop.reverse do
    sumEnc ← `(encSum $p $sumEnc)
  -- the encodings of the remaining summands, `rests[i]` for summands `i` to `n - 1`
  let mut rests : Array Term := #[payloads.back!]
  for p in payloads.pop.reverse do
    rests := #[← `(encSum $p $(rests[0]!))] ++ rests
  let payloadName := app name "Payload"
  elabCommand (← `(public abbrev $payloadName:ident := $sumEnc))
  addDocStringCore ((← getCurrNamespace) ++ payloadName.getId)
    s!"The encoding of the constructor payloads of `{name}`."
  -- the sum type, read back from the encoding
  let (sumTy, argTys) ← liftTermElabM do
    let some c := (← getEnv).find? ((← getCurrNamespace) ++ payloadName.getId) |
      throwError "enc_inductive: missing payload encoding"
    let ty ← whnfR (← instantiateMVars c.type)
    let some (σ, _) := ty.app2? ``Function.Embedding |
      throwError "enc_inductive: unexpected payload type{indentExpr ty}"
    let parts ← summands σ n
    return (← PrettyPrinter.delab σ, ← parts.mapM fun p => PrettyPrinter.delab p)
  let toSum := app name "_toSum"
  let alts ← liftMacroM <| (Array.range n).mapM fun i => do
    let xs := (Array.range encss[i]!.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let pat : Term := Syntax.mkApp (mkIdent (T.getId ++ cs[i]!.getId)) xs
    let rhs ← inject (← tuple xs) i n
    `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs)
  elabCommand (← `(/-- The constructor payloads of a value, as a summand. -/
    @[expose] public def $toSum:ident : $T → $sumTy := fun x => match x with $alts:matchAlt*))
  elabCommand (← `($[$doc:docComment]? @[expose] public def $eT:ident : $T ↪ List Bool :=
    (⟨$toSum, fun x y h => by cases x <;> cases y <;> simp_all [$toSum:ident]⟩ :
      $T ↪ $sumTy).trans $payloadName))
  elabCommand (← `(@[simp] public theorem $(app name "_apply") (x : $T) :
    $eT x = $payloadName ($toSum x) := rfl))
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_toSum_deg"):ident :
    ComputableInDegree $toSum $eT $payloadName 1 1 := ComputableInDegree.of_eq fun _ => rfl))
  -- constructor rules, adding up the bounds of the arguments
  let γ := mkIdent `γ
  let encIn := mkIdent `encIn
  let x := mkIdent `x
  for i in [0:n] do
    let es := encss[i]!
    let k := es.size
    let ctor := mkIdent (T.getId ++ cs[i]!.getId)
    let rule := app name s!"_{cs[i]!.getId}_inO"
    if k = 0 then
      elabCommand (← `(@[scoped fun_prop] public theorem $rule:ident {$γ : Type}
        {$encIn : $γ ↪ List Bool} :
        ComputableInO (fun _ : $γ => $ctor) $encIn $eT (fun $x => ($encIn $x).length)
          fun $x => ($encIn $x).length := ComputableInO.const _))
      elabCommand (← `(@[scoped fun_prop] public theorem
        $(app name s!"_{cs[i]!.getId}_inSpace"):ident {$γ : Type}
        {$encIn : $γ ↪ List Bool} :
        ComputableInSpace (fun _ : $γ => $ctor) $encIn $eT
          (fun $x => ($encIn $x).length) := ComputableInSpace.of_inO $rule))
      elabCommand (← `(@[scoped fun_prop] public theorem
        $(app name s!"_{cs[i]!.getId}_polyTime"):ident {$γ : Type}
        {$encIn : $γ ↪ List Bool} :
        ComputableInPolyTime (fun _ : $γ => $ctor) $encIn $eT :=
          ($rule).computableInPolyTime PolyBounded.self PolyBounded.self))
      continue
    let xN (j : Nat) := mkIdent (Name.mkSimple s!"x{j}")
    let hN (j : Nat) := mkIdent (Name.mkSimple s!"h{j}")
    let TN (j : Nat) := mkIdent (Name.mkSimple s!"T{j}")
    let SN (j : Nat) := mkIdent (Name.mkSimple s!"S{j}")
    let last := k - 1
    let mut sumT : Term ← `($(TN last) $x:ident)
    let mut sumS : Term ← `($(SN last) $x:ident)
    let mut pay : Term := hN last
    for j in (List.range last).reverse do
      sumT ← `($(TN j) $x:ident + $sumT)
      sumS ← `($(SN j) $x:ident + $sumS)
      pay ← `(ComputableInO.prod $(hN j) $pay)
    -- inject the payload: `inl` at its own summand, then `inr` for each earlier one
    let mut inj : Term := pay
    if i + 1 < n then
      inj ← `(ComputableInO.comp_linear (ComputableInO.inl $(payloads[i]!) $(rests[i + 1]!)) $inj)
    for j in (List.range i).reverse do
      inj ← `(ComputableInO.comp_linear (ComputableInO.inr $(payloads[j]!) $(rests[j + 1]!)) $inj)
    let args ← (Array.range k).mapM fun j => (`($(xN j) $x:ident) : CommandElabM Term)
    let appl : Term := Syntax.mkApp ctor args
    let mut binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    for j in [0:k] do
      binders := binders.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
      binders := binders.push (← `(bracketedBinder| {$(TN j) $(SN j) : $γ → ℕ}))
    for j in [0:k] do
      binders := binders.push (← `(bracketedBinder|
        ($(hN j) : ComputableInO $(xN j) $encIn $(es[j]!) $(TN j) $(SN j))))
    elabCommand (← `(@[scoped fun_prop] public theorem $rule:ident {$γ : Type}
      {$encIn : $γ ↪ List Bool} $binders* :
      ComputableInO (fun $x => $appl) $encIn $eT (fun $x => $sumT) fun $x => $sumS :=
        ComputableInO.of_enc_eq $inj fun _ => rfl))
    -- Space rules forget only the time witnesses, retaining independent workspace bounds.
    let mut sb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut unpack : TSyntaxArray `tactic := #[]
    for j in [0:k] do
      sb := sb.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
      sb := sb.push (← `(bracketedBinder| {$(SN j) : $γ → ℕ}))
    for j in [0:k] do
      sb := sb.push (← `(bracketedBinder|
        ($(hN j) : ComputableInSpace $(xN j) $encIn $(es[j]!) $(SN j))))
      unpack := unpack.push (← `(tactic| obtain ⟨$(TN j), $(hN j)⟩ := $(hN j).exists_inO))
    let hs : Array Term := (Array.range k).map fun j => hN j
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app name s!"_{cs[i]!.getId}_inSpace"):ident {$γ : Type}
      {$encIn : $γ ↪ List Bool} $sb* :
      ComputableInSpace (fun $x => $appl) $encIn $eT (fun $x => $sumS) := by
        $unpack:tactic*
        exact ComputableInSpace.of_inO ($rule $hs*)))
    -- Recover explicit clocks from the polynomial hypotheses, then lift the existing
    -- arbitrary-resource constructor certificate. No constructor machine is rebuilt here.
    let mut pb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut clocks : TSyntaxArray `tactic := #[]
    let boundBase : Term ← `(PolyBounded.self.add (PolyBounded.const 1))
    let dN (j : Nat) := mkIdent (Name.mkSimple s!"d{j}")
    let eN (j : Nat) := mkIdent (Name.mkSimple s!"e{j}")
    let mut proofs : Array Term := #[]
    for j in [0:k] do
      pb := pb.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
    for j in [0:k] do
      pb := pb.push (← `(bracketedBinder|
        ($(hN j) : ComputableInPolyTime $(xN j) $encIn $(es[j]!))))
      clocks := clocks.push (← `(tactic|
        obtain ⟨$(dN j), $(eN j), $(hN j)⟩ := $(hN j).exists_degree))
      proofs := proofs.push (← `($(hN j).inO))
    let mut polyBound : Term ← `(($boundBase).pow $(dN last))
    for j in (List.range last).reverse do
      polyBound ← `((($boundBase).pow $(dN j)).add $polyBound)
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app name s!"_{cs[i]!.getId}_polyTime"):ident {$γ : Type}
      {$encIn : $γ ↪ List Bool} $pb* :
      ComputableInPolyTime (fun $x => $appl) $encIn $eT := by
        $clocks:tactic*
        exact ($rule $proofs*).computableInPolyTime $polyBound $polyBound))
  let applyName := app name "_apply"
  -- Match tags using finite Boolean operations on the encoded prefix. Payload and field
  -- projections use the same matcher and the existing tail/frame streaming certificates.
  for i in [0:n] do
    let matcher := app name s!"_{cs[i]!.getId}_matches"
    let mut mas : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for j in [0:n] do
      let xs := (Array.range encss[j]!.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
      let pat : Term := Syntax.mkApp (mkIdent (T.getId ++ cs[j]!.getId)) xs
      let b : Term ← if i == j then `(true) else `(false)
      mas := mas.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $b))
    elabCommand (← `(/-- Test whether the value has this constructor. -/
      @[expose, nolint defsWithUnderscore]
      public def $matcher:ident (v : $T) : Bool := match v with $mas:matchAlt*))
    let mut raw : Term ← `(ComputableInDegree.of_eq (f := fun v : $T => $eT v)
      (encIn := $eT) (encMid := encBits) (fun _ => rfl))
    let mut test : Term ← `(ComputableInDegree.const (encIn := $eT) (encMid := encBool) true)
    let tags := i + (if i + 1 < n then 1 else 0)
    for j in [0:tags] do
      let bit : Term ← `((ComputableInDegree.headD (enc₁ := encBool)
        (enc := encBits) false).comp $raw)
      let wanted ← if j < i then pure bit else
        `((ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp $bit)
      test ← `((ComputableInDegree.of_finite (encIn := encPair encBool encBool)
        (encMid := encBool) (fun p : Bool × Bool => p.1 && p.2)).comp (($test).prod $wanted))
      raw ← `((ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).comp $raw)
    if i == 0 && n > 1 then
      test ← `((ComputableInO.isLeft_deg $(payloads[0]!) $(rests[1]!)).comp
        $(app name "_toSum_deg"))
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app matcher.getId "_deg"):ident : ComputableInDegree $matcher $eT encBool 1 0 :=
      (($test).mono (d' := 1) (e' := 0)).of_enc_eq (fun v => by
        cases v <;> simp [$matcher:ident, $applyName:ident, $toSum:ident, encBits,
          encBool, List.headD])))
    linearViews matcher eT (← `(encBool)) matcher.getId
    -- Include the complete payload and every individual field, without default inhabitants.
    for field in [0:encss[i]!.size + 1] do
      let projection := app name (if field == 0 then s!"_{cs[i]!.getId}_payload?"
        else s!"_{cs[i]!.getId}_field{field - 1}?")
      let out : Term := if field == 0 then payloads[i]! else (encss[i]!)[field - 1]!
      let outTy ← if field == 0 then pure argTys[i]! else liftTermElabM do
        let encoding ← Term.elabTerm out none
        let ty ← whnfR (← instantiateMVars (← inferType encoding))
        let some (α, _) := ty.app2? ``Function.Embedding |
          throwError "enc_inductive: unexpected field encoding type{indentExpr ty}"
        PrettyPrinter.delab α
      let mut pas : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for j in [0:n] do
        let xs := (Array.range encss[j]!.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
        let pat : Term := Syntax.mkApp (mkIdent (T.getId ++ cs[j]!.getId)) xs
        let value ← if field == 0 then liftMacroM (tuple xs) else
          pure (xs[field - 1]?.getD (mkIdent `unused) : Term)
        let rhs ← if i == j then `(some $value) else `(none)
        pas := pas.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs))
      elabCommand (← `(/-- Extract the constructor payload or field; return `none` otherwise. -/
        @[expose, nolint defsWithUnderscore]
        public def $projection:ident (v : $T) : Option $outTy :=
          match v with $pas:matchAlt*))
      elabCommand (← `(@[simp] public theorem $(app projection.getId "_isSome"):ident
        (v : $T) : ($projection v).isSome = $matcher v := by cases v <;> rfl))
      if field == 0 then
        -- Reconstruct the constructor from its complete right-nested payload. Keep this
        -- semantic interface independent of the encoded tag and frame layout.
        let a := mkIdent `a
        let ctor := mkIdent (T.getId ++ cs[i]!.getId)
        let mut args : Array Term := #[]
        let mut rest : Term := a
        for j in [0:encss[i]!.size] do
          if j + 1 < encss[i]!.size then
            args := args.push (← `(($rest).1))
            rest ← `(($rest).2)
          else
            args := args.push rest
        let reconstructed := Syntax.mkApp ctor args
        let valueIff := app projection.getId "_eq_some_iff"
        let valueProof ← if encss[i]!.size > 1 then
          `(tactic| cases v <;> simp [$projection:ident, Prod.ext_iff])
        else
          `(tactic| cases v <;> simp [$projection:ident])
        elabCommand (← `(/-- The complete payload determines exactly this constructor value. -/
          public theorem $valueIff:ident (v : $T) ($a : $(argTys[i]!)) :
            $projection v = some $a ↔ v = $reconstructed := by $valueProof:tactic))
        elabCommand (← `(/-- The matcher recognizes precisely the range of this constructor. -/
          public theorem $(app matcher.getId "_iff"):ident (v : $T) :
            $matcher v = true ↔ ∃ ($a:ident : $(argTys[i]!)), v = $reconstructed := by
              rw [← $(app projection.getId "_isSome")]
              simp only [Option.isSome_iff_exists, $valueIff:ident]))
        elabCommand (← `(/-- A payload exists precisely when this constructor matches. -/
          public theorem $(app projection.getId "_range"):ident (v : $T) :
            (∃ ($a:ident : $(argTys[i]!)), $projection v = some $a) ↔ $matcher v = true := by
              rw [← $(app projection.getId "_isSome")]
              exact Option.isSome_iff_exists.symm))
      let mut word := raw
      if field > 0 then
        for _ in [0:field - 1] do
          word ← `((ComputableInDegree.of_dropFrame (f := dropFrame)
            (encIn := encBits) (encMid := encBits) (fun _ => rfl)).comp $word)
        if field < encss[i]!.size then
          word ← `((ComputableInDegree.of_unframe (f := unframe)
            (encIn := encBits) (encMid := encBits) (fun _ => rfl)).comp $word)
      let someWord ← `((ComputableInDegree.const (encIn := $eT) (encMid := encBool) true).append
        $word (fun _ => rfl))
      if i == 0 && n > 1 && (field == 0 || encss[i]!.size == 1) then
        elabCommand (← `(@[scoped fun_prop] public theorem
          $(app projection.getId "_deg"):ident :
          ComputableInDegree $projection $eT (encOption $out) 1 1 :=
          ((ComputableInO.getLeft?_deg $(payloads[0]!) $(rests[1]!)).comp
            $(app name "_toSum_deg")).of_enc_eq (fun v => by
              cases v <;> rfl)))
      else
        elabCommand (← `(@[scoped fun_prop] public theorem
          $(app projection.getId "_deg"):ident :
          ComputableInDegree $projection $eT (encOption $out) 1 1 := by
          have hn : ComputableInDegree (fun _ : $T => ([] : List Bool)) $eT encBits 1 1 :=
            (ComputableInDegree.const (encMid := encBits) []).mono
          exact ((($(app matcher.getId "_deg")).ite
            (($someWord).restrict _) (hn.restrict _)).mono (d' := 1) (e' := 1)).of_enc_eq
              (fun v => by
                cases v <;>
                  simp [$projection:ident, $matcher:ident, $applyName:ident, $toSum:ident,
                    encBits, unframe_frame_append, dropFrame_frame_append]
                all_goals rfl)))
      linearViews projection eT (← `(encOption $out)) projection.getId
  -- case analysis on the payloads
  let elim := app name "_elim"
  let fN (i : Nat) := mkIdent (Name.mkSimple s!"f{i}")
  let mut elimBody : Term := fN (n - 1)
  for i in (List.range (n - 1)).reverse do
    elimBody ← `(Sum.elim $(fN i) $elimBody)
  let mut elimBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    elimBinders := elimBinders.push (← `(bracketedBinder| ($(fN i) : $(argTys[i]!) → ε)))
  elabCommand (← `(/-- Case analysis by constructor, on the constructor payloads. -/
    @[expose] public def $elim:ident {ε : Sort _} (v : $T) $elimBinders* : ε :=
      $elimBody ($toSum v)))
  -- its rule: nested `sumElimSnd`, pulled back along `toSum`
  let encP := mkIdent `encP
  let encE := mkIdent `encE
  let p := mkIdent `p
  let gN (i : Nat) := mkIdent (Name.mkSimple s!"g{i}")
  let hN (i : Nat) := mkIdent (Name.mkSimple s!"h{i}")
  let TN (i : Nat) := mkIdent (Name.mkSimple s!"T{i}")
  let SN (i : Nat) := mkIdent (Name.mkSimple s!"S{i}")
  let mut rb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    rb := rb.push (← `(bracketedBinder| {$(gN i) : π × $(argTys[i]!) → ε}))
    rb := rb.push (← `(bracketedBinder| {$(TN i) $(SN i) : π × $(argTys[i]!) → ℕ}))
  for i in [0:n] do
    rb := rb.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(gN i) (encPair $encP $(payloads[i]!)) $encE $(TN i) $(SN i))))
  let a := mkIdent `a
  let lam (F : Nat → Ident) (i : Nat) : CommandElabM Term := `(fun $a => $(F i) ($p.1, $a))
  let fs ← (Array.range n).mapM (lam gN)
  let ts ← (Array.range n).mapM (lam TN)
  let ss ← (Array.range n).mapM (lam SN)
  let fnTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ fs)
  let tTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ ts)
  let sTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ ss)
  let nLit := Syntax.mkNumLit (toString n)
  let mut nested : Term := hN (n - 1)
  for i in (List.range (n - 1)).reverse do
    nested ← `(ComputableInO.sumElimSnd $(hN i) $nested)
  elabCommand (← `(public theorem $(app name "_elim_inO"):ident {π ε : Type}
      {$encP : π ↪ List Bool} {$encE : ε ↪ List Bool} $rb* :
      ComputableInO (fun $p : π × $T => $fnTerm) (encPair $encP $eT) $encE
        (fun $p => $nLit * (encPair $encP $eT $p).length + $tTerm)
        fun $p => $nLit * (encPair $encP $eT $p).length + $sTerm := by
    refine (($nested).of_encIn_eq (fun q : π × $T => (q.1, $toSum q.2)) fun _ => rfl).mono_le
      ?_ ?_ <;>
    · rintro ⟨q, v⟩
      cases v <;>
      simp only [Function.comp_apply, $elim:ident, $toSum:ident, $applyName:ident, Sum.elim_inl,
        Sum.elim_inr, length_encPair, encSum_inl, encSum_inr, List.length_cons] <;>
      omega))
  -- The case space contract charges precisely the selected branch's workspace. Its time
  -- function is existential, independently for every branch.
  let mut spaceBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut unpack : TSyntaxArray `tactic := #[]
  for i in [0:n] do
    spaceBinders := spaceBinders.push (← `(bracketedBinder| {$(gN i) : π × $(argTys[i]!) → ε}))
    spaceBinders := spaceBinders.push (← `(bracketedBinder| {$(SN i) : π × $(argTys[i]!) → ℕ}))
  for i in [0:n] do
    spaceBinders := spaceBinders.push (← `(bracketedBinder|
      ($(hN i) : ComputableInSpace $(gN i) (encPair $encP $(payloads[i]!)) $encE $(SN i))))
    unpack := unpack.push (← `(tactic| obtain ⟨$(TN i), $(hN i)⟩ := $(hN i).exists_inO))
  let hs : Array Term := (Array.range n).map fun i => hN i
  elabCommand (← `(public theorem $(app name "_elim_inSpace"):ident {π ε : Type}
      {$encP : π ↪ List Bool} {$encE : ε ↪ List Bool} $spaceBinders* :
      ComputableInSpace (fun $p : π × $T => $fnTerm) (encPair $encP $eT) $encE
        (fun $p => $nLit * (encPair $encP $eT $p).length + $sTerm) := by
    $unpack:tactic*
    exact ComputableInSpace.of_inO ($(app name "_elim_inO") $hs*)))
  -- Polynomial elimination reuses the arbitrary-resource case machine. Each branch clock is
  -- bounded in the full input size before the finitely many envelopes are added.
  let mut pb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut clocks : TSyntaxArray `tactic := #[]
  let mut estimates : TSyntaxArray `tactic := #[]
  let mut facts : TSyntaxArray `tactic := #[]
  let mut proofs : Array Term := #[]
  let dN (i : Nat) := mkIdent (Name.mkSimple s!"d{i}")
  let eN (i : Nat) := mkIdent (Name.mkSimple s!"e{i}")
  let bN (i : Nat) := mkIdent (Name.mkSimple s!"bound{i}")
  let mut clockFs : Array Term := #[]
  let mut envelope : Term ← `((PolyBounded.const $nLit).mul PolyBounded.self)
  for i in [0:n] do
    pb := pb.push (← `(bracketedBinder| {$(gN i) : π × $(argTys[i]!) → ε}))
  for i in [0:n] do
    pb := pb.push (← `(bracketedBinder|
      ($(hN i) : ComputableInPolyTime $(gN i) (encPair $encP $(payloads[i]!)) $encE)))
    clocks := clocks.push (← `(tactic|
      obtain ⟨$(dN i), $(eN i), $(hN i)⟩ := $(hN i).exists_degree))
    proofs := proofs.push (← `($(hN i).inO))
    clockFs := clockFs.push (← `(fun $a =>
      ((encPair $encP $(payloads[i]!) ($p.1, $a)).length + 1) ^ $(dN i)))
    let selectors ← (Array.range n).mapM fun j => do
      if i == j then
        `(fun $a => ((encPair $encP $(payloads[j]!) ($p.1, $a)).length + 1) ^ $(dN i))
      else `(fun _ => (0 : ℕ))
    let selected := Syntax.mkApp elim (#[← `($p.2)] ++ selectors)
    estimates := estimates.push (← `(tactic|
      have $(bN i) : ∀ $p : π × $T, $selected ≤
          ((encPair $encP $eT $p).length + 1) ^ $(dN i) := by
        rintro ⟨q, v⟩
        cases v <;>
          simp only [$elim:ident, $toSum:ident, $applyName:ident, Sum.elim_inl,
            Sum.elim_inr, length_encPair, encSum_inl, encSum_inr, List.length_cons] <;>
          first | omega | (apply Nat.pow_le_pow_left; omega)))
    facts := facts.push (← `(tactic| have := $(bN i) (q, v)))
    envelope ← `(($envelope).add
      ((PolyBounded.self.add (PolyBounded.const 1)).pow $(dN i)))
  let selectedClock := Syntax.mkApp elim (#[← `($p.2)] ++ clockFs)
  elabCommand (← `(public theorem $(app name "_elim_polyTime"):ident {π ε : Type}
      {$encP : π ↪ List Bool} {$encE : ε ↪ List Bool} $pb* :
      ComputableInPolyTime (fun $p : π × $T => $fnTerm) (encPair $encP $eT) $encE := by
    $clocks:tactic*
    $estimates:tactic*
    have hb : PolyBounded (fun $p : π × $T => (encPair $encP $eT $p).length)
        (fun $p => $nLit * (encPair $encP $eT $p).length + $selectedClock) :=
      ($envelope).mono (by
      rintro ⟨q, v⟩
      $facts:tactic*
      cases v <;>
        simp only [$elim:ident, $toSum:ident, $applyName:ident, Sum.elim_inl,
          Sum.elim_inr, length_encPair, encSum_inl, encSum_inr, List.length_cons] at * <;>
        omega)
    exact ($(app name "_elim_inO") $proofs*).computableInPolyTime hb hb))

end Turing.MultiTapeTM
