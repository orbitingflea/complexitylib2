/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Tactic.RealizeGlue

/-!
# The `realize` tactic

The tactic is available inside `Cslib.WordRAM`, or after `open Cslib.WordRAM` or
`open scoped Cslib.WordRAM`. Importing this module alone does not activate its syntax.

`realize` proves a goal `Realizes B p input output safe work` or
`RealizesAt n C B p input output safe work` for a memory client `p`. It walks the client syntax,
unfolding definitions, with one rule per form:

* `bind`: `Realizes.bind₀` / `RealizesAt.bind₀`. After each bind the live words are the previous
  ones followed by the answer's encoding (`WordEncoding`); `realize` keeps this layout itself.
* `pure`: `Realizes.pure₀` / `RealizesAt.pure₀`, with each result word certified by a
  `GlueComputable` / `GlueComputableAt` proof assembled from the closure rules of
  `Complexity.Computability.WordRAM.Glue`: projections, constants, and the exact- or
  standard-basis arithmetic and bitwise operations.
* the four memory queries: `read`, `write`, `alloc` and `allocDirty`.
* a method with a local zero-work `Realizes` / `RealizesAt` certificate: `reindex`, selecting its
  arguments from live words before unfolding its implementation.
* `if` on `a = b`, `a < b` or `a > b`: `branch₀`.
* `match` on an optional word or word pair: the client equals the branch on its presence tag
  (`congr`, proved by cases).
* `iterate step D n a` whose step begins with a query: `iterate₀`, after adapting `D` and any
  captured live words to the whole environment. The source and reached-state domain are
  transported back to the client's original loop.
* `boundedWhile G step D n a` whose step begins with a query: `while₀`. The guard `G D r` may be
  `a = b`, `a < b`, `a > b` or `a ≠ 0` (tested as `0 < a`), with any decidability instance, over
  the live words and the state's words; an operand independent of the state, such as a constant, is
  computed before the loop. The cutoff `n` is a ghost bound and is not computed. The certificate is
  transported to the client's guard, step and `D` (`boundedWhile_congr`, `whileSafe_imp`), so the
  loop's domain is `whileSafe G step …` in the client's terms, under the loop's valid history
  (`consequence_valid`), ready for `whileSafe_of_measure`.

## Main definitions

* `realize`: the tactic.
-/

public meta section

namespace Cslib.Tactic.Realize

open Lean Meta Elab Tactic Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-! ### Realization -/

/-- The input encoding of the continuation of a bind. -/
private def appendInput (env : Env) (answer : Expr) (l : Nat) : MetaM Expr := do
  let prod ← mkAppM ``Function.Embedding.prodMap #[env.input, answer]
  let app ← mkAppM ``Equiv.toEmbedding
    #[← mkAppOptM ``Fin.appendEquiv #[mkConst ``Nat, mkNatLit env.k, mkNatLit l]]
  mkAppM ``Function.Embedding.trans #[prod, app]

/-- The environment of the continuation of a bind whose answer has type `α`. -/
private def extend (env : Env) (α answer : Expr) (l : Nat) : MetaM Env := do
  let ty ← mkAppM ``Prod #[env.ty, α]
  let input ← appendInput env answer l
  let atoms ← withLocalDeclD `x ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    let old ← env.atoms.mapM fun a => whnf (a.beta #[x1])
    let new ← encodingAtoms answer x2 l
    (old ++ new).mapM fun a => mkLambdaFVars #[x] a
  return { ty, k := env.k + l, input, atoms }

/-- The reply and next memory of a client from memory `s`, in the client's terms. -/
private def replyState (m s : Expr) : MetaM (Expr × Expr) := do
  let m' ← whnfR m
  let generic := do
    let spec ← mkAppM ``Memory.spec #[mkNatLit 0]
    return (← mkAppM ``StateTransitionSpec.clientResult #[spec, s, m],
      ← mkAppM ``StateTransitionSpec.clientState #[spec, s, m])
  let mem ← mkAppM ``Memory.State.mem #[s]
  let frontier ← mkAppM ``Memory.State.frontier #[s]
  if m'.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR m'.appArg!
    if let some a := op.app1? ``Memory.Op.read then return (mkApp mem a, s)
    if let some (a, v) := op.app2? ``Memory.Op.write then
      return (mkConst ``Unit.unit,
        ← mkAppM ``Memory.State.mk #[← mkAppM ``Function.update #[mem, a, v], frontier])
    if let some n := op.app1? ``Memory.Op.alloc then
      return (frontier, ← mkAppM ``Memory.State.mk
        #[← mkAppM ``Cslib.WordRAM.clear #[mem, frontier, n], ← mkAppM ``HAdd.hAdd #[frontier, n]])
    if let some n := op.app1? ``Memory.Op.allocDirty then
      return (frontier, ← mkAppM ``Memory.State.mk #[mem, ← mkAppM ``HAdd.hAdd #[frontier, n]])
    return ← generic
  if m'.isAppOfArity ``Pure.pure 4 then return (m'.appArg!, s)
  if m'.isAppOfArity ``PFunctor.FreeM.pure 3 then return (m'.appArg!, s)
  generic

/-- The result type of a memory client. -/
private def resultType (body : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType body)
  unless ty.isAppOfArity ``PFunctor.FreeM 2 do
    throwError "realize: expected a memory client, got{indentExpr body}\nof type{indentExpr ty}"
  whnf ty.appArg!

/-- The encoding of an intermediate answer type. -/
private def encodingOf (α : Expr) : MetaM Expr := do
  let some inst ← synthInstance? (← mkAppM ``WordEncoding #[α])
    | throwError "realize: no `WordEncoding` instance for the answer type{indentExpr α}"
  let e ← mkAppOptM ``WordEncoding.encode #[α, inst]
  return (← unfoldProjInst? e).getD e

/-- `Bind.bind (pure a) cont` in `Memory.Prog`. -/
private def bindPure (a cont : Expr) : MetaM Expr := do
  let prog := mkConst ``Memory.Prog
  let pa ← mkAppOptM ``Pure.pure #[prog, none, mkConst ``Nat, a]
  mkAppOptM ``Bind.bind #[prog, none, mkConst ``Nat, none, pa, cont]

/-- Prove `∀ d i, output (f d) i = g i (input d)` for `i : Fin l` by `Fin.cases`, with one `rfl` per
coordinate. Both sides are the same coordinate by construction of `g` (`coordinates`, `analyze`);
the kernel checks each `rfl`. -/
private def proveResult (ty : Expr) (l : Nat) : MetaM Expr :=
  forallBoundedTelescope ty (some 2) fun xs eq => do
    let #[d, i] := xs | throwError "realize: internal error in the result encoding"
    let P ← mkLambdaFVars #[i] eq
    let rec cover (n : Nat) (emb : Expr → MetaM Expr) : MetaM Expr := do
      let finN := mkApp (mkConst ``Fin) (mkNatLit n)
      match n with
      | 0 => withLocalDeclD `j finN fun j => do
        mkLambdaFVars #[j] (← mkAppOptM ``Fin.elim0 #[P.beta #[← emb j], j])
      | m + 1 => do
        let motive ← withLocalDeclD `j finN fun j => do mkLambdaFVars #[j] (P.beta #[← emb j])
        let goal := P.beta #[← emb (← mkNumeral finN 0)]
        let some (_, lhs, _) := goal.eq?
          | throwError "realize: internal error in the result encoding"
        let h0 ← mkExpectedTypeHint (← mkEqRefl lhs) goal
        let hs ← cover m fun j => do emb (← mkAppM ``Fin.succ #[j])
        mkAppOptM ``Fin.cases #[mkNatLit m, motive, h0, hs]
    mkLambdaFVars #[d] (← cover l pure)

/-- Certify `pure a` with the result encoding `out`, for the environment variable `d`. -/
private def realizePure (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr) (a out : Expr) :
    TermElabM Out := do
  let l ← encodingWidth out
  let coordsU ← coordinates out a l
  let gnodes ← coordsU.mapM fun c => liftMetaM (analyze atoms d c)
  unless ctx.exact || ctx.standard || gnodes.all (fun g => !(g matches .bin ..)) do
    throwError "realize: word arithmetic is certified in the exact and standard bases; the \
      goal's basis is{indentExpr ctx.basis}"
  let k := env.k
  let kE := mkNatLit k
  let B := ctx.basis
  let nat := mkConst ``Nat
  let finK := mkApp (mkConst ``Fin) kE
  let finL := mkApp (mkConst ``Fin) (mkNatLit l)
  let maxFn ← natMax
  withLocalDeclD `v (← mkArrow finK nat) fun v => do
    let (anodes, st) ← (gnodes.mapM (annotate ctx.exact k v)).run {}
    let uvals := gnodes.foldl (fun acc g => userVals g acc) #[]
    let domTy := conj st.domV.toList
    let P ← mkLambdaFVars #[v] domTy
    let bound ← mkLambdaFVars #[v]
      (if st.vals.isEmpty then mkNatLit 0 else maxChain maxFn st.vals)
    let hb (idx : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← memProof maxFn st.vals idx)
    let hd (di : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← conjunct hv st.domV.size di)
    let tproofs ← anodes.mapM fun n =>
      liftMetaM (glueProof ctx.graded ctx.exact B kE P bound k hb hd n)
    let T : Nat := tproofs.foldl (fun m (t, _) => max m t) 1
    let tE := mkNatLit T
    let vals := anodes.map (·.val)
    let proofs ← (Array.range anodes.size).mapM fun j => do
      let (t, pf) := tproofs[j]!
      if !ctx.graded || t == T then pure pf
      else
        let f ← mkLambdaFVars #[v] vals[j]!
        let ht ← natLeProof t T
        mkAppOptM ``GlueComputableAt.mono #[B, kE, mkNatLit t, P, bound, f, tE, ht, pf]
    let gfun ← withLocalDeclD `i finL fun i => do
      mkLambdaFVars #[i, v] (mkApp (← vecOf vals.toList) i)
    let hcoord ← if l == 0 then
        withLocalDeclD `i finL fun i => do
          let ty ← if ctx.graded then
              mkAppM ``GlueComputableAt #[tE, B, mkApp gfun i, P, bound]
            else
              mkAppM ``GlueComputable #[B, mkApp gfun i, P, bound]
          mkLambdaFVars #[i] (← mkAppOptM ``Fin.elim0 #[ty, i])
      else vecCoords ctx.graded tE B kE P bound v vals proofs 0
    withLocalDeclD `w nat fun w => do
      let needIdx := anodes.foldl (fun acc n => needNodes ctx.exact n false acc) #[]
      let needV ← needIdx.mapM fun i => mkAppM ``Fits #[w, st.vals[i]!]
      let needU ← needIdx.mapM fun i => mkAppM ``Fits #[w, uvals[i]!]
      let needTy := conj needV.toList
      let need ← mkLambdaFVars #[w, v] needTy
      let hregsTy ← withLocalDeclD `i finK fun i => do
        mkForallFVars #[i] (← mkAppM ``Fits #[w, mkApp v i])
      let hneed ← withLocalDeclD `hregs hregsTy fun hregs =>
        withLocalDeclD `hP domTy fun hP => withLocalDeclD `hn needTy fun hn => do
          let fits ← if st.vals.isEmpty then pure #[← mkAppM ``fits_zero #[w]] else do
            let (_, fits) ← (anodes.forM fun n => discard <|
              fitProofs ctx.exact k w hregs hP hn st.domV.size needIdx n none).run
                (Array.replicate st.vals.size default)
            pure fits
          mkLambdaFVars #[w, v, hregs, hP, hn] (← fitChain fits)
      let f ← mkLambdaFVars #[d] a
      let resTy ← withLocalDeclD `d env.ty fun d' => withLocalDeclD `i finL fun i => do
        let lhs := mkApp (← mkAppM ``DFunLike.coe #[out, f.beta #[d']]) i
        let rhs := mkApp2 gfun i (← mkAppM ``DFunLike.coe #[env.input, d'])
        mkForallFVars #[d', i] (← mkEq lhs rhs)
      let hresult ← proveResult resTy l
      let pureFn := if ctx.graded then ``RealizesAt.pure₀ else ``Realizes.pure₀
      let proof ← mkAppM pureFn #[env.input, out, f, gfun, need, hresult, hcoord, hneed]
      let safe ← withLocalDeclD `s (mkConst ``Memory.State) fun s =>
        mkLambdaFVars #[w, d, s] (mkAnd (conj st.domU.toList) (conj needU.toList))
      return { n := 2 * l * T, c := 1 * (l * T + l + 1), proof, output := out, safe }

/-- The output encoding of a certificate. -/
private def outputOf (proof : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType proof)
  if ty.isAppOfArity ``Realizes 10 then return ty.getArg! 7
  if ty.isAppOfArity ``RealizesAt 12 then return ty.getArg! 9
  throwError "realize: internal error, not a certificate"

/-- Check a query's output encoding against the required one. -/
private def checkOutput (proof : Expr) (output? : Option Expr) : MetaM Expr := do
  let out ← outputOf proof
  if let some o := output? then
    unless ← isDefEq out o do
      throwError "realize: the query returns its answer encoded by{indentExpr out}\n\
        but the goal requires{indentExpr o}"
  return out

/-- The native comparison of a word condition, equality or `<`, with its operands. -/
private def cond? (c : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (ty, a, b) := c.eq? then
    if (← whnfR ty).isConstOf ``Nat then return some (``Cond.eq, a, b)
  if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 2, c.getArg! 3)
  if c.isAppOfArity ``GT.gt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 3, c.getArg! 2)
  return none

/-- The comparison of a branch condition: equality or `<`, with its operands. -/
private def parseCond (c : Expr) : MetaM (Name × Expr × Expr) := do
  if let some r ← cond? c then return r
  throwError "realize: a branch condition must be `a = b`, `a < b` or `a > b` on words, \
    got{indentExpr c}"

/-- The comparison of a loop guard, after unfolding definitions. `a = b`, `a < b` and `a > b`
are tested as written. `a ≠ 0` is tested as `0 < a`; the flag records this rewriting. -/
private partial def parseGuard (g : Expr) (orig : Expr := g.headBeta) (fuel : Nat := 64) :
    MetaM (Name × Expr × Expr × Bool) := do
  let g := g.headBeta
  if let some (kind, a, b) ← cond? g then return (kind, a, b, false)
  if let some (ty, a, z) := g.ne?.orElse fun _ => g.not?.bind Expr.eq? then
    if (← whnfR ty).isConstOf ``Nat && (← withNewMCtxDepth (isDefEq z (mkNatLit 0))) then
      return (``Cond.lt, z, a, true)
  if fuel != 0 then
    let g' ← whnfR g
    if g' != g then return ← parseGuard g' orig (fuel - 1)
    if let some g' ← unfoldDefinition? g then return ← parseGuard g' orig (fuel - 1)
  throwError "realize: a loop guard must be `a = b`, `a < b`, `a > b` or `a ≠ 0` on words, \
    got{indentExpr orig}"

/-- Rebuild a branch condition with new operands. -/
private def rebuildCond (c a b : Expr) : MetaM Expr := do
  if c.isEq then mkEq a b
  else if c.isAppOfArity ``LT.lt 4 then mkAppM ``LT.lt #[a, b]
  else mkAppM ``GT.gt #[b, a]

/-- Whether the head is a client form `realize` handles directly. -/
private def isClientForm (e : Expr) : Bool :=
  e.isAppOfArity ``Bind.bind 6 || e.isAppOfArity ``PFunctor.FreeM.bind 5 ||
  e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``PFunctor.FreeM.pure 3 ||
  e.isAppOfArity ``PFunctor.FreeM.lift 2 || e.isAppOfArity ``PFunctor.FreeM.liftBind 4 ||
  e.isAppOfArity ``ite 5 || e.isAppOfArity ``boundedWhile 8

/-- Unfold definitions until a client form appears. -/
private partial def normBody (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let e ← whnfR e
  if isClientForm e || fuel == 0 then return e
  if let some e' ← unfoldDefinition? e then return ← normBody e'.headBeta (fuel - 1)
  return e

/-- An optional answer that a `match` in the client inspects: a discriminant of an `Option` type
that depends on the environment variable `d`. -/
private def optionDiscr? (d body : Expr) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  let found ← IO.mkRef (none : Option Expr)
  let _ ← Meta.transform body (pre := fun e => do
    if (← found.get).isSome then return .done e
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      for r in app.discrs do
        if r.containsFVar d.fvarId! &&
            (r.find? fun x => x.isFVar && !lctx.contains x.fvarId!).isNone then
          if (← whnfR (← inferType r)).isAppOfArity ``Option 1 then
            found.set (some r)
            return .done e
    return .continue)
  found.get

/-- Prove `∀ d, rhs = body` by a case split on the optional answer `r`. -/
private def proveSplit (d r ty : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar ty
  let (dfv, g) ← mvar.mvarId!.intro1
  let r' := r.replaceFVar d (mkFVar dfv)
  let (zs, g) ← g.generalize #[{ expr := r', xName? := `z }]
  for sg in ← g.cases zs[0]! do sg.mvarId.refl
  instantiateMVars mvar

/-- `∀ x s, 1 ≤ memoryCost (body x) s` for a loop body that begins with a query. -/
private def proveQuery (body ty : Expr) : MetaM Expr :=
  withLocalDeclD `x ty fun x => withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let b ← whnf (mkApp body x)
    unless b.isAppOfArity ``PFunctor.FreeM.liftBind 4 do
      throwError "realize: a loop body must begin with a memory query, which pays for the \
        iteration;\nthe body begins with{indentExpr b}"
    let pf ← mkAppM ``one_le_memoryCost_liftBind #[b.getArg! 2, b.getArg! 3, s]
    let goal ← mkAppM ``LE.le #[mkNatLit 1, ← mkAppM ``memoryCost #[mkApp body x, s]]
    mkLambdaFVars #[x, s] (← mkExpectedTypeHint pf goal)

/-- State `out.proof` as the certificate `Realizes[At n c] B prog input output safe 0`, for the
client `prog` as written and the domain `safe` in the client's terms. -/
private def certify (ctx : Ctx) (env : Env) (out : Out) (prog : Expr) : MetaM Out := do
  let expected ← if ctx.graded then
      mkAppM ``RealizesAt #[mkNatLit out.n, mkNatLit out.c, ctx.basis, prog, env.input,
        out.output, out.safe, ← zeroWork env.ty]
    else
      mkAppM ``Realizes #[ctx.basis, prog, env.input, out.output, out.safe, ← zeroWork env.ty]
  return { out with proof := ← mkExpectedTypeHint out.proof expected }

/-- `Realizes[At].bind₀_of_run hP hQ reply next`, with the reply and next memory `fun d s => …`
proved by `rfl`. -/
private def bindRun (ctx : Ctx) (hP hQ : Out) (l : Nat) (reply next : Expr) :
    MetaM (Nat × Nat × Expr) := do
  let refl (f : Expr) : MetaM Expr :=
    lambdaBoundedTelescope f 2 fun xs b => do mkLambdaFVars xs (← mkEqRefl b)
  let fn := if ctx.graded then ``RealizesAt.bind₀_of_run else ``Realizes.bind₀_of_run
  let pf ← mkAppM fn #[hP.proof, hQ.proof, reply, next, ← refl reply, ← refl next]
  return (hQ.n + l + hP.n + 1, hP.c + hQ.c, pf)

/-- Expose pair projections to unification when a certificate packages curried arguments.
Other types remain whole metavariables: no data constructor or runtime value is guessed. -/
private partial def callArgument (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if let some (a, b) := ty.app2? ``Prod then
    return mkAppN (mkConst ``Prod.mk ty.getAppFn.constLevels!)
      #[a, b, ← callArgument a, ← callArgument b]
  if let some (a, b) := ty.app2? ``Sigma then
    let x ← callArgument a
    return mkAppN (mkConst ``Sigma.mk ty.getAppFn.constLevels!)
      #[a, b, x, ← callArgument (b.beta #[x])]
  mkFreshExprMVar ty

/-- Reuse a local method certificate before unfolding its body. Every input word must already
be live: `reindex` supplies static wiring, without granting argument computation. -/
private def tryRealizeCall (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM (Option Out) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let isAt := ty.isAppOfArity ``RealizesAt 12
    let isPlain := ty.isAppOfArity ``Realizes 10
    unless (ctx.graded && isAt) || (!ctx.graded && isPlain) do continue
    let saved ← saveState
    try
      let args := ty.getAppArgs
      let off := if isAt then 2 else 0
      let (nCall, cCall) ← if isAt then
          let some n ← (evalNat (← whnf args[4]!)).run
            | throwError "realize: non-numeral scratch bound"
          let some c ← (evalNat (← whnf args[5]!)).run
            | throwError "realize: non-numeral factor bound"
          pure (n, c)
        else pure (0, 0)
      unless ← withReducible (isDefEq args[4 + off]! ctx.basis) do
        throwError "realize: the method's basis differs"
      unless ← withReducible (isDefEq args[9 + off]! (← zeroWork args[2]!)) do
        throwError "realize: a called certificate must have absorbed local work"
      let arg ← callArgument args[2]!
      let called := (mkApp args[5 + off]! arg).headBeta
      let matched ← if called.getAppFn == body.getAppFn &&
          called.getAppNumArgs == body.getAppNumArgs then
          (called.getAppArgs.zip body.getAppArgs).allM fun (a, b) => do
            withReducible (isDefEq (← whnfR a) (← whnfR b))
        else withReducible (isDefEq called body)
      unless matched do
        throwError "realize: the method does not match"
      let arg ← instantiateMVars arg
      if arg.hasMVar then throwError "realize: the method argument is undetermined"
      let out ← checkOutput decl.toExpr output?
      let k ← encodingWidth args[6 + off]!
      let coords ← encodingAtoms args[6 + off]! arg k
      let positions ← coords.mapM fun a => do
        let some i ← findAtom atoms a
          | throwError "realize: a method argument must first be computed into a live word"
        pure i
      let finK := mkApp (mkConst ``Fin) (mkNatLit k)
      let finEnv := mkApp (mkConst ``Fin) (mkNatLit env.k)
      let rec indices : List Nat → MetaM Expr
        | [] => mkAppOptM ``Matrix.vecEmpty #[finEnv]
        | i :: is => do mkAppM ``Matrix.vecCons #[← finLit env.k i, ← indices is]
      let ix ← indices positions.toList
      let f ← mkLambdaFVars #[d] arg
      let hwTy ← withLocalDeclD `e env.ty fun e => withLocalDeclD `i finK fun i => do
        let lhs := mkApp (← mkAppM ``DFunLike.coe #[args[6 + off]!, f.beta #[e]]) i
        let rhs := mkApp (← mkAppM ``DFunLike.coe #[env.input, e]) (mkApp ix i)
        mkForallFVars #[e, i] (← mkEq lhs rhs)
      let hw ← proveResult hwTy k
      let reindexFn := if isAt then ``RealizesAt.reindex else ``Realizes.reindex
      let proof ← mkAppM reindexFn #[decl.toExpr, f, env.input, ix, hw]
      let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
        withLocalDeclD `s (mkConst ``Memory.State) fun s => do
          mkLambdaFVars #[w, d, s] (← reducePairs (mkApp3 args[8 + off]! w arg s))
      return some { n := nCall, c := cCall, proof, output := out, safe }
    catch _ => saved.restore
  return none

mutual

/-- Certify a client `prog : δ → Memory.Prog α` in the environment `env`. -/
private partial def realizeProg (ctx : Ctx) (env : Env) (prog : Expr) (output? : Option Expr) :
    TermElabM Out :=
  withLocalDeclD `d env.ty fun d => do
    let atoms := env.atoms.map (·.beta #[d])
    if let some out ← tryRealizeCall ctx env d atoms (prog.beta #[d]).headBeta output? then
      return ← certify ctx env out prog
    let body ← normBody (prog.beta #[d]).headBeta
    let out ← realizeBody ctx env d atoms body output?
    certify ctx env out prog

/-- Certify the body of a client for the environment variable `d`. -/
private partial def realizeBody (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let k := env.k
  -- sequencing
  let bind? : Option (Expr × Expr) :=
    if body.isAppOfArity ``Bind.bind 6 then some (body.getArg! 4, body.getArg! 5)
    else if body.isAppOfArity ``PFunctor.FreeM.bind 5 then some (body.getArg! 3, body.getArg! 4)
    else none
  if let some (m, f) := bind? then return ← realizeBind ctx env d m f output?
  if body.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    let m ← mkAppOptM ``PFunctor.FreeM.lift #[body.getArg! 0, body.getArg! 2]
    return ← realizeBind ctx env d m (body.getArg! 3) output?
  -- return
  let pure? : Option Expr :=
    if body.isAppOfArity ``Pure.pure 4 then some body.appArg!
    else if body.isAppOfArity ``PFunctor.FreeM.pure 3 then some body.appArg!
    else none
  if let some a := pure? then
    let out ← match output? with
      | some o => pure o
      | none => encodingOf (← resultType body)
    return ← realizePure ctx env d atoms a out
  -- memory queries
  if body.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR body.appArg!
    let operands := op.getAppArgs
    for h : j in [0:operands.size] do
      if (← findAtom atoms operands[j]).isNone then
        let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
          mkLambdaFVars #[r] (mkApp2 (mkConst ``PFunctor.FreeM.lift
            body.getAppFn.constLevels!) (body.getArg! 0) (mkAppN op.getAppFn (operands.set j r)))
        return ← realizeBody ctx env d atoms (← bindPure operands[j] rebuilt) output?
    let idx ← operands.mapM fun a => do
      let some i ← findAtom atoms a | throwError "realize: internal error"
      finLit k i
    let input := env.input
    let kE := mkNatLit k
    let (nQ, cQ, proof) ← match op.getAppFn.constName? with
      | some ``Memory.Op.read =>
        let fn := if ctx.graded then ``RealizesAt.read else ``Realizes.read
        pure (0, 2, ← mkAppOptM fn #[ctx.basis, env.ty, kE, input, idx[0]!])
      | some ``Memory.Op.write =>
        let fn := if ctx.graded then ``RealizesAt.write else ``Realizes.write
        pure (0, 2, ← mkAppOptM fn #[ctx.basis, env.ty, kE, input, idx[0]!, idx[1]!])
      | some ``Memory.Op.alloc =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `Realizes.mapSimulates`"
        let fn := if ctx.graded then ``RealizesAt.alloc else ``Realizes.alloc
        pure (2, 6, ← mkAppOptM fn #[env.ty, kE, input, idx[0]!])
      | some ``Memory.Op.allocDirty =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `Realizes.mapSimulates`"
        let fn := if ctx.graded then ``RealizesAt.allocDirty else ``Realizes.allocDirty
        pure (1, 3, ← mkAppOptM fn #[env.ty, kE, input, idx[0]!])
      | _ => throwError "realize: unsupported memory operation{indentExpr op}"
    let output ← checkOutput proof output?
    return { n := nQ, c := cQ, proof, output, safe := ← trueSafe env.ty }
  -- branching
  if body.isAppOfArity ``ite 5 then
    let c := body.getArg! 1
    let inst := body.getArg! 2
    let t := body.getArg! 3
    let e := body.getArg! 4
    let (kind, a, b) ← parseCond c
    let ia? ← findAtom atoms a
    let ib? ← findAtom atoms b
    let (some ia, some ib) := (ia?, ib?) | do
      let x := if ia?.isNone then a else b
      let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
        let c' ← if ia?.isNone then rebuildCond c r b else rebuildCond c a r
        mkLambdaFVars #[r] (← mkAppM ``ite #[c', t, e])
      return ← realizeBody ctx env d atoms (← bindPure x rebuilt) output?
    let out ← match output? with
      | some o => pure o
      | none => encodingOf (← resultType body)
    let hp ← realizeProg ctx env (← mkLambdaFVars #[d] t) (some out)
    let hn ← realizeProg ctx env (← mkLambdaFVars #[d] e) (some out)
    let cond ← mkAppM kind #[← finLit k ia, ← finLit k ib]
    let branchFn := if ctx.graded then ``RealizesAt.branch₀ else ``Realizes.branch₀
    let proof ← mkAppM branchFn #[cond, hp.proof, hn.proof]
    let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        mkLambdaFVars #[w, d, s] (mkApp5 (mkConst ``ite [Level.one]) (mkSort Level.zero) c inst
          (hp.safe.beta #[w, d, s]) (hn.safe.beta #[w, d, s]))
    return { n := max hp.n hn.n, c := max hp.c hn.c + 2, proof, output := out, safe }
  -- a guarded loop
  if body.isAppOfArity ``boundedWhile 8 then
    return ← realizeWhile ctx env d atoms body output?
  -- a runtime-bounded loop
  if body.isAppOfArity ``iterate 6 then
    return ← realizeIterate ctx env d atoms (body.getArg! 1) (body.getArg! 2) (body.getArg! 3)
      (body.getArg! 4) (body.getArg! 5) output?
  -- a `match` on an optional answer becomes a test of its presence tag
  let body ← Core.betaReduce body
  if let some r ← optionDiscr? d body then
    return ← realizeOptionSplit ctx env d atoms body r output?
  throwError "realize: unsupported client form{indentExpr body}\n\
    Expected `bind`, `pure`, a memory query, `if` on a word comparison,\n\
    a `match` on an optional answer, `iterate` or `boundedWhile`.\n\
    Write recursion on a runtime value as one of these loops."

/-- Certify a client that matches on the optional answer `r`: it equals the branch on `r`'s
presence tag, with `r` replaced by `none` and by `some` of its payload. -/
private partial def realizeOptionSplit (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body r : Expr) (output? : Option Expr) : TermElabM Out := do
  let rTy ← whnfR (← inferType r)
  let enc ← encodingOf rTy
  let words ← mkAppM ``DFunLike.coe #[enc, r]
  let l ← encodingWidth enc
  let payloadTy ← whnfR rTy.appArg!
  let payload ← if payloadTy.isConstOf ``Nat then
      unless l == 2 do
        throwError "realize: expected a tag and payload encoding for{indentExpr r}"
      pure (mkApp words (← finLit l 1))
    else if let some (a, b) := payloadTy.app2? ``Prod then
      unless (← whnfR a).isConstOf ``Nat && (← whnfR b).isConstOf ``Nat do
        throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
      unless l == 3 do
        throwError "realize: expected a tag and two payload words for{indentExpr r}"
      mkAppM ``Prod.mk #[mkApp words (← finLit l 1), mkApp words (← finLit l 2)]
    else
      throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
  let tag := mkApp words (← finLit l 0)
  let cond ← mkEq tag (← mkNumeral (mkConst ``Nat) 0)
  let noneE ← mkAppOptM ``Option.none #[rTy.appArg!]
  let someE ← mkAppM ``Option.some #[payload]
  let bodyNone := body.replace fun e => if e == r then some noneE else none
  let bodySome := body.replace fun e => if e == r then some someE else none
  let rhs ← mkAppM ``ite #[cond, bodyNone, bodySome]
  let eq ← proveSplit d r (← mkForallFVars #[d] (← mkEq rhs body))
  let out ← realizeBody ctx env d atoms rhs output?
  let out ← certify ctx env out (← mkLambdaFVars #[d] rhs)
  let congrFn := if ctx.graded then ``RealizesAt.congr else ``Realizes.congr
  let proof ← mkAppM congrFn #[out.proof, eq]
  return { out with proof }

/-- Certify `iterate step D n a`: copy the initial state and the fuel, then run the loop over the
whole environment (`iterate_comap`). The body must begin with a query (`iterate₀`). -/
private partial def realizeIterate (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (σ step D n a : Expr) (output? : Option Expr) : TermElabM Out := do
  unless ctx.exact do throwError "realize: loops are certified in the exact basis"
  let out ← match output? with
    | some o => pure o
    | none => encodingOf σ
  let l ← encodingWidth out
  let envB ← extend env σ out l
  let captured := step.containsFVar d.fvarId!
  let body ← if D == d && !captured then pure step else
    withLocalDeclD `x envB.ty fun x => do
      let x1 ← mkAppM ``Prod.fst #[x]
      let x2 ← mkAppM ``Prod.snd #[x]
      let Dx := (← mkLambdaFVars #[d] D).beta #[x1]
      mkLambdaFVars #[x] (mkApp (step.replaceFVar d x1) (← mkAppM ``Prod.mk #[Dx, x2]))
  let hB ← realizeProg ctx envB body (some out)
  let hq ← proveQuery body envB.ty
  let iterFn := if ctx.graded then ``RealizesAt.iterate₀ else ``Realizes.iterate₀
  let hLoopPf ← mkAppM iterFn #[env.input, out, hB.proof, hq]
  let hLoop : Out :=
    { n := l + hB.n + 3, c := (hB.c + 2 * l + 8) * 2, proof := hLoopPf, output := out,
      safe := default }
  let hN ← withLocalDeclD `x envB.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let nx := (← mkLambdaFVars #[d] n).beta #[x1]
    let word ← encodingOf (mkConst ``Nat)
    let atomsX := envB.atoms.map (·.beta #[x])
    realizePure ctx envB x atomsX nx word
  let hA ← realizePure ctx env d atoms a out
  let (nReply, nNext) ← withLocalDeclD `x envB.ty fun x =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let nx := (← mkLambdaFVars #[d] n).beta #[← mkAppM ``Prod.fst #[x]]
      return (← mkLambdaFVars #[x, s] nx, ← mkLambdaFVars #[x, s] s)
  let (n2, c2, h2Pf) ← bindRun ctx hN hLoop 1 nReply nNext
  let h2 : Out := { n := n2, c := c2, proof := h2Pf, output := out, safe := default }
  let (aReply, aNext) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    return (← mkLambdaFVars #[d, s] a, ← mkLambdaFVars #[d, s] s)
  let (nFinal, cFinal, proof) ← bindRun ctx hA h2 l aReply aNext
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, a]
      let sn ← reducePairs (hN.safe.beta #[w, pair, s])
      let sl ← mkAppM ``iterationSafe #[body, hB.safe, w, d, n, a, s]
      mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let progR ← mkLambdaFVars #[d] (← mkAppM ``iterate #[body, d, n, a])
  let outR ← certify ctx env { n := nFinal, c := cFinal, proof, output := out, safe } progR
  if D == d && !captured then return outR
  let g ← mkLambdaFVars #[d] D
  let eq ← if captured then do
    let ty ← withLocalDeclD `n (mkConst ``Nat) fun n => withLocalDeclD `a σ fun a => do
      mkForallFVars #[n, a] (← mkEq (← mkAppM ``iterate #[body, d, n, a])
        (← mkAppM ``iterate #[step, D, n, a]))
    let h ← Term.withSynthesize <| Term.elabTermEnsuringType (← `(by
      intro n a
      induction n generalizing a with
      | zero => rfl
      | succ n ih =>
        simp only [iterate]
        congr 1
        funext b
        exact ih b)) (some ty)
    mkLambdaFVars #[d] (mkApp2 (← instantiateMVars h) n a)
  else
    mkLambdaFVars #[d] (← mkEqSymm (← mkAppM ``iterate_comap #[g, step, d, n, a]))
  let congrFn := if ctx.graded then ``RealizesAt.congr else ``Realizes.congr
  let proof ← mkAppM congrFn #[outR.proof, eq]
  if !captured then return { outR with proof }
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  let pairTy ← mkAppM ``Prod #[← inferType D, σ]
  let clientSafe ← withLocalDeclD `w nat fun w =>
    withLocalDeclD `x pairTy fun x =>
      withLocalDeclD `s state fun s => do
        let pair ← mkAppM ``Prod.mk #[d, ← mkAppM ``Prod.snd #[x]]
        mkLambdaFVars #[w, x, s] (← reducePairs (hB.safe.beta #[w, pair, s]))
  let safe' ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reducePairs (hN.safe.beta #[w, pair, s])
    let sl ← mkAppM ``iterationSafe #[step, clientSafe, w, D, n, a, s]
    mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let pointwise ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let ty ← withLocalDeclD `n nat fun n => withLocalDeclD `a σ fun a =>
      withLocalDeclD `s state fun s => do
        mkForallFVars #[n, a, s] (← mkEq
          (← mkAppM ``iterationSafe #[body, hB.safe, w, d, n, a, s])
          (← mkAppM ``iterationSafe #[step, clientSafe, w, D, n, a, s]))
    let h ← Term.withSynthesize <| Term.elabTermEnsuringType (← `(by
      intro n a s
      induction n generalizing a s with
      | zero => rfl
      | succ n ih =>
        simp only [iterationSafe]
        congr 1
        exact ih _ _)) (some ty)
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reducePairs (hN.safe.beta #[w, pair, s])
    let wrap ← withLocalDeclD `p (mkSort Level.zero) fun p =>
      mkLambdaFVars #[p] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn p))
    mkLambdaFVars #[w, d, s] (← mkAppM ``congrArg
      #[wrap, mkApp3 (← instantiateMVars h) n a s])
  let safeEq ← withLocalDeclD `w nat fun w => do
    let hd ← withLocalDeclD `e env.ty fun e => do
      mkLambdaFVars #[e] (← mkAppM ``funext #[mkApp2 pointwise w e])
    mkLambdaFVars #[w] (← mkAppM ``funext #[hd])
  let safeEq ← mkAppM ``funext #[safeEq]
  let proofTy ← inferType proof
  let safeIdx := if ctx.graded then 10 else 8
  let wrap ← withLocalDeclD `safe (← inferType safe) fun s =>
    mkLambdaFVars #[s] (mkAppN proofTy.getAppFn (proofTy.getAppArgs.set! safeIdx s))
  let proof ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[wrap, safeEq], proof]
  return { outR with proof, safe := safe' }

/-- Certify `boundedWhile G step D n a` for the environment variable `d`. -/
private partial def realizeWhile (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let args := body.getAppArgs
  let (Δ, σ, G, inst, step, D, n, a) :=
    (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
  let out ← match output? with
    | some o => pure o
    | none => encodingOf σ
  let l ← encodingWidth out
  let k := env.k
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  let (kind, posA, posB, pre?, neFn?) ← withLocalDeclD `a σ fun x => do
    let (kind, oa, ob, ne) ← parseGuard (mkApp2 G D x)
    let words := atoms ++ (← encodingAtoms out x l)
    let locate (o : Expr) : MetaM (Option Nat) := do
      if let some i ← findAtom words o then return some i
      if o.containsFVar x.fvarId! then
        throwError "realize: a loop guard compares words; the operand{indentExpr o}\n\
          depends on the loop state but is not one of its words"
      return none
    let (ia, ib) := (← locate oa, ← locate ob)
    let pre? ← match ia, ib with
      | none, none => throwError "realize: the loop guard{indentExpr (mkApp2 G D x)}\n\
          does not depend on the loop state"
      | none, _ => pure (some oa)
      | _, none => pure (some ob)
      | _, _ => pure none
    let neFn? ← if ne then pure (some (← mkLambdaFVars #[x] ob)) else pure none
    return (kind, ia, ib, pre?, neFn?)
  let word ← encodingOf nat
  let envP ← if pre?.isSome then extend env nat word 1 else pure env
  let cmp := envP.k + l
  let pos (i? : Option Nat) : MetaM Expr := finLit cmp <| match i? with
    | none => k
    | some i => if i < k || pre?.isNone then i else i + 1
  let cond ← mkAppM kind #[← pos posA, ← pos posB]
  let atEnv (X e : Expr) : MetaM Expr := do
    return X.replaceFVar d (← if pre?.isSome then mkAppM ``Prod.fst #[e] else pure e)
  let envB ← extend envP σ out l
  let (bodyN, cutoff) ← withLocalDeclD `y envB.ty fun y => do
    let e ← mkAppM ``Prod.fst #[y]
    let x ← mkAppM ``Prod.mk #[← atEnv D e, ← mkAppM ``Prod.snd #[y]]
    return (← mkLambdaFVars #[y] (mkApp (← atEnv step e) x), ← mkLambdaFVars #[y] (← atEnv n e))
  let hB ← realizeProg ctx envB bodyN (some out)
  let whileFn := if ctx.graded then ``RealizesAt.while₀ else ``Realizes.while₀
  let hLoopPf ← mkAppM whileFn
    #[envP.input, out, cond, cutoff, hB.proof, ← proveQuery bodyN envB.ty]
  let hLoop : Out :=
    { n := l + hB.n + 1, c := (hB.c + 2 * l + 4) * 2, proof := hLoopPf, output := out,
      safe := default }
  let (hA, h) ← withLocalDeclD `e envP.ty fun e => do
    let ae ← atEnv a e
    let hA ← realizePure ctx envP e (envP.atoms.map (·.beta #[e])) ae out
    let (reply, next) ← withLocalDeclD `s state fun s => do
      return (← mkLambdaFVars #[e, s] ae, ← mkLambdaFVars #[e, s] s)
    let (na, ca, haPf) ← bindRun ctx hA hLoop l reply next
    return (hA, ({ n := na, c := ca, proof := haPf, output := out, safe := default } : Out))
  let (hC?, h, e₀) ← match pre? with
    | none => pure (none, h, d)
    | some c => do
      let hC ← realizePure ctx env d atoms c word
      let (reply, next) ← withLocalDeclD `s state fun s => do
        return (← mkLambdaFVars #[d, s] c, ← mkLambdaFVars #[d, s] s)
      let (nc, cc, hcPf) ← bindRun ctx hC h 1 reply next
      pure (some hC, { h with n := nc, c := cc, proof := hcPf }, ← mkAppM ``Prod.mk #[d, c])
  let (gN, iN) ← withLocalDeclD `e envP.ty fun e => withLocalDeclD `a σ fun x => do
    let words ← mkAppM ``DFunLike.coe
      #[← mkAppM ``appendWords #[envP.input, out], ← mkAppM ``Prod.mk #[e, x]]
    let t ← mkAppM ``test #[cond, words]
    return (← mkLambdaFVars #[e, x] t,
      ← mkLambdaFVars #[e, x] (← synthInstance (← mkAppM ``Decidable #[t])))
  let (hgU, hgN, hbU, hbN) ← withLocalDeclD `a σ fun x => do
    let gU := mkApp2 G D x
    let gn := mkApp2 gN e₀ x
    let iff ← match neFn? with
      | some f => mkAppM ``Iff.symm #[← mkAppOptM ``Nat.pos_iff_ne_zero #[f.beta #[x]]]
      | none => mkAppM ``Iff.refl #[gU]
    let hgU ← mkExpectedTypeHint iff (mkApp2 (mkConst ``Iff) gU gn)
    let bU := mkApp step (← mkAppM ``Prod.mk #[D, x])
    let bN := mkApp bodyN (← mkAppM ``Prod.mk #[e₀, x])
    let hbU ← mkExpectedTypeHint (← mkEqRefl bU) (← mkEq bU bN)
    return (← mkLambdaFVars #[x] hgU, ← mkLambdaFVars #[x] (← mkAppM ``Iff.symm #[hgU]),
      ← mkLambdaFVars #[x] hbU, ← mkLambdaFVars #[x] (← mkEqSymm hbU))
  let progIdx := if ctx.graded then 7 else 5
  let prog := (← instantiateMVars (← inferType h.proof)).getArg! progIdx
  let eq ← mkLambdaFVars #[d] (← mkExpectedTypeHint
    (← mkAppOptM ``boundedWhile_congr #[envP.ty, Δ, σ, gN, iN, G, inst, bodyN, step, e₀, D,
      hgN, hbN, n, a])
    (← mkEq (mkApp prog d) body))
  let congrFn := if ctx.graded then ``RealizesAt.congr else ``Realizes.congr
  let hPf ← mkAppM congrFn #[h.proof, eq]
  let pairTy ← mkAppM ``Prod #[Δ, σ]
  let safeB ← withLocalDeclD `w nat fun w => withLocalDeclD `x pairTy fun x =>
    withLocalDeclD `s state fun s => do
      let y ← mkAppM ``Prod.mk #[e₀, ← mkAppM ``Prod.snd #[x]]
      mkLambdaFVars #[w, x, s] (← reducePairs (hB.safe.beta #[w, y, s]))
  let safe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let spec ← mkAppM ``Memory.spec #[w]
    let valid ← mkAppM ``StateTransitionSpec.ValidHistory
      #[spec, s, ← mkAppM ``StateTransitionSpec.clientHistory #[spec, s, body]]
    let loop ← mkArrow valid
      (← mkAppOptM ``whileSafe #[Δ, σ, G, inst, step, safeB, w, D, n, a, s])
    let dom := mkAnd (← reducePairs (hA.safe.beta #[w, e₀, s])) loop
    mkLambdaFVars #[w, d, s] <| match hC? with
      | some hC => mkAnd (hC.safe.beta #[w, d, s]) dom
      | none => dom
  let cv ← if ctx.graded then
      mkAppM ``RealizesAt.consequence_valid #[safe, hPf]
    else
      mkAppOptM ``Realizes.consequence_valid
        #[none, none, none, none, none, none, none, none, none, none, safe, hPf]
  let hsafeTy := (← whnf (← inferType cv)).bindingDomain!
  let hsafe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    forallBoundedTelescope (← instantiateForall hsafeTy #[w, d, s]) (some 4) fun hs goal => do
      let #[_, _, hv, hd] := hs | throwError "realize: internal error in the loop domain"
      let part (h : Expr) : MetaM (Expr × Expr) := do
        return (← mkAppM ``And.left #[h], ← mkAppM ``And.right #[h])
      let (hcs, rest) ← match hC? with
        | some _ => do let (p, q) ← part hd; pure (some p, q)
        | none => pure (none, hd)
      let (has, hloop) ← part rest
      let hsU ← withLocalDeclD `a σ fun x => withLocalDeclD `s state fun s' =>
        withLocalDeclD `hg (mkApp2 G D x) fun hg => do
          let hs := mkApp3 safeB w (← mkAppM ``Prod.mk #[D, x]) s'
          withLocalDeclD `h hs fun hh => do
            let hN := mkApp3 hB.safe w (← mkAppM ``Prod.mk #[e₀, x]) s'
            mkLambdaFVars #[x, s', hg, hh] (← mkExpectedTypeHint hh hN)
      let ws ← mkAppOptM ``whileSafe_imp #[Δ, envP.ty, σ, G, inst, gN, iN, step, bodyN, D, e₀,
        safeB, hB.safe, w, hgU, hbU, hsU, none, none, none, mkApp hloop hv]
      let dom ← mkAppM ``And.intro #[has, ws]
      let pf ← match hcs with
        | some p => mkAppM ``And.intro #[p, dom]
        | none => pure dom
      mkLambdaFVars (#[w, d, s] ++ hs) (← mkExpectedTypeHint pf goal)
  return { n := h.n, c := h.c, proof := mkApp cv hsafe, output := out, safe }

/-- Certify `bind m f`: the first client, then the continuation over the extended environment. -/
private partial def realizeBind (ctx : Ctx) (env : Env) (d m f : Expr) (output? : Option Expr) :
    TermElabM Out := do
  let α ← resultType m
  let hP ← realizeProg ctx env (← mkLambdaFVars #[d] m) none
  let l ← encodingWidth hP.output
  let env' ← extend env α hP.output l
  let fd ← mkLambdaFVars #[d] f
  let q ← withLocalDeclD `x env'.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    mkLambdaFVars #[x] (fd.beta #[x1, x2]).headBeta
  let hQ ← realizeProg ctx env' q output?
  let (reply, next) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let (r, s') ← replyState m s
    return (← mkLambdaFVars #[d, s] r, ← mkLambdaFVars #[d, s] s')
  let (nBind, cBind, proof) ← bindRun ctx hP hQ l reply next
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, reply.beta #[d, s]]
      let sq ← reducePairs (hQ.safe.beta #[w, pair, next.beta #[d, s]])
      mkLambdaFVars #[w, d, s] (mkAnd (hP.safe.beta #[w, d, s]) sq)
  return { n := nBind, c := cBind, proof, output := hQ.output, safe }

end

/-- Split the conjunctions and `if`s of a synthesized domain into separate goals. -/
private partial def splitDomain (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if t.isAppOfArity ``And 2 then
    let [g₁, g₂] ← g.apply (mkConst ``And.intro) | throwError "realize: internal split error"
    return (← splitDomain g₁) ++ (← splitDomain g₂)
  if t.isAppOfArity ``ite 5 then
    let c := t.getArg! 1
    let (gpos, gneg) ← g.byCases c `hc
    let pos ← gpos.mvarId.withContext do
      let eq ← mkAppOptM ``if_pos
        #[c, t.getArg! 2, mkFVar gpos.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gpos.mvarId.replaceTargetEq (t.getArg! 3) eq
    let neg ← gneg.mvarId.withContext do
      let eq ← mkAppOptM ``if_neg
        #[c, t.getArg! 2, mkFVar gneg.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gneg.mvarId.replaceTargetEq (t.getArg! 4) eq
    return (← splitDomain pos) ++ (← splitDomain neg)
  return [g]

end Cslib.Tactic.Realize

namespace Cslib.WordRAM

open Lean Meta Elab Tactic Cslib.WordRAM Cslib.WordRAM.Realization Cslib.Tactic.Realize in
/-- Prove `Realizes B p input output safe work` or `RealizesAt n C B p input output safe work`
for a memory client `p`, leaving the genuine fit and domain conditions as goals in the context
`w d s hwords hmem h`. -/
scoped elab "realize" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← whnfR (← goal.getType))
  let isAt := target.isAppOfArity ``RealizesAt 12
  let isPlain := target.isAppOfArity ``Realizes 10
  unless isAt || isPlain do
    throwError "realize: the goal is not a `Realizes` certificate:{indentExpr target}"
  let args := target.getAppArgs
  let off := if isAt then 2 else 0
  let δ := args[2]!
  let B := args[4 + off]!
  let p := args[5 + off]!
  let input := args[6 + off]!
  let output := args[7 + off]!
  let k ← encodingWidth input
  let exact ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.exact))
  let standard ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.standard))
  let atoms ← withLocalDeclD `d δ fun d => do
    (← encodingAtoms input d k).mapM (mkLambdaFVars #[d] ·)
  let env : Env := { ty := δ, k, input, atoms }
  let out ← realizeProg { basis := B, exact, standard, graded := isAt } env p (some output)
  let cons ← if isAt then
      let nGoal := args[4]!
      let cGoal := args[5]!
      let _ ← isDefEq nGoal (mkNatLit out.n)
      let _ ← isDefEq cGoal (mkNatLit out.c)
      let nGoal ← instantiateMVars nGoal
      let cGoal ← instantiateMVars cGoal
      let some nTarget ← (evalNat (← whnf nGoal)).run
        | throwError "realize: expected a numeral or metavariable for the scratch bound, \
            got{indentExpr nGoal}"
      let some cTarget ← (evalNat (← whnf cGoal)).run
        | throwError "realize: expected a numeral or metavariable for the factor bound, \
            got{indentExpr cGoal}"
      let pf ← if out.n == nTarget && out.c == cTarget then
          pure out.proof
        else
          let hn ← natLeProof out.n nTarget
          let hc ← natLeProof out.c cTarget
          mkAppM ``RealizesAt.mono #[hn, hc, out.proof]
      mkAppOptM ``RealizesAt.consequence #[B, args[0]!, args[1]!, δ, args[3]!,
        mkNatLit nTarget, mkNatLit cTarget, p, input, output, out.safe, ← zeroWork δ,
        args[10]!, args[11]!, pf]
    else
      mkAppOptM ``Realizes.consequence #[B, args[0]!, args[1]!, δ, args[3]!, p, input,
        output, out.safe, ← zeroWork δ, args[8]!, args[9]!, out.proof]
  let [hsafe, hwork] ← goal.apply cons | throwError "realize: internal error in `consequence`"
  setGoals [hwork]
  evalTactic (← `(tactic| exact fun _ _ => Nat.zero_le _))
  let (_, g) ← hsafe.introN 6 [`w, `d, `s, `hwords, `hmem, `h]
  let g ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let g ← g.replaceTargetDefEq (← Core.betaReduce t)
    let hdecl := (← getLCtx).lastDecl.get!
    g.replaceLocalDeclDefEq hdecl.fvarId (← Core.betaReduce hdecl.type)
  setGoals [g]
  evalTactic (← `(tactic|
    try simp only [true_and, and_true, and_self, Nat.add_zero, iterationSafe_true]))
  let gs ← getGoals
  let gs ← gs.flatMapM fun g => liftMetaM (splitDomain g)
  let mut kept : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let lctx := (← g.getDecl).lctx
    let dup? ← kept.findM? fun g' => do
      return (← g'.getDecl).lctx.getFVarIds == lctx.getFVarIds &&
        (← instantiateMVars (← g'.getType)) == t
    match dup? with
    | some g' => g.assign (mkMVar g')
    | none => kept := kept.push g
  setGoals kept.toList

end Cslib.WordRAM
