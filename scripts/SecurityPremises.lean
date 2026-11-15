/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Security premises about constructed objects, for `scripts/check_security_premises.py`

Run as `lake env lean --run scripts/SecurityPremises.lean <lib-dir> < modules.txt`, with one module
name per line on standard input. It reads the built `.olean` files (all three parts of a split
module) without importing them, so it sees elaborated statements: notation, `do` blocks, dot
notation and coercions are already resolved.

The scanned theorems are the public theorems of the listed modules, other than instances and
those Lean generates, that lie under `CslibFrontier.Crypto` or in the namespace `Cslib.Crypto`.

**Claims.** A hypothesis's *claim atoms* are what remains after its own `∀`s and premises, split
at `∧`, `∃` and `∀ᶠ`. An atom is a *security claim* of one of these kinds:

* `negligible`: `Negligible …`;
* `advantage`: an inequality `a ≤ b`, `a < b`, `a ≥ b` or `a > b` one of whose sides mentions an
  advantage, that is a constant whose last name component is `advantage` or `succProbability` or
  ends in `Advantage`;
* `member`: a membership `x ∈ S`, the shape of an adversary class `𝒟`, unless `S` is a support,
  range or interval (`ignoredContainers`), or a bound predicate applied to arguments, the shape of
  an abstract admissibility class `Admissible x`;
* `efficiency`: a predicate whose last name component starts with `IsPPT` or `IsOraclePPT`;
* `indistinguishable`: a predicate whose last name component contains `Indistinguishable`.

Its *subjects* are the explicit arguments of the predicate (all arguments when the predicate is not
a constant of the listed modules), both sides of the inequality, the element of the membership, or
the arguments of the bound predicate.
An atom of no kind headed by a Prop-valued definition of the listed modules is unfolded, at most
three times; there, only the constructed constants of the definition's arguments count (`unfolded`
kinds). So a notion applied to a constructed object, such as `Secure (reduction A)`, is seen, while
a named assumption such as `F.DDH setup` is not flagged, nor is a notion whose own definition builds
a fixed object of the framework (the dummy adversary of UC emulation).

**Constructed constants.** A constant `c` occurring in a subject, applied to `k` arguments, is
*constructed* when it is a definition (or opaque constant) of the scope above that is not a
structure projection, an instance or generated, whose last name component does not contain `game`
or `experiment` (any case) nor name an advantage, and whose type after `k` arguments, with type
synonyms of the listed modules unfolded, is

* a value whose type is not a distribution or game (`PMF`, `Game`), a number, `Bool`, a sort, `Set`
  or an embedding: so a program, a scheme or adversary structure, or a key;
* or a function whose final result is none of a number, `Bool`, `Prop` or an embedding (a
  predicate, test, numeric function or family of encodings), and which is not an ensemble or game
  family, a function of security parameters `ℕ → … → PMF _` or `→ Game`;
* or a distribution, game, ensemble or game family as above, when one of its `k` arguments is
  explicit and its domain is an *object type*: a type other than a sort, a type variable, a
  function type, a number, `Bool`, `Set`, `PMF` or `Game`, such as an adversary or scheme
  structure. So `simulatorView A`, with `simulatorView : Adversary → ℕ → PMF Bool`, is
  constructed.

Reductions, distinguishers (including `PMF`-valued and `Experiment`-valued ones), simulators,
extractors, key generators, schemes and adapters are constructed; games, experiments, advantages,
ideal laws, predicates and encodings are not. Bound variables (the input adversary, generic
components supplied by the caller) are never constants, so they never count.

**Known gaps.** Review covers these; the fixture in `scripts/test_check_security_premises.py`
pins each one.

* A distribution applied only to numbers or functions counts as infrastructure: a key law at
  fixed parameters (`keyLawOf 3`), or one applied to an adversary given as a function rather than
  a structure.
* A bound that mentions no advantage-named constant, such as `forgeExperiment (reduction A) 0 ≤ ε`,
  is not a security claim.
* A premise whose own definition builds the constructed object in its body, rather than taking it
  as an argument, is not seen.
* A caller-supplied object whose existence is what the theorem should prove (the extractor of a
  proof of knowledge) is a bound variable, so it never counts.
* A realization (below) stated other than as an equation, such as an inequality, a predicate of
  the library or a bundled certified program, or whose constructed side applies the constructed
  constant to no other variable of the theorem, is not seen.

Conversely, a named assumption instantiated at an object of the library, such as `DDH G` for a
group family `G` that the library defines, is flagged through its unfolding. Such a premise is
allowed by the rule and belongs in the baseline with its justification.

A *flagged premise* is a hypothesis with a security claim whose subjects mention a constructed
constant. The conclusion is flagged (as the binder `⊢`) when, under an `∃` reached through `∀` and
`∧`, an advantage inequality applies a constructed constant to an `∃`-bound variable, as in
`∃ m₀ m₁, Adv(A) ≤ Adv(B A m₀ m₁)`: the bound holds only for parameters chosen after the
adversary, so it is not a uniform reduction.

**Realizations.** A premise is also flagged, with the kind `realization`, when the theorem takes
the reduction from the caller as a variable `x` and assumes that `x` realizes the constructed
object. Another premise *certifies* `x`: it has an efficiency or membership claim whose subject is
`x` or a function that applies it (`hD : IsOraclePPT encBool D`, `IsPPTOn … (fun p => test p.1
p.2)`, `D ∈ 𝒟`). The flagged premise is an equation, under its own `∀`s, `∧`, `∃` and `∀ᶠ`, one
side of which mentions `x`; the other side does not, and applies a constructed constant to
another variable of the theorem, such as the adversary, whether or not another premise certifies
that variable too. For example, the Carter–Wegman theorems that #5347 deleted took `hreal : eval
(prfRealGame family D n) = (prfFnDist family n).bind (nonceFnDistinguisher (seed n) (hash n)
(forger n))` beside `hD`, which is flagged with the constant `nonceFnDistinguisher`. An equation
between variables only, such as a word program computing a caller's typed simulator, is not.

It prints one JSON line per theorem with a flagged premise or conclusion,
`{"n": theorem, "m": module, "l": line, "h": [{"b": binder, "k": [kinds], "c": [constructed
constants]}]}`, and finally `{"theorems": scanned, "modules": read, "missing": [modules without
build outputs]}`.

**Reductions.** With `--reductions` (`lake env lean --run scripts/SecurityPremises.lean
<lib-dir> --reductions`), for `scripts/check_reduction_witnesses.py`, it reports the explicit
reductions and their efficiency witnesses instead. Input lines `<dir>\t<module>` are context
modules as for `--assumptions`.

An *advantage bound* is a claim atom `a ≤ b`, `a < b`, a reversal of these, or `a = b` read as
`a ≤ b`, in the conclusion of a public scanned theorem, one side of which mentions an advantage.
A *reduction* is a constructed constant (above) of a scanned module that occurs on the bounding
side `b` of an advantage bound and not on the bounded side `a`, whose type finally yields a
*program* (a `ProbComp`, `OracleComp` or other `PFunctor.FreeM` computation, a `PMF`, or a
structure with such a field, nested at most two deep), and which is there applied to an argument
that mentions a *program variable* of the theorem that `a` mentions too: a variable whose type is
a computation with coins or oracles, a function into a computation other than an ensemble
`ℕ → … → PMF _`, or a structure of programs. So `B` is a reduction in
`Adv(scheme, A) ≤ Adv(problem, B A)`; `scheme`, `problem`, a key law and an attack applied to no
adversary are not.

An *efficiency witness* of a constant is a scanned theorem, private ones included, whose
conclusion has a claim atom headed by an efficiency certificate that mentions the constant: a
predicate whose last name component starts with `IsPPT`, `IsOraclePPT`, `IsTidyOraclePPT`,
`ComputableIn`, `ComputableTidilyIn`, `IsPolyTime`, `IsEfficient` or `Efficient`. A query bound
is not a certificate. A reduction is *certified* `direct`ly by its witnesses; as an `abbrev`
when it is reducible and every reduction-shaped constant of its body (a constructed constant of
a scanned module that finally yields a program) is certified; or through a `wrapper`, a
definition with a witness whose body mentions it, such as the word-level program that runs it.

It prints `{"n": reduction, "m": module, "l": line, "t": [theorems stating a bound with it],
"tm": [their modules], "k": "direct" | "abbrev" | "wrapper" | "", "w": [the witnesses,
abbreviated constants or wrappers]}` for each reduction, certified or not, and the same summary
line.

Known gaps of this mode, which review covers: a reduction written inline in the bound rather than
as a definition; a bound that mentions no advantage-named constant; a simulator or extractor on
the bounded side (`Adv(protocol, sim) ≤ …`) or outside any advantage bound; an attack, whose
bounded side mentions no program variable; a reduction that appears only in premises or proofs
(the premise scan above covers premises); and a `PMF`-valued distinguisher applied to all its
arguments when none of them is a structure, which the constructed-constant rule reads as a law
(first gap above). A witness is recognized by the constants its conclusion mentions, so a
certificate about a larger program that merely contains the reduction counts. Conversely a
scheme or protocol built from a component on the bounding side only, such as
`Adv(A) = Adv(toScheme S, B A)`, is reported as a reduction: the baseline exempts it.

**Named assumptions.** With `--assumptions` (`lake env lean --run scripts/SecurityPremises.lean
<lib-dir> --assumptions`), for `scripts/check_hardness_assumptions.py`, it reports the named
assumptions instead. A *named assumption* is a Prop-valued definition or `structure` whose
definition mentions negligibility, an advantage or indistinguishability (a constant whose last
name component is `Negligible`, names an advantage as above, or contains `Indistinguishable`),
directly or through other Prop-valued declarations, at most five deep. No declaration is excluded
by its name: generic notions such as `Game.Indistinguishable` are reported too, and the inventory
decides which of them are vocabulary. An input line `<dir>\t<module>` reads a *context* module,
such as one of CSLib's, from another build directory: its declarations are followed and reported,
but its theorems are not scanned. It prints
`{"a": assumption, "m": module, "l": line, "doc": docstring}` for each named assumption,
`{"t": theorem, "m": module, "l": line, "doc": docstring, "u": [assumptions]}` for each scanned
theorem whose premises' claim atoms are headed by named assumptions, and the same summary line.
-/
open Lean

namespace CslibFrontierScripts.SecurityPremises

/-- The last component of a name, or `""`. -/
def last (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

/-- Whether `s` is `pre` followed by digits, such as `eq_1`. -/
def numbered (pre s : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all Char.isDigit

/-- Whether a name, without its private prefix, is one Lean generates. -/
def isGenerated (n : Name) : Bool :=
  let n := privateToUserName n
  let s := last n
  n.isInternalDetail || n.hasMacroScopes || numbered "match_" s || numbered "proof_" s ||
    numbered "eq_" s ||
    ["eq_def", "eq_unfold", "injEq", "inj", "induct", "induct_unfolding", "mutual_induct",
      "fun_cases", "fun_cases_unfolding", "congr_simp", "sizeOf_spec"].contains s

/-- Whether a constant of a module is in scope: under `CslibFrontier.Crypto`, or named in the
namespace `Cslib.Crypto`. -/
def inScope (module : Name) (n : Name) : Bool :=
  (`CslibFrontier.Crypto).isPrefixOf module || (`Cslib.Crypto).isPrefixOf (privateToUserName n)

/-- Whether a last name component names an efficiency predicate. -/
def efficiencyName (s : String) : Bool :=
  s.startsWith "IsPPT" || s.startsWith "IsOraclePPT"

/-- Whether a last name component names an advantage. -/
def advantageName (s : String) : Bool :=
  s == "advantage" || s == "succProbability" || s.endsWith "Advantage"

/-- Type heads of infrastructure values: distributions and games, numbers, truth values, sets,
encodings and sorts. -/
def infrastructure : NameSet :=
  [`PMF, `Cslib.Crypto.Game, `Real, `NNReal, `ENNReal, `Nat, `Int, `Rat, `Bool, `Prop, `Set,
    `Function.Embedding].foldl (·.insert ·) {}

/-- Result types of infrastructure functions: predicates, tests and numeric functions. -/
def infrastructureCodomain : NameSet :=
  [`Real, `NNReal, `ENNReal, `Nat, `Int, `Rat, `Bool, `Prop, `Function.Embedding].foldl
    (·.insert ·) {}

/-- Result types of ensembles and game families when indexed by the security parameter alone. -/
def ensembleCodomain : NameSet :=
  [`PMF, `Cslib.Crypto.Game].foldl (·.insert ·) {}

/-- Containers of a membership that are not adversary classes. -/
def ignoredContainers : NameSet :=
  [`PMF.support, `Set.range, `Finset.range, `List.range, `Finset.univ, `Set.univ,
    `Finset.Icc, `Finset.Ico, `Set.Icc, `Set.Ico, `Set.Iio, `Set.Ioi].foldl (·.insert ·) {}

/-- A binder's name, or `#i` for the `i`-th binder when its name is inaccessible, as for a premise
written with an arrow. -/
def binderLabel (n : Name) (i : Nat) : String :=
  if n.hasMacroScopes || n.isAnonymous then s!"#{i}" else n.toString

/-- The domains of the leading `∀`s of `e`. -/
partial def forallDomains : Expr → Array Expr
  | .forallE _ t b _ => #[t] ++ forallDomains b
  | .mdata _ b => forallDomains b
  | _ => #[]

/-- The leading `∀`s of `e` stripped (with loose bound variables left in place). -/
partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ b => stripForall b
  | e => e

/-- `e` with its first `k` leading `∀`s stripped. -/
def dropForall : Nat → Expr → Expr
  | k + 1, .forallE _ _ b _ => dropForall k b
  | k, .mdata _ b => dropForall k b
  | _, e => e

/-- The environment: every constant of the listed modules, with its module, and their
docstrings. -/
structure Env where
  consts : Std.HashMap Name ConstantInfo := {}
  moduleOf : Std.HashMap Name Name := {}
  skip : NameSet := {}
  docs : Std.HashMap Name String := {}
  lines : Std.HashMap Name Nat := {}
  reducible : NameSet := {}

/-- `type` with type synonyms of the environment at its head unfolded (`fuel` times at most). -/
partial def unfoldSynonyms (env : Env) (fuel : Nat) (type : Expr) : Expr :=
  match fuel, type.consumeMData.getAppFn with
  | fuel + 1, .const c _ =>
    if infrastructure.contains c then type else
    match env.consts[c]? with
    | some (.defnInfo v) =>
      match stripForall v.type with
      | .sort _ =>
        unfoldSynonyms env fuel (v.value.beta type.consumeMData.getAppArgs).headBeta
      | _ => type
    | _ => type
  | _, _ => type

/-- The head of a type after unfolding type synonyms: a constant, or `Prop` for a sort. -/
def typeHead (env : Env) (type : Expr) : Option Name :=
  match (unfoldSynonyms env 8 type).consumeMData.getAppFn with
  | .sort _ => some `Prop
  | .const c _ => some c
  | _ => none

/-- Whether a binder domain is an object type, such as an adversary or a scheme: not a sort, a
type variable, a function, a number, truth value, set, distribution or game. -/
def objectDomain (env : Env) (domain : Expr) : Bool :=
  match (unfoldSynonyms env 8 domain).consumeMData with
  | .sort _ | .forallE .. => false
  | d =>
    match typeHead env d with
    | some h => !infrastructure.contains h
    | none => false

/-- Whether one of the first `k` binders of `type` is explicit with an object domain. -/
def objectArgument (env : Env) (type : Expr) : Nat → Bool
  | k + 1 =>
    match type.consumeMData with
    | .forallE _ d b bi => bi.isExplicit && objectDomain env d || objectArgument env b k
    | _ => false
  | 0 => false

/-- Whether the constant `c`, applied to `k` arguments, is a constructed object (see the module
docstring): a value of an algorithmic type (a program, a structure such as a scheme or adversary),
a function other than a predicate, test or numeric function, or a distribution, ensemble or game
applied to an object. -/
def constructedAt (env : Env) (c : Name) (k : Nat) : Bool := Id.run do
  let some info := env.consts[c]? | return false
  let some m := env.moduleOf[c]? | return false
  unless inScope m c do return false
  if env.skip.contains c || isGenerated c then return false
  match info with
  | .defnInfo _ | .opaqueInfo _ => pure ()
  | _ => return false
  let s := (last c).toLower
  if s.contains "game" || s.contains "experiment" || advantageName (last c) then return false
  let rest := unfoldSynonyms env 8 (dropForall k info.type)
  -- A distribution, ensemble or game applied to an object, such as `simulatorView A`.
  let derived := objectArgument env info.type k
  match rest.consumeMData with
  | .forallE .. =>
    match typeHead env (stripForall rest) with
    | some h =>
      if ensembleCodomain.contains h &&
          (forallDomains rest).all (·.consumeMData.isConstOf `Nat) then derived
      else !infrastructureCodomain.contains h
    | none => true
  | .sort _ => false
  | r =>
    match typeHead env r with
    | some h => !infrastructure.contains h || ensembleCodomain.contains h && derived
    | none => true

/-- The constructed constants of `e`, each judged at the number of arguments it is applied to. -/
partial def constructedIn (env : Env) (e : Expr) : StateM NameSet Unit := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ => if constructedAt env c args.size then modify (·.insert c)
    | _ => constructedIn env f
    args.forM (constructedIn env)
  | .const c _ => if constructedAt env c 0 then modify (·.insert c)
  | .lam _ t b _ | .forallE _ t b _ => constructedIn env t; constructedIn env b
  | .letE _ t v b _ => constructedIn env t; constructedIn env v; constructedIn env b
  | .mdata _ b | .proj _ _ b => constructedIn env b
  | _ => pure ()

/-- The constructed constants of the expressions `es`. -/
def constructedOf (env : Env) (es : Array Expr) : NameSet :=
  ((es.forM (constructedIn env)).run {}).2

/-- Whether `e` mentions an advantage. -/
def mentionsAdvantage (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => advantageName (last c)

/-- The claim atoms of a hypothesis type: through its own `∀`s and premises, `∧`, `∃`, `∀ᶠ` and
metadata. -/
partial def atoms (e : Expr) : Array Expr :=
  match e with
  | .forallE _ _ b _ => atoms b
  | .mdata _ b => atoms b
  | .lam _ _ b _ => atoms b
  | e =>
    if e.isAppOfArity ``And 2 then atoms e.appFn!.appArg! ++ atoms e.appArg!
    else if e.isAppOfArity ``Exists 2 then atoms e.appArg!
    else if e.isAppOfArity `Filter.Eventually 3 then atoms e.appFn!.appArg!
    else #[e]

/-- The explicit arguments of an application of `f`, when the environment has `f`; otherwise all
of them. -/
def explicitArgs (env : Env) (f : Name) (args : Array Expr) : Array Expr := Id.run do
  let some info := env.consts[f]? | return args
  let mut type := info.type
  let mut out := #[]
  for a in args do
    match type.consumeMData with
    | .forallE _ _ b bi =>
      if bi.isExplicit then out := out.push a
      type := b
    | _ => out := out.push a
  return out

/-- The kind and subjects of a security atom, or `none`. -/
def classify (env : Env) (e : Expr) : Option (String × Array Expr) :=
  match e.getAppFn with
  | .const f _ =>
    let s := last f
    let all := e.getAppArgs
    let args := explicitArgs env f all
    if s == "Negligible" then some ("negligible", args)
    else if (f == ``LE.le || f == ``LT.lt || f == ``GE.ge || f == ``GT.gt) && all.size == 4 then
      if mentionsAdvantage all[2]! || mentionsAdvantage all[3]! then
        some ("advantage", #[all[2]!, all[3]!])
      else none
    else if f == ``Membership.mem && all.size == 5 then
      match all[3]!.getAppFn with
      | .const g _ => if ignoredContainers.contains g then none else some ("member", #[all[4]!])
      | _ => some ("member", #[all[4]!])
    else if efficiencyName s then some ("efficiency", args)
    else if s.contains "Indistinguishable" then some ("indistinguishable", args)
    else none
  -- A bound predicate, such as an abstract admissibility class `Admissible B`.
  | .bvar _ | .fvar _ => if e.getAppNumArgs > 0 then some ("member", e.getAppArgs) else none
  | _ => none

/-- Unfold a Prop-valued definition of the environment heading `e`, once. -/
def unfoldProp? (env : Env) (e : Expr) : Option Expr := do
  let .const c _ := e.getAppFn | none
  let .defnInfo v ← env.consts[c]? | none
  let .sort .zero := stripForall v.type | none
  some (v.value.beta e.getAppArgs).headBeta

/-- The security atoms of a hypothesis type that mention a constructed object, as
`(kind, constructed constants)`. Within an unfolded definition, only the constructed constants of
its arguments (`allowed`) count: the objects that a notion's own definition builds, such as the
dummy adversary of UC emulation, are part of the notion. -/
partial def findings (env : Env) (fuel : Nat) (allowed : Option NameSet) (e : Expr) :
    Array (String × Array Name) :=
  (atoms e).foldl (init := #[]) fun acc a =>
    match classify env a with
    | some (k, subjects) =>
      let cs := (constructedOf env subjects).toArray.filter fun c =>
        allowed.all (·.contains c)
      if cs.isEmpty then acc else acc.push (k, cs)
    | none =>
      match fuel, unfoldProp? env a with
      | fuel + 1, some u =>
        let args := constructedOf env a.getAppArgs
        let allowed := some (allowed.elim args fun s => args.filter s.contains)
        if args.isEmpty then acc else
        acc ++ (findings env fuel allowed u).map fun (k, cs) => ("unfolded " ++ k, cs)
      | _, _ => acc

/-- The constructed constants of `e` applied to an argument that mentions one of `vars`. -/
partial def constructedWith (env : Env) (vars : Array FVarId) (e : Expr) :
    StateM NameSet Unit := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      if constructedAt env c args.size &&
          args.any (·.hasAnyFVar (vars.contains ·)) then
        modify (·.insert c)
    | _ => constructedWith env vars f
    args.forM (constructedWith env vars)
  | .lam _ t b _ | .forallE _ t b _ => constructedWith env vars t; constructedWith env vars b
  | .letE _ t v b _ =>
    constructedWith env vars t; constructedWith env vars v; constructedWith env vars b
  | .mdata _ b | .proj _ _ b => constructedWith env vars b
  | _ => pure ()

/-- Advantage bounds in a conclusion that hold only for some existentially chosen parameters of
a constructed reduction, such as `∃ m₀ m₁, … ≤ Adv(B A m₀ m₁)`: the constructed constants applied
to an `∃`-bound variable in an advantage inequality under the `∃`. The textbook reduction chooses
such parameters itself (by sampling), so the bound does not give a uniform reduction. -/
partial def existentialFindings (env : Env) (vars : Array FVarId) (fresh : Nat) (e : Expr) :
    Array Name :=
  match e with
  | .forallE _ _ b _ | .mdata _ b => existentialFindings env vars fresh b
  | e =>
    if e.isAppOfArity ``And 2 then
      existentialFindings env vars fresh e.appFn!.appArg! ++
        existentialFindings env vars fresh e.appArg!
    else if e.isAppOfArity ``Exists 2 then
      match e.appArg!.consumeMData with
      | .lam _ _ body _ =>
        let x : FVarId := ⟨.num `_exists fresh⟩
        existentialFindings env (vars.push x) (fresh + 1) (body.instantiate1 (.fvar x))
      | _ => #[]
    else if vars.isEmpty then #[]
    else
      match classify env e with
      | some ("advantage", subjects) =>
        (((subjects.forM (constructedWith env vars)).run {}).2).toArray
      | _ => #[]

/-- Whether `e`, under its `fun`s, is the variable `x` or an application of it. -/
partial def headedBy (x : FVarId) (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => headedBy x b
  | e => e.getAppFn.consumeMData.isFVarOf x

/-- The variables among `vars` to which the hypothesis type `premise` gives an efficiency or
class-membership claim, whose subject is the variable or a function that applies it, as in
`hD : IsOraclePPT encBool D`, `IsPPTOn … (fun p => test p.1 p.2)` or `D ∈ 𝒟`. -/
def certifiedBy (env : Env) (vars : Array FVarId) (premise : Expr) : Array FVarId :=
  (atoms premise).foldl (init := #[]) fun acc a =>
    match classify env a with
    | some ("efficiency", subjects) | some ("member", subjects) =>
      acc ++ vars.filter fun x => subjects.any (headedBy x)
    | _ => acc

/-- Realization premises: an equation one side of which mentions a variable `x` of `certified`
and the other side does not, but applies a constructed constant to another of the theorem's
variables `vars`. With `x`'s efficiency premise, it assumes that the constructed object has an
efficient realization, as in `hreal : eval (prfRealGame family D n) = … (nonceFnDistinguisher
(seed n) (hash n) (forger n))` beside `hD : IsOraclePPT encBool D`. Only `x` is excluded on the
other side, and it does not occur there: the other variable may be certified too, as the input
adversary is in `D.run n = (reduction A).run n` beside `hA : A.IsPPT` and `hD : D.IsPPT`.
Returns the constructed constants of the other side. -/
def realizations (env : Env) (certified vars : Array FVarId) (premise : Expr) : Array Name :=
  (atoms premise).foldl (init := #[]) fun acc a =>
    if a.isAppOfArity ``Eq 3 then
      let side (s t : Expr) : Array Name :=
        if certified.any fun x => s.containsFVar x && !t.containsFVar x then
          ((constructedWith env vars t).run {}).2.toArray
        else #[]
      acc ++ side a.appFn!.appArg! a.appArg! ++ side a.appArg! a.appFn!.appArg!
    else acc

/-! ### Named assumptions, for `scripts/check_hardness_assumptions.py` -/

/-- The constants that a proposition-valued declaration's definition mentions: the body of a
definition whose type ends in `Prop`, or the fields of an inductive proposition such as a
`structure … : Prop`. `none` for any other constant. -/
def propositionConstants? (env : Env) (c : Name) : Option (Array Name) :=
  match env.consts[c]? with
  | some (.defnInfo v) =>
    match stripForall v.type with
    | .sort .zero => some v.value.getUsedConstants
    | _ => none
  | some (.inductInfo v) =>
    match stripForall v.type with
    | .sort .zero => some <| v.ctors.foldl (init := #[]) fun acc k =>
        acc ++ ((env.consts[k]?).map (·.type.getUsedConstants)).getD #[]
    | _ => none
  | _ => none

/-- Whether a last name component names a security atom: negligibility, an advantage or
indistinguishability. This decides only what a definition must reach to be security-shaped. -/
def securityAtomName (s : String) : Bool :=
  s == "Negligible" || advantageName s || s.contains "Indistinguishable"

/-- Whether `c` is a proposition-valued declaration that states a security claim: its definition
mentions a security atom, directly or through proposition-valued declarations of the environment
at most `fuel` deep. -/
partial def securityShaped (env : Env) (fuel : Nat) (c : Name) : Bool :=
  match propositionConstants? env c with
  | some cs => cs.any fun d =>
      securityAtomName (last d) || fuel > 0 && d != c && securityShaped env (fuel - 1) d
  | none => false

/-- Whether `c` is a *named assumption*: a security-shaped proposition-valued declaration that
Lean does not generate. Its name excludes nothing: a declaration named like a security atom, such
as `Game.Indistinguishable` or a library-specific `KeysIndistinguishable`, is reported when its
definition is security-shaped, and the assumptions inventory records which ones are generic
vocabulary. -/
def namedAssumption (env : Env) (c : Name) : Bool :=
  !isGenerated c && !env.skip.contains c && securityShaped env 5 c

/-- The named assumptions that head the claim atoms of a hypothesis type. -/
def assumptionHeads (env : Env) (ty : Expr) : Array Name :=
  (atoms ty).foldl (init := #[]) fun acc a =>
    match a.getAppFn with
    | .const c _ => if namedAssumption env c && !acc.contains c then acc.push c else acc
    | _ => acc

unsafe def docEntries (entries : Array (Name × Array EnvExtensionEntry)) :
    Array (Name × String) := Id.run do
  let mut out := #[]
  for (ext, es) in entries do
    if ext == `Lean.docStringExt then
      for e in es do
        out := out.push (unsafeCast e : Name × String)
  return out

unsafe def declRanges (entries : Array (Name × Array EnvExtensionEntry)) :
    NameMap DeclarationRanges := Id.run do
  let mut ranges : NameMap DeclarationRanges := {}
  for (ext, es) in entries do
    if ext == `Lean.declRangeExt then
      for e in es do
        let (n, r) := (unsafeCast e : Name × DeclarationRanges)
        ranges := ranges.insert n r
  return ranges

/-- The instances and structure projections of a module. -/
unsafe def skipped (entries : Array (Name × Array EnvExtensionEntry)) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (ext, es) in entries do
    if ext == `Lean.projectionFnInfoExt then
      for e in es do
        out := out.insert (unsafeCast e : Name × ProjectionFunctionInfo).1
    if ext == `Lean.Meta.instanceExtension then
      for e in es do
        let entry := match (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry) with
          | .global a => a
          | .scoped _ a => a
        if let some n := entry.globalName? then out := out.insert n
  return out

/-- The `@[reducible]` definitions of a module, `abbrev`s among them. -/
unsafe def reducibles (entries : Array (Name × Array EnvExtensionEntry)) : Array Name := Id.run do
  let mut out := #[]
  for (ext, es) in entries do
    if ext == `reducibilityCore then
      for e in es do
        let (n, status) := (unsafeCast e : Name × ReducibilityStatus)
        if status matches .reducible then out := out.push n
  return out

/-- Read the modules listed on standard input, one per line. A line `<dir>\t<module>` reads a
*context* module from another build directory, such as CSLib's: its constants are in the
environment, so definitions can be followed into it, but its theorems are not scanned. Returns
the environment, the scanned modules, the compacted regions (to keep reachable while their
expressions are used) and the modules without build outputs. -/
unsafe def load (libDir : System.FilePath) :
    IO (Env × Array (Name × ModuleData) × Array CompactedRegion × Array String) := do
  let stdin ← IO.getStdin
  let mut regions : Array CompactedRegion := #[]
  let mut missing : Array String := #[]
  let mut env : Env := {}
  let mut mods : Array (Name × ModuleData) := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let raw := line.trimAscii.toString
    if raw.isEmpty then continue
    let (dir, mod, scan) := match raw.splitOn "\t" with
      | [dir, mod] => ((dir : System.FilePath), mod, false)
      | _ => (libDir, raw, true)
    let base := (dir / System.FilePath.mk (mod.replace "." "/")).addExtension "olean"
    unless ← base.pathExists do
      missing := missing.push mod
      continue
    let split ← (base.addExtension "private").pathExists
    let paths := if split then #[base, base.addExtension "server", base.addExtension "private"]
      else #[base]
    let parts ← readModuleDataParts paths
    regions := regions ++ parts.map (·.2)
    let some (data, _) := parts[if split then 2 else 0]? |
      throw <| IO.userError s!"cannot read {base}"
    let m := mod.toName
    if scan then mods := mods.push (m, data)
    for c in data.constants do
      env := { env with consts := env.consts.insert c.name c,
                        moduleOf := env.moduleOf.insert c.name m }
    env := { env with skip := (skipped data.entries).foldl (·.insert ·) env.skip }
    for (part, _) in parts do
      env := { env with reducible := (reducibles part.entries).foldl (·.insert ·) env.reducible }
    for (part, _) in parts do
      for (n, doc) in docEntries part.entries do
        env := { env with docs := env.docs.insert n doc }
    for (n, r) in declRanges data.entries do
      env := { env with lines := env.lines.insert n r.selectionRange.pos.line }
  return (env, mods, regions, missing)

unsafe def run (libDir : System.FilePath) : IO Unit := do
  let stdout ← IO.getStdout
  let (env, mods, regions, missing) ← load libDir
  let mut scanned := 0
  for (m, data) in mods do
    let ranges := declRanges data.entries
    for c in data.constants do
      let .thmInfo v := c | continue
      if isPrivateName c.name || isGenerated c.name || env.skip.contains c.name then continue
      unless inScope m c.name do continue
      scanned := scanned + 1
      let mut hyps : Array Json := #[]
      let mut t := v.type
      let mut index := 0
      -- The theorem's variables, and its premises as `(binder label, type)`.
      let mut vars : Array FVarId := #[]
      let mut premises : Array (String × Expr) := #[]
      repeat
        match t with
        | .mdata _ b => t := b
        | .forallE n ty b bi =>
          index := index + 1
          unless bi.isInstImplicit do
            premises := premises.push (binderLabel n index, ty)
            let fs := findings env 3 none ty
            unless fs.isEmpty do
              let kinds := (fs.map (·.1)).toList.eraseDups
              let cs := (fs.foldl (fun acc (_, cs) => acc ++ cs) #[]).toList.eraseDups
              hyps := hyps.push <| Json.mkObj [("b", toJson (binderLabel n index)),
                ("k", toJson kinds), ("c", toJson (cs.map (privateToUserName · |>.toString)))]
          let x : FVarId := ⟨.num `_binder index⟩
          vars := vars.push x
          t := b.instantiate1 (.fvar x)
        | _ => break
      let certified := premises.foldl (fun acc (_, ty) => acc ++ certifiedBy env vars ty) #[]
      unless certified.isEmpty do
        for (label, ty) in premises do
          let cs := (realizations env certified vars ty).toList.eraseDups
          unless cs.isEmpty do
            hyps := hyps.push <| Json.mkObj [("b", toJson label), ("k", toJson ["realization"]),
              ("c", toJson (cs.map (privateToUserName · |>.toString)))]
      let cs := (existentialFindings env #[] 0 t).toList.eraseDups
      unless cs.isEmpty do
        hyps := hyps.push <| Json.mkObj [("b", toJson "⊢"),
          ("k", toJson ["exists advantage"]),
          ("c", toJson (cs.map (privateToUserName · |>.toString)))]
      unless hyps.isEmpty do
        let line := ((ranges.find? c.name).map (·.selectionRange.pos.line)).getD 0
        stdout.putStrLn <| Json.compress <| Json.mkObj [("n", toJson c.name.toString),
          ("m", toJson m.toString), ("l", toJson line), ("h", Json.arr hyps)]
  stdout.putStrLn <| Json.compress <| Json.mkObj [("theorems", toJson scanned),
    ("modules", toJson mods.size), ("missing", toJson missing)]
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

/-- The `--assumptions` mode (see the module docstring): every named assumption of the
environment with its module, line and docstring, and every scanned theorem whose premises it
heads, with the theorem's docstring. -/
unsafe def runAssumptions (libDir : System.FilePath) : IO Unit := do
  let stdout ← IO.getStdout
  let (env, mods, regions, missing) ← load libDir
  let record (key : String) (c : Name) (extra : List (String × Json)) : String :=
    Json.compress <| Json.mkObj <| [(key, toJson c.toString),
      ("m", toJson ((env.moduleOf.get? c).getD .anonymous).toString),
      ("l", toJson ((env.lines.get? c).getD 0)), ("doc", toJson ((env.docs.get? c).getD ""))] ++
      extra
  -- Named assumptions of context modules too: a theorem may assume a notion that CSLib defines.
  for (c, _) in env.consts.toArray.qsort (fun a b => a.1.lt b.1) do
    if namedAssumption env c then stdout.putStrLn (record "a" c [])
  let mut scanned := 0
  for (m, data) in mods do
    for c in data.constants do
      let .thmInfo v := c | continue
      if isPrivateName c.name || isGenerated c.name || env.skip.contains c.name then continue
      unless inScope m c.name do continue
      scanned := scanned + 1
      let mut heads : Array Name := #[]
      let mut t := v.type
      repeat
        match t with
        | .mdata _ b => t := b
        | .forallE _ ty b bi =>
          unless bi.isInstImplicit do
            heads := (assumptionHeads env ty).foldl (fun acc h =>
              if acc.contains h then acc else acc.push h) heads
          t := b
        | _ => break
      unless heads.isEmpty do
        stdout.putStrLn (record "t" c.name [("u", toJson (heads.map (·.toString)))])
  stdout.putStrLn <| Json.compress <| Json.mkObj [("theorems", toJson scanned),
    ("modules", toJson mods.size), ("missing", toJson missing)]
  if regions.isEmpty then stdout.flush

/-! ### Reductions and efficiency witnesses, for `scripts/check_reduction_witnesses.py` -/

/-- Whether a last name component names an efficiency certificate: strict polynomial time for a
probabilistic or oracle program, or a machine-level time bound. A query or call bound
(`IsQueryBounded`) is not one. -/
def witnessName (s : String) : Bool :=
  efficiencyName s || s.startsWith "IsTidyOraclePPT" || s.startsWith "ComputableIn" ||
    s.startsWith "ComputableTidilyIn" || s.startsWith "IsPolyTime" || s.startsWith "IsEfficient" ||
    s.startsWith "Efficient"

/-- Type heads of computations: distributions, and programs with coins or oracles. -/
def computation : NameSet :=
  [`PMF, `PFunctor.FreeM].foldl (·.insert ·) {}

/-- The final result of a type, with type synonyms of the environment unfolded at each step. -/
partial def finalResult (env : Env) (fuel : Nat) (type : Expr) : Expr :=
  match fuel, (unfoldSynonyms env 8 type).consumeMData with
  | fuel + 1, t@(.forallE ..) => finalResult env fuel (stripForall t)
  | _, t => t

/-- Whether `type` is a program type: a computation with coins or oracles, or a function into a
computation other than an ensemble `ℕ → … → PMF _`. -/
def programType (env : Env) (type : Expr) : Bool :=
  match (unfoldSynonyms env 8 type).consumeMData with
  | u@(.forallE ..) =>
    match (finalResult env 8 u).getAppFn with
    | .const h _ =>
      h == `PFunctor.FreeM ||
        h == `PMF && !(forallDomains u).all (·.consumeMData.isConstOf `Nat)
    | _ => false
  | u => u.getAppFn.isConstOf `PFunctor.FreeM

/-- Whether `type` is a structure with a field of a program type, or (at most `fuel` deep) of
such a structure: an adversary, a simulator, a scheme. -/
partial def programStructure (env : Env) (fuel : Nat) (type : Expr) : Bool :=
  match (unfoldSynonyms env 8 type).consumeMData.getAppFn with
  | .const c _ =>
    match env.consts[c]? with
    | some (.inductInfo v) =>
      match v.ctors, v.isRec with
      | [k], false =>
        match env.consts[k]? with
        | some info =>
          (forallDomains (dropForall v.numParams info.type)).any fun d =>
            programType env d || fuel > 0 && programStructure env (fuel - 1) d
        | none => false
      | _, _ => false
    | _ => false
  | _ => false

/-- Whether a variable of this type is a program: the input adversary, or a component that runs. -/
def programVariable (env : Env) (type : Expr) : Bool :=
  programType env type || programStructure env 2 type

/-- Whether a constant of this type finally yields a program: a computation, a distribution (a
`PMF`-valued distinguisher or reduction) or a structure of programs. -/
def programResult (env : Env) (type : Expr) : Bool :=
  let result := finalResult env 8 type
  (match result.getAppFn with
    | .const h _ => computation.contains h
    | _ => false) || programStructure env 2 result

/-- The constructed constants of `e`, each with the positions in `vars` of the theorem's variables
that its arguments mention. -/
partial def constructedArgs (env : Env) (vars : Array FVarId) (e : Expr) :
    StateM (Std.HashMap Name (Array Nat)) Unit := do
  let note (c : Name) (args : Array Expr) : StateM (Std.HashMap Name (Array Nat)) Unit :=
    modify fun found =>
      let old := found.getD c #[]
      found.insert c <| old ++ (Array.range vars.size).filter fun i =>
        !old.contains i && args.any (·.containsFVar vars[i]!)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ => if constructedAt env c args.size then note c args
    | _ => constructedArgs env vars f
    args.forM (constructedArgs env vars)
  | .const c _ => if constructedAt env c 0 then note c #[]
  | .lam _ t b _ | .forallE _ t b _ => constructedArgs env vars t; constructedArgs env vars b
  | .letE _ t v b _ =>
    constructedArgs env vars t; constructedArgs env vars v; constructedArgs env vars b
  | .mdata _ b | .proj _ _ b => constructedArgs env vars b
  | _ => pure ()

/-- The bounded and the bounding side of an advantage bound: `a ≤ b`, `a < b`, their reversals,
or `a = b` read as `a ≤ b`, one side of which mentions an advantage. -/
def boundSides? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFn with
  | .const f _ =>
    let args := e.getAppArgs
    let sides : Option (Expr × Expr) :=
      if (f == ``LE.le || f == ``LT.lt) && args.size == 4 then some (args[2]!, args[3]!)
      else if (f == ``GE.ge || f == ``GT.gt) && args.size == 4 then some (args[3]!, args[2]!)
      else if f == ``Eq && args.size == 3 then some (args[1]!, args[2]!)
      else none
    sides.filter fun (a, b) => mentionsAdvantage a || mentionsAdvantage b
  | _ => none

/-- Push `x` onto the array at `key`, once. -/
def pushOnce (m : Std.HashMap Name (Array Name)) (key x : Name) : Std.HashMap Name (Array Name) :=
  let old := m.getD key #[]
  if old.contains x then m else m.insert key (old.push x)

/-- How the reduction `c` is certified, with the certifying declarations, or `none`: `direct` by
theorems that conclude an efficiency certificate mentioning it, `abbrev` when it is reducible and
the programs of the scanned modules in its body (`parts`) are all certified, or `wrapper` by
certified definitions whose bodies mention it. -/
partial def certificate? (env : Env) (witnesses wrappers : Std.HashMap Name (Array Name))
    (parts : Name → Array Name) (fuel : Nat) (c : Name) : Option (String × Array Name) :=
  match witnesses[c]? with
  | some ws => some ("direct", ws)
  | none =>
    let ps := parts c
    if fuel > 0 && env.reducible.contains c && !ps.isEmpty &&
        ps.all (certificate? env witnesses wrappers parts (fuel - 1) · |>.isSome) then
      some ("abbrev", ps)
    else (wrappers[c]?).map (("wrapper", ·))

/-- The `--reductions` mode (see the module docstring): every reduction that a public theorem
states an advantage bound with, and how it is certified. -/
unsafe def runReductions (libDir : System.FilePath) : IO Unit := do
  let stdout ← IO.getStdout
  let (env, mods, regions, missing) ← load libDir
  let scannedModules : NameSet := mods.foldl (fun s (m, _) => s.insert m) {}
  let mut scanned := 0
  -- A reduction's stating theorems, and a constant's efficiency theorems.
  let mut stated : Std.HashMap Name (Array Name) := {}
  let mut witnesses : Std.HashMap Name (Array Name) := {}
  for (m, data) in mods do
    for c in data.constants do
      let .thmInfo v := c | continue
      if isGenerated c.name || env.skip.contains c.name then continue
      unless inScope m c.name do continue
      scanned := scanned + 1
      let mut t := v.type
      let mut index := 0
      let mut vars : Array FVarId := #[]
      let mut programs : Array Bool := #[]
      repeat
        match t with
        | .mdata _ b => t := b
        | .forallE _ ty b _ =>
          index := index + 1
          programs := programs.push (programVariable env ty)
          let x : FVarId := ⟨.num `_binder index⟩
          vars := vars.push x
          t := b.instantiate1 (.fvar x)
        | _ => break
      for a in atoms t do
        if let .const f _ := a.getAppFn then
          if witnessName (last f) then
            for u in a.getUsedConstants do
              witnesses := pushOnce witnesses u c.name
        if isPrivateName c.name then continue
        let some (lower, upper) := boundSides? a | continue
        let below := constructedOf env #[lower]
        for (r, positions) in ((constructedArgs env vars upper).run {}).2.toArray do
          if below.contains r then continue
          unless (env.moduleOf[r]?).any scannedModules.contains do continue
          unless (env.consts[r]?).any (programResult env ·.type) do continue
          if positions.any fun i => programs[i]! && lower.containsFVar vars[i]! then
            stated := pushOnce stated r c.name
  -- Certified definitions, by the reductions that their bodies mention.
  let mut wrappers : Std.HashMap Name (Array Name) := {}
  for (u, _) in witnesses.toArray do
    let some (.defnInfo v) := env.consts[u]? | continue
    unless (env.moduleOf[u]?).any (inScope · u) do continue
    for b in v.value.getUsedConstants do
      if b != u && stated.contains b then wrappers := pushOnce wrappers b u
  let parts (c : Name) : Array Name :=
    match env.consts[c]? with
    | some (.defnInfo v) => (constructedOf env #[v.value]).toArray.filter fun p =>
        p != c && (env.moduleOf[p]?).any scannedModules.contains &&
          (env.consts[p]?).any (programResult env ·.type)
    | _ => #[]
  let names (ns : Array Name) : Json :=
    toJson ((ns.map (privateToUserName · |>.toString)).qsort (· < ·))
  for (r, theorems) in stated.toArray.qsort (fun a b => a.1.lt b.1) do
    let (kind, by_) := (certificate? env witnesses wrappers parts 4 r).getD ("", #[])
    let modules := theorems.filterMap fun t => (env.moduleOf.get? t).map (·.toString)
    stdout.putStrLn <| Json.compress <| Json.mkObj [
      ("n", toJson (privateToUserName r).toString),
      ("m", toJson ((env.moduleOf.get? r).getD .anonymous).toString),
      ("l", toJson ((env.lines.get? r).getD 0)), ("t", names theorems),
      ("tm", toJson (modules.toList.eraseDups.toArray.qsort (· < ·))),
      ("k", toJson kind), ("w", names by_)]
  stdout.putStrLn <| Json.compress <| Json.mkObj [("theorems", toJson scanned),
    ("modules", toJson mods.size), ("missing", toJson missing)]
  if regions.isEmpty then stdout.flush

end CslibFrontierScripts.SecurityPremises

unsafe def main (args : List String) : IO Unit :=
  match args with
  | [] => CslibFrontierScripts.SecurityPremises.run ".lake/build/lib/lean"
  | [libDir] => CslibFrontierScripts.SecurityPremises.run libDir
  | [libDir, "--assumptions"] => CslibFrontierScripts.SecurityPremises.runAssumptions libDir
  | [libDir, "--reductions"] => CslibFrontierScripts.SecurityPremises.runReductions libDir
  | _ => throw <| IO.userError
      "usage: SecurityPremises [<lib-dir> [--assumptions | --reductions]] < modules.txt"
