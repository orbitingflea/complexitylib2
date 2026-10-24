# T15/T17: formal abstract of Dijkstra's algorithm, O((m + 1) log n)

Branch `t15-dijkstra-abstract`, first based on `c766a2cf` (fork main with T14 merged), later
merged with `origin/main` `ddd3a2a9` and then `dcf8b70f` (T16: the Dijkstra programs on the exact
basis). T17 replaced the library's machine in the statement by the abstract's own exact-basis
machine. Line numbers in `C/` are at `c766a2cf`; those in `D/` and `X/` are at the branch head. Paths: `C/` = `Complexity/Computability/WordRAM/`,
`D/` = `Complexity/Algorithms/WordRAM/Dijkstra/`, `X/` = `abstracts/ComplexityAbstracts/`.
"(inferred)" marks what I derived rather than read.

## Files

* `X/DijkstraAbstract.lean`: the abstract. It defines the graph, walks, the distance, the number
  of edges, the largest weight, the input and output layouts, and states `dijkstra_logLinear`.
  It also defines its own word RAM over the exact basis. The proof is one term through the bridge.
  `#check_abstract` passes with no allowlist: the abstract depends only on Lean, Mathlib and
  CSLib.
* `X/DijkstraBridge.lean`: proves that the walk distance equals the library's distance
  (`walkDist_eq`), that a run of a library program over `Basis.exact` is a run of its
  translation (`runs_map`), and transfers `logLinearStatement` (`logLinear`).
* `abstracts/ComplexityAbstracts.lean`: imports both.

No library file changed. No `catalogue.json` entry was added.

## Layout

Following "Lead with the mathematics" (`.agents/skills/lean-abstract/SKILL.md`) and "Layout and
sources" (`abstracts/README.md`), the abstract has, in source order:

1. the module docstring;
2. "Graphs and distances": `Graph`, `IsWalk`, `dist`, `numEdges`, `maxWeight`;
3. "Input, output and cost": prose only, stating in words the input, the output cells, the
   word-size condition and the cost model, including that placing the input and its length
   header costs nothing (`C/Defs.lean`, `Data.init`) and that memory beyond them and the registers
   start at `0`, which removes an initialization term in `n` (`D/HeapStatement.lean:18-20`);
4. "Representation details": `offset`, `encode`, `outAddr`, `encodeDist`, and the machine
   (`AluOp`, `AluOp.eval`, `Instr`, `Program`, `State`, `Outcome`, `step`, `init`, `Runs`);
5. "Main theorem": `dijkstra_logLinear` and the audit.

The renderer moves a `## Representation details` group, up to the next `##` heading, to an
appendix after the main text (`scripts/abstract_to_tex.py`, `split_sections` and
`presentation_sections`). The group sits before the theorem in the source because the theorem uses
its definitions; `CookLevinAbstract.lean` does the same.

## Main theorem

```lean
theorem dijkstra_logLinear :
    ∃ r, ∃ p : Program r, ∃ K, ∀ (n : ℕ) (G : Graph n) (s : Fin n) (w : ℕ),
      8 * (n + numEdges G + 2) * (maxWeight G + 2) < 2 ^ w →
      ∃ t steps, Runs w p (init (encode G s)) t steps ∧
        (∃ v, step w p t = .halt v) ∧
        steps + 1 ≤ K * (numEdges G + 1) * (Nat.log 2 n + 1) ∧
        ∀ v : Fin n, t.mem (outAddr G v) = encodeDist (dist G s v)
```

Outside the machine names (`Program`, `Runs`, `init`, `step`, `.halt`, `t.mem`), the statement is
the one at `ef8165b7`, where it used `Cslib.WordRAM.Program .standard r`, `Cslib.WordRAM.Runs`,
`Cslib.WordRAM.State.init`, `Cslib.WordRAM.step` and `t.data.mem`.

## The machine

The user asked for the word RAM to appear in the abstract, depending only on Mathlib and public
CSLib, and for the Dijkstra proof to use the exact basis (CoS brief T17, 2026-10-24). T16 moved the
library theorem to the exact basis: `LogLinearSpec` and `LogLinearStatement` are over
`Program .exact r` (`D/HeapStatement.lean:157`, `:166`), proved at `D/LogLinear.lean:422`.

The abstract copies from `X/WordRAMAbstract.lean` exactly the definitions the statement needs:
`AluOp`, `AluOp.eval`, `Instr`, `Program`, `State`, `Outcome`, `step` and `init`
(`X/DijkstraAbstract.lean:139-243`). Their Lean code is character for character the same as in
`X/WordRAMAbstract.lean` (checked with `diff`); the prose differs only where `WordRAMAbstract`
names its `InputFits` and the library's `Runs.bounded_init`, which this abstract does not use. It
does not copy `Halts`, `InputFits`, `Decides` or `DecidableInTime`.

It adds `Runs` (`X/DijkstraAbstract.lean:249`), needed because `WordRAMAbstract`'s `Halts`
exposes only the output, not the final memory:

```lean
def Runs (w : ℕ) (p : Program r) : State r → State r → ℕ → Prop :=
  Relation.RelatesInSteps fun s t => step w p s = .next t
```

This is the library's definition (`C/Defs.lean`, `Runs` is `Relation.RelatesInSteps (Next w p)`
with `Next w p s t := step w p s = .next t`), with CSLib's `Relation.RelatesInSteps`
(`.lake/packages/cslib/Cslib/Foundations/Relation/RelatesInSteps.lean:40`). The docstring states
what `RelatesInSteps` means.

## The bridge for the machine

Upstream allows a bridge to import another bridge: `X/SubsetSumBridge.lean:9` imports
`CookLevinBridge`, and `.agents/skills/lean-abstract/SKILL.md` lists it as "Pattern A reusing
another bridge". So `X/DijkstraBridge.lean` imports `X/WordRAMBridge.lean` and copies nothing.
`WordRAMBridge` proves, for any presentation `S` of the exact word RAM with `Laws S`, that one step
of a library program `q` over `Basis.exact` matches one step of its translation
`q.map S.instrOf` (`step_matches`, `X/WordRAMBridge.lean:223`). The Dijkstra bridge adds:

* `Machine.stateOf`: the abstract state with the `pc`, registers and memory of a library state;
  `stateOf_init`: it maps the library's start state to the abstract `init`.
* `Machine.step_next`, `Machine.step_halt`: a continuing or halting library step is the same step
  of the translation (from `step_matches`).
* `Machine.runs_map`: a library run of `k` steps is a run of `k` steps of the translation, by
  induction on `Relation.RelatesInSteps`.
* `logLinear`: for any `S` with `Laws S` and a memory projection `mem`, the program
  `q.map S.instrOf` (with `q` from `logLinearStatement`) satisfies the abstract statement.

`WordRAMBridge.Presentation` has two fields the Dijkstra abstract does not define, `Halts` and
`OutcomeAgrees`. The abstract fills `Halts` with `DijkstraBridge.haltsVia`, a halting-run
predicate defined from `step` by cases on the outcome (as `WordRAMAbstract`'s `Halts`), and
`OutcomeAgrees` with `True`; the bridge uses neither, and both satisfy `Laws`. The abstract's
proof discharges `Laws` with `constructor <;> simp_all [step, DijkstraBridge.haltsVia,
AluOp.eval]`, as `WordRAMAbstract` does.

## Distance and the bridge

The abstract defines distance by walks:

```lean
def IsWalk (G : Graph n) : Fin n → List (Fin n × ℕ) → Fin n → Prop
  | u, [], v => u = v
  | u, e :: l, v => e ∈ G u ∧ IsWalk G e.1 l v

noncomputable def dist (G : Graph n) (u v : Fin n) : ℕ∞ :=
  ⨅ (l : List (Fin n × ℕ)) (_ : IsWalk G u l v), ((l.map Prod.snd).sum : ℕ∞)
```

The library defines it as the least `Quiver.Path` weight of the weight-matrix instance that keeps
the lightest parallel edge (`D/HeapStatement.lean:82-96`, `D/Statement.lean:89`). The bridge
takes any walk predicate `W` with the two defining laws (`WalkLaws`, `X/DijkstraBridge.lean:45`)
and proves `walkDist_eq` (`X/DijkstraBridge.lean:126`) by two inequalities:

* every path is a walk of the same weight (`exists_walk`, `X/DijkstraBridge.lean:77`);
* every walk gives a path of at most its weight, replacing each edge by the lightest one between
  the same endpoints (`exists_path`, `X/DijkstraBridge.lean:96`), using `lightest_eq_some_iff`
  and `lightest_eq_none_iff` (`D/HeapStatement.lean:125`, `:138`).

The abstract passes `@IsWalk` with both laws proved by `Iff.rfl`. The laws are needed because
`IsWalk` is defined by recursion in the abstract, so the bridge cannot name it (inferred: a
bridge cannot import the abstract that imports it).

## Fidelity

Compared with `LogLinearSpec` (`D/HeapStatement.lean:157-161`) and `LogLinearStatement`
(`:166`):

* Quantifiers: the same, `∃ r p K, ∀ instance w`. The instance `⟨n, G, s⟩` is three parameters.
* Encoding: `offset`, `encode`, `numEdges`, `maxWeight` are the library's `offset`, `encode`,
  `m`, `maxWeight` (`D/HeapStatement.lean:99-118`) with the structure unfolded. They agree by
  `rfl` (the bridge passes them unchanged).
* Output: `outAddr G v = n + 2 m + 4 + v` is `D/HeapStatement.lean:121`, and `encodeDist` is
  `D/Statement.lean:120`.
* Word size: `8 (n + m + 2) (W + 2) < 2 ^ w` is `Fits` (`C/Defs.lean:156`) unfolded.
* Bound: `steps + 1 ≤ K (m + 1) (Nat.log 2 n + 1)`, as in the library.
* No added hypotheses.

What the abstract does not say exactly or not self-contained:

1. The machine is defined in the file. Its relation to the library's `Basis.exact` machine is
   proved in the bridge, not stated in the abstract (unlike `WordRAMAbstract`'s `runsAgree`).
2. The value returned by `halt` is not part of the result (as in the library).
3. `Nat.log 2 n` is `⌊log₂ n⌋` for `n ≥ 1` and `0` for `n = 0`.
4. The constants `r` and `K` are hidden behind `∃`.

## Rendering

The PDF was rendered with upstream's renderer without changing `catalogue.json`: a helper script
outside the repository imports `scripts/build_abstracts.py`, builds an in-memory catalogue entry
(id `dijkstra`, headline `ComplexityAbstracts.DijkstraAbstract.dijkstra_logLinear`), and calls
`render_entry`, `document` and `build_pdf`. The abstract imports no shared foundation, so the entry
lists none. The renderer has no list support in section comments
and no TeX mapping for `⌊`, `⌋` or `ᵢ`, so the docstrings avoid them.

## Checks

* `scripts/check.sh`: all six gates pass.
* `lake build --wfail --iofail ComplexityAbstracts.DijkstraAbstract`: passes.
* `#check_abstract` (no allowlist): "abstract audit passed for
  `ComplexityAbstracts.DijkstraAbstract`: 218 root declarations, 229 dependencies checked". The
  root count includes the declarations Lean generates for the new inductive types.
* `#print axioms ComplexityAbstracts.DijkstraAbstract.dijkstra_logLinear`:
  `[propext, Classical.choice, Quot.sound]`.
* `python3 -B scripts/build_abstracts.py --check`: passes (14 abstracts, 19 headline theorems;
  the new abstract is not in the catalogue).
* `scripts/check_abstract_ci.py` checks GitHub CI of a pushed `main` commit before a release; it
  does not apply to a branch before merge, so I did not run it.
