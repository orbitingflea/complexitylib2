# T23: Dijkstra and notation declarations under upstream's #949 item-8 rule (read-only check)

Checked: `origin/dijkstra-loglinear-upstream` at `f1714dfc`, which sits on
`origin/wordram-notation-scoped` (`7c68492f`), which sits on upstream `0b838c43`. Only declarations
that `7c68492f`, `8b6e1085`, `5f321a8d` and `f1714dfc` add or change were checked
(`git diff --stat 0b838c43 f1714dfc`: 10 Dijkstra modules, `Structured.lean` +22, `Notation.lean`,
the test, the abstract and the bridge). No Lean file and no T22 branch was changed. No build was run.

## 1. The rule, and how upstream finds the candidates

**Rule.** Issue cslib-community/complexitylib#949, comment "New item 8. Declarations whose only
outside reference was a named axiom guard" (SamuelSchlesinger, 2026-10-25T08:57:09Z, read with
`gh issue view 949 --json`):

> #996 (`ComplexityTests/Axioms.lean`) and #1004 (the other test modules) delete the named
> `#print axioms` guards that only restate the global axiom audit. For the 1,257 library
> declarations below, one of those guards was the only reference outside the declaration's own
> module, counting `Complexity/`, `ComplexityTests/`, `abstracts/` and the guide. For each
> declaration:
>
> - **API:** its docstring and the module doc's *Main* list should state its purpose.
> - **Plumbing:** make it private, following #926 (privatize by intent).
>
> […] Uses inside the defining module do not count.
>
> - **†** marks the 148 declarations that are not named in their module doc. […] for them only
>   the docstring needs checking.
> - **‡** marks 114 declarations with a `simp`, `fun_prop`, instance or similar attribute.
>   Automation can use these without a syntactic reference, so check before privatizing.

"Privatize by intent" is `CONTRIBUTING.md` § "Public surface under the module system" (upstream/main,
same text at `f1714dfc`, lines 77–85):

> A helper is proof plumbing: a step meaningful only inside one proof, or a fact about a
> module-local construction, encoding or intermediate quantity. Helpers are `private` by default.
> […] What stays public, even if nothing outside the module uses it yet. Facts stated only in
> terms of public definitions that a user of those definitions would expect: characterizations
> (`_iff`), bounds, […] simp and extensionality equations, […]. Reference counts are evidence about
> current use, not the criterion; privatize by intent.

**How it was applied** (worked examples on upstream/main, all in our base `0b838c43`):

- `a89f8dc3` (#1010, Complexity): "entries marked † but not ‡. Ten declarations are API and get Main
  entries. The docstring of `MIP.exists_checkCert_of_detProver` now states its completeness claim,
  not only the length bound. Two are proof plumbing used only in their own file and become
  private". A follow-up commit in the same PR then made `isPolyTime_queryTable` public again,
  because it is "the polynomial-time bound of the Main definition queryTable".
- `137f8dee` (#1009, PCP): first privatized three declarations, then made two of them public
  again with Main entries ("the evaluation law of proofQueries and the round trip", "API under
  privatize-by-intent").
- `458b6378` (#1021, Computability) and `08ef1db2` (#1020, Crypto): Main entries only, plus
  docstring corrections, for every † declaration ("All declarations were verified to have
  existing docstrings and represent public API").
- The `Algorithms.WordRAM` area itself (PR #1012, issue comment 2026-10-25T09:56:18Z): Main entries
  for the † declarations (`PrefixSums.Dynamic.instruction_bound_log`, `execOp_frame`) and
  `Stack.frame`, with every other declaration confirmed as public API.

In practice, then: the default is a *Main* entry plus a docstring that states the claim. `private`
is used only for a step that makes sense in one proof alone, and reviewers reversed it twice when
the declaration was a law of a public definition.

**How upstream finds the candidates.** The list in the issue was computed once, from the `.ilean`
data of `Complexity`, `ComplexityTests` and `ComplexityAbstracts` at baseline `b3cbabf9` plus #996
and #1004. The issue shows no script for it. The general tool is
`scripts/audit_queries.py references [--unused] PREFIX...` (present at `f1714dfc`). CONTRIBUTING
lines 94–97 name it for this use, and it reads the same `.ilean` data. It scans only `Complexity.*`
modules (`scripts/lean_outputs.py:233`), so abstract and bridge declarations are never
candidates. Tests and abstracts count as outside references. The issue's list is a one-off
snapshot: every area PR for item 8 has merged (#1009/#1010/#1012/#1013/#1014/#1016–#1021, issue
comments through 12:17Z). Nothing recurring will find declarations that a later PR adds.

**What I ran** (read-only; the worktree was checked out detached at `f1714dfc`, using the build
outputs of the clean `f1714dfc` checkout `worktrees/lean/lead-gate-T22`):

```
python3 -I scripts/audit_queries.py references [--unused] \
  --build-dir <lead-gate-T22>/.lake/build/lib/lean --no-build-check \
  Complexity/Algorithms/WordRAM/Dijkstra/ Complexity/Computability/WordRAM/Notation.lean \
  Complexity/Computability/WordRAM/Structured.lean abstracts/ComplexityAbstracts/Dijkstra{Bridge,Abstract}.lean
```

The script lists 118 public declarations in the 10 Dijkstra modules. 101 have a reference from
another module. The 17 below have none (the `--unused` output). I cross-checked each with
`git grep -w <name> f1714dfc`. The grep hits outside the defining file are other declarations
that share the short name (`ListInstance.le_maxWeight`, FusionTree's `encode_length`, the common
words `remaining`/`potential`), plus the docstring mention of `heapDijkstra_spec` at
`ComplexityTests/WordRAMDijkstra.lean:53`, which is not a reference.

I also ran upstream's changed-file lint (`scripts/check_changed_files.py --base 0b838c43`, against
the same build outputs). It passes: "Changed-file lints passed (12 changed library module(s), 1 new
test file(s))". So every name in our current *Main* lists resolves.

**How I counted references** (the issue's convention):

- Uses only inside the same file: not an outside reference. These are the candidates.
- Uses only in tests: an outside reference, so not a candidate. Example: `logLinearSpec`
  (`LogLinear.lean:410`), referenced only by `ComplexityTests/WordRAMDijkstra.lean:42`.
- Uses only in the abstract or bridge: an outside reference, so not a candidate. Example:
  `logLinearStatement` (`LogLinear.lean:423`), referenced only by `DijkstraBridge.lean:222`.
- Uses from another Dijkstra module count as outside references, as in the issue (other module).

## 2. The list

Namespace `Cslib.Algorithms.WordRAM.Dijkstra` unless stated. Lines are at `f1714dfc`, on the
declaration keyword. Outside references: 0 for all of them, by `.ilean` and by `git grep -w`.

| # | Declaration | file:line | † (not in module doc) | ‡ | Docstring | The rule asks | Reason |
|---|---|---|---|---|---|---|---|
| 1 | `heapDijkstra_spec` | `LogLinear.lean:397` | no (Main results) | – | yes, short | nothing; optionally a fuller docstring | The literal item-8 case: `f1714dfc` deleted its `#print axioms` guard, its only outside reference. It is the main correctness theorem of the program, so it is API and stays public. Its docstring "**Correctness and running time of the structured program.**" states the purpose. The bound is only in the Main entry, which is why a89f8dc3-style reviewers may ask for it in the docstring. |
| 2 | `ListInstance.distOf` | `LogLinear.lean:53` | yes | – | yes | Main definitions entry | Decodes the machine state into the abstract tentative distances. It occurs in the signatures of the public `OuterInv` (field `inv`) and `potential` chain, so it cannot be private alone. |
| 3 | `ListInstance.visitedOf` | `LogLinear.lean:58` | yes | – | yes | Main definitions entry | Same as 2 (the visited set). |
| 4 | `ListInstance.remaining` | `LogLinear.lean:62` | yes | – | yes | Main definitions entry | Same as 2; used in the public `potential` (line 67). |
| 5 | `ListInstance.potential` | `LogLinear.lean:67` | no (Main definitions) | – | yes | nothing | Already listed and documented. |
| 6 | `ListInstance.OuterInv` | `LogLinear.lean:73` | no (Main definitions) | – | yes | nothing | Already listed and documented. |
| 7 | `heapSetup_spec` | `LogLinear.lean:96` | yes | – | yes | Main results entry | Spec of the public program `heapSetup`; same kind as upstream's WordRAM phase specs (`VanEmdeBoas.insert_call`, `PrefixSums.Dynamic.execOp_frame`), which got Main entries. |
| 8 | `heapRound_spec` | `LogLinear.lean:199` | yes | – | yes | Main results entry | Spec of the public program `heapRound`; the potential argument the module doc describes. |
| 9 | `heapExit_spec` | `LogLinear.lean:379` | yes | – | yes | Main results entry | The exit step: an empty heap means exact distances in the output cells. |
| 10 | `pushNew` | `HeapProgram.lean:178` | yes | – | yes | Main definitions entry | Heap insertion, a part of the program like `siftUp` and `extractMin` (both in Main definitions). It cannot be private: it is in the exposed body of the public `edgeBody` (line 190), which `heapDijkstra` unfolds to, and the test runs `heapDijkstra` with `decide +kernel` (`WordRAMDijkstra.lean:57`) (*inferred* from the module-system rule that exposed public bodies cannot name private constants). |
| 11 | `siftDown_spec` | `HeapSift.lean:623` | no (Main results, line 28) | – | yes | nothing | Spec of the public `siftDown`; used at line 832 of its own file. |
| 12 | `decodeDist_encodeDist` | `Invariant.lean:67` | yes | ‡ `@[simp]` | **no** | docstring + Main entry, keep public | A simp round-trip equation of the public `encodeDist`/`decodeDist`: "simp […] equations" stay public (CONTRIBUTING). The missing docstring is exactly what the issue singled out ("Two have no docstring"). |
| 13 | `Instance.le_maxWeight` | `Invariant.lean:87` | yes | – | yes | Main results entry, keep public | A bound stated only in terms of the public `Instance.weight`/`maxWeight` (Statement.lean), the twin of the public `ListInstance.le_maxWeight` (`ListEncode.lean:182`). The plausible alternative is `private` (it is used only at line 230, inside `Inv.step`'s proof); under "bounds […] stay public" I expect API. |
| 14 | `Instance.dist_le_edge` | `Invariant.lean:121` | no (Main results, line 38) | – | yes | nothing | Already listed and documented. |
| 15 | `ListInstance.encode_length` | `ListEncode.lean:117` | yes | – | yes | Main results entry | The length of the public input encoding `encode`; a fact a user of `encode` expects. |
| 16 | `Instance.instQuiverVertex` | `Statement.lean:68` | yes | ‡ instance | no | nothing | An anonymous instance, used through `⟶`/`Quiver.Path` by `dist` and by Invariant, Bridge and LogLinear. It cannot be private: a private instance stays local (CONTRIBUTING), which would break those uses. The docstring of `Vertex` (line 64) describes the quiver. Upstream's lists do not ask for docstrings on instances. |
| 17 | `ramExactEval` | `ExactNotation.lean:98` | yes | ‡ notation | yes | nothing | The syntax-node name of the tactic `ram_exact_eval`, which the module doc lists under Main definitions and Tactics. Upstream's own `Cslib.WordRAM.ramEval` (`Notation.lean:163`) is in the same position and is on no item-8 list. |

Outside the 10 Dijkstra modules:

- `Structured.lean`: the only addition is `Cslib.WordRAM.ExecWithin.loop_potential` (line 369).
  It is referenced by `Dijkstra/LogLinear.lean`, has a docstring, and is already in Main results
  (lines 64–65). Nothing to do. The 25 unreferenced declarations the script lists in
  this file (e.g. `Exec.loop_once`, `ExecWithin.alu`) are upstream's and out of scope.
- `Notation.lean` (`7c68492f`): it adds no declarations. It makes the statement syntax and
  `ram_eval` `scoped` and rewrites the module doc. Nothing to do.
- `DijkstraAbstract.lean`, `DijkstraBridge.lean`: not candidates. Item 8 covers only library
  declarations, and `audit_queries.py` scans only `Complexity.*`. Every bridge declaration has a
  docstring (`DijkstraBridge.lean:53–206`), and upstream's bridges keep their helpers public too
  (17 of 20 upstream `*Bridge.lean` files have no `private`). Nothing to do.
- `ComplexityTests/WordRAMDijkstra.lean`: not a source of declarations.

## 3. Estimated edit size

For the recommended form (Main entries, one docstring, no `private`):

| File | Edit | Lines |
|---|---|---|
| `Dijkstra/LogLinear.lean` | Main definitions: `distOf`, `visitedOf`, `remaining` (+2–3). Main results: `heapSetup_spec`, `heapRound_spec`, `heapExit_spec` (+4–6). Optional: give `heapDijkstra_spec`'s docstring its bound (+1–2, −0–1). | +6 to +11 |
| `Dijkstra/Invariant.lean` | Docstring for `decodeDist_encodeDist` (+1). Main results: `decodeDist_encodeDist` and `Instance.le_maxWeight` (+2–3). | +3 to +4 |
| `Dijkstra/ListEncode.lean` | Main results: `ListInstance.encode_length`. | +1 to +2 |
| `Dijkstra/HeapProgram.lean` | Main definitions: `pushNew`. | +1 |
| all other files | none | 0 |
| **Total** | 4 files, doc comments only | **about +11 to +18, −0 to −1** |

Under the module system, docstring and module-doc edits leave the exported `.olean` unchanged
(CONTRIBUTING lines 71–74), so importers do not rebuild. After the edit,
`scripts/check_changed_files.py` must still pass, so each new Main entry must name an existing
declaration.

**Would a `private` change break a use elsewhere?** None of the 17 is referenced outside its own
module, so no test, abstract or bridge would break. Within their modules, two constraints apply:
`pushNew` (10) and `instQuiverVertex` (16) cannot become private (see their rows), and
`distOf`/`visitedOf`/`remaining` (2–4) could become private only together with `potential`,
`OuterInv` and `heapSetup/Round/Exit_spec`. Those three specs mention `OuterInv` in their
statements, and `heapDijkstra_spec`'s statement mentions none of them (`LogLinear.lean:397–400`),
so the whole round layer could be private. That alternative is 8 `private` keywords plus removing
the 2-entry Main definitions section of LogLinear (about 8 lines changed, −4 lines). It needs a
build to confirm, and it goes against the module doc, which presents the invariant and the
potential as the proof's structure. I do not recommend it. Upstream's WordRAM precedent (#1012)
kept phase specs public with Main entries.

## 4. Abstract and `dijkstra_logLinear`

Nothing in the recommended edit, or in the `private` alternative, touches
`abstracts/ComplexityAbstracts/DijkstraAbstract.lean`, `DijkstraBridge.lean`, `dijkstra_logLinear`
(`DijkstraAbstract.lean:263`), `logLinearStatement` or `logLinearSpec`. All edits are in module
docs and docstrings of `Complexity/Algorithms/WordRAM/Dijkstra/{LogLinear,Invariant,ListEncode,HeapProgram}.lean`.
`dijkstra_logLinear` stays byte-identical.

## 5. Recommendation

**Do it in the Dijkstra PR before opening**, as one small doc commit on `dijkstra-loglinear-upstream`,
when the CoS allows T22 edits. The reasons:

1. Leaving it to upstream's sweep means nobody does it. Item 8 is a one-off list computed at
   baseline `b3cbabf9`, and all its area PRs have merged, so declarations added by our PR are on
   no list.
2. Our own `f1714dfc` created the item-8 situation: it deleted the axiom guard that was
   `heapDijkstra_spec`'s only outside reference. Upstream's reviewers review new PRs against the
   rule of the day. They asked for Main entries and full docstrings in #1009/#1010/#1021.
3. The edit is small and safe: about 15 lines of doc in 4 files, no statement change, no
   `private`, no rebuild of importers, and the abstract is untouched.

Reading of the task, not a decision I made: the CoS said "no edits to T22 branches until I say".
So this report only proposes the commit. The T22 owner applies it later.
