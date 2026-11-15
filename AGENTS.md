# Project Instructions

cslib-frontier is the frontier formalization library for **cslib** (`leanprover/cslib`): a Lean 4
library covering computer science generally, including algorithms and data structures,
complexity, cryptography, logic and models of computation. Library modules must be upstreamable
unchanged apart from rewriting `CslibFrontier.` → `Cslib.`. General mathematics destined for Mathlib
and local project scaffolding are documented exceptions, recorded in each module's `-- upstream:`
marker.

Follow the mathematical, API and style conventions of the pinned cslib (`AGENTS.md`,
`CONTRIBUTING.md` and `CODESTYLE.md` in `.lake/packages/cslib`). This repository's workflow,
validation and test layout are defined here, in `policy/` and in `CONTRIBUTING.md`. `ROADMAP.md`
and the per-area files under `roadmap/` record outstanding directions.

## How to read these instructions

This file is kept under 32 KB because some agent clients load only that much of it. It states
every rule in brief, most important first. The full text of each rule lives in `policy/`, and is
binding: read the file for a task before doing that task.

| Before you… | Read in full |
|---|---|
| state or change a theorem, definition or encoding | [policy/statements.md](policy/statements.md) |
| add a public declaration, or review one | [policy/taste.md](policy/taste.md) |
| review, approve, queue or restack a PR | [policy/review.md](policy/review.md) |
| claim, hand off, coordinate or open work | [policy/workflow.md](policy/workflow.md) |
| build, validate, add a file or bump the pin | [policy/build-and-files.md](policy/build-and-files.md) |

At the start of work and when resuming, read this file and the policy files for your task from
current `main`, not from a feature worktree or an automatically supplied snapshot, which can be
stale. Coordinators recheck the revisions of `AGENTS.md`, `policy/*.md`, `CONTRIBUTING.md` and the
relevant manual sections on current `main` before assigning reviews, reviewing or integrating,
pass material changes to retained workers and reviewers, and record the checked commit in their
private handoff ([details](policy/workflow.md#staying-current-with-these-instructions)). Explicit
user directions still control; surface material conflicts. Keep policy changes focused on
recurring problems, update linked guidance and templates together, and prefer shortening a rule
to adding an exception.

## What matters most

1. **Faithful statements come before progress.** Lean checks proofs, not whether a statement says
   what its name, docstring and PR title claim. Do not land a weaker result under the name of a
   stronger one, and do not assume the hard part as a hypothesis
   ([Faithful headlines](#faithful-headlines)).
2. **The library is better smaller.** Every public declaration, definition and file must earn its
   place. Do not add restatements, unused scaffolding, parallel notions or lemmas that Mathlib,
   CSLib or this library already has ([Placement and reuse](#placement-and-reuse);
   [policy/taste.md](policy/taste.md) shows the patterns to avoid).
3. **Review judges what Lean cannot:** the statement, the design and what should not exist. A
   review that only confirms the build, placement and process is incomplete
   ([Review cycle](#review-cycle)).
4. **Code quality is part of acceptance.** Passing CI or preserving statements does not discharge
   avoidable duplication, proof plumbing or unfinished migration
   ([Completion and scope](#completion-and-scope)).
5. **Merges to `main` go through the merge queue**, never a direct merge call
   ([Approve and queue](#approve-and-queue)).
6. **Shared machines and checkouts are protected.** Never use the shared stash, pattern-based
   kills, or history repair in a shared Git database ([Repository isolation](#repository-isolation)).
7. **Records are honest.** Say what was proved, what was only assumed, what was not checked, and
   that agent review is not human review.

## New statements and definitions

Full text: [policy/statements.md](policy/statements.md).

When a declaration claims to formalize a cited result, give the precise source version and
locator and map the source claim to Lean: quantifiers, hypotheses, models, encodings and resource
conventions. Verify locators and quotations against the source itself; invented or misattributed
ones block approval. New mathematics needs no source; label it original. Search for an existing
notion before adding a public definition, and explain any parallel one. Reviewers may ask for a
checked instance where a definition holds and one where it fails.

### Faithful headlines

A *headline* is a theorem presented as a cited result or as the property its name advertises
("security", "soundness", "hardness", "is PPT"), whether by its name, docstring, module
documentation, manual page, PR title or [results inventory](results/README.md) entry.

1. **A headline states the result it names.** Its quantifiers, hypotheses, model, admitted
   adversaries or inputs, resource conventions and conclusion match the source, apart from
   deviations the docstring names and review accepts as the same theorem in another formal setting.
2. **Disclosure does not license a weaker headline.** A result is a *stand-in* when it assumes a
   step of the cited proof, something about an object its own proof builds (a reduction,
   simulator, extractor, hybrid, decoder), or a caller-supplied object whose existence or
   efficiency is what the result proves; when it idealizes the construction's algorithms; when it
   proves a fixed finite instance instead of a family; when it weakens the notion, model or
   adversary class; or when it rests on an assumption other than the source's that the source's
   is not proved or cited to imply, such as a stronger or novel one. A useful stand-in may land only as a named step (`…_of_reduction_le`,
   `…_of_realization`) whose docstring opens by saying it is not the cited result, with the cited
   objective left open. Listing the gap under "Limitations" does not meet this rule.
3. **No vacuous headlines.** Hypotheses that cannot hold together, or a conclusion that follows
   trivially, are a misformalization even when documented. Check a satisfying instance.
4. **The faithful statement supersedes its stand-ins.** The change that proves it deletes or
   demotes them, with their docstrings, manual text, `ROADMAP.md` lines and inventory entries.

Stand-ins already on `main` are defects to fix, not precedents (#5293 for cryptography).

### Structures for domain objects and records

Define domain objects, problem instances, certificates, configurations and multi-field records as
documented `structure`s with named fields, not tuple synonyms or bare products in problem sets;
no `.1.2` projection chains (#1764). Keep plain `×` for generic combinators, mathematical products
and uncurried inputs such as a verifier's `Instance × List Bool`. Migration is tracked in #4385.

### Encodings in statements

An encoding is part of what a statement claims, so statements show every encoding without making
the reader parse the same nested one repeatedly. For new and changed statements:

1. **Name repeated compound encodings.** A nested application of `encPair`, `encList`,
   `encOption`, `encSum`, `encFramed`, `encPi` or `encDPi` that occurs in the types of three or
   more public declarations of a module gets a named `abbrev`, used everywhere.
2. **Document the layout** in the `abbrev`'s docstring: order of parts, framing, tag bits.
3. **Keep it reducible:** `abbrev`, not `def`, and never a `local notation`.
4. **Name domain encodings:** a formula, graph, circuit or instance is encoded by a named,
   documented definition.
5. **Declare structure encodings with `enc_structure`.** A migration keeps the encoded words,
   adds a checked equality with the former tuple encoding to the tests, and says "encoded words
   unchanged" in the PR. Changing a layout needs a coordinator's scope decision.
6. **Show meaning-bearing choices** (unary or binary, graph and matrix representation, framing
   that changes a length bound) in the name or the first docstring line.
7. **No hidden defaults:** no elaborator or typeclass chooses an encoding (`enc%`, #1830, is parked).

### Security theorems

A security theorem may assume only (a) named hardness assumptions, stated relative to the setup
sampler or component they concern; (b) that the adversary is in the admitted class; and (c)
properties of components that the cited result itself takes as given.

It must not assume anything about an object its proof constructs (a reduction, distinguisher,
simulator, extractor or hybrid): not its advantage, its class membership or its efficiency. It
must not take from the caller an object whose existence or efficiency is the cited result, assume
the scheme's own algorithms are ideal, or stop at a bound for parameters an `∃` chooses after the
adversary. Write each reduction as an explicit program with an efficiency witness proved from the
adversary's certificate, and prove the asymptotic theorem by applying the assumption through that
witness. Asymptotic statements come first; a concrete bound `Adv(A) ≤ f(Adv(B_A))` is a lemma.
Names and docstrings state the model, the notion and any deviation from the source.

Every named assumption is listed in the
[assumptions inventory](manual/programs-crypto-and-probability/assumptions.md) as *standard* (a
cited source states it; the docstring cites the definition with a checked locator and names every
material difference), *novel* (no source states it, or it strengthens its source; the docstring
says so, relates it to standard assumptions and says why it is plausible) or *vocabulary* (a
generic notion that becomes an assumption only through the instance a theorem supplies). A row
says "locator not verified" until a reviewer has confirmed the locator at the source. A theorem
claiming a cited result rests on the source's assumption, on one review accepts as the same in
another formal setting, or on one the source's implies; otherwise it is a stand-in. A novel
assumption may support a result presented as original and named for it.
`scripts/check_security_premises.py` and `scripts/check_hardness_assumptions.py` supplement these
rules; they do not replace semantic review.

## Review cycle

Full text: [policy/review.md](policy/review.md). Independent review covers correctness and API
quality. One non-authoring reviewer may cover both; add a reviewer for an uncovered question, not
to reach a count. A review does the following, in this order.

1. **Check every new or changed headline first.** Quote its statement (abridged) and compare the
   name, docstring, PR title and inventory entry with what it proves. For a cited result, classify
   each hypothesis: (i) an assumption the source names (in cryptography, listed in the
   [assumptions inventory](manual/programs-crypto-and-probability/assumptions.md) with a checked
   locator, and for a parametric or vocabulary notion the instance supplied is the source's); (ii) membership of the adversary or input
   in the admitted class; (iii) a property of a generic component the source takes as given; (iv)
   anything else. Any vacuous hypothesis blocks approval. For a statement presented as the cited
   endpoint, or one advertising a headline property that its premises assume rather than
   establish, any (iv) hypothesis, undisclosed deviation, overclaiming name or weaker stand-in
   blocks approval; it is not a nit, is not deferred to a follow-up, and is not resolved by
   "document it as a milestone". Fix the statement or rename it as a step, and check that the
   change removes or demotes any stand-in it supersedes.
2. **Ask what should not exist.** For each new public declaration, definition, file and test, ask
   whether the library is better with it ([policy/taste.md](policy/taste.md)). Is it used by a
   caller in this PR, by a stated next step or by a reader applying the cited result? Is it a
   one-line restatement of another declaration, or a specialization a caller gets for free? Does
   it parallel a neighbouring API? Name what you asked the author to delete, merge or make
   private, or say that you looked and found nothing to remove. A review without an answer to
   this question is incomplete. A zero reference count alone does not justify removing expected
   mathematical API.
3. **Name the first real property.** For each new definition, construction or transcribed
   algorithm, say what its first non-trivial property is (signatures verify, the padding is
   block-aligned, the simulator's output is close) and whether this PR proves it. Unfoldings,
   `rfl` equalities and restated library lemmas are not results; do not let them be listed as
   main results. If the property is missing, request it or have the PR and module documentation
   say plainly that only definitions are provided.
4. **Read the mathematics.** Read the actual definitions, statements and proof arguments and a
   representative client. For substantive mathematics, say briefly what is proved, its limiting
   hypotheses, model and resource conventions, and a checked instance or edge case. Consider
   whether a different statement, representation or proof strategy would be more natural to
   state, prove and apply ([Improving library ergonomics](#improving-library-ergonomics)).
5. **Check reuse.** Read new proofs against the rest of their file and nearby modules, and read
   the Parallel-definition, Duplicate-statement and Repeated-proof-block notices in CI for the
   reviewed revision. Record each relevant candidate's resolution. An empty report is not
   evidence of uniqueness.
6. **Check the documentation the change affects**, including both manuals
   ([Maintaining the manuals](CONTRIBUTING.md#maintaining-the-manuals)).
7. **Give a clear verdict** for an identified revision: a short approval or a specific request
   for changes, with the limits of the review. A clean review needs no checklist of everything
   inspected. Lean acceptance does not establish that a definition matches its intended
   mathematics.

After fixes, review the delta and the reasoning it affects; do not repeat a full review of
unchanged code. An approval carries across a mechanical delta only when a coordinator verifies
that meaning, exports, attributes, imports and automation are preserved; changed reasoning, API,
source claims or security claims need fresh non-author review.

A non-authoring agent may review work from the same coordinator or account, in a separate
review context, reaching its own verdict. Anyone who took part in the implementation or its
design cannot supply that review. If a shared GitHub account prevents formal approval, use one
brief PR comment naming the reviewer agent or session, revision and verdict. Agent review is
never presented as human review. Before a published theorem enters the
[results inventory](results/README.md), a human maintainer checks the statement against the
source and records that in a comment the human writes.

### Approve and queue

Approving a PR's exact current head and queueing it are one step. The non-authoring reviewer
queues the approved head with `scripts/queue_pr.py`, run from a trusted checkout of current
`main` ([command](manual/workflows/agent-operations.md#queue-approved-work-and-keep-its-approval)).
Authors do not queue their own PRs. Approve without queueing, and say why, when human review has
been requested or the approval names a hold (an unlanded lower PR, a migration, or pending
source, advisory-notice or rendered-manual review). A passing check does not release a review
hold; do not start `queue_pr.py --wait` while running CI will still produce notices or rendered
pages that need review.

**Every merge to `main` goes through the merge queue.** Never call a direct merge endpoint: the
REST merge API, a GitHub connector's `merge_pull_request` tool, or `gh pr merge --admin`. With
admin rights such a call skips the queue, lands a combination that was never built, and restarts
every queued build. The only exception is a human maintainer's explicit request for that PR,
recorded in the PR.

A queued PR is not done. Coordinators watch queued batches until they land, requeue ejected PRs,
and sequence tree-wide refactors so they do not stall smaller PRs behind cold rebuilds.

### Restacks

Merge `main` into a PR only when it conflicts with `main`, needs a change on `main` to pass CI,
or a lower stacked PR has landed; refreshing an approved PR only replaces the approved head.
Dequeue a queued PR before pushing to it. A restack keeps its approval when
`python3 scripts/check_restack.py <approved head> <new head>` passes, run from a checkout of
current `origin/main`, and CI passes at the new head; the non-author who queues reruns the
command. `scripts/restack_mechanical.py` performs aggregate-only and bibliography-only restacks.
Never trust a `merge=union` result for the import aggregates; regenerate them with
`lake exe mk_all`.

## Proof hygiene

These rules exist for readability and robustness. When following one would make a particular
proof or statement worse (longer, harder to read, or working against the automation), deviate,
say why in the PR, and propose amending the rule. Reviewers judge a deviation by the rule's
purpose, not its letter.

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment. A
  `maxHeartbeats` above the 200000 default, or zero (unlimited), also needs a reviewed entry in
  `scripts/heartbeat_allowlist.txt`, which `scripts/check_hygiene.py` enforces and keeps
  shrinking; prefer reducing the proof's cost.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`, so that later steps do not depend on the shape of a
  `simp` normal form. A `simp` whose result is closed by a finishing tactic that does not depend
  on that shape (`omega`, `linarith`, `nlinarith`, `norm_num`, `ring`, `grind`, `tauto`), as in
  `simp [h]; omega`, counts as terminal, as in Mathlib's flexible-tactic linter.
- Definitions as terms, not `by` blocks, where possible.
- Prefer `do` notation for sequential monadic computations, including probabilistic experiments
  in theorem statements. Keep explicit `bind` in laws about bind and proof steps that use those
  laws directly, and for operations such as `PMF.bind` between different universes. Retain
  concise point-free composition where naming an intermediate value would not help.
- Before the first supported release, do not add deprecated aliases or compatibility wrappers
  for renamed, moved, removed or privatized declarations. Update all in-repository clients
  (library, tests, results inventory and guide) and remove the superseded interface in the same
  change. Upstream shims ([File rules](#file-rules)) are the one exception.
- `CslibFrontierTests/Axioms.lean` audits all declarations for dependencies beyond `propext`,
  `Classical.choice` and `Quot.sound`. Add a named `#print axioms` guard only when a result is
  meant to depend on fewer axioms than these three.
- Watch for vacuous hypotheses: when a structure bundles bounds, provide at least one instance in
  the test suite.

## Agent roles and task ownership

Full text: [policy/workflow.md](policy/workflow.md). Each agent works as a **coordinator** or a
**worker**; follow the assigned role, default to worker, and state your role when starting.
Changing roles does not make an author eligible to approve their own changes. Give parallel
agents distinct scope, branches and build outputs; the delegating agent brings their work to
completion. When review or integration is the bottleneck, do requested fixes, reviews and landing
before starting more PRs. Use issues for substantial tasks and search for existing ones first; do
not open an issue or PR for each incidental cleanup.

### Completion and scope

Authors resolve avoidable duplication, unnecessary proof plumbing, misplaced shared
infrastructure and incomplete migration cleanup affecting their changes and clients before
requesting approval. Optimize for trustworthy, reusable results, not the number of closed issues
or merged PRs. When narrowing a task, keep its original objective visible and record the bounded
deliverable and the remaining gap; a restricted model, conditional result or partial theorem does
not complete a broader objective. Distinguish **completed**, **milestone completed** (link what
remains) and **not planned** (remove it from the roadmap, which has no deferred tier).

### Durable records

The issue owns scope, ownership and remaining work; the PR owns the change, validation and
review. Link between records instead of mirroring them, and record tested and reviewed revisions
once. A local path alone is not a handoff. At integration, say briefly what landed and what
remains.

### Workers

1. Claim the issue or create one with concrete scope and completion criteria, naming your agent
   or session and branch. A shared GitHub account does not identify the active agent.
2. Update the task when scope changes, a blocker needs help, work is handed off, or you stop.
3. Before taking over work, inspect the issue, PR, recent commits and activity, and notify the
   owner in the task record. Explicitly released work is available immediately. A claim with no
   open PR and no activity by its owner for 24 hours after that notice is released: record the
   takeover and proceed. A PR that needs author action (changes requested, a conflict or failing
   CI) may be reassigned by a coordinator after the same notice and 24 hours; a PR awaiting
   review is never released by silence. Preserve the earlier work and its credit.
4. Implement, self-review and validate. Assess both manuals and update affected instructions,
   reference sections and checked examples in the same change.
5. Open a PR with validation and limitations and request coordinator review.
6. Address requested changes before starting more work. Do not approve or merge your own PR.

### Coordinators

Reviewing submitted PRs is the highest priority. Give simplification and usability real priority
alongside new mathematics: replacing repeated proof plumbing with a small lemma, finishing a
migration and removing what it superseded, deleting unused scaffolding, and making results easy
to find, import and apply. Give a clear verdict and a useful next step; resolve ownership and
dependency conflicts; help stale tasks reach a next step. Merge only with required validation and
independent review of the current revision, through the queue
([Approve and queue](#approve-and-queue)). For your own implementation, follow the worker rules
and obtain non-author review.

## Working on changes

Full text: [policy/workflow.md](policy/workflow.md). Use ordinary branches or isolated worktrees,
and split large developments into independently useful, reviewable milestones. Preserve other
contributors' work and source credit.

### Repository isolation

Treat the user's checkout and the shared Git object database as protected infrastructure.

- Never import reconstructed Git objects, install shallow boundaries or experiment with history
  repair in a shared database; use an independent repository.
- Never delete objects, refs, worktree registrations or metadata belonging to another session.
- Worktrees share one stash stack: never push, pop, apply or drop stash entries. Keep work in
  progress as a commit on your own branch or a patch file in your scratch directory.
- Stop only processes you started, by PID or task ID; never `pkill -f` or similar.
- Keep build outputs and scratch files separate per agent, and agree a limit on concurrent Lean
  builds ([troubleshooting](manual/workflows/troubleshooting.md#diagnose-too-many-open-files-in-system)).

### Placement and reuse

Place reusable definitions and general lemmas in the lowest suitable mathematical module, and
extract general APIs buried in an application, updating the affected clients in the same PR.
"Lowest suitable" does not mean the most widely imported file: prefer a small topic module to
appending to a hub, and `@[expose]` only what downstream proofs must unfold.

Do not prove a lemma that this library, CSLib, Mathlib or core already has, even privately or
inline: use it, or make a private original public. Search before proving;
`python3 scripts/parallel_defs.py --theorems` and the CI notices help but cannot see a fact
re-derived inside a proof.

### Improving library ergonomics

When work exposes library friction, improve the API, lemma, proof strategy, documentation or
automation in the original PR and carry it through to affected clients. Require a concrete
benefit: checked usage or a focused comparison showing what becomes clearer or easier. Proof
length alone is not a finding, and a personal preference does not justify a rewrite. Defer
cleanup only for a specific technical dependency or an independently substantial redesign,
accepted by the reviewing coordinator and recorded in an issue naming the declarations, clients,
approach and owner. A follow-up issue does not discharge cleanup that fits in the change.

### Check the API through its callers

Before handing off a changed API or reuse refactor, inspect a representative caller and the
nearby implementations of the same idea; reviewers repeat the check on the final change. Use
named fields and semantic facts rather than making callers decode representations; keep one
implementation of shared behavior; derive specializations from a general statement and an
existing bridge; keep expected properties of public objects public and one-proof wrappers
private. The handoff names the caller and what it no longer has to repeat.

## Writing in issues and PRs

Full text: [policy/workflow.md](policy/workflow.md#writing-in-issues-and-prs). Write for a human
who has not followed the task. Start with the point: the problem or mathematical setting, the
central idea, and what the change enables, then validation, manual impact and AI disclosure.
Small PRs need a paragraph or two. Keep evidence in one place and link to it. Comments add a
finding, answer, decision, blocker or handoff; keep CI polling and internal agent discussion out
of public threads. Do not imply that an agent review is human review.

## Lean development: use the Lean MCP server first

Full text: [policy/build-and-files.md](policy/build-and-files.md). Bootstrap a cold checkout with
`scripts/cache/ensure.sh` before elaborating or building. Use MCP goal inspection, diagnostics
and theorem search while iterating. When a build is needed, use
`scripts/build.sh <affected modules and representative clients> --wfail --iofail`, and
`scripts/worktree.sh` for isolated worktrees. Bare `lake` and MCP commands do not bootstrap the
cache.

## Validation sequence

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

For Lean, dependency or build changes, all of these and the other CI checks must pass on the
final revision before integration. A successful hosted run for that revision supplies full
validation; run `scripts/check.sh` locally only when asked or when hosted coverage is
unavailable. During development, check affected modules and representative clients;
`scripts/check.sh --quick --no-full-fallback [--base REF]` is the local checkpoint, and exit
status 3 means "run focused checks and leave the full run to CI". Documentation-only changes need
consistency and link checks, not a rebuild. `lake exe mk_all` regenerates `CslibFrontier.lean`
after adding a file; new tests go in `CslibFrontierTests/`. Details and what each mode covers:
[policy/build-and-files.md](policy/build-and-files.md#validation-sequence).

## File rules

Full text, including the file template: [policy/build-and-files.md](policy/build-and-files.md#file-rules).

1. **Path and namespace mirror cslib.** Multi-tape machine files use the upstream root namespace
   `Turing`, everything else `Cslib.*`.
2. **File template:** Apache header, `module`, an `-- upstream:` marker, `public import` for API
   dependencies and plain `import` for proof-only ones, and a module docstring describing the
   actual API and its sources. `@[expose]` only what clients must unfold. `Authors:` names the
   originator of the issue and the human whose agents implemented it.
3. **Upstream marker:** `candidate`, `submitted #N @SHA`, `vendored <owner>:<branch> @SHA
   (unsubmitted)`, `merged @SHA` (a deprecated shim), or `local-only (reason)`. A port keeps the
   original authors.
4. **Every module publicly imports `Cslib.Init`** (through `CslibFrontier.Init`).
5. **Reuse upstream first:** search cslib and in-flight upstream PRs before defining anything.
6. **Bit strings** live in `Cslib.BitString`; they add with `+`, single bits with `^^`.
7. **Citations** use `references.bib` keys, added in key order.

## Staying current with upstream

Keep the cslib pin on an upstream `main` SHA and coordinate bumps in focused dependency PRs.
When the pin adopts merged work, the same commit replaces the superseded local file with its
deprecated shim ([details](policy/build-and-files.md#staying-current-with-upstream)).

## Design commitments (do not re-litigate casually)

- Base pin is upstream cslib `main` at a SHA; never a fork.
- One parametric machine extending upstream `Turing.Cfg`/`Turing.Action`, with `Choose := Id`
  recovering `MultiTapeTM` and `Choose := Set` recovering `MultiTapeNTM`, step-exactly.
- Computability predicates are `@[fun_prop]`-registered; loops go through Hoare-style
  `iterate_spec` rules and the Aesop `polytime` set.
- Definitions and public results use plain computability with independent time and space bounds:
  upstream `ComputableInTimeAndSpace…` and the notions built on it, such as `ComputableInPolyTime`.
  The tidy computability calculus is being deleted (#862); tidiness survives only as a machine-level
  kernel inside the Machines layer, used inside proofs of plain rules.
- Programs are `PFunctor.FreeM` values; a machine's clocked run is itself a program.
- The universal machine is an interpreter program certified by the calculus, not a hand-built
  machine.
- Do not cite the unpublished draft "A Small Calculus of Finite Computation" in source or PR text.

## PR titles (for upstream PRs and here)

`type(scope): description`, type ∈ `feat|fix|doc|style|refactor|test|chore|perf|ci`, no trailing
period. Disclose AI assistance in the PR description, as cslib's policy requires.
