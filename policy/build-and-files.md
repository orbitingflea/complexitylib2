# Building, validation and file rules

This file is part of the project instructions. [AGENTS.md](../AGENTS.md) states the rules in
brief and says when to read this file; the full text here governs the details.

## Lean development: use the Lean MCP server first

Bootstrap a cold checkout with `scripts/cache/ensure.sh` before Lean elaboration or building.
Retry when needed artifacts are missing or toolchain/dependency changes require new ones;
a new commit or branch switch alone does not require a manual bootstrap if outputs are warm.
MCP's `lean_build(fetch_cache=true)` fetches Mathlib's cache, not cslib-frontier's. Cache misses
or download failures leave Lean to compile missing outputs. The helper's actual retry behavior
and opt-out for warm local builds are documented in [the cache guide](../scripts/cache/README.md).

Use MCP goal inspection, diagnostics and theorem search while iterating. When a build is needed,
use `scripts/build.sh <affected modules and representative clients> --wfail --iofail`;
reserve `scripts/check.sh --quick --no-full-fallback` for local validation checkpoints.
`scripts/build.sh [Lake build arguments]`, `scripts/check.sh` and `scripts/worktree.sh create`
run the same bootstrap automatically. Bare `lake` and MCP commands do
not invoke it. If MCP tools are unavailable, say so and use the smallest shell check.

Use `scripts/worktree.sh` for isolated worktrees; follow its
[cache and isolation guidance](../scripts/cache/README.md). Exported API changes can rebuild
dependents; proof edits can too when axiom dependencies change or a client uses `import all`.
See [the module-system guidance](../CONTRIBUTING.md#public-surface-under-the-module-system).

## Validation sequence

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` runs every locally reproducible step of CI's `source-checks` and `lean-checks`
jobs, whose results feed the required `ci-checks` aggregator. `scripts/full_check.py` lists the
steps and records why the remaining ones stay CI-only. The manual checks catch source and link
drift; they do not replace review of the manuals' meaning and usability.
For Lean, dependency or build changes, all of these must pass on the final source revision before
integration. A successful hosted run covering that revision supplies full validation; do not
repeat it locally merely to satisfy a second reporting requirement. Run local full validation
(`scripts/check.sh`) only when explicitly requested or hosted coverage is unavailable; changes
to validation machinery also need direct checks of the changed behavior. Required CI and
merge-group checks still apply.

During development, check affected modules and representative clients before requesting review;
a PR may use CI for the full run. For documentation-only changes, check consistency, links and
any Lean examples introduced; a local whole-library rebuild is unnecessary.

At local validation checkpoints, `scripts/check.sh --quick --no-full-fallback [--base REF]`
builds changed Lean modules and their transitive importing clients, checks import aggregates and
runs the source-only lints. It compares with the merge base of local `origin/main` and does not
fetch. It is not full validation. Exit status 3 means the change is outside what quick mode
supports: run focused checks for the changed files and representative clients, and leave the full
run to hosted CI. Documentation-only checks need not invoke quick mode.

`lake exe mk_all` regenerates `CslibFrontier.lean` after adding a file. New test files go in
`CslibFrontierTests/`; the test library is built from a Lake glob, so there is no aggregator to update.

## File rules

1. **Path and namespace mirror cslib.** `CslibFrontier/Foundations/Data/Encoding.lean` is destined
   for `Cslib/Foundations/Data/Encoding.lean`; multi-tape machine files use the upstream root
   namespace `Turing`, everything else `Cslib.*` as upstream does.
2. **File template:** use the Apache header below, `module`, an `-- upstream:` marker,
   `public import` for API dependencies and plain `import` for proof-only dependencies. Add a
   module docstring describing the actual API, with applicable `## Main definitions`,
   `## Main results` and `## References` sections; omit empty sections. Use `public section`
   with `private` helpers, or per-declaration `public`. Add `@[expose]` only to definitions
   whose bodies downstream clients need to unfold; do not default to blanket exposure.
   ```lean
   /-
   Copyright (c) <year> <authors>. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: <authors>
   -/

   module
   -- upstream: candidate

   public import CslibFrontier.Init

   /-!
   # <Module topic>

   <Purpose, public API and mathematical sources.>
   -/

   public section
   ```
   In a new file, `<authors>` names (a) the originator(s) of the issue or proposal the file
   implements: the person named in the issue's "Originated by" field when someone wrote the issue
   on their behalf, and otherwise the issue's author; and (b) the person whose agents did the
   implementation (the human, not a fleet or bot account). The rule applies going forward, not
   retroactively: existing headers stay unless someone asks for a correction. A port still keeps
   the original authors (rule 3).
3. **Upstream marker** values: `candidate`, `submitted #N @SHA` (a copy of an open cslib pull
   request at its head `SHA`), `vendored <owner>:<branch> @SHA (unsubmitted)` (a copy of a branch
   of a contributor's cslib fork that has no pull request yet), `merged @SHA` (a deprecated shim
   for a module that cslib provides from its commit `SHA`; see below), `local-only (reason)`.
   Nothing is `local-only` without a reason; valid reasons are project scaffolding and tests of
   local-only files.
   When the pin adopts a module, whether it was upstreamed from here or copied from upstream
   work, the commit that bumps the pin replaces the file with a deprecated shim instead of
   deleting it, so that downstream `import CslibFrontier.X` keeps working with a warning. The shim
   keeps the file's copyright header and otherwise contains only the following, where `Cslib.X`
   is the upstream module and the date is that of the pin bump:
   ```lean
   module -- shake: keep-all
   -- upstream: merged @SHA

   public import Cslib.X

   deprecated_module "upstreamed to cslib" (since := "YYYY-MM-DD")
   ```
   `deprecated_module` is Lean's core command, and Mathlib writes its stubs the same way:
   importing the shim warns and names `Cslib.X` as the replacement. Because `--wfail` builds fail
   on that warning, the same commit points every in-repository import at `Cslib.X`; only the
   generated `CslibFrontier.lean` imports the shim, under its `-- deprecated_module: ignore`
   pragma. Shims are the one exception to the rule against compatibility wrappers under
   [Proof hygiene](../AGENTS.md#proof-hygiene). Delete a shim once its `since` date is six months old,
   Mathlib's window for removing deprecations; a pin bump that moves or removes `Cslib.X`
   repoints or deletes the shim itself.
   A port keeps the authors of the files it is ported from: v1's PCP internals, Sipser–Lautemann
   and containment internals are by Bolton Bailey, so their ports carry
   `Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger` and `Authors: Bolton Bailey, Samuel
   Schlesinger`; ports of Christian Reitwiessner's work carry his name likewise. Check the v1
   file's `Authors:` line before porting.
4. **Every module publicly imports `Cslib.Init`** (through `CslibFrontier.Init`); the test driver
   runs `checkInitImports`.
5. **Reuse upstream first.** Before defining anything, search cslib (`.lake/packages/cslib/Cslib`,
   or the local `../cslib/Cslib` checkout) and the in-flight PRs recorded in source markers, and
   consult the coordination threads in `CONTRIBUTING.md` (Upstreaming). A thin local copy of an
   unmerged upstream PR (or an unsubmitted branch of an upstream contributor) is allowed at the
   mirrored path, keeping the
   original authors and declaration names, marked `-- upstream: submitted #N @SHA` (or
   `vendored …`). A copy holds only what the pinned cslib lacks: when a PR modifies an existing
   cslib file, the copy contains just its additions. When the pin adopts the merged work, the
   copy becomes a deprecated shim (rule 3).
6. **Bit strings.** Declarations about bit strings and the cube `ι → Bool` (operations, sampling,
   Fourier analysis, sensitivity, influence, codes) live in `Cslib.BitString`; only the named
   Boolean functions `parityOn`, `parity`, `threshold`, `majority`, `strictMajority` sit in `Cslib`
   beside cslib's `BooleanFunction`. Bit strings add with `+` (Mathlib's `BooleanRing Bool`),
   single bits with `^^`.
7. **Citations.** Cite textbook sources in docstrings via `references.bib` keys
   (`[AroraBarak09]`, `[Papadimitriou94]`, `[Sipser2013]`, `[Jukna2012]`, …). Add new entries in cslib's
   format at their place in key order (`scripts/check_hygiene.py` checks the order and that every
   cited key has an entry), keeping bibliography and project-documentation changes in focused
   commits.

## Staying current with upstream

Keep the cslib pin on an upstream `main` SHA. Coordinate updates in focused dependency PRs,
fixing breakage in the same change; update it within another task when that task needs new
upstream code or turns a merged module into its shim. Merely inspecting upstream does not
require a pin bump.

Run `scripts/upstream_sync.py` during synchronization work. Inspect changed, merged or closed
upstream PRs against source markers, `-- vendored:` comments and module docstrings; preserve
documented local adaptations and contributor work rather than blindly replacing copies. When
adopting merged work, advance the pin past it and, in the same commit, replace the superseded
local file with its deprecated shim ([file rule 3](#file-rules)). Record unresolved decisions in
the module's marker or docstring, the coordination threads in `CONTRIBUTING.md`, or a linked issue
instead of expanding an unrelated PR.
