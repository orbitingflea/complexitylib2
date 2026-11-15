# Roles, ownership and working on changes

This file is part of the project instructions. [AGENTS.md](../AGENTS.md) states the rules in
brief and says when to read this file; the full text here governs the details.

## Staying current with these instructions

At the start of work and when resuming, read the full applicable instructions. Coordinators
also check the instruction revisions on current `main` before assigning reviews, reviewing or
integrating work. Fetch in an authorized checkout and keep your own clean `main` current with
fast-forward updates; preserve occupied checkouts, other contributors' work and approved PR heads.
When local Git operations are restricted, read the files remotely at a pinned current-main commit.
A feature worktree or automatically supplied instruction snapshot can remain stale.

Compare with the revisions recorded in your private handoff. Read changed `AGENTS.md`,
`policy/*.md`, `CONTRIBUTING.md`, applicable upstream guidance and relevant manual sections, and
pass material changes to retained workers and reviewers before affected work continues. Record the
checked main commit and instruction revisions in that handoff; a fetched branch or an old
conversation summary alone does not establish that the guidance was read. Apply any additional
instructions for the files being changed. Explicit user directions still control; surface material
conflicts. Keep policy changes focused on recurring problems, and update linked guidance and
templates together instead of adding another exception for each incident.

## Agent roles and task ownership

Each agent works as either a **coordinator** or a **worker**. Follow the role assigned by the
human or coordinating agent; otherwise default to worker. State your role when starting work.
Changing roles does not make an author eligible to approve their own changes.

Use parallel agents where their work can proceed independently. Give each a role, clear scope
and distinct ownership, branches and mutable build outputs. The delegating agent tracks the
work and brings it to completion. When review or integration is the bottleneck, prioritize
requested fixes, reviews and landing existing work before starting more PRs.

Use issues for substantial tasks, dependencies and remaining objectives; a small fix may use its
PR as the durable task record. Search existing issues and PRs before creating a duplicate.
Record smaller delegated subtasks in the parent task. Split work into independently useful,
reviewable changes; batch closely related mechanical fixes when they share a contract and
validation. Do not create a separate issue or PR for each incidental cleanup.

### Completion and scope

Code quality is part of the acceptance criteria. Authors must resolve avoidable duplication,
unnecessary proof plumbing, misplaced shared infrastructure and incomplete migration cleanup
affecting their changes and clients before requesting approval. Passing CI or preserving theorem
statements does not discharge this work. Deferral is exceptional under
[Improving library ergonomics](#improving-library-ergonomics).

Optimize for trustworthy, reusable results, not the number of closed issues or merged PRs.
Correct statements that are faithful to their sources take priority over forward progress. When
the two conflict, fix the statement or the name, even if the milestone slips; do not land a weaker
result under the name of the stronger one
([Faithful headlines](statements.md#faithful-headlines)).
When narrowing a task, preserve its original objective and record the bounded deliverable and
remaining gap prominently. A restricted model, conditional result, or partial theorem does not
complete a broader objective. Do not silently retitle an ambitious issue into an easier completed
task.

Distinguish these dispositions in the issue:

- **Completed:** the agreed acceptance criteria are satisfied.
- **Milestone completed:** a bounded deliverable is finished; link the remaining objective.
- **Not planned (dropped):** work is intentionally stopped; preserve its results, explain what
  remains unproved, and remove the direction from `ROADMAP.md`, which has no deferred tier.

Close a milestone issue as completed when its own criteria are met. Keep the broader objective
open, or, when authorized to drop it, close it as not planned and link the completed milestone.
PR descriptions must distinguish mathematical progress from infrastructure, refactoring, and
documentation progress.

### Workers

1. Before substantial implementation, claim the existing issue or create one with concrete scope
   and completion criteria. Identify your agent/session and branch in the task record; assign
   the issue when possible. For a small fix, record this in the PR instead. A shared GitHub
   account does not identify the active agent.
2. Update the task when scope changes, a blocker needs help, work is handed off, or you stop.
   Give the state and next step, linking code or evidence. Keep unchanged polling and internal
   agent discussion out of public threads. Do not promise unattended updates after stopping.
3. Before taking over, inspect the issue, linked PR, recent commits and available activity
   evidence, and notify the owner in the task record, naming what you intend to take over.
   Explicitly released work is available immediately. A claim with no open PR and no activity by
   its owner (a commit, push or comment) for 24 hours after that notice is released without
   further action: record the takeover in the task and proceed. Work that has an open PR is not
   released by silence, since awaiting review is not abandonment; when such a PR needs author
   action (changes requested, a conflict or failing CI), a coordinator may reassign it after the
   same notice and 24 hours. Where a human has given a session a stricter standing direction on
   ownership, that direction controls for that session. Whoever takes over preserves the earlier work and its
   credit, builds on it where it is sound, and says what was carried over. A returning owner
   rebases onto the result and raises anything it lost.
4. Implement, self-review and validate. Assess both manuals for every change and update affected
   instructions, reference sections and checked examples in the same change, following
   [the manual requirements](../CONTRIBUTING.md#maintaining-the-manuals).
5. Open a PR with validation and limitations; link its issue when there is one and request
   coordinator review. Record the handoff once. Awaiting review is not abandoned work. Keep
   linked issues open until integration or an explicit disposition.
6. Address requested changes on open PRs before starting more work. Request review of the delta
   after fixes; release work explicitly if unavailable. Do not approve or merge your own PR.

Plain comments such as `active`, `blocked`, `available`, `awaiting review` and `changes requested`
are sufficient; no custom labels or recurring heartbeat comments are required.

### Coordinators

Reviewing submitted PRs is the highest priority. Keep reviews moving alongside other work.

When choosing work, give simplification and usability real priority alongside new mathematics:
replacing repeated proof plumbing with a small lemma, finishing a migration and removing what it
superseded, removing unused scaffolding, fixing recurring build or search problems, and making
results easy to find, import and apply. Choose these from the friction met during ongoing work,
and carry each improvement through to the clients that benefit. In review, ask what the next
person will no longer have to figure out; the answer should be visible in the code, examples or
tooling.

- Read the PR and existing reviews. Arrange review of uncovered questions under
  [Review cycle](review.md#review-cycle); do not commission a fresh review merely because a new coordinator arrived.
- Give a clear verdict and a useful next step. Link requested changes from the task issue when
  needed for handoff; resolve unavailable ownership using the worker rules above.
- Resolve ownership and dependency conflicts, and help stale tasks reach a useful next step.
- Require review of both the Operator's Manual and the Agent Operator's Manual, including any
  reason that no edit is needed. Make this part of reviewing and integrating each change.
  Check affected `ROADMAP.md`, the [results inventory](../results/README.md), upstream markers, the
  coordination threads in `CONTRIBUTING.md` and other documentation.
  Preserve source credit and the distinction between a completed milestone and its open objective.
- Merge only with required validation and independent review of the current revision. Reviewers
  queue the heads they approve ([Approve and queue](review.md#approve-and-queue)); coordinators queue any
  approved head still waiting and keep the queue moving: do not treat a PR as done when it is
  merely queued. Monitor queued batches until they land on `main`, merge `main` into or re-queue
  PRs ejected by conflicts or transient failures, sequence broad tree-wide refactors so they do
  not stall smaller PRs behind cold cache rebuilds, and diagnose and fix merge-queue or CI
  bottlenecks when the queue jams. The queue squash-merges: a stacked PR that edits lines a lower
  PR introduces conflicts with that PR's squashed commit and is ejected, so queue it once the
  lower PRs land (GitHub then retargets it to `main`) and it has merged `main`. Close completed
  issues and link any remaining work once the change lands.
- For your own implementation, follow the worker rules and obtain non-author review under
  [Review cycle](review.md#review-cycle).

If a shared GitHub account prevents formal approval, use one brief PR comment naming the reviewer
agent/session, revision and verdict. This is agent review, not platform or human approval.

## Working on changes

Use ordinary Git branches or isolated worktrees for substantial changes. Preserve other
contributors' work and keep mutable build outputs separate between worktrees. Agree substantial
scope through Issues or pull requests, and split large developments into independently useful,
reviewable milestones. Record unfinished work in `ROADMAP.md` without claiming it complete.

### Repository isolation

Treat the user's checkout and shared Git object database as protected infrastructure. Ordinary
worktrees share their Git object database. Never import reconstructed Git objects, install shallow
boundaries, or experiment with history repair in that shared database. Use an independent
repository with its own Git object database for such operations.

Before Git recovery or nonstandard object manipulation, verify the actual Git common directory,
object alternates, and storage sharing. The experimental repository must not use the shared
database through a gitfile, alternate object directory, or hard-linked object files. Never delete
objects, refs, worktree registrations, or metadata belonging to another session. Worktrees also
share one stash stack, so `git stash pop` can apply and drop another session's entry: never push,
pop, apply or drop stash entries in a shared checkout or its worktrees. Keep work in progress as a
commit on your own branch or as a patch file in your scratch directory
([procedure and recovery](../manual/workflows/agent-operations.md#isolate-work-and-build-outputs)).

Keep mutable build outputs separate. Integration experiments must be contained so their failure
cannot damage the user's checkout or another worker's repository.

Machines are shared between agents. Stop only processes and tasks you started, by PID or task
ID; never use pattern-based kills such as `pkill -f`, which also hit other agents' builds. Keep
scratch files under a directory or name unique to your agent. Concurrent Lean builds can
exhaust the host's file handles before its processors; agree on a limit on concurrent builds
(see [the troubleshooting chapter](../manual/workflows/troubleshooting.md#diagnose-too-many-open-files-in-system)).

### Placement and reuse

Place reusable definitions and general lemmas in the lowest suitable mathematical module.
Specialized theorem modules should import their prerequisites. During review, look for general
APIs buried in a particular application or proof. Extract them to their natural shared home and
update the affected clients in the same PR, applying [the migration rule](../AGENTS.md#proof-hygiene). A second
application importing the first for general infrastructure is a concrete signal to do this.
Keep unrelated architectural redesign out of scope; use the exceptional deferral rule below when
a technical dependency prevents completing the extraction.

Do not prove a lemma that the library, CSLib, Mathlib or core already has, even privately or by
re-deriving it inline inside another proof: use it, or make a private original public. After a
build, `python3 scripts/parallel_defs.py --theorems` lists the theorems a change adds or modifies
whose statement already exists; CI posts the same notice. It cannot see a fact re-derived inside a
proof, so search for an existing lemma first. When a proof you add or change needs a substantial
argument that another proof makes, derive it once; the
[library quality standard](../CONTRIBUTING.md#library-quality-standard) says when a shared lemma pays.

"Lowest suitable" does not mean the most widely imported file. Adding a public declaration changes
a module's public interface and can invalidate downstream build artifacts, even for clients that do
not use the new declaration. Prefer a small topic module imported by its consumers over appending
to a hub such as `Foundations/Data/List/Basic.lean` or `Probability/PMF.lean`; #569 records the
measured fan-out. Exposed definition bodies (`@[expose]`) belong to the interface too, so expose
only what downstream proofs must unfold.

### Improving library ergonomics

When work exposes library friction, improve the relevant API, lemma, proof strategy, documentation
or automation in the original PR and carry the improvement through to its affected clients. Search
existing APIs in this repository, Mathlib and CSLib before adding or re-proving anything, including
private helpers. Making a duplicate private does not resolve duplication.

Reviewers must consider whether a different statement, representation, invariant, decomposition or
proof strategy would make the mathematics more natural to state, prove and apply. Look beyond
local tactic edits: applying an existing theorem, choosing a better induction argument or adding a
small shared lemma can remove whole blocks of encoding, case or state-update bookkeeping. Assess
the resulting client proofs and required imports as well as the new API. Preserve the mathematical
claim, models, encodings, quantifiers and independent resource bounds when simplifying.

Require a concrete benefit from a proposed alternative: representative checked usage or a focused
proof comparison explaining what becomes clearer or easier. Prefer the smallest generally useful
change that fits the mathematical API and upstream design. Challenge speculative abstractions and
arbitrary conventions; proof length alone is not a finding, and a personal preference does not
justify rewriting an otherwise clear argument.

Defer cleanup only when a specific technical dependency or independently substantial redesign
prevents completing it with the PR. The reviewing coordinator must explicitly accept the reason,
and a linked issue must name the remaining declarations, affected clients, proposed approach and
responsible owner. A separate prerequisite PR may keep review focused, but the dependent PR waits
for it. Creating a follow-up issue or citing scheduling pressure does not discharge cleanup that
can be completed with the change.

Keep the evidence proportional. A small improvement needs a short explanation and a checked
client; broader API changes need representative affected clients and an in-repository migration
plan. Investigate elaboration time and other performance costs when material, without requiring
a benchmark campaign or separate design study for every small improvement.

### Check the API through its callers

Before handing off a changed API or reuse refactor, inspect a representative caller and the
nearby implementations of the same idea. Reviewers repeat this check against the final change:

- **Named access and semantic facts.** Use record fields or existing accessors in public
  statements. When callers decode a Boolean matcher, unfold an embedding's coordinate arithmetic,
  or rebuild field-projection certificates, provide the reusable characterization, range fact or
  generated certificate they need and use it in the caller. Preserve the encoding layout and
  resource bounds when migrating records; check a caller of the generated `enc_structure` rules.
- **One implementation of shared behavior.** A game or algorithm should call its named handler
  instead of repeating the same dispatch or transition code in its definition and proofs.
  Different representations may need distinct implementations; keep their differences explicit
  and connect them with the appropriate simulation or conversion lemma.
- **Shared mathematics across representations.** Before repeating an argument in a sibling
  module, look for a general statement and an existing bridge, such as PMF integration against
  its induced measure. Derive the specialization when the bridge preserves the hypotheses and
  intended dependencies. Put shared facts in a small topic module and migrate the existing
  consumers together; do not create an abstraction whose callers must reconstruct the proof.
- **Public API by purpose.** Keep expected properties of public objects available, including
  matcher characterizations and embedding range facts. Keep one-proof wrappers around casts,
  cache layouts or intermediate states private. Inspect references and automation before changing
  visibility, but do not use a zero reference count alone to remove useful mathematical API.

The handoff should identify the representative caller and the reasoning or representation work
it no longer repeats, or explain why separate implementations remain necessary. A concise
before/after example or source reference is enough; no separate audit report is required.

## Writing in issues and PRs

Write for human collaborators. Start with the point; use short paragraphs or a small flat list.
Use headings, tables and checklists only when they make the content easier to read. Give technical
detail where it explains a finding or decision; omit routine inspection narratives and boilerplate.

Small PRs usually need one or two paragraphs plus validation/review links and a brief AI
disclosure. State what changed, why, and important limitations. Keep evidence in one place;
link to it instead of copying full reports, hashes or logs across threads.

Write for a contributor who has not followed the task. Introduce the problem or mathematical
setting, explain the central idea, and say what the change enables. Introduce specialized terms
and notation before relying on them. For substantial developments, give a short roadmap
explaining how the main steps connect and why consequential choices are needed. Use an example,
equation, or before/after comparison when helpful. Scale the explanation to what the reader
needs to understand, and put validation, manual impact and AI disclosure after it.

Comments should add a finding, answer, decision, blocker or useful handoff. Keep CI polling and
internal agent discussion out of public threads. Reply directly to questions and fixes; a short
"Fixed in <commit>" is enough when the change is clear. Be courteous, welcome disagreement, and
do not imply that an agent review is human review.
