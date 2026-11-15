# Review, queueing and restacks

This file is part of the project instructions. [AGENTS.md](../AGENTS.md) states the rules in
brief and says when to read this file; the full text here governs the details.

## Review cycle

Maintainers arrange independent review of correctness and API quality (naming, reuse, placement,
documentation and source credit). One non-authoring reviewer may cover both. Add a reviewer for a
specific uncovered question or needed expertise, not to reach an approval count.

Read the actual definitions, statements and proof arguments, and inspect representative clients.
For substantive mathematics, explain briefly what is proved, its limiting hypotheses/model/resource
conventions, and a checked instance or edge case.
For a refactor, check declaration preservation, imports and a client using the intended API.
For changed APIs and reuse refactors, follow [Check the API through its callers](workflow.md#check-the-api-through-its-callers):
inspect the actual caller and relevant sibling implementation, including generated certificates
and any representation bridge. Compilation alone does not check placement or duplicated behavior.
Check new and changed statements against
[Structures for domain objects and records](statements.md#structures-for-domain-objects-and-records) and
[Encodings in statements](statements.md#encodings-in-statements).
Read new and changed proofs against the rest of their file and nearby modules, not only the diff:
a new copy of an argument the library already makes is a finding when the
[library quality standard](../CONTRIBUTING.md#library-quality-standard) says a shared lemma pays.
Lean acceptance under audited axioms does not establish that a definition matches its intended
mathematics; state material limits of the review.

**Check every new or changed headline before anything else**
([Faithful headlines](statements.md#faithful-headlines)). In the review, quote its statement (abridged) and
compare the name, docstring, PR title and any inventory entry with what the statement proves. For
a theorem that claims a cited result, classify each hypothesis as one of:

- (i) an assumption the cited source names, stated relative to the problem, sampler or component
  it concerns. In cryptography it is listed in the
  [assumptions inventory](../manual/programs-crypto-and-probability/assumptions.md) with that source
  and a checked locator: when its row says "locator not verified" or "status pending", the
  reviewer checks the source before classifying the hypothesis as (i). For a parametric
  assumption or a vocabulary notion, the instance the theorem supplies must be the source's
  ([Security theorems](statements.md#security-theorems));
- (ii) membership of the adversary or input in the admitted class;
- (iii) a property of a generic component that the source takes as given;
- (iv) anything else: a step of the cited proof, a property of an object the proof builds, a
  caller-supplied object whose existence or efficiency is what the result proves, or unassumed
  idealized behaviour of the construction's own algorithms.

For original mathematics or internal library infrastructure
([New statements and definitions](statements.md#new-statements-and-definitions)), an absent cited source is not
a defect: check instead that its name, docstring and PR title accurately match its actual
hypotheses and scope, that it is non-vacuous and genuinely reusable, and that it does not imply a
cited endpoint was proved.

Any vacuous hypothesis blocks approval. When a statement is presented as the cited endpoint, or
advertises a headline property that its premises assume rather than establish, any (iv)
hypothesis, undisclosed deviation, overclaiming name/title or weaker stand-in blocks approval.
Such a finding is not a nit, and it is not deferred to a follow-up under
[Improving library ergonomics](workflow.md#improving-library-ergonomics); a reviewer does not offer "document
it as a milestone" in place of fixing it. Resolve it either by proving the faithful statement,
or—when the conditional statement is a useful, non-vacuous intermediate step—by renaming
(`…_of_reduction_le`, `…_of_realization`) and documenting it as a helper under rule 2 of
[Faithful headlines](statements.md#faithful-headlines): such a helper is permitted provided the published
theorem stays open and the helper never occupies its name, PR title or
[results inventory](../results/README.md) entry. Also check that the change removes or demotes any
stand-in it supersedes (rule 4). In `Cslib.Crypto`, `scripts/check_security_premises.py`
supplements this gate on elaborated premise shapes ([Security theorems](statements.md#security-theorems)),
without replacing semantic review.

**Ask what should not exist.** For each new public declaration, definition, file and test, ask
whether the library is better with it ([taste.md](taste.md)). Is it used by a caller in this PR, by
a stated next step or by a reader applying the cited result?
Is it a one-line restatement of another declaration (a `.not_superset` or negated-containment
companion, a re-export, a specialization a caller obtains with `simpa`)? Does it parallel a
neighbouring API? In the review, name what you asked the author to delete, merge or make private,
or say that you looked and found nothing to remove. A review without an answer to this question is
incomplete. Do not use a zero reference count alone to remove expected mathematical API
([Check the API through its callers](workflow.md#check-the-api-through-its-callers)).

**Name the first real property.** For each new definition, construction or transcribed algorithm,
say what its first non-trivial property is (signatures verify under the transcribed signer, the
padding is block-aligned, no revealed node is an ancestor of the hidden leaf, the simulator's
output is close to the real view) and whether this PR proves it. Unfoldings, `rfl` equalities,
`simpa` restatements of library lemmas and tests on toy instances are not results, and are not
listed under "Main results". If the property is missing, request it, or have the PR title, body
and module documentation say plainly that the change provides definitions only.

Before a published theorem enters the [results inventory](../results/README.md), a human maintainer
checks the statement against the source and records that check in a comment written by the human,
not by an agent posting from their account. Agent review alone does not admit an entry.

Before approving library changes, read the **Parallel-definition**, **Duplicate-statement** and
**Repeated-proof-block** notices in the CI job summary or step logs for the reviewed revision. Inspect both
declarations or proof blocks for each relevant candidate. Record its resolution by reuse or
generalization, or the concrete mathematical or API difference that justifies keeping both; link
an existing author explanation rather than duplicating it. Locally, after a build, use
`python3 -B scripts/parallel_defs.py --base REF` and the same command with `--theorems`;
`python3 -B scripts/proof_copies.py --base REF` compares source proof blocks. `--limit N` expands
truncated reports. Resolve skipped or incomplete scans, or record their coverage limits and
perform targeted source checks. A successful exit, an empty report or a private declaration is
not evidence of uniqueness; the tools supplement source search and semantic review.

Review of both manuals is mandatory for every change. Follow
[Maintaining the manuals](../CONTRIBUTING.md#maintaining-the-manuals): check the impact assessment
against the final revision. Check affected codebase procedures and examples from the Operator's
Manual's documented starting point; a human should be able to perform the task by hand, and an
agent should be able to reuse the account without reconstructing it from conversations. Check
human direction, roles and handoffs in the Agent Operator's Manual when the workflow changes.
A passing link or excerpt check does not replace this review.

Review API and proof quality for private helpers as well as public declarations, following
[Improving library ergonomics](workflow.md#improving-library-ergonomics). Request changes for concrete,
avoidable complexity or duplication affecting the PR; reserve nits for optional preferences.
Use inline comments for local findings, explain the problem and a concrete change or question,
and group related points. Authors may disagree: discuss the technical reason and settle the point.

After fixes, review the delta and affected reasoning. Revisit more of the code when a change
invalidates earlier conclusions. Reuse existing reviews after verifying their scope and source
identity; do not repeat a full review of unchanged code. Before merging, confirm that the current
revision is covered and required validation passes.

A coordinator may fix conflicts and review findings directly when authorized to edit the branch.
Check its head and coordinate ownership first; add commits on top, or announce a necessary rebase.
Preserve author credit and record the delta and validation.

Existing independent approval can carry across a mechanical delta when the coordinator verifies
that it preserves meaning, exported availability, attributes, imports and automation behavior,
and checks affected clients. Record that limited carry-forward decision. A typo fix may qualify,
and [Restacks](#restacks) gives a mechanical check for merging `main` or rebasing; a proof repair,
privatization, changed test coverage or a conflict resolution that changes the PR's own lines is
not automatically mechanical. Changed reasoning, API, source claims or security claims, and
uncertain cases, need fresh non-author review of the affected delta.

A non-authoring agent may independently review work from the same coordinator or account. It must
inspect the source and evidence in a separate review context and reach its own verdict; an
implementation agent's self-check or a coordinator's summary is not independent review. Reviewers
who participated in the implementation or its design cannot supply that review. The coordinator
may integrate after this review and required validation, but must not present it as self-approval
or human review. Add expertise for uncovered questions, not an approval count or agent affiliation.

Finish with a short approval or a clear request for changes. A substantive concern may need a
long explanation; a clean review does not need a checklist of everything inspected. Record the
reviewed revision, meaningful findings and resolutions once in the PR, following
[CONTRIBUTING.md](../CONTRIBUTING.md#ai-assistance-and-review).

### Approve and queue

Approving a PR's exact current head and queueing it are one step. A non-authoring reviewer with
write access who approves uses `scripts/queue_pr.py` from a trusted checkout of current `main`,
or an isolated copy obtained from a pinned revision of current `main`. Do not use the PR branch's
helper or an old copy. Invoke the trusted script by its path; from private scratch, pass `--repo OWNER/NAME`
explicitly ([queue command](../manual/workflows/agent-operations.md#queue-approved-work-and-keep-its-approval)).
Keep the approved PR head; do not refresh its branch just to obtain the tool. The helper queues
exactly that head once its required check passes; `--wait 30` waits up to 30 minutes for a running
check. Write access is sufficient authority to queue a head approved under this cycle. Approve
without queueing, and say why in the approval, when:

- human review has been requested in the PR, its comments or a linked issue; queueing is then left
  to that human or to whomever they name;
- the approval names a hold, such as an unlanded lower PR, a migration or an upstream dependency;
  queue once the hold clears.

Pending source, advisory-notice or rendered-manual review is also a hold. Inspect that material,
record the hold's resolution and link the existing proof/API/caller assessment before queueing;
do not start a waiting helper while completing CI will still produce material that needs review.
A successful check does not release a review hold, and the helper does not judge whether review
is complete. Updating `main` does not upgrade a running copy of the helper: its owner stops an old
waiter before replacing it after holds clear. The helper's waiting behavior is described in the
module docstring of `scripts/queue_pr.py` and in
[the queueing procedure](../manual/workflows/agent-operations.md#queue-approved-work-and-keep-its-approval).

The script refuses a head other than the approved one, a draft, a PR not based on `main`, a
conflicting PR and failed checks. When the reviewer cannot queue, any other non-author agent with
write access may run the same command for the approved head; coordinators sweep for approved heads
still waiting. Authors do not queue their own PRs.

**Every merge to `main` goes through the merge queue.** Enqueue with `scripts/queue_pr.py`. Never
call a direct merge endpoint: the REST merge API, a GitHub connector's `merge_pull_request` tool,
or `gh pr merge --admin`. With admin rights such a call skips the queue: it lands a combination
that the queue never built, and every queued build restarts on the new `main`. The only exception
is a human maintainer's explicit request for that PR, recorded in the PR.

### Restacks

Merge `main` into a PR only when it conflicts with `main`, needs a change on `main` to pass CI, or a
lower stacked PR has landed. The merge queue tests every PR on top of the current `main`, and `main`
does not require branches to be up to date, so refreshing an approved PR only replaces the approved
head. After the merge, regenerate the import aggregates with `lake exe mk_all`, or let the opt-in
[`leanagg` driver](../CONTRIBUTING.md#proposing-and-contributing-work) merge them and then check them
with `lake exe mk_all --check`, since the driver sees only the aggregates and not the merged tree;
never trust a `merge=union` result, which keeps deleted imports and can misorder added ones.

GitHub declines every push to the branch of a PR that is in the merge queue ("protected branch
hook declined"), even when its entry is `UNMERGEABLE`. Whoever restacks a queued PR, by hand or
with `--push` below, first removes it with **Remove from queue** on the PR page or:

```bash
gh api graphql -f id="$(gh pr view <PR> --json id --jq .id)" -f query='
  mutation($id: ID!) { dequeuePullRequest(input: {id: $id}) { mergeQueueEntry { state } } }'
```

Dequeueing merges nothing, so the author may do it; the new head is queued again only by a
non-author, once the `check_restack.py` check below passes or the delta is reviewed.

When the only conflicts with `main` are in the aggregates or `references.bib`,
`python3 scripts/restack_mechanical.py <PR> --approved-head <approved head>` does the whole restack
without running the PR's code. It requires the `check_restack.py` check below to pass for the
current head, merges `origin/main` with both drivers, writes the aggregates as `lake exe mk_all`
would for the merged tree, and runs the check on the result, both times from a checkout of
`origin/main`. It refuses any other conflict and is a dry run unless given `--push`, which pushes
the merge only when the check passes and the PR's branch still points at the head it merged. It
never queues and never comments: post its result line, and queue the new head under the rules
below once CI passes.

A restack keeps its approval when `python3 scripts/check_restack.py <approved head> <new head>`
passes and CI passes at the new head. The script replays the approved change onto the `main` that
the new head is based on, which is what the merge queue would have built from the approved head,
and passes only when the new head's tree is exactly that replay. The one exception is the
`mk_all` import aggregates, which must instead be exactly what `lake exe mk_all` writes for the new
head's tree. A conflict in the replay elsewhere, and any other difference, fails it. The replay
merges `references.bib` entry by entry, as `scripts/resolve_bib_conflict.py` does, so a
bibliography merge written by that script, with nothing else changed, passes. After
`git fetch origin`, run the script from a checkout of current `origin/main`, not of the PR's
branch, which could change it.
An approval given while a PR is based on another branch also names that branch's head, and the
check then needs `--approved-base <that head>`. Without it, the lower branch's changes, which this
review did not cover, would carry the approval if the lower PR never landed. Pass that head even
when the approved head had also merged a newer `main`: the script then replays from the merge of
the lower head and that `main`, and names it in the result. Anyone, including
the author, may post the script's result line, which names both heads and the exact command. The
non-author who queues the new head runs that command again rather than relying on the posted line.
When the script reports differences, review the paths and diffs it prints as a delta, under the
carry-forward rule above.
