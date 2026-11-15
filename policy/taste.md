# Taste: what earns a place in the library

This file is part of the project instructions ([AGENTS.md](../AGENTS.md)). The other policy files
say what is required. This one says what good looks like, through patterns that have landed on
`main`, passed review, and should not have. Authors check their change against it before
requesting review; reviewers use it to answer "what should not exist?" and "what is the first
real property?" ([Review cycle](../AGENTS.md#review-cycle)).

A reader of this library wants a small number of statements they can trust and apply. Every extra
public name is something they must read, tell apart from its neighbours and keep working. Prefer
the change that leaves fewer declarations and one way to say each thing.

## A result is something a reader could not have written down for free

Not results, and not listed under "Main results":

- **Unfoldings.** `Desc.runOracle_eq_toMachine`, where `Desc.runOracle` is defined as the
  right-hand side, is `rfl`. So is an `X_iff` that is `Iff.rfl` against the definition's body.
- **Restated library lemmas.** A `simpa` wrapper around `Fin.findSome?_eq_none_iff`,
  `List.length_map` or `Embedding.injective` under a domain name.
- **Properties true by construction.** A predicate defined to describe a list, with one theorem
  saying that the list just built satisfies it.
- **Tests.** `decide` or `#guard` on a toy instance shows a definition computes; it does not
  establish the general property.

Interface lemmas are a different thing. Under the module system a public definition's body is
not exposed, so clients cannot unfold it and rely on its `@[simp]`, `_apply` and `_iff`
specifications, including those `enc_structure` generates; their proofs are `rfl` inside the
defining module, and they are legitimate API. They are still not listed under "Main results". What
should not exist is a bare `rfl` restatement of an exposed definition or `abbrev` that plays no
part in a `simp` normal form.

If a module has definitions and none of its theorems would survive this list, say so: the PR
title and module documentation call it definitions only.

## Prove the first real property with the definition

A transcribed algorithm or new construction comes with the property that shows the transcription
means something: a signer's signatures verify; padding is block-aligned; no revealed tree node is
an ancestor of the hidden leaf; a simulator's output is close to the real view. A faithful
transcription with no such theorem is unvalidated, however careful its source mapping.

## One name per fact

- **No negated or weakened companions.** If `A ⊂ B` is a theorem, do not add `¬ B ⊆ A`; callers
  write `h.not_superset`. If `=` is proved, do not add `⊆` in each direction.
- **No corollary grids.** Do not enumerate {subset, equality} × {each class} × {each encoding}.
  State the general theorem and the one or two instances that a caller or a cited source needs.
- **No eta-copies or re-exports** of a theorem under a second name or namespace.
- **No arity series.** After `_pair` and `_triple`, the next lemma is the `k`-ary one, not `_six`.
- **No wrapper definitions** that only rename a library function (`FixedBytes.take` for
  `Fin.take`, `addInt` for `+`, `leafCount h` for `2 ^ h`). Introduce a named operation when it
  carries content or when a second implementation exists, not because one might.

## A declaration has a caller

A public declaration is used by another module, by the stated next step of its issue, or by a
reader applying the cited result. Its own test file is not a caller. "Prerequisite" and "layer 1"
do not license surface that nothing consumes: land it with its first consumer, or keep it private
until then. Efficiency certificates follow the same rule: a certificate for an experiment that no
theorem consumes is not needed.

## Replace, do not accumulate

When a change introduces a better notion, it migrates the old one's clients and deletes it,
except under an accepted deferral
([Improving library ergonomics](../AGENTS.md#improving-library-ergonomics)). A third eavesdropping game beside two existing ones, a second
CPA formalism bridged to the first, a new first-success construction beside two others: each
leaves the reader to work out which is authoritative. Bridging lemmas between parallel notions
are a sign that one of them should go ([Faithful headlines](../AGENTS.md#faithful-headlines),
rule 4).

## Hypotheses are checked one at a time

- Every hypothesis of a corollary is needed by that corollary, not inherited from the headline it
  follows. Ask whether a stronger lemma already on `main` removes it.
- No proof arguments the definition ignores (`sha256 input (_h : Valid input)`).
- No hypothesis whose variables do not appear in the conclusion or in another hypothesis that
  does.
- A hypothesis bundle repeated across many theorems becomes a `structure` or a `variable` block.
- No auto-param (`:= by fun_prop`) on a mathematical hypothesis of a headline.

## Words match what is proved

- "Exact", "complete", "native", "uniform" and "secure" describe the theorem, not the intent. If
  only the exponent draw is native, the title does not say the scheme is.
- A module docstring describes mathematics, not the process that produced it: no review notes,
  provenance of checks or status of other PRs.
- A sentence about the source's theorem is not placed where it reads as a claim about the Lean
  one.
- A locator names the line, page or section you looked at in the pinned source.

## Small facts are shared

An arithmetic identity needed in a second file is a lemma in a shared module, not a second inline
`have` (`((q - a % q : ℕ) : ZMod q) = -a` appeared in five files). A migration that makes helper
lemmas into pass-throughs deletes them and tidies their call sites in the same change.
