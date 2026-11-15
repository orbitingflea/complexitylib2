# Statements and definitions

This file is part of the project instructions. [AGENTS.md](../AGENTS.md) states the rules in
brief and says when to read this file; the full text here governs the details.

## New statements and definitions

When a declaration claims to formalize a cited result, give its precise source version and locator
and map the source claim to Lean: quantifiers, hypotheses, models, encodings and resource
conventions. An accurate paraphrase is sufficient; identify material differences or weaker scope.
Reviewers check the primary source and mapping. If quoting, verify the exact words and locator
against that source; invented or misattributed quotations block approval. New mathematics and
new proof ideas need no source; label them as original without implying a cited endpoint was proved.

Whether a new definition needs checked examples on both sides (an instance where it holds and one
where it fails) is for the author and reviewers to judge; reviewers may ask for them when a
definition could be vacuous or trivially satisfied.

Search for existing notions before adding public definitions. Reuse or extend them when they
express the intended mathematics; explain a non-obvious decision to introduce a parallel notion.
Syntactic similarity is a prompt to inspect reuse, not proof that models should be identified.
Generalization should improve concrete clients without obscuring semantics or making inference
and usage harder.

### Faithful headlines

A *headline* is a theorem presented as a cited result or as the property its name advertises
("security", "soundness", "hardness", "proof of knowledge", "is PPT"), whether by its name, its
docstring, its module documentation, a manual page, a PR title or a
[results inventory](../results/README.md) entry. Lean checks proofs, not whether a statement says what
its presentation claims, so this is the part of a change that review exists to check.

1. **A headline states the result it names.** For a cited result, its quantifiers, hypotheses,
   model, admitted adversaries or inputs, resource conventions and conclusion match the source,
   apart from deviations that the docstring names as part of the result's scope and that review
   accepts as the same theorem in a different formal setting (for example, the library's two-world
   advantage in place of the source's `|Pr[b' = b] - 1/2|`, with the factor of two carried
   through). Original mathematics and internal library infrastructure need no cited source
   ([New statements and definitions](#new-statements-and-definitions)); their names, docstrings and
   PR titles state their actual hypotheses and scope, they are genuinely reusable, and they do not
   imply that a cited endpoint was proved.
2. **Disclosure does not license a weaker headline.** A result is a *stand-in* when it assumes a
   step of the cited proof, something about an object that its own proof builds (a reduction,
   simulator, extractor, hybrid or decoder), or a caller-supplied object whose existence or
   efficiency is what the result proves. It is also a stand-in when it replaces the construction's
   algorithms with idealized ones, proves the claim for a fixed finite instance instead of a
   family, weakens the notion, model or adversary class (including parameters chosen after the
   adversary), or rests on an assumption other than the source's that the source's assumption is
   not proved in the library or cited to imply, such as a stronger or novel one
   ([Security theorems](#security-theorems)). A theorem the source itself states conditionally,
   such as a hardness-magnification implication, is not a stand-in when its hypothesis is the
   source's.
   A useful, non-vacuous stand-in may land as an intermediate step, never as the headline for the
   cited result: its name states the condition (`…_of_reduction_le`, `…_of_realization`), its
   docstring opens by saying it is a step or helper and not the cited result, it cites the source
   as "a step of" or "after" rather than as its endpoint, the cited objective stays open, and
   neither the PR title nor the results inventory presents it as the cited result. Listing the gap
   under "Limitations", in the PR body, at the end of a docstring or in an inventory scope note
   does not meet this rule.
3. **No vacuous headlines.** A headline—or a step landed under rule 2—whose hypotheses cannot hold
   together, or whose conclusion follows trivially (an extractor that ignores the transcript), is a
   misformalization even when it is documented. When a hypothesis might be unsatisfiable, check a
   satisfying instance.
4. **The faithful statement supersedes its stand-ins.** A change that proves the faithful
   statement deletes or demotes every stand-in it supersedes, together with their docstrings,
   manual text, `ROADMAP.md` lines and inventory entries. Search for them by conclusion, by
   `_of_…` names and in the milestone's issue, not only by name.

Stand-ins already on `main` are misformalizations to fix under these rules, not precedents to copy.
Record them in an issue (#5293 for cryptography). Domain contracts, such as
[Security theorems](#security-theorems) for cryptography, refine what counts as a named assumption
and a generic component in their area.

### Structures for domain objects and records

Define domain objects, problem instances, certificates, configurations, and multi-field algorithm
contexts, states or records as documented `structure`s with named, documented fields—not as tuple
type synonyms (`abbrev HittingSetInstance := (List ℕ × List (List ℕ)) × ℕ`) or bare product types
in problem sets (`Set (List (ℕ × ℕ) × ℕ × ℕ)`, `Set (Graph × ℕ)`). A `structure` gives every
component a name and docstring in editor hover and `doc-gen4`, supports dot-notation, prevents
swapping homogeneous components, and avoids the `.1.2` positional projection chains banned by
[#1764](https://github.com/cslib-community/cslib-frontier/issues/1764). Encode field-tuple
structures with `enc_structure` under [Encodings in statements](#encodings-in-statements) below.

Keep plain `Prod` (`×`) where the pair is not a domain record: generic binary combinators,
mathematical Cartesian products, and uncurried multi-argument function inputs that merely pair an
instance with a witness or second operand (such as an NP verifier `Instance × List Bool → Bool` or
a binary operation `α × β → γ`). Existing tuple abbreviations and bare-product problem sets are
migrated under [#4385](https://github.com/cslib-community/cslib-frontier/issues/4385).

### Encodings in statements

An encoding is part of what a statement claims, so statements show every encoding; but a reader
should not have to parse the same nested encoding again and again. New declarations, and
declarations whose statements change, follow these rules. Existing code is brought into line by
a tracked sweep ([#1656](https://github.com/cslib-community/cslib-frontier/issues/1656)), and the
encoding-readability lint checks rule 1 against a per-module baseline that may only fall.

1. **Name repeated compound encodings.** A *compound encoding* is a term of type
   `α ↪ List Bool` in which one of the generic combinators `encPair`, `encList`, `encOption`,
   `encSum`, `encFramed`, `encPi` or `encDPi` is applied to another application of one of them,
   such as `encPair encS (encOption encBool)`. When the same compound encoding, up to the names of
   local variables, occurs in the types of three or more public declarations of a module, give it
   a named `abbrev` and write the name in those statements. Occurrences inside larger terms count,
   including bounds that restate an input encoding, such as
   `fun p => (encPair encS (encOption encBool) p).length`. The varying encodings become the
   `abbrev`'s parameters. Define it in that module, or in the lowest module its users share, and
   once a name exists, use it instead of restating its body.
2. **Document the layout.** The `abbrev`'s docstring says what is encoded and how: the order of
   the parts, which parts are framed, and any tag bits. For example, `QueryMachine.encStateRead`
   is "a state paired with the bit read; the state is framed".
3. **Keep it reducible.** Use `abbrev`, not `def`. The statement is definitionally identical to
   the spelled-out one: `enc_len`, `fun_prop`, instance search and `simp` with the combinators'
   lemmas such as `length_encPair` see through the name, and so does `rw`, except where the name
   heads the rewritten term. Syntactic tools may not: `omega` takes `(encX e p).length` and its
   spelled-out form as different atoms, so the facts it combines must use one form, which can
   need small proof edits. Do not abbreviate an encoding with a `local notation`: the lint reads
   it as an atom, so it hides a compound encoding, and the documentation shows its expansion.
   When you touch a module that abbreviates a compound encoding with one, replace it with a
   documented `abbrev`.
4. **Name domain encodings.** Encode a mathematical object (a formula, graph, circuit or problem
   instance) by a named, documented definition, not by a compound spelled out inside a larger
   encoding, even where it occurs only once.
5. **Declare structure encodings with `enc_structure`.** When a structure is encoded as the
   tuple of its fields in declaration order, declare the encoding with `enc_structure`, which
   generates the embedding, its `_apply` equation and its `fun_prop` certificates (for degree,
   `ComputableInO`, workspace budgets and `ComputableInPolyTime`), rather than writing a `.trans`
   embedding and proving the certificates by hand. The
   [Operator's Manual](../manual/workflows/choosing-models.md#write-the-contract-before-the-proof)
   shows the declaration and what it generates. Migrating a tuple to a record keeps its encoded
   words, which `IsPPTOn` and the other machine predicates read. `enc_structure` frames every
   field but the last and adds no nested grouping, so it reproduces a right-nested tuple such as
   `encPair a (encPair b c)` but not a left-grouped one such as
   `encPair (encPair a b) (encPair c d)`. For a left-grouped tuple, nest sub-records whose
   generated layout matches, or define the encoding as `encOfEquiv` into the former tuple encoding
   and keep the named projection and constructor certificates. Every migration, including a
   right-nested one, adds a checked equality `encX r = <former tuple encoding> (…)` to the tests
   (usually `rfl`) and states "encoded words unchanged" in the PR. Changing the layout needs a
   coordinator's scope decision and a checked transport of efficiency and security in both
   directions; a claim that the re-association is polynomial-time equivalent is not enough.
6. **Show meaning-bearing choices.** Unary versus binary numbers, the representation of graphs
   and matrices, and framing that changes a length bound stay visible: the name or the first line
   of its docstring states the choice (`encUnaryPair`, not `encArgs`). A name must not hide one.
7. **No hidden defaults.** Do not let an elaborator or typeclass choose an encoding for a type;
   the `enc%` proposal (#1830) is parked.

### Security theorems

A security theorem may assume only (a) named hardness assumptions, that is, Prop-valued
definitions documented as assumptions (`F.DDH setup`, `DecisionLWE …`, `OneWay f`,
`QuadraticResiduosityHard setup`, or a named collision-resistance or circular-security assumption
on a component the scheme uses), stated relative to the setup sampler or component they concern;
(b) that the adversary is in the admitted class (`A.IsPPT`, `IsOraclePPT …`, or the model's
circuit bound); and (c) properties of components that the cited result itself takes as given,
supplied by the caller.

It must not assume anything about an object that its proof constructs, whether from the adversary
or not (a reduction, distinguisher, simulator, extractor or hybrid): not its advantage or success,
its membership in an adversary class, or its efficiency. Nor may it take from the caller an object
whose existence or efficiency is the content of the cited result, such as the knowledge extractor
of a proof of knowledge or the simulator of a zero-knowledge proof. It must not assume that the
scheme's own algorithms behave like idealized ones (for example, that the key generator's output
is indistinguishable from an ideal key law) unless the cited result names that as an assumption.
And it may not stop at a bound for parameters that an `∃` chooses after the adversary
(`∃ m₀ m₁, Adv(A) ≤ Adv(B A m₀ m₁)`); a uniform reduction chooses them itself.

Every named assumption, including a security notion assumed of a caller's component, is listed in
the [assumptions inventory](../manual/programs-crypto-and-probability/assumptions.md) as *standard*,
*novel* or *vocabulary*.

- **Standard.** A cited source states it, up to deviations that do not strengthen it. Its
  docstring cites the source definition it formalizes, with a locator checked at the source
  ([New statements and definitions](#new-statements-and-definitions)), and names every material
  difference from it: for example uniform instead of non-uniform adversaries, a decision instead
  of a search problem, a restricted modulus, noise law or parameter range, or a setup law that
  need not be efficiently samplable.
- **Novel.** No cited source states it. A deviation that strengthens an assumption relative to
  its source, such as admitting more adversaries, giving them more information or dropping a
  restriction that the source relies on, makes it novel, unless a cited source states that form
  or the library proves it from the standard one. Its docstring says that it is novel to this
  library, how it relates to standard assumptions (it follows from one, implies one, or neither)
  and why it is plausible. Where an insecure instance is easy to give, a test shows that the
  assumption fails for it.
- **Vocabulary.** A generic notion parameterized by the objects whose security it states (games,
  ensembles, an adversary predicate, a bound), such as `Game.Indistinguishable` or
  `ComputationallyIndistinguishable`. It becomes an assumption only through the instance that a
  theorem supplies. A primitive's or problem's own security notion is never vocabulary, even in a
  concrete form against a caller's adversary class and bound.

A row of any status says "locator not verified" until its locator has been read at the source.
An author removes the phrase only in a pull request whose body records that check (the source's
version or URL and what was read there), and only once a reviewer has confirmed it at the source.
Whether a parametric assumption (with a setup, noise or error law, an adversary class or a bound)
or a vocabulary notion is the source's depends on the instance that a theorem supplies, so under
a cited headline review checks that instance against the source: `DecisionLWEWithErrors` with a
correlated error law is not plain LWE, and `ComputationallyIndistinguishable` of the scheme's keys
and an ideal key law is a premise about the scheme's own algorithms.

A novel assumption may support a result presented as original, whose name mentions the
assumption. A theorem that claims a cited result rests on the assumption that the source uses, on
one that review accepts as the same assumption in a different formal setting and the inventory
documents as such, or on one that the source's assumption implies, with the implication proved in
the library or cited. Resting it on any other assumption makes it a stand-in under
[Faithful headlines](#faithful-headlines) rule 2.

Write each reduction as an explicit program with an efficiency witness proved from the
adversary's certificate: an `isPPT_…` or `isOraclePPT_…` lemma, or the model's efficiency
certificate (for example a circuit-size bound). Prove the asymptotic theorem by applying the
assumption to the reduction through that witness, as `DDH.elGamalINDCPA` does
([pattern](../manual/programs-crypto-and-probability/security-games-and-primitives.md#security-theorems-and-efficiency-witnesses)).
Asymptotic statements come first; concrete runtime maps are secondary (#4088). A concrete bound
`Adv(A) ≤ f(Adv(B_A))` is a lemma, not a security theorem. A lemma that takes a bound on `B_A`'s
advantage, or `B_A ∈ 𝒟`, as a premise is an algebraic helper: its name (`…_of_reduction_le`) and
docstring say so, and no headline or asymptotic theorem stops at it.

Names and docstrings state the model (standard, random-oracle, ideal, query-bounded or
information-theoretic), the notion (single- or multi-challenge, one-time or many-time,
honest-verifier or malicious zero knowledge, semi-honest, static), and any deviation from the
cited source. When a change replaces a misformalized theorem, it deletes the old one, or demotes it
to an honestly named and documented helper, and updates its ROADMAP, manual and
[results inventory](../results/README.md) mentions ([Faithful headlines](#faithful-headlines); #5293).
`scripts/check_security_premises.py` checks the premise rule after a build against a justified
baseline, `scripts/check_reduction_witnesses.py` checks that each explicit reduction in an
advantage bound has an efficiency witness or a justified baseline entry, and
`scripts/check_hardness_assumptions.py` checks that named assumptions are listed in the inventory
and documented ([details](../CONTRIBUTING.md#library-quality-standard)).
