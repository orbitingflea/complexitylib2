# How Demaine and Langerman present their Lean abstract

Source: <https://github.com/edemaine/translation-tiling-paper>, commit
`5309313e662377d2efb353acba454859469606bd` (2026-10-14). Citations are `file:line` at that
commit.

## The pattern

1. **One section, "Formal Verification in Lean"** (`paper.texlish:392`), after the proof
   overview. It opens with the trust story: the proof is long, so it is formalized; a reader
   need only check "the handful of definitions and theorem statements in a single file,
   `Abstract.lean`", and Lean checks the proofs and that they use only `propext`,
   `Classical.choice`, `Quot.sound` (`paper.texlish:393-404`).
2. **Scope and authority.** "In the rest of this section, we explain the statements from
   `Abstract.lean`", the source file "remains the authoritative version", it imports only
   Mathlib and `lean-wang`'s co-RE definitions, and `AbstractBridge.lean` connects the
   statements to the rest of the formalization "but need not be checked by a human"
   (`paper.texlish:405-412`). Then the import block is quoted (`paper.texlish:413`).
3. **One subsection per concept, in file order**, each a short prose paragraph that defines
   the notion in mathematical language (bold-italic term, one or two sentences of why, e.g.
   "a list (not a set) so that it can be given as input to an algorithm"), followed by one
   box quoting the matching declarations: Prototiles, Connectivity, Tiling Z³, Main Theorem
   for Z³, Tiling R³, Main Theorem for R³ (`paper.texlish:418-478`). Every declaration of
   `Abstract.lean` is quoted; each theorem subsection has a `\phantomsection\label` so the
   footnotes of the informal theorem can point to it (`paper.texlish:434,457,477`).
4. **Theorems.** The informal theorem is in the introduction, with one footnote per claim
   naming the Lean theorem with a Lean logo and pointing to its subsection
   (`paper.texlish:255-274`). In the Lean section, the theorem prose says what the statement
   means, that its proof is one call into the bridge, and the boxes show only the statement,
   proof elided as `:= ...` (`paper.texlish:446-458`). The section closes: "Together, these
   four Lean theorems establish" the main theorem (`paper.texlish:480`).
5. **Snippets cannot drift.** `figures/extract_lean_snippets.py` cuts `Abstract.lean` into one
   file per declaration, dropping doc and section comments, eliding theorem proofs
   (`figures/extract_lean_snippets.py:15-37`); `Makefile:19-24` reruns it when
   `Abstract.lean` changes. The paper typesets them with `listings` inside a `tcolorbox` with
   the Lean logo in a corner; `\leansnippet{A,B}` puts several declarations in one box
   (`paper.texlish:50-68`). The generated snippets are checked in.

## What this draft keeps and changes

Kept: the import box with the scope and authority facts, one subsection per concept in file
order with prose then box, theorem statements with `:= ...`, the box style, and the snippet
script and Makefile rule (the script is a port of his).

Changed, and why:

- **The opening, by the user's choice.** There is no trust story and no informal theorem up
  front: one or two sentences say what the document is for, then the "Imports" subsection
  starts. No theorem comes before the definitions; the two theorems are stated once, in the
  last subsection. The trust note (read only the definitions and the two statements; Lean
  checks the proofs, with the three standard axioms) is at the end, where Erik's section
  instead closes with "Together, these four Lean theorems establish" the informal theorem.
- **Theorems live in the bridge.** In Erik's repo `Abstract.lean` imports the bridge and
  states the theorems (`lean/TranslationTiling/Abstract.lean:4`); ours does not import the
  library at all, so the two theorems are cut by name from `AbstractBridge.lean`, together with the two definitions
  (`OutcomeAgrees`, `Same`) that their statements use. Their statements mention the
  library's own definitions, so the "Main Theorems" subsection first says what the unprefixed
  names are and why the reader need not read them.
- **`variable {r : ℕ}` is shown beside `Instr`,** in the "Instructions and Programs" box,
  not first: in the file it comes before `AluOp`, but it is about registers, which that
  subsection introduces. All other boxes keep file order.
- **Longer prose.** Erik gives each concept one or two sentences. The `step` subsection here
  has a bullet per instruction kind and a paragraph on why copies, loads and stores need no
  check (the word invariant), and the decision subsection explains the quantifiers over word
  sizes. The machine has more cases than his tiling definitions, and these points are easy
  to misread from the code.
- **An extra sentence before the trust note** says that a library theorem concluding
  `DecidableInTime .exact A encode T bits` is a time bound on the machine of the section. This is the use of the bridge, which Erik's section does not need.
- **No Lean logo.** His repository has no license file, and the logo is the Lean FRO's mark;
  a text label "Lean" replaces it.
- **No Texlish.** His source is Texlish (`Makefile:16-17`); this draft is plain LaTeX with the
  same packages and the same `listings`/`tcolorbox` setup, built by `latexmk`.
- **Fixed-width code columns.** His style uses `columns=fullflexible`; `Instr` has aligned
  `--` comments, so this draft uses fixed columns and draws each Unicode symbol in one column
  (arrows in two).
- **`--` comments are kept** in the snippets (his file has none); doc comments are dropped as
  in his script.
- **The script also checks coverage:** it fails if `section.tex` leaves out a declaration of
  `Abstract.lean`, quotes a snippet that was not made, or a snippet has a Unicode character the
  `literate` list does not cover.
- **No GitHub links** to the Lean files: the branch is not published. Paths and the commit
  are given instead.
