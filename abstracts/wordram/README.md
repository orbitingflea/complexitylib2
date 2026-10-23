# The word RAM in Lean: a hand-written section

A standalone section that presents the definitions of
`ComplexityTests/Abstracts/WordRAMAbstract.lean`, in the style of Section 4 of Demaine and
Langerman's tiling paper. This directory is local to the fork. `scripts/build_abstracts.py` can
render the abstract from its doc comments, given a catalogue entry for it, but
`abstracts/catalogue.json` has no such entry, so the catalogue workflow does not select it.

- `section.tex`: the section; `section.pdf` is its build.
- `extract_lean_snippets.py`: cuts the definitions of `WordRAMAbstract.lean`, up to its section
  "Main theorems", into `lean-snippets/`, one file per declaration, so the boxes show the real
  code. It fails if `section.tex` leaves out one of them or quotes a snippet that was not made, or
  if a snippet has a Unicode character that the `literate` list of `section.tex` does not cover.
- `lean-snippets/`: generated, checked in so that `latexmk -pdf section.tex` alone builds.

Build with `make` (Python 3 and `latexmk` with `pdflatex`).

## Source of the style

<https://github.com/edemaine/translation-tiling-paper>, commit
`5309313e662377d2efb353acba454859469606bd` (2026-10-14). Citations are `file:line` at that
commit.

1. **One section, "Formal Verification in Lean"** (`paper.texlish:392`). It opens with the trust
   story: a reader need only check "the handful of definitions and theorem statements in a single
   file, `Abstract.lean`", and Lean checks the proofs and that they use only `propext`,
   `Classical.choice`, `Quot.sound` (`paper.texlish:393-404`).
2. **Scope and authority.** The source file "remains the authoritative version", and the import
   block is quoted (`paper.texlish:405-413`).
3. **One subsection per concept, in file order**, each a short prose paragraph followed by one box
   quoting the matching declarations (`paper.texlish:418-478`).
4. **Theorems** are shown as statements, proof elided as `:= ...` (`paper.texlish:446-458`).
5. **Snippets cannot drift.** `figures/extract_lean_snippets.py` cuts `Abstract.lean` into one file
   per declaration, dropping doc and section comments (`figures/extract_lean_snippets.py:15-37`),
   and `Makefile:19-24` reruns it when `Abstract.lean` changes. The boxes are `listings` inside a
   `tcolorbox` (`paper.texlish:50-68`).

## What this section keeps and changes

Kept: the import box with the scope and authority facts, one subsection per concept in file order
with prose then box, the box style, and the snippet script and Makefile rule (the script is a port
of his).

Changed, and why:

- **The opening, by the user's choice.** There is no trust story and no informal theorem up front:
  one or two sentences say what the document is for, then the "Imports" subsection starts.
- **No theorem is quoted.** The abstract imports `WordRAMBridge.lean` and states the two theorems
  at its end, as Erik's does. The section quotes only the definitions, and its last subsection,
  "Main Theorems", says in one sentence that `WordRAMBridge.lean` proves them equal to the
  library's word RAM. `universe u` is not quoted either: only the theorems use it.
- **`variable {r : ℕ}` is shown beside `Instr`,** in the "Instructions and Programs" box, not
  first: in the file it comes before `AluOp`, but it is about registers, which that subsection
  introduces. All other boxes keep file order.
- **Longer prose.** Erik gives each concept one or two sentences. The `step` subsection here has a
  bullet per instruction kind and a paragraph on why copies, loads and stores need no check (the
  word invariant), and the decision subsection explains the quantifiers over word sizes. The
  machine has more cases than his tiling definitions, and these points are easy to misread from
  the code. The same prose is in the section docs of `WordRAMAbstract.lean`.
- **No Lean logo.** His repository has no license file, and the logo is the Lean FRO's mark; a
  text label "Lean" replaces it.
- **No Texlish.** His source is Texlish (`Makefile:16-17`); this section is plain LaTeX with the
  same packages and the same `listings`/`tcolorbox` setup, built by `latexmk`.
- **Fixed-width code columns.** His style uses `columns=fullflexible`; `Instr` has aligned `--`
  comments, so this section uses fixed columns and draws each Unicode symbol in one column (arrows
  in two).
- **`--` comments are kept** in the snippets (his file has none); doc comments are dropped as in
  his script.
- **The script also checks coverage,** as listed above.
- **No GitHub links** to the Lean files. The path and the commit are given instead.
