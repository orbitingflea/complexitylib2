# The word RAM in Lean: a draft paper section

A draft section that presents `Complexity/Computability/WordRAM/Abstract.lean` and the two
theorems of `AbstractBridge.lean`, in the style of Section 4 of Demaine and Langerman's tiling
paper. `NOTES.md` describes that style and where this draft departs from it.

- `section.tex`: the section, as a standalone document; `section.pdf` is its build.
- `extract_lean_snippets.py`: cuts the Lean files into `lean-snippets/`, one file per
  declaration, so the boxes show the real code. It fails if `section.tex` leaves out a
  declaration of `Abstract.lean`.
- `lean-snippets/`: generated, checked in so that `latexmk -pdf section.tex` alone builds.

Build with `make` (Python 3 and `latexmk` with `pdflatex`).
