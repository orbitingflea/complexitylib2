PYTHON ?= python3
LEAN = ../../ComplexityTests/Abstracts

all: section.pdf

lean-snippets/.stamp: $(LEAN)/WordRAMAbstract.lean extract_lean_snippets.py section.tex
	$(PYTHON) extract_lean_snippets.py
	touch $@

section.pdf: section.tex lean-snippets/.stamp
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<

clean:
	latexmk -c section.tex
	rm -f lean-snippets/.stamp

.PHONY: all clean
