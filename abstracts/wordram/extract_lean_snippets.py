#!/usr/bin/env python3
"""Split the definitions of ComplexityTests/Abstracts/WordRAMAbstract.lean into one snippet file
per declaration, in lean-snippets/, so the section typesets exactly the Lean code. Doc and
section comments are removed; `--` comments are kept. Only the declarations before the section
"Main theorems" are cut: the section does not quote the theorems. Follows
figures/extract_lean_snippets.py of github.com/edemaine/translation-tiling-paper.

Then check that section.tex quotes every snippet, and quotes no snippet that was not made."""
import re
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
abstract = root / "ComplexityTests/Abstracts/WordRAMAbstract.lean"
namespace = "ComplexityTests.Abstracts.WordRAMAbstract"
out = here / "lean-snippets"
out.mkdir(exist_ok=True)
for old in out.glob("*.lean"):
    old.unlink()

# Non-ASCII characters that section.tex typesets (its `literate` list); any other is an error.
LITERATE = set("ℕ→∀∃∈∉∧≤↔⟨⟩α")


def blocks(text):
    """The declarations of `namespace` before "Main theorems", without doc or section
    comments. `universe u` is skipped: only the main theorems use it."""
    body = text.split(f"namespace {namespace}\n", 1)[1]
    body = body.split("/-! ## Main theorems", 1)[0]
    body = re.sub(r"/-!.*?-/", "", body, flags=re.S)  # section comments
    body = re.sub(r"[ \t]*/--.*?-/[ \t]*\n?", "", body, flags=re.S)  # doc comments
    for block in re.split(r"\n\s*\n", body):
        block = block.strip("\n")
        if not block.strip() or block.startswith("universe"):
            continue
        if block.startswith("variable"):
            yield "variable", block
            continue
        m = re.match(r"(?:abbrev|def|inductive|structure)\s+(\S+)", block)
        if not m:
            sys.exit(f"cannot name block in {abstract.name}:\n{block}")
        yield m.group(1), block


def write(name, block):
    bad = {c for c in block if ord(c) > 127} - LITERATE
    if bad:
        sys.exit(f"{name}: characters not in LITERATE: {''.join(sorted(bad))}")
    (out / f"{name}.lean").write_text(block + "\n")


text = abstract.read_text()
imports = re.search(r"(?:^import [^\n]+\n)+", text, flags=re.M)
if imports is None:
    sys.exit("cannot find the import block")
write("Imports", imports.group().rstrip("\n"))
names = ["Imports"]
for name, block in blocks(text):
    write(name, block)
    names.append(name)

quoted = set()
for arg in re.findall(r"\\leansnippet\{([^}]*)\}", (here / "section.tex").read_text()):
    quoted |= {n.strip() for n in arg.split(",")}
if missing := [n for n in names if n not in quoted]:
    sys.exit(f"section.tex does not quote: {' '.join(missing)}")
if unknown := sorted(quoted - set(names)):
    sys.exit(f"section.tex quotes snippets that were not made: {' '.join(unknown)}")
print(" ".join(names))
