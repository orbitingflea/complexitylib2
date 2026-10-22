#!/usr/bin/env python3
"""Split Complexity/Computability/WordRAM/Abstract.lean into one snippet file per declaration,
and cut the quoted statements out of AbstractBridge.lean by name, into lean-snippets/, so the
section typesets exactly the Lean code. Doc and section comments are removed and theorem proofs
are elided; `--` comments are kept. Follows figures/extract_lean_snippets.py of
github.com/edemaine/translation-tiling-paper.

Then check that section.tex quotes every snippet of Abstract.lean, and quotes no snippet that
was not made."""
import re
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
wordram = root / "Complexity/Computability/WordRAM"
out = here / "lean-snippets"
out.mkdir(exist_ok=True)
for old in out.glob("*.lean"):
    old.unlink()

# Statements quoted from the bridge, in the order they appear in the section.
BRIDGE = ["OutcomeAgrees", "Same", "runsAgree", "decidableInTime_iff"]
# Non-ASCII characters that section.tex typesets (its `literate` list); any other is an error.
LITERATE = set("ℕ→∀∃∈∉∧≤↔⟨⟩α")


def blocks(path, namespace):
    """The declarations of `namespace` in `path`, without doc or section comments."""
    body = path.read_text().split(f"namespace {namespace}\n", 1)[1]
    body = body.rsplit(f"end {namespace}\n", 1)[0]
    body = re.sub(r"/-!.*?-/", "", body, flags=re.S)  # section comments
    body = re.sub(r"[ \t]*/--.*?-/[ \t]*\n?", "", body, flags=re.S)  # doc comments
    for block in re.split(r"\n\s*\n", body):
        block = block.strip("\n")
        if not block.strip():
            continue
        if block.startswith(("variable", "universe")):
            yield block.split()[0], block
            continue
        block = re.sub(r"^@\[[^\]]*\]\n", "", block)  # attributes
        m = re.match(r"(?:abbrev|def|theorem|lemma|inductive|structure)\s+(\S+)", block)
        if not m:
            sys.exit(f"cannot name block in {path.name}:\n{block}")
        if block.startswith(("theorem", "lemma")):  # show the statement only, not the proof
            block = re.split(r" :=(?:\n| )", block, maxsplit=1)[0].rstrip() + " := ..."
        yield m.group(1), block


def write(name, block):
    bad = {c for c in block if ord(c) > 127} - LITERATE
    if bad:
        sys.exit(f"{name}: characters not in LITERATE: {''.join(sorted(bad))}")
    (out / f"{name}.lean").write_text(block + "\n")


abstract = wordram / "Abstract.lean"
imports = re.search(r"(?:^(?:public )?import [^\n]+\n)+", abstract.read_text(), flags=re.M)
if imports is None:
    sys.exit("cannot find the import block")
write("Imports", imports.group().rstrip("\n"))
names = ["Imports"]
for name, block in blocks(abstract, "Cslib.WordRAM.Abstract"):
    write(name, block)
    names.append(name)

bridge = dict(blocks(wordram / "AbstractBridge.lean", "Cslib.WordRAM.AbstractBridge"))
for name in BRIDGE:
    if name not in bridge:
        sys.exit(f"AbstractBridge.lean has no declaration {name}")
    write(name, bridge[name])

quoted = set()
for arg in re.findall(r"\\leansnippet\{([^}]*)\}", (here / "section.tex").read_text()):
    quoted |= {n.strip() for n in arg.split(",")}
if missing := [n for n in names if n not in quoted]:
    sys.exit(f"section.tex does not quote: {' '.join(missing)}")
if unknown := sorted(quoted - set(names) - set(BRIDGE)):
    sys.exit(f"section.tex quotes snippets that were not made: {' '.join(unknown)}")
print(" ".join(names + BRIDGE))
