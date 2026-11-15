#!/usr/bin/env python3
"""Keep the named assumptions of security theorems cited, or documented as novel (#5578).

Usage: python3 scripts/check_hardness_assumptions.py [--report | --list] [--update-baseline]
           [--no-build-check] [--baseline FILE]

This checks the rule on named assumptions in AGENTS.md, "Security theorems". A security theorem
may assume named hardness assumptions: Prop-valued definitions documented as assumptions, such as
`F.DDH setup`, `DecisionLWE …` or `OneWay f`, including security notions of a component that the
caller supplies. Each is registered in the assumptions inventory,
`manual/programs-crypto-and-probability/assumptions.md`, as *standard* (its docstring cites the
source definition, with a locator checked at the source), *novel* (its docstring says that it is
novel to this library and how it relates to standard assumptions) or *vocabulary* (a generic notion
parameterized by the objects whose security it states, such as `Game.Indistinguishable` or
`ComputationallyIndistinguishable`, which becomes an assumption only through the instance a theorem
supplies; never a primitive's own security notion). A theorem that rests on a novel assumption
names it, and is not presented as a cited result.

`scripts/SecurityPremises.lean --assumptions` reads the built `.olean` files of the library, with
CSLib's as context. A *named assumption* is a Prop-valued definition or `structure` whose
definition mentions negligibility, an advantage or indistinguishability, directly or through
other Prop-valued declarations. No declaration is excluded by its name: generic notions are named
assumptions too, and their inventory rows mark them as vocabulary. The reader reports each one,
and each public theorem under `CslibFrontier/Crypto` or in `Cslib.Crypto` whose premises, through
their own `∀`s and premises, `∧`, `∃` and `∀ᶠ`, are headed by one.

The check fails when
* an inventory row is malformed, names no named assumption, or repeats one; a standard row cites no
  key of `references.bib`; a novel or vocabulary row does not say how it relates to standard
  assumptions; or a nonvacuity file or test it names does not exist;
* a named assumption that some scanned theorem assumes is not in the inventory;
* a standard assumption's docstring cites none of its row's keys, or a novel assumption's docstring
  does not say "novel to this library";
* a row of any status says "locator not verified";
* a theorem that rests on a novel assumption does not mention it in its name, or its docstring
  presents a cited result (it cites a `references.bib` key, or its first sentence says "theorem" or
  opens with a bold title) without opening as a step or helper: its first sentence must contain
  the word "step" or "helper";
* a results-inventory entry (`CslibFrontierResults/Entries.lean`) lists a theorem that rests on a
  novel assumption.

`scripts/hardness_assumptions_baseline.json` records the existing gaps of the third, fourth and
fifth kinds, one per line with a justification, under `docstrings`, `locators` and `headlines`.
An entry that no longer matches a gap fails too, so the baseline only shrinks unless a change adds
an entry on purpose. The check covers the whole library, so pull requests and merge groups both
enforce it: a merge group whose pull requests conflict only in meaning (two of them registering
the same assumption, say) fails, and the queue ejects the pull request that broke it instead of
landing it on `main`. Pushes to `main` run `--report`, which prints the differences and succeeds.
`--list` prints the inventory with the theorems that rest on each assumption. `--update-baseline`
rewrites the baseline for the current gaps, keeping existing justifications and leaving new ones
empty; fill them in, or the check fails.

This is a post-build check: it needs the outputs of `lake build CslibFrontier`, and refuses stale
ones unless `--no-build-check` is given. It supplements review: it does not judge whether a
definition matches its cited source, whether a locator is right, or whether a standard assumption
under a headline, with the instance the theorem supplies, is the one the cited result assumes. It
does not see a cited result that a docstring names without a bibliography key, the word "theorem"
or a bold title in its first sentence, nor one that only a theorem's name claims. Conversely, an
original result on a novel assumption, which the rule allows, is flagged when its docstring
presents a cited result in that sense, and then passes only through a justified baseline entry.

The inventory is not complete. The reader misses a premise written inline, such as a
hypothesis `∀ A, Negligible (advantage A)`, which no named declaration heads. It also misses an
assumption whose definition reaches no security atom through Prop-valued declarations within five
levels: a bound on a quantity not named like an advantage (a success probability, an agreement
fraction), an advantage behind a helper that is not Prop-valued, or an atom reached only through a
longer chain of Prop-valued declarations. A row for such an assumption fails as naming no named
assumption. The known cases (#5578 finding 9) are `Cslib.Complexity.MildlyHardOnAverage` and
`MildlyHardOnAverageENat` (the Liu–Pass converse, `OneWay/LiuPassConverse.lean`),
`Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap` and `HasGapWithAdvice` (`Pseudoentropy/`), and
`Cslib.Circuits.Boolean.IsAverageCaseHard` (the Nisan–Wigderson generator).
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_security_premises as csp  # noqa: E402
import lean_outputs as lo  # noqa: E402

INVENTORY = ROOT / "manual/programs-crypto-and-probability/assumptions.md"
BASELINE = ROOT / "scripts/hardness_assumptions_baseline.json"
BIBLIOGRAPHY = ROOT / "references.bib"
RESULTS = ROOT / "CslibFrontierResults/Entries.lean"
UPSTREAM_BUILD = ROOT / ".lake/packages/cslib/.lake/build/lib/lean"
HEADER = ["Assumption", "Status", "Source definition", "Deviations or relation", "Nonvacuity"]
STATUSES = ("standard", "novel", "vocabulary")
SECTIONS = ("docstrings", "locators", "headlines")
NOVEL = "novel to this library"
UNVERIFIED = "locator not verified"
UPDATE = "python3 scripts/check_hardness_assumptions.py --update-baseline"
CODE = re.compile(r"`([^`]+)`")
BRACKET = re.compile(r"\[([^\[\]]*)\]")
STEP = re.compile(r"\b(?:step|helper)\b", re.I)
THEOREM = re.compile(r"\btheorem\b", re.I)
SENTENCE_END = re.compile(r"[.!?][*_)\"']*(?:\s|$)")
LINK = re.compile(r"\]\(([^)\s]+)\)")
BIB_KEY = re.compile(r"^@\w+\{\s*([^,\s]+)\s*,", re.M)
RESULT_NAME = re.compile(r"\b(?:Cslib|Turing)\.[A-Za-z0-9_.'!?]+")


@dataclass(frozen=True)
class Row:
    """An inventory row: the assumption's full name, its status, the cell texts and the line."""
    name: str
    status: str
    source: str
    relation: str
    nonvacuity: str
    line: int


@dataclass
class Reading:
    """The reader's output: named assumptions as `name -> (module, line, docstring)` and the
    scanned theorems that rest on them as `name -> (module, line, docstring, assumptions)`."""
    assumptions: dict[str, tuple[str, int, str]] = field(default_factory=dict)
    theorems: dict[str, tuple[str, int, str, tuple[str, ...]]] = field(default_factory=dict)
    summary: dict = field(default_factory=dict)


def cells(line: str) -> list[str]:
    """The cells of a Markdown table row, splitting at `|` outside code spans."""
    out, current, code = [], "", False
    for ch in line.strip().strip("|"):
        if ch == "`":
            code = not code
        if ch == "|" and not code:
            out.append(current.strip())
            current = ""
        else:
            current += ch
    return out + [current.strip()]


def parse_inventory(text: str) -> tuple[list[Row], list[str]]:
    """The rows of every table with the inventory header, and the format errors."""
    rows, errors, in_table = [], [], False
    for number, line in enumerate(text.splitlines(), 1):
        if not line.lstrip().startswith("|"):
            in_table = False
            continue
        row = cells(line)
        if row == HEADER:
            in_table = True
            continue
        if not in_table or set(line.replace("|", "").strip()) <= set("-: "):
            continue
        if len(row) != len(HEADER):
            errors.append(f"line {number}: expected {len(HEADER)} cells, found {len(row)}")
            continue
        names = CODE.findall(row[0])
        status = row[1].strip().lower()
        if len(names) != 1:
            errors.append(f"line {number}: the first cell names one declaration in backticks")
            continue
        if status not in STATUSES:
            errors.append(f"line {number}: status {row[1]!r} is not one of {', '.join(STATUSES)}")
            continue
        name = names[0] if names[0].startswith("Cslib.") else "Cslib.Crypto." + names[0]
        rows.append(Row(name, status, row[2], row[3], row[4], number))
    return rows, errors


def bibliography_keys(text: str) -> set[str]:
    return set(BIB_KEY.findall(text))


def cited_keys(text: str, keys: set[str]) -> list[str]:
    """The bibliography keys that `text` cites, in the forms that `scripts/check_hygiene.py`
    accepts: `[Key]`, `[Key, Theorem 2]`, `[Key; Other]` and the reference of `[text][Key]`."""
    found: list[str] = []
    for segment in BRACKET.findall(text):
        for part in segment.split(";"):
            key = part.split(",")[0].strip()
            if key in keys and key not in found:
                found.append(key)
    return found


def first_sentence(doc: str) -> str:
    """A docstring's opening sentence: its text up to the first `.`, `!` or `?` outside code spans
    that is followed, after closing emphasis, brackets or quotes, by whitespace or the end. An
    abbreviation such as "Thm." can end it early, which only makes the step test stricter."""
    text = " ".join(doc.split())
    outside = re.sub(r"`[^`]*`", lambda m: "x" * len(m.group(0)), text)
    m = SENTENCE_END.search(outside)
    return text[:m.end()].strip() if m else text


def presents_cited_result(doc: str, keys: set[str]) -> bool:
    """Whether a theorem's docstring presents a cited result: it cites a bibliography key, or its
    first sentence calls it a theorem or opens with a bold title, as named results do ("**The GMW
    theorem**", "**Soundness-amplified GMW for NP relations.**"). An original result with a bold
    title is caught too; its docstring says "step" or "helper", or the baseline records why not."""
    opening = first_sentence(doc)
    return bool(cited_keys(doc, keys) or THEOREM.search(opening) or opening.startswith("**"))


def opens_as_step(doc: str) -> bool:
    """Whether a docstring opens by saying that its theorem is a step or a helper: its first
    sentence contains the word "step" or "helper" (not, say, "steps")."""
    return bool(STEP.search(first_sentence(doc)))


def read(output: str) -> Reading:
    reading = Reading()
    for line in output.splitlines():
        row = json.loads(line)
        if "a" in row:
            reading.assumptions[row["a"]] = (row["m"], row["l"], row["doc"])
        elif "t" in row:
            reading.theorems[row["t"]] = (row["m"], row["l"], row["doc"], tuple(row["u"]))
        else:
            reading.summary = row
    return reading


def context_modules(build: Path) -> list[str]:
    """CSLib's modules, as `<dir>\\t<module>` lines: definitions are followed into them."""
    return [f"{build}\t{'.'.join(p.relative_to(build).with_suffix('').parts)}"
            for p in sorted(build.glob("Cslib/**/*.olean"))]


def scan(root: Path, build_dir: Path, upstream: Path) -> Reading:
    """Run the Lean reader over the library, with CSLib as context."""
    lines = context_modules(upstream) + csp.library_modules(root)
    out = subprocess.run(["lake", "env", "lean", "--run", csp.TOOL, str(build_dir),
                          "--assumptions"], cwd=root, input="\n".join(lines) + "\n",
                         capture_output=True, text=True)
    if out.returncode:
        sys.exit(f"{csp.TOOL} failed:\n{out.stderr or out.stdout}")
    reading = read(out.stdout)
    if reading.summary.get("missing"):
        sys.exit(f"build outputs are missing for {len(reading.summary['missing'])} module(s), "
                 f"e.g. {reading.summary['missing'][0]}; run `lake build CslibFrontier` first")
    return reading


def short(name: str) -> str:
    return name.removeprefix("Cslib.Crypto.")


def nonvacuity_errors(row: Row, base: Path) -> list[str]:
    """A nonvacuity cell links test files (`[…](path)`, relative to the inventory's directory
    `base`) and may name tests in backticks; each file must exist and contain each named test."""
    texts, errors = [], []
    for p in LINK.findall(row.nonvacuity):
        path = (base / p).resolve()
        if not path.is_file():
            errors.append(f"{short(row.name)}: nonvacuity file {p} does not exist")
        else:
            texts.append(path.read_text(encoding="utf-8"))
    for test in CODE.findall(row.nonvacuity):
        if not any(re.search(rf"\b{re.escape(test.split('.')[-1])}\b", t) for t in texts):
            errors.append(f"{short(row.name)}: nonvacuity test `{test}` is not in the linked files")
    return errors


@dataclass
class Problems:
    errors: list[str]
    gaps: dict[str, dict[str, str]]  # section -> name -> description

    def baseline_differences(self, baseline: dict[str, dict[str, str]]) -> tuple[list, list, list]:
        """Unrecorded gaps, stale entries and entries without a justification."""
        new = [(s, n, d) for s in SECTIONS for n, d in sorted(self.gaps[s].items())
               if n not in baseline.get(s, {})]
        stale = [(s, n) for s in SECTIONS for n in sorted(baseline.get(s, {}))
                 if n not in self.gaps[s]]
        unjustified = [(s, n) for s in SECTIONS for n, why in sorted(baseline.get(s, {}).items())
                       if not why.strip()]
        return new, stale, unjustified


def check(rows: list[Row], format_errors: list[str], reading: Reading, keys: set[str],
          results: str, base: Path) -> Problems:
    errors = list(format_errors)
    gaps: dict[str, dict[str, str]] = {s: {} for s in SECTIONS}
    registered: dict[str, Row] = {}
    for row in rows:
        if row.name in registered:
            errors.append(f"line {row.line}: `{short(row.name)}` is registered twice")
            continue
        registered[row.name] = row
        if row.name not in reading.assumptions:
            errors.append(f"line {row.line}: `{short(row.name)}` is not a named assumption of the "
                          "library or CSLib (a Prop-valued declaration stating a security claim)")
        if row.status == "standard" and not cited_keys(row.source, keys):
            errors.append(f"line {row.line}: standard `{short(row.name)}` cites no key of "
                          "references.bib in its source cell")
        if row.status != "standard" and not row.relation.strip(" —-"):
            errors.append(f"line {row.line}: {row.status} `{short(row.name)}` needs its relation "
                          "to standard assumptions")
        errors += nonvacuity_errors(row, base)
    used: dict[str, list[str]] = {}
    for theorem, (_, _, _, heads) in reading.theorems.items():
        for h in heads:
            used.setdefault(h, []).append(theorem)
    for name, theorems in sorted(used.items()):
        if name not in registered:
            module, line, _ = reading.assumptions.get(name, ("?", 0, ""))
            errors.append(f"`{short(name)}` ({module}:{line}) is assumed by {len(theorems)} "
                          f"theorem(s), e.g. `{short(sorted(theorems)[0])}`, but is not in the "
                          "assumptions inventory")
    results_names = set(RESULT_NAME.findall(results))
    for name, row in registered.items():
        if name not in reading.assumptions:
            continue
        doc = reading.assumptions[name][2]
        if UNVERIFIED in row.source.lower():
            gaps["locators"][name] = "locator not verified"
        if row.status == "standard":
            row_keys = cited_keys(row.source, keys)
            if row_keys and not set(row_keys) & set(cited_keys(doc, keys)):
                gaps["docstrings"][name] = f"docstring cites none of {', '.join(row_keys)}"
        elif row.status == "novel":
            if NOVEL not in " ".join(doc.split()).lower():
                gaps["docstrings"][name] = f'docstring does not say "{NOVEL}"'
            stem = name.split(".")[-1].lower()
            for theorem in sorted(used.get(name, [])):
                tdoc = reading.theorems[theorem][2]
                problems = []
                if stem not in theorem.lower():
                    problems.append(f"name does not mention `{name.split('.')[-1]}`")
                if presents_cited_result(tdoc, keys) and not opens_as_step(tdoc):
                    problems.append("docstring presents a cited result but does not open as a "
                                    "step or helper")
                if problems:
                    gaps["headlines"][theorem] = (f"rests on novel `{short(name)}`: "
                                                  + "; ".join(problems))
                if theorem in results_names:
                    errors.append(f"results inventory lists `{short(theorem)}`, which rests on "
                                  f"the novel assumption `{short(name)}`")
    return Problems(errors, gaps)


def load_baseline(path: Path) -> dict[str, dict[str, str]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    ok = (isinstance(data, dict) and set(data) <= set(SECTIONS) and all(
        isinstance(v, dict) and all(isinstance(k, str) and isinstance(w, str)
                                    for k, w in v.items()) for v in data.values()))
    if not ok:
        sys.exit(f"{path}: expected {{section: {{name: justification}}}} with sections "
                 f"{', '.join(SECTIONS)}")
    return {s: data.get(s, {}) for s in SECTIONS}


def baseline_text(baseline: dict[str, dict[str, str]]) -> str:
    """One entry per line, so that concurrent edits rarely touch the same lines."""
    parts = []
    for s in SECTIONS:
        entries = baseline.get(s, {})
        lines = [f"  {json.dumps(n, ensure_ascii=False)}: "
                 + json.dumps(entries[n], ensure_ascii=False) for n in sorted(entries)]
        body = ("{\n" + ",\n".join(lines) + "\n }") if lines else "{}"
        parts.append(f" {json.dumps(s)}: {body}")
    return "{\n" + ",\n".join(parts) + "\n}\n"


def report(problems: Problems, baseline: dict[str, dict[str, str]]) -> str:
    out = []
    if problems.errors:
        out += ["Assumptions inventory errors (AGENTS.md, Security theorems):"]
        out += [f"  {e}" for e in problems.errors]
    new, stale, unjustified = problems.baseline_differences(baseline)
    if new:
        out += ([""] if out else []) + [
            "Named assumptions cite their source definition with a checked locator, or say that "
            f'they are "{NOVEL}"; a theorem resting on a novel assumption names it and is not '
            "presented as a cited result (AGENTS.md, Security theorems). Fix these, or record a "
            f"deliberate exception with a justification (`{UPDATE}`, then fill in the entry):"]
        out += [f"  {s}: `{short(n)}`: {d}" for s, n, d in new]
    if stale:
        out += ([""] if out else []) + [
            f"Baseline entries that no longer match a gap; remove them (`{UPDATE}`):"]
        out += [f"  {s}: `{short(n)}`" for s, n in stale]
    if unjustified:
        out += ([""] if out else []) + ["Baseline entries without a justification:"]
        out += [f"  {s}: `{short(n)}`" for s, n in unjustified]
    return "\n".join(out)


def listing(rows: list[Row], reading: Reading) -> str:
    used: dict[str, list[str]] = {}
    for theorem, (_, _, _, heads) in reading.theorems.items():
        for h in heads:
            used.setdefault(h, []).append(theorem)
    out = []
    for row in rows:
        users = sorted(used.get(row.name, []))
        out.append(f"{short(row.name)} [{row.status}]: {len(users)} theorem(s)")
        out += [f"  {short(u)}" for u in users]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--report", action="store_true",
                      help="print every difference and succeed")
    mode.add_argument("--list", action="store_true",
                      help="print the inventory with the theorems that rest on each assumption")
    parser.add_argument("--update-baseline", action="store_true",
                        help="record the current gaps, keeping existing justifications")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)
    if (args.report or args.list) and args.update_baseline:
        parser.error("--report and --list do not combine with --update-baseline")
    if not args.no_build_check and not lo.lake_outputs_current(("CslibFrontier",)):
        sys.exit("build outputs are missing or stale; run `lake build CslibFrontier` "
                 "(or pass --no-build-check)")
    reading = scan(ROOT, lo.DEFAULT_BUILD_DIR, UPSTREAM_BUILD)
    rows, format_errors = parse_inventory(INVENTORY.read_text(encoding="utf-8"))
    if args.list:
        print(listing(rows, reading))
        return 0
    keys = bibliography_keys(BIBLIOGRAPHY.read_text(encoding="utf-8"))
    results = RESULTS.read_text(encoding="utf-8") if RESULTS.exists() else ""
    problems = check(rows, format_errors, reading, keys, results, INVENTORY.parent)
    baseline = load_baseline(args.baseline) if args.baseline.exists() else \
        {s: {} for s in SECTIONS}
    if args.update_baseline:
        updated = {s: {n: baseline[s].get(n, "") for n in problems.gaps[s]} for s in SECTIONS}
        args.baseline.write_text(baseline_text(updated), encoding="utf-8")
        empty = [f"{s}: {n}" for s in SECTIONS for n, w in updated[s].items() if not w.strip()]
        print(f"Wrote {args.baseline}." + (f" Fill in: {', '.join(empty)}." if empty else ""))
        return 0 if not problems.errors else 1
    text = report(problems, baseline)
    status = (f"{len(rows)} registered assumption(s), {len(reading.theorems)} theorem(s) resting "
              f"on named assumptions, {sum(len(v) for v in baseline.values())} baseline entries")
    if args.report:
        print((text + "\n\n" if text else "") + f"{status}; report only, nothing is enforced.")
        return 0
    if text:
        print(text, file=sys.stderr)
        return 1
    print(f"{status}; every named assumption is registered and documented.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
