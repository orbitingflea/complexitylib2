#!/usr/bin/env python3
"""Keep explicit security reductions from lacking an efficiency witness (#5293).

Usage: python3 scripts/check_reduction_witnesses.py [--base REF | --all | --report]
           [--list [PREFIX]] [--update-baseline] [--no-build-check] [--baseline FILE]

This checks the rule "Security theorems" in AGENTS.md: each reduction is an explicit program with
an efficiency witness proved from the adversary's certificate, an `isPPT_…` or `isOraclePPT_…`
lemma or the model's certificate. `scripts/check_security_premises.py` catches a theorem that
assumes the reduction's efficiency; this check catches a reduction that has no certificate at
all, so that no asymptotic theorem can apply a hardness assumption to it.

`scripts/SecurityPremises.lean --reductions` reads the built `.olean` files of the library, with
CSLib's as context, so it sees elaborated statements. A *reduction* is a definition under
`CslibFrontier/Crypto` or in the namespace `Cslib.Crypto` that finally yields a program (a
`ProbComp`, `OracleComp` or `PMF`, or a structure of these such as an adversary) and that a
public theorem uses on the bounding side of an advantage bound, applied to a program variable
that the bounded side mentions: `B` in `Adv(scheme, A) ≤ Adv(problem, B A)`, or in
`Adv(scheme, A) = Adv(problem, B A)`. An *efficiency witness* is a theorem, private ones
included, that concludes an efficiency certificate mentioning the reduction: a predicate named
`IsPPT…`, `IsOraclePPT…`, `IsTidyOraclePPT…`, `ComputableIn…`, `ComputableTidilyIn…`,
`IsPolyTime…`, `IsEfficient…` or `Efficient…`. A query bound is not one. A reduction is also
certified when it is an `abbrev` of certified reductions, or when a certified definition applies
it (the word-level program that runs it). The Lean file's docstring gives the exact rules and the
known gaps.

`scripts/reduction_witnesses_baseline.json` records the uncertified reductions that are allowed,
one per line, as `{reduction: {"module": source path, "kind": "gap" | "exempt", "why":
justification}}`. A `gap` is a reduction that still needs its witness; its `why` names the issue
that tracks it. An `exempt` entry needs none, and its `why` says which case it is: the bound is
information-theoretic (it holds for unbounded adversaries and no computational theorem applies an
assumption to the reduction), or the definition is not a reduction, such as a scheme or protocol
built from a component, which the checker cannot tell apart. Every entry needs a one-line
justification.

In a module that the change touches (adds, modifies or deletes, against the merge base of
`--base`, default `origin/main`, and the working tree, as `scripts/check_changed_files.py`
computes it), an uncertified reduction without an entry fails, and so does an entry that no
longer matches an uncertified reduction, until the baseline drops it in the same change: the
baseline only shrinks unless a change adds an entry on purpose. A reduction belongs to the module
that defines it and to the modules of the theorems that state bounds with it. A change that adds
or modifies the checker or the baseline enforces every module. Differences in other modules are
printed as a notice but do not fail: a change can cause them without touching those modules, for
example by deleting a witness. Pull requests run this mode. `--all` enforces every module.
`--report` prints every difference and always succeeds; merge groups and pushes to `main` run it,
so that a queued pull request is never ejected by a change elsewhere. `--list [PREFIX]` ignores
the baseline and prints every reduction defined in the modules under the path PREFIX with its
certificate. `--update-baseline` adds `gap` entries with an empty justification for the
unrecorded uncertified reductions of the enforced modules and removes their stale entries; fill
in each `why`, or the check fails.

This is a post-build check: it needs the outputs of `lake build CslibFrontier`, and refuses stale
ones unless `--no-build-check` is given.

The check supplements review: a clean run is not evidence that a reduction is efficient in the
sense its theorem needs. A witness is recognized by the constants its conclusion mentions, so
the check does not judge whether the witness assumes only the adversary's certificate, covers the
oracles the reduction simulates, or is the one the asymptotic theorem uses. It does not see a
reduction written inline in a bound, a bound without an advantage-named constant, a simulator or
extractor on the bounded side or outside any advantage bound, an attack, or an uncertified setup
sampler or scheme algorithm.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import check_hardness_assumptions as cha  # noqa: E402
import check_security_premises as csp  # noqa: E402
import lean_outputs as lo  # noqa: E402

BASELINE = ROOT / "scripts/reduction_witnesses_baseline.json"
# A change to the checker or its baseline enforces every module, so that its own CI run sees
# whether the whole library still matches.
CHECKER_FILES = frozenset({csp.TOOL, "scripts/check_reduction_witnesses.py",
                           "scripts/reduction_witnesses_baseline.json"})
UPDATE = "python3 scripts/check_reduction_witnesses.py --update-baseline"
RULE = "AGENTS.md, Security theorems"
KINDS = ("gap", "exempt")


@dataclass(frozen=True)
class Reduction:
    """A reduction: its name, defining module path and line, the theorems that state an advantage
    bound with it and their module paths, and its certificate: `direct`, `abbrev` or `wrapper`
    with the certifying declarations, or the empty string when it has none."""
    name: str
    path: str
    line: int
    theorems: tuple[str, ...]
    stated_in: tuple[str, ...]
    certificate: str
    certified_by: tuple[str, ...]

    def paths(self) -> set[str]:
        return {self.path, *self.stated_in}


def parse(output: str) -> tuple[dict[str, Reduction], dict]:
    """The reductions and the summary line of `scripts/SecurityPremises.lean --reductions`."""
    reductions, summary = {}, {}
    for line in output.splitlines():
        row = json.loads(line)
        if "n" not in row:
            summary = row
            continue
        reductions[row["n"]] = Reduction(
            row["n"], csp.module_path(row["m"]), row["l"], tuple(row["t"]),
            tuple(csp.module_path(m) for m in row["tm"]), row["k"], tuple(row["w"]))
    return reductions, summary


def scan(root: Path, build_dir: Path, upstream: Path) -> dict[str, Reduction]:
    """Run the Lean reader over every library module, with CSLib as context."""
    lines = cha.context_modules(upstream) + csp.library_modules(root)
    out = subprocess.run(["lake", "env", "lean", "--run", csp.TOOL, str(build_dir),
                          "--reductions"], cwd=root, input="\n".join(lines) + "\n",
                         capture_output=True, text=True)
    if out.returncode:
        sys.exit(f"{csp.TOOL} failed:\n{out.stderr or out.stdout}")
    reductions, summary = parse(out.stdout)
    if summary.get("missing"):
        sys.exit(f"build outputs are missing for {len(summary['missing'])} module(s), e.g. "
                 f"{summary['missing'][0]}; run `lake build CslibFrontier` first")
    return reductions


def uncertified(reductions: dict[str, Reduction]) -> dict[str, Reduction]:
    return {name: r for name, r in reductions.items() if not r.certificate}


def load_baseline(path: Path) -> dict[str, dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    ok = isinstance(data, dict) and all(
        isinstance(v, dict) and set(v) == {"module", "kind", "why"}
        and isinstance(v["module"], str) and isinstance(v["why"], str) and v["kind"] in KINDS
        for v in data.values())
    if not ok:
        sys.exit(f"{path}: expected a JSON object from reduction names to "
                 '{"module": path, "kind": "gap" or "exempt", "why": justification}')
    return data


def baseline_text(entries: dict[str, dict]) -> str:
    """One entry per line, grouped by module, so concurrent edits rarely touch the same lines."""
    order = sorted(entries, key=lambda n: (entries[n]["module"], n))
    lines = [f" {json.dumps(n, ensure_ascii=False)}: "
             + json.dumps({"module": entries[n]["module"], "kind": entries[n]["kind"],
                           "why": entries[n]["why"]}, ensure_ascii=False)
             for n in order]
    return "{\n" + ",\n".join(lines) + ("\n" if lines else "") + "}\n"


@dataclass(frozen=True)
class Problems:
    """Differences from the baseline: unrecorded uncertified reductions, entries that no longer
    match as `(reduction, entry, reason)`, and entries without a justification."""
    new: list[Reduction]
    stale: list[tuple[str, dict, str]]
    unjustified: list[str]

    def __bool__(self) -> bool:
        return bool(self.new or self.stale or self.unjustified)


def compare(reductions: dict[str, Reduction], baseline: dict[str, dict],
            paths: set[str] | None) -> Problems:
    """The differences in the modules `paths` (every module when `None`)."""
    def scoped(*candidates: str) -> bool:
        return paths is None or bool(paths.intersection(candidates))
    new, stale, unjustified = [], [], []
    for name, r in sorted(uncertified(reductions).items(),
                          key=lambda i: (i[1].path, i[1].line, i[0])):
        if scoped(*r.paths()) and name not in baseline:
            new.append(r)
    for name, entry in sorted(baseline.items(), key=lambda i: (i[1]["module"], i[0])):
        r = reductions.get(name)
        if not scoped(entry["module"], *(r.paths() if r else ())):
            continue
        if r is None:
            stale.append((name, entry, "no theorem states an advantage bound with it"))
        elif r.certificate:
            stale.append((name, entry, f"certified ({r.certificate}: {', '.join(r.certified_by)})"))
        elif r.path != entry["module"]:
            stale.append((name, entry, f"now defined in {r.path}"))
        if not entry["why"].strip():
            unjustified.append(name)
    return Problems(new, stale, unjustified)


def outside(everywhere: Problems, here: Problems) -> Problems:
    """The differences of `everywhere` that are not in `here`."""
    return Problems([p for p in everywhere.new if p not in here.new],
                    [p for p in everywhere.stale if p not in here.stale],
                    [p for p in everywhere.unjustified if p not in here.unjustified])


def checker_changed(root: Path, ref: str) -> bool:
    """Whether the change adds or modifies the checker or its baseline."""
    added, modified = cer.ccf.changed_files(root, ref)
    return bool(CHECKER_FILES.intersection(added + modified))


def describe(r: Reduction) -> list[str]:
    shown = ", ".join(f"`{t}`" for t in r.theorems[:3])
    more = f" and {len(r.theorems) - 3} more" if len(r.theorems) > 3 else ""
    return [f"  {r.path}:{r.line}: {r.name}", f"    bound stated by {shown}{more}"]


def report(problems: Problems) -> str:
    out = []
    if problems.new:
        out += ["Explicit reductions without an efficiency witness. Each reduction needs a "
                f"certificate proved from the adversary's ({RULE}): prove `isPPT_…` or "
                "`isOraclePPT_…` for it (as `isPPT_elGamalMsgToDDHDistinguisher` does), or for the "
                "word-level program that runs it, and apply the hardness assumption through that "
                "lemma. If the bound is information-theoretic, or the definition is not a "
                "reduction (a scheme or protocol built from a component), add a baseline entry "
                f"with `\"kind\": \"exempt\"` and a justification (`{UPDATE}`, then fill in "
                "`why`).", ""]
        for r in problems.new:
            out += describe(r)
    if problems.stale:
        out += ([""] if out else []) + [
            "Baseline entries that no longer match an uncertified reduction; remove or update "
            f"them in the same change (`{UPDATE}`):"]
        out += [f"  {entry['module']}: {name} ({reason})" for name, entry, reason in problems.stale]
    if problems.unjustified:
        out += ([""] if out else []) + ["Baseline entries without a justification (`why`):"]
        out += [f"  {name}" for name in problems.unjustified]
    return "\n".join(out)


def listing(reductions: dict[str, Reduction], prefix: str) -> str:
    chosen = sorted((r for r in reductions.values() if r.path.startswith(prefix)),
                    key=lambda r: (r.path, r.line, r.name))
    out = []
    for r in chosen:
        out += describe(r)
        out.append(f"    certified {r.certificate}: {', '.join(r.certified_by[:3])}"
                   if r.certificate else "    no efficiency witness")
    return "\n".join(out + [f"{len(chosen)} reduction(s), "
                            f"{len(uncertified({r.name: r for r in chosen}))} without an "
                            "efficiency witness"])


def update(reductions: dict[str, Reduction], baseline: dict[str, dict], paths: set[str] | None
           ) -> dict[str, dict]:
    """The baseline with the entries of the modules `paths` (all when `None`) matching the
    uncertified reductions: existing kinds and justifications are kept, new entries are gaps with
    an empty justification."""
    def scoped(*candidates: str) -> bool:
        return paths is None or bool(paths.intersection(candidates))
    updated = {}
    for name, entry in baseline.items():
        r = reductions.get(name)
        if not scoped(entry["module"], *(r.paths() if r else ())):
            updated[name] = entry
    for name, r in uncertified(reductions).items():
        if scoped(*r.paths()):
            old = baseline.get(name, {})
            updated[name] = {"module": r.path, "kind": old.get("kind", "gap"),
                             "why": old.get("why", "")}
    return updated


def status(reductions: dict[str, Reduction], baseline: dict[str, dict], scope_text: str) -> str:
    kinds = Counter(entry["kind"] for entry in baseline.values())
    return (f"{len(reductions)} reduction(s), {len(uncertified(reductions))} without an efficiency "
            f"witness; {len(baseline)} baseline entries ({kinds['gap']} gap(s), "
            f"{kinds['exempt']} exempt), checking {scope_text}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="enforce in the modules changed since the merge base with this "
                            "revision (default origin/main)")
    scope.add_argument("--all", action="store_true", help="enforce in every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help="ignore the baseline and list every reduction defined in the modules "
                            "under the path PREFIX with its certificate; always succeeds")
    parser.add_argument("--update-baseline", action="store_true",
                        help="record the uncertified reductions of the enforced modules")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)
    if (args.report or args.list is not None) and args.update_baseline:
        parser.error("--report and --list do not combine with --update-baseline")
    if not args.no_build_check and not lo.lake_outputs_current(("CslibFrontier",)):
        sys.exit("build outputs are missing or stale; run `lake build CslibFrontier` "
                 "(or pass --no-build-check)")
    reductions = scan(ROOT, lo.DEFAULT_BUILD_DIR, cha.UPSTREAM_BUILD)
    if args.list is not None:
        print(listing(reductions, args.list))
        return 0
    baseline = load_baseline(args.baseline) if args.baseline.exists() else {}
    whole = args.all or args.report
    if not whole and checker_changed(ROOT, args.base):
        whole = True
        print("This change edits the reduction-witness checker or its baseline, so every module "
              "is enforced.")
    paths = None if whole else cer.touched_modules(ROOT, args.base)
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    if args.update_baseline:
        updated = update(reductions, baseline, paths)
        args.baseline.write_text(baseline_text(updated), encoding="utf-8")
        empty = sorted(n for n, e in updated.items() if not e["why"].strip())
        print(f"Wrote {args.baseline} for {scope_text}."
              + (f" Fill in `why` for: {', '.join(empty)}." if empty else ""))
        return 0
    problems = compare(reductions, baseline, paths)
    summary = status(reductions, baseline, scope_text)
    if args.report:
        if problems:
            print(report(problems) + "\n")
        print(f"{summary}; report only, nothing is enforced.")
        return 0
    elsewhere = (outside(compare(reductions, baseline, None), problems)
                 if paths is not None else None)
    if elsewhere:
        print("Not enforced: differences from the baseline in modules this change does not touch. "
              "They fail the next change to those modules. A change can cause them without "
              "touching those modules, for example by deleting a witness; if this one did, fix "
              "them here.\n\n" + report(elsewhere) + "\n")
        if os.environ.get("GITHUB_ACTIONS") == "true":
            count = len(elsewhere.new) + len(elsewhere.stale) + len(elsewhere.unjustified)
            print(f"::notice title=Reduction witnesses::{count} difference(s) from the baseline in "
                  "modules this change does not touch; see the step log.")
    if problems:
        print(report(problems), file=sys.stderr)
        return 1
    print(f"{summary}; every uncertified reduction is recorded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
