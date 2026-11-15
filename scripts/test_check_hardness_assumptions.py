"""Unit tests for scripts/check_hardness_assumptions.py, on synthetic inventories and reader
output and, when Lean is available, on a compiled module (`CompiledFixtureTests`) read by
`scripts/SecurityPremises.lean --assumptions`."""

from __future__ import annotations

import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_hardness_assumptions as c  # noqa: E402

DDH = "Cslib.Crypto.DDH"
ADVICE = "Cslib.Crypto.AdvicePRG"
GENERIC = "Cslib.Crypto.Generic"
KEYS = {"BonehShoup2023", "Gentry2009"}

INVENTORY = """# Inventory

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `DDH` | standard | [BonehShoup2023] Definition 10.8 | Any setup law, `fun x => \\|x\\|`. | — |
| `AdvicePRG` | novel | — | Follows from a non-uniform PRG. | — |
| `Generic` | vocabulary | — | A caller's adversary class. | — |

Text between tables.

| Other | Header |
|---|---|
| `Ignored` | row |
"""


def reading(theorems: dict[str, tuple[str, tuple[str, ...]]],
            docs: dict[str, str] | None = None) -> c.Reading:
    """A reader output: the three assumptions with the given docstrings, and theorems as
    `name -> (docstring, assumptions)`."""
    docs = {DDH: "The DDH assumption ([BonehShoup2023], Definition 10.8).",
            ADVICE: "A PRG against advice. It is novel to this library.",
            GENERIC: "Concrete security.", **(docs or {})}
    r = c.Reading()
    r.assumptions = {n: ("CslibFrontier.Crypto.X", 1, d) for n, d in docs.items()}
    r.theorems = {n: ("CslibFrontier.Crypto.X", 2, d, u) for n, (d, u) in theorems.items()}
    return r


def run(text: str, r: c.Reading, results: str = "") -> c.Problems:
    rows, errors = c.parse_inventory(text)
    return c.check(rows, errors, r, KEYS, results, pathlib.Path("."))


class ParseTests(unittest.TestCase):
    def test_rows_of_inventory_tables_only(self) -> None:
        rows, errors = c.parse_inventory(INVENTORY)
        self.assertEqual(errors, [])
        self.assertEqual([r.name for r in rows], [DDH, ADVICE, GENERIC])
        self.assertEqual([r.status for r in rows], ["standard", "novel", "vocabulary"])
        self.assertEqual(rows[0].line, 5)

    def test_bars_in_code_spans_do_not_split_cells(self) -> None:
        self.assertEqual(c.cells("| `a | b` | c |"), ["`a | b`", "c"])

    def test_malformed_rows(self) -> None:
        header = "\n".join(INVENTORY.splitlines()[2:4])
        _, errors = c.parse_inventory(header + "\n| `X` | standard | s |\n")
        self.assertIn("expected 5 cells", errors[0])
        _, errors = c.parse_inventory(header + "\n| X | standard | s | r | n |\n")
        self.assertIn("one declaration", errors[0])
        _, errors = c.parse_inventory(header + "\n| `X` | assumed | s | r | n |\n")
        self.assertIn("not one of", errors[0])

    def test_full_names_are_kept(self) -> None:
        header = "\n".join(INVENTORY.splitlines()[2:4])
        rows, _ = c.parse_inventory(header + "\n| `Cslib.Other.X` | vocabulary | — | r | — |\n")
        self.assertEqual(rows[0].name, "Cslib.Other.X")

    def test_cited_keys(self) -> None:
        text = "see [BonehShoup2023], [text][Gentry2009], [BonehShoup2023, Sec. 1] and [Unknown]"
        self.assertEqual(c.cited_keys(text, KEYS), ["BonehShoup2023", "Gentry2009"])
        self.assertEqual(c.cited_keys("[Gentry2009; BonehShoup2023, Definition 10.8]", KEYS),
                         ["Gentry2009", "BonehShoup2023"])

    def test_first_sentence(self) -> None:
        self.assertEqual(c.first_sentence("**The GMW theorem.** A step."), "**The GMW theorem.**")
        self.assertEqual(c.first_sentence("Uses `a.b`  here.\nNext."), "Uses `a.b` here.")
        self.assertEqual(c.first_sentence("No full stop"), "No full stop")


class CheckTests(unittest.TestCase):
    def test_documented_assumptions_pass(self) -> None:
        r = reading({"Cslib.Crypto.elGamal": ("ElGamal is secure.", (DDH,)),
                     "Cslib.Crypto.AdvicePRG.gmw": ("A step towards [BonehShoup2023].", (ADVICE,))})
        problems = run(INVENTORY, r)
        self.assertEqual(problems.errors, [])
        self.assertEqual(problems.gaps, {s: {} for s in c.SECTIONS})

    def test_unregistered_assumption_fails(self) -> None:
        r = reading({"Cslib.Crypto.thm": ("", ("Cslib.Crypto.LWE",))},
                    {"Cslib.Crypto.LWE": "LWE."})
        self.assertIn("not in the assumptions inventory", run(INVENTORY, r).errors[0])

    def test_rows_must_name_assumptions_and_cite_keys(self) -> None:
        text = INVENTORY.replace("`Generic` | vocabulary | — | A caller's adversary class.",
                                 "`Missing` | standard | Boneh–Shoup | —")
        errors = run(text, reading({})).errors
        self.assertTrue(any("`Missing` is not a named assumption" in e for e in errors))
        self.assertTrue(any("cites no key" in e for e in errors))
        text = INVENTORY.replace("Follows from a non-uniform PRG.", "—")
        self.assertTrue(any("needs its relation" in e for e in run(text, reading({})).errors))
        self.assertTrue(any("registered twice" in e for e in run(
            INVENTORY.replace("| `Generic` |", "| `DDH` |"), reading({})).errors))

    def test_docstring_and_locator_gaps(self) -> None:
        text = INVENTORY.replace("Definition 10.8 |", "Definition 10.8 (locator not verified) |")
        r = reading({}, {DDH: "The DDH assumption.", ADVICE: "A PRG against advice."})
        gaps = run(text, r).gaps
        self.assertEqual(set(gaps["docstrings"]), {DDH, ADVICE})
        self.assertEqual(set(gaps["locators"]), {DDH})

    def test_docstrings_may_cite_with_locators_and_several_keys(self) -> None:
        for doc in ("DDH ([BonehShoup2023, Definition 10.8]).",
                    "DDH [Gentry2009; BonehShoup2023]."):
            self.assertEqual(run(INVENTORY, reading({}, {DDH: doc})).gaps["docstrings"], {}, doc)

    def test_locators_are_checked_for_every_status(self) -> None:
        text = (INVENTORY.replace("| novel | — |", "| novel | [Gentry2009] Section 2 "
                                  "(locator not verified) is the closest source. |")
                .replace("| vocabulary | — |", "| vocabulary | [BonehShoup2023] Section 3 "
                         "(locator not verified) |"))
        self.assertEqual(set(run(text, reading({})).gaps["locators"]), {ADVICE, GENERIC})

    def test_premises_named_like_vocabulary_need_rows(self) -> None:
        keys = "Cslib.Crypto.KeysIndistinguishable"
        r = reading({"Cslib.Crypto.scheme_secure": ("Secure.", (keys, GENERIC))},
                    {keys: "The keys are indistinguishable from ideal ones."})
        errors = run(INVENTORY, r).errors
        self.assertEqual(len(errors), 1)
        self.assertIn("`KeysIndistinguishable`", errors[0])
        self.assertIn("not in the assumptions inventory", errors[0])

    def test_theorems_on_novel_assumptions_name_them_and_are_steps(self) -> None:
        r = reading({"Cslib.Crypto.PseudorandomGenerator.gmw": ("GMW [BonehShoup2023].",
                                                               (ADVICE,)),
                     "Cslib.Crypto.gmw_of_advicePRG": ("GMW [BonehShoup2023].", (ADVICE,)),
                     "Cslib.Crypto.AdvicePRG.helper": ("No citation.", (ADVICE,))})
        gaps = run(INVENTORY, r).gaps["headlines"]
        self.assertIn("name does not mention", gaps["Cslib.Crypto.PseudorandomGenerator.gmw"])
        self.assertIn("does not open as a step", gaps["Cslib.Crypto.gmw_of_advicePRG"])
        self.assertNotIn("Cslib.Crypto.AdvicePRG.helper", gaps)

    def test_the_step_test_reads_the_first_sentence(self) -> None:
        docs = {
            # A later "steps" does not make a headline a step.
            "zk_of_advicePRG": "**The GMW theorem** [BonehShoup2023]: the simulator's steps are "
                               "polynomial.",
            # A named theorem without a bibliography key is still a cited result.
            "zk2_of_advicePRG": "**The GMW theorem**: every NP language has a proof.",
            "zk3_of_advicePRG": "**Soundness-amplified GMW theorem under `AdvicePRG`.** A step.",
            # A bold title names a result even without the word "theorem".
            "zk4_of_advicePRG": "**Soundness-amplified GMW for NP relations.** Every relation.",
            "step_of_advicePRG": "A step towards [BonehShoup2023], Section 20.1, not that result.",
            "helper_of_advicePRG": "Algebraic helper, not a security theorem [BonehShoup2023].",
            "original_of_advicePRG": "An original consequence of `AdvicePRG`.",
        }
        r = reading({f"Cslib.Crypto.{n}": (d, (ADVICE,)) for n, d in docs.items()})
        gaps = run(INVENTORY, r).gaps["headlines"]
        self.assertEqual({n.removeprefix("Cslib.Crypto.") for n in gaps},
                         {"zk_of_advicePRG", "zk2_of_advicePRG", "zk3_of_advicePRG",
                          "zk4_of_advicePRG"})

    def test_results_inventory_never_lists_a_novel_assumption(self) -> None:
        r = reading({"Cslib.Crypto.AdvicePRG.gmw": ("", (ADVICE,)),
                     "Cslib.Crypto.elGamal": ("", (DDH,))})
        results = "theorems := [Cslib.Crypto.AdvicePRG.gmw, Cslib.Crypto.elGamal]"
        errors = run(INVENTORY, r, results).errors
        self.assertEqual(len(errors), 1)
        self.assertIn("results inventory lists `AdvicePRG.gmw`", errors[0])

    def test_nonvacuity_links(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp)
            (base / "Test.lean").write_text("theorem not_ddh : True := trivial\n")
            row = c.Row(DDH, "standard", "", "", "[Test.lean](Test.lean) `not_ddh`", 1)
            self.assertEqual(c.nonvacuity_errors(row, base), [])
            row = c.Row(DDH, "standard", "", "", "[Test.lean](Test.lean) `not_cdh`", 1)
            self.assertIn("not in the linked files", c.nonvacuity_errors(row, base)[0])
            row = c.Row(DDH, "standard", "", "", "[Gone.lean](Gone.lean)", 1)
            self.assertIn("does not exist", c.nonvacuity_errors(row, base)[0])


class BaselineTests(unittest.TestCase):
    def test_new_stale_and_unjustified_entries(self) -> None:
        problems = c.Problems([], {"docstrings": {DDH: "no citation"}, "locators": {},
                                   "headlines": {}})
        baseline = {"docstrings": {}, "locators": {ADVICE: ""}, "headlines": {}}
        new, stale, unjustified = problems.baseline_differences(baseline)
        self.assertEqual(new, [("docstrings", DDH, "no citation")])
        self.assertEqual(stale, [("locators", ADVICE)])
        self.assertEqual(unjustified, [("locators", ADVICE)])

    def test_text_round_trips_one_entry_per_line(self) -> None:
        baseline = {"docstrings": {DDH: "why", ADVICE: "because"}, "locators": {},
                    "headlines": {"Cslib.Crypto.t": "step"}}
        text = c.baseline_text(baseline)
        self.assertEqual(json.loads(text), baseline)
        self.assertIn(f'  "{ADVICE}": "because",\n', text)


FIXTURE = """module
public import Init
public section

namespace Cslib.Crypto

def Negligible (f : Nat → Nat) : Prop := ∀ n, f n = 0
def advantage (_A : Nat) (n : Nat) : Nat := n
def Game.Indistinguishable (f : Nat → Nat → Nat) : Prop := ∀ A, Negligible (f A)

/-- A named assumption. -/
def Hard : Prop := ∀ A : Nat, Negligible (advantage A)
/-- A named assumption through another one. -/
def HardToo (k : Nat) : Prop := Hard ∧ k = k
/-- A notion as a structure. -/
structure Secure (k : Nat) : Prop where
  secure : Game.Indistinguishable fun A n => advantage (A + k) n
/-- A library-specific premise named like generic vocabulary. -/
def KeysIndistinguishable (k : Nat) : Prop := Game.Indistinguishable fun A n => advantage A (n + k)
/-- Not a security claim. -/
def Correct (k : Nat) : Prop := k = k

/-- Rests on two named assumptions. -/
theorem fromHard (_h : Hard) (_h' : ∀ k, HardToo k ∧ Secure k) (_c : Correct 0) : True :=
  trivial
theorem fromVocabulary (_h : Negligible id) (_h' : Game.Indistinguishable fun _ n => n) :
    True := trivial
theorem fromKeys (_h : KeysIndistinguishable 0) : True := trivial
theorem fromCorrect (_c : Correct 0) : True := trivial
private theorem privateHard (_h : Hard) : True := trivial

end Cslib.Crypto
"""


@unittest.skipUnless(shutil.which("lake") and (c.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """What `scripts/SecurityPremises.lean --assumptions` reports for a compiled module."""

    @classmethod
    def setUpClass(cls) -> None:
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        source = root / "src/CslibFrontier/Crypto/Fixture.lean"
        olean = root / "build/CslibFrontier/Crypto/Fixture.olean"
        source.parent.mkdir(parents=True)
        olean.parent.mkdir(parents=True)
        source.write_text(FIXTURE)
        subprocess.run(["lake", "env", "lean", f"--root={root / 'src'}", "-o", str(olean),
                        str(source)], cwd=c.ROOT, check=True, capture_output=True)
        out = subprocess.run(["lake", "env", "lean", "--run", c.csp.TOOL, str(root / "build"),
                              "--assumptions"], cwd=c.ROOT,
                             input="CslibFrontier.Crypto.Fixture\n", capture_output=True,
                             text=True, check=True).stdout
        cls.reading = c.read(out)

    def test_named_assumptions(self) -> None:
        """No name is excluded: generic `Game.Indistinguishable` and a library-specific
        `KeysIndistinguishable` are reported; `Negligible`, whose definition reaches no security
        atom, and `Correct` are not."""
        names = {n.removeprefix("Cslib.Crypto.") for n in self.reading.assumptions}
        self.assertEqual(names, {"Hard", "HardToo", "Secure", "KeysIndistinguishable",
                                 "Game.Indistinguishable"})
        self.assertEqual(self.reading.assumptions["Cslib.Crypto.Hard"][2], "A named assumption.")

    def test_theorems_and_their_assumptions(self) -> None:
        theorems = {n.removeprefix("Cslib.Crypto."): set(u)
                    for n, (_, _, _, u) in self.reading.theorems.items()}
        self.assertEqual(theorems, {
            "fromHard": {"Cslib.Crypto.Hard", "Cslib.Crypto.HardToo", "Cslib.Crypto.Secure"},
            "fromVocabulary": {"Cslib.Crypto.Game.Indistinguishable"},
            "fromKeys": {"Cslib.Crypto.KeysIndistinguishable"}})
        self.assertEqual(self.reading.summary["theorems"], 4)


class CommittedFilesTests(unittest.TestCase):
    """The inventory and the baseline themselves, which every event checks."""

    def test_inventory_parses(self) -> None:
        rows, errors = c.parse_inventory(c.INVENTORY.read_text(encoding="utf-8"))
        self.assertEqual(errors, [])
        keys = c.bibliography_keys(c.BIBLIOGRAPHY.read_text(encoding="utf-8"))
        for row in rows:
            if row.status == "standard":
                self.assertTrue(c.cited_keys(row.source, keys), row.name)
            self.assertEqual(c.nonvacuity_errors(row, c.INVENTORY.parent), [], row.name)

    def test_baseline_is_canonical_and_justified(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(encoding="utf-8"), c.baseline_text(baseline))
        for section, entries in baseline.items():
            for name, why in entries.items():
                self.assertTrue(why.strip(), f"{section}: {name}")


if __name__ == "__main__":
    unittest.main()
