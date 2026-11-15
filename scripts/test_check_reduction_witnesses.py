"""Unit tests for scripts/check_reduction_witnesses.py, on synthetic reader output and, when Lean
is available, on a compiled module (`CompiledFixtureTests`) read by
`scripts/SecurityPremises.lean --reductions`."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_reduction_witnesses as c  # noqa: E402

CERTIFIED = "Cslib.Crypto.ElGamal.toDDHDistinguisher"
UNCERTIFIED = "Cslib.Crypto.Schnorr.forkingReduction"
EXEMPT = "Cslib.Crypto.Signature.toScheme"
ELGAMAL_PATH = "CslibFrontier/Crypto/ElGamal.lean"
SCHNORR_PATH = "CslibFrontier/Crypto/Schnorr.lean"
SIGNATURE_PATH = "CslibFrontier/Crypto/Signature.lean"
CLIENT_PATH = "CslibFrontier/Crypto/SchnorrClient.lean"


def row(name: str, module: str, line: int, theorems: list[str], stated_in: list[str],
        certificate: str = "", certified_by: list[str] | None = None) -> str:
    """A line of the reader's output."""
    return json.dumps({"n": name, "m": module, "l": line, "t": theorems, "tm": stated_in,
                       "k": certificate, "w": certified_by or []})


OUTPUT = "\n".join([
    row(CERTIFIED, "CslibFrontier.Crypto.ElGamal", 10, ["Cslib.Crypto.ElGamal.advantage_le"],
        ["CslibFrontier.Crypto.ElGamal"], "direct", ["Cslib.Crypto.ElGamal.isPPT_toDDH"]),
    row(UNCERTIFIED, "CslibFrontier.Crypto.Schnorr", 20,
        ["Cslib.Crypto.Schnorr.succProbability_le", "Cslib.Crypto.SchnorrClient.bound"],
        ["CslibFrontier.Crypto.Schnorr", "CslibFrontier.Crypto.SchnorrClient"]),
    row(EXEMPT, "CslibFrontier.Crypto.Signature", 30, ["Cslib.Crypto.Signature.advantage_eq"],
        ["CslibFrontier.Crypto.Signature"]),
    json.dumps({"theorems": 4, "modules": 4, "missing": []}),
])


def entry(path: str, kind: str = "gap", why: str = "tracked in #5293 section 2") -> dict:
    return {"module": path, "kind": kind, "why": why}


BASELINE = {UNCERTIFIED: entry(SCHNORR_PATH),
            EXEMPT: entry(SIGNATURE_PATH, "exempt", "not a reduction: a typed scheme")}


class ParseTests(unittest.TestCase):
    def test_rows_and_summary(self) -> None:
        reductions, summary = c.parse(OUTPUT)
        self.assertEqual(summary["theorems"], 4)
        self.assertEqual(reductions[CERTIFIED].path, ELGAMAL_PATH)
        self.assertEqual(reductions[CERTIFIED].certificate, "direct")
        self.assertEqual(reductions[UNCERTIFIED].line, 20)
        self.assertEqual(reductions[UNCERTIFIED].paths(), {SCHNORR_PATH, CLIENT_PATH})
        self.assertEqual(set(c.uncertified(reductions)), {UNCERTIFIED, EXEMPT})


class CompareTests(unittest.TestCase):
    def setUp(self) -> None:
        self.reductions, _ = c.parse(OUTPUT)

    def test_certified_and_recorded_reductions_pass(self) -> None:
        self.assertFalse(c.compare(self.reductions, BASELINE, None))

    def test_an_uncertified_reduction_fails_only_in_scope(self) -> None:
        problems = c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, None)
        self.assertEqual([r.name for r in problems.new], [UNCERTIFIED])
        self.assertFalse(c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, {ELGAMAL_PATH}))

    def test_a_reduction_belongs_to_the_modules_that_state_its_bounds(self) -> None:
        # A change to a client that states a bound with the reduction enforces it too.
        problems = c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, {CLIENT_PATH})
        self.assertEqual([r.name for r in problems.new], [UNCERTIFIED])

    def test_an_exempt_reduction_needs_its_entry(self) -> None:
        problems = c.compare(self.reductions, {UNCERTIFIED: BASELINE[UNCERTIFIED]}, None)
        self.assertEqual([r.name for r in problems.new], [EXEMPT])

    def test_stale_entries_fail_in_their_module(self) -> None:
        # A reduction that gained its witness, and one that no theorem bounds any more.
        baseline = {**BASELINE, CERTIFIED: entry(ELGAMAL_PATH),
                    "Cslib.Crypto.Gone.reduction": entry("CslibFrontier/Crypto/Gone.lean")}
        stale = c.compare(self.reductions, baseline, None).stale
        self.assertEqual([(name, reason) for name, _, reason in stale], [
            (CERTIFIED, "certified (direct: Cslib.Crypto.ElGamal.isPPT_toDDH)"),
            ("Cslib.Crypto.Gone.reduction", "no theorem states an advantage bound with it")])
        self.assertFalse(c.compare(self.reductions, baseline, {SCHNORR_PATH}))
        self.assertEqual(len(c.compare(self.reductions, baseline, {ELGAMAL_PATH}).stale), 1)

    def test_moved_reduction_needs_its_entry_updated(self) -> None:
        baseline = {**BASELINE, UNCERTIFIED: entry("CslibFrontier/Crypto/Old.lean")}
        problems = c.compare(self.reductions, baseline, {SCHNORR_PATH})
        self.assertEqual([(name, reason) for name, _, reason in problems.stale],
                         [(UNCERTIFIED, f"now defined in {SCHNORR_PATH}")])

    def test_entries_need_a_justification(self) -> None:
        baseline = {**BASELINE, UNCERTIFIED: entry(SCHNORR_PATH, why="  ")}
        self.assertEqual(c.compare(self.reductions, baseline, None).unjustified, [UNCERTIFIED])


class BaselineTests(unittest.TestCase):
    def test_text_round_trips_one_entry_per_line(self) -> None:
        text = c.baseline_text(BASELINE)
        self.assertEqual(json.loads(text), BASELINE)
        self.assertEqual(len(text.splitlines()), len(BASELINE) + 2)
        self.assertEqual(c.baseline_text({}), "{\n}\n")

    def test_kind_is_gap_or_exempt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "baseline.json"
            path.write_text(json.dumps({UNCERTIFIED: entry(SCHNORR_PATH, "later")}))
            with self.assertRaises(SystemExit):
                c.load_baseline(path)

    def test_update_keeps_justifications_and_drops_stale_entries(self) -> None:
        reductions, _ = c.parse(OUTPUT)
        baseline = {EXEMPT: BASELINE[EXEMPT], CERTIFIED: entry(ELGAMAL_PATH),
                    "Cslib.Crypto.Gone.reduction": entry("CslibFrontier/Crypto/Gone.lean")}
        updated = c.update(reductions, baseline, None)
        self.assertEqual(updated, {EXEMPT: BASELINE[EXEMPT],
                                   UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})
        # Outside the changed modules, entries stay as they are.
        self.assertEqual(c.update(reductions, baseline, {SCHNORR_PATH}),
                         {**baseline, UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})


class CheckerChangedTests(unittest.TestCase):
    def test_only_the_checker_and_its_baseline_count(self) -> None:
        for changed, expected in ((["scripts/reduction_witnesses_baseline.json"], True),
                                  (["scripts/SecurityPremises.lean"], True),
                                  (["scripts/check_reduction_witnesses.py"], True),
                                  (["scripts/security_premises_baseline.json"], False),
                                  (["CslibFrontier/Crypto/Schnorr.lean", "AGENTS.md"], False)):
            with mock.patch.object(c.cer.ccf, "changed_files", return_value=(changed, [])):
                self.assertEqual(c.checker_changed(c.ROOT, "origin/main"), expected, changed)


class MainTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.baseline = pathlib.Path(tmp.name) / "baseline.json"
        reductions, _ = c.parse(OUTPUT)
        for patcher in (mock.patch.object(c, "scan", return_value=reductions),
                        mock.patch.object(c.cer, "touched_modules", return_value={SCHNORR_PATH}),
                        mock.patch.object(c, "checker_changed", return_value=False)):
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_main(self, baseline: dict | None, *args: str) -> tuple[int, str, str]:
        if baseline is not None:
            self.baseline.write_text(c.baseline_text(baseline))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--no-build-check", "--baseline", str(self.baseline), *args])
        return code, out.getvalue(), err.getvalue()

    def test_pull_request_that_adds_an_uncertified_reduction_fails(self) -> None:
        code, _, err = self.run_main({EXEMPT: BASELINE[EXEMPT]})
        self.assertEqual(code, 1)
        self.assertIn(f"{SCHNORR_PATH}:20: {UNCERTIFIED}", err)
        self.assertIn("bound stated by `Cslib.Crypto.Schnorr.succProbability_le`", err)
        self.assertIn("isPPT_", err)
        self.assertNotIn(EXEMPT, err)
        self.assertNotIn(CERTIFIED, err)

    def test_pull_request_mode_passes_with_the_baseline(self) -> None:
        code, out, err = self.run_main(BASELINE)
        self.assertEqual((code, err), (0, ""))
        self.assertIn("3 reduction(s), 2 without an efficiency witness; 2 baseline entries "
                      "(1 gap(s), 1 exempt), checking 1 changed module(s)", out)

    def test_pull_request_mode_reports_untouched_modules(self) -> None:
        code, out, err = self.run_main({UNCERTIFIED: BASELINE[UNCERTIFIED]})
        self.assertEqual(code, 0)
        self.assertIn("Not enforced", out)
        self.assertIn(f"{SIGNATURE_PATH}:30: {EXEMPT}", out)
        self.assertEqual(err, "")
        with mock.patch.dict(c.os.environ, {"GITHUB_ACTIONS": "true"}):
            out = self.run_main(None)[1]
        self.assertIn("::notice title=Reduction witnesses::1 difference(s)", out)

    def test_a_stale_entry_fails_the_change_that_certifies_the_reduction(self) -> None:
        with mock.patch.object(c.cer, "touched_modules", return_value={ELGAMAL_PATH}):
            code, _, err = self.run_main({**BASELINE, CERTIFIED: entry(ELGAMAL_PATH)})
        self.assertEqual(code, 1)
        self.assertIn(f"{ELGAMAL_PATH}: {CERTIFIED} (certified (direct:", err)

    def test_a_change_to_the_checker_enforces_every_module(self) -> None:
        with mock.patch.object(c, "checker_changed", return_value=True):
            code, out, err = self.run_main({UNCERTIFIED: BASELINE[UNCERTIFIED]})
        self.assertEqual(code, 1)
        self.assertIn("every module is enforced", out)
        self.assertIn(f"{SIGNATURE_PATH}:30: {EXEMPT}", err)

    def test_report_mode_succeeds(self) -> None:
        code, out, _ = self.run_main({}, "--report")
        self.assertEqual(code, 0)
        self.assertIn(UNCERTIFIED, out)
        self.assertIn(EXEMPT, out)
        self.assertIn("report only", out)

    def test_list_shows_certificates(self) -> None:
        code, out, _ = self.run_main(None, "--list", "CslibFrontier/Crypto/")
        self.assertEqual(code, 0)
        self.assertIn("certified direct: Cslib.Crypto.ElGamal.isPPT_toDDH", out)
        self.assertIn("3 reduction(s), 2 without an efficiency witness", out)

    def test_update_then_justify(self) -> None:
        self.assertEqual(self.run_main({}, "--update-baseline")[0], 0)
        written = json.loads(self.baseline.read_text())
        self.assertEqual(written, {UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})
        code, _, err = self.run_main(None)
        self.assertEqual(code, 1)
        self.assertIn("without a justification", err)
        written[UNCERTIFIED]["why"] = "tracked in #5293 section 2"
        self.assertEqual(self.run_main(written)[0], 0)


# A compiled module for `CompiledFixtureTests`, under `CslibFrontier/Crypto` so that it is scanned.
FIXTURE = """module
public import Init
public section

/-- Stands in for Mathlib's `PMF`: a distribution by name. -/
structure PMF (α : Type) where
  weight : α → Nat

/-- Stands in for `PFunctor.FreeM`, which `ProbComp` and `OracleComp` unfold to. -/
structure PFunctor.FreeM (α : Type) where
  run : Nat → α

namespace Cslib.Crypto.Fixture

abbrev ProbComp := PFunctor.FreeM
/-- An adversary given as a function into a computation. -/
abbrev Adversary := Nat → ProbComp Bool
/-- An adversary given as a structure of programs. -/
structure TwoStage where
  choose : Nat → ProbComp Nat
  guess : Nat → ProbComp Bool
/-- A scheme: a structure of programs too. -/
structure Scheme where
  keyGen : Nat → ProbComp Nat
/-- A group: not a program. -/
structure Group where
  order : Nat

def IsPPT (_A : Adversary) : Prop := True
def TwoStage.IsPPT (_A : TwoStage) : Prop := True
def IsPPTOn (_f : Nat → Nat → ProbComp Bool) : Prop := True
def IsQueryBounded (_A : Adversary) (_q : Nat) : Prop := True

def advantage (_G : Group) (_A : Adversary) (n : Nat) : Nat := n
def schemeAdvantage (_S : Scheme) (_A : Adversary) (n : Nat) : Nat := n
def twoStageAdvantage (_A : TwoStage) (n : Nat) : Nat := n
def lawAdvantage (_X : PMF Nat) (_A : Adversary) (n : Nat) : Nat := n
def forgeExperiment (_A : Adversary) (n : Nat) : Nat := n

variable (G : Group) (S : Scheme) (A : Adversary) (n : Nat)

/-! Certified reductions. -/

def certified (A : Adversary) : Adversary := A
theorem isPPT_certified {A : Adversary} (_h : IsPPT A) : IsPPT (certified A) := trivial
theorem certified_le : schemeAdvantage S A n ≤ advantage G (certified A) n := Nat.le_refl _

def privatelyCertified (A : Adversary) : Adversary := A
private theorem isPPT_privatelyCertified : IsPPT (privatelyCertified A) := trivial
theorem privatelyCertified_le : schemeAdvantage S A n ≤ advantage G (privatelyCertified A) n :=
  Nat.le_refl _

def certifiedTwoStage (A : Adversary) : TwoStage := ⟨fun _ => ⟨fun k => k⟩, A⟩
theorem isPPT_certifiedTwoStage (_h : IsPPT A) : (certifiedTwoStage A).IsPPT := trivial
theorem certifiedTwoStage_le :
    schemeAdvantage S A n ≤ twoStageAdvantage (certifiedTwoStage A) n := Nat.le_refl _

/-- An abbreviation of certified reductions is certified. -/
abbrev abbreviated (A : Adversary) : Adversary := certified (privatelyCertified A)
theorem abbreviated_le : schemeAdvantage S A n ≤ advantage G (abbreviated A) n := Nat.le_refl _

/-- A reduction that a certified word-level program runs is certified. -/
def wrapped (A : Adversary) : Adversary := A
def wrappedWords (A : Adversary) (n k : Nat) : ProbComp Bool := wrapped A (n + k)
theorem isPPTOn_wrappedWords (_h : IsPPT A) : IsPPTOn (wrappedWords A) := trivial
theorem wrapped_le : schemeAdvantage S A n ≤ advantage G (wrapped A) n := Nat.le_refl _

/-! Reductions without an efficiency witness. -/

def uncertified (A : Adversary) : Adversary := A
theorem uncertified_le : schemeAdvantage S A n ≤ advantage G (uncertified A) n + 1 :=
  Nat.le_succ _

/-- A query bound is not an efficiency witness. -/
def queryBounded (A : Adversary) : Adversary := A
theorem isQueryBounded_queryBounded : IsQueryBounded (queryBounded A) 3 := trivial
theorem queryBounded_le : schemeAdvantage S A n ≤ advantage G (queryBounded A) n := Nat.le_refl _

def equated (A : Adversary) : Adversary := A
theorem equated_eq : schemeAdvantage S A n = advantage G (equated A) n :=
  Nat.le_antisymm (Nat.le_refl _) (Nat.le_refl _)

def reversed (A : Adversary) : Adversary := A
theorem reversed_ge : advantage G (reversed A) n ≥ schemeAdvantage S A n := Nat.le_refl _

def indexed (A : Adversary) (_i : Nat) : Adversary := A
theorem indexed_le : ∃ i, schemeAdvantage S A n ≤ advantage G (indexed A i) n :=
  ⟨0, Nat.le_refl _⟩

def uncertifiedTwoStage (A : Adversary) : TwoStage := ⟨fun _ => ⟨fun k => k⟩, A⟩
theorem uncertifiedTwoStage_le :
    schemeAdvantage S A n ≤ twoStageAdvantage (uncertifiedTwoStage A) n := Nat.le_refl _

/-- An abbreviation of an uncertified reduction is not certified. -/
abbrev abbreviatedUncertified (A : Adversary) : Adversary := certified (uncertified A)
theorem abbreviatedUncertified_le :
    schemeAdvantage S A n ≤ advantage G (abbreviatedUncertified A) n := Nat.le_refl _

/-- Reported, though not a reduction: a scheme built from the scheme, on the bounding side only.
The baseline exempts such a definition. -/
def typedScheme (S : Scheme) : Scheme := S
theorem typedScheme_eq :
    schemeAdvantage S A n = schemeAdvantage (typedScheme S) (certified A) n :=
  Nat.le_antisymm (Nat.le_refl _) (Nat.le_refl _)

/-! Not reductions. -/

/-- A scheme on both sides. -/
def derivedScheme (S : Scheme) : Scheme := S
theorem derivedScheme_le :
    schemeAdvantage (derivedScheme S) A n ≤ schemeAdvantage (derivedScheme S) (certified A) n :=
  Nat.le_refl _

/-- A law of a component that is not a program. -/
def keyLaw (_G : Group) (_n : Nat) : PMF Nat := ⟨fun _ => 0⟩
theorem keyLaw_le : schemeAdvantage S A n ≤ lawAdvantage (keyLaw G n) (certified A) n :=
  Nat.le_refl _

/-- A number. -/
def loss (_A : Adversary) : Nat := 0
theorem loss_le : schemeAdvantage S A n ≤ advantage G (certified A) n + loss A := Nat.le_refl _

/-- An attack: the bounded side mentions no program variable. -/
def attack (_S : Scheme) : Adversary := fun _ => ⟨fun _ => true⟩
theorem attack_le : n ≤ schemeAdvantage S (attack S) n := Nat.le_refl _

/-- A simulator on the bounded side (a known gap). -/
def simulator (A : Adversary) : Adversary := A
theorem simulator_le : schemeAdvantage S (simulator A) n ≤ advantage G (certified A) n :=
  Nat.le_refl _

/-- A bound without an advantage-named constant (a known gap). -/
def unnamedBound (A : Adversary) : Adversary := A
theorem unnamedBound_le : forgeExperiment A n ≤ forgeExperiment (unnamedBound A) n :=
  Nat.le_refl _

/-- A reduction written inline (a known gap). -/
theorem inline_le : schemeAdvantage S A n ≤ advantage G (fun k => A (k + 1)) n := Nat.le_refl _

/-- A bound stated only by a private theorem. -/
def privatelyStated (A : Adversary) : Adversary := A
private theorem privatelyStated_le :
    schemeAdvantage S A n ≤ advantage G (privatelyStated A) n := Nat.le_refl _

end Cslib.Crypto.Fixture
"""

PREFIX = "Cslib.Crypto.Fixture."


@unittest.skipUnless(shutil.which("lake") and (c.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """What `scripts/SecurityPremises.lean --reductions` reports for a compiled module."""

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
                              "--reductions"], cwd=c.ROOT,
                             input="CslibFrontier.Crypto.Fixture\n",
                             capture_output=True, text=True, check=True).stdout
        reductions, cls.summary = c.parse(out)
        cls.reductions = {name.removeprefix(PREFIX): r for name, r in reductions.items()}

    def certificate(self, name: str) -> tuple[str, tuple[str, ...]]:
        r = self.reductions[name]
        return r.certificate, tuple(w.removeprefix(PREFIX) for w in r.certified_by)

    def test_certified_reductions(self) -> None:
        self.assertEqual(self.certificate("certified"), ("direct", ("isPPT_certified",)))
        self.assertEqual(self.reductions["certified"].path, "CslibFrontier/Crypto/Fixture.lean")
        self.assertIn(PREFIX + "certified_le", self.reductions["certified"].theorems)
        # A private witness counts, and so does a certificate of a structure of programs.
        self.assertEqual(self.certificate("privatelyCertified"),
                         ("direct", ("isPPT_privatelyCertified",)))
        self.assertEqual(self.certificate("certifiedTwoStage"),
                         ("direct", ("isPPT_certifiedTwoStage",)))

    def test_abbreviations_and_wrappers_carry_certificates(self) -> None:
        self.assertEqual(self.certificate("abbreviated"),
                         ("abbrev", ("certified", "privatelyCertified")))
        self.assertEqual(self.certificate("wrapped"), ("wrapper", ("wrappedWords",)))
        self.assertEqual(self.certificate("abbreviatedUncertified"), ("", ()))

    def test_uncertified_reductions(self) -> None:
        for name in ("uncertified", "queryBounded", "equated", "reversed", "indexed",
                     "uncertifiedTwoStage", "abbreviatedUncertified"):
            self.assertEqual(self.certificate(name), ("", ()), name)

    def test_a_scheme_on_the_bounding_side_only_is_reported(self) -> None:
        # A known false positive, which the baseline exempts.
        self.assertEqual(self.certificate("typedScheme"), ("", ()))

    def test_schemes_laws_numbers_and_attacks_are_not_reductions(self) -> None:
        for name in ("derivedScheme", "keyLaw", "loss", "attack", "privatelyStated"):
            self.assertNotIn(name, self.reductions)

    def test_known_limitations(self) -> None:
        # Review covers these cases (the reader's docstring, "Known gaps of this mode").
        for name in ("simulator", "unnamedBound"):
            self.assertNotIn(name, self.reductions)
        self.assertNotIn(PREFIX + "inline_le",
                         [t for r in self.reductions.values() for t in r.theorems])

    def test_exactly_the_expected_reductions(self) -> None:
        self.assertEqual(len(self.reductions), 13)
        self.assertEqual(len(c.uncertified(self.reductions)), 8)
        self.assertEqual(self.summary["missing"], [])


class CommittedFilesTests(unittest.TestCase):
    """These run on every event, merge groups included, so they check only the baseline file
    itself. Whether its entries match the library (a moved or deleted module, say) is the pull
    request check's job, which merge groups only report."""

    def test_baseline_is_canonical_and_justified(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(encoding="utf-8"), c.baseline_text(baseline))
        for name, value in baseline.items():
            self.assertTrue(value["why"].strip(), name)
            self.assertIn(value["kind"], c.KINDS, name)


if __name__ == "__main__":
    unittest.main()
