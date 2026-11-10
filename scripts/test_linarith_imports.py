#!/usr/bin/env python3
"""Fixtures for scripts/linarith-imports.py: throwaway source trees with their own boundaries.toml."""
import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "linarith_imports", Path(__file__).resolve().parent / "linarith-imports.py")
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)

BOUNDARIES = """\
[checks]
trusted_paths = ["ConsensusLean/Spec"]

[[lib]]
name = "ConsensusLean"

[[lib]]
name = "ConsensusLeanTest"

[[lib]]
name = "Solution"

[[layer]]
name = "Spec"
prefixes = ["ConsensusLean.Spec"]

[[layer]]
name = "Lemmas"
prefixes = ["ConsensusLean.Lemmas"]

[[layer]]
name = "Proofs"
prefixes = ["ConsensusLean.Proofs"]
allow = ["Lemmas"]

[[layer]]
name = "Tests"
prefixes = ["ConsensusLeanTest"]
allow = ["Lemmas"]

[[layer]]
name = "Core"
prefixes = ["ConsensusLean.Core"]

[[layer]]
name = "Solution"
prefixes = ["Solution"]
allow = ["Lemmas"]
"""
HEADER = "module\npublic import ConsensusLean.Lemmas.Base\n"
CALLS = "public section\n\ntheorem t (a b : Int) (h : a < b) : a ≤ b := by\n  linarith\n"
FRONT = "import ConsensusLean.Lemmas.Tactic.Linarith\n"


class LinarithImportsTests(unittest.TestCase):
    def run_tool(self, files, check=True, exempt=None):
        """Write `files` (path -> text) under a fresh root and run the tool; (exit code, stdout, stderr,
        the files after the run)."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            (root / "scripts/boundaries.toml").write_text(BOUNDARIES)
            for rel, text in files.items():
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(text)
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = tool.main(["--check"] if check else [], root=root, exempt=exempt or {})
            after = {rel: (root / rel).read_text() for rel in files if (root / rel).exists()}
            return rc, out.getvalue(), err.getvalue(), after

    def test_missing_import_fails_and_add_mode_inserts_it(self):
        files = {"ConsensusLean/Lemmas/A.lean": HEADER + CALLS}
        rc, out, err, after = self.run_tool(files)
        self.assertEqual(rc, 1, err)
        self.assertEqual(out, "ConsensusLean/Lemmas/A.lean\n")
        self.assertIn("1 missing", err)
        self.assertEqual(after, files)  # --check changes nothing
        rc, out, err, after = self.run_tool(files, check=False)
        self.assertEqual(rc, 0, err)
        self.assertEqual(after["ConsensusLean/Lemmas/A.lean"], HEADER + FRONT + CALLS)
        rc, _, err, _ = self.run_tool(after)
        self.assertEqual(rc, 0, err)
        self.assertIn("1 already import", err)

    def test_every_import_form_and_the_root_count(self):
        for line in (FRONT, "public import ConsensusLean.Lemmas.Tactic.Linarith\n",
                     "public meta import ConsensusLean.Lemmas.Tactic.Linarith\n", "import ConsensusLean\n"):
            rc, out, err, _ = self.run_tool({"ConsensusLeanTest/T.lean": HEADER + line + CALLS})
            self.assertEqual((rc, out), (0, ""), line + err)
            self.assertIn("1 calling modules, 1 already import", err)

    def test_import_commands_split_over_lines(self):
        for line in ("import\n  ConsensusLean.Lemmas.Tactic.Linarith\n",
                     "public\n  meta import\n    ConsensusLean.Lemmas.Tactic.Linarith\n", "import\n  ConsensusLean\n"):
            rc, out, err, _ = self.run_tool({"ConsensusLean/Lemmas/A.lean": HEADER + line + CALLS})
            self.assertEqual((rc, out), (0, ""), line + err)
        split = "module\npublic import\n  ConsensusLean.Lemmas.Base\n"
        rc, _, err, after = self.run_tool({"ConsensusLean/Lemmas/A.lean": split + CALLS}, check=False)
        self.assertEqual(rc, 0, err)
        self.assertEqual(after["ConsensusLean/Lemmas/A.lean"], split + FRONT + CALLS)  # after the last token

    def test_insertion_goes_before_whatever_follows_the_last_token(self):
        base = "module\npublic import ConsensusLean.Lemmas.Base"
        for trailing in (" /- import note\ncontinued -/\n", " -- import note\n", " public section\n\n"):
            files = {"ConsensusLean/Lemmas/A.lean": base + trailing + CALLS}
            rc, _, err, after = self.run_tool(files, check=False)
            self.assertEqual(rc, 0, err)
            self.assertEqual(after["ConsensusLean/Lemmas/A.lean"],
                             base + "\n" + FRONT.rstrip("\n") + trailing + CALLS)
            rc, out, err, _ = self.run_tool(after)  # the repair holds: the check passes, add is a no-op
            self.assertEqual((rc, out), (0, ""), trailing + err)
            self.assertEqual(self.run_tool(after, check=False)[3], after)

    def test_single_module_library_root(self):
        rc, out, err, _ = self.run_tool({"Solution.lean": HEADER + CALLS})
        self.assertEqual((rc, out), (1, "Solution.lean\n"), err)
        rc, out, err, _ = self.run_tool({"Solution.lean": HEADER + FRONT + CALLS})
        self.assertEqual((rc, out), (0, ""), err)
        self.assertIn("1 calling modules, 1 already import", err)
        rc, out, err, _ = self.run_tool({"Other.lean": HEADER + CALLS})  # control: not a checked library
        self.assertEqual((rc, out), (0, ""), err)
        self.assertIn("0 calling modules", err)

    def test_prelude_with_and_without_module(self):
        for opening in ("module\nprelude\n", "prelude\n"):
            rc, out, err, _ = self.run_tool({"ConsensusLean/Lemmas/A.lean": opening + FRONT + CALLS})
            self.assertEqual((rc, out), (0, ""), opening + err)
            for rest in ("import ConsensusLean.Lemmas.Base\n", ""):  # the import goes after the last token
                rc, _, err, after = self.run_tool({"ConsensusLean/Lemmas/A.lean": opening + rest + CALLS},
                                                  check=False)
                self.assertEqual(rc, 0, opening + rest + err)
                self.assertEqual(after["ConsensusLean/Lemmas/A.lean"], opening + rest + FRONT + CALLS)

    def test_only_plain_calls_count(self):
        for body in ("  linarith only [h]\n", "  linarith!\n", "  linarith (config := {}) [h]\n",
                     "  linarith (preprocessors := []) [h]\n", "  linarith ( config := {})\n",
                     "  nlinarith\n    (config := { splitNe := true })\n",
                     "  nlinarith -splitHypotheses\n", "  exact my_linarith h\n", "  exact Linarith.lemma h\n",
                     "  exact «linarith»\n", "  exact «nlinarith» h\n",
                     "  -- linarith\n  omega\n", "  /- linarith -/ omega\n", '  trace "linarith"\n'):
            text = HEADER + "public section\n\ntheorem t : True := by\n" + body
            rc, out, err, _ = self.run_tool({"ConsensusLean/Lemmas/A.lean": text})
            self.assertEqual((rc, out), (0, ""), body + err)
            self.assertIn("0 calling modules", err, body)
        for body in ("  nlinarith [h]\n", "  first | omega | linarith\n"):  # controls: plain calls
            text = HEADER + "public section\n\ntheorem t : True := by\n" + body
            rc, _, err, _ = self.run_tool({"ConsensusLean/Lemmas/A.lean": text})
            self.assertEqual(rc, 1, body + err)

    def test_modules_that_may_not_import_it_are_left_alone(self):
        files = {"ConsensusLean/Spec/S.lean": HEADER + CALLS,  # trusted path
                 "ConsensusLean/Core/C.lean": HEADER + CALLS,  # layer without Lemmas
                 "ConsensusLean/Lemmas/Tactic/Linarith.lean": HEADER + CALLS}  # the front end itself
        rc, out, err, after = self.run_tool(files, check=False)
        self.assertEqual((rc, out, after), (0, "", files), err)
        self.assertIn("0 calling modules", err)
        rc, out, _, _ = self.run_tool({"ConsensusLean/Proofs/P.lean": HEADER + CALLS})
        self.assertEqual((rc, out), (1, "ConsensusLean/Proofs/P.lean\n"))  # control: Proofs may import Lemmas

    def test_exempt_module_passes_and_is_not_edited(self):
        files = {"ConsensusLean/Lemmas/A.lean": HEADER + CALLS, "ConsensusLean/Lemmas/B.lean": HEADER + CALLS}
        exempt = {"ConsensusLean.Lemmas.A": "measured slower"}
        rc, out, err, after = self.run_tool(files, exempt=exempt)
        self.assertEqual((rc, out), (1, "ConsensusLean/Lemmas/B.lean\n"), err)  # control: B still missing
        self.assertIn("2 calling modules, 0 already import ConsensusLean.Lemmas.Tactic.Linarith, 1 exempt", err)
        rc, out, err, after = self.run_tool(files, check=False, exempt=exempt)
        self.assertEqual(rc, 0, err)
        self.assertEqual(after["ConsensusLean/Lemmas/A.lean"], HEADER + CALLS)
        self.assertEqual(after["ConsensusLean/Lemmas/B.lean"], HEADER + FRONT + CALLS)

    def test_stale_exemptions_fail_both_modes(self):
        exempt = {"ConsensusLean.Lemmas.A": "measured slower"}
        no_call = "no module that may import it calls plain linarith"
        cases = [  # (the file tree, the reason reported)
            ({"ConsensusLean/Lemmas/A.lean": HEADER + FRONT + CALLS}, "imports the front end"),
            ({"ConsensusLean/Lemmas/A.lean": HEADER + "public section\n\ntheorem t : True := trivial\n"}, no_call),
            ({"ConsensusLean/Lemmas/A.lean": HEADER + CALLS.replace("linarith\n", "linarith (preprocessors := [])\n")},
             no_call),  # its only call is configured
            ({"ConsensusLean/Lemmas/B.lean": HEADER + FRONT + CALLS}, no_call),  # gone
        ]
        for files, why in cases:
            for check in (True, False):
                rc, out, err, _ = self.run_tool(files, check=check, exempt=exempt)
                self.assertEqual(rc, 1, str(files) + err)
                self.assertEqual(out, f"stale exemption: ConsensusLean.Lemmas.A ({why})\n", files)
                self.assertIn("1 stale exemptions", err)


if __name__ == "__main__":
    unittest.main()
