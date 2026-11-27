#!/usr/bin/env python3
"""Public CLI fixtures for the adoption rename and collision refusal."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("adopt_pu_names.py")
SOURCE = "ConsensusLean/Instances/Goldilocks/Lemmas/Shadow/PU/Fixture.lean"


class AdoptionRenameTest(unittest.TestCase):
    def test_rename_is_token_aware_and_idempotent(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / SOURCE
            p.parent.mkdir(parents=True)
            p.write_text("namespace N\n"
                         "-- f_at' remains documentation\n"
                         "/- outer /- f_at' -/ f_at' -/\n"
                         "theorem f_at' := True.intro\n"
                         "def frameKey'' := 2\n"
                         "def use := (f_at', frameKey'', \"f_at'\")\n"
                         "def localVar (st' : Nat) := st'\nend N\n")
            run = lambda mode: subprocess.run(
                [sys.executable, "-I", str(SCRIPT), mode, "--root", d],
                capture_output=True, text=True)
            self.assertEqual(run("--check").returncode, 1)
            self.assertEqual(run("--write").returncode, 0)
            expected = ("namespace N\n"
                        "-- f_at' remains documentation\n"
                        "/- outer /- f_at' -/ f_at' -/\n"
                        "theorem f_at := True.intro\n"
                        "def frameKey'' := 2\n"
                        "def use := (f_at, frameKey'', \"f_at'\")\n"
                        "def localVar (st' : Nat) := st'\nend N\n")
            self.assertEqual(p.read_text(), expected)
            self.assertEqual(run("--check").returncode, 0)
            self.assertEqual(run("--write").returncode, 0)
            self.assertEqual(p.read_text(), expected)

    def test_reintroduced_reference_without_primed_definition(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / "ConsensusLean/Merged.lean"
            p.parent.mkdir(parents=True)
            p.write_text("def use := GoldilocksRun'\n")
            args = [sys.executable, "-I", str(SCRIPT), "--root", d]
            result = subprocess.run([*args, "--write"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0)
            self.assertEqual(p.read_text(), "def use := GoldilocksRun\n")
            self.assertEqual(subprocess.run([*args, "--check"], capture_output=True).returncode, 0)

    def test_stock_private_helper_preserves_shared_atom(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / SOURCE
            p.parent.mkdir(parents=True)
            original = "namespace N\ntheorem f_at' : True := True.intro\nend N\n"
            p.write_text(original)
            stock = root / "ConsensusLean/Stock.lean"
            private = "namespace Other\nprivate theorem f_at' : True := True.intro\nend Other\n"
            stock.write_text(private)
            result = subprocess.run([sys.executable, "-I", str(SCRIPT), "--root", d, "--write"],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0)
            self.assertEqual(p.read_text(), original)
            self.assertEqual(stock.read_text(), private)

    def test_collision_refuses_all_writes(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / SOURCE
            p.parent.mkdir(parents=True)
            original = "namespace N\ntheorem f_at' := True.intro\nend N\n"
            p.write_text(original)
            stock = root / "ConsensusLean/Stock.lean"
            stock.write_text("namespace N\ntheorem f_at (n : Nat) := True.intro\nend N\n")
            args = [sys.executable, "-I", str(SCRIPT), "--root", d]
            report = subprocess.run([*args, "--report"], check=True, capture_output=True, text=True)
            self.assertEqual(set(json.loads(report.stdout)["collisions"]), {"N.f_at"})
            result = subprocess.run([*args, "--write"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("N.f_at", result.stdout)
            self.assertEqual(p.read_text(), original)

    def test_matching_proof_keeps_stock_and_redirects_shadow(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / SOURCE
            p.parent.mkdir(parents=True)
            p.write_text("module\nnamespace N\ntheorem f_at' : True := True.intro\nend N\n")
            stock = root / "ConsensusLean/Stock.lean"
            canonical = "module\nnamespace N\ntheorem f_at : True := by trivial\nend N\n"
            stock.write_text(canonical)
            args = [sys.executable, "-I", str(SCRIPT), "--root", d]
            self.assertEqual(subprocess.run([*args, "--write"], capture_output=True).returncode, 0)
            self.assertEqual(stock.read_text(), canonical)
            self.assertNotIn("theorem f_at", p.read_text())
            self.assertIn("public import ConsensusLean.Stock", p.read_text())
            self.assertEqual(subprocess.run([*args, "--check"], capture_output=True).returncode, 0)

    def test_import_cycle_refuses_all_writes(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent.parent / ".amp/in/orb-backup") as d:
            root = Path(d)
            p = root / SOURCE
            p.parent.mkdir(parents=True)
            original = "module\nnamespace N\ntheorem f_at' : True := True.intro\nend N\n"
            p.write_text(original)
            stock = root / "ConsensusLean/Stock.lean"
            stock.write_text("module\nimport " + SOURCE.removesuffix(".lean").replace("/", ".") +
                             "\nnamespace N\ntheorem f_at : True := True.intro\nend N\n")
            result = subprocess.run([sys.executable, "-I", str(SCRIPT), "--root", d, "--write"],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("IMPORT CYCLE", result.stdout)
            self.assertEqual(p.read_text(), original)


if __name__ == "__main__":
    unittest.main()
