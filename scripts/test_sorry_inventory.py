#!/usr/bin/env python3
"""Regression fixtures for the public inventory CLI and compiled environment."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class InventoryTests(unittest.TestCase):
    def report(self, roots, mapped=None, modules=None, extra="", missing=False):
        """Run the CLI on a config with `modules`, `roots`, the `mapped` table (name -> argument) and `extra`
        TOML lines."""
        modules = modules if modules is not None else ["CheckFixtures.SorryInventory"]
        with tempfile.TemporaryDirectory(dir=os.environ.get("RUN_DIR")) as tmp:
            config, out = Path(tmp) / "sorry-inventory.toml", Path(tmp) / "report.json"
            if not missing:
                config.write_text("modules = " + json.dumps(modules) + "\nroots = " + json.dumps(roots) + "\n"
                                  + extra + "\n[mapped]\n" + "".join(f"{k} = {json.dumps(v)}\n"
                                                                     for k, v in (mapped or {}).items()))
            proc = subprocess.run(["python3", "-I", "scripts/sorry-inventory.py",
                                   "--config", str(config), "--json-out", str(out)],
                                  capture_output=True, text=True)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            return json.loads(out.read_text())

    def test_compiled_private_types_cycles_and_mapping(self):
        report = self.report(["SorryInventory.through_private", "SorryInventory.type_only",
                              "SorryInventory.Cycle"], {'"SorryInventory.unfinishedType"': "OPEN"})
        owners = report["sorries"]
        self.assertEqual(len(owners), 2, report)
        private = next(o for o in owners if o["declaration"].endswith(".hidden"))
        self.assertIn("_private", private["declaration"])
        self.assertEqual([a["declaration"] for a in private["ancestors"]],
                         ["SorryInventory.through_private"])
        typed = next(o for o in owners if o["declaration"] == "SorryInventory.unfinishedType")
        ancestors = {a["declaration"] for a in typed["ancestors"]}
        self.assertTrue({"SorryInventory.type_only", "SorryInventory.Cycle",
                         "SorryInventory.Cycle.mk"} <= ancestors, ancestors)
        self.assertEqual(typed["file"], "CheckFixtures/SorryInventory.lean")
        self.assertEqual(typed["mapping"]["argument"], "OPEN")
        self.assertIsNone(private["mapping"])
        self.assertIn(f"unmapped sorry owner: {private['declaration']}", report["issues"])
        self.assertNotIn("SorryInventory.unrelated", {o["declaration"] for o in owners})

    def test_sorry_free_closure_is_mapped_with_no_owners(self):
        # The repository's case today: the closure of the root has no sorry owner and `mapped` is empty.
        report = self.report(["SorryInventory.clean"])
        self.assertEqual((report["status"], report["sorries"], report["issues"]), ("mapped", [], []), report)
        # The negative control: a root whose closure has an owner that `mapped` does not list.
        report = self.report(["SorryInventory.clean", "SorryInventory.through_private"])
        self.assertEqual(report["status"], "incomplete", report)
        self.assertEqual(len(report["sorries"]), 1, report)
        self.assertTrue(any(i.startswith("unmapped sorry owner: ") and i.endswith(".hidden")
                            for i in report["issues"]), report)

    def test_missing_root_is_not_empty_success(self):
        report = self.report([], modules=[])
        self.assertEqual(report["status"], "incomplete")
        self.assertIn("missing concrete obligations root", report["issues"][0])
        self.assertEqual(report["sorries"], [])
        report = self.report(["SorryInventory.missing"])
        self.assertIn("unknown declaration: SorryInventory.missing", report["issues"])

    def test_imported_nonexposed_body(self):
        report = self.report(["SorryInventory.imported"],
                             modules=["CheckFixtures.SorryInventoryImport"])
        self.assertEqual(len(report["sorries"]), 1, report)
        owner = report["sorries"][0]
        self.assertTrue(owner["declaration"].endswith(".hidden"))
        self.assertEqual({a["declaration"] for a in owner["ancestors"]},
                         {"SorryInventory.imported", "SorryInventory.through_private"})

    def test_errors_cannot_be_reported_as_mapped(self):
        for options in ({"missing": True}, {"extra": "not valid TOML"},
                        {"modules": ["CheckFixtures.Nonexistent"],
                         "extra": 'status = "mapped"\nschema_version = 99\nmode = "gate"\nsorries = ["fake"]'}):
            report = self.report(["SorryInventory.type_only"], **options)
            self.assertEqual(report["status"], "incomplete", report)
            self.assertEqual(report["schema_version"], 2)
            self.assertEqual(report["mode"], "report-only")
            self.assertEqual(report["sorries"], [])
            self.assertTrue(report["issues"])

    def test_mapping_errors_and_clean_control(self):
        root = "SorryInventory.unfinishedType"
        report = self.report([root], {f'"{root}"': "OPEN"})
        self.assertEqual(report["status"], "mapped", report)
        report = self.report([root], {f'"{root}"': " "})
        self.assertIn(f"missing paper argument or OPEN: {root}", report["issues"])
        report = self.report([root], {'"unqualified"': "OPEN"})
        self.assertIn("malformed mapped entry: unqualified", report["issues"])
        self.assertIn(f"unmapped sorry owner: {root}", report["issues"])
        report = self.report([root], {f'"{root}"': "OPEN", '"SorryInventory.no_such_name"': "OPEN"})
        self.assertIn("unknown declaration: SorryInventory.no_such_name", report["issues"])


if __name__ == "__main__":
    unittest.main()
