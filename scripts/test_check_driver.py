#!/usr/bin/env python3
"""Run the actual shell driver with cheap step bodies, not the Lean checks themselves."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).with_name("check.sh").read_text()
CONFIG = Path(__file__).with_name("boundaries.toml").read_text()


class DriverTests(unittest.TestCase):
    def drive(self, *args, bwrap=True, fail_build=False, replay=False, fail_leaf=False,
              stale=False, changed=False):
        with tempfile.TemporaryDirectory(prefix="check-driver-") as tmp:
            root = Path(tmp)
            scripts = root / "scripts"
            scripts.mkdir()
            (scripts / "boundaries.toml").write_text(CONFIG)
            (scripts / "test_check_decls_waivers.sh").write_text("exit 0\n")
            # Keep parsing, configuration, selection, failure handling and summaries verbatim.
            # Only expensive step implementations and external self-test programs are replaced.
            stubs = "\n".join(f'{name}() {{ echo "EXEC {name}"; }}' for name in
                              re.findall(r"^((?:step_|selftest_)\w+)\(\)", SOURCE, re.M)
                              if not (replay and name == "step_replay"))
            stubs += f'\nhave_bwrap() {{ return {0 if bwrap else 1}; }}\n'
            stubs += '''
python3() { echo "EXEC $*"; }
lake() { echo "EXEC lake $*"; }
step_boundaries() {
  printf 'Lib\tLib.Z\tleaf\tlayer\t-\t-\nLib\tLib.A\tleaf\tlayer\t-\t-\nLib\tLib.Parent\tparent\tlayer\t-\t-\nLib\tLib.C\tleaf\tlayer\t-\t-\nLib\tLib.B\tleaf\tlayer\t-\t-\nLib\tLib.D\tleaf\tlayer\t-\t-\n' >"$INV"
}
load_search_path() { return 0; }
replay_leaf() { echo "EXEC replay $1"; echo '1024 0.01' >"$WORK/time.$1"; }
'''
            if fail_leaf:
                stubs += 'replay_leaf() { echo "rejected $1"; return 1; }\n'
            if fail_build:
                stubs += 'step_build() { echo "EXEC failed-build"; return 1; }\n'
            if stale:
                stubs += 'lake() { return 1; }\n'
            if changed:
                # Isolate the result-file contract from graph selection (separate fixtures).
                stubs += 'compute_changes() { BUILD_TARGETS=(); DECL_LIBS=(); do_surface=0; do_protected=0; do_comparator_config=0; do_audit=0; do_audit_tests=0; do_audit_report=0; }\n'
            marker = "# --- driver "
            before, after = SOURCE.split(marker, 1)
            (scripts / "check.sh").write_text(before + stubs + "\n" + marker + after)
            env = {k: v for k, v in os.environ.items() if k != "CI"}
            env["RUN_DIR"] = tmp
            env["REPLAY_JOBS"] = "2"
            result_path = root / "result.json"
            inventory = root / "inventory"
            args = [str(inventory) if a == "INVENTORY" else a for a in args]
            result = subprocess.run(["bash", str(scripts / "check.sh"), *args,
                                     "--result-file", str(result_path)], env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            result.record = json.loads(result_path.read_text())
            result.inventories = {p.name: p.read_text().splitlines() for p in inventory.glob("*.txt")}
            self.assertEqual(result.record["exit_code"], result.returncode, result.stdout)
            return result

    def test_missing_sandbox_is_not_full_success(self):
        for part in ((), ("--split", "main"), ("--split", "lake-check")):
            with self.subTest(part=part):
                result = self.drive("--full", *part, bwrap=False)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("check.sh: PARTIAL", result.stdout)
                self.assertEqual(result.record["status"], "partial")
                self.assertTrue(any(s["reason"] == "skipped: no bwrap" for s in result.record["steps_skipped"]))
                self.assertNotIn("check.sh: ALL CHECKS PASSED", result.stdout)
                self.assertNotIn("check.sh: PART PASSED", result.stdout)

    def test_complete_and_intentionally_restricted_results(self):
        for args, verdict in ((["--full"], "ALL CHECKS PASSED"),
                              (["--fast"], "PASSED (fast mode"),
                              (["--full", "--split", "main"], "PART PASSED (split main"),
                              (["--full", "--split", "lake-check"], "PART PASSED (split lake-check")):
            with self.subTest(args=args):
                result = self.drive(*args)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertIn("check.sh: " + verdict, result.stdout)
                self.assertEqual(result.record["status"], "passed")
                self.assertEqual(result.record["mode"], args[0][2:])
                self.assertEqual(result.record["part"], args[-1] if "--split" in args else None)
                self.assertTrue(result.record["steps_run"])

    def test_failed_build_does_not_read_stale_outputs(self):
        result = self.drive("--full", fail_build=True)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("check.sh: FAILURES PRESENT", result.stdout)
        for step in ("decls", "audit", "surface", "protected", "replay", "review",
                     "comparator_config", "lake_check", "lake_comparator", "canary"):
            self.assertNotIn("EXEC step_" + step + "\n", result.stdout)
        self.assertIn("EXEC step_grep", result.stdout)
        self.assertEqual(result.record["status"], "failed")

    def test_producer_and_shared_selftest_ownership(self):
        result = self.drive("--full", "--split", "main", "--defer-replay")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertNotIn("EXEC step_replay\n", result.stdout)
        self.assertIn("EXEC selftest_replay", result.stdout)
        self.assertIn("EXEC -I scripts/test_const_diff.py", result.stdout)
        self.assertIn({"step": "5 kernel replay", "reason": "owned by replay shards"},
                      result.record["steps_skipped"])
        result = self.drive("--full", "--split", "lake-check", "--no-shared-selftests")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("EXEC selftest_pins", result.stdout)
        self.assertIn("EXEC step_lake_check", result.stdout)
        self.assertNotIn("EXEC -I scripts/test_const_diff.py", result.stdout)
        self.assertTrue(any(s["reason"] == "shared self-test owned by split main"
                            for s in result.record["steps_skipped"]))

    def test_replay_shards_cover_exactly_the_existing_leaves(self):
        expected = ["Lib.A", "Lib.B", "Lib.C", "Lib.D", "Lib.Z"]
        union = []
        for i in range(1, 5):
            result = self.drive("--replay-shard", f"{i}/4", "--replay-inventory", "INVENTORY", replay=True)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertEqual(result.inventories["expected.txt"], expected)
            self.assertEqual(result.inventories["replayed.txt"], expected[i-1::4])
            union += result.inventories["replayed.txt"]
            self.assertEqual(result.record["mode"], "replay-shard")
            self.assertEqual(result.record["part"], f"{i}/4")
            self.assertEqual(result.record["status"], "passed")
            self.assertEqual(len(result.record["steps_run"]), 3)
            self.assertEqual(result.record["steps_skipped"], [])
            self.assertTrue(result.record["inventories"]["replayed"].endswith("/replayed.txt"))
            self.assertNotIn("EXEC step_build", result.stdout)
        self.assertEqual(sorted(union), expected)  # also rejects overlaps
        failed = self.drive("--replay-shard", "1/4", "--replay-inventory", "INVENTORY",
                            replay=True, fail_leaf=True)
        self.assertEqual(failed.returncode, 1, failed.stdout)
        self.assertEqual(failed.record["status"], "failed")
        self.assertNotIn("replayed.txt", failed.inventories)
        stale = self.drive("--replay-shard", "1/4", "--replay-inventory", "INVENTORY", replay=True, stale=True)
        self.assertEqual(stale.returncode, 1, stale.stdout)
        self.assertEqual(stale.record["status"], "failed")
        self.assertNotIn("EXEC replay ", stale.stdout)
        self.assertNotIn("replayed.txt", stale.inventories)
        empty = self.drive("--replay-shard", "6/6", "--replay-inventory", "INVENTORY", replay=True)
        self.assertEqual(empty.returncode, 0, empty.stdout)
        self.assertEqual(empty.inventories["replayed.txt"], [])

    def test_changed_result_contract(self):
        result = self.drive("--changed", changed=True)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(result.record["mode"], "changed")
        self.assertEqual(result.record["status"], "passed")
        self.assertIn({"step": "1 build", "reason": "no Lean module changed"}, result.record["steps_skipped"])

    def test_invalid_modes_produce_failure_records(self):
        for args in (("--replay-shard", "0/4"), ("--defer-replay",),
                     ("--no-shared-selftests",), ("--unknown",)):
            result = self.drive(*args)
            self.assertEqual(result.returncode, 2, result.stdout)
            self.assertEqual(result.record["status"], "failed")
            self.assertEqual(result.record["steps_run"], [])


if __name__ == "__main__":
    unittest.main()
