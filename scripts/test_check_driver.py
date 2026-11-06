#!/usr/bin/env python3
"""Run the actual shell driver with cheap step bodies, not the Lean checks themselves."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).with_name("check.sh").read_text()
CONFIG = Path(__file__).with_name("boundaries.toml").read_text()


class DriverTests(unittest.TestCase):
    def drive(self, *args, bwrap=True, fail_build=False):
        with tempfile.TemporaryDirectory(prefix="check-driver-") as tmp:
            root = Path(tmp)
            scripts = root / "scripts"
            scripts.mkdir()
            (scripts / "boundaries.toml").write_text(CONFIG)
            (scripts / "test_check_decls_waivers.sh").write_text("exit 0\n")
            # Keep parsing, configuration, selection, failure handling and summaries verbatim.
            # Only expensive step implementations and external self-test programs are replaced.
            stubs = "\n".join(f'{name}() {{ echo "EXEC {name}"; }}' for name in
                              re.findall(r"^((?:step_|selftest_)\w+)\(\)", SOURCE, re.M))
            stubs += f'\nhave_bwrap() {{ return {0 if bwrap else 1}; }}\n'
            stubs += '''
python3() { echo "EXEC $*"; }
step_boundaries() { printf 'Lib\tLib\tleaf\tlayer\t-\t-\n' >"$INV"; }
'''
            if fail_build:
                stubs += 'step_build() { echo "EXEC failed-build"; return 1; }\n'
            marker = "# --- driver "
            before, after = SOURCE.split(marker, 1)
            (scripts / "check.sh").write_text(before + stubs + "\n" + marker + after)
            env = {k: v for k, v in os.environ.items() if k != "CI"}
            env["RUN_DIR"] = tmp
            return subprocess.run(["bash", str(scripts / "check.sh"), *args], env=env,
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def test_missing_sandbox_is_not_full_success(self):
        for part in ((), ("--split", "main"), ("--split", "lake-check")):
            with self.subTest(part=part):
                result = self.drive("--full", *part, bwrap=False)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("check.sh: PARTIAL", result.stdout)
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

    def test_failed_build_does_not_read_stale_outputs(self):
        result = self.drive("--full", fail_build=True)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("check.sh: FAILURES PRESENT", result.stdout)
        for step in ("decls", "audit", "surface", "protected", "replay", "review",
                     "comparator_config", "lake_check", "lake_comparator", "canary"):
            self.assertNotIn("EXEC step_" + step + "\n", result.stdout)
        self.assertIn("EXEC step_grep", result.stdout)


if __name__ == "__main__":
    unittest.main()
