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
              stale=False, changed=False, result_file=True, paths=None, graph=True, fail_lint=False):
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
            if fail_lint:
                stubs += 'step_syntax_lint() { echo "planted lint warning"; return 1; }\n'
            if stale:
                stubs += 'lake() { return 1; }\n'
            if changed:
                # Isolate the result-file contract from graph selection (separate fixtures).
                stubs += 'compute_changes() { BUILD_TARGETS=(); DECL_LIBS=(); do_surface=0; do_protected=0; do_comparator_config=0; do_audit=0; do_audit_tests=0; do_audit_report=0; }\n'
            if paths is not None:
                # Real Git discovery and cone selection; only graph extraction is replaced.
                stubs += '''
python3() {
  if [[ "$2" == scripts/check-boundaries.py ]]; then
    while (($#)); do
      case "$1" in
        --graph-out) cp scripts/graph.tsv "$2"; shift ;;
        --inventory-out) cp scripts/inventory.tsv "$2"; shift ;;
      esac
      shift
    done
  elif [[ "$2" == - ]]; then command python3 "$@"
  else echo "EXEC $*"
  fi
}
'''
                modules = [("ConsensusLean", "ConsensusLean.Spec.Probe", "-", "trusted", "protected"),
                           ("ConsensusLean", "ConsensusLean.Lemmas.Probe", "ConsensusLean.Spec.Probe", "-", "-"),
                           ("Solution", "Solution", "ConsensusLean.Lemmas.Probe", "-", "-"),
                           ("ConsensusLeanTest", "ConsensusLeanTest", "ConsensusLean.Spec.Probe", "-", "-")]
                modules = [row for row in modules if paths.get(row[1].replace(".", "/") + ".lean") != "deleted"]
                (scripts / "graph.tsv").write_text("".join(f"{lib}\t{m}\t{dep}\n" for lib, m, dep, _, _ in modules) if graph else "")
                (scripts / "inventory.tsv").write_text("".join(f"{lib}\t{m}\tleaf\tlayer\t{trust}\t{protected}\n"
                                                              for lib, m, _, trust, protected in modules))
                before, after = SOURCE.split("# --- driver ", 1)
                (scripts / "check.sh").write_text(before + stubs + "\n# --- driver " + after)
                def git(*cmd):
                    return subprocess.check_output(["git", *cmd], cwd=root, stderr=subprocess.DEVNULL, text=True).strip()
                git("init", "-q")
                git("config", "user.name", "Fixture")
                git("config", "user.email", "fixture@example.invalid")
                for path, action in paths.items():
                    if action != "untracked":
                        p = root / path
                        p.parent.mkdir(parents=True, exist_ok=True)
                        p.write_text("before\n")
                git("add", ".")
                git("commit", "-qm", "base")
                base = git("rev-parse", "HEAD")
                for path, action in paths.items():
                    p = root / path
                    if action == "deleted":
                        p.unlink()
                    else:
                        p.parent.mkdir(parents=True, exist_ok=True)
                        p.write_text("after\n")
                args = tuple(base if a == "BASE" else a for a in args)
            marker = "# --- driver "
            before, after = SOURCE.split(marker, 1)
            (scripts / "check.sh").write_text(before + stubs + "\n" + marker + after)
            env = {k: v for k, v in os.environ.items() if k != "CI"}
            env["RUN_DIR"] = tmp
            env["REPLAY_JOBS"] = "2"
            result_path = root / "result.json"
            inventory = root / "inventory"
            args = [str(inventory) if a == "INVENTORY" else a for a in args]
            result_args = ["--result-file", str(result_path)] if result_file else []
            result = subprocess.run(["bash", str(scripts / "check.sh"), *args, *result_args], env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            result.record = json.loads(result_path.read_text()) if result_file else None
            result.inventories = {p.name: p.read_text().splitlines() for p in inventory.glob("*.txt")}
            if result_file:
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
        for step in ("syntax_lint", "decls", "audit", "surface", "protected", "replay", "review",
                     "comparator_config", "lake_check", "lake_comparator", "canary"):
            self.assertNotIn("EXEC step_" + step + "\n", result.stdout)
        self.assertIn("EXEC step_grep", result.stdout)
        self.assertEqual(result.record["status"], "failed")

    def test_producer_and_shared_selftest_ownership(self):
        result = self.drive("--full", "--split", "main", "--defer-replay", "--defer-lint")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertNotIn("EXEC step_replay\n", result.stdout)
        self.assertIn("EXEC selftest_replay", result.stdout)
        self.assertIn("EXEC -I scripts/test_const_diff.py", result.stdout)
        self.assertIn({"step": "5 kernel replay", "reason": "owned by replay shards"},
                      result.record["steps_skipped"])
        self.assertIn({"step": "1b deferred syntax lint", "reason": "owned by lint job"},
                      result.record["steps_skipped"])
        self.assertNotIn("EXEC step_syntax_lint\n", result.stdout)
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
                     ("--defer-lint",), ("--no-shared-selftests",), ("--unknown",), ("--plan",)):
            result = self.drive(*args)
            self.assertEqual(result.returncode, 2, result.stdout)
            self.assertEqual(result.record["status"], "failed")
            self.assertEqual(result.record["steps_run"], [])

    def test_plan_refuses_replay_execution_mode(self):
        result = self.drive("--plan", "--replay-shard", "1/4", "--replay-inventory", "INVENTORY",
                            result_file=False)
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertNotIn("EXEC ", result.stdout)

    def test_plan_matches_execution_selection_without_running_checks(self):
        for args in (("--fast",), ("--full",), ("--full", "--split", "main", "--defer-replay", "--defer-lint"),
                     ("--full", "--split", "lake-check", "--no-shared-selftests"), ("--changed",)):
            with self.subTest(args=args):
                planned = self.drive(*args, "--plan", result_file=False, changed=True)
                executed = self.drive(*args, changed=True)
                self.assertEqual(planned.returncode, 0, planned.stdout)
                self.assertNotIn("EXEC ", planned.stdout)
                self.assertIn("check.sh: PLAN ONLY", planned.stdout)
                self.assertNotIn("check.sh: PASSED", planned.stdout)
                labels = [line[6:].split(" (selected by ")[0] for line in planned.stdout.splitlines()
                          if line.startswith("PLAN  ")]
                self.assertEqual(labels, executed.record["steps_run"])
                self.assertEqual([line for line in planned.stdout.splitlines() if line.startswith(("SKIP ", "DEFER "))],
                                 [line for line in executed.stdout.splitlines() if line.startswith(("SKIP ", "DEFER "))])

    def test_lint_failure_fails_ci_result(self):
        for args in (("--fast",), ("--changed",), ("--full",)):
            result = self.drive(*args, changed=True, fail_lint=True)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertEqual(result.record["status"], "failed")
            self.assertIn("FAIL  1b deferred syntax lint", result.stdout)

    def test_plan_uses_real_changed_selection_and_conservative_fallbacks(self):
        cases = [({"docs/probe.md": "modified"}, True, "changed", "no Lean module changed", "no library affected"),
                 ({"ConsensusLean/Spec/Probe.lean": "untracked"}, True, "changed", "downstream cone (built): 4 modules", "PLAN  4 Spec surface"),
                 ({"ConsensusLean/Spec/Probe.lean": "deleted"}, True, "changed", "check-decls: ConsensusLean", "PLAN  4 Spec surface"),
                 ({"ConsensusLean/Lemmas/Probe.lean": "modified"}, True, "changed", "downstream cone (built): 2 modules", "PLAN  3b axiom audit"),
                 ({"docs/probe.md": "modified"}, False, "fast", "no import graph", "PLAN  1 build"),
                 ({"scripts/probe.py": "untracked"}, True, "fast", "with the self-tests", "PLAN  0 pins self-test")]
        for paths, graph, mode, first, second in cases:
            with self.subTest(paths=paths, graph=graph):
                result = self.drive("--changed", "BASE", "--plan", paths=paths, graph=graph, result_file=False)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertIn(f"PLAN ONLY ({mode} mode", result.stdout)
                self.assertIn(first, result.stdout)
                self.assertIn(second, result.stdout)
                self.assertNotIn("EXEC ", result.stdout)


if __name__ == "__main__":
    unittest.main()
