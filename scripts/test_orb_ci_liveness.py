#!/usr/bin/env python3
"""Deterministic alert-contract fixtures; no services, credentials or notifications."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("liveness", Path(__file__).with_name("orb-ci-liveness.py"))
liveness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(liveness)
spec = importlib.util.spec_from_file_location("installer", Path(__file__).with_name("install-orb-ci-liveness.py"))
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)
A, B, C = (c * 40 for c in "abc")


def body(*rows):
    return "<!-- orb-ci results -->\n|---|---|---|---|---|\n" + "\n".join(rows) + "\n<!-- /orb-ci results -->"


def row(sha, ref="main", mode="--fast --selftests", result="PASSED in 12s"):
    return f"| 10-01 00:00 | {ref} | `{sha[:8]}` | {mode} | {result} |"


class Liveness(unittest.TestCase):
    def setUp(self):
        self.state = {}

    def tick(self, now, head=A, rows=(), status="active", fail=()):
        def read(*args):
            kind = "service" if "systemctl" in args[0] else "head" if args[-1].endswith("/main") else "issue"
            if kind in fail:
                raise subprocess.TimeoutExpired(args[0], 25)
            return status if kind == "service" else json.dumps({"object": {"sha": head}} if kind == "head" else {"body": body(*rows)})
        alerts = []
        liveness.check(self.state, now, alerts, read)
        return {a[0].split(":")[1] for a in alerts}

    def test_startup_grace_stale_result_and_published_failure(self):
        self.assertEqual(self.tick(100, rows=[row(B)]), set())
        self.assertEqual(self.tick(1899), set())
        self.assertEqual(self.tick(1900), {"missing-row"})
        self.assertEqual(self.tick(1901, rows=[row(A, "main (re-check)", "--changed deadbeef", "**FAILED** in 8s: check")]), set())
        # Aged/evicted row on unchanged main is still healthy.
        self.assertEqual(self.tick(100000), set())

    def test_reads_main_from_the_code_repo_and_rows_from_the_issues_repo(self):
        # Split repositories (scripts/repos.toml): main's head from `code`, the #63 rows from `issues`.
        calls = []
        def read(*args):
            calls.append(args)
            if "systemctl" in args[0]:
                return "active"
            return json.dumps({"object": {"sha": A}} if args[-1].endswith("/main") else {"body": body(row(A))})
        with patch.object(liveness, "CODE_SLUG", "fx/code"), patch.object(liveness, "ISSUES_SLUG", "fx/coord"):
            alerts = []
            liveness.check(self.state, 0, alerts, read)
        self.assertEqual(alerts, [])
        paths = [a[-1] for a in calls if "systemctl" not in a[0]]
        self.assertIn("repos/fx/code/git/ref/heads/main", paths)
        self.assertIn("repos/fx/coord/issues/63", paths)
        self.assertFalse([p for p in paths if "fx/code/issues" in p or "fx/coord/git" in p])

    def test_stopped_is_immediate_even_with_published_result(self):
        for status in ("inactive", "failed", "activating", ""):
            self.assertEqual(self.tick(10, rows=[row(A)], status=status), {"stopped"})
        self.assertEqual(self.tick(11, rows=[row(A)]), set())

    def test_pr_full_and_non_result_do_not_count(self):
        rows = [row(A, "PR #3"), row(A, "main (full, manual)", "--full"),
                row(A, result="running"), row(A, mode="--full")]
        self.tick(0, rows=rows)
        self.assertEqual(self.tick(1800, rows=rows), {"missing-row"})

    def test_churn_keeps_deadline_and_later_publication_covers_skips(self):
        self.tick(0)
        self.tick(1000, head=B)
        self.assertEqual(self.tick(1800, head=C), {"missing-row"})
        # B's publication covers A, but C retains its own observation time.
        self.assertEqual(self.tick(1801, head=C, rows=[row(B)]), set())
        self.assertEqual(self.tick(3600, head=C), {"missing-row"})
        self.assertEqual(self.tick(3601, head=C, rows=[row(C)]), set())

    def test_api_outage_no_fabricated_health_and_recovery(self):
        self.tick(0)
        self.assertEqual(self.tick(10, fail=("head", "issue")), set())
        self.assertEqual(self.tick(1810, fail=("head", "issue")), {"unavailable", "missing-row"})
        self.assertEqual(self.tick(1811, rows=[row(A)]), set())
        self.assertEqual(self.tick(9000, fail=("issue",)), set())

    def test_first_start_offline_and_service_query_failure(self):
        self.assertEqual(self.tick(0, fail=("head", "issue", "service")), set())
        self.assertEqual(self.tick(1800, fail=("head", "issue", "service")), {"unavailable"})
        self.assertEqual(self.tick(1801), set())
        self.assertEqual(self.tick(3601), {"missing-row"})

    def test_restart_preserves_deadline(self):
        self.tick(100)
        self.state = json.loads(json.dumps(self.state))
        self.assertEqual(self.tick(1900), {"missing-row"})

    def test_confirmed_head_does_not_hide_next_head(self):
        self.tick(0, rows=[row(A)])
        self.tick(50, head=B, rows=[row(A)])
        self.assertEqual(self.tick(1850, head=B, rows=[row(A)]), {"missing-row"})

    def test_malformed_issue_is_not_empty_success(self):
        for malformed in ("", "<!-- orb-ci results -->", "<!-- orb-ci results -->\n<!-- /orb-ci results -->"):
            with self.assertRaises((ValueError, IndexError)):
                liveness.published(malformed)

    def test_hook_idempotence_and_missing_helper_isolation(self):
        host = '''def existing(st, now, alerts):
    alerts.append(("original", "title", "message"))
CHECKS = [existing]


def main():
    alerts = []
    for check in CHECKS:
        try:
            check({}, 0, alerts)
        except Exception:
            alerts.append(("broken", "title", "message"))
    return alerts
'''
        updated = installer.hooked(host)
        self.assertEqual(installer.hooked(updated), updated)
        self.assertEqual(updated.replace(installer.HOOK, ""), host)
        namespace = {}
        exec(updated, namespace)
        with patch("runpy.run_path", side_effect=FileNotFoundError):
            self.assertEqual([a[0] for a in namespace["main"]()], ["original", "broken"])


if __name__ == "__main__":
    unittest.main()
