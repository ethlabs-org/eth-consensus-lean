#!/usr/bin/env python3
"""Report-only timing CLI fixtures; deterministic process costs, no Lean build needed."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True


def load(name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


timer = load("time-modules")
profiler = load("profile-module")


class BuildTimingTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        setup = self.root / ".lake/build/ir/ConsensusLean/Fixture.setup.json"
        setup.parent.mkdir(parents=True)
        setup.write_text("{}")

    def time(self, cpu=10, baseline=None, flags=(), status=0, modules=("ConsensusLean.Fixture",)):
        args = ["time-modules", "--repo", str(self.root), *flags, *modules]
        if baseline is not None:
            path = self.root / "base.tsv"
            path.write_text(baseline)
            args += ["--compare", str(path)]
        stdout, stderr = io.StringIO(), io.StringIO()
        usage = SimpleNamespace(ru_utime=cpu, ru_stime=0, ru_maxrss=2048)
        with patch.object(sys, "argv", args), contextlib.redirect_stdout(stdout), \
                contextlib.redirect_stderr(stderr), \
                patch.object(timer.subprocess, "check_output", return_value="/fixture"), \
                patch.object(timer.subprocess, "run", return_value=SimpleNamespace(stdout="abc123", returncode=0)), \
                patch.object(timer.subprocess, "Popen", return_value=SimpleNamespace(pid=123)), \
                patch.object(timer.os, "wait4", return_value=(123, status << 8, usage)):
            rc = timer.main()
        return rc, stdout.getvalue(), stderr.getvalue()

    def test_baseline_status_and_thresholds(self):
        rc, baseline, _ = self.time(cpu=8)
        self.assertEqual(rc, 0)
        header = json.loads(baseline.splitlines()[0][2:])
        self.assertTrue(header["cpu_model"])
        self.assertGreater(header["cpus"], 0)
        self.assertEqual(header["jobs"], 1)
        self.assertEqual(header["commit"], "abc123")
        # Exactly 25% is not a regression; above it is, once the absolute delta exceeds 1 s.
        self.assertEqual(self.time(cpu=10, baseline=baseline)[0], 0)
        rc, _, report = self.time(cpu=10.1, baseline=baseline)
        self.assertEqual(rc, 2)
        self.assertIn("SLOWER ConsensusLean.Fixture", report)
        _, small, _ = self.time(cpu=2)
        self.assertEqual(self.time(cpu=3, baseline=small)[0], 0)
        self.assertEqual(self.time(cpu=3.1, baseline=small)[0], 2)
        # A failed duplicate must not overwrite the valid baseline and invent a regression.
        mixed = baseline + "ConsensusLean.Fixture\t0\t0.01\t0\t1\n"
        self.assertEqual(self.time(cpu=8, baseline=mixed)[0], 0)
        failed = baseline.rsplit("\t0\n", 1)[0] + "\t1\n"
        rc, _, report = self.time(baseline=failed)
        self.assertEqual(rc, 1)
        self.assertIn("no matching exit-0 baseline rows", report)

    def test_provenance_refusal_and_explicit_override(self):
        _, baseline, _ = self.time()
        line, rows = baseline.split("\n", 1)
        header = json.loads(line[2:])
        for key, value in (("cpu_model", "different CPU"), ("cpus", header["cpus"] + 1),
                           ("jobs", 2)):
            with self.subTest(key=key):
                mismatch = "# " + json.dumps({**header, key: value}) + "\n" + rows
                self.assertEqual(self.time(baseline=mismatch)[0], 1)
                rc, _, report = self.time(baseline=mismatch, flags=("--same-machine",))
                self.assertEqual(rc, 0)
                self.assertIn("WARNING", report)
        self.assertEqual(self.time(baseline=rows)[0], 1)
        self.assertEqual(self.time(baseline=rows, flags=("--same-machine",))[0], 0)
        # Different revisions are the point of a comparison, not a machine mismatch.
        changed = "# " + json.dumps({**header, "commit": "other"}) + "\n" + rows
        self.assertEqual(self.time(baseline=changed)[0], 0)

    def test_incomplete_runs(self):
        for kwargs in ({"status": 7}, {"modules": ("ConsensusLean.Unbuilt",)}):
            with self.subTest(kwargs=kwargs):
                rc, _, report = self.time(**kwargs)
                self.assertEqual(rc, 1)
                self.assertIn("INCOMPLETE", report)
        (self.root / ".lake/build/ir/ConsensusLean/Fixture.setup.json").unlink()
        rc, _, report = self.time(modules=())
        self.assertEqual(rc, 1)
        self.assertIn("no module to time", report)

    def test_profile_does_not_summarise_stale_or_failed_output(self):
        out = self.root / "profile.json"
        for status, writes_profile, expected in ((7, True, 7), (0, False, 1), (0, True, 0)):
            with self.subTest(status=status, writes_profile=writes_profile):
                out.write_text('{"threads": []}')

                def run(_):
                    if writes_profile:
                        out.write_text('{"threads": []}')
                    return SimpleNamespace(returncode=status)

                stdout, stderr = io.StringIO(), io.StringIO()
                with patch.object(sys, "argv", ["profile-module", "Fixture.lean", "-o", str(out)]), \
                        patch.object(profiler.subprocess, "run", side_effect=run), \
                        contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    self.assertEqual(profiler.main(), expected)
                self.assertEqual("Slowest declarations" in stdout.getvalue(), expected == 0)


if __name__ == "__main__":
    unittest.main()
