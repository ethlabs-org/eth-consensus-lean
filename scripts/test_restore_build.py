#!/usr/bin/env python3
"""Exercise optional build restoration without network access or a Lean build."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parent


class RestoreTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="restore-build-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "scripts").mkdir()
        shutil.copy2(SCRIPTS / "restore-build.sh", self.root / "scripts")
        shutil.copy2(SCRIPTS / "repos.toml", self.root / "scripts")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        # A deliberately closed PATH makes missing-tool tests independent of the host.
        for tool in ("bash", "dirname", "python3", "grep", "mkdir", "mktemp", "rm", "mv", "tar", "cat"):
            (self.bin / tool).symlink_to(shutil.which(tool))
        self.env = {**os.environ, "PATH": str(self.bin), "CALLS": str(self.root / "calls")}
        self.stub("git", 'if [ "$1" = rev-parse ]; then echo fixture-head; else exit 1; fi')
        self.stub("gh", '''echo "gh $*" >>"$CALLS"
case "$*" in
  'auth status') exit 0 ;;
  *'/compare/'*) echo ahead ;;
  *'/artifacts'*) [ "${ARTIFACT:-0}" = 1 ] && echo lake-build; exit 0 ;;
  *'workflows/ci.yml/runs?'*) echo '42 fixture-base' ;;
  'run download '*)
    [ "${DOWNLOAD_FAIL:-0}" = 0 ] || exit 1
    while [ "$1" != -D ]; do shift; done
    shift; mkdir -p "$1/build"; echo restored >"$1/build/marker"
    tar -C "$1" -cf "$1/lake-build.tar.zst" build
    rm -rf "$1/build" ;;
esac''')
        self.stub("zstd", '[ "${UNPACK_FAIL:-0}" = 0 ] || exit 1; cat "$2"')
        self.stub("lake", 'echo "lake $*" >>"$CALLS"; exit 0')

    def stub(self, name, body):
        p = self.bin / name
        p.write_text("#!/bin/sh\n" + body + "\n")
        p.chmod(0o755)

    def run_restore(self, **env):
        return subprocess.run([str(self.bin / "bash"), "scripts/restore-build.sh", "--force"],
                              cwd=self.root, env={**self.env, **env}, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def setup_tail(self, **env):
        # Retain setup's real optional wrapper and restore/build sequence; omit installers.
        setup = SCRIPTS.parent.joinpath(".agents/setup").read_text()
        optional = next(line for line in setup.splitlines() if line.startswith("optional()"))
        tail = setup[setup.index('step "Project build from CI (optional)"'):]
        program = "set -euo pipefail\nstep() { :; }; timed() { \"$@\"; }\n" + optional + "\n" + tail
        self.stub("install_lakeprof", "exit 0")
        return subprocess.run([str(self.bin / "bash"), "-c", program], cwd=self.root,
                              env={**self.env, **env}, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def test_missing_tools_fail_clearly(self):
        for tool in ("gh", "zstd"):
            with self.subTest(tool=tool):
                p = self.bin / tool
                saved = p.read_text()
                p.unlink()
                result = self.run_restore()
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(f"required tool {tool} not installed", result.stdout)
                self.stub(tool, saved.split("\n", 1)[1])

    def test_missing_artifact_falls_back_to_build(self):
        result = self.setup_tail()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("no lake-build artifact", result.stdout)
        calls = (self.root / "calls").read_text()
        self.assertIn("--paginate", calls)
        self.assertIn("per_page=100", calls)
        self.assertIn("lake build\n", calls)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_setup_continues_after_restore_failure(self):
        (self.bin / "gh").unlink()
        result = self.setup_tail()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("required tool gh not installed", result.stdout)
        self.assertIn("setup continues without it", result.stdout)
        self.assertIn("lake build\n", (self.root / "calls").read_text())

    def test_failed_restore_preserves_previous_build_and_control_replaces_it(self):
        build = self.root / ".lake/build"
        build.mkdir(parents=True)
        (build / "marker").write_text("previous\n")
        for failure in ("DOWNLOAD_FAIL", "UNPACK_FAIL"):
            result = self.run_restore(ARTIFACT="1", **{failure: "1"})
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual((build / "marker").read_text(), "previous\n")
            self.assertEqual(list(build.parent.glob("restore-build.*")), [])
        result = self.run_restore(ARTIFACT="1")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual((build / "marker").read_text(), "restored\n")
        self.assertEqual(list(build.parent.glob("restore-build.*")), [])


if __name__ == "__main__":
    unittest.main()
