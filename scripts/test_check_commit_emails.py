#!/usr/bin/env python3
"""Verdicts of scripts/check-commit-emails.py on throwaway repositories: accepted and rejected identities, the
range, and that a failure never prints the rejected address."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("check-commit-emails.py").resolve()
ALLOWLIST = Path(__file__).with_name("commit-emails.toml").resolve()
OK = "1+fixture@users.noreply.github.com"
BAD = "someone.private@example.invalid"


class CommitEmails(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="commit-emails-test-")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        self.git("init", "-q", "-b", "main")
        self.base = self.commit("base")

    def git(self, *args, **env):
        full = {**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1", **env}
        return subprocess.run(["git", "-c", "commit.gpgsign=false", *args], cwd=self.repo, env=full, check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, message, author=OK, committer=OK):
        self.git("commit", "-q", "--allow-empty", "-m", message, GIT_AUTHOR_NAME="A", GIT_AUTHOR_EMAIL=author,
                 GIT_COMMITTER_NAME="C", GIT_COMMITTER_EMAIL=committer)
        return self.git("rev-parse", "HEAD")

    def check(self, *args):
        proc = subprocess.run(["python3", "-I", str(SCRIPT), "--allowlist", str(ALLOWLIST), *args], cwd=self.repo,
                              capture_output=True, text=True, env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null"})
        self.assertNotIn(BAD.split("@")[0], proc.stdout + proc.stderr, "a rejected address was printed")
        return proc.returncode, proc.stdout

    def test_accepts_noreply_and_service_identities(self):
        self.commit("change\n\nCo-authored-by: Amp <amp@ampcode.com>\nCo-authored-by: Claude <noreply@anthropic.com>",
                    committer="noreply@github.com")
        self.commit("other", author="2+Other@Users.NoReply.GitHub.com")  # case-insensitive
        rc, out = self.check(self.base)
        self.assertEqual(rc, 0, out)
        self.assertIn("6 addresses in 2 commits, all on the allowlist: pass", out)

    def test_rejects_author_committer_and_coauthor_without_printing_them(self):
        for kwargs, field in (({"author": BAD}, "author"), ({"committer": BAD}, "committer"),
                              ({}, "Co-authored-by #2")):
            with self.subTest(field=field):
                base = self.git("rev-parse", "HEAD")
                message = "x\n\nCo-authored-by: Amp <amp@ampcode.com>"
                if not kwargs:
                    message += f"\nCo-authored-by: Someone <{BAD}>"
                sha = self.commit(message, **kwargs)
                rc, out = self.check(base)
                self.assertEqual(rc, 1, out)
                self.assertIn(f"FAIL[emails] {sha[:12]} {field}: address not on the allowlist", out)

    def test_rejects_a_coauthor_without_an_address_and_a_lookalike_domain(self):
        self.commit("x\n\nCo-authored-by: Nobody")
        rc, out = self.check(self.base)
        self.assertEqual((rc, "Co-authored-by #1" in out), (1, True), out)
        for lookalike in ("1+x@users.noreply.github.com.example.invalid", "x@notusers.noreply.github.com",
                          "amp@ampcode.com.example.invalid"):
            with self.subTest(lookalike=lookalike):
                base = self.git("rev-parse", "HEAD")
                self.commit("y", author=lookalike)
                rc, out = self.check(base)
                self.assertEqual(rc, 1, out)

    def test_range_excludes_the_base_and_no_base_checks_everything(self):
        bad = self.commit("old", author=BAD)
        rc, out = self.check(bad)  # nothing after the bad commit
        self.assertEqual(rc, 0, out)
        self.assertIn("in 0 commits", out)
        for base in ([], ["0" * 40], ["f" * 40]):  # no base, a first push, an unknown base: the whole history
            with self.subTest(base=base):
                rc, out = self.check(*base)
                self.assertEqual(rc, 1, out)
                self.assertIn(f"FAIL[emails] {bad[:12]} author", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
