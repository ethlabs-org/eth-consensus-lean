#!/usr/bin/env python3
"""Black-box orb-ci fixtures: local Git, stub GitHub/checks, no Lean or network.

Run with python3 scripts/test_orb_ci.py. Each test owns and removes its temporary
remote, worktrees, CI state, logs and subprocess TMPDIR. Only the external check
and review-boundary scripts and gh are replaced; orb-ci itself is executed as-is.
Verdicts are read from the issue #63 body, not inferred from the watcher's exit.
"""
import json
import shutil
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("orb-ci.sh").resolve()
ISSUE = """Fixture results
| time | ref | commit | mode | result |
|---|---|---|---|---|
<!-- /orb-ci results -->
"""
GH = r'''#!/usr/bin/env python3
import json, os, pathlib, sys
a = sys.argv[1:]
root = pathlib.Path(os.environ["FIXTURE_ROOT"])
with (root / "gh.jsonl").open("a") as f:
    f.write(json.dumps(a) + "\n")
if a[:2] == ["repo", "view"]:
    print("fixture/consensus-lean")
elif a[:2] == ["pr", "list"]:
    pass
elif a[:2] == ["issue", "view"] and a[2] == "63":
    print((root / "issue").read_text(), end="")
elif a[:2] == ["issue", "edit"] and a[2] == "63":
    (root / "issue").write_text(a[a.index("--body") + 1])
elif a[:2] in (["issue", "comment"], ["pr", "comment"]):
    pass
else:
    raise SystemExit("unexpected gh call: " + repr(a))
'''
CHECK = r'''#!/usr/bin/env python3
import json, os, pathlib, subprocess, sys
root = pathlib.Path(os.environ["FIXTURE_ROOT"])
config = json.loads((root / "config").read_text())
mode = sys.argv[1].removeprefix("--")
entry = {"kind": "check", "args": sys.argv[1:],
         "sha": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
         "sentinel": pathlib.Path(".lake/build/sentinel").exists(),
         "cache": os.environ.get("LAKE_ARTIFACT_CACHE"),
         "restore": os.environ.get("LAKE_RESTORE_ARTIFACTS")}
with (root / "calls.jsonl").open("a") as f:
    f.write(json.dumps(entry) + "\n")
output = config.get("output")
if output is None:
    output = ("check.sh: ALL CHECKS PASSED" if mode == "full" else
              "check.sh: PASSED (" + mode + " mode; fixture)")
if config.get("inventory"):
    work = pathlib.Path(os.environ["RUN_DIR"]) / "check.fixture"
    work.mkdir()
    (work / "sorry-inventory.json").write_text(json.dumps({
        "schema_version": 1, "mode": "report-only", "status": "incomplete",
        "issues": ["fixture open debt"], "roots": [], "sorries": []}))
print(output)
raise SystemExit(config.get("exit", 0))
'''
REVIEW = r'''#!/usr/bin/env python3
import json, os, pathlib, sys
root = pathlib.Path(os.environ["FIXTURE_ROOT"])
with (root / "calls.jsonl").open("a") as f:
    f.write(json.dumps({"kind": "review", "args": sys.argv[1:]}) + "\n")
if "--self-test" in sys.argv and json.loads((root / "config").read_text()).get("review_fail"):
    print("FAIL review-boundary self-test fixture")
    raise SystemExit(1)
print("review-boundary fixture passed")
'''


class OrbCI(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="orb-ci-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.remote = self.root / "remote.git"
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.write(self.bin / "gh", GH, executable=True)
        (self.root / "issue").write_text(ISSUE)
        self.configure()
        self.git("init", "--bare", str(self.remote), cwd=self.root)
        self.git("init", "-b", "main", str(self.repo), cwd=self.root)
        for key, value in (("user.name", "Fixture"), ("user.email", "fixture@example.invalid"),
                           ("commit.gpgsign", "false"), ("tag.gpgsign", "false"),
                           ("core.hooksPath", "/dev/null")):
            self.git("config", key, value)
        self.write(self.repo / ".gitignore", ".lake/\n")
        self.write(self.repo / "lakefile.toml", 'name = "fixture"\n')
        self.write(self.repo / "scripts/boundaries.toml",
                   '[checks]\ntrusted_paths = ["Trusted.lean"]\n')
        self.write(self.repo / "Trusted.lean", "-- trusted fixture\n")
        self.write(self.repo / "scripts/check.sh", CHECK, executable=True)
        self.write(self.repo / "scripts/review-boundary.sh", REVIEW, executable=True)
        self.base = self.commit("base")
        self.git("remote", "add", "origin", str(self.remote))
        self.git("push", "-u", "origin", "main")
        (self.repo / ".lake/packages").mkdir(parents=True)
        self.write(self.repo / ".lake/build/sentinel", "must disappear for full\n")
        self.home = self.root / "ci"
        self.home.mkdir()
        self.env = {**os.environ, "PATH": f"{self.bin}:{os.environ['PATH']}",
                    "HOME": str(self.root), "TMPDIR": str(self.root),
                    "FIXTURE_ROOT": str(self.root), "ORB_CI_REPO": str(self.repo),
                    "ORB_CI_HOME": str(self.home), "ORB_CI_ISSUE": "63",
                    "ORB_CI_JOB": "", "ORB_CI_FULL_ENV": "", "ORB_CI_COPY": "", "ORB_CI_SANDBOX": "0",
                    "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true",
                    "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"}

    @staticmethod
    def write(path, body, executable=False):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body)
        if executable:
            path.chmod(0o755)

    def git(self, *args, cwd=None):
        proc = subprocess.run(["git", *args], cwd=cwd or self.repo, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              env={**os.environ, "GIT_CONFIG_NOSYSTEM": "1",
                                   "GIT_CONFIG_GLOBAL": "/dev/null"}, timeout=20)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return proc.stdout.strip()

    def commit(self, message):
        self.git("add", ".")
        self.git("commit", "-m", message)
        return self.git("rev-parse", "HEAD")

    def change(self, path="Code.lean"):
        self.write(self.repo / path, f"fixture change {path}\n")
        sha = self.commit(path)
        self.git("push", "origin", "main")
        return sha

    def configure(self, **values):
        (self.root / "config").write_text(json.dumps(values))

    def invoke(self, *args):
        proc = subprocess.run(["bash", str(SCRIPT), *args], cwd=self.repo,
                              env=self.env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=30)
        self.assertEqual(proc.returncode, 0, proc.stdout)
        return proc.stdout

    def calls(self, kind="check"):
        path = self.root / "calls.jsonl"
        calls = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
        return [call for call in calls if call["kind"] == kind]

    def rows(self):
        return [line for line in (self.root / "issue").read_text().splitlines()
                if line.startswith("| ") and "`" in line]

    def verdict(self, sha, passed, mode):
        rows = self.rows()
        self.assertTrue(rows, "no recorded #63 row")
        row = rows[0]
        self.assertIn(f"`{sha[:8]}`", row)
        self.assertIn(f"| --{mode}", row)
        self.assertIn("PASSED" if passed else "**FAILED**", row)
        calls = self.calls()
        self.assertTrue(calls, "check stub was not run")
        self.assertEqual(calls[-1]["args"][0], f"--{mode}")
        self.assertEqual(calls[-1]["sha"], sha)

    def fresh_ci(self):
        # Separate watcher state per subcase; the remote and source stay identical.
        self.home = self.root / f"ci-{len(list(self.root.glob('ci-*')))}"
        self.home.mkdir()
        self.env["ORB_CI_HOME"] = str(self.home)
        (self.root / "issue").write_text(ISSUE)
        (self.root / "calls.jsonl").write_text("")

    def test_fast_and_changed_require_matching_summary(self):
        for path, mode in (("Code.lean", "fast"), ("docs/guide.md", "changed")):
            sha = self.change(path)
            other = "changed" if mode == "fast" else "fast"
            for output, passed in ((None, True), ("", False), ("ALL CHECKS PASSED", False),
                                   (f"check.sh: PASSED ({other} mode; fixture)", False),
                                   (f"prefix check.sh: PASSED ({mode} mode; fixture)", False),
                                   (f"check.sh: PASSED ({mode} model; fixture)", False)):
                with self.subTest(mode=mode, output=output):
                    self.fresh_ci()
                    self.configure(output=output)
                    self.invoke("--once")
                    self.verdict(sha, passed, mode)

    def test_nonzero_check_fails_despite_summary(self):
        sha = self.change()
        self.configure(exit=1)
        self.invoke("--once")
        self.verdict(sha, False, "fast")

    def test_inventory_capture_and_retry_do_not_change_verdict(self):
        sha = self.change()
        self.configure(inventory=True)
        self.invoke("--once")  # gh API stub refuses publishing; captured report must survive.
        self.verdict(sha, True, "fast")
        outbox = self.home / f"inventory-outbox/{sha}.json"
        first = json.loads(outbox.read_text())
        self.assertEqual(first["report"]["commit"], sha)
        self.assertEqual(first["report"]["inventory"]["issues"], ["fixture open debt"])
        self.assertIn("inventory upload pending", self.invoke("--once"))
        self.assertEqual(len(self.calls()), 1, "publication retry reran checks")
        self.assertEqual(json.loads(outbox.read_text()), first)
        sha2 = self.change("Other.lean")
        self.configure(exit=1)
        self.invoke("--once")
        self.verdict(sha2, False, "fast")
        second = json.loads((self.home / f"inventory-outbox/{sha2}.json").read_text())
        self.assertEqual(second["report"]["availability"], "unavailable")
        self.assertIsNone(second["report"]["inventory"], "old job report leaked into failed build")

    def test_cached_pair_refresh_preserves_pair_on_invalid_update(self):
        self.write(self.repo / "scripts/orb-ci.sh", "#!/bin/bash\necho fixture\n")
        self.write(self.repo / "scripts/publish-inventory.py", "print('fixture')\n")
        self.write(self.repo / "scripts/ci-sandbox.sh", "#!/bin/bash\necho sandbox\n")
        self.commit("valid pair")
        self.git("push", "origin", "main")
        refresh = SCRIPT.with_name("orb-ci-refresh.sh")
        def invoke():
            return subprocess.run(["bash", str(refresh)], env=self.env, cwd=self.repo,
                                  capture_output=True, text=True, timeout=20)
        self.assertEqual(invoke().returncode, 0)
        cached = ("orb-ci.sh", "publish-inventory.py", "ci-sandbox.sh")
        before = [(self.home / f).read_bytes() for f in cached]
        self.write(self.repo / "scripts/orb-ci.sh", "#!/bin/bash\necho changed\n")
        self.write(self.repo / "scripts/publish-inventory.py", "invalid python (\n")
        self.commit("invalid pair")
        self.git("push", "origin", "main")
        self.assertNotEqual(invoke().returncode, 0)
        self.assertEqual([(self.home / f).read_bytes() for f in cached], before)
        self.assertFalse([p for p in self.home.glob("refresh.*") if p.is_dir()])

    @unittest.skipUnless(shutil.which("bwrap"), "needs bwrap")
    def test_head_code_runs_sandboxed(self):
        # The head's check.sh and review boundary see no watcher state, issue, credentials or network, and cannot
        # write the shared packages; the row passes only if every probe held.
        probe = f'''#!/bin/bash
leak=""
cat "{self.root}/issue" 2>/dev/null && leak+=" issue"
cat "{self.home}/done" 2>/dev/null && leak+=" watcher-state"
[[ -n "${{GH_TOKEN:-}}${{FIXTURE_ROOT:-}}" ]] && leak+=" env"
echo bad 2>/dev/null >.lake/packages/dep.olean && leak+=" packages"
python3 -c 'import socket; socket.create_connection(("1.1.1.1", 53), 3)' 2>/dev/null && leak+=" network"
[[ -z "$leak" ]] || {{ echo "FAIL  1 leak:$leak"; exit 1; }}
echo "sandboxed probes held"
[[ "${{1:-}}" == --self-test || "$0" == *review-boundary.sh ]] || echo "check.sh: PASSED (${{1#--}} mode; fixture)"
'''
        self.write(self.repo / "scripts/check.sh", probe, executable=True)
        self.write(self.repo / "scripts/review-boundary.sh", probe, executable=True)
        self.write(self.repo / ".lake/packages/dep.olean", "shared\n")
        sha = self.change()
        self.git("push", "origin", "main")
        self.env["ORB_CI_SANDBOX"] = "1"
        self.env["GH_TOKEN"] = "fixture-secret"
        out = self.invoke("--once")
        rows = self.rows()
        self.assertTrue(rows and f"`{sha[:8]}`" in rows[0] and "PASSED" in rows[0], (rows, out))
        logs = "".join(p.read_text() for p in (self.home / "logs").glob(f"{sha}.*"))
        self.assertEqual(logs.count("sandboxed probes held"), 3, logs)
        self.assertEqual((self.repo / ".lake/packages/dep.olean").read_text(), "shared\n")

    def test_review_boundary_self_test_failure_fails_docs(self):
        sha = self.change("docs/guide.md")
        self.configure(review_fail=True)
        self.invoke("--once")
        self.verdict(sha, False, "changed")
        self.assertTrue(any("--self-test" in call["args"] for call in self.calls("review")),
                        "review-boundary --self-test never ran for docs")

    def test_docs_only_classification(self):
        for path, mode in (("docs/Example.lean", "fast"), ("scripts/guide.md", "fast"),
                           (".github/guide.md", "fast"), ("docs/guide.md", "changed"),
                           ("GUIDE.md", "changed")):
            with self.subTest(path=path):
                sha = self.change(path)
                self.fresh_ci()
                self.invoke("--once")
                self.verdict(sha, True, mode)

    def test_full_is_cold_and_disables_cache(self):
        self.invoke("--full", "sha", self.base, "fixture cold")
        self.verdict(self.base, True, "full")
        call = self.calls()[-1]
        self.assertFalse(call["sentinel"], ".lake/build was reused in full run")
        self.assertEqual(call["cache"], "false", "artifact cache not disabled")
        self.assertEqual(call["restore"], "false", "artifact restore not disabled")

    def test_nightly_ignores_warm_ledger_then_deduplicates_cold(self):
        (self.home / "done-full").write_text(f"{self.base} nightly 0 1\n")
        self.invoke("--full", "nightly")
        self.verdict(self.base, True, "full")
        self.assertEqual(len(self.calls()), 1, "warm historical pass skipped cold nightly")
        self.assertFalse(self.calls()[0]["sentinel"])
        self.assertEqual(self.calls()[0]["cache"], "false")
        self.assertEqual(self.calls()[0]["restore"], "false")
        cold = self.lines("done-full-cold")
        self.assertEqual(len(cold), 1, cold)
        self.assertEqual(cold[0].split()[:3], [self.base, "nightly", "0"])
        before = (self.rows(), self.calls(), cold)
        self.invoke("--full", "nightly")
        self.assertEqual((self.rows(), self.calls(), self.lines("done-full-cold")), before)

    def test_full_requires_summary_and_rejects_skips(self):
        for output, passed in (("check.sh: ALL CHECKS PASSED", True), ("", False),
                               ("check.sh: PASSED (full mode; fixture)", False),
                               ("check.sh: ALL CHECKS PASSED\nSKIP 10 fixture", False),
                               ("check.sh: ALL CHECKS PASSED\nskipped: no bwrap", False)):
            with self.subTest(output=output):
                self.fresh_ci()
                self.configure(output=output)
                self.invoke("--full", "sha", self.base, "fixture summary")
                self.verdict(self.base, passed, "full")

    def tag(self, name, sha, annotated=False):
        args = ["tag", "-f"]
        if annotated:
            args += ["-a", "-m", "fixture annotated tag"]
        self.git(*args, name, sha)
        self.git("push", "--force", "origin", f"refs/tags/{name}")

    def lines(self, name):
        path = self.home / name
        return path.read_text().splitlines() if path.exists() else []

    def test_release_poll_and_exact_off_main_commits(self):
        # An off-main commit is checked itself, not replaced by main. Two refs on
        # one commit must each get a row.
        self.git("checkout", "-b", "side")
        self.write(self.repo / "side.txt", "off main\n")
        side = self.commit("off main")
        self.git("checkout", "main")
        pairs = {(f"refs/tags/{name}", sha) for name, sha, annotated in (
            ("milestone-light", side, False), ("milestone-annotated", self.base, True),
            ("release-light", self.base, False), ("release-annotated", side, True))}
        for ref, sha in sorted(pairs):
            self.tag(ref.removeprefix("refs/tags/"), sha, "annotated" in ref)
        self.tag("unrelated", self.base, True)
        self.invoke("--full", "poll")
        self.invoke("--full", "poll")
        seen = [line.split() for line in self.lines("release-tags-seen")]
        self.assertEqual({tuple(line[:2]) for line in seen}, pairs)
        self.assertEqual(len(seen), len(pairs), "poll duplicated unchanged refs")
        self.assertTrue(all(len(line) == 3 and line[2].isdigit() for line in seen), seen)
        self.assertFalse(self.calls(), "poll ran checks")
        self.invoke("--full", "tag")
        self.assertEqual({tuple(line.split()) for line in self.lines("full-release-tags")}, pairs)
        rows = self.rows()
        self.assertEqual(len(rows), len(pairs), rows)
        for ref, sha in pairs:
            matching = [row for row in rows if ref.removeprefix("refs/tags/") in row]
            self.assertEqual(len(matching), 1, rows)
            self.assertIn(f"`{sha[:8]}`", matching[0])
            self.assertIn("PASSED", matching[0])
        self.assertIn(side, {call["sha"] for call in self.calls()})
        before = (list(rows), list(self.calls()), self.lines("full-release-tags"))
        self.invoke("--full", "tag")
        self.assertEqual((self.rows(), self.calls(), self.lines("full-release-tags")), before)
        # Same ref at a different commit is new work, not ref-only deduplication.
        self.tag("release-annotated", self.base, True)
        self.invoke("--full", "poll")
        self.invoke("--full", "tag")
        pairs.add(("refs/tags/release-annotated", self.base))
        self.assertEqual({tuple(line.split()) for line in self.lines("full-release-tags")}, pairs)
        self.assertEqual(len(self.rows()), len(pairs))
        self.assertIn("release-annotated", self.rows()[0])
        self.assertIn(f"`{self.base[:8]}`", self.rows()[0])

    def test_unavailable_release_does_not_block_later_release(self):
        missing = "0123456789abcdef0123456789abcdef01234567"
        self.tag("release-valid", self.base)
        self.tag("spec-approved", self.base, annotated=True)
        self.invoke("--full", "poll")
        queue = self.home / "release-tags-seen"
        queue.write_text(f"refs/tags/release-missing {missing} 1\n" + queue.read_text())
        self.invoke("--full", "tag")
        self.assertEqual(self.lines("full-release-tags"),
                         [f"refs/tags/release-valid {self.base}"])
        self.assertIn(f"refs/tags/release-missing {missing} 1", self.lines("release-tags-seen"))
        rows = self.rows()
        self.assertEqual(len(rows), 1, rows)
        self.assertTrue(any("release-valid" in row for row in rows), rows)
        self.assertTrue(all("PASSED" in row for row in rows), rows)
        self.assertEqual([call["sha"] for call in self.calls()], [self.base])
        # Repeated failure to fetch must remain pending, without duplicate rows.
        before = (self.rows(), self.calls())
        self.invoke("--full", "tag")
        self.assertEqual((self.rows(), self.calls()), before)
        self.assertNotIn(f"refs/tags/release-missing {missing}", self.lines("full-release-tags"))

    def test_noncommit_release_tags_record_explicit_failure(self):
        targets = {"release-tree": self.git("rev-parse", "HEAD^{tree}"),
                   "milestone-blob": self.git("rev-parse", "HEAD:Trusted.lean")}
        for name, target in targets.items():
            self.tag(name, target, annotated=name == "release-tree")
        self.invoke("--full", "poll")
        self.invoke("--full", "tag")
        rows = self.rows()
        self.assertEqual(len(rows), len(targets), rows)
        for name, target in targets.items():
            matching = [row for row in rows if name in row]
            self.assertEqual(len(matching), 1, rows)
            self.assertIn(f"`{target[:8]}`", matching[0])
            self.assertIn("**FAILED**", matching[0])
            self.assertIn("not target a commit", matching[0])
        self.assertFalse(self.calls(), "noncommit tag ran check.sh")
        self.assertEqual(set(self.lines("full-release-tags")),
                         {f"refs/tags/{name} {target}" for name, target in targets.items()})
        self.invoke("--full", "tag")
        self.assertEqual(self.rows(), rows, "noncommit failure recorded twice")

    def test_release_checkout_failure_stays_unhandled_until_retry(self):
        self.tag("release-locked", self.base)
        self.invoke("--full", "poll")
        wt = self.home / "wt-full"
        self.git("worktree", "add", "--detach", str(wt), "origin/main")
        index = Path(self.git("rev-parse", "--path-format=absolute", "--git-path", "index", cwd=wt))
        lock = Path(str(index) + ".lock")
        lock.write_text("fixture checkout failure\n")
        self.invoke("--full", "tag")
        self.assertFalse(self.lines("full-release-tags"), "failed checkout marked tag handled")
        self.assertFalse(self.lines("done-full-cold"), "failed checkout recorded a completed check")
        self.assertFalse(self.calls(), "check.sh ran despite checkout failure")
        self.assertFalse(self.rows(), "failed checkout fabricated a check verdict")
        lock.unlink()
        self.invoke("--full", "tag")
        self.verdict(self.base, True, "full")
        self.assertEqual(self.lines("full-release-tags"),
                         [f"refs/tags/release-locked {self.base}"])
        self.assertEqual(len(self.calls()), 1)

    def test_retired_spec_approved_tag_runs_nothing(self):
        # The spec-approved tag is retired (2026-11-01): moving it queues and runs nothing.
        self.tag("spec-approved", self.base, annotated=True)
        self.invoke("--full", "poll")
        self.invoke("--full", "tag")
        self.assertFalse(self.lines("tags-seen"))
        self.assertFalse(self.lines("release-tags-seen"))
        self.assertFalse(self.calls(), "the retired tag ran a check")
        self.assertFalse(self.rows(), "the retired tag recorded a row")


if __name__ == "__main__":
    unittest.main(verbosity=2)
