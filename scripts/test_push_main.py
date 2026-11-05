#!/usr/bin/env python3
"""Exercise cancellation and normal landing against disposable local Git remotes."""
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time


SCRIPT = Path(__file__).with_name("push-main.sh").resolve()


def run(*args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.DEVNULL).strip()


REPOS = 'code = "fixture/code"\n'
# The email allowlist check (its verdicts: test_check_commit_emails.py); EMAILS_FAIL=1 makes it reject.
EMAILS = "import os, sys\nprint('emails fixture')\nsys.exit(int(os.environ.get('EMAILS_FAIL', '0')))\n"
GH = """#!/bin/sh
printf '%s\\n' "$*" >>"$GH_LOG"
"""


def landing_repo(root, repos=REPOS, trusted=False):
    """A repository with a passing check stub and one change to land; a stub gh logs its calls."""
    remote, repo = root / "remote.git", root / "repo"
    run("git", "init", "--bare", str(remote), cwd=root)
    run("git", "init", "-b", "main", str(repo), cwd=root)
    for key, value in (("user.name", "Test"), ("user.email", "test@example.invalid"),
                       ("commit.gpgsign", "false"), ("core.hooksPath", "/dev/null")):
        run("git", "config", key, value, cwd=repo)
    scripts = repo / "scripts"
    scripts.mkdir()
    (scripts / "check.sh").write_text("#!/bin/sh\necho 'check.sh: PASSED (fixture)'\n")
    (scripts / "review-boundary.sh").write_text("#!/bin/sh\nexit 0\n")
    (scripts / "repos.toml").write_text(repos)
    (scripts / "check-commit-emails.py").write_text(EMAILS)
    (scripts / "boundaries.toml").write_text('[checks]\ntrusted_paths = ["Trusted.lean"]\n')
    for script in scripts.glob("*.sh"):
        script.chmod(0o755)
    (repo / "Trusted.lean").write_text("-- trusted\n")
    run("git", "add", ".", cwd=repo)
    run("git", "commit", "-m", "base", cwd=repo)
    run("git", "remote", "add", "origin", str(remote), cwd=repo)
    run("git", "push", "-u", "origin", "main", cwd=repo)
    (repo / ("Trusted.lean" if trusted else "change")).write_text("land me\n")
    run("git", "add", ".", cwd=repo)
    run("git", "commit", "-m", "change\n\nTrusted-surface: fixture", cwd=repo)
    bin_dir = root / "bin"
    bin_dir.mkdir()
    (bin_dir / "gh").write_text(GH)
    (bin_dir / "gh").chmod(0o755)
    env = {**os.environ, "RUN_DIR": str(root), "GH_LOG": str(root / "gh.log"),
           "PATH": f"{bin_dir}:{os.environ['PATH']}"}
    return remote, repo, env


def land(repo, env):
    proc = subprocess.run(["bash", str(SCRIPT)], cwd=repo, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    return proc.returncode, proc.stdout


def check_trusted_landing_posts_nothing():
    # A landing that touches the trusted surface lands like any other and calls no GitHub API: its record is the
    # commits' Trusted-surface lines and main's `check` run (scripts/review-boundary.sh).
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root, trusted=True)
        rc, out = land(repo, env)
        assert rc == 0, out
        assert run("git", "rev-parse", "main", cwd=remote) == run("git", "rev-parse", "HEAD", cwd=repo)
        log = root / "gh.log"
        assert not log.exists() or not log.read_text().strip(), log.read_text()
    print("PASS: a trusted-surface landing makes no gh call")


def check_remote_rule_rejection_fails_hard():
    # A rule of the remote (here a pre-receive hook standing in for GitHub's GH013 ruleset rejection) declines the
    # push to main: push-main stops after that one attempt, says why, and leaves no lock; it does not retry it as
    # contention.
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root)
        base = run("git", "rev-parse", "main", cwd=remote)
        hook = remote / "hooks/pre-receive"
        hook.write_text(f"""#!/bin/sh
while read old new ref; do
  if [ "$ref" = refs/heads/main ]; then
    echo attempt >>"{root}/main-pushes"
    echo "error: GH013: Repository rule violations found for refs/heads/main." >&2
    exit 1
  fi
done
""")
        hook.chmod(0o755)
        rc, out = land(repo, env)
        assert rc == 1 and "REFUSED: the remote declined the push to main, not because main moved (GH013" in out, out
        assert (root / "main-pushes").read_text().count("attempt") == 1, "retried a rule rejection"
        assert run("git", "rev-parse", "main", cwd=remote) == base
        assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
        assert "main moved at the last moment" not in out, out
    print("PASS: a rule rejection by the remote (GH013) fails after one attempt, with no lock left")


def check_transport_failure_fails_hard():
    # A push that fails for another reason than a moved main (here the push URL is unreachable, as for a 403 or a
    # network failure) stops after one round instead of being retried as contention; no lock is left.
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root)
        base = run("git", "rev-parse", "main", cwd=remote)
        run("git", "config", "remote.origin.pushurl", str(root / "unreachable.git"), cwd=repo)
        rc, out = land(repo, env)
        assert rc == 1 and "REFUSED: the push to main failed, not because main moved" in out, out
        assert "rebased onto" not in out and "main moved at the last moment" not in out, out
        assert run("git", "rev-parse", "main", cwd=remote) == base
        assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
    print("PASS: a push failure that is not a moved main fails after one round, with no lock left")


def check_refuses_a_commit_email_off_the_allowlist():
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root)
        base = run("git", "rev-parse", "main", cwd=remote)
        rc, out = land(repo, {**env, "EMAILS_FAIL": "1"})
        assert rc == 1 and "REFUSED: commit emails" in out, out
        assert run("git", "rev-parse", "main", cwd=remote) == base, "pushed despite a rejected email"
        assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
        rc, out = land(repo, env)  # control: the same change lands once the check passes
        assert rc == 0 and run("git", "rev-parse", "main", cwd=remote) != base, out
    print("PASS: a commit email off the allowlist is refused before the push; the control lands")


def check_refuses_an_origin_other_than_the_code_repo():
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root)
        base = run("git", "rev-parse", "main", cwd=remote)
        for url in ("https://github.com/fixture/coordination.git", "git@github.com:fixture/old.git"):
            run("git", "remote", "set-url", "origin", url, cwd=repo)
            rc, out = land(repo, env)
            # (`git remote get-url` may print an insteadOf-rewritten form of the URL.)
            assert rc == 1 and "REFUSED: origin is " in out and "code repository is fixture/code" in out, out
        # The code repository's GitHub URL passes the guard (and then fails to fetch: no network here).
        run("git", "remote", "set-url", "origin", "https://github.com/fixture/code.git", cwd=repo)
        rc, out = land(repo, env)
        assert "but the code repository is" not in out, out
        assert run("git", "rev-parse", "main", cwd=remote) == base
    print("PASS: a GitHub origin other than the code repository is refused before any fetch or push")


def check_renaming_the_code_repository_lands_under_the_old_name_then_freezes():
    # The change that renames the code repository is checked against the name the target (origin/main) gives, so it
    # can land; afterwards every clone of the old name is refused, also one whose origin/main predates the rename
    # (refused right after its fetch). The GitHub URL is backed by the local remote through insteadOf.
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo, env = landing_repo(root)
        url = "https://github.com/fixture/code.git"
        stale = root / "stale"
        run("git", "clone", "-q", str(remote), str(stale), cwd=root)
        for clone in (repo, stale):
            for key, value in ((f"url.{remote}.insteadOf", url), ("user.name", "Test"),
                               ("user.email", "test@example.invalid"), ("commit.gpgsign", "false"),
                               ("core.hooksPath", "/dev/null")):
                run("git", "config", key, value, cwd=clone)
            run("git", "remote", "set-url", "origin", url, cwd=clone)
        run("git", "commit", "--allow-empty", "-q", "-m", "stale change", cwd=stale)
        (repo / "scripts/repos.toml").write_text('code = "fixture/renamed"\n')
        run("git", "commit", "-q", "-am", "rename the code repository", cwd=repo)
        rc, out = land(repo, env)
        assert rc == 0, out
        assert run("git", "rev-parse", "main", cwd=remote) == run("git", "rev-parse", "HEAD", cwd=repo), out
        landed = run("git", "rev-parse", "main", cwd=remote)
        run("git", "commit", "--allow-empty", "-q", "-m", "after the rename", cwd=repo)
        for clone in (repo, stale):
            rc, out = land(clone, env)
            assert rc == 1 and "REFUSED: origin is " in out and "code repository is fixture/renamed" in out, out
        assert run("git", "rev-parse", "main", cwd=remote) == landed
        assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
    print("PASS: a rename of the code repository lands under the old name; afterwards old-name clones are refused")


def check(sig, mutation=None, before_rebase=False):
    with tempfile.TemporaryDirectory(prefix="push-main-test-") as tmp:
        root = Path(tmp)
        remote, repo = root / "remote.git", root / "repo"
        run("git", "init", "--bare", str(remote), cwd=root)
        run("git", "init", "-b", "main", str(repo), cwd=root)
        for key, value in (("user.name", "Test"), ("user.email", "test@example.invalid"),
                           ("commit.gpgsign", "false"), ("core.hooksPath", "/dev/null")):
            run("git", "config", key, value, cwd=repo)
        scripts = repo / "scripts"
        scripts.mkdir()
        # Move main on the first check to force the real lock/rebase path. Pause the
        # second check while the lander holds that lock; no Lean build is needed.
        (scripts / "check.sh").write_text('''#!/usr/bin/env bash
set -eu
if [[ ! -f "$RUN_DIR/first" ]]; then
  touch "$RUN_DIR/first"
  base=$(git rev-parse origin/main)
  next=$(git commit-tree -p "$base" -m concurrent "$base^{tree}")
  git push -q origin "$next:main"
  if [[ "$PAUSE_FIRST" == 1 ]]; then
    touch "$RUN_DIR/ready"
    while [[ ! -f "$RUN_DIR/continue" ]]; do sleep 0.05; done
  fi
else
  touch "$RUN_DIR/ready"
  while [[ ! -f "$RUN_DIR/continue" ]]; do sleep 0.05; done
fi
echo 'check.sh: PASSED (fixture)'
''')
        (scripts / "review-boundary.sh").write_text("#!/bin/sh\nexit 0\n")
        (scripts / "repos.toml").write_text(REPOS)
        (scripts / "check-commit-emails.py").write_text(EMAILS)
        for script in scripts.iterdir():
            script.chmod(0o755)
        run("git", "add", ".", cwd=repo)
        run("git", "commit", "-m", "base", cwd=repo)
        run("git", "remote", "add", "origin", str(remote), cwd=repo)
        run("git", "push", "-u", "origin", "main", cwd=repo)
        (repo / "change").write_text("land me\n")
        run("git", "add", ".", cwd=repo)
        run("git", "commit", "-m", "change", cwd=repo)
        with (root / "log").open("w+") as log:
            proc = subprocess.Popen(["bash", str(SCRIPT)], cwd=repo, stdout=log,
                                    stderr=subprocess.STDOUT, start_new_session=True,
                                    # Background test runners may inherit ignored SIGINT;
                                    # Bash cannot trap a signal ignored at startup.
                                    preexec_fn=lambda: signal.signal(signal.SIGINT, signal.SIG_DFL),
                                    env={**os.environ, "RUN_DIR": tmp,
                                         "PAUSE_FIRST": str(int(before_rebase))})
            try:
                deadline = time.monotonic() + 20
                while not (root / "ready").exists():
                    if proc.poll() is not None or time.monotonic() > deadline:
                        raise AssertionError("lander did not reach its locked check")
                    time.sleep(0.05)
                base = run("git", "rev-parse", "main", cwd=remote)
                if not before_rebase:
                    assert run("git", "branch", "--list", "push-main-lock", cwd=remote)
                if mutation == "dirty":
                    (repo / "change").write_text("unchecked edit\n")
                elif mutation == "head":
                    run("git", "commit", "--allow-empty", "-m", "unchecked commit", cwd=repo)
                elif mutation == "gate":
                    (scripts / "review-boundary.sh").write_text("#!/bin/sh\nexit 1\n")
                local_head = run("git", "rev-parse", "HEAD", cwd=repo)
                if sig:
                    # Signal the shell itself: its foreground check is allowed to
                    # finish, but cancellation must prevent the subsequent push.
                    proc.send_signal(sig)
                (root / "continue").touch()
                rc = proc.wait(timeout=20)
                head = run("git", "rev-parse", "main", cwd=remote)
                assert rc == (128 + sig if sig else 1 if mutation else 0), f"unexpected exit {rc}"
                assert (head == base) == bool(sig or mutation), "wrong remote main after refusal/landing"
                assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
                log.seek(0)
                output = log.read()
                assert output.count("push-main: timing total=") == 1
                assert f"push-main: exit={rc}" in output
                if not sig and not mutation:
                    for phase in ("check", "review-boundary", "lock-acquire", "fetch-rebase", "delivery", "total"):
                        assert f"push-main: timing {phase}=" in output, f"missing {phase} timing"
                if mutation in ("dirty", "head"):
                    where = "before rebase" if before_rebase else "during checks"
                    assert f"HEAD or tree changed {where}" in output
                    assert run("git", "rev-parse", "HEAD", cwd=repo) == local_head
                if mutation == "gate":
                    assert "REFUSED: review boundary:" in output
            except BaseException:
                log.seek(0)
                print(log.read())
                raise
            finally:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
        print(f"PASS: {signal.Signals(sig).name if sig else mutation or 'normal landing'}; main and lock correct")


if __name__ == "__main__":
    for sig in (signal.SIGTERM, signal.SIGINT, None):
        check(sig)
    for mutation in ("dirty", "head", "gate"):
        check(None, mutation)
    for mutation in ("dirty", "head"):
        check(None, mutation, before_rebase=True)
    check_trusted_landing_posts_nothing()
    check_refuses_an_origin_other_than_the_code_repo()
    check_refuses_a_commit_email_off_the_allowlist()
    check_remote_rule_rejection_fails_hard()
    check_transport_failure_fails_hard()
    check_renaming_the_code_repository_lands_under_the_old_name_then_freezes()
