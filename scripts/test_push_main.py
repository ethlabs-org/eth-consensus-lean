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
