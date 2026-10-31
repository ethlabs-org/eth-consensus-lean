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


def check(sig):
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
                                    env={**os.environ, "RUN_DIR": tmp})
            try:
                deadline = time.monotonic() + 20
                while not (root / "ready").exists():
                    if proc.poll() is not None or time.monotonic() > deadline:
                        raise AssertionError("lander did not reach its locked check")
                    time.sleep(0.05)
                base = run("git", "rev-parse", "main", cwd=remote)
                assert run("git", "branch", "--list", "push-main-lock", cwd=remote)
                if sig:
                    # Signal the shell itself: its foreground check is allowed to
                    # finish, but cancellation must prevent the subsequent push.
                    proc.send_signal(sig)
                (root / "continue").touch()
                rc = proc.wait(timeout=20)
                head = run("git", "rev-parse", "main", cwd=remote)
                assert rc == (128 + sig if sig else 0), f"unexpected exit {rc}"
                assert (head == base) == bool(sig), "wrong remote main after cancellation/landing"
                assert not run("git", "branch", "--list", "push-main-lock", cwd=remote), "lock leaked"
            except BaseException:
                log.seek(0)
                print(log.read())
                raise
            finally:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
        print(f"PASS: {signal.Signals(sig).name if sig else 'normal landing'}; main and lock correct")


if __name__ == "__main__":
    for sig in (signal.SIGTERM, signal.SIGINT, None):
        check(sig)
