#!/usr/bin/env python3
"""Project-specific CHECKS hook for the box's existing ethlabs-alerts runner.

Installed root-owned, never imported by root from a writable checkout. No credentials,
notification transport or independent timer: state/dedup/delivery belong to the host.
"""
import json
import os
import pwd
import re
import subprocess


SLUG = "ethlabs-org/consensus-lean"
UNIT = "consensus-lean-orb-ci.service"
GRACE = 1800


def user_read(*args):
    """Bounded reads with the watcher's identity; never echo gh stderr/credentials."""
    user = pwd.getpwnam("fradamt")
    env = {"HOME": user.pw_dir, "PATH": "/usr/bin:/bin",
           "XDG_RUNTIME_DIR": f"/run/user/{user.pw_uid}",
           "DBUS_SESSION_BUS_ADDRESS": f"unix:path=/run/user/{user.pw_uid}/bus"}
    identity = {}
    if os.geteuid() == 0:
        identity = dict(user=user.pw_uid, group=user.pw_gid, extra_groups=[])
    elif os.geteuid() != user.pw_uid:
        raise RuntimeError("liveness reader requires root or watcher owner")
    result = subprocess.run(args, env=env, capture_output=True, text=True,
                            timeout=25, **identity)
    if result.returncode:
        raise RuntimeError(f"{args[0]} read failed (exit {result.returncode})")
    return result.stdout.strip()


def published(body):
    """Only actual main fast/changed result rows, including failed checks, count."""
    table = body.split("<!-- orb-ci results -->", 1)[1].split("<!-- /orb-ci results -->", 1)
    if len(table) != 2 or "|---|---|---|---|---|" not in table[0]:
        raise ValueError("missing results table")
    hashes = set()
    for line in table[0].splitlines():
        cells = [c.strip() for c in line.split("|")]
        if len(cells) < 7 or cells[2] not in ("main", "main (re-check)"):
            continue
        if (re.fullmatch(r"`[0-9a-f]{8}`", cells[3]) and
                re.match(r"^--(?:fast|changed)(?:\s|$)", cells[4]) and
                re.match(r"^(?:PASSED|\*\*FAILED\*\*) in \d+s(?:$|:)", cells[5])):
            hashes.add(cells[3].strip("`"))
    return hashes


def check(st, now, alerts, read=user_read):
    state = st.setdefault("consensus_lean_liveness", {})
    errors = []
    try:
        status = read("/usr/bin/systemctl", "--user", "show", UNIT,
                      "--property=ActiveState", "--value")
        if status != "active":
            alerts.append(("consensus-ci:stopped", "consensus CI watcher stopped",
                           f"fradamt user unit {UNIT}: {status or 'unknown'}. "
                           "Inspect the user journal; do not interrupt a live CI job."))
    except (OSError, subprocess.SubprocessError, RuntimeError) as error:
        errors.append("user service status unavailable (" + type(error).__name__ + ")")

    try:
        head = json.loads(read("/usr/bin/gh", "api", f"repos/{SLUG}/git/ref/heads/main"))["object"]["sha"]
        if not isinstance(head, str) or not re.fullmatch(r"[0-9a-f]{40}", head):
            raise ValueError("invalid main SHA")
        if head != state.get("head"):
            state["head"] = head
            state.setdefault("pending", []).append([head, now])
    except (OSError, subprocess.SubprocessError, RuntimeError, ValueError, KeyError, TypeError):
        errors.append("GitHub main head unavailable")

    try:
        rows = published(json.loads(read("/usr/bin/gh", "api", f"repos/{SLUG}/issues/63"))["body"])
        pending = state.get("pending", [])
        # Polling intentionally coalesces heads. A published later observed head
        # covers superseded observations, but mere churn never resets the deadline.
        covered = max((i for i, (sha, _) in enumerate(pending) if sha[:8] in rows), default=-1)
        state["pending"] = pending[covered + 1:]
    except (OSError, subprocess.SubprocessError, RuntimeError, ValueError, KeyError, TypeError, IndexError):
        errors.append("GitHub #63 results unavailable or malformed")

    if errors:
        since = state.setdefault("unavailable_since", now)
        if now - since >= GRACE:
            alerts.append(("consensus-ci:unavailable", "consensus CI observation unavailable",
                           "; ".join(errors) + f"; impaired for {int((now - since) / 60)} min. "
                           "Cannot confirm watcher/publication health."))
    else:
        state.pop("unavailable_since", None)
    pending = state.get("pending", [])
    if pending and now - pending[0][1] >= GRACE:
        alerts.append(("consensus-ci:missing-row", "consensus CI result overdue",
                       f"No observed main progress published on #63 for {int((now - pending[0][1]) / 60)} min; "
                       f"oldest {pending[0][0][:8]}, latest {state['head'][:8]}. "
                       "Local done is not publication evidence. "
                       + ("GitHub observation impaired; result may exist." if errors else
                          "Watcher may be stuck, checks slow, or publication failing.")))
