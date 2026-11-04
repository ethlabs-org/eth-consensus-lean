#!/usr/bin/env python3
"""Capture job-bound reports and publish privately, independently of CI's done ledger.

Data branch writes are atomic fast-forwards. Per-source-SHA files are first-record
wins, including unavailable reports. Failed publications stay in the local outbox.
"""
import argparse
import base64
import datetime
import fcntl
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

BRANCH = "ci-inventory"
MAX_BYTES = 4 * 1024 * 1024


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def capture(home, sha, kind, run, checked_at, ci_result):
    if not re.fullmatch(r"[0-9a-f]{40}", sha) or kind not in ("main", "main-recheck"):
        raise ValueError("capture requires a full main commit SHA")
    report = {"schema_version": 1, "commit": sha, "checked_at": checked_at,
              "ci_result": ci_result, "availability": "unavailable",
              "reason": "no job-bound step 3c output (missing/skipped/build failed)", "inventory": None}
    if run is not None:
        # Exactly this job's fresh WORK, never the persistent CI worktree or old jobs.
        files = list(run.glob("check.*/sorry-inventory.json"))
        if len(files) == 1:
            try:
                if not files[0].resolve().is_relative_to(run.resolve()):  # a link planted by the checked head
                    raise ValueError("inventory resolves outside the job's run folder")
                if files[0].stat().st_size > MAX_BYTES:
                    raise ValueError("inventory exceeds 4 MiB limit; not truncated")
                inventory = json.loads(files[0].read_text())
                if (inventory.get("schema_version") != 1 or inventory.get("mode") != "report-only" or
                        inventory.get("status") not in ("mapped", "incomplete") or
                        not all(isinstance(inventory.get(k), list) for k in ("issues", "sorries", "roots"))):
                    raise ValueError("invalid inventory schema")
                report.update(availability="available", reason=None, inventory=inventory)
                if len(encoded(report)) > MAX_BYTES:
                    raise ValueError("envelope exceeds 4 MiB limit; not truncated")
            except (OSError, ValueError, AttributeError) as error:
                report.update(availability="unavailable", reason=str(error), inventory=None)
        elif len(files) > 1:
            report["reason"] = "ambiguous job output: multiple step 3c reports"
    outbox = home / "inventory-outbox"
    outbox.mkdir(parents=True, exist_ok=True)
    target = outbox / f"{sha}.json"
    # Preserve the first captured attempt even across retries/rechecks.
    item = {"kind": kind, "report": report}
    if target.exists():
        item = json.loads(target.read_text())
        if kind != "main" or item["kind"] == "main":
            return target
        # A queued recheck can precede the normal main observation. Preserve its
        # immutable report, but do not lose that later observation's eligibility.
        item["kind"] = "main"
    with tempfile.NamedTemporaryFile(dir=outbox, delete=False) as file:
        file.write(encoded(item))
        temporary = Path(file.name)
    temporary.replace(target)
    return target


def api(slug, path, data=None, missing=False, method="POST"):
    command = ["gh", "api", f"repos/{slug}/{path}"]
    if data is not None:
        command += ["--method", method, "--input", "-"]
    proc = subprocess.run(command, input=json.dumps(data) if data is not None else None,
                          text=True, capture_output=True, timeout=45)
    if proc.returncode:
        if missing and "(HTTP 404)" in proc.stderr:
            return None
        # No captured stderr or credentials in published diagnostics.
        raise RuntimeError(f"GitHub {path.split('/')[0]} request failed (exit {proc.returncode})")
    return json.loads(proc.stdout)


def publish(slug, item, request=api, code=None):
    # The ci-inventory branch lives in `slug` (the coordination repository); the freshness check reads the head of
    # main in the code repository `code` (the same repository when not given).
    def call(path, data=None, missing=False, method="POST"):
        return request(slug, path, data, missing, method)

    def code_main():
        return request(code or slug, "git/ref/heads/main", None, False, "POST")["object"]["sha"]

    ref = call(f"git/ref/heads/{BRANCH}", missing=True)
    parent = ref["object"]["sha"] if ref else None
    files = {}
    if parent:
        commit = call(f"git/commits/{parent}")
        tree = call(f"git/trees/{commit['tree']['sha']}?recursive=1")
        if tree.get("truncated"):
            raise RuntimeError("inventory branch tree truncated; refusing partial view")
        files = {entry["path"]: entry["sha"] for entry in tree["tree"] if entry["type"] == "blob"}

    def blob_json(blob):
        return json.loads(base64.b64decode(call(f"git/blobs/{blob}")["content"]))

    def blob(value):
        return call("git/blobs", {"content": base64.b64encode(encoded(value)).decode(), "encoding": "base64"})["sha"]

    report = item["report"]
    path = f"commits/{report['commit']}.json"
    changes = []
    if path in files:
        report = blob_json(files[path])
        payload_blob = files[path]
    else:
        payload_blob = blob(report)
        changes.append({"path": path, "mode": "100644", "type": "blob", "sha": payload_blob})
    latest = blob_json(files["latest.json"]) if "latest.json" in files else None
    # A current-head recheck may discover an existing immutable report. Historical
    # retries/rechecks must not replace discovery, regardless of their timestamps.
    advance = (latest is None or latest["commit"] != report["commit"]) and code_main() == report["commit"]
    if advance:
        latest = {"schema_version": 1, "commit": report["commit"], "checked_at": report["checked_at"],
                  "published_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "availability": report["availability"],
                  "inventory_status": report["inventory"]["status"] if report["inventory"] else None,
                  "payload_path": path, "payload_api": f"repos/{slug}/git/blobs/{payload_blob}",
                  "payload_sha256": hashlib.sha256(encoded(report)).hexdigest()}
        changes.append({"path": "latest.json", "mode": "100644", "type": "blob", "sha": blob(latest)})
    if not changes:
        return
    tree_data = {"tree": changes}
    if parent:
        tree_data["base_tree"] = commit["tree"]["sha"]
    tree_sha = call("git/trees", tree_data)["sha"]
    commit_sha = call("git/commits", {"message": f"Inventory for {report['commit']}",
                                      "tree": tree_sha, "parents": [parent] if parent else []})["sha"]
    if advance and code_main() != report["commit"]:
        raise RuntimeError("main advanced during publication; retained for retry")
    if parent:
        # GitHub refuses a non-fast-forward racing publisher; retry from fresh ref.
        call(f"git/refs/heads/{BRANCH}", {"sha": commit_sha, "force": False}, method="PATCH")
    else:
        call("git/refs", {"ref": f"refs/heads/{BRANCH}", "sha": commit_sha})


def flush(home, slug, code=None):
    failed = False
    outbox = home / "inventory-outbox"
    for path in sorted(outbox.glob("*.json")):
        try:
            publish(slug, json.loads(path.read_text()), code=code)
            path.unlink()
            print(f"inventory published: {path.stem}")
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            print(f"REPORT inventory publication pending {path.stem}: {type(error).__name__}: {error}")
            failed = True
            break  # bounded API outage retry; next watcher pass tries again
    return 1 if failed else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--home", type=Path, required=True)
    sub = parser.add_subparsers(dest="command", required=True)
    cap = sub.add_parser("capture")
    cap.add_argument("sha")
    cap.add_argument("kind", choices=("main", "main-recheck"))
    cap.add_argument("run")
    cap.add_argument("checked_at")
    cap.add_argument("ci_result", choices=("passed", "failed"))
    push = sub.add_parser("flush")
    push.add_argument("slug", help="repository of the ci-inventory branch (`issues` in scripts/repos.toml)")
    # Optional, so that a watcher cached before the split keeps working with this publisher (orb-ci-refresh.sh).
    push.add_argument("code", nargs="?", help="repository whose main is checked (`code`); default: slug")
    args = parser.parse_args()
    args.home.mkdir(parents=True, exist_ok=True)
    with (args.home / "inventory.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if args.command == "capture":
            capture(args.home, args.sha, args.kind, Path(args.run) if args.run else None, args.checked_at, args.ci_result)
            return 0
        return flush(args.home, args.slug, args.code)


if __name__ == "__main__":
    raise SystemExit(main())
