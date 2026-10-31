#!/usr/bin/env python3
"""Scoped box installation; run with sudo after landing/review, never the full host installer.

The host alert source is an unversioned setup bundle. Preserve it and the deployed
copy together, adding only this hook. No timer, config, credentials or CI changes.
"""
import argparse
import datetime
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile


DEST = Path("/usr/local/lib/ethlabs-alerts/orb-ci-liveness.py")
DEPLOYED = Path("/usr/local/sbin/ethlabs-alerts")
BEGIN = "# BEGIN consensus-lean liveness hook\n"
END = "# END consensus-lean liveness hook\n"
HOOK = BEGIN + '''def check_consensus_ci(st, now, alerts):
    # Import inside the check: a missing/broken helper becomes a normal broken-check
    # alert, without preventing any of the existing host checks from running.
    import runpy
    runpy.run_path("/usr/local/lib/ethlabs-alerts/orb-ci-liveness.py")["check"](st, now, alerts)


CHECKS.append(check_consensus_ci)
''' + END + "\n\n"


def hooked(text):
    if BEGIN in text:
        start = text.index(BEGIN)
        end = text.index(END, start) + len(END)
        text = text[:start] + text[end:].lstrip("\n")
    anchor = "def main():\n"
    if text.count(anchor) != 1 or "CHECKS = [" not in text:
        raise ValueError("unrecognized host alert source; refusing to modify")
    result = text.replace(anchor, HOOK + anchor)
    compile(result, "ethlabs-alerts", "exec")
    return result


def secure_directory(path):
    for directory in [path, *path.parents]:
        info = directory.lstat()
        if not stat.S_ISDIR(info.st_mode) or info.st_uid != 0 or info.st_mode & 0o022:
            raise ValueError(f"unsafe root code directory: {directory}")


def replace(path, data, owner, mode):
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as file:
            file.write(data)
            os.fchmod(file.fileno(), mode)
            os.fchown(file.fileno(), *owner)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path,
                        default=Path("/home/fradamt/ethlabs-setup/files/ethlabs-alerts.py"))
    args = parser.parse_args()
    if os.geteuid() != 0:
        parser.error("run with sudo")
    source = args.source
    if source.is_symlink() or DEPLOYED.is_symlink():
        parser.error("refusing symlinked alert source/deployment")
    original = source.read_bytes()
    if original != DEPLOYED.read_bytes():
        parser.error("source and deployed alerts differ; reconcile before installation")
    updated = hooked(original.decode()).encode()
    helper = Path(__file__).with_name("orb-ci-liveness.py").read_bytes()
    compile(helper, str(DEST), "exec")
    secure_directory(DEST.parent.parent)
    DEST.parent.mkdir(mode=0o755, exist_ok=True)
    secure_directory(DEST.parent)
    secure_directory(DEPLOYED.parent)
    backup_root = Path("/var/backups/ethlabs-alerts")
    secure_directory(backup_root.parent)
    backup_root.mkdir(mode=0o700, exist_ok=True)
    secure_directory(backup_root)
    backup = Path(tempfile.mkdtemp(prefix="liveness-", dir=backup_root))
    shutil.copy2(source, backup / "source.py")
    shutil.copy2(DEPLOYED, backup / "deployed.py")
    if DEST.exists():
        shutil.copy2(DEST, backup / "helper.py")
    owner = source.stat()
    # Install root-owned code first, before either copy gains the hook.
    replace(DEST, helper, (0, 0), 0o644)
    replace(source, updated, (owner.st_uid, owner.st_gid), stat.S_IMODE(owner.st_mode))
    replace(DEPLOYED, updated, (0, 0), 0o755)
    subprocess.run(["/usr/local/sbin/ethlabs-inventory", "register",
                    "lib:/usr/local/lib/ethlabs-alerts", "manual",
                    "consensus-lean scripts/install-orb-ci-liveness.py; update after reviewed push-main"], check=True)
    timestamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    with open("/srv/NOTES.md", "a") as notes:
        notes.write(f"\n{timestamp} | Astra (fradamt) | Installed consensus-lean liveness hook in existing alerts; "
                    f"source/deployed parity, backup {backup}; timer/config/watcher unchanged.\n")
    print(f"Installed {DEST}; source/deployed parity verified: {source.read_bytes() == DEPLOYED.read_bytes()}")
    print(f"Backup: {backup}; no services restarted, no test notification sent")


if __name__ == "__main__":
    main()
