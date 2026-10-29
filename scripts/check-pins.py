#!/usr/bin/env python3
"""Pins check (step 0 of scripts/check.sh): the toolchain and every dependency equal scripts/pins.toml.

`lean-toolchain` equals `toolchain`; the manifest's package set equals the pinned set exactly, with
identical url/rev/inputRev; with --packages-dir, every package's checkout is at its pinned rev and clean.
Run as `python3 -I scripts/check-pins.py`. Failures are tagged FAIL[pins].
"""
import argparse, json, subprocess, sys, tomllib
from pathlib import Path

def check(toolchain, manifest, pins, packages_dir=None):
    pin = tomllib.loads(Path(pins).read_text())
    fails = []
    if Path(toolchain).read_text().strip() != pin["toolchain"]:
        fails.append(f"FAIL[pins] lean-toolchain is {Path(toolchain).read_text().strip()!r}, pinned {pin['toolchain']!r}")
    want = {p["name"]: p for p in pin.get("package", [])}
    have = {p["name"]: p for p in json.loads(Path(manifest).read_text())["packages"]}
    for n in sorted(set(want) ^ set(have)):
        fails.append(f"FAIL[pins] package {n} is {'not pinned' if n in have else 'pinned but not in the manifest'}")
    for n in sorted(set(want) & set(have)):
        for k in ("url", "rev", "inputRev"):
            if want[n][k] != have[n].get(k):
                fails.append(f"FAIL[pins] {n}.{k} is {have[n].get(k)!r}, pinned {want[n][k]!r}")
        if packages_dir:
            d = Path(packages_dir) / n
            head = subprocess.run(["git", "-C", str(d), "rev-parse", "HEAD"], capture_output=True, text=True)
            dirty = subprocess.run(["git", "-C", str(d), "status", "--porcelain"], capture_output=True, text=True)
            if head.returncode or head.stdout.strip() != want[n]["rev"]:
                fails.append(f"FAIL[pins] checkout {d} is at {head.stdout.strip() or head.stderr.strip()!r}, pinned {want[n]['rev']}")
            if dirty.returncode or dirty.stdout.strip():
                fails.append(f"FAIL[pins] checkout {d} is not clean")
    if not want:
        fails.append("FAIL[pins] no packages pinned")
    return fails

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolchain", default="lean-toolchain")
    ap.add_argument("--manifest", default="lake-manifest.json")
    ap.add_argument("--pins", default="scripts/pins.toml")
    ap.add_argument("--packages-dir")
    a = ap.parse_args()
    fails = check(a.toolchain, a.manifest, a.pins, a.packages_dir)
    print("\n".join(fails) or "check-pins: toolchain and every package match scripts/pins.toml")
    sys.exit(1 if fails else 0)
