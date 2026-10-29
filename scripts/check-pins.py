#!/usr/bin/env python3
"""Pins check (step 0 of scripts/check.sh): the toolchain and every dependency equal scripts/pins.toml.

`lean-toolchain` equals `toolchain`; the manifest's package set equals the pinned set exactly, with
identical url/rev/inputRev; with --packages-dir, every package's checkout is at its pinned rev and clean.
Only the resolution Lake uses by default is accepted: git packages without subDir in the manifest's
`packagesDir = ".lake/packages"`, no package-overrides file, no `packagesDir` in the lakefile. With
--lean-path (the LEAN_PATH of `lake env`), the directories Lake actually resolved must be exactly the pinned
checkouts' build directories, the project's and the toolchain's.
Run as `python3 -I scripts/check-pins.py`. Failures are tagged FAIL[pins].
"""
import argparse, json, subprocess, sys, tomllib
from pathlib import Path

PACKAGES_DIR = ".lake/packages"

def check(toolchain, manifest, pins, packages_dir=None, overrides=None, lakefile=None, lean_path=None, libdir=None):
    pin = tomllib.loads(Path(pins).read_text())
    fails = []
    if Path(toolchain).read_text().strip() != pin["toolchain"]:
        fails.append(f"FAIL[pins] lean-toolchain is {Path(toolchain).read_text().strip()!r}, pinned {pin['toolchain']!r}")
    man = json.loads(Path(manifest).read_text())
    if man.get("packagesDir") != PACKAGES_DIR or man.get("lakeDir", ".lake") != ".lake":
        fails.append(f"FAIL[pins] resolution: manifest packagesDir/lakeDir {man.get('packagesDir')!r}/{man.get('lakeDir')!r}, "
                     f"only {PACKAGES_DIR!r}/'.lake' is checked")
    if overrides and Path(overrides).exists():
        fails.append(f"FAIL[pins] resolution: {overrides} exists (Lake would use the packages it names)")
    if lakefile and "packagesDir" in tomllib.loads(Path(lakefile).read_text()):
        fails.append(f"FAIL[pins] resolution: {lakefile} sets packagesDir")
    want = {p["name"]: p for p in pin.get("package", [])}
    have = {p["name"]: p for p in man["packages"]}
    for n in sorted(set(want) ^ set(have)):
        fails.append(f"FAIL[pins] package {n} is {'not pinned' if n in have else 'pinned but not in the manifest'}")
    for n, p in sorted(have.items()):
        if p.get("type") != "git" or p.get("subDir") is not None:
            fails.append(f"FAIL[pins] resolution: package {n} is type {p.get('type')!r} subDir {p.get('subDir')!r}, "
                         "only git packages without subDir are checked")
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
    if lean_path is not None:
        expect = {(Path(packages_dir or PACKAGES_DIR) / n / ".lake/build/lib/lean").resolve() for n in want}
        expect |= {Path(".lake/build/lib/lean").resolve()} | ({Path(libdir).resolve()} if libdir else set())
        got = [Path(p).resolve() for p in lean_path.split(":") if p]
        for p in sorted(set(got) ^ expect):
            fails.append(f"FAIL[pins] resolution: LEAN_PATH {'has' if p in got else 'lacks'} {p}")
        if len(got) != len(set(got)):
            fails.append("FAIL[pins] resolution: LEAN_PATH has duplicate entries")
    if not want:
        fails.append("FAIL[pins] no packages pinned")
    return fails

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolchain", default="lean-toolchain")
    ap.add_argument("--manifest", default="lake-manifest.json")
    ap.add_argument("--pins", default="scripts/pins.toml")
    ap.add_argument("--packages-dir")
    ap.add_argument("--overrides", help="Lake's package-overrides file (.lake/package-overrides.json): must not exist")
    ap.add_argument("--lakefile", help="lakefile.toml: must not set packagesDir")
    ap.add_argument("--lean-path", help="LEAN_PATH of `lake env`: exactly the pinned checkouts' build dirs + project + --libdir")
    ap.add_argument("--libdir", help="the toolchain library (`lean --print-libdir`)")
    a = ap.parse_args()
    fails = check(a.toolchain, a.manifest, a.pins, a.packages_dir, a.overrides, a.lakefile, a.lean_path, a.libdir)
    print("\n".join(fails) or "check-pins: toolchain and every package match scripts/pins.toml")
    sys.exit(1 if fails else 0)
