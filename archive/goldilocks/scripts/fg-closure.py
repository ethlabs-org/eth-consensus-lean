#!/usr/bin/env python3
"""FG-closure skip rule for landing scripts (lead ruling 2026-10-03).

check-fg.sh checks only the FG libraries and its own inputs. This script derives that input set
MECHANICALLY at a git revision and decides whether a landing diff can skip check-fg:

  * the shell inputs: scripts/check-fg.sh, its check-fg-<word>.sh helpers (followed), and every
    scripts/* or docs/* file they name on a non-comment line. A sourced helper such as
    scripts/gate-common.sh is an input, but the files it names are not followed: check-fg-pins.sh
    reaches only its gate_build function, which runs `lake build` on targets that this script reads
    from the gate_build call itself. The FGSA checkers (check-fgsa*.sh, CheckFGSA*.lean) are not inputs;
  * the build targets: every target of a `lake build` or `gate_build` line in the shell inputs. Each
    target is a [[lean_lib]] of lakefile.toml; every file that its `globs` match is an input
    ("X" = the module X; "X.*" = X and every module under X; "X.+" = every module under X; no globs =
    the root module), within the library's srcDir;
  * the in-repo Lean import closure of those files and of the Lean scripts that check-fg runs;
  * lakefile*, lean-toolchain, lake-manifest.json, and this script.

Usage:
  python3 scripts/fg-closure.py --list [REV]          print the closure at REV (default HEAD)
  python3 scripts/fg-closure.py --changed BASE HEAD   exit 0 and print the skip line when the diff
                                                      BASE..HEAD touches no file of closure(BASE) ∪
                                                      closure(HEAD); else exit 1 and list the files.
  python3 scripts/fg-closure.py --selftest [REV]      negative controls (exit 0 when all hold).
Any error exits 1 with "FG-closure script error; check-fg needed" (fail closed).
This is a landing-script rule only. FULL-tier gates and the daily full main run always run check-fg.
"""
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from source_layout import Layout

ENTRY = "scripts/check-fg.sh"
HELPER = re.compile(r"^scripts/check-fg-[a-z]+\.sh$")
FIXED = ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json", "scripts/fg-closure.py")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.']*)")
NAMED = re.compile(r"(?<![\w/.-])((?:scripts|docs)/[\w./-]+)")
BUILD = re.compile(r"(?:\blake\s+build|\bgate_build)\b((?:\s+[-\w.=\"$]+)*)")
TARGET = re.compile(r"^[A-Z][\w]*(?:\.[\w]+)*$")


def git(*args):
    return subprocess.run(("git",) + args, check=True, capture_output=True, text=True).stdout


def closure(rev):
    files = set(git("ls-tree", "-r", "--name-only", rev).split())

    def show(path):
        return git("show", f"{rev}:{path}")

    if "lakefile.lean" in files:
        raise RuntimeError("lakefile.lean is not parsed by this script")
    layout = Layout(Path.cwd(), rev)
    libs = {lib["name"]: lib for lib in tomllib.loads(show("lakefile.toml")).get("lean_lib", [])}
    src_dirs = sorted({lib.get("srcDir", ".") for lib in libs.values()})

    out = {f for f in FIXED if f in files}
    shells, lean_files, targets, pending = set(), set(), set(), [ENTRY]
    while pending:
        f = pending.pop()
        if f in shells or f not in files:
            continue
        shells.add(f)
        out.add(f)
        for line in show(f).splitlines():
            if line.lstrip().startswith("#"):
                continue
            for m in BUILD.finditer(line):
                targets.update(t for t in m.group(1).split() if TARGET.match(t))
            for ref in NAMED.findall(line):
                if ref not in files:
                    continue
                out.add(ref)
                if HELPER.match(ref):
                    pending.append(ref)
                elif ref.endswith(".lean"):
                    lean_files.add(ref)
    if not targets:
        raise RuntimeError("no lake build / gate_build target found in the check-fg scripts")

    def prefix(src, module):
        path = module.replace(".", "/")
        return path if src == "." else f"{src}/{path}"

    for t in sorted(targets):
        if t not in libs:
            raise RuntimeError(f"build target {t} is not a [[lean_lib]] of lakefile.toml")
        lib, src = libs[t], libs[t].get("srcDir", ".")
        for glob in lib.get("globs", [t]):
            if glob.endswith(".*") or glob.endswith(".+"):
                base = prefix(src, glob[:-2])
                if glob.endswith(".*"):
                    lean_files.add(base + ".lean")
                lean_files.update(f for f in files if f.startswith(base + "/") and f.endswith(".lean"))
            else:
                lean_files.add(prefix(src, glob) + ".lean")

    def resolve(module):
        try:
            path = layout.source_path(module)
        except ValueError:
            return None
        return path if path in files else None

    todo, seen = sorted(lean_files), set()
    while todo:
        path = todo.pop()
        if path in seen or path not in files:
            continue
        seen.add(path)
        out.add(path)
        for line in show(path).splitlines():
            m = IMPORT.match(line)
            if m:
                dep = resolve(m.group(1))
                if dep:
                    todo.append(dep)
    return out


def decide(changed, cl):
    hit = sorted(set(changed) & cl)
    if hit:
        return 1, f"check-fg needed: {len(hit)} FG-closure file(s) changed: " + " ".join(hit)
    return 0, f"check-fg skipped: no FG-closure change ({len(set(changed))} files checked)"


def selftest(rev):
    cl = closure(rev)
    files = set(git("ls-tree", "-r", "--name-only", rev).split())
    layout = Layout(Path.cwd(), rev)
    kit_dir = layout.source_dir("AvailableChainKitFG")
    kit_tests = sorted(f for f in files
                       if f.startswith(kit_dir + "/Tests/") and f.endswith(".lean"))
    checks = [
        ("a KitFG/Tests-only diff needs check-fg", bool(kit_tests) and decide(kit_tests[:1], cl)[0] == 1),
        ("every KitFG module is in the closure", all(f in cl for f in files
                                                     if f.startswith(kit_dir + "/") and
                                                     f.endswith(".lean"))),
        ("a SimplexFG module needs check-fg",
         decide([layout.source_path("AvailableChainSimplexFG")], cl)[0] == 1),
        ("a check-fg script needs check-fg", decide(["scripts/check-fg-pins.sh"], cl)[0] == 1),
        ("gate-common.sh needs check-fg", decide(["scripts/gate-common.sh"], cl)[0] == 1),
        ("the toolchain needs check-fg", decide(["lean-toolchain"], cl)[0] == 1),
        ("an FGSA-only diff skips",
         decide([layout.source_path("AvailableChainFGSAProofs.Proofs.Healing.Base"),
                                            "scripts/check-fgsa-claims.sh"], cl)[0] == 0),
    ]
    checks += [
        ("deep archived FG registry is in closure",
         layout.archive_doc_path("docs/FG-COMPOSITION.md") in cl),
        ("source layout helper is in closure when present",
         "scripts/source_layout.py" not in files or "scripts/source_layout.py" in cl),
    ]
    bad = [name for name, ok in checks if not ok]
    for name, ok in checks:
        print(("ok   " if ok else "FAIL ") + name)
    return 1 if bad else 0


def main(argv):
    if argv[:1] == ["--list"]:
        for f in sorted(closure(argv[1] if len(argv) > 1 else "HEAD")):
            print(f)
        return 0
    if argv[:1] == ["--selftest"]:
        return selftest(argv[1] if len(argv) > 1 else "HEAD")
    if len(argv) == 3 and argv[0] == "--changed":
        base, head = argv[1], argv[2]
        changed = git("diff", "--no-renames", "--name-only", f"{base}..{head}").split()
        rc, line = decide(changed, closure(base) | closure(head))
        print(line)
        return rc
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Exception as e:  # fail closed by design: any error means "run check-fg"
        print(f"FG-closure script error; check-fg needed ({type(e).__name__}: {e})")
        sys.exit(1)
