#!/usr/bin/env python3
"""Re-elaborate project sources with the build-deferred syntax linters enabled.

Run after `lake build --wfail ConsensusLean ConsensusLeanTest Solution Challenge`.
Unlike `lake lint` (environment linters), these checks need source syntax and info trees.
Outputs and modified module setups stay in a temporary directory, never the build cache.
Optional module arguments restrict a local run; --changed BASE includes tracked and untracked
source edits, or all modules when elaboration configuration changes. Run from the repository root.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import tempfile
import time


DEFERRED = (
    "style.whitespace", "unreachableTactic", "style.multiGoal", "style.cdot",
    "unusedTactic", "unnecessarySeqFocus",
)

# Modules whose lint elaboration peaks near 10 GiB. They run one at a time before the parallel
# pool, so no two of them overlap on a 16 GiB machine. A full run fails if one is renamed away.
ALONE = (
    "ConsensusLeanTest.Goldilocks.Generic.HealingLeavesCut",
    "ConsensusLeanTest.Goldilocks.Generic.SleepyCut",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*")
    parser.add_argument("-j", "--jobs", type=int, default=1,
                        help="parallel Lean processes (default 1; use 2 with 16 GiB)")
    parser.add_argument("--changed", metavar="BASE",
                        help="lint touched sources, or all after elaboration configuration changes")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.changed and args.modules:
        parser.error("use either module arguments or --changed, not both")
    modules = sorted(
        str(path.with_suffix("")).replace("/", ".")
        for prefix in ("ConsensusLean", "ConsensusLeanTest")
        for path in [Path(prefix + ".lean"), *Path(prefix).rglob("*.lean")]
    ) + ["Solution", "Challenge"]
    missing = [m for m in ALONE if m not in modules]
    if missing and not args.modules and not args.changed:
        parser.error("lint-syntax: ALONE names no module: " + ", ".join(missing))
    if args.modules:
        modules = args.modules
    if args.changed:
        changed = subprocess.check_output([
            "git", "diff", "--name-only", "-z", args.changed, "--",
        ]).decode().split("\0")
        changed += subprocess.check_output([
            "git", "ls-files", "--others", "--exclude-standard", "-z",
        ]).decode().split("\0")
        if not any(p in (
            "lakefile.toml", "lean-toolchain", "lake-manifest.json",
            "scripts/pins.toml", "scripts/lint-syntax.py",
        ) for p in changed):
            touched = {p.removesuffix(".lean").replace("/", ".")
                       for p in changed if p.endswith(".lean")}
            modules = [m for m in modules if m in touched]
    # Query all setups in one Lake invocation: saved .setup.json files are refreshed only
    # by compilation, not by cache hits/restores, and can contain obsolete imports/options.
    # Lake emits one JSON result per target, in argument order. Do not lint on query failure.
    setups = []
    if modules:
        query = subprocess.run(["lake", "query", "--json", *[f"+{m}:setup" for m in modules]],
                               capture_output=True, text=True)
        if query.stderr:
            print(query.stderr, end="", flush=True)
        if query.returncode:
            print("lint-syntax: FAIL (Lake setup query failed)", flush=True)
            return 1
        setups = [json.loads(line) for line in query.stdout.splitlines()]
        if len(setups) != len(modules) or any(s["name"] != m for s, m in zip(setups, modules)):
            raise ValueError("Lake setup query did not return the requested modules")
    setups = dict(zip(modules, setups))

    def lint(module):
        with tempfile.TemporaryDirectory(prefix="lint-syntax-") as scratch:
            scratch = Path(scratch)
            source = Path(module.replace(".", "/") + ".lean")
            setup = setups[module]
            for name in DEFERRED:
                setup["options"]["weak.linter." + name] = True
            lint_setup = scratch / "module.setup.json"
            lint_setup.write_text(json.dumps(setup))
            print(f"lint-syntax: {module}", flush=True)
            start = time.monotonic()
            result = subprocess.run([
                "lean", str(source), "--setup", str(lint_setup), "--json",
                "-o", str(scratch / "module.olean"),
            ], capture_output=True, text=True)
            warnings = False
            for line in result.stdout.splitlines():
                message = json.loads(line)
                print(line, flush=True)
                warnings |= message.get("severity") == "warning"
            if result.stderr:
                print(result.stderr, end="", flush=True)
            print(f"lint-syntax: done {module} ({time.monotonic() - start:.0f}s)", flush=True)
            if result.returncode:
                return result.returncode
            if warnings:
                return 1
            return 0

    results = [lint(m) for m in modules if m in ALONE]
    with ThreadPoolExecutor(args.jobs) as pool:
        results += pool.map(lint, [m for m in modules if m not in ALONE])
    if any(results):
        return 1
    print(f"lint-syntax: PASS ({len(modules)} modules; {len(DEFERRED)} deferred linters)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
