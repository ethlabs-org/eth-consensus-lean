#!/usr/bin/env python3
"""Per-declaration profile of one module (CONTRIBUTING.md "Profile before raising heartbeats"). Report-only.

Elaborates <file> once with Lean's built-in profiler (`lake lean <file> -- -Dtrace.profiler=true
-Dtrace.profiler.output=<json>`), so the run uses the lakefile's leanOptions and needs the file's imports
built. Writes the Firefox Profiler JSON (open it at https://profiler.firefox.com/from-file/) and prints
the wall time, the peak RSS, the slowest declarations and the slowest leaf steps (tactics, simp,
linarith, linters, kernel). With --from <json> it only summarises an existing profile.

Times are the profiler's trace-node durations in milliseconds, summed over the elaboration threads
(proofs elaborate in parallel, so the declaration total can exceed the wall time). Nodes shorter than
--threshold (Lean's trace.profiler.threshold, default 10 ms) are not recorded.

Usage: python3 -I scripts/profile-module.py <file.lean> [-o <out.json>] [-n 15] [--threshold 10]
       python3 -I scripts/profile-module.py --from <profile.json> [-n 15]
"""
import argparse, json, os, resource, subprocess, sys, time
from collections import Counter

ASYNC = "Elab.async: elaborating proof of "


def label(name):
    return name.split("\n", 1)[0].strip()


def summarise(path, top):
    profile = json.load(open(path))
    decls, leaves = Counter(), Counter()
    for t in profile["threads"]:
        strings, s, frames = t["stringArray"], t["samples"], t["frameTable"]
        funcs, stacks = t["funcTable"], t["stackTable"]
        for stack, weight in zip(s["stack"], s["weight"]):
            names, i = [], stack
            while i is not None:
                names.append(label(strings[funcs["name"][frames["func"][stacks["frame"][i]]]]))
                i = stacks["prefix"][i]
            names.reverse()
            if names[0].startswith("runFrontend"):  # the main thread's whole-file span
                names = names[1:]
            if not names:
                continue
            root = names[0].removeprefix(ASYNC)
            decls[root] += weight
            leaves[names[-1]] += weight
    for title, counter in (("Slowest declarations and async tasks (inclusive)", decls),
                           ("Slowest leaf steps (self)", leaves)):
        print(f"\n{title}, ms:")
        for name, ms in counter.most_common(top):
            print(f"{ms:9.0f}  {name[:160]}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("file", nargs="?", help="Lean source file of a project module")
    ap.add_argument("-o", "--out", help="profile JSON (default: /tmp/<module>.profile.json)")
    ap.add_argument("--from", dest="src", help="summarise an existing profile JSON, no run")
    ap.add_argument("-n", "--top", type=int, default=15)
    ap.add_argument("--threshold", type=int, default=10, help="trace.profiler.threshold in ms")
    a = ap.parse_args()
    if a.src:
        summarise(a.src, a.top)
        return 0
    if not a.file:
        ap.error("give a file or --from")
    out = a.out or f"/tmp/{a.file.removesuffix('.lean').replace('/', '.')}.profile.json"
    if os.path.exists(out):
        os.remove(out)  # never summarise a previous run's profile
    start = time.monotonic()
    run = subprocess.run(["lake", "lean", a.file, "--", "-Dtrace.profiler=true",
                          f"-Dtrace.profiler.threshold={a.threshold}",
                          f"-Dtrace.profiler.output={out}", "-Dtrace.profiler.output.pp=true"])
    wall = time.monotonic() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024 ** 2
    print(f"{a.file}: {wall:.1f} s wall, peak RSS {rss:.2f} GiB, lean exit {run.returncode}")
    print(f"profile: {out}")
    if run.returncode != 0 or not os.path.exists(out):
        print("no profile summary: lean failed (its messages are above)", file=sys.stderr)
        return run.returncode or 1
    summarise(out, a.top)
    return 0


if __name__ == "__main__":
    sys.exit(main())
