#!/usr/bin/env python3
"""Per-module build cost, each module elaborated on its own. Report-only.

Runs `lean` on each module with the `.setup.json` Lake wrote for it (same options and imports as
`lake build`, outputs to a scratch directory), so the imports must be built first. Prints a TSV
(module, wall s, CPU s, peak RSS MB, exit code) with a JSON header recording the commit, CPU model,
CPU count and job count. With `--jobs 1` (the default) each module runs alone. For a before/after
comparison, use the same machine, toolchain, build options and job count, without competing builds.
The CPU facts do not identify a physical machine: the caller must still ensure that the runs are
comparable. Interleave base/new runs and take the best of two rounds (docs/build-speed.md).

Exits 1 when the run is incomplete: no module to time, or a module whose run exits nonzero (for
example, unbuilt imports or stale `.setup.json`). Failed rows are written with their exit code.

`--compare TABLE` reads an earlier table and compares only rows whose exit column is exactly 0.
After timing, it lists modules whose CPU time grew by more than 25% and more than 1 s, and exits 2
if there is one. A missing or mismatched CPU/job header is refused unless the caller explicitly
overrides it with `--same-machine`. If no successful baseline row matches, the comparison is
incomplete (exit 1). Generate the baseline with `-o base.tsv`; no baseline table ships in the repo.

Usage: python3 -I scripts/time-modules.py [-o out.tsv] [-j N] [--repo DIR] [--compare TABLE] [MODULE ...]
       (no MODULE: every module of the default library that Lake has built)
"""
import argparse, json, os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("-o", "--out", help="TSV output (default: stdout)")
    ap.add_argument("-j", "--jobs", type=int, default=1)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--compare", help="earlier table: report modules whose CPU grew > 25%% and > 1 s")
    ap.add_argument("--same-machine", action="store_true",
                    help="override missing/mismatched baseline provenance after checking comparability")
    ap.add_argument("modules", nargs="*")
    a = ap.parse_args()
    repo = os.path.abspath(a.repo)
    ir = os.path.join(repo, ".lake/build/ir")
    lean = os.path.join(subprocess.check_output(["lean", "--print-prefix"], text=True, cwd=repo).strip(),
                        "bin", "lean")
    mods = a.modules or sorted(
        os.path.relpath(os.path.join(d, f), ir)[: -len(".setup.json")].replace("/", ".")
        for d, _, fs in os.walk(os.path.join(ir, "ConsensusLean")) for f in fs if f.endswith(".setup.json"))
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True,
                            cwd=repo).stdout.strip()
    dirty = subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=repo).returncode != 0
    with open("/proc/cpuinfo") as cpuinfo:
        cpu_model = next((line.split(":", 1)[1].strip() for line in cpuinfo
                          if line.startswith("model name")), "unknown")
    provenance = {"commit": commit + (" (dirty)" if dirty else ""), "cpu_model": cpu_model,
                  "cpus": os.cpu_count(), "jobs": a.jobs}
    old = {}
    if a.compare:
        with open(a.compare) as baseline:
            header = baseline.readline()
            try:
                previous = json.loads(header.removeprefix("# "))
            except json.JSONDecodeError:
                previous = None
            compatible = (isinstance(previous, dict) and cpu_model != "unknown"
                          and all(previous.get(k) == provenance[k] for k in ("cpu_model", "cpus", "jobs")))
            if not compatible:
                if not a.same_machine:
                    print("time-modules: INCOMPLETE: missing/mismatched baseline provenance; "
                          "use --same-machine only after checking comparability", file=sys.stderr)
                    return 1
                print("WARNING: overriding baseline provenance with --same-machine", file=sys.stderr)
            for line in baseline:
                p = line.rstrip("\n").split("\t")
                if line.startswith("#") or p[0] == "module" or len(p) != 5 or p[4] != "0":
                    continue
                old[p[0]] = float(p[2])
    scratch = tempfile.mkdtemp(prefix="time-modules-")

    def run(m):
        rel = m.replace(".", "/")
        setup = os.path.join(ir, rel + ".setup.json")
        if not os.path.exists(setup):
            return m, 0.0, 0.0, 0.0, "unbuilt"
        out = os.path.join(scratch, m)
        start = time.monotonic()
        p = subprocess.Popen([lean, os.path.join(repo, rel + ".lean"), "--setup", setup, "-o", out + ".olean",
                              "-i", out + ".ilean", "-c", out + ".c"], cwd=repo,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        _, status, ru = os.wait4(p.pid, 0)
        wall = time.monotonic() - start
        return m, wall, ru.ru_utime + ru.ru_stime, ru.ru_maxrss / 1024, str(os.waitstatus_to_exitcode(status))

    fo = open(a.out, "w") if a.out else sys.stdout
    fo.write(f"# {json.dumps(provenance, sort_keys=True)}\n")
    fo.write("module\twall_s\tcpu_s\trss_mb\texit\n")
    new, failed = {}, []
    try:
        if not mods:
            print("time-modules: INCOMPLETE: no module to time (is the library built?)", file=sys.stderr)
            return 1
        with ThreadPoolExecutor(a.jobs) as ex:
            for i, (m, w, c, r, rc) in enumerate(ex.map(run, mods)):
                if rc != "0":
                    failed.append(m)
                    print(f"FAILED {m}: exit {rc}; its time is not a build time (stale .setup.json? "
                          "run `lake build` first)", file=sys.stderr)
                else:
                    new[m] = c
                fo.write(f"{m}\t{w:.2f}\t{c:.2f}\t{r:.0f}\t{rc}\n")
                fo.flush()
                if a.out:
                    print(f"[{i + 1}/{len(mods)}] {m} {w:.1f} s", file=sys.stderr)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
        if a.out:
            fo.close()
    print(f"time-modules: {len(new)} modules timed, {len(failed)} failed", file=sys.stderr)
    if failed:
        print("time-modules: INCOMPLETE: the failed modules have no valid time", file=sys.stderr)
        return 1
    if a.compare:
        common = set(new) & set(old)
        if not common:
            print("time-modules: INCOMPLETE: no matching exit-0 baseline rows", file=sys.stderr)
            return 1
        print(f"compared with {a.compare}", file=sys.stderr)
        slower = sorted((new[m] - old[m], m) for m in common
                        if new[m] > 1.25 * old[m] and new[m] - old[m] > 1.0)
        for d, m in reversed(slower):
            print(f"SLOWER {m}: CPU {old[m]:.1f} -> {new[m]:.1f} s (+{d:.1f} s)", file=sys.stderr)
        print(f"time-modules: {len(slower)} of {len(common)} modules slower", file=sys.stderr)
        return 2 if slower else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
