#!/usr/bin/env python3
"""Baseline metrics of the module graph (foundation plan §11 step 1). Report-only: check.sh step 13 prints its totals.

Reports, as Markdown on stdout: the layer of every module (the [[layer]] matrix of scripts/boundaries.toml),
import depth, downstream cones, `@[expose]` and import-kind counts, lines, and (with --timings) a build
profile from Lake's per-module times. Exit 1 if a module of a checked library maps to no layer or the inputs
cannot be read; exit 0 otherwise. Nothing here gates anything (scripts/check-boundaries.py does).

Modules are those of the lakefile targets: every file matched by a lean_lib's globs (default: its roots;
under its srcDir) or a lean_exe's root, plus every project file they import (Lake builds exactly these).
Files that only check.sh compiles directly (scripts/fixtures/*.lean outside CheckFixtures) are not
modules of a target and are not counted. Imports come from the pinned
Lean parser (`lake env lean --deps-json`, header only, no build), as in check-boundaries.py. The implicit
`Init` import is not counted.

Usage: python3 -I scripts/metrics-baseline.py [--config scripts/boundaries.toml] [--timings <lake build -v log>]
                                              [--json <out.json>] [--no-modules]
"""
import argparse, json, re, statistics, subprocess, sys, tomllib
from collections import defaultdict
from pathlib import Path

def under(m, prefix):  # component-wise module prefix: A covers A and A.x, not AB
    return m == prefix or m.startswith(prefix + ".")

def inventory(tree, lake):
    """module -> (target name, file, default?) for every module of the lakefile targets."""
    default = set(lake.get("defaultTargets", []))
    srcdirs, seeds = set(), []
    for lib in lake.get("lean_lib", []):
        src = tree / lib.get("srcDir", ".")
        srcdirs.add(src)
        roots = lib.get("roots", [lib["name"]])
        globs = lib.get("globs", roots)
        for g in globs:
            stem = g[:-2] if g.endswith((".*", ".+")) else g
            base = src / stem.replace(".", "/")
            if not g.endswith(".+") and base.with_suffix(".lean").is_file():
                seeds.append((stem, base.with_suffix(".lean"), lib["name"]))
            if g.endswith((".*", ".+")) and base.is_dir():
                for p in sorted(base.rglob("*.lean")):
                    seeds.append((".".join(p.relative_to(src).with_suffix("").parts), p, lib["name"]))
    for exe in lake.get("lean_exe", []):
        src = tree / exe.get("srcDir", ".")
        srcdirs.add(src)
        r = exe.get("root", exe["name"])
        seeds.append((r, src / (r.replace(".", "/") + ".lean"), exe["name"]))
    mods = {}
    for m, p, t in seeds:
        mods.setdefault(m, (t, p, t in default))
    return mods, sorted(srcdirs, key=lambda d: -len(d.parts))

def resolve(m, srcdirs):  # the project file of module m, if any
    for d in srcdirs:
        p = d / (m.replace(".", "/") + ".lean")
        if p.is_file():
            return p
    return None

def deps_json(tree, files):
    res = subprocess.run(["lake", "env", "lean", "--deps-json", *(str(f.relative_to(tree)) for f in files)],
                         capture_output=True, text=True, cwd=tree)
    if res.returncode != 0:
        sys.exit(f"FAIL lean --deps-json exited {res.returncode}: {res.stderr.strip()}")
    out = json.loads(res.stdout)["imports"]
    if len(out) != len(files):
        sys.exit("FAIL lean --deps-json returned a different number of results")
    return out

def load_graph(tree, lake):
    mods, srcdirs = inventory(tree, lake)
    imports, kinds, todo = {}, {}, sorted(mods)
    while todo:  # parse, then add project files reached by imports (owned by the importer's target)
        res = deps_json(tree, [mods[m][1] for m in todo])
        new = []
        for m, r in zip(todo, res):
            if r.get("errors") or "result" not in r:
                sys.exit(f"FAIL lean --deps-json: {mods[m][1]}: {r.get('errors')}")
            imps = [i for i in r["result"]["imports"] if i["module"] != "Init"]
            imports[m] = sorted({i["module"] for i in imps})
            kinds[m] = imps
            for i in imports[m]:
                if i not in mods and (p := resolve(i, srcdirs)) is not None:
                    mods[i] = (mods[m][0], p, mods[m][2])
                    new.append(i)
        todo = sorted(set(new))
    local = {m: [i for i in imports[m] if i in mods] for m in mods}
    return mods, local, kinds

def assign_layers(mods, cfg):
    """module -> layer of scripts/boundaries.toml (prefixes never overlap; check-boundaries.py validates the
    file). A generated library root is `Aggregate`; a module of a target outside the checked libraries
    (fixtures, the challenge, the check-decls tool) is `(<target>)`."""
    fails, layer = [], {}
    roots = {l["name"] for l in cfg.get("lib", []) if l.get("root_lists_all") is True}
    checked = {l["name"] for l in cfg.get("lib", [])}
    owner = {p: l["name"] for l in cfg.get("layer", []) for p in l.get("prefixes", [])}
    for m in mods:
        hit = [o for p, o in owner.items() if under(m, p)]
        if m in roots:
            layer[m] = "Aggregate"
        elif hit:
            layer[m] = hit[0]
        elif mods[m][0] in checked:
            fails.append(f"FAIL[unmapped] {m} ({mods[m][1]}) maps to no layer")
        else:
            layer[m] = f"({mods[m][0]})"
    return layer, fails

def milestones(cfg):
    """milestone layer -> its entry module `<parent>.<M>.Main` (boundaries.toml `milestone_parents`)."""
    out = {}
    for l in cfg.get("layer", []):
        for p in l.get("prefixes", []):
            if any(under(p, P) and p.count(".") == P.count(".") + 1 for P in cfg.get("milestone_parents", [])):
                out[l["name"]] = p + ".Main"
    return out

def closures(nodes, edges):
    """Reflexive-free transitive closure along `edges` (node -> list of nodes), restricted to `nodes`."""
    memo = {}
    def go(m):
        if m not in memo:
            s = set()
            for i in edges.get(m, []):
                if i in nodes:
                    s.add(i); s |= go(i)
            memo[m] = s
        return memo[m]
    sys.setrecursionlimit(10000)
    return {m: go(m) for m in nodes}

def longest(nodes, local, weight):
    """Longest path downward (through imports) ending at each node: (total weight, path top-first)."""
    memo = {}
    def go(m):
        if m not in memo:
            best = (0.0, [])
            for i in local[m]:
                if i in nodes:
                    best = max(best, go(i), key=lambda x: x[0])
            memo[m] = (best[0] + weight(m), [m] + best[1])
        return memo[m]
    return {m: go(m) for m in nodes}

TIME = re.compile(r"Built (\S+)(?: \(([\d.]+)(ms|s)\))?")

def read_timings(path):
    t = {}
    for line in Path(path).read_text(errors="replace").splitlines():
        if (mm := TIME.search(line)) and mm.group(2):
            secs = float(mm.group(2)) / (1000 if mm.group(3) == "ms" else 1)
            t[mm.group(1)] = t.get(mm.group(1), 0.0) + secs
    return t

def file_counts(p):
    text = p.read_text()
    lines = text.count("\n")
    return {
        "lines": lines,
        "module": bool(re.search(r"^module\b", text, re.M)),
        "expose_section": len(re.findall(r"^@\[expose\]\s+public\s+section\b", text, re.M)),
        "expose_other": len(re.findall(r"@\[(?:[^\]]*,\s*)?expose\b", text)) - len(
            re.findall(r"^@\[expose\]\s+public\s+section\b", text, re.M)),
        "public_section": len(re.findall(r"^(?:@\[[^\]]*\]\s+)?public\s+section\b", text, re.M)),
    }

def import_kinds(imps, mods, is_module):
    c = defaultdict(int)
    for i in imps:  # in a non-`module` file every import is exported: counted as `legacy`, not public
        loc = "local" if i["module"] in mods else "ext"
        k = ("legacy" if not is_module else "all" if i["importAll"] else "meta" if i["isMeta"]
             else "public" if i["isExported"] else "plain")
        c[f"{k}_{loc}"] += 1
        if i["module"] == "Mathlib":
            c["import_mathlib"] += 1
    return c

def table(rows, head):
    out = ["| " + " | ".join(head) + " |", "|" + "|".join("---" for _ in head) + "|"]
    out += ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]
    return "\n".join(out)

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tree", default=".")
    ap.add_argument("--lakefile", default="lakefile.toml")
    ap.add_argument("--config", default="scripts/boundaries.toml")
    ap.add_argument("--timings", help="output of `lake build -v` (lines `Built <Module> (<t>s)`)")
    ap.add_argument("--json", help="also write every per-module number as JSON here")
    ap.add_argument("--no-modules", action="store_true", help="omit the per-module table")
    a = ap.parse_args()
    tree = Path(a.tree)
    try:
        lake = tomllib.loads((tree / a.lakefile).read_text())
        cfg = tomllib.loads((tree / a.config).read_text())
    except (OSError, tomllib.TOMLDecodeError) as e:
        sys.exit(f"FAIL[config] {e}")
    mods, local, kinds = load_graph(tree, lake)
    layer, fails = assign_layers(mods, cfg)
    rev = defaultdict(list)
    for m in mods:
        for i in local[m]:
            rev[i].append(m)
    up = closures(set(mods), local)            # what m imports, transitively
    seeds = {m for m in mods if mods[m][2]}    # modules of a default target ...
    deflt = seeds.union(*(up[m] for m in seeds))  # ... and everything they import (Lake builds it too)
    down = closures(deflt, rev)                # default-target modules that import m, transitively
    depth = {m: (int(w), path) for m, (w, path) in longest(set(mods), local, lambda m: 1).items()}
    fc = {m: file_counts(mods[m][1]) for m in mods}
    ik = {m: import_kinds(kinds[m], mods, fc[m]["module"]) for m in mods}
    try:
        times = read_timings(a.timings) if a.timings else {}
    except OSError as e:
        sys.exit(f"FAIL[config] --timings: {e}")
    if a.timings and not any(m in mods for m in times):
        sys.exit(f"FAIL[config] --timings {a.timings}: no `Built <module> (<time>)` line for a project module "
                 "(a cold `lake build -v` log is expected)")
    ms_cfg = milestones(cfg)
    used_by = {m: sorted(k for k, top in ms_cfg.items() if top in mods and (m == top or m in up[top])) for m in mods}

    p = print
    p("# Module metrics (scripts/metrics-baseline.py; report-only)\n")
    nd = len(deflt)
    p(f"Modules: {len(mods)} in lakefile targets, {nd} in the default targets "
      f"({', '.join(lake.get('defaultTargets', []))}).\n")
    # per layer
    order = [l["name"] for l in cfg.get("layer", [])] + ["Aggregate"]
    rows = []
    for L in order + sorted({*layer.values()} - set(order)):
        ms = [m for m in mods if layer.get(m) == L]
        if not ms:
            continue
        def s(k): return sum(fc[m][k] for m in ms)
        def si(k): return sum(ik[m][k] for m in ms)
        cones = [len(down[m]) for m in ms if m in deflt]
        rows.append([L, len(ms), s("lines"), max(depth[m][0] for m in ms) - 1,
                     max(cones) if cones else "-", s("expose_section"), s("expose_other"),
                     si("public_local") + si("public_ext"), si("plain_local") + si("plain_ext"),
                     si("meta_local") + si("meta_ext"), si("all_local") + si("all_ext"),
                     f"{sum(times.get(m, 0) for m in ms):.1f}" if any(m in times for m in ms) else "-"])
    p("## Per target layer\n")
    p(table(rows, ["layer", "modules", "lines", "max depth", "max cone", "`@[expose]` sections",
                   "other `@[expose]`", "public imports", "plain imports", "meta imports", "`import all`",
                   "build s"]))
    # totals
    allk = defaultdict(int)
    for m in mods:
        for k, v in ik[m].items():
            allk[k] += v
    nmod = sum(fc[m]["module"] for m in mods)
    p("\n## Totals\n")
    top = max(sorted(mods), key=lambda m: depth[m][0])
    p(f"- Depth (longest chain of project imports, in edges): max {depth[top][0] - 1}, "
      f"`{' -> '.join(depth[top][1])}`.")
    dd = [depth[m][0] - 1 for m in deflt]
    p(f"- Depth over the default targets: max {max(dd)}, median {statistics.median(dd):g}.")
    deflibs = {l["name"] for l in cfg.get("lib", []) if l.get("default") is True}
    libm = {m for m in mods if mods[m][0] in deflibs and layer.get(m) != "Aggregate"}
    def expand(i, acc, seen):  # an import of an aggregate counts as importing what the aggregate imports
        for j in local[i]:
            if j not in seen:
                seen.add(j)
                (expand(j, acc, seen) if layer.get(j) == "Aggregate" else acc.add(j))
    contracted = {}
    for m in libm:
        acc = set(); expand(m, acc, set()); contracted[m] = sorted(acc)
    if libm:
        ld = longest(libm, contracted, lambda m: 1)
        lt = max(sorted(libm), key=lambda m: ld[m][0])
        p(f"- Library depth (the default libraries without their roots; an aggregate import counts as its imports): "
          f"max {int(ld[lt][0]) - 1}, `{' -> '.join(ld[lt][1])}`.")
    cs = sorted(((len(down[m]), m) for m in deflt), reverse=True)
    p(f"- Downstream cone (default-target modules that import the module, transitively; {nd} = 100%): "
      f"max {cs[0][0]} ({100 * cs[0][0] / nd:.0f}%, `{cs[0][1]}`), median {statistics.median(c for c, _ in cs):g}, "
      f"{sum(c > 0.15 * nd for c, _ in cs)} modules above 15%.")
    p(f"- `module` files: {nmod}/{len(mods)}. Whole-file `@[expose] public section`: "
      f"{sum(fc[m]['expose_section'] for m in mods)}; other `@[expose]`: {sum(fc[m]['expose_other'] for m in mods)}; "
      f"`public section` (any): {sum(fc[m]['public_section'] for m in mods)}.")
    p(f"- Imports of project modules: {allk['public_local']} public, {allk['plain_local']} plain, "
      f"{allk['meta_local']} meta, {allk['all_local']} `import all`. External imports: {allk['public_ext']} public, "
      f"{allk['plain_ext']} plain, {allk['meta_ext']} meta, {allk['all_ext']} `import all`; "
      f"`import Mathlib`: {allk['import_mathlib']}. Imports in non-`module` files (not counted above): "
      f"{allk['legacy_local'] + allk['legacy_ext']}.")
    ext = sorted({i["module"] for m in mods for i in kinds[m] if i["module"] not in mods})
    p(f"- Distinct external modules imported directly: {len(ext)}.")
    agg = [m for m in mods if layer.get(m) == "Aggregate"]
    agg_in = sorted({(m, i) for m in mods for i in local[m] if layer.get(i) == "Aggregate" and layer.get(m) != "Aggregate"})
    p(f"- Import-only aggregates (layer Aggregate): {len(agg)}; imports of an aggregate by another layer: {len(agg_in)} "
      f"(from {len({m for m, _ in agg_in})} modules).")
    edges = defaultdict(list)
    for m in mods:
        for i in local[m]:
            if layer.get(m) != layer.get(i):
                edges[(layer.get(m, "?"), layer.get(i, "?"))].append(f"`{m}` -> `{i}`")
    p("\nDirect imports between distinct layers (from -> to: count; up to two examples):\n")
    p(table([[a_, b_, len(v), "; ".join(sorted(v)[:2])] for (a_, b_), v in
             sorted(edges.items(), key=lambda kv: (order.index(kv[0][0]) if kv[0][0] in order else 99, kv[0][1]))],
            ["from", "to", "imports", "examples"]))
    p("\nLargest downstream cones (default targets):\n")
    p(table([[f"`{m}`", layer.get(m, "?"), c, f"{100 * c / nd:.0f}%"] for c, m in cs[:12]],
            ["module", "layer", "cone", "share"]))
    # profile
    if times:
        built = {m for m in mods if m in times}
        crit = longest(built, local, lambda m: times[m])
        ctop = max(sorted(built), key=lambda m: crit[m][0])
        p("\n## Build profile (from --timings)\n")
        p(f"- Project modules with a time: {len(built)}/{len(mods)}; sum of module times {sum(times[m] for m in built):.1f} s.")
        other = {k: v for k, v in times.items() if k not in mods}
        if other:
            p(f"- Other built targets with a time (not project modules): {len(other)}, {sum(other.values()):.1f} s.")
        p(f"- Critical path (longest import chain weighted by module time): {crit[ctop][0]:.1f} s, "
          f"{len(crit[ctop][1])} modules: `{' -> '.join(crit[ctop][1])}`.")
        p("\nSlowest modules:\n")
        p(table([[f"`{m}`", layer.get(m, "?"), f"{times[m]:.1f}"] for m in sorted(built, key=lambda m: (-times[m], m))[:12]],
                ["module", "layer", "s"]))
    if not a.no_modules:
        p("\n## Every module\n")
        p("Cone: default-target modules that import it (`-`: not a default-target module). "
          "Milestones: the milestone layers of scripts/boundaries.toml whose `Main` reaches it.\n")
        rows = []
        for m in sorted(mods, key=lambda m: (order.index(layer[m]) if layer.get(m) in order else 99, m)):
            rows.append([f"`{m}`", layer.get(m, "**UNMAPPED**"), mods[m][0], fc[m]["lines"], depth[m][0] - 1,
                         len(down[m]) if m in deflt else "-",
                         ik[m]["public_local"] + ik[m]["public_ext"], ik[m]["plain_local"] + ik[m]["plain_ext"],
                         fc[m]["expose_section"] + fc[m]["expose_other"],
                         f"{times[m]:.1f}" if m in times else "-", ", ".join(used_by[m]) or "-"])
        p(table(rows, ["module", "layer", "target", "lines", "depth", "cone", "public imp", "plain imp",
                       "expose", "build s", "milestones"]))
    if a.json:
        Path(a.json).write_text(json.dumps({m: {
            "layer": layer.get(m), "target": mods[m][0], "default": m in deflt, "file": str(mods[m][1]),
            "depth": depth[m][0] - 1, "cone": len(down[m]) if m in deflt else None, "imports": local[m],
            "import_kinds": dict(ik[m]), **fc[m], "build_s": times.get(m), "milestones": used_by[m]}
            for m in sorted(mods)}, indent=1) + "\n")
    if fails:
        p("\n## Failures\n")
        for f in fails:
            p(f"- {f}")
        print("\n".join(fails), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
