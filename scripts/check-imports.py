#!/usr/bin/env python3
"""Import discipline of every default library (rules R1-R3 of the plan, as configured).

Port of verified-consensus scripts/check-review-boundary.rb (CC0-1.0). Imports come from the pinned
Lean parser (`lean --deps-json`), never from source text. Run as `python3 -I scripts/check-imports.py`.
Configuration: scripts/boundaries.toml (`base`, `fixture_libs`, `tool_exes`, one `[[lib]]` per default library).
Every lakefile target is a configured library, a fixture library or a tool, and no project module, file or
directory takes a top-level name of the base set (it would pass every check as a dependency module).
Failures carry stable tags: FAIL[import] FAIL[base] FAIL[root] FAIL[root-import] FAIL[fixture] FAIL[config].
"""
import argparse, json, subprocess, sys, tomllib
from pathlib import Path

def under(m, prefix):  # module-name prefix, component-wise: A covers A and A.x, not AB
    return m == prefix or m.startswith(prefix + ".")

def lib_prefixes(lake_lib):  # module prefixes a lakefile lib owns (its roots, glob stems and one-module globs)
    globs = [g[:-2] if g.endswith((".*", ".+")) else g for g in lake_lib.get("globs", [])]
    return lake_lib.get("roots", [lake_lib["name"]]) + globs

def check(tree, cfg_path, lakefile, inventory_out=None, graph_out=None):
    tree = Path(tree)
    cfg = tomllib.loads(Path(cfg_path).read_text())
    lake = tomllib.loads(Path(lakefile).read_text())
    fails = []
    libs = cfg.get("lib", [])
    base = set(cfg.get("base", []))
    lake_libs = {l["name"]: l for l in lake.get("lean_lib", [])}
    names = [l["name"] for l in libs]
    if (tree / "lakefile.lean").exists():
        fails.append("FAIL[config] lakefile.lean exists: Lake would use it instead of lakefile.toml")
    for k, v in lake.items():  # targets: only lean_lib/lean_exe, each one known
        if k not in ("lean_lib", "lean_exe", "require") and isinstance(v, list) and any(isinstance(x, dict) for x in v):
            fails.append(f"FAIL[config] target: lakefile table [[{k}]] is not supported")
    exes = lake.get("lean_exe", [])
    known = set(names) | set(cfg.get("fixture_libs", [])) | set(cfg.get("tool_exes", []))
    for t in list(lake_libs.values()) + exes:
        if t["name"] not in known:
            fails.append(f"FAIL[config] target: lakefile target {t['name']} is not a configured lib, fixture lib or tool")
    stems = [p for t in lake_libs.values() for p in lib_prefixes(t)] + [e.get("root", e["name"]) for e in exes]
    tops = [p.name.removesuffix(".lean") for d in {tree} | {tree / t["srcDir"] for t in list(lake_libs.values()) + exes
            if "srcDir" in t} if d.is_dir() for p in d.iterdir()]
    for x in sorted({m.split(".")[0] for m in stems} | set(tops)):
        if x in base:
            fails.append(f"FAIL[config] base name: {x} is a project module prefix, file or directory")
    if not libs or sorted(lake.get("defaultTargets", [])) != sorted(names):
        fails.append(f"FAIL[config] defaultTargets {lake.get('defaultTargets')} != configured libs {names}")
    if lake.get("srcDir", ".") not in (".", "./"):
        fails.append(f"FAIL[config] package srcDir {lake['srcDir']!r}: sources are audited relative to the root")
    fixture_pfx = []
    for f in cfg.get("fixture_libs", []):
        if f not in lake_libs:
            fails.append(f"FAIL[config] fixture lib {f} not in the lakefile")
        else:
            fixture_pfx += lib_prefixes(lake_libs[f])
    inv = {}  # lib name -> list of (module, file)
    for l in libs:
        n, root = l["name"], l["root"]
        ll = lake_libs.get(n, {})
        if "srcDir" in ll:
            fails.append(f"FAIL[config] {n}: a default library may not set srcDir")
        if l.get("root_covers") is not True:
            fails.append(f"FAIL[config] {n}: root_covers must be true")
        if not ((ll.get("globs") == [f"{root}.*"] and ll.get("roots", [n]) == [root])
                or (ll.get("globs") == [f"{root}.+"] and ll.get("roots") == [root])):
            fails.append(f"FAIL[config] {n}: lakefile globs/roots are not exactly [{root}.*] (or roots=[{root}] + [{root}.+])")
        rootfile, d = tree / f"{root.replace('.', '/')}.lean", tree / root.replace(".", "/")
        if l.get("dir") != root.replace(".", "/") or not rootfile.is_file():
            fails.append(f"FAIL[config] {n}: dir must be {root.replace('.', '/')} and {rootfile} must exist")
            inv[n] = []
            continue
        sub = sorted(d.rglob("*.lean")) if d.is_dir() else []
        inv[n] = mods = [(root, rootfile)] + [(".".join(p.relative_to(tree).with_suffix("").parts), p) for p in sub]
        for m, _ in mods:
            if {"Proofs", "Exports"} & set(m.split(".")):
                fails.append(f"FAIL[config] {m}: a component named Proofs/Exports is exempt in check-decls")
    files = [str(p) for mods in inv.values() for _, p in mods]
    if not files:
        return fails + ["FAIL[config] no modules"]
    res = subprocess.run(["lake", "env", "lean", "--deps-json", *files], capture_output=True, text=True)
    if res.returncode != 0:
        return fails + [f"FAIL[config] lean --deps-json exited {res.returncode}: {res.stderr.strip()}"]
    results = json.loads(res.stdout)["imports"]
    if len(results) != len(files):
        return fails + ["FAIL[config] lean --deps-json returned a different number of results"]
    imports = {}
    for f, r in zip(files, results):
        if r.get("errors") or "result" not in r:
            return fails + [f"FAIL[config] lean --deps-json: {f}: {r.get('errors')}"]
        mod = next(m for mods in inv.values() for m, p in mods if str(p) == f)
        imports[mod] = sorted({i["module"] for i in r["result"]["imports"]})
    owner = {m: n for n, mods in inv.items() for m, _ in mods}
    if graph_out:  # `lib<TAB>module<TAB>import` per direct import (`-` for none): check.sh --changed's cone
        with open(graph_out, "w") as out:
            for m, n in owner.items():
                for i in imports[m] or ["-"]:
                    out.write(f"{n}\t{m}\t{i}\n")
    roots = {l["root"] for l in libs}
    for l in libs:
        n = l["name"]
        allow = l.get("allow", [])
        for start, _ in inv[n]:
            path, seen, todo = {start: [start]}, {start}, [start]
            while todo:
                m = todo.pop()
                for i in imports[m]:
                    if any(under(i, p) for p in fixture_pfx):
                        fails.append(f"FAIL[fixture] {i} reached from {' -> '.join(path[m])}")
                    elif i in owner:
                        if not any(under(i, p) for p in allow):
                            fails.append(f"FAIL[import] {i} reached from {' -> '.join(path[m])} (lib {n})")
                        elif i not in seen:
                            seen.add(i); path[i] = path[m] + [i]; todo.append(i)
                    elif i.split(".")[0] not in base:
                        fails.append(f"FAIL[base] {i} imported by {m}")
            if start == l["root"]:
                for m, p in inv[n]:
                    if m not in seen:
                        fails.append(f"FAIL[root] {p} is not reached from {start}")
        if not l.get("may_import_roots", False):
            for m, _ in inv[n]:
                for i in imports[m]:
                    if m != l["root"] and i in roots:
                        fails.append(f"FAIL[root-import] {m} imports {i}")
    if inventory_out:
        with open(inventory_out, "w") as out:
            for n, mods in inv.items():
                for m, _ in mods:
                    kind = "parent" if any(under(o, m) and o != m for o, _ in mods) else "leaf"
                    out.write(f"{n}\t{m}\t{kind}\n")
    return sorted(set(fails), key=fails.index)

CASES = {  # scripts/fixtures/imports/<case>: expected tag (None = must pass)
    "Good": None, "BadImport": "FAIL[import]", "RootImport": "FAIL[import]", "Orphan": "FAIL[root]",
    "OrphanProofs": "FAIL[root]", "ChildImportsRoot": "FAIL[root-import]", "UnknownTop": "FAIL[base]",
    "FixtureImport": "FAIL[fixture]", "NoRootCovers": "FAIL[config]", "EmptyLib": "FAIL[config]",
    "LibMismatch": "FAIL[config]", "ProofsComponent": "FAIL[config]",
    "LakefileLean": "FAIL[config] lakefile.lean", "ShadowBase": "FAIL[config] base name",
    "ShadowGlob": "FAIL[config] base name", "ShadowTop": "FAIL[config] base name",
    "UnknownTarget": "FAIL[config] target",
}

def self_test(fixtures):
    ok = True
    assert under("A.B", "A") and under("A", "A") and not under("AB", "A") and not under("A", "A.B")
    assert lib_prefixes({"name": "F", "roots": [], "globs": ["F.+"]}) == ["F"]
    assert lib_prefixes({"name": "L", "globs": ["L.*"]}) == ["L", "L"]
    assert lib_prefixes({"name": "S", "roots": [], "globs": ["M.S"]}) == ["M.S"]
    for case, tag in CASES.items():
        d = Path(fixtures) / case
        fails = check(d, d / "boundaries.toml", d / "lakefile.toml")
        good = (not fails) if tag is None else any(f.startswith(tag) for f in fails)
        print(f"{'ok  ' if good else 'FAIL'} self-test {case}: expected {tag or 'pass'}, got {fails or 'pass'}")
        ok &= good
    return ok

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default="scripts/boundaries.toml")
    ap.add_argument("--lakefile", default="lakefile.toml")
    ap.add_argument("--tree", default=".")
    ap.add_argument("--inventory-out")
    ap.add_argument("--graph-out", help="write the import graph of the default libraries (lib, module, import)")
    ap.add_argument("--self-test", metavar="FIXTURES_DIR", nargs="?", const="scripts/fixtures/imports")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(0 if self_test(a.self_test) else 1)
    fails = check(a.tree, a.config, a.lakefile, a.inventory_out, a.graph_out)
    for f in fails:
        print(f)
    print(f"check-imports: {'FAILED' if fails else 'passed'} ({len(fails)} findings)")
    sys.exit(1 if fails else 0)
