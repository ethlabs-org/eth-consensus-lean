#!/usr/bin/env python3
"""Import discipline of the checked libraries (plan §1: one certified library, layers as module prefixes).

Port of verified-consensus scripts/check-review-boundary.rb (CC0-1.0). Imports come from the pinned
Lean parser (`lean --deps-json`), never from source text. Run as `python3 -I scripts/check-imports.py`.
Configuration: scripts/boundaries.toml (`base`, `fixture_libs`, `tool_exes`, `[[lib]]`, `[[group]]`,
`[checks].proofs_component_prefixes`).

* Every lakefile target is a configured lib, a fixture lib or a tool; `defaultTargets` is exactly the libs
  with `default = true`, `testDriver` the lib with `test_driver = true`. No project module, file or
  directory takes a top-level name of the base set (it would pass every check as a dependency module).
* A lib's root module is its name. With `root_lists_all`, the lib is the root plus every file under its
  directory (lakefile globs exactly `[<name>.*]`), and the root (generated, `lake exe mk_all`) imports
  exactly every other module of the lib: an unlisted file fails. Otherwise the lib is the root alone.
* Every module except a `root_lists_all` root is in exactly one `[[group]]` (longest component-wise
  prefix). The import closure of a module holds only modules of its own group, of the groups in its
  `allow`, and base modules; no fixture module; and a `root_lists_all` root only in a group with
  `may_import_roots` (the tests). A module named with a `Proofs` component (check-decls exempts its
  definitions from the reaches-opaque check) must be under `proofs_component_prefixes` and in a group
  that no `trusted` group may reach; an `Exports` component (exempt there too) is refused.
* `[checks].trusted_paths` (CI's review-boundary list) holds plain relative paths only (no git pathspec
  magic, glob or `..`), and covers the file of every module of a `trusted` group.
Failures carry stable tags: FAIL[import] FAIL[base] FAIL[root] FAIL[root-import] FAIL[fixture] FAIL[config].
"""
import argparse, json, re, subprocess, sys, tomllib
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
    libs, groups = cfg.get("lib", []), cfg.get("group", [])
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
    defaults = [l["name"] for l in libs if l.get("default") is True]
    if not libs or not defaults or sorted(lake.get("defaultTargets", [])) != sorted(defaults):
        fails.append(f"FAIL[config] defaultTargets {lake.get('defaultTargets')} != configured default libs {defaults}")
    drivers = [l["name"] for l in libs if l.get("test_driver") is True]
    if len(drivers) > 1 or lake.get("testDriver") != (drivers[0] if drivers else None):
        fails.append(f"FAIL[config] testDriver {lake.get('testDriver')!r} != configured test_driver lib {drivers}")
    if lake.get("srcDir", ".") not in (".", "./"):
        fails.append(f"FAIL[config] package srcDir {lake['srcDir']!r}: sources are audited relative to the root")
    fixture_pfx = []
    for f in cfg.get("fixture_libs", []):
        if f not in lake_libs:
            fails.append(f"FAIL[config] fixture lib {f} not in the lakefile")
        else:
            fixture_pfx += lib_prefixes(lake_libs[f])
    # groups: unique names, known allow entries, no prefix in two groups
    gnames = [g.get("name") for g in groups]
    if not groups or len(set(gnames)) != len(gnames) or None in gnames:
        fails.append(f"FAIL[config] groups: missing, unnamed or duplicate names {gnames}")
    gby = {g["name"]: g for g in groups if "name" in g}
    seen_pfx = {}
    for g in groups:
        if not g.get("prefixes"):
            fails.append(f"FAIL[config] group {g.get('name')}: no prefixes")
        for a in g.get("allow", []):
            if a not in gby or a == g.get("name"):
                fails.append(f"FAIL[config] group {g.get('name')}: allow entry {a} is not another group")
        for p in g.get("prefixes", []):
            if p in seen_pfx:
                fails.append(f"FAIL[config] prefix {p} is in groups {seen_pfx[p]} and {g.get('name')}")
            seen_pfx[p] = g.get("name")
    def group_of(m):
        best = max((p for p in seen_pfx if under(m, p)), key=len, default=None)
        return seen_pfx[best] if best else None
    def reach(gs):  # groups reachable from gs through allow (gs included)
        out, todo = set(), list(gs)
        while todo:
            x = todo.pop()
            if x in gby and x not in out:
                out.add(x); todo += gby[x].get("allow", [])
        return out
    trusted_reach = reach([g["name"] for g in groups if g.get("trusted") is True and "name" in g])
    proofs_pfx = cfg.get("checks", {}).get("proofs_component_prefixes", [])
    for p in proofs_pfx:
        if group_of(p) in trusted_reach:
            fails.append(f"FAIL[config] proofs_component_prefixes {p} is in group {group_of(p)}, reachable from a trusted group")
    inv, aggregate = {}, set()  # lib name -> list of (module, file); aggregate = root_lists_all roots
    for l in libs:
        n = l["name"]
        ll = lake_libs.get(n)
        rootfile, d = tree / f"{n.replace('.', '/')}.lean", tree / n.replace(".", "/")
        inv[n] = []
        if ll is None:
            fails.append(f"FAIL[config] {n}: not a lean_lib of the lakefile"); continue
        if "srcDir" in ll:
            fails.append(f"FAIL[config] {n}: a checked library may not set srcDir")
        if ll.get("roots", [n]) != [n]:
            fails.append(f"FAIL[config] {n}: lakefile roots must be [{n}]")
        if not rootfile.is_file():
            fails.append(f"FAIL[config] {n}: {rootfile} must exist"); continue
        if l.get("root_lists_all") is True:
            if ll.get("globs") != [f"{n}.*"]:
                fails.append(f"FAIL[config] {n}: lakefile globs are not exactly [{n}.*]")
            sub = sorted(d.rglob("*.lean")) if d.is_dir() else []
            inv[n] = [(n, rootfile)] + [(".".join(p.relative_to(tree).with_suffix("").parts), p) for p in sub]
            aggregate.add(n)
        else:
            if ll.get("globs", [n]) != [n]:
                fails.append(f"FAIL[config] {n}: a single-module lib has globs [{n}] (the default)")
            if d.exists():
                fails.append(f"FAIL[config] {n}: a single-module lib has no directory {d}")
            inv[n] = [(n, rootfile)]
    group = {}
    for n, mods in inv.items():
        for m, _ in mods:
            comps = m.split(".")
            if "Exports" in comps:
                fails.append(f"FAIL[config] {m}: a component named Exports is exempt in check-decls")
            if "Proofs" in comps and not any(under(m, p) for p in proofs_pfx):
                fails.append(f"FAIL[config] {m}: a component named Proofs (exempt in check-decls) outside proofs_component_prefixes")
            if m in aggregate:
                continue
            group[m] = group_of(m)
            if group[m] is None:
                fails.append(f"FAIL[config] {m}: in no group (boundaries.toml [[group]] prefixes)")
            elif "Proofs" in comps and group[m] in trusted_reach:
                fails.append(f"FAIL[config] {m}: a component named Proofs (exempt in check-decls) in group {group[m]}, reachable from a trusted group")
    trusted_paths = cfg.get("checks", {}).get("trusted_paths", [])
    for t in trusted_paths:
        if not (isinstance(t, str) and re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*", t)
                and ".." not in t.split("/")):
            fails.append(f"FAIL[config] trusted_paths entry {t!r}: not a plain relative path")
    for n, mods in inv.items():
        for m, p in mods:
            rel = p.relative_to(tree).as_posix()
            if group.get(m) in trusted_reach and not any(rel == t or rel.startswith(t + "/") for t in trusted_paths):
                fails.append(f"FAIL[config] {rel} (module {m}, group {group[m]}) is not covered by trusted_paths")
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
    for n in sorted(aggregate):  # the generated root imports exactly the other modules of its lib
        want = {m for m, _ in inv[n]} - {n}
        for m in sorted(want - set(imports[n])):
            fails.append(f"FAIL[root] {m} is not imported by the root {n} (regenerate: lake exe mk_all --lib {n} --module)")
        for i in sorted(set(imports[n]) - want - {"Init"}):  # `Init`: the implicit prelude import
            fails.append(f"FAIL[root] the root {n} imports {i}, not a module of {n}")
    for start, g in group.items():
        ok = ({g} | set(gby[g].get("allow", []))) if g in gby else set()
        path, seen, todo = {start: [start]}, {start}, [start]
        while todo:
            m = todo.pop()
            for i in imports[m]:
                if any(under(i, p) for p in fixture_pfx):
                    fails.append(f"FAIL[fixture] {i} reached from {' -> '.join(path[m])}")
                    continue
                if i not in owner:
                    if i.split(".")[0] not in base:
                        fails.append(f"FAIL[base] {i} imported by {m}")
                    continue
                if i in aggregate:
                    if not (g in gby and gby[g].get("may_import_roots") is True):
                        fails.append(f"FAIL[root-import] {m} imports the library root {i}" if m == start else
                                     f"FAIL[root-import] the library root {i} reached from {' -> '.join(path[m])}")
                        continue
                elif group.get(i) not in ok:
                    fails.append(f"FAIL[import] {i} (group {group.get(i)}) reached from {' -> '.join(path[m])} (group {g})")
                    continue
                if i not in seen:
                    seen.add(i); path[i] = path[m] + [i]; todo.append(i)
    if inventory_out:
        with open(inventory_out, "w") as out:
            for n, mods in inv.items():
                for m, _ in mods:
                    kind = "parent" if any(under(o, m) and o != m for o, _ in mods) else "leaf"
                    out.write(f"{n}\t{m}\t{kind}\t{group.get(m) or '-'}\n")
    return sorted(set(fails), key=fails.index)

CASES = {  # scripts/fixtures/imports/<case>: expected tag (None = must pass)
    "Good": None, "BadImport": "FAIL[import]",
    "BadImportTransitive": "FAIL[import] Fx.Impl.B (group impl) reached from Fx.Spec.A -> Fx.Spec.A2",
    "SolutionImport": "FAIL[import]", "RootImport": "FAIL[root-import]", "ChildImportsRoot": "FAIL[root-import]",
    "Orphan": "FAIL[root]", "OrphanTest": "FAIL[root]", "RootExtra": "FAIL[root]",
    "UnknownTop": "FAIL[base]", "FixtureImport": "FAIL[fixture]",
    "Unmapped": "FAIL[config] Fx.Other.D: in no group", "DupPrefix": "FAIL[config] prefix",
    "UnknownGroup": "FAIL[config] group", "EmptyLib": "FAIL[config]", "GlobMismatch": "FAIL[config] Fx: lakefile globs",
    "SingleModuleDir": "FAIL[config] FxSol: a single-module lib has no directory",
    "DefaultMismatch": "FAIL[config] defaultTargets", "TestDriverMismatch": "FAIL[config] testDriver",
    "ProofsComponent": "FAIL[config] Fx.Impl.Proofs.C", "ProofsTrusted": "FAIL[config] proofs_component_prefixes",
    "ProofsNested": "FAIL[config] Fx.Proofs.Trusted.E: a component named Proofs (exempt in check-decls) in group spec",
    "ProofsBroad": "FAIL[config] Fx.Spec.Proofs.E: a component named Proofs (exempt in check-decls) in group spec",
    "TrustedUncovered": "FAIL[config] Fx/Spec.lean (module Fx.Spec, group spec) is not covered by trusted_paths",
    "TrustedPathMagic": "FAIL[config] trusted_paths entry ':(exclude)Fx/Spec'",
    "ExportsComponent": "FAIL[config] Fx.Impl.Exports.E",
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
    have = sorted(p.name for p in Path(fixtures).iterdir() if p.is_dir())
    if have != sorted(CASES):
        print(f"FAIL self-test: fixture directories {have} != cases {sorted(CASES)}")
        ok = False
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
    ap.add_argument("--graph-out", help="write the import graph of the checked libraries (lib, module, import)")
    ap.add_argument("--self-test", metavar="FIXTURES_DIR", nargs="?", const="scripts/fixtures/imports")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(0 if self_test(a.self_test) else 1)
    fails = check(a.tree, a.config, a.lakefile, a.inventory_out, a.graph_out)
    for f in fails:
        print(f)
    print(f"check-imports: {'FAILED' if fails else 'passed'} ({len(fails)} findings)")
    sys.exit(1 if fails else 0)
