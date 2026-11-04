#!/usr/bin/env python3
"""Source-level import boundaries (foundation plan §2) and the library inventory of the check stack.

One configuration file, scripts/boundaries.toml (the pattern of leanerSTFSpec's boundaries.toml and
check_boundaries.py). Imports come from the pinned Lean parser (`lean --deps-json`: module headers only,
no build), so no stale build output can hide a violation. Run as `python3 -I scripts/check-boundaries.py`;
`--self-test` runs every case of scripts/fixtures/boundaries/cases.toml.

Config: a missing, unparsable or mistyped file fails, and so does a missing or unknown key (a typo would
  check less), a `forbidden_imports` name outside `base`, and a `milestone_parents` or `init_exempt` entry
  that meets no layer.
Libraries: every lakefile target is a configured lib, a fixture lib or a tool (`tool_exes`, `tool_libs`: the
  check stack's own tools, which no checked module may import: an unknown top-level name); `defaultTargets` is exactly
  the libs with `default = true`, `testDriver` the lib with `test_driver = true`. No project module, file
  or directory takes a top-level name of `base`. A lib's root module is its name. With `root_lists_all`
  the lib is the root plus every file under its directory (lakefile globs exactly `[<name>.*]`) and the
  root (generated: `lake exe mk_all`) imports exactly every other module of the lib.
Layers: every module except a generated root is in exactly one `[[layer]]`: prefixes never overlap.
  `allow` lists the other layers a module may import directly; the lists are acyclic and downward-closed
  (a layer allows everything its allowed layers allow), so the direct rule bounds the whole import closure.
  A trusted layer allows only trusted layers; a `protected` layer only trusted and protected ones. `sorry = true`
  (where check.sh lets unfinished proofs stay) is allowed only on an untrusted layer whose every prefix is in a
  default library and has a `Lemmas` or `Proofs` component. Every directory `<parent>.<M>` under a
  `milestone_parents` entry is one milestone layer, entered from other layers only through `<parent>.<M>.Main`.
Imports (each module, each import): an edge outside `allow` fails unless an `[[exception]]` lets the
  modules under its `from` import the modules under its `to`; an import into a milestone layer other than
  its entry fails, exception or not. The import closure of each module is walked too: it may hold only its
  own and allowed layers, except that the walk stops at a dependency an exception approves for that very
  module (that module's closure is checked as its own). So an exception does not extend to the importers of
  its `from` modules (the transitive case, printed with its path). No exception starts in a trusted layer,
  and every `from` and `to` entry must be used. `forbidden_imports` (`import Mathlib`), a fixture module, an
  unknown top-level name, `import all`, and an import of a generated root or an import-only aggregate
  (except `init_module`) fail unless the importing layer has `may_import_all` / `may_import_roots` (the
  tests); an aggregate import is still held to `allow`.
Init chain: every module of a layer, except under an `init_exempt` prefix, reaches `init_module` through
  public imports.
Visibility (plan §3): the attribute `expose` (whole-file `@[expose] public section`, on a declaration, or
  through `attribute [expose]`; found in the code with comments and string/char literals blanked, inside a
  balanced `@[...]`/`attribute [...]` list, also as `«expose»`) only in a layer with `expose = true`; that flag
  never on a layer whose prefixes have a `Lemmas`, `Proofs`, `ToMathlib` or `Main` component. Not checked: the
  bodies Lean exposes without the attribute (`abbrev`, instances of non-`Prop` classes); README "Layout". Known
  scan limit: inside an interpolated string (`s!"..{..}.."`), a `'"'` char literal ends the string early.
check-decls exemptions: a module with a `Proofs` component must be under
  `[checks].proofs_component_prefixes` and in a layer no trusted layer may reach; `Exports` is refused.
`[checks].trusted_paths` (CI's review-boundary list) holds plain relative paths only and covers the file
  of every module of a trusted layer and of every `protected` layer (an untrusted layer whose files the tag
  still covers: the instance semantics and statements, #38).
Protected surface (the inventory's 6th column; check.sh step 4's instance snapshot): every module of a default
  lib whose file `trusted_paths` covers and whose layer is not trusted. Every module of a `protected` layer must
  be in it, and none of a trusted layer.
Failure tags: FAIL[config] FAIL[layer] FAIL[milestone] FAIL[import] FAIL[entry] FAIL[umbrella]
  FAIL[import-all] FAIL[root] FAIL[root-import] FAIL[aggregate] FAIL[init] FAIL[base] FAIL[fixture]
  FAIL[expose].
"""
import argparse, json, re, shutil, subprocess, sys, tempfile, tomllib
from pathlib import Path

REQUIRED_KEYS = {"base", "fixture_libs", "tool_exes", "init_module", "init_exempt", "milestone_parents",
                 "forbidden_imports", "lib", "layer", "checks"}
TOP_KEYS = REQUIRED_KEYS | {"exception", "tool_libs"}
# [checks]: read by scripts/check.sh (and trusted_paths by CI's review-boundary job); a new key is added here.
CHECKS_KEYS = {"proofs_component_prefixes", "noconst_exempt", "theorems_mode", "review_axioms_module", "review_root",
               "challenge_module", "solution_module", "statements_module", "milestone_statements_modules",
               "proved_milestone_modules",
               "extra_build_targets", "trusted_paths",
               "canary_module", "canary_proof_edit", "canary_statement_edit", "doc_name_files", "name_index_module"}
LIB_KEYS = {"name", "default", "test_driver", "root_lists_all"}
LAYER_KEYS = {"name", "prefixes", "allow", "trusted", "protected", "sorry", "expose", "may_import_roots", "may_import_all",
              "about"}
EXCEPTION_KEYS = {"from", "to", "reason"}

def under(m, prefix):  # module-name prefix, component-wise: A covers A and A.x, not AB
    return m == prefix or m.startswith(prefix + ".")

def lib_prefixes(lake_lib):  # module prefixes a lakefile lib owns (its roots, glob stems and one-module globs)
    globs = [g[:-2] if g.endswith((".*", ".+")) else g for g in lake_lib.get("globs", [])]
    return lake_lib.get("roots", [lake_lib["name"]]) + globs

def strip_comments(src):  # Lean comments (nested block comments, line comments) become blanks
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; out.append("  "); continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; out.append("  "); continue
        if not depth and src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(src[i] if not depth or src[i] == "\n" else " "); i += 1
    return "".join(out)

def code_only(src):  # comments (nested), string and char literals blanked; newlines kept
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == "«":  # a quoted identifier is one token; only «expose» keeps its text
            j = src.find("»", i + 1)
            j = n if j < 0 else j + 1
            tok = src[i:j]
            closed = len(tok) >= 2 and tok.endswith("»")
            out.append(tok if tok == "«expose»" else "«" + "x" * (len(tok) - 1 - closed) + "»" * closed); i = j
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src.startswith("/-", i):
            depth = 0
            while i < n:
                if src.startswith("/-", i):
                    depth += 1; out.append("  "); i += 2
                elif src.startswith("-/", i):
                    depth -= 1; out.append("  "); i += 2
                    if depth == 0:
                        break
                else:
                    out.append("\n" if src[i] == "\n" else " "); i += 1
            continue
        m = re.match(r'r(#*)"', src[i:]) if c == "r" and (i == 0 or not IDENT.match(src[i - 1])) else None
        if m:  # raw string r"...", r#"..."#
            end = src.find('"' + m.group(1), i + m.end())
            end = n if end < 0 else end + 1 + len(m.group(1))
            out.append("".join("\n" if x == "\n" else " " for x in src[i:end])); i = end
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if x == "\n" else " " for x in src[i:j])); i = j
            continue
        if c == "'" and (i == 0 or not IDENT.match(src[i - 1])):
            m = re.match(r"'(?:\\.[^']*|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * m.end()); i += m.end()
                continue
        out.append(c); i += 1
    return "".join(out)

IDENT = re.compile(r"[\w'!?₀-₉ₐ-ₜ]")
# The attribute `expose` in an attribute list: not part of a longer or dotted name.
EXPOSE_NAME = re.compile(r"(?<![\w.'«])(?:expose|«expose»)(?![\w'!?»])")

def has_expose(src):  # an `@[...]` or `attribute [...]` list (balanced brackets) naming `expose`
    code = code_only(src)
    for m in re.finditer(r"@\[|\battribute\s*\[", code):
        i, depth = m.end(), 1
        while i < len(code) and depth:
            depth += {"[": 1, "]": -1}.get(code[i], 0); i += 1
        if EXPOSE_NAME.search(code[m.end():i - 1]):
            return True
    return False

HEADER_ITEM = re.compile(r"\s*(?:module|prelude|(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?[^\s]+)(?=\s|$)")

def import_only(text):  # nothing but a module header (an aggregate of re-exports)
    code, pos = strip_comments(text), 0
    while (m := HEADER_ITEM.match(code, pos)) and m.end() > pos:
        pos = m.end()
    return code[pos:].strip() == ""

def strings(v, nonempty=False):
    return isinstance(v, list) and all(isinstance(x, str) and x for x in v) and (v or not nonempty)

def load_toml(path, what, fails):
    try:
        text = Path(path).read_text()
    except OSError as e:
        fails.append(f"FAIL[config] cannot read the {what} {path}: {e.strerror}")
        return None
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        fails.append(f"FAIL[config] the {what} {path} is not valid TOML: {e}")
        return None

def validate(cfg):  # the shape of boundaries.toml (FAIL[config] findings)
    fails = []
    def bad(msg): fails.append(f"FAIL[config] {msg}")
    for k in sorted(set(cfg) - TOP_KEYS):
        bad(f"unknown top-level key {k}")
    for k in sorted(REQUIRED_KEYS - set(cfg)):
        bad(f"missing top-level key {k}")
    for k in ("base", "fixture_libs", "tool_exes", "tool_libs", "init_exempt", "milestone_parents", "forbidden_imports"):
        if not strings(cfg.get(k, [])):
            bad(f"{k} must be a list of names")
    if not isinstance(cfg.get("init_module"), str) or not cfg.get("init_module"):
        bad("init_module (the module every module reaches by public imports) is missing")
    if not isinstance(cfg.get("checks", {}), dict):
        bad("[checks] must be a table")
    else:
        for k in sorted(set(cfg.get("checks", {})) - CHECKS_KEYS):
            bad(f"[checks]: unknown key {k}")
    if strings(cfg.get("forbidden_imports", [])) and strings(cfg.get("base", [])):
        for x in cfg.get("forbidden_imports", []):
            if x.split(".")[0] not in cfg["base"]:
                bad(f"forbidden_imports entry {x} is not under a base name")
    for kind, keys in (("lib", LIB_KEYS), ("layer", LAYER_KEYS), ("exception", EXCEPTION_KEYS)):
        entries = cfg.get(kind, [])
        if not isinstance(entries, list) or not all(isinstance(e, dict) for e in entries):
            bad(f"{kind} must be an array of tables [[{kind}]]"); continue
        if kind != "exception" and not entries:
            bad(f"no [[{kind}]] entries")
        for n, e in enumerate(entries, 1):
            what = f"[[{kind}]] {e.get('name', n)}"
            for k in sorted(set(e) - keys):
                bad(f"{what}: unknown key {k}")
            for k in ("default", "test_driver", "root_lists_all", "trusted", "protected", "sorry", "expose",
                      "may_import_roots", "may_import_all"):
                if k in e and not isinstance(e[k], bool):
                    bad(f"{what}: {k} must be true or false")
            if kind != "exception" and (not isinstance(e.get("name"), str) or not e.get("name")):
                bad(f"{what}: no name")
            if kind == "layer":
                if not strings(e.get("prefixes"), nonempty=True):
                    bad(f"{what}: prefixes must be a nonempty list of module prefixes")
                if not strings(e.get("allow")):
                    bad(f"{what}: allow must be a list of layer names ([] for none)")
            if kind == "exception":
                for k in ("from", "to"):
                    if not strings(e.get(k), nonempty=True):
                        bad(f"exception {n}: {k} must be a nonempty list of module prefixes")
                if not isinstance(e.get("reason"), str) or not e.get("reason", "").strip():
                    bad(f"exception {n}: no reason")
    return fails

def deps_json(files):  # lean --deps-json over files: one result per file, in order
    res = subprocess.run(["lake", "env", "lean", "--deps-json", *files], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"lean --deps-json exited {res.returncode}: {res.stderr.strip()}")
    out = json.loads(res.stdout)["imports"]
    if len(out) != len(files):
        raise RuntimeError("lean --deps-json returned a different number of results")
    return out

def check(tree, cfg_path, lakefile, parse=deps_json, inventory_out=None, graph_out=None):
    tree = Path(tree)
    fails = []
    cfg = load_toml(cfg_path, "boundaries config", fails)
    lake = load_toml(lakefile, "lakefile", fails)
    if cfg is None or lake is None:
        return fails
    if (fails := validate(cfg)):
        return fails
    libs, base = cfg["lib"], set(cfg.get("base", []))
    lake_libs = {l["name"]: l for l in lake.get("lean_lib", [])}
    names = [l["name"] for l in libs]
    if (tree / "lakefile.lean").exists():
        fails.append("FAIL[config] lakefile.lean exists: Lake would use it instead of lakefile.toml")
    for k, v in lake.items():  # targets: only lean_lib/lean_exe, each one known
        if k not in ("lean_lib", "lean_exe", "require") and isinstance(v, list) and any(isinstance(x, dict) for x in v):
            fails.append(f"FAIL[config] target: lakefile table [[{k}]] is not supported")
    exes = lake.get("lean_exe", [])
    known = set(names) | set(cfg.get("fixture_libs", [])) | set(cfg.get("tool_exes", [])) | set(cfg.get("tool_libs", []))
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
    if not defaults or sorted(lake.get("defaultTargets", [])) != sorted(defaults):
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

    # --- layers: names, prefixes, allow lists (acyclic, downward-closed, trusted below trusted), milestones
    layers = {}
    for l in cfg["layer"]:
        if l["name"] in layers:
            fails.append(f"FAIL[config] layer {l['name']} is defined twice")
        layers[l["name"]] = l
    owner_of = {}  # prefix -> layer
    for l in cfg["layer"]:
        for p in l["prefixes"]:
            for q, o in owner_of.items():
                if under(p, q) or under(q, p):
                    fails.append(f"FAIL[config] prefix {p} (layer {l['name']}) overlaps {q} (layer {o}): a module would map to two layers")
            owner_of[p] = l["name"]
    def layer_of(m):
        return next((o for p, o in owner_of.items() if under(m, p)), None)
    allow = {n: set(l["allow"]) for n, l in layers.items()}
    for n, a in allow.items():
        for x in sorted(a):
            if x not in layers or x == n:
                fails.append(f"FAIL[config] layer {n}: allow entry {x} is not another layer")
        allow[n] = {x for x in a if x in layers and x != n}
    state = {}
    def cyclic(n, stack):
        if state.get(n) == 1:
            fails.append(f"FAIL[config] layer cycle: {' -> '.join(stack[stack.index(n):] + [n])}")
            return True
        if state.get(n) == 2:
            return False
        state[n] = 1
        hit = any(cyclic(x, stack + [n]) for x in sorted(allow[n]))
        state[n] = 2
        return hit
    if not any([cyclic(n, []) for n in layers]):
        for n in layers:
            for x in sorted(allow[n]):
                for y in sorted(allow[x] - allow[n]):
                    fails.append(f"FAIL[config] layer {n}: allow is not downward-closed: it allows {x}, which allows {y}")
    trusted = {n for n, l in layers.items() if l.get("trusted") is True}
    for n in sorted(trusted):
        for x in sorted(allow[n] - trusted):
            fails.append(f"FAIL[config] trusted layer {n} allows the untrusted layer {x}")
    protected = {n for n, l in layers.items() if l.get("protected") is True}
    for n in sorted(protected):  # the protected surface's closure stays inside it (docs/decisions.md, 2026-11-04)
        for x in sorted(allow[n] - trusted - protected):
            fails.append(f"FAIL[config] protected layer {n} allows the unprotected layer {x}")
    for n, l in sorted(layers.items()):  # `sorry = true` (check.sh steps 3, 7): only Lemmas and Proofs (plan §5)
        if l.get("sorry") is True:
            if n in trusted:
                fails.append(f"FAIL[config] trusted layer {n} allows sorry")
            for p in l["prefixes"]:
                if not {"Lemmas", "Proofs"} & set(p.split(".")):
                    fails.append(f"FAIL[config] layer {n}: sorry = true outside Lemmas and Proofs ({p})")
                if not any(under(p, d) for d in defaults):
                    fails.append(f"FAIL[config] layer {n}: sorry = true outside the default libraries ({p})")
        if l.get("expose") is True:  # plan §3: Lemmas, Proofs, ToMathlib and Main carry no @[expose]
            for p in l["prefixes"]:
                if {"Lemmas", "Proofs", "ToMathlib", "Main"} & set(p.split(".")):
                    fails.append(f"FAIL[config] layer {n}: expose = true on Lemmas, Proofs, ToMathlib or Main ({p})")
    def reach(ns):  # layers reachable from ns through allow (ns included)
        out, todo = set(), list(ns)
        while todo:
            x = todo.pop()
            if x not in out:
                out.add(x); todo += allow.get(x, ())
        return out
    trusted_reach = reach(trusted)
    entry = {}  # milestone layer -> its entry module
    parents = cfg.get("milestone_parents", [])
    for n, l in layers.items():
        for p in l["prefixes"]:
            for P in parents:
                if under(P, p):
                    fails.append(f"FAIL[config] layer {n}: prefix {p} covers the milestone parent {P} (one layer per milestone)")
                elif under(p, P):
                    if p.count(".") != P.count(".") + 1 or len(l["prefixes"]) != 1:
                        fails.append(f"FAIL[config] layer {n}: a milestone layer has the one prefix {P}.<M>, not {l['prefixes']}")
                    else:
                        entry[n] = p + ".Main"
    for key in ("milestone_parents", "init_exempt"):
        for x in cfg[key]:
            if not any(under(p, x) or under(x, p) for p in owner_of):
                fails.append(f"FAIL[config] {key} entry {x} meets no layer prefix")
    exceptions = cfg.get("exception", [])
    for k, e in enumerate(exceptions, 1):
        for f in e["from"]:
            hit = sorted({o for p, o in owner_of.items() if (under(f, p) or under(p, f)) and o in trusted})
            if hit:
                fails.append(f"FAIL[config] exception {k}: from {f} meets the trusted layer {', '.join(hit)}")
    def covers(x, y):  # (exception, from entry, to entry) that allow module x to import or reach module y
        return [(k, f, t) for k, e in enumerate(exceptions, 1) for f in e["from"] for t in e["to"]
                if under(x, f) and under(y, t)]
    used = set()
    proofs_pfx = cfg.get("checks", {}).get("proofs_component_prefixes", [])
    for p in proofs_pfx:
        if layer_of(p) in trusted_reach:
            fails.append(f"FAIL[config] proofs_component_prefixes {p} is in layer {layer_of(p)}, reachable from a trusted layer")

    # --- inventory: the modules of every checked lib
    inv, roots = {}, set()  # lib name -> list of (module, file); roots = root_lists_all roots (generated)
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
            roots.add(n)
        else:
            if ll.get("globs", [n]) != [n]:
                fails.append(f"FAIL[config] {n}: a single-module lib has globs [{n}] (the default)")
            if d.exists():
                fails.append(f"FAIL[config] {n}: a single-module lib has no directory {d}")
            inv[n] = [(n, rootfile)]
    owner = {m: n for n, mods in inv.items() for m, _ in mods}
    layer = {}
    for n, mods in inv.items():
        for m, _ in mods:
            comps = m.split(".")
            if "Exports" in comps:
                fails.append(f"FAIL[config] {m}: a component named Exports is exempt in check-decls")
            if "Proofs" in comps and not any(under(m, p) for p in proofs_pfx):
                fails.append(f"FAIL[config] {m}: a component named Proofs (exempt in check-decls) outside proofs_component_prefixes")
            if m in roots:
                continue
            layer[m] = layer_of(m)
            for P in parents:
                if under(m, P) and (m.count(".") < P.count(".") + 2 or layer[m] not in entry):
                    fails.append(f"FAIL[milestone] {m}: a milestone is a directory {P}.<M> with its own layer "
                                 f"(boundaries.toml [[layer]] prefixes = [\"{'.'.join(m.split('.')[:P.count('.') + 2])}\"])")
            if layer[m] is None:
                fails.append(f"FAIL[layer] {m}: in no layer (boundaries.toml [[layer]] prefixes)")
            elif "Proofs" in comps and layer[m] in trusted_reach:
                fails.append(f"FAIL[config] {m}: a component named Proofs (exempt in check-decls) in layer {layer[m]}, reachable from a trusted layer")
    for n, e in sorted(entry.items()):
        if any(layer.get(m) == n for m in owner) and e not in owner:
            fails.append(f"FAIL[milestone] layer {n} has modules but no entry module {e}")
    init = cfg["init_module"]
    if layer.get(init) is None:
        fails.append(f"FAIL[config] init_module {init} is not a module of a layer")
    trusted_paths = cfg.get("checks", {}).get("trusted_paths", [])
    for t in trusted_paths:
        if not (isinstance(t, str) and re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*", t)
                and ".." not in t.split("/")):
            fails.append(f"FAIL[config] trusted_paths entry {t!r}: not a plain relative path")
    # The protected surface (check.sh step 4, scripts/instance-spec-snapshot.txt): every module of a default
    # library whose file trusted_paths covers, outside the trusted layers (which the Spec snapshot holds).
    protected_surface = set()
    for n, mods in inv.items():
        for m, p in mods:
            rel = p.relative_to(tree).as_posix()
            covered = any(rel == t or rel.startswith(t + "/") for t in trusted_paths)
            if (layer.get(m) in trusted_reach or layers.get(layer.get(m), {}).get("protected") is True) and \
                    not covered:
                fails.append(f"FAIL[config] {rel} (module {m}, layer {layer[m]}) is not covered by trusted_paths")
            if covered and n in defaults and layer.get(m) not in trusted:
                protected_surface.add(m)
    for n, mods in inv.items():
        for m, p in mods:
            if layers.get(layer.get(m), {}).get("protected") is True and m not in protected_surface:
                fails.append(f"FAIL[config] {m} (protected layer {layer[m]}) is not in the protected surface "
                             f"(a default library's module covered by trusted_paths)")
            if m in protected_surface and layer.get(m) in trusted:
                fails.append(f"FAIL[config] {m}: in the protected surface and in the trusted layer {layer[m]}")

    # --- imports (lean --deps-json; the implicit prelude `Init` dropped)
    files = [str(p) for mods in inv.values() for _, p in mods]
    if not files:
        return fails + ["FAIL[config] no modules"]
    try:
        results = parse(files)
    except RuntimeError as e:
        return fails + [f"FAIL[config] {e}"]
    imports, path_of = {}, {m: p for mods in inv.values() for m, p in mods}
    mod_of = {str(p): m for m, p in path_of.items()}
    for f, r in zip(files, results):
        if r.get("errors") or "result" not in r:
            return fails + [f"FAIL[config] lean --deps-json: {f}: {r.get('errors')}"]
        is_module = r["result"].get("isModule", True)
        imports[mod_of[f]] = [{"module": i["module"], "public": i.get("isExported", True) or not is_module,
                               "all": i.get("importAll", False)} for i in r["result"]["imports"] if i["module"] != "Init"]
    direct = {m: sorted({i["module"] for i in imps}) for m, imps in imports.items()}
    if graph_out:  # `lib<TAB>module<TAB>import` per direct import (`-` for none): check.sh --changed's cone
        with open(graph_out, "w") as out:
            for m, n in owner.items():
                for i in direct[m] or ["-"]:
                    out.write(f"{n}\t{m}\t{i}\n")
    aggregates = {m for m in owner if m not in roots and m != init and import_only(path_of[m].read_text())}
    for n in sorted(roots):  # the generated root imports exactly the other modules of its lib
        want = {m for m, _ in inv[n]} - {n}
        for m in sorted(want - set(direct[n])):
            fails.append(f"FAIL[root] {m} is not imported by the root {n} (regenerate: lake exe mk_all --lib {n} --module)")
        for i in sorted(set(direct[n]) - want):
            fails.append(f"FAIL[root] the root {n} imports {i}, not a module of {n}")
    forbidden = set(cfg.get("forbidden_imports", []))
    def entry_ok(m, i):  # into a milestone layer from another layer only through its entry module
        Li = layer.get(i)
        return Li is None or Li == layer.get(m) or Li not in entry or i == entry[Li]
    def edge_ok(m, i):  # module m may import module i: entry rule, then allow or an exception
        L, Li = layer.get(m), layer.get(i)
        if L is None or Li is None or Li == L:
            return True
        if not entry_ok(m, i):
            return False
        if Li in allow[L]:
            return True
        if (cov := covers(m, i)):
            used.update(cov)
            return True
        return False
    for m in owner:  # @[expose] only in the exposed layers (plan §3)
        L = layer.get(m)
        if L and not layers[L].get("expose") and has_expose(path_of[m].read_text()):
            fails.append(f"FAIL[expose] {m}: @[expose] in layer {L}, which has no expose = true (plan §3: "
                         "public theorems, private helpers; a characterising lemma instead of an exposed body)")
    for m in owner:  # direct imports
        L = layer.get(m)
        flags = layers[L] if L else {}
        for imp in imports[m]:
            i = imp["module"]
            if i in forbidden:
                fails.append(f"FAIL[umbrella] {m} imports {i} (forbidden_imports: import the modules it needs)")
            if imp["all"] and m not in roots and not flags.get("may_import_all"):
                fails.append(f"FAIL[import-all] {m}: import all {i} (only a layer with may_import_all)")
            if any(under(i, p) for p in fixture_pfx):
                fails.append(f"FAIL[fixture] {m} imports the fixture module {i}"); continue
            if i not in owner:
                if i.split(".")[0] not in base:
                    fails.append(f"FAIL[base] {i} imported by {m}")
                continue
            if m in roots:
                continue
            if i in roots:
                if not flags.get("may_import_roots"):
                    fails.append(f"FAIL[root-import] {m} imports the library root {i}")
                continue
            if i in aggregates and not flags.get("may_import_roots"):
                fails.append(f"FAIL[aggregate] {m} imports {i}, an import-only module (import what it re-exports)")
                continue
            if edge_ok(m, i):
                continue
            if not entry_ok(m, i):
                fails.append(f"FAIL[entry] {m} imports {i}: the milestone layer {layer[i]} is entered only through {entry[layer[i]]}")
            else:
                fails.append(f"FAIL[import] {i} (layer {layer[i]}) imported by {m} (layer {L})")
    for s in owner:  # the import closure: an exception approves a dependency of its `from` modules only
        L = layer.get(s)
        if L is None:
            continue
        ok = {L} | allow[L]
        path, todo = {s: [s]}, [s]
        while todo:
            m = todo.pop()
            for i in direct[m]:
                if i not in owner or i in path or (i in roots and not layers[L].get("may_import_roots")):
                    continue  # a forbidden root import is reported at its importer
                Li = layer.get(i)
                if Li is not None and Li not in ok:
                    if m == s or not edge_ok(m, i):
                        continue  # a direct import: approved by an exception (edge_ok), or reported above
                    if (cov := covers(s, i)):
                        used.update(cov)  # an approved dependency of s: its own closure is its own check
                    else:  # m -> i is an exception of m, not of s
                        fails.append(f"FAIL[import] {i} (layer {Li}) reached from {' -> '.join(path[m])} (layer {L})")
                    continue
                path[i] = path[m] + [i]; todo.append(i)
    for k, e in enumerate(exceptions, 1):
        if not any(u[0] == k for u in used):
            fails.append(f"FAIL[config] exception {k} (from {e['from']} to {e['to']}) covers no import: remove it")
            continue
        for side, n in (("from", 1), ("to", 2)):
            for x in e[side]:
                if not any(u[0] == k and u[n] == x for u in used):
                    fails.append(f"FAIL[config] exception {k}: {side} entry {x} covers no import: remove it")
    public, grew = {init}, True  # the init chain: modules reaching init_module through public imports
    while grew:
        grew = False
        for m in owner:
            if m not in public and any(i["public"] and i["module"] in public for i in imports[m]):
                public.add(m); grew = True
    for m in owner:
        if layer.get(m) and m not in public and not any(under(m, p) for p in cfg.get("init_exempt", [])):
            fails.append(f"FAIL[init] {m} does not reach {init} through public imports")
    if inventory_out:  # lib, module, leaf|parent, layer (`-`: a generated root), trusted|-, protected|-
        with open(inventory_out, "w") as out:
            for n, mods in inv.items():
                for m, _ in mods:
                    kind = "parent" if any(under(o, m) and o != m for o, _ in mods) else "leaf"
                    t = "trusted" if layer.get(m) in trusted else "-"
                    pr = "protected" if m in protected_surface else "-"
                    out.write(f"{n}\t{m}\t{kind}\t{layer.get(m) or '-'}\t{t}\t{pr}\n")
    return sorted(set(fails), key=fails.index)

def self_test(fixtures):
    """Every case of <fixtures>/cases.toml: a copy of <fixtures>/Good with the case's edits must fail with a
    finding that starts with `expect` (or pass, without `expect`); with `protected`, the inventory's protected
    surface (6th column) must be exactly that list. One lean --deps-json call for all cases."""
    fixtures = Path(fixtures)
    cases = tomllib.loads((fixtures / "cases.toml").read_text())
    ok = "Good" in cases and "expect" not in cases["Good"]
    if not ok:
        print("FAIL self-test: cases.toml has no passing case Good")
    work = Path(tempfile.mkdtemp(prefix="boundaries-selftest."))
    try:
        for case, c in cases.items():
            d = work / case
            shutil.copytree(fixtures / "Good", d)
            for k in sorted(set(c) - {"expect", "files", "edit", "delete", "protected"}):
                print(f"FAIL self-test {case}: unknown key {k}"); ok = False
            for rel in c.get("delete", []):
                (d / rel).unlink()
            for rel, text in c.get("files", {}).items():
                (d / rel).parent.mkdir(parents=True, exist_ok=True)
                (d / rel).write_text(text)
            for rel, subs in c.get("edit", {}).items():
                text = (d / rel).read_text()
                for old, new in subs:
                    if text.count(old) != 1:
                        print(f"FAIL self-test {case}: edit of {rel} does not match exactly once: {old!r}"); ok = False
                    text = text.replace(old, new, 1)
                (d / rel).write_text(text)
        files = sorted(str(p.resolve()) for p in work.rglob("*.lean"))
        cache = dict(zip(files, deps_json(files)))
        parse = lambda fs: [cache[str(Path(f).resolve())] for f in fs]
        for case, c in cases.items():
            d, tag = work / case, c.get("expect")
            inv = work / f"{case}.inventory.tsv"
            fails = check(d, d / "boundaries.toml", d / "lakefile.toml", parse=parse, inventory_out=inv)
            good = (not fails) if tag is None else any(f.startswith(tag) for f in fails)
            print(f"{'ok  ' if good else 'FAIL'} self-test {case}: expected {tag or 'pass'}, got {fails or 'pass'}")
            ok &= good
            if "protected" in c:
                got = sorted(r.split("\t")[1] for r in inv.read_text().splitlines()
                             if r.split("\t")[5] == "protected") if inv.exists() else None
                good = got == sorted(c["protected"])
                print(f"{'ok  ' if good else 'FAIL'} self-test {case}: protected surface {got}, "
                      f"expected {sorted(c['protected'])}")
                ok &= good
    finally:
        shutil.rmtree(work)
    assert under("A.B", "A") and under("A", "A") and not under("AB", "A") and not under("A", "A.B")
    assert lib_prefixes({"name": "F", "roots": [], "globs": ["F.+"]}) == ["F"]
    assert has_expose("@[\n  expose] public section") and has_expose("@[instance, «expose»] def x := 1") and \
        has_expose('@[foo "]", expose] def x := 1') and has_expose('def s := "/-"\n@[expose] def x := 1') and \
        has_expose("attribute [expose] f") and has_expose("@[simp, foo [a, b], expose] def x := 1")
    assert not has_expose('def s := "@[expose]"') and not has_expose("-- @[expose]\n/- @[expose] -/") and \
        not has_expose("@[no_expose, exposeFoo, foo_expose, Foo.expose] def x := 1") and \
        not has_expose("/-- doc `@[expose]` -/ def x := 1") and not has_expose("def h' := '['\n#check expose") and \
        not has_expose("def c := ']' @[simp] def expose := 1") and not has_expose("def «@[expose]» := 1")
    assert has_expose("def «/-» := 0\n@[expose] def x := 1") and has_expose('def «"» := 0\n@[expose] def x := 1')
    assert import_only("module -- c\n/-! doc /- nested -/ -/\npublic import A.B\nimport all C\n") and \
        not import_only("module\npublic import A\ndef x := 1\n") and import_only("import A") and \
        not import_only("module\nimport A\n#check 1 -- import B\n")
    return ok

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default="scripts/boundaries.toml")
    ap.add_argument("--lakefile", default="lakefile.toml")
    ap.add_argument("--tree", default=".")
    ap.add_argument("--inventory-out",
                    help="write the inventory (lib, module, leaf|parent, layer, trusted|-, protected|-)")
    ap.add_argument("--graph-out", help="write the import graph of the checked libraries (lib, module, import)")
    ap.add_argument("--self-test", metavar="FIXTURES_DIR", nargs="?", const="scripts/fixtures/boundaries")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(0 if self_test(a.self_test) else 1)
    fails = check(a.tree, a.config, a.lakefile, inventory_out=a.inventory_out, graph_out=a.graph_out)
    for f in fails:
        print(f)
    print(f"check-boundaries: {'FAILED' if fails else 'passed'} ({len(fails)} findings)")
    sys.exit(1 if fails else 0)
