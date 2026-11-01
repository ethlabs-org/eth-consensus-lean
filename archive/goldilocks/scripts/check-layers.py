#!/usr/bin/env python3
"""Check direct Lean module imports. Python 3.11+, standard library only.

Rule table (line numbers refer to the source snapshots read on 2026-09-29):
ID                 Rule                                      Source
B4                 Model/Statements import no proof modules   BUILD:63-65,111
B6-FACADE          No foreign facade; new FGSA libs: none    BUILD:69-72,199-213
B6-MATHLIB         No whole Mathlib import                    BUILD:69-72
B6-TACTIC          Whole Mathlib.Tactic only in leaf proofs   BUILD:69-72
                   or leaf test modules
B7-TESTS           A facade imports no Tests module           BUILD:73-75,112
B7-BODY            A facade contains only its import header   BUILD:73-75
B7-GLOBS           Library globs: Lib.* (CheckSupport: Lib.+)  BUILD:73-75,171-175
GLY-SPURE          S/Pure import set; Walk exception          GLY:401-403,463-465
GLY-SV2            S/V2 set; only KitV2.{,Duty}ClockLaws       GLY:404-408; BUILD:115-116
GLY-SAC            S/AC import set                            GLY:409-410
GLY-PPURE          P/Pure import set; Walk exception          GLY:411,463-465
GLY-PV2            P/V2 import set                            GLY:412
GLY-PAC            P/AC import set                            GLY:413-414
GLY-FG             Generic imports no FG library              GLY:420-422
GLY-AC-USE         Only Gen, SA and FGSA may use AC now        GLY:409-414,426-427
GLY-KITFG-DEF      KitFG definitions: S/Pure, except Walk      GLY:434-437; BUILD:112-114
GLY-KITFG-PROOF    KitFG proofs: S/Pure + P/Pure, except Walk  GLY:434-450; BUILD:113-114
                   WeightsBridge: S/Pure only
GLY-LOCKED         Locked modules: S/Pure !Walk + S/V2        GLY:446-447; BUILD:116-118
GLY-NOGEN          SimplexFG and GridCO.Model import no Gen    GLY:423-427,2141-2146
GLY-WALK           GridCO.Model.Walk: Mathlib/Model.Objects    GLY:466-479
FG-GRID            FGSA*/KitFG: GridCO proofs only StoreFacts BUILD:118-120,199-207
RUN                FGSARun import set                         BUILD:199-200
CLAIMS             FGSAClaims statement-only import set       BUILD:201-203
LANE               A proof lane imports only its allowed set SYN:106-114; BUILD:204-212
SHARED             Shared imports no lane/Export/Assembly    SYN:106-114; BUILD:204-212; L42
ASSEMBLY           Assembly joins lanes through Exports      SYN:112-114; BUILD:210-212
                   (Shared has an Export too: SYN L50)
                   Exact Assembly.Root imports facade and    SYN L58
                   named lower Assembly modules, including ResetArrival
CLAIM-USE          Claims/<F> only from matching lane Export SYN:112-114; BUILD:234-236; L42
LANE-CLAIMS        A lane module other than its Export reaches R-F1 D6 (fgsa-lean
                   no Claims/* or Shared.Claims, directly    2026-09-30); R5-66
                   or transitively
EXPORT-USE         Exports only from Assembly                SYN:112-114; BUILD:126-128
INHABIT            FGSAInhabit import set                     BUILD:213
TEST-USE           Nothing imports a test (facades: B7-TESTS) BUILD:214,241-243
TEST-SCOPE         Tests import only their own project lib    BUILD:214
PHASES             PhasesInternal only from the F4 tree      BUILD:218-225; SYN:237-242
CHECK-SUPPORT      Only files in scripts/ import CheckSupport BUILD:132-135

BUILD = claude-files/a0/build.md r3.4; GLY = generic-layer.md A.3-A.4/F-8
(the supplied file is r3.13); SYN = docs/LEAN-ARCHITECTURE.md P10/section 3.
KitFG definition names come from baselines/kitfg-def-modules.txt (D06).
Locked module names/prefixes come from CatalogLock.lean:64-74, not a copy.

Scope: all files below each lean_lib's roots/glob prefixes, regardless of
whether its globs build them, plus root facades. srcDir and roots are read
from lakefile.toml. Other repository .lean files get CHECK-SUPPORT only.
Hidden directories (including .lake and .git) and symlink directories are
not scanned. Imported modules need not exist: future rules still apply.

Readings used where sources differ:
* All 'may import' sets are closed sets. The Generic sets and GridCO Walk
  allow only Mathlib as an external library. Other FGSA role rules also
  allow Init/Lean/Std. Same-layer imports are allowed.
* Only the exact S/Pure/Walk and P/Pure/Walk modules can directly import
  GridCO.Model.Walk. Other S/Pure modules cannot import S/Pure/Walk.
* P/AC's later GridCO.Proofs/SAPC consumers are not enabled before F2.
* Claims and Export restrictions apply to facades, tests and 1c as well.
  'Nothing imports a test' includes other tests. Scripts are outside the
  library checks. Whole Mathlib.Tactic requires a proof or test with no
  direct library importer (including facade/test importers).
* Both FGSAProofs/<lane> and FGSAProofs/Proofs/<lane> paths are recognized;
  F4 and Finality denote the F4 tree. Same-lane proof imports are allowed.
  Shared accepts only the upstream set; its name cannot hide a lane.
* KitFG modules not on D06's list are proof modules (except the facade and
  Tests). The tighter WeightsBridge S/Pure limit at GLY:448-450 also applies.
* B7 is literal: even empty section/end commands are facade body content.
  B7-BODY and B7-GLOBS use <body:token> and <globs:Lib.*> in the target
  column because these two findings have no imported module.

LANE-CLAIMS is the one transitive rule: the finding names the direct import
through which the importer reaches Claims/* or Shared.Claims (a missing
module is a leaf). Exports, Assembly, Shared.Claims (claim-to-claim
implications only, R5-66), Tests and facades are outside its scope.

Apart from LANE-CLAIMS, this is a direct-import check, not a Lean parser/elaborator or an unused-
import check (BUILD check (f)). It does not inspect declaration bodies,
axioms, equation lemmas, closureRoots, or proof/definition content.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
import tomllib
from collections.abc import Callable, Iterator

sys.path.insert(0, str(Path(__file__).parent))
import import_policy as P


GEN = "AvailableChainGeneric"
SP = GEN + ".Statements.Pure"
SV = GEN + ".Statements.V2"
SA = GEN + ".Statements.AC"
PP = GEN + ".Proofs.Pure"
PV = GEN + ".Proofs.V2"
PA = GEN + ".Proofs.AC"
COMPOSE = "AvailableChainFGCompose"
KITFG = "AvailableChainKitFG"
FGSA = "AvailableChainFGSA"
RUN = "AvailableChainFGSARun"
CLAIMS = "AvailableChainFGSAClaims"
PROOFS = "AvailableChainFGSAProofs"
INHABIT = "AvailableChainFGSAInhabit"
PC_PROOFS = "AvailableChainPCSAProofs"
PC_CLAIMS = "AvailableChainPCSAClaims"
CLOCK = "AvailableChainKitV2.ClockLaws"
DUTY_CLOCK = "AvailableChainKitV2.DutyClockLaws"  # no-round migration 02: same shape as CLOCK
CLOCKS = (CLOCK, DUTY_CLOCK)
WALK = "AvailableChainGridCO.Model.Walk"
STORE_FACTS = "AvailableChainGridCO.Proofs.StoreFacts"
FUTURE_LIBS = {COMPOSE, GEN, RUN, CLAIMS, PROOFS, INHABIT, PC_PROOFS, "AvailableChainCheckSupport"}
BASELINE = Path("scripts/baselines/check-layers.txt")
# L42 (SYN P10 amendment): the only modules outside a lane Export that may
# import Claims/*. Exact module names, not prefixes. Statement-only assembly
# (root, facade), audit (Tests.Axioms), claim -> claim implications (Shared).
CLAIM_USE_EXEMPT = frozenset({CLAIMS, CLAIMS + ".FGSAClaims", CLAIMS + ".Tests.Axioms",
                              PROOFS + ".Proofs.Shared.Claims"})
SHARED_CLAIMS = PROOFS + ".Proofs.Shared.Claims"
# L50 (lead ruling 2026-10-01): the Shared lane has an Export. It is the only
# proof module that may import Claims/Shared; it imports Shared proof modules
# and Claims/Shared only; only Assembly imports it (EXPORT-USE, as for every
# lane Export).
SHARED_EXPORT = PROOFS + ".Proofs.Shared.Export"
# SYN L58: only this exact aggregate-proof home may import the claim facade
# and these named lower Assembly modules. Global checks still apply.
ASSEMBLY_ROOT = PROOFS + ".Proofs.Assembly.Root"
ASSEMBLY_ROOT_IMPORTS = frozenset({CLAIMS + ".FGSAClaims",
                                  PROOFS + ".Proofs.Assembly.Foundations",
                                  PROOFS + ".Proofs.Assembly.Shared",
                                  PROOFS + ".Proofs.Assembly.Clean",
                                  PROOFS + ".Proofs.Assembly.Outage",
                                  PROOFS + ".Proofs.Assembly.Finality",
                                  PROOFS + ".Proofs.Assembly.ResetArrival",
                                  PROOFS + ".Proofs.Assembly.WeakContinuation",
                                  PROOFS + ".Proofs.Assembly.WeakContinuationGrowth",
                                  PROOFS + ".Proofs.Assembly.WeakContinuationGrowthSeed"})
NAME_PART = r"(?:«[^»]+»|[^\W\d][\w'!?]*)"
NAME = re.compile(NAME_PART + r"(?:\." + NAME_PART + r")*")
Finding = tuple[str, str, str]


def under(name: str, prefix: str) -> bool:
    """Use module components, never a raw string-prefix test."""
    return name == prefix or name.startswith(prefix + ".")


def any_under(name: str, prefixes: tuple[str, ...]) -> bool:
    return any(under(name, prefix) for prefix in prefixes)


def lean_tokens(source: str) -> Iterator[str]:
    """Read header tokens, including nested comments and quoted identifiers.

    The caller stops at the first body token. Thus import-like text in a
    string, quotation or command body cannot create a dependency.
    """
    i = 0
    while i < len(source):
        if source[i].isspace() or source[i] == "\ufeff":
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end + 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment in import header")
        else:
            match = NAME.match(source, i)
            if match:
                yield match.group()
                i = match.end()
            else:
                yield source[i]
                i += 1


def read_header(source: str) -> tuple[tuple[str, ...], str]:
    """Match Lean's [module] [prelude] ([public] [meta] import [all] id)*.

    Whitespace, newlines, comments and same-line import commands work alike.
    Import visibility is irrelevant for this check; check (a) enforces B1.
    """
    tokens = iter(lean_tokens(source))
    token = next(tokens, "")
    for keyword in ("module", "prelude"):
        if token == keyword:
            token = next(tokens, "")
    imports = set()
    while token:
        first = token
        if token == "public":
            token = next(tokens, "")
        if token == "meta":
            token = next(tokens, "")
        if token != "import":
            return tuple(sorted(imports)), first
        token = next(tokens, "")
        if token == "all":
            token = next(tokens, "")
        if not NAME.fullmatch(token) or token in {"import", "public", "meta"}:
            raise ValueError("missing module name after import")
        imports.add(re.sub(r"«([^»]+)»", r"\1", token))
        token = next(tokens, "")
    return tuple(sorted(imports)), ""


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    library: str | None
    facade: bool
    imports: tuple[str, ...]
    body: str


@dataclass
class Context:
    root: Path
    modules: dict[str, Module]
    libraries: list[dict]
    facades: set[str]
    definitions: set[str]
    locked: set[str]
    locked_prefixes: tuple[str, ...]
    importers: dict[str, set[str]]
    claims_reach: dict[str, bool] = field(default_factory=dict)


def lean_files(directory: Path) -> Iterator[Path]:
    for current, dirs, files in os.walk(directory):
        dirs[:] = sorted(d for d in dirs if not d.startswith("."))
        for filename in sorted(files):
            if filename.endswith(".lean"):
                yield Path(current) / filename


def locked_scope(root: Path) -> tuple[set[str], tuple[str, ...]]:
    source = (root / "scripts/CatalogLock.lean").read_text(encoding="utf-8")
    lists = []
    for name in ("lockedModules", "lockedModulePrefixes"):
        match = re.search(r"\bdef\s+" + name + r"\s*:\s*List\s+Name\s*:=\s*\[([^]]*)\]", source)
        if not match:
            raise ValueError(f"cannot read {name} from scripts/CatalogLock.lean")
        lists.append(re.findall(r"`([\w.]+)", match[1]))
    return set(lists[0]), tuple(lists[1])


def load_context(root: Path) -> Context:
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    libraries = config.get("lean_lib", [])
    if not libraries:
        raise ValueError("lakefile.toml has no lean_lib entries")
    modules: dict[str, Module] = {}
    paths: set[Path] = set()
    facades = set(FUTURE_LIBS)

    def add(path: Path, src: Path, library: str | None, roots: list[str]) -> None:
        if path in paths:
            return
        name = ".".join(path.relative_to(src).with_suffix("").parts)
        imports, body = read_header(path.read_text(encoding="utf-8"))
        if name in modules:
            raise ValueError(f"duplicate module {name}: {modules[name].path} and {path}")
        modules[name] = Module(name, path.relative_to(root), library, name in roots, imports, body)
        paths.add(path)

    for lib in libraries:
        name = lib["name"]
        src = root / lib.get("srcDir", config.get("srcDir", "."))
        if not src.resolve().is_relative_to(root):
            raise ValueError(f"srcDir for {name} is outside the selected root")
        roots = lib.get("roots", [name])
        facades.update([name, *roots])
        prefixes = set(roots)
        for glob in lib.get("globs", []):
            prefixes.add(glob[:-2] if glob.endswith((".*", ".+")) else glob)
        for prefix in sorted(prefixes):
            stem = src.joinpath(*prefix.split("."))
            facade = stem.with_suffix(".lean")
            if facade.is_file():
                add(facade, src, name, roots)
            for path in lean_files(stem):
                add(path, src, name, roots)
    # The support guard says 'no module outside scripts/', not just libraries.
    for path in lean_files(root):
        if path not in paths:
            add(path, root, None, [])
    definitions = set()
    def_path = root / "scripts/baselines/kitfg-def-modules.txt"
    for line in def_path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            if not NAME.fullmatch(line) or "." in line:
                raise ValueError(f"invalid short KitFG definition module: {line}")
            name = KITFG + "." + line
            if name not in modules or modules[name].library != KITFG:
                raise ValueError(f"missing KitFG definition module: {line}")
            definitions.add(name)
    locked, prefixes = locked_scope(root)
    importers: dict[str, set[str]] = {}
    for module in modules.values():
        if module.library is not None and module.path.parts[0] != "scripts":
            for dep in module.imports:
                importers.setdefault(dep, set()).add(module.name)
    return Context(root, modules, libraries, facades, definitions, locked, prefixes, importers)


def is_test(name: str) -> bool:
    return "Tests" in name.split(".")[1:]


def is_statement(ctx: Context, name: str) -> bool:
    return (any(x in name.split(".")[1:] for x in ("Model", "Statements"))
            or any_under(name, ("AvailableChainModel", "AvailableChainStatements"))
            or name in ctx.definitions)


def is_proof(ctx: Context, name: str) -> bool:
    if name in ctx.facades or is_test(name) or name in ctx.definitions or name in CLOCKS:
        return False
    return ("Proofs" in name.split(".")[1:]
            or any_under(name, (KITFG, "AvailableChainKit", "AvailableChainKitV2", PROOFS)))


def foundation(dep: str) -> bool:
    return P.matches("foundation", dep)


def pure_base(dep: str) -> bool:
    return under(dep, "Mathlib") or under(dep, "AvailableChainModel.Objects")


def pure_statements(dep: str) -> bool:
    return under(dep, SP) and not under(dep, SP + ".Walk")


def v2_base(dep: str) -> bool:
    return (pure_base(dep) or pure_statements(dep) or under(dep, SV) or dep in CLOCKS
            or any_under(dep, tuple("AvailableChainEngineV2." + p for p in ("Engine", "Conditions", "Laws"))))


def ac_models(dep: str) -> bool:
    return any_under(dep, ("AvailableChainGridCO.Model", "AvailableChainSA.Model"))


def pure_proofs(dep: str) -> bool:
    return pure_base(dep) or any_under(dep, (SP, PP))


def v2_proofs(dep: str) -> bool:
    return pure_proofs(dep) or v2_base(dep) or any_under(dep, (PV, "AvailableChainKitV2"))


def b4(ctx: Context, m: Module, dep: str) -> bool:
    return not m.facade and is_statement(ctx, m.name) and is_proof(ctx, dep)


def b6_facade(ctx: Context, m: Module, dep: str) -> bool:
    if dep not in ctx.facades:
        return False
    if any_under(m.name, (RUN, CLAIMS, PROOFS, INHABIT)):
        return True
    owner = ctx.modules[dep].library if dep in ctx.modules else dep
    return owner != m.library


def b6_mathlib(ctx: Context, m: Module, dep: str) -> bool:
    return dep == "Mathlib"


def b6_tactic(ctx: Context, m: Module, dep: str) -> bool:
    leaf = not ctx.importers.get(m.name)
    return dep == "Mathlib.Tactic" and not (leaf and (is_test(m.name) or is_proof(ctx, m.name)))


def b7_tests(ctx: Context, m: Module, dep: str) -> bool:
    return m.facade and is_test(dep)


def b7_body(module: Module) -> Finding | None:
    if module.facade and module.body:
        return ("B7-BODY", module.name, f"<body:{module.body}>")
    return None


def b7_globs(ctx: Context) -> Iterator[Finding]:
    for lib in ctx.libraries:
        name = lib["name"]
        # The three F0 Tests targets build submodules of the owning library.
        if name in {x + "Tests" for x in (CLAIMS, PROOFS, INHABIT, PC_PROOFS)}:
            owner = name.removesuffix("Tests")
            if lib.get("roots") != [] or lib.get("globs") != [owner + ".Tests.+"]:
                yield ("B7-GLOBS", name, f"<globs:{owner}.Tests.+>")
            continue
        suffix = ".+" if name == "AvailableChainCheckSupport" else ".*"
        if lib.get("globs") != [name + suffix]:
            yield ("B7-GLOBS", name, f"<globs:{name}{suffix}>")


def gly_spure(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, SP) and not (pure_base(dep) or pure_statements(dep)
        or (m.name == SP + ".Walk" and dep in {WALK, SP + ".Walk"}))


def gly_sv2(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, SV) and not v2_base(dep)


def gly_sac(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, SA) and not (v2_base(dep) or under(dep, SA) or ac_models(dep))


def gly_ppure(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, PP) and not (pure_proofs(dep) or (m.name == PP + ".Walk" and dep == WALK))


def gly_pv2(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, PV) and not v2_proofs(dep)


def gly_pac(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, PA) and not (v2_proofs(dep) or any_under(dep, (SA, PA)) or ac_models(dep))


def is_fg(name: str) -> bool:
    return any_under(name, ("AvailableChainSimplexFG", KITFG, COMPOSE, FGSA, RUN, CLAIMS, PROOFS, INHABIT))


def gly_fg(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, GEN) and is_fg(dep)


def gly_ac_use(ctx: Context, m: Module, dep: str) -> bool:
    return any_under(dep, (SA, PA)) and not any_under(m.name, (GEN, "AvailableChainSA", FGSA, RUN, CLAIMS, PROOFS, INHABIT))


def gly_kitfg_def(ctx: Context, m: Module, dep: str) -> bool:
    return m.name in ctx.definitions and under(dep, GEN) and not pure_statements(dep)


def gly_kitfg_proof(ctx: Context, m: Module, dep: str) -> bool:
    allowed = pure_statements(dep) or (under(dep, PP) and not under(dep, PP + ".Walk"))
    if m.name == KITFG + ".WeightsBridge":
        allowed = pure_statements(dep)
    return under(m.name, KITFG) and m.name not in ctx.definitions and under(dep, GEN) and not allowed


def gly_locked(ctx: Context, m: Module, dep: str) -> bool:
    locked = m.name in ctx.locked or any_under(m.name, ctx.locked_prefixes)
    return locked and under(dep, GEN) and not (pure_statements(dep) or under(dep, SV))


def gly_nogen(ctx: Context, m: Module, dep: str) -> bool:
    return any_under(m.name, ("AvailableChainSimplexFG", "AvailableChainGridCO.Model")) and under(dep, GEN)


def gly_walk(ctx: Context, m: Module, dep: str) -> bool:
    return m.name == WALK and not pure_base(dep)


def fg_grid(ctx: Context, m: Module, dep: str) -> bool:
    return (any_under(m.name, (KITFG, FGSA, RUN, CLAIMS, PROOFS, INHABIT))
            and under(dep, "AvailableChainGridCO.Proofs") and dep != STORE_FACTS)


def run(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, RUN) and not m.facade and not is_test(m.name) and not (
        foundation(dep) or P.matches("layersRun", dep)
        or dep == STORE_FACTS)


def claims(ctx: Context, m: Module, dep: str) -> bool:
    allowed = foundation(dep) or dep in ctx.definitions or P.matches("layersClaims", dep)
    if under(m.name, PC_CLAIMS):
        allowed = allowed or any_under(dep, (PC_CLAIMS, "AvailableChainPCSA.Model",
            "AvailableChainPCSA.Statements", "AvailableChainPCSARun.Model",
            "AvailableChainPCSARun.Statements", "AvailableChainEngineV2.Conditions"))
        allowed = allowed or dep == "AvailableChainSimplexFG.Evidence" or (m.name, dep) in COMPOSE_EDGES
        return not m.facade and not is_test(m.name) and (not allowed or is_proof(ctx, dep))
    return under(m.name, CLAIMS) and not m.facade and not is_test(m.name) and (not allowed or is_proof(ctx, dep))


def proof_path(name: str) -> tuple[str, ...]:
    if not under(name, PROOFS) or name == PROOFS:
        return ()
    parts = tuple(name.split(".")[1:])
    return parts[1:] if parts[0] == "Proofs" else parts


def claim_path(name: str) -> tuple[str, ...]:
    prefix = CLAIMS + ".Claims"
    return tuple(name[len(prefix) + 1:].split(".")) if name.startswith(prefix + ".") else ()


def is_export(name: str) -> bool:
    parts = proof_path(name)
    return len(parts) >= 2 and parts[0] != "Assembly" and parts[1] == "Export"


def lane_upstream(ctx: Context, dep: str) -> bool:
    return (foundation(dep) or is_statement(ctx, dep)
            or P.matches("laneUpstream", dep)
            or dep == STORE_FACTS)


def lane(ctx: Context, m: Module, dep: str) -> bool:
    parts, target = proof_path(m.name), proof_path(dep)
    if not parts or parts[0] in {"Shared", "Assembly", "Statements", "Model", "Tests"}:
        return False
    # Import-policy lead ruling 2026-10-07: OutageContinuation Export route.
    # Only the six new Outage continuation modules may cross this lane boundary.
    if (m.name == PROOFS + ".Proofs.OutageContinuation.Export" and dep in {
            PROOFS + ".Proofs.Outage.Continuation" + suffix for suffix in
            ("Timing", "Induction", "Receipt", "Frame", "Gate", "Joint")}):
        return False
    if target and target[0] not in {"Statements", "Model"}:
        return target[0] not in {parts[0], "Shared"} or is_export(dep)
    own_claim = is_export(m.name) and claim_path(dep) == (parts[0],)
    return not (lane_upstream(ctx, dep) or own_claim)


def shared(ctx: Context, m: Module, dep: str) -> bool:
    parts, target = proof_path(m.name), proof_path(dep)
    if not parts or parts[0] != "Shared":
        return False
    if is_export(m.name):
        own = bool(target) and target[0] == "Shared" and not is_export(dep)
        return not (foundation(dep) or own or claim_path(dep) == ("Shared",))
    if m.name == SHARED_CLAIMS and (claim_path(dep) or dep == CLAIMS + ".Claims"):
        return False
    if target and target[0] not in {"Statements", "Model"}:
        return target[0] != "Shared"
    return not lane_upstream(ctx, dep)


def assembly(ctx: Context, m: Module, dep: str) -> bool:
    parts, target = proof_path(m.name), proof_path(dep)
    if not parts or parts[0] != "Assembly":
        return False
    if m.name == ASSEMBLY_ROOT:
        return not (foundation(dep) or dep in ASSEMBLY_ROOT_IMPORTS)
    if target and target[0] not in {"Statements", "Model"}:
        return target[0] != "Shared" and not is_export(dep)
    return not lane_upstream(ctx, dep)


def claim_use(ctx: Context, m: Module, dep: str) -> bool:
    parts = claim_path(dep)
    if not parts and dep != CLAIMS + ".Claims":
        return False
    if m.name in CLAIM_USE_EXEMPT and not (m.name == SHARED_CLAIMS and parts == ("Shared",)):
        return False
    return not (is_export(m.name) and len(parts) == 1 and proof_path(m.name) == (parts[0], "Export"))


def claims_target(dep: str) -> bool:
    return (bool(claim_path(dep)) or under(dep, PC_CLAIMS + ".Claims")
            or dep in {CLAIMS + ".Claims", SHARED_CLAIMS,
                       PC_PROOFS + ".Proofs.Shared.Claims"})


def reaches_claims(ctx: Context, dep: str) -> bool:
    memo = ctx.claims_reach
    if dep not in memo:
        memo[dep] = False  # Lean imports are acyclic; this only stops a bad fixture.
        memo[dep] = claims_target(dep) or (
            dep in ctx.modules and any(reaches_claims(ctx, d) for d in ctx.modules[dep].imports))
    return memo[dep]


def lane_claims(ctx: Context, m: Module, dep: str) -> bool:
    parts = proof_path(m.name)
    if (not parts or parts[0] in {"Shared", "Assembly", "Statements", "Model", "Tests"}
            or m.facade or is_test(m.name) or is_export(m.name)):
        return False
    return reaches_claims(ctx, dep)


def export_use(ctx: Context, m: Module, dep: str) -> bool:
    parts = proof_path(m.name)
    return is_export(dep) and not (len(parts) >= 2 and parts[0] == "Assembly")


def inhabit(ctx: Context, m: Module, dep: str) -> bool:
    return under(m.name, INHABIT) and not m.facade and not is_test(m.name) and not (
        foundation(dep) or any_under(dep, (INHABIT, CLAIMS, RUN, "AvailableChainKitV2", GEN)))


def test_use(ctx: Context, m: Module, dep: str) -> bool:
    return not m.facade and is_test(dep)


def test_scope(ctx: Context, m: Module, dep: str) -> bool:
    # P0b1: private fieldwise correspondence, with exact external suppliers.
    if (m.name, dep) in {
        (PROOFS + ".Tests.P0d5a", COMPOSE + ".Statements.FrontierSearch"),
        (PROOFS + ".Tests.P0d4", COMPOSE + ".Proofs.Healing.AttemptStop"),
        (PROOFS + ".Tests.P0d7c", COMPOSE + ".Proofs.Finality.Joined"),
        (PROOFS + ".Tests.P0d7c", COMPOSE + ".Proofs.Finality.Local"),
        (PROOFS + ".Tests.P0Origin", COMPOSE + ".Proofs.SafetyOrigin"),
        (COMPOSE + ".Tests.P0d3", KITFG + ".WindowHeightBridge"),
        (PROOFS + ".Tests.P0c1", COMPOSE + ".Proofs.ObservationTransport"),
        (PROOFS + ".Tests.P0HistoricalReads", COMPOSE + ".Proofs.HistoricalReads"),
        (PROOFS + ".Tests.P0HistoricalReads", FGSA + ".Proofs.NamedReachable"),
        (PROOFS + ".Tests.P0HistoricalReads", FGSA + ".Proofs.Restart"),
        (PROOFS + ".Tests.P0c1", INHABIT + ".WitnessPositive"),
        (PROOFS + ".Tests.P0b1", FGSA + ".Model.WindowStore"),
        (PROOFS + ".Tests.P0b1", FGSA + ".Statements.FinalityView"),
        (PROOFS + ".Tests.P0b1", KITFG + ".WindowTransport"),
        (PROOFS + ".Tests.P0b1", "AvailableChainSimplexFG.WindowStore"),
        (PROOFS + ".Tests.P0b2", FGSA + ".Proofs.WindowInvariant"),
        (PROOFS + ".Tests.P0b2", KITFG + ".WindowInvariant"),
        (PROOFS + ".Tests.P0b2", FGSA + ".Proofs.WindowSelection"),
        (PROOFS + ".Tests.P0b2", FGSA + ".Proofs.WindowStore"),
        (PROOFS + ".Tests.P0b3", FGSA + ".Proofs.WindowOccurrences"),
        (PROOFS + ".Tests.P0b3", FGSA + ".Proofs.WindowTerminal"),
        (PROOFS + ".Tests.P0b3", FGSA + ".Proofs.WindowValidity"),
    }:
        return False
    if not is_test(m.name) or foundation(dep):
        return False
    owner = ctx.modules[dep].library if dep in ctx.modules else dep.split(".")[0]
    return owner != m.library


def phases(ctx: Context, m: Module, dep: str) -> bool:
    if not under(dep, CLAIMS + ".Statements.PhasesInternal"):
        return False
    parts = proof_path(m.name)
    return not parts or parts[0] not in {"F4", "Finality"}


def check_support(ctx: Context, m: Module, dep: str) -> bool:
    return m.path.parts[0] != "scripts" and under(dep, "AvailableChainCheckSupport")


# Exact external edges. Both source guards use this table.
COMPOSE_MODULES = (COMPOSE + ".Statements.EventReads", COMPOSE + ".Statements.CoreReads",
                   COMPOSE + ".Proofs.SourceHead")
COMPOSE_SAFETY_MODULES = tuple(COMPOSE + ".Statements." + name for name in
                               ("SafetyReads", "SafetyStore", "SafetyClient", "SafetyClaims"))
COMPOSE_MODULES += COMPOSE_SAFETY_MODULES
# Lead ruling 2026-10-07 (s2-plan P1): the facade may import the P1 proof modules.
COMPOSE_MODULES += tuple(COMPOSE + ".Proofs." + name for name in
                         ("SafetyStore", "SafetyAccountable"))
COMPOSE_SAFETY_IMPORTS = frozenset({
    (COMPOSE + ".Statements.SafetyReads", KITFG + ".ClientOnce"),
    (COMPOSE + ".Statements.SafetyReads", "AvailableChainSimplexFG.Evidence"),
    (COMPOSE + ".Statements.SafetyReads", KITFG + ".CertificateCoreDef"),
    (COMPOSE + ".Statements.SafetyReads", SV + ".Duty.Slashing"),
    (COMPOSE + ".Statements.SafetyStore", KITFG + ".StoreSafetyDef"),
    (COMPOSE + ".Statements.SafetyClient", SP + ".Quorum"),
})
# Lead rulings 2026-10-07 (P2, S3a) and 2026-10-08 (P3, S3b): the facade may
# import the P2 and P3 proof modules.
COMPOSE_MODULES += tuple(COMPOSE + ".Proofs." + name for name in
                         ("SafetyClient", "SafetyCount", "SafetyMonotone", "SafetySlashing"))
# Lead ruling 2026-10-07 (s2-plan P1): one exact Compose proof edge. No prefix.
# Lead ruling 2026-10-07 (P2, S3a): two exact pairs for Proofs.SafetyClient. No prefix.
COMPOSE_PROOF_IMPORTS = frozenset({
    (COMPOSE + ".Proofs.SafetyAccountable", KITFG + ".AccountableCore"),
    (COMPOSE + ".Proofs.SafetyClient", KITFG + ".ClientOnceSafety"),
    (COMPOSE + ".Proofs.SafetyClient", PV + ".Duty.Fields"),
})
COMPOSE_EDGES = frozenset(
    [(PROOFS + ".Proofs.Shared.FGCompose", dep) for dep in COMPOSE_MODULES[:3]]
    + [(PROOFS + ".Proofs.Finality." + name, COMPOSE + ".Proofs.SourceHead")
       for name in ("MiddleSupport", "Rows")]
    + [("AvailableChainPCSAProofs.Proofs.Shared.FGCompose", COMPOSE + ".Statements.CoreReads")]
    + [("AvailableChainPCSAClaims.Statements.Reads", COMPOSE + ".Statements.EventReads")])

COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient', 'AvailableChainFGCompose.Statements.SafetyClient'),
    ('AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient', 'AvailableChainFGCompose.Statements.SafetyStore'),
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient', 'AvailableChainFGCompose.Statements.SafetyClient'),
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient', 'AvailableChainFGCompose.Statements.SafetyStore'),
})
# Lead ruling 2026-10-07 (s2-plan P9): the FG-SA accountability bridge reads the
# Compose accountability proofs. One exact pair. No prefix.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyAccountable'),
})
# Lead ruling 2026-10-08 (s2-plan P10, D2): the bridge also reads the Compose
# count, monotone and slashing proofs. Three exact pairs. No prefix.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyCount'),
    ('AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyMonotone'),
    ('AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetySlashing'),
})
# P12: four exact PC-SA safety bridge pairs (derisk §3). No prefix.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyAccountable'),
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyCount'),
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetyMonotone'),
    ('AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge', 'AvailableChainFGCompose.Proofs.SafetySlashing'),
})

# P0a: exact restart facade modules and the private FG-SA wrapper edge.
COMPOSE_MODULES += (COMPOSE + ".Statements.Restart", COMPOSE + ".Proofs.Restart")
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Finality.MiddleSupport", COMPOSE + ".Proofs.Restart"),
})


# P0c2: exact service, history, and receipt modules and wrapper edges.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.ResetHistory',
    'AvailableChainFGCompose.Statements.Service',
    'AvailableChainFGCompose.Statements.Bounds',
    'AvailableChainFGCompose.Statements.Finality',
    'AvailableChainFGCompose.Statements.FinalityReceipts',
    'AvailableChainFGCompose.Proofs.ServiceTransport',
)
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.Rows',
     'AvailableChainFGCompose.Proofs.ServiceTransport'),
    ('AvailableChainFGSAProofs.Proofs.Finality.RowsBatch',
     'AvailableChainFGCompose.Proofs.ServiceTransport'),
})


# P0c1: exact observation, paired selection, channel, and timing modules.
COMPOSE_MODULES += (
    "AvailableChainFGCompose.Statements.Observations",
    "AvailableChainFGCompose.Statements.Selection",
    "AvailableChainFGCompose.Statements.Timing",
    "AvailableChainFGCompose.Statements.Channels",
    "AvailableChainFGCompose.Statements.ChannelLaws",
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    (COMPOSE + ".Statements.Observations", KITFG + ".TreeFrameDef"),
    (COMPOSE + ".Statements.Observations", KITFG + ".CertificateCoreDef"),
})


COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Shared.FGCompose", COMPOSE + ".Statements.Selection"),
})


COMPOSE_MODULES += (
    COMPOSE + ".Proofs.ObservationTransport",
    COMPOSE + ".Proofs.Timing",
)
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Shared.FGCompose", COMPOSE + ".Statements.ChannelLaws"),
    (PROOFS + ".Proofs.Shared.FGCompose", COMPOSE + ".Proofs.ObservationTransport"),
    (PROOFS + ".Proofs.Shared.FGCompose", COMPOSE + ".Proofs.SourceHead"),
    (PROOFS + ".Proofs.Finality.ActionTime", COMPOSE + ".Proofs.Timing"),
    (PROOFS + ".Tests.P0c1", COMPOSE + ".Proofs.ObservationTransport"),
})


# P0c4: cumulative full-body reads and one exact geometry proof edge.
COMPOSE_MODULES += (
    COMPOSE + ".Statements.HistoricalReads",
    COMPOSE + ".Proofs.HistoricalReads",
)
COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.HistoricalReads", "AvailableChainGeneric.Proofs.Pure.CommonAncestor"),
})
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Tests.P0HistoricalReads", COMPOSE + ".Proofs.HistoricalReads"),
})

# P0d1: exact phase modules.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.Phase',
    'AvailableChainFGCompose.Statements.PhaseReceipts',
    'AvailableChainFGCompose.Proofs.Healing.PhaseFrame',
    'AvailableChainFGCompose.Proofs.Healing.PhaseOrder',
    'AvailableChainFGCompose.Proofs.Healing.PhaseSettle',
)

COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Healing.PhaseFrame',
     'AvailableChainKitFG.StoreBounds'),
    ('AvailableChainFGCompose.Proofs.Healing.PhaseFrame',
     'AvailableChainKitFG.FrameGeometry'),
    ('AvailableChainFGCompose.Proofs.Healing.PhaseSettle',
     'AvailableChainGeneric.Proofs.V2.Duty.Reads'),
})

COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame',
     'AvailableChainFGCompose.Proofs.Healing.PhaseFrame'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseOrder',
     'AvailableChainFGCompose.Proofs.Healing.PhaseOrder'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle',
     'AvailableChainFGCompose.Proofs.Healing.PhaseSettle'),
})

# P0d2: exact row permission homes and wrapper imports.
COMPOSE_MODULES += (COMPOSE + ".Statements.RowPermission", COMPOSE + ".Proofs.RowPermission")
COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.RowPermission", KITFG + ".ClientOnceSafety"),
})
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Foundations.RowPermission", COMPOSE + ".Proofs.RowPermission"),
})



# P0d3: promotion consumers and exact wrapper edges.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.Promotion',
    'AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic',
    'AvailableChainFGCompose.Proofs.Healing.CommonEntry',
    'AvailableChainFGCompose.Proofs.Healing.Promotion',
    'AvailableChainFGCompose.Proofs.Healing.PromotionRows',
)
COMPOSE_PROOF_IMPORTS |= frozenset({
    ("AvailableChainFGCompose.Proofs.Healing.PromotionRows",
     "AvailableChainSimplexFG.Window"),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic',
     'AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic'),
    ('AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts',
     'AvailableChainFGCompose.Proofs.Healing.CommonEntry'),
    ('AvailableChainFGSAProofs.Proofs.Healing.CommonEntryHeight',
     'AvailableChainFGCompose.Proofs.Healing.CommonEntry'),
    ('AvailableChainFGSAProofs.Proofs.Healing.Promotion',
     'AvailableChainFGCompose.Proofs.Healing.Promotion'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PromotionRows',
     'AvailableChainFGCompose.Proofs.Healing.PromotionRows'),
})




COMPOSE_PROOF_IMPORTS |= frozenset({
    ("AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic",
     "AvailableChainGeneric.Proofs.V2.Duty.Reads"),
})

COMPOSE_PROOF_IMPORTS |= frozenset({
    ("AvailableChainFGCompose.Proofs.Healing.CommonEntry",
     "AvailableChainKitFG.Ancestry"),
    ("AvailableChainFGCompose.Proofs.Healing.PromotionRows",
     "AvailableChainKitFG.Ancestry"),
})

# P0d4: exact attempt home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Statements.Attempt',)

# P0d4: exact attempt home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.AttemptStop',)

# P0d4: exact attempt home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.AttemptSettle',)

# P0d4: exact attempt home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.AttemptRows',)

# P0d4: exact attempt home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.Attempt',)

# P0d4: private correspondence test.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Tests.P0d4',
     'AvailableChainFGCompose.Proofs.Healing.AttemptStop'),
})

# P0d1: exact phase modules.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.Phase',
    'AvailableChainFGCompose.Statements.PhaseReceipts',
    'AvailableChainFGCompose.Proofs.Healing.PhaseFrame',
    'AvailableChainFGCompose.Proofs.Healing.PhaseOrder',
    'AvailableChainFGCompose.Proofs.Healing.PhaseSettle',
)


# P0d4: exact frozen-wrapper edges.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.AttemptStop',
     'AvailableChainFGCompose.Proofs.Healing.AttemptStop'),
    ('AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle',
     'AvailableChainFGCompose.Proofs.Healing.AttemptSettle'),
    ('AvailableChainFGSAProofs.Proofs.Healing.AttemptRows',
     'AvailableChainFGCompose.Proofs.Healing.AttemptRows'),
    ('AvailableChainFGSAProofs.Proofs.Healing.Attempt',
     'AvailableChainFGCompose.Proofs.Healing.Attempt'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame',
     'AvailableChainFGCompose.Proofs.Healing.PhaseFrame'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseOrder',
     'AvailableChainFGCompose.Proofs.Healing.PhaseOrder'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle',
     'AvailableChainFGCompose.Proofs.Healing.PhaseSettle'),
})

# P0d6a: causal reset-cut statement home.
COMPOSE_MODULES += (COMPOSE + ".Statements.ResetCut",)

# P0d6a: direct b2 store bound and the frozen FG-SA adapter.
COMPOSE_MODULES += (COMPOSE + ".Proofs.Healing.ResetCut",)
COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.Healing.ResetCut", KITFG + ".StoreBounds"),
})
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Healing.ResetCut", COMPOSE + ".Proofs.Healing.ResetCut"),
})

# P0d7a1: exact causal history consumers and frozen wrapper.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.FinalityHistory',
    'AvailableChainFGCompose.Proofs.Finality.History',
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityHistory', 'AvailableChainKitFG.WindowEntriesDef'),
})
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Finality.History', 'AvailableChainKitFG.CausalCapCore'),
    ('AvailableChainFGCompose.Proofs.Finality.History',
     'AvailableChainKitFG.HeightHistoryTransfer'),
    ('AvailableChainFGCompose.Proofs.Finality.History', 'AvailableChainKitFG.WindowRetention'),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.History',
     'AvailableChainFGCompose.Proofs.Finality.History'),
})

COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.Finality.History", "AvailableChainGeneric.Proofs.V2.Duty.Reads"),
})

COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.Finality.History", KITFG + ".WindowSelection"),
})

# P0c3: exact dependency contract and proof modules.
COMPOSE_MODULES += (
    "AvailableChainFGCompose.Statements.Dependency",
    "AvailableChainFGCompose.Statements.DependencyTrace",
    "AvailableChainFGCompose.Proofs.Dependency",
)
# P0d2: exact row permission homes and wrapper imports.
COMPOSE_MODULES += (COMPOSE + ".Statements.RowPermission", COMPOSE + ".Proofs.RowPermission")
COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.RowPermission", KITFG + ".ClientOnceSafety"),
})
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Foundations.RowPermission", COMPOSE + ".Proofs.RowPermission"),
})

# POP-C: direct imports of the extracted client and read helpers.
COMPOSE_PROOF_IMPORTS |= frozenset({
    (COMPOSE + ".Proofs.Population.HolderBaseHighTarget", "AvailableChainSimplexFG.Client"),
    (COMPOSE + ".Proofs.Population.HolderBaseTop", GEN + ".Proofs.V2.Duty.Reads"),
})

# P0d7a2: high-record consumers and the frozen wrapper.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.FinalityRecords',
    'AvailableChainFGCompose.Proofs.Finality.RecordInv',
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityRecords',
     'AvailableChainKitFG.ProvenanceCoreDef'),
})
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Finality.RecordInv',
     'AvailableChainKitFG.ProvenanceCore'),
    ('AvailableChainFGCompose.Proofs.Finality.RecordInv',
     'AvailableChainKitFG.StoreSafetyDef'),
    ('AvailableChainFGCompose.Proofs.Finality.RecordInv',
     'AvailableChainGeneric.Proofs.V2.Duty.Fields'),
})
COMPOSE_EDGES |= frozenset({
    (PROOFS + ".Proofs.Finality.RecordInv", COMPOSE + ".Proofs.Finality.RecordInv"),
})


# P0d7a3 middle support and construction.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.FinalityKernel',
    'AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
    'AvailableChainFGCompose.Proofs.Finality.Middle',
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityKernel',
     'AvailableChainKitFG.WindowEntriesDef'),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityKernel',
     'AvailableChainFGCompose.Statements.Promotion'),
    ('AvailableChainFGCompose.Statements.FinalityKernel',
     'AvailableChainFGCompose.Statements.Finality'),
    ('AvailableChainFGCompose.Statements.FinalityKernel',
     'AvailableChainFGCompose.Statements.FinalityRecords'),
    ('AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Statements.FinalityKernel'),
    ('AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Proofs.Finality.History'),
    ('AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Proofs.Finality.RecordInv'),
    ('AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Proofs.Timing'),
    ('AvailableChainFGCompose.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Proofs.Healing.ResetCut'),
    ('AvailableChainFGCompose.Proofs.Finality.Middle',
     'AvailableChainFGCompose.Proofs.Finality.MiddleSupport'),
    ('AvailableChainFGCompose.Tests.P0d7a3',
     'AvailableChainFGCompose.Proofs.Finality.Middle'),
    ('AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport',
     'AvailableChainFGCompose.Proofs.Finality.MiddleSupport'),
    ('AvailableChainFGSAProofs.Proofs.Finality.Middle',
     'AvailableChainFGCompose.Proofs.Finality.Middle'),
})


# P0d7a4: exact action-row, batch, and carriage entries.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.FinalityRows',
    'AvailableChainFGCompose.Proofs.Finality.Rows',
    'AvailableChainFGCompose.Proofs.Finality.RowsRecords',
    'AvailableChainFGCompose.Proofs.Finality.RowsPrem',
    'AvailableChainFGCompose.Proofs.Finality.Batch',
    'AvailableChainFGCompose.Proofs.Finality.Carry',
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityRows',
     'AvailableChainKitFG.WindowViewsDef'),
})
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Finality.Rows',
     'AvailableChainKitFG.HeightHistoryTransfer'),
    ('AvailableChainFGCompose.Proofs.Finality.Rows',
     'AvailableChainKitFG.WindowTerminal'),
    ('AvailableChainFGCompose.Proofs.Finality.Batch',
     'AvailableChainKitFG.WindowRetention'),
    ('AvailableChainFGCompose.Proofs.Finality.Carry',
     'AvailableChainKitFG.WindowValidity'),
    ('AvailableChainFGCompose.Proofs.Finality.Carry',
     'AvailableChainKitFG.WindowHeightBridge'),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.Rows',
     'AvailableChainFGCompose.Proofs.Finality.Rows'),
    ('AvailableChainFGSAProofs.Proofs.Finality.RowsRecords',
     'AvailableChainFGCompose.Proofs.Finality.RowsRecords'),
    ('AvailableChainFGSAProofs.Proofs.Finality.RowsPrem',
     'AvailableChainFGCompose.Proofs.Finality.RowsPrem'),
    ('AvailableChainFGSAProofs.Proofs.Finality.Batch',
     'AvailableChainFGCompose.Proofs.Finality.Batch'),
    ('AvailableChainFGSAProofs.Proofs.Finality.Carry',
     'AvailableChainFGCompose.Proofs.Finality.Carry'),
})

# P0d7a4: the inhabited interface test uses the owned consumers.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGCompose.Tests.P0d7a4',
     'AvailableChainFGCompose.Proofs.Finality.Rows'),
    ('AvailableChainFGCompose.Tests.P0d7a4',
     'AvailableChainFGCompose.Proofs.Finality.Carry'),
    ('AvailableChainFGCompose.Tests.P0d7a4',
     'AvailableChainFGCompose.Proofs.Finality.RowsRecords'),
})

# X1a: shared execution observation statements and the ordinary-fold instance.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.ExecutionObs',
    'AvailableChainFGCompose.Statements.ExecutionBridges',
    'AvailableChainFGCompose.Statements.ExecutionRecords',
    'AvailableChainFGCompose.Proofs.ExecutionObs',
)

# X1b: strict-cut history and accepted-body origin proofs.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.ExecutionHistory',)

# X1c: holder client observations, proofs and ordinary bridges.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.HolderClient',
    'AvailableChainFGCompose.Proofs.HolderClient',
    'AvailableChainFGCompose.Proofs.OrdinaryHolderClient',
)


# X1e: window views in the additive selected-acceptance statement.
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.ExecutionAcceptance',
     'AvailableChainKitFG.WindowViewsDef'),
})


def compose_base(dep: str) -> bool:
    return (foundation(dep) or under(dep, "AvailableChainModel.Objects")
            or any_under(dep, ("AvailableChainEngineV2.Engine",
                               "AvailableChainEngineV2.Conditions",
                               "AvailableChainEngineV2.Laws.Duty"))
            or pure_statements(dep) or under(dep, SV + ".Duty")
            or dep in {"AvailableChainSimplexFG.Store", KITFG + ".HeightLawsDef"})


def compose_s(ctx: Context, m: Module, dep: str) -> bool:
    if not under(m.name, COMPOSE):
        return False
    if m.facade:
        return dep not in COMPOSE_MODULES
    if under(m.name, COMPOSE + ".Statements"):
        return not (compose_base(dep) or under(dep, COMPOSE + ".Statements")
                    or (m.name, dep) in COMPOSE_SAFETY_IMPORTS)
    return not any_under(m.name, (COMPOSE + ".Proofs", COMPOSE + ".Tests"))


def compose_p(ctx: Context, m: Module, dep: str) -> bool:
    # P0d3: the non-genesis interface fixture uses the proved window height laws.
    if (m.name, dep) in {
        (COMPOSE + ".Tests.P0d3", KITFG + ".WindowHeightBridge"),
    }:
        return False
    if not (under(m.name, COMPOSE + ".Proofs") or under(m.name, COMPOSE + ".Tests")):
        return False
    own = any_under(dep, (COMPOSE + ".Statements", COMPOSE + ".Proofs"))
    if is_test(m.name):
        return not (foundation(dep) or own)
    return not (compose_base(dep) or own
                or dep in {"AvailableChainKitV2.DutyStable", KITFG + ".Correspondence"}
                or (m.name, dep) in COMPOSE_PROOF_IMPORTS)


def upstream_compose(ctx: Context, m: Module, dep: str) -> bool:
    return under(dep, COMPOSE) and not under(m.name, COMPOSE) and (m.name, dep) not in COMPOSE_EDGES


EDGE_RULES: dict[str, Callable[[Context, Module, str], bool]] = {
    "COMPOSE-S": compose_s, "COMPOSE-P": compose_p,
    "UPSTREAM-COMPOSE": upstream_compose,
    "B4": b4, "B6-FACADE": b6_facade, "B6-MATHLIB": b6_mathlib,
    "B6-TACTIC": b6_tactic, "B7-TESTS": b7_tests,
    "GLY-SPURE": gly_spure, "GLY-SV2": gly_sv2, "GLY-SAC": gly_sac,
    "GLY-PPURE": gly_ppure, "GLY-PV2": gly_pv2, "GLY-PAC": gly_pac,
    "GLY-FG": gly_fg, "GLY-AC-USE": gly_ac_use,
    "GLY-KITFG-DEF": gly_kitfg_def, "GLY-KITFG-PROOF": gly_kitfg_proof,
    "GLY-LOCKED": gly_locked, "GLY-NOGEN": gly_nogen, "GLY-WALK": gly_walk,
    "FG-GRID": fg_grid, "RUN": run, "CLAIMS": claims, "LANE": lane,
    "SHARED": shared, "ASSEMBLY": assembly, "CLAIM-USE": claim_use,
    "LANE-CLAIMS": lane_claims, "EXPORT-USE": export_use,
    "INHABIT": inhabit, "TEST-USE": test_use, "TEST-SCOPE": test_scope,
    "PHASES": phases, "CHECK-SUPPORT": check_support,
}
RULE_IDS = set(EDGE_RULES) | {"B7-BODY", "B7-GLOBS"}



def pcsa_findings(ctx: Context, m: Module, dep: str) -> Iterator[Finding]:
    """PC-SA proof-plan §3: keep this policy separate from the FG-SA lanes."""
    def path(name: str) -> tuple[str, ...]:
        if not under(name, PC_PROOFS) or name == PC_PROOFS:
            return ()
        parts = tuple(name.split(".")[1:])
        return parts[1:] if parts[0] == "Proofs" else parts

    parts, target = path(m.name), path(dep)
    claim = under(dep, PC_CLAIMS + ".Claims")
    export = len(parts) == 2 and parts[1] == "Export"
    target_export = len(target) == 2 and target[1] == "Export"
    shared_claims = PC_PROOFS + ".Proofs.Shared.Claims"
    own_claim = export and dep == PC_CLAIMS + ".Claims." + parts[0]
    if claim and not (own_claim or m.name in {
            PC_CLAIMS, PC_CLAIMS + ".PCSAClaims", PC_CLAIMS + ".Tests.Axioms",
            shared_claims}):
        yield ("CLAIM-USE", m.name, dep)
    if target_export and not (parts and parts[0] == "Assembly"):
        yield ("EXPORT-USE", m.name, dep)
    if under(m.name, GEN) and under(dep, PC_PROOFS):
        yield ("GLY-FG", m.name, dep)
    if not parts or parts[0] == "Tests":
        return
    if dep in ctx.facades:
        yield ("B6-FACADE", m.name, dep)
    upstream = (foundation(dep) or any_under(dep, (
        "AvailableChainPCSA.Model", "AvailableChainPCSA.Statements", "AvailableChainPCSA.Proofs",
        "AvailableChainPCSARun.Model", "AvailableChainPCSARun.Statements",
        PC_CLAIMS + ".Statements", GEN, "AvailableChainKitV2", "AvailableChainKitFG",
        "AvailableChainSimplexFG", "AvailableChainFGSA.Model", "AvailableChainFGSA.Statements",
        "AvailableChainFGSA.Proofs", "AvailableChainFGSARun", PROOFS + ".Proofs"))
        or dep == STORE_FACTS or (m.name, dep) in COMPOSE_EDGES)
    # New safety adapters use named FG-SA model producers, never its run claims.
    if m.name in {
            PC_PROOFS + ".Proofs.Foundations.FGSafetyClient",
            PC_PROOFS + ".Proofs.Foundations.FGSafetyStore",
            PC_PROOFS + ".Proofs.Foundations.NamedScope",
            PC_PROOFS + ".Proofs.Foundations.Proposals",
            PC_PROOFS + ".Proofs.Foundations.TickOutput",
            PC_PROOFS + ".Proofs.Foundations.FGSafetyScope",
            PC_PROOFS + ".Proofs.Foundations.FGSafetyClientLaws",
            PC_PROOFS + ".Proofs.Foundations.FGSafetyBridge",
            PC_PROOFS + ".Proofs.Foundations.FinalitySafety"} and any_under(dep, (
                "AvailableChainFGSA", "AvailableChainFGSARun", PROOFS, CLAIMS)):
        upstream = dep in {"AvailableChainFGSA.Proofs.Carrier",
                           "AvailableChainFGSA.Proofs.StoreLaws"}
    if parts[0] == "Assembly":
        allowed = upstream or (target and (target[0] == "Shared" or target_export))
        allowed = allowed or (
            m.name == PC_PROOFS + ".Proofs.Assembly.Formation" and
            dep == PC_PROOFS + ".Proofs.Clean.FormationExport")
        if m.name == PC_PROOFS + ".Proofs.Assembly.Root":
            allowed = foundation(dep) or dep in {
                PC_PROOFS + ".Proofs.Assembly." + name for name in
                ("Foundations", "Shared", "PC", "Small", "AcFrame", "Clean", "Outage",
                 "Finality", "ResetArrival", "WeakContinuation")}
        allowed = allowed or (m.name == PC_PROOFS + ".Proofs.Assembly.Root" and
                              dep == PC_CLAIMS + ".PCSAClaims")
        rule = "ASSEMBLY"
    elif parts[0] == "Shared":
        allowed = upstream or (target and target[0] in {"Shared", "Foundations"} and not target_export)
        allowed = allowed or (m.name == shared_claims and claim) or own_claim
        rule = "SHARED"
    else:
        allowed = upstream or own_claim or (target and target[0] in {
            parts[0], "Foundations", "Shared"} and not target_export)
        rule = "LANE"
    if (parts[0] != "Assembly" and m.name != shared_claims
            and not own_claim and reaches_claims(ctx, dep)):
        yield ("LANE-CLAIMS", m.name, dep)
    if not allowed:
        yield (rule, m.name, dep)


def findings(ctx: Context) -> set[Finding]:
    found = set(b7_globs(ctx))
    for module in ctx.modules.values():
        library_file = module.library is not None and module.path.parts[0] != "scripts"
        if library_file and (body_finding := b7_body(module)):
            found.add(body_finding)
        rules = EDGE_RULES if library_file else {"CHECK-SUPPORT": check_support}
        for dep in module.imports:
            if library_file:
                found.update(pcsa_findings(ctx, module, dep))
            for rule_id, predicate in rules.items():
                if predicate(ctx, module, dep):
                    found.add((rule_id, module.name, dep))
    return found


def read_baseline(path: Path) -> set[Finding]:
    if not path.exists():
        return set()
    result = set()
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 3 or parts[0] not in RULE_IDS:
            raise ValueError(f"{path}:{line_number}: invalid baseline finding")
        result.add(tuple(parts))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent,
                        help="repository or temporary fixture tree")
    parser.add_argument("--write-baseline", action="store_true", help="replace the baseline with current findings")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        ctx = load_context(root)
        current = findings(ctx)
        path = root / BASELINE
        if args.write_baseline:
            path.parent.mkdir(parents=True, exist_ok=True)
            header = ("# Generated with: python3 scripts/check-layers.py --write-baseline\n"
                      "# Initial snapshot: available-chain main 7ac5b0c (2026-09-29).\n"
                      "# Format: rule-id importer imported-module (B7 body/globs use markers).\n")
            path.write_text(header + "".join(" ".join(f) + "\n" for f in sorted(current)), encoding="utf-8")
            new = set()
        else:
            new = current - read_baseline(path)
        # All legacy findings remain visible; baseline matching is exact.
        for finding in sorted(current):
            print(" ".join(finding))
        print(f"check-layers: {len(current)} findings, {len(new)} new"
              + ("; baseline written" if args.write_baseline else ""), file=sys.stderr)
        return 1 if new else 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"check-layers: {error}", file=sys.stderr)
        return 2


# P0d5a: exact generic home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Statements.FrontierSearch',)

# P0d5a: exact frozen-wrapper edges and generic read proof input.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Tests.P0d5a',
     'AvailableChainFGCompose.Statements.FrontierSearch'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs',
     'AvailableChainFGCompose.Statements.FrontierSearch'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSeedDefs',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchStop',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchBudget',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget'),
})
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop',
     'AvailableChainGeneric.Proofs.V2.Duty.Reads'),
    ('AvailableChainFGCompose.Proofs.ExecutionHistory',
     'AvailableChainGeneric.Proofs.V2.Duty.Reads'),
})

COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget',)
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop',)
# P0d7a5: exact receipt and acceptance entries.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Proofs.Finality.RestoreReads',
    'AvailableChainFGCompose.Proofs.Finality.Receipt',
    'AvailableChainFGCompose.Proofs.Finality.Accept',
)
COMPOSE_SAFETY_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Statements.FinalityReceipts',
     'AvailableChainSimplexFG.WindowStore'),
})
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Finality.RestoreReads',
     'AvailableChainGeneric.Proofs.V2.Duty.Reads'),
    ('AvailableChainFGCompose.Proofs.Finality.RestoreReads',
     'AvailableChainKitFG.Ancestry'),
    ('AvailableChainFGCompose.Proofs.Finality.Receipt',
     'AvailableChainKitFG.FrameGeometry'),
    ('AvailableChainFGCompose.Proofs.Finality.Receipt',
     'AvailableChainGeneric.Proofs.V2.Duty.Reads'),
    ('AvailableChainFGCompose.Proofs.Finality.Accept',
     'AvailableChainKitFG.FrameGeometry'),
    ('AvailableChainFGCompose.Proofs.Finality.Accept',
     'AvailableChainKitFG.WindowStore'),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.RestoreReads',
     'AvailableChainFGCompose.Proofs.Finality.RestoreReads'),
    ('AvailableChainFGSAProofs.Proofs.Finality.Receipt',
     'AvailableChainFGCompose.Proofs.Finality.Receipt'),
    ('AvailableChainFGSAProofs.Proofs.Finality.Accept',
     'AvailableChainFGCompose.Proofs.Finality.Accept'),
})

# P0d5b: exact generic homes.
COMPOSE_MODULES += ('AvailableChainFGCompose.Statements.FrontierMaturity',
                    'AvailableChainFGCompose.Proofs.Healing.PromotionSource',
                    'AvailableChainFGCompose.Proofs.Healing.PromotionAge',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchAge',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchHG2a',)

# P0d5b: exact frozen-wrapper edges.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.PromotionSource',
     'AvailableChainFGCompose.Proofs.Healing.PromotionSource'),
    ('AvailableChainFGSAProofs.Proofs.Healing.PromotionAge',
     'AvailableChainFGCompose.Proofs.Healing.PromotionAge'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchAge',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchAge'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchHG2a'),
})
# P0d5c: exact generic homes.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise',)

# P0d5c: exact frozen-wrapper edges.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRepair',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchGap',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTop',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail'),
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRise',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise'),
})
# P0d5d-a: exact generic home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchCompose',)

# P0d5d-a: exact frozen-wrapper edge.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchCompose',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchCompose'),
})
# P0d7b-a: exact generic finality kernel entries.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Finality.Kernel',)
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.Kernel',
     'AvailableChainFGCompose.Proofs.Finality.Kernel'),
})

# P0d5d-b: exact generic homes.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.FrontierSearchTasks',
                    'AvailableChainFGCompose.Proofs.Healing.FrontierSearchFull',)

# P0d5d-b: exact frozen-wrapper edge.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTasks',
     'AvailableChainFGCompose.Proofs.Healing.FrontierSearchTasks'),
})
# P0d6b: exact generic home.
COMPOSE_MODULES += ('AvailableChainFGCompose.Proofs.Healing.Reset',)

# P0d6b: exact frozen-wrapper edge.
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Healing.Reset',
     'AvailableChainFGCompose.Proofs.Healing.Reset'),
})
# P0d7b-b: exact generic finality exporter entries.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Proofs.Finality.Joined',
    'AvailableChainFGCompose.Proofs.Finality.Forward',
    'AvailableChainFGCompose.Proofs.Finality.Local',
)
COMPOSE_PROOF_IMPORTS |= frozenset({
    ('AvailableChainFGCompose.Proofs.Finality.Forward',
     'AvailableChainGeneric.Proofs.Pure.ScheduleW'),
    ('AvailableChainFGCompose.Proofs.Finality.Local',
     'AvailableChainGeneric.Proofs.Pure.BlockOrder'),
})
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Proofs.Finality.Forward',
     'AvailableChainFGCompose.Proofs.Finality.Forward'),
})

# P0-origin: the origin store record and its consumers; one FG-SA test edge.
COMPOSE_MODULES += (
    'AvailableChainFGCompose.Statements.SafetyOrigin',
    'AvailableChainFGCompose.Proofs.SafetyOrigin',
)
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Tests.P0Origin',
     'AvailableChainFGCompose.Proofs.SafetyOrigin'),
})

# P0d7c: exact private test-adapter edges (generic finality chain G0).
COMPOSE_EDGES |= frozenset({
    ('AvailableChainFGSAProofs.Tests.P0d7c',
     'AvailableChainFGCompose.Proofs.Finality.Joined'),
    ('AvailableChainFGSAProofs.Tests.P0d7c',
     'AvailableChainFGCompose.Proofs.Finality.Local'),
})

if __name__ == "__main__":
    sys.exit(main())
