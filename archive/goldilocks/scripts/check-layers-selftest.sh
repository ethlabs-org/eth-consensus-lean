#!/usr/bin/env bash
# Run all controls, or one named rule: bash scripts/check-layers-selftest.sh B4
# All fixture files are in a temporary directory. No Lean build is needed.
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec "${PYTHON:-python3}" -u -B - "$script_dir" "$@" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import tomllib

scripts = Path(sys.argv[1])
repo = scripts.parent
checker = scripts / "check-layers.py"
api = runpy.run_path(str(checker), run_name="check_layers_selftest")
rule_ids = api["RULE_IDS"]
selected = sys.argv[2:]
if len(selected) > 1 or (selected and selected[0] not in rule_ids):
    raise SystemExit("usage: check-layers-selftest.sh [RULE-ID]")

CO = "AvailableChainFGCompose"
G = "AvailableChainGeneric"
K = "AvailableChainKitFG"
F = "AvailableChainFGSA"
R = "AvailableChainFGSARun"
C = "AvailableChainFGSAClaims"
P = "AvailableChainFGSAProofs"
ASSEMBLY_ROOT = P + ".Proofs.Assembly.Root"
I = "AvailableChainFGSAInhabit"
X = "AvailableChainRegistry"
SP = G + ".Statements.Pure"
SV = G + ".Statements.V2"
SA = G + ".Statements.AC"
PP = G + ".Proofs.Pure"
PV = G + ".Proofs.V2"
PA = G + ".Proofs.AC"

# Each control adds precisely one finding, with the named rule ID. Targets
# need not exist: this is a text check, not an elaboration check.
controls = {
    "COMPOSE-S": (CO + ".Statements.Control", "AvailableChainSA.Model.Protocol"),
    "COMPOSE-P": (CO + ".Proofs.Control", "AvailableChainSA.Model.Protocol"),
    "UPSTREAM-COMPOSE": (X + ".Control", CO + ".Statements.EventReads"),
    "B4": (F + ".Model.Control", F + ".Proofs.Helper"),
    "B6-FACADE": (X + ".Control", "AvailableChainFramework"),
    "B6-MATHLIB": (X + ".Proofs.Control", "Mathlib"),
    "B6-TACTIC": (K + ".Control", "Mathlib.Tactic"),
    "B7-TESTS": (X, X + ".Tests.Helper"),
    "B7-BODY": (X, None),
    "B7-GLOBS": (X + ".Control", None),
    "GLY-SPURE": (SP + ".Control", "AvailableChainModel.Generic.Run"),
    "GLY-SV2": (SV + ".Control", "AvailableChainModel.Generic.Run"),
    "GLY-SAC": (SA + ".Control", "AvailableChainSA.Statements.Contract"),
    "GLY-PPURE": (PP + ".Control", "AvailableChainEngineV2.Engine.Run"),
    "GLY-PV2": (PV + ".Control", "AvailableChainSA.Model.Protocol"),
    "GLY-PAC": (PA + ".Control", "AvailableChainSAPC.Model.Protocol"),
    "GLY-FG": (G, "AvailableChainSimplexFG.Objects"),
    "GLY-AC-USE": (X + ".Control", SA + ".Reads"),
    "GLY-KITFG-DEF": (K + ".ViewLock", SP + ".Walk"),
    "GLY-KITFG-PROOF": (K + ".Control", PP + ".Walk"),
    "GLY-LOCKED": ("AvailableChainFramework.Hooks", SP + ".Walk"),
    "GLY-NOGEN": ("AvailableChainSimplexFG.Control", SP + ".Quorum"),
    "GLY-WALK": ("AvailableChainGridCO.Model.Walk", "AvailableChainModel.Generic.Run"),
    "FG-GRID": (K + ".Control", "AvailableChainGridCO.Proofs.Map"),
    "RUN": (R + ".Proofs.Control", "AvailableChainKit.Engine.Clock"),
    "CLAIMS": (C + ".Statements.Control", "AvailableChainModel.Generic.Run"),
    "LANE": (P + ".Proofs.F1.Control", P + ".Proofs.F2.Helper"),
    "SHARED": (P + ".Proofs.Shared.Control", P + ".Proofs.F1.Helper"),
    "ASSEMBLY": (P + ".Proofs.Assembly.Control", P + ".Proofs.F1.Helper"),
    "CLAIM-USE": (X + ".Control", C + ".Claims.F1"),
    "LANE-CLAIMS": (P + ".Proofs.F1.Control", P + ".Proofs.Shared.Claims"),
    "EXPORT-USE": (X + ".Control", P + ".Proofs.F1.Export"),
    "INHABIT": (I + ".Control", "AvailableChainFramework.Hooks"),
    "TEST-USE": (X + ".Proofs.Control", X + ".Tests.Helper"),
    "TEST-SCOPE": (X + ".Tests.Control", "AvailableChainModel.Objects.Blocks"),
    "PHASES": (X + ".Control", C + ".Statements.PhasesInternal"),
    "CHECK-SUPPORT": (X + ".Control", "AvailableChainCheckSupport.GeneratedOwner"),
}
assert controls.keys() == rule_ids, (controls.keys() ^ rule_ids)

config = tomllib.loads((repo / "lakefile.toml").read_text())
lib_names = sorted({lib["name"] for lib in config["lean_lib"]} | api["FUTURE_LIBS"])
tests_libs = {x + "Tests" for x in (C, P, I, api["PC_PROOFS"])}


def put(root, relative, text):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def module(root, name, dep=None, form="public import", body="", src=""):
    relative = Path(src).joinpath(*name.split(".")).with_suffix(".lean")
    return put(root, relative, "module\n" + (f"{form} {dep}\n" if dep else "") + body)


def setup(root):
    text = 'name = "check-layers-fixture"\n'
    for name in lib_names:
        support = name == "AvailableChainCheckSupport"
        suffix = ".+" if support else ".*"
        text += f'\n[[lean_lib]]\nname = {json.dumps(name)}\n'
        if name in tests_libs:  # F0.0b Tests targets: submodules of the owner.
            text += f'roots = []\nglobs = [{json.dumps(name.removesuffix("Tests") + ".Tests.+")}]\n'
        else:
            text += f'globs = [{json.dumps(name + suffix)}]\n'
        if support:
            text += 'srcDir = "scripts"\n'
    put(root, "lakefile.toml", text)
    for relative in ("scripts/CatalogLock.lean", "scripts/baselines/kitfg-def-modules.txt"):
        put(root, relative, (repo / relative).read_text(encoding="utf-8"))
    for line in (repo / "scripts/baselines/kitfg-def-modules.txt").read_text().splitlines():
        name = line.split("#", 1)[0].strip()
        if name:
            module(root, K + "." + name)


def run(root, expected_code, expected=None, extra=()):
    command = [sys.executable, "-B", str(checker), "--root", str(root), *extra]
    result = subprocess.run(command, text=True, capture_output=True)
    found = {tuple(line.split()) for line in result.stdout.splitlines()}
    assert result.returncode == expected_code, (command, result.returncode, result.stdout, result.stderr)
    if expected is not None:
        assert found == set(expected), (command, "expected", expected, "found", found, result.stderr)
    return found


def snapshot():
    # Read-only fingerprint of the worktree, including untracked files.
    # Build output and Git metadata are outside the self-test's scope.
    result = {}
    for current, dirs, files in os.walk(repo):
        dirs[:] = [name for name in dirs if not name.startswith(".")]
        for name in files:
            path = Path(current) / name
            if not name.startswith("."):
                result[str(path.relative_to(repo))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


before = snapshot()
with tempfile.TemporaryDirectory(prefix="check-layers-selftest-") as temporary:
    temp = Path(temporary)
    for rule in selected or controls:
        root = temp / rule
        setup(root)
        run(root, 0, set())  # Missing future libraries/modules pass vacuously.
        importer, dep = controls[rule]
        module(root, importer, dep)
        if rule == "B6-TACTIC":
            module(root, K + ".Consumer", importer)
        elif rule == "B7-BODY":
            module(root, importer, body="def value : Nat := 0\n")
            dep = "<body:def>"
        elif rule == "B7-GLOBS":
            path = root / "lakefile.toml"
            path.write_text(path.read_text().replace(f'globs = ["{X}.*"]\n', ""))
            importer, dep = X, f"<globs:{X}.*>"
        run(root, 1, {(rule, importer, dep)})
        print(f"PASS {rule}: python3 scripts/check-layers.py --root <temp> -> exit 1; one exact finding")

    if not selected:
        for index, (importer, dep, rule) in enumerate([
            (CO + ".Statements.Control", CO + ".Proofs.SourceHead", "COMPOSE-S"),
            (CO + ".Helper", F + ".Model.Store", "COMPOSE-S"),
            (CO + ".Model.Orphan", SV + ".Duty.Reads", "COMPOSE-S"),
            (CO, SV + ".Duty.Reads", "COMPOSE-S"),
            (CO + ".Statements.Control", "AvailableChainKitV2.DutyStable", "COMPOSE-S"),
            (CO + ".Statements.Control", K + ".Correspondence", "COMPOSE-S"),
            ("AvailableChainPCSARun.Model.Protocol", CO + ".Statements.EventReads", "UPSTREAM-COMPOSE"),
            ("AvailableChainPCSAClaims.Statements.Reads", CO + ".Statements.CoreReads", "UPSTREAM-COMPOSE"),
            *[(CO + ".Proofs.Control", dep, "COMPOSE-P") for dep in
              [F + ".Model.Store", "AvailableChainPCSA.Model.Store",
               "AvailableChainGridCO.Model.Protocol", "AvailableChainSA.Model.Protocol",
               "AvailableChainFramework.Hooks", SA + ".Reads", SP + ".Walk",
               "AvailableChainKitV2.DutyStable.Extra", K + ".HeightLawsDef.Extra"]],
            *[(importer, CO + ".Statements.EventReads", "UPSTREAM-COMPOSE") for importer in
              [G + ".Statements.Pure.Control", K + ".Control",
               "AvailableChainEngineV2.Engine.Control", "AvailableChainFramework.Hooks",
               F + ".Model.Store", C + ".Statements.Control", R + ".Model.Control",
               I + ".Control", P + ".Proofs.Shared.Claims", P + ".Proofs.Finality.Control",
               P + ".Proofs.Shared.FGCompose.Extra"]],
            (P + ".Proofs.Shared.FGCompose", CO + ".Statements.EventReads.Extra", "UPSTREAM-COMPOSE"),
        ]):
            root = temp / f"compose-boundary-{index}"
            setup(root)
            module(root, importer, dep)
            found = run(root, 1)
            assert (rule, importer, dep) in found, (rule, found)
        print("PASS Compose closed boundaries and exact edge neighbors")
        for index, (importer, dep) in enumerate([
            (CO + ".Statements.EventReads", SV + ".Duty.Reads"),
            (CO + ".Statements.CoreReads", "AvailableChainSimplexFG.Store"),
            (CO + ".Statements.CoreReads", K + ".HeightLawsDef"),
            (CO + ".Proofs.SourceHead", "AvailableChainKitV2.DutyStable"),
            (CO + ".Proofs.SourceHead", K + ".Correspondence"),
            *sorted(api["COMPOSE_EDGES"]),
            *sorted(api["COMPOSE_SAFETY_IMPORTS"]),
            *sorted(api["COMPOSE_PROOF_IMPORTS"]),
        ]):
            root = temp / f"compose-positive-{index}"
            setup(root)
            module(root, importer, dep)
            run(root, 0, set())
        print("PASS Compose positive exact edges")
        for index, (importer, dep) in enumerate(sorted(api["COMPOSE_SAFETY_IMPORTS"])):
            for neighbor, target in ((importer + ".Extra", dep), (importer, dep + ".Extra")):
                root = temp / f"safety-boundary-{index}-{neighbor}-{target}"
                setup(root)
                module(root, neighbor, target)
                # Some imports were already allowed by the step-1 base policy.
                if api["compose_base"](target):
                    run(root, 0, set())
                else:
                    found = run(root, 1)
                    assert ("COMPOSE-S", neighbor, target) in found, found
        # Negative controls: a neighbour of an exact proof edge must still fail.
        for index, (importer, dep) in enumerate(sorted(api["COMPOSE_PROOF_IMPORTS"])):
            for neighbor, target in ((importer + ".Extra", dep), (importer, dep + ".Extra")):
                root = temp / f"safety-proof-boundary-{index}-{neighbor}-{target}"
                setup(root)
                module(root, neighbor, target)
                found = run(root, 1)
                assert ("COMPOSE-P", neighbor, target) in found, found
        for index, (importer, dep) in enumerate([
            (CO + ".Proofs.SafetyStore", K + ".AccountableCore"),
            (CO + ".Proofs.SafetyAccountable", K + ".ClientOnce"),
        ]):
            root = temp / f"safety-proof-other-{index}"
            setup(root)
            module(root, importer, dep)
            found = run(root, 1)
            assert ("COMPOSE-P", importer, dep) in found, found
        print("PASS Safety exact external edges and neighbors")
        # Lead ruling 2026-10-07 (P2, S3a): other importers and other targets fail.
        proof_negatives = []
        for importer, dep in sorted(api["COMPOSE_PROOF_IMPORTS"]):
            proof_negatives += [(CO + ".Proofs." + other, dep, "COMPOSE-P")
                                for other in ("SafetyCount", "SafetyMonotone", "SafetySlashing",
                                              "SourceHead", "Control")]
            proof_negatives += [(CO + ".Statements.SafetyClient", dep, "COMPOSE-S"),
                                (CO + ".Tests.SafetyReads", dep, "COMPOSE-P")]
        proof_negatives += [(CO + ".Proofs.SafetyClient", dep, "COMPOSE-P") for dep in
                            [K + ".ClientOnce", K + ".AccountableCore", K + ".ClientOnceSafety.Extra",
                             PV + ".Duty", PV + ".Duty.LinkedHolders", PP + ".Quorum",
                             G + ".Proofs.V2.Duty.Fields.Extra"]]
        for index, (importer, dep, rule) in enumerate(proof_negatives):
            root = temp / f"compose-proof-boundary-{index}"
            setup(root)
            module(root, importer, dep)
            found = run(root, 1)
            assert (rule, importer, dep) in found, (rule, importer, dep, found)
        print("PASS Compose Proofs exact external edges and neighbors")
        # Lead ruling 2026-10-08 (P3, S3b): the facade imports the exact P3 module only.
        root = temp / "compose-facade-slashing"
        setup(root)
        module(root, CO, CO + ".Proofs.SafetySlashing")
        run(root, 0, set())
        root = temp / "compose-facade-slashing-extra"
        setup(root)
        module(root, CO, CO + ".Proofs.SafetySlashing.Extra")
        found = run(root, 1)
        assert ("COMPOSE-S", CO, CO + ".Proofs.SafetySlashing.Extra") in found, found
        print("PASS Compose facade P3 module and neighbor")
        for index, (importer, dep) in enumerate(sorted(api["COMPOSE_EDGES"])):
            if not any(name in importer for name in ("FGSafetyClient", "FGSafetyBridge")):
                continue
            for neighbor, target in ((importer + ".Extra", dep), (importer, dep + ".Extra")):
                root = temp / f"safety-adapter-{index}-{neighbor}-{target}"
                setup(root)
                module(root, neighbor, target)
                found = run(root, 1)
                assert ("UPSTREAM-COMPOSE", neighbor, target) in found, found
        for index, (importer, dep) in enumerate([
            ("AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient",
             R + ".Proofs.Protocol"),
            ("AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore",
             R + ".Proofs.Reachable"),
            ("AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge",
             R + ".Proofs.Reachable"),
            ("AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore",
             "AvailableChainPCSAProofs.Proofs.AcFrame.Store"),
            ("AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore",
             F + ".Proofs.StoreLaws.Extra"),
        ]):
            root = temp / f"safety-forbidden-{index}"
            setup(root)
            module(root, importer, dep)
            found = run(root, 1)
            assert ("LANE", importer, dep) in found, found
        print("PASS Safety adapters, run exclusion, and AcFrame lane STOP")



        # Real-file header controls. Each spelling must produce the same
        # edge, including newlines, nested comments and quoted identifiers.
        forms = ["import", "public import", "meta import", "public meta import",
                 "import all", "meta import all", "public import all", "public meta import all",
                 "public\n/- outer /- inner -/ end -/ meta\nimport\nall"]
        for index, form in enumerate(forms):
            root = temp / f"header-{index}"
            setup(root)
            module(root, X + ".Control", "«Mathlib»", form=form,
                   body='/- import AvailableChainCheckSupport.Fake -/\n'
                        'def text := "import AvailableChainCheckSupport.Fake"\n')
            run(root, 1, {("B6-MATHLIB", X + ".Control", "Mathlib")})
        print("PASS header syntax: 9 forms -> exit 1; comments and body text ignored")

        # Positive controls cover the narrow allowances. Use separate trees
        # so a proof's importer does not change the leaf-tactic test.
        positives = [
            (SP + ".Quorum", "AvailableChainModel.Objects.Blocks"),
            (SP + ".Other", SP + ".Quorum"),
            (SP + ".Walk", "AvailableChainGridCO.Model.Walk"),
            (PP + ".Walk", "AvailableChainGridCO.Model.Walk"),
            (PP + ".Numeric", SP + ".Quorum"),
            (SV + ".Reads", "AvailableChainKitV2.ClockLaws"),
            (SV + ".Reads", "AvailableChainKitV2.DutyClockLaws"),
            (SV + ".Reads", "AvailableChainEngineV2.Conditions.Interface"),
            (SA + ".Reads", "AvailableChainSA.Model.Protocol"),
            (PV + ".Receipt", "AvailableChainKitV2.Receipt"),
            (PA + ".Votes", "AvailableChainGridCO.Model.Protocol"),
            (K + ".StoreInvDef", SP + ".Quorum"),
            (K + ".ViewLock", SP + ".Quorum"),
            (K + ".HonestRows", SP + ".Quorum"),
            (K + ".WeightsBridge", SP + ".Quorum"),
            (K + ".QuorumFacts", PP + ".Quorum"),
            ("AvailableChainFramework.Hooks", SP + ".Quorum"),
            ("AvailableChainFramework.Catalog.Control", SV + ".Reads"),
            ("AvailableChainGridCO.Model.Walk", "AvailableChainModel.Objects.Blocks"),
            (F + ".Proofs.Control", "AvailableChainGridCO.Proofs.StoreFacts"),
            (K + ".Control", "AvailableChainGridCO.Proofs.StoreFacts"),
            (R + ".Proofs.Control", F + ".Proofs.StoreInv"),
            (C + ".Statements.Control", R + ".Statements.Control"),
            (C + ".Statements.Control", K + ".HonestRows"),
            (P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper"),
            (P + ".F1.Control", P + ".Shared.Reads"),
            (P + ".Proofs.F1.Control", C + ".Statements.ChannelProps"),
            (P + ".Proofs.F1.Export", C + ".Claims.F1"),
            (P + ".F1.Export", C + ".Claims.F1"),
            (P + ".Proofs.Assembly.Control", P + ".Proofs.F1.Export"),
            (P + ".Assembly.Control", P + ".F1.Export"),
            (P + ".Proofs.Shared.Control", F + ".Proofs.StoreInv"),
            (P + ".Proofs.F4.Control", C + ".Statements.PhasesInternal"),
            (P + ".Finality.Control", C + ".Statements.PhasesInternal"),
            (I + ".Control", C + ".Statements.ChannelProps"),
            (X + ".Tests.Control", X + ".Proofs.Control"),
            (X + ".Tests.Control", "Mathlib.Tactic"),
            (X + ".Proofs.Leaf", "Mathlib.Tactic"),
            (X, X + ".Proofs.Helper"),
            (X + ".Control", "AvailableChainCheckSupportExtra.Helper"),
            # L42: the exact modules that may import Claims/*.
            (C, C + ".Claims.Clean"),
            (C + ".FGSAClaims", C + ".Claims.Clean"),
            (C + ".Tests.Axioms", C + ".Claims.Clean"),
            (P + ".Proofs.Shared.Claims", C + ".Claims.Clean"),
            (P + ".Proofs.Shared.Claims", C + ".Claims"),
            # R-F1 D6: the modules that may import Shared.Claims.
            (P + ".Proofs.F1.Export", P + ".Proofs.Shared.Claims"),
            (P + ".Proofs.Assembly.Control", P + ".Proofs.Shared.Claims"),
            (P + ".Tests.Axioms", P + ".Proofs.Shared.Claims"),
            (P, P + ".Proofs.Shared.Claims"),
            # L50: the Shared Export.
            (P + ".Proofs.Shared.Export", C + ".Claims.Shared"),
            (P + ".Proofs.Shared.Export", P + ".Proofs.Shared.Reads"),
            (P + ".Proofs.Assembly.Control", P + ".Proofs.Shared.Export"),
            # SYN L58: exact root and named lower Assembly imports only.
            (ASSEMBLY_ROOT, C + ".FGSAClaims"),
            (ASSEMBLY_ROOT, P + ".Proofs.Assembly.Foundations"),
            (ASSEMBLY_ROOT, P + ".Proofs.Assembly.Shared"),
            (ASSEMBLY_ROOT, P + ".Proofs.Assembly.Clean"),
            (ASSEMBLY_ROOT, "Lean.Elab.Command"),
            (P, ASSEMBLY_ROOT),
        ]
        for index, (importer, dep) in enumerate(positives):
            root = temp / f"positive-{index}"
            setup(root)
            module(root, importer, dep)
            run(root, 0, set())
        print(f"PASS allowed imports: {len(positives)} cases -> exit 0")

        # Boundary tests can match more than one rule. They ensure that a
        # specific exception or a file-name component cannot widen a set.
        boundaries = [
            (R + ".Proofs.Control", R, "B6-FACADE"),
            (C + ".Statements.Control", C, "B6-FACADE"),
            (P + ".F1.Control", P, "B6-FACADE"),
            (I + ".Control", I, "B6-FACADE"),
            (SP + ".Control", "Lean.Elab.Command", "GLY-SPURE"),
            (SV + ".Control", "AvailableChainKitV2.Other", "GLY-SV2"),
            (SV + ".Control", "AvailableChainKitV2.ClockLaws.Extra", "GLY-SV2"),
            (SV + ".Control", "AvailableChainKitV2.DutyClockLaws.Extra", "GLY-SV2"),
            (SV + ".Control", "AvailableChainKitV2.DutyRecord", "GLY-SV2"),
            (SP + ".Control", "AvailableChainGridCO.Model.Walk", "GLY-SPURE"),
            (SP + ".Walk", "AvailableChainGridCO.Model.WalkExtra", "GLY-SPURE"),
            (PP + ".Control", "AvailableChainGridCO.Model.Walk", "GLY-PPURE"),
            (SV + ".Control", SP + ".Walk", "GLY-SV2"),
            (K + ".StoreInvDef", PP + ".Quorum", "GLY-KITFG-DEF"),
            (K + ".HonestRows", SV + ".Reads", "GLY-KITFG-DEF"),
            (K + ".Proof", SP + ".Walk", "GLY-KITFG-PROOF"),
            (K + ".WeightsBridge", PP + ".Quorum", "GLY-KITFG-PROOF"),
            ("AvailableChainFramework.Catalog.Control", PP + ".Quorum", "GLY-LOCKED"),
            ("AvailableChainFramework.V2.Control", SA + ".Reads", "GLY-LOCKED"),
            ("AvailableChainGridCO.Model.Control", SP + ".Quorum", "GLY-NOGEN"),
            (F + ".Proofs.Control", "AvailableChainGridCO.Proofs.StoreFacts.Extra", "FG-GRID"),
            (R + ".Proofs.Control", "AvailableChainModel.Generic.Run", "RUN"),
            (C + ".Statements.Control", R + ".Proofs.Control", "CLAIMS"),
            (P + ".F1.Control", P + ".F2.Model.Hidden", "LANE"),
            (P + ".Shared.Control", P + ".F1.Statements.Hidden", "SHARED"),
            (P + ".Shared.Control", P + ".Assembly.Control", "SHARED"),
            (P + ".Shared.Control", P + ".F1.Export", "SHARED"),
            (P + ".F1.Export", C + ".Claims.F2", "CLAIM-USE"),
            (P + ".F1.Control", P + ".F1.Export", "EXPORT-USE"),
            (P + ".Assembly.Control", C + ".Claims.F1", "CLAIM-USE"),
            (I + ".Control", P + ".F1.Control", "INHABIT"),
            (P + ".Proofs.F5.Control", C + ".Statements.PhasesInternal", "PHASES"),
            # L42 negatives: any other module that imports Claims/* is rejected;
            # the Shared.Claims exception covers Claims/* only.
            (C + ".Statements.Control", C + ".Claims.Clean", "CLAIM-USE"),
            (C + ".FGSAClaims.Extra", C + ".Claims.Clean", "CLAIM-USE"),
            (C + ".Tests.Control", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Other", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Other", C + ".Claims.Clean", "SHARED"),
            (P + ".Shared.Claims", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Claims", P + ".Proofs.F1.Helper", "SHARED"),
            # L50 negatives: only Shared/Export imports Claims/Shared; it imports
            # Shared proofs and Claims/Shared only; only Assembly imports it.
            (P + ".Proofs.Shared.Reads", C + ".Claims.Shared", "CLAIM-USE"),
            (P + ".Proofs.Shared.Claims", C + ".Claims.Shared", "CLAIM-USE"),
            (P + ".Proofs.F1.Control", C + ".Claims.Shared", "CLAIM-USE"),
            (P + ".Proofs.F1.Control", P + ".Proofs.Shared.Export", "EXPORT-USE"),
            (P + ".Proofs.F1.Control", P + ".Proofs.Shared.Export", "LANE"),
            (P + ".Proofs.Shared.Reads", P + ".Proofs.Shared.Export", "EXPORT-USE"),
            (P, P + ".Proofs.Shared.Export", "EXPORT-USE"),
            (P + ".Proofs.Shared.Export", P + ".Proofs.F1.Helper", "SHARED"),
            (P + ".Proofs.Shared.Export", G + ".Proofs.Pure.Quorum", "SHARED"),
            (P + ".Proofs.Shared.Export", C + ".Claims.F1", "SHARED"),
            # SYN L58: no sibling exception, return edge or broader root set.
            (P + ".Proofs.Assembly.Control", C + ".FGSAClaims", "ASSEMBLY"),
            (P + ".Proofs.Assembly.RootExtra", C + ".FGSAClaims", "ASSEMBLY"),
            (ASSEMBLY_ROOT + ".Extra", C + ".FGSAClaims", "ASSEMBLY"),
            (P + ".Proofs.Assembly.Control", ASSEMBLY_ROOT, "ASSEMBLY"),
            (ASSEMBLY_ROOT, C, "ASSEMBLY"),
            (ASSEMBLY_ROOT, P, "ASSEMBLY"),
            (ASSEMBLY_ROOT, P + ".Proofs.Foundations.Store", "ASSEMBLY"),
            (ASSEMBLY_ROOT, P + ".Proofs.Foundations.Export", "ASSEMBLY"),
            (ASSEMBLY_ROOT, P + ".Proofs.Assembly.Other", "ASSEMBLY"),
            (ASSEMBLY_ROOT, P + ".Proofs.Assembly.Foundations.Extra", "ASSEMBLY"),
            (ASSEMBLY_ROOT, P + ".Tests.Axioms", "ASSEMBLY"),
            (ASSEMBLY_ROOT, I + ".Control", "ASSEMBLY"),
            (ASSEMBLY_ROOT, C + ".Claims.Clean", "CLAIM-USE"),
            (ASSEMBLY_ROOT, C + ".Statements.PhasesInternal", "PHASES"),
        ]
        for index, (importer, dep, rule) in enumerate(boundaries):
            root = temp / f"boundary-{index}"
            setup(root)
            module(root, importer, dep)
            result = run(root, 1)
            assert (rule, importer, dep) in result, (rule, result)
        print(f"PASS rule boundaries: {len(boundaries)} cases -> exit 1")

        # PC-SA uses the same boundaries, with Foundations as a common lane.
        pc, cc = api["PC_PROOFS"], api["PC_CLAIMS"]
        pc_positives = [
            (pc + ".Proofs.Assembly.Root", pc + ".Proofs.Assembly.Small"),
            (pc + ".Proofs.Assembly.Root", cc + ".PCSAClaims"),
            (cc + ".Claims.PC", cc + ".Statements.Reads"),
            (pc + ".Proofs.PC.Store", pc + ".Proofs.Foundations.Store"),
            (pc + ".Proofs.PC.Store", pc + ".Proofs.Shared.Reads"),
            (pc + ".Proofs.PC.Export", cc + ".Claims.PC"),
            (pc + ".Proofs.Shared.Claims", cc + ".Claims.PC"),
            (pc + ".Proofs.Assembly.PC", pc + ".Proofs.PC.Export"),
            (pc + ".Proofs.Assembly.Formation", pc + ".Proofs.Clean.FormationExport"),
        ]
        for index, (importer, dep) in enumerate(pc_positives):
            root = temp / f"pcsa-positive-{index}"
            setup(root)
            module(root, importer, dep)
            run(root, 0, set())
        pc_negatives = [
            (cc + ".Claims.PC", pc + ".Proofs.Foundations.Store", "CLAIMS"),
            (pc + ".Proofs.Shared.Other", pc + ".Proofs.Shared.Claims", "LANE-CLAIMS"),
            (pc + ".Proofs.Assembly.PC", pc + ".Proofs.Assembly.Clean", "ASSEMBLY"),
            (pc + ".Proofs.Assembly.Formation", pc + ".Proofs.Clean.Store", "ASSEMBLY"),
            (pc + ".Proofs.Assembly.PC", pc + ".Proofs.Clean.FormationExport", "ASSEMBLY"),
            (pc + ".Proofs.PC.Store", pc + ".Proofs.Clean.Store", "LANE"),
            (pc + ".Proofs.Shared.Reads", pc + ".Proofs.Clean.Store", "SHARED"),
            (pc + ".Proofs.Assembly.PC", pc + ".Proofs.PC.Store", "ASSEMBLY"),
            (pc + ".Proofs.PC.Export", cc + ".Claims.Clean", "CLAIM-USE"),
            (cc + ".Claims.PC", cc + ".Claims.Clean", "CLAIM-USE"),
            (pc + ".Proofs.PC.Store", pc + ".Proofs.Shared.Claims", "LANE-CLAIMS"),
            (pc + ".Proofs.Clean.Store", pc + ".Proofs.PC.Export", "EXPORT-USE"),
        ]
        for index, (importer, dep, rule) in enumerate(pc_negatives):
            root = temp / f"pcsa-negative-{index}"
            setup(root)
            module(root, importer, dep)
            assert (rule, importer, dep) in run(root, 1)
        root = temp / "pcsa-export-transitive"
        setup(root)
        module(root, pc + ".Proofs.Shared.Claims", cc + ".Claims.Clean")
        module(root, pc + ".Proofs.PC.Export", pc + ".Proofs.Shared.Claims")
        run(root, 1, {("LANE-CLAIMS", pc + ".Proofs.PC.Export",
                       pc + ".Proofs.Shared.Claims")})
        root = temp / "pcsa-transitive"
        setup(root)
        module(root, pc + ".Proofs.Shared.Mid", pc + ".Proofs.Shared.Claims")
        module(root, pc + ".Proofs.PC.Store", pc + ".Proofs.Shared.Mid")
        assert ("LANE-CLAIMS", pc + ".Proofs.PC.Store",
                pc + ".Proofs.Shared.Mid") in run(root, 1)
        print("PASS PC-SA lanes: positive, negative and transitive controls")

        # R-F1 D6 is transitive: a lane helper that imports Shared.Claims
        # taints every lane module that imports the helper.
        root = temp / "lane-claims-transitive"
        setup(root)
        module(root, P + ".Proofs.F1.Helper", P + ".Proofs.Shared.Claims")
        module(root, P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper")
        module(root, P + ".Proofs.F1.Export", P + ".Proofs.F1.Helper")
        run(root, 1, {("LANE-CLAIMS", P + ".Proofs.F1.Helper", P + ".Proofs.Shared.Claims"),
                      ("LANE-CLAIMS", P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper")})
        root = temp / "lane-claims-via-shared"
        setup(root)
        module(root, P + ".Proofs.Shared.Mid", P + ".Proofs.Shared.Claims")
        module(root, P + ".F2.Control", P + ".Shared.Mid")
        module(root, P + ".Shared.Mid", C + ".Claims.F2")
        found = run(root, 1)
        assert ("LANE-CLAIMS", P + ".F2.Control", P + ".Shared.Mid") in found, found
        assert not any(f[0] == "LANE-CLAIMS" and f[1].startswith(P + ".Proofs.Shared") for f in found), found
        print("PASS lane claims transitive: helper and importer rejected; Export and Shared exempt")

        root = temp / "test-tactic-leaf"
        setup(root)
        module(root, X + ".Tests.Control", "Mathlib.Tactic")
        module(root, X + ".Tests.Consumer", X + ".Tests.Control")
        run(root, 1, {("B6-TACTIC", X + ".Tests.Control", "Mathlib.Tactic"),
                      ("TEST-USE", X + ".Tests.Consumer", X + ".Tests.Control")})
        print("PASS test tactic must be a leaf: exit 1")

        # srcDir, root facades, explicit roots, glob-only files, scripts and
        # undeclared .lean files must all have the intended scan scope.
        root = temp / "discovery"
        setup(root)
        path = root / "lakefile.toml"
        path.write_text(path.read_text() + '\n[[lean_lib]]\nname = "Custom"\n'
                        'srcDir = "src"\nroots = ["CustomRoot"]\n'
                        'globs = ["Custom.*"]\n')
        module(root, "CustomRoot", "Mathlib", src="src")
        module(root, "Custom.Hidden", "Mathlib", src="src")
        module(root, "CustomRoot.Pending.Hidden", "Mathlib", src="src")
        module(root, "AvailableChainCheckSupport.Helper", "Lean", src="scripts")
        module(root, "Helper", "AvailableChainCheckSupport.Helper", src="scripts")
        module(root, "Unlisted", "AvailableChainCheckSupport.Helper")
        module(root, "Ignored", "Mathlib", src=".lake/packages/example")
        expected = {("B6-MATHLIB", name, "Mathlib") for name in
                    ("CustomRoot", "Custom.Hidden", "CustomRoot.Pending.Hidden")}
        expected.add(("CHECK-SUPPORT", "Unlisted", "AvailableChainCheckSupport.Helper"))
        run(root, 1, expected)
        print("PASS discovery: roots/srcDir/globs/facades/support/unlisted files -> exit 1")

        # Five-folder twin: every owner and overlapping Tests target uses Lake's mapping.
        root = temp / "five-srcdirs"
        setup(root)
        module(root, F + ".Model.Control", F + ".Proofs.Helper")
        module(root, "Unlisted", "AvailableChainCheckSupport.Helper", src="engine")
        current = tomllib.loads((repo / "lakefile.toml").read_text())
        sources = {lib["name"]: lib.get("srcDir", ".") for lib in current["lean_lib"]}
        cfg = root / "lakefile.toml"
        text = cfg.read_text()
        for name in lib_names:
            if sources[name] == "scripts":
                continue
            anchor = 'name = ' + json.dumps(name) + '\n'
            assert text.count(anchor) == 1
            text = text.replace(anchor, anchor + 'srcDir = ' + json.dumps(sources[name]) + '\n')
        cfg.write_text(text)
        files = list(root.glob("AvailableChain*.lean")) + list(root.glob("AvailableChain*/*.lean"))
        for file in files:
            name = file.relative_to(root).parts[0].removesuffix(".lean")
            target = root / sources[name] / file.relative_to(root)
            target.parent.mkdir(parents=True, exist_ok=True)
            file.rename(target)
        # The control above has a deeper source path; move any remaining descendants.
        for directory in list(root.glob("AvailableChain*")):
            if directory.is_dir():
                for file in list(directory.rglob("*.lean")):
                    target = root / sources[directory.name] / file.relative_to(root)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    file.rename(target)
        run(root, 1, {("B4", F + ".Model.Control", F + ".Proofs.Helper"),
                      ("CHECK-SUPPORT", "engine.Unlisted", "AvailableChainCheckSupport.Helper")})
        print("PASS five srcDirs: stable module names, Tests overlap, unlisted support guard")

        # An exact baseline accepts a legacy edge, still prints it, rejects
        # a new edge, and shrinks when --write-baseline runs after removal.
        root = temp / "baseline"
        setup(root)
        module(root, X + ".Control", "Mathlib")
        first = {("B6-MATHLIB", X + ".Control", "Mathlib")}
        run(root, 1, first)
        run(root, 0, first, extra=("--write-baseline",))
        baseline = root / "scripts/baselines/check-layers.txt"
        content = baseline.read_bytes()
        run(root, 0, first)
        run(root, 0, first, extra=("--write-baseline",))
        assert baseline.read_bytes() == content
        module(root, X + ".New", "Mathlib")
        run(root, 1, first | {("B6-MATHLIB", X + ".New", "Mathlib")})
        module(root, X + ".Control")
        module(root, X + ".New")
        run(root, 0, set(), extra=("--write-baseline",))
        assert all(line.startswith("#") for line in baseline.read_text().splitlines())
        print("PASS baseline: new=1, write=0, legacy=0, added=1, shrink=0; deterministic")

        baseline.write_text("UNKNOWN Importer Target\n")
        run(root, 2)
        print("PASS invalid baseline: exit 2")

assert snapshot() == before, "self-test changed the worktree"
print(f"PASS self-test: {len(selected) if selected else len(controls)} rule controls; worktree unchanged")
PY
