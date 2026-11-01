#!/usr/bin/env python3
"""Negative controls for DCK scopes, strict audits and scoped proof coverage."""
import importlib.util
from pathlib import Path
import subprocess
import shutil
import tempfile
from unittest.mock import patch

import check_common as C
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


D = load('dev', 'scripts/dev-check.py')
S = load('scopes', 'scripts/check-sleep-scopes.py')
P = load('coverage', 'scripts/check-proof-coverage.py')
B = load('blueprint', 'scripts/check-fgsa-blueprint.py')
H = load('shake', 'scripts/shake_scope.py')
ROOT = Path(__file__).resolve().parents[1]


def rejected(label, diagnostic, action):
    try:
        action()
    except ValueError as error:
        if diagnostic not in str(error):
            raise AssertionError(f'{label}: wrong failure: {error}') from error
        print(f'CONTROL {label}: PASS ({error})', flush=True)
    else:
        raise AssertionError(label + ': accepted invalid fixture')


def section_bytes(text):
    lines = text.splitlines(keepends=True)
    return {key: ''.join(lines[start:end]) for key, (start, end) in P.sections(text).items()}


def package_fixture(required):
    return '[TARGETS]\n[GREEN]\n' + '\n'.join(sorted(required)) + '\n[EXPECTED-FAIL]\n'


def scoped_write_control(tmp, src="."):
    # An isolated library supplies the real compiled generator. No project audit
    # olean is loaded, including audits a package can mark EXPECTED-FAIL.
    root = tmp / ('coverage-build-' + src.replace('.', 'flat'))
    scripts = root / 'scripts'
    scripts.mkdir(parents=True)
    for name in ('check-proof-coverage.py', 'CheckProofEqns.lean', 'source_layout.py'):
        shutil.copyfile(ROOT / 'scripts' / name, scripts / name)
    support = scripts / 'AvailableChainCheckSupport'
    support.mkdir()
    shutil.copyfile(ROOT / 'scripts/AvailableChainCheckSupport/GeneratedOwner.lean',
                    support / 'GeneratedOwner.lean')
    (scripts / 'baselines').mkdir()
    for name in ('kitfg-def-modules.txt', 'check-proof-eqns.txt'):
        shutil.copyfile(ROOT / 'scripts/baselines' / name, scripts / 'baselines' / name)
    (root / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
    (root / 'lakefile.toml').write_text(
        'name = "dev-coverage"\nversion = "0.1.0"\n'
        '[[lean_lib]]\nname = "AvailableChainGeneric"\n'
        'srcDir = "' + src + '"\n'
        'roots = ["AvailableChainGeneric.Tests.Axioms"]\n'
        '[[lean_lib]]\nname = "AvailableChainCheckSupport"\nsrcDir = "scripts"\n'
        'roots = ["AvailableChainCheckSupport.GeneratedOwner"]\n')
    key = 'AvailableChainGeneric.Tests.Axioms'
    audit = root / src / (key.replace('.', '/') + '.lean')
    audit.parent.mkdir(parents=True)
    audit.write_text('module\npublic section\n'
                     'theorem devCoverage_premises_sat : True := True.intro\n'
                     'theorem devCoverage : True := devCoverage_premises_sat\n'
                     '#print axioms devCoverage\n')
    subprocess.run(['lake', 'build', '--wfail', key, 'AvailableChainCheckSupport'],
                   cwd=root, check=True)
    inventory = scripts / 'proof-audit-coverage.txt'
    original = (ROOT / 'scripts/proof-audit-coverage.txt').read_text()
    before = section_bytes(original)
    inventory.write_text(P.replace_sections(original, {
        key: P.section_text(key, [(key, 'devStaleName', key)])}))
    command = ['python3', '-B', 'scripts/check-proof-coverage.py', '--audits', key]
    subprocess.run([*command, '--write'], cwd=root, check=True)
    after = section_bytes(inventory.read_text())
    assert set(before) == set(after) == set(P.AUDITS)
    assert all(before[k] == after[k] for k in before if k != key)
    assert after[key] == P.section_text(key, [(key, 'devCoverage', key)])
    subprocess.run(command, cwd=root, check=True)
    inventory.write_text(P.replace_sections(inventory.read_text(), {
        key: P.section_text(key, [(key, 'devStaleName', key)])}))
    result = subprocess.run(command, cwd=root, text=True, capture_output=True)
    assert result.returncode == 1 and 'AUDIT DECLARATION MISSING' in result.stdout, result.stdout
    print('CONTROL isolated scoped write / stale compiled row: PASS '
          '(other sections unchanged; real checker rc 1)', flush=True)


def main():
    result = subprocess.run(['python3', '-B', 'scripts/check-fg-finality-coverage.py'],
                            cwd=ROOT, text=True, capture_output=True)
    assert result.returncode == 0, result.stdout + result.stderr
    print('CONTROL real finality source inventories: PASS (221 declarations)', flush=True)
    data = B.fixture_map()
    assert all(not where.startswith('safety PC-SA ') for where, _ in B.compiled_clauses(data))
    with patch.object(B.subprocess, 'run', side_effect=AssertionError('PC-SA Lean import')):
        assert B.run_oracle(B.REPO, []) == {}
    print('CONTROL blueprint defers PC-SA safety section: PASS', flush=True)
    with tempfile.TemporaryDirectory(prefix='blueprint-control-') as tmp:
        root = Path(tmp)
        B.make_fixture(root)
        import contextlib
        import io
        import json
        data = json.loads((root / B.MAP).read_text())
        row = data['safety_package']['FG-SA'][0]
        row.update(module='AvailableChainPCSAProofs.Proofs.ReviewStub',
                   theorem='Fix.DoesNotExist')
        with (root / 'lakefile.toml').open('a') as config:
            config.write('[[lean_lib]]\nname="AvailableChainPCSAProofs"\n')
        stub = B.module_source(root, row['module'])
        stub.parent.mkdir(parents=True)
        stub.write_text('-- source exists; theorem does not\n')
        (root / B.MAP).write_text(json.dumps(data))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            rc = B.run(root, oracle=B.fixture_oracle(B.GOOD), oleans=False)
        reason = 'MISSING CONSTANT: Fix.DoesNotExist (safety FG-SA accountable)'
        assert rc == 1 and reason in output.getvalue(), output.getvalue()
        print(f'CONTROL blueprint cross-section module: PASS (rc {rc}; {reason})', flush=True)
    graph = C.import_graph()
    scope = ROOT / 'scripts/dev-scope-s1.txt'
    original = scope.read_text()
    required = D.validate_scope(scope, graph)
    with tempfile.TemporaryDirectory(prefix='dev-controls-', dir=ROOT / '.lake') as tmp:
        tmp = Path(tmp)
        files = [f for f in C.library_files() if f.module.startswith('AvailableChainFG')
                 or S.deferred(f.module)]
        build = tmp / 'shake-oleans'
        for file in files:
            olean = build / (file.module.replace('.', '/') + '.olean')
            olean.parent.mkdir(parents=True, exist_ok=True)
            olean.touch()
        selected = set(H.selection(files, build))
        assert selected == {f.module for f in files if not S.deferred(f.module)}
        assert not any(S.deferred(m) for m in selected)
        print('CONTROL shake PC-SA oleans present / all FG-SA retained: PASS '
              f'({len(selected)} active modules)', flush=True)
        fixture = tmp / 'scope.txt'
        for option, name in (('--inventory', 'proof-audit-coverage.txt'),
                             ('--source-inventory', 'pcsa-source-audit-coverage.txt')):
            inventory = tmp / name
            inventory.write_text('{}\n')
            result = subprocess.run(['python3', '-B', 'scripts/check-fg-finality-coverage.py',
                                     option, str(inventory)], cwd=ROOT,
                                    text=True, capture_output=True)
            assert result.returncode == 1 and 'NOT IN COVERAGE:' in result.stdout, result.stdout
            print(f'CONTROL missing {name}: PASS (real checker rejected rows)', flush=True)
        omitted = sorted(required)[0]
        fixture.write_text(original.replace(omitted + '\n', '', 1))
        rejected('omitted REQUIRED', 'OMITTED S1 MODULE',
                 lambda: D.validate_scope(fixture, graph))
        fixture.write_text(original + '\n[EXPECTED-FAIL]\n' + omitted + ' W3\n')
        rejected('EXPECTED-FAIL at s1', 'UNKNOWN SECTION',
                 lambda: D.validate_scope(fixture, graph))
        fixture.write_text(original)
        changed = {**graph, omitted: [*graph[omitted], D.SHARED + '.Claims'],
                   D.SHARED + '.Claims': []}
        rejected('REQUIRED imports DEFERRED', 'REQUIRED IMPORTS DEFERRED',
                 lambda: D.validate_scope(fixture, changed))
        package = package_fixture(required)
        fixture.write_text(package.replace(omitted + '\n', '', 1))
        rejected('omitted package module', 'OMITTED PACKAGE MODULE',
                 lambda: D.validate_package(fixture, required, graph))
        fixture.write_text(package.replace(
            '[GREEN]', '[GREEN]\nAvailableChainMissing.NoSuchModule'))
        rejected('unknown package target', 'UNKNOWN PACKAGE TARGET',
                 lambda: D.validate_package(fixture, required, graph))
        # A package target outside S1 is allowed, and a REQUIRED target may be
        # EXPECTED-FAIL in this level only. This guards the r8 domain rule.
        fixture.write_text(package.replace(omitted + '\n', '', 1).replace(
            '[EXPECTED-FAIL]', '[EXPECTED-FAIL]\n' + omitted + ' W3').replace(
            '[TARGETS]', '[TARGETS]\nAvailableChainModel.Generic.Env'))
        fixture.write_text(fixture.read_text().replace(
            '[GREEN]', '[GREEN]\nAvailableChainModel.Generic.Env'))
        green = D.validate_package(fixture, required, graph)
        assert 'AvailableChainModel.Generic.Env' in green and omitted not in green
        print('CONTROL package target outside S1 / owned EXPECTED-FAIL: PASS', flush=True)
        fixture.write_text(fixture.read_text().replace(
            '[GREEN]\nAvailableChainModel.Generic.Env', '[GREEN]'))
        rejected('omitted outside-S1 package target', 'OMITTED PACKAGE MODULE',
                 lambda: D.validate_package(fixture, required, graph))
        new = 'AvailableChainEngineV2.Tests.ReviewNewSleep'
        grown_graph = {**graph, new: []}
        fixture.write_text(original.replace('[REQUIRED]', '[REQUIRED]\n' + new))
        grown_required = D.validate_scope(fixture, grown_graph)
        fixture.write_text(package_fixture(grown_required))
        assert D.validate_package(fixture, grown_required, grown_graph) == grown_required
        print('CONTROL valid S1 growth: PASS (current REQUIRED fixture)', flush=True)
        fixture.write_text(package.replace(D.SHARED_AUDIT + '\n', '', 1).replace(
            '[EXPECTED-FAIL]', '[EXPECTED-FAIL]\n' + D.SHARED_AUDIT + ' P-ShA'))
        green = D.validate_package(fixture, required, graph)
        assert D.SHARED_AUDIT not in green
        assert set(D.AUDITS) & green == set(D.AUDITS) - {D.SHARED_AUDIT}
        print('CONTROL package Shared audit EXPECTED-FAIL: PASS (not selected)', flush=True)
        rejected('active imports PC-SA', 'ACTIVE IMPORTS PC-SA', lambda: S.check_active(
            {'AvailableChainFGSA': ['AvailableChainPCSA']}, ['AvailableChainFGSA']))
        rejected('deferred source proof', 'DEFERRED FORBIDDEN PROOF', lambda:
                 S.check_deferred('AvailableChainPCSA.Proofs.Control',
                                  'theorem bad : True := sorry'))
        rejected('deferred adapter extension', 'DEFERRED GLOBAL EXTENSION', lambda:
                 S.check_deferred('AvailableChainPCSAProofs.Proofs.Shared.FGCompose',
                                  'infix:50 \"bad\" => Nat.add'))
        orphan = 'AvailableChainPCSAProofs.Proofs.Foundations.ReviewOrphan'
        S.check_deferred_facades({'AvailableChainPCSAProofs': [orphan], orphan: []})
        rejected('PC-SA facade orphan', 'NOT IMPORTED BY ROOT: ' + orphan,
                 lambda: S.check_deferred_facades(
                     {'AvailableChainPCSAProofs': [], orphan: []}))
        sorry_dir = tmp / 'sorry-build'
        sorry_dir.mkdir()
        (sorry_dir / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
        (sorry_dir / 'lakefile.toml').write_text(
            'name = "dev-negative"\nversion = "0.1.0"\n'
            'defaultTargets = ["DevSorry"]\n[[lean_lib]]\nname = "DevSorry"\n'
            '[[lean_lib]]\nname = "DevClean"\n')
        (sorry_dir / 'DevSorry.lean').write_text('theorem devSorry : True := by sorry\n')
        (sorry_dir / 'DevClean.lean').write_text('theorem devClean : True := True.intro\n')
        clean = subprocess.run(['lake', 'build', '--wfail', 'DevClean'], cwd=sorry_dir,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert clean.returncode == 0, clean.stdout
        result = subprocess.run(['lake', 'build', '--wfail', 'DevSorry'], cwd=sorry_dir,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode and "declaration uses `sorry`" in result.stdout, result.stdout
        print('CONTROL sorry module: PASS (placeholder diagnostic; clean companion rc 0)',
              flush=True)
        axiom = tmp / 'Axiom.lean'
        axiom.write_text('axiom devUnexpected : True\n#print axioms devUnexpected\n')
        result = subprocess.run(['lake', 'env', 'lean', str(axiom)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode == 0, result.stdout
        rejected('non-standard axiom', 'BAD AXIOMS: devUnexpected',
                 lambda: D.strict_results(axiom.read_text(), result.stdout))
        rejected('missing axiom result', 'AXIOM RESULTS',
                 lambda: D.strict_results('#print axioms missing\n', ''))
        scoped_write_control(tmp)
        scoped_write_control(tmp, "generic")
        result = subprocess.run(['python3', '-B', 'scripts/check-proof-coverage.py',
                                 '--audits', 'AvailableChainUnknown.Tests.Axioms'], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode and 'unknown coverage key' in result.stdout, result.stdout
        print('CONTROL unknown coverage key: PASS (rejected before Lean import)', flush=True)
    print('DCK controls: PASS', flush=True)


if __name__ == '__main__':
    main()
