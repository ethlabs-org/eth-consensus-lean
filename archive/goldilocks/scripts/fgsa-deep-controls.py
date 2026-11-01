#!/usr/bin/env python3
"""Compiled, isolated controls for current deep snapshots and root attribution."""
from copy import deepcopy
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

spec = importlib.util.spec_from_file_location('fgsa_deep', 'scripts/fgsa-deep.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def require_failure(label, action, reason):
    try:
        result = action()
    except (ValueError, OSError) as exc:
        result = [str(exc)]
    assert result and any(reason in msg for msg in result), (label, result, reason)
    print(f'CONTROL {label}: PASS ({reason})')


PROBE = r'''
def main (args : List String) : IO UInt32 := do
  let [dir] := args | return 2
  initSearchPath (← findSysroot)
  searchPathRef.modify fun paths => System.FilePath.mk dir :: paths
  let env ← importModules #[{ module := `DeepStatements }] {}
  let root := `AvailableChain.FGSA.DeepControl.claim
  unless !(← runCore env (generated `AvailableChain.FGSA.DeepControl.reader)) do
    throw (IO.userError "control reader must be public")
  let shallow ← runCore env (entryHex .fgsa root)
  let some (.thmInfo claim) := env.find? root | return 2
  IO.FS.writeFile (System.FilePath.mk dir / "proof-value") (deepExpr claim.value)
  let snapshot ← deepSnapshot env #[root]
  IO.FS.writeFile (System.FilePath.mk dir / "snapshot.json") snapshot.compress
  IO.FS.writeFile (System.FilePath.mk dir / "shallow") shallow
  return 0
'''


def check_wiring(root=Path('.'), shell=None):
    # Both required positive commands must run before the NEG exit.
    if shell is None:
        shell = (root / 'scripts/check-fgsa-manifest.sh').read_text()
    shell = shell.replace('\\\n', '')
    boundary = shell.index('if [ "${NEG:-1}"')
    assert shell.index('--scope fgsa --check') < boundary
    assert shell.index('--scope fgsa --deep --check') < boundary
    assert shell.index('--scope legacy --check') < boundary
    for scope, label in [('v2', 'v2-deep'), ('gen', 'gen-deep'),
                         ('compose', 'compose-api'), ('fgsa-claims', 'claims-api')]:
        call = 'manifest_run ' + label + ' python3 -B scripts/api-snapshot.py'
        start = shell.index(call)
        assert start < boundary
        command = shell[start:shell.index('\n', start)]
        if scope in ('v2', 'gen'):
            assert '--output docs/internal/api/' + label + '.json --check' in command
        assert '--scope ' + scope in command and '--check' in command
    gate = (root / 'scripts/gate.sh').read_text()
    assert 'fgsa-manifest) step "$1" gate_measure_command bash scripts/check-fgsa-manifest.sh ;;' in gate
    group = ('run_group fgsa-claims check-fg-compose fgsa-manifest check-fgsa-run check-fgsa '
             '\\\n  check-build\n')
    assert group in gate
    assert gate.index(group) > gate.index('fi\n# Start the measured long tail earlier;')
    print('CONTROL merge/full mandatory current shallow and deep wiring: PASS')


def omitted_products():
    shell = Path('scripts/check-fgsa-manifest.sh').read_text()
    for label in ('v2-deep', 'gen-deep', 'compose-api', 'claims-api'):
        bad = shell.replace('manifest_run ' + label + ' ', 'manifest_run omitted ')
        try:
            check_wiring(shell=bad)
        except ValueError:
            print('CONTROL omitted gate product ' + label + ': PASS')
        else:
            raise AssertionError('accepted omitted product ' + label)


def main():
    with tempfile.TemporaryDirectory(prefix='fgsa-deep-controls-') as scratch:
        tmp = Path(scratch)
        # Reuse the exact production extraction/digest functions. This is the same
        # isolated probe pattern; never edit repo sources.
        helper = Path('scripts/V2Manifest.lean').read_text().split(
            'def main (args : List String)')[0]
        probe = tmp / 'DeepProbe.lean'
        probe.write_text(helper + PROBE)
        snapshots, shallow = {}, {}
        for variant in ('base', 'body', 'proof', 'private', 'constructor'):
            target = tmp / variant
            target.mkdir()
            model = ('namespace AvailableChain.FGSA.DeepControl\n'
                     f'private def hidden : Nat := {2 if variant == "private" else 1}\n'
                     f'def reader : Nat := hidden{" + 1" if variant == "body" else ""}\n'
                     'structure Carrier where\n  value : ' +
                     ('Bool' if variant == 'constructor' else 'Nat') + '\n'
                     'end AvailableChain.FGSA.DeepControl\n')
            (target / 'DeepModel.lean').write_text(model)
            proof = 'Eq.refl reader' if variant != 'proof' else 'Eq.symm (Eq.refl reader)'
            (target / 'DeepStatements.lean').write_text('import DeepModel\n'
                'namespace AvailableChain.FGSA.DeepControl\n'
                f'theorem claim (_x : Carrier) : reader = reader := {proof}\n'
                'end AvailableChain.FGSA.DeepControl\n')
            for module in ('DeepModel', 'DeepStatements'):
                # Lake env supplies the repository and toolchain imports; add only
                # the isolated fixture directory to the inherited search path.
                env = dict(os.environ)
                env['LEAN_PATH'] = str(target) + os.pathsep + env.get('LEAN_PATH', '')
                command = ['lake', 'env', 'lean', f'--root={target}', '-o',
                           str(target / (module + '.olean')), str(target / (module + '.lean'))]
                result = subprocess.run(command, env=env, capture_output=True, text=True)
                assert result.returncode == 0, (command, result.stdout, result.stderr)
            result = subprocess.run(['lake', 'env', 'lean', '--run', str(probe), str(target)],
                                    capture_output=True, text=True)
            assert result.returncode == 0, (result.stdout, result.stderr)
            snapshots[variant] = check.strict_json(target / 'snapshot.json')
            shallow[variant] = (target / 'shallow').read_text()
        base, body, proof, private = (snapshots[v] for v in ('base', 'body', 'proof', 'private'))
        name = next(iter(base['entries']))
        assert shallow['base'] == shallow['body'] == shallow['proof'] == shallow['private']
        assert not check.check_deep(base, base)
        print('CONTROL deep unchanged positive: PASS')
        for label in ('body', 'private', 'constructor'):
            require_failure(label, lambda: check.check_deep(base, snapshots[label]), 'DEEP CHANGED')
        assert not check.check_deep(base, proof)
        assert base == proof
        assert (tmp / 'base/proof-value').read_text() != (tmp / 'proof/proof-value').read_text()
        print('CONTROL theorem proof only: PASS (identical complete snapshot)')
        reader = 'AvailableChain.FGSA.DeepControl.reader'
        report = check.diff_report(base, body, [dict(name=reader)])
        assert report['entries'][0]['attribution'][0]['relation'] == 'through-root'
        assert report['groups'][reader] == [name]
        print('CONTROL all changed nodes, groups and through-root paths: PASS')
        for field, value in [('kind', 'def'), ('module', 'MovedControl')]:
            bad = deepcopy(base)
            bad['entries'][name][field] = value
            bad['nodes'][name][field] = value
            require_failure('root ' + field, lambda: check.check_deep(base, bad), 'DEEP CHANGED')
        bad = deepcopy(base)
        bad['nodes']['Unreachable.Control'] = deepcopy(bad['nodes'][name])
        bad['node_order'].append('Unreachable.Control')
        require_failure('extra unattached node', lambda: check.validate_graph(bad), 'UNREACHABLE')
        bad = deepcopy(base)
        bad['node_order'].append(bad['node_order'][0])
        require_failure('duplicate node order', lambda: check.validate_graph(bad), 'NODE ORDER')
        bad = deepcopy(base)
        bad['nodes'][name]['dependencies'].pop()
        require_failure('incomplete closure', lambda: check.validate_graph(bad), 'INCOMPLETE ROOT')
        bad = deepcopy(base)
        bad['nodes'][reader]['dependencies'].append('Missing.Control')
        require_failure('missing dependency', lambda: check.validate_graph(bad), 'MISSING DEEP')
        # A foreign kernel dependency is checked without a library filter.
        foreign = next(n for n in base['nodes'] if not n.startswith('AvailableChain'))
        bad = deepcopy(base)
        bad['nodes'][foreign]['digest'] = '0' * 64
        for n in bad['entries']:
            bad['entries'][n]['digest'] = check.root_digest(bad, n)
        require_failure('foreign node drift', lambda: check.check_deep(base, bad), 'DEEP CHANGED')
        report = check.diff_report(base, bad, [dict(name=reader)])
        assert any(r['relation'] == 'shared-dependency'
                   for e in report['entries'] for r in e['attribution']) is False
        # Give another root a shared dependency but no entry-to-root path.
        shared = deepcopy(base)
        shared['entries'][reader] = dict(digest=check.root_digest(shared, reader),
            kind=shared['nodes'][reader]['kind'], module=shared['nodes'][reader]['module'])
        shared_bad = deepcopy(shared)
        shared_bad['nodes'][reader]['digest'] = '3' * 64
        for n in shared_bad['entries']:
            shared_bad['entries'][n]['digest'] = check.root_digest(shared_bad, n)
        report = check.diff_report(shared, shared_bad, [dict(name=name)])
        assert any(r['relation'] == 'shared-dependency'
                   for e in report['entries'] for r in e['attribution'])
        removed = deepcopy(shared)
        del removed['entries'][name]
        reachable = set().union(*(check.closure(removed['nodes'], n)
                                  for n in removed['entries']))
        removed['nodes'] = {n: r for n, r in removed['nodes'].items() if n in reachable}
        removed['node_order'] = [n for n in removed['node_order'] if n in reachable]
        report = check.diff_report(shared, removed, [dict(name=name)])
        assert any(e['name'] == name and e['membership'] == 'removed' for e in report['entries'])
        assert any(p['side'] == 'base' for e in report['entries']
                   for n in e['changed_nodes'] for p in n['paths'])
        require_failure('deleted root', lambda: check.check_deep(shared, removed), 'DEEP CHANGED')
        require_failure('added root', lambda: check.check_deep(removed, shared), 'DEEP CHANGED')
        report = check.diff_report(base, body, [dict(name='Planned.Absent', status='planned')])
        assert report['unresolved'][0]['name'] == 'Planned.Absent'
        print('CONTROL shared dependencies, removal union, addition, absent roots: PASS')
        path = tmp / 'duplicate.json'
        path.write_text('{"entries":{},"entries":{}}')
        require_failure('duplicate JSON', lambda: check.strict_json(path), 'DUPLICATE JSON KEY')
        fixture_manifest = tmp / 'fixture.md'
        fixture_manifest.write_text('### `DeepStatements`\n\n```text\n' +
            f'theorem {name} {shallow["base"]}\n```\n')
        baseline = tmp / 'current.json'
        snapshot = tmp / 'snapshot.json'
        snapshot.write_text(json.dumps(base))
        command = ['python3', '-B', 'scripts/fgsa-deep.py', '--snapshot', str(snapshot),
                   '--manifest', str(fixture_manifest), '--baseline', str(baseline)]
        for mode in ('--write', '--check'):
            result = subprocess.run(command + [mode], capture_output=True, text=True)
            assert result.returncode == 0, result
        snapshot.write_text(json.dumps(body))
        result = subprocess.run(command + ['--check'], capture_output=True, text=True)
        assert result.returncode == 1 and 'DEEP CHANGED' in result.stderr, result
        snapshot.write_text(json.dumps(base))
        data = check.strict_json(baseline)
        data['pins']['toolchain'] = 'wrong'
        baseline.write_text(json.dumps(data))
        result = subprocess.run(command + ['--check'], capture_output=True, text=True)
        assert result.returncode == 1 and 'SNAPSHOT PIN MISMATCH' in result.stderr, result
        baseline.unlink()
        result = subprocess.run(command + ['--check'], capture_output=True, text=True)
        assert result.returncode == 1, result
        current = check.manifest(fixture_manifest)
        current['Not.Compiled'] = dict(kind='def', module='Wrong', digest='0' * 16)
        require_failure('manifest addition',
                        lambda: check.bind_manifest(base, current), 'ROOTS DIFFER')
        require_failure('manifest deletion', lambda: check.bind_manifest(base, {}), 'ROOTS DIFFER')
        roots = tmp / 'roots.txt'
        roots.write_text(reader + '\n' + reader + '\n')
        require_failure('duplicate roots', lambda: check.root_list(roots), 'INVALID ROOT LIST')
        result = subprocess.run(command + ['--write', '--roots', str(roots)],
                                capture_output=True, text=True)
        assert result.returncode == 2, result
        print('CONTROL CLI stale/missing snapshots, pins, roots, write rejection: PASS')
    check_wiring()
    omitted_products()
    subprocess.run(['python3', '-B', 'scripts/root-report-controls.py'], check=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--source-only', action='store_true')
    if ap.parse_args().source_only:
        check_wiring()
        omitted_products()
        subprocess.run(['python3', '-B', 'scripts/root-report-controls.py'], check=True)
    else:
        main()
