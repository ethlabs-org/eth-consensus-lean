#!/usr/bin/env python3
"""Run the production gate graph with stub checks. No Lean, build, or FULL gate."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / 'scripts'))
from audit_pool import AuditPool

HEAVY = ('fgsa-claims', 'check-fg-compose', 'fgsa-manifest', 'check-fgsa-run',
         'check-fgsa', 'check-build')
CHEAP = ('build', 'fg-finality-coverage', 'catalog-lock',
         'v2-manifest', 'gen-manifest', 'fgsa-old-reads', 'proof-audit-coverage',
         'Generic-axioms', 'FGSA-axioms', 'FGSARun-axioms', 'FGCompose-axioms',
         'FGSACompose-axioms', 'FGSafety-axioms',
         'FGSASafety-axioms', 'FGSAGrowth-axioms', 'fgsa-blueprint')
AXIOMS = {
    'Generic': 'AvailableChainGeneric/Tests/Axioms.lean',
    'FGSA': 'AvailableChainFGSA/Tests/Axioms.lean',
    'FGSARun': 'AvailableChainFGSARun/Tests/Axioms.lean',
    'FGCompose': 'AvailableChainFGCompose/Tests/Axioms.lean',
    'FGSACompose': 'AvailableChainFGSAProofs/Tests/FGCompose.lean',
    'FGSafety': 'AvailableChainFGCompose/Tests/SafetyAxioms.lean',
    'FGSASafety': 'AvailableChainFGSAProofs/Tests/FGSafety.lean',
    'FGSAGrowth': 'AvailableChainFGSAProofs/Tests/WeakContinuationGrowthAssemblyAxioms.lean',
}
STUB = r'''
import fcntl, json, os, sys, time
from pathlib import Path
name = sys.argv[1]
heavy = name in json.loads(os.environ['STUB_HEAVY'])
def event(kind):
    with Path(os.environ['STUB_EVENTS']).open('a') as out:
        fcntl.flock(out, fcntl.LOCK_EX)
        out.write(json.dumps(dict(name=name, kind=kind, time=time.monotonic(),
                                 neg=os.environ.get('NEG'))) + '\n')
event('start')
delay = 8 if heavy and os.environ.get('STUB_FAIL') and name != os.environ['STUB_FAIL'] else 0.8
time.sleep(delay if heavy else 0.01)
event('end')
if name.endswith('-axioms'):
    print('Stub does not depend on any axioms')
sys.exit(9 if name == os.environ.get('STUB_FAIL') else 0)
'''


REAL_RUN = subprocess.run


def signing_stub(args, **kwargs):
    if args[0] == 'ssh-keygen':
        return subprocess.CompletedProcess(args, 0)
    return REAL_RUN(args, **kwargs)


def write(path, text, executable=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    if executable:
        path.chmod(0o755)


def records(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def peak(events, names):
    active = maximum = 0
    for event in events:
        if event['name'] not in names:
            continue
        active += 1 if event['kind'] == 'start' else -1
        maximum = max(maximum, active)
    return maximum


def graph(root, tier, slots, fail='', change='', force=False, env_neg='0', integration=False,
          reviewed=(), old_stamp=False):
    scripts = root / 'scripts'
    scripts.mkdir(parents=True)
    (root / '.lake').mkdir()
    for name in ('gate.sh', 'gate-common.sh', 'checker_scope.py', 'checker-paths.txt',
                 'unported.py', 'unported-libraries.txt', 'gate_timing.py',
                 'integration_scope.py', 'full-pass.py', 'check_inventory.py', 'source_layout.py'):
        shutil.copy2(REPO / 'scripts' / name, scripts / name)
    write(root / 'lakefile.toml', ''.join(
        '[[lean_lib]]\nname="' + lib + '"\n' for lib in
        ('AvailableChainGeneric', 'AvailableChainFGSA', 'AvailableChainFGSARun',
         'AvailableChainFGSAClaims', 'AvailableChainFGSAProofs', 'AvailableChainFGCompose')))
    # Test the driver after precheck. Real source prechecks run separately.
    with (scripts / 'gate-common.sh').open('a') as out:
        out.write('\ngate_precheck() { echo "STUB PRECHECK PASS"; }\n')
    write(scripts / 'stub.py', STUB)
    for name in HEAVY:
        script = name if name.startswith('check-') else 'check-' + name
        write(scripts / (script + '.sh'),
              '#!/usr/bin/env bash\nset -euo pipefail\nsource scripts/gate-common.sh\n' +
              ('if [ "${1:-}" = --selftests-only ]; then\n'
               '  gate_with_slot python3 scripts/stub.py checker-self-tests\n'
               'else\n'
               f'  gate_with_slot python3 scripts/stub.py {name}\nfi\n'))
    for script, name in (('check-fg-finality-coverage.py', 'fg-finality-coverage'),
                         ('check-proof-coverage.py', 'proof-audit-coverage'),
                         ('check-fgsa-blueprint.py', 'fgsa-blueprint')):
        write(scripts / script, f'import runpy,sys\nsys.argv = ["stub", {name!r}]\n'
              'runpy.run_path("scripts/stub.py")\n')
    write(scripts / 'integration_g0.py',
          'import json,os,runpy,sys\nfrom pathlib import Path\n'
          'Path(os.environ["GATE_LOG_DIR"]).joinpath("package-g0.json").write_text('
          'json.dumps({"results": [{"module": "Stub.Tests.G0", "rc": 0}]}))\n'
          'sys.argv = ["stub", "package-g0"]\nrunpy.run_path("scripts/stub.py")\n')
    for path in AXIOMS.values():
        write(root / path, '#print axioms Stub\n')
    # Lake only selects stub checks. No toolchain is called.
    write(root / 'bin/lake', '#!/usr/bin/env python3\n'
          'import os,subprocess,sys\n'
          f'axioms = {AXIOMS!r}\n'
          'a = sys.argv[1:]\n'
          'if "--libraries" in a: print("Stub"); sys.exit(0)\n'
          'if a[0] == "build": name = "build"\n'
          'elif "scripts/CatalogLock.lean" in a: name = "catalog-lock"\n'
          'elif "scripts/CheckFGSAOldReads.lean" in a: name = "fgsa-old-reads"\n'
          'elif "scripts/V2Manifest.lean" in a:\n'
          '    name = "gen-manifest" if "gen" in a else "v2-manifest"\n'
          'else: name = next(k + "-axioms" for k,v in axioms.items() if v in a)\n'
          'sys.exit(subprocess.call([sys.executable,"scripts/stub.py",name]))\n', True)
    # Stub commands need no Linux scope; retain the real platform's time flags.
    platform = 'Darwin' if sys.platform == 'darwin' else 'Linux'
    write(root / 'bin/uname', f'#!/usr/bin/env bash\necho {platform}\n', True)
    write(root / '.gitignore', '.lake/\nevents\n')
    write(root / 'scripts/gly-f13-allow.txt', 'Old.allowed\n')
    write(root / 'scripts/fgsa-claims-expected.txt', "('Old.name',)\n")
    snapshot = {'entries': {'Old.name': {'digest': 'old'}}, 'nodes': {},
                'node_order': [], 'format_version': 1, 'pins': {}}
    write(root / 'docs/internal/api/gen-deep.json', json.dumps(snapshot))
    subprocess.run(['git', 'init', '-q', str(root)], check=True)
    subprocess.run(['git', 'symbolic-ref', 'HEAD', 'refs/heads/p0-control'], cwd=root, check=True)
    subprocess.run(['git', 'add', '.'], cwd=root, check=True)
    tree = subprocess.check_output(['git', 'write-tree'], cwd=root, text=True).strip()
    base = subprocess.check_output(['git', '-c', 'user.name=Control', '-c',
        'user.email=control@example.invalid', 'commit-tree', tree], cwd=root,
        input='graph base\n', text=True).strip()
    subprocess.run(['git', 'update-ref', 'HEAD', base], cwd=root, check=True)
    if change:
        changed_text = 'Old.allowed\nNew.allowed\n' if reviewed else 'changed\n'
        if integration and change == 'scripts/fgsa-claims-expected.txt':
            changed_text = "('Old.name', 'New.name')\n"
        if integration and change == 'docs/internal/api/gen-deep.json':
            snapshot['entries']['New.name'] = {'digest': 'new'}
            changed_text = json.dumps(snapshot)
        write(root / change, changed_text)
        subprocess.run(['git', 'add', '.'], cwd=root, check=True)
        tree = subprocess.check_output(['git', 'write-tree'], cwd=root, text=True).strip()
        head = subprocess.check_output(['git', '-c', 'user.name=Control', '-c',
            'user.email=control@example.invalid', 'commit-tree', tree, '-p', base], cwd=root,
            input='graph change\n', text=True).strip()
        subprocess.run(['git', 'update-ref', 'HEAD', head], cwd=root, check=True)
    else:
        head = base
    selected = bool(reviewed) if integration else (force or env_neg == '1' or not change or
                                                  change.startswith(('scripts/', 'docs/internal/')))
    stamp = root / '.lake/gate-last-full'
    if old_stamp:
        stamp.write_text('prior FULL evidence\n')
        stamp_before = stamp.stat().st_mtime_ns
    events = root / 'events'
    env = dict(os.environ, PATH=str(root / 'bin') + os.pathsep + os.environ['PATH'],
               GATE_SLOTS=str(slots), LEAN_SLOTS=str(slots), GATE_FF_GRACE='2',
               GATE_MEM_SCOPED='1',
               STUB_EVENTS=str(events), STUB_HEAVY=json.dumps(HEAVY), STUB_FAIL=fail,
               SOURCE_ONLY='0', NEG=env_neg, SKIP_CONE='1')
    for key in ('GATE_SLOT_DIR', 'GATE_SLOT_HELD', 'GATE_NO_BUILD'):
        env.pop(key, None)
    result = subprocess.run(['bash', 'scripts/gate.sh', '--tier', tier, '--base', base] +
                            (['--neg'] if force else []) + (['--integration'] if integration else []) +
                            [arg for path in reviewed for arg in ('--reviewed-allow', path)], cwd=root,
                            env=env, capture_output=True, text=True)
    assert events.exists(), result
    seen = records(events)
    starts = [e['name'] for e in seen if e['kind'] == 'start']
    expected = list(CHEAP if tier == 'full' else CHEAP[:-1])
    if integration:
        expected.insert(1, 'package-g0')
    if selected:
        expected.append('checker-self-tests')
    early = fail in expected
    assert starts[:len(expected)] == (expected[:expected.index(fail) + 1]
                                    if early else expected), (starts, result)
    maximum = peak(seen, HEAVY)
    assert maximum <= slots, (maximum, result)
    heavy_starts = starts[len(expected):] if not early else []
    if slots == 1 and not fail:
        assert heavy_starts == list(HEAVY), heavy_starts
    elif not early:
        assert set(heavy_starts[:slots]) == set(HEAVY[:slots]), heavy_starts
    logs = next((root / '.lake').glob('gate-logs.*'))
    assert not list((root / '.lake').glob('gate-slots.*/slot.*'))
    if not early:
        for name in HEAVY:
            record = json.loads((logs / f'timings/{name}/{name}.json').read_text())
            assert record['queued'] <= record['end'] and record['rc'] is not None, record
            if record['start'] is not None:
                assert record['queued'] <= record['start'] <= record['end'], record
            if not fail:
                assert record['slot_acquired'] is not None, record
                assert record['peak_rss_bytes'] is not None, record
    if fail:
        assert result.returncode == 1 and ('PROVISIONAL INTEGRATION FAIL' if integration else f'GATE FAIL tier={tier}') in result.stdout, result
        if fail != 'build':
            assert 'fail-fast:' in result.stdout, result
        assert not (root / '.lake/gate-last-full').exists()
        if early:
            assert not set(starts) & set(HEAVY), starts
        else:
            assert 'stopped:' in result.stdout, result
            assert not all((logs / (n + '.result')).exists() for n in HEAVY), result
            assert set(heavy_starts) == set(HEAVY[:slots]), heavy_starts
            assert not any(e['name'] == 'check-fg-compose' and e['kind'] == 'end'
                           for e in seen), seen
    else:
        assert result.returncode == 0 and ('PROVISIONAL INTEGRATION PASS' if integration else f'GATE PASS tier={tier}') in result.stdout, result
        assert set(starts[len(expected):]) == set(HEAVY), starts
        assert maximum == slots, (maximum, result)
        assert all(e['neg'] == ('1' if selected else '0')
                   for e in seen if e['name'] in HEAVY)
        if integration:
            if old_stamp:
                assert stamp.read_text() == 'prior FULL evidence\n' and stamp.stat().st_mtime_ns == stamp_before
            else:
                assert not stamp.exists()
            assert not (logs / 'full-pass.json').exists()
            completed = json.loads((logs / 'integration-result.json').read_text())
            assert completed['result'] == 'PROVISIONAL PASS'
            assert bool(completed['deferred_controls']) == (not reviewed)
            if change.startswith(('scripts/', 'docs/internal/api/')):
                assert completed['matched_checker_paths'] == [change]
            assert completed['package_g0']['results'][0]['rc'] == 0
            assert set(completed['positive_steps']) == (set(CHEAP) - {'fgsa-old-reads'} | set(HEAVY) |
                                                       {'package-g0'} | ({'checker-self-tests'} if selected else set()))
            assert 'GATE PASS tier=full' not in result.stdout
            for forbidden in (['--attest-key', 'key'], ['--neg'], ['--tier', 'merge'], ['--critical-path']):
                refusal = subprocess.run(['bash', 'scripts/gate.sh', '--integration', '--base', base, *forbidden],
                                         cwd=root, env=env, capture_output=True, text=True)
                assert refusal.returncode == 2 and 'INTEGRATION REFUSED' in refusal.stderr, refusal
            assert records(events) == seen
        elif tier == 'full':
            spec = importlib.util.spec_from_file_location('receipt', REPO / 'scripts/full-pass.py')
            receipt = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(receipt)
            scope = json.loads((logs / 'negative-controls.json').read_text())
            assert {p.stem for p in logs.glob('*.result')} == set(receipt.steps_for(scope))
            with patch.object(receipt, 'clean_head'), \
                    patch.object(receipt.subprocess, 'run', side_effect=signing_stub):
                receipt.sign(root, head, base, logs, root / 'key', logs / 'receipt.json')
                for bad in ('missing', 'extra'):
                    target = logs / ('build.result' if bad == 'missing' else 'extra.result')
                    if bad == 'missing':
                        saved = target.read_text()
                        target.unlink()
                    else:
                        target.write_text('0 0\n')
                    try:
                        receipt.sign(root, head, base, logs, root / 'key', logs / 'bad.json')
                    except ValueError as exc:
                        assert 'STEP SET' in str(exc), exc
                    else:
                        raise AssertionError('receipt accepted ' + bad)
                    if bad == 'missing':
                        target.write_text(saved)
                    else:
                        target.unlink()
            print('receipt exact step set and missing/extra rejection: PASS')
    print(f'graph {tier} slots={slots} {fail or "pass"}: peak={maximum} rc={result.returncode}')
    print('start order: ' + ' -> '.join(starts))
    if fail:
        print('\n'.join(line for line in result.stdout.splitlines()
                        if line.startswith(('fail-fast:', 'GATE '))))


def copy_control(root):
    source, target = root / 'source', root / 'private'
    for path in ('fgsa/AvailableChainFGSA/Tests/Keep.lean', '.lake/build/keep.olean',
                 '.lake/config/keep', '.lake/packages/dependency/keep'):
        write(source / path, 'unchanged\n')
    write(source / '.lake/gate-logs.live/log', 'excluded\n')
    write(source / '.git/config', 'excluded\n')
    subprocess.run(['bash', '-c', 'set -e; source "$1"; gate_copy_control_tree "$2" "$3"',
                    'copy-control', str(REPO / 'scripts/gate-common.sh'),
                    str(source), str(target)], check=True)
    assert not (target / '.git').exists()
    assert set(p.name for p in (target / '.lake').iterdir()) == {'build', 'config', 'packages'}
    for path in ('fgsa/AvailableChainFGSA/Tests/Keep.lean', '.lake/build/keep.olean',
                 '.lake/config/keep', '.lake/packages/dependency/keep'):
        assert not (target / path).is_symlink()
        assert (source / path).stat().st_ino != (target / path).stat().st_ino
        assert int((source / path).stat().st_mtime) == int((target / path).stat().st_mtime)
        (target / path).write_text('private edit\n')
        assert (source / path).read_text() == 'unchanged\n'
    fallback = root / 'rsync'
    subprocess.run(['bash', '-c',
                    'set -e; source "$1"; cp() { return 1; }; '
                    'gate_copy_control_tree "$2" "$3"', 'copy-fallback',
                    str(REPO / 'scripts/gate-common.sh'), str(source), str(fallback)], check=True)
    for path in ('.lake/build/keep.olean', '.lake/packages/dependency/keep'):
        (fallback / path).write_text('fallback edit\n')
        assert (source / path).read_text() == 'unchanged\n'
    # Exercise C23 in a nested source tree, including diagnostic and cleanup assertions.
    write(source / 'lakefile.toml',
          '[[lean_lib]]\nname="AvailableChainFGSA"\nsrcDir="fgsa"\n')
    write(source / 'scripts/source_layout.py', (REPO / 'scripts/source_layout.py').read_text())
    text = (REPO / 'scripts/check-fgsa.sh').read_text()
    function = text[text.index('control_glob_build() {'):text.index('control_closure() {')]
    write(source / 'bin/lake', '#!/usr/bin/env bash\n'
          'test -f fgsa/AvailableChainFGSA/Tests/NegBuildC23.lean || exit 2\n'
          'echo private-build > .lake/build/keep.olean\n'
          'echo private-package > .lake/packages/dependency/keep\n'
          'echo "AvailableChainFGSA.Tests.NegBuildC23 rejected"\nexit 1\n', True)
    (source / '.lake/control').mkdir()
    harness = ('set -euo pipefail\nsource "$1"\nneg=$PWD/.lake/control\n'
               'run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }\n'
               'expect_fail() { test "$2" = 1; [[ $3 == *"$4"* ]]; }\n' + function +
               '\ncontrol_glob_build\n')
    subprocess.run(['bash', '-c', harness, 'c23-control', str(REPO / 'scripts/gate-common.sh')],
                   cwd=source, env=dict(os.environ, PATH=str(source / 'bin') + os.pathsep +
                                       os.environ['PATH']), check=True)
    assert not (source / 'fgsa/AvailableChainFGSA/Tests/NegBuildC23.lean').exists()
    assert (source / '.lake/build/keep.olean').read_text() == 'unchanged\n'
    assert (source / '.lake/packages/dependency/keep').read_text() == 'unchanged\n'
    print('private source/build/config/packages (clone and rsync); C23 cleanup: PASS')


def pool_slots(root, slots):
    root.mkdir()
    events = root / 'events'
    stub = root / 'stub.py'
    write(stub, STUB)
    env = dict(os.environ, GATE_SLOTS=str(slots), GATE_SLOT_DIR=str(root / 'slots'),
               STUB_EVENTS=str(events), STUB_HEAVY=json.dumps(['a', 'b', 'c']), STUB_FAIL='')
    env.pop('GATE_SLOT_HELD', None)
    pool = AuditPool(root, 3, slot_script=REPO / 'scripts/gate-common.sh')
    pool.run_pool([(n, [sys.executable, str(stub), n], dict(env=env, cwd=root))
                   for n in ('a', 'b', 'c')])
    maximum = peak(records(events), {'a', 'b', 'c'})
    assert maximum == slots, maximum
    assert not list((root / 'slots').glob('slot.*'))
    print(f'audit pool workers=3 slots={slots}: peak={maximum}; slots released: PASS')


with tempfile.TemporaryDirectory(prefix='gate-graph-') as temp:
    # Stubs must not hide a stale assertion in the real manifest control suite.
    subprocess.run([sys.executable, '-B', 'scripts/fgsa-deep-controls.py', '--source-only'],
                   cwd=REPO, check=True)
    root = Path(temp)
    for tier, slots, fail in (('full', 1, ''), ('full', 2, ''), ('full', 3, ''),
                              ('full', 1, 'fgsa-claims'), ('full', 3, 'fgsa-claims'),
                              ('full', 2, 'build'),
                              ('full', 2, 'fg-finality-coverage'),
                              ('full', 2, 'fgsa-claims'), ('merge', 2, '')):
        graph(root / f'{tier}-{slots}-{fail or "pass"}', tier, slots, fail,
              force=tier == 'full')
    for tier in ('merge', 'full'):
        for label, change, force, env_neg in (
                ('proof', 'AvailableChainFGSAProofs/Proofs/Shared/Example.lean', False, '0'),
                ('script', 'scripts/new-check-data.txt', False, '0'),
                ('doc', 'docs/internal/catalog.lock', False, '0'),
                ('override', '', True, '0'), ('env-override', '', False, '1')):
            graph(root / (tier + '-' + label), tier, 2, change=change, force=force,
                  env_neg=env_neg)
    for slots in (1, 2, 3):
        graph(root / f'integration-{slots}', 'full', slots,
              change='AvailableChainFGSAProofs/Proofs/Shared/New.lean', integration=True, old_stamp=slots == 3)
    graph(root / 'integration-reviewed', 'full', 2, change='scripts/gly-f13-allow.txt',
          integration=True, reviewed=['scripts/gly-f13-allow.txt'])
    for label, change in (('inventory', 'scripts/fgsa-claims-expected.txt'),
                          ('snapshot', 'docs/internal/api/gen-deep.json')):
        graph(root / ('integration-' + label), 'full', 2, change=change, integration=True)
    graph(root / 'integration-g0-fail', 'full', 2, fail='package-g0',
          change='AvailableChainFGSAProofs/Proofs/Shared/New.lean', integration=True)
    copy_control(root / 'copy')
    for slots in (1, 2, 3):
        pool_slots(root / f'pool-{slots}', slots)
print('gate-graph-selftest: PASS')
