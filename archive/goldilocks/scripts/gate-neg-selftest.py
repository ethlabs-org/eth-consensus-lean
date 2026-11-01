#!/usr/bin/env python3
"""Test checker scope and receipt rules with isolated commits; no Lean or gate tier."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from unittest.mock import patch

from checker_scope import select, validate

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('full_pass', REPO / 'scripts/full-pass.py')
full = importlib.util.module_from_spec(spec)
spec.loader.exec_module(full)


REAL_RUN = subprocess.run


def signing_stub(args, **kwargs):
    if args[0] == 'ssh-keygen':
        return subprocess.CompletedProcess(args, 0)
    return REAL_RUN(args, **kwargs)


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def commit(root, parent=None):
    git(root, 'add', '.')
    tree = git(root, 'write-tree')
    args = ['git', '-C', str(root), '-c', 'user.name=Control', '-c',
            'user.email=control@example.invalid', 'commit-tree', tree]
    if parent:
        args += ['-p', parent]
    head = subprocess.check_output(args, input='scope fixture\n', text=True).strip()
    git(root, 'update-ref', 'HEAD', head)
    return head


with tempfile.TemporaryDirectory(prefix='gate-neg-') as tmp:
    root = Path(tmp)
    git(root, 'init', '-q')
    (root / 'scripts').mkdir()
    shutil.copy2(REPO / 'scripts/checker-paths.txt', root / 'scripts/checker-paths.txt')
    (root / 'lakefile.toml').write_text(
        '[[lean_lib]]\nname="AvailableChainKitFG"\n'
        '[[lean_lib]]\nname="AvailableChainFGSAProofs"\n')
    base = commit(root)
    for label, path, want in (
            ('proof only', 'AvailableChainFGSAProofs/Proofs/Shared/Example.lean', 0),
            ('scripts data', 'scripts/new-inventory.txt', 1),
            ('docs data outside old tier list', 'docs/internal/catalog.lock', 1),
            ('current dependency snapshot', 'docs/internal/api/fgsa-deep.json', 1),
            ('historical port ledger', 'docs/internal/FGSA-PORT-CHANGES.json', 0),
            ('blueprint chapter', 'docs/internal/blueprint/fgsa/new.tex', 1),
            ('new control module', 'FGSAControl/New.lean', 1),
            ('audit input', 'AvailableChainFGSAProofs/Tests/Axioms.lean', 1),
            ('FG pin checker data', 'AvailableChainKitFG/Pins.lean', 1),
            ('ordinary docs', 'docs/internal/unrelated.md', 0)):
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text('fixture\n')
        head = commit(root, base)
        scope = select(root, base, head)
        assert scope['neg'] == want, (label, scope)
        assert scope['matched_paths'] == ([path] if want else []), scope
        validate(root, base, head, scope)
        forced = select(root, base, head, True)
        assert forced['neg'] == 1 and forced['reason'] == 'override', forced
        logs = Path(tmp) / '.lake/logs'
        logs.mkdir(parents=True, exist_ok=True)
        (logs / 'negative-controls.json').write_text(json.dumps(scope))
        for step in full.steps_for(scope):
            (logs / (step + '.result')).write_text('0 1\n')
        with patch.object(full, 'clean_head'), \
                patch.object(full.subprocess, 'run', side_effect=signing_stub):
            full.sign(root, head, base, logs, root / 'key', logs / 'receipt.json')
            record = json.loads((logs / 'receipt.json').read_text())
            assert record['controls'] == scope and record['version'] == 2
            if want:
                bad = dict(neg=0, reason='no checker path changed', matched_paths=[])
                (logs / 'negative-controls.json').write_text(json.dumps(bad))
                try:
                    full.sign(root, head, base, logs, root / 'key', logs / 'bad.json')
                except ValueError as exc:
                    assert 'CONTROL SCOPE' in str(exc), exc
                else:
                    raise AssertionError('receipt accepted skipped controls for ' + path)
            (logs / 'negative-controls.json').write_text(json.dumps(scope))
            marker = logs / 'checker-self-tests.result'
            if want:
                marker.unlink()
            else:
                marker.write_text('0 1\n')
            try:
                full.sign(root, head, base, logs, root / 'key', logs / 'bad.json')
            except ValueError as exc:
                assert 'STEP SET' in str(exc), exc
            else:
                raise AssertionError('receipt accepted wrong control step set')
        shutil.rmtree(root / '.lake')
        print(f'CONTROL scope {label}: NEG={want}; override and receipt rules: PASS')
        base = head

    # base = HEAD (main after a landing): an empty range selects the controls.
    scope = select(root, base, base)
    assert scope == dict(neg=1, reason='empty range', matched_paths=[]), scope
    validate(root, base, base, scope)
    try:
        validate(root, base, base, dict(neg=0, reason='no checker path changed',
                                        matched_paths=[]))
    except ValueError as exc:
        assert 'CONTROL SCOPE' in str(exc), exc
    else:
        raise AssertionError('receipt accepted NEG=0 for an empty range')
    print('CONTROL scope empty range (base = HEAD): NEG=1: PASS')

# Run the actual claims source fixtures up to the compiled checks, without Lean.
text = (REPO / 'scripts/check-fgsa-claims.sh').read_text()
body = text.split("<<'PY'\n", 1)[1].split('\nfor lib in LIBS:\n    build(', 1)[0]
for neg in ('0', '1'):
    result = subprocess.run(['python3', '-B', '-c', body], cwd=REPO,
                            env=dict(os.environ, SOURCE_ONLY='0', NEG=neg),
                            capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    assert ('rejected as expected' in result.stdout) == (neg == '1'), result.stdout
    assert 'f4-reach-twin: rc 0' in result.stdout, result.stdout
    print(f'CONTROL claims source fixtures NEG={neg}: selection and positive checks: PASS')
print('gate-neg-selftest: PASS')
