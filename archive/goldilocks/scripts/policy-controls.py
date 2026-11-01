#!/usr/bin/env python3
"""Fast negative controls for policy data, scope, and signed FULL receipts."""
import importlib.util
import json
import os
from pathlib import Path
from source_layout import Layout
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile

from check_inventory import parse_names
import import_policy as P

REPO = Path(__file__).resolve().parent.parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, REPO / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


scope = load('precheck-scope')
full = load('full-pass')
layers = load('check-layers')
guards = load('guard-lists')
coverage = load('check-proof-coverage')


def refused(label, reason, action):
    try:
        action()
    except (ValueError, OSError) as error:
        assert reason in str(error), (label, str(error))
        print(f'CONTROL {label}: PASS ({reason})')
    else:
        raise AssertionError(f'accepted {label}')


for text in ('()', "('__import__(\"os\")',)", "('valid', 2)", "['valid']"):
    refused('inventory data', 'inventory' if text == '()' else 'inventory',
            lambda: parse_names(text, 'inventory'))
assert parse_names("('AvailableChain.FGSA.Run.Base₂',)", 'unicode')
assert parse_names("('AvailableChain.FGSA.Run.blockOf?', 'lookup!')", 'Lean identifiers')
refused('inventory executable punctuation', 'inventory',
        lambda: parse_names("('lookup!()',)", 'inventory'))
refused('duplicate inventory', 'duplicate inventory',
        lambda: parse_names("('valid', 'valid')", 'inventory'))
for name in guards.LISTS:
    body = "#!/bin/bash\nexec python3 - <<'PY'\n"
    body += '\n'.join(f'{key} = ' + ("('a', 'a')" if key == name else "('a',)")
                      for key in guards.LISTS) + '\nPY\n'
    refused('duplicate guard ' + name, 'duplicate ' + name,
            lambda: guards.read_guard(body, 'control'))
# Generated inventories still require independent source coverage and exact
# compiled equality. Removing an audit target is not a guard-list waiver.
inventories = load('write-check-inventories')
current = load('current-inventory')
for expected, actual in [(('a',), ('a', 'b')), (('a', 'b'), ('a',))]:
    refused('current compiled inventory', 'INVENTORY DIFF',
            lambda: inventories.compare(expected, actual, 'control'))
from unittest.mock import patch
with patch.object(current, 'source_names', return_value={'Source.present', 'Source.new'}):
    refused('source inventory deletion/addition', 'SOURCE INVENTORY UNLISTED',
            lambda: current.check_source('control', ('Source.present',)))
assert current.public_lines('module\nnamespace A\npublic section\ndef visible := 1\n'
                            'end\ndef hidden := 1\nend A\n') == [False, False, True,
                                                                              True, True,
                                                                              False, False]
print('CONTROL module public/private section scope: PASS')
print('CONTROL source and compiled inventory completeness: PASS')
refused('duplicate import entries', 'duplicate import-policy entry',
        lambda: P.expand(['Init.**', 'Init.**']))
refused('duplicate JSON keys', 'duplicate import-policy key',
        lambda: P.read_policy('{"groups": {}, "groups": {}, "profiles": {}}'))
refused('duplicate raw import rows', 'duplicate import-policy entry',
        lambda: P.read_policy('{"groups":{"x":["Init", "Init"]},"profiles":{}}'))
refused('duplicate expanded import rows', 'duplicate expanded import-policy entry',
        lambda: P.expand(['@foundation', 'Init.**']))
for name in ('../Wrong', '@missing', 'AvailableChain*'):
    refused('import-policy data', 'import-policy', lambda: P.expand([name]))
for lib in P.POLICY['profiles']:
    assert P.allowed(lib, 'Model', lib + '.Model.Control')
    for layer, dep in [('Model', lib + '.Proofs.Control'),
                       ('root', 'Mathlib.Data.Nat.Basic'),
                       ('Proofs', 'AvailableChainKit.Engine.Clock')]:
        assert not P.allowed(lib, layer, dep), (lib, layer, dep)
print('CONTROL shared import layer refusals: PASS')
for text in ('', 'ALLOWED_PATHS:\n```text\n\n```',
             'ALLOWED_PATHS:\n```text\n../outside\n```',
             'ALLOWED_PATHS:\n```text\n/a\n```',
             'ALLOWED_PATHS:\n```text\n**\n```',
             'ALLOWED_PATHS:\n```text\n.\n```'):
    refused('brief syntax', 'ALLOWED_PATHS', lambda: scope.allowed_paths(text))


def call(args, cwd=None):
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert result.returncode == 0, result.stdout.decode()
    return result.stdout


with tempfile.TemporaryDirectory(prefix='guard-order-') as tmp:
    base, target = Path(tmp) / 'base.sh', Path(tmp) / 'target.sh'
    body = "#!/bin/bash\npython3 - <<'PY'\nEXPECTED = ('a', 'b')\nORDER = {}\nPY\n"
    base.write_text(body.format("('a', 'b')"))
    target.write_text(body.format("('b', 'a')"))
    output = call(['python3', '-B', 'scripts/guard-lists.py', 'diff',
                   '--main', str(base), '--target', str(target)]).decode()
    assert 'GUARD ORDER MOVED: a: 0 -> 1' in output
    assert 'GUARD ORDER MOVED: b: 1 -> 0' in output
    assert 'ADDED' not in output and 'REMOVED' not in output
    print('CONTROL ORDER move without membership change: PASS')


with tempfile.TemporaryDirectory(prefix='inventory-shell-') as tmp:
    root = Path(tmp)
    (root / 'scripts').mkdir()
    shutil.copy2(REPO / 'scripts/check_inventory.py', root / 'scripts/check_inventory.py')
    shutil.copy2(REPO / 'scripts/gate-common.sh', root / 'scripts/gate-common.sh')
    # Run the real driver setup, before its first filesystem/build operation.
    setup = (REPO / 'scripts/check-fg.sh').read_text().split('targets=$(python3', 1)[0]
    driver = root / 'scripts/check-fg.sh'
    driver.write_text(setup + 'gate_inventory_args names.txt\n')
    (root / 'names.txt').write_text("('lookup?', 'lookup!',)\n")
    call(['bash', str(driver)])
    driver.write_text(setup.replace('source scripts/gate-common.sh\n', '') +
                      'gate_inventory_args names.txt\n')
    result = subprocess.run(['bash', str(driver)], capture_output=True)
    assert result.returncode == 127 and b'gate_inventory_args: command not found' in result.stderr
    print('CONTROL FG driver setup without shared helper: PASS (source only)')
    (root / 'names.txt').write_text("('lookup?', 'lookup!',)\n")
    (root / 'lookupX').touch()
    script = ('source "$1"; gate_inventory_args names.txt; '
              'test "${#GATE_INVENTORY[@]}" = 2; '
              'test "${GATE_INVENTORY[0]}" = "lookup?"; '
              'test "${GATE_INVENTORY[1]}" = "lookup!"')
    result = subprocess.run(['bash', '-ec', script, 'inventory-control',
                             str(REPO / 'scripts/gate-common.sh')], cwd=root)
    assert result.returncode == 0
    (root / 'names.txt').write_text("('lookup?', 'lookup?',)\n")
    result = subprocess.run(['bash', '-ec', script, 'inventory-control',
                             str(REPO / 'scripts/gate-common.sh')], cwd=root, capture_output=True)
    assert result.returncode != 0 and b'duplicate inventory' in result.stderr
    print('CONTROL shell inventory glob collision and malformed data: PASS')

with tempfile.TemporaryDirectory(prefix='policy-controls-') as tmp:
    root = Path(tmp).resolve()
    # Exercise the gate entry point before any precheck, build or allocation.
    gate = root / 'gate/scripts'
    gate.mkdir(parents=True)
    for name in ('gate.sh', 'gate-common.sh', 'checker_scope.py',
                 'checker-paths.txt', 'source_layout.py'):
        shutil.copy2(REPO / 'scripts' / name, gate / name)
    result = subprocess.run(['bash', str(gate / 'gate.sh'), '--tier', 'full'],
                            env=dict(os.environ, SOURCE_ONLY='1'), capture_output=True, text=True)
    assert result.returncode == 2 and 'GATE REFUSED: SOURCE_ONLY' in result.stderr
    assert not (gate.parent / '.lake').exists()
    print('CONTROL gate refuses inherited SOURCE_ONLY before work: PASS')
    data = root / 'coverage'
    for label, raw in (
        ('audit key', "{'A': {'O': ('n',)}, 'A': {'O': ('m',)}}"),
        ('owner key', "{'A': {'O': ('n',), 'O': ('m',)}}"),
        ('name', "{'A': {'O': ('n', 'n')}}"),
        ('name across owners', "{'A': {'O': ('n',), 'P': ('n',)}}"),
    ):
        data.write_text(raw)
        refused('duplicate coverage ' + label, 'duplicate proof coverage',
                lambda: coverage.read_coverage(data))
    data.write_text(repr({'A': {'O': ("B'_resetF", 'block?_proposal', "clock_gate'")}}))
    assert len(coverage.read_coverage(data)) == 3
    print('CONTROL coverage primes and question marks: PASS')
    generated = root / 'generated'
    generated.mkdir()
    (generated / 'AvailableChainCheckSupport').mkdir()
    for name in ('generate-import-policy.py', 'import_policy.py', 'import-policy.json',
                 'import-policy.sh', 'AvailableChainCheckSupport/ImportPolicy.lean'):
        shutil.copy2(REPO / 'scripts' / name, generated / name)
    command = [sys.executable, str(generated / 'generate-import-policy.py'), '--check']
    call(command)
    with (generated / 'import-policy.sh').open('a') as output:
        output.write('# stale generated data\n')
    result = subprocess.run(command, capture_output=True, text=True)
    assert result.returncode != 0 and 'IMPORT POLICY DRIFT' in result.stderr
    print('CONTROL stale generated import policy: PASS')

    # Exact KitFG names must refer to a real module in the chosen checkout.
    source = root / 'layers'
    source.mkdir()
    shutil.copy2(REPO / 'lakefile.toml', source / 'lakefile.toml')
    (source / 'scripts/baselines').mkdir(parents=True)
    shutil.copy2(REPO / 'scripts/CatalogLock.lean', source / 'scripts/CatalogLock.lean')
    data = source / 'scripts/baselines/kitfg-def-modules.txt'
    for name, reason in [('AvailableChainKitFG.ViewLock', 'invalid short'),
                         ('Missing', 'missing KitFG'), ('ViewLock.Extra', 'invalid short')]:
        data.write_text(name + '\n')
        refused('KitFG definition ' + name, reason, lambda: layers.load_context(source))
    data.write_text('ViewLock\n')
    (source / Layout(source).source_dir('AvailableChainKitFG')).mkdir(parents=True)
    (source / Layout(source).source_path('AvailableChainKitFG.ViewLock')).write_text('module\n')
    assert layers.load_context(source).definitions == {'AvailableChainKitFG.ViewLock'}
    print('CONTROL KitFG short existing module: PASS')

    # A private fixture repository supplies the trusted policy and exact HEAD.
    repo = root / 'repo'
    repo.mkdir()
    call(['git', 'init', '-q', str(repo)])
    (repo / 'scripts').mkdir()
    (repo / 'lakefile.toml').write_text('name="policy-fixture"\n')
    for name in ('precheck.sh', 'full-pass.py', 'checker_scope.py',
                 'checker-paths.txt', 'source_layout.py'):
        shutil.copy2(REPO / 'scripts' / name, repo / 'scripts' / name)
    (repo / 'allowed').mkdir()
    (repo / 'allowed/a').write_text('base\n')
    (repo / 'forbidden-source').write_text('base\n')
    key = root / 'key'
    call(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-f', str(key)])
    (repo / 'scripts/full-pass-signers').write_text(
        full.IDENTITY + ' ' + key.with_suffix('.pub').read_text())
    call(['git', 'add', '.'], repo)
    tree = call(['git', 'write-tree'], repo).decode().strip()
    head = subprocess.check_output(['git', '-c', 'user.name=Control',
        '-c', 'user.email=control@example.invalid', 'commit-tree', tree],
        cwd=repo, input=b'isolated policy fixture\n').decode().strip()
    call(['git', 'update-ref', 'HEAD', head], repo)
    brief = root / 'brief'
    brief.write_text('ALLOWED_PATHS:\n```text\nallowed/\n```\n')
    (repo / 'allowed/a').write_text('edit\n')
    scope.check(repo, head, brief)
    (repo / 'outside').write_text('untracked\n')
    refused('untracked scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'add', 'outside'], repo)
    refused('staged scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'reset', '-q', '--', 'outside'], repo)
    (repo / 'outside').unlink()
    (repo / 'forbidden-source').rename(repo / 'allowed/b')
    refused('rename source scope', 'DIFF SCOPE REFUSED',
            lambda: scope.check(repo, head, brief))
    (repo / 'allowed/b').rename(repo / 'forbidden-source')
    (repo / 'forbidden-source').unlink()
    refused('deletion scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'checkout', '--', 'forbidden-source'], repo)
    # A rename is checked as a deletion and an addition, including its old path.
    (repo / 'allowed/a').rename(repo / 'outside')
    refused('rename scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    (repo / 'outside').unlink()
    call(['git', 'checkout', '--', 'allowed/a'], repo)
    receipt = root / 'receipt'
    refused('missing receipt', 'MISSING', lambda: full.verify(repo, repo, receipt))
    control_scope = full.validate(repo, head, head,
        dict(neg=1, reason='empty range', matched_paths=[]))
    record = dict(version=2, head=head, policy=head, tier='full', result='PASS',
                  controls=control_scope)
    receipt.write_text(json.dumps(record))
    refused('forged unsigned receipt', 'SIGNATURE REFUSED',
            lambda: full.verify(repo, repo, receipt))
    # Sign through the same producer as gate.sh. Missing/failed steps must refuse.
    logs = root / 'logs'
    logs.mkdir()
    (logs / 'negative-controls.json').write_text(json.dumps(control_scope))
    refused('empty FULL step set', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').write_text('0 1\n')
    refused('partial FULL step set', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    for step in full.steps_for(control_scope):
        (logs / (step + '.result')).write_text('0 1\n')
    for step in full.steps_for(control_scope):
        result = logs / (step + '.result')
        result.unlink()
        refused('missing FULL step ' + step, 'FAILED OR MISSING STEP SET',
                lambda: full.sign(repo, head, head, logs, key, receipt))
        result.write_text('1 1\n')
        refused('failed FULL step ' + step, 'FAILED OR MISSING STEP: ' + step,
                lambda: full.sign(repo, head, head, logs, key, receipt))
        result.write_text('0 1\n')
    (logs / 'build.result').write_text('1 1\n')
    refused('failed FULL step', 'FAILED OR MISSING STEP',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').unlink()
    refused('missing FULL step', 'FAILED OR MISSING STEP',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').write_text('0 1\n')
    (logs / 'unexpected.result').write_text('0 1\n')
    refused('extra FULL step', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'unexpected.result').unlink()
    full.sign(repo, head, head, logs, key, receipt)
    full.verify(repo, repo, receipt)
    output = call(['bash', str(repo / 'scripts/precheck.sh'),
                   '--full-pass', str(receipt), str(repo)]).decode()
    assert 'MAIN POLICY COPY SKIPPED: verified exact-head FULL PASS' in output
    print('CONTROL precheck verified FULL mode: PASS')
    signed = receipt.read_bytes()
    for field, value, reason in [('head', '0' * 40, 'WRONG HEAD'),
                                  ('tier', 'merge', 'NOT FULL PASS'),
                                  ('policy', '0' * 40, 'WRONG POLICY HEAD'),
                                  ('result', 'FAIL', 'NOT FULL PASS')]:
        receipt.write_text(json.dumps(dict(record, **{field: value})))
        refused('receipt ' + field, reason, lambda: full.verify(repo, repo, receipt))
    receipt.write_bytes(signed + b' ')
    refused('forged signed payload', 'SIGNATURE REFUSED',
            lambda: full.verify(repo, repo, receipt))
    receipt.write_bytes(signed)
    (repo / 'allowed/a').write_text('dirty\n')
    refused('dirty exact head', 'DIRTY TARGET', lambda: full.verify(repo, repo, receipt))
    call(['git', 'checkout', '--', 'allowed/a'], repo)
    # An ignored source can change a Lake glob without changing the commit.
    (repo / '.git/info/exclude').write_text('hidden.lean\n')
    (repo / 'hidden.lean').write_text('def hidden : Nat := 0\n')
    refused('ignored source', 'IGNORED SOURCE', lambda: full.verify(repo, repo, receipt))
    (repo / 'hidden.lean').unlink()
    # Local trust edits do not add an issuer; only main's committed file is read.
    other_key = root / 'other-key'
    call(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-f', str(other_key)])
    receipt.with_suffix('.sig').unlink()
    call(['ssh-keygen', '-Y', 'sign', '-f', str(other_key), '-n', full.NAMESPACE,
          str(receipt)])
    refused('untrusted issuer', 'SIGNATURE REFUSED', lambda: full.verify(repo, repo, receipt))
    # NEG=0 on a non-empty range: policy checkout at the parent, proof-only child.
    policy_repo = root / 'policy'
    call(['git', 'clone', '-q', str(repo), str(policy_repo)])
    (repo / 'Proofs').mkdir()
    (repo / 'Proofs/Example.lean').write_text('theorem example0 : True := trivial\n')
    call(['git', 'add', '.'], repo)
    tree = call(['git', 'write-tree'], repo).decode().strip()
    child = subprocess.check_output(['git', '-c', 'user.name=Control',
        '-c', 'user.email=control@example.invalid', 'commit-tree', tree, '-p', head],
        cwd=repo, input=b'proof-only child\n').decode().strip()
    call(['git', 'update-ref', 'HEAD', child], repo)
    assert child != head
    scope0 = full.validate(repo, head, child,
        dict(neg=0, reason='no checker path changed', matched_paths=[]))
    assert 'checker-self-tests' not in full.steps_for(scope0)
    logs0 = root / 'logs0'
    logs0.mkdir()
    (logs0 / 'negative-controls.json').write_text(json.dumps(scope0))
    for step in full.steps_for(scope0):
        (logs0 / (step + '.result')).write_text('0 1\n')
    receipt0 = root / 'receipt0'
    full.sign(repo, child, head, logs0, key, receipt0)
    full.verify(policy_repo, repo, receipt0)
    output = call(['bash', str(policy_repo / 'scripts/precheck.sh'),
                   '--full-pass', str(receipt0), str(repo)]).decode()
    assert 'MAIN POLICY COPY SKIPPED: verified exact-head FULL PASS' in output
    print('CONTROL signed NEG=0 receipt on a non-empty range: PASS')

with tempfile.TemporaryDirectory(prefix='compose-gate-policy-') as tmp:
    tree = Path(tmp)
    scripts = tree / 'scripts'
    scripts.mkdir()
    (tree / '.lake').mkdir()
    for name in ('gate.sh', 'gate-common.sh', 'checker_scope.py', 'checker-paths.txt',
                 'unported.py', 'unported-libraries.txt', 'gate_timing.py', 'source_layout.py'):
        shutil.copy2(REPO / 'scripts' / name, scripts / name)
    (tree / 'lakefile.toml').write_text(''.join(
        '[[lean_lib]]\nname="' + lib + '"\n' for lib in
        ('AvailableChainGeneric', 'AvailableChainFGSA', 'AvailableChainFGSARun',
         'AvailableChainFGSAClaims', 'AvailableChainFGSAProofs', 'AvailableChainFGCompose')))
    # Keep the real tier dispatch. The unrelated steps have local stub commands.
    with (scripts / 'gate-common.sh').open('a') as out:
        out.write('\ngate_precheck() { return 0; }\n'
                  'gate_check_base() { return 0; }\n'
                  f'gate_select_neg() {{ cd {str(REPO)!r}; '
                  'local force=$2; GATE_NEG_SCOPE=$(python3 scripts/checker_scope.py '
                  '"$PWD" HEAD HEAD $([ "$force" = 0 ] || echo --force)); '
                  'NEG=$force; export NEG; cd - >/dev/null; }\n')
    for name in ('check-build.sh', 'check-fgsa.sh', 'check-fgsa-run.sh',
                 'check-fgsa-manifest.sh', 'check-fgsa-claims.sh'):
        (scripts / name).write_text('#!/bin/bash\nexit 0\n')
    (scripts / 'check-proof-coverage.py').write_text('print("coverage stub")\n')
    for name in ('check-fg-finality-coverage.py',
                 'check-fgsa-blueprint.py'):
        (scripts / name).write_text('print("P13 stub")\n')
    (scripts / 'check-fg-compose.sh').write_text(
        '#!/bin/bash\necho "compose NEG=$NEG" >> calls\n')
    bindir = tree / 'bin'
    bindir.mkdir()
    fake = bindir / 'lake'
    fake.write_text('#!/bin/bash\necho "lake $*" >> calls\n'
                    'case "$*" in *--libraries*) echo AvailableChainFGCompose ;;\n'
                    "  *WeakContinuationGrowthAssemblyAxioms*) echo \"'x' depends on axioms: "
                    '[propext, ${BAD_AXIOM:-Quot.sound}]" ;; esac\n')
    growth = tree / 'AvailableChainFGSAProofs/Tests/WeakContinuationGrowthAssemblyAxioms.lean'
    growth.parent.mkdir(parents=True)
    growth.write_text('#print axioms x\n')
    fake.chmod(0o755)
    env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'])
    for tier, neg in [('merge', '0'), ('full', '1')]:
        result = subprocess.run(['bash', 'scripts/gate.sh', '--tier', tier,
                                 '--base', 'HEAD'], cwd=tree,
                                env=dict(env, NEG=neg), text=True, capture_output=True)
        assert result.returncode == 0, (tier, result.stdout, result.stderr)
        calls = (tree / 'calls').read_text()
        assert 'build --wfail @ AvailableChainCheckSupport AvailableChainFGCompose' in calls, calls
        assert 'compose NEG=' + neg in calls, calls
        assert 'FGCompose-axioms rc=0' in result.stdout, result.stdout
        assert 'FGSACompose-axioms rc=0' in result.stdout, result.stdout
        assert 'PCSACompose-axioms' not in result.stdout, result.stdout
        assert 'PCSASafety-axioms' not in result.stdout, result.stdout
        assert 'pcsa-manifest' not in result.stdout, result.stdout
        for step in ('FGSAGrowth-axioms', 'fg-finality-coverage'):
            assert step + ' rc=0' in result.stdout, result.stdout
        # The compiled blueprint check runs in the FULL tier only.
        assert ('fgsa-blueprint rc=0' in result.stdout) == (tier == 'full'), result.stdout
        (tree / 'calls').write_text('')
        print(f'CONTROL Compose gate {tier}: build, scan and NEG={neg}: PASS')
    # The growth audit step fails on a project axiom and on a missing result.
    for label, extra, text, reason in [
            ('project axiom', {'BAD_AXIOM': 'Fix.bad'}, '#print axioms x\n', 'BAD AXIOMS: Fix.bad'),
            ('missing result', {}, '#print axioms x\n#print axioms y\n',
             'AXIOM RESULTS: 1 of 2 commands')]:
        growth.write_text(text)
        result = subprocess.run(['bash', 'scripts/gate.sh', '--tier', 'merge',
                                 '--base', 'HEAD'], cwd=tree,
                                env=dict(env, **extra), text=True, capture_output=True)
        logs = sorted((tree / '.lake').glob('gate-logs.*/FGSAGrowth-axioms*'))
        output = result.stdout + ''.join(path.read_text() for path in logs)
        assert result.returncode != 0 and 'FGSAGrowth-axioms rc=1' in result.stdout, result.stdout
        assert reason in output, output
        print(f'CONTROL growth audit {label}: PASS ({reason})')

print('policy-controls: PASS')
