#!/usr/bin/env python3
"""Check each provisional eligibility class without a Lean process."""
import importlib
import json
import os
from pathlib import Path
from source_layout import Layout
import shutil
import subprocess
import tempfile

from integration_scope import select

REPO = Path(__file__).resolve().parents[1]


def write(root, path, text):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)


def commit(root):
    subprocess.run(['git', 'add', '.'], cwd=root, check=True)
    subprocess.run(['git', '-c', 'user.name=Control', '-c',
                    'user.email=control@example.invalid', 'commit', '-qm', 'control'],
                   cwd=root, check=True)
    return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()


with tempfile.TemporaryDirectory(prefix='gate-integration-') as scratch:
    seed = Path(scratch) / 'seed'
    seed.mkdir()
    subprocess.run(['git', 'init', '-q', str(seed)], check=True)
    subprocess.run(['git', 'symbolic-ref', 'HEAD', 'refs/heads/p0-control'], cwd=seed, check=True)
    (seed / 'scripts').mkdir()
    for name in ('checker-paths.txt', 'gate.sh', 'check-fgsa-claims.sh', 'check-fg-compose.sh',
                 'check-fgsa-manifest.sh', 'check-fgsa-run.sh', 'check-fgsa.sh'):
        shutil.copy2(REPO / 'scripts' / name, seed / 'scripts' / name)
    snapshot = dict(entries={'old': {'digest': 'abc'}}, nodes={'old': {'kind': 'theorem'}},
                    node_order=['old'], format_version=1, pins={'toolchain': 'fixed'})
    files = {
        'scripts/fgsa-claims-expected.txt': "('Old.name',)\n",
        'scripts/claims-model-scope.txt': 'AvailableChainFGSA.Model.Objects Old.name\n',
        'scripts/gly-f13-allow.txt': 'Old.exemption\n',
        'scripts/baselines/check-layers.txt': 'old finding\n',
        'scripts/unported-libraries.txt': 'AvailableChainPCSA\n',
        'scripts/fixture.py': 'value = 1\n',
        'lean-toolchain': 'fixed\n', 'lakefile.toml': ('name = "control"\n' + ''.join(
            '[[lean_lib]]\nname="' + lib + '"\n' for lib in
            ('AvailableChainGeneric', 'AvailableChainFGSAProofs', 'AvailableChainFGSA'))),
        'lake-manifest.json': '{}\n',
        'AvailableChainFGSAProofs/Proofs/Shared/Keep.lean': 'module\n',
        'AvailableChainGeneric.lean': 'module\npublic import AvailableChainGeneric.Keep\n',
        'AvailableChainGeneric/Keep.lean': 'module\npublic section\ndef Old.name := 1\n',
        'AvailableChainGeneric/Extract.lean': 'module\npublic import Init\n\npublic section\nnamespace Old\ndef moved := 1\nend Old\n',
        'AvailableChainFGSA/Tests/Control.lean': 'module\n',
        'docs/internal/api/compose-api.json': json.dumps(snapshot),
    }
    for path, text in files.items():
        write(seed, path, text)
    for path in ('docs/internal/GEN-API.md', 'docs/internal/FGSA-API.md',
                 'docs/internal/api/gen-deep.json'):
        write(seed, path, (REPO / path).read_text())
    write(seed, 'scripts/check-fgsa-blueprint.py', (REPO / 'scripts/check-fgsa-blueprint.py').read_text())
    base = commit(seed)

    def candidate(label, edits, reviewed=(), eligible=False, extractions=()):
        root = Path(scratch) / label
        shutil.copytree(seed, root)
        for path, text in edits.items():
            if text is None:
                (root / path).unlink()
            else:
                write(root, path, text)
        commit(root)
        try:
            result = select(root, base, reviewed=reviewed, extractions=extractions)
        except (ValueError, subprocess.CalledProcessError) as error:
            assert not eligible, (label, error)
            print(f'CONTROL integration {label}: REFUSED ({error})')
            return root
        assert eligible, ('ineligible candidate accepted', label, result)
        assert result['base'] == base and result['head'] != base
        assert result['main_accepted'] is False and result['full_receipt'] is False
        assert bool(result['deferred_controls']) == (not reviewed)
        assert result['neg'] == int(bool(reviewed))
        assert len(result['reviewed_extractions']) == len(extractions)
        for record in result['reviewed_extractions']:
            assert record['base'] == base and record['head'] == result['head']
            assert record['before_sha256'] == record['target_sha256']
        assert not (root / '.lake/gate-last-full').exists()
        print(f'CONTROL integration {label}: eligible; no FULL stamp')
        return root

    added = dict(snapshot)
    added['entries'] = dict(snapshot['entries'], new={'digest': 'def'})
    added['nodes'] = dict(snapshot['nodes'], new={'kind': 'theorem'})
    added['node_order'] = ['old', 'new']
    claims = (seed / 'scripts/check-fgsa-claims.sh').read_text()
    ast_added = claims.replace("ORDER = ('Recurrence',", "ORDER = ('NewLane', 'Recurrence',")
    blueprint = (seed / 'scripts/check-fgsa-blueprint.py').read_text()
    # Exercise each real constant without importing or executing its checker.
    for constant, path, original, anchor, valid, old in (
        ('SAFETY_FIELDS', 'scripts/check-fgsa-blueprint.py', blueprint,
         "'assembled package')", 'newField', 'assembled package'),
        ('CLAIMS_STRUCTURES', 'scripts/check-fgsa-blueprint.py', blueprint,
         "'FGSAClaims')", 'NewClaims', 'FGSAClaims'),
        ('ORDER', 'scripts/check-fgsa-claims.sh', claims,
         "'Packages.Healing')", 'NewLane', 'Packages.Healing'),
    ):
        def extend(literal):
            return original.replace(anchor, anchor[:-1] + ', ' + literal + ')', 1)
        candidate(constant + '-addition', {path: extend(repr(valid))}, eligible=True)
        for label, literal in (('duplicate', repr(old)), ('wildcard', repr('New*Field')),
                               ('glob-question', repr('New?Field')), ('glob-class', repr('New[AB]Field')),
                               ('expression', "str('NewField')"), ('wrong-type', '42')):
            candidate(constant + '-' + label, {path: extend(literal)})
        candidate(constant + '-removal', {path: extend(repr(valid)).replace(repr(old) + ',', '', 1)})
        candidate(constant + '-logic', {path: extend(repr(valid)) + '\nunsafe_logic = True\n'})
    candidate('SAFETY_FIELDS-label-addition', {'scripts/check-fgsa-blueprint.py':
              blueprint.replace("'assembled package')", "'assembled package', 'new field')")}, eligible=True)
    candidate('CLAIMS_STRUCTURES-qualified-name', {'scripts/check-fgsa-blueprint.py':
              blueprint.replace("'FGSAClaims')", "'FGSAClaims', 'New.Claims')")})
    scope_anchor = 'REQUIRED_MODEL_SCOPE = {\n'
    scope_pair = "('AvailableChainFGSA.Model.RowCore', 'AvailableChain.FGSA.newField')"
    scope_added = claims.replace(scope_anchor, scope_anchor + '    ' + scope_pair + ',\n', 1)
    candidate('REQUIRED_MODEL_SCOPE-addition', {'scripts/check-fgsa-claims.sh': scope_added}, eligible=True)
    for label, content in (
        ('duplicate', scope_added.replace(scope_anchor, scope_anchor + '    ' + scope_pair + ',\n', 1)),
        ('wildcard', scope_added.replace('AvailableChain.FGSA.newField', 'AvailableChain.FGSA.*')),
        ('wrong-owner', scope_added.replace("'AvailableChainFGSA.Model.RowCore', 'AvailableChain.FGSA.newField'",
                                            "'AvailableChainGeneric.Model.RowCore', 'AvailableChain.FGSA.newField'")),
        ('wrong-shape', claims.replace(scope_anchor, scope_anchor + "    'NewField',\n", 1)),
        ('removal', scope_added.replace("'AvailableChain.FGSA.parentFoldState_def'", "'AvailableChain.FGSA.changed'", 1)),
        ('logic', scope_added.replace('workers = audit_workers()', 'workers = 1')),
    ):
        candidate('REQUIRED_MODEL_SCOPE-' + label, {'scripts/check-fgsa-claims.sh': content})
    eligible = candidate('additions', {
        'scripts/fgsa-claims-expected.txt': "('Old.name', 'New.name')\n",
        'scripts/claims-model-scope.txt': files['scripts/claims-model-scope.txt'] +
            'AvailableChainFGSA.Model.RowCore New.name\n',
        'docs/internal/api/compose-api.json': json.dumps(added),
        'scripts/check-fgsa-claims.sh': ast_added,
        'AvailableChainFGSAProofs/Proofs/Shared/New.lean': 'module\n',
        'AvailableChainFGSAProofs/Tests/PackageG0.lean': 'module\n',
    }, eligible=True)
    candidate('source-addition', {'AvailableChainGeneric/Keep.lean':
              files['AvailableChainGeneric/Keep.lean'] + 'def New.name : Nat := 2\n'}, eligible=True)
    candidate('facade-import-addition', {'AvailableChainGeneric.lean':
              files['AvailableChainGeneric.lean'] + 'public import AvailableChainGeneric.New\n',
              'AvailableChainGeneric/New.lean': 'module\npublic section\ndef New.name := 2\n'}, eligible=True)
    extraction = {
        'AvailableChainGeneric/Extract.lean': 'module\npublic import Init\n\npublic import AvailableChainGeneric.Moved\n',
        'AvailableChainGeneric/Moved.lean': files['AvailableChainGeneric/Extract.lean'],
    }
    pair = 'AvailableChainGeneric/Extract.lean:AvailableChainGeneric/Moved.lean'
    candidate('reviewed-extraction', extraction, extractions=[pair], eligible=True)
    candidate('unreviewed-extraction', extraction)
    candidate('extraction-changed-body', dict(extraction, **{
        'AvailableChainGeneric/Moved.lean': files['AvailableChainGeneric/Extract.lean'].replace(':= 1', ':= 2')}),
        extractions=[pair])
    candidate('extraction-removed-import', dict(extraction, **{
        'AvailableChainGeneric/Extract.lean': 'module\npublic import AvailableChainGeneric.Moved\n'}),
        extractions=[pair])
    candidate('extraction-existing-target', {'AvailableChainGeneric/Extract.lean':
        'module\npublic import AvailableChainGeneric.Keep\n'},
        extractions=['AvailableChainGeneric/Extract.lean:AvailableChainGeneric/Keep.lean'])
    # Use the real generated manifests and deep schema, not the toy snapshot.
    shallow = (seed / 'docs/internal/GEN-API.md').read_text()
    deep = json.loads((seed / 'docs/internal/api/gen-deep.json').read_text())
    owner = 'AvailableChainGeneric.Statements.ZZGateEligibility'
    name = 'AvailableChain.Gen.gateEligibilityAdded'
    shallow_added = shallow.replace('Entries: 852; modules: 55.', 'Entries: 853; modules: 56.') + (
        f'\n### `{owner}`\n\n```text\ndef {name} 123456789abcdef0\n```\n')
    deep['entries'][name] = dict(module=owner, kind='def', digest='1' * 64)
    node = dict(next(iter(deep['nodes'].values())))
    node.update(module=owner, kind='def', digest='1' * 64,
                kernel_name='str:2:12:anonymous:0:20:gateEligibilityAdded')
    deep['nodes'][name] = node
    deep['node_order'] = [*deep['node_order'], name]
    generic = {
        'AvailableChainGeneric.lean': files['AvailableChainGeneric.lean'] + f'public import {owner}\n',
        owner.replace('.', '/') + '.lean':
            'module\n\npublic section\nnamespace AvailableChain.Gen\ndef gateEligibilityAdded : Nat := 1\nend AvailableChain.Gen\n',
        'docs/internal/GEN-API.md': shallow_added,
        'docs/internal/api/gen-deep.json': json.dumps(deep),
    }
    candidate('generic-shallow-and-deep-addition', generic, eligible=True)
    fgsa = (seed / 'docs/internal/FGSA-API.md').read_text()
    fgsa_added = fgsa.replace('Entries: 1358;', 'Entries: 1359;', 1).replace(
        '```\n', 'def AvailableChain.FGSA.gateEligibilityAdded 123456789abcdef0\n```\n', 1)
    candidate('fgsa-shallow-addition', {'docs/internal/FGSA-API.md': fgsa_added}, eligible=True)
    for label, content in (
        ('shallow-declaration-removal', shallow_added.replace(
            'structure AvailableChain.Gen.AC.Duty.ACReads a5157729fa91592f\n', '').replace('Entries: 853;', 'Entries: 852;')),
        ('shallow-owner-change', shallow_added.replace(
            '### `AvailableChainGeneric.Statements.AC.Duty.Reads`', '### `AvailableChainGeneric.Statements.AC.Duty.Renamed`')),
        ('shallow-kind-change', shallow_added.replace('structure AvailableChain.Gen.AC.Duty.ACReads ', 'def AvailableChain.Gen.AC.Duty.ACReads ', 1)),
        ('shallow-digest-change', shallow_added.replace('a5157729fa91592f', 'a5157729fa91592e', 1)),
        ('shallow-metadata-change', shallow_added.replace('Policy: 2026-10-09', 'Policy: 2026-10-10')),
        ('shallow-wrong-count', shallow_added.replace('Entries: 853;', 'Entries: 854;')),
        ('shallow-duplicate', shallow_added.replace(f'def {name} ', 'def AvailableChain.Gen.AC.Duty.ACReads ')),
        ('shallow-unknown-markdown', shallow_added + '\nUnclassified policy text.\n'),
    ):
        candidate(label, {'docs/internal/GEN-API.md': content})
    candidate('fgsa-library-change', {'docs/internal/FGSA-API.md': fgsa_added.replace(
        '## `AvailableChainFGSA`', '## `AvailableChainFGSARun`', 1)})
    for label, edits in (
        ('declaration-removal', {'AvailableChainGeneric/Keep.lean': 'module\npublic section\n'}),
        ('replaced-file', {'AvailableChainGeneric/Keep.lean': 'module\n'}),
        ('facade-import-removal', {'AvailableChainGeneric.lean': 'module\n'}),
        ('existing-body-change', {'AvailableChainGeneric/Keep.lean':
            files['AvailableChainGeneric/Keep.lean'].replace(':= 1', ':= 2')}),
        ('ambiguous-edit', {'AvailableChainGeneric/Keep.lean':
            files['AvailableChainGeneric/Keep.lean'] + 'set_option maxRecDepth 0\n'}),
        ('body-insertion', {'AvailableChainGeneric/Extract.lean':
            files['AvailableChainGeneric/Extract.lean'].replace('end Old', '  + 2\nend Old')}),
        ('scope-removal-existing-file', {'AvailableChainGeneric/Extract.lean':
            files['AvailableChainGeneric/Extract.lean'].replace('namespace Old\n', '').replace('end Old\n', '')}),
        ('checker-logic', {'scripts/check-fgsa-claims.sh': ast_added.replace('workers = audit_workers()', 'workers = 1')}),
        ('parser', {'scripts/new-parser.py': 'print("unsafe")\n'}),
        ('control-fixture', {'AvailableChainFGSA/Tests/Control.lean': 'module\n-- changed\n'}),
        ('toolchain', {'lean-toolchain': 'changed\n'}),
        ('dependency', {'lake-manifest.json': '{"dependency": 1}\n'}),
        ('lakefile', {'lakefile.toml': 'name = "changed"\n'}),
        ('scope-removal', {'AvailableChainFGSAProofs/Proofs/Shared/Keep.lean': None}),
        ('scope-switch', {'scripts/unported-libraries.txt': ''}),
        ('inventory-removal', {'scripts/fgsa-claims-expected.txt': "('New.name',)\n"}),
        ('map-change', {'scripts/claims-model-scope.txt': 'AvailableChainFGSA.Model.Objects New.name\n'}),
        ('snapshot-change', {'docs/internal/api/compose-api.json':
                              json.dumps(dict(added, entries={'old': {}, 'new': {}}))}),
        ('snapshot-removal', {'docs/internal/api/compose-api.json':
                              json.dumps(dict(added, entries={'new': {}}))}),
        ('snapshot-pins', {'docs/internal/api/compose-api.json':
                              json.dumps(dict(added, pins={'toolchain': 'changed'}))}),
        ('snapshot-duplicates', {'docs/internal/api/compose-api.json':
                                 '{"entries": {}, "entries": {}}'}),
        ('unknown-data', {'scripts/new-data.txt': 'New.name\n'}),
        ('unknown-checker-markdown', {'docs/internal/V2-API.md': '# Arbitrary Markdown\n'}),
        ('baseline-growth', {'scripts/baselines/check-layers.txt': 'old finding\nnew finding\n'}),
        ('allow-growth', {'scripts/gly-f13-allow.txt': 'Old.exemption\nNew.exemption\n'}),
        ('exclusion-growth', {'scripts/new-exclusions.txt': 'New.module\n'}),
        ('wildcard', {'scripts/claims-model-scope.txt': files['scripts/claims-model-scope.txt'] + 'AvailableChainFGSA.Model.* New.name\n'}),
        ('constant-expression', {'scripts/check-fgsa-claims.sh': claims.replace("ORDER = ('Recurrence',", "ORDER = (str('NewLane'), 'Recurrence',")}),
        ('constant-removal', {'scripts/check-fgsa-claims.sh': claims.replace("ORDER = ('Recurrence',", "ORDER = ('NewLane',")}),
        ('unknown-constant', {'scripts/check-fgsa-claims.sh': ast_added.replace("'Classical.choice'", "'New.permission'") + '\n# outside heredoc\n'}),
    ):
        candidate(label, edits)
    reviewed = candidate('reviewed-allow', {'scripts/gly-f13-allow.txt': 'Old.exemption\nNew.exemption\n'},
                         reviewed=['scripts/gly-f13-allow.txt'], eligible=True)
    candidate('reviewed-baseline', {'scripts/baselines/check-layers.txt': 'old finding\nnew finding\n'},
              reviewed=['scripts/baselines/check-layers.txt'], eligible=True)
    candidate('review-does-not-permit-logic', {'scripts/fixture.py': 'value = 2\n'}, reviewed=['scripts/fixture.py'])
    candidate('review-does-not-permit-allow-code', {'scripts/new-allow.py': 'print("unsafe")\n'}, reviewed=['scripts/new-allow.py'])
    candidate('review-does-not-permit-removal', {'scripts/gly-f13-allow.txt': 'New.exemption\n'}, reviewed=['scripts/gly-f13-allow.txt'])
    for label, operation in (
        ('dirty', lambda: write(eligible, 'scripts/untracked.py', 'pass\n')),
        ('main', lambda: subprocess.run(['git', 'branch', '-M', 'main'], cwd=reviewed, check=True)),
    ):
        operation()
        try:
            select(eligible if label == 'dirty' else reviewed, base)
        except ValueError:
            print(f'CONTROL integration {label}: REFUSED')
        else:
            raise AssertionError(label)
    receipt = importlib.import_module('full-pass')
    logs = Path(scratch) / 'logs'
    logs.mkdir()
    (logs / 'integration.json').write_text('{}')
    try:
        receipt.sign(seed, base, base, logs, seed / 'key', logs / 'full-pass.json')
    except ValueError as error:
        assert 'provisional integration' in str(error), error
    else:
        raise AssertionError('integration logs signed')
    try:
        receipt.verify(seed, seed, logs / 'integration.json')
    except ValueError:
        pass
    else:
        raise AssertionError('provisional result accepted as FULL receipt')
    assert not (logs / 'full-pass.json').exists()
    print('CONTROL integration cannot sign or verify a FULL receipt: PASS')

    # Exercise real G0 module selection and recording with a fake build function.
    g0 = Path(scratch) / 'g0'
    shutil.copytree(seed, g0)
    write(g0, 'AvailableChainFGSAProofs/Tests/Positive.lean', 'module\n')
    write(g0, 'AvailableChainFGSAProofs/Tests/Negative.lean', 'module\n')
    write(g0, 'AvailableChainPCSA/Tests/Unported.lean', 'module\n')
    with (g0 / 'lakefile.toml').open('a') as config:
        config.write('[[lean_lib]]\nname="AvailableChainPCSA"\n')
    write(g0, 'scripts/gate-common.sh',
          'gate_with_slot() { "$@"; }\n'
          'gate_build() { printf "%s\\n" "$@" > g0-calls; return "${G0_RC:-0}"; }\n')
    commit(g0)
    for rc in (0, 7):
        result = subprocess.run(['python3', '-B', str(REPO / 'scripts/integration_g0.py')],
            cwd=g0, env=dict(os.environ, GATE_NO_BUILD='1', GATE_LOG_DIR=str(logs), G0_RC=str(rc)))
        assert result.returncode == rc, result
        record = json.loads((logs / 'package-g0.json').read_text())
        modules = {row['module'] for row in record['results']}
        assert modules == {'AvailableChainFGSA.Tests.Control',
                           'AvailableChainFGSAProofs.Tests.Positive',
                           'AvailableChainFGSAProofs.Tests.Negative'}, modules
        assert all(row['rc'] == rc for row in record['results'])
        assert (g0 / 'g0-calls').read_text().startswith('--wfail\n')
    print('CONTROL package G0: positive/negative module coverage and failed freshness: PASS')
    # Move a fixture using the real configuration's srcDirs, preserving every module identity.
    def nested_tree(root):
        before = Layout(root)
        paths = before.source_files()
        config = (root / 'lakefile.toml').read_text()
        current = Layout(REPO)
        for library in before.declarations():
            name = library['name']
            src = str(Path(current.source_dir(name)).parent)
            config = config.replace('name="' + name + '"\n',
                                    'name="' + name + '"\nsrcDir="' + src + '"\n')
        (root / 'lakefile.toml').write_text(config)
        after = Layout(root)
        for path in paths:
            target = root / after.source_path(before.module_of_source(path))
            target.parent.mkdir(parents=True, exist_ok=True)
            (root / path).rename(target)
        after.check()
        return after

    nested_tree(g0)
    commit(g0)
    result = subprocess.run(['python3', '-B', str(REPO / 'scripts/integration_g0.py')],
        cwd=g0, env=dict(os.environ, GATE_NO_BUILD='1', GATE_LOG_DIR=str(logs), G0_RC='0'))
    assert result.returncode == 0
    nested_record = json.loads((logs / 'package-g0.json').read_text())
    assert {row['module'] for row in nested_record['results']} == modules
    assert not any('PCSA' in row['module'] for row in nested_record['results'])
    print('CONTROL nested package G0: same module identities; declared PC tests excluded: PASS')

    nested_tree(seed)
    base = commit(seed)
    layout = Layout(seed)
    source = layout.source_path('AvailableChainGeneric.Extract')
    target = layout.source_path('AvailableChainGeneric.Extracted')
    before = (seed / source).read_text()
    candidate('nested-reviewed-extraction', {
        source: before.partition('public section\n')[0] +
                'public import AvailableChainGeneric.Extracted\n', target: before},
        eligible=True, extractions=[source + ':' + target])
    candidate('nested-source-addition', {
        layout.source_path('AvailableChainGeneric.Keep'):
        (seed / layout.source_path('AvailableChainGeneric.Keep')).read_text() +
        'def Old.more := 2\n'}, eligible=True)
    candidate('stale-flat-source', {
        'AvailableChainFGSAProofs/Proofs/Shared/Extra.lean': 'module\n'})

print('gate-integration-selftest: PASS')
