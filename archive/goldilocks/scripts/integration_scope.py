"""Conservative eligibility for a provisional gate; never main evidence."""
import argparse
import ast
import hashlib
from difflib import SequenceMatcher
import json
from importlib import import_module
from pathlib import Path
from source_layout import Layout
import re
import subprocess
import sys

from checker_scope import matched_paths, resolve

INVENTORIES = {f'scripts/{name}-expected.txt' for name in
               ('fg', 'fgsa', 'fgsa-run', 'fgsa-claims', 'fg-compose')}
SNAPSHOTS = {f'docs/api/{name}.json' for name in
             ('legacy-api', 'compose-api', 'fgsa-deep', 'fgsa-claims-api',
              'gen-deep', 'v2-deep')}
SHALLOW_MANIFESTS = {'docs/GEN-API.md': ('Entries',),
                     'docs/FGSA-API.md': ('AvailableChainFGSA', 'AvailableChainFGSARun',
                                          'AvailableChainFGSAClaims')}
# Only coverage lists can grow. Permission/exemption lists are not in this set.
CONSTANTS = {'scripts/check-fgsa-claims.sh': {'ORDER': 'module_suffix',
                                           'REQUIRED_MODEL_SCOPE': 'model_scope'},
             'scripts/check-fgsa-blueprint.py': {'CLAIMS_STRUCTURES': 'structure_name',
                                               'SAFETY_FIELDS': 'field_label'}}
P0 = ('AvailableChainGeneric', 'AvailableChainFGSA', 'AvailableChainFGSARun',
      'AvailableChainFGSAClaims', 'AvailableChainFGSAProofs',
      'AvailableChainFGSAInhabit', 'AvailableChainFGCompose')
LEAN_NAME = r"[^\W\d][\w'.!?]*"
IMPORT = re.compile(r'(?:public )?import (' + LEAN_NAME + r')\n')
# A deliberately small grammar. Complex declaration edits need the full gate.
SIMPLE_DEF = re.compile(r'def (' + LEAN_NAME + r')(?: : Nat)? := [0-9]+\n')


def production_source(path, layout):
    if not path.endswith('.lean'):
        return False
    try:
        module = layout.module_of_source(path)
    except ValueError:
        return False
    return (any(module == p or module.startswith(p + '.') for p in P0) and
            not re.search(r'Check|Control', path) and '.Tests.' not in module)


def source_additions(before, after):
    old, new = before.splitlines(keepends=True), after.splitlines(keepends=True)
    if not old or old[0] != 'module\n':
        raise ValueError('unclassified source header')
    header = 1
    while header < len(old) and (old[header] == '\n' or IMPORT.fullmatch(old[header])):
        header += 1
    simple = all(line in ('module\n', '\n', 'public section\n') or
                 IMPORT.fullmatch(line) or SIMPLE_DEF.fullmatch(line) for line in old)
    names = {m[1] for line in old if (m := SIMPLE_DEF.fullmatch(line))}
    imports = {m[1] for line in old[:header] if (m := IMPORT.fullmatch(line))}
    count = 0
    for tag, i, j, k, l in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag not in ('equal', 'insert'):
            raise ValueError('source declaration, import, or scope removed or changed')
        if tag == 'insert':
            for line in new[k:l]:
                if 1 <= i <= header and (m := IMPORT.fullmatch(line)) and m[1] not in imports:
                    imports.add(m[1])
                elif simple and i == len(old) and (m := SIMPLE_DEF.fullmatch(line)) and m[1] not in names:
                    names.add(m[1])
                else:
                    raise ValueError('unclassified source addition')
                count += 1
    if not count:
        raise ValueError('no classified source additions')
    return count


def reviewed_extractions(root, base, head, pairs, paths):
    records = {}
    layouts = [Layout(root, rev) for rev in (base, head)]
    targets = set()
    for pair in pairs:
        parts = pair.split(':')
        if len(parts) != 2:
            raise ValueError('--reviewed-extraction requires exact SOURCE:TARGET paths')
        source, target = parts
        if (source == target or source in records or target in targets or
                any(p not in paths or not production_source(p, layouts[i]) or
                    any(c in p for c in '*?[]') for i, p in enumerate(parts))):
            raise ValueError('invalid or duplicate reviewed extraction paths')
        if git(root, 'ls-tree', base, '--', target).strip():
            raise ValueError('extraction target must be a new module')
        before = git(root, 'show', base + ':' + source).decode()
        after = git(root, 'show', head + ':' + source).decode()
        moved = git(root, 'show', head + ':' + target).decode()
        header, marker, body = before.partition('public section\n')
        module = layouts[1].module_of_source(target)
        exact_names([module])
        if (not marker or not body.strip() or not header.startswith('module\n') or
                any(line not in ('module\n', '\n') and not IMPORT.fullmatch(line)
                    for line in header.splitlines(keepends=True)) or
                moved != before or after != header + 'public import ' + module + '\n'):
            raise ValueError('extraction must preserve the complete old source in the new module and all facade imports')
        records[source] = dict(source=source, target=target, base=base, head=head,
            before_sha256=hashlib.sha256(before.encode()).hexdigest(),
            after_sha256=hashlib.sha256(after.encode()).hexdigest(),
            target_sha256=hashlib.sha256(moved.encode()).hexdigest())
        targets.add(target)
    if targets & records.keys():
        raise ValueError('overlapping reviewed extractions')
    return records


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def ordered_additions(before, after):
    if len(after) != len(set(after)) or len(before) >= len(after):
        raise ValueError('needs distinct additions')
    remaining = iter(after)
    if not all(any(old == new for new in remaining) for old in before):
        raise ValueError('old entry removed, changed, or reordered')


def added_lines(before, after):
    old, new = before.splitlines(), after.splitlines()
    additions = []
    for tag, i, j, k, l in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag not in ('equal', 'insert'):
            raise ValueError('old line removed or changed')
        if tag == 'insert':
            additions.extend(new[k:l])
    if not additions:
        raise ValueError('no added lines')
    return additions


def exact_names(values):
    # ? and ! are literal Lean identifier characters in inventories, not glob
    # permissions. These lists are parsed and compared as exact strings.
    if not all(isinstance(x, str) and re.fullmatch(r"[^\W\d][\w'.!?]*", x)
               for x in values):
        raise ValueError('entries must be exact names without wildcards')


def constant_literals(values, schema):
    identifier = r'[A-Za-z_][A-Za-z0-9_]*'
    dotted = identifier + r'(?:\.' + identifier + r')*'
    if schema == 'model_scope':
        for pair in values:
            if (not isinstance(pair, tuple) or len(pair) != 2 or
                    not all(isinstance(x, str) and re.fullmatch(dotted, x) for x in pair) or
                    not pair[0].startswith('AvailableChainFGSA.Model.')):
                raise ValueError('scope entry must be an exact model owner/name pair')
    else:
        pattern = {'module_suffix': dotted, 'structure_name': identifier,
                   'field_label': identifier + r'(?: ' + identifier + r')*'}[schema]
        if not all(isinstance(x, str) and re.fullmatch(pattern, x) for x in values):
            raise ValueError('invalid exact ' + schema + ' literal; wildcards are refused')


def constant_additions(before, after, names, shell=False):
    if shell:
        marker = "<<'PY'\n"
        a, before = before.split(marker, 1)
        b, after = after.split(marker, 1)
        before, c = before.rsplit('\nPY', 1)
        after, d = after.rsplit('\nPY', 1)
        if (a, c) != (b, d):
            raise ValueError('shell logic changed')
    old, new = ast.parse(before), ast.parse(after)
    changed = []
    for name in sorted(names):
        def assignment(tree):
            nodes = [n for n in tree.body if isinstance(n, ast.Assign) and
                     len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and
                     n.targets[0].id == name]
            if len(nodes) != 1:
                raise ValueError('missing or ambiguous constant: ' + name)
            return nodes[0]
        x, y = assignment(old), assignment(new)
        if ast.dump(x) == ast.dump(y):
            continue
        schema = names[name]
        expected = ast.Set if schema == 'model_scope' else ast.Tuple
        if not isinstance(x.value, expected) or not isinstance(y.value, expected):
            raise ValueError('constant is not a literal list: ' + name)
        first, last = [ast.literal_eval(n) for n in (x.value, y.value)]
        constant_literals(last, schema)
        if isinstance(first, set):
            if not first < last or len(x.value.elts) != len(first) or len(y.value.elts) != len(last):
                raise ValueError('set is not a distinct strict superset: ' + name)
        else:
            ordered_additions(first, last)
        x.value = y.value = ast.Constant(value=None)
        changed.append(name)
    if not changed or ast.dump(old) != ast.dump(new):
        raise ValueError('checker logic or an unapproved constant changed')
    return changed


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def snapshot_additions(before, after):
    old, new = [json.loads(x, object_pairs_hook=unique_object) for x in (before, after)]
    if not isinstance(old, dict) or not isinstance(new, dict) or set(old) != set(new):
        raise ValueError('snapshot schema changed')
    count = 0
    for field in old:
        a, b = old[field], new[field]
        if field in ('entries', 'nodes'):
            if not isinstance(a, dict) or not isinstance(b, dict) or any(
                    key not in b or b[key] != value for key, value in a.items()):
                raise ValueError('old snapshot entry removed or changed: ' + field)
            count += len(b) - len(a)
        elif field == 'node_order' and a != b:
            ordered_additions(a, b)
        elif a != b:
            raise ValueError('snapshot metadata changed: ' + field)
    if count <= 0:
        raise ValueError('no snapshot entries added')
    return count


def shallow_manifest(text, path):
    header, separator, body = text.partition('\n## ')
    counts = re.findall(r'^Entries: ([0-9]+); modules: ([0-9]+)\.$', header, re.M)
    if not separator or len(counts) != 1:
        raise ValueError('invalid shallow manifest header')
    metadata = re.sub(r'^Entries: [0-9]+; modules: [0-9]+\.$',
                      'Entries: <count>; modules: <count>.', header, flags=re.M)
    body = '## ' + body
    groups, modules, entries = [], {}, {}
    group = None
    while body:
        heading = re.match(r'## (Entries|`([^`]+)`)\n\n', body)
        if heading:
            group = heading[2] or heading[1]
            if group not in SHALLOW_MANIFESTS[path] or group in groups:
                raise ValueError('unknown or duplicate manifest library')
            groups.append(group)
            body = body[heading.end():]
        block = re.match(r'### `([^`]+)`\n\n```text\n([^`]*)```(?:\n\n|\n$)', body)
        if not group or not block:
            raise ValueError('unclassified shallow manifest content')
        owner, rows = block[1], block[2].splitlines()
        exact_names([owner])
        if (owner in modules or
                (path == 'docs/GEN-API.md' and not owner.startswith('AvailableChainGeneric.Statements.')) or
                (path == 'docs/FGSA-API.md' and not owner.startswith(group + '.'))):
            raise ValueError('invalid or duplicate manifest owner')
        modules[owner] = []
        for row in rows:
            entry = re.fullmatch(r'(axiom|def|theorem|opaque|quot|structure|inductive|ctor|rec|field) '
                                 r'(\S+) ([0-9a-f]{1,16})', row)
            if not entry or entry[2] in entries:
                raise ValueError('invalid or duplicate manifest declaration')
            kind, name, digest = entry.groups()
            exact_names([name])
            entries[name] = (group, owner, kind, digest)
            modules[owner].append(name)
        body = body[block.end():]
    if tuple(map(int, counts[0])) != (len(entries), len(modules)):
        raise ValueError('shallow manifest counts do not match content')
    return metadata, groups, modules, entries


def shallow_additions(before, after, path):
    a, b = [shallow_manifest(text, path) for text in (before, after)]
    if a[0] != b[0]:
        raise ValueError('shallow manifest metadata changed')
    for first, last in ((a[1], b[1]), (list(a[2]), list(b[2]))):
        if first != last:
            ordered_additions(first, last)
    for owner, names in a[2].items():
        if owner not in b[2]:
            raise ValueError('old shallow manifest owner removed')
        if names != b[2][owner]:
            ordered_additions(names, b[2][owner])
    if any(b[3].get(name) != value for name, value in a[3].items()):
        raise ValueError('old shallow declaration, owner, kind, or digest changed')
    count = len(b[3]) - len(a[3])
    if count <= 0:
        raise ValueError('no shallow manifest declarations added')
    return count


def policy_file(path):
    return (path.startswith('scripts/baselines/') or
            bool(re.search(r'(?:allow|exclu|wildcard)', path, re.I)))


def deferred_controls(root):
    # These are the precise NEG-controlled drivers/blocks. Package Tests are
    # built and checked separately; none of their results are deferred.
    selectors = ['gate.sh: checker-self-tests (check-build.sh --selftests-only)',
            'check-fgsa-claims.sh: NEG-selected source and compiled fixture controls',
            'check-fg-compose.sh: check-fg-compose-controls.py',
            'check-fgsa-manifest.sh: api-snapshot-controls.py',
            'check-fgsa-manifest.sh: fgsa-deep-controls.py',
            'check-fgsa-run.sh: NEG-selected source and compiled fixture controls',
            'check-fgsa.sh: NEG-selected fixture controls and CheckFGSAOldReads --controls']
    records = []
    for selector in selectors:
        driver = selector.split(':', 1)[0]
        text = (root / 'scripts' / driver).read_text()
        # The source hash and line numbers identify the exact deferred dispatch.
        lines = [i for i, line in enumerate(text.splitlines(), 1)
                 if 'NEG' in line and not line.lstrip().startswith('#')]
        records.append(dict(selector=selector, driver=driver,
                            neg_dispatch_lines=lines,
                            driver_sha256=hashlib.sha256(text.encode()).hexdigest()))
    return records


def select(root, base, head='HEAD', reviewed=(), extractions=()):
    base, head = resolve(root, base), resolve(root, head)
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', base, head], check=True)
    if base == head:
        raise ValueError('empty candidate range')
    branch = git(root, 'symbolic-ref', '--quiet', '--short', 'HEAD').decode().strip() \
        if subprocess.run(['git', '-C', str(root), 'symbolic-ref', '--quiet', 'HEAD'],
                          stdout=subprocess.DEVNULL).returncode == 0 else ''
    if branch in ('main', 'master'):
        raise ValueError('integration mode cannot run on main')
    if git(root, 'status', '--porcelain', '--untracked-files=all').strip():
        raise ValueError('candidate must be clean and committed')
    ignored = git(root, 'ls-files', '--others', '--ignored', '--exclude-standard', '--',
                  '*.lean', 'scripts/*', ':(exclude).lake/**').strip()
    if ignored:
        raise ValueError('ignored source or checker file')
    paths = [p for p in git(root, 'diff', '--no-ext-diff', '--no-renames', '--name-only',
                           '-z', base + '..' + head).decode().split('\0') if p]
    matched = matched_paths(root, base, head)
    extraction_records = reviewed_extractions(root, base, head, extractions, paths)
    reviewed = sorted(set(reviewed))
    if any(p not in paths or not p.startswith('scripts/') or not p.endswith('.txt') or not policy_file(p) or
           any(c in p for c in '*?[]') for p in reviewed):
        raise ValueError('--reviewed-allow must name changed, exact policy-data files')
    layouts = [Layout(root, rev) for rev in (base, head)]
    evidence = []
    for path in paths:
        logical = layouts[1].logical_path(path)
        doc = path.replace("docs/internal/", "docs/", 1)
        try:
            old_tree, new_tree = [git(root, 'ls-tree', rev, '--', path).decode().strip()
                                  for rev in (base, head)]
            if not new_tree or new_tree.split()[0] != '100644':
                # Existing executable checker wrappers are allowed only as AST data.
                if not (new_tree and old_tree and new_tree.split()[0] == old_tree.split()[0] ==
                        '100755' and path in CONSTANTS):
                    raise ValueError('scope removal, symlink, executable addition, or mode change')
            if old_tree and old_tree.split()[0] != new_tree.split()[0]:
                raise ValueError('file mode changed')
            before = git(root, 'show', base + ':' + path).decode() if old_tree else ''
            after = git(root, 'show', head + ':' + path).decode()
            if policy_file(path):
                if path not in reviewed:
                    raise ValueError('policy/baseline/allow/exclusion growth requires --reviewed-allow')
                added_lines(before, after)
                reason = 'explicitly reviewed policy additions; all generic controls retained'
            elif path in INVENTORIES:
                from check_inventory import parse_names
                first, last = parse_names(before, path), parse_names(after, path)
                exact_names(last)
                ordered_additions(first, last)
                reason = 'parsed inventory additions'
            elif path == 'scripts/claims-model-scope.txt':
                lines = added_lines(before, after)
                for line in lines:
                    if not line.strip() or line.lstrip().startswith('#'):
                        continue
                    pair = line.split()
                    if len(pair) != 2 or not pair[0].startswith('AvailableChainFGSA.Model.'):
                        raise ValueError('invalid audit owner/name map entry')
                    exact_names(pair)
                reason = 'exact owner/name map additions'
            elif doc in SNAPSHOTS:
                reason = f'structural snapshot additions: {snapshot_additions(before, after)}'
            elif doc in SHALLOW_MANIFESTS:
                count = shallow_additions(before, after, doc)
                reason = f'structural shallow manifest additions: {count}'
            elif path in CONSTANTS:
                reason = 'AST coverage-list additions: ' + ', '.join(constant_additions(
                    before, after, CONSTANTS[path], path.endswith('.sh')))
            elif (path.endswith('.lean') and
                  any(logical == p + '.lean' or logical.startswith(p + '/') for p in P0) and
                  not re.search(r'Check|Control', path) and
                  ('/Tests/' not in path or not old_tree)):
                # A physical folder prefix must not invent a new module or admit a stale flat file.
                layouts[1].module_of_source(path)
                if path in extraction_records:
                    reason = 'explicitly reviewed exact module extraction; source and facade imports preserved'
                elif old_tree:
                    reason = f'classified P0 source additions: {source_additions(before, after)}'
                else:
                    reason = 'new P0 source; complete positive and package G0 checks required'
            elif doc.startswith(('scripts/', 'docs/api/')) or path in matched:
                raise ValueError('checker logic, parser, fixture, toolchain, dependency, or unknown checker data')
            elif path.startswith('docs/') and path.endswith('.md'):
                reason = 'non-checker documentation'
            else:
                raise ValueError('ambiguous change outside P0 source and approved data additions')
            evidence.append(dict(path=path, reason=reason))
        except (ValueError, SyntaxError, TypeError) as error:
            raise ValueError(path + ': ' + str(error)) from None
    return dict(mode='integration', provisional=True, eligible=True, base=base, head=head,
                matched_checker_paths=matched, reviewed_allow=reviewed, evidence=evidence,
                reviewed_extractions=[extraction_records[p] for p in sorted(extraction_records)],
                neg=1 if reviewed else 0,
                deferred_controls=[] if reviewed else deferred_controls(root),
                main_accepted=False, full_receipt=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('base')
    parser.add_argument('--reviewed-allow', action='append', default=[])
    parser.add_argument('--reviewed-extraction', action='append', default=[])
    parser.add_argument('--complete', type=Path)
    args = parser.parse_args()
    try:
        record = select(args.root, args.base, reviewed=args.reviewed_allow,
                        extractions=args.reviewed_extraction)
        if args.complete:
            if json.loads((args.complete / 'integration.json').read_text()) != record:
                raise ValueError('candidate or eligibility changed during the gate')
            required = set(import_module('full-pass').STEPS) | {'package-g0'}
            if record['neg']:
                required.add('checker-self-tests')
            actual = {p.stem for p in args.complete.glob('*.result')}
            if actual != required:
                raise ValueError('incomplete provisional step coverage')
            results = {}
            for step in sorted(required):
                rc, wall = (args.complete / (step + '.result')).read_text().split()
                if rc != '0' or not wall.isdigit():
                    raise ValueError('failed provisional step: ' + step)
                results[step] = dict(rc=0, wall_s=int(wall))
            g0 = json.loads((args.complete / 'package-g0.json').read_text())
            if not g0['results'] or any(row['rc'] != 0 for row in g0['results']):
                raise ValueError('missing or failed package G0 results')
            record.update(result='PROVISIONAL PASS', positive_steps=results, package_g0=g0)
            (args.complete / 'integration-result.json').write_text(json.dumps(record, sort_keys=True) + '\n')
        print(json.dumps(record, sort_keys=True))
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(2, 'INTEGRATION REFUSED: ' + str(error) + '\n')
