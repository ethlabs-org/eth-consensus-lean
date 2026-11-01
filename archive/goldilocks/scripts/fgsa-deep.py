#!/usr/bin/env python3
"""Check/write a current kernel dependency snapshot; report named root attribution.

V2Manifest supplies independently discovered compiled roots. --check is read-only.
--attribute compares two graph files for dry-run measurement. --roots accepts a
name list, P24 TSV, or JSON list. Attribution never grants a snapshot exception.
"""
import argparse
from collections import deque
import csv
import hashlib
import json
from pathlib import Path
import re
import sys

DEEP = Path('docs/internal/api/fgsa-deep.json')
MANIFEST = Path('docs/internal/FGSA-API.md')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f'DUPLICATE JSON KEY {path}: {key}')
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=pairs)


def manifest(path):
    result, module = {}, None
    for line in path.read_text().splitlines():
        heading = re.fullmatch(r'### `([^`]+)`', line)
        if heading:
            module = heading[1]
        entry = re.fullmatch(r'([a-z]+) (\S+) ([0-9a-f]{16})', line)
        if entry:
            if entry[2] in result or module is None:
                raise ValueError(f'INVALID MANIFEST ENTRY {entry[2]}')
            result[entry[2]] = dict(kind=entry[1], module=module, digest=entry[3])
    if not result:
        raise ValueError(f'EMPTY MANIFEST {path}')
    return result


def pins():
    return dict(toolchain=Path('lean-toolchain').read_text().strip(),
                package_pins_sha256=sha(Path('lake-manifest.json').read_bytes()))


def closure(nodes, name):
    seen, stack = set(), [name]
    while stack:
        n = stack.pop()
        if n not in nodes:
            raise ValueError(f'MISSING DEEP DEPENDENCY {n}')
        if n not in seen:
            seen.add(n)
            stack.extend(nodes[n]['dependencies'])
    return seen


def pack(tag, fields):
    return f'{tag}:{len(fields)}:' + ''.join(f'{len(s.encode())}:{s}' for s in fields)


def root_digest(data, name):
    reached = closure(data['nodes'], name)
    parts = [pack('dependency', [data['nodes'][n]['kernel_name'], data['nodes'][n]['digest']])
             for n in data['node_order'] if n in reached]
    return sha(pack('fgsa-deep-entry-v1', parts).encode())


def checkpoint_scope(data):
    if 'checkpoint' not in data:
        return None
    scope = data['checkpoint']
    if (not isinstance(scope, dict) or set(scope) != {'name', 'modules'} or
            scope['name'] != 'g-s1' or not isinstance(scope['modules'], list) or
            not scope['modules'] or not all(isinstance(m, str) and
                re.fullmatch(r"[^\W\d][\w'.?!]*", m) for m in scope['modules']) or
            len(scope['modules']) != len(set(scope['modules']))):
        raise ValueError('INVALID CHECKPOINT SCOPE')
    return scope


def validate_graph(data):
    checkpoint_scope(data)
    if (type(data['format_version']) is not int or data['format_version'] != 2 or
            not isinstance(data['entries'], dict) or
            not data['entries'] or not isinstance(data['nodes'], dict) or not data['nodes']):
        raise ValueError('INVALID DEEP SNAPSHOT')
    nodes = data['nodes']
    order = data['node_order']
    if (not isinstance(order, list) or not all(isinstance(n, str) for n in order) or
            len(order) != len(set(order)) or set(order) != set(nodes)):
        raise ValueError('INVALID DEEP NODE ORDER')
    for name, row in nodes.items():
        if set(row) != {'digest', 'kernel_name', 'module', 'kind', 'type', 'body', 'dependencies'}:
            raise ValueError(f'INVALID DEEP NODE {name}')
        if not re.fullmatch('[0-9a-f]{64}', row['digest']):
            raise ValueError(f'INVALID NODE DIGEST {name}')
        if not all(isinstance(row[k], str) for k in ('module', 'kind', 'kernel_name')):
            raise ValueError(f'INVALID NODE METADATA {name}')
        for k in ('type', 'body'):
            if not isinstance(row[k], list) or not all(isinstance(s, str) for s in row[k]):
                raise ValueError(f'INVALID READABLE NODE {name}')
        ds = row['dependencies']
        if (not isinstance(ds, list) or not all(isinstance(d, str) for d in ds) or
                len(ds) != len(set(ds))):
            raise ValueError(f'INVALID NODE DEPENDENCIES {name}')
        if set(ds) - set(nodes):
            raise ValueError(f'MISSING DEEP DEPENDENCY {name}')
    reached = set()
    for name, row in data['entries'].items():
        if (set(row) != {'digest', 'module', 'kind'} or name not in nodes or
                not re.fullmatch('[0-9a-f]{64}', row['digest'])):
            raise ValueError(f'INVALID ROOT {name}')
        if any(row[k] != nodes[name][k] for k in ('module', 'kind')):
            raise ValueError(f'ROOT METADATA MISMATCH {name}')
        actual = closure(nodes, name)
        if row['digest'] != root_digest(data, name):
            raise ValueError(f'INCOMPLETE ROOT DIGEST {name}')
        reached.update(actual)
    if reached != set(nodes):
        raise ValueError('UNREACHABLE DEEP NODES')


def canonical(data):
    # Stable names and sorted edges avoid unrelated changes after an insertion.
    data = json.loads(json.dumps(data))
    for section in ('nodes',):
        for row in data[section].values():
            row['dependencies'] = sorted(row['dependencies'])
    return data


def render(data):
    return json.dumps(canonical(data), indent=2, sort_keys=True, ensure_ascii=False) + '\n'


def bind_manifest(data, current):
    if set(data['entries']) != set(current):
        raise ValueError('DEEP ROOTS DIFFER FROM COMPLETE CURRENT MANIFEST')
    for name, row in data['entries'].items():
        if any(row[k] != current[name][k] for k in ('kind', 'module')):
            raise ValueError(f'DEEP MANIFEST METADATA MISMATCH {name}')


def read_baseline(path):
    data = strict_json(path)
    validate_graph(data)
    if data.get('pins') != pins():
        raise ValueError(f'SNAPSHOT PIN MISMATCH {path}')
    return data


def paths_from(nodes, start):
    if start not in nodes:
        return {}
    queue, parents = deque([start]), {start: None}
    while queue:
        name = queue.popleft()
        for dep in sorted(nodes[name]['dependencies']):
            if dep not in parents:
                parents[dep] = name
                queue.append(dep)
    return parents


def witness(parents, end):
    if end not in parents:
        return None
    path = []
    while end is not None:
        path.append(end)
        end = parents[end]
    return list(reversed(path))


def path_to(nodes, start, end):
    return witness(paths_from(nodes, start), end)


def root_list(path):
    raw = path.read_text()
    if path.suffix == '.tsv':
        rows = list(csv.DictReader(raw.splitlines(), delimiter='\t'))
    elif path.suffix == '.json':
        rows = strict_json(path)
        if isinstance(rows, dict):
            rows = rows['roots']
        rows = [dict(name=r) if isinstance(r, str) else r for r in rows]
    else:
        rows = [dict(name=line.strip()) for line in raw.splitlines()
                if line.strip() and not line.lstrip().startswith('#')]
    names = [r['name'] for r in rows]
    if not names or len(names) != len(set(names)) or any(
            not isinstance(n, str) or not re.fullmatch(r"[^\W\d][\w'.?!]*", n) for n in names):
        raise ValueError('INVALID ROOT LIST: empty or duplicate names')
    return rows


def root_diagnostics(old, now, roots, checkpoint='baseline'):
    # Only the collector passes None: it has no accepted reference to validate.
    diagnostics = []
    scope = now.get('checkpoint', {})
    modules = scope.get('modules') if scope.get('name') == 'g-s1' else None
    for root in roots:
        name = root['name']
        status = root.get('status', 'existing')
        present = [(side, data['nodes'][name]['module'])
                   for side, data in [('base', old), ('target', now)]
                   if data is not None and name in data['nodes']]
        reason, state = None, 'error'
        if status not in ('existing', 'planned'):
            reason = 'unknown root status'
        elif (checkpoint == 'g-s1' or modules is not None) and (
                not isinstance(root.get('module'), str) or
                not re.fullmatch(r"[^\W\d][\w'.?!]*", root['module'])):
            reason = 'G-S1 subjects require exact module identities'
        elif root.get('module') and any(m != root['module'] for _, m in present):
            reason = 'root module mismatch'
        elif old is not None and status == 'existing' and name not in old['nodes']:
            reason = 'required root absent from reference graph'
        elif modules is not None and root.get('module') not in modules:
            if checkpoint in ('g-s2', 'g-s3'):
                reason = 'root outside final checkpoint import scope'
            else:
                reason, state = 'outside checkpoint import scope', 'pending'
        elif name not in now['nodes']:
            if status == 'planned' and checkpoint in ('baseline', 'g-s1'):
                reason, state = 'planned root absent before final measurement', 'pending'
            else:
                reason = 'required root absent from target graph'
        if reason:
            diagnostics.append(dict(name=name, reason=reason, state=state,
                                    status=status, actual=present))
    return diagnostics


def require_roots(report):
    failures = [f'ROOT ERROR {row["name"]}: {row["reason"]}'
                for row in report['unresolved'] if row['state'] == 'error']
    if failures:
        raise ValueError('\n'.join(failures))


def diff_report(old, now, roots=(), checkpoint='baseline'):
    validate_graph(old)
    validate_graph(now)
    old, now = canonical(old), canonical(now)
    sides = [('base', old['nodes']), ('target', now['nodes'])]
    changed_nodes = sorted(n for n in set(old['nodes']) | set(now['nodes'])
                           if old['nodes'].get(n) != now['nodes'].get(n))
    groups = {n: [] for n in changed_nodes}
    root_paths = {(side, root['name']): paths_from(nodes, root['name'])
                  for side, nodes in sides for root in roots}
    entries = []
    for name in sorted(set(old['entries']) | set(now['entries'])):
        before, after = old['entries'].get(name), now['entries'].get(name)
        if before == after:
            continue
        relations, changes = [], []
        entry_paths = {side: paths_from(nodes, name) for side, nodes in sides}
        closure_added = sorted(set(entry_paths['target']) - set(entry_paths['base']))
        closure_removed = sorted(set(entry_paths['base']) - set(entry_paths['target']))
        closure_paths = [dict(name=n, side=side, path=witness(entry_paths[side], n))
                         for side, names in [('base', closure_removed), ('target', closure_added)]
                         for n in names]
        for node in changed_nodes:
            witnesses = []
            for side, nodes in sides:
                path = witness(entry_paths[side], node)
                if path:
                    witnesses.append(dict(side=side, path=path))
                    for root in roots:
                        subject = root['name']
                        root_path = witness(root_paths[side, subject], node)
                        if not root_path:
                            continue
                        entry_path = witness(entry_paths[side], subject)
                        relations.append(dict(root=subject, node=node, side=side,
                            relation='through-root' if entry_path else 'shared-dependency',
                            entry_path=entry_path, node_path=path, root_path=root_path))
            if witnesses:
                changes.append(dict(name=node, paths=witnesses))
                groups[node].append(name)
        entries.append(dict(name=name, membership='added' if before is None else
                            'removed' if after is None else 'changed', old=before, new=after,
                            old_type='\n'.join(old['nodes'].get(name, {}).get('type', [])),
                            new_type='\n'.join(now['nodes'].get(name, {}).get('type', [])),
                            changed_nodes=changes, attribution=relations,
                            closure_added=closure_added, closure_removed=closure_removed,
                            closure_paths=closure_paths))
    unresolved = root_diagnostics(old, now, roots, checkpoint)
    return dict(format_version=1, entries=entries,
                nodes=[dict(name=n, old=old['nodes'].get(n), new=now['nodes'].get(n))
                       for n in changed_nodes], groups=groups, unresolved=unresolved,
                counts=dict(entries=len(entries), nodes=len(changed_nodes), roots=len(roots)))


def check_deep(old, now):
    validate_graph(old)
    validate_graph(now)
    report = diff_report(old, now)
    failures = [f'DEEP CHANGED {row["name"]}: {row["membership"]}' for row in report['entries']]
    if canonical(old) != canonical(now) and not failures:
        failures.append('DEEP SNAPSHOT CHANGED: nodes, pins or metadata')
    return failures


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    modes = ap.add_mutually_exclusive_group(required=True)
    for mode in ('write', 'check', 'attribute'):
        modes.add_argument('--' + mode, action='store_true')
    ap.add_argument('--snapshot', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, default=MANIFEST)
    ap.add_argument('--baseline', type=Path, default=DEEP)
    ap.add_argument('--roots', type=Path)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--checkpoint', choices=('baseline', 'g-s1', 'g-s2', 'g-s3'),
                    default='baseline')
    args = ap.parse_args()
    if args.write and args.roots:
        ap.error('--roots is read-only; use --attribute or --check')
    now = strict_json(args.snapshot)
    validate_graph(now)
    if not args.attribute:
        bind_manifest(now, manifest(args.manifest))
    now['pins'] = pins()
    if args.write:
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        args.baseline.write_text(render(now))
        print(f'{args.baseline}: written; {len(now["entries"])} entries')
        return
    old = read_baseline(args.baseline)
    roots = root_list(args.roots) if args.roots else []
    report = diff_report(old, now, roots, args.checkpoint)
    report['inputs'] = dict(base_sha256=sha(args.baseline.read_bytes()),
                           target_sha256=sha(args.snapshot.read_bytes()),
                           roots_sha256=sha(args.roots.read_bytes()) if args.roots else None)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    if args.roots and args.check:
        print('ROOT ATTRIBUTION: ' + json.dumps(report['counts']))
        for row in report['unresolved']:
            print('UNRESOLVED ROOT: ' + row['name'] + ': ' + row['reason'])
    if args.attribute:
        if not args.output:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        require_roots(report)
        return
    require_roots(report)
    failures = check_deep(old, now)
    if failures:
        raise ValueError('\n'.join(failures))
    print(f'DEEP PASS: {len(now["entries"])} entries; current snapshot matches')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print(f'DEEP SNAPSHOT FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
