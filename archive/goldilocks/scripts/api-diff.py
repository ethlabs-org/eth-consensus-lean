#!/usr/bin/env python3
"""Emit a complete base-to-target review from committed current API graphs."""
import argparse
import importlib.util
import json
from pathlib import Path
from source_layout import Layout
import subprocess

spec = importlib.util.spec_from_file_location('deep', 'scripts/fgsa-deep.py')
deep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(deep)


def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()


def combine(graphs):
    result = dict(format_version=2, entries={}, nodes={}, node_order=[])
    scope = deep.checkpoint_scope(graphs[0]) if graphs else None
    if scope is not None:
        result['checkpoint'] = scope
    for data in graphs:
        deep.validate_graph(data)
        if deep.checkpoint_scope(data) != scope:
            raise ValueError('INCONSISTENT SNAPSHOT CHECKPOINT SCOPE')
        result['node_order'] += [n for n in data['node_order']
                                 if n not in result['node_order']]
        for section in ('entries', 'nodes'):
            for name, row in data[section].items():
                if name in result[section] and result[section][name] != row:
                    raise ValueError('CONFLICTING SNAPSHOT NODE/ROOT: ' + name)
                result[section][name] = row
    # Each compiler graph has the same Name.lt ordering. Merge these order
    # constraints so every root keeps the exact order of its own closure.
    from graphlib import TopologicalSorter
    graph = TopologicalSorter()
    for data in graphs:
        previous = None
        for name in data['node_order']:
            graph.add(name, *([previous] if previous is not None else []))
            previous = name
    graph.prepare()
    result['node_order'] = []
    while graph.is_active():
        ready = sorted(graph.get_ready())
        result['node_order'].extend(ready)
        graph.done(*ready)
    deep.validate_graph(result)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', required=True, help='exact snapshot base commit')
    ap.add_argument('--target', default='HEAD')
    snapshots = ap.add_mutually_exclusive_group()
    snapshots.add_argument('--snapshots', nargs='+', help='exact physical paths at both revisions')
    snapshots.add_argument('--logical-snapshots', nargs='+',
                           help='archive paths resolved independently at each revision')
    ap.add_argument('--roots', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--checkpoint', choices=('baseline', 'g-s1', 'g-s2', 'g-s3'),
                    default='baseline')
    args = ap.parse_args()
    commits = [git('rev-parse', ref + '^{commit}') for ref in (args.base, args.target)]
    graphs, inputs = [], []
    for commit in commits:
        side = []
        for logical in args.snapshots or args.logical_snapshots or ['docs/api/fgsa-deep.json']:
            path = (Layout(Path.cwd(), commit).archive_doc_path(logical)
                    if args.snapshots is None else logical)
            raw = subprocess.check_output(['git', 'show', commit + ':' + path])
            # Use the same duplicate-key parser for Git object inputs.
            import tempfile
            with tempfile.TemporaryDirectory(prefix='api-diff-') as tmp:
                source = Path(tmp) / 'snapshot.json'
                source.write_bytes(raw)
                side.append(deep.strict_json(source))
            inputs.append(dict(commit=commit, path=path, sha256=deep.sha(raw)))
        graphs.append(combine(side))
    roots = deep.root_list(args.roots) if args.roots else []
    report = deep.diff_report(*graphs, roots, checkpoint=args.checkpoint)
    report['source'] = dict(base=commits[0], target=commits[1],
                          target_tree=git('rev-parse', commits[1] + '^{tree}'), inputs=inputs,
                          roots_sha256=deep.sha(args.roots.read_bytes()) if args.roots else None)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    lines = [f'Base: {commits[0]}', f'Target: {commits[1]}',
             f'Changed roots: {report["counts"]["entries"]}',
             f'Changed nodes: {report["counts"]["nodes"]}']
    for row in report['entries']:
        lines += ['', row['membership'] + ' ' + row['name'],
                  'Old statement:', row['old_type'] or '<absent>',
                  'New statement:', row['new_type'] or '<absent>']
        for side in ('old', 'new'):
            entry = row[side]
            lines.append(side + ': ' + (json.dumps(entry, ensure_ascii=False)
                                       if entry else '<absent>'))
        for node in row['changed_nodes']:
            lines.append('Dependency: ' + node['name'])
            lines.extend(p['side'] + ': ' + ' -> '.join(p['path']) for p in node['paths'])
        lines.append('Closure additions: ' + ', '.join(row['closure_added']))
        lines.append('Closure removals: ' + ', '.join(row['closure_removed']))
        lines.extend(p['side'] + ' closure: ' + ' -> '.join(p['path'])
                     for p in row['closure_paths'])
    for row in report['nodes']:
        lines += ['', 'Node: ' + row['name'], 'Old type:',
                  '\n'.join((row['old'] or {}).get('type', ['<absent>'])), 'New type:',
                  '\n'.join((row['new'] or {}).get('type', ['<absent>'])), 'Old body:',
                  '\n'.join((row['old'] or {}).get('body', ['<absent>'])), 'New body:',
                  '\n'.join((row['new'] or {}).get('body', ['<absent>']))]
    lines += ['', 'Unresolved: ' + json.dumps(report['unresolved'], ensure_ascii=False)]
    args.output.with_suffix('.md').write_text('\n'.join(lines) + '\n')
    print(json.dumps(report['counts']))
    deep.require_roots(report)


if __name__ == '__main__':
    main()
