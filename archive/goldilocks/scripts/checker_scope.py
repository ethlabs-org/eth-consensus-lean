#!/usr/bin/env python3
"""Select controls from BASE..HEAD using the single checker path set."""
import argparse
from fnmatch import fnmatchcase
import json
from pathlib import Path
from source_layout import Layout
import subprocess


def matched_paths(root, base, head):
    lines = (root / 'scripts/checker-paths.txt').read_text().splitlines()
    patterns = [line.strip() for line in lines
                if line.strip() and not line.lstrip().startswith('#')]
    if not patterns:
        raise ValueError('empty checker path set')
    layouts = [Layout(root, revision) for revision in (base, head)]
    patterns = sorted(set(patterns) | {layout.expand_checker_pattern(p)
                                      for layout in layouts for p in patterns})
    result = subprocess.check_output(['git', '-C', str(root), 'diff', '--no-ext-diff',
                                      '--no-renames', '--name-only', '-z', f'{base}..{head}'])
    paths = result.decode('utf-8', errors='surrogateescape').split('\0')
    return sorted({p for p in paths if p and any(fnmatchcase(p, glob) for glob in patterns)})


def resolve(root, rev):
    return subprocess.check_output(['git', '-C', str(root), 'rev-parse', '--verify',
                                    f'{rev}^{{commit}}'], text=True).strip()


def select(root, base, head, force=False):
    # An empty range is no evidence that no checker changed (base = HEAD on main).
    if not force and resolve(root, base) == resolve(root, head):
        return dict(neg=1, reason='empty range', matched_paths=[])
    paths = matched_paths(root, base, head)
    reason = ('override' if force else 'checker paths changed' if paths
              else 'no checker path changed')
    return dict(neg=int(force or bool(paths)), reason=reason, matched_paths=paths)


def validate(root, base, head, scope):
    if not isinstance(scope, dict) or set(scope) != {'neg', 'reason', 'matched_paths'}:
        raise ValueError('FULL RECEIPT INVALID CONTROL SCOPE')
    if type(scope['neg']) is not int or scope['neg'] not in (0, 1):
        raise ValueError('FULL RECEIPT INVALID NEG')
    expected = select(root, base, head, force=scope['reason'] == 'override')
    if scope != expected:
        raise ValueError('FULL RECEIPT CONTROL SCOPE DIFFERS FROM DIFF')
    return scope


def summary(scope):
    print(f'negative controls: NEG={scope["neg"]} ({scope["reason"]})')
    for path in scope['matched_paths']:
        print('checker path: ' + json.dumps(path, ensure_ascii=True))
    if not scope['matched_paths']:
        print('checker paths: none')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('base')
    parser.add_argument('head')
    parser.add_argument('--force', action='store_true')
    parser.add_argument('--summary', type=Path)
    args = parser.parse_args()
    if args.summary:
        summary(json.loads(args.summary.read_text()))
    else:
        print(json.dumps(select(args.root, args.base, args.head, args.force), sort_keys=True))
