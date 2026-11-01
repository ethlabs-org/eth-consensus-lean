#!/usr/bin/env python3
"""Write/check public audit inventories from all compiled source modules."""
import argparse
import importlib.util
from pathlib import Path
import sys
from check_inventory import read_names

spec = importlib.util.spec_from_file_location('snapshot', 'scripts/api-snapshot.py')
snapshot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(snapshot)
SCOPES = ('fg', 'fgsa', 'fgsa-run', 'fgsa-claims', 'compose')


def path_for(scope):
    name = 'fg-compose' if scope == 'compose' else scope
    return Path('scripts/' + name + '-expected.txt')


def compare(expected, actual, scope):
    if set(expected) != set(actual):
        missing = sorted(set(actual) - set(expected))
        stale = sorted(set(expected) - set(actual))
        raise ValueError(f'{scope} INVENTORY DIFF: unlisted={missing}; stale={stale}')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    ap.add_argument('--scope', choices=SCOPES, action='append')
    args = ap.parse_args()
    for scope in args.scope or SCOPES:
        names = snapshot.extract(scope, inventory=True)
        path = path_for(scope)
        if args.write:
            path.write_text('# Generated current public audit inventory. Review every diff.\n(\n' +
                            ''.join('    ' + repr(n) + ',\n' for n in sorted(names)) + ')\n')
        else:
            compare(read_names(path), names, scope)
        print(f'{path}: PASS ({len(names)} public declarations/projections)', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        print(f'INVENTORY FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
