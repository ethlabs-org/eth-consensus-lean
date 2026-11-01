#!/usr/bin/env python3
"""One explicit writer/checker for all current API snapshot products."""
import argparse
import subprocess
import unported as U


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    modes = ap.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    ap.add_argument('--scope', action='append',
                    choices=('v2', 'gen', 'fgsa', 'pcsa', 'legacy', 'compose', 'auxiliary'))
    args = ap.parse_args()
    mode = '--write' if args.write else '--check'
    for scope in args.scope or ('v2', 'gen', 'fgsa', 'pcsa', 'legacy', 'compose', 'auxiliary'):
        if scope == 'pcsa' and U.pcsa():
            print('SKIP UNPORTED: PC-SA shallow and deep snapshots', flush=True)
            continue
        if scope in ('legacy', 'compose', 'auxiliary'):
            name = 'fgsa-claims' if scope == 'auxiliary' else scope
            subprocess.run(['python3', '-B', 'scripts/api-snapshot.py', '--scope', name, mode],
                           check=True)
        else:
            cmd = ['lake', 'env', 'lean', '--run', 'scripts/V2Manifest.lean', '--scope', scope]
            if scope != 'pcsa' or mode == '--check':
                subprocess.run(cmd + [mode], check=True)
            # PC-SA's shallow doc is retained on this branch; verify it before deep writes.
            if scope == 'pcsa' and mode == '--write':
                subprocess.run(cmd + ['--check'], check=True)
            if scope in ('v2', 'gen'):
                subprocess.run(['python3', '-B', 'scripts/api-snapshot.py', '--scope', scope,
                    '--output', 'docs/internal/api/' + scope + '-deep.json', mode], check=True)
            if scope in ('fgsa', 'pcsa'):
                subprocess.run(cmd + ['--deep', mode], check=True)


if __name__ == '__main__':
    main()
