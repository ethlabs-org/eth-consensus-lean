#!/usr/bin/env python3
"""Validate changed paths against one fenced ALLOWED_PATHS section in a brief."""
import argparse
from pathlib import Path, PurePosixPath
import re
import subprocess


def allowed_paths(text):
    # Explicit grammar prevents a prose example from widening the scope.
    sections = re.findall(r'(?m)^ALLOWED_PATHS:\s*\n```(?:text)?\n(.*?)\n```', text, re.S)
    if len(sections) != 1 or len(re.findall(r'(?m)^ALLOWED_PATHS:', text)) != 1:
        raise ValueError('brief needs one fenced ALLOWED_PATHS section')
    paths = []
    for raw in sections[0].splitlines():
        path = raw.strip()
        if not path or path.startswith('#'):
            continue
        parts = PurePosixPath(path).parts
        if (path.startswith('/') or '..' in parts or '.' in path.split('/') or
                '\\' in path or any(c in path for c in '*?[]') or
                not parts or parts[0] in ('.git', '.lake')):
            raise ValueError(f'invalid ALLOWED_PATHS entry: {path}')
        paths.append(path)
    if not paths:
        raise ValueError('ALLOWED_PATHS is empty')
    return paths


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def check(root, base, brief):
    resolved = git(root, 'rev-parse', '--verify', base + '^{commit}').decode().strip()
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', resolved, 'HEAD'],
                   check=True)
    allowed = allowed_paths(brief.read_text())
    changed = set()
    for args in [('diff', '--no-ext-diff', '--no-renames', '--name-only', '-z',
                  resolved + '..HEAD'),
                 ('diff', '--no-ext-diff', '--no-renames', '--name-only', '-z', 'HEAD'),
                 ('ls-files', '--others', '--exclude-standard', '-z')]:
        changed.update(p.decode() for p in git(root, *args).split(b'\0') if p)
    bad = sorted(p for p in changed if not any(
        p == a or (a.endswith('/') and p.startswith(a)) for a in allowed))
    if bad:
        raise ValueError('DIFF SCOPE REFUSED: ' + ', '.join(bad))
    print(f'diff scope: {len(changed)} changed paths within ALLOWED_PATHS')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('base')
    parser.add_argument('brief', type=Path)
    args = parser.parse_args()
    try:
        check(args.root, args.base, args.brief)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(2, f'{error}\n')


if __name__ == '__main__':
    main()
