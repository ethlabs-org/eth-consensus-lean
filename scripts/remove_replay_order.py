#!/usr/bin/env python3
"""Remove the unused Goldilocks replay-order parameter from selected Lean sources.

Like rename_sa.py, this is a source migration, not a Lean elaborator. No base commit
is required. Run after merging the order-free definitions; review and build the diff.

  python3 scripts/remove_replay_order.py PATH...          preview unified diffs
  python3 scripts/remove_replay_order.py --write PATH...  apply changes
  python3 scripts/remove_replay_order.py --check PATH...  exit 1 if changes remain
  python3 scripts/remove_replay_order.py --selftest       run migration fixtures

Paths are explicit files or directories (recursive *.lean); no implicit repository
scope. Comments and strings are preserved. Both generic and List-payload binders,
named arguments, primed constructors, and standalone ro arguments are supported.
The operation is idempotent. It deliberately does not delete declarations or proofs
about ReplayOrder, choose replacements for concrete order values, or edit Setup.ro.
Residual order names and field reads are reported and require manual review.
Only use on sources where the identifier ro denotes the removed replay order.
Snapshots must be regenerated, not rewritten by this script.
"""

import argparse
import difflib
from pathlib import Path
import re
import sys


def tokens(source):
    """Code tokens with offsets, excluding nested comments and string literals."""
    result = []
    i = 0
    while i < len(source):
        if source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i].isspace():
            i += 1
        else:
            match = re.match(r"[\w']+|:=|=>|.", source[i:])
            end = i + len(match[0])
            result.append((match[0], i, end))
            i = end
    return result


def migrate(source):
    ts = tokens(source)
    pairs = {}
    stack = []
    for i, (word, _, _) in enumerate(ts):
        if word in ('(', '{', '['):
            stack.append(i)
        elif word in (')', '}', ']') and stack:
            start = stack.pop()
            pairs[start] = i
    removed = set()
    order_names = {'ro', "ro'", 'ro1', 'ro6'}
    for i, j in pairs.items():
        words = [t[0] for t in ts[i + 1:j]]
        if len(words) >= 3 and words[1] == ':' and 'ReplayOrder' in words[2:]:
            order_names.add(words[0])
    # Remove whole typed binders and named arguments, including nested payload types.
    for i, j in pairs.items():
        words = [t[0] for t in ts[i + 1:j]]
        if len(words) >= 3 and words[0] in order_names:
            typed = words[1] == ':' and 'ReplayOrder' in words[2:]
            named = words[1] == ':='
            if typed or named:
                removed.update(range(i, j + 1))
        # Setup projections used as positional arguments, including (S.ro n).
        if len(words) >= 4 and words[1:3] == ['.', 'ro']:
            removed.update(range(i, j + 1))
    for i, (word, _, _) in enumerate(ts):
        if i in removed:
            continue
        if word in order_names and (i == 0 or ts[i - 1][0] != '.'):
            # Field declarations need a manual edit, not a malformed empty name.
            if i + 1 < len(ts) and ts[i + 1][0] == ':':
                continue
            if i + 2 < len(ts) and ts[i + 1][0] == '.' and ts[i + 2][0] in (
                    'order', 'parentOrder'):
                continue
            removed.add(i)
        if word == 'ReplayOrder':
            # Only imports in `open Namespace (names...)`, not type/declaration names.
            for start, end in pairs.items():
                if start < i < end and ts[start][0] == '(':
                    before = [t[0] for t in ts[max(0, start - 5):start]]
                    if 'open' in before:
                        removed.add(i)
                        break
    spans = []
    for i in sorted(removed):
        start, end = ts[i][1:]
        # Consume adjacent horizontal whitespace only; preserve line structure.
        while end < len(source) and source[end] in ' \t':
            end += 1
        if end == len(source) or source[end] in '\n)}],':
            while start > 0 and source[start - 1] in ' \t':
                start -= 1
        if spans and start <= spans[-1][1]:
            spans[-1] = (spans[-1][0], max(end, spans[-1][1]))
        else:
            spans.append((start, end))
    # Delete a line emptied by the migration, but never an existing blank line
    # or a line with a comment. Empty lines inside Lean commands are warnings.
    empty_lines = []
    offset = 0
    for line in source.splitlines(True):
        remaining = line
        for start, end in reversed(spans):
            lo, hi = max(start, offset), min(end, offset + len(line))
            if lo < hi:
                remaining = remaining[:lo - offset] + remaining[hi - offset:]
        if line.strip() and not remaining.strip():
            empty_lines.append((offset, offset + len(line)))
        offset += len(line)
    merged = []
    for start, end in sorted(spans + empty_lines):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(end, merged[-1][1]))
        else:
            merged.append((start, end))
    spans = merged
    for start, end in reversed(spans):
        if end == len(source) or source[end] in '\n)}],':
            while start > 0 and source[start - 1] in ' \t':
                start -= 1
        source = source[:start] + source[end:]
    # Keep the keyword when later lines continue the variable command.
    if re.search(r'(?m)^variable[ \t]*\n', source):
        code_starts = {start for word, start, _ in tokens(source) if word == 'variable'}
        source = re.sub(r'(?m)^variable[ \t]*\n',
                        lambda match: '' if match.start() in code_starts and not re.match(
                            r'[ \t]+[({\[]', source[match.end():]) else match[0], source)
    return source


def selftest():
    cases = [
        ('variable {sp : ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}\n',
         'variable {sp : ACParams}\n'),
        ('def goldilocksNode\' (ro : ReplayOrder sp FGP) := goldilocksAC sp FGP ro\n',
         'def goldilocksNode\' := goldilocksAC sp FGP\n'),
        ('foo (ro := S.ro _) (GoldilocksTrace\' sp ro)', 'foo (GoldilocksTrace\' sp)'),
        ('State (S.params pub hn) (S.ro _) binding', 'State (S.params pub hn) binding'),
        ('open AC (Blk ReplayOrder goldilocksAC)', 'open AC (Blk goldilocksAC)'),
        ('variable {sp ro}\nintro FGP ro self\n', 'variable {sp}\nintro FGP self\n'),
        ('outTip sp ro .confirmed st t', 'outTip sp .confirmed st t'),
        ("foo (ro' := ro) ro1 ro6", 'foo'),
        ('∀ (FGP : Type) (ro : ReplayOrder sp FGP), P FGP ro',
         '∀ (FGP : Type), P FGP'),
        ("variable {ro' : ReplayOrder sp FGP}\nfoo ro'", 'foo'),
        ('/- ro /- nested -/ ReplayOrder -/ "ro" -- ro\nfoo ro',
         '/- ro /- nested -/ ReplayOrder -/ "ro" -- ro\nfoo'),
        ('/-\nvariable\n-/\nvariable {ro : ReplayOrder sp FGP}\nfoo ro',
         '/-\nvariable\n-/\nfoo'),
        ('ro.order t Φ\n  ro : ReplayOrderData n root FGP',
         'ro.order t Φ\n  ro : ReplayOrderData n root FGP'),
        ('theorem foo {sp : ACParams}\n    {ro : ReplayOrder sp FGP}\n    (x : Nat) : True := by trivial\n',
         'theorem foo {sp : ACParams}\n    (x : Nat) : True := by trivial\n'),
        ('foo\n\n  (ro := S.ro _) -- keep comment\n  x',
         'foo\n\n  -- keep comment\n  x'),
        ('variable {ro : ReplayOrder sp FGP}\n  {t : Time}\n',
         'variable\n  {t : Time}\n'),
    ]
    for old, new in cases:
        assert migrate(old) == new, (old, migrate(old), new)
        assert migrate(new) == new, new
    print(f'PASS: {len(cases)} fixtures, including idempotence and preserved residuals')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--selftest', action='store_true')
    parser.add_argument('paths', nargs='*', type=Path)
    args = parser.parse_args()
    if args.selftest:
        selftest()
        return 0
    if not args.paths:
        parser.error('provide explicit file or directory paths')
    files = set()
    for path in args.paths:
        if not path.exists():
            parser.error(f'path does not exist: {path}')
        files.update(path.rglob('*.lean') if path.is_dir() else [path])
    changed = 0
    residual = 0
    for path in sorted(files):
        before = path.read_text()
        after = migrate(before)
        if before != after:
            changed += 1
            if args.write:
                path.write_text(after)
            elif not args.check:
                sys.stdout.writelines(difflib.unified_diff(
                    before.splitlines(True), after.splitlines(True), str(path), str(path)))
        for word, start, _ in tokens(after):
            if word in ('ro', "ro'", 'ro1', 'ro6', 'ReplayOrder', 'ReplayOrderData', 'ParentOrderAt'):
                residual += 1
                line = after.count('\n', 0, start) + 1
                print(f'RESIDUAL {path}:{line}: {word}', file=sys.stderr)
    print(f'{len(files)} files scanned; {changed} changed; {residual} residual tokens', file=sys.stderr)
    return 1 if args.check and (changed or residual) else 0


if __name__ == '__main__':
    sys.exit(main())
