#!/usr/bin/env python3
"""Check (h), BUILD §7.3: `set_option backward.isDefEq.respectTransparency
false`.

Each use in a library file (comments and strings removed)
- is `set_option backward.isDefEq.respectTransparency false in` as the first
  tactic of a proof: the token before it is `by`. A use at the command level
  (on a declaration), a use later in a proof, a use without `in` and any
  other value are findings;
- has a reason comment on the line before (a `--` line with text);
- has an entry `<module> <declaration> <reason>` in
  scripts/transparency-allow.txt (declaration = the full name of the
  enclosing declaration; for a command-level use, the next declaration).
The option in lakefile.toml is a finding too (BUILD §7.5: per declaration,
not global).

The 142 uses on main 7ac5b0c (the v4.34.1 port) have allow entries with a
legacy reason; their missing reason comments are the baseline
scripts/baselines/check-transparency.txt. A new use without an entry fails.
Scope: scripts/new-libraries.txt. Exit 0: no failing finding; 1: a failing
finding. `--missing-entries` prints an allow line for each use without an
entry (reason `TODO`)."""
import argparse
import os
import re
import sys

sys.dont_write_bytecode = True
import check_common as C  # noqa: E402

NAME = 'check-transparency'
ALLOW = os.path.join(C.SCRIPTS, 'transparency-allow.txt')
OPTION = 'backward.isDefEq.respectTransparency'
USE = re.compile(r'set_option\s+backward\.isDefEq\.respectTransparency\b[ \t]*(\S*)([ \t]+in\b)?')
MENTION = re.compile(r'\brespectTransparency\b')


def read_allow():
    allow = {}
    if os.path.exists(ALLOW):
        for n, line in enumerate(open(ALLOW, encoding='utf-8'), 1):
            if not line.strip() or line.lstrip().startswith('#'):
                continue
            parts = line.split(None, 2)
            if len(parts) < 3 or not parts[2].strip():
                sys.exit(f'scripts/transparency-allow.txt:{n}: expected <module> <declaration> <reason>')
            allow[(parts[0], parts[1])] = parts[2].strip()
    return allow


def main():
    ap = C.standard_args(argparse.ArgumentParser(description=__doc__.split('\n')[0]))
    ap.add_argument('--missing-entries', action='store_true')
    a = ap.parse_args()
    scope = C.Scope()
    allow = read_allow()
    used, findings, missing, n_uses = set(), [], [], 0
    for lf in C.library_files():
        text = lf.stripped
        if 'respectTransparency' not in text:
            continue
        new = scope.is_new_file(lf)
        decls = C.declarations(lf)
        raw_lines = lf.raw.split('\n')
        covered = set()
        for m in USE.finditer(text):
            n_uses += 1
            covered.update(range(m.start(), m.end()))
            line = C.line_of(text, m.start())
            line_start = text.rfind('\n', 0, m.start()) + 1
            before = text[:m.start()].rstrip()
            if re.search(r'(^|[^\w.])by$', before):
                placement = 'first-tactic'
            elif m.start() == line_start:
                placement = 'on-declaration'
            else:
                placement = 'not-first-tactic'
            if placement == 'on-declaration':
                d = next((d for d in decls if d.start >= m.start()), None)
            else:
                d = next((d for d in reversed(decls) if d.start <= m.start()), None)
            decl = d.full if d else '<none>'
            where = f'{lf.path}:{line} ({decl})'
            if placement != 'first-tactic':
                findings.append(C.Finding(f'placement {lf.module} {decl} {placement}',
                                          f'{where}: {placement}; the option must be the first tactic of the proof', new))
            if m.group(1) != 'false' or not m.group(2):
                form = f'{m.group(1)}{" in" if m.group(2) else ""}'
                findings.append(C.Finding(f'form {lf.module} {decl} {form}',
                                          f'{where}: form `set_option {OPTION} {form}`; expected `false in`', new))
            prev = raw_lines[line - 2].strip() if line >= 2 else ''
            if not (prev.startswith('--') and prev.lstrip('-').strip()):
                findings.append(C.Finding(f'no-reason {lf.module} {decl}',
                                          f'{where}: no reason comment on the line before', new))
            if (lf.module, decl) in allow:
                used.add((lf.module, decl))
            else:
                findings.append(C.Finding(f'no-entry {lf.module} {decl}',
                                          f'{where}: no entry in scripts/transparency-allow.txt', new))
                missing.append(f'{lf.module} {decl} TODO')
        for m in MENTION.finditer(text):
            if m.start() not in covered:
                findings.append(C.Finding(f'other-use {lf.module}',
                                          f'{lf.path}:{C.line_of(text, m.start())}: respectTransparency outside a `set_option … in`', new))
    lake = open(os.path.join(C.ROOT, 'lakefile.toml'), encoding='utf-8').read()
    if MENTION.search(re.sub(r'#.*', '', lake)):
        findings.append(C.Finding('lakefile-option', 'lakefile.toml: respectTransparency as a global option'))
    if a.missing_entries:
        print('\n'.join(missing))
        return 0
    if a.write_baseline:
        n = C.write_baseline(NAME, findings, [
            'check (h) check-transparency: legacy findings (BUILD §7.3; the 142 uses of the v4.34.1 port).',
            'Generated by: python3 scripts/check-transparency.py --write-baseline'])
        print(f'{NAME}: wrote {n} baseline entries')
        return 0
    print(f'{NAME}: {n_uses} uses; {len(allow)} allow entries')
    for k in sorted(set(allow) - used):
        print(f'note: allow entry with no use (remove it): {k[0]} {k[1]}')
    return 1 if C.evaluate(NAME, findings, a.list_legacy) else 0


if __name__ == '__main__':
    sys.exit(main())
