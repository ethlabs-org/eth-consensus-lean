#!/usr/bin/env python3
"""Check that each public source declaration of the FG finality-safety modules is audited.

The proof-audit coverage check starts from the `#print axioms` commands. This
check starts from the source instead. It reads the public declarations of the
exact safety adapter, bridge, export and assembly modules below (MODULES is the
one list). Each one must have a `#print axioms` command in one owning audit of
its module, and a row with that owner and audit in
scripts/proof-audit-coverage.txt (active) or
scripts/pcsa-source-audit-coverage.txt (deferred PC-SA). The scope is exact: it needs no legacy
baseline. A safety module that is not in MODULES fails the check: every
`Safety*` module of AvailableChainFGCompose and every `*FGSafety*` or
`*FinalitySafety*` module of the two protocol proof libraries.
"""
import argparse
import ast
import os
from pathlib import Path
from source_layout import Layout
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_common as C  # noqa: E402
import unported as U

ROOT = Path(C.ROOT)

FGC = 'AvailableChainFGCompose.Tests.SafetyAxioms'
FGB = 'AvailableChainFGSAProofs.Tests.FGSafety'
FGA = 'AvailableChainFGSAProofs.Tests.Axioms'
PCB = 'AvailableChainPCSAProofs.Tests.FGSafety'
PCA = 'AvailableChainPCSAProofs.Tests.Axioms'
GROWTH = 'AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms'

# module -> owning audit (or audits)
MODULES = {
    'AvailableChainFGCompose.Statements.SafetyReads': FGC,
    'AvailableChainFGCompose.Statements.SafetyStore': FGC,
    'AvailableChainFGCompose.Statements.SafetyClient': FGC,
    'AvailableChainFGCompose.Statements.SafetyClaims': FGC,
    'AvailableChainFGCompose.Proofs.SafetyStore': FGC,
    'AvailableChainFGCompose.Proofs.SafetyAccountable': FGC,
    'AvailableChainFGCompose.Proofs.SafetyClient': FGC,
    'AvailableChainFGCompose.Proofs.SafetyCount': FGC,
    'AvailableChainFGCompose.Proofs.SafetyMonotone': FGC,
    'AvailableChainFGCompose.Proofs.SafetySlashing': FGC,
    'AvailableChainFGCompose.Statements.SafetyOrigin': 'AvailableChainFGCompose.Tests.Axioms',
    'AvailableChainFGCompose.Proofs.SafetyOrigin': 'AvailableChainFGCompose.Tests.Axioms',
    'AvailableChainFGCompose.Proofs.Population.Safety': 'AvailableChainFGCompose.Tests.PopulationAxioms',
    'AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge': FGB,
    'AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient': FGB,
    'AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope': FGB,
    'AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore': FGB,
    'AvailableChainFGSAProofs.Proofs.Foundations.Export': FGA,
    'AvailableChainFGSAProofs.Proofs.Assembly.Root': (FGA, GROWTH),
    'AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClientLaws': PCA,
    'AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyScope': PCA,
    'AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge': PCB,
    'AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient': PCB,
    'AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore': PCB,
    'AvailableChainPCSAProofs.Proofs.Foundations.FinalitySafety': PCB,
    'AvailableChainPCSAProofs.Proofs.Finality.Export': PCB,
    'AvailableChainPCSAProofs.Proofs.Assembly.Finality': PCB,
}

DEFERRED_MODULES = {m: a for m, a in MODULES.items() if U.contains(m)}
ACTIVE_MODULES = {m: a for m, a in MODULES.items() if m not in DEFERRED_MODULES}

KINDS = ('theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'inductive', 'opaque',
         'irreducible_def', 'instance', 'axiom')
PUBLIC_SECTION = re.compile(r'^(?:@\[expose\]\s+)?public\s+section\b')
PRINT = re.compile(r'^#print\s+axioms\s+(\S+)\s*$')
# Safety modules that MODULES must list: (library directory, file-name pattern).
DISCOVER = (('AvailableChainFGCompose', re.compile(r'^Safety\w*\.lean$')),
            ('AvailableChainFGSAProofs', re.compile(r'^\w*(FGSafety|FinalitySafety)\w*\.lean$')),
            ('AvailableChainPCSAProofs', re.compile(r'^\w*(FGSafety|FinalitySafety)\w*\.lean$')))


def source(root, module):
    return root / Layout(root).source_path(module)


def public_declarations(root, module):
    """Non-private, named declarations inside a top-level `public section`."""
    path = source(root, module)
    if not path.is_file():
        raise LookupError(f'MISSING SOURCE: {module}')
    lf = C.LeanFile(module.split('.')[0], str(path), module)
    lines = lf.stripped.split('\n')
    public, inside = set(), False
    for k, line in enumerate(lines, 1):
        if PUBLIC_SECTION.match(line):
            inside = True
        elif inside and re.match(r'^end\s*$', line):
            inside = False
        if inside:
            public.add(k)
    names = []
    for d in C.declarations(lf):
        if d.kind == 'example' or not d.name:
            continue
        if d.kind not in KINDS:
            continue
        if d.kind == 'axiom':
            raise ValueError(f'AXIOM IN SAFETY MODULE: {module} {d.full}')
        if d.private or (d.line not in public and 'public' not in d.text().split(d.kind)[0]):
            continue
        names.append(d.full)
    if not names:
        raise ValueError(f'NO PUBLIC DECLARATIONS: {module}')
    if len(names) != len(set(names)):
        raise ValueError(f'DUPLICATE DECLARATION: {module}')
    return names


def read_coverage(path):
    tree = ast.parse(path.read_text(), mode='eval')
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            keys = [ast.literal_eval(key) for key in node.keys]
            if len(keys) != len(set(keys)):
                raise ValueError('DUPLICATE COVERAGE KEY')
    data = ast.literal_eval(tree)
    return {(owner, name, audit) for audit, owners in data.items()
            for owner, names in owners.items() for name in names}


def audit_commands(root, audit):
    """Full names of the `#print axioms` commands; a short name resolves in the
    audit's `open` namespaces."""
    path = source(root, audit)
    if not path.is_file():
        raise LookupError(f'MISSING AUDIT: {audit}')
    text = C.strip(path.read_text())
    opened = [ns for line in text.split('\n') for m in [re.match(r'^open\s+(.*)$', line)] if m
              for ns in m.group(1).split()]
    names = set()
    for line in text.split('\n'):
        m = PRINT.match(line)
        if m:
            names.add(m.group(1))
            names.update(ns + '.' + m.group(1) for ns in opened)
    return names


def audits_of(owner):
    return owner if isinstance(owner, tuple) else (owner,)


def unlisted_modules(root, modules):
    found = []
    for lib, pattern in DISCOVER:
        for path in sorted((root / Layout(root).source_dir(lib)).rglob('*.lean')):
            if '/Tests/' in str(path) or not pattern.match(path.name):
                continue
            module = Layout(root).module_of_source(path)
            if module not in modules:
                found.append(module)
    return found


def check(root, modules=MODULES, coverage=None, source_coverage=None):
    rows = read_coverage(coverage or root / 'scripts/proof-audit-coverage.txt')
    deferred_rows = read_coverage(source_coverage or
                                  root / 'scripts/pcsa-source-audit-coverage.txt') \
        if modules is MODULES else set()
    audits = sorted({a for owner in modules.values() for a in audits_of(owner)})
    commands = {audit: audit_commands(root, audit) for audit in audits}
    errors = [f'UNLISTED SAFETY MODULE: {m}' for m in unlisted_modules(root, modules)]
    total = 0
    for module, owner in modules.items():
        names = public_declarations(root, module)
        total += len(names)
        for name in names:
            owning = [a for a in audits_of(owner) if name in commands[a]]
            label = ', '.join(audits_of(owner))
            if not owning:
                errors.append(f'NOT IN OWNING AUDIT: {name} ({module}; {label})')
            else:
                inventory = deferred_rows if module in DEFERRED_MODULES else rows
                if any((module, name, a) in inventory for a in owning):
                    continue
                owners = sorted(f'{o} / {a}' for o, n, a in inventory if n == name)
                where = '; found under ' + ', '.join(owners) if owners else ''
                errors.append(f'NOT IN COVERAGE: {name} ({module}; {label}){where}')
    return total, errors


def report(root, **kw):
    try:
        total, errors = check(root, **kw)
    except (LookupError, ValueError, SyntaxError) as e:
        print(f'FG finality coverage: INPUT ERROR: {e}')
        return 2
    for e in errors:
        print(e)
    if errors:
        print(f'FG finality coverage: FAIL ({len(errors)} missing of {total} declarations)')
        return 1
    print(f'FG finality coverage: PASS ({len(MODULES) if kw.get("modules") is None else len(kw["modules"])}'
          f' modules; {total} public declarations)')
    return 0


def selftest():
    owner, audit = 'Fix.Proofs.Safe', 'Fix.Tests.Audit'
    good = ('module\npublic section\nnamespace Fix\n'
            'theorem good : True := True.intro\n'
            'def value : Nat := 1\n'
            'private theorem hidden : True := True.intro\n'
            'example : True := True.intro\nend Fix\nend\n'
            'theorem outside : True := True.intro\n')
    audit_src = 'module\npublic section\n#print axioms Fix.good\n#print axioms Fix.value\n'
    cover = ("{'Fix.Tests.Audit': {'Fix.Proofs.Safe': ('Fix.good', 'Fix.value')}}\n")
    cases = [
        ('positive', {}, 0, 'PASS (1 modules; 2 public'),
        ('missing audit command', {'audit': audit_src.replace('#print axioms Fix.value\n', '')},
         1, 'NOT IN OWNING AUDIT: Fix.value'),
        ('missing coverage row', {'cover': cover.replace(", 'Fix.value'", '')},
         1, 'NOT IN COVERAGE: Fix.value'),
        ('wrong owner', {'cover': "{'Fix.Tests.Audit': {'Fix.Proofs.Safe': ('Fix.good',),"
                                  " 'Fix.Proofs.Other': ('Fix.value',)}}\n"},
         1, 'found under Fix.Proofs.Other / Fix.Tests.Audit'),
        ('wrong audit', {'cover': "{'Fix.Tests.Audit': {'Fix.Proofs.Safe': ('Fix.good',)},"
                                  " 'Fix.Tests.Other': {'Fix.Proofs.Safe': ('Fix.value',)}}\n"},
         1, 'found under Fix.Proofs.Safe / Fix.Tests.Other'),
        ('unlisted public declaration', {'src': good.replace('end Fix\nend\n',
                                                        'theorem added : True := True.intro\n'
                                                        'end Fix\nend\n')},
         1, 'NOT IN OWNING AUDIT: Fix.added'),
        ('new structure', {'src': good.replace('end Fix\nend\n',
                                               'structure Laws where\n  ok : True\nend Fix\nend\n')},
         1, 'NOT IN OWNING AUDIT: Fix.Laws'),
        ('missing source', {'src': None}, 2, 'MISSING SOURCE: Fix.Proofs.Safe'),
        ('missing audit', {'audit': None}, 2, 'MISSING AUDIT: Fix.Tests.Audit'),
        ('empty module', {'src': 'module\npublic section\nend\n'}, 2,
         'NO PUBLIC DECLARATIONS: Fix.Proofs.Safe'),
        ('axiom', {'src': good.replace('end Fix\nend\n', 'axiom bad : False\nend Fix\nend\n')},
         2, 'AXIOM IN SAFETY MODULE'),
        ('unlisted safety module', {'extra': ('AvailableChainFGCompose/Proofs/SafetyExtra.lean',
                                              'module\npublic section\ntheorem extra : True := '
                                              'True.intro\nend\n')},
         1, 'UNLISTED SAFETY MODULE: AvailableChainFGCompose.Proofs.SafetyExtra'),
        ('short audit name', {'audit': 'module\npublic section\nopen Fix\n#print axioms good\n'
                                       '#print axioms value\n'}, 0, 'PASS (1 modules; 2 public'),
        ('duplicate coverage key', {'cover': "{'Fix.Tests.Audit': {'Fix.Proofs.Safe': ('Fix.good',),"
                                             " 'Fix.Proofs.Safe': ('Fix.value',)}}\n"},
         2, 'DUPLICATE COVERAGE KEY'),
    ]
    import contextlib
    import io
    for nested in (False, True):
        for label, change, code, reason in cases:
            with tempfile.TemporaryDirectory(prefix='fg-fin-coverage.') as tmp:
                root = Path(tmp)
                (root / 'lakefile.toml').write_text(
                    'srcDir="' + ('src' if nested else '.') + '"\n' +
                    '[[lean_lib]]\nname="Fix"\n' + ''.join(
                        '[[lean_lib]]\nname="' + lib + '"\n' for lib, _ in DISCOVER))
                files = {'src': (source(root, owner), good),
                         'audit': (source(root, audit), audit_src),
                         'cover': (root / 'cover.txt', cover)}
                if 'extra' in change:
                    extra = root / Layout(root).physical_path(change['extra'][0])
                    extra.parent.mkdir(parents=True, exist_ok=True)
                    extra.write_text(change['extra'][1])
                for key, (path, text) in files.items():
                    text = change.get(key, text)
                    if text is not None:
                        path.parent.mkdir(parents=True, exist_ok=True)
                        path.write_text(text)
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    rc = report(root, modules={owner: audit}, coverage=root / 'cover.txt')
                text = out.getvalue()
                assert rc == code and reason in text, (label, rc, text)
                print(f'SELFTEST FG finality coverage nested={nested} {label}: '
                      f'PASS (rc {code}; {reason})')
    print('FG finality coverage selftest: PASS')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--inventory', type=Path)
    parser.add_argument('--source-inventory', type=Path)
    args = parser.parse_args()
    return selftest() if args.selftest else report(
        ROOT, coverage=args.inventory, source_coverage=args.source_inventory)


if __name__ == '__main__':
    raise SystemExit(main())
