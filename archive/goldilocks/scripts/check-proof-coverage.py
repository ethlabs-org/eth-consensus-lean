#!/usr/bin/env python3
"""Run CheckProofEqns with the fixed owning-module and #print axioms inventory."""
import ast
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

AUDITS = tuple('AvailableChain' + lib + '.Tests.Axioms' for lib in
               ('Generic', 'FGSA', 'FGSARun', 'FGSAClaims', 'FGSAProofs', 'FGSAInhabit',
                'FGCompose')) + ('AvailableChainFGSAProofs.Tests.FGCompose',
                                            'AvailableChainFGCompose.Tests.SafetyAxioms',
                                            'AvailableChainFGSAProofs.Tests.FGSafety',
                                            'AvailableChainFGSAProofs.Tests.SharedAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationPromotionAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationAgeAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationServiceAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationSearchAxioms',
                                            'AvailableChainFGCompose.Tests.PopulationTailAxioms',
                                            ('AvailableChainFGCompose.Tests.'
                                             'PopulationOwnerSearchAxioms'),
                                        'AvailableChainFGCompose.Tests.PopulationHighTargetAxioms',
                                        'AvailableChainFGCompose.Tests.PopulationMiddleAxioms',
                                        'AvailableChainFGCompose.Tests.PopulationRowsAxioms',
                                        'AvailableChainFGCompose.Tests.PopulationKernelAxioms',
                                            ('AvailableChainFGSAProofs.Tests.'
                                             'WeakContinuationGrowthAssemblyAxioms'))


def read_coverage(path):
    tree = ast.parse(path.read_text(), mode='eval')
    # Reject repeated keys before literal_eval can discard them.
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            keys = [ast.literal_eval(key) for key in node.keys]
            if len(keys) != len(set(keys)):
                raise ValueError('duplicate proof coverage key')
    data = ast.literal_eval(tree)
    if not isinstance(data, dict) or not data:
        raise ValueError('empty or invalid proof coverage inventory')
    rows = []
    for audit, owners in data.items():
        if not isinstance(owners, dict) or not owners:
            raise ValueError('empty or invalid proof coverage owner map')
        for owner, names in owners.items():
            if not isinstance(names, tuple) or not names:
                raise ValueError('empty or invalid proof coverage names')
            for name in names:
                if not all(isinstance(n, str) and re.fullmatch(r"[^\W\d][\w'.?!]*", n)
                           for n in (audit, owner, name)):
                    raise ValueError('invalid proof coverage identifier')
                rows.append((owner, name, audit))
    if len(rows) != len({(name, audit) for _, name, audit in rows}):
        raise ValueError('duplicate proof coverage row')
    return sorted(rows)


def section_text(audit, rows):
    lines = [f'    {audit!r}: {{']
    for owner in sorted({o for o, _, a in rows if a == audit}):
        lines.append(f'        {owner!r}: (')
        for name in sorted({n for o, n, a in rows if o == owner and a == audit}):
            if len(repr(name)) <= 86:
                lines.append(f'            {name!r},')
            else:
                cut = name.rfind('.', 0, 80) + 1
                lines += [f'            ({name[:cut]!r}', f'             {name[cut:]!r}),']
        lines.append('        ),')
    return '\n'.join([*lines, '    },']) + '\n'


def sections(text):
    tree = ast.parse(text, mode='eval').body
    return {ast.literal_eval(k): (k.lineno - 1, v.end_lineno)
            for k, v in zip(tree.keys, tree.values)}


def replace_sections(text, updates):
    lines = text.splitlines(keepends=True)
    spans = sections(text)
    for key, (start, end) in sorted(spans.items(), key=lambda item: item[1], reverse=True):
        if key in updates:
            lines[start:end] = [updates[key]]
    return ''.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate; review the diff')
    parser.add_argument('--audits', nargs='+', help='check or rewrite only these audit keys')
    parser.add_argument('--inventory', type=Path, help='alternate inventory for isolated controls')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    inventory = args.inventory or root / 'scripts/proof-audit-coverage.txt'
    audits = sorted(set(args.audits if args.audits is not None else AUDITS))
    unknown = set(audits) - set(AUDITS)
    if unknown:
        parser.error('unknown coverage key: ' + ', '.join(sorted(unknown)))
    original = inventory.read_text()
    rows = read_coverage(inventory) if not args.write or args.audits else []
    if (not args.write or args.audits) and set(sections(original)) != set(AUDITS):
        raise ValueError('proof coverage audit set differs from the FULL tier')
    updates = {}
    with tempfile.TemporaryDirectory(prefix='proof-coverage-', dir=root / '.lake') as tmp:
        coverage = Path(tmp) / 'coverage.txt'
        print(f'proof audit coverage: {len(rows)} declarations; {len(audits)} audits', flush=True)
        # Load only selected audit roots, one private environment per process.
        for audit in audits:
            selected = [row for row in rows if row[2] == audit]
            coverage.write_text(''.join(' '.join(row) + '\n' for row in selected))
            print(f'proof audit: {audit} ({len(selected)} declarations)', flush=True)
            mode = ['--write-coverage', str(coverage)] if args.write else [
                '--coverage', str(coverage), '--complete-coverage']
            rc = subprocess.call(['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
                                  '--baseline', 'scripts/baselines/check-proof-eqns.txt',
                                  *(['--roots-only'] if args.audits else []),
                                  *mode, audit], cwd=root)
            if rc:
                return rc
            if args.write:
                generated = [tuple(line.split()) for line in coverage.read_text().splitlines()]
                updates[audit] = section_text(audit, generated)
                if not args.audits and audit in sections(original):
                    start, end = sections(original)[audit]
                    prior = ''.join(original.splitlines(keepends=True)[start:end])
                    def row_set(section):
                        data = ast.literal_eval('{' + section + '}')[audit]
                        return {(o, n) for o, names in data.items() for n in names}
                    if row_set(prior) == row_set(updates[audit]):
                        updates[audit] = prior
        if args.write:
            if args.audits:
                output = replace_sections(original, updates)
            else:
                header = ('# Complete C14 audit inventory. Generate with '
                          'check-proof-coverage.py --write.\n'
                          '# Review changes. Normal checks never regenerate this file.\n{\n')
                output = header + ''.join(updates[a] for a in audits) + '}\n'
            inventory.write_text(output)
        return 0


if __name__ == '__main__':
    raise SystemExit(main())
