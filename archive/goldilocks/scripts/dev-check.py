#!/usr/bin/env python3
"""Development checks for sleep packages and the fixed S1 scope."""
import argparse
from pathlib import Path
from source_layout import Layout
import re
import subprocess
import sys

import check_common as C
import unported as U

ROOT = Path(__file__).resolve().parents[1]
PREFIXES = tuple('AvailableChain' + s for s in
                 ('EngineV2', 'KitV2', 'Generic', 'FGSA', 'FGSARun', 'FGCompose'))
SHARED = 'AvailableChainFGSAProofs.Proofs.Shared'
SHARED_CLAIM = 'AvailableChainFGSAClaims.Claims.Shared'
SHARED_AUDIT = 'AvailableChainFGSAProofs.Tests.SharedAxioms'
AUDITS = tuple(p + '.Tests.Axioms' for p in PREFIXES) + (
    'AvailableChainFGCompose.Tests.SafetyAxioms', SHARED_AUDIT)
COVERAGE = tuple(a for a in AUDITS if not a.startswith(
    ('AvailableChainEngineV2.', 'AvailableChainKitV2.')))
STABLE = {'AvailableChainCheckSupport', 'AvailableChainFramework', 'AvailableChainGridCO',
          'AvailableChainKit', 'AvailableChainKitFG', 'AvailableChainLStar',
          'AvailableChainModel', 'AvailableChainRegistry', 'AvailableChainSA',
          'AvailableChainSAPC', 'AvailableChainSimplexFG', 'AvailableChainStatements',
          'AvailableChainWitnesses', 'Init', 'Lean', 'Mathlib', 'Std'}


def under(module, prefix):
    return module == prefix or module.startswith(prefix + '.')


def read_map(path, sections, owned):
    data = {s: {} for s in sections}
    section = None
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.split('#', 1)[0].strip()
        if not line:
            continue
        if line.startswith('['):
            section = line[1:-1] if line.endswith(']') else None
            if section not in data:
                raise ValueError(f'UNKNOWN SECTION {path}:{lineno}: {line}')
            continue
        parts = line.split()
        if section is None or len(parts) != (2 if section in owned else 1):
            raise ValueError(f'INVALID ENTRY {path}:{lineno}: {line}')
        name = parts[0]
        if not re.fullmatch(r'[A-Za-z][\w]*(?:\.[A-Za-z][\w]*)*', name):
            raise ValueError('INVALID MODULE: ' + name)
        if name in data[section] or (section != 'TARGETS' and any(
                name in entries for key, entries in data.items() if key != 'TARGETS')):
            raise ValueError('DUPLICATE ENTRY: ' + name)
        if section in owned and not re.fullmatch(r'[A-Za-z][\w-]*', parts[1]):
            raise ValueError('INVALID OWNER: ' + line)
        data[section][name] = parts[1] if section in owned else None
    return data


def s1_domain(graph):
    base = {m for m in graph if any(under(m, p) for p in PREFIXES) or under(m, SHARED)}
    base |= {SHARED_CLAIM, SHARED_AUDIT}
    return base | {m for b in base - {SHARED + '.Claims'} for m in C.closure(graph, b)
                   if under(m, 'AvailableChainFGSAClaims.Statements')}


def validate_scope(path, graph):
    data = read_map(path, ('REQUIRED', 'DEFERRED', 'STABLE'), {'DEFERRED'})
    required, deferred, stable = (set(data[s]) for s in ('REQUIRED', 'DEFERRED', 'STABLE'))
    if stable != STABLE:
        raise ValueError('STABLE LIBRARIES DIFFER: ' + ', '.join(sorted(stable ^ STABLE)))
    domain = s1_domain(graph)
    missing = domain - required - deferred
    if missing:
        raise ValueError('OMITTED S1 MODULE: ' + ', '.join(sorted(missing)))
    extra = (required | deferred) - domain
    if extra:
        raise ValueError('UNKNOWN S1 TARGET: ' + ', '.join(sorted(extra)))
    if not set(AUDITS) <= required:
        raise ValueError('S1 AUDIT NOT REQUIRED')
    for name in sorted(required):
        if name not in graph:
            raise ValueError('UNKNOWN REQUIRED MODULE: ' + name)
        closure = C.closure(graph, name)
        bad = closure & deferred
        if bad:
            raise ValueError('REQUIRED IMPORTS DEFERRED: ' + name + ' -> ' + ', '.join(sorted(bad)))
        bad = {m for m in closure - required if not any(under(m, p) for p in stable)}
        if bad:
            raise ValueError('REQUIRED IMPORTS OUTSIDE SCOPE: ' + name + ' -> ' +
                             ', '.join(sorted(bad)))
    return required


def validate_package(path, required, graph):
    data = read_map(path, ('TARGETS', 'GREEN', 'EXPECTED-FAIL'), {'EXPECTED-FAIL'})
    green, expected = ({m for m in data[s] if not U.contains(m)}
                       for s in ('GREEN', 'EXPECTED-FAIL'))
    targets = {m for m in data['TARGETS'] if not U.contains(m)}
    for module in sorted(set().union(*data.values())):
        if U.contains(module):
            print('SKIP UNPORTED package module: ' + module, flush=True)
    domain = required | targets
    unknown = (targets | green | expected) - set(graph)
    if unknown:
        raise ValueError('UNKNOWN PACKAGE TARGET: ' + ', '.join(sorted(unknown)))
    extra = (green | expected) - domain
    if extra:
        raise ValueError('UNKNOWN PACKAGE TARGET: ' + ', '.join(sorted(extra)))
    missing = domain - green - expected
    if missing:
        raise ValueError('OMITTED PACKAGE MODULE: ' + ', '.join(sorted(missing)))
    for m in sorted(expected):
        print(f'EXPECTED-FAIL {m}: repair owner {data["EXPECTED-FAIL"][m]}', flush=True)
    return green


def strict_results(source, output):
    want = len(re.findall(r'^#print axioms\b', source, re.M))
    results = re.findall(r'depends on axioms: \[([^]]*)\]|does not depend on any axioms',
                         output, re.S)
    bad = {a.strip() for row in results for a in row.split(',') if a.strip()} - {
        'propext', 'Classical.choice', 'Quot.sound'}
    if bad:
        raise ValueError('BAD AXIOMS: ' + ', '.join(sorted(bad)))
    if want == 0 or len(results) != want:
        raise ValueError(f'AXIOM RESULTS: {len(results)} of {want} commands')
    print(f'axioms: {want} results; only propext, Classical.choice, Quot.sound', flush=True)


def run(args):
    subprocess.run(args, cwd=ROOT, check=True)


def audit_strict(path):
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    result.check_returncode()
    strict_results(path.read_text(), result.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    level = parser.add_mutually_exclusive_group(required=True)
    level.add_argument('--stage', choices=['s1'])
    level.add_argument('--package')
    level.add_argument('--all', action='store_true')
    parser.add_argument('--scope', type=Path, default=ROOT / 'scripts/dev-scope-s1.txt')
    parser.add_argument('--package-map', type=Path)
    args = parser.parse_args()
    graph = C.import_graph()
    required = validate_scope(args.scope, graph)
    if args.package:
        if not re.fullmatch(r'[A-Za-z][\w-]*', args.package):
            parser.error('invalid package ID')
        path = args.package_map or ROOT / 'scripts/dev-pkg' / (args.package + '.txt')
        green = validate_package(path, required, graph)
        audits = [m for m in sorted(green) if re.search(
            r'^#print axioms\b', (ROOT / Layout(ROOT).source_path(m)).read_text(), re.M)]
        label = 'package ' + args.package
    elif args.stage:
        if args.package_map:
            parser.error('--package-map requires --package')
        green, audits, label = required, AUDITS, 'stage s1'
    else:
        green, audits, label = None, AUDITS, 'all'
    run(['python3', '-B', 'scripts/check-sleep-scopes.py'])
    # --wfail rejects a proof placeholder even when Lean would accept its warning.
    run(['lake', 'build', '--wfail', *(sorted(green) if green is not None else ['@']),
         'AvailableChainCheckSupport'])
    for module in audits:
        audit_strict(ROOT / Layout(ROOT).source_path(module))
    if args.stage:
        run(['python3', '-B', 'scripts/check-proof-coverage.py', '--audits', *COVERAGE])
        run(['python3', '-B', 'scripts/check-fg-compose-source.py'])
    elif args.all:
        run(['bash', 'scripts/check-fgsa-claims.sh'])
        run(['python3', '-B', 'scripts/check-proof-coverage.py'])
        run(['bash', 'scripts/check-fg-compose.sh'])
        # At S2 the late-family roots are also strict.
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'coverage', ROOT / 'scripts/check-proof-coverage.py')
        coverage = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(coverage)
        for module in coverage.AUDITS:
            if module not in audits:
                audit_strict(ROOT / Layout(ROOT).source_path(module))
    if __import__('os').environ.get('NEG', '1') != '0':
        run(['python3', '-B', 'scripts/dev-check-controls.py'])
    print(f'DCK PASS ({label})', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
