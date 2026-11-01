#!/usr/bin/env python3
"""Compile F-24 route controls under .lake, outside all library source trees."""
import os
from pathlib import Path
import subprocess
import tempfile


CHECKER = 'scripts/CheckFaultXRoute.lean'
PREFIX = 'AvailableChainFaultXRouteControl'
NAMESPACE = 'AvailableChain.FaultXRouteControl'


def run(args, *, env=None, expected_rc=0):
    result = subprocess.run(args, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode != expected_rc:
        raise RuntimeError(f'control command failed: {args}; rc {result.returncode}\n{result.stdout}')
    return result.stdout


def main():
    if os.environ.get('NEG', '1') == '0':
        print('F-24-ROUTE controls: SKIPPED (NEG=0)')
        return
    # A separate AvailableChain* prefix keeps the built library roots visible.
    # Lake retains the extra LEAN_PATH entry when it adds its build paths.
    with tempfile.TemporaryDirectory(prefix='faultx-route.', dir='.lake') as scratch:
        root = Path(scratch).resolve()
        env = dict(os.environ, LEAN_PATH=str(root) + os.pathsep + os.environ.get('LEAN_PATH', ''))

        def compile_module(suffix, body):
            module = PREFIX + '.' + suffix
            source = root / (module.replace('.', '/') + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('''module
public import AvailableChainGeneric.Proofs.Pure.Quorum
public section
open AvailableChain.Gen.Pure
namespace AvailableChain.FaultXRouteControl
''' + body + '\nend AvailableChain.FaultXRouteControl\nend\n')
            run(['lake', 'env', 'lean', '--root=' + str(root), '-o',
                 str(source.with_suffix('.olean')), str(source)], env=env)
            return module

        positive = compile_module('Positive', '''
theorem count_rec_positive {n a : Nat} (hn : 0 < n) (hf : a ≤ (n - 1) / 3) :
    FaultX n a := count_rec hn hf
private def bridge {n a : Nat} (hn : 0 < n) (hf : a ≤ (n - 1) / 3) :
    FaultX n a := count_rec hn hf
private theorem count_rec_private_positive {n a : Nat} :
    0 < n → a ≤ (n - 1) / 3 → FaultX n a := fun hn hf => bridge hn hf
theorem count_rec_indirect {n a : Nat} (hn : 0 < n) (hf : a ≤ (n - 1) / 3) :
    FaultX n a := count_rec_private_positive hn hf
''')
        output = run(['lake', 'env', 'lean', '--run', CHECKER, positive, '--routes',
                      '--expect', NAMESPACE + '.count_rec_positive',
                      NAMESPACE + '.count_rec_indirect'], env=env)
        accepted = [line for line in output.splitlines()
                    if line.startswith('F-24-ROUTE-OK ') and f'({positive})' in line]
        if len(accepted) != 3 or not any('bridge' in line for line in accepted):
            raise RuntimeError('positive control did not check direct/private/transitive routes:\n' + output)
        print('F-24-ROUTE controls: PASS (direct, private, and transitive routes)')

        negative = compile_module('Negative', '''
-- The name passes the old rule, and count_rec is imported but not used.
theorem count_rec_bypass : FaultX 4 0 := by
  constructor
  simp only [qF_def]
  omega
private theorem count_rec_private_bypass : FaultX 4 0 := by
  constructor
  simp only [qF_def]
  omega
theorem count_rec_arrow {n a : Nat} : FaultX n a → FaultX n a := fun h => h
''')
        output = run(['lake', 'env', 'lean', '--run', CHECKER, negative,
                      '--expect', NAMESPACE + '.count_rec_bypass',
                      NAMESPACE + '.count_rec_arrow'], env=env, expected_rc=1)
        rejected = [line for line in output.splitlines() if line.startswith('F-24-ROUTE ')]
        expected = {f'F-24-ROUTE {NAMESPACE}.{name} ({negative})'
                    for name in ('count_rec_bypass', 'count_rec_arrow')}
        private = [line for line in rejected
                   if line.startswith('F-24-ROUTE _private.')
                   and line.endswith(f'.count_rec_private_bypass ({negative})')]
        if len(private) != 1 or set(rejected) != expected | set(private):
            raise RuntimeError('negative control diagnostic mismatch:\n' + output)
        for line in rejected:
            print('F-24-ROUTE controls: rejected ' + line)
        print('F-24-ROUTE controls: PASS (omega, private omega, and arrow; rc 1)')


if __name__ == '__main__':
    main()
