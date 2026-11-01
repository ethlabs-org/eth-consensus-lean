#!/usr/bin/env python3
"""Check the UNPORTED boundary, then test it with isolated negative controls."""
import argparse
from pathlib import Path
import tempfile
import tomllib

import check_common as C
import unported as U


def check():
    names = U.read()
    config = tomllib.loads((U.ROOT / 'lakefile.toml').read_text())
    if names & set(config['defaultTargets']):
        raise ValueError('UNPORTED DEFAULT TARGET')
    libraries = {lib['name'] for lib in config['lean_lib']}
    if not names <= libraries:
        raise ValueError('UNKNOWN UNPORTED LIBRARY')
    graph = C.import_graph()
    roots = [m for m in graph if m.startswith('AvailableChainFGSA') or
             U.contains(m, ('AvailableChainGeneric', 'AvailableChainFGCompose'))]
    U.check_imports(graph, roots)
    print(f'UNPORTED boundary: PASS ({len(roots)} FG-SA/Generic/Compose modules)')
    return libraries


def rejected(label, reason, action):
    try:
        action()
    except ValueError as error:
        if reason not in str(error):
            raise AssertionError(str(error)) from error
        print('CONTROL ' + label + ': PASS (' + str(error) + ')')
        return
    raise AssertionError('CONTROL ACCEPTED: ' + label)


def selftest(libraries):
    with tempfile.TemporaryDirectory(prefix='unported-controls-') as scratch:
        path = Path(scratch) / 'unported.txt'
        for lib in sorted(libraries):
            if lib.startswith('AvailableChainFGSA'):
                path.write_text(U.LIST.read_text() + lib + '\n')
                rejected(lib, 'FG-SA library', lambda: U.read(path))
        for text in ('AvailableChainGeneric\n', 'AvailableChainPCSA\n',
                     U.LIST.read_text() + 'AvailableChainPCSA\n'):
            path.write_text(text)
            rejected('invalid list', 'UNPORTED REFUSED', lambda: U.read(path))
        path.write_text('# Port complete\n')
        assert not U.read(path)
    for root in ('AvailableChainFGSA.Proofs.Control', 'AvailableChainGeneric.Pure.Control',
                 'AvailableChainFGCompose.Proofs.Control'):
        for pc in sorted(U.PCSA - {'AvailableChainPCSAProofsTests'}):
            for indirect in (False, True):
                module = pc + '.Model.Control'
                graph = {root: ['Aux.Control'] if indirect else [module],
                         'Aux.Control': [module]}
                rejected(root + (' transitive' if indirect else ' direct'),
                         'ACTIVE IMPORTS PC-SA', lambda: U.check_imports(graph, [root]))
    U.check_imports({'AvailableChainFGSA': ['AvailableChainGeneric.Pure'],
                     'AvailableChainGeneric.Pure': []}, ['AvailableChainFGSA'])
    print('UNPORTED self-tests: PASS')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check current source only')
    args = parser.parse_args()
    libraries = check()
    if not args.check:
        selftest(libraries)
