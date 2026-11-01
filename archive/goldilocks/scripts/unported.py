"""Read the one UNPORTED switch. Source checks retain every library."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
LIST = ROOT / 'scripts/unported-libraries.txt'
PCSA = frozenset('AvailableChain' + s for s in
                 ('PCSA', 'PCSARun', 'PCSAClaims', 'PCSAProofs', 'PCSAProofsTests'))


def read(path=LIST):
    names = [line.split('#', 1)[0].strip() for line in path.read_text().splitlines()]
    names = [name for name in names if name]
    if any(name.startswith('AvailableChainFGSA') for name in names):
        raise ValueError('UNPORTED REFUSED: FG-SA library')
    if len(names) != len(set(names)) or set(names) not in (set(), PCSA):
        raise ValueError('UNPORTED REFUSED: use the complete PC-SA group or an empty list')
    return frozenset(names)


UNPORTED = read()


def contains(module, names=None):
    return any(module == p or module.startswith(p + '.')
               for p in (UNPORTED if names is None else names))


def pcsa():
    return 'AvailableChainPCSA' in UNPORTED


def check_imports(graph, roots):
    for root in roots:
        seen, pending = set(), [root]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            pending.extend(graph.get(module, ()))
        bad = {m for m in seen if contains(m, PCSA)}
        if bad:
            raise ValueError('ACTIVE IMPORTS PC-SA: ' + root + ' -> ' +
                             ', '.join(sorted(bad)))


def blueprint_clauses(data):
    """Keep FG-SA rows strict even if their module field names PC-SA."""
    for proto, rows in data.get('safety_package', {}).items():
        if proto == 'PC-SA' and pcsa():
            continue
        yield from rows


if __name__ == '__main__':
    try:
        # Filter build targets as data; retain options and the default-target token.
        for target in sys.argv[1:]:
            if contains(target.split(':', 1)[0]):
                print('SKIP UNPORTED: ' + target, file=sys.stderr)
            else:
                print(target)
    except (ValueError, OSError) as error:
        sys.exit(str(error))
