"""Read declaration inventories as data. Never execute an inventory."""
import ast
from pathlib import Path
import re
import sys


def parse_names(text, label):
    try:
        names = ast.literal_eval(text)
    except (ValueError, SyntaxError) as exc:
        raise ValueError(f'{label}: invalid inventory') from exc
    if not isinstance(names, tuple) or not names or not all(
            isinstance(n, str) and re.fullmatch(r"[^\W\d][\w'.?!]*", n)
            for n in names):
        raise ValueError(f'{label}: expected a nonempty tuple of declaration names')
    if len(names) != len(set(names)):
        raise ValueError(f'{label}: duplicate inventory name')
    return names


def read_names(path):
    return parse_names(Path(path).read_text(), path)


if __name__ == '__main__':
    print('\n'.join(read_names(sys.argv[1])))
