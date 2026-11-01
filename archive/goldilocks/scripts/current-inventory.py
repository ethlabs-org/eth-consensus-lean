#!/usr/bin/env python3
"""Independent source coverage for compiled public audit inventories."""
import importlib.util
from pathlib import Path
import sys
import re
import check_common as C

spec = importlib.util.spec_from_file_location('snapshot', 'scripts/api-snapshot.py')
snapshot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(snapshot)


def public_lines(text):
    # Module files default to private. Sections and namespaces carry visibility.
    public = not bool(re.search(r'^\s*module\s*$', text, re.M))
    stack, result = [], []
    for line in text.splitlines():
        result.append(public or bool(re.match(r'^\s*(?:@\[[^]]*\]\s*)?public\b', line)))
        namespace = C.NAMESPACE.match(line)
        section = C.SECTION.match(line)
        end = C.END.match(line)
        if namespace:
            stack.append((namespace[1], public))
        elif section:
            stack.append((section[1], public))
            if re.search(r'\bpublic\b', line):
                public = True
            elif re.search(r'\bprivate\b', line):
                public = False
        elif end and stack:
            name = end[1]
            if not name or stack[-1][0] == name:
                _, public = stack.pop()
    return result


def source_names(scope):
    libraries = set(snapshot.SCOPES[scope])
    found = set()
    for lf in C.library_files():
        if lf.lib not in libraries:
            continue
        visible = public_lines(lf.stripped)
        for decl in C.declarations(lf):
            if decl.name and not decl.private and visible[decl.line - 1]:
                found.add(decl.full)
    if not found:
        raise ValueError('EMPTY SOURCE INVENTORY: ' + scope)
    return found


def check_source(scope, expected):
    found = source_names(scope)
    missing = sorted(found - set(expected))
    if missing:
        raise ValueError(f'{scope} SOURCE INVENTORY UNLISTED: {missing}')
    print(f'{scope} source inventory: PASS ({len(found)} declarations)')


if __name__ == '__main__':
    from check_inventory import read_names
    try:
        path = Path(sys.argv[2])
        expected = (snapshot.deep.read_baseline(path)['entries'] if path.suffix == '.json'
                    else read_names(path))
        check_source(sys.argv[1], expected)
    except (ValueError, OSError) as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)
