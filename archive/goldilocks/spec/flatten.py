#!/usr/bin/env python3
"""Flatten a spec: replace each line '\\input{shared/<name>}' by the file shared/<name>.tex.
Usage: flatten.py <spec.tex>  -> writes the flattened text to stdout.
Pins hash the flattened text, so a split does not change a pin."""
import re, sys, pathlib
src = pathlib.Path(sys.argv[1])
out = []
for line in src.read_text().splitlines(keepends=True):
    m = re.fullmatch(r'\\input\{(shared/[A-Za-z0-9_-]+)\}\n', line)
    out.append((src.parent / (m.group(1) + '.tex')).read_text() if m else line)
sys.stdout.write(''.join(out))
