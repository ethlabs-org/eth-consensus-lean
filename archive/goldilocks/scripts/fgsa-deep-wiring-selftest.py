#!/usr/bin/env python3
"""Test the real dispatch assertions without a Lean process."""
import os
from pathlib import Path
import runpy
import tempfile

REPO = Path(__file__).resolve().parents[1]
os.chdir(REPO)
wiring = runpy.run_path('scripts/fgsa-deep-controls.py')['check_wiring']
with tempfile.TemporaryDirectory(prefix='fgsa-wiring-') as scratch:
    root = Path(scratch)
    (root / 'scripts').mkdir()
    paths = ('scripts/gate.sh', 'scripts/check-fgsa-manifest.sh')
    original = {p: (REPO / p).read_text() for p in paths}
    for p, text in original.items():
        (root / p).write_text(text)
    wiring(root)
    for label, path, before, after in (
        ('missing dispatch', paths[0],
         'fgsa-manifest) step "$1" gate_measure_command bash scripts/check-fgsa-manifest.sh ;;', ''),
        ('missing group member', paths[0], '  check-build\n', '\n'),
        ('shallow after NEG exit', paths[1], '--scope fgsa --check', 'shallow-disabled'),
        ('deep after NEG exit', paths[1], '--scope fgsa --deep --check', 'deep-disabled'),
        ('legacy after NEG exit', paths[1], '--scope legacy --check', 'legacy-disabled'),
    ):
        assert original[path].count(before) == 1, (label, before)
        text = original[path].replace(before, after)
        if 'after NEG' in label:
            text += '\n' + before + '\n'
        (root / path).write_text(text)
        try:
            wiring(root)
        except (AssertionError, ValueError):
            print(f'CONTROL wiring {label}: PASS (rejected)')
        else:
            raise AssertionError('wiring accepted ' + label)
        (root / path).write_text(original[path])
print('fgsa-deep-wiring-selftest: PASS')
