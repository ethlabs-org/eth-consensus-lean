#!/usr/bin/env python3
"""Select active library modules with compiled artifacts for default shake checks."""
from importlib import import_module
from pathlib import Path
import sys

import check_common as C

deferred = import_module('check-sleep-scopes').deferred


def selection(files, build):
    modules = []
    for file in files:
        if deferred(file.module):
            continue
        olean = build / (file.module.replace('.', '/') + '.olean')
        if olean.is_file():
            modules.append(file.module)
        else:
            print('shake-report: SKIPPED (no .olean; not built by any target): ' + file.module,
                  file=sys.stderr)
    return modules


if __name__ == '__main__':
    print('\n'.join(selection(C.library_files(), Path('.lake/build/lib/lean'))))
