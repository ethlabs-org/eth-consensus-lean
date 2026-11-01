"""Record package semantic test coverage; generic controls do not select it."""
import json
import os
from pathlib import Path
from source_layout import Layout
import subprocess
import sys

import unported


def run(root, output):
    if os.environ.get('GATE_NO_BUILD') != '1':
        raise ValueError('package G0 requires the complete build barrier')
    files = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z']).decode().split('\0')
    layout = Layout(root)
    declared = set(layout.source_files())
    modules = sorted(layout.module_of_source(p) for p in files
                     if p in declared and '/Tests/' in p and
                     p.endswith('.lean') and not unported.contains(layout.module_of_source(p)))
    if not modules:
        raise ValueError('package G0 has no active test modules')
    result = subprocess.run(['bash', '-c',
        'set -euo pipefail; source scripts/gate-common.sh; gate_with_slot gate_build --wfail "$@"',
        'package-g0', *modules], cwd=root)
    output.write_text(json.dumps(dict(kind='package-g0',
        evidence='complete --wfail build and mandatory no-build freshness of every active Tests module',
        controls_deferred=False, results=[dict(module=m, rc=result.returncode)
                                                 for m in modules]), sort_keys=True) + '\n')
    return result.returncode


if __name__ == '__main__':
    try:
        sys.exit(run(Path.cwd(), Path(os.environ['GATE_LOG_DIR']) / 'package-g0.json'))
    except (ValueError, OSError) as error:
        sys.exit(str(error))
