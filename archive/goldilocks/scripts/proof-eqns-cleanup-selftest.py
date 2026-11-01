#!/usr/bin/env python3
"""Send TERM during proof-control copy and checker calls, without Lean."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

REPO = Path(__file__).resolve().parents[1]
FAKE = r"""
import json, os, signal, subprocess, sys, time
from pathlib import Path
args = sys.argv[1:]
root = next(Path('.lake').glob('proof-eqns-neg.*'))
if Path(sys.argv[0]).name == 'rsync':
    (root / 'repo/copied-source').write_text('partial copy\n')
    if os.environ['TEST_PHASE'] != 'copy':
        sys.exit(0)
elif '--run' not in args:
    sys.exit(0)
child_code = '''
import os, signal, sys, time
from pathlib import Path
def term(_sig, _frame):
    Path(sys.argv[2]).write_text(str(Path(sys.argv[1]).exists()))
signal.signal(signal.SIGTERM, term)
Path(sys.argv[3]).touch()
time.sleep(120)
'''
child = subprocess.Popen([sys.executable, '-c', child_code, str(root),
                          os.environ['TEST_NOTE'], os.environ['TEST_CHILD_READY']])
deadline = time.monotonic() + 10
while not Path(os.environ['TEST_CHILD_READY']).exists():
    assert child.poll() is None and time.monotonic() < deadline
    time.sleep(0.01)
Path(os.environ['TEST_READY']).write_text(json.dumps(
    dict(parent=os.getpid(), child=child.pid, root=str(root.resolve()))))
time.sleep(120)
"""


def gone(pid):
    deadline = time.monotonic() + 5
    while True:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return
        assert time.monotonic() < deadline, f'child still exists: {pid}'
        time.sleep(0.01)


with tempfile.TemporaryDirectory(prefix='proof-cleanup-') as scratch:
    root = Path(scratch)
    for phase in ('copy', 'checker'):
        for target in ('parent', 'group'):
            case = root / (phase + '-' + target)
            scripts = case / 'scripts'
            scripts.mkdir(parents=True)
            (case / '.lake').mkdir()
            for name in ('check-proof-eqns-controls.py', 'audit_pool.py', 'gate_timing.py'):
                shutil.copy2(REPO / 'scripts' / name, scripts / name)
            bindir = case / 'bin'
            bindir.mkdir()
            for name in ('lake', 'rsync'):
                path = bindir / name
                path.write_text('#!' + sys.executable + '\n' + FAKE)
                path.chmod(0o755)
            ready, note = case / 'ready.json', case / 'term-note'
            env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'],
                       PYTHONDONTWRITEBYTECODE='1', TEST_PHASE=phase,
                       TEST_READY=str(ready), TEST_NOTE=str(note),
                       TEST_CHILD_READY=str(case / 'child-ready'))
            proc = subprocess.Popen([sys.executable, '-B',
                                     str(scripts / 'check-proof-eqns-controls.py')],
                                    env=env, start_new_session=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            data = None
            try:
                deadline = time.monotonic() + 10
                while not ready.exists():
                    assert proc.poll() is None, proc.communicate()[0]
                    assert time.monotonic() < deadline, 'copy/checker did not start'
                    time.sleep(0.01)
                data = json.loads(ready.read_text())
                copy = Path(data['root'])
                assert (copy / 'repo/copied-source').is_file()
                if phase == 'checker':
                    assert (copy / 'repo/AvailableChainCoverageControl').is_symlink()
                if target == 'group':
                    os.killpg(proc.pid, signal.SIGTERM)
                else:
                    proc.terminate()
                output, _ = proc.communicate(timeout=10)
                assert proc.returncode == 143, (proc.returncode, output)
                # The TERM-resistant child must stop before its inputs are removed.
                assert note.read_text() == 'True', 'source copy removed before child stop'
                gone(data['parent'])
                gone(data['child'])
                assert not copy.exists(), f'proof fixture remains: {copy}'
                assert not list((case / '.lake').glob('proof-eqns-neg.*'))
            finally:
                if proc.poll() is None:
                    proc.kill()
                    proc.wait()
                if data is not None:
                    try:
                        os.killpg(data['parent'], signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            print(f'CONTROL proof TERM during {phase} ({target}): children/copy gone: PASS')
print('proof-eqns-cleanup-selftest: PASS')
