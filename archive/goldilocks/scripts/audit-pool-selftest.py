#!/usr/bin/env python3
"""Exercise the production pool without a Lean build or a claims-audit hook."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import json
import signal
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile
import time
from unittest.mock import patch

from audit_pool import AuditPool, positive_seconds

# Fake audit fixtures must not use the calling FULL gate's persistent log path.
os.environ.pop('GATE_LOG_DIR', None)


def command(body):
    return [sys.executable, '-c', body]


with tempfile.TemporaryDirectory(prefix='audit-pool-control-') as temp:
    pool = AuditPool(Path(temp), 2, timeout=120)
    # Keep passing commands outside the short timeout budget.
    timeout_pool = AuditPool(Path(temp) / 'timeouts', 2, timeout=5)
    pool.run_pool([('valid-reject', command('print("CONTROL"); exit(1)'),
                    {'expect': 'CONTROL'}), ('pass', command('print("PASS")'), {})])
    for label, body, expect in (
        ('missed-reject', 'print("CONTROL")', 'CONTROL'),
        ('wrong-reason', 'print("WRONG"); exit(1)', 'CONTROL'),
        ('signal', 'import os, signal; os.kill(os.getpid(), signal.SIGTERM)', 'CONTROL'),
        ('failure', 'exit(7)', None),
    ):
        previous_twins = set(pool.work.glob('*-passing-twin.rc'))
        try:
            pool.run_pool([(label, command(body), {'expect': expect}),
                           ('passing-twin', command('print("PASS")'), {})])
        except SystemExit as exc:
            expected = 7 if expect is None else (
                f"STOP: negative control {label} did not fail with {expect!r}")
            assert exc.code == expected, exc
            new_twins = set(pool.work.glob('*-passing-twin.rc')) - previous_twins
            assert len(new_twins) == 1, (label, new_twins)
            assert next(iter(new_twins)).read_text().strip() == '0', label
            print(f'CONTROL pool {label}: PASS')
        else:
            raise AssertionError(f'pool accepted {label}')
    try:
        timeout_pool.run_pool([('timeout', command(
            'import time; print("CONTROL", flush=True); time.sleep(120)'), {'expect': 'CONTROL'})])
    except SystemExit as exc:
        assert exc.code == "STOP: negative control timeout did not fail with 'CONTROL'", exc
    else:
        raise AssertionError('pool accepted timeout')
    assert (timeout_pool.work / '01-timeout.rc').read_text().strip() == '124'
    assert 'CONTROL' in (timeout_pool.work / '01-timeout.log').read_text()
    print('CONTROL pool timeout: PASS')
    pidfile = Path(temp) / 'child.pid'
    child_body = ('import os, signal, time; from pathlib import Path; '
                  'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                  f'Path({str(pidfile)!r}).write_text(str(os.getpid())); time.sleep(120)')
    body = ('import subprocess, sys, time; '
            f'subprocess.Popen({command(child_body)!r}); time.sleep(120)')
    with ThreadPoolExecutor(max_workers=1) as runner:
        pending = runner.submit(timeout_pool.run, 'timeout-child', command(body))
        deadline = time.monotonic() + 120
        while not pidfile.exists() or not pidfile.stat().st_size:
            assert not pending.done(), 'timeout child exited before publishing its PID'
            assert time.monotonic() < deadline, 'timeout child did not publish its PID'
            time.sleep(0.01)
        pid = int(pidfile.read_text())
        try:
            pending.result()
        except SystemExit as exc:
            assert exc.code == 124, exc
        else:
            raise AssertionError('timeout child completed without a timeout')
    deadline = time.monotonic() + 5
    while True:
        try:
            os.kill(int(pid), 0)
        except ProcessLookupError:
            break
        assert time.monotonic() < deadline, f'child still exists: {pid}'
        time.sleep(0.01)
    print('CONTROL timeout terminates descendants: PASS')
    # A gate fail-fast TERM must stop the new process groups too.
    pidfile.unlink()
    driver = ("from audit_pool import AuditPool; from pathlib import Path; "
              f"p = AuditPool(Path({str(Path(temp) / 'signal')!r}), 2, timeout=120); "
              f"p.run('child', {command(body)!r})")
    child = subprocess.Popen(command(driver), cwd=Path(__file__).resolve().parent,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    try:
        deadline = time.monotonic() + 120
        while not pidfile.exists() or not pidfile.stat().st_size:
            assert child.poll() is None and time.monotonic() < deadline
            time.sleep(0.01)
        os.kill(child.pid, signal.SIGTERM)
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 143, (child.returncode, output)
        pid = int(pidfile.read_text())
        deadline = time.monotonic() + 5
        while True:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            assert time.monotonic() < deadline, f'signal child still exists: {pid}'
            time.sleep(0.01)
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
    print('CONTROL pool TERM terminates descendants: PASS')
    for value in ('0', '-1', '1.5', 'bad', ''):
        try:
            positive_seconds(value)
        except ValueError:
            pass
        else:
            raise AssertionError(value)
    print('CONTROL timeout inputs: PASS')
    with patch.dict(os.environ, AUDIT_TIMING='1'):
        timed = AuditPool(Path(temp) / 'timed', 1, timeout=120)
        timed.run('timer', command('print("PASS")'))
        assert list(timed.work.glob('*.time'))
        with patch('audit_pool.subprocess.run',
                   return_value=subprocess.CompletedProcess([], 1)):
            try:
                AuditPool(Path(temp) / 'bad-timer', 1)
            except SystemExit as exc:
                assert 'TIMING PREFLIGHT FAILED' in str(exc)
            else:
                raise AssertionError('unsupported timer accepted')
    print('CONTROL timer preflight and output: PASS')

    retained = Path(temp) / 'gate-logs'
    with patch.dict(os.environ, GATE_LOG_DIR=str(retained), GATE_STEP='claims',
                    AUDIT_TIMING='1'):
        measured = AuditPool(Path(temp), 1, temp_prefix='retained.')
        scratch = measured.work
        output = measured.run('json', command(
            'import sys; print("{\\"ok\\": true}"); print("diagnostic", file=sys.stderr)'))
        measured.cleanup()
        assert not scratch.exists()
        path = retained / 'substeps/claims/01-json'
        assert json.loads(path.with_suffix('.stdout').read_text()) == {'ok': True}
        assert path.with_suffix('.stderr').read_text().strip() == 'diagnostic'
        assert 'diagnostic' in output
        record = json.loads(path.with_suffix('.json').read_text())
        assert record['queued'] <= record['start'] <= record['end']
        assert record['rc'] == 0 and record['cpu_user_s'] is not None
        assert record['peak_rss_bytes'] is not None
    print('CONTROL retained timing and separate JSON/stderr after cleanup: PASS')
    with patch.dict(os.environ, AUDIT_TIMING='0'):
        spawning = AuditPool(Path(temp) / 'spawn-failure', 1)
        try:
            spawning.run('missing-command', ['/nonexistent/audit-command'])
        except FileNotFoundError:
            record = json.loads(next(spawning.work.glob('*-missing-command.json')).read_text())
            assert record['rc'] == 127 and record['end'] >= record['start']
        else:
            raise AssertionError('missing command accepted')
    print('CONTROL spawn failure has a completed timing record: PASS')

    # A live slot owner must not consume a waiting command's one-second budget.
    repo = Path(__file__).resolve().parents[1]
    slots = Path(temp) / 'wait-slots'
    owner = slots / 'slot.1' / f'owner.{os.getpid()}'
    owner.mkdir(parents=True)
    wait_env = dict(os.environ, GATE_SLOTS='1', GATE_SLOT_DIR=str(slots),
                    GATE_SLOT_HELD='0')
    waiting = AuditPool(Path(temp) / 'waiting', 1, timeout=1,
                        slot_script=repo / 'scripts/gate-common.sh')
    path = waiting.reserve_log('valid-after-wait')
    with ThreadPoolExecutor(max_workers=1) as runner:
        pending = runner.submit(waiting.execute, path,
                                command('import time; time.sleep(0.6); print("PASS")'),
                                env=wait_env)
        try:
            time.sleep(1.5)
            assert not pending.done(), 'command used its budget before slot acquisition'
            assert owner.is_dir(), 'waiting command removed a live owner'
        finally:
            owner.rmdir()
            owner.parent.rmdir()
        assert pending.result(timeout=10) == 0, path.read_text()
    assert 'PASS' in path.read_text()
    assert not list(slots.glob('slot.*'))
    assert not list(waiting.work.glob('*.started'))
    print('CONTROL one-second budget starts after live slot owner releases: PASS')
    try:
        waiting.run('slot-timeout', command(
            'import time; print("CONTROL", flush=True); time.sleep(120)'),
            expect='CONTROL', env=wait_env)
    except SystemExit as exc:
        assert exc.code == "STOP: negative control slot-timeout did not fail with 'CONTROL'"
    else:
        raise AssertionError('pool accepted slotted timeout')
    assert (waiting.work / '02-slot-timeout.rc').read_text().strip() == '124'
    assert not list(slots.glob('slot.*'))
    assert not list(waiting.work.glob('*.started'))
    print('CONTROL slotted timeout remains an invalid negative rejection: PASS')

    # TERM must also cancel a command which has not acquired its slot.
    owner.mkdir(parents=True)
    marker = Path(temp) / 'wait-command-started'
    waiting_command = command(f'from pathlib import Path; Path({str(marker)!r}).touch()')
    driver = ("from audit_pool import AuditPool; from pathlib import Path; "
              f"p = AuditPool(Path({str(Path(temp) / 'wait-term')!r}), 1, timeout=1, "
              f"slot_script=Path({str(repo / 'scripts/gate-common.sh')!r})); "
              f"p.run('wait', {waiting_command!r})")
    child = subprocess.Popen(command(driver), cwd=repo / 'scripts', env=wait_env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    try:
        time.sleep(1.5)
        assert child.poll() is None, 'waiting driver expired before acquiring its slot'
        child.terminate()
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 143, (child.returncode, output)
        assert not marker.exists(), 'cancelled waiting command started'
        assert owner.is_dir(), 'cancellation removed a live owner'
    finally:
        if child.poll() is None:
            child.terminate()
            child.wait(timeout=10)
        owner.rmdir()
        owner.parent.rmdir()
    print('CONTROL TERM cancels slot wait and preserves live owner: PASS')

    # Run the real claims entry point. Stop its first Lake call without Lean.
    repo = Path(__file__).resolve().parents[1]
    claims_repo = Path(temp) / 'claims'
    shutil.copytree(repo, claims_repo,
                    ignore=shutil.ignore_patterns('.lake', '.git', 'claude-files', '__pycache__'))
    bindir = Path(temp) / 'bin'
    bindir.mkdir()
    lake = bindir / 'lake'
    # The pre-Lake audits get 20 s; the fake Lake outlasts that budget.
    lake.write_text('#!' + sys.executable + '\n'
                    'from pathlib import Path\nimport os, time\n'
                    'Path(os.environ["CLAIMS_READY"]).touch()\ntime.sleep(120)\n')
    lake.chmod(0o755)
    for mode, timeout, rc in (('TERM', '120', 143), ('timeout', '20', 124)):
        ready = Path(temp) / (mode + '.ready')
        log = Path(temp) / (mode + '.log')
        env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'],
                   CLAIMS_READY=str(ready), AUDIT_TIMEOUT=timeout, SOURCE_ONLY='0', NEG='0',
                   GATE_SLOT_DIR=str(claims_repo / '.lake/test-slots'), GATE_SLOT_HELD='0')
        with log.open('w') as output:
            child = subprocess.Popen(['bash', 'scripts/check-fgsa-claims.sh'], cwd=claims_repo,
                                     env=env, stdout=output, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 120
            while not ready.exists():
                assert child.poll() is None, log.read_text()
                assert time.monotonic() < deadline, log.read_text()
                time.sleep(0.01)
            line = next(line for line in log.read_text().splitlines()
                        if line.startswith('FGSA claims temporary audit logs: '))
            work = Path(line.split(': ', 1)[1])
            assert work.is_dir() and list(work.iterdir()), work
            if mode == 'TERM':
                child.terminate()
            assert child.wait(timeout=int(timeout) + 10) == rc, log.read_text()
            assert not work.exists(), f'claims fixtures remain after {mode}: {work}'
            assert not (claims_repo / '.lake/gate-build.lock.d').exists()
            assert not list((claims_repo / '.lake/test-slots').glob('slot.*'))
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait(timeout=10)
        print(f'CONTROL claims directory gone after {mode} (rc {rc}): PASS')

    # Deliver TERM in the allocation/store gap. The stored path must still be removed.
    marker = Path(temp) / 'allocated'
    driver = f'''
import os, signal, tempfile
from pathlib import Path
from unittest.mock import patch
from audit_pool import AuditPool
allocate = tempfile.mkdtemp
def interrupted_allocation(*args, **kwargs):
    assert signal.getsignal(signal.SIGTERM).__self__.__class__ is AuditPool
    path = allocate(*args, **kwargs)
    Path({str(marker)!r}).write_text(path)
    os.kill(os.getpid(), signal.SIGTERM)
    return path
with patch('audit_pool.tempfile.mkdtemp', interrupted_allocation):
    AuditPool({temp!r}, 1, temp_prefix='allocation-control.')
'''
    result = subprocess.run(command(driver), cwd=repo / 'scripts',
                            capture_output=True, text=True)
    assert result.returncode == 143, result
    assert not Path(marker.read_text()).exists()
    print('CONTROL cleanup installed before allocation; pending TERM removes directory: PASS')
