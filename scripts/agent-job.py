#!/usr/bin/env python3
"""Opt-in, per-user FIFO for two consensus-lean agent builds (not CI/landings).

Usage: python3 -I scripts/agent-job.py <name> -- <command...>
Delegates to the installed job unchanged. An uncertain launch keeps its reservation;
inspect its UUID job name with jobs-all, /srv/status and systemctl before manual repair.
Never remove a reservation merely because its owner died or its heartbeat is old.
"""
import contextlib
import fcntl
import getpass
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import uuid


class Uncertain(RuntimeError):
    pass


def identity(pid=None):
    pid = os.getpid() if pid is None else pid
    # comm may contain spaces and parentheses; starttime is field 22.
    ticks = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19]
    return {'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
            'pid': pid, 'proc_start_ticks': ticks}


def alive(owner):
    try:
        if owner['boot_id'] != Path('/proc/sys/kernel/random/boot_id').read_text().strip():
            return False
        return identity(owner['pid']) == owner
    except FileNotFoundError:
        return False
    except (OSError, ValueError):
        return None


class Backend:
    def __init__(self):
        self.status_dir = Path('/srv/status')
        self.user = getpass.getuser()

    @staticmethod
    def matches(ticket, unit):
        return re.fullmatch(r'job-consensus-lean-' + re.escape(ticket['job_name']) +
                            r'-\d{8}-\d{6}-[0-9a-f]{4}(?:\.service)?', unit) is not None

    def discover(self, ticket):
        units = set()
        result = subprocess.run(['systemctl', '--user', 'list-units', '--all', '--plain',
                                 '--no-legend', 'job-consensus-lean-*.service'],
                                capture_output=True, text=True, check=True, timeout=10)
        for line in result.stdout.splitlines():
            for word in line.split()[:2]:
                if self.matches(ticket, word):
                    units.add(word.removesuffix('.service'))
        for path in self.status_dir.glob(f'{self.user}.job-consensus-lean-{ticket["job_name"]}-*.json'):
            row = json.loads(path.read_text())
            if (row.get('user') == self.user and row.get('project') == 'consensus-lean'
                    and row.get('name') == ticket['job_name'] and self.matches(ticket, row['unit'])):
                units.add(row['unit'].removesuffix('.service'))
        if len(units) > 1:
            raise Uncertain(f'multiple units for {ticket["job_name"]}: {sorted(units)}')
        return next(iter(units), None)

    def outcome(self, ticket):
        unit = ticket['unit']
        if not unit or not self.matches(ticket, unit):
            raise Uncertain(f'invalid unit for {ticket["job_name"]}')
        result = subprocess.run(['systemctl', '--user', 'show', unit, '--property=LoadState',
                                 '--property=ActiveState', '--property=ExecMainStatus',
                                 '--property=ExecMainCode'], capture_output=True, text=True, timeout=10)
        props = dict(line.split('=', 1) for line in result.stdout.splitlines() if '=' in line)
        if props.get('ActiveState') in ('active', 'activating', 'deactivating', 'reloading'):
            return None
        if props.get('LoadState') == 'loaded' and props.get('ActiveState') in ('inactive', 'failed'):
            code = int(props['ExecMainStatus'])
            return code if props.get('ExecMainCode') == '1' else 128 + code
        if props.get('LoadState') != 'not-found':
            raise Uncertain(f'cannot query exact unit {unit}: {result.stderr.strip()}')
        path = self.status_dir / f'{self.user}.{unit}.json'
        if path.exists():
            row = json.loads(path.read_text())
            if (row.get('unit') == unit and row.get('name') == ticket['job_name']
                    and row.get('user') == self.user and row.get('project') == 'consensus-lean'
                    and row.get('state') in ('done', 'failed', 'stopped') and 'exit' in row):
                return row['exit'] if row['exit'] >= 0 else 128 - row['exit']
        raise Uncertain(f'{unit} collected without terminal status; reservation retained')

    def launch(self, ticket):
        # cwd, environment and command argv pass through unchanged; no shell interpolation.
        return subprocess.Popen(['job', '--mem', '16G', '--cpus', '8', 'consensus-lean',
                                 ticket['job_name'], '--', *ticket['argv']], cwd=ticket['cwd'])

    def stop(self, ticket):
        if not self.matches(ticket, ticket['unit']):
            raise Uncertain('refusing to stop unverified unit')
        subprocess.run(['systemctl', '--user', 'stop', ticket['unit']], check=True, timeout=30)


class Queue:
    def __init__(self, directory, backend):
        self.directory, self.backend = Path(directory), backend
        self.directory.mkdir(parents=True, exist_ok=True, mode=0o700)
        if self.directory.is_symlink() or self.directory.stat().st_uid != os.getuid():
            raise Uncertain('state directory must be owned by this user and not a symlink')
        self.directory.chmod(0o700)

    @contextlib.contextmanager
    def locked(self):
        fd = os.open(self.directory / 'lock', os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        try:
            os.fchmod(fd, 0o600)
            fcntl.flock(fd, fcntl.LOCK_EX)
            path = self.directory / 'queue.json'
            data = json.loads(path.read_text()) if path.exists() else {
                'version': 1, 'next_sequence': 0, 'tickets': []}
            if (data.get('version') != 1 or not isinstance(data.get('next_sequence'), int)
                    or not isinstance(data.get('tickets'), list)):
                raise Uncertain('corrupt queue; manual reconciliation required')
            ids, sequences = set(), set()
            for t in data['tickets']:
                if (t['state'] not in ('queued', 'launching', 'running') or t['id'] in ids
                        or t['sequence'] in sequences or t['sequence'] >= data['next_sequence']):
                    raise Uncertain('corrupt tickets; manual reconciliation required')
                ids.add(t['id'])
                sequences.add(t['sequence'])
            if sum(t['state'] != 'queued' for t in data['tickets']) > 2:
                raise Uncertain('more than two reservations; manual reconciliation required')
            yield data
            temp = self.directory / 'queue.json.tmp'
            with temp.open('w') as out:
                os.chmod(temp, 0o600)
                json.dump(data, out, indent=2)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp, path)
        finally:
            os.close(fd)

    def enqueue(self, name, argv):
        with self.locked() as data:
            token = str(uuid.uuid4())
            ticket = {'id': token, 'sequence': data['next_sequence'],
                      'job_name': name + '-' + token, 'cwd': os.getcwd(), 'argv': argv,
                      'owner': identity(), 'created_at': time.time(), 'heartbeat_at': time.time(),
                      'state': 'queued', 'unit': None}
            data['next_sequence'] += 1
            data['tickets'].append(ticket)
            return token

    def tick(self, token, cancel=False):
        """Reconcile, heartbeat and atomically reserve; never launch under the lock."""
        with self.locked() as data:
            own = None
            for ticket in list(data['tickets']):
                if ticket['id'] == token:
                    own = ticket
                    if ticket['owner'] != identity():
                        raise Uncertain('ticket ownership changed')
                    ticket['heartbeat_at'] = time.time()
                if ticket['state'] == 'queued':
                    live = alive(ticket['owner'])
                    if live is None:
                        print(f'owner uncertain: {ticket["id"]}; retained', file=sys.stderr)
                    if live is False or (ticket is own and cancel):
                        data['tickets'].remove(ticket)
                else:
                    if ticket['unit'] is None:
                        ticket['unit'] = self.backend.discover(ticket)
                    if ticket['unit']:
                        ticket['state'] = 'running'
                        try:
                            result = self.backend.outcome(ticket)
                        except Uncertain as error:
                            print(str(error), file=sys.stderr)
                        else:
                            if result is not None and (ticket is own or alive(ticket['owner']) is False):
                                data['tickets'].remove(ticket)
                                if ticket is own:
                                    return 'done', ticket, result
                    elif alive(ticket['owner']) is not True:
                        print(f'launch ambiguous: {ticket["job_name"]}; manual reconciliation required',
                              file=sys.stderr)
            if own is None:
                raise Uncertain('own ticket missing')
            if own not in data['tickets']:
                return 'cancelled', own, None
            waiting = sorted((t for t in data['tickets'] if t['state'] == 'queued'),
                             key=lambda t: t['sequence'])
            reserved = sum(t['state'] != 'queued' for t in data['tickets'])
            if own['state'] == 'queued' and reserved < 2 and waiting[0] is own:
                own['state'] = 'launching'
                return 'launch', own, None
            return own['state'], own, None


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if (len(argv) < 3 or argv[1] != '--'
            or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', argv[0])):
        print(__doc__, file=sys.stderr)
        return 2
    directory = Path(os.environ.get('XDG_STATE_HOME', str(Path.home() / '.local/state')))
    queue = Queue(directory / 'consensus-lean/agent-build-queue', Backend())
    cancelled = 0

    def on_signal(sig, _):
        nonlocal cancelled
        cancelled = sig

    signal.signal(signal.SIGINT, on_signal)
    signal.signal(signal.SIGTERM, on_signal)
    token = queue.enqueue(argv[0], argv[2:])
    started, launcher, stopped, reported_unit = time.monotonic(), None, False, None
    print(f'ticket {token} queued', flush=True)
    while True:
        state, ticket, result = queue.tick(token, bool(cancelled))
        elapsed = time.monotonic() - started
        if state == 'done':
            print(f'ticket {token} result={result} elapsed={elapsed:.1f}s', flush=True)
            return 128 + cancelled if cancelled else result
        if state == 'cancelled':
            return 128 + cancelled
        if ticket['unit'] and ticket['unit'] != reported_unit:
            reported_unit = ticket['unit']
            print(f'ticket {token} unit={reported_unit} elapsed={elapsed:.1f}s', flush=True)
        if state == 'launch':
            # Recheck cancellation/ownership after the persisted reservation, before spawn.
            with queue.locked() as data:
                own = next(t for t in data['tickets'] if t['id'] == token)
                if own['owner'] != identity() or own['state'] != 'launching':
                    raise Uncertain('launch reservation changed')
                if cancelled:
                    data['tickets'].remove(own)
                    return 128 + cancelled
            print(f'ticket {token} launch wait={elapsed:.1f}s name={ticket["job_name"]}', flush=True)
            launcher = queue.backend.launch(ticket)
        if ticket['unit'] and cancelled and not stopped:
            queue.backend.stop(ticket)
            stopped = True
        if launcher is not None and launcher.poll() is not None and not ticket['unit']:
            # Even a failed launcher may have created a unit; never retry/release on exit alone.
            print(f'launcher exited {launcher.returncode}; awaiting exact unit discovery', file=sys.stderr)
        time.sleep(2)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (Uncertain, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        sys.exit(f'agent-job: {error}; reservation, if any, retained for reconciliation')
