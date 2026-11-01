#!/usr/bin/env python3
"""Disposable FIFO/lifecycle fixtures; never launch or stop shared systemd units."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('agent_job', Path(__file__).with_name('agent-job.py'))
agent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(agent)


class FakeBackend:
    def __init__(self):
        self.units, self.results = {}, {}

    def discover(self, ticket):
        return self.units.get(ticket['id'])

    def outcome(self, ticket):
        return self.results.get(ticket['unit'])


class Admission(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.backend = FakeBackend()
        self.queue = agent.Queue(Path(self.temp.name) / 'queue', self.backend)

    def enqueue(self, name):
        return self.queue.enqueue(name, ['printf', '%s', 'asymmetric input'])

    def edit(self, token, **fields):
        with self.queue.locked() as data:
            next(t for t in data['tickets'] if t['id'] == token).update(fields)

    def tickets(self):
        with self.queue.locked() as data:
            return data['tickets']

    def dead(self, token):
        self.edit(token, owner={**agent.identity(), 'proc_start_ticks': 'not-current'})

    def test_fifo_four_arrivals_two_slots_and_launch_reservation(self):
        a, b, c, d = [self.enqueue(n) for n in ['z-last-name', 'a-first-name', 'middle', 'fourth']]
        self.assertEqual(self.queue.tick(d)[0], 'queued')
        self.assertEqual(self.queue.tick(a)[0], 'launch')
        self.assertEqual(self.queue.tick(c)[0], 'queued')
        self.assertEqual(self.queue.tick(b)[0], 'launch')
        self.assertEqual(self.queue.tick(c)[0], 'queued')
        self.backend.units[a] = 'unit-a'
        self.backend.units[b] = 'unit-b'
        self.assertEqual(self.queue.tick(a)[0], 'running')
        self.backend.results['unit-b'] = 7
        self.assertEqual(self.queue.tick(b), ('done', unittest.mock.ANY, 7))
        self.assertEqual(self.queue.tick(d)[0], 'queued')
        self.assertEqual(self.queue.tick(c)[0], 'launch')
        self.assertEqual(self.queue.tick(d)[0], 'queued')
        self.assertEqual(sum(t['state'] != 'queued' for t in self.tickets()), 2)

    def test_dead_queued_pid_reuse_and_old_live_heartbeat(self):
        a, b = self.enqueue('dead'), self.enqueue('live')
        self.edit(a, heartbeat_at=0)
        self.dead(a)
        self.edit(b, heartbeat_at=0)
        self.assertEqual(self.queue.tick(b)[0], 'launch')
        self.assertNotIn(a, [t['id'] for t in self.tickets()])
        self.assertTrue(agent.alive(agent.identity()))
        self.assertFalse(agent.alive({**agent.identity(), 'boot_id': 'old-boot'}))

    def test_queued_cancellation(self):
        a, b = self.enqueue('cancel'), self.enqueue('next')
        self.assertEqual(self.queue.tick(a, cancel=True)[0], 'cancelled')
        self.assertEqual(self.queue.tick(b)[0], 'launch')

    def test_crash_before_launch_fails_closed_and_after_launch_recovers(self):
        a, b, c = [self.enqueue(n) for n in ['crash', 'second', 'third']]
        self.queue.tick(a)
        self.dead(a)
        self.queue.tick(b)
        self.assertEqual(self.queue.tick(c)[0], 'queued')
        self.assertEqual(self.tickets()[0]['state'], 'launching')
        self.backend.units[a] = 'surviving-unit'
        self.queue.tick(c)
        self.assertEqual(self.tickets()[0]['state'], 'running')
        self.edit(a, heartbeat_at=-1000000)
        self.assertEqual(self.queue.tick(c)[0], 'queued')
        self.backend.results['surviving-unit'] = 0
        self.assertEqual(self.queue.tick(c)[0], 'launch')

    def test_running_cancel_keeps_slot_until_terminal(self):
        a = self.enqueue('running')
        self.queue.tick(a)
        self.backend.units[a] = 'own-unit'
        self.assertEqual(self.queue.tick(a, cancel=True)[0], 'running')
        self.assertEqual(len(self.tickets()), 1)
        self.backend.results['own-unit'] = 143
        self.assertEqual(self.queue.tick(a, cancel=True)[2], 143)

    def test_corrupt_state_not_reset_and_permissions(self):
        self.enqueue('one')
        self.assertEqual(self.queue.directory.stat().st_mode & 0o777, 0o700)
        self.assertEqual((self.queue.directory / 'lock').stat().st_mode & 0o777, 0o600)
        path = self.queue.directory / 'queue.json'
        path.write_text('{corrupt')
        with self.assertRaises(ValueError):
            self.queue.tick('anything')
        self.assertEqual(path.read_text(), '{corrupt')

    def test_concurrent_enqueue_sequence_and_admission(self):
        # Actual separate processes contend on flock, not a mocked mutex.
        children = []
        for i in range(8):
            pid = os.fork()
            if pid == 0:
                try:
                    self.queue.enqueue(str(i), ['true'])
                finally:
                    os._exit(0)
            children.append(pid)
        for pid in children:
            self.assertEqual(os.waitpid(pid, 0)[1], 0)
        tickets = self.tickets()
        self.assertEqual(sorted(t['sequence'] for t in tickets), list(range(8)))
        self.assertEqual(len({t['id'] for t in tickets}), 8)

    def test_concurrent_reservations_never_exceed_two(self):
        tokens = [self.enqueue(str(i)) for i in range(6)]
        children = []
        for token in tokens:
            pid = os.fork()
            if pid == 0:
                try:
                    # Keep ownership live in the parent while competing for admission.
                    with patch.object(agent, 'identity', return_value=agent.identity(os.getppid())):
                        for _ in range(10):
                            self.queue.tick(token)
                            time.sleep(0.005)
                    os._exit(0)
                except BaseException:
                    os._exit(1)
            children.append(pid)
        for pid in children:
            self.assertEqual(os.waitpid(pid, 0)[1], 0)
        tickets = self.tickets()
        reserved = [t['sequence'] for t in tickets if t['state'] == 'launching']
        self.assertEqual(reserved, [0, 1])

    def test_main_running_signals_stop_only_own_and_return_signal_code(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(sig=sig):
                handlers = {}
                backend = FakeBackend()
                backend.stop = unittest.mock.Mock()

                def launch(ticket):
                    backend.units[ticket['id']] = 'own-unit'
                    return unittest.mock.Mock(poll=lambda: 0, returncode=0)

                backend.launch = launch
                backend.stop.side_effect = lambda t: backend.results.update({'own-unit': 143})
                sleeps = []

                def sleep(_):
                    sleeps.append(1)
                    if len(sleeps) == 1:
                        handlers[sig](sig, None)
                    self.assertLess(len(sleeps), 5)

                with patch.object(agent, 'Backend', return_value=backend), \
                        patch.object(agent.signal, 'signal', side_effect=lambda s, f: handlers.update({s: f})), \
                        patch.object(agent.time, 'sleep', side_effect=sleep), \
                        patch.dict(os.environ, {'XDG_STATE_HOME': self.temp.name}):
                    self.assertEqual(agent.main(['signal-test', '--', 'true']), 128 + sig)
                backend.stop.assert_called_once()
                self.assertEqual(backend.stop.call_args.args[0]['unit'], 'own-unit')

    def test_uncertain_owner_and_old_live_owner_are_not_evicted(self):
        a, b = self.enqueue('first'), self.enqueue('second')
        self.edit(a, heartbeat_at=0)
        with patch.object(agent, 'alive', return_value=None):
            self.assertEqual(self.queue.tick(b)[0], 'queued')
        self.assertEqual(self.queue.tick(b)[0], 'queued')
        self.assertEqual(len(self.tickets()), 2)


class SystemdProtocol(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.backend = agent.Backend()
        self.backend.status_dir = Path(self.temp.name)
        self.ticket = {'id': 'test', 'job_name': 'asymmetric-uuid', 'cwd': '/tmp',
                       'argv': ['printf', '%s', 'literal ; input'],
                       'unit': 'job-consensus-lean-asymmetric-uuid-20261101-123456-abcd'}

    def response(self, props, rc=0):
        return subprocess.CompletedProcess([], rc, props, '')

    def test_collected_terminal_and_stale_running_status(self):
        row = {'unit': self.ticket['unit'], 'name': self.ticket['job_name'],
               'user': self.backend.user, 'project': 'consensus-lean', 'state': 'running'}
        path = self.backend.status_dir / f'{self.backend.user}.{self.ticket["unit"]}.json'
        path.write_text(json.dumps(row))
        with patch.object(agent.subprocess, 'run', return_value=self.response('LoadState=not-found\n', 1)):
            with self.assertRaises(agent.Uncertain):
                self.backend.outcome(self.ticket)
            row.update(state='done', exit=17)
            path.write_text(json.dumps(row))
            self.assertEqual(self.backend.outcome(self.ticket), 17)
        with patch.object(agent.subprocess, 'run', return_value=self.response('LoadState=loaded\nActiveState=active\n')):
            self.assertIsNone(self.backend.outcome(self.ticket))

    def test_discovery_and_stop_only_exact_ticket_not_runner_or_ci(self):
        unit = self.ticket['unit']
        listing = f'{unit}.service loaded active running\njob-consensus-lean-sol-landing-20261101-123456-abcd.service loaded active running\n'
        with patch.object(agent.subprocess, 'run', return_value=self.response(listing)):
            self.assertEqual(self.backend.discover(self.ticket), unit)
        with patch.object(agent.subprocess, 'run') as run:
            self.backend.stop(self.ticket)
            run.assert_called_once_with(['systemctl', '--user', 'stop', unit], check=True, timeout=30)
            with self.assertRaises(agent.Uncertain):
                self.backend.stop({**self.ticket, 'unit': 'job-consensus-lean-orb-ci.service'})
            self.assertEqual(run.call_count, 1)

    def test_delegate_fixed_resources_cwd_and_literal_argv(self):
        with patch.object(agent.subprocess, 'Popen') as popen:
            self.backend.launch(self.ticket)
            popen.assert_called_once_with(['job', '--mem', '16G', '--cpus', '8', 'consensus-lean',
                self.ticket['job_name'], '--', *self.ticket['argv']], cwd='/tmp')


if __name__ == '__main__':
    unittest.main()
