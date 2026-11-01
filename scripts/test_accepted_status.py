"""Regression tests for status selection (the dependency audit remains authoritative)."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('status', Path(__file__).with_name('accepted-status.py'))
status = importlib.util.module_from_spec(spec)
spec.loader.exec_module(status)


class StatusTests(unittest.TestCase):
    def test_sleepy_regeneration_distinguishes_body_and_type_dependency(self):
        prefix = 'Consensus.Goldilocks.Refinement.'
        names = ['accepted_heal', 'sleepy_query_sync', 'sleepy_safety_inputs',
                 'simTrace_vote_forwarded']
        source = 'namespace ' + prefix[:-1] + '\n' + '\n'.join(
            'theorem ' + n + ' : True := by ' +
            ('sorry' if n == 'accepted_heal' else 'trivial') for n in names)
        records = [{'declaration': prefix + n, 'dependencies': deps}
                   for n, deps in [
                       ('accepted', [prefix + n for n in names]),
                       ('accepted_heal', ['sorryAx']),
                       ('sleepy_query_sync', [prefix + 'accepted_heal']),
                       ('sleepy_safety_inputs', [prefix + 'accepted_heal']),
                       ('simTrace_vote_forwarded', [])]]

        def run(*args):
            if args[:2] == ('git', 'rev-parse'):
                return 'fixture-pin\n'
            if args[:2] == ('git', 'ls-tree'):
                return '100644 blob fixture\t' + str(file) + '\n'
            if args[:2] == ('git', 'cat-file'):
                return source.replace('trivial', 'sorry')
            if args[:2] == ('git', 'rev-list') or args[:3] == ('lake', 'env', 'lean'):
                return ''
            if args[:3] == ('lake', 'exe', 'spec-surface'):
                return '\n'.join(json.dumps(r) for r in records)
            self.fail(f'Unexpected command: {args}')

        cwd = os.getcwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                file = Path('ConsensusLean/Instances/Goldilocks/Lemmas/Fixture.lean')
                file.parent.mkdir(parents=True)
                file.write_text(source)
                ledger = Path('docs/accepted-status.json')
                ledger.parent.mkdir()
                ledger.write_text(json.dumps({'rows': [
                    {'name': prefix + n, 'status': 'paper-open (research)',
                     'obstruction': '#128 stale', 'evidence': 'stale',
                     'derisk-verdict': 'complete', 'adversarial-pass-done': 'y'}
                    for n in names]}))
                with patch.object(status, 'run', side_effect=run), \
                        patch.object(status.subprocess, 'run'), \
                        patch('sys.argv', ['accepted-status.py']):
                    status.main()
                rows = {r['name']: r for r in json.loads(ledger.read_text())['rows']}
                for n in names[1:3]:
                    r = rows[prefix + n]
                    self.assertFalse(r['direct_sorry'])
                    self.assertEqual(r['lean-status'], 'sorry-dependent')
                    self.assertEqual(r['status'], 'unknown')
                    self.assertEqual(r['blocked-by'], [prefix + 'accepted_heal'])
                    self.assertIn('Body proved', r['evidence'])
                    self.assertIn('K S A', r['evidence'])
                    self.assertNotIn('obstruction', r)
                    self.assertEqual(r['derisk-verdict'], 'complete')
                self.assertEqual(rows[prefix + names[3]]['status'], 'lean-proved')
                self.assertTrue(rows[prefix + names[0]]['direct_sorry'])
            finally:
                os.chdir(cwd)

    def test_card_repositories_preserve_mixed_pins(self):
        archive = {'card-path': 'old.md', 'card-commit': 'old-pin'}
        team = {'card-path': 'new.md', 'card-commit': 'new-pin',
                'card-repo': 'ethlabs-org/workbench'}
        shared = {'path': 'shared.md', 'commit': 'shared-pin'}
        cores = {'path': 'cores.md', 'commit': 'cores-pin',
                 'card-repo': 'ethlabs-org/workbench'}
        document = {'audit_commit': 'audit-pin', 'rows': [archive, team, {}],
                    'shared-cards': [shared], 'research-cores': cores}
        status.card_repositories(document)
        self.assertEqual(archive, {'card-path': 'old.md', 'card-commit': 'old-pin',
                                  'card-repo': 'fradamt-agent/workbench'})
        self.assertEqual(team['card-repo'], 'ethlabs-org/workbench')
        self.assertIsNone(document['rows'][2]['card-repo'])
        self.assertEqual(shared['card-repo'], 'fradamt-agent/workbench')
        self.assertEqual(cores['card-repo'], 'ethlabs-org/workbench')
        self.assertEqual(document['audit_commit'], 'audit-pin')

    def test_comments_are_not_proof_holes(self):
        source = '''namespace Consensus.Test
/- sorry /- nested -/ still a comment -/
theorem closed : True := by trivial -- sorry
private theorem openLeaf : True := by
  sorry
theorem later : True := by trivial
'''
        self.assertEqual(status.declarations(source), [
            ('Consensus.Test.closed', 3, False),
            ('Consensus.Test.openLeaf', 4, True),
            ('Consensus.Test.later', 6, False)])

    def test_closure_keeps_type_edges_and_handles_cycles(self):
        edges = {'root': ['body', 'type'], 'body': ['root'], 'type': ['leaf'],
                 'leaf': ['sorryAx'], 'unreached': ['sorryAx']}
        self.assertEqual(status.closure(['root'], edges),
                         {'root', 'body', 'type', 'leaf', 'sorryAx'})


if __name__ == '__main__':
    unittest.main()
