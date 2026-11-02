"""Regression tests for status selection (the dependency audit remains authoritative)."""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True  # a self-test leaves no scripts/__pycache__ in the checkout

spec = importlib.util.spec_from_file_location('status', Path(__file__).with_name('accepted-status.py'))
status = importlib.util.module_from_spec(spec)
spec.loader.exec_module(status)


class StatusTests(unittest.TestCase):
    PREFIX = 'Consensus.Goldilocks.Refinement.'

    def regenerate(self, names, sorry, dependencies, prior, head='fixture-pin'):
        """Run `main` on a one-file fixture: every name was a historical sorry, `sorry` are the
        current ones, `dependencies` the compiled edges, `prior` the previous rows; return rows."""
        prefix = self.PREFIX
        source = 'namespace ' + prefix[:-1] + '\n' + '\n'.join(
            'theorem ' + n + ' : True := by ' + ('sorry' if n in sorry else 'trivial')
            for n in names)
        records = [{'declaration': prefix + 'accepted', 'dependencies': [prefix + n for n in names]}]
        records += [{'declaration': prefix + n,
                     'dependencies': ['sorryAx'] if n in sorry else
                     [prefix + d for d in dependencies.get(n, [])]} for n in names]

        def run(*args):
            if args[:2] == ('git', 'rev-parse'):
                return head + '\n'
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
                ledger.write_text(json.dumps({'rows': [{'name': prefix + n, **prior(n)} for n in names]}))
                with patch.object(status, 'run', side_effect=run), \
                        patch.object(status.subprocess, 'run'), \
                        patch('sys.argv', ['accepted-status.py']):
                    status.main()
                return {r['name'][len(prefix):]: r for r in json.loads(ledger.read_text())['rows']}
            finally:
                os.chdir(cwd)

    def test_sleepy_regeneration_distinguishes_body_and_type_dependency(self):
        names = ['accepted_heal', 'sleepy_query_sync', 'sleepy_safety_inputs',
                 'simTrace_vote_forwarded', 'final_duty_proposal']
        rows = self.regenerate(
            names, {'accepted_heal'},
            {n: ['accepted_heal'] for n in ('sleepy_query_sync', 'sleepy_safety_inputs',
                                            'final_duty_proposal')},
            lambda n: {'status': 'paper-open (research)', 'obstruction': '#128 stale',
                       'evidence': 'stale', 'derisk-verdict': 'complete',
                       'adversarial-pass-done': 'y'})
        for n in names[1:3]:
            r = rows[n]
            self.assertFalse(r['direct_sorry'])
            self.assertEqual(r['lean-status'], 'sorry-dependent')
            self.assertEqual(r['status'], 'unknown')
            self.assertEqual(r['blocked-by'], [self.PREFIX + 'accepted_heal'])
            self.assertIn('Body proved', r['evidence'])
            self.assertIn('K S A', r['evidence'])
            self.assertNotIn('obstruction', r)
            self.assertEqual(r['derisk-verdict'], 'complete')
        self.assertEqual(rows[names[3]]['status'], 'lean-proved')
        duty = rows['final_duty_proposal']
        self.assertFalse(duty['direct_sorry'])
        self.assertEqual(duty['lean-status'], 'sorry-dependent')
        self.assertEqual(duty['status'], 'unknown')
        self.assertEqual(duty['status-source'], 'compiled dependency audit')
        self.assertIn('final_duty_proposal_run', duty['evidence'])
        self.assertIn('K S A', duty['evidence'])
        self.assertTrue(rows[names[0]]['direct_sorry'])

    def test_proved_rows_refresh_ratings_and_skip_unproved_overrides(self):
        # every row was reviewed before (status-source set), with stale prose evidence
        names = ['final_reset_premises', 'outage_arm', 'sleepy_query_sync', 'healthy_cut_agreement',
                 'outage_repair']
        prior = lambda n: {'status': 'paper-partial', 'status-source': 'reviewed',
                           'evidence': 'Open: stale prose that remains'}
        rows = self.regenerate(names, {'outage_repair'}, {}, prior)
        # (a) a REFRESH name takes its current RATINGS entry, not the previous evidence
        self.assertIn('final_reset_premises', status.REFRESH)
        self.assertEqual(rows['final_reset_premises']['evidence'],
                         status.RATINGS['final_reset_premises'][2])
        self.assertEqual(rows['final_reset_premises']['status'], 'lean-proved')
        # (b) proved rows do not take the unproved-only overrides; their prose becomes the audit fact
        for n in ('outage_arm', 'sleepy_query_sync', 'healthy_cut_agreement'):
            self.assertEqual(rows[n]['status'], 'lean-proved')
            self.assertEqual(rows[n]['evidence'], status.PROVED_EVIDENCE + 'fixture-.')
        # an open row keeps its reviewed evidence
        self.assertEqual(rows['outage_repair']['evidence'], 'Open: stale prose that remains')
        self.assertTrue(rows['outage_repair']['direct_sorry'])
        # the audit fact records the first proving audit and is stable across later audits
        again = self.regenerate(names, {'outage_repair'}, {},
                                lambda n: {k: v for k, v in rows[n].items() if k != 'name'},
                                head='later-pin')
        self.assertEqual(again['outage_arm']['evidence'], status.PROVED_EVIDENCE + 'fixture-.')

    def test_regressed_rows_drop_proof_ratings_and_evidence(self):
        # proved at an earlier audit, now back to a sorry: a lean-proved REFRESH entry and an
        # audit-fact row
        self.assertIn('healthy_repair_schedule', status.REFRESH)
        self.assertEqual(status.RATINGS['healthy_repair_schedule'][0], 'lean-proved')
        names = ['healthy_repair_schedule', 'outage_arm']
        before = {'healthy_repair_schedule': status.RATINGS['healthy_repair_schedule'][2],
                  'outage_arm': status.PROVED_EVIDENCE + 'earlier.'}
        prior = lambda n: {'status': 'lean-proved', 'status-source': 'compiled dependency audit',
                           'evidence': before[n]}
        rows = self.regenerate(names, set(names), {}, prior)
        for n in names:
            self.assertTrue(rows[n]['direct_sorry'])
            self.assertNotEqual(rows[n]['status'], 'lean-proved')
            self.assertFalse(rows[n].get('evidence', '').startswith('Proved'))
        # the proof rating (and its source) is not applied to the regressed REFRESH row
        self.assertEqual(rows['healthy_repair_schedule']['status-source'],
                         'compiled dependency audit')

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
