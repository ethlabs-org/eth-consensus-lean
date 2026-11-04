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

spec = importlib.util.spec_from_file_location('status', Path(__file__).with_name('obligations-status.py'))
status = importlib.util.module_from_spec(spec)
spec.loader.exec_module(status)


class StatusTests(unittest.TestCase):
    PREFIX = 'Consensus.Goldilocks.'

    def regenerate(self, names, sorry, dependencies, prior, head='fixture-pin', prior_rows=None,
                   historical=None, document=False):
        """Run `main` on a one-file fixture: every name was a historical sorry, `sorry` are the
        current ones, `dependencies` the compiled edges, `prior` the previous rows (or
        `prior_rows`, whole rows with their own names); return rows (or, with `document`, the
        ledger). `historical` replaces the fixture as the historical blob."""
        prefix = self.PREFIX
        source = 'namespace ' + prefix[:-1] + '\n' + '\n'.join(
            'theorem ' + n + ' : True := by ' + ('sorry' if n in sorry else 'trivial')
            for n in names)
        records = [{'declaration': 'Consensus.Goldilocks.Obligations.accepted',
                    'dependencies': [prefix + n for n in names]}]
        records += [{'declaration': prefix + n,
                     'dependencies': ['sorryAx'] if n in sorry else
                     [prefix + d for d in dependencies.get(n, [])]} for n in names]

        def run(*args):
            if args[:2] == ('git', 'rev-parse'):
                return head + '\n'
            if args[:2] == ('git', 'ls-tree'):
                return '100644 blob fixture\t' + str(file) + '\n'
            if args[:2] == ('git', 'cat-file'):
                return historical if historical is not None else source.replace('trivial', 'sorry')
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
                ledger = Path('docs/obligations-status.json')
                ledger.parent.mkdir()
                if prior_rows is None:
                    prior_rows = [{'name': prefix + n, **prior(n)} for n in names]
                ledger.write_text(json.dumps({'rows': prior_rows}))
                with patch.object(status, 'run', side_effect=run), \
                        patch.object(status.subprocess, 'run'), \
                        patch('sys.argv', ['obligations-status.py']):
                    status.main()
                result = json.loads(ledger.read_text())
                if document:
                    return result
                return {r['name'][len(prefix):]: r for r in result['rows']}
            finally:
                os.chdir(cwd)

    def test_sleepy_regeneration_distinguishes_body_and_type_dependency(self):
        names = ['contract_heal', 'sleepy_query_sync', 'sleepy_safety_inputs',
                 'simTrace_vote_forwarded', 'final_duty_proposal']
        rows = self.regenerate(
            names, {'contract_heal'},
            {n: ['contract_heal'] for n in ('sleepy_query_sync', 'sleepy_safety_inputs',
                                            'final_duty_proposal')},
            lambda n: {'status': 'paper-open (research)', 'obstruction': '#128 stale',
                       'evidence': 'stale', 'derisk-verdict': 'complete',
                       'adversarial-pass-done': 'y'})
        for n in names[1:3]:
            r = rows[n]
            self.assertFalse(r['direct_sorry'])
            self.assertEqual(r['lean-status'], 'sorry-dependent')
            self.assertEqual(r['status'], 'unknown')
            self.assertEqual(r['blocked-by'], [self.PREFIX + 'contract_heal'])
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

    def test_step1_renames_keep_former_owners(self):
        # The historical blob names the former owner by its pre-2026-11-04 name: it keeps its row under
        # the name it became (the coefficient in the root namespace). A historical name that no current
        # declaration took stays historical.
        historical = ('namespace Consensus.Goldilocks.Refinement\n'
                      'theorem accepted_heal : True := by sorry\n'
                      'theorem gone_leaf : True := by sorry\n')
        ledger = self.regenerate(['contract_heal'], set(), {}, lambda n: {}, historical=historical,
                                 prior_rows=[], document=True)
        self.assertEqual([r['name'] for r in ledger['rows']], [self.PREFIX + 'contract_heal'])
        self.assertEqual(ledger['historical_removed'], ['Consensus.Goldilocks.Refinement.gone_leaf'])
        self.assertEqual(status.renamed('Consensus.Goldilocks.Refinement.accepted_heal', set()),
                         'Consensus.Goldilocks.Refinement.accepted_heal')

    def test_leftover_renames_keep_former_owners_outside_refinement(self):
        # The naming leftovers renamed Obligations.rowDelay_pos (a former owner outside Refinement) to
        # protoFGDelay_pos: it keeps its row under the new name, and nothing becomes historical.
        historical = ('namespace Consensus.Goldilocks.Obligations\n'
                      'theorem rowDelay_pos : True := by sorry\n')
        ledger = self.regenerate(['Obligations.protoFGDelay_pos'], set(), {}, lambda n: {},
                                 historical=historical, prior_rows=[], document=True)
        self.assertEqual([r['name'] for r in ledger['rows']],
                         [self.PREFIX + 'Obligations.protoFGDelay_pos'])
        self.assertEqual(ledger['historical_removed'], [])

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

    PRIVATE = '_private.ConsensusLean.Instances.Goldilocks.Lemmas.{}.0.' + PREFIX
    CARRIED = {'status': 'lean-proved', 'status-source': 'compiled dependency audit',
               'owner-thread': 'T-override', 'area': 'healing', 'card-path': 'cards/foo.md',
               'card-commit': 'card-pin', 'card-repo': 'ethlabs-org/workbench',
               'derisk-verdict': 'research', 'adversarial-pass-done': 'y',
               'evidence': status.PROVED_EVIDENCE + 'oldsha.', 'last-changed': '2026-01-01'}

    def test_private_to_public_rename_keeps_row_metadata(self):
        prior_rows = [{'name': self.PRIVATE.format('Old') + 'foo', **self.CARRIED}]
        row = self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)['foo']
        for key in ('owner-thread', 'card-path', 'card-commit', 'card-repo', 'derisk-verdict',
                    'adversarial-pass-done', 'evidence'):
            self.assertEqual(row[key], self.CARRIED[key])
        self.assertEqual(row['status'], 'lean-proved')
        self.assertNotEqual(row['last-changed'], '2026-01-01')
        # the compiled closure still decides the status of a renamed row
        regressed = self.regenerate(['foo'], {'foo'}, {}, None, prior_rows=prior_rows)['foo']
        self.assertTrue(regressed['direct_sorry'])
        self.assertNotEqual(regressed['status'], 'lean-proved')
        self.assertNotIn('evidence', regressed)
        self.assertEqual(regressed['card-path'], 'cards/foo.md')

    def assert_defaults(self, row):
        self.assertEqual(row['owner-thread'], 'T-01a18fec-6e1e-7342-9ca9-8562977d7347')
        self.assertEqual(row['area'], 'network+Sleepy')
        self.assertIsNone(row['card-path'])
        self.assertEqual(row['derisk-verdict'], 'none yet')
        self.assertEqual(row['evidence'], status.PROVED_EVIDENCE + 'fixture-.')

    def test_ambiguous_rename_carries_nothing(self):
        prior_rows = [{'name': self.PRIVATE.format(m) + 'foo', **self.CARRIED} for m in ('A', 'B')]
        self.assert_defaults(self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)['foo'])

    def test_unrelated_new_row_carries_nothing(self):
        prior_rows = [{'name': self.PRIVATE.format('Old') + 'bar', **self.CARRIED}]
        rows = self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)
        self.assertEqual(set(rows), {'foo'})
        self.assert_defaults(rows['foo'])

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

    def test_declarations_take_the_enclosing_namespace_block(self):
        source = '''namespace Consensus.Helper
theorem h : True := by trivial
end Consensus.Helper

namespace Consensus.Main
section Inner
private theorem leaf : True := by
  sorry
end Inner
namespace Sub
theorem deep : True := by trivial
end Sub
theorem after : True := by trivial
end Consensus.Main
'''
        self.assertEqual(status.declarations(source), [
            ('Consensus.Helper.h', 2, False),
            ('Consensus.Main.leaf', 7, True),
            ('Consensus.Main.Sub.deep', 11, False),
            ('Consensus.Main.after', 13, False)])

    def test_closure_keeps_type_edges_and_handles_cycles(self):
        edges = {'root': ['body', 'type'], 'body': ['root'], 'type': ['leaf'],
                 'leaf': ['sorryAx'], 'unreached': ['sorryAx']}
        self.assertEqual(status.closure(['root'], edges),
                         {'root', 'body', 'type', 'leaf', 'sorryAx'})


if __name__ == '__main__':
    unittest.main()
