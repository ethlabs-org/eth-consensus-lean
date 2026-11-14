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
        records = [{'declaration': status.ROOT,
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
                ledger = Path('docs/notes/obligations-status.json')
                ledger.parent.mkdir(parents=True)
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

    def test_regeneration_distinguishes_body_and_type_dependency(self):
        names = ['contract_heal', 'simTrace_vote_forwarded', 'final_duty_proposal']
        rows = self.regenerate(
            names, {'contract_heal'}, {'final_duty_proposal': ['contract_heal']},
            lambda n: {'status': 'paper-open (research)', 'evidence': 'stale',
                       'owner-thread': 'T-fixture', 'derisk-verdict': 'complete'})
        self.assertEqual(rows['simTrace_vote_forwarded']['status'], 'lean-proved')
        duty = rows['final_duty_proposal']
        self.assertFalse(duty['direct_sorry'])
        self.assertEqual(duty['lean-status'], 'sorry-dependent')
        self.assertEqual(duty['status'], 'unknown')
        self.assertEqual(duty['blocked-by'], [self.PREFIX + 'contract_heal'])
        self.assertIn('final_duty_proposal_run', duty['evidence'])
        self.assertIn('K S A', duty['evidence'])
        # a prior ledger's routing and process fields are not carried into the public row
        self.assertLessEqual(set(duty), set(status.ROW_FIELDS))
        self.assertTrue(rows['contract_heal']['direct_sorry'])

    def test_step1_renames_keep_former_owners(self):
        # The historical blob names the former owner by its earlier name: it keeps its row under
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

    def test_step3b_renames_keep_former_owners(self):
        # A historical owner among Concrete's field theorems keeps its row under its step-3b name.
        historical = ('namespace Consensus.Goldilocks.Obligations\n'
                      'theorem accepted_claims : True := by sorry\n')
        ledger = self.regenerate(['Obligations.meetsObligations_claims'], set(), {}, lambda n: {},
                                 historical=historical, prior_rows=[], document=True)
        self.assertEqual([r['name'] for r in ledger['rows']],
                         [self.PREFIX + 'Obligations.meetsObligations_claims'])
        self.assertEqual(ledger['historical_removed'], [])

    def test_fields_cover_the_growing_endpoint(self):
        # the root and the growing endpoint's field theorems are field keys; other closure members are not
        field = 'Obligations.Growing.meetsObligations_persists_growing'
        ledger = self.regenerate([field, 'Obligations.Growing.outage_helper'], set(), {}, lambda n: {},
                                 prior_rows=[], document=True)
        self.assertIn(status.ROOT, ledger['fields'])
        self.assertIn(self.PREFIX + field, ledger['fields'])
        self.assertNotIn(self.PREFIX + 'Obligations.Growing.outage_helper', ledger['fields'])

    def test_proved_rows_refresh_ratings_and_skip_unproved_overrides(self):
        # every row was reviewed before (it has a status), with stale prose evidence
        names = ['final_reset_premises', 'ready_unanimous', 'final_duty_proposal',
                 'vote_old_live_lock_below_parent', 'outage_repair']
        prior = lambda n: {'status': 'paper-partial', 'evidence': 'Open: stale prose that remains'}
        rows = self.regenerate(names, {'outage_repair'}, {}, prior)
        # (a) a REFRESH name takes its current RATINGS entry, not the previous evidence
        self.assertIn('final_reset_premises', status.REFRESH)
        self.assertEqual(rows['final_reset_premises']['evidence'],
                         status.RATINGS['final_reset_premises'][1])
        self.assertEqual(rows['final_reset_premises']['status'], 'lean-proved')
        # (b) proved rows do not take the unproved-only overrides; their prose becomes the audit fact
        for n in ('ready_unanimous', 'final_duty_proposal', 'vote_old_live_lock_below_parent'):
            self.assertEqual(rows[n]['status'], 'lean-proved')
            self.assertEqual(rows[n]['evidence'], status.PROVED_EVIDENCE + 'fixture-.')
        # an open row keeps its reviewed evidence
        self.assertEqual(rows['outage_repair']['evidence'], 'Open: stale prose that remains')
        self.assertTrue(rows['outage_repair']['direct_sorry'])
        # the audit fact records the first proving audit and is stable across later audits
        again = self.regenerate(names, {'outage_repair'}, {},
                                lambda n: {k: v for k, v in rows[n].items() if k != 'name'},
                                head='later-pin')
        self.assertEqual(again['ready_unanimous']['evidence'], status.PROVED_EVIDENCE + 'fixture-.')

    def test_regressed_rows_drop_proof_ratings_and_evidence(self):
        # proved at an earlier audit, now back to a sorry: a lean-proved REFRESH entry and an
        # audit-fact row
        self.assertIn('final_reset_premises', status.REFRESH)
        self.assertEqual(status.RATINGS['final_reset_premises'][0], 'lean-proved')
        names = ['final_reset_premises', 'ready_unanimous']
        before = {'final_reset_premises': status.RATINGS['final_reset_premises'][1],
                  'ready_unanimous': status.PROVED_EVIDENCE + 'earlier.'}
        prior = lambda n: {'status': 'lean-proved', 'evidence': before[n]}
        rows = self.regenerate(names, set(names), {}, prior)
        for n in names:
            self.assertTrue(rows[n]['direct_sorry'])
            self.assertNotEqual(rows[n]['status'], 'lean-proved')
            self.assertFalse(rows[n].get('evidence', '').startswith('Proved'))

    PRIVATE = '_private.ConsensusLean.Instances.Goldilocks.Lemmas.{}.0.' + PREFIX
    CARRIED = {'status': 'lean-proved', 'evidence': status.PROVED_EVIDENCE + 'oldsha.',
               'owner-thread': 'T-override', 'card-path': 'cards/foo.md'}

    def test_private_to_public_rename_keeps_row_metadata(self):
        prior_rows = [{'name': self.PRIVATE.format('Old') + 'foo', **self.CARRIED}]
        row = self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)['foo']
        self.assertEqual(row['evidence'], self.CARRIED['evidence'])
        self.assertEqual(row['status'], 'lean-proved')
        self.assertLessEqual(set(row), set(status.ROW_FIELDS))
        # the compiled closure still decides the status of a renamed row
        regressed = self.regenerate(['foo'], {'foo'}, {}, None, prior_rows=prior_rows)['foo']
        self.assertTrue(regressed['direct_sorry'])
        self.assertNotEqual(regressed['status'], 'lean-proved')
        self.assertNotIn('evidence', regressed)

    def assert_defaults(self, row):
        self.assertEqual(row['evidence'], status.PROVED_EVIDENCE + 'fixture-.')
        self.assertLessEqual(set(row), set(status.ROW_FIELDS))

    def test_ambiguous_rename_carries_nothing(self):
        prior_rows = [{'name': self.PRIVATE.format(m) + 'foo', **self.CARRIED} for m in ('A', 'B')]
        self.assert_defaults(self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)['foo'])

    def test_unrelated_new_row_carries_nothing(self):
        prior_rows = [{'name': self.PRIVATE.format('Old') + 'bar', **self.CARRIED}]
        rows = self.regenerate(['foo'], set(), {}, None, prior_rows=prior_rows)
        self.assertEqual(set(rows), {'foo'})
        self.assert_defaults(rows['foo'])

    def test_retired_rows_keep_only_public_fields(self):
        # A former owner that a reviewed refactor removed moves to `retired` with the current RETIRED texts and
        # without its routing and process fields; an already retired row keeps its own texts.
        gone = {'name': self.PREFIX + 'final_row_signers', 'status': 'paper-partial', 'evidence': 'e',
                'owner-thread': 'T-x', 'card-path': 'cards/x.md', 'last-changed': '2026-01-01'}
        kept = {'name': self.PREFIX + 'final_inherited_progress', 'status': 'retired (not proved)',
                'retired-by': 'stale reason', 'retirement-note': 'stale note', 'area': 'final liveness'}
        retired = status.retired_rows({'rows': [gone], 'retired': [kept]}, current={})
        self.assertEqual([r['name'] for r in retired], [kept['name'], gone['name']])
        for row in retired:
            self.assertLessEqual(set(row), set(status.RETIRED_FIELDS))
        self.assertEqual((retired[0]['retired-by'], retired[0]['retirement-note']), ('stale reason', 'stale note'))
        self.assertEqual((retired[1]['retired-by'], retired[1]['retirement-note']),
                         status.RETIRED['final_row_signers'])
        self.assertEqual(retired[1]['status'], 'retired (not proved)')
        self.assertEqual(retired[1]['status-before-retirement'], 'paper-partial')

    def test_same_named_privates_keep_their_own_module(self):
        # Two modules declare a private `foo`, both former sorry owners: each compiled copy gets its own row,
        # named by its own module and with its own file:line (not one row pairing one copy's name with the
        # other's source line).
        sources = {'A': 'namespace Consensus.Goldilocks\nprivate theorem foo : True := by trivial\n',
                   'B': 'namespace Consensus.Goldilocks\n\n\nprivate theorem foo : True := by trivial\n'}
        privates = {m: self.PRIVATE.format(m) + 'foo' for m in sources}
        root = status.ROOT
        records = [{'declaration': root, 'dependencies': sorted(privates.values())}]
        records += [{'declaration': p, 'dependencies': []} for p in privates.values()]

        def run(*args):
            if args[:2] == ('git', 'rev-parse'):
                return 'fixture-pin\n'
            if args[:2] == ('git', 'ls-tree'):
                return ''.join(f'100644 blob {m}\t{files[m]}\n' for m in sources)
            if args[:2] == ('git', 'cat-file'):
                return sources[args[-1]].replace('trivial', 'sorry')
            if args[:2] == ('git', 'rev-list'):
                return ''
            if args[:3] == ('lake', 'env', 'lean'):  # the environment's private names, in hash order
                return ''.join(f'{self.PREFIX}foo\t{privates[m]}\n' for m in ('B', 'A'))
            if args[:3] == ('lake', 'exe', 'spec-surface'):
                self.assertEqual(sorted(args[6:8]), sorted(privates.values()))
                return '\n'.join(json.dumps(r) for r in records)
            self.fail(f'Unexpected command: {args}')

        cwd = os.getcwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                files = {m: Path(f'ConsensusLean/Instances/Goldilocks/Lemmas/{m}.lean') for m in sources}
                for m, f in files.items():
                    f.parent.mkdir(parents=True, exist_ok=True)
                    f.write_text(sources[m])
                ledger = Path('docs/notes/obligations-status.json')
                ledger.parent.mkdir(parents=True)
                ledger.write_text(json.dumps({'rows': []}))
                with patch.object(status, 'run', side_effect=run), \
                        patch.object(status.subprocess, 'run'), \
                        patch('sys.argv', ['obligations-status.py']):
                    status.main()
                rows = {r['name']: r for r in json.loads(ledger.read_text())['rows']}
            finally:
                os.chdir(cwd)
        self.assertEqual(set(rows), set(privates.values()))
        self.assertEqual(rows[privates['A']]['file:line'], f'{files["A"]}:2')
        self.assertEqual(rows[privates['B']]['file:line'], f'{files["B"]}:4')
        for row in rows.values():
            self.assertEqual(row['status'], 'lean-proved')
            self.assertTrue(row['in_obligations_closure'])

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
