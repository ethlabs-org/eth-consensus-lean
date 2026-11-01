"""Regression tests for status selection (the dependency audit remains authoritative)."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('status', Path(__file__).with_name('accepted-status.py'))
status = importlib.util.module_from_spec(spec)
spec.loader.exec_module(status)


class StatusTests(unittest.TestCase):
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
