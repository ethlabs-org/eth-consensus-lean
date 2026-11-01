"""Regression tests for status selection (the dependency audit remains authoritative)."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('status', Path(__file__).with_name('accepted-status.py'))
status = importlib.util.module_from_spec(spec)
spec.loader.exec_module(status)


class StatusTests(unittest.TestCase):
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
