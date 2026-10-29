module
public import CheckFixtures.Proof

@[expose] public section

namespace CheckFixtures.GenDep

/-! Regression of the `shapeProgress` leak: a definition whose embedded proof field is filled by a
lemma of a proof module. The leak is only in the generated `b._proof_1`. -/

structure Bound where
  n : Nat
  h : n ≤ n + CheckFixtures.Proof.helper

def b : Bound where
  n := 0
  h := by exact CheckFixtures.Proof.le_helper 0

end CheckFixtures.GenDep
