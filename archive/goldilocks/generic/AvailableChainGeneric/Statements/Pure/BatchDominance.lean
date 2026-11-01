module
public import AvailableChainGeneric.Statements.Pure.Quorum

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- DC: DecoupledConsensusProofs/Availability/Confirmation.lean:489;
INTENTIONAL: extract scalar Batch premises. -/
def AnchorPassesStatement : Prop :=
  ∀ (h m denominator anchorScore : Nat), Batch h m →
    denominator ≤ h + m → h ≤ anchorScore →
    denominator < 2 * anchorScore ∧ decide (denominator < 2 * anchorScore) = true

theorem AnchorPassesStatement_def : AnchorPassesStatement =
  (∀ (h m denominator anchorScore : Nat), Batch h m →
    denominator ≤ h + m → h ≤ anchorScore →
    denominator < 2 * anchorScore ∧ decide (denominator < 2 * anchorScore) = true) := by rfl

/-- DC: DecoupledConsensusProofs/Availability/Confirmation.lean:562;
INTENTIONAL: extract the shared-denominator count argument. -/
def UnsupportedFailsStatement : Prop :=
  ∀ (h m denominator score : Nat), Batch h m →
    denominator ≤ h + m → h + score ≤ denominator →
    2 * score ≤ denominator ∧ decide (denominator < 2 * score) = false

theorem UnsupportedFailsStatement_def : UnsupportedFailsStatement =
  (∀ (h m denominator score : Nat), Batch h m →
    denominator ≤ h + m → h + score ≤ denominator →
    2 * score ≤ denominator ∧ decide (denominator < 2 * score) = false) := by rfl

-- A score cap and a denominator cap alone do not prove failure:
-- h=3, m=2, denominator=3, score=2 is a counterexample.

end AvailableChain.Gen.Pure
