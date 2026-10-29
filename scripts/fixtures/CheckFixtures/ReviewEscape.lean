module
@[expose] public section

/-! Fixture module for `scripts/fixtures/ReviewEscapeBad.lean`: a statements module, laid out
like `ConsensusLean/Statements/Review.lean`, in which only `Stmt` will have a review pair. The other
statements try to escape `Consensus.ReviewGuard.checkComplete`: one in another namespace, one with
a name that `Name.isInternalDetail` treats as internal (`eq_1`), one with a leading underscore and
one `private`. -/

namespace CheckFixtures.ReviewEscape

def Stmt : Prop := ∀ (n : Nat), n = n

def eq_1 : Prop := True

def _Extra : Prop := True

private def Priv : Prop := True

theorem src : ∀ (n : Nat), n = n := fun _ => rfl

end CheckFixtures.ReviewEscape

namespace CheckFixtures.Elsewhere

def Extra : Prop := True

end CheckFixtures.Elsewhere

end
