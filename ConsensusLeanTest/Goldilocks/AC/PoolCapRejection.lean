module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Views

@[expose] public section

/-! # A late honest vote can be rejected after its signer is compromised

Kind (r), a rejection test (CONTRIBUTING "Statements"), of exact pool membership under the pool
cap (`SA.PoolCap`): `third_vote_rejected` is a local admission witness in which two distinct votes
forged after compromise fill the same-validator cap before the genuine vote arrives. It is not a
complete engine-run counterexample. -/

namespace Consensus.Goldilocks.SA.Test

/-- Two earlier distinct votes of the same validator prevent admission of a third vote,
even in its current slot. The third vote can have been honestly cast before compromise. -/
theorem third_vote_rejected (sp : SAParams) (x : Fin sp.n) :
    let forged₁ : Vote sp.n := ⟨x, 0, 1⟩
    let forged₂ : Vote sp.n := ⟨x, 0, 2⟩
    let genuine : Vote sp.n := ⟨x, 0, 0⟩
    let A := admitVote sp (admitVote sp (SAState.initial 0) 0 forged₁) 0 forged₂
    forged₁ ∈ A.pool 0 ∧ forged₂ ∈ A.pool 0 ∧
      genuine ∉ (admitVote sp A 0 genuine).pool 0 := by
  have hs : sp.slot 0 = 0 := by simp [SAParams.slot, Params.slotOf]
  simp [admitVote, hs, SAState.initial]

end Consensus.Goldilocks.SA.Test

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned message is longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.SA.Test.third_vote_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.third_vote_rejected

end
