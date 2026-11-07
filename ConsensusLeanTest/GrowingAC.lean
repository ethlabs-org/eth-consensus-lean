module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.AC.Main

@[expose] public section

/-! # Growing-fault AC milestone and axiom pins -/

theorem Consensus.Goldilocks.SA.Growing.aCSteps : Consensus.Goldilocks.SA.Growing.ACSteps :=
  Consensus.Goldilocks.SA.Growing.acSteps

theorem Consensus.Goldilocks.SA.Growing.joinedAwake (sp : Consensus.Goldilocks.SA.SAParams) :
    Consensus.Goldilocks.SA.Growing.JoinedAwake sp :=
  Consensus.Goldilocks.SA.Growing.joined_awake sp

theorem Consensus.Goldilocks.SA.Growing.joinedKeepsVotes (sp : Consensus.Goldilocks.SA.SAParams) :
    Consensus.Goldilocks.SA.Growing.JoinedKeepsVotes sp :=
  Consensus.Goldilocks.SA.Growing.joined_keeps_votes sp

theorem Consensus.Goldilocks.SA.Growing.oneVotePerSlot (sp : Consensus.Goldilocks.SA.SAParams) :
    Consensus.Goldilocks.SA.Growing.OneVotePerSlot sp :=
  Consensus.Goldilocks.SA.Growing.one_vote_per_slot sp

theorem Consensus.Goldilocks.Growing.localRunReachable :
    Consensus.Goldilocks.Growing.LocalRunReachable :=
  Consensus.Goldilocks.Growing.localRun_reachable

set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.SA.Growing.aCSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.SA.Growing.aCSteps

/-- info: 'Consensus.Goldilocks.SA.Growing.joinedAwake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.SA.Growing.joinedAwake

/-- info: 'Consensus.Goldilocks.SA.Growing.joinedKeepsVotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.SA.Growing.joinedKeepsVotes

/-- info: 'Consensus.Goldilocks.SA.Growing.oneVotePerSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.SA.Growing.oneVotePerSlot

/-- info: 'Consensus.Goldilocks.Growing.localRunReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.Growing.localRunReachable

end
