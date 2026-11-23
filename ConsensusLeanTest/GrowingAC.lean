module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.AC.Main

@[expose] public section

/-! # Growing-fault AC milestone and axiom pins -/

theorem Consensus.Goldilocks.AC.Growing.aCSteps : Consensus.Goldilocks.AC.Growing.ACSteps :=
  Consensus.Goldilocks.AC.Growing.acSteps

theorem Consensus.Goldilocks.AC.Growing.joinedAwake (sp : Consensus.Goldilocks.AC.ACParams) :
    Consensus.Goldilocks.AC.Growing.JoinedAwake sp :=
  Consensus.Goldilocks.AC.Growing.joined_awake sp

theorem Consensus.Goldilocks.AC.Growing.joinedKeepsVotes (sp : Consensus.Goldilocks.AC.ACParams) :
    Consensus.Goldilocks.AC.Growing.JoinedKeepsVotes sp :=
  Consensus.Goldilocks.AC.Growing.joined_keeps_votes sp

theorem Consensus.Goldilocks.AC.Growing.oneVotePerSlot (sp : Consensus.Goldilocks.AC.ACParams) :
    Consensus.Goldilocks.AC.Growing.OneVotePerSlot sp :=
  Consensus.Goldilocks.AC.Growing.one_vote_per_slot sp

theorem Consensus.Goldilocks.Growing.localRunReachable :
    Consensus.Goldilocks.Growing.LocalRunReachable :=
  Consensus.Goldilocks.Growing.localRun_reachable

set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.AC.Growing.aCSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.AC.Growing.aCSteps

/-- info: 'Consensus.Goldilocks.AC.Growing.joinedAwake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.AC.Growing.joinedAwake

/-- info: 'Consensus.Goldilocks.AC.Growing.joinedKeepsVotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.AC.Growing.joinedKeepsVotes

/-- info: 'Consensus.Goldilocks.AC.Growing.oneVotePerSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.AC.Growing.oneVotePerSlot

/-- info: 'Consensus.Goldilocks.Growing.localRunReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Consensus.Goldilocks.Growing.localRunReachable

end
