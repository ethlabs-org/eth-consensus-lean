module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Consensus.Goldilocks.SA

/-- Number of distinct validators in the externally fixed slot committee. -/
noncomputable def CommitteeDict.card {n : Nat} (K : CommitteeDict n) (s : Nat) : Nat :=
  (K.committee s).ncard

/-- Every actual slot has a nonempty committee. No fault or awake bound is hidden here. -/
def CommitteeDict.WellFormed {n : Nat} (K : CommitteeDict n) : Prop :=
  ∀ s, (K.committee s).Nonempty

end Consensus.Goldilocks.SA
