module
public import ConsensusLean.Init

/-! # Slot-indexed committee dictionaries -/

@[expose] public section

namespace Consensus.Goldilocks.SA

/-- The validators selected for each slot, independently of an execution engine. -/
structure CommitteeDict (n : Nat) where
  committee : Nat → Set (Fin n)

/-- Every validator participates in every slot. -/
def CommitteeDict.full (n : Nat) : CommitteeDict n := ⟨fun _ => Set.univ⟩

/-- Every slot's committee is the full validator set. -/
def CommitteeDict.IsFull {n : Nat} (K : CommitteeDict n) : Prop :=
  ∀ s, K.committee s = Set.univ

end Consensus.Goldilocks.SA

end
