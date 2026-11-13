module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee

/-! # Instance committee binding to the run's role selection

`CommitteeDict.BindsSel` ties a slot dictionary to the run's actual vote-role selection. It
supplies neither an engine role plan nor a public reader instance. -/

public section
namespace Consensus.Goldilocks.SA
open Model

variable {V : Type} [Fintype V]
  {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}

/-- The dictionary binds the actual role selection, without reading selection in honest code. -/
def CommitteeDict.BindsSel (K : CommitteeDict (Fintype.card V)) (rho : Run F E)
    (voteRole : Nat → (protoOf F E).Role) : Prop :=
  ∀ s k, k ∈ K.committee s ↔ k ∈ rho.sel (voteRole s)

theorem CommitteeDict.bindsSel_iff (K : CommitteeDict (Fintype.card V)) (rho : Run F E)
    (voteRole : Nat → (protoOf F E).Role) :
    K.BindsSel rho voteRole ↔ ∀ s k, k ∈ K.committee s ↔ k ∈ rho.sel (voteRole s) := by rfl

end Consensus.Goldilocks.SA
