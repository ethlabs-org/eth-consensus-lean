module
public import ConsensusLean.Lemmas.Model.RoleReader
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee

/-! # Instance role and validator-committee adapters

These contracts supply neither an engine role plan nor a public reader instance.
No generic regime definition imports this adapter. -/

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

/-- The PKI image of the entire slot dictionary, usable as plain environment regime data. -/
noncomputable def CommitteeDict.validators (K : CommitteeDict (Fintype.card V))
    (key : Fin (Fintype.card V) ≃ V) : Nat → Finset V :=
  fun s => Model.validatorCommittee key (open scoped Classical in Set.toFinset (K.committee s))

theorem CommitteeDict.validators_eq (K : CommitteeDict (Fintype.card V))
    (key : Fin (Fintype.card V) ≃ V) (s : Nat) :
    K.validators key s = Model.validatorCommittee key
      (open scoped Classical in Set.toFinset (K.committee s)) := by rfl

/-- Intended image equality under binding; it is a theorem type, not supplied evidence. -/
def CommitteeDict.ValidatorSelectionEdge (K : CommitteeDict (Fintype.card V))
    (rho : Run F E) (voteRole : Nat → (protoOf F E).Role) : Prop :=
  K.BindsSel rho voteRole →
    ∀ s, K.validators rho.key s = Model.validatorCommittee rho.key (rho.sel (voteRole s))

theorem CommitteeDict.validatorSelectionEdge_iff (K : CommitteeDict (Fintype.card V))
    (rho : Run F E) (voteRole : Nat → (protoOf F E).Role) :
    K.ValidatorSelectionEdge rho voteRole ↔ (K.BindsSel rho voteRole →
      ∀ s, K.validators rho.key s = Model.validatorCommittee rho.key (rho.sel (voteRole s))) := by
  rfl

/-- ACK key q binds to the slot-(q+2) vote role, not a second selection. -/
def AckRoleBinding (voteRole ackRole : Nat → (protoOf F E).Role) : Prop :=
  ∀ q, ackRole q = voteRole (q + 2)

theorem ackRoleBinding_iff (voteRole ackRole : Nat → (protoOf F E).Role) :
    AckRoleBinding voteRole ackRole ↔ ∀ q, ackRole q = voteRole (q + 2) := by rfl

/-- Intended transport of the ACK selection through the same dictionary and PKI image. -/
def CommitteeDict.AckSelectionEdge (K : CommitteeDict (Fintype.card V))
    (rho : Run F E) (voteRole ackRole : Nat → (protoOf F E).Role) : Prop :=
  K.BindsSel rho voteRole → AckRoleBinding voteRole ackRole →
    ∀ q, Model.validatorCommittee rho.key (rho.sel (ackRole q)) = K.validators rho.key (q + 2)

theorem CommitteeDict.ackSelectionEdge_iff (K : CommitteeDict (Fintype.card V))
    (rho : Run F E) (voteRole ackRole : Nat → (protoOf F E).Role) :
    K.AckSelectionEdge rho voteRole ackRole ↔
      (K.BindsSel rho voteRole → AckRoleBinding voteRole ackRole →
        ∀ q, Model.validatorCommittee rho.key (rho.sel (ackRole q)) =
          K.validators rho.key (q + 2)) := by rfl

end Consensus.Goldilocks.SA
