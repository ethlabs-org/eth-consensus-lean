module
public import ConsensusLean.Spec.Problem.CorrectProtocol

/-! # Public-skeleton role readers

Selection is external run data. A reader supplies no executable access to hidden selection.
These definitions construct no reader or model binding. -/

public section
namespace Consensus

/-- Only cardinality and positive public delays, never awake/fault/submission profiles. -/
structure PublicSkeleton where
  n : Nat
  deltaAC : Time
  deltaAC_pos : 0 < deltaAC
  deltaFG : Time
  deltaFG_pos : 0 < deltaFG

def publicSkeleton {V : Type} [Fintype V] (E : Env V) : PublicSkeleton :=
  ⟨Fintype.card V, E.ΔAC, E.ΔAC_pos, E.ΔFG, E.ΔFG_pos⟩

theorem publicSkeleton_eq {V : Type} [Fintype V] (E : Env V) :
    publicSkeleton E = ⟨Fintype.card V, E.ΔAC, E.ΔAC_pos, E.ΔFG, E.ΔFG_pos⟩ := by rfl

/-- Role identities factor through public data, while selection remains external. -/
structure PublicRoleReader {V : Type} [Fintype V] (S : System V) (X : External S) where
  Role : PublicSkeleton → Type
  voteRole : (p : PublicSkeleton) → Nat → Role p
  selected : (E : Env V) → X.Ext E → Role (publicSkeleton E) → Finset V

def PublicRoleReader.moveRole {V : Type} [Fintype V] {S : System V} {X : External S}
    (R : PublicRoleReader S X) {E E' : Env V} (h : publicSkeleton E = publicSkeleton E')
    (r : R.Role (publicSkeleton E)) : R.Role (publicSkeleton E') := h ▸ r

/-- Intended historical-selection preservation contract, not supplied evidence. -/
def PublicRoleReader.ReaderTransport {V : Type} [Fintype V] {S : System V} {X : External S}
    (R : PublicRoleReader S X) {E E' : Env V} (h : publicSkeleton E = publicSkeleton E')
    (e : X.Ext E) (e' : X.Ext E') : Prop :=
  ∀ r, R.selected E' e' (R.moveRole h r) = R.selected E e r

end Consensus
