module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Locks

/-! # Independent record invariants, writes and read-point origins -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- The record is above every stored lock in the coherent universe. -/
def LockInvariant (U : Set (Blk sp.n FGP)) (st : SAState sp.n) (Φ : Frm sp.n FGP) : Prop :=
  ∃ E ∈ U, E.root = st.latestConfirmed ∧ (Anc U Φ.F E → E ∈ Φ.tree) ∧
    ∀ l ∈ st.locks, ∀ X ∈ U, X.root = l.block → Anc U X E

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

end Consensus.Goldilocks.SA.FamilyFacts

end
