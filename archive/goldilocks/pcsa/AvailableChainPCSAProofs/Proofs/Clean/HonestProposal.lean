module
public import AvailableChainPCSARun.Statements.Interface
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainPCSAProofs.Proofs.Clean.CommonViews
public import AvailableChainPCSAProofs.Proofs.Clean.CommonScores
public import AvailableChainPCSAProofs.Proofs.Clean.CommonTree
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalPaths
public import AvailableChainPCSAProofs.Proofs.Clean.BodySlotBounds
public import AvailableChainPCSAProofs.Proofs.Clean.CommonEligibility
public import AvailableChainPCSAProofs.Proofs.Clean.RetainedProposal
public import AvailableChainPCSAProofs.Proofs.Clean.RootAgreement
public import AvailableChainPCSAProofs.Proofs.Clean.ProposerReads
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalDelivery

public section

/-! C6 HonestProposal: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The claim-level honest proposal has exact named metadata and an authenticated emission. -/
theorem pcsa_honest_proposal_named (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (P : Block)
    (hP : Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s P) :
    rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest ∧ ∃ N : NamedProposal p.n, N.erase = P ∧
      V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
        (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s) := by
  obtain ⟨hx, payload, hb, he⟩ := hP
  cases payload with
  | head r => change (none : Option Block) = some P at hb; cases hb
  | row r => change (none : Option Block) = some P at hb; cases hb
  | ack r => change (none : Option Block) = some P at hb; cases hb
  | pc C => change (none : Option Block) = some P at hb; cases hb
  | proposal N =>
    change some N.erase = some P at hb
    exact ⟨hx, N, Option.some.inj hb, he⟩
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
variable {n : Nat}
/-- The named parent's erasure is a prefix of the erased proposal. -/
theorem pcsa_named_parent_prefix (N : NamedProposal n) : Block.Preceq N.parent.erase N.erase := by
  cases N with
  | genesis => rfl
  | node P s r app raw sup rows pc =>
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl _))
/-- A positive-slot named proposal has its named parent as its geometric parent. -/
theorem pcsa_named_parent_of_positive (N : NamedProposal n) (hs : 0 < N.slot) :
    N.erase.parent? = some N.parent.erase := by
  cases N with
  | genesis => exact (Nat.not_lt_zero _ hs).elim
  | node P s r app raw sup rows pc => rfl
end AvailableChain.PCSA

end
