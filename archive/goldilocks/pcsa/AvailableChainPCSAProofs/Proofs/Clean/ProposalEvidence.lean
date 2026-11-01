module
public import AvailableChainPCSAProofs.Proofs.Clean.ProposerInputs

public section

/-! C6 ProposalEvidence: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem proposal_evidence_wire (o : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (h : o.decode = some (.block s N)) : o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at h <;> cases h
  | proposer t =>
    cases payload <;> delta Wire.decode at h <;> cases h
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at h <;> cases h
/-- A decoded proposal delivery has the exact proposer-signed object. -/
theorem pcsa_decoded_proposal_object (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ :=
  ((toWireEquiv p).left_inv o).symm.trans
    (congrArg (ofWire p) (proposal_evidence_wire (toWire p o) s N h))
/-- A stored proposal of an honest proposer is that proposer's exact emitted body. -/
theorem pcsa_proposal_pool_eq_emitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot) (N M : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (hm : (⟨.proposer s, .proposal M⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals) : M = N := by
  obtain ⟨j, _, t, o, slot, A, P, hj, hd, hw, _⟩ :=
    pcsa_proposal_receipt_origin E rho k y _ hm
  have hs : s = slot := Auth.proposer.inj (congrArg (fun w : Wire p.n => w.auth) hw)
  have hM : M = A := Msg.proposal.inj (congrArg (fun w : Wire p.n => w.payload) hw)
  subst slot
  subst A
  have ho := pcsa_decoded_proposal_object o s M hd
  subst o
  obtain ⟨t', _, hEm⟩ := hv.unforgeable y _ t ⟨j, hj⟩ _ hx rfl
  obtain ⟨a, ha, hma⟩ := hEm
  obtain ⟨b, hb, hmb⟩ := he
  have hEq := (Gen.V2.Duty.emitted_unique_of_singleDuty E rho hv.nodup (.prop s)
    (pcsa_prop_single_duty p c m s) (0 : Fin 1) _ a b t' _ _ _ ha hb hma hmb rfl rfl).2
  exact Msg.proposal.inj (congrArg (fun o : Obj p => o.payload) hEq)
/-- Every decoded stored proposal of that slot has the same honest emitted metadata. -/
theorem pcsa_proposal_decoded_eq_emitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (w : Wire p.n) (hw : w ∈ (V2.D.Run.stateBefore E rho k y).st.proposals)
    (M : NamedProposal p.n) (hd : w.decode = some (.block s M)) : M = N := by
  rw [proposal_evidence_wire w s M hd] at hw
  exact pcsa_proposal_pool_eq_emitted E rho hv k y s N M hx he hw
end AvailableChain.PCSA.Run

end
