module
public import AvailableChainPCSAProofs.Proofs.Clean.CommonInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs

public section

/-! C6 CommonRaw: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A stored proposal's signing slot is its content slot. -/
theorem pcsa_proposal_pool_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.DeliveryWellFormed E rho)
    (k : Nat) (x : V) (w : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (hm : w ∈ (V2.D.Run.stateBefore E rho k x).st.proposals)
    (hd : w.decode = some (.block s N)) : s = N.slot := by
  have hw := pcsa_proposal_pool_wellFormed E rho hv k x w hm
  change AvailableChain.PCSA.wellFormed p w = true at hw
  delta AvailableChain.PCSA.wellFormed at hw
  rw [hd] at hw
  change (_ && s == N.erase.slot && _ && _ && _ && _ && _ && _) = true at hw
  have hs := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp hw).1).1).1).1).1).1).2
  have he : N.erase.slot = N.slot := by cases N <;> rfl
  exact (beq_iff_eq.mp hs).trans he
/-- At an honest proposer slot, a raw voter input is frozen or in the exact emitted list. -/
theorem pcsa_honest_headVotes_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (v : Time) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st v) s) :
    (o ∈ GridCO.votesAt (clock p (V2.D.Run.stateBefore E rho k y).st v).base (s - 1) ∧
      GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st v).base o <
        SA.freezeTime p.toParams (s - 1)) ∨ o ∈ N.raw.map baseVote := by
  rcases pcsa_headVotes_mem p _ s o ho with hf | ⟨w, hw, t, M, a, hd, hs, ha, hbase, _⟩
  · exact Or.inl hf
  · rw [pcsa_clock_proposals] at hw
    have ht : t = s := (pcsa_proposal_pool_slot E rho hv.toDeliveryWellFormed k y w t M hw
      hd).trans hs
    subst t
    have hMN := pcsa_proposal_decoded_eq_emitted E rho hv k y s N hx he w hw M hd
    subst M
    exact Or.inr (List.mem_map.mpr ⟨a, ha, hbase⟩)
/-- Receipt of an honest proposal includes its full raw list at the voter read. -/
theorem pcsa_emitted_raw_in_headVotes (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (y : V) (v : Time)
    (s : Slot) (N : NamedProposal p.n) (hslot : N.slot = s)
    (hlabel : ∀ o ∈ N.raw.map baseVote, GridCO.headLabel? o = some (s - 1))
    (hmem : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals) :
    N.raw.map baseVote ⊆ headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st v) s := by
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
  apply pcsa_headVotes_of_carried p _ s ⟨.proposer s, .proposal N⟩
    (by rwa [pcsa_clock_proposals]) s N rfl hslot a ha
  exact hlabel _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: Honest proposal receipt gives both directions of the actual raw-input
comparison. -/
theorem pcsa_common_raw_transfer_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hslot : N.slot = s + 1)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho a y).st.proposals)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hr : N.raw.map baseVote = proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) :
    let src := clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
    proposerVotes src (s + 1) ⊆ headVotes p dst (s + 1) ∧
      ∀ o ∈ headVotes p dst (s + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ proposerVotes src (s + 1) ∨ GridCO.equivocates (proposerVotes src (s + 1)) i = true :=
          by
  dsimp only
  constructor
  · rw [← hr]
    apply pcsa_emitted_raw_in_headVotes E rho a y v (s + 1) N hslot
    · intro o ho
      rw [hr] at ho
      exact beq_iff_eq.mp (List.mem_filter.mp ho).2
    · exact hmem
  · intro o ho i hi
    rcases pcsa_honest_headVotes_source E rho h.valid a y v (s + 1) N hx he o ho with
      ⟨hm, ht⟩ | hm
    · rw [Nat.add_sub_cancel] at hm ht
      have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp hm).2
      obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
      exact pcsa_frozen_input_in_proposer_win E rho h hD (hT := hT) a k y _ hy hx s i r v hc hk
        (List.mem_filter.mp hm).1 ht
    · exact Or.inl (hr ▸ hm)
/-- Honest proposal receipt gives both directions of the actual raw-input comparison. -/
theorem pcsa_common_raw_transfer (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hslot : N.slot = s + 1)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho a y).st.proposals)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hr : N.raw.map baseVote = proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) :
    let src := clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
    proposerVotes src (s + 1) ⊆ headVotes p dst (s + 1) ∧
      ∀ o ∈ headVotes p dst (s + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ proposerVotes src (s + 1) ∨ GridCO.equivocates (proposerVotes src (s + 1)) i = true :=
  pcsa_common_raw_transfer_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k y hy s v N hx
    he hk hslot hmem (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hr
end AvailableChain.PCSA.Run

end
