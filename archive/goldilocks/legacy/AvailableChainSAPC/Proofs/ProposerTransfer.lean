module
public import AvailableChainSAPC.Proofs.ProposalTransport
public import AvailableChainSAPC.Proofs.TransferRegimes
public import AvailableChainGridCO.Proofs.ProposerTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The existing SA receipt interface also holds at the honest proposer.
The proof reflects its own proposal's merged view back to the source;
it does not copy the SA support-count or GHOST proof. -/
theorem honest_proposal_transfer_receipts {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (a : Block) :
    GridCO.TransferReceipts p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r
      (proposalState p rho (r + 1)).base.blocks
      (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1))
      (GridCO.proposerSupportView (proposalState p rho (r + 1)).base (r + 1)) a := by
  have hef : earlyTime p r ≤ freezeTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have hfp : freezeTime p r ≤ proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hph : proposalTime p (r + 1) ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    linarith [p.deltaPos]
  have he : max (earlyTime p r) E.t_GST + E.Δ = freezeTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  have forward : RelayBy p rho (earlyTime p r) (freezeTime p r) :=
    he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hfp.trans (hph.trans hh))
  have back := local_back_receipts p E rho hx.toScheduleWellFormed r reader
  have receipts := genuine_transfer_receipts_of_back_receipts p E rho hx hΔ r
    reader reader hr hr (hfp.trans (hph.trans hh)) forward back a
  have subset := proposer_raw_subset_head_view p E rho hx hΔ hnet (r + 1) b hb
    (hsync.trans (hef.trans hfp)) hh reader hr
  constructor
  · intro o ho covers
    have hl : GridCO.headLabel? o = some r := by
      simpa using (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    have shape : ∃ i target, o = (⟨.seat r i, .head target⟩ : GridCO.Wire p.n) := by
      rcases o with ⟨auth, payload⟩
      cases auth <;> cases payload <;> simp_all [GridCO.headLabel?]
    obtain ⟨i, target, rfl⟩ := shape
    have support := (receipts.forward _ ho covers).1
    have unique := receipts.seat_unique i _ ho rfl
    have sourceUnique : GridCO.equivocates
        (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)) i = false := by
      apply GridCO.equivocates_false_of_unique
      intro x hx y hy
      obtain ⟨hx, hxi⟩ := List.mem_filter.mp hx
      obtain ⟨hy, hyi⟩ := List.mem_filter.mp hy
      exact (unique x (subset hx) (by simpa using hxi)).trans
        (unique y (subset hy) (by simpa using hyi)).symm
    have reflected := honest_proposal_support_back p E rho hx hΔ hrelay r (hsync.trans hef)
      hh b hb reader hr _ i rfl support
    have sourceSupport := reflected.resolve_right (by simp [sourceUnique])
    refine ⟨sourceSupport, target, rfl, ?_⟩
    have resolved := (List.mem_filter.mp sourceSupport).2
    by_cases hm : target ∈ (proposalState p rho (r + 1)).base.blocks
    · exact hm
    · simp [GridCO.resolvedHead?, GridCO.headTarget?, GridCO.resolveTarget,
        GridCO.resolutionTree, hm] at resolved
  · intro o ho i hi
    exact receipts.backward o (subset ho) i hi
  · intro o ho
    exact (List.mem_filter.mp ho).1

/-- Every raw genuine prefix lies on the next honest proposer's ordinary
walk. This result is independent of PC authority and finite admission. -/
theorem genuine_prefix_at_ordinary_proposal {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (a c : Block)
    (hc : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r = some c)
    (hp : Block.Preceq a c) :
    Block.Preceq a (GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1)) := by
  let st := (proposalState p rho (r + 1)).base
  have receipts := honest_proposal_transfer_receipts p E rho hx hΔ hnet hrelay r
    hsync hh b hb reader hr a
  have major := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r c hc
  have mono := GridCO.prefixSupport_mono p.engine
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r a c hp
  have pos : 0 < (GridCO.prefixSupportSeats p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r a).card := by
    rw [← GridCO.prefixSupport_eq_card]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp pos
  obtain ⟨o, ho, _, target, ht, hat⟩ := GridCO.prefixSupportSeats_witness p.engine _ r a i hi
  obtain ⟨_, target', ht', stored⟩ := receipts.forward o ho ⟨target, ht, hat⟩
  have eq : target' = target := Option.some.inj (ht'.symm.trans ht)
  subst target'
  have cover := @GridCO.forkChoice_covers_of_transfer GridCO.slowLeasePolicy p.n p.engine
    _ { st with obligations := [] } r (r + 1) st.blocks
    (GridCO.proposerView st (r + 1)) (GridCO.proposerSupportView st (r + 1)) a c hc hp receipts
    (by exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix a)))
    (fun d hn hd => (proposalState_paths p rho (r + 1)).1 target stored d hn
      (GridCO.prefix_trans d a target hd hat))
  simpa only [GridCO.forkChoice, GridCO.liveRoot, GridCO.liveTargets, List.filterMap_nil,
    List.foldl_nil] using! cover

end AvailableChain.SAPC
end
