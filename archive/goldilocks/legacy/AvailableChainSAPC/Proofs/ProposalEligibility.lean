module
public import AvailableChainSAPC.Proofs.ProposalRoots

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A transferred genuine majority leaves fewer than half the raw seats
available for detected equivocation. This uses the receipt interface,
not the actual fault cap. -/
theorem transfer_detected_minority {n : Nat} (p : Params) (source : GridCO.State n)
    (r : Slot) (tree : List Block) (raw support : List (GridCO.Wire n)) (b : Block)
    (h : GridCO.TransferReceipts p.engine source r tree raw support b)
    (hm : GridCO.voterCount (GridCO.lateVotes p.engine source r) <
      2 * GridCO.prefixSupport p.engine source r b) :
    2 * (detectedSeats raw).card < GridCO.voterCount raw := by
  let good := GridCO.prefixSupportSeats p.engine source r b
  let voters := (GridCO.seats n raw).toFinset
  have goodSub : good ⊆ voters := fun i hi =>
    (Finset.mem_filter.mp (h.supporters_subset hi)).1
  have badSub : detectedSeats raw ⊆ voters := by
    intro i hi
    simpa only [voters, GridCO.seats, List.mem_toFinset, List.mem_dedup] using
      (Finset.mem_filter.mp hi).1
  have disjoint : Disjoint good (detectedSeats raw) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨o, ho, hs, _⟩ := GridCO.prefixSupportSeats_witness p.engine source r b i hi
    have unique := GridCO.equivocates_false_of_unique raw i (by
      intro x hx y hy
      obtain ⟨hx, hxi⟩ := List.mem_filter.mp hx
      obtain ⟨hy, hyi⟩ := List.mem_filter.mp hy
      exact (h.seat_unique i o ho hs x hx (by simpa using hxi)).trans
        (h.seat_unique i o ho hs y hy (by simpa using hyi)).symm)
    have := (Finset.mem_filter.mp he).2
    simp [unique] at this
  have sum := Finset.card_le_card (Finset.union_subset goodSub badSub)
  rw [Finset.card_union_of_disjoint disjoint] at sum
  have count : voters.card = GridCO.voterCount raw :=
    List.toFinset_card_of_nodup (List.nodup_dedup _)
  have upper := Finset.card_le_card h.participants_subset
  rw [GridCO.lateSeats_card, count] at upper
  rw [GridCO.prefixSupport_eq_card] at hm
  change GridCO.voterCount (GridCO.lateVotes p.engine source r) < 2 * good.card at hm
  rw [count] at sum
  omega

/-- A clean honest proposer's raw view has a strict non-equivocating
majority from the preceding batch, including when the actual cap fails. -/
theorem clean_proposal_detected_minority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b) :
    let raw := GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)
    2 * (detectedSeats raw).card < GridCO.voterCount raw := by
  have early : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨c, hc, _⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r early .genesis
    (fun _ _ => GridCO.genesis_prefix _) _ hb.1
  have sync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact transfer_detected_minority p _ r _ _ _ c
    (honest_proposal_transfer_receipts p E rho hs.execution hΔ hs.partialSynchrony
      hs.acceptedRelay r sync hh b hb _ hb.1 c)
    (@GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r c hc)

/-- Any admitted block at the honest proposal's slot is that proposal.
Authentication applies to its original direct acceptance. -/
theorem stored_honest_proposal_slot_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (index : Nat) (reader : V) (c : Block)
    (hm : c ∈ (Run.stateBefore (sapc p) rho index reader).base.blocks)
    (hc : c.slot = s) : c = b := by
  have hn : c ≠ .genesis := by
    have positive := (honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb).1
    intro he
    have zero : s = 0 := by simpa only [he, Block.slot] using hc.symm
    exact (Nat.ne_of_gt positive) zero
  obtain ⟨j, _, t, o, raw, support, cert, he, hp, _⟩ :=
    stored_block_accepted p rho index reader c hn hm
  have hw := hx.wire j reader o t he
  change wellFormed p o = true at hw
  have ha : o.auth = .proposer s := by
    cases ho : o.auth <;> simp only [wellFormed, ho, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq] at hw
        rw [hw.1.1.1.1.1, hc]
  obtain ⟨t', _, hem⟩ := hx.unforgeable reader o t ⟨j, he⟩ (rho.proposerOf s) hb.1
    (by simp [Run.holder, ha])
  have ho : o = ⟨.proposer s, o.payload⟩ := by cases o; simp_all
  rw [ho] at hem
  have eq := honest_proposal_payload_unique p E rho hx.toScheduleWellFormed s b hb _ t' hem
  rw [hp] at eq
  exact (Msg.proposal.inj eq).1

/-- Every eligible block at the HEAD is either the fresh proposal or
already in the proposer's tree. Extra admitted paths cannot compete.
The old-block case uses a declared witness above detected equivocation. -/
theorem honest_proposal_eligible_reflects_of_minority {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (net : PartialSynchrony (sapc p) E rho) (relay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (sync : E.t_GST ≤ freezeTime p r)
    (minority : 2 * (detectedSeats (GridCO.proposerView
      (proposalState p rho (r + 1)).base (r + 1))).card <
        GridCO.voterCount (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)))
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (c : Block)
    (hc : c ∈ (headState p rho (r + 1) reader).base.blocks)
    (eligible : GridCO.goldfishEligible (headState p rho (r + 1) reader).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) reader).base (r + 1))
      (r + 1) c = true) :
    c = b ∨ c ∈ (proposalState p rho (r + 1)).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  rcases Bool.or_eq_true_iff.mp eligible with fresh | majority
  · left
    simp only [beq_iff_eq] at fresh
    simp only [headState, clock_blocks] at hc
    rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at hc
    exact stored_honest_proposal_slot_unique p E rho hx (r + 1) b hb _ reader c hc fresh
  · right
    have counts := honest_proposal_counts p E rho hx hΔ net
      relay r sync hh b hb reader hr
    have majority := of_decide_eq_true majority
    rw [← counts.1, ← counts.2.2 c] at majority
    have high : (detectedSeats (GridCO.proposerView
        (proposalState p rho (r + 1)).base (r + 1))).card <
        GridCO.goldfishScore (proposalState p rho (r + 1)).base.blocks
          (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1))
          (GridCO.proposerSupportView (proposalState p rho (r + 1)).base (r + 1)) c := by
      omega
    obtain ⟨_, _, target, _, _, _, _, stored, _, hprefix⟩ :=
      score_above_detected_witness _ _ _ c high
    by_cases hg : c = .genesis
    · simpa only [hg] using (proposalState_paths p rho (r + 1)).2
    · exact (proposalState_paths p rho (r + 1)).1 target stored c hg hprefix

/-- Clean Sleepy supplies the minority premise for the shared reflection proof. -/
theorem clean_honest_proposal_eligible_reflects {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (c : Block)
    (hc : c ∈ (headState p rho (r + 1) reader).base.blocks)
    (eligible : GridCO.goldfishEligible (headState p rho (r + 1) reader).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) reader).base (r + 1))
      (r + 1) c = true) :
    c = b ∨ c ∈ (proposalState p rho (r + 1)).base.blocks := by
  have sync : E.t_GST ≤ freezeTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact honest_proposal_eligible_reflects_of_minority p E rho hΔ hs.execution
    hs.partialSynchrony hs.acceptedRelay r hh sync
    (clean_proposal_detected_minority p E rho hΔ t₀ hs r hh b hb) b hb reader hr c hc eligible

end AvailableChain.SAPC
end
