module
public import AvailableChainSAPC.Proofs.MergedReceipts

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The shared genuine-support comparison also applies to a state's
own late pool. Equivocators cannot be surviving genuine supporters. -/
theorem self_late_transfer (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (b : Block) :
    GridCO.TransferReceipts p.engine st r st.blocks
      (GridCO.lateVotes p.engine st r) (GridCO.lateVotes p.engine st r) b := by
  refine ⟨?_, fun o ho _ _ => Or.inl ho, fun _ ho => ho⟩
  intro o ho htarget
  obtain ⟨target, ht, _⟩ := htarget
  have hearly := (List.mem_filter.mp ho).1
  have hres := (List.mem_filter.mp hearly).2
  simp only [GridCO.resolvedBefore_block, ht, Bool.and_eq_true_iff,
    decide_eq_true_eq, GridCO.blockKnown] at hres
  exact ⟨GridCO.earlyVotes_subset_lateVotes p.engine st r o hearly,
    target, ht, hres.1.1.1⟩

/-- A raw exact-target quorum and a genuine result at the same label
are compatible once the quorum reaches the late pool. The q bound is
absolute; this proof has no fault-cap or active-mode premise. -/
theorem raw_quorum_compatible_confirmation (p : Params) (st : GridCO.State p.n .block)
    (r : Slot) (b c : Block) (hb : b ∈ st.blocks) (hslot : b.slot ≤ r)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hrec : ∀ i ∈ seats, (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈
        GridCO.lateVotes p.engine st r ∨
      GridCO.equivocates (GridCO.lateVotes p.engine st r) i = true)
    (hc : SA.confirmation p st r = some c) : Block.Compatible c b := by
  have hscore : pcQuorum p ≤ GridCO.goldfishScore st.blocks
      (GridCO.lateVotes p.engine st r) (GridCO.lateVotes p.engine st r) b := by
    rw [GridCO.goldfishScore_eq_card]
    apply hq.trans
    apply Finset.card_le_card
    intro i hi
    apply scoreSeat_of_exact_or_equivocation st.blocks _ _ r b hslot hb i
    exact (hrec i hi).imp (fun hm => ⟨hm, hm⟩) id
  have hn : GridCO.voterCount (GridCO.lateVotes p.engine st r) ≤ p.n := by
    unfold GridCO.voterCount
    rw [← List.toFinset_card_of_nodup
      (show (GridCO.seats p.n (GridCO.lateVotes p.engine st r)).Nodup from List.nodup_dedup _)]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin p.n)
  have hmaj := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n st r c hc
  cases hcomp : Block.compatible c b with
  | true => exact hcomp
  | false =>
      have hsum := (self_late_transfer p st r c).conflicting_score_bound b hcomp
      have hquorum := (quorum_bounds p).2.2
      omega

/-- Relay of timely preparation evidence rules out a conflicting raw
genuine result at any reader's same-label gate. This statement concerns
the raw result before either the finite guard or the PC guard. -/
theorem timely_compatible_confirmation {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (source reader : V) (hsource : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (hrelay : RelayBy p rho (earlyTime p r) (gateTime p r)) (b c : Block)
    (hc : timelyCandidate p
      (Run.stateBeforeTime (sapc p) rho (earlyTime p r) source) r b = true)
    (hg : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r = some c) :
    Block.Compatible c b := by
  let src := Run.stateBeforeTime (sapc p) rho (earlyTime p r) source
  have hparts := hc
  simp only [timelyCandidate, Bool.and_eq_true_iff, decide_eq_true_eq,
    bne_iff_ne, beq_iff_eq] at hparts
  have htime : earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have hb : b ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base.blocks := by
    apply strict_block_relay p E rho hs _ _ htime hrelay source reader hsource hr b
    cases b with
    | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1.2).1
    | node parent slot r_slot root =>
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp hparts.1.2).1).1
  apply raw_quorum_compatible_confirmation p _ r b c hb (le_of_eq hparts.1.1.2)
    (timelySeats p src r b) (timelySeats_quorum p src r b hc) _ hg
  intro i hi
  obtain ⟨data, hm, ht, _⟩ := timelySeats_witness p src r b i hi
  have he : src = Run.readAt (sapc p) rho (earlyTime p r - 1) source := by
    simp only [src, Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [he] at hm
  have hz : 0 < gateTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hcut : gateTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have h := read_head_base_relay p E rho hs (earlyTime p r - 1) (gateTime p r)
    ((Int.sub_lt_self _ (by decide : (0 : Int) < 1)).trans_le htime) hz r hcut
    (fun v hv j obj t hle hac w hw hn => hrelay v hv j obj t
      (le_of_lt (Int.le_sub_one_iff.mp hle)) hac w hw hn) source reader hsource hr i data hm
  simpa only [base_lateVotes_at_input p E rho hs, baseWire, baseHead, GridCO.fromHead, ht]
    using h

end AvailableChain.SAPC
end
