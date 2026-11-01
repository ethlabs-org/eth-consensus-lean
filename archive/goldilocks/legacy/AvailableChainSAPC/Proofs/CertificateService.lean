module
public import AvailableChainSAPC.Proofs.HeadEmission
public import AvailableChainSAPC.Proofs.ProposalDelivery
public import AvailableChainSAPC.Proofs.AckDelivery

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Each duty gets its own honest-seat set. No cross-label seat identity
is used by the protocol or by this counting interface. -/
def honestSeats {V : Type} [DecidableEq V] (p : Params) (rho : Run V (sapc p))
    (r : Slot) : Finset (Fin p.n) :=
  rho.honest.map (rho.seatOf r).symm.toEmbedding

theorem mem_honestSeats {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (i : Fin p.n) :
    i ∈ honestSeats p rho r ↔ rho.seatOf r i ∈ rho.honest := by
  simp [honestSeats]

theorem honestSeats_quorum {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (rho : Run V (sapc p)) (hcap : FaultBound (sapc p) (pcFaultCap p) rho) (r : Slot) :
    pcQuorum p ≤ (honestSeats p rho r).card := by
  have hc : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf r)).symm
  have htotal : rho.honest.card + (faulty rho).card = p.n := by
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  simpa [honestSeats] using (capped_counts p _ _ hcap htotal).2.2.1

/-- Awake seats at this duty; preparation and ack duties use separate sets. -/
def awakeSeats {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (r : Slot) : Finset (Fin p.n) :=
  (awakeAt E rho.honest (voteTime p r)).map (rho.seatOf r).symm.toEmbedding

theorem mem_awakeSeats {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (r : Slot) (i : Fin p.n) :
    i ∈ awakeSeats p E rho r ↔
      rho.seatOf r i ∈ rho.honest ∧ E.awake (rho.seatOf r i) (voteTime p r) = true := by
  simp [awakeSeats, awakeAt]

/-- Full turnout supplies the awake count used by the new service theorem. -/
theorem full_awake_quorum {V : Type} [DecidableEq V] [Fintype V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (r : Slot) (full : ∀ v ∈ rho.honest, E.awake v (voteTime p r) = true) :
    pcQuorum p ≤ (awakeAt E rho.honest (voteTime p r)).card := by
  have eq : awakeAt E rho.honest (voteTime p r) = rho.honest :=
    Finset.filter_eq_self.mpr full
  rw [eq]
  simpa [honestSeats] using honestSeats_quorum p rho cap r

theorem savedTimely_after_tick {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (index : Nat) (v : V)
    (r : Slot) (b : Block) (t cut : Time)
    (hi : rho.events[index]? = some (.tick v t)) (ht : t < cut)
    (hsave : savedTimely (Run.stateBefore (sapc p) rho (index + 1) v) r = some (some b)) :
    savedTimely (Run.stateBeforeTime (sapc p) rho cut v) r = some (some b) := by
  rw [time_input_eq_event_prefix p E rho hs]
  apply savedTimely_at_later_input p rho (v := v) _ r (some b) hsave
  exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
    (Int.le_sub_one_iff.mpr ht))

/-- An awake quorum under the cap supplies the seat count and actual
handler calls. Only the fork-choice equality remains as a proof input;
the proposal path and early clock tick follow from the engine. -/
theorem quorum_preparations_saved {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : earlyTime p s ≤ rho.horizon)
    (hawake : pcQuorum p ≤ (awakeAt E rho.honest (voteTime p s)).card)
    (hchoice : ∀ v ∈ rho.honest, (headData p rho s v).target = b)
    (reader : V) (hr : reader ∈ rho.honest) (cut : Time) (hcut : earlyTime p s < cut) :
    savedTimely (Run.stateBeforeTime (sapc p) rho cut reader) s = some (some b) := by
  have hpe : proposalTime p s ≤ voteTime p s := by
    change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ
    linarith [p.deltaPos]
  have hve : voteTime p s ≤ earlyTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have hpub : PublicTime E (earlyTime p s) := by
    refine ⟨4 * s + 2, ?_⟩
    change 4 * p.Δ * (s : Time) + 2 * p.Δ = (4 * s + 2 : Nat) * E.Δ
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ earlyTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp (hx.tick_total reader hr _ hpub hn hh)
  apply savedTimely_after_tick p E rho hx.toScheduleWellFormed index reader s b _ cut hi hcut
  obtain ⟨hpos, hne, hslot⟩ := honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb
  refine timely_saved_of_synchronous_preparations p E rho hx hcap hnet hΔ
    index reader hr s b hi hpos hne hslot (hsync.trans hpe) hh ?_
    (awakeSeats p E rho s) (by simpa [awakeSeats] using hawake) ?_
  · obtain ⟨_, _, hem⟩ := honest_proposal_views p E rho hx.toScheduleWellFormed s b hb
    obtain ⟨j, t, _, ht, ha⟩ := synchronous_proposal_accepted p E rho hx hΔ hnet s hsync
      (hve.trans hh) (rho.proposerOf s) reader hb.1 hr b _ _ _ hem
    exact ⟨j, _, _, _, _, t, rfl, ha, ht.trans_le hve⟩
  · intro i hi
    obtain ⟨honest, awake⟩ := (mem_awakeSeats p E rho s i).mp hi
    exact ⟨honest, headData p rho s (rho.seatOf s i), hchoice _ honest,
      honest_head_emitted p E rho hx.toScheduleWellFormed hΔ s i honest awake
        (hve.trans hh)⟩

/-- The full-participation interface follows from awake quorum service. -/
theorem full_preparations_saved {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : earlyTime p s ≤ rho.horizon)
    (hawake : ∀ v ∈ rho.honest, E.awake v (voteTime p s) = true)
    (hchoice : ∀ v ∈ rho.honest, (headData p rho s v).target = b)
    (reader : V) (hr : reader ∈ rho.honest) (cut : Time) (hcut : earlyTime p s < cut) :
    savedTimely (Run.stateBeforeTime (sapc p) rho cut reader) s = some (some b) :=
  quorum_preparations_saved p E rho hx hΔ hcap hnet s b hb hsync hh (full_awake_quorum p E rho hcap
    s hawake) hchoice reader hr cut hcut

/-- A completed save supplies the ack exactly when the actual next HEAD
extends it. The next duty clock does not replace the saved value. -/
theorem headData_ack_of_saved {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) (b : Block) (v : V)
    (hsave : savedTimely (Run.stateBeforeTime (sapc p) rho (voteTime p (s + 1)) v) s =
      some (some b)) (hext : Block.Preceq b (headData p rho (s + 1) v).target) :
    (headData p rho (s + 1) v).ack = some (s, b) := by
  set_option backward.isDefEq.respectTransparency false in
  have hs : savedTimely (headState p rho (s + 1) v) s = some (some b) := by
    simpa only [headState, savedTimely, clock_timely_at_vote] using! hsave
  change ackFor (headState p rho (s + 1) v) (s + 1)
    (headData p rho (s + 1) v).target = _
  simp [ackFor, hs, show Block.preceq b (headData p rho (s + 1) v).target = true from hext]

/-- Exact preparations and extending next HEADs complete a PC before
the 6Δ gate. Seat quorums, signatures, saves, paths, and deadlines all
follow from the engine and fixed delivery premises. Choice transfer and
compatibility of a higher stored PC remain separate obligations. -/
theorem quorum_preparation_ack_service {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : gateTime p s ≤ rho.horizon)
    (hprepAwake : pcQuorum p ≤ (awakeAt E rho.honest (voteTime p s)).card)
    (hackAwake : pcQuorum p ≤ (awakeAt E rho.honest (voteTime p (s + 1))).card)
    (hprep : ∀ v ∈ rho.honest, (headData p rho s v).target = b)
    (hack : ∀ v ∈ rho.honest, Block.Preceq b (headData p rho (s + 1) v).target)
    (reader : V) (hr : reader ∈ rho.honest) :
    (∃ c, c.slot = s ∧ c.target = b ∧
      pcValid p (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader) c = true) ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader).bestPC = some d ∧
        s ≤ d.slot := by
  have htimes : proposalTime p s ≤ voteTime p s ∧
      voteTime p s ≤ earlyTime p s ∧ earlyTime p s < voteTime p (s + 1) ∧
      voteTime p (s + 1) ≤ gateTime p s := by
    change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ ∧
      4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ ∧
      4 * p.Δ * (s : Time) + 2 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ∧
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    push_cast
    constructor
    · linarith [p.deltaPos]
    constructor
    · linarith [p.deltaPos]
    constructor <;> linarith [p.deltaPos]
  have hearly := (le_of_lt htimes.2.2.1).trans (htimes.2.2.2.trans hh)
  have hackSync := hsync.trans (htimes.1.trans (htimes.2.1.trans (le_of_lt htimes.2.2.1)))
  obtain ⟨hpos, hne, hslot⟩ := honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb
  refine synchronous_ack_quorum_complete p E rho hx.toScheduleWellFormed hΔ hnet
    reader hr s b hpos hne hslot hackSync hh ?_
    (awakeSeats p E rho (s + 1)) (by simpa [awakeSeats] using hackAwake) ?_
  · obtain ⟨_, _, hem⟩ := honest_proposal_views p E rho hx.toScheduleWellFormed s b hb
    obtain ⟨j, t, _, ht, ha⟩ := synchronous_proposal_accepted p E rho hx hΔ hnet s hsync
      (htimes.2.1.trans hearly) (rho.proposerOf s) reader hb.1 hr b _ _ _ hem
    exact accepted_block_before_cut p E rho hx.toScheduleWellFormed j reader _ b _ _ _
      rfl t _ ha (ht.trans_le (htimes.2.1.trans
        ((le_of_lt htimes.2.2.1).trans htimes.2.2.2)))
  · intro i hi
    obtain ⟨honest, awake⟩ := (mem_awakeSeats p E rho (s + 1) i).mp hi
    have hsave := quorum_preparations_saved p E rho hx hΔ hcap hnet s b hb hsync hearly
      hprepAwake hprep _ honest _ htimes.2.2.1
    refine ⟨honest, headData p rho (s + 1) (rho.seatOf (s + 1) i),
      headData_ack_of_saved p rho s b _ hsave (hack _ honest), hack _ honest,
      headData_target_slot p E rho hx.toScheduleWellFormed (s + 1) _,
      honest_head_emitted p E rho hx.toScheduleWellFormed hΔ (s + 1) i honest
        awake (htimes.2.2.2.trans hh), ?_⟩
    rw [← ack_early_eq_gate]
    exact headData_target_at_early p E rho hx.toScheduleWellFormed hΔ hrelay (s + 1)
      hackSync (by rwa [ack_early_eq_gate]) _ reader honest hr

/-- The full-participation interface follows from awake quorum service. -/
theorem full_preparation_ack_service {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : gateTime p s ≤ rho.horizon)
    (hprepAwake : ∀ v ∈ rho.honest, E.awake v (voteTime p s) = true)
    (hackAwake : ∀ v ∈ rho.honest, E.awake v (voteTime p (s + 1)) = true)
    (hprep : ∀ v ∈ rho.honest, (headData p rho s v).target = b)
    (hack : ∀ v ∈ rho.honest, Block.Preceq b (headData p rho (s + 1) v).target)
    (reader : V) (hr : reader ∈ rho.honest) :
    (∃ c, c.slot = s ∧ c.target = b ∧
      pcValid p (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader) c = true) ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader).bestPC = some d ∧
        s ≤ d.slot :=
  quorum_preparation_ack_service p E rho hx hΔ hcap hnet hrelay s b hb hsync hh (full_awake_quorum
    p E rho hcap s hprepAwake) (full_awake_quorum p E rho hcap (s + 1) hackAwake) hprep hack reader
    hr

end AvailableChain.SAPC
end
