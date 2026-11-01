module
public import AvailableChainSAPC.Proofs.BaseReceipts
public import AvailableChainSAPC.Proofs.Timely

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem timelyInput_receiptData (p : Params) {n : Nat} (st : State n) (t : Time) :
    GridCO.receiptData (timelyInput p st t).base = GridCO.receiptData st.base := by
  unfold timelyInput
  dsimp only
  split_ifs <;> rfl

theorem timelyInput_headStamp (p : Params) {n : Nat} (st : State n) (t : Time) :
    (timelyInput p st t).headStamp = st.headStamp := by
  unfold timelyInput
  dsimp only
  split_ifs <;> rfl

/-- A quorum of complete, stamped, exact-target HEADs meets the local N
test. Counts use seats, so duplicate signatures give no extra weight. -/
theorem timelyCandidate_of_seats (p : Params) {n : Nat} (st : State n)
    (r : Slot) (b : Block) (hr : 0 < r) (hb : b ≠ .genesis) (hslot : b.slot = r)
    (hpath : pathBefore st (earlyTime p r) b = true) (seats : Finset (Fin n))
    (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, ∃ data, (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads ∧
      data.target = b ∧ stampHead st ⟨.seat r i, data⟩ < earlyTime p r) :
    timelyCandidate p st r b = true := by
  have hsub : seats ⊆ timelySeats p st r b := by
    intro i hi
    obtain ⟨data, hm, ht, hs⟩ := hheads i hi
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    refine ⟨⟨.seat r i, data⟩, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩
    simp [headLabel?, ht, hs]
  have hc := hq.trans (Finset.card_le_card hsub)
  simpa [timelyCandidate, hr, hb, hslot, hpath, timelySeats, List.card_toFinset] using hc

/-- The early clock phase retains all data used by a qualifying N.
Its new fallback clock cannot change any stored first stamp. -/
theorem timelyCandidate_at_timelyInput (p : Params) {n : Nat} (st : State n)
    (hbase : GridCO.ReceiptStamped st.base) (hheads : ArchiveStamped st)
    (r : Slot) (b : Block) (t : Time) (hc : timelyCandidate p st r b = true) :
    timelyCandidate p (timelyInput p st t) r b = true := by
  have hp := GridCO.receiptPrefix_of_data_eq (timelyInput_receiptData p st t)
  have hparts := hc
  simp only [timelyCandidate, Bool.and_eq_true_iff, decide_eq_true_eq,
    bne_iff_ne, beq_iff_eq] at hparts
  apply timelyCandidate_of_seats p _ r b hparts.1.1.1.1 hparts.1.1.1.2
    hparts.1.1.2 (pathBefore_mono _ _ hp hbase _ b hparts.1.2)
    (timelySeats p st r b) (timelySeats_quorum p st r b hc)
  intro i hi
  obtain ⟨data, hm, ht, hs⟩ := timelySeats_witness p st r b i hi
  refine ⟨data, by simpa only [timelyInput_archive] using hm, ht, ?_⟩
  rwa [stampHead_eq_of_prefix st _ hheads
    (by rw [timelyInput_headStamp]) _ hm]

/-- Actual handler calls before the cutoff and an accepted target path
produce a qualifying N at that cutoff. This includes carried calls. -/
theorem timelyCandidate_of_delivered_quorum {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (v : V) (r : Slot) (b : Block)
    (hr : 0 < r) (hb : b ≠ .genesis) (hslot : b.slot = r)
    (hpath : ∃ index o raw support c t, o.payload = Msg.proposal b raw support c ∧
      Run.acceptsAt (sapc p) rho index v o t ∧ t < earlyTime p r)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, ∃ data index t, data.target = b ∧ voteTime p r ≤ t ∧
      t < earlyTime p r ∧
      Run.handlesAt (sapc p) rho index v (fromHead ⟨.seat r i, data⟩) t) :
    timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true := by
  refine timelyCandidate_of_seats p _ r b hr hb hslot ?_ seats hq ?_
  · obtain ⟨index, o, raw, support, c, t, hp, ha, ht⟩ := hpath
    exact accepted_path_before_cut p E rho hs index v o b raw support c hp t _ _ ha ht le_rfl
  · intro i hi
    obtain ⟨data, index, t, ht, hlo, hhi, hh⟩ := hheads i hi
    have he := early_handled_head_at_cut p E rho hs hΔ index v r i data t _ hlo hhi le_rfl hh
    exact ⟨data, he.1, ht, he.2⟩

/-- Under the cap, a delivered exact quorum is saved at the real early
tick. Receipt completeness, uniqueness, and the clock phase are all checked. -/
theorem timely_saved_of_delivered_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (v : V) (r : Slot) (b : Block)
    (hi : rho.events[index]? = some (.tick v (earlyTime p r)))
    (hr : 0 < r) (hb : b ≠ .genesis) (hslot : b.slot = r)
    (hpath : ∃ j o raw support c t, o.payload = Msg.proposal b raw support c ∧
      Run.acceptsAt (sapc p) rho j v o t ∧ t < earlyTime p r)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, ∃ data j t, data.target = b ∧ voteTime p r ≤ t ∧
      t < earlyTime p r ∧
      Run.handlesAt (sapc p) rho j v (fromHead ⟨.seat r i, data⟩) t) :
    savedTimely (Run.stateBefore (sapc p) rho (index + 1) v) r = some (some b) := by
  apply timely_saved_at_early p E rho hx hcap index v r b hi
  apply timelyCandidate_at_timelyInput p _ (base_receiptStamped_at_fold p _ v)
    (archiveStamped_at_fold p _ v)
  change timelyCandidate p (Run.stateBefore (sapc p) rho index v) r b = true
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hi]
  exact timelyCandidate_of_delivered_quorum p E rho hx.toScheduleWellFormed hΔ
    v r b hr hb hslot hpath seats hq hheads

/-- Synchronous honest preparations supply the delivered quorum above.
The accepted proposal path remains an explicit, separate input. -/
theorem timely_saved_of_synchronous_preparations {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (hnet : PartialSynchrony (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (index : Nat) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (hi : rho.events[index]? = some (.tick v (earlyTime p r)))
    (hr : 0 < r) (hb : b ≠ .genesis) (hslot : b.slot = r)
    (hsync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (hpath : ∃ j o raw support c t, o.payload = Msg.proposal b raw support c ∧
      Run.acceptsAt (sapc p) rho j v o t ∧ t < earlyTime p r)
    (seats : Finset (Fin p.n)) (hq : pcQuorum p ≤ seats.card)
    (hheads : ∀ i ∈ seats, rho.seatOf r i ∈ rho.honest ∧ ∃ data, data.target = b ∧
      Run.emits (sapc p) E rho (rho.seatOf r i)
        (fromHead ⟨.seat r i, data⟩) (voteTime p r)) :
    savedTimely (Run.stateBefore (sapc p) rho (index + 1) v) r = some (some b) := by
  apply timely_saved_of_delivered_quorum p E rho hx hcap hΔ index v r b hi
    hr hb hslot hpath seats hq
  intro i hseat
  obtain ⟨honest, data, ht, he⟩ := hheads i hseat
  have htime : max (voteTime p r) E.t_GST + E.Δ = earlyTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 2 * p.Δ
    ring
  obtain ⟨t, hlo, hhi, j, hh⟩ := hnet.broadcast _ honest _ _ he v hv
    (by rwa [htime]) rfl
  exact ⟨data, j, t, ht, hlo, by rwa [htime] at hhi, hh⟩

end AvailableChain.SAPC
end
