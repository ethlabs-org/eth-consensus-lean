module
public import AvailableChainSAPC.Proofs.RecoveryRows

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Snapshot keys relay back to the raw source gate, including evidence
for keys omitted from the two-target cache. -/
theorem release_raw_at_gate {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (source reader : V) (hsr : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (relay : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n) (i : Fin p.n) (seat : GridCO.headSeat? o = some i)
    (stored : o ∈ GridCO.votesAt
      (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r) :
    o ∈ GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r ∨
      GridCO.equivocates (GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) i = true := by
  have label : GridCO.headLabel? o = some r := by simpa using (List.mem_filter.mp stored).2
  obtain ⟨target, rfl⟩ := GridCO.head_wire_shape o r i label seat
  obtain ⟨data, archived, targetEq⟩ := baseArchived_head _ (baseArchived_at_fold p _ reader)
    r i target (List.mem_filter.mp stored).1
  have readEq : Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) =
      Run.readAt (sapc p) rho (voteTime p (r + 1) - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  change (⟨.seat r i, data⟩ : HeadWire p.n) ∈
    (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).receivedHeads at archived
  rw [readEq] at archived
  have before : voteTime p (r + 1) - 1 < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ - 1 <
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  have positive : 0 < gateTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have recent : gateTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast; linarith [p.deltaPos]
  have transported := read_head_base_relay p E rho hs _ _ before positive r recent
    (fun v hv j obj t ht hac w hw hn => relay v hv j obj t
      (le_of_lt (Int.le_sub_one_iff.mp ht)) hac w hw hn)
    reader source hr hsr i data archived
  simpa only [baseWire, baseHead, GridCO.fromHead, targetEq,
    base_lateVotes_at_input p E rho hs] using transported

/-- Reverse relay prevents a surviving source supporter from equivocating
in another reader's release snapshot. -/
theorem cleanSupport_release_unique {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (source reader : V) (hsr : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (relay : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n) (i : Fin p.n) (seat : GridCO.headSeat? o = some i)
    (clean : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) :
    ∀ key ∈ GridCO.votesAt
      (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r,
      GridCO.headSeat? key = some i → key = o := by
  intro key stored sameSeat
  rcases release_raw_at_gate p E rho hs r source reader hsr hr relay key i sameSeat stored
    with late | bad
  · exact (GridCO.cleanSupport_eq_of_late_same_seat p.engine _ r i o key
      clean late seat sameSeat).symm
  · rw [cleanSupport_not_equivocating p _ r o i seat clean] at bad
    contradiction

/-- Genuine supporters reach the release snapshot as resolved keys.
Forward relay brings the key and path; reverse relay excludes cache eviction. -/
theorem cleanSupport_resolved_at_release {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (source reader : V)
    (hsr : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (forward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (back : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n) (i : Fin p.n) (seat : GridCO.headSeat? o = some i)
    (clean : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) :
    o ∈ GridCO.votesAt
        (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r ∧
      GridCO.resolvedBefore
        (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base o
        (GridCO.releaseTime p.engine r) = true := by
  have early := (List.mem_filter.mp clean).1
  have label : GridCO.headLabel? o = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp early).1).2
  obtain ⟨b, rfl⟩ := GridCO.head_wire_shape o r i label seat
  obtain ⟨block, key⟩ := early_head_at_freeze p E rho hs hΔ r source reader hsr hr forward i b early
  have time : freezeTime p r ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast; linarith [p.deltaPos]
  have receipts := time_input_base_receiptPrefix p E rho hs _ _ time reader
  have subset : (GridCO.freezeView p.engine
        (Run.stateBeforeTime (sapc p) rho (freezeTime p r) reader).base r).1 ⊆
      GridCO.votesAt (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r := by
    rw [(base_freezeView_at_input p E rho hs r reader).1]
    intro x hx
    exact List.mem_filter.mpr ⟨receipts.votes.subset (List.mem_filter.mp hx).1,
      (List.mem_filter.mp hx).2⟩
  have noEq : GridCO.equivocates
      (GridCO.votesAt (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r)
      i = false := by
    apply GridCO.equivocates_false_of_unique
    intro a ha b hb
    have unique := cleanSupport_release_unique p E rho hs r source reader hsr hr back _ i rfl clean
    exact (unique a (List.mem_filter.mp ha).1 (by simpa using (List.mem_filter.mp ha).2)).trans
      (unique b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)).symm
  have support : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈
      (GridCO.freezeView p.engine
        (Run.stateBeforeTime (sapc p) rho (freezeTime p r) reader).base r).2.1 := by
    rcases key with member | equiv
    · exact member
    · have bad := GridCO.equivocates_mono _ _ i subset equiv
      rw [noEq] at bad
      contradiction
  have raw := (List.mem_filter.mp support).1
  have atRelease := subset (by
    rw [(base_freezeView_at_input p E rho hs r reader).1]
    exact raw)
  refine ⟨atRelease, ?_⟩
  have slot := (List.mem_filter.mp early).2
  simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?, Option.getD_some,
    Bool.and_eq_true_iff, decide_eq_true_eq] at slot
  have positive : 0 < voteTime p (r + 1) := by
    change 0 < 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  have stamps := time_input_stamps_lt p E rho hs _ positive reader
  have releaseEq : GridCO.releaseTime p.engine r = voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 5 * p.Δ =
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast; ring
  simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?, Option.getD_some,
    Bool.and_eq_true_iff, decide_eq_true_eq, GridCO.blockKnown, releaseEq]
  exact ⟨⟨⟨receipts.blocks.subset block, slot.1.1.2⟩, stamps.1 _⟩, stamps.2 _⟩

/-- The shared SA counting theorem applies to the actual SA-PC release
snapshot. Support can include faulty seats; no PC premise is used. -/
theorem snapshot_from_engine {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (relay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (sync : E.t_GST ≤ earlyTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B K : Block) (conflict : Block.compatible K B = false) :
    GridCO.prefixSupport p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B ≤
      GridCO.releaseCount p.engine
        (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader).base r K := by
  obtain ⟨forward, back⟩ := synchronous_transfer_relays p E rho hΔ relay r sync horizon
  rw [GridCO.prefixSupport_eq_card]
  apply GridCO.snapshot_count_of_relayed_seats
  · intro i member
    obtain ⟨o, clean, seat, target, targetEq, below⟩ := GridCO.prefixSupportSeats_witness
      p.engine _ r B i member
    obtain ⟨raw, resolved⟩ := cleanSupport_resolved_at_release p E rho hx.toScheduleWellFormed
      hΔ r source reader hs hr forward back o i seat clean
    refine ⟨o, raw, resolved, seat, ?_⟩
    have conf := GridCO.conflict_mono_descendant B target K below conflict
    have conf' : Block.compatible target K = false := by
      simpa [Block.compatible, Bool.or_comm] using conf
    simp [targetEq, conf']
  · intro i member
    obtain ⟨o, clean, seat, _⟩ := GridCO.prefixSupportSeats_witness p.engine _ r B i member
    apply GridCO.equivocates_false_of_unique
    intro a ha b hb
    have unique := cleanSupport_release_unique p E rho hx.toScheduleWellFormed r
      source reader hs hr back o i seat clean
    exact (unique a (List.mem_filter.mp ha).1 (by simpa using (List.mem_filter.mp ha).2)).trans
      (unique b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)).symm

/-- A fast source removes every conflicting threshold-τ lease at equality. -/
theorem fast_source_rows_compatible {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (relay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (sync : E.t_GST ≤ earlyTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B : Block) (fast : SA.releaseThreshold p ≤ GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B)
    (K : Block) (g : Nat) (d : Time)
    (row : (K, g, d) ∈ (headState p rho (r + 1) reader).base.obligations) :
    Block.Compatible K B := by
  obtain ⟨old, _, count⟩ := head_row_survives_release p rho r reader K g d row
  obtain ⟨s, C, _, _, _, admission, _⟩ := time_input_row_admitted_source p E rho
    hx.toScheduleWellFormed _ reader K g d old
  have level := (SA.admissionLevels_iff p _ s K g).mp admission |>.1
  cases comp : Block.compatible K B with
  | true => exact comp
  | false =>
    have lower := snapshot_from_engine p E rho hx hΔ relay r sync horizon
      source reader hs hr B K comp
    rw [level] at count
    omega

end AvailableChain.SAPC
end
