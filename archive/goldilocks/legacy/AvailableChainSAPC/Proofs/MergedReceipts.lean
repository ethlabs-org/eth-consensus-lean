module
public import AvailableChainSAPC.Proofs.TimelyTransfer

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The exact reverse receipt condition used by genuine transfer. Local
receipt retention can supply it without a future relay deadline. -/
def BackReceipts {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (source reader : V) : Prop :=
  ∀ o i, GridCO.headSeat? o = some i →
    o ∈ GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1) →
    o ∈ GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r ∨
      GridCO.equivocates (GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) i = true

theorem headState_voterView_archived {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) (v : V) (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.voterView p.engine (headState p rho s v).base s) :
    ∃ head ∈ (headState p rho s v).receivedHeads, baseWire head = o := by
  let events := rho.events.filter (fun e => decide (e.time < voteTime p s)) ++
    [.tick v (voteTime p s)]
  have he : (events.foldl World.step World.init) v = headState p rho s v := by
    simp only [events, List.foldl_append, List.foldl_cons, List.foldl_nil,
      World.step, Function.update_self]
    rfl
  exact voterView_archived p _ (he ▸ baseArchived_at_fold p events v)
    (he ▸ frozenViewsStored_at_fold p events v) (he ▸ proposalViewsArchived_at_fold p events v)
    s o ho

theorem headState_voterView_label {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) (v : V) (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.voterView p.engine (headState p rho s v).base s) :
    GridCO.headLabel? o = some (s - 1) := by
  apply voterView_label p _ _ s o ho
  have h := frozenViewsStored_at_fold p
    ((rho.events.filter (fun e => decide (e.time < voteTime p s))) ++ [.tick v (voteTime p s)]) v
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    World.step, Function.update_self] using! h

/-- No receipt in a strict gate input is excluded from its late pool. -/
theorem base_lateVotes_at_input {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v : V) :
    GridCO.lateVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r =
      GridCO.votesAt (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  apply List.filter_eq_self.mpr
  intro o _
  apply decide_eq_true
  exact (time_input_stamps_lt p E rho hs _ (by
    change 0 < 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]) v).1 o

/-- Every key in the complete merged HEAD view relays back to the
source gate's late pool, or supplies two-copy evidence there. The proof
includes all proposal-carried keys and requires no equality of raw sets. -/
theorem voter_raw_at_gate {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (source reader : V) (hsr : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (hrelay : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1)) :
    o ∈ GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r ∨
      GridCO.equivocates (GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) i = true := by
  set_option backward.isDefEq.respectTransparency false in
  have hl : GridCO.headLabel? o = some r := by
    simpa using headState_voterView_label p rho (r + 1) reader o ho
  obtain ⟨target, rfl⟩ := GridCO.head_wire_shape o r i hl hi
  obtain ⟨head, hm, he⟩ := headState_voterView_archived p rho (r + 1) reader _ ho
  have ha : head.auth = .seat r i := congrArg Signed.auth he
  have hshape : head = ⟨.seat r i, head.payload⟩ := by cases head; simp_all
  rw [hshape] at hm he
  simp only [headState, clock_archive] at hm
  have hrtime : voteTime p (r + 1) - 1 < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ - 1 <
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hz : 0 < gateTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hcut : gateTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hread : Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) =
      Run.readAt (sapc p) rho (voteTime p (r + 1) - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [hread] at hm
  have h := read_head_base_relay p E rho hs _ _ hrtime hz r hcut
    (fun v hv j obj t ht hac w hw hn => hrelay v hv j obj t
      (le_of_lt (Int.le_sub_one_iff.mp ht)) hac w hw hn)
    reader source hr hsr i head.payload hm
  rw [base_lateVotes_at_input p E rho hs, he] at *
  exact h

/-- Every merged key is already in this reader's archive. Local retention
supplies the reverse comparison even if the run stops before the gate. -/
theorem local_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) : BackReceipts p rho r reader reader := by
  set_option backward.isDefEq.respectTransparency false in
  intro o i hi ho
  have hl : GridCO.headLabel? o = some r := by
    simpa using headState_voterView_label p rho (r + 1) reader o ho
  obtain ⟨target, rfl⟩ := GridCO.head_wire_shape o r i hl hi
  obtain ⟨head, hm, he⟩ := headState_voterView_archived p rho (r + 1) reader _ ho
  have ha : head.auth = .seat r i := congrArg Signed.auth he
  have hshape : head = ⟨.seat r i, head.payload⟩ := by cases head; simp_all
  rw [hshape] at hm he
  simp only [headState, clock_archive] at hm
  have htime : voteTime p (r + 1) ≤ gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have stored : (⟨.seat r i, head.payload⟩ : HeadWire p.n) ∈
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).receivedHeads := by
    rw [time_input_eq_event_prefix p E rho hs] at hm ⊢
    exact stateBefore_archive_mono p rho
      (read_length_mono (rho := rho) _ _ (sub_le_sub_right htime 1)) reader hm
  have hz : 0 < gateTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hcut : gateTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have h := archived_base_at_cut p E rho hs _ hz r hcut reader i head.payload stored
  rw [base_lateVotes_at_input p E rho hs, he] at *
  exact h

theorem synchronous_voter_raw_at_gate {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (hsync : E.t_GST ≤ voteTime p (r + 1)) (hh : gateTime p r ≤ rho.horizon)
    (source reader : V) (hsr : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1)) :
    o ∈ GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r ∨
      GridCO.equivocates (GridCO.lateVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r) i = true := by
  have he : max (voteTime p (r + 1)) E.t_GST + E.Δ = gateTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ + p.Δ =
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    ring
  exact voter_raw_at_gate p E rho hs r source reader hsr hr
    (he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hh)) o i hi ho

end AvailableChain.SAPC
end
