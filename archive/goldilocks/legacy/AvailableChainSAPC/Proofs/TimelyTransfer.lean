module
public import AvailableChainSAPC.Proofs.RecentArchive
public import AvailableChainSAPC.Proofs.HeadEmission
public import AvailableChainSAPC.Proofs.EffectiveScores
public import AvailableChainSAPC.Proofs.TimelyDelivery

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem headState_base_frozenAt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) :
    GridCO.frozenAt (headState p rho (r + 1) v).base r =
      some (GridCO.freezeView p.engine
        (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).base r) := by
  set_option backward.isDefEq.respectTransparency false in
  have ht : freezeTime p r < voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hnf : ¬ (0 ≤ voteTime p (r + 1) - 3 * p.Δ &&
      voteTime p (r + 1) == freezeTime p
        ((voteTime p (r + 1) - 3 * p.Δ) / (4 * p.Δ)).toNat) = true := by
    intro he
    have heq := of_decide_eq_true (Bool.and_eq_true_iff.mp he).2
    have ha := heq
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ =
      4 * p.Δ * _ + 3 * p.Δ at ha
    have hd := p.deltaPos
    have hdiv := congrArg (fun t : Int => t / p.Δ) ha
    simp only [show ∀ s : Int, 4 * p.Δ * s + p.Δ = (4 * s + 1) * p.Δ by
      intro s; ring, show ∀ s : Int, 4 * p.Δ * s + 3 * p.Δ = (4 * s + 3) * p.Δ by
      intro s; ring, Int.mul_ediv_cancel _ (ne_of_gt hd)] at hdiv
    omega
  unfold headState GridCO.frozenAt
  rw [clock_base_frozen]
  simp only [hnf]
  exact base_frozenAt_after_freeze p E rho hs hΔ r v hv _ ht hh

/-- A frozen raw key contributes its exact target; a dropped third copy
contributes through the same seat's retained equivocation evidence. -/
theorem frozen_exact_seat_scores (p : Params) {n : Nat} (st : State n)
    (r : Slot) (b : Block) (hslot : b.slot ≤ r) (hb : b ∈ st.base.blocks)
    (raw support : List (GridCO.Wire n)) (tree : List Block)
    (hf : GridCO.frozenAt st.base r = some (raw, support, tree))
    (i : Fin n)
    (hrec : (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ support ∧
        (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ raw ∨
      GridCO.equivocates raw i = true) :
    i ∈ GridCO.scoreSeats st.base.blocks (GridCO.voterView p.engine st.base (r + 1))
      (GridCO.voterSupportView p.engine st.base (r + 1)) b := by
  have hr : raw ⊆ GridCO.voterView p.engine st.base (r + 1) := by
    intro o ho
    simp only [GridCO.voterView, Nat.add_sub_cancel, hf]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ ho)
  have hs : support ⊆ GridCO.voterSupportView p.engine st.base (r + 1) := by
    intro o ho
    simp only [GridCO.voterSupportView, Nat.add_sub_cancel, hf]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ ho)
  apply scoreSeat_of_exact_or_equivocation st.base.blocks _ _ r b hslot hb i
  rcases hrec with ⟨hsp, hraw⟩ | he
  · exact Or.inl ⟨hs hsp, hr hraw⟩
  · exact Or.inr (GridCO.equivocates_mono _ _ i hr he)

/-- Timely N reaches the next frozen and merged view with score at
least q. This uses relay and the two-copy alternative, with no fault cap. -/
theorem timely_quorum_score_at_head {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V)
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r)) (b : Block)
    (hc : timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true) :
    pcQuorum p ≤ GridCO.goldfishScore (headState p rho (r + 1) w).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) b := by
  set_option backward.isDefEq.respectTransparency false in
  let src := Run.stateBeforeTime (sapc p) rho (earlyTime p r) v
  let frozen := Run.stateBeforeTime (sapc p) rho (freezeTime p r) w
  have hparts := hc
  simp only [timelyCandidate, Bool.and_eq_true_iff, decide_eq_true_eq,
    bne_iff_ne, beq_iff_eq] at hparts
  have hslot : b.slot = r := hparts.1.1.2
  have hef : earlyTime p r ≤ freezeTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have hfh : freezeTime p r ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hzero : 0 < freezeTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hcut : freezeTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hb : b ∈ frozen.base.blocks := by
    apply strict_block_relay p E rho hs _ _ hef hrelay v w hv hw b
    cases b with
    | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1.2).1
    | node parent slot r_slot root =>
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp hparts.1.2).1).1
  have hbh : b ∈ (headState p rho (r + 1) w).base.blocks := by
    simp only [headState, clock_blocks]
    exact (time_input_base_receiptPrefix p E rho hs _ _ hfh w).blocks.subset hb
  rw [GridCO.goldfishScore_eq_card]
  apply (timelySeats_quorum p src r b hc).trans
  apply Finset.card_le_card
  intro i hi
  obtain ⟨data, hm, ht, _⟩ := timelySeats_witness p src r b i hi
  have ha : (⟨.seat r i, data⟩ : HeadWire p.n) ∈ frozen.receivedHeads := by
    have he : src = Run.readAt (sapc p) rho (earlyTime p r - 1) v := by
      simp only [src, Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
    rw [he] at hm
    apply read_head_relay p E rho hs (earlyTime p r - 1) (freezeTime p r)
      ((Int.sub_lt_self _ (by decide : (0 : Int) < 1)).trans_le hef) _ v w hv hw _ hm
    intro u hu j o t htime hac reader hr hn
    exact hrelay u hu j o t (le_of_lt (Int.le_sub_one_iff.mp htime)) hac reader hr hn
  have hrec := archived_base_at_cut p E rho hs _ hzero r hcut w i data ha
  have hraw := (base_freezeView_at_input p E rho hs r w).1
  have stamps := time_input_stamps_lt p E rho hs _ hzero w
  apply frozen_exact_seat_scores p _ r b (le_of_eq hslot) hbh _ _ _
    (headState_base_frozenAt p E rho hs hΔ r w hw hh) i
  rcases hrec with hk | he
  · left
    have hkey : baseWire ⟨.seat r i, data⟩ =
        (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) := by
      simp [baseWire, baseHead, GridCO.fromHead, ht]
    rw [hkey] at hk
    refine ⟨List.mem_filter.mpr ⟨hk, ?_⟩, ?_⟩
    · simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
        Option.getD_some, GridCO.blockKnown]
      simpa only [hslot, le_refl, decide_true, stamps.1, stamps.2,
        Bool.and_true] using (show decide (b ∈ frozen.base.blocks) = true from decide_eq_true hb)
    · exact List.mem_filter.mpr ⟨hk, decide_eq_true (stamps.1 _)⟩
  · right
    change GridCO.equivocates (GridCO.freezeView p.engine frozen.base r).1 i = true
    rw [hraw]
    exact he

/-- The early clock cannot create a preparation quorum from later data. -/
theorem timelyCandidate_of_timelyInput (p : Params) {n : Nat} (st : State n)
    (hbase : GridCO.ReceiptStamped st.base) (hheads : ArchiveStamped st)
    (r : Slot) (b : Block) (t : Time)
    (hc : timelyCandidate p (timelyInput p st t) r b = true) :
    timelyCandidate p st r b = true := by
  have he := timelyInput_receiptData p st t
  have hp := GridCO.receiptPrefix_of_data_eq he.symm
  have hparts := hc
  simp only [timelyCandidate, Bool.and_eq_true_iff, decide_eq_true_eq,
    bne_iff_ne, beq_iff_eq] at hparts
  apply timelyCandidate_of_seats p st r b hparts.1.1.1.1 hparts.1.1.1.2
    hparts.1.1.2
    (pathBefore_mono _ _ hp (GridCO.stamped_of_data_eq he hbase) _ b hparts.1.2)
    (timelySeats p (timelyInput p st t) r b) (timelySeats_quorum p _ r b hc)
  intro i hi
  obtain ⟨data, hm, ht, hs⟩ := timelySeats_witness p _ r b i hi
  rw [timelyInput_archive] at hm
  refine ⟨data, hm, ht, ?_⟩
  rwa [stampHead_eq_of_prefix st _ hheads
    (by rw [timelyInput_headStamp]) _ hm] at hs

/-- A stored successful save identifies a quorum at its actual strict
early input, independent of subsequent archive growth. -/
theorem savedTimely_candidate_at_early {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (r : Slot) (b : Block)
    (h : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b)) :
    timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true := by
  obtain ⟨j, _, hj, hc⟩ := savedTimely_origin_before p rho index v r b h
  have hc' := timelyCandidate_of_timelyInput p _ (base_receiptStamped_at_fold p _ v)
    (archiveStamped_at_fold p _ v) r b _ hc
  change timelyCandidate p (Run.stateBefore (sapc p) rho j v) r b = true at hc'
  rwa [stateBefore_tick_eq_stateBeforeTime hs hj] at hc'

/-- The HEAD state is the state after the scheduled tick. Sleeping
readers execute that same clock phase. -/
theorem headState_at_tick {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v : V) (index : Nat)
    (hi : rho.events[index]? = some (.tick v (voteTime p r))) :
    Run.stateBefore (sapc p) rho (index + 1) v = headState p rho r v := by
  rw [stateBefore_succ_event hi]
  simp only [World.step, Function.update_self]
  rw [stateBefore_tick_eq_stateBeforeTime hs hi]
  rfl

/-- A timely N controls every active next HEAD whose finite root is
compatible. Relay supplies the quorum and paths; F4 handles any PC. -/
theorem timely_active_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V)
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : voteTime p (r + 1) ≤ rho.horizon)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r)) (b : Block)
    (hc : timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true)
    (ha : capBroken p (headState p rho (r + 1) w) = false)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (headData p rho (r + 1) w).target := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp
    (hx.tick_total w hw _ hpub hn hh)
  have he := headState_at_tick p E rho hx.toScheduleWellFormed (r + 1) w index hi
  have hf : freezeTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hscore := timely_quorum_score_at_head p E rho hx.toScheduleWellFormed hΔ r v w
    hv hw hf hrelay b hc
  have h := active_voter_quorum_covers p E rho hx (index + 1) w (r + 1)
    (selectedPC p (headState p rho (r + 1) w) (r + 1)) b
    (he.symm ▸ ha) (he.symm ▸ hscore) (he.symm ▸ hroot)
  simpa only [he, headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ha] using! h

theorem savedTimely_active_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (r : Slot) (v w : V)
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : voteTime p (r + 1) ≤ rho.horizon)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r)) (b : Block)
    (hc : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b))
    (ha : capBroken p (headState p rho (r + 1) w) = false)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (headData p rho (r + 1) w).target :=
  timely_active_head_covers p E rho hx hΔ r v w hv hw hh hrelay b
    (savedTimely_candidate_at_early p E rho hx.toScheduleWellFormed index v r b hc) ha hroot

/-- If a compatible-root HEAD leaves a timely target, it has disabled
PC control. Relay makes that disablement common before the first gate
where a PC from these preparations could have an effect. -/
theorem timely_departure_disables_by_gate {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (source reader other : V)
    (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest) (ho : other ∈ rho.honest)
    (hh : voteTime p (r + 1) ≤ rho.horizon)
    (hprep : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hrelay : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b : Block)
    (hc : timelyCandidate p
      (Run.stateBeforeTime (sapc p) rho (earlyTime p r) source) r b = true)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) reader).base) b)
    (hleave : ¬ Block.Preceq b (headData p rho (r + 1) reader).target) :
    capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) other) = true := by
  set_option backward.isDefEq.respectTransparency false in
  have hbroken : capBroken p (headState p rho (r + 1) reader) = true := by
    cases ha : capBroken p (headState p rho (r + 1) reader) with
    | false => exact (hleave (timely_active_head_covers p E rho hx hΔ r source reader
        hs hr hh hprep b hc ha hroot)).elim
    | true => rfl
  have ht : voteTime p (r + 1) - 1 < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ - 1 <
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  apply capBroken_mono p _ _ _ hbroken
  intro head hm
  simp only [headState, clock_archive] at hm
  have he : Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) =
      Run.readAt (sapc p) rho (voteTime p (r + 1) - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [he] at hm
  exact read_head_relay p E rho hx.toScheduleWellFormed _ _ ht
    (fun v hv j obj t htime hac w hw hn => hrelay v hv j obj t
      (le_of_lt (Int.le_sub_one_iff.mp htime)) hac w hw hn) reader other hr ho head hm

theorem synchronous_timely_active_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (hsync : E.t_GST ≤ earlyTime p r) (v w : V)
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : voteTime p (r + 1) ≤ rho.horizon) (b : Block)
    (hc : timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true)
    (ha : capBroken p (headState p rho (r + 1) w) = false)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (headData p rho (r + 1) w).target := by
  have he : max (earlyTime p r) E.t_GST + E.Δ = freezeTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  have hf : freezeTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  exact timely_active_head_covers p E rho hx hΔ r v w hv hw hh
    (he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hf)) b hc ha hroot

theorem healthy_timely_active_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (cut : Time) (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hcut : freezeTime p r ≤ cut) (v w : V)
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : voteTime p (r + 1) ≤ rho.horizon) (b : Block)
    (hc : timelyCandidate p (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v) r b = true)
    (ha : capBroken p (headState p rho (r + 1) w) = false)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (headData p rho (r + 1) w).target := by
  have he : earlyTime p r + E.Δ = freezeTime p r := by
    rw [hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  exact timely_active_head_covers p E rho hx hΔ r v w hv hw hh
    (he ▸ healthy_relayBy p E rho cut _ hrelay (he.symm ▸ hcut)) b hc ha hroot

end AvailableChain.SAPC
end
