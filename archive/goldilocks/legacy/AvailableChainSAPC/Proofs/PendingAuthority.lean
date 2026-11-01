module
public import AvailableChainSAPC.Proofs.HealthyHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A timely source older than the pending label must have continued
through the last healthy batch if PC control is still active later.
The source may be disclosed only after the healthy cutoff. -/
theorem healthy_timely_continues_of_later_active
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (later : earlyTime p r < e.time) (observer : V) (ho : observer ∈ rho.honest)
    (active : capBroken p (Run.stateBefore (sapc p) rho i observer) = false)
    (s : Slot) (hsr : s < r) (B : Block) (source : HonestTimelySource p rho i s B)
    (w : V) (hw : w ∈ rho.honest) : Block.Preceq B (headData p rho r w).target := by
  have hs := hx.toScheduleWellFormed
  have sleepy := healthy_sleepy_through_early p E rho hx roots cut net relay majority r hearly hh
  have pub : PublicTime E (earlyTime p r) := by
    refine ⟨4 * r + 2, ?_⟩
    change 4 * p.Δ * (r : Time) + 2 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ earlyTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨m, tick⟩ := List.mem_iff_getElem?.mp (hs.tick_total observer ho _ pub nonneg hh)
  have hmi := eventIndex_lt_of_time_lt hs tick he later
  have activeM : capBroken p (Run.stateBefore (sapc p) rho m observer) = false := by
    cases hm : capBroken p (Run.stateBefore (sapc p) rho m observer) with
    | false => rfl
    | true =>
      have bad := capBroken_before_mono p rho hmi.le observer hm
      rw [active] at bad
      cases bad
  have prefixTick := (runPrefix_event_iff hs (earlyTime p r) m _).mpr ⟨tick, le_refl _⟩
  have bound := (index_lt_read_length_iff hs (earlyTime p r) tick).mpr (le_refl _)
  have states := runPrefix_stateBefore (rho := rho) (earlyTime p r) m bound.le
  have invariant := clean_run_invariant p (prefixEnv E (earlyTime p r))
    (runPrefix rho (earlyTime p r)) hΔ 0 sleepy m
    (by rw [runPrefix_events hs]; exact bound.le)
  obtain ⟨v, hv, j, _, early, saved⟩ := source
  have earlyLt : earlyTime p s < earlyTime p r := by
    have cast : (s : Time) < r := by exact_mod_cast hsr
    change 4 * p.Δ * (s : Time) + 2 * p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have hjm := eventIndex_lt_of_time_lt hs early tick earlyLt
  have prefixEarly := (runPrefix_event_iff hs (earlyTime p r) j _).mpr ⟨early, earlyLt.le⟩
  have saved' : savedTimely
      (Run.stateBefore (sapc p) (runPrefix rho (earlyTime p r)) (j + 1) v) s = some (some B) := by
    rw [runPrefix_stateBefore (earlyTime p r) (j + 1)
      ((Nat.succ_le_of_lt hjm).trans bound.le)]
    exact saved
  have gateBound : gateTime p s ≤ earlyTime p r := by
    have cast : (s : Time) + 1 ≤ r := by exact_mod_cast hsr
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have voteBound : voteTime p r < earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have result := timely_continues_before_active_input p (prefixEnv E (earlyTime p r))
    (runPrefix rho (earlyTime p r)) hΔ 0 sleepy m _ prefixTick invariant observer ho
    (states.symm ▸ activeM) r s B ⟨v, hv, j, hjm, prefixEarly, saved'⟩
    gateBound hsr voteBound w hw
  simpa only [headData, headState, runPrefix_stateBeforeTime hs (earlyTime p r)
    (voteTime p r) voteBound.le] using result

/-- Any still-active valid PC no later than the pending label is
compatible with its protected prefix. Old sources use healthy transfer;
a same-label source uses an honest exact preparation. -/
theorem healthy_pending_validPC_compatible
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (later : earlyTime p r < e.time) (v : V) (hv : v ∈ rho.honest)
    (active : capBroken p (Run.stateBefore (sapc p) rho i v) = false)
    (B : Block) (cover : ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target)
    (c : PC p.n) (valid : pcValid p (Run.stateBefore (sapc p) rho i v) c = true)
    (slot : c.slot ≤ r) : Block.Compatible c.target B := by
  have sleepy := healthy_sleepy_through_early p E rho hx roots cut net relay majority r hearly hh
  have ha : (faulty rho).card < pcQuorum p :=
    sleepy_quorum_above_faults p (prefixEnv E (earlyTime p r))
      (runPrefix rho (earlyTime p r)) 0 sleepy
  rcases lt_or_eq_of_le slot with older | same
  · obtain ⟨w, hw, j, hj, tick, saved⟩ := validPC_prior_timely p E rho hx ha i v c valid
    have certCover := healthy_timely_continues_of_later_active p E rho hΔ hx roots cut net
      relay majority r hearly hh i e he later v hv active c.slot older c.target
      ⟨w, hw, j, by omega, tick, saved⟩ v hv
    exact GridCO.ancestors_compatible c.target B _ certCover (cover v hv)
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (pc_prefix_of_head_coverage p E rho hx ha i v B c valid (same.symm ▸ cover)))

/-- At the pending gate, the honest ack time rules out later PC labels.
The prefix PC guard therefore holds without a fault cap or outage relay. -/
theorem healthy_pending_gate_pcOK
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block)
    (cover : ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target) :
    pcOK (if capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v) then none
      else (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).bestPC) B = true := by
  have earlyLt : earlyTime p r < gateTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ < 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have eh := earlyLt.le.trans hh
  have sleepy := healthy_sleepy_through_early p E rho hx roots cut net relay majority r hearly eh
  have ha : (faulty rho).card < pcQuorum p :=
    sleepy_quorum_above_faults p (prefixEnv E (earlyTime p r))
      (runPrefix rho (earlyTime p r)) 0 sleepy
  have pub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    change 4 * p.Δ * (r : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ gateTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hx.tick_total v hv _ pub nonneg hh)
  cases active : capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v) with
  | true => simp [pcOK]
  | false =>
    cases selected : (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).bestPC with
    | none => simp [pcOK]
    | some c =>
      have bound := installedPC_slot_le_at_gate p E rho hx ha v r c selected
      rw [← stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick] at active selected
      have compatible := healthy_pending_validPC_compatible p E rho hΔ hx roots cut net relay
        majority r hearly eh i _ tick earlyLt v hv active B cover c
        (installedPC_valid_before p rho v i c selected) bound
      rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick] at active selected
      simpa only [active, Bool.false_eq_true, ↓reduceIte, selected, pcOK,
        Block.Compatible, Block.compatible, Bool.or_comm] using compatible

/-- The pending HEAD's frozen/carried PC has a strictly older label.
Healthy continuation therefore compares its authority with the prefix,
including a PC first carried after the healthy cutoff. -/
theorem healthy_pending_head_pc_compatible
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block)
    (cover : ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target)
    (active : capBroken p (headState p rho (r + 1) v) = false)
    (c : PC p.n) (selected : selectedPC p (headState p rho (r + 1) v) (r + 1) = some c) :
    Block.Compatible c.target B := by
  set_option backward.isDefEq.respectTransparency false in
  have earlyLt : earlyTime p r < voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have eh := earlyLt.le.trans hh
  have sleepy := healthy_sleepy_through_early p E rho hx roots cut net relay majority r hearly eh
  have ha : (faulty rho).card < pcQuorum p :=
    sleepy_quorum_above_faults p (prefixEnv E (earlyTime p r))
      (runPrefix rho (earlyTime p r)) 0 sleepy
  have slot := selectedPC_slot_lt_at_nextHead p E rho hx ha v r c selected
  have pub : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hx.tick_total v hv _ pub nonneg hh)
  rw [headState, ← stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick]
    at active selected
  rw [capBroken_clock] at active
  have certs := certificates_valid_at_fold p (rho.events.take i) v
  have valid := selectedPC_valid p _ (clock_frozenPC_valid p _ _ certs.2 certs.1)
    (r + 1) c selected
  rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at valid
  exact healthy_pending_validPC_compatible p E rho hΔ hx roots cut net relay majority
    r hearly eh i _ tick earlyLt v hv active B cover c valid slot.le

end AvailableChain.SAPC
end
