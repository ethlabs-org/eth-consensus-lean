module
public import AvailableChainSAPC.Proofs.RunCleanFacts
public import AvailableChainSAPC.Proofs.Disabled

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A timely save contains every live finite root at its next HEAD.
Each row has an earlier raw source. The retained continuation invariant
puts that source below the save's exact honest preparation. No cap or
membership of the uncapped timely save in the canonical path is assumed. -/
theorem nextHead_root_prefix_timely_of_run_invariant
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i) (index : Nat) (source : V) (b : Block)
    (saved : savedTimely (Run.stateBefore (sapc p) rho index source) r = some (some b)) :
    Block.Preceq (GridCO.liveRoot (headState p rho (r + 1) reader).base) b := by
  obtain ⟨seat, data, honest, target, k, hk, emitted⟩ :=
    savedTimely_honest_preparation p E rho hs.execution.toUnforgeableSignatures
      (sleepy_quorum_above_faults p E rho t₀ hs) index source r b saved
  have action := (emittedAt_seat_action (sapc p) E rho k _ (voteTime p r)
    r seat (.head data) emitted).2
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk] at action
  change some (Msg.head (headData p rho r (rho.seatOf r seat))) = some (.head data) at action
  have exactHead : (headData p rho r (rho.seatOf r seat)).target = b :=
    (congrArg HeadData.target (Msg.head.inj (Option.some.inj action))).trans target
  have hki : k < i := by
    apply eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed hk he
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  rcases (GridCO.liveRoot_is_deepest (headState p rho (r + 1) reader).base).1 with hg | hm
  · rw [hg]
    exact GridCO.genesis_prefix b
  · obtain ⟨⟨a, g, d⟩, hm, ht⟩ := List.mem_filterMap.mp hm
    dsimp only at ht
    split at ht
    · have rootEq := Option.some.inj ht
      obtain ⟨s, c, hsr, raw, hp⟩ := nextHead_target_genuine_origin p E rho
        hs.execution.toScheduleWellFormed r reader a g d hm
      have time : gateTime p s < voteTime p (r + 1) := by
        have hle : (s : Time) + 1 ≤ r := by exact_mod_cast hsr
        change 4 * p.Δ * (s : Time) + 6 * p.Δ <
          4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
        push_cast
        nlinarith [p.deltaPos]
      have pub : PublicTime E (gateTime p s) := by
        refine ⟨4 * s + 6, ?_⟩
        change 4 * p.Δ * (s : Time) + 6 * p.Δ = _
        rw [hΔ]
        push_cast
        ring
      have nonneg : 0 ≤ gateTime p s := by
        change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg s]
      obtain ⟨j, tick⟩ := List.mem_iff_getElem?.mp (hs.execution.tick_total reader hr _ pub
        nonneg (time.le.trans (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2))
      have hji := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed tick he time
      have raw' : SA.confirmation p (Run.stateBefore (sapc p) rho j reader).base s =
          some c := by
        rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick]
        exact raw
      have cover := h.facts.transferred j hji reader hr s c tick raw'
        k hki (rho.seatOf r seat) honest r hsr hk
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk] at cover
      change Block.Preceq c (headData p rho r (rho.seatOf r seat)).target at cover
      rw [exactHead] at cover
      rw [← rootEq]
      exact GridCO.prefix_trans a c b hp cover
    · contradiction

/-- The uncapped invariant supplies the missing finite-root premise of
active timely transfer. A stored timely target need not be a path source. -/
theorem timely_nextHead_active_of_run_invariant
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i) (b : Block)
    (source : HonestTimelySource p rho i r b)
    (active : capBroken p (headState p rho (r + 1) reader) = false) :
    Block.Preceq b (headData p rho (r + 1) reader).target := by
  obtain ⟨v, hv, j, _, _, saved⟩ := source
  have root := nextHead_root_prefix_timely_of_run_invariant p E rho hΔ t₀ hs
    i reader hr r he h (j + 1) v b saved
  have sync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact synchronous_timely_active_head_covers p E rho hs.execution hΔ hs.acceptedRelay r sync
    v reader hv hr (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2 b
    (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed (j + 1) v r b saved)
    active (Bool.or_eq_true_iff.mpr (Or.inl root))

/-- A departure now implies common disablement using the actual input
invariant, with no extra finite-root premise and no fault cap. -/
theorem timely_departure_disables_of_run_invariant
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i) (b : Block)
    (source : HonestTimelySource p rho i r b)
    (hh : gateTime p r ≤ rho.horizon)
    (leave : ¬ Block.Preceq b (headData p rho (r + 1) reader).target)
    (other : V) (ho : other ∈ rho.honest) :
    capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) other) = true := by
  obtain ⟨v, hv, j, _, _, saved⟩ := source
  have root := nextHead_root_prefix_timely_of_run_invariant p E rho hΔ t₀ hs
    i reader hr r he h (j + 1) v b saved
  have sync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨forward, back⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay r sync hh
  exact timely_departure_disables_by_gate p E rho hs.execution hΔ r v reader other hv hr ho
    (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2 forward back b
    (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed (j + 1) v r b saved)
    (Bool.or_eq_true_iff.mpr (Or.inl root)) leave

/-- If PC control is still active at or after the first possible gate,
every honest next HEAD transferred the timely target. A failed transfer
would have made the cap proof common by that gate and retained it here. -/
theorem timely_next_heads_of_active_input
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (h : JointCleanInvariant p E rho i) (r : Slot) (b : Block)
    (source : HonestTimelySource p rho i r b) (hgate : gateTime p r ≤ e.time)
    (observer : V) (ho : observer ∈ rho.honest)
    (active : capBroken p (Run.stateBefore (sapc p) rho i observer) = false)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq b (headData p rho (r + 1) reader).target := by
  have hh := hgate.trans (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have time : voteTime p (r + 1) < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ < 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have pub : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have nonneg : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  obtain ⟨k, tick⟩ := List.mem_iff_getElem?.mp (hs.execution.tick_total reader hr _ pub
    nonneg (time.le.trans hh))
  have hki := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed tick he
    (time.trans_le hgate)
  have hk := h.restrict hs.execution (sleepy_quorum_above_faults p E rho t₀ hs) hki.le
  obtain ⟨v, hv, j, _, early, saved⟩ := source
  have hjk : j < k := by
    apply eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed early tick
    change 4 * p.Δ * (r : Time) + 2 * p.Δ <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  by_contra leave
  have disabled := timely_departure_disables_of_run_invariant p E rho hΔ t₀ hs
    k reader hr r tick hk b ⟨v, hv, j, hjk, early, saved⟩ hh leave observer ho
  rw [time_input_eq_event_prefix p E rho hs.execution.toScheduleWellFormed] at disabled
  have bound : (rho.events.filter (fun event => decide (event.time ≤ gateTime p r - 1))).length
      ≤ i := by
    by_contra hn
    have ht := (index_lt_read_length_iff hs.execution.toScheduleWellFormed
      (gateTime p r - 1) he).mp (Nat.lt_of_not_ge hn)
    have conflict : e.time < gateTime p r := Int.le_sub_one_iff.mp ht
    exact (not_lt_of_ge hgate) conflict
  have broken := capBroken_before_mono p rho bound observer disabled
  rw [active] at broken
  cases broken

/-- A live PC at a gate needs an earlier honest ack. Its preparation
label is therefore no later than this gate's label, without a fault cap. -/
theorem installedPC_slot_le_at_gate {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (reader : V) (r : Slot) (c : PC p.n)
    (hc : (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).bestPC = some c) :
    c.slot ≤ r := by
  have input : Run.stateBeforeTime (sapc p) rho (gateTime p r) =
      Run.readAt (sapc p) rho (gateTime p r - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at hc
  have bound := installedPC_time_le_read p E rho hx.toUnforgeableSignatures ha
    reader (gateTime p r - 1) c hc
  by_contra hn
  have hlt : (r : Time) + 1 ≤ c.slot := by exact_mod_cast lt_of_not_ge hn
  change 4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ ≤
    4 * p.Δ * (r : Time) + 6 * p.Δ - 1 at bound
  push_cast at bound
  nlinarith [p.deltaPos]

/-- An actual active gate PC has a timely source which transferred to
all honest next HEADs. This closes first-use disablement at the gate;
comparison with later raw sources still needs chronological continuation. -/
theorem gatePC_next_heads_of_run_invariant
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (gateTime p r)))
    (h : JointCleanInvariant p E rho i) (c : PC p.n)
    (active : capBroken p (Run.stateBefore (sapc p) rho i reader) = false)
    (selected : (Run.stateBefore (sapc p) rho i reader).bestPC = some c)
    (other : V) (ho : other ∈ rho.honest) :
    Block.Preceq c.target (headData p rho (c.slot + 1) other).target := by
  have source := (h.facts.certificates i (le_refl _) reader hr c
    (installedPC_valid_before p rho reader i c selected)).1
  have selected' := selected
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at selected'
  have bound := installedPC_slot_le_at_gate p E rho hs.execution
    (sleepy_quorum_above_faults p E rho t₀ hs) reader r c selected'
  exact timely_next_heads_of_active_input p E rho hΔ t₀ hs i _ he h c.slot c.target source
    ((GridCO.gateTime_le_iff p.engine c.slot r).mpr bound) reader hr active other ho

end AvailableChain.SAPC
end
