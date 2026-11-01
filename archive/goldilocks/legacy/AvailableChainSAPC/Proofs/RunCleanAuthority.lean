module
public import AvailableChainSAPC.Proofs.RunCleanActiveTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- At a public tick, a valid PC's first possible gate is already due.
An honest ack precedes the strict input; the public clock grid supplies
the remaining delta. This applies to every authority phase. -/
theorem validPC_gate_le_tick {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t)) (c : PC p.n)
    (hc : pcValid p (Run.stateBefore (sapc p) rho i reader) c = true) :
    gateTime p c.slot ≤ t := by
  obtain ⟨seat, data, honest, hm, _, _⟩ := pc_honest_witness p rho _ c hc ha
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed he] at hm
  have input : Run.stateBeforeTime (sapc p) rho t = Run.readAt (sapc p) rho (t - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at hm
  have bound := archived_honest_head_time_le_read p E rho hx.toUnforgeableSignatures
    reader (t - 1) (c.slot + 1) seat data hm honest
  obtain ⟨k, ht⟩ := hx.tick_public reader t (List.mem_of_getElem? he)
  rw [hΔ] at ht
  have count : 4 * (c.slot : Time) + 5 < k := by
    change 4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ ≤ t - 1 at bound
    push_cast at bound
    rw [ht] at bound
    nlinarith [p.deltaPos]
  have count' : 4 * (c.slot : Time) + 6 ≤ k := by
    linarith [Int.add_one_le_iff.mpr count]
  rw [ht]
  change 4 * p.Δ * (c.slot : Time) + 6 * p.Δ ≤ (k : Time) * p.Δ
  nlinarith [p.deltaPos]

/-- Once a target has first transferred and is an actual path source,
its continuation uses the retained path invariant in either mode. Old
PC sources remain protected after the observer or reader is disabled. -/
theorem timely_continues_on_run_path
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (h : JointCleanInvariant p E rho i) (r : Slot) (b : Block)
    (hb : cleanRunPath p rho i b)
    (first : ∀ v ∈ rho.honest, Block.Preceq b (headData p rho (r + 1) v).target)
    (s : Slot) (hrs : r < s) (htime : voteTime p s < e.time)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq b (headData p rho s reader).target := by
  set_option backward.isDefEq.respectTransparency false in
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have heads (s : Slot) (hsr : r + 1 ≤ s) : voteTime p s < e.time →
      ∀ reader ∈ rho.honest, Block.Preceq b (headData p rho s reader).target := by
    induction s, hsr using Nat.le_induction with
    | base => exact fun _ => first
    | succ s hsr ih =>
      intro time reader hr
      have earlier : voteTime p s < e.time := by
        apply lt_trans _ time
        change 4 * p.Δ * (s : Time) + p.Δ <
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        linarith [p.deltaPos]
      have earlyBound : earlyTime p s ≤ rho.horizon := by
        apply le_trans _ (time.le.trans horizon)
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        linarith [p.deltaPos]
      have freezeBound : freezeTime p s ≤ rho.horizon := by
        apply le_trans _ (time.le.trans horizon)
        change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        linarith [p.deltaPos]
      obtain ⟨c, raw, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs s
        earlyBound b (ih earlier) reader hr
      have pub : PublicTime E (voteTime p (s + 1)) := by
        refine ⟨4 * (s + 1) + 1, ?_⟩
        change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ = _
        rw [hΔ]
        push_cast
        ring
      have nonneg : 0 ≤ voteTime p (s + 1) := by
        change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg (s + 1)]
      obtain ⟨k, tick⟩ := List.mem_iff_getElem?.mp
        (hs.execution.tick_total reader hr _ pub nonneg (time.le.trans horizon))
      have hki := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed tick he time
      have root : cleanRunPath p rho i
          (GridCO.liveRoot (headState p rho (s + 1) reader).base) := by
        apply CleanStateOnPath.liveRoot h.facts.chain
        rw [headState, ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick,
          clock_eq_preGate_of_no_gate p _ _ (voteTime_ne_gateTime p (s + 1))]
        exact (clockPreGate_clean p _ _ (h.facts.states k hki.le reader hr)).1
      have sync : E.t_GST ≤ earlyTime p s := by
        rw [hs.gst_zero]
        change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg s]
      apply synchronous_local_genuine_activePC_head_covers p E rho hs.execution hΔ
        hs.acceptedRelay s sync freezeBound reader hr b c raw hp
        (h.facts.chain.comparable _ _ root hb)
      intro active cert selected
      rw [headState, ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick]
        at active selected
      exact h.facts.chain.comparable _ _
        (h.facts.headAuthorities k hki reader hr (s + 1) cert tick active selected) hb
  exact heads s (Nat.succ_le_of_lt hrs) htime reader hr

/-- Above the cap, every non-raw canonical source is a timely target
whose first transfer succeeded. The witness uses the actual authority
input, even if all readers have since disabled PC control. -/
theorem cleanRunSource_raw_or_transferred_timely
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (nocap : ¬ FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (h : JointCleanInvariant p E rho i) (b : Block)
    (source : CleanRunSource p rho i b) :
    (∃ j < i, ∃ v ∈ rho.honest, ∃ r,
      rho.events[j]? = some (.tick v (gateTime p r)) ∧
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) ∨
    (∃ r, HonestTimelySource p rho i r b ∧
      ∀ v ∈ rho.honest, Block.Preceq b (headData p rho (r + 1) v).target) := by
  set_option backward.isDefEq.respectTransparency false in
  have ha := sleepy_quorum_above_faults p E rho t₀ hs
  have pc (j : Nat) (hj : j < i) (v : V) (hv : v ∈ rho.honest) (t : Time)
      (tick : rho.events[j]? = some (.tick v t)) (cert : PC p.n)
      (active : capBroken p (Run.stateBefore (sapc p) rho j v) = false)
      (valid : pcValid p (Run.stateBefore (sapc p) rho j v) cert = true) :
      ∃ r, HonestTimelySource p rho i r cert.target ∧
        ∀ w ∈ rho.honest, Block.Preceq cert.target (headData p rho (r + 1) w).target := by
    have src := (h.facts.certificates j hj.le v hv cert valid).1
    refine ⟨cert.slot, ?_, ?_⟩
    · obtain ⟨w, hw, k, hk, ht, saved⟩ := src
      exact ⟨w, hw, k, hk.trans hj, ht, saved⟩
    · exact timely_next_heads_of_active_input p E rho hΔ t₀ hs j _ tick
        (h.restrict hs.execution ha hj.le) cert.slot cert.target src
        (validPC_gate_le_tick p E rho hΔ hs.execution ha j v t tick cert valid) v hv active
  cases source with
  | genuine j hj v hv r b tick raw => exact Or.inl ⟨j, hj, v, hv, r, tick, raw⟩
  | timely _ _ cap _ => exact (nocap cap).elim
  | gate j hj v hv r cert tick active selected =>
    exact Or.inr (pc j hj v hv _ tick cert active
      (installedPC_valid_before p rho v j cert selected))
  | proposal j hj v hv r cert tick active selected =>
    rw [capBroken_clock] at active
    rw [clock_bestPC] at selected
    exact Or.inr (pc j hj v hv _ tick cert active
      (installedPC_valid_before p rho v j cert selected))
  | head j hj v hv r cert tick active selected =>
    rw [capBroken_clock] at active
    have valid := certificates_valid_at_fold p (rho.events.take j) v
    have hc := selectedPC_valid p _ (clock_frozenPC_valid p _ _ valid.2 valid.1) _ cert selected
    rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc
    exact Or.inr (pc j hj v hv _ tick cert active hc)

end AvailableChain.SAPC
end
