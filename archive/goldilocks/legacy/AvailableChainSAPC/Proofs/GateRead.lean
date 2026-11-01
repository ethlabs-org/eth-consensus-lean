module
public import AvailableChainSAPC.Proofs.OutageProtection

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A clock writes only its scheduled deadline. Existing rows have no
later deadline than the new local clock plus the fixed lifetime. -/
theorem clock_deadlines_bounded (p : Params) {n : Nat} (st : State n) (t : Time)
    (ht : st.base.now ≤ t)
    (bound : GridCO.DeadlinesAtMost st.base (st.base.now + lifetime p)) :
    GridCO.DeadlinesAtMost (clock p st t).base
      ((clock p st t).base.now + lifetime p) := by
  rw [clock_now]
  have pre : GridCO.DeadlinesAtMost (clockPreGate p st t).base (t + lifetime p) := by
    rw [clockPreGate_base]
    intro B g d row
    have hd := bound B g d (GridCO.clockPreGate_obligations_subset p.engine st.base t _ row)
    change d ≤ t + lifetime p
    linarith
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rename_i gateTimeEq
    intro B g d row
    rcases gateWithPC_row_origin p _ _ _ B g d row with old | ⟨C, _, _, _, _, eq⟩
    · exact pre B g d old
    · have time : t = gateTime p ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
        simpa using (Bool.and_eq_true_iff.mp gateTimeEq).2
      rw [eq, ← time]
  · exact pre

/-- Deadline bounds follow from the schedule and source rule, with no
clean-path, participation, or cap premise. -/
theorem run_deadlines_bounded {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (i : Nat) (v : V) :
    GridCO.DeadlinesAtMost (Run.stateBefore (sapc p) rho i v).base
      ((Run.stateBefore (sapc p) rho i v).base.now + lifetime p) := by
  set_option backward.isDefEq.respectTransparency false in
  apply stateBefore_invariant (engineClock p) E rho hs
    (fun st => GridCO.DeadlinesAtMost st.base (st.base.now + lifetime p))
  · simp [GridCO.DeadlinesAtMost, sapc, initial, GridCO.initial]
  · exact clock_deadlines_bounded p
  · intro st o h
    simpa only [sapc, GridCO.DeadlinesAtMost, process_obligations, process_now] using! h

/-- A raw result above B either advances S above B or retains its old
prefix. This includes a PC veto of the raw descendant. -/
theorem gateWithPC_retains_raw_prefix (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) (B C : Block)
    (raw : SA.confirmation p st r = some C) (below : Block.Preceq B C)
    (old : Block.Preceq B st.stableRecord) :
    Block.Preceq B (gateWithPC p st r cert).stableRecord := by
  rcases (gateWithPC_records p st r cert).1 with same | ⟨D, result, eq⟩
  · exact same ▸ old
  · have eqD : D = C := Option.some.inj (result.symm.trans raw)
    rw [eq, eqD]
    exact GridCO.advance_preserves_prefix B st.stableRecord C old
      (Bool.or_eq_true_iff.mpr (Or.inl below))

/-- At the actual gate, each admitted compatible prefix gets its exact
new deadline. The raw tip can be PC-vetoed and no previous lease is needed.
The old record prefix is retained through equal-time deliveries. -/
theorem read_gate_arms_prefix {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B C : Block) (g : Nat)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (finite : (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base.obligations.any
      (fun (a, _, _) => !Block.compatible a C) = false)
    (stored : B ∈ (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base.blocks)
    (nonzero : B ≠ .genesis) (below : Block.Preceq B C)
    (admitted : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B)
    (compatible : pcOK
      (if capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v) then none
       else (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).bestPC) B = true)
    (old : Block.Preceq B (stable (Run.stateBeforeTime (sapc p) rho (gateTime p r) v))) :
    (B, g, gateTime p r + lifetime p) ∈
        (Run.readAt (sapc p) rho (gateTime p r) v).base.obligations ∧
      Block.Preceq B (stable (Run.readAt (sapc p) rho (gateTime p r) v)) := by
  set_option backward.isDefEq.respectTransparency false in
  let st := Run.stateBeforeTime (sapc p) rho (gateTime p r) v
  let pre := clockPreGate p st (gateTime p r)
  have publicTime : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    change 4 * p.Δ * (r : Time) + 6 * p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have nonneg : 0 ≤ gateTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have tick := hs.tick_total v hv _ publicTime nonneg hh
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp tick
  have stamped := base_receiptStamped_at_fold p
    (rho.events.filter (fun e => decide (e.time < gateTime p r))) v
  have rawPre : SA.confirmation p pre.base r = some C := by
    rw [clockPreGate_base]
    exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
      _ st.base (GridCO.clockPreGate_receiptData p.engine st.base _) stamped r).trans raw
  have finitePre : pre.base.obligations.any (fun (a, _, _) => !Block.compatible a C) = false := by
    apply List.any_eq_false.mpr
    intro row member
    exact List.any_eq_false.mp finite row
      (GridCO.clockPreGate_obligations_subset p.engine st.base _ row
        (by simpa only [pre, clockPreGate_base] using! member))
  have storedPre : B ∈ pre.base.blocks := by
    have blocks : pre.base.blocks = st.base.blocks := by
      change (clockPreGate p st (gateTime p r)).base.blocks = st.base.blocks
      rw [clockPreGate_base]
      exact congrArg Prod.fst (GridCO.clockPreGate_receiptData p.engine st.base (gateTime p r))
    rwa [blocks]
  have admittedPre : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
      pre.base r B := by
    simpa only [pre, clockPreGate_base,
      @GridCO.admissionLevels_preGate GridCO.slowLeasePolicy p.engine p.n st.base
        (gateTime p r) stamped r B] using! admitted
  have cert : (if capBroken p pre then none else pre.bestPC) =
      (if capBroken p st then none else st.bestPC) := by
    rw [(clockPreGate_pcData p st (gateTime p r)).1,
      (clockPreGate_pcData p st (gateTime p r)).2]
  have bound : GridCO.DeadlinesAtMost pre.base (gateTime p r + lifetime p) := by
    intro a k d row
    have input := run_deadlines_bounded p E rho hs i v
    have time := stateBefore_now_le_event p E rho hs hi v
    rw [stateBefore_tick_eq_stateBeforeTime hs hi] at input time
    have hd := input a k d (GridCO.clockPreGate_obligations_subset p.engine st.base _ _
      (by simpa only [pre, clockPreGate_base] using! row))
    change _ ≤ gateTime p r at time
    change d ≤ gateTime p r + lifetime p
    linarith
  have oldPre : Block.Preceq B pre.base.stableRecord := by
    simpa only [pre, clockPreGate_base, GridCO.clockPreGate_stable] using! old
  constructor
  · rw [read_obligations_eq_clock p E rho hs v _ tick, clock_at_gate]
    exact gateWithPC_writes_admitted_prefix p pre.base r _ B C g rawPre finitePre
      storedPre nonzero below admittedPre (by rw [cert]; exact compatible) bound
  · rw [read_stable_eq_clock p E rho hs v _ tick, clock_at_gate]
    exact gateWithPC_retains_raw_prefix p pre.base r _ B C rawPre below oldPre

end AvailableChain.SAPC
end
