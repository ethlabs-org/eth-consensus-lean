module
public import AvailableChainSAPC.Proofs.RecordHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A completed healthy gate includes its raw result in the public read,
including receipts at the gate time. No fault cap is required. -/
theorem healthy_gate_includes {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hgate : gateTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some B) :
    Block.Preceq B (stable (Run.readAt (sapc p) rho (gateTime p r) v)) := by
  have eq : earlyTime p (r + 1) = gateTime p r := GridCO.early_next_eq_gate p.engine r
  have invariant := healthy_run_invariant_through_early p E rho hΔ hx roots cut net relay
    majority (r + 1) (eq.symm ▸ hgate) (eq.symm ▸ hh) _ (le_refl _)
  rw [eq] at invariant
  have pub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    change 4 * p.Δ * (r : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ gateTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hx.tick_total v hv _ pub nonneg hh)
  have index := (index_lt_read_length_iff hx.toScheduleWellFormed (gateTime p r) tick).mpr
    (le_refl _)
  have includes := gate_includes_of_joint p E rho _ i invariant.facts index v hv r B tick
    (by rwa [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick])
  rw [readAt_eq_stateBefore hx.toScheduleWellFormed]
  exact GridCO.prefix_trans _ _ _ includes
    (record_prefix_of_joint p E rho _ invariant.facts (i + 1) _
      (Nat.succ_le_of_lt index) (le_refl _) v hv)

/-- Healthy raw results cover a prior stable read at every honest reader.
Only the later label's early cutoff must be healthy. -/
theorem healthy_result_after_stable {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (T : Time) (before : T < gateTime p r) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (below : Block.Preceq B (stable (Run.readAt (sapc p) rho T v))) (w : V) (hw : w ∈ rho.honest) :
    ∃ C, SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) w).base r = some C ∧
      Block.Preceq B C := by
  have nonneg : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have voteBefore : voteTime p r < cut := by
    apply lt_of_lt_of_le _ hearly
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  exact healthy_preserve_from_heads p E rho hx hΔ cut net relay r hearly hh
    (majority _ nonneg voteBefore) B
    (healthy_stable_heads p E rho hΔ hx roots cut net relay majority r hearly hh
      T before v hv B below)
    w hw

/-- A later completed healthy gate makes a stable prefix common. -/
theorem healthy_record_after_stable {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hgate : gateTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (T : Time) (before : T < gateTime p r) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (below : Block.Preceq B (stable (Run.readAt (sapc p) rho T v))) (w : V) (hw : w ∈ rho.honest) :
    Block.Preceq B (stable (Run.readAt (sapc p) rho (gateTime p r) w)) := by
  have earlyLe : earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨C, raw, belowC⟩ := healthy_result_after_stable p E rho hΔ hx roots cut net relay
    majority r (earlyLe.trans hgate) (earlyLe.trans hh) T before v hv B below w hw
  exact GridCO.prefix_trans B C _ belowC
    (healthy_gate_includes p E rho hΔ hx roots cut net relay majority r hgate hh w hw C raw)

end AvailableChain.SAPC
end
