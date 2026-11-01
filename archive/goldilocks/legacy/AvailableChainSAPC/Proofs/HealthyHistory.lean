module
public import AvailableChainSAPC.Proofs.HealthyRun
public import AvailableChainSAPC.Proofs.HealthyBatch

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Every earlier raw source transfers to the last healthy HEAD batch.
The previous gate may be exactly at the healthy cutoff. -/
theorem genuine_heads_of_early_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) (r : Slot) (hh : earlyTime p r ≤ rho.horizon)
    (h : JointCleanInvariant p E rho
      (rho.events.filter (fun e => decide (e.time ≤ earlyTime p r))).length)
    (s : Slot) (hsr : s < r) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s =
      some B) (w : V) (hw : w ∈ rho.honest) :
    Block.Preceq B (headData p rho r w).target := by
  have gateBound : gateTime p s ≤ earlyTime p r := by
    have cast : (s : Time) + 1 ≤ r := by exact_mod_cast hsr
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have voteBound : voteTime p r ≤ earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have pubGate : PublicTime E (gateTime p s) := by
    refine ⟨4 * s + 6, ?_⟩
    change 4 * p.Δ * (s : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have pubVote : PublicTime E (voteTime p r) := by
    refine ⟨4 * r + 1, ?_⟩
    change 4 * p.Δ * (r : Time) + p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonnegGate : 0 ≤ gateTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have nonnegVote : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨j, gate⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total v hv _ pubGate nonnegGate (gateBound.trans hh))
  obtain ⟨k, vote⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total w hw _ pubVote nonnegVote (voteBound.trans hh))
  have result := h.facts.transferred j
    ((index_lt_read_length_iff hs _ gate).mpr gateBound) v hv s B gate
    (by rwa [stateBefore_tick_eq_stateBeforeTime hs gate]) k
    ((index_lt_read_length_iff hs _ vote).mpr voteBound) w hw r hsr vote
  rwa [stateBefore_tick_eq_stateBeforeTime hs vote] at result

/-- Uncapped healthy genesis, rather than a supplied path invariant,
gives continuation of every earlier raw source. -/
theorem healthy_genuine_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (s : Slot) (hsr : s < r) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s =
      some B) (w : V) (hw : w ∈ rho.honest) :
    Block.Preceq B (headData p rho r w).target := by
  have invariant := healthy_run_invariant_through_early p E rho hΔ hx roots cut net relay
    majority r hearly hh _ (le_refl _)
  exact genuine_heads_of_early_invariant p E rho hΔ hx.toScheduleWellFormed r hh
    invariant s hsr v hv B raw w hw

/-- The pending raw gate extends every earlier genuine result. Late
receipts and PC effects at that gate can be arbitrary. -/
theorem healthy_pending_extends_history {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (s : Slot) (hsr : s < r) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B C : Block)
    (rawB : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B)
    (rawC : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) w).base r = some C) :
    Block.Preceq B C := by
  have nonneg : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have before : voteTime p r < cut := by
    apply lt_of_lt_of_le _ hearly
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨D, rawD, hp⟩ := healthy_preserve_from_heads p E rho hx hΔ cut net relay
    r hearly hh (majority _ nonneg before) B
    (healthy_genuine_heads p E rho hΔ hx roots cut net relay majority r hearly hh s hsr v hv B rawB)
    w hw
  have eq := Option.some.inj (rawD.symm.trans rawC)
  exact eq ▸ hp

/-- The whole-tip finite guard at the pending gate follows from lease
sources. It does not require every lease to lie below the stable record. -/
theorem healthy_pending_gate_guard {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C) :
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base.obligations.any
      (fun (a, _, _) => !Block.compatible a C) = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨⟨B, g, d⟩, row, conflict⟩ := List.any_eq_true.mp bad
  rw [time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at row
  obtain ⟨j, hj, s, D, tick, rawD, hp⟩ := run_target_genuine_origin p rho _ v B g d row
  have time := Int.le_sub_one_iff.mp
    ((index_lt_read_length_iff hx.toScheduleWellFormed (gateTime p r - 1) tick).mp hj)
  have hsr : s < r := by
    by_contra hn
    exact (not_lt_of_ge ((GridCO.gateTime_le_iff p.engine r s).mpr
      (Nat.le_of_not_gt hn))) time
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick] at rawD
  have contain := healthy_pending_extends_history p E rho hΔ hx roots cut net relay majority
    r hearly hh s hsr v v hv hv D C rawD raw
  have compatible : Block.compatible B C = true :=
    Bool.or_eq_true_iff.mpr (Or.inl (GridCO.prefix_trans B D C hp contain))
  simp [compatible] at conflict

/-- The next HEAD's finite root is compatible with any prefix covered by
the last healthy batch, even before that prefix has a lease. -/
theorem healthy_pending_head_root {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block)
    (cover : Block.Preceq B (headData p rho r v).target) :
    Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) v).base) B := by
  rcases (GridCO.liveRoot_is_deepest (headState p rho (r + 1) v).base).1 with hg | hm
  · rw [hg]
    exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix B))
  · obtain ⟨⟨target, g, d⟩, row, ht⟩ := List.mem_filterMap.mp hm
    dsimp only at ht
    split at ht
    · have eq := Option.some.inj ht
      obtain ⟨s, C, hsr, raw, hp⟩ := nextHead_target_genuine_origin p E rho
        hx.toScheduleWellFormed r v target g d row
      have heads := healthy_genuine_heads p E rho hΔ hx roots cut net relay majority
        r hearly hh s hsr v hv C raw v hv
      rw [← eq]
      exact GridCO.ancestors_compatible _ _ _ (GridCO.prefix_trans target C _ hp heads) cover
    · contradiction

end AvailableChain.SAPC
end
