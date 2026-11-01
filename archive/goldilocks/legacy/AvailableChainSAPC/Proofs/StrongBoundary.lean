module
public import AvailableChainSAPC.Proofs.StrongArming

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The protected PC's actual timely source covers every later healthy
batch. The following HEAD can be in the outage; no delivery there is used. -/
theorem strongArmed_healthy_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (slot : c.slot < r) (early : earlyTime p r ≤ b₀)
    (horizon : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq c.target (headData p rho r v).target := by
  have hs := h.execution.toScheduleWellFormed
  have sleepy := healthy_sleepy_through_early p E rho h.execution h.rootInjective
    b₀ h.healthy h.acceptedRelay h.sleepyBefore r early horizon
  have pub : PublicTime E (earlyTime p r) := by
    refine ⟨4 * r + 2, ?_⟩
    change 4 * p.Δ * (r : Time) + 2 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ earlyTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ pub nonneg horizon)
  rw [readAt_eq_stateBefore hs] at selected
  obtain ⟨w, hw, j, _, sourceTick, saved⟩ := validPC_prior_timely p E rho h.execution
    (capped_quorum_above_faults p rho h.faultBound) _ u c
    (installedPC_valid_before p rho u _ c selected)
  have sourceBefore : earlyTime p c.slot < earlyTime p r := by
    have cast : (c.slot : Time) < r := by exact_mod_cast slot
    change 4 * p.Δ * (c.slot : Time) + 2 * p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have ji := eventIndex_lt_of_time_lt hs sourceTick tick sourceBefore
  have ib := (index_lt_read_length_iff hs (earlyTime p r) tick).mpr (le_refl _)
  have states := runPrefix_stateBefore (rho := rho) (earlyTime p r) i ib.le
  have tick' := (runPrefix_event_iff hs (earlyTime p r) i _).mpr ⟨tick, le_refl _⟩
  have source' := (runPrefix_event_iff hs (earlyTime p r) j _).mpr
    ⟨sourceTick, sourceBefore.le⟩
  have saved' := (runPrefix_stateBefore (rho := rho) (earlyTime p r) (j + 1)
    ((Nat.succ_le_of_lt ji).trans ib.le)).symm ▸ saved
  have gateBound : gateTime p c.slot ≤ earlyTime p r := by
    have cast : (c.slot : Time) + 1 ≤ r := by exact_mod_cast slot
    change 4 * p.Δ * (c.slot : Time) + 6 * p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have voteBefore : voteTime p r < earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have result := timely_continues_before_active_input p (prefixEnv E (earlyTime p r))
    (runPrefix rho (earlyTime p r)) hΔ 0 sleepy i _ tick'
    (clean_run_invariant p (prefixEnv E (earlyTime p r)) (runPrefix rho (earlyTime p r))
      hΔ 0 sleepy i (by rw [runPrefix_events hs]; exact ib.le)) v hv
    (states.symm ▸ capBroken_false_before p E rho h.execution h.faultBound v i)
    r c.slot c.target ⟨w, hw, j, ji, source', saved'⟩ gateBound slot voteBefore v hv
  simpa only [headData, headState, runPrefix_stateBeforeTime hs (earlyTime p r)
    (voteTime p r) voteBefore.le] using result

/-- The first HEAD after a healthy batch retains the armed target even
when its frozen PC predates common receipt. Local SA transfer uses the
healthy raw batch and lease sources, with no delivery in the outage. -/
theorem strongArmed_pending_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (slot : c.slot < r) (early : earlyTime p r ≤ b₀)
    (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq c.target (headData p rho (r + 1) v).target := by
  have times : voteTime p r < earlyTime p r ∧
      earlyTime p r ≤ voteTime p (r + 1) ∧ freezeTime p r ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ∧
      4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    constructor
    · linarith [p.deltaPos]
    constructor <;> linarith [p.deltaPos]
  have nonneg : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have eh := times.2.1.trans horizon
  have heads := strongArmed_healthy_heads p E rho hΔ T b₀ h u c selected r slot early eh
  obtain ⟨C, raw, below⟩ := healthy_preserve_from_heads p E rho h.execution hΔ b₀ h.healthy
    h.acceptedRelay r early eh (h.sleepyBefore _ nonneg (times.1.trans_le early))
    c.target heads v hv
  exact local_genuine_activePC_head_covers p E rho h.execution hΔ r v hv
    (times.2.2.trans horizon) c.target C raw below
    (healthy_pending_head_root p E rho hΔ h.execution h.rootInjective b₀ h.healthy
      h.acceptedRelay h.sleepyBefore r early eh v hv c.target (heads v hv))
    (healthy_pending_head_pc_compatible p E rho hΔ h.execution h.rootInjective b₀ h.healthy
      h.acceptedRelay h.sleepyBefore r early horizon v hv c.target heads)

/-- Discharge the old-freeze boundary case from the companion premises.
The honest ack time puts the protected preparation before this batch. -/
theorem strongArmed_head_of_healthy_freeze {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (frozen : freezeTime p r ≤ b₀) (after : b₀ ≤ voteTime p (r + 1))
    (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq c.target (headData p rho (r + 1) v).target := by
  have ack := installedPC_time_le_read p E rho h.execution.toUnforgeableSignatures
    (capped_quorum_above_faults p rho h.faultBound) u T c selected
  have slot : c.slot < r := by
    by_contra hn
    have cast : (r : Time) ≤ c.slot := by exact_mod_cast Nat.le_of_not_gt hn
    have armed := h.armed
    rw [hΔ] at armed
    change 4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ ≤ T at ack
    change b₀ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ at after
    push_cast at ack after
    nlinarith [p.deltaPos]
  have early : earlyTime p r ≤ b₀ := by
    apply le_trans _ frozen
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  exact strongArmed_pending_head p E rho hΔ T b₀ h u c selected r slot early horizon v hv

end AvailableChain.SAPC
end
