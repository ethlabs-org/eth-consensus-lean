module
public import AvailableChainKit.Engine.HealthyInterior
public import AvailableChainSAPC.Proofs.StrongClean

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The complete state just before the outage is a clean prefix. This
includes arbitrary receipt times and proposal duties before the boundary. -/
theorem strongArmed_sleepy_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀) :
    SleepyRegime (sapc p) (genesisEnv E) (sapcInterface p).toInterface
      (runPrefix rho (b₀ - 1)) 0 := by
  apply healthyInterior_sleepy h.execution (sapcInterface p).toInterface b₀ (b₀ - 1)
    (by
      have := h.interval.1
      have := h.armed
      have : (1 : Time) ≤ E.Δ := Int.add_one_le_iff.mpr E.Δ_pos
      linarith)
    (by linarith) (by have := h.interval.2.2; linarith)
    h.rootInjective h.healthy h.sleepyBefore

/-- Transport the existing clean invariant to every input before the
outage. In particular its finite entries still have actual raw sources. -/
theorem strongArmed_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (i : Nat) (bound : i ≤ (rho.events.filter (fun e => decide (e.time ≤ b₀ - 1))).length) :
    JointCleanInvariant p E rho i := by
  have sleepy := strongArmed_sleepy_prefix p E rho T b₀ h
  exact jointClean_of_runPrefix p E (genesisEnv E) rho h.execution
    (capped_quorum_above_faults p rho h.faultBound) (b₀ - 1) i bound
    (clean_run_invariant p (genesisEnv E) (runPrefix rho (b₀ - 1)) hΔ 0 sleepy i
      (by rw [runPrefix_events h.execution.toScheduleWellFormed]; exact bound))

/-- Before the outage, PC rank order is target-prefix order, including
certificates assembled at different readers and arbitrary receipt times. -/
theorem strongArmed_pc_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (i j : Nat)
    (hi : i ≤ (rho.events.filter (fun e => decide (e.time ≤ b₀ - 1))).length)
    (hj : j ≤ (rho.events.filter (fun e => decide (e.time ≤ b₀ - 1))).length)
    (u v : V) (c d : PC p.n)
    (hc : pcValid p (Run.stateBefore (sapc p) rho i u) c = true)
    (hd : pcValid p (Run.stateBefore (sapc p) rho j v) d = true)
    (rank : c.slot ≤ d.slot) : Block.Preceq c.target d.target := by
  rcases lt_or_eq_of_le rank with less | eq
  · have sleepy := strongArmed_sleepy_prefix p E rho T b₀ h
    apply clean_pc_target_prefix_of_slot_lt p (genesisEnv E) (runPrefix rho (b₀ - 1))
      hΔ 0 sleepy h.faultBound i j u v c d _ _ less
    · rwa [runPrefix_stateBefore (b₀ - 1) i hi]
    · rwa [runPrefix_stateBefore (b₀ - 1) j hj]
  · have same := pc_same_slot_unique p E rho h.execution.toScheduleWellFormed h.faultBound
      _ _ (archive_authenticated_before p E rho h.execution.toUnforgeableSignatures i u)
      (archive_authenticated_before p E rho h.execution.toUnforgeableSignatures j v)
      c d hc hd eq
    rw [same]
    exact GridCO.block_preceq_self _

/-- Common receipt gives an extending PC, not only a certificate of
higher rank. The state is the strict input at the outage boundary. -/
theorem strongArmed_common_pc {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (v : V) (hv : v ∈ rho.honest) :
    ∃ d, (Run.stateBeforeTime (sapc p) rho b₀ v).bestPC = some d ∧
      c.slot ≤ d.slot ∧ Block.Preceq c.target d.target := by
  have hs := h.execution.toScheduleWellFormed
  obtain ⟨_, d, common, rank⟩ := installedPC_healthy_relay p E rho hs b₀ T h.acceptedRelay
    h.armed u v hu hv c selected
  have input (t : Time) : Run.stateBeforeTime (sapc p) rho t =
      Run.readAt (sapc p) rho (t - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at common
  obtain ⟨e, later, next⟩ := strong_certificate_retained p E rho hs v
    (T + E.Δ - 1) (b₀ - 1) (by linarith [h.armed]) d common
  refine ⟨e, (input b₀).symm ▸ later, rank.trans next, ?_⟩
  rw [readAt_eq_stateBefore hs] at selected later
  exact strongArmed_pc_prefix p E rho hΔ T b₀ h _ _
    (read_length_mono T (b₀ - 1) (by
      have := h.armed
      have : (1 : Time) ≤ E.Δ := Int.add_one_le_iff.mpr E.Δ_pos
      linarith))
    (le_refl _) u v c e (installedPC_valid_before p rho u _ c selected)
    (installedPC_valid_before p rho v _ e later) (rank.trans next)

/-- Every finite entry at arming is compatible with the protected PC.
The clean invariant proves this from raw sources, with no lease-below-S
assertion and no slow-window arming premise. -/
theorem strongArmed_finite_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (v : V) (hv : v ∈ rho.honest) (b : Block) (g : Nat) (d : Time)
    (row : (b, g, d) ∈ (Run.stateBeforeTime (sapc p) rho b₀ v).base.obligations) :
    Block.Compatible b c.target := by
  have hs := h.execution.toScheduleWellFormed
  have invariant := strongArmed_invariant p E rho hΔ T b₀ h _ (le_refl _)
  rw [time_input_eq_event_prefix p E rho hs] at row
  rw [readAt_eq_stateBefore hs] at selected
  have pc := (invariant.facts.certificates _
    (read_length_mono T (b₀ - 1) (by
      have := h.armed
      have : (1 : Time) ≤ E.Δ := Int.add_one_le_iff.mpr E.Δ_pos
      linarith))
    u hu c (installedPC_valid_before p rho u _ c selected)).2 h.faultBound
  exact invariant.facts.chain.comparable b c.target
    ((invariant.facts.states _ (le_refl _) v hv).finite b g d row) pc

/-- All honest strong inputs at the boundary contain the protected read.
Persistence after this input is a separate event-induction obligation. -/
theorem strongArmed_common_strong {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq (strong (Run.readAt (sapc p) rho T u))
      (strong (Run.stateBeforeTime (sapc p) rho b₀ v)) := by
  cases selected : (Run.readAt (sapc p) rho T u).bestPC with
  | none => simpa only [strong, selected, Option.map_none, Option.getD_none]
      using GridCO.genesis_prefix (strong (Run.stateBeforeTime (sapc p) rho b₀ v))
  | some c =>
    obtain ⟨d, hd, _, hp⟩ := strongArmed_common_pc p E rho hΔ T b₀ h u hu c selected v hv
    simpa only [strong, selected, hd, Option.map_some, Option.getD_some] using hp

end AvailableChain.SAPC
end
