module
public import AvailableChainSA.Proofs.Clean
public import AvailableChainGridCO.Proofs.RawHistory
public import AvailableChainGridCO.Proofs.Outage

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic

local instance saFastOutageLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- Honest awake validators and faulty validators occupy disjoint seats. -/
theorem awake_add_faults_le_seats {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (t : Time) :
    (awakeAt E rho.honest t).card + (faulty rho).card ≤ p.n := by
  have hd : Disjoint (awakeAt E rho.honest t) (faulty rho) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  have hn : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_univ _).trans_eq hn

/-- Both constants records have the same outage fields for the fast lag.
Recovery bounds are irrelevant to this conversion. -/
theorem fast_outage_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (G T b₀ b₁ : Time)
    (ho : FastOutageRegime (sa p) E (saInterface p) (saConstants p G) rho T b₀ b₁) :
    OutageRegime (sa p) E (GridCO.gridInterface p.engine)
      (GridCO.gridConstants p.engine G) rho T b₀ b₁ := by
  exact ⟨ho.execution, ho.rootInjective, ho.healthy, ho.interval,
    ho.armed, ho.withinBudget, ho.sleepyBefore, ho.etaSleepyBefore⟩

/-- A complete high-participation batch admits τ at the pending gate.
Its support survives arbitrary later delivery; the clean guard permits it. -/
theorem pending_fast_protection {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (sa p) E (GridCO.gridInterface p.engine)
      (GridCO.gridConstants p.engine G) rho T b₀ b₁)
    (hhigh : HighParticipationBefore p E rho b₀)
    (r : Slot) (hgate : gateTime p r ≤ b₀) (hearly : earlyTime p (r + 1) ≤ b₀)
    (hh : gateTime p (r + 1) ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B : Block) (hn : B ≠ .genesis)
    (hp : Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p r) source))) :
    ∀ reader ∈ rho.honest,
      (faulty rho).card < releaseThreshold p ∧
      GridCO.ProtectsUntil (Run.readAt (sa p) rho (gateTime p (r + 1)) reader)
        B (releaseThreshold p) (gateTime p (r + 1) + lifetime p) ∧
      Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p (r + 1)) reader)) := by
  have hclean := GridCO.cleanThroughLabel_of_outage G T b₀ b₁ ho r hgate
  have hvote : voteTime p (r + 1) < b₀ := by
    dsimp [voteTime, earlyTime, GridCO.voteTime, GridCO.earlyTime] at *
    linarith [p.engine.deltaPos]
  have hz : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * (r + 1 : Nat) + p.Δ
    have hd := p.deltaPos
    positivity
  have hm := ho.sleepyBefore _ hz hvote
  have hstrong := faults_lt_releaseThreshold p _ _ hm
    (awake_add_faults_le_seats p E rho (voteTime p (r + 1)))
  have hd := GridCO.EarlyDelivery.of_outage G T b₀ b₁ ho (r + 1) hearly
  have hheads := GridCO.clean_stable_heads_cover p.engine E rho hΔ r hclean source hs B hp
  intro reader hr
  obtain ⟨C, hc, hBC, hB⟩ :=
    GridCO.preserve_of_early_delivery p.engine E rho hΔ r hd hm B hheads reader hr
  have hsupp := GridCO.prefixSupport_ge_early_honest_batch p.engine E rho ho.execution
    _ reader (r + 1) B
    (GridCO.synchronous_next_head_batch p.engine E rho hΔ r hd B hheads reader hr)
  have hcount : releaseThreshold p ≤ prefixSupport p
      (GridCO.gateInput p.engine rho (r + 1) reader) (r + 1) B :=
    (hhigh _ hz hvote).trans hsupp
  have hadmit : releaseThreshold p ∈ GridCO.admissionLevels p.engine
      (GridCO.clockPreGate p.engine (GridCO.gateInput p.engine rho (r + 1) reader)
        (gateTime p (r + 1))) (r + 1) B := by
    rw [GridCO.admissionLevels_preGate p.engine
      (GridCO.gateInput p.engine rho (r + 1) reader) (gateTime p (r + 1))
      (GridCO.run_time_receiptStamped p.engine rho _ reader) (r + 1) B]
    have hpolicy : GridCO.LeasePolicy.slowArming = true := rfl
    simp [GridCO.admissionLevels, hpolicy, hcount, releaseThreshold]
  obtain ⟨hrecord, hrow⟩ := GridCO.read_gate_writes_admitted_prefix p.engine E rho hΔ
    ho.execution.toScheduleWellFormed (r + 1) hh reader hr B C (releaseThreshold p)
    hc hBC hn hB hadmit
    (GridCO.pending_gate_guard p.engine E rho hΔ r hclean hd hm reader hr C hc)
  exact ⟨hstrong, ⟨_, le_refl _, hrow⟩, hrecord⟩

/-- The fast P1 field of Draft 4.3. The outage starts after 4Δ and high honest
participation is required throughout the healthy prefix from genesis. -/
theorem fastP1_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hΔ : E.Δ = p.Δ) :
    ∀ (rho : Run V (sa p)) T b₀ b₁,
      FastOutageRegime (sa p) E (saInterface p) (saConstants p G) rho T b₀ b₁ →
      PersistsThrough (sa p) rho (saInterface p).stable T b₀ b₁ := by
  intro rho T b₀ b₁ ho
  have hhigh : HighParticipationBefore p E rho b₀ := ho.highParticipation
  have hengine := fast_outage_engine p E rho G T b₀ b₁ ho
  apply GridCO.resilient_of_covering_protection p.engine E rho hΔ G T b₀ b₁ hengine
    (fun _ _ _ => releaseThreshold p)
  · intro r hgate source hs B hn hp
    have hg : gateTime p r ≤ b₀ :=
      ((GridCO.gateTime_le_iff p.engine r (r + 1)).mpr (Nat.le_succ r)).trans hgate
    exact pending_fast_protection p E rho hΔ G T b₀ b₁ hengine hhigh r hg
      (by change GridCO.earlyTime p.engine (r + 1) ≤ b₀
          rw [GridCO.early_next_eq_gate]; exact hg)
      (hgate.trans (ho.interval.2.2.1.trans ho.interval.2.2.2)) source hs B hn hp
  · exact pending_fast_protection p E rho hΔ G T b₀ b₁ hengine hhigh

end AvailableChain.SA
end
