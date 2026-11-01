module
public import AvailableChainSA.Proofs.FastOutage
public import AvailableChainSA.Proofs.SlowWindow
public import AvailableChainGridCO.Proofs.LocalTransfer

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic
local instance saOutageLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- The slow-lag outage supplies the shared healthy-prefix premises. -/
theorem outage_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (G T b₀ b₁ : Time)
    (ho : OutageRegime (sa p) E (saInterface p) (saConstants p G) rho T b₀ b₁) :
    OutageRegime (sa p) E (GridCO.gridInterface p.engine)
      (GridCO.gridConstants p.engine G) rho T b₀ b₁ := by
  refine ⟨ho.execution, ho.rootInjective, ho.healthy, ho.interval,
    ?_, ho.withinBudget, ho.sleepyBefore, ho.etaSleepyBefore⟩
  have hlag := fastLag_le_slowLag p G
  change 4 * p.Δ ≤ (saConstants p G).armingLag at hlag
  change T + 4 * p.Δ ≤ b₀
  linarith [ho.armed]

/-- Every later clean raw result covers a prefix of an earlier stable
read, even if the earlier result was local to a different reader. -/
theorem clean_result_after_stable {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (r s : Slot) (hrs : r < s) (hclean : GridCO.CleanThroughLabel p.engine E rho s)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B : Block) (hn : B ≠ .genesis)
    (hp : Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p r) source))) :
    ∃ C, confirmation p (GridCO.gateInput p.engine rho s reader) s = some C ∧ Block.Preceq B C := by
  have hrlabel := hclean r hrs.le
  rcases GridCO.gate_record_genuine_origin p.engine E rho hrlabel.1.toScheduleWellFormed hΔ
    r hrlabel.2.2.1 source hs with hg | ⟨a, har, ha⟩
  · have hgen : stable (Run.readAt (sa p) rho (gateTime p r) source) = .genesis := hg
    rw [hgen] at hp
    exact (hn (by simpa [Block.Preceq, Block.preceq] using hp)).elim
  · obtain ⟨C, hc, hBC⟩ := (GridCO.clean_genuine_history p.engine E rho hΔ s hclean).1
      a (har.trans_lt hrs) source hs _ ha reader hr
    exact ⟨C, hc, GridCO.prefix_trans _ _ _ hp hBC⟩

/-- The pending healthy batch still drives each local ordinary HEAD.
All roots at that HEAD have earlier clean sources. No armed lease is assumed. -/
theorem pending_heads_cover {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : GridCO.CleanThroughLabel p.engine E rho r)
    (hd : GridCO.EarlyDelivery p.engine E rho (r + 1))
    (hm : AwakeMajority E rho (voteTime p (r + 1)))
    (hh : gateTime p (r + 1) ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B : Block)
    (hp : Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p r) source))) :
    GridCO.HeadCovers p.engine rho (r + 1) B := by
  have hheads := GridCO.clean_stable_heads_cover p.engine E rho hΔ r hclean source hs B hp
  intro reader hr
  obtain ⟨C, hc, hBC, _⟩ :=
    GridCO.preserve_of_early_delivery p.engine E rho hΔ r hd hm B hheads reader hr
  have hroot : Block.Preceq
      (GridCO.liveRoot (GridCO.nextHeadState p.engine rho (r + 1) reader)) C := by
    apply GridCO.liveRoot_below_of_rows
    intro K g d hrow
    obtain ⟨s, D, hsr, hD, hKD⟩ := GridCO.nextHeadState_target_genuine_origin
      p.engine E rho hd.execution.toScheduleWellFormed (r + 1) reader K g d hrow
    exact GridCO.prefix_trans K D C hKD
      (GridCO.pending_genuine_extends_history p.engine E rho hΔ r hclean hd hm
        s (Nat.le_of_lt_succ hsr) reader reader hr hr D C hD hc)
  exact GridCO.local_transfer_from_engine p.engine E rho hΔ hd.execution (r + 1) hh
    reader hr B C hc hBC (GridCO.ancestors_compatible _ B C hroot hBC)

/-- General P1. The last healthy batch completes the k-result window at
its pending gate; the prefix is retained until that gate without an armed lease. -/
theorem stable_resilient_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (sa p) E (saInterface p) (saConstants p G) rho T b₀ b₁) :
    PersistsThrough (sa p) rho (saInterface p).stable T b₀ b₁ := by
  intro source hs B hB t ht0 ht1
  change Block.Preceq B (stable (Run.readAt (sa p) rho T source)) at hB
  by_cases hn : B = .genesis
  · subst B; intro reader _; exact GridCO.genesis_prefix _
  have hengine := outage_engine p E rho G T b₀ b₁ ho
  have hT : gateTime p 0 ≤ T := by
    by_contra h
    have he := GridCO.read_stable_before_first_gate p.engine rho T (lt_of_not_ge h) source
    change stable (Run.readAt (sa p) rho T source) = .genesis at he
    rw [he] at hB
    exact hn (by simpa [Block.Preceq, Block.preceq] using hB)
  obtain ⟨s, hslo, hshi⟩ := GridCO.exists_latest_gate p.engine T hT
  obtain ⟨l, hllo, hlhi⟩ := GridCO.exists_latest_gate p.engine b₀ (hT.trans ho.interval.2.1)
  have hlag : gateTime p (s + (p.k - 1)) = gateTime p s + (saConstants p G).armingLag := by
    have hk : 1 ≤ p.k := by have := p.kLarge; omega
    simp only [gateTime, GridCO.gateTime, GridCO.proposalTime, Params.engine,
      saConstants, Nat.cast_add, Nat.cast_sub hk, Nat.cast_one]
    ring
  have hlast : s + (p.k - 1) ≤ l := by
    have hg : gateTime p (s + (p.k - 1)) ≤ b₀ := by
      rw [hlag]
      change gateTime p s ≤ T at hslo
      linarith [ho.armed]
    by_contra h
    have hle := (GridCO.gateTime_le_iff p.engine (l + 1) (s + (p.k - 1))).mpr
      (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
    exact (not_lt.mpr (hle.trans hg)) hlhi
  have hsl : s < l := by have := p.kLarge; simp only [Slot] at *; omega
  have hclean := GridCO.cleanThroughLabel_of_outage G T b₀ b₁ hengine l hllo
  have he := GridCO.read_stable_eq_latest_gate p.engine E rho ho.execution.toScheduleWellFormed
    s T hslo hshi source
  change stable (Run.readAt (sa p) rho T source) = _ at he
  rw [he] at hB
  have hrecords : ∀ reader ∈ rho.honest,
      Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p l) reader)) := by
    intro reader hr
    obtain ⟨C, hc, hp⟩ := clean_result_after_stable p E rho hΔ s l hsl hclean
      source reader hs hr B hn hB
    exact GridCO.prefix_trans _ _ _ hp
      (GridCO.read_gate_covers_result p.engine E rho hΔ ho.execution.toScheduleWellFormed
        l (hclean l (le_refl _)).2.2.1 reader hr C hc
        (GridCO.clean_gate_guard p.engine E rho hΔ l hclean reader hr C hc))
  by_cases hbefore : t < gateTime p (l + 1)
  · intro reader hr
    change Block.Preceq B (GridCO.stable (Run.readAt (GridCO.gridCO p.engine) rho t reader))
    rw [GridCO.read_stable_eq_latest_gate p.engine E rho ho.execution.toScheduleWellFormed
      l t (hllo.trans ht0) hbefore reader]
    exact hrecords reader hr
  · have hwt : gateTime p (l + 1) ≤ t := le_of_not_gt hbefore
    have hh : gateTime p (l + 1) ≤ rho.horizon := hwt.trans (ht1.le.trans ho.interval.2.2.2)
    have hearly : earlyTime p (l + 1) ≤ b₀ := by
      change GridCO.earlyTime p.engine (l + 1) ≤ b₀
      rw [GridCO.early_next_eq_gate]; exact hllo
    have hd := GridCO.EarlyDelivery.of_outage G T b₀ b₁ hengine (l + 1) hearly
    have hvote : voteTime p (l + 1) < b₀ := by
      dsimp [voteTime, earlyTime, GridCO.voteTime, GridCO.earlyTime] at *
      linarith [p.engine.deltaPos]
    have hz : 0 ≤ voteTime p (l + 1) := by
      change 0 ≤ 4 * p.Δ * (l + 1 : Nat) + p.Δ
      have hd := p.deltaPos; positivity
    have hm := ho.sleepyBefore _ hz hvote
    have hstrong := faults_lt_releaseThreshold p _ _ hm
      (awake_add_faults_le_seats p E rho (voteTime p (l + 1)))
    have hheads := GridCO.clean_stable_heads_cover p.engine E rho hΔ l hclean
      source hs B (hrecords source hs)
    have hbase : ∀ reader ∈ rho.honest,
        GridCO.ProtectsUntil (Run.readAt (sa p) rho (gateTime p (l + 1)) reader)
          B (releaseThreshold p) (gateTime p (l + 1) + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (sa p) rho (gateTime p (l + 1)) reader)) := by
      intro reader hr
      obtain ⟨C, hc, hp, hb⟩ := GridCO.preserve_of_early_delivery p.engine E rho hΔ
        l hd hm B hheads reader hr
      have hslow := slowEligible_of_input_covers p E rho ho.execution.toScheduleWellFormed
        hΔ reader hr (l + 1) B (by simp only [Slot] at *; omega) hh (by
          intro u hul hwindow
          have hsu : s < u := by simp only [Slot] at *; omega
          exact clean_result_after_stable p E rho hΔ s u hsu
            (fun q hq => hclean q (hq.trans (Nat.le_of_lt_succ hul)))
            source reader hs hr B hn hB)
      have ha : releaseThreshold p ∈ GridCO.admissionLevels p.engine
          (GridCO.clockPreGate p.engine (GridCO.gateInput p.engine rho (l + 1) reader)
            (gateTime p (l + 1))) (l + 1) B := by
        rw [GridCO.admissionLevels_preGate p.engine (GridCO.gateInput p.engine rho (l + 1) reader)
          (gateTime p (l + 1)) (GridCO.run_time_receiptStamped p.engine rho _ reader)]
        exact (admissionLevels_iff p _ (l + 1) B (releaseThreshold p)).mpr ⟨rfl, Or.inr hslow⟩
      obtain ⟨hrecord, hrow⟩ := GridCO.read_gate_writes_admitted_prefix p.engine E rho hΔ
        ho.execution.toScheduleWellFormed (l + 1) hh reader hr B C (releaseThreshold p)
        hc hp hn hb ha (GridCO.pending_gate_guard p.engine E rho hΔ l hclean hd hm reader hr C hc)
      exact ⟨⟨_, le_refl _, hrow⟩, hrecord⟩
    have hseed := GridCO.armingHeadsCompatible_of_heads p.engine E rho ho.execution
      (l + 1) B (pending_heads_cover p E rho hΔ l hclean hd hm hh source hs B (hrecords source hs))
    have hbudget : b₁ - b₀ ≤ lifetime p := ho.withinBudget.trans (min_le_right _ _)
    have htd : t < gateTime p (l + 1) + lifetime p := by
      change b₀ < gateTime p (l + 1) at hlhi
      linarith
    intro reader hr
    exact (GridCO.protection_from_armed_read p.engine E rho ho.execution B
      (fun _ => releaseThreshold p) (gateTime p (l + 1)) (gateTime p (l + 1) + lifetime p)
      (fun _ _ => hstrong) hbase hseed t hwt htd reader hr).2

end AvailableChain.SA
end
