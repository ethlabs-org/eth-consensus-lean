module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTasks

public import AvailableChainFGSAProofs.Proofs.Healing.Repair
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryPerm

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3.
The full producer uses HG.3, the capped HG.4 rise, and exact-height row provenance.
The first-row witness is shared by both allowed repair bounds. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, full FrontierSearchStatement.
DC: SAME rise from M, then first row at M+1. Both complete horizon guards are retained.
RCap supplies a skipped row; otherwise the event at M+1 starts the row task. -/
theorem healing_frontierSearch [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (cap : RCap p c E rho)
    (origin : RQCOrigin p c E rho) (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (perm : TPerm p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    : FrontierSearchStatement p c E rho G ΔF := by
  classical
  apply (frontierSearchStatement_iff p c E rho G ΔF).mpr
  intro hδ hbound rG u₀ M hgst hfirst hu₀ hdelay hM _rowCap
  have hs := hrec.base.valid.toScheduleWellFormed
  have hstartLower := healing_recovery_start_lower (p := p) E
  have frontier := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage
  have rise : ∀ ρbar,
      (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
      u₀ + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon →
      ∃ (j : Nat) (ev : V2.Event V (Obj p)), timeIdx rho u₀ ≤ j ∧
        rho.events[j]? = some ev ∧ u₀ ≤ ev.time ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
        M < frontierAtIdx p c E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M) := by
    intro ρbar hmode hhor
    have hb := (frontierSearch_task_bounds E rho hrec hbound hmode .gap).2.2.2.2.1
    have hcutHor : u₀ ≤ rho.horizon := by linarith only [hhor, hb]
    obtain ⟨i, ev, kind, hstart, ht, hidx⟩ :=
      frontierSearch_cut_start E rho hrec hgst hfirst hu₀ hdelay hM hcutHor
    have hdelayEv : recoveryStart p E + 2 * P p ≤ ev.time := by
      rw [ht]
      linarith only [hdelay, hstartLower, p.deltaPos]
    have hhorEv : ev.time + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon := by
      rw [ht]
      exact hhor
    have hrise := frontierSearch_rise_task E rho hrec mono crossing origin
      repair common
      hδ hbound perm frontier rowsReceipt progressCoverage hfold faultQ honestQuorum
      hstart hdelayEv hmode hhorEv
    obtain ⟨j, nextEv, hij, hj, htime, hh, hcap⟩ :=
      (frontierRiseBy_iff p c E rho i M _).mp hrise
    have hi := ((frontierSearchStart_iff p c E rho i ev M kind).mp hstart).1
    have hlow : u₀ ≤ nextEv.time := ht ▸ frontierSearch_event_time_mono E rho hs hi hj hij.le
    refine ⟨j, nextEv, by omega, hj, hlow, ?_, hh, ?_⟩
    · rwa [ht] at htime
    · intro k hk hkj
      exact hcap k (by omega) hkj
  refine ⟨?_, ?_⟩
  · intro ρbar hmode hhor
    obtain ⟨j, ev, hjcut, hj, _, ht, hh, hcap⟩ := rise ρbar hmode hhor
    exact ⟨j, ev, hjcut, hj, ht, hh, hcap⟩
  · intro hex
    have rows : ∀ ρbar,
        (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
        u₀ + frontierSearchRiseBudget p G ΔF ρbar +
          frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon →
        ∃ (j : Nat) (ev : V2.Event V (Obj p)), timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
          M < frontierAtIdx p c E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M) ∧
          FirstHeightRowBy p c E rho (M + 1)
            (ev.time + frontierSearchRowBudget p G ΔF ρbar) := by
      intro ρbar hmode hhor
      have hb := (frontierSearch_task_bounds E rho hrec hbound hmode .gap).2.2.2.2.2
      have hRiseHor : u₀ + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon := by
        linarith only [hhor, hb]
      obtain ⟨j, ev, hjcut, hj, hlow, ht, hh, hcap⟩ := rise ρbar hmode hRiseHor
      have hgstCut : recoveryStart p E ≤ u₀ := by
        have hP := frontierSearch_period_bound p
        linarith [p.deltaPos]
      have hrowHor : ev.time + frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon := by
        linarith only [ht, hhor]
      refine ⟨j, ev, hjcut, hj, ht, hh, hcap, ?_⟩
      by_cases heq : frontierAtIdx p c E rho (j + 1) = M + 1
      · obtain ⟨kind, hkind⟩ := frontierSearch_phase_exists E rho (j + 1) (M + 1)
        have heff : EffectiveEvent p c E rho j := Or.inl
          ((hcap j hjcut le_rfl).trans_lt hh)
        have hstart : FrontierSearchStart p c E rho j ev (M + 1) kind :=
          (frontierSearchStart_iff p c E rho j ev (M + 1) kind).mpr
            ⟨hj, hgstCut.trans hlow,
              Or.inl heff, heq, by omega, hkind⟩
        exact frontierSearch_row_task E rho hrec mono crossing origin
          scopeProducer repair common hδ hbound
          perm cap writes rowCoverage rowsReceipt progressCoverage hfold faultQ honestQuorum
          hstart (by linarith only [hdelay, hlow, healing_recovery_start_lower (p := p) E,
            p.deltaPos]) hmode hrowHor
      · obtain ⟨x, W, hW, hWh⟩ :=
          (healing_phaseWitness p c E rho (i := j + 1)
            (m := frontierAtIdx p c E rho (j + 1)) (by omega) rfl).frontier
        obtain ⟨l, z, r, a, e, hlj, ha, hn, _⟩ := cap M (j + 1) x W hW
          (by simp only [Height] at *; omega)
        have hcut : l < timeIdx rho ev.time := by
          have hjcut := healing_phase_lt_timeIdx p c E rho hs hj le_rfl
          exact (Nat.le_of_lt_succ hlj).trans_lt hjcut
        have htime : p.actionTime r ≤ ev.time :=
          frontierSearch_event_time_le p c E rho hs ha.2.1 hcut
        exact frontierSearch_first_row p c E rho ⟨l, z, a, e, ha, hn⟩
          (by linarith only [htime, hb])
    obtain ⟨ρ0, hm0, hhor0⟩ := hex
    obtain ⟨_, _, _, _, _, _, _, hrow0⟩ := rows ρ0 hm0 hhor0
    obtain ⟨rStar, hrStar, hfirstStar, _⟩ :=
      (firstHeightRowBy_iff p c E rho (M + 1) _).mp hrow0
    refine ⟨rStar, hrStar, hfirstStar, ?_⟩
    intro ρbar hmode hhor
    obtain ⟨j, ev, hjcut, hj, ht, hh, hcap, hrow⟩ := rows ρbar hmode hhor
    obtain ⟨r, hr, hfirst, htime⟩ := (firstHeightRowBy_iff p c E rho (M + 1) _).mp hrow
    have heq : rStar = r := frontierSearch_first_row_unique p c E rho
      hrStar hfirstStar hr hfirst
    exact ⟨j, ev, hjcut, hj, ht, hh, hcap, heq.symm ▸ htime⟩

/-- Recovery and the named Foundations supply HG.5 without service factories. -/
theorem healing_frontierSearch_recovery [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : HealingSet p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (cap : RCap p c E rho)
    (origin : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    : FrontierSearchStatement p c E rho G ΔF := by
  have repair := healing_tRepair E rho hrec mono crossing origin
    (healing_repair_service_scopes_recovery E rho hrec mono) writes
  have common := healing_tCommon E rho hrec mono crossing
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage
  have perm := healing_tPerm_recovery E rho hrec mono crossing writes
  exact healing_frontierSearch E rho hrec mono crossing cap origin repair common perm
    (fun q v _ _ _ => healing_frontier_service_scopes_recovery E rho hrec mono q v)
    writes rowCoverage rowsReceipt progressCoverage hfold faultQ honestQuorum

end AvailableChain.FGSA.Run
end
