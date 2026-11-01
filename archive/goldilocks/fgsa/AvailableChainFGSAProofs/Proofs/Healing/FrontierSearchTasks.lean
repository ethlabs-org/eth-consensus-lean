module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchCompose
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRise
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTasks

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3.
First rise, then the first height-M+1 row, with one row selected before both allowances. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5dTskCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private def p0d5dTskTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5dTskTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5dTskTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5dTskObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5dTskCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5dTskSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

private def p0d5dTskSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5dTskDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

private def p0d5dTskWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5dTskSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5dTskSigner
  decode_height a u ha := by
    delta p0d5dTskSafety at ha
    rw [p0d5dTskDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5dTskSafety at ha
    rw [p0d5dTskDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5dTskSafety at ha
    rw [p0d5dTskDecodeRow ha]
    rfl

private def p0d5dTskKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem p0d5dTskRem (G ΔF ρbar tail : Time) (kind : PhaseKind) :
    frontierSearch_remaining p G ΔF ρbar tail kind =
      FGCompose.frontierSearch_remaining (p0d5dTskTiming p) G ΔF ρbar tail
        (p0d5dTskKind kind) := by
  cases kind
  · change _ = FGCompose.frontierSearch_remaining (p0d5dTskTiming p) G ΔF ρbar tail .gap
    simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
      frontierSearch_phaseRank_gap, FGCompose.frontierSearch_phaseRank_gap_def,
      Nat.reduceEqDiff, ↓reduceIte]
    rfl
  · change _ = FGCompose.frontierSearch_remaining (p0d5dTskTiming p) G ΔF ρbar tail .topJ
    simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
      frontierSearch_phaseRank_topJ, FGCompose.frontierSearch_phaseRank_topJ_def,
      Nat.reduceEqDiff, ↓reduceIte]
    rfl
  · change _ = FGCompose.frontierSearch_remaining (p0d5dTskTiming p) G ΔF ρbar tail .contest
    simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
      frontierSearch_phaseRank_contest, FGCompose.frontierSearch_phaseRank_contest_def,
      Nat.reduceEqDiff, ↓reduceIte]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, budget arithmetic.
DC: SAME each remaining phase sum fits its frozen total, with a nonnegative tail. -/
theorem frontierSearch_task_bounds [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) (kind : PhaseKind) :
    frontierSearch_remaining p G ΔF ρbar (2 * P p + Γ p G - 9 * p.Δ) kind ≤
        frontierSearchRiseBudget p G ΔF ρbar ∧
    frontierSearch_remaining p G ΔF ρbar (P p - 4 * p.Δ) kind ≤
        frontierSearchRowBudget p G ΔF ρbar ∧
    0 ≤ 2 * P p + Γ p G - 9 * p.Δ ∧ 0 ≤ P p - 4 * p.Δ ∧
    0 ≤ frontierSearchRiseBudget p G ΔF ρbar ∧ 0 ≤ frontierSearchRowBudget p G ΔF ρbar := by
  have h := FGCompose.frontierSearch_task_bounds (p0d5dTskTiming p) (p0d5dTskTimingLaws p)
    hrec.gapPos (ΔF := ΔF) ⟨hbound.kappa_le_R⟩
    (frontierSearch_allowance_nonneg E rho hrec hmode) (p0d5dTskKind kind)
  rw [FGCompose.frontierSearchRiseBudget_def, FGCompose.frontierSearchRowBudget_def] at h
  rw [p0d5dTskRem, p0d5dTskRem, frontierSearchRiseBudget_eq, frontierSearchRowBudget_eq]
  exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, first task.
DC: SAME HG.3 reaches a saved seed or advances phase; HG.4 finishes the rise. -/
theorem frontierSearch_rise_task [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : recoveryStart p E + 2 * P p ≤ ev.time)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    (hhor : ev.time + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (ev.time + frontierSearchRiseBudget p G ΔF ρbar) := by
  obtain ⟨hb, _, ht, _, _, _⟩ := frontierSearch_task_bounds E rho hrec hbound hmode kind
  have hbudget : ev.time + frontierSearch_remaining p G ΔF ρbar
      (2 * P p + Γ p G - 9 * p.Δ) kind ≤ ev.time + frontierSearchRiseBudget p G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail E rho hrec mono crossing origin repair common
    hδ hbound
      perm rowsReceipt progressCoverage hfold faultQ honestQuorum
      (2 * P p + Γ p G - 9 * p.Δ) ht hmode hstart hdelay
      ((hbudget).trans hhor) with hr | ⟨t, _, htail, hserved⟩
  · exact frontierSearch_rise_mono p c E rho (hbudget) hr
  · have hf := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.1
    exact frontierSearch_rise_mono p c E rho (htail.trans (hbudget))
      (healing_frontierTail_rise_of_seed E rho hrec hδ hbound mono crossing
        frontier
        rowsReceipt progressCoverage hfold faultQ honestQuorum hf.le hserved
        ((htail.trans (hbudget)).trans hhor))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, row provenance.
DC: SAME a rise past m supplies an earlier real height-m row through RCap. -/
theorem frontierSearch_row_of_rise (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (cap : RCap p c E rho)
    {i m : Nat} {D : Time} (hm : 1 ≤ m) (hrise : FrontierRiseBy p c E rho i m D) :
    FirstHeightRowBy p c E rho m D := by
  simp only [frontierRiseBy_iff] at hrise
  exact (firstHeightRowBy_iff p c E rho m D).mpr
    (FGCompose.frontierSearch_row_of_rise (R := p0d5dTskCore p c) (S := p0d5dTskSafety p c)
      (O := p0d5dTskObs p c) (T := p0d5dTskTiming p) (E := E) (rho := rho)
      (D := p0d5dTskWire p c) (Ef := p.E) (cert := fgCertificateLaws p)
      (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
      (chainRows := fun nd B => chainWireRows nd.st B) (p0d5dTskTimingLaws p) hs cap hm hrise)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, second task.
DC: SAME HG.3 plus the HG.4 row tail keeps exact height m and the frozen row budget. -/
theorem frontierSearch_row_task [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (origin : RQCOrigin p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (cap : RCap p c E rho)
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
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : recoveryStart p E + 2 * P p ≤ ev.time)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    (hhor : ev.time + frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon) :
    FirstHeightRowBy p c E rho m (ev.time + frontierSearchRowBudget p G ΔF ρbar) := by
  obtain ⟨_, hb, _, ht, _, _⟩ := frontierSearch_task_bounds E rho hrec hbound hmode kind
  have hbudget : ev.time + frontierSearch_remaining p G ΔF ρbar
      (P p - 4 * p.Δ) kind ≤ ev.time + frontierSearchRowBudget p G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail E rho hrec mono crossing origin repair common
    hδ hbound
      perm rowsReceipt progressCoverage hfold faultQ honestQuorum
      (P p - 4 * p.Δ) ht hmode hstart hdelay
      ((hbudget).trans hhor) with hr | ⟨t, _, htail, hserved⟩
  · have hm := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.2.1
    exact frontierSearch_row_of_rise E rho hrec.base.valid.toScheduleWellFormed cap hm
      (frontierSearch_rise_mono p c E rho (hbudget) hr)
  · obtain ⟨r, hr, hfirst, htime⟩ :=
      (firstHeightRowBy_iff p c E rho m _).mp
        (healing_frontierTail_row E rho hrec mono crossing cap scopeProducer writes
          rowCoverage hserved
          ((htail.trans (hbudget)).trans hhor))
    exact (firstHeightRowBy_iff p c E rho m _).mpr
      ⟨r, hr, hfirst, htime.trans (htail.trans (hbudget))⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3, inclusive cut.
DC: SAME Recovery₂ gives an honest node and a cut event under the task's horizon. -/
theorem frontierSearch_cut_start [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {rG M : Nat} {u₀ : Time} (hgst : recoveryStart p E ≤ p.actionTime rG)
    (hfirst : ∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r)
    (hu₀ : u₀ = p.actionTime (rG + 2)) (hdelay : recoveryStart p E + 2 * P p ≤ u₀)
    (hM : M = honestFrontier p c E rho u₀) (hhor : u₀ ≤ rho.horizon) :
    ∃ i ev kind, FrontierSearchStart p c E rho i ev M kind ∧
      ev.time = u₀ ∧ timeIdx rho u₀ = i + 1 := by
  classical
  have hne : rho.honest.Nonempty := by
    have hn : Fintype.card V = p.n :=
      (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hf := hrec.fault
    rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
    have := p.nPos
    omega
  have hlow := healing_recovery_start_lower (p := p) E
  obtain ⟨i, ev, kind, hst, ht, hidx⟩ := FGCompose.frontierSearch_cut_start
    (R := p0d5dTskCore p c) (O := p0d5dTskObs p c) (T := p0d5dTskTiming p) (E := E)
    (rho := rho) (Ef := p.E) (Jst := recoveryStart p E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (p0d5dTskTimingLaws p) hrec.base.valid.toScheduleWellFormed hne
    (fun y hy t ht hh => hrec.awake y hy t ht hh) hrec.base.delta
    (by linarith [hlow, p.deltaPos]) hgst hfirst hu₀ hdelay hM hhor
  cases kind with
  | gap => exact ⟨i, ev, .gap, (frontierSearchStart_iff p c E rho i ev M .gap).mpr hst, ht, hidx⟩
  | topJ =>
    exact ⟨i, ev, .topJ, (frontierSearchStart_iff p c E rho i ev M .topJ).mpr hst, ht, hidx⟩
  | contest =>
    exact ⟨i, ev, .contest, (frontierSearchStart_iff p c E rho i ev M .contest).mpr hst, ht,
      hidx⟩

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3.
DC: SAME event order also permits equal timestamps. -/
theorem frontierSearch_event_time_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {ev ev' : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) (hj : rho.events[j]? = some ev') (hij : i ≤ j) :
    ev.time ≤ ev'.time := by
  exact FGCompose.frontierSearch_event_time_mono E rho hs hi hj hij

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3.
DC: SAME classify a frontier by its accepted evidence. -/
theorem frontierSearch_phase_exists (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i m : Nat) : ∃ kind, AttemptPhaseAt p c E rho i m kind := by
  obtain ⟨k, hk⟩ := FGCompose.frontierSearch_phase_exists (p0d5dTskCore p c)
    (p0d5dTskObs p c) E rho i m
  cases k with
  | gap => exact ⟨.gap, hk⟩
  | topJ => exact ⟨.topJ, hk⟩
  | contest => exact ⟨.contest, hk⟩

end AvailableChain.FGSA.Run
end
