module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetOpening
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetGate

public section

/-! Blueprint 21 H.17:2946–3048; plan J6-3 O2/S1; B1/B17/B18.
DC: SAME exact service at the named cut. PostResetOpening supplies the
opening predicate and the independent exact HEAD/raw/F-floor derivations.
The gate geometry combines these with the cut-aware J6-2 guard and the
old-output bound. The producer gives both service conjuncts without a
service input. S2 and the PostResetGate H6 adapter keep their public types. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O2; B1/B17/B18.
DC: SAME opening geometry field from the separate predicate at its cut.
This projection uses no service premise. -/
theorem healing_postReset_gate_opening_domain
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v) :
    ∀ r, v = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st) := by
  rw [PostResetOpeningDomain_def] at hopening
  exact hopening k hk x v Q hx ht hp hv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan J6-3 O2; B1/B17/B18.
DC: SAME opening-domain membership puts the current F below Q.
This result is restricted to opening labels. -/
theorem healing_postReset_opening_finality
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R) :
    Block.Preceq (eraseFG (storeAt p c E rho k x).fg.F) Q := by
  obtain ⟨D, he, hD⟩ :=
    healing_postReset_gate_opening_domain E rho w i hopening hk hx ht hp hv r hr
  have hF := ((KitFG.mem_filteredFromView _ _ _ _).mp hD).2.1
  have hfg := clock_fg p (storeAt p c E rho k x) (p.actionTime r)
  change FGBlock.Preceq (clock p (storeAt p c E rho k x) (p.actionTime r)).fg.F D at hF
  rw [hfg] at hF
  simpa only [he] using eraseFG_preceq hF

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3024–3040; plan J6-3 O2; B1/B17/B18.
DC: SAME exact HEAD and opening F bound give the receipt target floor.
gate_finality below supplies the target floor at arbitrary labels.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_opening_target_floor_at [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    {v : Slot} (hcone : PostResetConeAt p c E rho w v)
    (i : Nat) (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head v)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true →
      ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head v)) q)
        (ofHead p ⟨.seat (.head v) q, K.root⟩) (SA.voteTime p.toParams v) K →
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho k x)
          (SA.gateTime p.toParams v)).fg.F) K := by
  have hGateHorizon := (hrec.base.valid.toScheduleWellFormed.in_horizon _
    (List.mem_of_getElem? ht)).2
  have hhead := healing_postReset_exactHead_at E rho hrec mono w hreset hcone Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)
  have hFQ := healing_postReset_opening_finality E rho w i hopening hk hx ht hp hv r hr
  intro q hy _ K he
  have heq := exactService_emitted_head E rho hrec.base.valid.toScheduleWellFormed
    v Q hhead q hy K (SA.voteTime p.toParams v) he
  simpa only [heq, clockPre_fg] using hFQ

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3024–3030; plan J6-3 O2; B1/B17/B18.
DC: SAME old-output split and stored strict-slot order. Standing mono has
producer fgsa_rMono. The current F bound is a derived gate fact. -/
theorem healing_postReset_gate_old_output
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (mono : RMonoAll p c E rho) {k : Nat} {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho k x).fg.F) Q) :
    Block.Preceq Q ((fgsaAC E rho).output k x) → (fgsaAC E rho).output k x = Q := by
  intro hQo
  rcases repair_output_bound E rho hE mono hx ht k le_rfl with h | ⟨hm, hsl⟩
  · exact block_preceq_antisymm (block_preceq_trans h hFQ) hQo
  · by_contra hne
    have hlt := repair_stored_slot_lt E rho hE k x hm hQo (Ne.symm hne)
    rw [repair_proposal_slot E rho hp] at hlt
    exact lt_irrefl _ (hlt.trans_le hsl)

section CompleteService
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

variable (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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

include hrec hreset cap rowCovered mono writes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:3021–3040; plan J6-3 O2; B1/B13/B17/B18.
DC: SAME exact gate geometry at the named event-prefix cut.
Standing mono/cap have producers fgsa_rMono/fgsa_rCap_channel. INLINE
rowCovered/writes have producers rowPermission_covered/fgsa_leaseOrigins_lastWrite.
The three carrier inputs remain named predicates at i.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_gate_geometry_at (i : Nat) {v : Slot}
    (hcone : PostResetConeAt p c E rho w v)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i) :
    ExactServiceGateGeometry E rho k x v Q := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hGateHorizon := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
  have hFQ := healing_postReset_gate_finality E rho hrec w hreset cap rowCovered
    i hfp hraw hk hx ht hp hv hcut
  have hhead := healing_postReset_exactHead_at E rho hrec mono w hreset hcone Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)
  have hreceipt : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams v)) v Q := by
    refine ⟨?_, healing_postReset_gate_covered_prefix_at E rho hrec mono w hreset hcone
      hp hv hGateHorizon⟩
    intro q hy _ K he
    have heq := exactService_emitted_head E rho hs v Q hhead q hy K
      (SA.voteTime p.toParams v) he
    simpa only [heq, clockPre_fg] using hFQ
  have hrelease : SA.releaseTime p.toParams v < SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) + 5 * p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hReleaseCut : timeIdx rho (SA.releaseTime p.toParams v) ≤ i :=
    (healing_postReset_time_cut_le_tick E rho hs ht hrelease).trans hk.le
  have hlower : w.sStar ≤ v := (Nat.le_add_right w.sStar 2).trans hv
  have hBatchCut := healing_reset_vote_cutoff (s := v) hreset
    ((Nat.le_succ (w.sStar + 1)).trans hv)
  have hEnabled := healing_recovery_gate_enabled E rho hrec hx ht
    (healing_gate_cut_of_batch_cut E v hBatchCut)
  have hguardAll := healing_postReset_gate_guard_at_cut E rho hrec.toRecovery₂ w i hraw writes
    hlower (healing_window_of_cut E hBatchCut).sync hGateHorizon hx ht hEnabled hk hReleaseCut
  have hresult := healing_postReset_gate_raw_at E rho hrec mono w hreset cap rowCovered
    i hcone hfp hraw hk hx ht hp hv hcut
  have hr := (fgsa_gate_raw_of_nonempty p c E rho hs ht hresult).2
  have hrawQ : (fgsaAC E rho).raw k v x = some Q := by
    have he := fgsa_clockPre_gateView p (storeAt p c E rho k x) v
    have hr' := hr
    rw [clockPre_fg] at hr'
    exact (congrArg (fun st => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho k x).fg.F) st v) he).symm.trans hr'
  exact { toGateReceiptGeometry := hreceipt
          guard := hguardAll Q hrawQ
          old_output := healing_postReset_gate_old_output E rho hrec.base.valid
            mono hx ht hp hFQ
          opening_domain := healing_postReset_gate_opening_domain E rho w i hopening
            hk hx ht hp hv }

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2946–3048; plan J6-3 O2/S1; B1/B13/B17/B18.
DC: SAME complete HEAD and gate conjunction at cut i. The opening input is
separate and follows raw_transfer in the joint order. No service input,
carrier successor, full H0, or complete-run premise is used.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_service_step_at (i : Nat)
    (hcone : ∀ v, timeIdx rho (SA.voteTime p.toParams v) ≤ i →
      PostResetConeAt p c E rho w v)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetService p c E rho w i := by
  rw [PostResetService_def]
  intro v Q hp hv hcut
  refine ⟨fun hh hc => healing_postReset_exactHead_at E rho hrec mono w hreset
    (hcone v hc) Q hp hv hh, ?_⟩
  intro hGateHorizon hGateCut x hx
  have hconeV := hcone v (healing_postReset_head_cut_le_afterTicks E rho
    hrec.base.valid.toScheduleWellFormed hGateCut)
  have hs := hrec.base.valid.toScheduleWellFormed
  have htime : ((4 * v + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams v := by
    change ((4 * v + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (v : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨k, ht, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx
    (4 * v + 6) (htime ▸ hGateHorizon)
    (htime ▸ hrec.awake x hx (SA.gateTime p.toParams v) (by
      have hg := postReset_synchronous_window p c E rho w hreset hv
      change E.t_GST ≤ 4 * p.Δ * (v : Int) - p.Δ at hg
      change E.t_GST ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
      linarith [p.deltaPos]) hGateHorizon)
  rw [htime] at ht
  have hk := healing_postReset_tick_lt_cut E rho hs ht hGateCut
  have hgeom := healing_postReset_gate_geometry_at E rho hrec w hreset cap rowCovered
    mono writes i hconeV hfp hraw hopening hk hx ht hp hv hcut
  have hh := postReset_head_horizon p c rho hGateHorizon
  have hhead := healing_postReset_exactHead_at E rho hrec mono w hreset hconeV Q hp hv hh
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams v := by
    refine (postReset_synchronous_window p c E rho w hreset hv).trans ?_
    change 4 * p.Δ * (v : Int) - p.Δ ≤ 4 * p.Δ * (v : Int) + p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) _ _ hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd hGateHorizon
  obtain ⟨H, hH, hbatch, hfast⟩ := healing_postReset_gate_participation E rho hrec hgsts hh
  have hne : Q ≠ .genesis := by
    intro he
    have hslot := repair_proposal_slot E rho hp
    rw [he] at hslot
    change 0 = v at hslot
    have hvpos : 0 < v := (Nat.zero_lt_succ (w.sStar + 1)).trans_le
      (by simpa only [Nat.add_assoc] using hv)
    rw [← hslot] at hvpos
    exact Nat.lt_irrefl 0 hvpos
  have hEnabled := healing_recovery_gate_enabled E rho hrec hx ht
    (healing_reset_slot_cutoff hreset |>.trans (by
      have hl : (w.sStar : Int) ≤ (v : Int) := by
        exact_mod_cast ((Nat.le_add_right w.sStar 2).trans hv)
      change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (v : Int)
      nlinarith [p.deltaPos]))
  have hHJoined q : q ∈ H ↔ rho.seatOf (.base (.head v)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head v)) q) v (SA.voteTime p.toParams v) := by
    rw [hH q]
    constructor
    · rintro ⟨hy, _⟩
      exact ⟨hy, healing_recovery_joined E rho hrec hy
        (healing_reset_vote_cutoff (s := v) hreset
          ((Nat.le_succ (w.sStar + 1)).trans hv)) hgsts hh⟩
    · rintro ⟨hy, _⟩
      exact ⟨hy, hrec.awake _ hy _ hgsts hh⟩
  obtain ⟨hresult, ⟨j, hj, hpass⟩, hwrite, hstable, hsource⟩ :=
    exactService_gate_at_of_head_on (hroots := hrec.base.receiptIdealization)
      E rho hrec.base.valid hrec.base.delta hrec.base.cstar v Q hne
      (fun y hy _ => hhead y hy) hSync hx ht hgeom
      (healing_gate_receipt_scope_recovery E rho hrec mono hgsts hx hEnabled
        hgeom.toGateReceiptGeometry) H hHJoined hbatch hfast
  exact ⟨hresult, ⟨j, healing_postReset_tick_lt_cut E rho hs hj.1 hGateCut, hj.1, hpass⟩,
    hwrite, hstable, hsource⟩

end CompleteService

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3048; plan J6-2 S2; B1/B17.
DC: SAME projection of exact service from the named carrier at its cut.
The proposal, HEAD, and post-gate cuts are explicit. The gate witness
keeps its event and passed guard when its prefix bound is removed. -/
theorem healing_postReset_exactService_at_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hservice : PostResetService p c E rho w i)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hProposalCut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i)
    (hHeadCut : SA.voteTime p.toParams v ≤ rho.horizon →
      timeIdx rho (SA.voteTime p.toParams v) ≤ i)
    (hGateCut : SA.gateTime p.toParams v ≤ rho.horizon →
      afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i) :
    ExactService p c E rho v Q := by
  rw [PostResetService_def] at hservice
  obtain ⟨hhead, hgate⟩ := hservice v Q hp hv hProposalCut
  refine ⟨fun hh x hx _ => hhead hh (hHeadCut hh) x hx, ?_⟩
  intro hg x hx _
  obtain ⟨hraw, ⟨j, _, ht, hpass⟩, hfast, hstable, hsource⟩ :=
    hgate hg (hGateCut hg) x hx
  have hEnabled : enabledGateAt p c E rho j x v := by
    obtain ⟨y, s, hy, _⟩ := hpass
    have he := Option.some.inj (ht.symm.trans hy.1)
    obtain ⟨rfl, htime⟩ := V2.Event.tick.inj he
    have hslot : s = v := by
      change 4 * p.Δ * (v : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at htime
      exact_mod_cast (show (s : Int) = (v : Int) by nlinarith [p.deltaPos])
    subst s
    exact hy
  exact ⟨hraw, ⟨j, hEnabled, hpass⟩, hfast, hstable, hsource⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3048; plan J6-2 S2; B1/B17.
DC: SAME a carrier cut at or after the run's length gives the H3 shape.
The cut may exceed the run's length. Each time cut is bounded by the length
of the event list; the two horizon guards remain in ExactService. -/
theorem healing_postReset_exactService
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hcomplete : rho.events.length ≤ i)
    (hservice : PostResetService p c E rho w i) : H3 p c E rho w := by
  intro v Q hp hv
  have hProposalCut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  have hHeadCut : timeIdx rho (SA.voteTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  have hGateCut : afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  exact healing_postReset_exactService_at_cut E rho w i hservice hp hv
    hProposalCut (fun _ => hHeadCut) (fun _ => hGateCut)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_opening_target_floor [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (i : Nat) (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head v)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true →
      ∀ K, HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head v)) q)
        (ofHead p ⟨.seat (.head v) q, K.root⟩) (SA.voteTime p.toParams v) K →
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho k x)
          (SA.gateTime p.toParams v)).fg.F) K := by
  exact healing_postReset_opening_target_floor_at E rho hrec mono w hreset
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    i hopening hk hx ht hp hv r hr

section RunConeWrappers
variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
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

include hrec hreset hcone cap rowCovered mono writes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_gate_geometry (i : Nat)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i)
    {k : Nat} (hk : k < i) {x : V} {v : Slot} {Q : Block}
    (hx : x ∈ rho.honest) (ht : IsGateTick p c rho k x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hcut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i) :
    ExactServiceGateGeometry E rho k x v Q := by
  exact healing_postReset_gate_geometry_at E rho hrec w hreset cap rowCovered mono writes i
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone v) hfp hraw hopening hk hx ht hp hv hcut

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_service_step (i : Nat)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetService p c E rho w i := by
  exact healing_postReset_service_step_at E rho hrec w hreset cap rowCovered mono writes i
    (fun v _ => (postResetRetainedCone_iff_at p c E rho w).mp hcone v)
    hfp hraw hopening

end RunConeWrappers

end AvailableChain.FGSA.Run
end
