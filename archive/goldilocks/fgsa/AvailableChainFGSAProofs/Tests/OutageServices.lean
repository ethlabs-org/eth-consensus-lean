module
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDeadlines
public import AvailableChainFGSAProofs.Proofs.Outage.Induction -- shake: keep (source declarations)
public import AvailableChainFGSAProofs.Proofs.Clean.Closure
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources

public section

namespace AvailableChain.FGSA.Run.Tests.OutageServices

open AvailableChain.SimplexFG Gen.Pure

/-- The regime supplies both receipt services. Receivers in W are included. -/
theorem restored_receipt_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ :=
  outage_continuation_receipt h

/-- The actual opponent release bound consumes E's strict good-set count. -/
theorem good_release_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hBase : Base₂ p c E rho) (fast : Bool) (b₀ : Time) (r s : Slot) (B : Block)
    (i : Nat) (x : V)
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card)
    (hheads : ∀ y ∈ outageH p E rho s \ outageW p E rho fast b₀ r,
      ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ q K, o.auth = .seat (.base (.head s)) q →
        HeadTargetAtEmission p c E rho y o t K → Block.Compatible K B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B <
      SA.releaseThreshold p.toParams :=
  (outage_good_release_bound E rho hBase.valid hBase.cstar hBase.idealization
    fast b₀ r s B i x hheads).trans_lt (outage_opponents_lt_release hBase hCount)

/-- A row expires at equality; a later row remains in the same model view. -/
theorem handover_expiry_equality :
    let st : GridCO.State 1 .root :=
      { GridCO.initial 1 .root with obligations := [(.genesis, 1, 25), (.genesis, 2, 26)] }
    (GridCO.expire { st with now := 25 } 25).obligations = [(.genesis, 2, 26)] := by
  rfl

/-- The real prefix producers close the pending seed without a pending-source input.
The result includes all honest actions, even actions by receivers in W. -/
theorem pending_seed_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ ΔF : Time} (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF)
    (htsrc : TSrc p c E rho) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) :=
  outage_arming_sources_from_prefix h htsrc hc htransfer

/-- The checked P-Cl1 Clean history supplies the exact transfer projection.
This test derives the pending seed without a separate transfer or source premise. -/
theorem pending_seed_of_clean_history {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ ΔF : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) := by
  have hTransfer := (cleanHistoryAt_body p c E rho h hq hf hsrc).2.2.1
  exact outage_arming_sources_from_prefix h htsrc hc
    (fun y z s C H hy hz hJ hcut hC hH => hTransfer y z s C H hy hz hcut hC hJ hH)

/-- The handover consumer uses actual gate origins in all receiver epochs.
It needs only the late-result projection of the joint invariant. -/
theorem handover_rows_consumer {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (r : Slot) (B : Block) {i : Nat} {x : V}
    (hi : rho.events[i]? = some (.tick x (OutageEnd p r)))
    (hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B) :
    ∀ row ∈ (storeAt p c E rho (i + 1) x).base.obligations, Block.Compatible row.1 B :=
  outage_handover_tick_rows hs r B hi hResults

/-- Clean retained provenance supplies the general fast construction at actual joined reads. -/
theorem joined_provenance_producer {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hV : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ) :
    ArmingJoinedProvenance (c := c) E rho := by
  intro s i y hy hi hJ
  have hs := hV.toScheduleWellFormed
  have hw := arming_joined_window (c := c) hy hJ
  have ht : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    rw [arming_proposal_eq, arming_vote_eq]; push_cast; linarith [p.deltaPos]
  obtain ⟨it, hit⟩ := arming_tick_exists hs hdelta hy (4 * s) (arming_proposal_nat p s)
    (ht.trans (hs.in_horizon _ (List.mem_of_getElem? hi)).2)
    (hw.awake _ (by rw [arming_proposal_eq]; have := p.deltaPos; positivity) le_rfl ht)
  exact clean_headVotes_provenance E rho hV i y s hi hJ hit


/-- The real Clean and P-Fd producers discharge every pending seed input at any fast cut. -/
theorem fast_seed_of_clean_history {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh ∧
      OutageSourceHistory p c E rho B
        (afterTicksIdx rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  have htransfer := (cleanHistoryAt_body p c E rho h.sleepPre hq hf hsrc).2.2.1
  exact outage_fast_seed_scoped h hf hsrc htsrc hState hh
    (fun y z s C H hy hz hJ hcut hRes hHead => htransfer y z s C H hy hz hcut hRes hJ hHead)
    (joined_provenance_producer h.pre.base.valid h.pre.base.delta) hread hne

/-- The exact P-Fd named-source producer closes the general protection and domain seed. -/
theorem pending_protection_of_source_discipline {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (htsrc : TSrc p c E rho) {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      OutageProtection p B (l + 1) st ∧
        (Block.Preceq B (F_at p c E rho I y) ∨
          (∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z)) :=
  outage_arming_protection_scoped h hf htsrc hne hc
    (fun _ _ _ _ _ ha he => by
      simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf]
        using sourceDiscipline_emittedName p c E rho h.base.valid.toScheduleWellFormed ha he)
    hgate

/-- The full pre-restoration induction consumes the actual Clean state and duty
producers. Restarts are allowed; no local seed or good-target callback is supplied. -/
theorem pre_restored_joint_of_clean_history {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hq : FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block} {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hβ : eraseFG β = B) (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ i, afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i → i ≤ rho.idxBefore b₁ →
      OutageSourceHistory p c E rho B i ∧
      OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho)
        fast b₀ B (l + 1) i ∧ OutageNamedHistory p c E rho β i ∧
      ∀ y ∈ coveredNodes p E rho fast b₀,
        OutageProtection p B (l + 1) (storeAt p c E rho i y) := by
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  exact outage_armed_induction_scoped h hf hsrc
    (sourceDiscipline_tSrc p c E rho h.pre.base.valid.toScheduleWellFormed)
    (fun _ _ _ _ _ ha he => by
      simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf]
        using sourceDiscipline_emittedName p c E rho h.pre.base.valid.toScheduleWellFormed ha he)
    hState
    (joined_provenance_producer h.pre.base.valid h.pre.base.delta) hne hc hβ hgate

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.restored_receipt_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.good_release_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.handover_expiry_equality
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pending_seed_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pending_seed_of_clean_history
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.handover_rows_consumer

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.joined_provenance_producer

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.fast_seed_of_clean_history

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pending_protection_of_source_discipline

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pre_restored_joint_of_clean_history

end AvailableChain.FGSA.Run.Tests.OutageServices
end
