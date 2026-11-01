module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Growth

public section

/-! WC J3, plan §§6.12–7; DC joint growth contract.
These tests retain the exact deadline and the inclusive read at the cut. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth

open AvailableChain.SimplexFG AvailableChain.KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J3, plan §7; DC AvailableChainGrowth.afterGST: match the reviewed growth type. -/
theorem growthContract (ΔF : Time) (u : Slot)
    (Q : Block) (iStar : Nat)
    (hcache : WCCachedSafety p c E rho iStar Q)
    (hcover : ∀ pt : PtSP, u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon →
      ∃ x ∈ rho.honest, Block.Preceq pt.P (S_at p c E rho rho.events.length x)) :
    WCGrowthStatement p c E rho ΔF u Q iStar :=
  wc_growth_of_safety_inclusion ΔF u Q iStar hcache hcover

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC cut reads: match the reviewed public-read type. -/
theorem readContract (w : HealingWitness) (iStar : Nat) :
    WCCutPublicReadStatement p c E rho w iStar := by
  intro hs hcut t ht
  exact wc_cut_publicRead hs hcut t ht

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC cut reads: include same-time deliveries at the trigger. -/
theorem readAtCut {u : Slot} {iStar : Nat}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hcut : iStar = afterTicksIdx rho (SA.gateTime p.toParams u)) :
    iStar ≤ timeIdx rho (SA.gateTime p.toParams u) ∧
      timeIdx rho (SA.gateTime p.toParams u) ≤ rho.events.length :=
  wc_cut_publicRead hs hcut _ le_rfl

/-- WC J3, plan §7; DC checkpoint: fixed seed, four Statements, exact growth deadline. -/
theorem checkpointContract [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hinduction : WCSeededInductionStatement p c E rho ΔF w iStar)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar)
    (hsafety : WCSeededSafetyStatement p c E rho w iStar)
    (hfinalBelow : WCFinalBelowStatement p c E rho ΔF w iStar) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
      enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → SA.gateTime p.toParams w.u ≤ rho.horizon →
    SSafeFromCut₂ p c E rho iStar w.QStar ΔF ∧
    (∀ pt : PtSP, w.u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E rho pt) ∧
    ∀ G' : Time, 4 * p.Δ ≤ G' →
      AwakeProposerRecurrenceFrom p c E rho (SA.gateTime p.toParams w.u) G' →
      ∀ t : Time, SA.gateTime p.toParams w.u ≤ t →
        t + G' + 6 * p.Δ ≤ rho.horizon → JointGrowthAt p c E rho t (t + G' + 6 * p.Δ) :=
  wc_checkpoint ΔF w iStar hinduction hframeLive hsafety hfinalBelow

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth
end

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth.growthContract

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth.readContract

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth.readAtCut

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth.checkpointContract
