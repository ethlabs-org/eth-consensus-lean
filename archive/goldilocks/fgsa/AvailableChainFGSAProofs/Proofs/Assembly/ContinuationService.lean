module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export
-- shake: keep (current-epoch service boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
-- shake: keep (durable channels and row origins)

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J1; DC premise discharge: supply every separate lane input to its consumer.
The consumer telescope is the literal [L] expansion; no foundation bundle is passed. -/
theorem assembly_wcg_dischargeL {ΔF : Time} {w : HealingWitness} {Result : Prop}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (haccountable : FinalitySlashableBound p c E rho)
    (hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
    (hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
      rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
        wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
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
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result := by
  have hs := hb.valid.toScheduleWellFormed
  have hstore := fgsa_rStore p c E rho
  apply consume hb.valid hb.linked hb.cstar hb.restartsAtWakes hb.delta hb.receiptIdealization
    hsync hdeltaF hq haccountable hpart
    hstore ⟨fgsa_rStoreDurable p c E rho, fgsa_rStoreEpoch p c E rho⟩
    (fgsa_rMonoAll p c E rho)
    (fgsa_rActive p c E rho) (fgsa_rFrameExactNext p c E rho) (fgsa_rFrameNextEpoch p c E rho)
    (fgsa_rRec p c E rho) (fgsa_rGeo p c E rho) (fgsa_rCert p c E rho)
    (sourceDiscipline_tSrc p c E rho hs) (sourceDiscipline_labelBound p c E rho hs)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (fgsa_clientSafeAll p c E rho hb.linked)
  · intro j x r a e ha he
    exact sourceDiscipline_emittedName p c E rho hs ha he
  · intro i x row hr
    exact storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
  · intro i x row hr
    obtain ⟨j, hj, s, B, hG, hpass, hB, hp, hkeys, hdeadline, hrelease, hlast⟩ :=
      fgsa_leaseOrigins_lastWrite p c E rho hs i x row hr
    refine ⟨j, hj, s, B, hG, hpass, hB, hp, hkeys, hdeadline, hrelease, ?_⟩
    intro k w C hjk hki hEnabled
    dsimp only
    intro hn hc hg
    exact hlast k w C hjk hki hEnabled.1
      (by rw [clockPre_joined]; exact fgsa_gate_joined_of_enabled E rho hEnabled) hn hc hg
  · exact fgsa_leaseOrigins_fastWrites_epoch p c E rho hs
  · exact fgsa_leaseOrigins_ancestorDeadlines p c E rho
  · exact held_chain_row_origin_before p c E rho hb.valid.toUnforgeableSignatures hs
  · exact hscopeRows
  · intro j z r a u ha hsign hd fp hf
    exact cap_finality_head p c E rho ha hsign hd fp hf


/-- Discharge the returned WCG service from the current run and its actual seed.
The participation input covers every time through selection of the gate actor. -/
theorem wcg_service4OfSeed {ΔF : Time} {w : HealingWitness} {iStar : Nat}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (ha : FinalitySlashableBound p c E rho)
    (hp : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
    (hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
      rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
        wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
    (hs : WCSeed p c E rho w iStar)
    (hinv : ∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) :
    ∀ j x s B, x ∈ rho.honest → iStar ≤ j → IsGateTick p c rho j x s → w.u < s →
      gateResultAt p c E rho j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
        i ≤ rho.events.length → confirmedReaderIdx p c E rho y i →
          Block.Preceq B (S_at p c E rho i y) := by
  apply assembly_wcg_dischargeL hb hsync hdeltaF hq ha hp hscopeRows
  intro hvalid hlinked hcstar hwakes hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
  exact wcg_service4 hvalid hlinked hcstar hwakes hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv

omit [Fintype V] in
/-- A later read uses its own confirmed epoch and both getters.
The service cut includes all ticks at its deadline; no original reader tick is needed. -/
theorem wcg_service_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (ht : d ≤ t) (hy : confirmedReaderIdx p c E rho y (timeIdx rho t)) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Block.Preceq B (V2.D.outputAt E rho g y t) := by
  intro g hg
  exact wcg_service_result_outputs hS hservice
    ((preIdx_le_afterTicksIdx E rho hS d).2.trans
      (V2.D.Engine.read_length_mono (rho := rho) d t ht)) hy g hg

end AvailableChain.FGSA.Run
end
