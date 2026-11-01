module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Step
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.FinalBelow

public section

/-! WC plan §§6.6–6.8; DC joint event induction and the five seeded safety fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC initialization and actual event steps prove the complete suffix invariant. -/
theorem wc_seededInduction : WCSeededInductionStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have initial := wc_init hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hs.within
  have step := wc_step hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have all : ∀ i, iStar ≤ i → i ≤ rho.events.length → WCInv p c E rho w iStar i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; exact initial
    | succ i hi ih =>
      intro hbound
      have hlt : i < rho.events.length := by omega
      exact step i hi hlt (ih (Nat.le_of_lt hlt)) rho.events[i]
        (List.getElem?_eq_getElem hlt)
  intro i hi
  exact all i hi.1 hi.2

/-- WC plan §8 Job 2; DC all five safety fields follow from the seed and separate lane premises. -/
theorem wc_seededSafeFromCut :
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
  WCSeed p c E rho w iStar → SSafeFromCut₂ p c E rho iStar w.QStar ΔF := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have hinv := wc_seededInduction hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have hsafe := wc_seededSafety hvalid.toScheduleWellFormed hs hinv
  have hfinal := wc_finalBelow hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv
  exact ⟨hsafe.1, hsafe.2.1, hsafe.2.2.1,
    (fun i x y hlo hhi hx hy => hfinal i x y ⟨hlo, hhi⟩ hx hy), hsafe.2.2.2⟩

end AvailableChain.FGSA.Run
end
