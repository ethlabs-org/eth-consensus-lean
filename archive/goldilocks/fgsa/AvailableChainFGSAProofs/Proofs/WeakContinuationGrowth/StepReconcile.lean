module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepService
public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC finality at a delivery cannot overtake the preceding honest outputs. -/
theorem wcg_reconcileBound (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
  (w : HealingWitness) (iStar : Nat) :
  ∀
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
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ v o t, rho.events[i]? = some (.deliver v o t) →
    ∀ x y, x ∈ rho.honest → confirmedReaderIdx p c E rho y i →
      Block.Preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i y) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi _hilen inv v o t he x y hx hy
  obtain ⟨D, hD, hF⟩ := (hstore (i + 1) x hx).1.fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · have hbelow := (wcg_lowFinalized (hroots.toNamedRootCollisionFree E rho) haccountable hs
      D _ _ (wcg_finalizedOccurrence hscopeRows hnoslash D _ _
        (rootScope_store hx hD) hF rfl) hlo).2
    exact block_preceq_trans hbelow (inv.served i y hi le_rfl hy)
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, q, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ
      (hroots.toNamedRootCollisionFree E rho) hheldRows hfinalHead hqc
      hemitted (i + 1) x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
  have hfi : jf < i := by
    rcases (Nat.le_of_lt_succ hjf).lt_or_eq with h | h
    · exact h
    · subst jf
      have hf := haf.2.1
      rw [he] at hf
      cases hf
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E rho (i + 1) x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt q rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact block_preceq_trans (eraseFG_preceq hXK)
      (block_preceq_trans (heq ▸ hbelow) (inv.served i y hi le_rfl hy))
  obtain ⟨C, hr, hKC⟩ := inv.suffixSources jt q rt K (Nat.le_of_not_gt hbefore)
    (hjt.trans hfi) haT.1 haT.2.1 hK
  have hhor : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ ≤ rho.horizon :=
    hgap.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? haf.2.1)).2
  have hcut : afterTicksIdx rho (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ) ≤ i := by
    apply le_trans (b := jf) _ (Nat.le_of_lt hfi)
    by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hm : V2.Event.tick z (p.actionTime rf) ∈ rho.events.filter
        (cutPred (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)) := by
      rw [V2.D.Engine.filter_eq_take hvalid.toScheduleWellFormed _ (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := jf)
      change (rho.events.take (afterTicksIdx rho
        (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)))[jf]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact haf.2.1
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have ht : p.actionTime rf ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    exact (not_lt.mpr ht) hgap
  have hserved := wcg_service4_prefix hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i inv jt q (rt * p.R) C hr hhor i y hcut le_rfl hy
  exact block_preceq_trans (eraseFG_preceq hXK) (block_preceq_trans hKC hserved)

end AvailableChain.FGSA.Run
end
