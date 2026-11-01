module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepGateBatch
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Safety
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel

public section

/-! WC plan §6.5; DC gate order and the guard precede retrospective transfer. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC the new gate extends the seed and all results at earlier labels. -/
theorem wcg_gateResult (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
    (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
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
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → enabledGateAt p c E rho i x s → w.u < s →
    ∃ B, gateResultAt p c E rho i = some (some B) ∧ gatePassedAt p c E rho i ∧
      Block.Preceq w.QStar B ∧
      (∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s → Block.Preceq C B) ∧
      (∀ j y r C, WCResult p c E rho w iStar i j y r C → Block.Compatible C B) ∧
      Block.Compatible (S_at p c E rho i x) B := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv hEnabled hslabel
  have ht := hEnabled.1
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hhead := wcg_gateHeads ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv ht hslabel
  have batch := wcg_gateBatch hcausal ΔF w iStar hvalid hlinked hcstar hnr hdelta
    hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv hEnabled hslabel
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  have hFS : Block.Preceq (eraseFG pre.fg.F) (S_at p c E rho i x) := by
    change Block.Preceq (eraseFG (clockPre p _ _).fg.F) _
    rw [clockPre_fg]
    exact nestOK_stateBefore E rho i x
  have hFQ : Block.Compatible (eraseFG pre.fg.F) w.QStar := by
    dsimp only [pre]
    rw [clockPre_fg]
    change Block.Compatible (F_at p c E rho i x) w.QStar
    have ho := wcg_finalHistoryAt hs inv hi le_rfl hx
    rcases ho.origin with h | ⟨j, y, r, C, hr, hFC⟩
    · exact block_compatible_of_common h (block_preceq_refl _)
    · obtain ⟨D, hD, hQD, _⟩ := inv.nonempty j y r hr.afterCut hr.completed hr.honest
        (wcg_result_enabled hr hsch) hr.label
      have he : D = C := Option.some.inj (Option.some.inj (hD.symm.trans hr.value))
      exact block_compatible_of_common hFC (he ▸ hQD)
  have hbatchQ := batch w.QStar (fun k y hk hJ =>
    (hhead k y (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk hJ).1)
  obtain ⟨B, hraw, hQB⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
    (eraseFG pre.fg.F) w.QStar s w.QStar.root hFQ hbatchQ.1 hbatchQ.2.1 hbatchQ.2.2
  have hrawAt : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
      (eraseFG pre.fg.F) (actView pre) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht]
    change _ = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) _).fg.F) _ s)
    rw [clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho hEnabled)
  have hB : gateResultAt p c E rho i = some (some B) := hrawAt.trans (congrArg some hraw)
  have ordered : ∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s →
      Block.Preceq C B := by
    intro j y r C hr hrs
    have hc := block_compatible_of_preceq_compatible hFS
      (wcg_result_output_compatible hsch inv hr hi le_rfl hx)
    have hb := batch C (fun k z hk hJ =>
      (hhead k z (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk hJ).2 j y r C hr hrs)
    obtain ⟨D, hD, hCD⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
      (eraseFG pre.fg.F) C s C.root hc hb.1 hb.2.1 hb.2.2
    exact (Option.some.inj (hD.symm.trans hraw)) ▸ hCD
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hc : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hsyncLabel := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s)
    hsync (fgsaDelay_nonrow E.Δ _) hGST (by
      rw [hdelta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have compatible : ∀ j y r C, WCResult p c E rho w iStar i j y r C →
      Block.Compatible C B := by
    intro j y r C hr
    have hle : r ≤ s := by
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hr.event
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp ht
      have hk := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hr.completed
      rw [hje, hie] at hk
      have ht := V2.D.Engine.time_le_of_key_le _ _ hk
      change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
      have hc : (r : Int) ≤ s := by nlinarith [p.deltaPos]
      exact Int.ofNat_le.mp hc
    rcases hle.lt_or_eq with hlt | heq
    · exact block_compatible_of_common (ordered j y r C hr hlt) (block_preceq_refl B)
    · subst r
      exact fgsa_sameLabel_on p c E rho hvalid s
        (fgsa_sameLabel_serviceScope E rho hvalid hnr hdelta s hsyncLabel)
        (hroots.toNamedRootCollisionFree E rho)
        y x C B hr.honest hx
        ((gateResultAt_eq_gateResult p c E rho hsch hr.event).symm.trans hr.value)
        ((gateResultAt_eq_gateResult p c E rho hsch ht).symm.trans hB)
  have hFB : Block.Preceq (eraseFG pre.fg.F) B := by
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · cases hraw
      apply walk_covers_of_dominated_suffix _ _ _ _ _
      · exact block_compatible_of_common (block_preceq_refl _) (block_preceq_refl _)
      · intro C hAC hCA
        change (!decide (_ = C) && Block.preceq _ C) = true at hAC
        have heq := block_preceq_antisymm (Bool.and_eq_true_iff.mp hAC).2 hCA
        simp only [heq, decide_true, Bool.not_true, Bool.false_and, Bool.false_eq_true] at hAC
    · contradiction
  have hSB : Block.Compatible (S_at p c E rho i x) B := by
    rcases inv.outputOrigin i x hi le_rfl hx with hq | ⟨j, y, r, hr⟩ | ⟨l, _, hli, he, _⟩
    · rw [hq]
      exact block_compatible_of_common hQB (block_preceq_refl B)
    · exact compatible j y r _ hr
    · rw [he]
      have hFi : Block.Preceq (F_at p c E rho i x) B := by
        change Block.Preceq (eraseFG (clockPre p _ _).fg.F) B at hFB
        rwa [clockPre_fg] at hFB
      exact block_compatible_of_common
        (block_preceq_trans (eraseFG_preceq (hmono l i x hx hli).1) hFi)
        (block_preceq_refl B)
  refine ⟨B, hB, ?_, hQB, ordered, compatible, hSB⟩
  refine ⟨x, s, hEnabled, ?_, B, hraw, ?_⟩
  · change ((clockPre p (storeAt p c E rho i x) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  · apply List.any_eq_false.mpr
    intro row hr
    have hold := (clockPre_obligations_sublist p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s)).subset hr
    have hb := htargets i x row hold
    have hc := block_compatible_of_preceq_compatible hb hSB
    simpa only [Block.Compatible, Bool.not_eq_true', Bool.not_eq_false] using hc

end AvailableChain.FGSA.Run
end
