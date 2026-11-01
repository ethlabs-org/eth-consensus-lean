module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG KitFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
/-- WC plan §6.5; DC every event strictly after the cut has a later key. -/
private theorem time_before_cut (hsch : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {t : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho t) : e.time ≤ t := by
  have hm : e ∈ rho.events.filter (cutPred t) := by
    rw [V2.D.Engine.filter_eq_take hsch (cutPred t) (by
      intro e f hk hf
      exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho t))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hk := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem wcg_gateHeads (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
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
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s →
    ∀ k y, y ∈ rho.honest → rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      Block.Preceq w.QStar (headAtIdx p c E rho k s) ∧
      ∀ j z r B, WCResult p c E rho w iStar i j z r B → r < s →
        Block.Preceq B (headAtIdx p c E rho k s) := by
  intro hvalid _hlinked _hcstar _hnr hdelta _hroots _hsync _hdeltaF _hfaultQ
    _haccountable hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead hs i x s _hi _hilen inv ht hlabel k y hy hk hJ
  have hsch := hvalid.toScheduleWellFormed
  by_cases hfirst : s = w.u + 1
  · subst s
    obtain ⟨l, _, hhead⟩ := hs.nextHeads y hy
    have he : l = k := fgsa_tick_unique E rho hsch hhead.event hk
    refine ⟨he ▸ hhead.covers, ?_⟩
    intro j z r B hr hlt
    have hh := hr.label
    exact ((Nat.not_lt_of_ge (Nat.succ_le_of_lt hh)) hlt).elim
  have hsuc : s - 1 + 1 = s := Nat.sub_add_cancel
    (Nat.succ_le_of_lt ((Nat.zero_le w.u).trans_lt hlabel))
  have hprev : w.u < s - 1 := by
    simp only [Slot] at hlabel hfirst ⊢
    omega
  have hclock : ((4 * (s - 1) + 6 : Nat) : Time) * p.Δ =
      SA.gateTime p.toParams (s - 1) := by
    change ((4 * (s - 1) + 6 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hlt : SA.gateTime p.toParams (s - 1) < SA.gateTime p.toParams s := by
    have hh : ((s - 1 : Nat) : Int) < s := by
      exact_mod_cast Nat.sub_lt ((Nat.zero_le w.u).trans_lt hlabel) (by decide : 0 < 1)
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ <
      4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hhor : SA.gateTime p.toParams (s - 1) ≤ rho.horizon :=
    hlt.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hcutTime : SA.voteTime p.toParams (w.u + 1) ≤
      SA.gateTime p.toParams (s - 1) := by
    have hh : ((w.u + 1 : Nat) : Int) ≤ (s - 1 : Nat) :=
      Int.ofNat_le.mpr (Nat.succ_le_of_lt hprev)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  obtain ⟨z, l, hz, hG, _⟩ := wcg_joined_gate_witness hvalid hdelta (s - 1)
    (hpart _ hcutTime hhor) hhor
  have hl := hG.1
  have hli : l < i := V2.D.Engine.eventIndex_lt_of_time_lt hsch hl ht hlt
  have hafter : iStar ≤ l := by
    by_contra hn
    have hh := time_before_cut hsch hl (hs.cut ▸ (Nat.lt_of_not_ge hn))
    change SA.gateTime p.toParams (s - 1) ≤ SA.gateTime p.toParams w.u at hh
    have hp : (w.u : Int) < (s - 1 : Nat) := Int.ofNat_lt.mpr hprev
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ at hh
    nlinarith [p.deltaPos]
  obtain ⟨C, hC, hQC, _⟩ := inv.nonempty l z (s - 1) hafter hli hz hG hprev
  have hresult : WCResult p c E rho w iStar i l z (s - 1) C :=
    ⟨hz, hafter, hli, hprev, hl, hC⟩
  have covers (j : Nat) (v : V) (B : Block)
      (hr : WCResult p c E rho w iStar i j v (s - 1) B) :
      Block.Preceq B (headAtIdx p c E rho k s) := by
    obtain ⟨q, _, hhead⟩ := inv.retrospective j v (s - 1) B hr y hy (hsuc ▸ hJ)
    rw [hsuc] at hhead
    exact (fgsa_tick_unique E rho hsch hhead.event hk) ▸ hhead.covers
  have hCH := covers l z C hresult
  refine ⟨block_preceq_trans hQC hCH, ?_⟩
  intro j v r B hr hrs
  rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt hrs) with hlt | heq
  · exact block_preceq_trans (inv.ordered j l v z r (s - 1) B C hr hresult hlt) hCH
  · subst r
    exact covers j v B hr

theorem wcg_gateFinalOrigin (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
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
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s →
      Block.Preceq (F_at p c E rho i x) w.QStar ∨
      ∃ j y r B, WCResult p c E rho w iStar i j y r B ∧ r < s ∧
        Block.Preceq (F_at p c E rho i x) B := by
  intro hvalid hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel hqc _hstrat _hnoslash hemitted _htargets _hlease _hfast _hdeadlines
    hheldRows _hscopeRows hfinalHead hs i x s hi _hilen inv ht _hlabel
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  obtain ⟨D, hD, hF⟩ := ((inv.finite i hi le_rfl).store x hx).fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · exact Or.inl (block_preceq_trans
      (inv.lowFinalized i x D _ _ hi le_rfl ⟨hx, hD⟩ hF rfl hlo) hs.sourcePrefix)
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, v, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ (hroots.toNamedRootCollisionFree E rho) hheldRows hfinalHead hqc
      hemitted i x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
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
      some ((finalityView p D).h_F, (storeAt p c E rho i x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt v rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))
  have hafter : iStar ≤ jt := Nat.le_of_not_gt hbefore
  obtain ⟨C, hC, hKC⟩ := inv.suffixSources jt v rt K hafter (hjt.trans hjf) haT.1 haT.2.1 hK
  have htime : p.actionTime rf ≤ SA.gateTime p.toParams s := by
    obtain ⟨hfl, hfe⟩ := List.getElem?_eq_some_iff.mp haf.2.1
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hvalid.sorted) jf i hfl hil hjf
    rw [hfe, hie] at hk
    exact V2.D.Engine.time_le_of_key_le _ _ hk
  have hlt : rt * p.R < s := by
    have hh : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ < SA.gateTime p.toParams s :=
      hgap.trans_le htime
    change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ + 4 * p.Δ <
      4 * p.Δ * (s : Int) + 6 * p.Δ at hh
    have hcast : ((rt * p.R : Nat) : Int) < s := by nlinarith [p.deltaPos]
    exact Int.ofNat_lt.mp hcast
  exact Or.inr ⟨jt, v, rt * p.R, C, hC, hlt, block_preceq_trans (eraseFG_preceq hXK) hKC⟩


end AvailableChain.FGSA.Run
end
