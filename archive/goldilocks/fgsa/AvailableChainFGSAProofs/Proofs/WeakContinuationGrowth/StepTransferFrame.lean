module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Frame
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Safety
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! WC plan §6.5; DC retrospective frame bounds use only earlier result labels. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC the next HEAD clock runs no gate. -/
private theorem transfer_vote_clock (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.voteTime p.toParams (s + 1)) =
      clockPre p st (SA.voteTime p.toParams (s + 1)) := by
  have hn : isGateTime p (SA.voteTime p.toParams (s + 1)) ≠ true := by
    intro hh
    obtain ⟨r, hr⟩ := (isGateTime_iff p _).mp hh
    symm at hr
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ =
      4 * p.Δ * (r : Int) + 6 * p.Δ at hr
    push_cast at hr
    have hd := p.deltaPos
    rcases Nat.lt_or_ge r s with hrs | hsr
    · have hi : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast hrs
      nlinarith
    · have hi : (s : Int) ≤ (r : Int) := by exact_mod_cast hsr
      nlinarith
  change (if isGateTime p _ then _ else _) = _
  rw [ite_eq_right hn]

/-- WC plan §6.5; DC the earlier HEAD frame is bounded by the newly ordered result. -/
theorem wcg_retrospectiveFrame (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
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
  WCSeed p c E rho w iStar → ∀ i k x y s (Bfg : FGBlock (Fin p.n)),
    iStar ≤ i → i < rho.events.length → WCInv p c E rho w iStar i →
    IsGateTick p c rho i x s → w.u < s → k < i →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    Block.Preceq w.QStar (eraseFG Bfg) →
    (∀ j z r C, WCResult p c E rho w iStar i j z r C → r < s →
      Block.Preceq C (eraseFG Bfg)) →
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    WCFrameLiveBelow p st (.head (s + 1)) Bfg (voterBlocks p st (s + 1)) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s Bfg _hi _hilen inv _ht hslabel hki hk hJ hQB hord st
  have hy := hvalid.honest_only _ (List.mem_of_getElem? hk)
  have hsch := hvalid.toScheduleWellFormed
  have hafter : iStar ≤ k := by
    by_contra hn
    have hlt : k < afterTicksIdx rho (SA.gateTime p.toParams w.u) :=
      hs.cut ▸ (Nat.lt_of_not_ge hn)
    have hm : V2.Event.tick y (SA.voteTime p.toParams (s + 1)) ∈
        rho.events.filter (cutPred (SA.gateTime p.toParams w.u)) := by
      rw [V2.D.Engine.filter_eq_take hsch _ (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := k)
      change (rho.events.take (afterTicksIdx rho (SA.gateTime p.toParams w.u)))[k]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact hk
    have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
    have ht : SA.voteTime p.toParams (s + 1) ≤ SA.gateTime p.toParams w.u := by
      rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
    have hc : (w.u : Int) + 1 ≤ s := by exact_mod_cast hslabel
    push_cast at ht
    nlinarith [p.deltaPos]
  have hstate : Block.Preceq (S_at p c E rho k y) (eraseFG Bfg) := by
    rcases (wcg_outputHistoryAt hs inv hafter (Nat.le_of_lt hki) hy).origin with
      h | ⟨j, z, r, C, hr, hSC⟩
    · exact block_preceq_trans h hQB
    · have ht : SA.gateTime p.toParams r ≤ SA.voteTime p.toParams (s + 1) := by
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hr.event
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
        have hh := (List.pairwise_iff_getElem.mp hsch.sorted) j k hjl hkl hr.completed
        rw [hje, hke] at hh
        exact V2.D.Engine.time_le_of_key_le _ _ hh
      have hrs : r < s := by
        change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
        push_cast at ht
        have hh : (r : Int) < s := by nlinarith [p.deltaPos]
        exact Int.ofNat_lt.mp hh
      exact block_preceq_trans hSC (hord j z r C
        { hr with completed := hr.completed.trans hki } hrs)
  have hhigh : WCUsableHighSourcesBelow p c E rho w k y st (eraseFG Bfg) := by
    refine ⟨hy, ?_⟩
    intro a _ha j z r wire e K hj hrow _hdecode hname hhigh hK
    by_cases hpre : j < iStar
    · obtain ⟨K', G, hK', _, _, _, _, hbelow⟩ :=
        hs.highSources j z r wire e hpre hrow hname hhigh
      have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
      exact block_preceq_trans (heq ▸ hbelow) hQB
    · obtain ⟨C, hr, hKC⟩ := inv.suffixSources j z r K (Nat.le_of_not_gt hpre)
        (hj.trans hki) hrow.1 hrow.2.1 hK
      have hbound := (hlabel k y z r wire _ hy hk ⟨j, hj, hrow⟩).2.2 (s + 1)
        (Nat.succ_le_succ (Nat.zero_le s)) (Or.inr rfl)
      have hrs : r * p.R < s := by
        simp only [Slot] at hbound hslabel ⊢
        omega
      exact block_preceq_trans hKC (hord j z (r * p.R) C hr hrs)
  obtain ⟨W, hW, hh, hmem⟩ := inv.carrier
  have hWst : W ∈ st.fg.TF := by
    change W ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hmem k y hafter (Nat.le_of_lt hki) hy
  have hd : WCDutyInput p c E rho k y (.head (s + 1)) st :=
    ⟨(List.getElem?_eq_some_iff.mp hk).1,
      fgsa_head_joined_of_joinedAt E rho hsch hk hJ, _, hk, Or.inr (Or.inl ⟨s + 1, rfl, rfl, rfl⟩)⟩
  have htarget : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Preceq row.1 (eraseFG Bfg) := by
    intro row hr _
    change row ∈ (FGSA.clock p _ _).base.obligations at hr
    rw [transfer_vote_clock] at hr
    exact block_preceq_trans (htargets k y row
      ((clockPre_obligations_sublist p _ _).subset hr)) hstate
  exact wcg_seededFrameLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs k y (.head (s + 1)) st W Bfg hd hy hafter
    hWst hW hh hQB hhigh htarget (voterBlocks p st (s + 1))
    ⟨Or.inl ⟨s + 1, rfl, rfl⟩⟩ (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1)

end AvailableChain.FGSA.Run
end
