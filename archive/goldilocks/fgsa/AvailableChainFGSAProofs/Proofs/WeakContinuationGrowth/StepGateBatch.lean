module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.AnchorCoverage
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepInputs

public section

/-! WC plan §6.5; DC the honest batch retains its original receipt deadlines. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

omit [DecidableEq V] in
private theorem wcg_joinedHonest_mem (x : V) (t : Time) :
    x ∈ joinedHonest p E rho t ↔ x ∈ rho.honest ∧ joinedAt p E rho x (slotAt p t) t := by
  classical
  change x ∈ rho.honest.filter _ ↔ _
  exact Finset.mem_filter

/-- WC plan §6.5; DC cumulative stamps retain their first receipt. -/
private theorem stamp_find_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨⟨b, t⟩, ht, hb⟩ := List.mem_map.mp hm
    dsimp only at hb
    subst b
    have hn := List.find?_eq_none.mp hf (a, t) ht
    simp only [beq_self_eq_true] at hn
    exact (hn trivial).elim
  | some row => rfl


/-- WC plan §6.5; DC gate inputs retain the original stored stamps. -/
private theorem gate_stamps (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
    {j i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hRF : V2.D.restartFree rho x j i) (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (o : GridCO.Wire p.n .root) (B : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v B = GridCO.stampBlock (storeAt p c E rho j x).base B := by
  intro v
  have hc := hcumul.2 j i x hx hji hi hRF
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : B ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  have hev := stamp_find_kept hc.2 o hv
  have heb := stamp_find_kept hc.1 B hb
  refine ⟨?_, ?_, ?_⟩
  · change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
    rw [← fgsa_vote_stamp_keys E rho i x]
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨row, hc.2.subset hr, he⟩
  · change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).2, hev]
    unfold GridCO.stampVote
    cases he : (storeAt p c E rho j x).base.voteStamp.find? (fun row => row.1 == o) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hv
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  · change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1, heb]
    unfold GridCO.stampBlock
    cases he : (storeAt p c E rho j x).base.blockStamp.find? (fun row => row.1 == B) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hb
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
/-- WC plan §6.5; DC an awake honest HEAD and its path arrive before the early tick. -/
private theorem gate_active_heads
    (hvalid : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho) (hdelta : E.Δ = p.Δ)
    (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho) {i : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho i x s) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s))
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      Block.Preceq B (headAtIdx p c E rho k s)) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s
        (SA.voteTime p.toParams s) →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have ht := hG.1
  intro q hy hJ
  have hawake := hJ.1
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hvalid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have hcut := (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have htimes : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ <
      4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    rw [← htimes]
    exact lt_add_of_pos_right _ hd
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * s + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans hcut))) (hvt ▸ hawake)
  rw [hvt] at hk
  let K := headAtIdx p c E rho k s
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams s)).st s := by
    change headAtIdx p c E rho k s = _
    unfold headAtIdx
    rw [hk]
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr
      ⟨hawake, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hsch hk hJ, congrArg Block.root hKeq⟩
  have hprefix := hfinal k y hk hJ
  obtain ⟨required, paths, hcov, hp⟩ :=
    wcg_gate_path_coverage hvalid hR hdelta hsync hGST hG hcut hy hk hKsource hprefix
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hFearly : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix _ hidx
  have hpath := fgsa_active_path_of_coverage_anchor (hroots := hroots)
    E rho hvalid hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.earlyTime p.toParams s) 0 x K required paths
    (fun _ _ => SA.voteTime p.toParams s) hx hcov hp hFearly
  let j := V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hm
    exact hm.1
  have hr := wcg_gate_head_receipt hvalid hR hdelta hsync hGST hx hG hcut q K.root hy hem
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hr
  have hRF := wcg_gate_read_epoch hvalid hG
    (D := SA.earlyTime p.toParams s) (by
      change 4 * p.Δ * ((s : Nat) : Int) <
        4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
      linarith)
  have htrans := gate_stamps hcumul hx hRF (s := s) hidx hil _ K hr.1 hKearly
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(hcumul.1 j i x hx hidx hil).2.1.subset hKearly,
      block_compatible_of_common (block_preceq_refl K) (hprefix i le_rfl)⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := fgsa_preTick_now_le E rho hsch hk
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams s, hy, hem, htrans.1, hKg, hslot,
    ?_, ?_, ?_, hB k y hk hJ⟩
  · rw [htrans.2.1]
    exact hr.2
  · rw [htrans.2.2]
    have hm : K ∈ (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base.blocks := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
      exact hKearly
    have hb := fgsa_block_stamp_before_read E rho hsch x _ hpos K hm
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hb
    exact hb
  · rw [clockPre_fg]
    exact hprefix i le_rfl

/-- WC plan §6.5; DC the actual awake batch gives both anchor and target majorities. -/
theorem wcg_gateBatch [Fintype V]
    (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
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
    WCInv p c E rho w iStar i → enabledGateAt p c E rho i x s → w.u < s → ∀ B,
    (∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      Block.Preceq B (headAtIdx p c E rho k s)) →
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  classical
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv hG hslabel B hB
  have ht := hG.1
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hcut : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hc : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hhead := wcg_gateHeads ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hF := wcg_gateFinalOrigin hcausal ΔF w iStar hvalid hlinked hcstar hnr hdelta
    hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s) := by
    intro k y hk hJ j hji
    have hh := hhead k y (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk hJ
    apply block_preceq_trans (eraseFG_preceq (hmono j i x hx hji).1)
    rcases hF with hF | ⟨l, z, r, C, hr, hrs, hFC⟩
    · exact block_preceq_trans hF hh.1
    · exact block_preceq_trans hFC (hh.2 l z r C hr hrs)
  let A := joinedHonest p E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (hcstar (.base (.head s)) trivial)
  let H := A.image e.symm
  have hH : ∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s) := by
    intro k
    have he : k ∈ H ↔ e k ∈ A := by
      change k ∈ A.image e.symm ↔ e k ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hk => ⟨e k, hk, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) k ∈
      joinedHonest p E rho (SA.voteTime p.toParams s) ↔ _
    have hslot : slotAt p (SA.voteTime p.toParams s) = s := by
      exact slotOf_offset p s p.Δ p.deltaPos.le (by linarith [p.deltaPos])
    rw [wcg_joinedHonest_mem, hslot]
  have hv : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans (b := SA.gateTime p.toParams s) _ hcut
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hcard : H.card = A.card := Finset.card_image_of_injective A e.symm.injective
  have hb : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card :=
    ⟨hcard ▸ hpart _ (by
      have hh : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr
        (Nat.succ_le_of_lt hslabel)
      change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
        4 * p.Δ * (s : Int) + p.Δ
      nlinarith [p.deltaPos]) hv⟩
  apply fgsa_gate_batch_premises_joined E rho hvalid hcstar i x s B H hb
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩)
  intro k hk
  exact gate_active_heads hvalid hnr hdelta hcstar hroots hsync hcumul hG hGST hfinal B hB
    k ((hH k).mp hk).1 ((hH k).mp hk).2

end AvailableChain.FGSA.Run
end
