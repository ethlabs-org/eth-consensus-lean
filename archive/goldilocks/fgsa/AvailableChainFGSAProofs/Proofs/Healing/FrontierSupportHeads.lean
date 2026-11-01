module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportFrame
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads

public section

/-! G-HG1 capped H.1/H.2 HEAD steps (plan fgsa-s5-frontier §3.1 steps 3–4; blueprint 21
HG.1:1536–1565). These restate `healing_support_honest_batch_seat`,
`healing_next_transfer_core` and `healing_first_transfer_core` (Healing/SupportHeads.lean,
Healing/SupportTransfer.lean) with the fixed-phase frame replaced by the capped
self-witness: each witness is an honest HEAD block above the height-m pivot. The lease
premise stays explicit at each step. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem fheads_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

omit [DecidableEq V] in
private theorem fheads_idxBefore_le_timeIdx (rho : V2.D.Run V (fgsa p c)) {t v : Time}
    (htv : t ≤ v) : V2.D.Run.idxBefore rho t ≤ timeIdx rho v := by
  change (rho.events.filter (fun e => decide (e.time < t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ v))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans htv))

private theorem fheads_kept_anchor (p : Params) (dst : State p.n)
    (hinv : CStoreInv p dst) (B : Block) (W : FGBlock (Fin p.n))
    (hW : W ∈ dst.fg.TF) (hBW : Block.Preceq B (eraseFG W))
    (X : Finset (FGBlock (Fin p.n)))
    (hfrozen : ∀ A, FGBlock.Preceq dst.fg.F A → FGBlock.Preceq A W → A ∈ X)
    (hlo : (controls p dst).lo ≤ (heightView p W).h)
    (hZW : FGBlock.Preceq (controls p dst).Z W)
    (hrows : ∀ row ∈ dst.base.obligations, Block.Compatible row.1 B) :
    (∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (domainR p dst X)) ∧ Block.Compatible (liveRoot p dst) B := by
  constructor
  · intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hW (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq dst.fg.F A := eraseFG_preceq_iff.mp
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (controls p dst).Z A := eraseFG_preceq_iff.mp
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (controls p dst) _ A).mpr
      ⟨hfrozen A hFA hAW, hFA, hZA, W,
        hfrozen W (KitFG.preceq_trans hFA hAW) (KitFG.preceq_refl W), hAW, hlo⟩
  · have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (controls p dst).Z)
    change liveRoot p dst = _ ∨ liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZW) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1529–1534, H.2 S1:709–715; plan §3.1 step 4 (restates
`healing_support_honest_batch_seat`). DC: INTENTIONAL under the cap, an honest label-i
HEAD that covers the pivot and B is, at the receiver's v_(i+1) read, a clean resolved
frozen vote that supports B. The HEAD block itself is the relayed witness. -/
theorem frontier_head_batch_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hScope : NextTransferScope E rho iy y i)
    (hCut : HealingWindow p E 1 i)
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head i)) k ∈ rho.honest)
    (hJoin : joinedAt p E rho (rho.seatOf (.base (.head i)) k) i
      (SA.voteTime p.toParams i)) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.blocks
      (FGSA.headSupport p (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))) (i + 1)) k B = true ∧
    GridCO.equivocates (FGSA.headVotes p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  let z := rho.seatOf (.base (.head i)) k
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hvh
  have hawake := hrec.awake z hk _ hgsti hhori
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk i hhori hawake
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
    (fgsa_head_joined_of_joinedAt E rho hS hjz hJoin)
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams i)) i
  have hBK : Block.Preceq B K := hcover z hk K hhl
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hvi.trans hv)
  -- The HEAD block itself is the witness; it reaches y before e_i (capped relay).
  obtain ⟨Kfg, hKz, hKe0, _, hrelay⟩ := frontier_head_relay_on
    (hroots := hrec.base.receiptIdealization)
    E rho crossing hE hQm hcap hk hjz (hcoverQ z hk K hhl) hcut
    hy (healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hy hiy hvi
      jz z hk hjz)
  have hKe' : eraseFG Kfg = K := hKe0
  have hfz : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hWf : Kfg ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams i) y).st.fg.TF := by
    have h := hrelay
    have hc := (fgsa_store_durable p c E rho
      (healing_phase_idxBefore_mono p c rho hfz) y).1 h
    change Kfg ∈ (V2.D.Run.stateBefore E rho _ y).st.fg.TF at hc
    rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hc
  have hpath := healing_support_prefreeze_path_on E rho hS hiy (hScope.epoch.mono
    (fgsa_idxBefore_mono rho hfz) le_rfl) hWf Kfg (KitFG.preceq_refl _)
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hKb : K ∈ dst.base.blocks := by
    rw [← hKe']
    exact (hinv.baseTree _).mpr ⟨Kfg, hpath.1, rfl⟩
  have hKst : GridCO.stampBlock dst.base K < SA.freezeTime p.toParams i := by
    rw [← hKe']
    exact hpath.2
  -- The HEAD block has slot at most i.
  have hKslot : K.slot ≤ i := by
    have hm := ((cstoreInv_stateBefore E rho jz z).baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKz, rfl⟩
    rw [hKe'] at hm
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hm
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hjz z
    rw [fgsa_clock_now p c (rho.stateBefore E jz z)] at hn
    have hsl := Internal.slotOf_mono (p := p) hn
    have he : p.slotOf (SA.voteTime p.toParams i) = i :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ i)
    exact hb.trans (hsl.trans_eq he)
  -- Fresh receipt reaches the freeze and keeps its strict stamp to the actual read.
  obtain ⟨hFresh⟩ := hScope.fresh k K.root hk hem
  obtain ⟨jem, hjEm, hoEm⟩ := hem
  have hem : V2.D.Run.emits E rho z (ofHead p ⟨.seat (.head i) k, K.root⟩)
      (SA.voteTime p.toParams i) := ⟨jem, hjEm, hoEm⟩
  obtain ⟨hom, hos⟩ := hFresh.receipt hE hy hjEm hoEm
  let o := baseVote (⟨.seat (.head i) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams i) ≤ iy := by
    apply healing_support_idxBefore_le p c E rho hS hiy
    change 4 * p.Δ * (i : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (SA.freezeTime p.toParams i)) y).base.votes := by
    change o ∈ (rho.stateBefore E _ y).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, hods⟩ := healing_support_vote_kept_on E rho hidx y
    (SA.voteTime p.toParams (i + 1)) (hScope.epoch.mono (fgsa_idxBefore_mono rho hfz) le_rfl) o hom'
  have hstampv : GridCO.stampVote dst.base o < SA.freezeTime p.toParams i := by
    change GridCO.stampVote (FGSA.clock p _ _).base o < _
    rw [hods]
    change GridCO.stampVote (rho.stateBefore E _ y).st.base o < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hos
  -- The receiver finality is below the height-m HEAD block (RXing under the cap).
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hjziy : jz ≤ iy := by
    have h1 : jz < V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr (lt_add_of_pos_right _ p.deltaPos)
    exact h1.le.trans (healing_support_idxBefore_le p c E rho hS hiy hvi)
  have hFK0 := frontier_F_below_all E rho crossing hy (hcap iy y hiyv hy) hk hjziy hKz
    (frontier_height_eq E rho hQm (hcap jz z (hjziy.trans hiyv) hk) hKz
      (hKe' ▸ hcoverQ z hk K hhl)).1.ge
  have hFK : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    rw [← hKe']
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (eraseFG_preceq hFK0)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK⟩) hoK
  -- The vote is in the frozen support arm and supports B.
  have hsupp : o ∈ FGSA.headSupport p dst (i + 1) := by
    change o ∈ List.eraseDups (_ ++ _)
    rw [List.mem_eraseDups, List.mem_append]
    left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hod, ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some i)
    · unfold GridCO.resolvedBefore
      rw [hresolve]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel,
        hol, Option.getD_some]
      exact ⟨⟨hKslot, hstampv⟩, hKst⟩
  have hvs : Gen.AC.Root.voteSupports dst.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-i vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho iy y).base i,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE iy y i k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hnoeq : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = false := by
    cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
      exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne
  cases he : GridCO.equivocates (FGSA.headVotes p dst (i + 1)) k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    have hprov := fgsa_headVotes_provenance_on_receipt E rho hE i iy y hy hScope.reads
    have hone : ∀ w ∈ FGSA.headVotes p dst (i + 1), GridCO.headSeat? w = some k → w = o := by
      intro w hw hwk
      rcases hprov w hw k hwk with hm | heq
      · exact hall w hm hwk
      · change GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = true at heq
        rw [hnoeq] at heq
        contradiction
    exact hne ((hone a ha hka).trans (hone b hb hkb).symm)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1536–1546, H.2 S1:709–715, H.3:748–783; plan §3.1 steps 3–4
(restates
`healing_next_transfer_core`). DC: INTENTIONAL one capped H.2 HEAD step. If every honest
label-i HEAD covers the pivot and B, every honest HEAD at label i+1 under the cap covers B.
The receiver's own label-i HEAD block is the witness; it has height m, so F and Z are below
it and the floor is at most m at either frame. `hlease` is the lease premise at this read. -/
theorem frontier_next_transfer_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hScope : NextTransferScope E rho iy y i)
    (hCut : HealingWindow p E 1 i)
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hvh
  -- The receiver's own label-i HEAD block is the witness (capped self-witness).
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hS hDelta hy i hhori
    (hrec.awake y hy _ hgsti hhori)
  have hhl : headAtLabel p c E rho y i = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jy y).st (SA.voteTime p.toParams i)) i) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjy]
    rfl
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hvi.trans hv)
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay_on (hroots := hrec.base.receiptIdealization)
    E rho crossing hE hQm hcap hy hjy (hcoverQ y hy _ hhl) hcut
    hy (healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hy hiy hvi
      jy y hy hjy)
  have hWd := hrelay
  have hBW : Block.Preceq B (eraseFG W) := by
    rw [hWe]
    exact hcover y hy _ hhl
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := by
    rw [hWe]
    exact hcoverQ y hy _ hhl
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_durable p c E rho
      (healing_support_idxBefore_le p c E rho hS hiy hvi) y).1 hWd
  obtain ⟨_, hFW, hZW, hloy⟩ := frontier_self_witness E rho crossing hQm hy
    (hcap iy y hiyv hy) hWy hQW
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := by
    rw [hdfg]
    exact hWy
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hFW
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos i)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path through the frozen v_(i+1) domain.
  have hread : postClock E rho y (SA.voteTime p.toParams (i + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (i + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams i + p.Δ := by
    change 0 < 4 * p.Δ * (i : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams (i + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path_on p c E rho hS hdpos hvi hdfreeze hWd hread (by
    intro j hj
    have he : j = iy := Option.some.inj
      ((fgsa_tickIdx_of_event p c E rho hS hj).symm.trans
        (fgsa_tickIdx_of_event p c E rho hS hiy))
    exact he.symm ▸ hScope.epoch)
  let X := voterBlocks p dst (i + 1)
  have kept := fheads_kept_anchor p dst hinv B W hWdst hBW X hfrozen
    (hRd ▸ hloy) (hRd ▸ hZW) (hlease hFB0)
  have hkeep := kept.1
  have hanchor := kept.2
  -- The honest batch of label i.
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho i
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := frontier_head_batch_seat E rho hrec crossing hQm
    hvh hcap hgsti hcoverQ hcover hy hiy hScope hCut hv k
    ((healingJoinedSeats_mem E rho i k).mp hk).1
    ((healingJoinedSeats_mem E rho i k).mp hk).2
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := hScope.batch
  have hother : ((GridCO.seats p.n (FGSA.headVotes p dst (i + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := hScope.rivals
  have hcov := batch_head_covers p dst X (FGSA.headVotes p dst (i + 1))
    (FGSA.headSupport p dst (i + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card B
    (fgsa_headSupport_subset_headVotes E rho hE iy y i) rfl
    (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb hanchor hkeep
  rw [fgsa_domainR_eq_filtered] at hcov
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero i)]
  exact hcov

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1546–1556, H.1:673–699, H.3:748–783; plan §3.1 steps 3–4
(restates
`healing_first_transfer_core`). DC: INTENTIONAL the capped first transfer at v_(s+1). One
honest clean supporter of B at the gate d_s has a label-s HEAD above the pivot. That HEAD
block has height m and is the witness: it reaches the receiver before e_s, and F and Z are
below it at the receiver's frame. The transfer counts are those of H.1. `hlease` is the
lease premise of H.1 (release for a fast body, the window for a slow body). -/
theorem frontier_first_transfer_core (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho) (_hDelta : E.Δ = p.Δ)
    {ΔF : Time} (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (_hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (_hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (_hgate : SA.gateTime p.toParams s ≤ v)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
      Block.Preceq (eraseFG Qfg) K)
    {ix : Nat} {x : V} (hx : x ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    {B : Block} {k : Fin p.n} {o : GridCO.Wire p.n .root}
    (hkh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
    (hko : GridCO.headSeat? o = some k)
    (hsup : Gen.AC.Root.voteSupports
      (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho ix x)
        (SA.gateTime p.toParams s)))) B o = true)
    (hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) <
      2 * GridCO.goldfishScore
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))).blocks
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) B)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hScope : FirstTransferScope E rho ix iy x y s)
    (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1)) := by
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  -- The honest supporter and its HEAD block, the capped witness.
  obtain ⟨K, hK, hKm, _, _, hom, hol⟩ := healing_support_clean_target E rho o ho
  have hBK : Block.Preceq B K := by
    rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hK] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  obtain ⟨jz, hjz, hKz, hSourceJoin⟩ := healing_support_honest_head_joined E rho hE hom hol hko hkh
  have hKeq := stored_eq_headVote E rho (hroots.toNamedRootCollisionFree E rho) ix x hKm jz
    (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) s
    (Option.some.inj ((resolvedHead_root _ o hK).symm.trans hKz))
  have hhlz : headAtLabel p c E rho (rho.seatOf (.base (.head s)) k) s =
      some (headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz
        (rho.seatOf (.base (.head s)) k)).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hvs : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hes : SA.voteTime p.toParams s + p.Δ ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hes.trans hv)
  have hQK := hcoverQ _ hkh _ hhlz
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay_on (hroots := hroots) E rho crossing hE hQm
    hcap hkh hjz hQK hcut hy (hScope.carriersOn hE hy hiy _hgsts
      jz _ hkh hjz hSourceJoin)
  have hKe2 : eraseFG W = K := hWe.trans hKeq.symm
  have hBW : Block.Preceq B (eraseFG W) := by
    rw [hKe2]
    exact hBK
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := by
    rw [hWe]
    exact hQK
  have hWd := hrelay
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_durable p c E rho
      (healing_support_idxBefore_le p c E rho hS hiy hes) y).1 hWd
  obtain ⟨_, hFWy, hZWy, hloy⟩ := frontier_self_witness E rho crossing hQm hy
    (hcap iy y hiyv hy) hWy hQW
  have hZFy : FGBlock.Preceq (R_at p c E rho iy y).Z W ∧
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F W := ⟨hZWy, hFWy⟩
  -- The receiver HEAD.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := hdfg ▸ hWy
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hZFy.2
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos s)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path: W and its ancestors are in the frozen v_(s+1) domain.
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams s + p.Δ := by
    change 0 < 4 * p.Δ * (s : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams s + p.Δ ≤ SA.freezeTime p.toParams (s + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path_on p c E rho hS hdpos hes hdfreeze hWd hread (by
    intro j hj
    have he : j = iy := Option.some.inj
      ((fgsa_tickIdx_of_event p c E rho hS hj).symm.trans
        (fgsa_tickIdx_of_event p c E rho hS hiy))
    have hed : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
      ring
    simpa only [he, hed] using hScope.epoch)
  have kept := fheads_kept_anchor p dst hinv B W hWdst hBW
    (voterBlocks p dst (s + 1)) hfrozen (hRd ▸ hloy) (hRd ▸ hZFy.1) (hlease hFB0)
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (filteredFrom p.E p.cfg (FGSA.controls p dst)
        (voterBlocks p dst (s + 1))) := by
    simpa only [fgsa_domainR_eq_filtered] using kept.1
  have hanchor := kept.2
  -- Majority and rival dominance at the receiver (forward and reverse relay).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq B K' := by
      have hlookup : Gen.AC.Root.resolvedTarget? src.blocks o' = some K' :=
        actView_target_of_resolvedHead p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _) o' hK'
      rw [Gen.AC.Root.voteSupports_def, hlookup] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path_on (hroots := hroots)
      E rho hS hy hiy (hScope.epoch.mono (fgsa_idxBefore_mono rho (by
        change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
        linarith)) le_rfl) K'
      (hScope.targets K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB0 hBK'))
    exact fgsa_cleanSupport_forward_relay_on_receipt E rho hE s hx hy hix hiy o' ho'
      seat hs' (fun b he => hScope.forward seat b (he ▸ ho')) Kfg' (hKe' ▸ hK') B
      (hKe' ▸ hBK') hpath' hFB
  have hc := Gen.AC.Root.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) B
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay_on_receipt E rho hE s ix iy x y hx
      (fun q b hb => hScope.backward q b (Or.inr hb)))
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.Root.TransferBounds_def] at hc
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
  exact fgsa_headInTree_covers_of_transfer p dst _ _ _ B
    hanchor hpath hc.2.2.2.2.2.1 hc.2.2.2.2.2.2

end AvailableChain.FGSA.Run
end
