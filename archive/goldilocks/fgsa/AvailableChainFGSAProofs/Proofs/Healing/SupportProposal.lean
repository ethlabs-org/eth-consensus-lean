module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportOutput
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist

public section

/-! H-SUPPORT S1 proposal clause (plan §4 step 7: "at a proposal i ≥ s+2, use the previous
common batch and the full-tree path"). The private decoder restates the private
`frame_proposal_read` of Healing/Frame.lean, which this lane may not edit. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Joined fresh HEADs and per-carrier services at one proposal read. -/
structure ProposalSupportScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ip : Nat) (x : V)
    (r : Slot) (t : Time) : Prop where
  batch : ∀ [Fintype V], Gen.Pure.Batch (healingJoinedSeats E rho r).card
    (Gen.V2.Duty.faulty rho).card
  rivals : ∀ [Fintype V], ((GridCO.seats p.n
    (proposerVotes (clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1))).toFinset
        \ healingJoinedSeats E rho r).card ≤ (Gen.V2.Duty.faulty rho).card
  lateRivals : ∀ [Fintype V], ((GridCO.seats p.n
    (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ip x)
        (SA.gateTime p.toParams r))) r)).toFinset
        \ healingJoinedSeats E rho r).card ≤ (Gen.V2.Duty.faulty rho).card
  epoch : V2.D.restartFree rho x
    (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r)) ip
  fresh : ∀ q K, rho.seatOf (.base (.head r)) q ∈ rho.honest →
    V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
      (ofHead p ⟨.seat (.head r) q, K⟩) (SA.voteTime p.toParams r) →
    Nonempty (FreshHeadService E rho r q K (SA.earlyTime p.toParams r) x)
  carriers : HealingCarriersAt E rho r ip x t

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The honest proposal's parent is the proposer head at the proposer's post-clock read. -/
private theorem proposal_read (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ j, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      Q.parent = proposerHead p (FGSA.clock p
        (storeAt p c E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)) s := by
  obtain ⟨_, o, ⟨j, hj, hem⟩, hb⟩ := hp
  rw [proposalTime_fgsa p c s] at hj
  refine ⟨j, hj, ?_⟩
  obtain ⟨auth, m⟩ := o
  cases m with
  | head _ => cases hb
  | row _ => cases hb
  | proposal N =>
    have he : N.erase = Q := Option.some.inj hb
    subst Q
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    change (⟨auth, .proposal N⟩ : Obj p) ∈
      (if E.awake _ (SA.proposalTime p.toParams s) then
        (duties p (SA.proposalTime p.toParams s)).flatMap (fun d =>
          (rho.ownSeats (RunDuty.signLabel d) _).filterMap (fun i =>
            (act p c ((fgsa p c).clock _ _) d (rho.input _ _)).map
              (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
                ([] : List (Obj p)) else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, hd, hem⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
      obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
      have he : m = .proposal N := congrArg V2.Signed.payload ho
      subst m
      cases d with
      | headAction _ =>
        change (if joinedNow p _ then some (Msg.head _) else none) = some (Msg.proposal N) at hm
        split at hm <;> cases hm
      | fgAction _ =>
        change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
        obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hm
        cases he
      | propAction s' =>
        have ht := (duties_spec p _ _).mp hd
        have hss : s' = s := by
          change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
          have hΔ := p.deltaPos
          have he : (s' : Int) = s := by nlinarith
          exact_mod_cast he
        subst s'
        change (if joinedNow p _ then
          (propose p _ s).map (withApp p _) else none) = some (.proposal N) at hm
        split at hm
        · exact (fgsa_walkRun_proposal_parent p _ s _ N hm).2.2
        · cases hm
    · exact (List.not_mem_nil hem).elim

private theorem proposal_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S2), 1240–1243 (proposer pools); plan H-SUPPORT §4
step 7.
DC: INTENTIONAL an honest label-r HEAD that covers B is, at the proposer's slot-(r+1)
read, a resolved non-equivocating proposer-support vote that supports B: the vote arrives
by e_r, and the HEAD block arrives through its HEAD witness W (F1 + F2). -/
theorem healing_proposal_batch_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (_mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams r)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq B K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hScope : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)))
    (hCut : HealingWindow p E 1 r)
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head r)) k ∈ rho.honest)
    (hJoin : joinedAt p E rho (rho.seatOf (.base (.head r)) k) r
      (SA.voteTime p.toParams r)) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))).base.blocks
      (FGSA.proposerSupport (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))) (r + 1)) k B = true ∧
    GridCO.equivocates (FGSA.proposerVotes (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let st := FGSA.clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  let z := rho.seatOf (.base (.head r)) k
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hgstr : E.t_GST ≤ SA.voteTime p.toParams r := hgst.trans hhead
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvv.trans hphase.2.1
  have hawake := hrec.awake z hk _ hgstr hhorr
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk r hhorr hawake
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
    (fgsa_head_joined_of_joinedAt E rho hS hjz hJoin)
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams r)) r
  have hBK : Block.Preceq B K := hcover z hk K hhl
  -- The HEAD block reaches the proposer through its witness before e_r.
  obtain ⟨Kfg, hKfull, hKe, W, _, hKW, _, hrelay⟩ :=
    healing_head_witness_relay_on (hroots := hrec.base.receiptIdealization)
      p c E rho crossing hE hk hjz hx
      ((healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hx hip hvp jz z hk hjz).relay
        (healing_head_carrier_demand_phase p c E rho crossing hE hphase
          hk hjz hhead (hvp.trans hv) hx))
  have hKe' : eraseFG Kfg = K := hKe
  have hKx : Kfg ∈ (storeAt p c E rho ip x).fg.TF := by
    have h := hrelay Kfg hKW
    have hW : Kfg ∈ (storeAt p c E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ)) x).fg.TF := by
      change Kfg ∈ (V2.D.Run.stateBefore E rho _ x).st.fg.TF
      rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
      exact h
    exact (fgsa_store_durable p c E rho
      (healing_support_idxBefore_le p c E rho hS hip hvp) x).1 hW
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hKb : K ∈ st.base.blocks := by
    rw [← hKe']
    refine (hinv.baseTree _).mpr ⟨Kfg, ?_, rfl⟩
    change Kfg ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hKx
  have hKslot : K.slot ≤ r := by
    have hzinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz z) (SA.voteTime p.toParams r)
    have hKT := ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).1
    have hm := (hzinv.baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKT, rfl⟩
    rw [clock_base_blocks, hKe'] at hm
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hm
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hjz z
    rw [fgsa_clock_now p c (rho.stateBefore E jz z)] at hn
    have hsl := Internal.slotOf_mono (p := p) hn
    have he : p.slotOf (SA.voteTime p.toParams r) = r :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ r)
    exact hb.trans (hsl.trans_eq he)
  -- Fresh HEAD service reaches earlyTime; its receiver epoch keeps the vote.
  obtain ⟨hFresh⟩ := hScope.fresh k K.root hk hem
  obtain ⟨jem, hjEm, hoEm⟩ := hem
  have hem : V2.D.Run.emits E rho z (ofHead p ⟨.seat (.head r) k, K.root⟩)
      (SA.voteTime p.toParams r) := ⟨jem, hjEm, hoEm⟩
  obtain ⟨hom, _⟩ := hFresh.receipt hE hx hjEm hoEm
  let o := baseVote (⟨.seat (.head r) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams r) ≤ ip := by
    apply healing_support_idxBefore_le p c E rho hS hip
    change 4 * p.Δ * (r : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (SA.earlyTime p.toParams r)) x).base.votes := by
    change o ∈ (rho.stateBefore E _ x).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, _⟩ := healing_support_vote_kept_on E rho hidx x
    (SA.proposalTime p.toParams (r + 1)) hScope.epoch o hom'
  have hFK : Block.Compatible K (eraseFG st.fg.F) := by
    change Block.Compatible K (eraseFG (FGSA.clock p _ _).fg.F)
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hol : GridCO.headLabel? o = some r := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p st hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x)))
    o ((actView_blocks st K).mpr ⟨hKb, hFK⟩) hoK
  have hvotes : o ∈ FGSA.proposerVotes st (r + 1) := by
    change o ∈ GridCO.votesAt st.base (r + 1 - 1)
    exact List.mem_filter.mpr ⟨hod, by
      simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some r)⟩
  have hsupp : o ∈ FGSA.proposerSupport st (r + 1) := by
    apply List.mem_filter.mpr
    refine ⟨hvotes, ?_⟩
    change (match GridCO.resolvedHead? (actView st) o with
      | some C => Block.preceq (eraseFG st.fg.F) C &&
        decide (C.slot ≤ r + 1 - 1) | none => false) = true
    rw [hresolve]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, decide_eq_true (by simpa only [Nat.add_sub_cancel] using hKslot)⟩
    change Block.Preceq (eraseFG (FGSA.clock p _ _).fg.F) K
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans hFB hBK
  have hvs : Gen.AC.Root.voteSupports st.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p _ hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-r vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho ip x).base r,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE ip x r k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hvat : FGSA.proposerVotes st (r + 1) = GridCO.votesAt (storeAt p c E rho ip x).base r := by
    change GridCO.votesAt st.base (r + 1 - 1) = _
    rw [Nat.add_sub_cancel]
    unfold GridCO.votesAt
    rw [(clock_vn (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))).1]
  rw [hvat]
  cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho ip x).base r) k with
  | false => rfl
  | true =>
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S2); plan H-SUPPORT §4 step 7.
DC: INTENTIONAL one proposal step. If every honest label-r HEAD covers B, the honest
proposer head at slot r+1 inside the phase covers B. The honest batch of label r gives
majority and rival bounds (`batch_head_covers` on the full tree); a witness W of the
proposer's own label-r HEAD gives the full-tree path and the frame; `hlease` is the
lease premise at this read. -/
theorem healing_proposal_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams r)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq B K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hScope : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)))
    (hCut : HealingWindow p E 1 r)
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B →
      ∀ row ∈ (storeAt p c E rho ip x).base.obligations, Block.Compatible row.1 B) :
    Block.Preceq B (proposerHead p (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let st := FGSA.clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hgstr : E.t_GST ≤ SA.voteTime p.toParams r := hgst.trans hhead
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvv.trans hphase.2.1
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hdfg : st.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  have hRd : FGSA.controls p st = R_at p c E rho ip x := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho ip x).fg
    rw [hdfg]
  -- The frame witness of the proposer's own label-r HEAD.
  obtain ⟨jx, hjx⟩ := healing_support_vote_tick E rho hS hDelta hx r hhorr
    (hrec.awake x hx _ hgstr hhorr)
  have hhl : headAtLabel p c E rho x r = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jx x).st (SA.voteTime p.toParams r)) r) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjx]
    rfl
  obtain ⟨W, hW, hBW, hZW, hFW, hloW⟩ := healing_support_frame_at
    (hroots := hrec.base.receiptIdealization)
    E rho (fun _ => mono) crossing hE
    hDelta hrec.sync hgst hphase hhead (hvp.trans hv) hx hjx
    x (healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hx hip hvp
      jx x hx hjx) (hcover x hx _ hhl) hx
    (healing_support_idxBefore_le p c E rho hS hip hvp)
    (healing_support_idxBefore_le p c E rho hS hip
      (hhead.trans ((le_add_of_nonneg_right hd.le).trans hvp)))
    (healing_phase_lt_timeIdx p c E rho hS hip hv).le
  have hWst : W ∈ st.fg.TF := hdfg ▸ hW
  have hFW' : Block.Preceq (eraseFG st.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hFW
  have hhead_eq : proposerHead p st (r + 1) = headInTree p st
      (erasedList st (domainR p st st.fg.TF)) (FGSA.proposerVotes st (r + 1))
      (FGSA.proposerSupport st (r + 1)) := by
    rw [fgsa_domainR_eq_treeStoreFrameView]
    rfl
  rw [hhead_eq]
  rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with hFB | hBF
  swap
  · exact Gen.Pure.block_preceq_trans hBF (F_preceq_headInTree p st hinv _ _ _)
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B := hdfg ▸ hFB
  -- The full-tree path to B.
  have hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (domainR p st st.fg.TF) := by
    intro C hr hCB
    have hr' : liveRoot p st ≠ C ∧ Block.Preceq (liveRoot p st) C := by
      change ((!decide (liveRoot p st = C)) && Block.preceq (liveRoot p st) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hWst (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq st.fg.F A := proposal_lift
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p st hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p st).Z A := proposal_lift
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p st) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) _ A).mpr
      ⟨hA, hFA, hZA, W, hWst, hAW, hRd ▸ hloW⟩
  -- The live root is compatible with B.
  have hanchor : Block.Compatible (liveRoot p st) B := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (st.base.obligations.filterMap (fun row =>
        if st.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p st, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p st).Z)
    change FGSA.liveRoot p st = _ ∨ FGSA.liveRoot p st ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq (hRd ▸ hZW)) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        refine hlease hFB0 row (healing_lease_clock_nongate _ _ ?_ row hr)
        intro w hw
        have h : (4 * ((r + 1 : Nat) : Int)) * p.Δ = (4 * (w : Int) + 6) * p.Δ := by
          change 4 * p.Δ * ((r + 1 : Nat) : Int) = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
          linarith
        have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h
        push_cast at h2
        omega
      · contradiction
  -- The selected joined batch at this read.
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho r
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := healing_proposal_batch_seat E rho hrec mono
    crossing hgst hphase hhead hcover hx hip hScope hCut hv hFB0 k
    ((healingJoinedSeats_mem E rho r k).mp hk).1
    ((healingJoinedSeats_mem E rho r k).mp hk).2
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := hScope.batch
  have hother : ((GridCO.seats p.n (FGSA.proposerVotes st (r + 1))).toFinset
      \ Hon).card ≤ (Gen.V2.Duty.faulty rho).card := hScope.rivals
  exact batch_head_covers p st st.fg.TF (FGSA.proposerVotes st (r + 1))
    (FGSA.proposerSupport st (r + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card B
    (fun _ ho => (List.mem_filter.mp ho).1) rfl (fun k hk => (hseat k hk).2)
    (fun k hk => (hseat k hk).1)
    hother hb hanchor hkeep

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2 S2); plan H-SUPPORT §4 step 7.
DC: INTENTIONAL the S1 proposal clause of Transfers from the HEAD clause and the lease
invariant at the honest proposal reads. -/
theorem healing_proposals_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hCut : HealingWindow p E 1 s)
    (hheads : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    (hScopes : ∀ r, s + 1 ≤ r → SA.proposalTime p.toParams (r + 1) ≤ v →
      ∀ ip x, x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
      joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) →
      ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)))
    (hlease : ∀ i, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
      ∀ ip x, x ∈ rho.honest → rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams i)) →
      Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B →
      ∀ row ∈ (storeAt p c E rho ip x).base.obligations, Block.Compatible row.1 B) :
    ∀ i Q, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
      HonestProposal E rho (fgsaInterface p c) i Q → Block.Preceq B Q.parent := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  intro i Q hi hv hp
  have hxh := hp.1.2
  obtain ⟨ip, hip, hpar⟩ := proposal_read (c := c) E rho hp
  rw [hpar]
  have hiI : (s : Int) + 2 ≤ (i : Int) := by exact_mod_cast hi
  have hpos : 0 < i := by exact_mod_cast (show (0 : Int) < (i : Int) by omega)
  obtain ⟨r, rfl⟩ : ∃ r : Slot, i = r + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hrI : (s : Int) + 1 ≤ (r : Int) := by push_cast at hiI; omega
  have hvr : SA.voteTime p.toParams r ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hsr : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams r := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  exact healing_proposal_core E rho hrec mono crossing hgst hphase (hhead.trans hsr)
    (hheads r (by exact_mod_cast hrI) (hvr.trans hv)) hxh hip
    (hScopes r (by exact_mod_cast hrI) hv ip _ hxh hip
      (healing_recovery_joined_next E rho hrec
        (hCut.cut_mono (by exact_mod_cast (show (s : Int) ≤ r from by omega))) hxh hvr
        (hv.trans hphase.2.1)))
    (hCut.cut_mono (by exact_mod_cast (show (s : Int) ≤ r from by omega))) hv
    (hlease (r + 1) hi hv ip _ hxh hip)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–715 (H.1 + H.2 S2, fast arm); plan H-SUPPORT §4 steps 1–7.
DC: INTENTIONAL the S1 proposal clause of Transfers for a fast PhaseBody arm. -/
theorem healing_fast_proposals [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hFast : FastSupportScope E rho s v x)
    (hCut : HealingWindow p E 1 s)
    (hScopes : ∀ r, s + 1 ≤ r → SA.proposalTime p.toParams (r + 1) ≤ v →
      ∀ ip x, x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
      joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) →
      ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1))) :
    ∀ i Q, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
      HonestProposal E rho (fgsaInterface p c) i Q → Block.Preceq B Q.parent := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hheads := healing_fast_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx
    hnd hB hFast hCut
  refine healing_proposals_cover E rho hrec mono crossing hgst hphase hhead hCut hheads hScopes ?_
  intro i hi hv ip y hy hip hFB
  have hiI : (s : Int) + 2 ≤ (i : Int) := by exact_mod_cast hi
  have hq : SA.voteTime p.toParams (s + 1) < SA.proposalTime p.toParams i := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (i : Int)
    push_cast
    nlinarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1)
    ((hq.le.trans hv).trans hphase.2.1) (hrec.awake y hy _ (by
      refine (hgst.trans hhead).trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith) ((hq.le.trans hv).trans hphase.2.1))
  have hqa : iq < ip := by
    rcases lt_trichotomy iq ip with h | h | h
    · exact h
    · subst h
      have he := Option.some.inj (hiq.symm.trans hip)
      injection he with _ ht
      exact absurd ht (ne_of_lt hq)
    · exact absurd (fgsa_tick_time_strict E rho hS hip hiq h) (not_lt.mpr hq.le)
  refine healing_fast_lease_at E rho hrec mono writes (hgst.trans hhead)
    (hgate.trans hphase.2.1) hx hnd hB hphase.2.1 hFast
    (healing_gate_cut_of_batch_cut E s hCut.2) ?_ hy hiq hqa ?_ hFB
  · intro w hw hwT
    refine hheads w hw (le_trans ?_ hwT)
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  · intro j' t hj' ht'
    exact ((fgsa_tick_time_strict E rho hS ht' hip hj').le).trans hv

end AvailableChain.FGSA.Run
end
