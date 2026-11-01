module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLoss
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads

public section

/-! H-DESCENT D2 (H.13): the continuation transfer at labels l ≥ sB + 2 in the
moving frame. The H.2 receipt and count of `healing_support_honest_batch_seat`
and `healing_next_transfer_core` with a per-vote relay of each honest HEAD
block (label-local synchrony on [v_i, v_(i+1)]) instead of the PhaseInterval
witness relay, and with the kept path from a domain witness of the HEAD view. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem next_idx_mono : Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

omit [DecidableEq V] in
private theorem next_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, o = ofWire p ⟨.proposer u, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i u N
    refine ⟨u, N, ?_, h⟩
    apply toWire_injective (p := p)
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd


omit [DecidableEq V] in
private theorem next_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–689, 709–715 (H.2 relay of each honest HEAD); plan
fgsa-s5-m5-d2d4 B `cause` (H.2 re-proved without PhaseInterval).
DC: INTENTIONAL per-block relay with label-local synchrony on [v_s, v_(s+1)],
not TDel. A block stamped before e_s in an honest store reaches each honest
receiver of the v_(s+1) tick before z_s when the receiver's finality is below
it. The window ends at v_(s+1), so the receiver tick bounds the horizon (no
d_s cut). -/
theorem healing_block_receipt_sync (hS : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {y : V} (hy : y ∈ rho.honest) (K : Block)
    (hService : TargetReceiptService E rho K (SA.freezeTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ Y, eraseFG Y = K ∧
      Y ∈ (rho.stateBeforeTime E (SA.freezeTime p.toParams s) y).st.fg.TF := by
  have hb := fgsa_target_receipt_on E rho hS hroots K (SA.freezeTime p.toParams s) y hy hService
  obtain ⟨Y, hY, he⟩ := ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree K).mp hb
  exact ⟨Y, he, hY⟩

/-- A source target service and the exact receiver epoch give the frozen path. -/
theorem healing_block_path_sync (hS : V2.D.ScheduleWellFormed E rho)
    {iy : Nat} {y : V} {s : Slot} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hEpoch : V2.D.restartFree rho y (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) iy)
    (K : Block) (hService : TargetReceiptService E rho K (SA.freezeTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (rho.stateBefore E iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Kfg, eraseFG Kfg = K ∧ ∀ A, FGBlock.Preceq A Kfg →
      A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s :=
  healing_support_target_path_on E rho hS hy hiy hEpoch K hService hroots

/-- Legacy stamp bound with an explicit global epoch. -/
theorem healing_block_stamp_le_now (hs : V2.D.ScheduleWellFormed E rho)
    (hN : V2.D.NoRestart rho) {jz : Nat} {z : V}
    {K : Block} (hK : K ∈ (storeAt p c E rho jz z).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho jz z).base K ≤
      (V2.D.Run.stateBefore E rho jz z).st.base.now := by
  have ht0 : 0 ≤ (V2.D.Run.stateBefore E rho jz z).st.base.now := by
    rcases V2.D.Engine.stateBefore_now_source_noRestart (fgsaClock p c) E rho hN jz z with
      h | ⟨j, -, hj⟩
    · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at h
      rw [h]
    · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at hj
      exact (hs.in_horizon _ (List.mem_of_getElem? hj)).1
  have hkeys : K ∈ (storeAt p c E rho jz z).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho jz z).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho jz z).«meta».stampKeys]
    exact hK
  unfold GridCO.stampBlock
  cases hf : (storeAt p c E rho jz z).base.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row =>
    simp only [Option.map_some, Option.getD_some]
    have hrm := List.mem_of_find?_eq_some hf
    have hre : row.1 = K := by simpa only [beq_iff_eq] using List.find?_some hf
    have hm : (K, row.2) ∈ (V2.D.Run.stateBefore E rho jz z).st.base.blockStamp := by
      rw [← hre]
      exact hrm
    rcases fgsa_block_stamp_source E rho hN jz z K row.2 hm with ⟨-, h0⟩ | ⟨j, hj, -, -, -, -, he⟩
    · rw [h0]
      exact ht0
    · rw [he]
      have h := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hs hN
        (le_of_lt hj) z
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j z),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at h
      exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S1), 673–689 (IF.5 relay); plan fgsa-s5-m5-d2d4 B
`cause` (H.2 receipt re-proved without PhaseInterval). DC: INTENTIONAL moving
frame. An honest label-i HEAD that covers B is, at the receiver's v_(i+1) read,
a clean resolved frozen vote that supports B. The vote arrives by e_i, and the
HEAD block arrives with strict stamps by the per-block relay
(`healing_block_path_sync`), not by a phase witness relay. -/
theorem healing_batch_seat_sync [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hScope : NextTransferScope E rho iy y i)
    (hCut : HealingWindow p E 1 i)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B)
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
  have hvh : SA.voteTime p.toParams (i + 1) ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hvh
  have hawake := hrec.awake z hk _ hgsti hhori
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk i hhori hawake
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
    (fgsa_head_joined_of_joinedAt E rho hS hjz hJoin)
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams i)) i
  have hBK : Block.Preceq B K := hcover z hk K hhl
  -- The HEAD block is stored at z before e_i.
  have hzinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz z)
    (SA.voteTime p.toParams i)
  have hKz : K ∈ (storeAt p c E rho jz z).base.blocks := by
    have hm := headVote_stored p _ hzinv i
    rwa [clock_base_blocks] at hm
  have hve : SA.voteTime p.toParams i + p.Δ = SA.earlyTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ = 4 * p.Δ * (i : Int) + 2 * p.Δ
    ring
  obtain ⟨Kfg, hKfg, hKe⟩ := ((cstoreInv_stateBefore E rho jz z).baseTree K).mp hKz
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams i + p.Δ) y).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact Gen.Pure.block_preceq_trans
      (eraseFG_preceq (mono _ _ y hy
        (healing_support_idxBefore_le p c E rho hS hiy hvi)).1)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hService := (healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hy hiy hvi
    jz z hk hjz).direct Kfg hKfg hKe
    (hKe ▸ hFloor)
  have hBase := fgsa_target_receipt_on E rho hS hrec.base.receiptIdealization K
    (SA.voteTime p.toParams i + p.Δ) y hy (hKe ▸ hService)
  rw [hve] at hBase
  obtain ⟨Y, hY, hYe⟩ := ((storeBundle_stateBeforeTime E rho _ y).cstore.baseTree K).mp hBase
  have hef : SA.earlyTime p.toParams i ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + 2 * p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hYf : Y ∈ (rho.stateBeforeTime E (SA.freezeTime p.toParams i) y).st.fg.TF := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hY ⊢
    exact (fgsa_store_durable p c E rho (fgsa_idxBefore_mono rho hef) y).1 hY
  have hEpoch : V2.D.restartFree rho y
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams i)) iy :=
    hScope.epoch.mono (fgsa_idxBefore_mono rho (by rw [hve]; exact hef)) le_rfl
  have hKe' := hYe
  have hpath := healing_support_prefreeze_path_on E rho hS hiy hEpoch hYf
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hKb : K ∈ dst.base.blocks := by
    rw [← hKe']
    exact (hinv.baseTree _).mpr ⟨Y, (hpath Y (KitFG.preceq_refl _)).1, rfl⟩
  have hKst : GridCO.stampBlock dst.base K < SA.freezeTime p.toParams i := by
    rw [← hKe']
    exact (hpath Y (KitFG.preceq_refl _)).2
  -- The HEAD block has slot at most i.
  have hKslot : K.slot ≤ i := by
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hKz
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
    (SA.voteTime p.toParams (i + 1)) hEpoch o hom'
  have hstampv : GridCO.stampVote dst.base o < SA.freezeTime p.toParams i := by
    change GridCO.stampVote (FGSA.clock p _ _).base o < _
    rw [hods]
    change GridCO.stampVote (rho.stateBefore E _ y).st.base o < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hos
  have hFK' : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK'⟩) hoK
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
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p _ hinv) o hKb hoK,
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
Blueprint 21:709–715 (H.2 S1), 748–783 (H.3); plan fgsa-s5-m5-d2d4 B `cause`
(continuation scores, H.2 re-proved without PhaseInterval). DC: INTENTIONAL
moving frame. If every honest label-i HEAD covers B, and B is in the domain of
an ancestor-closed part X of the frozen HEAD view of an honest node y at
v_(i+1), and the live leases of that read are compatible with B, then the HEAD
of y at label i + 1 covers B. The honest batch of label i gives the majority
and rival bounds (`batch_head_covers`); the domain gives the kept path. -/
theorem healing_next_transfer_domain [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {i : Slot} {B : FGBlock (Fin p.n)} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG B) K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hScope : NextTransferScope E rho iy y i)
    (hCut : HealingWindow p E 1 i)
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X)
    (hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 (eraseFG B)) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (i + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans
      (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  obtain ⟨-, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) X B).mp hD
  have hvW : W ∈ voterBlocks p dst (i + 1) := hXv hWX
  have hWdst : W ∈ dst.fg.TF :=
    Next.tree_subset_TF p dst (Finset.mem_filter.mp hvW).1
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  -- The kept path through the frozen domain.
  let Xv := voterBlocks p dst (i + 1)
  have hkeep : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList dst (domainR p dst Xv) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWdst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq dst.fg.F A := next_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := next_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A (hdfg ▸ hFA) hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- The live root is compatible with B.
  have hanchor : Block.Compatible (liveRoot p dst) (eraseFG B) := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he, hRd]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZB)
        (Gen.Pure.block_preceq_refl _)
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hlease row hr
      · contradiction
  -- The honest batch of label i.
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho i
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := healing_batch_seat_sync p c E rho hrec mono hgsti
    hcover hy hiy hScope hCut hFB0 k ((healingJoinedSeats_mem E rho i k).mp hk).1
    ((healingJoinedSeats_mem E rho i k).mp hk).2
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := hScope.batch
  have hother : ((GridCO.seats p.n (FGSA.headVotes p dst (i + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := hScope.rivals
  have hcov := batch_head_covers p dst Xv (FGSA.headVotes p dst (i + 1))
    (FGSA.headSupport p dst (i + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card (eraseFG B)
    (fgsa_headSupport_subset_headVotes E rho hE iy y i) rfl
    (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb hanchor hkeep
  rw [fgsa_domainR_eq_filtered] at hcov
  rw [healing_headAtIdx_tick p c E rho hiy]
  change Block.Preceq _ (headVote p dst (i + 1))
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero i)]
  exact hcov

end AvailableChain.FGSA.Run
end
