module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossNext
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossCause

public section

/-! Blueprint 21 H2′:3382–3391; H.1 release and H.2 next transfer.
Centaur fgsa-s5-h2p-route; B1/B15/B17/B18.
DC: SAME release count from unanimous honest HEADs before the gate. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.AC.Root

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem unanimous_vote_release (s : Slot) :
    SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
  push_cast
  ring

private theorem unanimous_vote_clock (st : State p.n) (s : Slot) :
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


private def unanimousReleaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B)))).toFinset

private theorem unanimous_release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) :
    GridCO.releaseCount q v s B = (unanimousReleaseSeats q v s B).card := by
  have hp : (fun o : GridCO.Wire n .root => match GridCO.resolvedHead? v o with
      | some C => !Block.compatible C B
      | none => false) = (fun o => (GridCO.resolvedHead? v o).any
        (fun C => !Block.compatible C B)) := by
    funext o
    cases GridCO.resolvedHead? v o <;> rfl
  unfold GridCO.releaseCount unanimousReleaseSeats
  dsimp only
  refine Eq.trans ?_ (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup (α := Fin n) _))).symm
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext k
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ k).any f)
  exact hp

private theorem unanimous_release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) (k : Fin n)
    (he : GridCO.equivocates (GridCO.votesAt v s) k = false)
    (o : GridCO.Wire n .root) (ho : o ∈ GridCO.votesAt v s)
    (hr : GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true)
    (hk : GridCO.headSeat? o = some k)
    (hc : (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B) = true) :
    k ∈ unanimousReleaseSeats q v s B := by
  dsimp only [unanimousReleaseSeats]
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq]
  refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
  exact List.mem_dedup.mpr (List.mem_filterMap.mpr
    ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hk⟩)

private theorem unanimous_seat_release [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hbatch : ∀ z ∈ rho.honest, headAtLabel p c E rho z i = some B)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hScope : NextTransferScope E rho iy y i)
    (hCut : HealingWindow p E 1 i)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B)
    (row : Block × Nat × Time) (hbad : ¬ Block.Compatible row.1 B)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head i)) k ∈ rho.honest)
    (hJoin : joinedAt p E rho (rho.seatOf (.base (.head i)) k) i
      (SA.voteTime p.toParams i)) :
    k ∈ unanimousReleaseSeats p.toParams.engine
      (actView (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1)))) i row.1 := by
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
  have heQ : K = B := Option.some.inj (hhl.symm.trans (hbatch z hk))
  have hBK : Block.Preceq B K := heQ ▸ Gen.Pure.block_preceq_refl B
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
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK'⟩) hoK
  have hresolved : GridCO.resolvedBefore (actView dst) o
      (SA.freezeTime p.toParams i) = true := by
    unfold GridCO.resolvedBefore
    rw [hresolve]
    simp only [Bool.and_eq_true, decide_eq_true_eq, hol, Option.getD_some]
    exact ⟨⟨hKslot, hstampv⟩, hKst⟩
  have hmono : GridCO.resolvedBefore (actView dst) o
      (GridCO.releaseTime p.toParams.engine i) = true := by
    unfold GridCO.resolvedBefore at hresolved ⊢
    rw [hresolve] at hresolved ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hresolved ⊢
    have htime : SA.freezeTime p.toParams i < GridCO.releaseTime p.toParams.engine i := by
      change 4 * p.Δ * (i : Int) + 3 * p.Δ < 4 * p.Δ * (i : Int) + 5 * p.Δ
      linarith [p.deltaPos]
    exact ⟨⟨hresolved.1.1, hresolved.1.2.trans htime⟩, hresolved.2.trans htime⟩
  have hvotes : GridCO.votesAt (actView dst) i =
      GridCO.votesAt (storeAt p c E rho iy y).base i := by
    unfold GridCO.votesAt
    change List.filter _ dst.base.votes = _
    dsimp only [dst]
    rw [(clock_vn _ _).1]
  apply unanimous_release_mem
  · rwa [hvotes]
  · rw [hvotes]
    have hod0 : o ∈ (storeAt p c E rho iy y).base.votes := by
      rwa [(clock_vn _ _).1] at hod
    exact List.mem_filter.mpr ⟨hod0, by simp only [hol, beq_iff_eq]⟩
  · exact hmono
  · exact hok
  · rw [hresolve, heQ]
    change (Bool.not (Block.compatible B row.1)) = true
    cases hc : Block.compatible B row.1 with
    | false => rfl
    | true =>
      apply False.elim
      apply hbad
      change (Block.preceq row.1 B || Block.preceq B row.1) = true
      rw [Bool.or_comm]
      exact hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.1:689–692, H2′:3382–3391; Centaur gate-free count;
B1/B15/B17/B18. DC: SAME honest opposition releases each conflicting lease.
The next HEAD tick bounds synchrony. No gate tick or fast-support input is used. -/
theorem healing_unanimous_release_compat [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {v : Slot} {Q : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams v)
    (hbatch : ∀ z ∈ rho.honest, headAtLabel p c E rho z v = some Q)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (v + 1))))
    (hScope : NextTransferScope E rho iy y v)
    (hCut : HealingWindow p E 1 v)
    (hJoined : joinedAtTime p (storeAt p c E rho iy y).restartTime
      (SA.releaseTime p.toParams v) = true)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) Q) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (v + 1))).base.obligations, Block.Compatible row.1 Q := by
  classical
  intro row hrow
  by_contra hbad
  let st0 := storeAt p c E rho iy y
  let dst := FGSA.clock p st0 (SA.voteTime p.toParams (v + 1))
  let st1 : State p.n := { st0 with
    base := GridCO.expire { st0.base with now := SA.releaseTime p.toParams v }
      (SA.releaseTime p.toParams v) }
  have hdst : dst = onView (fun view => SA.Root.release p.toParams view v) st1 := by
    dsimp only [dst]
    rw [unanimous_vote_clock, unanimous_vote_release, fgsa_release_clockPre st0 v hJoined]
  have hcount := (healing_support_release_rows st0 v hJoined row hrow).2
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hlevel : row.2.1 = SA.releaseThreshold p.toParams := hinv.leaseKeys.2 _ hrow
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho v
  have hsub : Hon ⊆ unanimousReleaseSeats p.toParams.engine (actView dst) v row.1 := by
    intro k hk
    exact unanimous_seat_release p c E rho hrec mono hgst hbatch hy hiy hScope hCut hFQ row hbad k
      ((healingJoinedSeats_mem E rho v k).mp hk).1
      ((healingJoinedSeats_mem E rho v k).mp hk).2
  have hle := Finset.card_le_card hsub
  rw [← unanimous_release_card] at hle
  have heq : GridCO.releaseCount p.toParams.engine (actView dst) v row.1 =
      GridCO.releaseCount p.toParams.engine (actView st1) v row.1 := by
    rw [hdst]
    rfl
  rw [heq] at hle
  have hselected : SA.releaseThreshold p.toParams ≤ Hon.card := hScope.release
  dsimp only [dst, st1, st0] at hle hcount
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H2′:3382–3391, H.2:709–715; Centaur proposed adapter;
B1/B15/B17/B18. DC: SAME next transfer from the unanimous prior batch.
Kept root cases use finality coverage; the domain case uses the gate-free count. -/
theorem healing_unanimous_next_transfer_kept [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    {v : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams v) (heQ : eraseFG Qfg = Q)
    (hbatch : ∀ z ∈ rho.honest, headAtLabel p c E rho z v = some Q)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (v + 1))))
    (hScope : NextTransferScope E rho iy y v)
    (hCut : HealingWindow p E 1 v)
    (hJoined : joinedAtTime p (storeAt p c E rho iy y).restartTime
      (SA.releaseTime p.toParams v) = true)
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (v + 1))) (v + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho iy y).fg.F A →
      FGBlock.Preceq A W → A ∈ X)
    (hkept : Kept p c E rho iy y X Qfg) :
    Block.Preceq Q (headAtIdx p c E rho iy (v + 1)) := by
  rw [← heQ]
  rcases hkept with hZ | hD | hF
  · exact healing_head_covers_root p c E rho hiy (Nat.succ_ne_zero v) (Or.inl hZ)
  · have hFQ := (KitFG.mem_filteredFromView (heightView p)
        (R_at p c E rho iy y) X Qfg).mp hD
    have hlease := healing_unanimous_release_compat p c E rho hrec mono hgst hbatch
      hy hiy hScope hCut hJoined
      (heQ ▸ eraseFG_preceq hFQ.2.1)
    exact healing_next_transfer_domain p c E rho hrec mono hgst
      (fun z hz K hK => by
        rw [hbatch z hz] at hK
        cases hK
        rw [heQ]
        exact Gen.Pure.block_preceq_refl _)
      hy hiy hScope hCut hXv hXc hD (by simpa only [heQ] using hlease)
  · exact healing_head_covers_root p c E rho hiy (Nat.succ_ne_zero v) (Or.inr hF)

end AvailableChain.FGSA.Run
end
