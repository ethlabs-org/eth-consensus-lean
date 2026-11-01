module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedContinuation -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Any pool with actual stored-seat provenance has the fixed A union W bound.
The pool can contain carried votes. Its consumer supplies their local provenance. -/
theorem outage_pool_opponent_bound [Fintype V]
    (hBase : Base₂ p c E rho) (fast : Bool) (b₀ : Time) (r s : Slot)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r)
    (L : List (GridCO.Wire p.n .root))
    (hL : ∀ o ∈ L, ∀ q, GridCO.headSeat? o = some q →
      ∃ i x, ∃ u ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? u = some s ∧ GridCO.headSeat? u = some q) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  classical
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro q hq
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hq
    by_cases hh : rho.seatOf (.base (.head s)) q ∈ rho.honest
    · apply Finset.mem_union_right
      by_contra hw
      apply hn ((hH q).mpr (Finset.mem_sdiff.mpr ⟨?_, hw⟩))
      obtain ⟨o, ho, hq⟩ := (Gen.AC.Root.vote_pool_mem_seats _ q).mp hl
      obtain ⟨i, x, u, hu, hs, hq⟩ := hL o ho q hq
      have hJ := fgsa_stored_honest_head_joined E rho hBase.valid i x s q u hu hs hq hh
      have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
        slotOf_offset p s p.Δ p.deltaPos.le
          (by have := p.deltaPos; dsimp [Time] at *; omega)
      change rho.seatOf (.base (.head s)) q ∈ rho.honest.filter
        (fun x => joinedAt p E rho x (slotAt p (SA.voteTime p.toParams s))
          (SA.voteTime p.toParams s))
      simp only [hslot, Finset.mem_filter]
      exact ⟨hh, hJ⟩
    · apply Finset.mem_union_left
      rw [Gen.V2.Duty.faulty_def]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩
  · intro q _ j _ he
    exact (hBase.cstar (.base (.head s)) trivial).injective he

/-- A selected honest batch gives retained scores with its actual opponent bound.
The read is joined; carried-vote provenance is proved at that read. -/
theorem outage_receiver_scores_of_bound
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) (r : Slot)
    {ih : Nat} {y : V}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hHonest : ∀ q ∈ H, rho.seatOf (.base (.head r)) q ∈ rho.honest)
    (a : Nat) (hbatch : Gen.Pure.Batch H.card a)
    (hOther : ∀ L : List (GridCO.Wire p.n .root),
      (∀ o ∈ L, ∀ q, GridCO.headSeat? o = some q →
        ∃ i x, ∃ u ∈ (storeAt p c E rho i x).base.votes,
          GridCO.headLabel? u = some r ∧ GridCO.headSeat? u = some q) →
      ((GridCO.seats p.n L).toFinset \ H).card ≤ a) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K)
    (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1))) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  obtain ⟨it, hit⟩ := inclusion_relay_vote_proposal_tick hE
    hDelta hy hih hJ
  have hprov := inclusion_relay_headVotes_provenance E rho hE ih y r hih hJ hit
  have hseat (q : Fin p.n) (hq : q ∈ H) : ∃ K t,
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t (hHonest q hq) he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      rw [hne] at heq
      contradiction
  have hclean : ∀ q ∈ H, GridCO.equivocates (headVotes p dst (r + 1)) q = false := by
    intro q hq
    obtain ⟨K, _, _, _, _, _, _, hu⟩ := hseat q hq
    exact inclusion_no_equivocation _ q _ hu
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K.root⟩, hv, rfl, ?_⟩
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)) _ hK rfl,
        hK, hslot, hDK⟩
  have hother := hOther (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card a D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, _, hnone⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  apply hnone B
  intro q hq
  obtain ⟨K, _, _, _, hK, _, hDK, hu⟩ := hseat q hq
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q B).mp hs
  rw [hu o (hsub ho) hk] at hvote
  have hlookup := resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _))
    (baseVote ⟨.seat (.head r) q, K.root⟩) hK rfl
  rw [Gen.AC.Root.voteSupports_def, hlookup] at hvote
  change (_ && _ && Block.preceq B K) = true at hvote
  have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
  have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
  change Block.compatible L B = true at hLB
  rw [hB] at hLB
  contradiction

/-- The prior good HEADs are received and retained in this joined reader's pool.
The floor is checked at the current read; its monotonicity supplies the early floor.
Synchrony and the epoch are local to the actual preceding label. -/
theorem outage_prior_good_receipts {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) {i : Nat} {y : V} {s : Slot} {B : Block}
    (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hFB : Block.Preceq (F_at p c E rho i y) B)
    (H : Finset (Fin p.n))
    (hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
      (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) K → Block.Preceq B K) :
    ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (s + 1))) (s + 1) ∧
      K ∈ (clock p (storeAt p c E rho i y)
        (SA.voteTime p.toParams (s + 1))).base.blocks ∧ K.slot ≤ s ∧ Block.Preceq B K := by
  have hs := hBase.valid.toScheduleWellFormed
  have hevs : SA.earlyTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    rw [arming_early_eq, arming_vote_eq]; push_cast; linarith [p.deltaPos]
  have hef : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
  have hAw : E.awake y (SA.earlyTime p.toParams s) = true := by
    apply fgsa_awake_of_joinedAt E rho y (s + 1) _ _ hJ
    · rw [arming_early_eq]; have := p.deltaPos; positivity
    · change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      push_cast; linarith [p.deltaPos]
    · exact hevs.le
  have hte : ((4 * s + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams s := by
    rw [arming_early_eq]; push_cast; ring
  obtain ⟨je, hje, _⟩ := fgsa_tick_total E rho hs hBase.delta y hy (4 * s + 2)
    (hte ▸ hevs.le.trans hhor) (hte ▸ hAw)
  rw [hte] at hje
  have hei := V2.D.Engine.eventIndex_lt_of_time_lt hs hje hi hevs
  have hEpoch := inclusion_epoch_of_joined_tick E rho hs hi hJ
    (a := SA.earlyTime p.toParams s) (by
      change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) < 4 * p.Δ * (s : Int) + 2 * p.Δ
      push_cast; linarith [p.deltaPos])
  have hCut : rho.idxBefore (SA.earlyTime p.toParams s) ≤ je := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hje _).mp hn)).elim
  let dst := clock p (storeAt p c E rho i y) (SA.voteTime p.toParams (s + 1))
  intro w hw
  obtain ⟨hyw, haw⟩ := hSelected w hw
  have htv : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    rw [arming_vote_eq]; push_cast; ring
  obtain ⟨kk, hkk, _⟩ := fgsa_tick_total E rho hs hBase.delta _ hyw (4 * s + 1)
    (htv ▸ (arming_vote_lt_early p s).1.le.trans (hevs.le.trans hhor)) (htv ▸ haw.1)
  rw [htv] at hkk
  let K := headVote p (clock p (storeAt p c E rho kk
    (rho.seatOf (.base (.head s)) w)) (SA.voteTime p.toParams s)) s
  have hemK : ofHead p ⟨.seat (.head s) w, K.root⟩ ∈ rho.emitsAt E kk := by
    rw [(rho.step_tick_eq E hkk).2]
    exact (fgsa_emits_head E rho _ _ _ s w K.root).mpr
      ⟨haw.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hkk haw, rfl⟩
  have hK : HeadTargetAtEmission p c E rho _
      (ofHead p ⟨.seat (.head s) w, K.root⟩) (SA.voteTime p.toParams s) K :=
    ⟨kk, s, w, hkk, hemK, rfl, rfl⟩
  have hBK := hTargets w hw K hK
  have hFK : Block.Preceq (F_at p c E rho je y) K :=
    block_preceq_trans (eraseFG_preceq (hf.mono je i y hy hei.le).1)
      (block_preceq_trans hFB hBK)
  obtain ⟨hHS, hBS⟩ := inclusion_early_services hBase hSync hevs.le hhor hGST
    ⟨hy, hJ⟩ hje hyw hK hFK
  obtain ⟨hem', hv, hvs, hKb, hbs, hslot⟩ := inclusion_head_receipt_early_on E rho
    hBase.valid s hje w hyw haw hkk K rfl hHS.some hBS
    (hEpoch.mono le_rfl hei.le) hBase.receiptIdealization
  have hkeep := inclusion_stamps_kept_on E rho hei.le y
    (hEpoch.mono hCut le_rfl) _ K hv hKb
  let o := baseVote (⟨.seat (.head (s)) w, K.root⟩ : HeadWire p.n)
  have hvd : o ∈ dst.base.votes := by
    change _ ∈ (clock p (storeAt p c E rho i y) _).base.votes
    rw [(clock_vn _ _).1]
    exact hkeep.1
  have hKd : K ∈ dst.base.blocks := by
    change K ∈ (clock p (storeAt p c E rho i y) _).base.blocks
    rw [clock_base_blocks]
    exact hkeep.2.1
  have hvsd : GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (s) := by
    change GridCO.stampVote (clock p (storeAt p c E rho i y) _).base o < _
    have hkey : o ∈ (storeAt p c E rho i y).base.voteStamp.map Prod.fst := by
      change o ∈ (V2.D.Run.stateBefore E rho i y).st.base.voteStamp.map Prod.fst
      rw [fgsa_vote_stamp_keys E rho i y]
      exact hkeep.1
    rw [inclusion_stampVote_of_prefix
      (by rw [(clock_cumulative p _ _).2.2.2.1]) hkey, hkeep.2.2.1]
    exact hvs.trans hef
  have hbsd : GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (s) := by
    change GridCO.stampBlock (clock p (storeAt p c E rho i y) _).base K < _
    have hkey : K ∈ (storeAt p c E rho i y).base.blockStamp.map Prod.fst := by
      change K ∈ (V2.D.Run.stateBefore E rho i y).st.base.blockStamp.map Prod.fst
      rw [(storeBundle_stateBefore E rho i y).«meta».stampKeys]
      exact hkeep.2.1
    rw [inclusion_stampBlock_of_prefix
      (by rw [(clock_cumulative p _ _).2.2.1]) hkey, hkeep.2.2.2]
    exact hbs.trans hef
  have hKa : GridCO.blockKnown (actView dst) K = true := by
    apply decide_eq_true
    apply (actView_blocks dst K).mpr
    refine ⟨hKd, block_compatible_of_common (block_preceq_refl K) ?_⟩
    change Block.Preceq (eraseFG (clock p (storeAt p c E rho i y) _).fg.F) K
    rw [clock_fg]
    exact block_preceq_trans (hFB) hBK
  refine ⟨K, _, hem', ?_, hKd, hslot, hBK⟩
  unfold headSupport
  dsimp only
  rw [List.mem_eraseDups]
  apply List.mem_append_left
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨hvd, beq_self_eq_true _⟩, ?_⟩
  have hInv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i y) _
  have hres := actView_resolve_target p dst hInv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho i y)))
    o (of_decide_eq_true hKa) rfl
  unfold GridCO.resolvedBefore
  rw [hres]
  change (decide (K.slot ≤ s) &&
    decide (GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (s)) &&
    decide (GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (s))) = true
  simp only [hslot, hvsd, hbsd, decide_true, Bool.and_self]
/-- A nonempty selected joined batch supplies an actual prior held source.
This local witness needs no receiver service or synchrony premise. -/
theorem outage_prior_covering_source
    (hBase : Base₂ p c E rho) {s : Slot} {B : Block}
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) (H : Finset (Fin p.n))
    (hNonempty : H.Nonempty)
    (hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))
    (hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
      (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) K → Block.Preceq B K) :
    ∃ j y P, rho.events[j]? = some (.tick y (SA.voteTime p.toParams s)) ∧
      y ∈ rho.honest ∧ P ∈ (storeAt p c E rho j y).fg.TF ∧ Block.Preceq B (eraseFG P) := by
  obtain ⟨q, hq⟩ := hNonempty
  obtain ⟨hy, hJ⟩ := hSelected q hq
  have hs := hBase.valid.toScheduleWellFormed
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hBase.delta _ hy (4 * s + 1)
    (by rw [arming_vote_nat]; exact hhor) (by rw [arming_vote_nat]; exact hJ.1)
  rw [arming_vote_nat] at hj
  let K := headVote p (clock p (storeAt p c E rho j
    (rho.seatOf (.base (.head s)) q)) (SA.voteTime p.toParams s)) s
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ rho.emitsAt E j := by
    rw [(rho.step_tick_eq E hj).2]
    exact (fgsa_emits_head E rho _ _ _ s q K.root).mpr
      ⟨hJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hj hJ, rfl⟩
  have hK : K ∈ (storeAt p c E rho j (rho.seatOf (.base (.head s)) q)).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho j (rho.seatOf (.base (.head s)) q)
      (SA.voteTime p.toParams s)).cstore s
    change K ∈ (clock p (storeAt p c E rho j _) _).base.blocks at hm
    rwa [clock_base_blocks] at hm
  obtain ⟨P, hP, heP⟩ := ((cstoreInv_stateBefore E rho j _).baseTree K).mp hK
  exact ⟨j, _, P, hj, hy, hP, heP.symm ▸ hTargets q hq K ⟨j, s, q, hj, hem, rfl, rfl⟩⟩

end AvailableChain.FGSA.Run
end
