module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Stored honest seats belong to the joined denominator at their vote time. -/
theorem arming_rest_bound_joined [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hE : V2.D.ExecutionValid E rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head r)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head r)) k) r (SA.voteTime p.toParams r) → k ∈ H)
    (L : List (GridCO.Wire p.n .root))
    (hL : ∀ o ∈ L, ∀ k, GridCO.headSeat? o = some k →
      ∃ i x, ∃ o' ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? o' = some r ∧ GridCO.headSeat? o' = some k) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
  classical
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    obtain ⟨i, x, o', ho', hl', hs'⟩ := hL o ho k hs
    exact fgsa_stored_honest_head_joined E rho hE i x r k o' ho' hl' hs' hh
  · intro k _ j _ he
    exact (hC (.base (.head r)) trivial).injective he

/-- Proposal scores use joined voters and receipts in the actual proposal store. -/
theorem arming_inclusion_proposer_prior_of_F_prefix_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head (s - 1))) q) (s - 1)
        (SA.voteTime p.toParams (s - 1)))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  intro L hL
  have hstored (o : GridCO.Wire p.n .root) (ho : o ∈ proposerVotes st s) :
      o ∈ (storeAt p c E rho i x).base.votes ∧ GridCO.headLabel? o = some (s - 1) := by
    have h := List.mem_filter.mp ho
    exact ⟨hvotes ▸ h.1, beq_iff_eq.mp h.2⟩
  have hclean : ∀ q ∈ H, GridCO.equivocates (proposerVotes st s) q = false := by
    intro q hq
    obtain ⟨K, t, he, _, _, _, _, _⟩ := hrec q hq
    refine inclusion_no_equivocation _ q
      (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) ?_
    intro o ho hs
    obtain ⟨hm, hl⟩ := hstored o ho
    exact fgsa_honest_head_eq_of_stored E rho hE i x (s - 1) q K.root t ((hH q).mp hq).1 he
      o hm hl hs
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports st.base.blocks (proposerSupport st s) q D0 = true := by
    intro q hq
    obtain ⟨K, t, _, hv, hK, hlookup, hslot, hDK⟩ := hrec q hq
    have hKb := (List.mem_filter.mp (resolvedHead_mem _ _ hK)).1
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head (s - 1)) q, K.root⟩, ?_, rfl, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
      change (match GridCO.resolvedHead? (actView st) _ with
        | some H => Block.preceq (eraseFG st.fg.F) H && decide (H.slot ≤ s - 1)
        | none => false) = true
      rw [hK]
      exact Bool.and_eq_true_iff.mpr ⟨block_preceq_trans hFD hDK, decide_eq_true hslot⟩
    · exact (Gen.AC.Root.vote_support_body _ _ _).mpr ⟨K, hlookup, hKb, hslot, hDK⟩
  have hother := arming_rest_bound_joined E rho hC hE (s - 1) H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (proposerVotes st s)
    (fun o ho k hk => ⟨i, x, o, (hstored o ho).1, (hstored o ho).2, hk⟩)
  have hc := Gen.AC.Root.batch_counts st.base.blocks (proposerVotes st s) (proposerVotes st s)
    (proposerSupport st s) H H.card (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1) rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, hrival, _⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  have hDB : Block.compatible D0 B = false := by
    cases h : Block.compatible D0 B with
    | false => rfl
    | true =>
      have hLB := block_compatible_of_preceq_compatible hL h
      change Block.compatible L B = true at hLB
      rw [hB] at hLB
      contradiction
  exact lt_of_le_of_lt (hrival B hDB) (lt_of_lt_of_le hbatch.lt (hprefix L hL).1)

/-- HEAD scores use joined voters and local provenance in the consuming read. -/
theorem arming_inclusion_reader_scores_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    {ih : Nat} {y : V}
    (_hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K)
    (hprov : ∀ o ∈ headVotes p
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1),
      ∀ q, GridCO.headSeat? o = some q →
      o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r ∨
        GridCO.equivocates (GridCO.votesAt (storeAt p c E rho ih y).base r) q = true) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
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
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t ((hH q).mp hq).1 he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      exact Bool.noConfusion (hne.symm.trans heq)
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
  have hother := arming_rest_bound_joined E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
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

end AvailableChain.FGSA.Run
end
