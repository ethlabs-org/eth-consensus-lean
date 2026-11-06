module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.SA
@[expose] public section

/-! # The healthy two-validator run: the SA's calls

The SA calls of the run on chain frames (`ChainFrame`), for either validator `y`:

* `acOnTick_eq`: the tick by the residue of the time; `tryVote_zero`: the vote of slot `0` at `1`;
  `tryVote_blk`: the vote of slot `k + 1` on the block of that slot, which is ready;
* `acProposal_tick`: `v0`'s proposal at `t_{k+1}` on the tip `k`, with both slot-`k` votes;
* `admitVote_fresh` and the optimistic check: one vote of the slot locks nothing
  (`optimisticSelect_one`), both votes lock the tip (`optimisticSelect_two`);
* `getConfirmation_tick`: the confirmation of slot `σ` is the block of slot `σ`;
* `acToFG_tick`, `acToFG_none`: `ac_to_fg` returns the new tip once, then nothing. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node ChainFrame

theorem slot4 (k : Nat) : sp.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by
  rw [slot_nat]; omega

theorem vote_zero (y : Fin sp.n) : vote y 0 = ⟨y, 0, (blk 0).root⟩ := rfl

/-- `ac_on_tick` by the residue of the time modulo a slot. -/
theorem acOnTick_eq (y : Fin sp.n) (A : SAState sp.n) (Φ : N.Frm) (n : Nat)
    (hj : A.restartTime = ⊥) :
    acOnTick sp y A Φ n =
      if n % 4 = 2 ∧ 4 ≤ n then (updateConfirmation sp A Φ n (n / 4 - 1), [])
      else if n % 4 = 1 then tryVote sp y A Φ n else (A, []) := by
  unfold acOnTick
  rw [ite_eq_right (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [slot_nat, ts_nat]
  have e1 : ((n : Int) = 4 * ((n / 4 : Nat) : Int) + sp.Δ) ↔ n % 4 = 1 := by
    change _ = _ + 1 ↔ _; omega
  have e2 : ((n : Int) = 4 * ((n / 4 : Nat) : Int) + 2 * sp.Δ ∧ 0 < n / 4) ↔
      (n % 4 = 2 ∧ 4 ≤ n) := by
    change _ = _ + 2 * 1 ∧ _ ↔ _; omega
  by_cases h1 : n % 4 = 1
  · have h2 : ¬ (n % 4 = 2 ∧ 4 ≤ n) := by omega
    rw [ite_eq_left (e1.2 h1), ite_eq_right (fun h => h2 (e2.1 h)), ite_eq_right h2,
      ite_eq_left h1]
  · rw [ite_eq_right (fun h => h1 (e1.1 h))]
    by_cases h2 : n % 4 = 2 ∧ 4 ≤ n
    · rw [ite_eq_left (e2.2 h2), ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 (e2.1 h)), ite_eq_right h2, ite_eq_right h1]

theorem tryVote_voted {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} {t : Time}
    (h : A.votedSlot = (sp.slot t : Int)) : tryVote sp y A Φ t = (A, []) := by
  unfold tryVote
  dsimp only
  rw [ite_eq_left (Or.inr (Or.inl h))]

/-- Admission of a vote of the current slot that the pool does not hold, with no other vote of
its validator. -/
theorem admitVote_fresh {A : SAState sp.n} {t : Time} {v : Vote sp.n}
    (hst : sp.slot t = v.slot) (hn : v ∉ A.pool v.slot)
    (hv : ∀ x ∈ A.pool v.slot, x.val ≠ v.val) :
    admitVote sp A t v =
      { A with pool := Function.update A.pool v.slot (A.pool v.slot ++ [v]),
               voteStamp := Function.update A.voteStamp v (ETime.of t) } := by
  unfold admitVote
  rw [ite_eq_right (by rw [hst]; push Not; exact ⟨by omega, le_rfl, hn⟩)]
  have hf : (A.pool v.slot).filter (fun x => x.val = v.val) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; simpa using hv x hx
  rw [hf, ite_eq_right (by simp)]

theorem optimisticSelect_slot_zero {A : SAState sp.n} {Φ : N.Frm} {t : Time}
    (h : sp.slot t = 0) : optimisticSelect sp A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  rw [ite_eq_left (Or.inr (Or.inl h))]

/-- One validator's vote locks nothing. -/
theorem optimisticSelect_one {A : SAState sp.n} {Φ : N.Frm} {t : Time} {v : Vote sp.n}
    (h : A.pool (sp.slot t) = [v]) : optimisticSelect sp A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  split_ifs
  · rfl
  · convert deepest_empty Φ
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h3 _
    have hsub : optimisticVoters sp A Φ (sp.slot t) B ⊆ {v.val} := by
      rintro i ⟨x, hx, rfl, -⟩
      rw [h, List.mem_singleton] at hx; subst hx; rfl
    have := le_trans (Set.ncard_le_ncard hsub (Set.finite_singleton _))
      (le_of_eq (Set.ncard_singleton _))
    change 3 * 2 ≤ 4 * _ at h3
    omega

/-- Both votes of the slot on its block lock that block. -/
theorem optimisticSelect_two {Φ : N.Frm} {f j s : Nat} (h : ChainFrame Φ f j s) (hs : 1 ≤ s)
    {A : SAState sp.n} {t : Time} (hst : sp.slot t = s) (ht : t < sp.ts s + 2 * sp.Δ)
    (hjn : joined sp A t) {y : Fin sp.n} (hpool : A.pool s = [vote y s, vote (other y) s]) :
    optimisticSelect sp A Φ t = some (blk s) := by
  unfold optimisticSelect
  rw [ite_eq_right (by rw [hst]; push Not; exact ⟨hjn, by omega, ht⟩)]
  have htip := h.mem (le_trans h.fj h.jτ) le_rfl
  apply h.deepest_eq (fun B hB => hB.1)
  · refine ⟨htip, ?_, ?_⟩
    · have : optimisticVoters sp A Φ (sp.slot t) (blk s) = Set.univ := by
        ext i
        simp only [optimisticVoters, Set.mem_ofPred_eq, Set.mem_univ, iff_true, hst, hpool]
        have hi : i = y ∨ i = other y := by
          have key : ∀ i y : Fin sp.n, i = y ∨ i = other y := by unfold other; decide
          exact key i y
        rcases hi with rfl | rfl
        · exact ⟨vote i s, List.mem_cons_self .., rfl, blk s, htip, rfl, Relation.ReflTransGen.refl⟩
        · exact ⟨vote (other y) s, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, blk s,
            htip, rfl, Relation.ReflTransGen.refl⟩
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · rintro ⟨B, hB, hnc⟩; exact hnc (compatible_chain h htip hB.1)
  · rintro B ⟨hB, -⟩
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB
    exact ⟨m, hm, rfl⟩

theorem optimisticConfirmation_of_some {A : SAState sp.n} {Φ : N.Frm} {t : Time} {B : N.Blk}
    (h : optimisticSelect sp A Φ t = some B) :
    optimisticConfirmation sp A Φ t = updateLatestConfirmed sp
      { A with locks := addLocks sp A.locks Φ t (sp.slot t) {(B.root, true, sp.slot t + 2)} }
      Φ B := by
  unfold optimisticConfirmation
  rw [h]
  dsimp only
  rw [fastExpiry_eq]

/-- The vote of slot `0`, at time `1`. -/
theorem tryVote_zero {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} (h : ChainFrame Φ 0 0 0)
    (hj : A.restartTime = ⊥) (hvs : A.votedSlot = -1) (hL : LocksLe A.locks 0) :
    ∃ d, tryVote sp y A Φ 1 = (admitVote sp { A with votedSlot := 0 } 1 (vote y 0),
      [⟨vote y 0, { A with votedSlot := 0 }, some d⟩]) := by
  have hs : sp.slot (1 : Int) = 0 := slot_nat 1
  unfold tryVote
  dsimp only
  rw [hs, ite_eq_right (by
      rw [ts_nat, hvs]; push Not; exact ⟨joined_of_bot hj _, by decide, by decide⟩),
    ite_eq_right (by rw [ts_nat]; change ¬ ((1 : Int) < 4 * 0 + 1 ∧ _); omega),
    ite_eq_right (lt_irrefl 0)]
  have hanc : getAnchor sp A Φ 1 = blk 0 := h.getAnchor_eq hL le_rfl (Or.inr rfl)
  have hhead : getHead sp A Φ 1 (Φ.viableTree (voteDomain sp A Φ 0))
      (mergedVoteView sp A Φ 0) ((0 : Nat) - 1) = blk 0 := by
    unfold getHead
    rw [hanc]
    refine ghost_tip (fun B hB => ?_) _ _ _
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem (voteDomain_subset_tree hB.1)
    exact ⟨m, hm, rfl⟩
  rw [hhead, optimisticConfirmation_of_none (optimisticSelect_slot_zero hs)]
  exact ⟨_, rfl⟩

theorem blockSupport_blk (k : Nat) : blockSupport (blk (k + 1)) = [vote w0 k, vote w1 k] := by
  change (blk (k + 1)).acPayload.2 = _; rw [blk_acPayload]

theorem blockVotes_blk (k : Nat) : blockVotes (blk (k + 1)) = [vote w0 k, vote w1 k] := by
  change (blk (k + 1)).acPayload.1 = _; rw [blk_acPayload]

theorem voteReady_blk {Φ : N.Frm} {f k : Nat} (h : ChainFrame Φ f (jx (k + 1)) (k + 1))
    (hf : f ≤ k) : voteReady sp Φ (k + 1) := by
  refine ⟨blk (k + 1), h.mem (by omega) le_rfl, blk_slot _, fun x hx _ => ?_⟩
  rw [blockSupport_blk] at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨blk k, h.mem hf (by omega), rfl, by rw [blk_slot]⟩
  · rw [List.mem_singleton] at hx; subst hx
    exact ⟨blk k, h.mem hf (by omega), rfl, by rw [blk_slot]⟩

theorem jx_succ_le (k : Nat) : jx (k + 1) ≤ k := by
  unfold jx ent hgt; split_ifs <;> omega

/-- **The vote of slot `k + 1`**, on the block of that slot, at `t_{k+1}`. -/
theorem tryVote_blk {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jx (k + 1)) (k + 1)) (hj : A.restartTime = ⊥)
    (hvs : A.votedSlot = (k : Int)) (hpool : A.pool (k + 1) = []) (hL : LocksLe A.locks k)
    (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ L₁ d, tryVote sp y A Φ ((4 * (k + 1) : Nat) : Int) =
      (admitVote sp { A with locks := L₁, votedSlot := (k + 1 : Nat) }
        ((4 * (k + 1) : Nat) : Int) (vote y (k + 1)),
        [⟨vote y (k + 1), { A with locks := L₁, votedSlot := (k + 1 : Nat) }, some d⟩]) ∧
      LocksLe L₁ k ∧ (1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁) := by
  have hs := slot4 k
  have hf : f ≤ k := le_trans h.fj (jx_succ_le k)
  unfold tryVote
  dsimp only
  rw [hs, ite_eq_right (by
      rw [ts_nat, hvs]; push Not
      exact ⟨joined_of_bot hj _, by push_cast; omega, by rw [delta1]; push_cast; linarith⟩),
    ite_eq_right (fun hc => hc.2.elim (by omega) (fun hn => hn (voteReady_blk h hf))),
    ite_eq_left (by omega : 0 < k + 1)]
  set V := mergedVoteView sp A Φ (k + 1)
  set L₁ := unlock sp A.locks Φ ((4 * (k + 1) : Nat) : Int) (((k + 1 : Nat) : Int) - 1) V
  have hL₁ : LocksLe L₁ k := unlock_le h hL _ _ _
  have htip₁ : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁ := fun hk =>
    mem_unlock h (htip hk) hf (by omega) rfl (by rw [hs]; change k + 1 ≤ k + 2; omega)
      (by push_cast; omega) V
  have hanc : getAnchor sp { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int) = blk k := by
    refine h.getAnchor_eq hL₁ (jx_succ_le k) ?_
    rcases Nat.lt_or_ge k 1 with hk | hk
    · right; obtain rfl : k = 0 := by omega
      rfl
    · left
      exact ⟨h.mem hf (by omega), _, h.mem_liveLocks (htip₁ hk) hf (by omega) rfl
        (by rw [hs]; change k + 1 ≤ k + 2; omega), rfl⟩
  have hncard : Φ.tree.ncard = (k + 1 - f) + 1 := by rw [h.tree_ncard]; omega
  have hhead : getHead sp { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int)
      (Φ.viableTree (voteDomain sp { A with locks := L₁ } Φ (k + 1))) V
      (((k + 1 : Nat) : Int) - 1) = blk (k + 1) := by
    unfold getHead
    rw [hanc, hncard]
    have hT : ∀ B ∈ Φ.viableTree (voteDomain sp { A with locks := L₁ } Φ (k + 1)),
        ∃ m ≤ k + 1, B = blk m := fun B hB => by
      obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem (voteDomain_subset_tree hB.1)
      exact ⟨m, hm, rfl⟩
    rw [ghost_step (fun B hB => (hT B hB).imp fun _ h => h.2)
      (viableTree_voterBlockTree_subset_voteDomain
        (h.mem_viableTree (mem_voterBlockTree h _ (by omega) le_rfl) (jx_le _) le_rfl
          (mem_voterBlockTree h _ (by omega) le_rfl)))
      (Or.inr (Or.inl (by rw [blk_slot, hs])))]
    exact ghost_tip hT _ _ _
  rw [hhead]
  have hadm : (admitVote sp { A with locks := L₁, votedSlot := (k + 1 : Nat) }
      ((4 * (k + 1) : Nat) : Int) (vote y (k + 1))).pool
        (sp.slot ((4 * (k + 1) : Nat) : Int)) = [vote y (k + 1)] := by
    rw [hs, admitVote_fresh (by rw [hs]; rfl) (by change _ ∉ A.pool (k + 1); rw [hpool]; simp)
      (by change ∀ x ∈ A.pool (k + 1), _; rw [hpool]; simp)]
    change Function.update A.pool (k + 1) (A.pool (k + 1) ++ [vote y (k + 1)]) (k + 1) = _
    rw [Function.update_self, hpool]; rfl
  exact ⟨L₁, ⟨blk (k + 1), getAnchor sp { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int),
    voteDomain sp { A with locks := L₁ } Φ (k + 1)⟩,
    Prod.ext (optimisticConfirmation_of_none (optimisticSelect_one hadm)) rfl, hL₁, htip₁⟩

/-- The resolution time of a vote on a chain block of the tree, of the block's slot. -/
theorem resolutionTime_vote {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {A : SAState sp.n}
    {y : Fin sp.n} {k : Nat} (h1 : f ≤ k) (h2 : k ≤ τ) :
    resolutionTime A Φ (vote y k) = max (A.voteStamp (vote y k)) (A.blockStamp (blk k).root) := by
  unfold resolutionTime
  rw [vote_head, h.lookup_blk h1 h2]
  dsimp only
  rw [ite_eq_right (by rw [blk_slot, vote_slot]; exact lt_irrefl k)]

/-- **`ac_proposal` at `t_{k+1}`**: the tip `k` as the parent, both slot-`k` votes as the
payload. -/
theorem acProposal_tick {A : SAState sp.n} {Φ : N.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jx k) k) (hj : A.restartTime = ⊥)
    (hpool : A.pool k = [vote w0 k, vote w1 k])
    (hvst : ∀ y, A.voteStamp (vote y k) < ⊤) (hbst : A.blockStamp (blk k).root < ⊤)
    (hL : LocksLe A.locks k) (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ L₁ d, SA.acProposal sp A Φ ((4 * (k + 1) : Nat) : Int) =
        ({ A with locks := L₁ },
          some (d, ([vote w0 k, vote w1 k], [vote w0 k, vote w1 k]))) ∧ d.head = blk k ∧
      LocksLe L₁ k ∧ (1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁) := by
  have hs := slot4 k
  have hf : f ≤ k := le_trans h.fj (jx_le k)
  unfold SA.acProposal
  rw [ite_eq_right (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [hs]
  have hk : (((k + 1 : Nat) : Int) - 1) = (k : Int) := by push_cast; ring
  rw [hk]
  have hp : voteViewList A Φ (k : Int) ⊤ =
      ([vote w0 k, vote w1 k], [vote w0 k, vote w1 k]) := by
    have hres : ∀ y, resolutionTime A Φ (vote y k) < ⊤ := fun y => by
      rw [resolutionTime_vote h hf le_rfl]; exact max_lt (hvst y) hbst
    unfold voteViewList SAState.poolAt
    rw [ite_eq_right (by omega), Int.toNat_natCast, hpool]
    simp [hvst, hres]
  rw [hp]
  set L₁ := unlock sp A.locks Φ ((4 * (k + 1) : Nat) : Int) (k : Int)
    (View.ofLists ([vote w0 k, vote w1 k], [vote w0 k, vote w1 k]))
  have hL₁ : LocksLe L₁ k := unlock_le h hL _ _ _
  have htip₁ : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁ := fun hk1 =>
    mem_unlock h (htip hk1) hf le_rfl rfl (by rw [hs]; change k + 1 ≤ k + 2; omega)
      (lt_irrefl _) _
  have hanc : getAnchor sp { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int) = blk k := by
    refine h.getAnchor_eq hL₁ (jx_le k) ?_
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · right; obtain rfl : k = 0 := by omega
      rfl
    · left
      exact ⟨h.mem hf le_rfl, _, h.mem_liveLocks (htip₁ hk1) hf le_rfl rfl
        (by rw [hs]; change k + 1 ≤ k + 2; omega), rfl⟩
  refine ⟨L₁, _, rfl, ?_, hL₁, htip₁⟩
  change ghost sp _ _ _ _ (getAnchor sp { A with locks := L₁ } Φ _) = _
  rw [hanc]
  refine ghost_tip (fun B hB => ?_) _ _ _
  obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB.1
  exact ⟨m, hm, rfl⟩

/-- `ac_to_fg` with the tip `τ` locked and the previous slot reported: the source is the tip. -/
theorem acToFG_tick {A : SAState sp.n} {Φ : N.Frm} {f τ : Nat} {t : Time}
    (h : ChainFrame Φ f (jx τ) τ) (hj : A.restartTime = ⊥) (hst : sp.slot t = τ)
    (htip : (⟨(blk τ).root, τ, true, τ + 2⟩ : Lock) ∈ A.locks)
    {r : Nat} (hr : r < τ) (hrep : A.fgReported = (blk r).root) :
    (SA.acToFG sp A Φ t).1 = { A with fgReported := (blk τ).root } ∧
      (SA.acToFG sp A Φ t).2 = some (blk τ) := by
  have hf : f ≤ τ := le_trans h.fj (jx_le _)
  have htip' := h.mem hf (le_refl τ)
  have hd : deepest Φ (toFGCandidates sp A Φ t) = some (blk τ) := by
    apply h.deepest_eq (fun B hB => hB.1.1)
    · exact ⟨h.mem_viableTree htip' (jx_le _) le_rfl htip', _,
        h.mem_liveLocks htip hf le_rfl rfl (by rw [hst]; dsimp only; omega), rfl, rfl,
        by rw [hst]; dsimp only; omega⟩
    · intro B hB
      obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB.1.1
      exact ⟨m, hm, rfl⟩
  have hn : ¬ AncR Φ (blk τ) A.fgReported := by
    rintro ⟨R, hR, hr', ha⟩
    rw [hrep] at hr'
    obtain ⟨rfl, -, -⟩ := h.eq_of_root hR hr'
    have := h.le_of_anc ha; omega
  unfold SA.acToFG
  rw [ite_eq_right (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [hd]
  dsimp only
  rw [ite_eq_right hn]
  exact ⟨rfl, rfl⟩

/-- `ac_to_fg` returns nothing when every lock is at or below the reported block. -/
theorem acToFG_none {A : SAState sp.n} {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ)
    {b : Nat} (hL : LocksLe A.locks b) (hb : f ≤ b) (hbτ : b ≤ τ)
    (hrep : A.fgReported = (blk b).root) (t : Time) :
    (SA.acToFG sp A Φ t).1 = A ∧ (SA.acToFG sp A Φ t).2 = none := by
  unfold SA.acToFG
  split_ifs
  all_goals try exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · rename_i C hC
      obtain ⟨⟨hCv, l, hl, hlb, -, -⟩, -⟩ := deepest_mem hC
      have hCt := hCv.1
      obtain ⟨m, hm1, hm, rfl⟩ := h.eq_of_mem hCt
      obtain ⟨hlL, -, -⟩ := h.liveLocks_sub hl
      obtain ⟨m', hm', hr'⟩ := hL l hlL
      obtain ⟨-, hm'1, hm'2⟩ := h.eq_of_root hCt (hlb.symm.trans hr')
      have hmm : m = m' := blk_root_inj (hlb.symm.trans hr')
      rw [ite_eq_left ⟨blk b, h.mem hb hbτ, hrep.symm, h.anc hm1 (by omega) hbτ⟩]
      exact ⟨rfl, rfl⟩

theorem fin2_cases (i y : Fin sp.n) : i = y ∨ i = other y := by
  have key : ∀ i y : Fin sp.n, i = y ∨ i = other y := by unfold other; decide
  exact key i y

theorem equivocators_pair {y : Fin sp.n} {σ : Nat} :
    equivocators {v | v ∈ [vote y σ, vote (other y) σ]} = ∅ := by
  ext i
  simp only [equivocators, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, x', hx', hne, rfl, hval⟩
  apply hne
  have hoy := other_ne y
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;>
    first | rfl | (exfalso; rw [vote_val, vote_val] at hval; exact hoy hval.symm) |
      (exfalso; rw [vote_val, vote_val] at hval; exact hoy hval)

theorem voters_pair {y : Fin sp.n} {σ : Nat} :
    voters {v | v ∈ [vote y σ, vote (other y) σ]} = Set.univ := by
  ext i
  simp only [voters, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rcases fin2_cases i y with rfl | rfl
  · exact ⟨vote i σ, List.mem_cons_self .., rfl⟩
  · exact ⟨vote (other y) σ, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩

theorem ncard_univ_two : (Set.univ : Set (Fin sp.n)).ncard = 2 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The confirmation of slot `σ`** is the block of slot `σ`: both slot-`σ` votes are on it and
resolved before `t_σ + 2Δ`. -/
theorem getConfirmation_tick {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {A : SAState sp.n}
    {σ : Nat} (h1 : f ≤ σ) (h2 : σ ≤ τ) {y : Fin sp.n}
    (hpool : A.pool σ = [vote y σ, vote (other y) σ])
    (hres : ∀ x ∈ A.pool σ, resolutionTime A Φ x < ETime.of (sp.ts σ + 2 * sp.Δ)) :
    getConfirmation sp A Φ σ = some (blk σ) := by
  have hsup : ∀ m, f ≤ m → m ≤ σ → supporters Φ ⟨{v | v ∈ A.pool σ},
      {v | v ∈ A.pool σ ∧ resolutionTime A Φ v < ETime.of (sp.ts σ + 2 * sp.Δ)}⟩ σ (blk m) =
        Set.univ := by
    intro m hm1 hm2
    ext i
    simp only [supporters, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨by rw [hpool, equivocators_pair]; exact Set.notMem_empty i, ?_⟩
    have hx : ∀ x ∈ A.pool σ, AncR Φ (blk m) x.head := fun x hx => by
      rw [hpool] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;>
        exact ⟨blk σ, h.mem h1 h2, rfl, h.anc hm1 hm2 h2⟩
    rcases fin2_cases i y with rfl | rfl
    · have hm : vote i σ ∈ A.pool σ := by rw [hpool]; exact List.mem_cons_self ..
      exact ⟨vote i σ, ⟨hm, hres _ hm⟩, rfl, rfl, hx _ hm⟩
    · have hm : vote (other y) σ ∈ A.pool σ := by
        rw [hpool]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      exact ⟨vote (other y) σ, ⟨hm, hres _ hm⟩, rfl, rfl, hx _ hm⟩
  unfold getConfirmation
  apply h.deepest_eq (fun B hB => hB.1)
  · refine ⟨h.mem h1 h2, by rw [h.F]; exact h.anc le_rfl h1 h2, ?_⟩
    rw [hpool, voters_pair, ncard_univ_two]
    unfold confirmationScore
    dsimp only
    rw [hsup σ h1 le_rfl, ncard_univ_two]; omega
  · rintro B ⟨hB, -, hsc⟩
    obtain ⟨m, hm1, hm2, rfl⟩ := h.eq_of_mem hB
    refine ⟨m, ?_, rfl⟩
    by_contra hlt
    have h0 : supporters Φ ⟨{v | v ∈ A.pool σ},
        {v | v ∈ A.pool σ ∧ resolutionTime A Φ v < ETime.of (sp.ts σ + 2 * sp.Δ)}⟩ σ (blk m) =
          ∅ := by
      ext i
      simp only [supporters, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        not_exists]
      intro _ x hx _ _ ⟨R, hR, hr, ha⟩
      rw [hpool] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx.1 with rfl | rfl <;>
      · obtain ⟨rfl, -, -⟩ := h.eq_of_root hR hr
        have := h.le_of_anc ha; omega
    unfold confirmationScore at hsc
    dsimp only at hsc
    rw [h0, Set.ncard_empty] at hsc
    omega

/-- **The confirmation update** of slot `σ` saves the block of slot `σ`, keeps the record (which
is at or above it) and the stamps, and adds locks on blocks of the tree. -/
theorem updateConfirmation_tick {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ)
    {A : SAState sp.n} {σ : Nat} {t : Time} (hC : getConfirmation sp A Φ σ = some (blk σ))
    {b : Nat} (hσb : σ ≤ b) (hb : b ≤ τ) (hσf : f ≤ σ)
    (hlat : A.latestConfirmed = (blk b).root) :
    Same A (updateConfirmation sp A Φ t σ) ∧
      (updateConfirmation sp A Φ t σ).saved = Function.update A.saved σ (some (blk σ).root) ∧
      (updateConfirmation sp A Φ t σ).latestConfirmed = A.latestConfirmed ∧
      ∃ N : Set (Nat × Bool × Nat), (∀ p ∈ N, ∃ B ∈ Φ.tree, p.1 = B.root) ∧
        (updateConfirmation sp A Φ t σ).locks = addLocks sp A.locks Φ t σ N := by
  have hanc : AncR Φ (blk σ) (blk b).root :=
    ⟨blk b, h.mem (by omega) hb, rfl, h.anc hσf hσb hb⟩
  unfold updateConfirmation
  rw [hC]
  dsimp only
  have hul : updateLatestConfirmed sp
      { A with saved := Function.update A.saved σ (some (blk σ).root) } Φ (blk σ) =
      { A with saved := Function.update A.saved σ (some (blk σ).root) } := by
    unfold updateLatestConfirmed; rw [ite_eq_left (by dsimp only; rw [hlat]; exact hanc)]
  simp only [Option.map_some, hul, ite_self]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, trivial, _, ?_, rfl⟩
  rintro p (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
  · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩
  · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩

end Consensus.Goldilocks.Witness.TwoRun

end
