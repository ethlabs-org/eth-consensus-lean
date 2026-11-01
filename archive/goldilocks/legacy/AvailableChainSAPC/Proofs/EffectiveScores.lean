module
public import AvailableChainSAPC.Proofs.Floor

@[expose] public section
namespace AvailableChain.SAPC

/-- One exact resolved target or two-copy evidence makes a seat score.
This is independent of receipt order and the complete HEAD ack field. -/
theorem scoreSeat_of_exact_or_equivocation {n : Nat} (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) (b : Block)
    (hslot : b.slot ≤ r) (hb : b ∈ tree) (i : Fin n)
    (hrec : (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ support ∧
        (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ raw ∨
      GridCO.equivocates raw i = true) :
    i ∈ GridCO.scoreSeats tree raw support b := by
  apply Finset.mem_filter.mpr
  rcases hrec with ⟨hsp, hraw⟩ | he
  · constructor
    · exact List.mem_toFinset.mpr (List.mem_dedup.mpr
        (List.mem_filterMap.mpr ⟨_, hraw, rfl⟩))
    · apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨⟨.seat r i, .head b⟩, List.mem_filter.mpr ⟨hsp, by simp [GridCO.headSeat?]⟩, ?_⟩
      simpa [GridCO.headTarget?, GridCO.headLabel?, hb, hslot] using!
        GridCO.block_preceq_self b
  · have he' := he
    constructor
    · have hlen : 0 < (GridCO.seatVotes raw i).eraseDups.length := by
        have := of_decide_eq_true he
        omega
      obtain ⟨o, ho⟩ := List.length_pos_iff_exists_mem.mp hlen
      obtain ⟨ho, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp ho)
      exact List.mem_toFinset.mpr (List.mem_dedup.mpr
        (List.mem_filterMap.mpr ⟨o, ho, by simpa using hi⟩))
    · exact Bool.or_eq_true_iff.mpr (Or.inl he')

/-- A non-equivocating seat has one base key in a raw view. -/
theorem non_equivocating_unique {n : Nat} (raw : List (GridCO.Wire n)) (i : Fin n)
    (h : GridCO.equivocates raw i = false) (a b : GridCO.Wire n)
    (ha : a ∈ GridCO.seatVotes raw i) (hb : b ∈ GridCO.seatVotes raw i) : a = b := by
  have hlen : (GridCO.seatVotes raw i).eraseDups.length ≤ 1 := by
    have := of_decide_eq_false h
    omega
  have heq : (GridCO.seatVotes raw i).eraseDups.toFinset =
      (GridCO.seatVotes raw i).toFinset := by ext o; simp
  have hcard : (GridCO.seatVotes raw i).toFinset.card ≤ 1 := by
    rw [← heq, List.toFinset_card_of_nodup (GridCO.eraseDups_nodup _)]
    exact hlen
  exact Finset.card_le_one.mp hcard a (List.mem_toFinset.mpr ha) b (List.mem_toFinset.mpr hb)

/-- A non-equivocating scoring seat supplies a resolved declared HEAD. -/
theorem scoreSeat_witness {n : Nat} (tree : List Block) (raw support : List (GridCO.Wire n))
    (b : Block) (i : Fin n) (hi : i ∈ GridCO.scoreSeats tree raw support b)
    (he : GridCO.equivocates raw i = false) :
    ∃ o target, o ∈ GridCO.seatVotes support i ∧ GridCO.headTarget? o = some target ∧
      target ∈ tree ∧ target.slot ≤ (GridCO.headLabel? o).getD 0 ∧ Block.Preceq b target := by
  have hs := (Finset.mem_filter.mp hi).2
  simp only [he, Bool.false_or] at hs
  obtain ⟨o, ho, ht⟩ := List.any_eq_true.mp hs
  cases hh : GridCO.headTarget? o with
  | none => simp [hh] at ht
  | some target =>
      simp only [hh, Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨o, target, ho, hh, ht.1.1, ht.1.2, ht.2⟩

/-- Only detected equivocators can score for two conflicting branches.
The support-subset premise is essential for proposal-carried metadata. -/
theorem conflicting_score_intersection {n : Nat} (tree : List Block)
    (raw support : List (GridCO.Wire n)) (hsub : support ⊆ raw) (a b : Block)
    (hconflict : Block.compatible a b = false) :
    GridCO.scoreSeats tree raw support a ∩ GridCO.scoreSeats tree raw support b ⊆
      detectedSeats raw := by
  intro i hi
  obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hi
  have hraw := (Finset.mem_filter.mp ha).1
  apply Finset.mem_filter.mpr
  refine ⟨by simpa only [GridCO.seats, List.mem_toFinset, List.mem_dedup] using hraw, ?_⟩
  by_contra hn
  have he : GridCO.equivocates raw i = false := Bool.eq_false_of_not_eq_true hn
  obtain ⟨x, X, hx, hX, _, _, haX⟩ := scoreSeat_witness tree raw support a i ha he
  obtain ⟨y, Y, hy, hY, _, _, hbY⟩ := scoreSeat_witness tree raw support b i hb he
  have hxy : x = y := non_equivocating_unique raw i he x y
    (List.mem_filter.mpr ⟨hsub (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩)
    (List.mem_filter.mpr ⟨hsub (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2⟩)
  have htarget : X = Y := Option.some.inj (hX.symm.trans (hxy ▸ hY))
  subst Y
  have hc := GridCO.ancestors_compatible a b X haX hbY
  change Block.compatible a b = true at hc
  rw [hconflict] at hc
  contradiction

/-- The two branch scores can overlap only in the detected fault set. -/
theorem conflicting_scores_bound {n : Nat} (tree : List Block)
    (raw support : List (GridCO.Wire n)) (hsub : support ⊆ raw) (a b : Block)
    (hconflict : Block.compatible a b = false) :
    GridCO.goldfishScore tree raw support a + GridCO.goldfishScore tree raw support b ≤
      n + (detectedSeats raw).card := by
  rw [GridCO.goldfishScore_eq_card, GridCO.goldfishScore_eq_card]
  have hi := Finset.card_le_card (conflicting_score_intersection tree raw support hsub a b
    hconflict)
  have hu : (GridCO.scoreSeats tree raw support a ∪
      GridCO.scoreSeats tree raw support b).card ≤ n := by
    simpa using Finset.card_le_univ (GridCO.scoreSeats tree raw support a ∪
      GridCO.scoreSeats tree raw support b)
  have he := Finset.card_union_add_card_inter (GridCO.scoreSeats tree raw support a)
    (GridCO.scoreSeats tree raw support b)
  omega

/-- In active mode q support strictly beats any conflicting score. The
actual fault count is unrestricted; only the live archive test is used. -/
theorem active_quorum_dominates (p : Params) (st : State p.n) (r : Slot)
    (raw support : List (GridCO.Wire p.n)) (hsub : support ⊆ raw)
    (ha : ∀ o ∈ raw, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (hl : ∀ o ∈ raw, GridCO.headLabel? o = some r)
    (hactive : capBroken p st = false) (a b : Block)
    (hq : pcQuorum p ≤ GridCO.goldfishScore st.base.blocks raw support a)
    (hc : Block.compatible a b = false) :
    GridCO.goldfishScore st.base.blocks raw support b <
      GridCO.goldfishScore st.base.blocks raw support a := by
  have hsum := conflicting_scores_bound st.base.blocks raw support hsub a b hc
  have he := active_view_count_le p st r raw ha hl hactive
  have hqf := (cap_bounds p).2.2
  omega

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The valid engine supplies the archive and declared-support premises
for the active merged-view comparison. A quorum score is the remaining
transfer input; this theorem does not assert its timely delivery. -/
theorem active_voter_quorum_dominates {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (v : V) (s : Slot) (a b : Block)
    (ha : capBroken p (Run.stateBefore (sapc p) rho index v) = false)
    (hq : pcQuorum p ≤ GridCO.goldfishScore (Run.stateBefore (sapc p) rho index v).base.blocks
      (GridCO.voterView p.engine (Run.stateBefore (sapc p) rho index v).base s)
      (GridCO.voterSupportView p.engine (Run.stateBefore (sapc p) rho index v).base s) a)
    (hc : Block.compatible a b = false) :
    let st := Run.stateBefore (sapc p) rho index v
    GridCO.goldfishScore st.base.blocks (GridCO.voterView p.engine st.base s)
      (GridCO.voterSupportView p.engine st.base s) b <
    GridCO.goldfishScore st.base.blocks (GridCO.voterView p.engine st.base s)
      (GridCO.voterSupportView p.engine st.base s) a := by
  apply active_quorum_dominates p _ (s - 1) _ _
    (voterSupport_subset_before p E rho hx index v s)
  · exact voterView_archived p _ (baseArchived_at_fold p _ v)
      (frozenViewsStored_at_fold p _ v) (proposalViewsArchived_at_fold p _ v) s
  · exact voterView_label p _ (frozenViewsStored_at_fold p _ v) s
  · exact ha
  · exact hq
  · exact hc

/-- The ordinary walk follows an active quorum on a complete path.
The shared GHOST proof supplies the walk; the archive bound supplies
strict dominance even when the actual fault count is above f. -/
theorem active_quorum_walk_covers (p : Params) (st : State p.n)
    (tree : List Block) (raw support : List (GridCO.Wire p.n)) (label current : Slot)
    (hsub : support ⊆ raw)
    (ha : ∀ o ∈ raw, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (hl : ∀ o ∈ raw, GridCO.headLabel? o = some label)
    (hactive : capBroken p st = false) (b : Block)
    (hq : pcQuorum p ≤ GridCO.goldfishScore st.base.blocks raw support b)
    (hpath : ∀ a, a ≠ .genesis → Block.Preceq a b → a ∈ tree) :
    Block.Preceq b (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishEligible st.base.blocks raw support current)) := by
  have hn : GridCO.voterCount raw ≤ p.n := by
    unfold GridCO.voterCount
    rw [← List.toFinset_card_of_nodup
      (show (GridCO.seats p.n raw).Nodup from List.nodup_dedup _)]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin p.n)
  have hmajority := (quorum_bounds p).2.2
  apply GridCO.ghost_covers_of_path_dominance tree _ _ .genesis b
    (Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))) hpath
  · intro a _ hab
    have hm := GridCO.goldfishScore_prefix_mono st.base.blocks raw support a b hab
    exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by omega)))
  · intro a _ hab d _ hparent _ hne
    have hconf := GridCO.conflict_mono_descendant a b d hab
      (GridCO.siblings_incompatible d a hparent hne)
    have hconf' : Block.compatible b d = false := by
      simpa [Block.compatible, Bool.or_comm] using hconf
    have hdom := active_quorum_dominates p st label raw support hsub ha hl hactive b d hq hconf'
    exact hdom.trans_le (GridCO.goldfishScore_prefix_mono st.base.blocks raw support a b hab)

/-- An active quorum drives F4 through its target, for any selected PC.
Only compatibility of the mandatory finite root remains for the joint
invariant. No separate ordinary-walk or path premise is needed. -/
theorem active_voter_quorum_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (v : V) (r : Slot) (c : Option (PC p.n)) (b : Block)
    (ha : capBroken p (Run.stateBefore (sapc p) rho index v) = false)
    (hq : pcQuorum p ≤ GridCO.goldfishScore (Run.stateBefore (sapc p) rho index v).base.blocks
      (GridCO.voterView p.engine (Run.stateBefore (sapc p) rho index v).base r)
      (GridCO.voterSupportView p.engine (Run.stateBefore (sapc p) rho index v).base r) b)
    (hr : Block.Compatible (GridCO.liveRoot (Run.stateBefore (sapc p) rho index v).base) b) :
    let st := Run.stateBefore (sapc p) rho index v
    Block.Preceq b (choice p st (activeVoterTree p st r c)
      (GridCO.voterView p.engine st.base r) (GridCO.voterSupportView p.engine st.base r) r c) := by
  dsimp only
  by_cases hg : b = .genesis
  · rw [hg]; exact GridCO.genesis_prefix _
  have hqf : pcFaultCap p < pcQuorum p := by
    have := cap_bounds p
    have := quorum_bounds p
    omega
  have hpath : ∀ a, a ≠ .genesis → Block.Preceq a b →
      a ∈ activeVoterTree p (Run.stateBefore (sapc p) rho index v) r c := by
    intro a hn hab
    apply active_voter_score_path p (rho.events.take index) v r c a hn ha
    exact hqf.trans_le (hq.trans (GridCO.goldfishScore_prefix_mono _ _ _ a b hab))
  apply choice_covers_of_ordinary_floor p _ _ _ _ r c b ha
    (activeVoterTree_subset p _ r c (hpath b hg (GridCO.block_preceq_self b))) hg
  · exact active_quorum_walk_covers p _ _ _ _ (r - 1) r
      (voterSupport_subset_before p E rho hx index v r)
      (voterView_archived p _ (baseArchived_at_fold p _ v)
        (frozenViewsStored_at_fold p _ v) (proposalViewsArchived_at_fold p _ v) r)
      (voterView_label p _ (frozenViewsStored_at_fold p _ v) r) ha b hq hpath
  · exact hqf.trans_le hq
  · exact hr

end AvailableChain.SAPC
end
