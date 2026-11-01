module
public import AvailableChainFGSA.Proofs.NamedStore
public import Mathlib.Data.Finset.Card -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Filtering cannot resolve an ambiguous identifier. -/
theorem actView_resolvedHead {n : Nat} (st : State n) (o : GridCO.Wire n .root) :
    GridCO.resolvedHead? (actView st) o =
      (GridCO.resolvedHead? st.base o).filter (activeCompatible st) := by
  unfold GridCO.resolvedHead?
  change ((GridCO.headTarget? o).bind fun r =>
      (Block.findByRoot? (GridCO.resolutionTree (actView st)) r).bind fun B =>
        if B ∈ (actView st).blocks then some B else none) =
    ((GridCO.headTarget? o).bind fun r =>
      (Block.findByRoot? (GridCO.resolutionTree st.base) r).bind fun B =>
        if B ∈ st.base.blocks then some B else none).filter (activeCompatible st)
  rw [actView_resolutionTree]
  cases ht : GridCO.headTarget? o with
  | none => rfl
  | some r =>
      change ((Block.findByRoot? (GridCO.resolutionTree st.base) r).bind fun B =>
        if B ∈ (actView st).blocks then some B else none) =
        ((Block.findByRoot? (GridCO.resolutionTree st.base) r).bind fun B =>
          if B ∈ st.base.blocks then some B else none).filter (activeCompatible st)
      cases hl : Block.findByRoot? (GridCO.resolutionTree st.base) r with
      | none => rfl
      | some B =>
          change (if B ∈ (actView st).blocks then some B else none) =
            (if B ∈ st.base.blocks then some B else none).filter (activeCompatible st)
          by_cases hm : B ∈ st.base.blocks <;> cases hc : activeCompatible st B <;>
            simp [actView, hm, hc, Option.filter]

/-- [ROOT-DIGEST-2 W1; DC resolution_time] A resolved active vote is cumulatively resolved. -/
theorem active_resolvedBefore_base {n : Nat} (st : State n) (o : GridCO.Wire n .root)
    (t : Time) (h : GridCO.resolvedBefore (actView st) o t = true) :
    GridCO.resolvedBefore st.base o t = true := by
  unfold GridCO.resolvedBefore at h ⊢
  rw [actView_resolvedHead] at h
  cases hb : GridCO.resolvedHead? st.base o with
  | none => simp [hb] at h
  | some B =>
      cases hc : activeCompatible st B <;> simp [hb, hc, Option.filter] at h
      change (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
        decide (GridCO.stampVote st.base o < t) &&
        decide (GridCO.stampBlock st.base B < t)) = true
      have hv : GridCO.stampVote (actView st) o = GridCO.stampVote st.base o := rfl
      have hb' : GridCO.stampBlock (actView st) B = GridCO.stampBlock st.base B := rfl
      rw [hv, hb'] at h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Resolution returns an active stored body. -/
theorem resolvedHead_mem {n : Nat} (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    {B : Block} (h : GridCO.resolvedHead? st o = some B) : B ∈ st.blocks := by
  unfold GridCO.resolvedHead? at h
  change ((GridCO.headTarget? o).bind fun r =>
    (GridCO.resolveTarget .root (GridCO.resolutionTree st) r).bind fun C =>
      if C ∈ st.blocks then some C else none) = some B at h
  cases ht : GridCO.headTarget? o with
  | none => simp [ht] at h
  | some r =>
      rw [ht] at h
      change ((GridCO.resolveTarget .root (GridCO.resolutionTree st) r).bind fun C =>
        if C ∈ st.blocks then some C else none) = some B at h
      cases hr : GridCO.resolveTarget .root (GridCO.resolutionTree st) r with
      | none => simp [hr] at h
      | some C =>
          rw [hr] at h
          change (if C ∈ st.blocks then some C else none) = some B at h
          split at h
          · cases h
            assumption
          · contradiction


private def namedReleaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B)))).toFinset

private theorem named_release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) : GridCO.releaseCount q v s B = (namedReleaseSeats q v s B).card := by
  have hp : (fun o : GridCO.Wire n .root => match GridCO.resolvedHead? v o with
      | some C => !Block.compatible C B
      | none => false) = (fun o => (GridCO.resolvedHead? v o).any
        (fun C => !Block.compatible C B)) := by
    funext o
    cases GridCO.resolvedHead? v o <;> rfl
  unfold GridCO.releaseCount namedReleaseSeats
  dsimp only
  refine Eq.trans ?_ (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup (α := Fin n) _))).symm
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext k
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ k).any f)
  exact hp

private theorem named_release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n .root)
    (s : Slot) (B : Block) (k : Fin n) : k ∈ namedReleaseSeats q v s B ↔
      GridCO.equivocates (GridCO.votesAt v s) k = false ∧
      ∃ o ∈ GridCO.votesAt v s,
        GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true ∧
        GridCO.headSeat? o = some k ∧
        (GridCO.resolvedHead? v o).any (fun C => !Block.compatible C B) = true := by
  dsimp only [namedReleaseSeats]
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq]
  constructor
  · rintro ⟨_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact ⟨he, o, ho, hr, hk, hc⟩
  · rintro ⟨he, o, ho, hr, hk, hc⟩
    refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hk⟩)

/-- [ROOT-DIGEST-2 W1; DC resolution_time] Active filtering cannot increase release counts. -/
theorem active_releaseCount_le (p : Params) (st : State p.n) (s : Slot) (B : Block) :
    GridCO.releaseCount p.toParams.engine (actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B := by
  rw [named_release_card, named_release_card]
  apply Finset.card_le_card
  intro k hk
  obtain ⟨he, o, ho, hr, hs, hc⟩ := (named_release_mem _ _ _ _ _).mp hk
  refine (named_release_mem _ _ _ _ _).mpr
    ⟨he, o, ho, active_resolvedBefore_base st o _ hr, hs, ?_⟩
  rw [actView_resolvedHead] at hc
  cases hb : GridCO.resolvedHead? st.base o with
  | none => simp [hb, Option.filter] at hc
  | some C =>
      cases ha : activeCompatible st C <;> simp [hb, ha, Option.filter] at hc
      simpa [hb] using hc

/-- [ROOT-DIGEST-2 W1; DC resolution_time] Active votes cannot release an ancestor of F. -/
theorem active_releaseCount_zero (p : Params) (st : State p.n) (s : Slot) {B : Block}
    (hB : Block.Preceq B (eraseFG st.fg.F)) :
    GridCO.releaseCount p.toParams.engine (actView st) s B = 0 := by
  rw [named_release_card, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨_, o, _, _, _, hc⟩ := (named_release_mem _ _ _ _ _).mp hk
  cases hh : GridCO.resolvedHead? (actView st) o with
  | none => simp [hh] at hc
  | some C =>
      have hm := resolvedHead_mem (actView st) o hh
      have hCF : Block.Compatible C (eraseFG st.fg.F) :=
        (List.mem_filter.mp hm).2
      have hCB : Block.Compatible C B := by
        rcases Bool.or_eq_true_iff.mp hCF with hCF | hFC
        · exact block_compatible_of_common hCF hB
        · exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_trans hB hFC))
      change Block.compatible C B = true at hCB
      simp [hh, hCB] at hc

end AvailableChain.FGSA
end
