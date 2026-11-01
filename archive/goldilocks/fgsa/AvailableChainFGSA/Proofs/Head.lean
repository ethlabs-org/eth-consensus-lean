module
public import AvailableChainFGSA.Proofs.StoreLaws -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.StoreInv

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! Store-level walk wrappers (T7.W; plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` §1b). Each statement mentions
only model-level constants; the Grid CO walk lemmas are called with
`GridCO.slowLeasePolicy`, as in `fgHead_stored`. -/

/-! ### (W1) The walk result is stored -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; T7.W] The erased list of a block set is a sublist of
the base list. -/
theorem erasedList_subset {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) :
    erasedList st X ⊆ st.base.blocks :=
  fun _ hb => (List.mem_filter.1 hb).1

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1074–1107; T7.W (W1)] The walk result is stored when its
tree is in
the base list, for every score and eligibility (the vote lists `raw` and
`support`). -/
theorem headInTree_stored (p : Params) (st : State p.n) (h : CStoreInv p st)
    (tree : List Block) (htree : tree ⊆ st.base.blocks)
    (raw support : List (GridCO.Wire p.n .root)) :
    headInTree p st tree raw support ∈ st.base.blocks := by
  unfold headInTree GridCO.ghost
  dsimp only
  rcases @GridCO.ghostWalk_mem GridCO.slowLeasePolicy _ _ _ _ (liveRoot p st) with he | hm
  · rw [he]
    exact liveRoot_stored p st h
  · exact htree (List.mem_eraseDups.1 hm)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1109–1114; T7.W (W1)] `get_head` is stored, for every
vote list. -/
theorem getHead_stored (p : Params) (st : State p.n) (h : CStoreInv p st)
    (raw support : List (GridCO.Wire p.n .root)) :
    getHead p st raw support ∈ st.base.blocks :=
  headInTree_stored p st h _ (erasedList_subset st _) raw support

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1276–1302; T7.W; G-walk MINOR-1] The HEAD vote at slot 0
is genesis
(for the slot-0 branch of T7.12). -/
theorem headVote_zero (p : Params) (st : State p.n) : headVote p st 0 = .genesis := by
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1276–1302; T7.W (W1)] The HEAD vote is stored, at every
slot. -/
theorem headVote_stored (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot) :
    headVote p st s ∈ st.base.blocks := by
  unfold headVote
  split
  · exact (h.baseTree _).2 ⟨.genesis, h.fg.gen, rfl⟩
  · exact headInTree_stored p st h _ (erasedList_subset st _) _ _

/-! ### (W2) The walk result extends the live root, and F -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1074–1107; T7.W (W2)] The walk result extends the live
root, for every
tree, score and eligibility. -/
theorem liveRoot_preceq_headInTree (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) :
    Block.Preceq (liveRoot p st) (headInTree p st tree raw support) :=
  @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 648–655; T7.W (W2)] F is an ancestor of the live root: Z
is F or J
(`F ⪯ J`), and every live lease target is in the full filtered tree, above F. -/
theorem F_preceq_liveRoot (p : Params) (st : State p.n) (h : CStoreInv p st) :
    Block.Preceq (eraseFG st.fg.F) (liveRoot p st) := by
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    apply eraseFG_preceq
    unfold Controls.Z
    split
    · exact h.fg.FJ
    · exact KitFG.preceq_refl _
  · obtain ⟨row, -, hrow⟩ := List.mem_filterMap.1 hm
    split at hrow
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨B, hB, hBe⟩ := hc.2
      rw [← Option.some.inj hrow, ← hBe]
      exact eraseFG_preceq ((KitFG.mem_filteredFromView (heightView p) _ _ B).1 hB).2.1
    · exact absurd hrow (by simp)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1074–1107; T7.W (W2)] The walk result extends F, for
every tree, score
and eligibility. -/
theorem F_preceq_headInTree (p : Params) (st : State p.n) (h : CStoreInv p st)
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    Block.Preceq (eraseFG st.fg.F) (headInTree p st tree raw support) :=
  block_preceq_trans (F_preceq_liveRoot p st h) (liveRoot_preceq_headInTree p st tree raw support)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1109–1114; T7.W (W2)] An ancestor of F is an ancestor of
`get_head`. -/
theorem preceq_getHead_of_preceq_F (p : Params) (st : State p.n) (h : CStoreInv p st)
    {B : Block} (hB : Block.Preceq B (eraseFG st.fg.F)) (raw support : List (GridCO.Wire p.n .root))
      :
    Block.Preceq B (getHead p st raw support) :=
  block_preceq_trans hB (F_preceq_headInTree p st h _ raw support)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1318–1323; T7.W (W2)] An ancestor of F is an ancestor of
the finality
head. -/
theorem preceq_fgHead_of_preceq_F (p : Params) (st : State p.n) (h : CStoreInv p st)
    {B : Block} (hB : Block.Preceq B (eraseFG st.fg.F)) :
    Block.Preceq B (fgHead p st) :=
  preceq_getHead_of_preceq_F p st h hB _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 1276–1302; T7.W (W2); Astra r11 m1] An ancestor of F is
an ancestor of
the HEAD vote at a slot `s > 0`. At `s = 0` the HEAD vote is genesis, and a
store with `CStoreInv` can have F ≠ genesis there (`clock pT stA 1`). -/
theorem preceq_headVote_of_preceq_F (p : Params) (st : State p.n) (h : CStoreInv p st)
    {B : Block} (hB : Block.Preceq B (eraseFG st.fg.F)) {s : Slot} (hs : 0 < s) :
    Block.Preceq B (headVote p st s) := by
  unfold headVote
  rw [ite_eq_right (Nat.pos_iff_ne_zero.1 hs)]
  exact block_preceq_trans hB (F_preceq_headInTree p st h _ _ _)

end AvailableChain.FGSA
end
