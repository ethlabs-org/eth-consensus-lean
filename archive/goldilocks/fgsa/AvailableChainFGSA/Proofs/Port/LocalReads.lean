module
public import AvailableChainFGSA.Proofs.Port.Support

public section

namespace AvailableChain.FGSA.Next

/-- Feeds the Next support readers in place of `actView_resolvedHead`.
Pin the cumulative domain before filtering held blocks; an ambiguous root
cannot become resolved when a block is removed. -/
theorem port_resolvedHead_filter {n : Nat} (v : GridCO.State n .root)
    (keep : Block → Bool) (o : GridCO.Wire n .root) :
    GridCO.resolvedHead? { v with
      blocks := v.blocks.filter keep
      headDomain := some (GridCO.resolutionTree v) } o =
    (GridCO.resolvedHead? v o).filter keep := by
  unfold GridCO.resolvedHead?
  have hd : GridCO.resolutionTree { v with
      blocks := v.blocks.filter keep
      headDomain := some (GridCO.resolutionTree v) } = GridCO.resolutionTree v := rfl
  rw [hd]
  cases ht : GridCO.headTarget? o with
  | none => rfl
  | some r =>
    cases hr : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
    | none => simp [hr]
    | some H =>
      by_cases hm : H ∈ v.blocks <;> cases hk : keep H <;> simp [hr, hm, hk, Option.filter]

/-- Feeds `active_resolvedBefore_base` and the frozen/early read adapters.
The shared GridCO implementation is unchanged; timestamps are preserved. -/
theorem port_resolvedBefore_filter {n : Nat} (v : GridCO.State n .root)
    (keep : Block → Bool) (o : GridCO.Wire n .root) (cut : Time) :
    GridCO.resolvedBefore { v with
      blocks := v.blocks.filter keep
      headDomain := some (GridCO.resolutionTree v) } o cut =
    (GridCO.resolvedBefore v o cut && (GridCO.resolvedHead? v o).any keep) := by
  unfold GridCO.resolvedBefore
  rw [port_resolvedHead_filter]
  cases hr : GridCO.resolvedHead? v o with
  | none => rfl
  | some H =>
    cases hk : keep H with
    | false => simp [Option.filter, hk]
    | true =>
      simp only [Option.filter, hk, ↓reduceIte, Option.any_some, Bool.and_true]
      rfl

/-- Feeds the spec-facing proposer resolver: prefix filtering the active view
is the same as prefix filtering the cumulative resolver. -/
theorem port_resolvedHead_above_F {n : Nat} (st : State n) (o : GridCO.Wire n .root) :
    (GridCO.resolvedHead? (actView st) o).filter (Block.preceq (eraseFG st.fg.F)) =
    (GridCO.resolvedHead? st.base o).filter (Block.preceq (eraseFG st.fg.F)) := by
  rw [actView_resolvedHead]
  cases hr : GridCO.resolvedHead? st.base o with
  | none => rfl
  | some H =>
    by_cases hF : Block.Preceq (eraseFG st.fg.F) H
    · have hc : activeCompatible st H = true := by
        change (Block.preceq H (eraseFG st.fg.F) || Block.preceq (eraseFG st.fg.F) H) = true
        exact Bool.or_eq_true_iff.mpr (Or.inr hF)
      simp [Option.filter, hc]
    · simp only [Block.Preceq] at hF
      cases hc : activeCompatible st H <;> simp [Option.filter, hc, hF]

/-- Feeds `headSupportNext` and the spec tree resolver. Erased tree membership
is tested after cumulative resolution, with no change to GridCO. -/
theorem port_resolvedHead_tree (p : Params) (st : State p.n) (o : GridCO.Wire p.n .root) :
    GridCO.resolvedHead? { st.base with
      blocks := erasedList st (tree p st)
      headDomain := some (GridCO.resolutionTree st.base) } o =
    (GridCO.resolvedHead? st.base o).filter
      (fun H => decide (∃ B ∈ tree p st, eraseFG B = H)) :=
  port_resolvedHead_filter st.base _ o

/-- Feeds the frozen support and early clean-support adapters for Next tree
reads. Receipt cutoffs stay strict and use the same stored timestamps. -/
theorem port_resolvedBefore_tree (p : Params) (st : State p.n)
    (o : GridCO.Wire p.n .root) (cut : Time) :
    GridCO.resolvedBefore { st.base with
      blocks := erasedList st (tree p st)
      headDomain := some (GridCO.resolutionTree st.base) } o cut =
    (GridCO.resolvedBefore st.base o cut && (GridCO.resolvedHead? st.base o).any
      (fun H => decide (∃ B ∈ tree p st, eraseFG B = H))) :=
  port_resolvedBefore_filter st.base _ o cut

/-- Feeds `fgSourceNext`: compare stored fast sets only after projection onto
the retained tree. No assertion is made about entries below F. -/
theorem port_fastSet_projection (F : Block) (xs ys : List Block)
    (h : ∀ B, Block.Preceq F B → (B ∈ xs ↔ B ∈ ys)) :
    (xs.filter (Block.preceq F)).toFinset = (ys.filter (Block.preceq F)).toFinset := by
  ext B
  simp only [List.mem_toFinset, List.mem_filter]
  constructor <;> rintro ⟨hm, hF⟩
  · exact ⟨(h B hF).mp hm, hF⟩
  · exact ⟨(h B hF).mpr hm, hF⟩

/-- Feeds `leaseOf` and `liveRootNext`: discarding lease rows below F preserves
the first deadline of each retained target, without equating stored rows. -/
theorem port_lease_projection {n : Nat} (st : State n) (F B : Block)
    (hFB : Block.Preceq F B) :
    leaseOf { st with base := { st.base with
      obligations := st.base.obligations.filter (fun row => Block.preceq F row.1) } } B =
    leaseOf st B := by
  unfold leaseOf
  congr 1
  change (st.base.obligations.filter (fun row => Block.preceq F row.1)).find?
    (fun row => row.1 == B) = st.base.obligations.find? (fun row => row.1 == B)
  change Block.preceq F B = true at hFB
  induction st.base.obligations with
  | nil => rfl
  | cons row rows ih =>
    by_cases he : row.1 = B
    · simp [List.filter, List.find?, he, hFB]
    · have hn : (row.1 == B) = false := beq_eq_false_iff_ne.mpr he
      cases hf : Block.preceq F row.1 <;> simp [List.filter, List.find?, hf, hn, ih]

/-- Feeds `Release`: the concrete prefix projection of the active view has
exactly the canonical release count for a compatible retained target. -/
theorem port_active_release_projection (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hB : Block.Compatible (eraseFG st.fg.F) B) :
    GridCO.releaseCount p.toParams.engine { actView st with
      blocks := (actView st).blocks.filter (Block.preceq (eraseFG st.fg.F))
      headDomain := some (GridCO.resolutionTree (actView st)) } s B =
    GridCO.releaseCount p.toParams.engine (actView st) s B := by
  apply port_releaseCount_eq p.toParams.engine (actView st)
    { actView st with
      blocks := (actView st).blocks.filter (Block.preceq (eraseFG st.fg.F))
      headDomain := some (GridCO.resolutionTree (actView st)) } s (eraseFG st.fg.F) B hB rfl
  · exact port_resolvedHead_filter (actView st) _
  · intro o
    exact port_resolvedBefore_filter (actView st) _ o _
  · intro o _ H hr
    exact (List.mem_filter.mp (resolvedHead_mem (actView st) o hr)).2

/-- Feeds `fastSet`/`gateStep`: the computed fast set agrees with the new clean
support score after projection above F. The internal set below F can differ. -/
theorem port_fastSet_filter (p : Params) (v : GridCO.State p.n .root) (F : Block)
    (s : Slot)
    (hc : ∀ i, GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) i = false) :
    let kept := (GridCO.cleanSupport p.toParams.engine v s).filter
      (fun o => (GridCO.resolvedHead? v o).any (Block.preceq F))
    (fastSet p F v s).filter (Block.preceq F) =
      match SA.Root.confirmationFrom p.toParams F v s with
      | none => []
      | some H =>
        if v.obligations.any (fun row => !Block.compatible row.1 H) then [] else
          v.blocks.filter (fun B => (B != Block.genesis && Block.preceq B H &&
            decide (SA.releaseThreshold p.toParams ≤ GridCO.goldfishScoreOn
              (GridCO.resolutionTree v) v.blocks kept kept B)) && Block.preceq F B) := by
  dsimp only
  change (match SA.Root.confirmationFrom p.toParams F v s with
    | none => ([] : List Block)
    | some H => if v.obligations.any (fun row => !Block.compatible row.1 H) then [] else
      v.blocks.filter (fun B => B != Block.genesis && Block.preceq B H &&
        decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s B))).filter
          (Block.preceq F) = _
  cases hh : SA.Root.confirmationFrom p.toParams F v s with
  | none => rfl
  | some H =>
    dsimp only
    split
    · rfl
    · rw [List.filter_filter]
      apply List.filter_congr
      intro B _
      by_cases hFB : Block.Preceq F B
      · have he := port_clean_filter_score v _ hc F B hFB
        unfold SA.Root.prefixSupport GridCO.prefixSupport
        rw [he]
        exact Bool.and_comm _ _
      · have hf : Block.preceq F B = false := Bool.eq_false_iff.mpr hFB
        simp [hf]

/-- Feeds `fastWriteAt`/`fgSourceNext`: project each stored fast set, preserving
its label lookup and the absence of a saved gate. -/
theorem port_fastWrite_projection {n : Nat} (st : State n) (F : Block) (r : Slot) :
    fastWriteAt { st with
      fastWrite := st.fastWrite.map (fun row => (row.1, row.2.filter (Block.preceq F))) } r =
    (fastWriteAt st r).map (List.filter (Block.preceq F)) := by
  unfold fastWriteAt
  simp only [List.find?_map, Option.map_map]
  rfl

end AvailableChain.FGSA.Next
end
