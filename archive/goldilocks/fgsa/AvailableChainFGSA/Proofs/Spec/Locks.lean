module
public import AvailableChainFGSA.Model.Spec.Transitions
public import AvailableChainFGSA.Proofs.BlockAncestry

public section

namespace AvailableChain.FGSA.Spec

/-- The maximum map records exactly the deadlines of covering entries. -/
theorem lt_lockMap_iff (entries : List (AvailableChain.Block × Time))
    (B : AvailableChain.Block) (t : Time) :
    (t : WithBot Time) < lockMap entries B ↔
      ∃ e ∈ entries, AvailableChain.Block.Preceq B e.1 ∧ t < e.2 := by
  induction entries with
  | nil => simp [lockMap]
  | cons e es ih =>
      change (t : WithBot Time) <
        (if AvailableChain.Block.preceq B e.1 then max (e.2 : WithBot Time) (lockMap es B)
         else lockMap es B) ↔ _
      by_cases h : AvailableChain.Block.preceq B e.1 = true
      · simp only [h, ↓reduceIte, lt_max_iff, WithBot.coe_lt_coe, ih,
          List.mem_cons, exists_eq_or_imp, AvailableChain.Block.Preceq, true_and]
      · simp only [h, ↓reduceIte, ih, List.mem_cons, exists_eq_or_imp,
          AvailableChain.Block.Preceq, Bool.false_eq_true, false_and, false_or]

/-- A live entry and a positive projected lease describe the same lock. -/
theorem locked_iff_map (tree : List AvailableChain.Block) (t : Time)
    (entries : List (AvailableChain.Block × Time)) (B : AvailableChain.Block) :
    locked tree t entries B ↔ (t : WithBot Time) < lockMap (liveEntries tree t entries) B := by
  rw [lt_lockMap_iff]
  constructor
  · rintro ⟨e, he, hB⟩
    exact ⟨e, he, hB, (of_decide_eq_true (List.mem_filter.mp he).2).1⟩
  · rintro ⟨e, he, hB, _⟩
    exact ⟨e, he, hB⟩

/-- Expiry changes no live-entry projection at the current time. -/
theorem liveEntries_expire (tree : List AvailableChain.Block) (t : Time)
    (A : ACState n) : liveEntries tree t (expire A t).locks = liveEntries tree t A.locks := by
  simp only [liveEntries, expire, List.filter_filter]
  congr 1
  funext e
  simp [Bool.and_comm]

/-- Removing the Lean-only level commutes with deadline expiry. -/
theorem expire_lease_projection (st : GridCO.State n .root) (t : Time) :
    (GridCO.expire st t).obligations.map (fun e => (e.1, e.2.2)) =
      (st.obligations.map (fun e => (e.1, e.2.2))).filter (fun e => decide (t < e.2)) := by
  simp only [GridCO.expire, List.filter_map]
  rfl

/-- Cleanup of conflicting entries has no effect on a map above F. -/
theorem lockMap_cleanup (entries : List (AvailableChain.Block × Time))
    (F B : AvailableChain.Block) (hFB : AvailableChain.Block.Preceq F B) :
    lockMap (entries.filter (fun e => AvailableChain.Block.compatible e.1 F)) B =
      lockMap entries B := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
      by_cases hBE : AvailableChain.Block.preceq B e.1 = true
      · have hFE := block_preceq_trans hFB hBE
        have hc : AvailableChain.Block.compatible e.1 F = true := by
          unfold AvailableChain.Block.compatible
          rw [hFE, Bool.or_true]
        simp only [List.filter_cons, hc, ↓reduceIte]
        simp only [lockMap, List.foldr_cons, hBE, ↓reduceIte] at ih ⊢
        rw [ih]
      · by_cases hc : AvailableChain.Block.compatible e.1 F = true <;>
          simp only [List.filter_cons, hc, ↓reduceIte, Bool.false_eq_true]
        all_goals simpa only [lockMap, List.foldr_cons, hBE, Bool.false_eq_true,
          ↓reduceIte] using ih

/-- Given the pointwise relation, the Lean lease and spec live-lock read agree. -/
theorem lease_locked_iff (st : State n) (tree : List AvailableChain.Block) (t : Time)
    (entries : List (AvailableChain.Block × Time)) (h : LeaseRelation st tree t entries)
    (B : AvailableChain.Block) (hB : B ∈ tree) (hne : B ≠ .genesis) :
    (t : WithBot Time) < ((leaseOf st B).map (fun d => (d : WithBot Time))).getD ⊥ ↔
      locked tree t entries B := by
  rw [h B hB hne, locked_iff_map]

end AvailableChain.FGSA.Spec
end
