module
public import AvailableChainGridCO.Proofs.Goldfish

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_proposerSupportView
    {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  (proposerView st s).filter (fun o =>
    match resolvedHead? st o with
    | some b => b.slot ≤ s - 1
    | none => false)

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_proposerSupportView_match_1_eq :
    hygieneEq% (@proposerSupportView) (@hygiene_proposerSupportView) := rfl

end AvailableChain.GridCO

-- Rewrite before simp can generate equations for the public matcher.
attribute [local simp↓]
  AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split at $h:ident))

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic
open AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The exact finite seat set counted by the executable release rule. -/
def releaseConflictSeats (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) : Finset (Fin n) :=
  let raw := votesAt st r
  let resolved := raw.filter (fun o => resolvedBefore st o (releaseTime p r))
  (seats n resolved).toFinset.filter (fun i =>
    !equivocates raw i &&
    (seatVotes resolved i).any (fun o =>
      match headTarget? o with
      | some target => !Block.compatible target B
      | none => false))

/-- [ROOT-DIGEST-2 W1; DC legacy HEAD] Resolved block votes keep the old seat count. -/
theorem releaseCount_eq_card (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) :
    releaseCount p st r B = (releaseConflictSeats p st r B).card := by
  have resolved (o : Wire n) (ho : resolvedBefore st o (releaseTime p r) = true) :
      resolvedHead? st o = headTarget? o := by
    unfold resolvedBefore at ho
    unfold resolvedHead? at ho ⊢
    cases ht : headTarget? o with
    | none => rfl
    | some B =>
      by_cases hm : B ∈ st.blocks <;>
        simp [ht, resolveTarget, resolutionTree, hm] at ho ⊢
  unfold releaseCount releaseConflictSeats
  dsimp only
  rw [← List.toFinset_filter]
  rw [List.toFinset_card_of_nodup (List.Nodup.filter _
    (show (seats n ((votesAt st r).filter
      (fun o => resolvedBefore st o (releaseTime p r)))).Nodup from List.nodup_dedup _))]
  congr 1
  apply List.filter_congr
  intro i _
  apply congrArg (fun x => !equivocates (votesAt st r) i && x)
  apply Bool.eq_iff_iff.mpr
  simp only [
      ↓AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq,
      List.any_eq_true]
  constructor <;> rintro ⟨o, ho, hx⟩ <;> refine ⟨o, ho, ?_⟩
  · rwa [resolved o (List.mem_filter.mp (List.mem_filter.mp ho).1).2] at hx
  · rwa [resolved o (List.mem_filter.mp (List.mem_filter.mp ho).1).2]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The snapshot counting step. `hreceipts` must be obtained from accepted
HEAD relay plus path admission before `q_r`. `hnoEquivocation` needs the
reverse relay of any second accepted copy before `d_r`; without that premise
the implication is false. Both premises concern the same run and reader. -/
theorem snapshot_count_of_relayed_seats
    (p : Params) {n : Nat} (reader : State n) (r : Slot) (B : Block)
    (Z : Finset (Fin n))
    (hreceipts : ∀ i ∈ Z, ∃ o,
      o ∈ votesAt reader r ∧
      resolvedBefore reader o (releaseTime p r) = true ∧
      headSeat? o = some i ∧
      (match headTarget? o with
       | some target => !Block.compatible target B
       | none => false) = true)
    (hnoEquivocation : ∀ i ∈ Z,
      equivocates (votesAt reader r) i = false) :
    Z.card ≤ releaseCount p reader r B := by
  rw [releaseCount_eq_card]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨o, hraw, hresolved, hseat, hconflict⟩ := hreceipts i hi
  have hmem : o ∈ (votesAt reader r).filter
      (fun u => resolvedBefore reader u (releaseTime p r)) :=
    List.mem_filter.mpr ⟨hraw, hresolved⟩
  have hseatmem : i ∈ seats n ((votesAt reader r).filter
      (fun u => resolvedBefore reader u (releaseTime p r))) := by
    simp only [seats, List.mem_dedup, List.mem_filterMap]
    exact ⟨o, hmem, hseat⟩
  have hany : ((seatVotes ((votesAt reader r).filter
      (fun u => resolvedBefore reader u (releaseTime p r))) i).any
      (fun u => match headTarget? u with
        | some target => !Block.compatible target B
        | none => false)) = true := by
    apply List.any_eq_true.mpr
    exact ⟨o, List.mem_filter.mpr ⟨hmem, by simp [hseat]⟩, hconflict⟩
  simp only [releaseConflictSeats, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hseatmem, by simp [hnoEquivocation i hi, hany]⟩

end AvailableChain.GridCO
end
