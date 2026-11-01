module
public import AvailableChainFGSAProofs.Proofs.Shared.Count -- shake: keep (source declarations)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; honest late seats and conflicting
support seats are disjoint subsets of the actual late denominator. -/
theorem outageV_partition_rejects {α : Type}
    (honest support late : Finset α) (a : Nat)
    (hH : honest ⊆ late) (hS : support ⊆ late) (hdis : Disjoint honest support)
    (hpart : a < honest.card) (hfault : support.card ≤ a) :
    2 * support.card < late.card := by
  classical
  have hunion : honest ∪ support ⊆ late := Finset.union_subset hH hS
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdis] at hcard
  omega

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; the terminal majority check also
applies to a result equal to the walk anchor. -/
theorem outageV_result_majority {n : Nat} (p : GridCO.Params) (st : GridCO.State n .root)
    (anchor C : Block) (s : Slot)
    (hresult : GridCO.confirmationFrom p anchor st s = some C) :
    GridCO.voterCount (GridCO.lateVotes p st s) <
      2 * GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
        (GridCO.cleanSupport p st s) (GridCO.cleanSupport p st s) C := by
  let score := GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
    (GridCO.cleanSupport p st s) (GridCO.cleanSupport p st s)
  let eligible := fun b => 2 * score b > GridCO.voterCount (GridCO.lateVotes p st s)
  let result := GridCO.ghost anchor st.blocks score (fun b => decide (eligible b))
  change (if eligible result then some result else none) = some C at hresult
  split at hresult
  · next h =>
    have he : result = C := Option.some.inj hresult
    exact he ▸ h
  · contradiction

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a bound using the actual late count
excludes every conflicting genuine result. Ancestor results are permitted. -/
theorem outageV_gate_compatible {n : Nat} (p : GridCO.Params) (st : GridCO.State n .root)
    (anchor B C : Block) (s : Slot)
    (hconflict : ∀ X, ¬ Block.Compatible X B →
      2 * GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
        (GridCO.cleanSupport p st s) (GridCO.cleanSupport p st s) X ≤
          GridCO.voterCount (GridCO.lateVotes p st s))
    (hresult : GridCO.confirmationFrom p anchor st s = some C) :
    Block.Compatible C B := by
  by_contra hn
  exact (not_lt_of_ge (hconflict C hn)) (outageV_result_majority p st anchor C s hresult)

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; compatible honest targets suffice
for the gate count. Honest HEADs may be strict ancestors of B. -/
theorem outageV_gate_of_compatible_batch {n : Nat} (p : GridCO.Params)
    (st : GridCO.State n .root) (anchor B C : Block) (s : Slot)
    (H : Finset (Fin n)) (a : Nat)
    (hH : H ⊆ (GridCO.seats n (GridCO.lateVotes p st s)).toFinset)
    (hraw : GridCO.cleanSupport p st s ⊆ GridCO.lateVotes p st s)
    (hfault : ((GridCO.seats n (GridCO.lateVotes p st s)).toFinset \ H).card ≤ a)
    (hpart : a < H.card)
    (hclean : ∀ i ∈ H, GridCO.equivocates (GridCO.cleanSupport p st s) i = false)
    (htargets : ∀ o ∈ GridCO.cleanSupport p st s, ∀ i ∈ H,
      GridCO.headSeat? o = some i → ∀ K,
      Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree st) o = some K →
        Block.Compatible K B)
    (hresult : GridCO.confirmationFrom p anchor st s = some C) :
    Block.Compatible C B := by
  apply outageV_gate_compatible p st anchor B C s ?_ hresult
  intro X hXB
  let pool := GridCO.cleanSupport p st s
  let domain := GridCO.resolutionTree st
  let late := (GridCO.seats n (GridCO.lateVotes p st s)).toFinset
  let voters := (GridCO.seats n pool).toFinset.filter (fun i =>
    (GridCO.equivocates pool i || Gen.AC.Root.poolSupports domain pool i X) = true)
  have hnone : ∀ i ∈ H, Gen.AC.Root.poolSupports domain pool i X = false := by
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hsupport
    obtain ⟨o, ho, hseat, hvote⟩ :=
      (Gen.AC.Root.vote_pool_support_witness domain pool i X).mp hsupport
    rw [Gen.AC.Root.voteSupports_def] at hvote
    cases hk : Gen.AC.Root.resolvedTarget? domain o with
    | none => rw [hk] at hvote; contradiction
    | some K =>
      rw [hk] at hvote
      have hXK := (Bool.and_eq_true_iff.mp hvote).2
      exact hXB (Gen.Pure.block_compatible_of_preceq_compatible hXK
        (htargets o ho i hi hseat K hk))
  have hsub : voters ⊆ late \ H := by
    intro i hi
    obtain ⟨hmem, hs⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_sdiff.mpr
      ⟨Gen.AC.Root.vote_pool_seats_subset _ _ hraw hmem, ?_⟩
    intro hh
    change (GridCO.equivocates pool i || Gen.AC.Root.poolSupports domain pool i X) = true at hs
    rw [hclean i hh, hnone i hh] at hs
    contradiction
  have hVL : voters ⊆ late := fun _ h => (Finset.mem_sdiff.mp (hsub h)).1
  have hdis : Disjoint H voters := Finset.disjoint_left.mpr (fun _ hh hv =>
    (Finset.mem_sdiff.mp (hsub hv)).2 hh)
  have hc := outageV_partition_rejects H voters late a hH hVL hdis hpart
    ((Finset.card_le_card hsub).trans hfault)
  have hscore : GridCO.goldfishScore domain pool pool X = voters.card :=
    Gen.AC.Root.vote_pool_score_card domain pool pool X
  have hle := Gen.AC.Root.goldfishScoreOn_le domain st.blocks pool pool X
  have hcount : GridCO.voterCount (GridCO.lateVotes p st s) = late.card :=
    Gen.AC.Root.vote_pool_voterCount_card _
  rw [hscore] at hle
  rw [hcount]
  exact (Nat.mul_le_mul_left 2 hle).trans hc.le

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a genuine result extends F even
when the terminal result equals the walk anchor. -/
theorem outageV_result_extends_anchor {n : Nat} (p : GridCO.Params) (st : GridCO.State n .root)
    (anchor C : Block) (s : Slot)
    (hresult : GridCO.confirmationFrom p anchor st s = some C) : Block.Preceq anchor C := by
  let score := GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
    (GridCO.cleanSupport p st s) (GridCO.cleanSupport p st s)
  let eligible := fun b => 2 * score b > GridCO.voterCount (GridCO.lateVotes p st s)
  let result := GridCO.ghost anchor st.blocks score (fun b => decide (eligible b))
  change (if eligible result then some result else none) = some C at hresult
  split at hresult
  · have he : result = C := Option.some.inj hresult
    rw [← he]
    apply Gen.Pure.walk_covers_of_dominated_suffix
    · exact Gen.Pure.block_compatible_of_common
        (Gen.Pure.block_preceq_refl anchor) (Gen.Pure.block_preceq_refl anchor)
    · rw [Gen.Pure.DominatedSuffix_def]
      intro A hA hAF
      change ((!decide (anchor = A)) && Block.preceq anchor A) = true at hA
      obtain ⟨hne, hpre⟩ := Bool.and_eq_true_iff.mp hA
      have he := Gen.Pure.block_preceq_antisymm hpre hAF
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hne
  · contradiction


end AvailableChain.FGSA.Run
end
