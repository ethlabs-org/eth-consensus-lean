module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service

public section

/-! # G1.9 (a) under P-U viability: the justification-step bridge

`CacheAcceptance` assumes a viable descendant of the finalized target `X` on the store after
`update_finality`'s `h_max` write alone, while the finalization step reads `has_viable_descendant`
on the store after the justification step as well (`afterJustification`). With the P-U
`IsViable` (`h_max ≤ h`, or `h = h_max − 1` and either `h_j + 1 < h_max` or `J ⪯ ·`), the bridge
holds under the same premises:

* `hasViableDescendant_afterJustification`: if `σ[B].h ≥ Σ.h_max`, `B` itself is viable after
  the `h_max` write (`h_max' = σ[B].h`) and extends `X`; otherwise `h_max` is unchanged, and a fired
  justification step sets `h_j := σ[B].h_j` with `σ[B].h_j < σ[B].h < h_max`, so
  `h_j + 1 < h_max` and the given viable descendant stays viable (its `J ⪯ ·` arm is not needed).
* `hasViableDescendant_of_attains`: the witness that G1.9 (b)'s `accepted_replay_finalized_cached`
  supplies (a block of height `max h_max σ[B].h`), now by the left arm of `IsViable`.
* `cache_acceptance_pu`: `CacheAcceptance` over the P-U `IsViable`, with the bridge in place of the
  floor argument of the stock proof.

No reachability premise is used. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- `afterJustification` changes only `h_max` (to `max Σ.h_max σ.h`) and, when the justification
step fires, `J` and `h_j` (to `σ.h_j`). -/
private theorem afterJustification_eq' (st : Store P ACP) (σ : FG.ChainState P.n) :
    (afterJustification P ACP st σ).blocks = st.blocks ∧
      (afterJustification P ACP st σ).σ = st.σ ∧ (afterJustification P ACP st σ).F = st.F ∧
      (afterJustification P ACP st σ).hmax = max st.hmax σ.h ∧
      ((afterJustification P ACP st σ) = { st with hmax := max st.hmax σ.h } ∨
        (afterJustification P ACP st σ).hj = σ.hj) := by
  unfold afterJustification; dsimp only
  split <;> (try split) <;> first | exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩ |
    exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- **The bridge.** A viable descendant of `X` after the `h_max` write gives one after the
justification step, for `σ = σ[B]` of a held `B` extending `X` with `σ.h_j < σ.h`. -/
theorem hasViableDescendant_afterJustification {st : Store P ACP} {B X : NodeBlock P ACP}
    (hB : B ∈ st.tree) (hXB : st.Anc X B) (hlt : (st.σ B.root).hj < (st.σ B.root).h)
    (hV : ({ st with hmax := max st.hmax (st.σ B.root).h } : Store P ACP).HasViableDescendant X) :
    (afterJustification P ACP st (st.σ B.root)).HasViableDescendant X := by
  obtain ⟨hb, hσ, -, hm, hj⟩ := afterJustification_eq' st (st.σ B.root)
  have ht : (afterJustification P ACP st (st.σ B.root)).tree = st.tree := by
    unfold Store.tree; rw [hb]
  by_cases hle : st.hmax ≤ (st.σ B.root).h
  · rw [Nat.max_eq_right hle] at hm
    refine ⟨B, ht ▸ hB, by rw [Store.Anc, ht]; exact hXB, ?_⟩
    unfold IsViable; rw [hσ, hm]; exact Or.inl le_rfl
  · have hlt' := Nat.lt_of_not_le hle
    rw [Nat.max_eq_left hlt'.le] at hm
    rcases hj with h | h
    · rw [h]; exact hV
    · obtain ⟨B', hB', hanc, hv⟩ := hV
      refine ⟨B', ht ▸ hB', by rw [Store.Anc, ht]; exact hanc, ?_⟩
      unfold IsViable at hv ⊢
      rw [hσ, hm, h]
      dsimp only at hv
      rw [Nat.max_eq_left hlt'.le] at hv
      rcases hv with hv | ⟨hv, -⟩
      · exact Or.inl hv
      · exact Or.inr ⟨hv, Or.inl (by omega)⟩

/-- **G1.9 (b)'s witness.** A held block `W` extending `X` whose state height reaches the raised
`h_max` is a viable descendant of `X` after the `h_max` write (left arm of the P-U `IsViable`). -/
theorem hasViableDescendant_of_attains {st : Store P ACP} {X W : NodeBlock P ACP} {h : Nat}
    (hW : W ∈ st.tree) (hXW : st.Anc X W) (hh : max st.hmax h ≤ (st.σ W.root).h) :
    ({ st with hmax := max st.hmax h } : Store P ACP).HasViableDescendant X :=
  ⟨W, hW, hXW, Or.inl hh⟩

/-- The finalization step of `update_finality` moves `Σ.F` to `X` when its four tests pass on
the state after the justification step. -/
private theorem updateFinality_F' (st : Store P ACP) (σ : FG.ChainState P.n)
    (X : NodeBlock P ACP) (hX : st.blocks σ.F = some X) (hFX : st.Anc st.F X) (hne : st.F ≠ X)
    (hJ : (afterJustification P ACP st σ).Anc X (afterJustification P ACP st σ).J)
    (hV : (afterJustification P ACP st σ).HasViableDescendant X) :
    (st.updateFinality σ).F = X := by
  obtain ⟨hb, -, hF, -⟩ := afterJustification_eq' st σ
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = afterJustification P ACP st σ := rfl
  have ht : st₂.tree = st.tree := by unfold Store.tree; rw [h2, hb]
  rw [show st₂.blocks σ.F = some X by rw [h2, hb, hX]]
  dsimp only
  rw [ite_eq_left ⟨by rw [Store.Anc, ht, h2, hF]; exact hFX, by rw [h2, hF]; exact hne,
    by rw [h2]; exact hJ, by rw [h2]; exact hV⟩]

/-- **G1.9 (a), cache acceptance, over the P-U `IsViable`.** -/
theorem cache_acceptance_pu : CacheAcceptance P ACP := by
  intro st B X hB hlt hX hXB hFX hne hJ hV
  rw [updateFinality_F' st _ X hX hFX hne hJ
    (hasViableDescendant_afterJustification hB hXB hlt hV)]
  exact Relation.ReflTransGen.refl

end Consensus.Goldilocks.Store

end
