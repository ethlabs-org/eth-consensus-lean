module
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol

public section

/-! # Accountable agreement at the later observation

The fault budget is read at the later of the two observations, not at the run horizon.
Evidence in those views was already public by that time, so non-framing confines its
convicted validators to the faulty set at that same time.
-/

namespace Consensus.System

variable {V : Type} [Fintype V]

/-- Accountable safety gives agreement for two honest observations whenever faults at
their later observation are below the accountable fraction. -/
theorem agree_of_accountable_at (S : System V) (hL : S.Laws) (r : S.Run)
    {g : S.schema.Id} {t₀ : Time} {α : ℚ}
    (hacc : S.AccountablySafe r α g t₀) (hnf : S.NonFraming r)
    {u v : V} {i j : Nat}
    (hi : i ≤ (S.trace r).cuts ∧ t₀ ≤ (S.trace r).cutTime i)
    (hj : j ≤ (S.trace r).cuts ∧ t₀ ≤ (S.trace r).cutTime j)
    (hu : (S.trace r).point.HonestAt u ((S.trace r).cutTime i))
    (hv : (S.trace r).point.HonestAt v ((S.trace r).cutTime j))
    (hb : (((S.trace r).point.faultyAt
      (max ((S.trace r).cutTime i) ((S.trace r).cutTime j)))).card < (Fintype.card V : ℚ) * α) :
    Compatible ((S.trace r).read g u i) ((S.trace r).read g v j) := by
  classical
  rcases hacc u v i j hi hj hu hv with hc | hcard
  · exact hc
  · exfalso
    have hsub : Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j) ⊆
        (S.trace r).point.faultyAt (max ((S.trace r).cutTime i) ((S.trace r).cutTime j)) := by
      intro x hx
      have hx' : S.convicts r (S.view r u i ∪ S.view r v j) x := by
        unfold Consensus.convicted at hx
        simpa using hx
      by_contra hxh
      apply hnf x (max ((S.trace r).cutTime i) ((S.trace r).cutTime j)) hxh
      refine hL.convicts_mono r _ _ x ?_ hx'
      rintro o (ho | ho)
      · exact ⟨u, i, hi.1, le_max_left _ _, hu, ho⟩
      · exact ⟨v, j, hj.1, le_max_right _ _, hv, ho⟩
    have hc := Finset.card_le_card hsub
    change (Fintype.card V : ℚ) * α ≤
      (Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j)).card at hcard
    have hc' : ((Consensus.convicted (S.convicts r) (S.view r u i ∪ S.view r v j)).card : ℚ) ≤
        ((S.trace r).point.faultyAt
          (max ((S.trace r).cutTime i) ((S.trace r).cutTime j))).card := by
      exact_mod_cast hc
    exact (not_lt_of_ge (hcard.trans hc')) hb

end Consensus.System

end
