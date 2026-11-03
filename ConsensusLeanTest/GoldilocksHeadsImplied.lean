module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface
@[expose] public section

/-! # Requirement 1's proposal clause follows from requirements 3 and 4

A limit test (CONTRIBUTING "Statements") for the AC interface requirements
(`Spec/AC/Interface.lean`), cited by the docstring of `Compose.FGProjection`
(`Statements/Compose/Run.lean`): the proof of the FG projection reads requirement 1 only through
`proposal_parent_held` (the parent of a proposal at a slot start extends `fc_root`), and that
clause already follows from requirement 4 (the parent is `ac_head` at the state `ac_proposal`
leaves) and requirement 3 (`ac_head` extends `fc_root` at every reachable state; the state after
`ac_proposal` is reachable by that call).

* `proposalHead_of_outputs_parent`: for every AC, `ReqOutputs` and `ReqParent` give the first
  conjunct of `ReqHeads`'s proposal clause. -/

namespace Consensus.Goldilocks.Compose.Test.HeadsImplied

/-- **Requirements 3 and 4 give requirement 1's proposal clause** (first conjunct): at every
reachable state, the parent of a proposal at a slot start extends `fc_root`. -/
theorem proposalHead_of_outputs_parent {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (h3 : A.ReqOutputs) (h4 : A.ReqParent) :
    A.AtReachable fun _ _ s Φ t₀ => ∀ σ : Nat, t₀ ≤ P.slotTime σ → ∀ d p,
      (A.proposal s Φ (P.slotTime σ)).2 = some (d, p) → Φ.Anc Φ.fcRoot d.head := by
  intro self U hU s Φ t₀ hr σ hσ d p hp
  have hFi : A.FrameIn U Φ := by
    induction hr with
    | init _ _ hin => exact hin
    | step _ _ _ hok => exact hok.1
  have hr' : A.ReachableAt self U (A.proposal s Φ (P.slotTime σ)).1 Φ (P.slotTime σ) :=
    .step .proposal hr hσ ⟨hFi, rfl⟩
  rw [h4 self U hU s Φ t₀ hr σ hσ _ d p (by rw [← hp])]
  exact (h3 self U hU _ Φ _ hr' (P.slotTime σ) le_rfl).1

end Consensus.Goldilocks.Compose.Test.HeadsImplied

end
