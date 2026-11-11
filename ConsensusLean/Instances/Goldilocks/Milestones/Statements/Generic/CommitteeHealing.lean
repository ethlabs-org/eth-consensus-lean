module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations

@[expose] public section

/-! # Native committee proposal chaining

This statement describes proposal ancestry in one native AC-parametric execution. It supplies
no healing proof and is not an equivalence with the legacy `HealedFrom` predicate.

OPEN producer obligations remain separate: select pairs whose earlier settlement fits the
actual consuming read without restricting existing read quantifiers or enlarging latency;
for final windows with gaps of at least two slots, justify
`P.slotTime s + settle ≤ P.slotTime (s + 2)`. Neither follows from the hold parameter alone.

The full healing interface remains open pending same-observation evidence-use coverage and
native healthy producers. No evidence-use relation or D-HEAL sufficiency is assumed here.
-/

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

/-- Native proposal-chaining counterpart: the earlier slot settles through `b`, and the
later proposal occurs through `b`. Both proposers are honest at their actual events and at
their respective hold charges. Protocol suppliers must justify `0 ≤ hold ≤ settle` and the
actual-use retention budgets; this predicate supplies neither.

Honesty is read on the same ambient execution. A later hold charge may exceed this local
bound `b`; applying the relation after honesty truncation separately requires both holds to
survive. This states no confirmed-read safety, inclusion, finality or committee sufficiency. -/
def CommitteeHealedFrom {P : Params} {A : NodeAC P}
    (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (hold settle : Time)
    (s₁ : Nat) (b : Time) : Prop :=
  ∀ s s' z z' k k' X X', s₁ ≤ s → s < s' →
    P.slotTime s + settle ≤ b → tr.time k' ≤ b →
    z ∈ H (tr.time k) → z' ∈ H (tr.time k') →
    z ∈ H (P.slotTime s + hold) → z' ∈ H (P.slotTime s' + hold) →
    z = proposer s → z' = proposer s' →
    tr.ProposesAt z k X → X.slot = s →
    tr.ProposesAt z' k' X' → X'.slot = s' →
    Anc (tr.HonestBlocksAt H) X X'

end Consensus.Goldilocks.Generic

end
