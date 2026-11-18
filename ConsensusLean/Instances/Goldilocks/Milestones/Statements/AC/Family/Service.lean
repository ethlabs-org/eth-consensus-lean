module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Trace

/-! # Statement-layer message service and its retained-evidence closure -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- Timestamped pool evidence, including two distinct votes by the same signer. -/
def PoolEvidenceBefore (st : SAState sp.n) (v : Vote sp.n) (T : Time) : Prop :=
  SA.HeldBefore st v T ∨ ∃ a b : Vote sp.n, a ≠ b ∧
    a.val = v.val ∧ b.val = v.val ∧ a.slot = v.slot ∧ b.slot = v.slot ∧
    SA.HeldBefore st a T ∧ SA.HeldBefore st b T

/-- Earlier evidence remains usable only across a restart-free interval. -/
def RetainedBefore (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (v : Vote sp.n) (T : Time) : Prop :=
  ∃ q ≤ j, PoolEvidenceBefore (o.state y q) v T ∧
    ∀ r, q ≤ r → r < j → ¬ o.RestartAt y r

/-- Fresh processing before its deadline, or retained timestamped evidence. -/
def MessageServedBefore (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (τ : Time) (v : Vote sp.n) : Prop :=
  (∃ k ≤ j, τ ≤ o.time k ∧ o.ProcessAt y k v ∧ o.time k < o.deadline y k τ) ∨
    RetainedBefore o y j v (o.deadline y j τ)

end Consensus.Goldilocks.SA.FamilyFacts

end
