module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Premises

/-! # Statement-layer message service and its retained-evidence closure -/

@[expose] public section

namespace Consensus.Goldilocks.AC.FamilyFacts

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- Timestamped pool evidence, including two distinct votes by the same signer. -/
def PoolEvidenceBefore (st : ACState sp.n) (v : Vote sp.n) (T : Time) : Prop :=
  AC.HeldBefore st v T ∨ ∃ a b : Vote sp.n, a ≠ b ∧
    a.val = v.val ∧ b.val = v.val ∧ a.slot = v.slot ∧ b.slot = v.slot ∧
    AC.HeldBefore st a T ∧ AC.HeldBefore st b T

/-- Earlier evidence remains usable only across a restart-free interval. -/
def RetainedBefore (o : GTrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (v : Vote sp.n) (T : Time) : Prop :=
  ∃ q ≤ j, PoolEvidenceBefore (o.state y q) v T ∧
    ∀ r, q ≤ r → r < j → ¬ o.RestartAt y r

/-- Fresh processing before its deadline, or retained timestamped evidence. -/
def MessageServedBefore (o : GTrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (τ : Time) (v : Vote sp.n) : Prop :=
  (∃ k ≤ j, τ ≤ o.time k ∧ o.ProcessAt y k v ∧ o.time k < o.deadline y k τ) ∨
    RetainedBefore o y j v (o.deadline y j τ)

end Consensus.Goldilocks.AC.FamilyFacts

end
