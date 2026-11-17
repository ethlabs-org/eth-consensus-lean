module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Explicit-input relational unlock observations -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- Relational over-approximation of unlock: ancestry witnesses, slot/expiry coverage,
and exempt live-lock retention, without injectivity or a deterministic target. -/
def UnlocksRel (sp : SAParams) (L : Set Lock) (Φ : Frm sp.n FGP)
    (t : Time) (s : Int) (V : View sp.n) (L₁ : Set Lock) : Prop :=
  (∀ l' ∈ L₁, ∃ l ∈ unlock sp L Φ t s V,
    l.slot = l'.slot ∧ l.fast = l'.fast ∧ l.expiry = l'.expiry ∧
    ∃ T ∈ Φ.tree, T.root = l.block ∧ ∃ Y ∈ Φ.tree, Y.root = l'.block ∧ Φ.Anc Y T) ∧
  (∀ l ∈ unlock sp L Φ t s V, ∃ l' ∈ L₁,
    l'.slot = l.slot ∧ l'.fast = l.fast ∧ l'.expiry = l.expiry) ∧
  (∀ l ∈ liveLocks sp L Φ t, s ≤ (l.slot : Int) → l ∈ L₁)

end Consensus.Goldilocks.SA.FamilyFacts

end
