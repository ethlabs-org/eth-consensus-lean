module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds

public section

/-! # Per-cut interfaces of the growing drain kernel

These interfaces keep the snapshot frontier fixed and read honesty separately at every cut.
They do not reconstruct the reset for a terminal honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}

/-- The frame data shared by the nodes honest at their individual cuts in an interval. -/
structure FrameWindow (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (lo hi : Time) (floor : Nat) (kindJ : Prop)
    (J : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  floor_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.headHeightFloor = floor
  kind_iff : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬ (tr.state y i).fg.Contest) ↔ kindJ)
  root_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi → kindJ →
    (tr.state y i).fg.J = J

/-- The bounded-gap proposal evidence includes honesty through the slot's vote deadline. -/
def ProposalGap (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (G s₀ N : Nat) : Prop :=
  ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
    proposer x ∈ H (sp.ts x + sp.Δ) ∧
      ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x

/-- Characterization for consumers without exporting the proposal-gap definition body. -/
theorem proposalGap_iff {proposer : Nat → Fin sp.n} {G s₀ N : Nat} :
    ProposalGap tr H proposer G s₀ N ↔
      ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
        proposer x ∈ H (sp.ts x + sp.Δ) ∧
          ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x := Iff.rfl

/-- A warm proposal on every sufficiently long frame window. Signature bounds apply at
signing cuts; the height frontier is the original snapshot frontier, not a retained one. -/
structure DrainOutputs (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n)
    (H : Time → Set (Fin sp.n)) (g : Time) (G Ld : Nat) (b : Time) : Prop where
  warm : ∀ {s₀ N floor : Nat} {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))},
    FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → s₀ + Ld ≤ N → sp.ts N + 2 * sp.Δ ≤ b →
    (∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k ≤ sp.ts N + 2 * sp.Δ → att.h ≤ HZ tr H g) →
    ProposalGap tr H proposer G s₀ N →
    ∃ u, s₀ + 2 * sp.k ≤ u ∧ u ≤ s₀ + Ld ∧
      ∃ z kP P, z ∈ H (sp.ts u + sp.Δ) ∧ z = proposer u ∧
        tr.ProposesAt z kP P ∧ P.slot = u ∧
          HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1

end Consensus.Goldilocks.Healing.Growing

end
