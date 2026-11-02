module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset

public section

/-! # Goldilocks Healing: H.4, healing of the available chain

`IncludedFrom` is monotone in its start time (`IncludedFrom.mono`). The whole-run H.4 assembly
`available_healing` was retired with the reset-existence route (#136). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- Inclusion from `t₁` gives inclusion from every later `t₂`. -/
theorem IncludedFrom.mono {t₁ t₂ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : IncludedFrom tr H t₁ P) (ht : t₁ ≤ t₂) : IncludedFrom tr H t₂ P := by
  intro y hy j ℓ hj htj htick
  exact h y hy j ℓ hj (ht.trans htj) fun he => htick (le_antisymm (he ▸ ht) htj)

end Consensus.Goldilocks.Healing

end
