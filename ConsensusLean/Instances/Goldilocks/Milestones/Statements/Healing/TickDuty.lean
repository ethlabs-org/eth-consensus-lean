module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events

@[expose] public section

/-! # Goldilocks milestone Healing: the tick duty

`TickDuty tr H`, the tick part of `Driven` (`Healing/AC`, (b)) on its own: every honest node awake
at a public time `t ≥ 0` runs its tick at `t`. The outage and frontier arguments over AC traces
read only this part of the driver (`Lemmas/Healing/AC/Frontier`). Definitions only. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **The tick duty** (`Driven.tick`): every honest node awake at a public time `t ≥ 0` runs its
tick at `t`. -/
def TickDuty (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ t, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ i ℓ, tr.CallAt y i ℓ ∧ ℓ.call = .tick ∧ tr.time i = t

end Consensus.Goldilocks.SA

end
