module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

@[expose] public section

/-! # Sleepy strict growth (R.2): committee vocabulary

`CommitteeSleepy`: the committee support of a slot dictionary `K` from genesis, with faults charged
at each consumption time. For every slot `s`, CS: the slot-`s` committee count
`FaultBoundK K s` read at `t_s + Δ` holds with the faults of every `d ∈ [t_s + Δ, t_s + 6Δ]`, and
CS2: fewer than half of the slot-`s` committee is compromised at every `d ∈ [t_s, t_s + 2Δ]`.

Vocabulary only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

/-- Committee support from genesis, with faults charged at each consumption time. -/
def CommitteeSleepy {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (K : SA.CommitteeDict sp.n) : Prop :=
  (∀ (s : Nat) (d : Time), sp.ts s + sp.Δ ≤ d → d ≤ sp.ts s + 6 * sp.Δ →
    SA.FaultBoundK K s tr.projAC (H d) (sp.ts s + sp.Δ)) ∧
  (∀ (s : Nat) (d : Time), sp.ts s ≤ d → d ≤ sp.ts s + 2 * sp.Δ →
    2 * (K.committee s ∩ (H d)ᶜ).ncard < (K.committee s).ncard)

end Consensus.Goldilocks.Regimes.Growing

end
