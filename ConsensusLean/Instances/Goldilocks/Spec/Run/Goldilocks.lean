module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Instance

@[expose] public section

/-! # Goldilocks: the concrete Goldilocks node

The Goldilocks protocol is the node (`Spec/Node`) with the Goldilocks SA as its AC
(composition.tex §"Composition"): `goldilocksNode sp ro` is `goldilocksSA` at the FG payload
the node uses, `List (FG.Att n)`.

This module holds only what the Challenge statements reach; its runs (`GoldilocksTrace`,
`GoldilocksRun`) are in `Milestones/Spec/Run/Goldilocks` (docs/decisions.md, 2026-11-04). -/

namespace Consensus.Goldilocks

open SA (SAParams ReplayOrder goldilocksSA Vote blockVotes Payload)

variable (sp : SAParams)

/-- The Goldilocks node's AC: the SA at the node's FG payload type, with the replay order
`ro`. -/
noncomputable abbrev goldilocksNode (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    NodeAC sp.toParams :=
  goldilocksSA sp (List (FG.Att sp.n)) ro

end Consensus.Goldilocks

end
