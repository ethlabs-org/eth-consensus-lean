module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Instance

@[expose] public section

/-! # Goldilocks: the concrete Goldilocks node

The Goldilocks protocol is the node (`Spec/Node`) with the Goldilocks AC as its AC
(composition.tex §"Composition"): `goldilocksNode sp` is `goldilocksAC` at the FG payload
the node uses, `List (FG.Att n)`.

This module holds only what the Challenge statements reach; its runs (`GoldilocksTrace`,
`GoldilocksRun`) are in `Milestones/Spec/Run/Goldilocks` (`docs/decisions.md`
§"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks

open AC (ACParams goldilocksAC Vote declaredHeadVotes Payload)

variable (sp : ACParams)

/-- The Goldilocks node's AC: the AC at the node's FG payload type. -/
noncomputable abbrev goldilocksNode :
    NodeAC sp.toParams :=
  goldilocksAC sp (List (FG.Att sp.n))

end Consensus.Goldilocks

end
