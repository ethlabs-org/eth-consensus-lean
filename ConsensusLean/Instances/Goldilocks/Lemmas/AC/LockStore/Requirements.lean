module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: the interface requirements 1–4 (A0.6)

The heads of the duties extend `fc_root` (the anchor does, and the walk only descends) and end in
`viable_heads` when they start in the viable tree of their domain (a walk inside a viable tree
stops only at a viable head); the block for the FG is a candidate below the anchor; the confirmed
tip is between `Φ.F` and the head; and the parent of a proposal is the head of `ac_head` at the
state the proposal leaves. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.6.** -/
theorem interface_requirements : InterfaceRequirements sp := by
  sorry

end Consensus.Goldilocks.SA

end
