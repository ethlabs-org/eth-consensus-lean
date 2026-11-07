module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FaultBound

public section

/-! # The node and seed layers of the reset-form suppliers

The node-layer and seed-layer facts that `Clean/ResetSuppliers` uses are proved in their homes,
re-exported here: `Compose.Growing.carryAt_of_delivered` and `Compose.Growing.result_writer_at`
(`Growing/Sleepy/Node/Transport`), and `Healing.Growing.fault_bound_late_before_at`
(`Growing/Healing/FaultBound`). This module holds no declarations; its importer can import the
homes directly, after which it is deleted. -/

end
