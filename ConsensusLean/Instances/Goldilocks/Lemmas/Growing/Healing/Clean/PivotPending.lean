module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RowSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RawReceipt

/-! # Pivot interface of the clean proposal domain, re-exported

The growing forms of the two `Outcome/PivotRowSources` lemmas that the clean proposal domain reads
(in `ProposalImpl`) are proved in their pivot homes and re-exported here:
`ProposalImpl.raw_writer_held_at_slot_start_at` (`Pivot/RawReceipt`) and
`ProposalImpl.protected_source_compatible_high_origin_at` (`Pivot/RowSources`). This module holds
no declarations. -/
