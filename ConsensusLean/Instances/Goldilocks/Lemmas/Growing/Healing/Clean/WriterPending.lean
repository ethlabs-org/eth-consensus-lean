module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.WriterCompatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.RawWriterTree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

public section

/-! # The AC writer comparisons, re-exported

The growing AC writer lemmas that the clean cluster consumes are proved in their homes and
re-exported here: `SA.Growing.result_result_compatible_window_before_at` and
`SA.Growing.result_optimistic_compatible_window_before_at` (`Growing/AC/WriterCompatible`), and
`SA.Growing.raw_writer_voterBlockTree_window_before_at` (`Clean/RawWriterTree`). This module holds
no declarations; its importers can import the homes directly, after which it is deleted. -/

end
