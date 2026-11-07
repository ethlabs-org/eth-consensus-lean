module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase

public section

/-! # Growing interface of the operational reports

The growing forms of the Healing and AC lemmas that the operational report lemmas consume have their
homes: `ResetPremisesUpTo.high_origin_votes_before_at` (retention R2) in `Kernel/ResetFacts`,
`ResetPremisesUpTo.restart_le_before_at` in `Growing/Healing/Restart` and the prefix form of
`healthy_base_of_reset_catch_before_at` in `Healthy/PrefixBase`, re-exported here. This module holds
no declarations; its importers can import the home modules directly, after which it is deleted. -/


end
