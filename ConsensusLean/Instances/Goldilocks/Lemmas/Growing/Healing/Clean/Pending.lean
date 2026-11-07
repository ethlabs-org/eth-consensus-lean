module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes

public section

/-! # Clean source votes, re-exported

The clean-source vote retention that the clean-source proposal parent reads is proved in
`Clean/FastVotes` and `Clean/SlowVotes`, re-exported here; the proposal domain is in
`Clean/Domain`, which its consumers import directly. This module holds no declarations; its
importers can import the home modules directly, after which it is deleted. -/
