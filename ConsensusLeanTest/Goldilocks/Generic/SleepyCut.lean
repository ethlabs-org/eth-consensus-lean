module
public import ConsensusLeanTest.Goldilocks.Generic.HealingLeavesCut
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyFG
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyGlue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ClaimReductionEdges

public section

/-! # Cut guard for the generic sleepy proofs

Reuse the healing guard's full type/value traversal, missing-constant checks,
concrete negative control and proof-body controls for every declaration in the
generic sleepy modules and their claim reductions, including private and auxiliary constants.
Only the existing placement-only `AC.gbar` is allowed in modules whose fixed
generic interface reaches it; its own cone is checked by the reused guard.
-/

open Lean Meta
open Consensus.Goldilocks.Generic.Test.HealingLeavesCut

run_meta do
  for (mod, allowed) in #[
      (`ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyFG,
        [``Consensus.Goldilocks.AC.gbar]),
      (`ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyGlue,
        [``Consensus.Goldilocks.AC.gbar]),
      (`ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyTransport,
        [``Consensus.Goldilocks.AC.gbar]),
      (`ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ClaimReductionEdges,
        [``Consensus.Goldilocks.AC.gbar])] do
    check mod allowed
      (`ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt,
        ``Consensus.Goldilocks.Healing.Growing.held_atts_safe_at)

end
