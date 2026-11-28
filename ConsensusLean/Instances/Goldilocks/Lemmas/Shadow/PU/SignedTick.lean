module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTick
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignCalendar
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedTickCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signing ticks and their report calls in the P-U run -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

end Consensus.Goldilocks.Shadow.PU.Growing

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams Payload)
open Node

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

end Consensus.Goldilocks.Shadow.PU.Growing

end
