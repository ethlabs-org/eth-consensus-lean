module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreLocal

public section

/-! # The node-run bundle at the canonical P-U run

The static, growing and reset cores use the canonical run-facts bundles.
-/

namespace Consensus.Goldilocks

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp} {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The node-run bundle under growing faults, obtained from the canonical growing core. -/
theorem Growing.GoldilocksRun.toLocalRunCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) :
    Generic.LocalRunCore Store.updateFinality proposer dg H tr ini :=
  hrun.toCore.toLocalRunCore

end Consensus.Goldilocks

end
