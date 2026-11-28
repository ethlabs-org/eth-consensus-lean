module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # The stock growing run-facts bundle

`Growing.GoldilocksRun.toCore`: a stock Goldilocks run under growing faults gives the growing
core at `Store.updateFinality` and `Node.frame` (`upTo` through `Growing.GoldilocksRun.upTo` and
`GoldilocksRun.toStaticCore`). -/

namespace Consensus.Goldilocks

open AC (ACParams Payload)

variable {sp : ACParams}
variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp} {ini : Fin sp.n → (goldilocksNode sp).State}

/-- **The core of a stock Goldilocks run under growing faults.** -/
theorem Growing.GoldilocksRun.toCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) :
    GoldilocksRunCore Store.updateFinality Node.frame proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality
  frameOf_F _ := rfl
  frameOf_tree _ _ := Iff.rfl
  antitone := hrun.antitone
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  upTo hd := (hrun.upTo hd).toStaticCore
  cutLaw y i c hc hy := (hrun.cutLaw y i c hc hy).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  acRun hnc := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  coherent hnc := Compose.Growing.honest_blocks_coherent hrun hnc
  held_anc_at hnc := fun hd hy hi h hW => Compose.Growing.held_anc_at hrun hnc hd hy hi h hW
  F_mono_at hd hy hi hki := Compose.Growing.F_mono_at hrun hd hy hi hki
  acRelayAt hx hacc hy hc hanc relay := hrun.toLocalRun.acRelayAt hx hacc hy hc hanc relay
  acCatchAt hcatch := fun hx ha hi hy hc hj hanc =>
    hrun.toLocalRun.acCatchAt hcatch hx ha hi hy hc hj hanc

end Consensus.Goldilocks

end
