module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks: `LocksWF` on a Goldilocks run

The lock well-formedness invariant (`SA.LocksWF`, `AC/Steps/ExpiryFloor`) at the AC states of an
honest node of a Goldilocks run and at the read point of its casts, through the AC projection
(`goldilocks_ac_projection`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **`LocksWF` at every honest AC state** of a Goldilocks run. -/
theorem locksWF_state (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) : SA.LocksWF sp (tr.state y i).ac.locks := by
  rw [← projAC_state hrun.toLocalRun hy]
  exact SA.locksWF_state (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun hy i

/-- **`LocksWF` at the read point of an honest cast** of a Goldilocks run. -/
theorem castAt_readPoint_locksWF (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) :
    SA.LocksWF sp e.readPoint.locks :=
  SA.castAt_readPoint_locksWF (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
    hy hc

end Consensus.Goldilocks.Compose

end
