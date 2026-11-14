module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Historical row delivery under growing faults

An honest signature remains owed after compromise. The receiver's honesty at the proposal
cut supplies honesty at its earlier restart cuts, without fixing an honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

namespace KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An honestly signed row is processed strictly before a sufficiently late honest proposal,
even if the signer has been compromised by then (`Generic.rows_delivered_service_at_from` at a
Goldilocks run). -/
theorem rows_delivered_service_at {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hv : gbar g ≤ v) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) : ∃ k' < kX, tr.ProcessAttAt p k' att :=
  Generic.rows_delivered_service_at_from hsvc.signedRow hnr hrun.toLocalRun hv hp hX hvx hkb hy
    hsig hk

end KernelProof

end Consensus.Goldilocks.Healing.Growing

end
