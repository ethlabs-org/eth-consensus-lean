module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Receiver-scoped service from post-stop service under growing faults

`receiverServiceAfterAt_of_postStop`: on any Goldilocks run, post-stop service gives the
  receiver-scoped service of the AC projection; its AC acceptance relay is derived from the node
  relay (`acBlock_prev`, `accept_next`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

section Run

open AC (ACParams)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- Post-stop service on a Goldilocks run gives every receiver honest at its call strict
processing and acceptance relay on the AC projection. Senders need be honest only at their
source cuts. -/
theorem receiverServiceAfterAt_of_postStop {ini}
    (h : Growing.GoldilocksRun proposer dg H tr ini) {g : Time}
    (hs : PostStopService tr H g) (y : Fin sp.n) :
    Compose.Growing.ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC := by
  refine ⟨fun x i m hx hsa j ℓ hy hc hdl => ?_,
    fun x i B hx hacc j ℓ hy hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, Compose.projAC_callAt.mp hc₀, by
      rw [Compose.Growing.projAC_state_at h hx] at hm
      exact hm⟩
    have hc := Compose.projAC_callAt.mp hc
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x i m hx hsa' y j hy ⟨_, hc⟩
      (by rw [← Compose.projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [Compose.projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    · exact ⟨ℓ', Compose.projAC_callAt.mpr hc', Or.inl hm'⟩
    · exact ⟨ℓ', Compose.projAC_callAt.mpr hc', Or.inr hm'⟩
  · apply h.toLocalRun.acRelayAt (σ := max (tr.time i) g) hx hacc hy hc hanc
    intro k hki hx' hk hj hF
    rw [← hki]
    exact hs.relay x k B hx' hk y j hy hj
      (by rw [hki, ← Compose.projAC_deadline]; exact hdl) hF

end Run

end Consensus.Goldilocks.Simulation

end
