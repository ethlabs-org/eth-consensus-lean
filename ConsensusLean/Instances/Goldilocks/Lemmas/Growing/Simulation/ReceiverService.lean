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

* `goldilocks_postStopService`: partial synchrony with GST `g` gives the node-level post-stop
  service of the canonical trace (`PostStopService`). Each recipient call is within the horizon
  (`isCall_time_le_horizon`), so the engine's horizon-bounded services apply unchanged.
* `receiverServiceAfterAt_of_postStop`: on any Goldilocks run, post-stop service gives the
  receiver-scoped service of the AC projection; its AC acceptance relay is derived from the node
  relay (`acBlock_prev`, `accept_next`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

section Run

open SA (SAParams ReplayOrder)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

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
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := Compose.projAC_callAt.mp hc
    have hp := h.upTo (h.time_nonneg i)
    have hc₀' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc₀⟩
    obtain ⟨i', rfl, hi', hti⟩ := Compose.acBlock_prev hp.toLocalRun hx hc₀' hb
    change tr.time i' = tr.time (i' + 1) at hti
    have hi := ((RunTrace.upTo_acceptAt tr).mp hi').2
    have hx' := h.antitone (h.time_mono (Nat.le_succ i')) hx
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.toLocalRun.cutLaw y j _ hc hy).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x i' B hx' hi y j hy ⟨_, hc⟩
      (by rw [hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    have hpj := h.upTo (h.time_nonneg j)
    obtain ⟨ℓ', hc', hb', htk⟩ := Compose.accept_next hpj.toLocalRun hy
      ((RunTrace.upTo_acceptAt tr).mpr ⟨h.time_mono hkj, hk⟩)
    change tr.time (k + 1) = tr.time k at htk
    have hc' := ((Trace.upTo_callAt tr).mp hc').2
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (max (tr.time (i' + 1)) g)
    rw [Compose.projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

end Run

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Partial synchrony with GST `g` gives post-stop service on the canonical trace: the engine's
message service and acceptance relay (including pre-GST acceptances) at every recipient call,
each of which lies within the horizon. -/
theorem goldilocks_postStopService (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) :
    PostStopService (simTraceAt S rho hn) (honestKeysAt S rho) g where
  message _ _ _ hx hi _ _ hy hj hd :=
    Obligations.Growing.message_service_psync_at S rho hn hv hnet hx hi hy hj
      (Obligations.Growing.isCall_time_le_horizon S rho hn hv hj) hd
  relay _ _ _ hx hi _ _ hy hj hd hF :=
    Obligations.Growing.acceptance_relay_psync_any_at S rho hn hv hnc hnet hx hi hy hj
      (Obligations.Growing.isCall_time_le_horizon S rho hn hv hj) hd hF

end Consensus.Goldilocks.Simulation

end
