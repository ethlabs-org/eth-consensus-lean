module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Receiver-scoped service from partial synchrony under growing faults -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Partial synchrony supplies strict processing and acceptance relay to a receiver
honest at its call. Senders need be honest only at their source cuts. -/
theorem receiverServiceAfterAt_of_psync (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) (y : Fin (Fintype.card V)) :
    Compose.Growing.ReceiverServiceAfterAt (honestKeysAt S rho)
      ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) g y
      (simTraceAt S rho hn).projAC := by
  let tr := simTraceAt S rho hn
  have h := simTraceAt_goldilocksRun S rho hn hv
  have bound {j : Nat} {ℓ} (hc : tr.CallAt y j ℓ) : tr.time j ≤ rho.horizon := by
    change (simTraceAt S rho hn).time j ≤ rho.horizon
    rw [simTraceAt_eq]
    exact simTrace_labelled_time_le S rho hn hv (by rw [← simTraceAt_eq, hc.2]; simp)
  have state {x : Fin (Fintype.card V)} {i : Nat}
      (hx : x ∈ honestKeysAt S rho (tr.time i)) : tr.projAC.state x i = (tr.state x i).ac := by
    have hp := h.upTo (h.time_nonneg i)
    have hs := Compose.projAC_state hp.toLocalRun hx i
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun q hq => h.time_mono hq.le),
      Trace.upTo_state tr x (fun q hq => h.time_mono hq.le)] at hs
    exact hs
  refine ⟨fun x i m hx hsa j ℓ hy hc hdl => ?_,
    fun x i B hx hacc j ℓ hy hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, Compose.projAC_callAt.mp hc₀, by
      rw [state hx] at hm
      exact hm⟩
    have hc := Compose.projAC_callAt.mp hc
    obtain ⟨k, hkj, htk, hp, hlt⟩ := Obligations.Growing.message_service_psync_at S rho hn hv
      hnet hx hsa' hy ⟨_, hc⟩ (bound hc) (by rw [← Compose.projAC_deadline]; exact hdl)
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
    obtain ⟨k, hkj, hk, hlt⟩ := Obligations.Growing.acceptance_relay_psync_any_at S rho hn hv
      hnc hnet hx' hi hy ⟨_, hc⟩ (bound hc)
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

end Consensus.Goldilocks.Simulation
