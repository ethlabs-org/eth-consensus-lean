module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run

public section

/-! # Receiver-scoped AC service from PSync

The finite valid engine run gives `ReceiverServiceAfter` for each honest receiver. The proof
follows the two arms of `syncWindowBefore_projection`; receiver calls lie in the horizon. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- PSync after `g` gives the receiver-scoped strict AC service for an honest receiver `y`. -/
theorem receiverServiceAfter_of_psync (hn : 1 ≤ Fintype.card V)
    (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys ⟨S, stock⟩ rho) :
    Compose.ReceiverServiceAfter (honestKeys ⟨S, stock⟩ rho)
      ((simTrace ⟨S, stock⟩ rho hn).HonestBlocks (honestKeys ⟨S, stock⟩ rho)) g y
          (simTrace ⟨S, stock⟩ rho hn).projAC := by
  have h := (simTrace_goldilocksRun S rho hn hconst hv).toLocalRun
  have bound {j : Nat} {ℓ} (hc : (simTrace ⟨S, stock⟩ rho hn).CallAt y j ℓ) :
      (simTrace ⟨S, stock⟩ rho hn).time j ≤ rho.horizon :=
    simTrace_labelled_time_le ⟨S, stock⟩ rho hn hv (by rw [hc.2]; simp)
  refine ⟨fun x hx i m hsa j ℓ hc hdl => ?_, fun x hx i B hacc j ℓ hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : (simTrace ⟨S, stock⟩ rho hn).SendOrAdmitAt x i m :=
        ⟨ℓ₀, Compose.projAC_callAt.1 hc₀, by
      rw [Compose.projAC_state h hx] at hm
      exact hm⟩
    have hc := Compose.projAC_callAt.1 hc
    obtain ⟨k, hkj, htk, hp, hlt⟩ := message_service_psync S rho hn hconst hv hnet hx hsa' hy
      ⟨_, hc⟩ (bound hc) (by rw [← Compose.projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [Compose.projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩,
      ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr hm'⟩]
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := Compose.projAC_callAt.1 hc
    obtain ⟨i', rfl, hi', hti⟩ := Compose.acBlock_prev h hx (Compose.projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = ((simTrace ⟨S, stock⟩ rho hn).state y j).fg.F := by
      rw [(h.cutLaw y hy j _ hc).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := acceptance_relay_psync_any S rho hn hconst hv hnc hnet hx hi'
      hy ⟨_, hc⟩ (bound hc)
      (by rw [hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := Compose.accept_next h hy hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ (simTrace ⟨S, stock⟩ rho hn).RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', Compose.projAC_callAt.2 hc', hb'⟩, ?_⟩
    change (simTrace ⟨S, stock⟩ rho hn).time (k + 1) <
      (simTrace ⟨S, stock⟩ rho hn).projAC.deadline y (k + 1)
          (max ((simTrace ⟨S, stock⟩ rho hn).time (i' + 1)) g)
    rw [Compose.projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

end Consensus.Goldilocks.Obligations
