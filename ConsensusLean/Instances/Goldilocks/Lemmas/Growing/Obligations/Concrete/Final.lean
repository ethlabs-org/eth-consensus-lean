module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalResetPremises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CarrierProcessed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorRoute
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCalendar
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The final window under growing faults (route A)

A final query has a window of four honest anchors with its run premises and anchor steps
(`final_window_extract_at`), from the final reset premises and the duty → proposal adapter
(`final_duty_proposal_at`). `Simulation.goldilocks_finalWindowSupply` reads it at the run map. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Obligations
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- (H2) of the final window, route A: the duty → proposal adapter under growing faults. -/
theorem final_duty_proposal_at
    (Q : FinalQueryAt S A V) :
    ∀ s : Nat, 0 < s → Q.params.ts s ≤ Q.run.2.horizon →
      HonestReadyIn Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) s
          ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((finalGridAt S A V Q).slotTime
        s) Q.run.2.point.env.ΔAC →
      ∃ P, Healing.Growing.HonestProposalRun Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn) s
          P := by
  intro s hs hth hduty
  obtain ⟨_, P, hP, -⟩ := final_duty_proposal_run_at S A V Q hs hth hduty
  exact ⟨P, hP⟩

/-- The setup's calendar has signing gap `A.signGap` from every time `t₀ ≥ 0` of a final query. -/
theorem final_signGap_at (Q : FinalQueryAt S A V) {t₀ : Time} (ht₀ : 0 ≤ t₀) :
    SignGapAt Q.params.toParams (S.sign (Model.pubOf Q.run.1)) A.signGap t₀ :=
  fun y t ht => signGapAt_of_assumptions A (Model.pubOf Q.run.1) Q.hn y t (ht₀.trans ht)

/-- **Final-window extraction** (route A) under growing faults: a window of four honest anchors
at the final gap `c′ = finalSlots` (the FG delay, the release wait `A.releaseGap` and the signing
wait `A.signGap`; `release_final_delivery`), with its
slack, its anchor run and its three anchor steps, on the setup's signing calendar, at the FG
delay `Δ_F,p + R·Δ` and release hold `R·Δ` of the release gap `R = A.releaseGap`
(`hsSharedUpTo_at`). -/
theorem final_window_extract_at
    (Q : FinalQueryAt S A V) :
    ∃ W : FinalWindowDataAt S A V Q,
        Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  have hcal := simTraceAt_signCalendar S Q.run.2 Q.hn Q.keys
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hfd := FinalQueryAt.protoFGDelay_delivery_at Q
  have hc2 : 2 ≤ A.finalSlots := by rw [A.finalSlots_eq]; exact two_le_releaseFinalSlots _ _ _
  have h3c : 3 * A.finalSlots ≤ S.δt := by rw [A.finalSlots_eq]; exact A.timeout_releaseFinalSlots
  have h4 : ((4 * A.fgSlots - 6 : Nat) : Time) + 6 = 4 * (A.fgSlots : Time) := by
    have : (4 * A.fgSlots - 6 + 6 : Nat) = 4 * A.fgSlots := by have := A.two_le_fgSlots; omega
    exact_mod_cast this
  have hT : 4 * (A.fgSlots : Time) + (A.releaseGap : Time) + (A.signGap : Time) ≤
      4 * (S.δt : Time) := by
    exact_mod_cast A.fgSlots_releaseGap_signGap_le
  have hR : (0 : Time) ≤ (A.releaseGap : Time) * Q.params.Δ :=
    mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hp : protoFGDelay (Model.pubOf Q.run.1) ≤
      ((4 * A.fgSlots - 6 : Nat) : Time) * Q.params.Δ := by
    rw [show ((4 * A.fgSlots - 6 : Nat) : Time) = 4 * (A.fgSlots : Time) - 6 by linarith]
    linarith
  -- the final gap pays the FG delay, the release wait and the signing wait
  have hfin := release_final_delivery (f := A.fgSlots) (R := A.releaseGap) (G := A.signGap) hΔ hp
  rw [← A.finalSlots_eq] at hfin
  have hb : 7 + A.signGap ≤ 4 * A.finalSlots := by
    have := releaseFinalSlots_budget A.fgSlots A.releaseGap A.signGap
    have := A.two_le_fgSlots
    rw [A.finalSlots_eq]; omega
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises_of_shared_within_at S A V Q hc2 h3c
    (finalWindow_offsets A) (FinalQueryAt.hsSharedUpTo_at Q) (d := 0) (L := 0) le_rfl
    (by simp) (Gs := A.signGap) le_rfl (by simpa using Q.mature)
    (Generic.voteLatency_zero_from (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun)
    (by linarith [mul_le_mul_of_nonneg_left hT hΔ.le])
    hcal (final_signGap_at S A V Q le_rfl) (signGap_δt A)
  have hdel : 6 * Q.params.Δ + (A.signGap : Time) * Q.params.Δ +
      (protoFGDelay (Model.pubOf Q.run.1) + (A.releaseGap : Time) * Q.params.Δ) ≤
        4 * Q.params.Δ * (A.finalSlots : Time) := hfin
  have hrelay : 7 * Q.params.Δ + (A.signGap : Time) * Q.params.Δ ≤
      4 * Q.params.Δ * (A.finalSlots : Time) := by
    have : (7 : Time) + (A.signGap : Time) ≤ 4 * (A.finalSlots : Time) := by exact_mod_cast hb
    linarith [mul_le_mul_of_nonneg_left this hΔ.le]
  obtain ⟨W, -, hslack, hrun, hsteps⟩ :=
    final_window_extract_of_gap_delayed_at S A V Q hc2 h3c (finalWindow_offsets A)
      (FinalQueryAt.hsSharedUpTo_at Q) hR hdel hrelay (final_latency_gap_at S A V Q)
      hreset hcal
      (fun s _ _ => final_signGap_at S A V Q (by
        change (0 : Time) ≤ 4 * Q.params.Δ * (s : Nat) + 6 * Q.params.Δ; positivity))
      (final_duty_proposal_at S A V Q) hplace (carrier_processed_of_honest_at S A V Q)
  exact ⟨W, hslack, hrun, hsteps⟩

end Consensus.Goldilocks.Obligations.Growing

end
