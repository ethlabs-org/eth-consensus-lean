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

/-- The final gap `c′ = finalSlots` pays the FG delay and the signing wait:
`6 + fgDelay + G ≤ 4c′`. -/
private theorem finalSlots_budget : 6 + (4 * A.fgSlots - 6) + A.signGap ≤ 4 * A.finalSlots := by
  have := A.two_le_fgSlots
  rw [ContractAssumptions.finalSlots, A.fgDelay_val]
  omega

/-- The setup's calendar has signing gap `A.signGap` from every time `t₀ ≥ 0` of a final query. -/
theorem final_signGap_at (Q : FinalQueryAt S A V) {t₀ : Time} (ht₀ : 0 ≤ t₀) :
    SignGapAt Q.params.toParams (S.sign (Model.pubOf Q.run.1)) A.signGap t₀ :=
  fun y t ht => signGapAt_of_assumptions A (Model.pubOf Q.run.1) Q.hn y t (ht₀.trans ht)

/-- **Final-window extraction** (route A) under growing faults: a window of four honest anchors
at the final gap `c′ = finalSlots` (the FG delay and the signing wait `A.signGap`), with its
slack, its anchor run and its three anchor steps, on the setup's signing calendar. -/
theorem final_window_extract_at
    (Q : FinalQueryAt S A V) :
    ∃ W : FinalWindowDataAt S A V Q,
        Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  have hcal := simTraceAt_signCalendar S Q.run.2 Q.hn Q.keys
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hfd := FinalQueryAt.protoFGDelay_delivery_at Q
  have hc2 : 2 ≤ A.finalSlots := by
    have := A.two_le_fgSlots; rw [ContractAssumptions.finalSlots, A.fgDelay_val]; omega
  have h3c : 3 * A.finalSlots ≤ S.δt := by
    rw [ContractAssumptions.finalSlots, A.fgDelay_val]; exact A.timeout
  have hb : (6 : Time) + ((4 * A.fgSlots - 6 : Nat) : Time) + (A.signGap : Time) ≤
      4 * (A.finalSlots : Time) := by exact_mod_cast finalSlots_budget S A
  have h4 : ((4 * A.fgSlots - 6 : Nat) : Time) + 6 = 4 * (A.fgSlots : Time) := by
    have : (4 * A.fgSlots - 6 + 6 : Nat) = 4 * A.fgSlots := by have := A.two_le_fgSlots; omega
    exact_mod_cast this
  have hT : 4 * (A.fgSlots : Time) + (A.signGap : Time) ≤ 4 * (S.δt : Time) := by
    exact_mod_cast fgSlots_signGap_le A
  have hfgS : (2 : Time) ≤ (A.fgSlots : Time) := by exact_mod_cast A.two_le_fgSlots
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises_of_shared_within_at S A V Q hc2 h3c
    (finalWindow_offsets A) (FinalQueryAt.hsSharedUpTo_at Q) (d := 0) (L := 0) le_rfl
    (by simp) (Gs := A.signGap) le_rfl (by simpa using Q.mature)
    (Generic.voteLatency_zero_from (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun)
    (by nlinarith) hcal (final_signGap_at S A V Q le_rfl) (signGap_δt A)
  have hdel : 6 * Q.params.Δ + (A.signGap : Time) * Q.params.Δ +
      protoFGDelay (Model.pubOf Q.run.1) ≤ 4 * Q.params.Δ * (A.finalSlots : Time) := by
    nlinarith
  have hrelay : 7 * Q.params.Δ + (A.signGap : Time) * Q.params.Δ ≤
      4 * Q.params.Δ * (A.finalSlots : Time) := by
    nlinarith
  obtain ⟨W, -, hslack, hrun, hsteps⟩ :=
    final_window_extract_of_gap_delayed_at S A V Q hc2 h3c (finalWindow_offsets A)
      (FinalQueryAt.hsSharedUpTo_at Q) hdel hrelay (final_latency_gap_at S A V Q) hreset hcal
      (fun s _ _ => final_signGap_at S A V Q (by
        change (0 : Time) ≤ 4 * Q.params.Δ * (s : Nat) + 6 * Q.params.Δ; positivity))
      (final_duty_proposal_at S A V Q) hplace (carrier_processed_of_honest_at S A V Q)
  exact ⟨W, hslack, hrun, hsteps⟩

end Consensus.Goldilocks.Obligations.Growing

end
