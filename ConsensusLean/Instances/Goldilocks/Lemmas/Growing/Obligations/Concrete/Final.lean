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

/-- **Final-window extraction** (route A) under growing faults: a window of four honest anchors
at the FG gap `c = fgSlots`, with its slack, its anchor run and its three anchor steps. -/
theorem final_window_extract_at
    (Q : FinalQueryAt S A V) :
    ∃ W : FinalWindowDataAt S A V Q,
        Q.trace.time (W.cut 3) + Q.params.Δ ≤ Q.deadline ∧
      W.AnchorRun ∧ W.AnchorSteps := by
  obtain ⟨ΔR, a, hreset, hplace⟩ := final_reset_premises_at S A V Q
  obtain ⟨W, -, hslack, hrun, hsteps⟩ :=
    final_window_extract_of_gap_at S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
      (FinalQueryAt.hsSharedUpTo_at Q) (FinalQueryAt.protoFGDelay_delivery_at Q)
      (final_latency_gap_at S A V Q)
      hreset (final_duty_proposal_at S A V Q) hplace
      (carrier_processed_of_honest_at S A V Q)
  exact ⟨W, hslack, hrun, hsteps⟩

end Consensus.Goldilocks.Obligations.Growing

end
