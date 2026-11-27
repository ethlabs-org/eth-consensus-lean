module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.SleepyWindows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.FinalReads
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.FinalWindowSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.HealedReadAncestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.HealingRows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.LocalRows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PreparationPremises
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RegimeTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.ResetHealBudget
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapRepresentation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1Proofs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The Goldilocks local claim suppliers

`goldilocks_localClaimSuppliers`: for any local supplier `C` at its data equations
(`GoldilocksLocalData`), the canonical run map of a valid engine run supplies every row of
`LocalClaimSuppliers` at the endpoint contract `K S A`, with `C` carried along the run map's signer
(`goldilocksRunMap_signer`), the outage policy `goldilocksOutagePolicy`, the stored read context
`goldilocksStoredReadContext` and the events `goldilocksEvents`. Each field is its proved row. -/

namespace Consensus.Goldilocks.Generic

open AsChainShape Shape Blocks Simulation Obligations SleepyLayer1
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The local claim suppliers of the canonical Goldilocks run map**, for any local supplier at
its data equations. -/
theorem goldilocks_localClaimSuppliers (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn))
      (fun v => v.val) fgHold)
    {sign : Fin (S.params (pubOf E) hn).n → Time → Bool} {G : Nat}
    (hdata : GoldilocksLocalData (S.params (pubOf E) hn) C sign G A.releaseGap) :
    LocalClaimSuppliers (goldilocksRunMap S rho hn hv)
      ((goldilocksRunMap_signer S rho hn hv).symm ▸ C) (K S A)
      (goldilocksOutagePolicy S rho hn hv) (goldilocksStoredReadContext S rho hn hv)
      (goldilocksEvents (S.params (pubOf E) hn)) := by
  have hsg := (goldilocksRunMap_signer S rho hn hv).symm
  have hcast := fun (Q : ∀ s, ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn))
      s fgHold → Prop) (h : Q _ C) => ACCorrectLocal.cast_signer hsg C Q h
  have hθK : (K S A).params.θ = 1 / 2 := by norm_num [Params.standard]
  have hΔ : (S.params (pubOf E) hn).Δ = E.ΔAC := rfl
  have hfields := hcast (fun _ C => C.θ = 1 / 2 ∧ C.look = 5 * E.ΔAC ∧
      C.committeeLook = 5 * E.ΔAC ∧ C.catchUp = 18 * E.ΔAC ∧ C.hold = E.ΔAC)
    ⟨hdata.θ, hΔ ▸ hdata.look, hΔ ▸ hdata.committeeLook, hΔ ▸ hdata.catchUp,
      hΔ ▸ hdata.hold⟩
  have hfgR : (K S A).params.fgDelay + 6 + A.releaseGap ≤ 4 * S.δt := by
    have h1 := A.fgDelay_val
    have h2 := A.fgSlots_releaseGap_signGap_le
    have h3 := A.two_le_fgSlots
    change (A.fgDelay : Nat) + 6 + A.releaseGap ≤ 4 * S.δt
    omega
  have hgap := releaseGapAt_of_assumptions A (pubOf E) hn
  have hheal : ∀ cap idx, 13 ≤ (K S A).params.heal cap idx := fun cap idx => by
    have h1 := contract_heal_ge_reset S A cap idx
    change 13 ≤ (contract_heal S A cap idx : Nat)
    omega
  have hruns := hcast (fun _ C => ∀ cm proposer dg H tr, C.run.Run cm proposer dg H tr →
      ∃ ini, Growing.GoldilocksRun proposer dg H tr ini)
    (fun cm proposer dg H tr h => by
      rw [hdata.healing.1.1] at h
      exact ⟨_, h.1⟩)
  exact
  { regime := ⟨_, goldilocks_regimeTransport S A rho hn hv C hdata hsg⟩
    outputValidity := goldilocksRunMap_outputValidity S rho hn hv
    reads := goldilocksRunMap_readRepresentation S rho hn hv
    honestReads := goldilocksRunMap_honestReadTransport S rho hn hv
    chains := by
      rw [show (goldilocksRunMap S rho hn hv).chain =
          fun st B => blocksTo st.fg.blocks (B.slot + 1) B from
        funext₂ (goldilocksRunMap_chain S rho hn hv), goldilocksRunMap_header]
      exact goldilocks_chainRepresentation _
    honestChains := goldilocksRunMap_honestChainReads S rho hn hv
    coherent := goldilocksRunMap_coherent S rho hn hv
    engineRead := goldilocksRunMap_engineReadPoint S rho hn hv
    localRead := hcast (fun _ C => LocalReadPoint C) (goldilocks_localReadPoint C hdata.healing.1)
    sleepyProposal := goldilocksRunMap_proposal_coverage S rho hn hv C hdata
    eventSafety := goldilocksRunMap_event_safety S rho hn hv C hdata
    outputProvenance := hcast (fun _ C => SleepyLayer1.OutputProvenance C _)
      (goldilocksLocal_output_provenance C hdata)
    extension := goldilocksRunMap_extension S rho hn hv C hdata
    sourceProvenance := hcast (fun _ C => SleepyLayer1.SourceProvenance C _)
      (goldilocksLocal_source_provenance C hdata)
    populationQuorum := goldilocks_population_quorum_supply S E rho hn hv (K S A) hθK.ge
    sleepyWindows := goldilocks_sleepy_window_supply
      S E rho hn hv (K S A) _
      (hfields.1.trans hθK.symm) (by rw [hfields.1]; norm_num) (by rw [hfields.1]; norm_num)
      (by rw [hfields.2.1]; change _ = ((5 : Nat) : Time) * E.ΔAC; norm_num)
      (by rw [hfields.2.2.1]; change _ = ((5 : Nat) : Time) * E.ΔAC; norm_num)
    healthyRead := hcast (fun _ C => HealthyReadPoint C) (goldilocks_healthyReadPoint C hdata)
    outageRead := hcast (fun _ C => OutageReadPoint C) (goldilocks_outageReadPoint C hdata)
    deadlines := goldilocks_claimDeadlineFit S A rho hn hv C hdata hsg
    progress := goldilocks_proposalProgressTransport S rho hn hv
    proposalWitness := goldilocks_proposalWitnessRefinement S A rho hn hv C hdata hsg
    deadlinePremises := by
      rw [hdata.fgHold_eq]
      exact goldilocks_deadlinePremisesSupply S rho hn hv (K S A) hgap
        (by norm_num [Params.standard]) hfgR (hheal .final)
    finalWindow := by
      rw [hfields.2.2.2.1, hfields.2.2.2.2]
      exact goldilocks_finalWindowSupply S A rho hn hv
    finalReads := goldilocks_finalReadTransport S rho hn hv _
    accountability := goldilocks_actualReadAccountability _ _ hruns
    outage := goldilocks_outageTransport S rho hn hv (K S A)
    recovery := goldilocks_outageRecoveryBinding S A hn _ C hdata hsg
    outageService := goldilocks_outageServiceSupply S A rho hn hv C hdata hsg
    resilience := goldilocksRunMap_resilienceTipTransport S rho hn hv
    preparation := by
      rw [hdata.fgHold_eq]
      exact goldilocks_preparation_premises_supply S rho hn hv (K S A) hgap hfgR
        (fun cap idx _ => hheal cap idx)
    highCanonical := goldilocks_highCanonicalSupply S rho hn hv (K S A) _
    resetBudget := goldilocks_resetHealBudgetSupply S A rho hn hv C hdata hsg
    storedRead := goldilocksRunMap_storedReadTransport S rho hn hv
    healedAncestry := goldilocks_healedReadAncestry S A rho hn hv }

end Consensus.Goldilocks.Generic

end
