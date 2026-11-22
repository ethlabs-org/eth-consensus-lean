module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLaws
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps

public section

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Model (pubOf)
open NodeAsChainShape.CanonicalTrace (afterClock_eq engineDuty_eq envelope_eq
  engineRole_eq engineObj_eq Encoding)

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V]

/-- The Goldilocks proposal guard holds at every selected propose duty of a valid tick. -/
theorem goldilocks_ready (S : Setup) (hn : 1 ≤ Fintype.card V) :
    (traceEncoding (E := E) S hn).ProposalReady :=
  traceEncoding_induction S hn (fun e _ => e.ProposalReady) fun _ => by
    rw [Encoding.proposalReady_iff]
    intro rho hv i v t he s hs hone hsel
    simp only [afterClock_eq, engineRole_eq, List.map_cons, List.map_nil, engineDuty_eq,
      engineObj_eq] at *
    rw (config := { transparency := .default }) [← atProposal_eq S rho v _ t]
    intro par info cs hp
    let nd := atProposal S rho v (rho.stateBefore i v) t
    rw [envelope_eq] at hp
    change (propose (shapeOf S hn nd) s).2 = some (par, info, cs) at hp
    change rho.ownKey v ∈ rho.sel (.proposer s) at hsel
    have hc := proposal_releasable S rho hn hv v i t he s par info cs hs hone hsel hp
    let h : Header Info := ⟨par, s, encodeTxs nd.st.2, info⟩
    let auth : Model.Auth (pubOf E).n (ShapeRole S.vote.Kind) :=
      .signed (rho.ownKey v) (.proposer s)
    change Model.releasable nd.seen (.mk auth (.item h) cs) = true ∧
      (dependencies _).ready (Model.closure nd.seen) (.mk auth (.item h) cs) = true
    refine ⟨List.all_eq_true.2 fun o ho => decide_eq_true (hc o ho), ?_⟩
    rw [propose_eq] at hp
    dsimp only at hp
    split at hp
    · cases hp
    · cases Option.some.inj hp
      exact dependencies_item _ _ _ _ _

/-- The Goldilocks run establishes the local replay laws; its due flag is proof-side only. -/
theorem traceEncoding_lawful (S : Setup) (hn : 1 ≤ Fintype.card V) :
    (traceEncoding (E := E) S hn).Lawful (traceDue S hn) :=
  (traceEncoding_opLaws S hn).toLawful (goldilocks_ready S hn)

end Consensus.Goldilocks.Simulation
