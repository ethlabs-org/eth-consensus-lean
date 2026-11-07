module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # Growing-fault confirmed proposals

`ConfirmedProposalAt Q`: an actual proposal of the canonical growing trace for a nonfinal query,
released and accepted at a cut after the query time and by its deadline, by a proposer ready
(with the query's readiness duration) at that cut. The proposer's hold is not part of it: the
sleepy route carries it separately. Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- Actual production at a finite cut by a proposer ready there, not an eligible schedule slot
alone. Acceptance is explicit: release alone does not imply local acceptance. -/
structure ConfirmedProposalAt (Q : ConfirmedQueryAt S A V) where
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Nat
  proposal : Q.trace.ProposesAt block.proposer cut block
  accepted : Q.trace.AcceptAt block.proposer cut block
  ready : Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration block.proposer (Q.trace.time cut)
  fresh : Q.query < Q.trace.time cut
  bounded : Q.trace.time cut ≤ Q.deadline

end Consensus.Goldilocks.Obligations.Growing

end
