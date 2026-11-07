module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Spec.Shape.Run

public section

/-! # Pending interface of the final route under growing faults

Statements the final route consumes whose home modules are not on this branch yet:

* final-cache ancestry is engine finalized output under growing faults (`finalized_inBy_at`,
  home `Lemmas/Growing/Sleepy/Engine/Reads`, proved there; `ready_proposal_at` of the same home
  is stood in by `Queries/Pending`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Final-cache ancestry is engine finalized output** under growing faults: if a non-genesis
block is an ancestor of the final cache of every node ready at `t ∈ [0, horizon]` after all
events at `t`, its header is in the finalized read of every engine node ready at `t`. -/
theorem finalized_inBy_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) (hth : t ≤ rho.horizon)
    {P : SA.Blk (Fintype.card V) (List (FG.Att (Fintype.card V)))}
    (hroot : P.root ≠ (S.params (pubOf E) hn).genesisRoot)
    (hinc : ∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c y t →
      Regimes.CutAfter (simTraceAt S rho hn) j t →
      Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
        ((simTraceAt S rho hn).state y j).fg.F) :
    InBy rho c .finalized (headerOf (S.params (pubOf E) hn) P) t := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
