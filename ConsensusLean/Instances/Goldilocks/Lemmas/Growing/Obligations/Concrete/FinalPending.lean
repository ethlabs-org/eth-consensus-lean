module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run

public section

/-! # Pending interface of the final route under growing faults

Statements the final route consumes whose home modules are not on this branch yet:

* final-cache ancestry is engine finalized output under growing faults (`finalized_inBy_at`,
  home `Lemmas/Growing/Sleepy/Engine/Reads`, proved there; `ready_proposal_at` of the same home
  is stood in by `Queries/Pending`);
* the reset premises and seed placement of a final query under growing faults
  (`final_reset_premises_of_query_at`, the growing form of `final_reset_premises_of_query`, home
  with the growing Healing reset kernel);
* the FG projection of a growing run (`Compose.Growing.fg_projection`, home
  `Lemmas/Growing/Compose/FGProjection`), proved on its branch over the growing FG modules.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
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

end Engine

section Query

variable (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- (H1)+(H3) of the final-window extraction under growing faults: one reset `a` with a bound
`ΔR` whose per-cut reset premises hold through the horizon at GST `Q.gst`, with the run proposer
and digest, and the seed placement at `finalSeedMinAt Q a`. -/
theorem final_reset_premises_of_query_at (Q : FinalQueryAt S A V) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen := by
  sorry

end Query

end Consensus.Goldilocks.Obligations.Growing

namespace Consensus.Goldilocks.Compose.Growing

/-- The FG projection obeys each law at the caller's own honesty horizon. -/
theorem fg_projection : FGProjection := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
