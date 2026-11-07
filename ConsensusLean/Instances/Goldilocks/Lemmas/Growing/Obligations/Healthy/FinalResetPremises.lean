module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs

public section

/-! # The reset premises and the placement of a final query, under growing faults

The growing form of `Obligations/FinalResetPremises.final_reset_premises_of_query` (the leaf
`final_reset_premises` of `Obligations/Concrete`): one reset `a` with its finite premises through
the horizon at GST `Q.gst`, over the validators honest at each time, and the placement with
`u_min = finalSeedMinAt Q a`.

The statement is open (`sorry`) until the growing drain kernel it consumes is on this branch. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The reset premises and the placement of a final query**, under growing faults. -/
theorem final_reset_premises_at (Q : FinalQueryAt S A V) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
