module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding

public section

/-! # The committee dictionary of an outage query

The query's vote role `Q.voteRole` (its binding's), the dictionary `Q.K` of the keys the run
selects for each slot's vote role, and the fact that `Q.K` binds that selection
(`Q.bindsSel`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace OutageQueryAt

/-- The vote role of the query's binding. -/
abbrev voteRole (_Q : OutageQueryAt S A V) := stock.voteRole

/-- The committee dictionary of the query: the keys selected for each slot's vote role. -/
def K (Q : OutageQueryAt S A V) : SA.CommitteeDict (Fintype.card V) :=
  ⟨fun s => {k | k ∈ Q.run.2.sel (Q.voteRole s)}⟩

/-- `Q.K` binds the run's selection for `Q.voteRole`. -/
theorem bindsSel (Q : OutageQueryAt S A V) : Q.K.BindsSel Q.run.2 Q.voteRole :=
  (Q.K.bindsSel_iff _ _).2 fun _ _ => Iff.rfl

end OutageQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
