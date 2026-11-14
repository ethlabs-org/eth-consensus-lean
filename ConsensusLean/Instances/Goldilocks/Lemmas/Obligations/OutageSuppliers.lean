module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers

public section

/-! # The outage query

`OutageQuery` packages a valid collision-free engine run with constant faults and its outage
premise, with its engine parameters (`OutageQuery.params`). `OutageQuery.toAt`
(`Lemmas/Growing/Obligations/Queries/Defs`) reads it as a growing-fault query. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

structure OutageQuery where
  run : (Sys (goldilocks S) V).Run
  constant : run.2.point.ConstantFaults
  hn : 1 ≤ Fintype.card V
  T : Time
  start : Time
  stop : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  outage : (Sys (goldilocks S) V).Outage
    (shapeProgress (goldilocks S) V).toExternal (K S A) T start stop run

namespace OutageQuery
variable {S A V}
abbrev params (Q : OutageQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
end OutageQuery

end Consensus.Goldilocks.Obligations
end
