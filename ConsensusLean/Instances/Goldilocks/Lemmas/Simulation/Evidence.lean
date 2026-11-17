module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Called blocks belong to the engine reader's view

Track the calling node cut back to its engine event, retaining the event index. A release
at the same time without that index would not suffice for an event-cut read. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Under constant faults every block a public tick of an honest node calls at a positive
position is released at that event. -/
private theorem tick_block_releases {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {j : Nat} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (({ S with vote := AsChainShape.stock } : Setup).params
      (pubOf E) hn).toParams.IsPublic t) :
    ∀ r ∈ eventCuts { S with vote := stock } rho hn j, ∀ B acc,
      r.label = .fg (.block B acc) → r.pos ≠ 0 →
      blockObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn) B ∈
        rho.releasesAt j := by
  have hnf := Regimes.non_framing _ _ _ _ _ _ (simTrace_goldilocksRun S rho hn hf hv)
    _ (honest_ownKey (S := { S with vote := stock }) hv')
  exact fun r hr => (tick_releases { S with vote := stock } rho hn hf hv hv' he hp hnf r hr).1

/-- Every called block, accepted or refused, has its canonical object in the final view
of the honest engine node responsible for the call. -/
theorem occurring_in_view {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)}
    (hB : (simTrace { S with vote := stock } rho hn).Occurs B) :
    B.parent ≠ none ∧ ∃ v, v ∉ rho.faultyAt 0 ∧
      blockObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn) B ∈
      rho.ViewIdx v rho.events.length := by
  have hhon {i : Nat} {ev} (he : rho.events[i]? = some ev) : ev.node ∉ rho.faultyAt 0 :=
    (rho.point.honestAt_iff_zero hf ev.node ev.time).mp
      (hv.honest_only ev (List.mem_of_getElem? he))
  obtain ⟨hp, i, ev, he, hb⟩ := block_call_in_view_of_releases { S with vote := stock } rho hn
    (fun he => tick_block_releases S rho hn hf hv (hhon he) he) hB
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  exact ⟨hp, ev.node, hhon he, rho.viewIdx_mono (by omega) _ hb⟩

end Consensus.Goldilocks.Simulation

end
