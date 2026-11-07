module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Always

public section

/-! # Pending interface of the growing engine endpoints

Statements the endpoint transports consume whose home modules are not on this branch yet, under
their final names (or, for the node row, in the form the engine needs):

* collision transport to the canonical growing trace (`Simulation.noCollRun_simTraceAt`, home
  `Lemmas/Growing/Simulation`);
* final accountability of two nodes each honest at a read point of its cut
  (`Regimes.Growing.final_accountable_readPoint`): the growing `FinalAccountable` row with each
  reader honest at a time `t ≥ 0` no earlier than every cut before its read, rather than at the
  read cut's own time. An engine reader is honest at the time of the event before its cut; the
  trace cut it reads lies at the time of the next event, possibly after its compromise.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Without an observed hash collision, the canonical growing trace is collision free. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  sorry

end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Final accountability at read points under growing faults.** If the finalized tips of two
nodes, each honest at a time `t ≥ 0` no earlier than every cut before its read, conflict inside
the blocks held while honest, at least `2q − n` validators each have a slashable pair among the
attestations included on two chains the two readers hold. No fault bound. -/
theorem final_accountable_readPoint
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t t' : Time}
    (ht : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (ht' : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t') (hz : z ∈ H t')
    (hc : ¬ Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j)) :
    ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
      ∃ W : Finset (Fin sp.n), 2 * sp.toParams.q - sp.n ≤ W.card ∧
        ∀ v ∈ W, ∃ a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
          ∃ b ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂, a.val = v ∧ FG.slashable a b := by
  sorry

end Consensus.Goldilocks.Regimes.Growing

end
