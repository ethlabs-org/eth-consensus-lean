module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # Pending interface of the outage engine reader and repair

Statements the outage engine reader and repair consume whose home modules are not on this
branch yet, under their final names and statements:

* `Obligations.Growing.ready_transport_at` (home `Lemmas/Growing/Sleepy/Engine/Transport`): an
  engine node ready at `t ∈ [0, horizon]` is ready at `t` in the canonical trace;
* `Obligations.Growing.read_prefix` (home `Lemmas/Growing/Sleepy/Engine/ReadPoint`): ancestry of
  two reads by nodes honest at their read times is a prefix of their confirmed chains.

Each is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Engine readiness under growing faults.** An engine node ready at `t ∈ [0, horizon]` is ready
at `t` in the canonical trace. -/
theorem ready_transport_at (hv : rho.ExecutionValid) {c : Time} {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c (rho.ownKey v) t := by
  sorry

/-- Ancestry, inside the blocks held while honest, of the reads of two nodes each honest at its
read time with every earlier cut no later is a prefix of their confirmed chains. -/
theorem read_prefix (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {y z : Fin (Fintype.card V)} {j j' : Nat} {t t' : Time}
    (ht : 0 ≤ t) (hj : ∀ k < j, (simTraceAt S rho hn).time k ≤ t) (hy : y ∈ honestKeysAt S rho t)
    (ht' : 0 ≤ t') (hj' : ∀ k < j', (simTraceAt S rho hn).time k ≤ t')
    (hz : z ∈ honestKeysAt S rho t')
    (ha : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      (Regimes.readAfter (simTraceAt S rho hn) y j t)
      (Regimes.readAfter (simTraceAt S rho hn) z j' t')) :
    chainTo ((simTraceAt S rho hn).state y j).fg.blocks
        ((Regimes.readAfter (simTraceAt S rho hn) y j t).slot + 1)
        (Regimes.readAfter (simTraceAt S rho hn) y j t) <+:
      chainTo ((simTraceAt S rho hn).state z j').fg.blocks
        ((Regimes.readAfter (simTraceAt S rho hn) z j' t').slot + 1)
        (Regimes.readAfter (simTraceAt S rho hn) z j' t') := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
