module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding

public section

/-! # Acceptance completeness of forwarding under growing faults

The growing-fault form of `ForwardAtAcceptance`: every acceptance by a key honest at the
acceptance cut's time queues and drains its wrapper in the same engine event. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- Acceptance by a key honest at the acceptance cut's time queues and drains a wrapper in the
same event, including own proposals. -/
def ForwardAtAcceptanceAt : Prop :=
  ∀ x k B, x ∈ honestKeysAt S rho (tr.time k) → tr.AcceptAt x k B →
    ∃ r p, pubExec.actual r ∧ r.origin = x ∧
      cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
      pubExec.eventTime r.event = tr.time k ∧
      r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
        some (x, tr.time k, p, B)

/-- Characterize acceptance completeness without exposing its definition body. -/
theorem forwardAtAcceptanceAt_iff : ForwardAtAcceptanceAt S rho hn tr cutMap pubExec ↔
    ∀ x k B, x ∈ honestKeysAt S rho (tr.time k) → tr.AcceptAt x k B →
      ∃ r p, pubExec.actual r ∧ r.origin = x ∧
        cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
        pubExec.eventTime r.event = tr.time k ∧
        r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
        decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
          some (x, tr.time k, p, B) := by
  rfl

end Consensus.Goldilocks.Simulation

end
