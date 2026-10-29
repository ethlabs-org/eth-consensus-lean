module
public import ConsensusProofs.Model.CanonicalStatement
public import Mathlib.Tactic

@[expose] public section

/-! Eager transaction ingress: a transaction submitted to an awake honest
source is in the inbox of every awake honest recipient from then on. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

/-- Eager ingress serves every awake honest recipient at the sampling time. -/
def EagerTxDelivery (rho : Run F E) : Prop :=
  ∀ u ∈ rho.honest, ∀ x τ, 0 ≤ τ → E.awake u τ = true → x ∈ rho.submit u τ →
    ∀ w ∈ rho.honest, ∀ a, τ ≤ a → E.awake w a = true → x ∈ rho.inbox w a

end Run
end Consensus.Model
end
