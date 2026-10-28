module
public import ConsensusModelProofs.CanonicalStatement
public import Mathlib.Tactic

@[expose] public section

/-! Eager network service for every deadline at or after its start. An eager
network delivers at every awake time, so a node awake at a deadline receives
the message at the deadline itself, which is L0 holding (`CommLog.Held`);
sleep history does not matter. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

/-- An eager network delivers every honest release to every awake honest
reader at each later integer time in the horizon. Repeated receipts are
harmless; the scheduler can deduplicate objects within each time. -/
def EagerDelivery (rho : Run F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ o t, rho.releases v o t →
    ∀ w ∈ rho.honest, ∀ a, t ≤ a → a ≤ rho.horizon →
      E.awake w a = true → rho.receives w o a

/-- Eager ingress serves every awake honest recipient at the sampling time. -/
def EagerTxDelivery (rho : Run F E) : Prop :=
  ∀ u ∈ rho.honest, ∀ x τ, 0 ≤ τ → E.awake u τ = true → x ∈ rho.submit u τ →
    ∀ w ∈ rho.honest, ∀ a, τ ≤ a → E.awake w a = true → x ∈ rho.inbox w a

/-- Eager delivery meets L0 delivery (`CommLog.Delivers`) for every deadline
function at or above the identity, at every cut. This is independent of GST,
the cut, and the shape of the deadline. -/
theorem delivers_of_eager (rho : Run F E) (he : rho.EagerDelivery) (ht : rho.EagerTxDelivery)
    (dl : Time → Time) (cut : Time) (hd : ∀ a, a ≤ dl a) :
    CommLog.Delivers rho.point rho.log dl cut := by
  constructor
  · intro v hv o t hs w hw _ hdh haw
    exact CommLog.held_of_recv (he v hv o t hs w hw (dl t) (hd t) hdh haw)
  · intro v hv o t hs w hw a hta _ hdh haw
    exact CommLog.held_of_recv (he v hv o t hs w hw (dl a) (le_trans hta.le (hd a)) hdh haw)
  · intro u hu x τ hτ haw hx w hw a hτa _ _ ha
    have hle : τ ≤ dl a := le_trans hτa (hd a)
    exact ⟨dl a, le_trans hτ hle, le_rfl, ht u hu x τ hτ haw hx w hw (dl a) hle ha⟩

end Run
end Consensus.Model
end
