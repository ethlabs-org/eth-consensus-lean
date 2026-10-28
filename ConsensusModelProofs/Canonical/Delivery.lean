module
public import ConsensusModelProofs.CanonicalStatement
public import Mathlib.Tactic

@[expose] public section

/-! Eager network service for arbitrary strictly later deadlines. The proof
uses only restart-at-wake and integer time: an awake interval cannot contain
a wake strictly after its start. -/

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

/-- Eager delivery serves every deadline strictly later than its start.
This is independent of GST, the cut, and the shape of the deadline. -/
theorem delivers_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery) (ht : rho.EagerTxDelivery)
    (dl : Time → Time) (cut : Time) (hd : ∀ a, a < dl a) :
    rho.Delivers dl cut := by
  constructor
  · intro v hv o t ht w hwh a hta _ hdh haw
    have har : rho.receives w o a :=
      he v hv o t ht w hwh a hta (le_trans (hd a).le hdh) (haw a le_rfl (hd a))
    refine ⟨a, hd a, Or.inr har, ?_⟩
    intro u hu ⟨hau, hud⟩
    have hwake := (hw.restart_at_wake w u hu).2
    have hp : E.awake w (u - 1) = true :=
      haw (u - 1) (Int.le_sub_one_of_lt hau)
        (lt_of_le_of_lt (sub_le_self u (by decide : (0 : Int) ≤ 1)) hud)
    rw [hwake.2] at hp
    cases hp
  · intro u hu x τ hτ haw hx w hw a hτa _ _ ha
    refine ⟨a, le_trans hτ hτa, hd a, ?_⟩
    exact ht u hu x τ hτ haw hx w hw a hτa (ha a le_rfl (hd a))

theorem partialSynchrony_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery) (ht : rho.EagerTxDelivery) :
    rho.PartialSynchrony := by
  apply rho.delivers_of_eager hw he ht
  intro a
  exact lt_add_of_le_of_pos (le_max_left a E.gst) E.Δ_pos

theorem healthyPrefixDelivery_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery) (ht : rho.EagerTxDelivery) (cut : Time) :
    rho.HealthyPrefixDelivery cut := by
  apply rho.delivers_of_eager hw he ht
  intro a
  exact lt_add_of_pos_right a E.Δ_pos

end Run
end Consensus.Model
end
