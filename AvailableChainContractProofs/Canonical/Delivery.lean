module
public import AvailableChainContractProofs.CanonicalStatement
public import Mathlib.Tactic

@[expose] public section

/-! Eager network service for arbitrary strictly later deadlines. The proof
uses only restart-at-wake and integer time: an awake interval cannot contain
a wake strictly after its start. -/

namespace AvailableChain.Contract
open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

/-- An eager network delivers every honest release to every awake honest
reader at each later integer time in the horizon. Repeated receipts are
harmless; the scheduler can deduplicate objects within each time. -/
def EagerDelivery (rho : Run F E) : Prop :=
  ∀ v ∈ rho.honest, ∀ o t, rho.releases v o t →
    ∀ w ∈ rho.honest, ∀ a, t ≤ a → a ≤ rho.horizon →
      E.awake w a = true → rho.receives w o a

/-- Eager delivery serves every deadline strictly later than its start.
This is independent of GST, the cut, and the shape of the deadline. -/
theorem delivers_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery)
    (dl : Time → Time) (cut : Time) (hd : ∀ a, a < dl a) :
    rho.Delivers dl cut := by
  intro v hv o t ht w hwh a hta _ hdh haw
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

theorem partialSynchrony_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery) : rho.PartialSynchrony := by
  apply rho.delivers_of_eager hw he
  intro a
  exact lt_add_of_le_of_pos (le_max_left a E.t_GST) E.Δ_pos

theorem healthyPrefixDelivery_of_eager (rho : Run F E)
    (hw : rho.SleepWellFormed) (he : rho.EagerDelivery) (cut : Time) :
    rho.HealthyPrefixDelivery cut := by
  apply rho.delivers_of_eager hw he
  intro a
  exact lt_add_of_pos_right a E.Δ_pos

end Run
end AvailableChain.Contract
end
