module
public import ConsensusModel.System

@[expose] public section
namespace Consensus.Model
open AvailableChain (Time)
open AvailableChain.Generic (Env)

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

private theorem event_time_nonneg (rho : Run F E) (h : rho.ScheduleWellFormed) (i : Nat) :
    0 ≤ rho.cutTime i := by
  cases i with
  | zero => simp [Run.cutTime]
  | succ i =>
    simp only [Run.cutTime]
    split
    · rename_i e he
      exact (h.in_horizon e (List.mem_of_getElem? he)).1
    · exact le_refl 0

private theorem event_time_le (rho : Run F E) (h : rho.ScheduleWellFormed)
    (i : Nat) (hi : i ≤ rho.events.length) : rho.cutTime i ≤ rho.horizon := by
  cases i with
  | zero => simpa [Run.cutTime] using h.horizon_nonneg
  | succ i =>
    have hib : i < rho.events.length := by omega
    simp only [Run.cutTime, List.getElem?_eq_getElem hib]
    exact (h.in_horizon _ (List.getElem_mem hib)).2

theorem sysOf_laws (F : Family) (V : Type) [Fintype V] [DecidableEq V] :
    (sysOf F V).Laws := by
  constructor
  · rintro ⟨E, rho⟩ hv i j hij hj
    change rho.cutTime i ≤ rho.cutTime j
    change j ≤ rho.events.length at hj
    cases i with
    | zero => simpa [Run.cutTime] using event_time_nonneg rho hv.toScheduleWellFormed j
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hi' : i < rho.events.length := by omega
        have hj' : j < rho.events.length := by omega
        simp only [Run.cutTime, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
        by_cases he : i = j
        · subst j; exact le_refl _
        · have hp := (List.pairwise_iff_getElem.mp hv.sorted) i j hi' hj' (by omega)
          rcases hp with hp | ⟨hp, _⟩
          · exact le_of_lt hp
          · exact le_of_eq hp
  · rintro ⟨E, rho⟩ hv i
    exact event_time_nonneg rho hv.toScheduleWellFormed i
  · rintro ⟨E, rho⟩ hv i hi
    exact event_time_le rho hv.toScheduleWellFormed i hi
  · rintro ⟨E, rho⟩ A B v hab ⟨o, ho, o', ho', h₁, h₂, hc⟩
    exact ⟨o, hab ho, o', hab ho', h₁, h₂, hc⟩
  · rintro ⟨E, rho⟩ v i j hij o ⟨o', ⟨k, x, hk, hx, hc⟩, rfl⟩
    exact ⟨o', ⟨k, x, lt_of_lt_of_le hk hij, hx, hc⟩, rfl⟩
end Consensus.Model
end
