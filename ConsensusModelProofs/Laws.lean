module
public import ConsensusModelProofs.View

@[expose] public section
namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

private theorem event_time_nonneg (rho : Run F E) (h : rho.ExecutionValid) (i : Nat) :
    0 ≤ rho.cutTime i := by
  cases i with
  | zero => simp [Run.cutTime]
  | succ i =>
    simp only [Run.cutTime]
    split
    · rename_i e he
      exact (h.in_horizon e (List.mem_of_getElem? he)).1
    · exact le_refl 0

private theorem event_time_le (rho : Run F E) (h : rho.ExecutionValid)
    (i : Nat) (hi : i ≤ rho.events.length) : rho.cutTime i ≤ rho.horizon := by
  cases i with
  | zero => simpa [Run.cutTime] using h.horizon_nonneg
  | succ i =>
    have hib : i < rho.events.length := by omega
    simp only [Run.cutTime, List.getElem?_eq_getElem hib]
    exact (h.in_horizon _ (List.getElem_mem hib)).2

theorem sysOf_laws (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V] :
    (sysOf O F V).Laws := by
  constructor
  · rintro ⟨E, rho⟩ hv
    refine ⟨rfl, ?_, ?_⟩
    · intro i j hij hj
      change rho.cutTime i ≤ rho.cutTime j
      change j ≤ rho.events.length at hj
      cases i with
      | zero => simpa [Run.cutTime] using event_time_nonneg rho hv j
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
    · intro i hi
      exact event_time_le rho hv i hi
  · rintro ⟨E, rho⟩ A B v hab ⟨o, ho, o', ho', h₁, h₂, hc⟩
    exact ⟨o, hab ho, o', hab ho', h₁, h₂, hc⟩
  · rintro ⟨E, rho⟩ v i j hij o ⟨o', ho', rfl⟩
    exact ⟨o', rho.viewIdx_mono hij v ho', rfl⟩
end Consensus.Model
end
