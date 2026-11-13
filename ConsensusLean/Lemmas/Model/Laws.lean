module
public import ConsensusLean.Lemmas.Model.View

public section

/-! # System laws of the execution model

`sysOf_laws` derives the generic system laws: ordered bounded cut times on valid runs,
monotone conviction under view inclusion, and monotone views along cuts. `View` supplies the
view interface; the protocol-independent time bounds remain local to this proof. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

/-- Validity admits the very external input exported by the execution, not a
separately chosen selection. -/
theorem sysExternal_admits (r : (sysOf O F V).Run) (h : (sysOf O F V).Valid r) :
    (sysExternal O F V).Admits r.1 ((sysExternal O F V).ext r) :=
  h.selValid

/-- Changing the awake profile at equal delays preserves the execution's key
assignment and its entire role selection. Roles are transported by the equality
of public protocol parameters, not selected again. -/
theorem sysExternal_transport {E E' : Env V} (hAC : E.ΔAC = E'.ΔAC)
    (hFG : E.ΔFG = E'.ΔFG) (x : (sysExternal O F V).Ext E) :
    let y := (sysExternal O F V).transport E E' hAC hFG x
    y.1 = x.1 ∧ HEq y.2 x.2 := by
  rcases E with ⟨a, ha, b, hb, awake⟩
  rcases E' with ⟨a', ha', b', hb', awake'⟩
  cases hAC
  cases hFG
  exact ⟨rfl, HEq.rfl⟩

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

theorem sysOf_laws (O : OutputSchema) (F : ProtocolFamily O) (V : Type) [Fintype V] [DecidableEq V]
    :
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
