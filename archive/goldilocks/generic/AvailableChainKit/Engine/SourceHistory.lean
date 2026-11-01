module
public import AvailableChainKit.Engine.EngineClock

@[expose] public section
namespace AvailableChain.Engine
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- From any event boundary, a clock-only field either retains its row
or has a later clock source. The field need not grow monotonically. -/
theorem clock_field_origin_since {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {α : Type} (field : P.State → List α)
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (rho : Run V P) (start finish : Nat) (le : start ≤ finish) (v : V) (row : α)
    (member : row ∈ field (Run.stateBefore P rho finish v)) :
    row ∈ field (Run.stateBefore P rho start v) ∨
      ∃ j, start ≤ j ∧ j < finish ∧ ∃ t, rho.events[j]? = some (.tick v t) ∧
        Q (Run.stateBefore P rho j v) t row := by
  induction finish with
  | zero => exact Or.inl (Nat.le_zero.mp le ▸ member)
  | succ finish ih =>
    by_cases eq : start = finish + 1
    · exact Or.inl (eq ▸ member)
    have before : start ≤ finish := by omega
    have old (h : row ∈ field (Run.stateBefore P rho finish v)) :
        row ∈ field (Run.stateBefore P rho start v) ∨
          ∃ j, start ≤ j ∧ j < finish + 1 ∧ ∃ t, rho.events[j]? = some (.tick v t) ∧
            Q (Run.stateBefore P rho j v) t row := by
      rcases ih before h with prior | ⟨j, lo, hi, rest⟩
      · exact Or.inl prior
      · exact Or.inr ⟨j, lo, by omega, rest⟩
    cases event : rho.events[finish]? with
    | none => exact old (by simpa [Run.stateBefore, List.take_add_one, event] using member)
    | some e =>
      rw [stateBefore_succ_event event] at member
      cases e with
      | tick u t =>
        by_cases same : v = u
        · subst u
          rcases hclock _ t row (by simpa only [World.step, Function.update_self] using member)
            with prior | source
          · exact old prior
          · exact Or.inr ⟨finish, before, by omega, t, event, source⟩
        · exact old (by simpa [World.step, same] using member)
      | deliver u o t =>
        apply old
        by_cases same : v = u
        · subst u; simpa [World.step, hprocess] using member
        · simpa [World.step, same] using member

end AvailableChain.Engine
end
