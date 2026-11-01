module
public import AvailableChainKit.Engine.Execution

@[expose] public section

namespace AvailableChain.Engine

open AvailableChain.Generic

/-- A state property that `clock` and `process` keep holds for the rest of
the run. -/
theorem stateBefore_stable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    (Q : P.State → Prop)
    (hclock : ∀ st t, Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hi : Q (Run.stateBefore P rho i v)) : Q (Run.stateBefore P rho j v) := by
  induction j with
  | zero => rwa [Nat.le_zero.mp hij] at hi
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact hi
      · have hj := ih (by omega)
        cases he : rho.events[j]? with
        | none => simpa [Run.stateBefore, List.take_add_one, he] using hj
        | some e =>
            rw [AvailableChain.Engine.stateBefore_succ_event he]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using hclock _ t hj
                · simpa [World.step, hv] using hj
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using hprocess _ o hj
                · simpa [World.step, hv] using hj

end AvailableChain.Engine
end
