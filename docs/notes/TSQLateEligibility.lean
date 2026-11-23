import Std

namespace LateEligibilityWitness

-- Distinct authenticated j votes, indexed by seat. `true` votes X, `false` votes G.
private def frozen : List (Fin 8 × Bool) :=
  [(0,true),(1,true),(2,true),(3,false),(4,false),(5,false)]
private def writer := frozen ++ [(6,true)]
private def reader := writer ++ [(7,false)]
private def eligible (v : List (Fin 8 × Bool)) := v.length < 2 * (v.filter Prod.snd).length
private instance (v) : Decidable (eligible v) := inferInstanceAs (Decidable (_ < _))

theorem strict_majority_lost : (reader.map Prod.fst).Nodup ∧ reader.take 7 = writer ∧
    ¬eligible frozen ∧ eligible writer ∧ ¬eligible reader := by decide

end LateEligibilityWitness
