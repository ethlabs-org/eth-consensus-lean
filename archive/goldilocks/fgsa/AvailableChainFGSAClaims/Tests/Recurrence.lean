module
public import AvailableChainFGSAClaims.Statements.Bounds -- shake: keep (positive controls)

public section

namespace AvailableChain.FGSA.Run.Tests.Recurrence

open Gen.Pure

example : FinForm.strongW.holds (fun s : Slot => 0 < s) 2 8 1 0 100 3 := by
  change 3 ≤ 3 ∧ Gen.Pure.RecPat _ 2 _ 8 1 0 100 1 2
  refine ⟨by decide, by decide, fun q hq _ _ => ⟨q, ⟨le_rfl, by omega⟩, ?_⟩⟩
  simp only [Gen.Pure.PatAt_def, Gen.Pure.FinForm.pat_def,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  repeat' constructor
  all_goals exact Nat.add_pos_left (Nat.mul_pos (Nat.add_pos_left hq _) (by decide)) _

example : FinForm.lit.holds (fun s : Slot => 0 < s) 2 8 1 0 100 3 := by
  change 3 ≤ 3 ∧ Gen.Pure.RecPat _ 2 _ 8 1 0 100 1 1
  refine ⟨by decide, by decide, fun q hq _ _ => ⟨q, ⟨le_rfl, by omega⟩, ?_⟩⟩
  simp only [Gen.Pure.PatAt_def, Gen.Pure.FinForm.pat_def,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  repeat' constructor
  all_goals exact Nat.add_pos_left (Nat.mul_pos (Nat.add_pos_left hq _) (by decide)) _

example : FinForm.lit.holds (fun s : Slot => 0 < s) 2 8 1 0 100 4 := by
  change 3 ≤ 4 ∧ Gen.Pure.RecPat _ 2 _ 8 1 0 100 1 2
  refine ⟨by decide, by decide, fun q hq _ _ => ⟨q, ⟨le_rfl, by omega⟩, ?_⟩⟩
  simp only [Gen.Pure.PatAt_def, Gen.Pure.FinForm.pat_def,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  repeat' constructor
  all_goals exact Nat.add_pos_left (Nat.mul_pos (Nat.add_pos_left hq _) (by decide)) _

end AvailableChain.FGSA.Run.Tests.Recurrence

end
