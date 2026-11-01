module
public import AvailableChainGeneric.Proofs.Pure.Schedule -- shake: keep (examples)
import Mathlib.Tactic.Linarith -- shake: keep (examples)
import Mathlib.Tactic.Positivity -- shake: keep (examples)
import Mathlib.Tactic.Ring -- shake: keep (examples)
import Mathlib.Tactic.Tauto -- shake: keep (examples)

public section

namespace AvailableChain.Gen.Pure

section
variable (R : Nat) (P Δ : Time) (q : Nat)

/-- The table rows of .strongW and .lit fail below the form minimum (Nat truncation of
f.len): at g = 0 the .strongW value is (q+1)P + 9Δ, not qP + 9Δ. -/
example : windowEndA .strongW R P Δ q 0 = ((q:Time) + 1) * P + 9 * Δ := by
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_strong, ls_strong]
  push_cast; ring

end

example : FinForm.strongW.holds (fun s : Nat => 0 < s) 2 8 1 0 100 3 := by
  rw [strongPair_iff]; intro q hq _ _; exact Or.inl (strong_all q hq)
example : FinForm.lit.holds (fun s : Nat => 0 < s) 2 8 1 0 100 3 := by
  rw [lit_min]; intro q hq _ _; exact strong_all q hq
example : FinForm.lit.holds (fun s : Nat => 0 < s) 2 8 1 0 100 4 := by
  rw [holds_iff_lit]
  exact ⟨by omega, fun q hq _ _ => ⟨q + 2, le_refl _, by omega, strong_all q hq⟩⟩

end AvailableChain.Gen.Pure
