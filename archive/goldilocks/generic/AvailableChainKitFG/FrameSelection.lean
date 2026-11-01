module
public import AvailableChainKitFG.FrameBridgeDef -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- port: DC/DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:53-64
omit [Fintype V] in
/-- [helper] `pickPair` returns the unique member that satisfies the test. -/
theorem pickPair_eq_of_unique {α : Type} [DecidableEq α] (T : Finset α) (p : α → Bool)
    (a : α) (ha : a ∈ T) (hpa : p a = true) (hu : ∀ b ∈ T, p b = true → b = a) :
    pickPair T p = some a := by
  have hex : ∃! x, x ∈ T ∧ p x = true := ⟨a, ⟨ha, hpa⟩, fun b hb => hu b hb.1 hb.2⟩
  unfold pickPair
  rw [dite_eq_left hex]
  have hch := Finset.choose_spec (fun x => p x = true) T hex
  exact congrArg some (hu _ hch.1 hch.2)

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- [helper] The band floor is at most the frontier. -/
theorem Controls.lo_le_H (c : Controls V) : c.lo ≤ c.H := by
  unfold Controls.lo
  split_ifs <;> simp only [Height] at * <;> omega

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- [helper] The band floor is at least `H − 1`. -/
theorem Controls.H_sub_one_le_lo (c : Controls V) : c.H - 1 ≤ c.lo := by
  unfold Controls.lo
  split_ifs <;> simp only [Height] at * <;> omega

omit [DecidableEq V] [Fintype V] in
/-- [helper] A lex key that is at most another has a height that is at most the
other height. -/
theorem fst_le_of_lexKey_le {p q : Height × FGBlock V} (h : lexKey p ≤ lexKey q) :
    p.1 ≤ q.1 := by
  unfold lexKey at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

end AvailableChain.KitFG
end
