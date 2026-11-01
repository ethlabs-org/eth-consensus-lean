module
public import AvailableChainKitFG.RecordHighOnceDef
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainKitFG.RecordHigh

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- Keeping or removing finality preserves the high record guards and the
height-pair guard. The height pair still uses the provisional finality lock.
DC: additive (no DC counterpart); reason: finality can be removed after
the height pair is built. This is the high-record form of
`record_row_optional_finality`; no global `RecordInv` premise is needed. -/
theorem recordHigh_optional_finality {V : Type} (h0 : Height)
    (entry : Height → BlockId) (Λ : Record) (signer : V)
    (fields : Option (Height × BlockId)) (hd : HeadFields)
    (hΛ : HighRecord h0 entry Λ)
    (hfields : ∀ h T, fields = some (h, T) → h0 ≤ h → T = entry h)
    (hfinal : ∀ fp, finality_pair Λ hd = some fp →
      h0 ≤ fp.height → fp.target = entry fp.height)
    (fp : Option FinalityPair) (hf : fp = none ∨ fp = finality_pair Λ hd) :
    let a : Row V := ⟨signer, height_pair Λ fields (finality_pair Λ hd), fp⟩
    HighRecord h0 entry (record_row Λ a) ∧
      (∀ h T timeout, a.height_pair = .vote h T timeout →
        h0 ≤ h → T = entry h ∧ timeout = false) := by
  have old := recordHigh h0 entry Λ signer fields hd hΛ hfields hfinal
  rcases hf with rfl | rfl
  · refine ⟨?_, old.2⟩
    intro h hh
    refine ⟨record_row_target_compatible_of _ _ (hΛ h hh).1
      (fun T hp => (old.2 h T false hp hh).1), ?_, ?_⟩
    · apply record_row_timeout_false_of_ne _ _ (hΛ h hh).2.1
      intro T hp
      exact Bool.noConfusion (old.2 h T true hp hh).2
    · rw [record_row_lock]
      exact (hΛ h hh).2.2
  · exact old

/-- A send-once step keeps the inclusive high guard and releases no high
timeout. A step with no release leaves the complete record unchanged.
DC: additive (no DC counterpart); reason: use the actual send-once write
with filtered finality, while preserving the old `recordHigh` theorem. -/
theorem recordHighOnce : RecordHighOnceStatement := by
  intro V _ _ _ E cfg h0 entry Λ signer src hd hΛ hfields hfinal
  dsimp only
  cases ha : (createRowOnce E cfg Λ signer src hd).1 with
  | none =>
      rw [createRowOnce_none E cfg Λ signer src hd ha]
      exact ⟨hΛ, by intro a he; cases he⟩
  | some a =>
      obtain ⟨h, T, timeout, hp, rfl, _, _, hw⟩ :=
        createRowOnce_released E cfg Λ signer src hd ha
      rw [hw]
      dsimp only [record_row_once]
      rw [← hp]
      have hf : (finality_pair Λ.toRecord hd).filter (fun p => decide (p.height < h)) = none ∨
          (finality_pair Λ.toRecord hd).filter (fun p => decide (p.height < h)) =
            finality_pair Λ.toRecord hd := by
        cases finality_pair Λ.toRecord hd <;> simp [Option.filter]
        simp only [Height]
        omega
      have high := recordHigh_optional_finality h0 entry Λ.toRecord signer
        (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) hd
        hΛ hfields hfinal _ hf
      refine ⟨high.1, ?_⟩
      intro b hb
      cases hb
      exact high.2

end AvailableChain.KitFG
end
