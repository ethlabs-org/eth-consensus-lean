module
public import AvailableChainKitFG.WindowOccurrences
public import AvailableChainKitFG.WindowTerminal
public import AvailableChainKitFG.WindowValidity -- shake: keep (axioms)

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.P0b3

open AvailableChain.SimplexFG hiding derive process_row
open AvailableChain.SimplexFG.Window
open AvailableChain.KitFG.Window

private def E : Electorate (Fin 2) :=
  ⟨fun i => if i = 0 then 3 else 1, fun i => by split <;> decide⟩
private def cfg : FGConfig := ⟨0⟩
private def B1 : FGBlock (Fin 2) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def B2 : FGBlock (Fin 2) :=
  .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, none⟩]
private def bitRow : Row (Fin 2) := ⟨1, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩
private def B3 : FGBlock (Fin 2) :=
  .node B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, none⟩, bitRow]
private def B4 : FGBlock (Fin 2) :=
  .node B3 4 ⟨13⟩ 0 [⟨0, .vote 4 B3.root false, some ⟨2, B1.root⟩⟩]

private theorem b3_quorum_nonempty : ¬ E.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem b3_window2 : (derive E cfg 2 B2).W =
    [⟨1, .genesis, ∅⟩, ⟨2, B1, ∅⟩] := by decide +kernel

private theorem b3_window3 : (derive E cfg 2 B3).W =
    [⟨2, B1, {1}⟩, ⟨3, B2, ∅⟩] := by decide +kernel

private theorem b3_window4 : (derive E cfg 2 B4).W =
    [⟨3, B2, ∅⟩, ⟨4, B3, ∅⟩] := by decide +kernel

private theorem b3_retained2 : RetainedW E cfg 2 B2 2 B1 := by
  rw [RetainedW_def, b3_window2]
  simp

private theorem b3_retained3 : RetainedW E cfg 2 B3 2 B1 := by
  rw [RetainedW_def, b3_window3]
  simp

/-- The exact occurrence adds a bit in a real retained entry. -/
private theorem b3_retained_bit : EntryBitW E cfg 2 B3 2 B1 1 := by
  exact entry_bit_insertW E cfg 2 b3_quorum_nonempty (by decide)
    B2 3 ⟨12⟩ 0 _ 2 B1 b3_retained2 b3_retained3
    bitRow (by simp [bitRow]) rfl

/-- The bit has an exact row witness strictly after the birth. -/
private theorem b3_bit_origin :
    ∃ C carrier a, JustificationBirth E (certificateHeight E cfg 2) C 2 B1 ∧
      StrictPrefix C carrier ∧ FGBlock.Preceq carrier B3 ∧ a ∈ carrier.rows ∧
      a.signer = (1 : Fin 2) ∧ a.finality_pair = some ⟨2, B1.root⟩ := by
  obtain ⟨e, he, hj, hX, hi⟩ := b3_retained_bit
  obtain ⟨C, _, birth, origin⟩ := window_entry_origin E cfg 2 (by decide) B3 e he
  obtain ⟨carrier, a, hCc, hcB, ha, hai, haf⟩ := origin 1 hi
  exact ⟨C, carrier, a, by simpa only [hj, hX] using birth,
    hCc, hcB, ha, hai, by simpa only [hj, hX] using haf⟩

/-- A strict post-birth occurrence contributes at the retained endpoint. -/
private theorem b3_exact_occurrence : EntryBitW E cfg 2 B3 2 B1 1 := by
  exact entry_bit_occurrenceW E cfg 2 b3_quorum_nonempty (by decide)
    B2 B3 B3 (by rw [StrictPrefix_def]; decide +kernel) (preceq_refl _) 2 B1
    b3_retained2 b3_retained3 bitRow (by change bitRow ∈ [_, bitRow]; simp) rfl

/-- The proved scalar cap supplies terminal retention on this inhabited chain. -/
private theorem b3_terminal_cap : RetainedW E cfg 2 B3 2 B1 ∨ CoveredW E cfg 2 B3 2 B1 := by
  exact terminalRetentionW E cfg 2 b3_quorum_nonempty (by decide) B2 B3 1 B1
    (preceq_parent_node _ _ _ _ _) b3_retained2 (by decide +kernel)
    (by decide +kernel)

/-- Finality covers the same exact key after a quorum bit arrives. -/
private theorem b3_covered : CoveredW E cfg 2 B4 2 B1 ∧ ¬ RetainedW E cfg 2 B4 2 B1 := by
  simp only [CoveredW_def, RetainedW_def, b3_window4]
  decide +kernel

/-- Capacity removes the oldest key while finality is still below it. -/
private theorem b3_evicted :
    ¬ RetainedW E cfg 2 B3 1 .genesis ∧ ¬ CoveredW E cfg 2 B3 1 .genesis ∧
      (derive E cfg 2 B3).W.length = 2 := by
  simp only [CoveredW_def, RetainedW_def, b3_window3]
  decide +kernel

private theorem b3_eviction_births :
    (derive E cfg 2 B3).W.length = 2 ∧
    ∃ C, FGBlock.Preceq C B2 ∧
      JustificationBirth E (certificateHeight E cfg 2) C 1 .genesis ∧
      ∀ d ∈ (derive E cfg 2 B3).W, 1 < d.j ∧
        ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D B3 ∧
          JustificationBirth E (certificateHeight E cfg 2) D d.j d.X := by
  exact window_evicted_has_K_newer E cfg 2 b3_quorum_nonempty (by decide)
    B2 3 ⟨12⟩ 0 _ ⟨1, .genesis, ∅⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- A bit for another exact key is absent despite the same signer and height. -/
private theorem b3_wrong_key : ¬ EntryBitW E cfg 2 B3 2 B2 1 := by
  simp only [EntryBitW_def, b3_window3]
  decide +kernel

/-- Two newer births meet capacity and do not imply retention of the oldest key. -/
private theorem b3_birth_guard :
    ({B2, B3} : Finset (FGBlock (Fin 2))).card = 2 ∧
      ¬ ({B2, B3} : Finset (FGBlock (Fin 2))).card < 2 ∧
      ¬ RetainedW E cfg 2 B3 1 .genesis := by
  simp only [RetainedW_def, b3_window3]
  decide +kernel

/-- The birth block cannot contribute a bit to its newly appended entry. -/
private theorem b3_birth_bit_guard : ¬ EntryBitW E cfg 2 B3 3 B2 1 := by
  simp only [EntryBitW_def, b3_window3]
  decide +kernel

/-- Useful stale finality alone does not supply a progress bit. -/
private theorem b3_stale_progress_guard :
    let σ : State (Fin 2) := { derive E cfg 2 B2 with h := 4, progress := ∅ }
    r6w σ bitRow = true ∧ heightMatch σ bitRow = false ∧
      bitRow.signer ∉ (process_row σ bitRow).progress := by
  decide +kernel

#print axioms b3_quorum_nonempty
#print axioms b3_window2
#print axioms b3_window3
#print axioms b3_window4
#print axioms b3_retained2
#print axioms b3_retained3
#print axioms b3_retained_bit
#print axioms b3_bit_origin
#print axioms b3_exact_occurrence
#print axioms b3_terminal_cap
#print axioms b3_covered
#print axioms b3_evicted
#print axioms b3_eviction_births
#print axioms b3_wrong_key
#print axioms b3_birth_guard
#print axioms b3_birth_bit_guard
#print axioms b3_stale_progress_guard
end AvailableChain.KitFG.Tests.P0b3
