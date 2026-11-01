module
public import AvailableChainFGSA.Proofs.WindowOccurrences
public import AvailableChainFGSA.Proofs.WindowTerminal
public import AvailableChainFGSA.Proofs.WindowValidity

set_option linter.privateModule false

namespace AvailableChain.FGSA.Tests.P0b3

open AvailableChain.SimplexFG
open AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
private def rows (h : Height) (X : BlockId) : List (Row (Fin p.n)) :=
  [⟨0, .vote h X false, none⟩, ⟨1, .vote h X false, none⟩,
    ⟨2, .vote h X false, none⟩]
private def B1 : FGBlock (Fin p.n) := .node .genesis 1 ⟨10⟩ 0 (rows 1 genesisRoot)
private def B2 : FGBlock (Fin p.n) := .node B1 2 ⟨11⟩ 0 (rows 2 B1.root)
private def bitRow : Row (Fin p.n) := ⟨3, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩
private def B3 : FGBlock (Fin p.n) :=
  .node B2 3 ⟨12⟩ 0 (rows 3 B2.root ++ [bitRow])
private def B4 : FGBlock (Fin p.n) :=
  .node B3 4 ⟨13⟩ 0
    [⟨0, .vote 4 B3.root false, some ⟨2, B1.root⟩⟩,
     ⟨1, .vote 4 B3.root false, some ⟨2, B1.root⟩⟩,
     ⟨2, .vote 4 B3.root false, some ⟨2, B1.root⟩⟩]

private theorem b3_fgsa_window2 : (FGSA.Window.derive p p.K_W B2).W =
    [⟨1, .genesis, ∅⟩, ⟨2, B1, ∅⟩] := by decide +kernel

private theorem b3_fgsa_window3 : (FGSA.Window.derive p p.K_W B3).W =
    [⟨2, B1, {3}⟩, ⟨3, B2, ∅⟩] := by decide +kernel

private theorem b3_fgsa_retained2 : FGSA.Window.RetainedW p B2 2 B1 := by
  rw [FGSA.Window.RetainedW_def, b3_fgsa_window2]
  simp

private theorem b3_fgsa_retained3 : FGSA.Window.RetainedW p B3 2 B1 := by
  rw [FGSA.Window.RetainedW_def, b3_fgsa_window3]
  simp

private theorem b3_fgsa_bit : FGSA.Window.EntryBitW p B3 2 B1 3 := by
  exact FGSA.Window.entry_bit_insertW p B2 3 ⟨12⟩ 0 _ 2 B1
    b3_fgsa_retained2 b3_fgsa_retained3 bitRow
    (by simp [bitRow]) rfl

private theorem b3_fgsa_covered : FGSA.Window.CoveredW p B4 2 B1 := by
  rw [FGSA.Window.CoveredW_def]
  decide +kernel

private theorem b3_fgsa_evicted :
    ¬ FGSA.Window.RetainedW p B3 1 .genesis ∧ ¬ FGSA.Window.CoveredW p B3 1 .genesis := by
  simp only [FGSA.Window.RetainedW_def, FGSA.Window.CoveredW_def]
  decide +kernel

/-- The terminal wrapper applies its causal premise to the no-next-action guard. -/
private theorem b3_fgsa_terminal :
    FGSA.Window.RetainedW p B3 2 B1 ∨ FGSA.Window.CoveredW p B3 2 B1 := by
  exact FGSA.Window.terminalRetentionW p B2 B3 1 B1 10 0
    (preceq_parent_node _ _ _ _ _) b3_fgsa_retained2 (by decide +kernel)
    (by decide +kernel) (by intro _; decide +kernel)

private theorem b3_fgsa_wrong_key : ¬ FGSA.Window.EntryBitW p B3 2 B2 3 := by
  simp only [FGSA.Window.EntryBitW_def]
  decide +kernel

private theorem b3_fgsa_birth_bit_guard : ¬ FGSA.Window.EntryBitW p B3 3 B2 3 := by
  simp only [FGSA.Window.EntryBitW_def]
  decide +kernel

/-- The unchanged wire validity API still returns the exact decoded row. -/
private theorem b3_fgsa_decoded (σ : FGSA.Window.State (Fin p.n))
    (a : RowWire p.n) (valid : FGSA.Window.rowValidW σ a = true) :
    ∃ b, a.toRow? = some b :=
  FGSA.Window.rowValidW_decodes σ a valid

#print axioms b3_fgsa_window2
#print axioms b3_fgsa_window3
#print axioms b3_fgsa_retained2
#print axioms b3_fgsa_retained3
#print axioms b3_fgsa_bit
#print axioms b3_fgsa_covered
#print axioms b3_fgsa_evicted
#print axioms b3_fgsa_terminal
#print axioms b3_fgsa_wrong_key
#print axioms b3_fgsa_birth_bit_guard
#print axioms b3_fgsa_decoded
end AvailableChain.FGSA.Tests.P0b3
