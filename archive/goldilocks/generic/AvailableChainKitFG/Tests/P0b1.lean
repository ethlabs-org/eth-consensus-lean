module
public import AvailableChainKitFG.WindowTransport -- shake: keep (axioms)
public import AvailableChainKitFG.WindowEntriesDef -- shake: keep (axioms)

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.P0b1

open AvailableChain.SimplexFG hiding derive process_row
open AvailableChain.SimplexFG.Window

private def E : Electorate (Fin 4) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
private def cfg : FGConfig := ⟨0⟩
private def B : FGBlock (Fin 4) := .node .genesis 3 ⟨17⟩ 0 []
private def voters : Finset (Fin 4) := {0, 1, 2}

/-- A stale height pair can set finality without changing the height bits. -/
private theorem stale_finality :
    let w : State (Fin 4) := { initial with h := 4, W := [⟨1, .genesis, ∅⟩] }
    let a : Row (Fin 4) := ⟨0, .vote 2 genesisRoot true, some ⟨1, genesisRoot⟩⟩
    r6w w a = true ∧ (process_row w a).W = [⟨1, .genesis, {0}⟩] ∧
      (process_row w a).target_participation = ∅ ∧ (process_row w a).progress = ∅ := by
  decide +kernel

/-- When both guards hold, the target appends a justification. -/
private theorem target_priority :
    let w : State (Fin 4) :=
      { initial with L := B, s := 3, target_participation := voters, progress := voters }
    let out := process_height_events E cfg 2 w
    out.h = 2 ∧ out.h_j = 1 ∧ out.W = [⟨1, .genesis, ∅⟩] ∧
      out.target_participation = ∅ ∧ out.progress = ∅ := by
  decide +kernel

/-- A progress quorum with zero delay advances at the entry's slot. -/
private theorem zero_delay :
    let w : State (Fin 4) := { initial with progress := voters }
    let out := process_height_events E cfg 2 w
    out.h = 2 ∧ out.h_j = 0 ∧ out.W = [] ∧ out.progress = ∅ ∧
      (process_height_events E ⟨1⟩ 2 w).h = 1 := by
  decide +kernel

/-- Capacity drops the oldest entry; eviction does not finalize it. -/
private theorem eviction :
    let w : State (Fin 4) :=
      { initial with
        h := 3, T_h := B, target_participation := voters
        W := [⟨1, .genesis, ∅⟩, ⟨2, B, ∅⟩] }
    let out := process_height_events E cfg 2 w
    out.W = [⟨2, B, ∅⟩, ⟨3, B, ∅⟩] ∧ out.h_F = 0 ∧ out.F = .genesis := by
  decide +kernel

/-- Finality prunes before append, and a new entry starts with no bits. -/
private theorem prune_before_append :
    let w : State (Fin 4) :=
      { initial with
        h := 3, T_h := B, target_participation := voters
        W := [⟨1, .genesis, ∅⟩, ⟨2, B, voters⟩] }
    let out := process_height_events E cfg 2 w
    out.W = [⟨3, B, ∅⟩] ∧ out.h_F = 2 ∧ out.F = B := by
  decide +kernel

/-- Weighted quorum is supported independently of an AC population. -/
private theorem weighted_target :
    let weighted : Electorate (Fin 2) :=
      ⟨fun i => if i = 0 then 3 else 1, fun i => by split <;> decide⟩
    let w : State (Fin 2) := { initial with target_participation := {0} }
    (process_height_events weighted cfg 2 w).h_j = 1 := by
  decide +kernel

#print axioms stale_finality
#print axioms target_priority
#print axioms zero_delay
#print axioms eviction
#print axioms prune_before_append
#print axioms weighted_target
#print axioms WindowFoldMap.fold_eq
#print axioms WindowFoldMap.view_eq
#print axioms WindowFoldMap.foldMap_height_eq
#print axioms WindowFoldMap.foldMap_finality_eq

end AvailableChain.KitFG.Tests.P0b1
