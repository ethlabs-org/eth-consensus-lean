module
public import AvailableChainFGSA.Proofs.WindowHistory -- shake: keep (examples)
public import AvailableChainFGSA.Proofs.WindowProvenance -- shake: keep (examples)

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.HistoryTests

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

abbrev params : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def targets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

def derived1 : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 (targets 1 .genesis)
def derived2 : FGBlock (Fin 4) := .node derived1 2 ⟨101⟩ 0 (targets 2 derived1)

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- This row was emitted while the first pair was latest. Its height pair
is stale when the second justification has entered the window. -/
def oldVote (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 2 derived1.root false, some ⟨1, genesisRoot⟩⟩

def bits1 : FGBlock (Fin 4) := .node derived2 3 ⟨102⟩ 0 [oldVote 0]
def bits2 : FGBlock (Fin 4) := .node bits1 4 ⟨103⟩ 0 [oldVote 1]

/-- A retained entry gains bits without a gap. -/
example : (derive params 2 derived2).W = [⟨1, .genesis, ∅⟩, ⟨2, derived1, ∅⟩] ∧
    (derive params 2 bits1).W = [⟨1, .genesis, {0}⟩, ⟨2, derived1, ∅⟩] ∧
    (derive params 2 bits2).W = [⟨1, .genesis, {1, 0}⟩, ⟨2, derived1, ∅⟩] := by decide +kernel

example : ∃ b ∈ (derive params 2 bits1).W, b.j = 1 ∧ b.X = .genesis ∧
    (∅ : Finset (Fin 4)) ⊆ b.Q ∧ b.Q ⊆ {1, 0} :=
  window_retained_bits_mono params 2 (by decide +kernel) derived2 bits1 bits2
    (by decide +kernel) (by decide +kernel) ⟨1, .genesis, ∅⟩ ⟨1, .genesis, {1, 0}⟩
    (by decide +kernel) (by decide +kernel) rfl rfl

/-- The stale arm accepts the earlier row and changes the older entry. -/
example : finality_pair Record.initial
      (certificateHeadFields (certificateHeight params 2) (certificateFinality params 2)
        derived1) = (oldVote 0).finality_pair ∧
    heightMatch (derive params 2 derived2) (oldVote 0) = false ∧
    staleUseful (derive params 2 derived2) (oldVote 0) = true ∧
    r6w (derive params 2 derived2) (oldVote 0) = true := by decide +kernel

def finals (j : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .empty, some ⟨j, X.root⟩⟩, ⟨1, .empty, some ⟨j, X.root⟩⟩,
   ⟨2, .empty, some ⟨j, X.root⟩⟩]

def cover2 : FGBlock (Fin 4) := .node derived2 3 ⟨104⟩ 0 (finals 2 derived1)

/-- The older entry is covered by a strictly higher finalization. The
latest pair remains even though its own entry has been pruned. -/
example : (derive params 2 cover2).W = [] ∧ (derive params 2 cover2).h_F = 2 ∧
    (derive params 2 cover2).F = derived1 ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive params 2 cover2).F ∧
    (derive params 2 cover2).h_j = 2 ∧ (derive params 2 cover2).J = derived1 ∧
    finality_pair Record.initial
      (certificateHeadFields (certificateHeight params 2) (certificateFinality params 2)
        cover2) = none := by decide +kernel

def evict3 : FGBlock (Fin 4) := .node derived2 3 ⟨105⟩ 0 (targets 3 derived2)

/-- Three justifications with K = 2 evict the first key without coverage. -/
example : (derive params 2 evict3).W = [⟨2, derived1, ∅⟩, ⟨3, derived2, ∅⟩] ∧
    (derive params 2 evict3).h_F = 0 ∧ ¬ (1 ≤ (derive params 2 evict3).h_F) ∧
    (derive params 2 evict3).h_j = 3 := by decide +kernel

def laterCover : FGBlock (Fin 4) := .node evict3 4 ⟨106⟩ 0 (finals 3 derived2)

/-- The same evicted key becomes covered by a later finalization. -/
example : (derive params 2 laterCover).h_F = 3 ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive params 2 laterCover).F ∧
    (derive params 2 laterCover).W = [] := by decide +kernel

/-- `window_entry_history` puts the first key in the EVICTED case at `evict3`. -/
example : (¬ ∃ d ∈ (derive params 2 evict3).W, d.j = 1 ∧ d.X = .genesis) ∧
    (derive params 2 evict3).h_F < 1 := by
  rcases window_entry_history params 2 (by decide) derived2 evict3 (by decide +kernel)
      ⟨1, .genesis, ∅⟩ (by decide +kernel) with
    ⟨d, hd, hj, hX, -⟩ | ⟨-, hle, -⟩ | ⟨hgone, -, hlt, -⟩
  · exact absurd ⟨d, hd, hj, hX⟩
      (by decide +kernel : ¬ ∃ d ∈ (derive params 2 evict3).W, d.j = 1 ∧ d.X = .genesis)
  · exact absurd hle (by decide +kernel : ¬ (1 ≤ (derive params 2 evict3).h_F))
  · exact ⟨hgone, hlt⟩

/-- The same key is in the COVERED case at `laterCover`. -/
example : (¬ ∃ d ∈ (derive params 2 laterCover).W, d.j = 1 ∧ d.X = .genesis) ∧
    1 ≤ (derive params 2 laterCover).h_F ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive params 2 laterCover).F := by
  rcases window_entry_history params 2 (by decide) derived2 laterCover (by decide +kernel)
      ⟨1, .genesis, ∅⟩ (by decide +kernel) with
    ⟨d, hd, hj, hX, -⟩ | ⟨hgone, hle, hcov⟩ | ⟨-, -, hlt, -⟩
  · exact absurd ⟨d, hd, hj, hX⟩
      (by decide +kernel : ¬ ∃ d ∈ (derive params 2 laterCover).W, d.j = 1 ∧ d.X = .genesis)
  · exact ⟨hgone, hle, hcov⟩
  · exact absurd hlt (by decide +kernel : ¬ ((derive params 2 laterCover).h_F < 1))

def olderReady : FGBlock (Fin 4) := .node bits2 5 ⟨107⟩ 0 [oldVote 2]

/-- A ready older entry exists in the prefinality fold. The latest-pair
fields still select the newer pair. This phase is not an admitted head state. -/
example : (certificateFolded params 2 olderReady).W =
      [⟨1, .genesis, {2, 1, 0}⟩, ⟨2, derived1, ∅⟩] ∧
    finality_pair Record.initial
      (certificateHeadFields
        (fun _ => projectHeight (certificateFolded params 2 olderReady))
        (fun _ => projectFinality (certificateFolded params 2 olderReady)) olderReady) =
      some ⟨2, derived1.root⟩ ∧
    (derive params 2 olderReady).h_F = 1 ∧
    finality_pair Record.initial
      (certificateHeadFields (certificateHeight params 2) (certificateFinality params 2)
        olderReady) = some ⟨2, derived1.root⟩ := by decide +kernel

/-- A ready-but-unfinalized entry cannot exist in a derived head post-state. -/
example (B : FGBlock (Fin 4)) (e : Entry (Fin 4)) (he : e ∈ (derive params 2 B).W) :
    ¬ params.E.IsQuorum e.Q := window_post_not_ready params 2 (by decide +kernel) B e he

end AvailableChain.FGSA.Window.HistoryTests
end
