module
public import AvailableChainFGSA.Proofs.WindowSelection -- shake: keep (examples)

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.Tests.Selection

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

local instance : DecidableEq (FGCertEntry (Fin 1)) := fun a b =>
  decidable_of_iff (a.j = b.j ∧ a.X = b.X ∧ a.Q = b.Q) (by cases a; cases b; simp)

abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- Progress first gives the oldest justification a non-genesis block. -/
def progressBlock : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨100⟩ 0 [⟨0, .vote 1 genesisRoot true, none⟩]

def birth1 : FGBlock (Fin 1) :=
  .node progressBlock 2 ⟨101⟩ 0 [⟨0, .vote 2 progressBlock.root false, none⟩]

def birth2 : FGBlock (Fin 1) :=
  .node birth1 3 ⟨102⟩ 0 [⟨0, .vote 3 birth1.root false, none⟩]

def olderChoice : FGBlock (Fin 1) :=
  .node birth2 4 ⟨103⟩ 0 [⟨0, .empty, some ⟨2, progressBlock.root⟩⟩]

/-- Two retained entries: only the lower one is ready. -/
example : (certificateSelection params 2).before olderChoice =
    [⟨2, progressBlock, {0}⟩, ⟨3, birth1, ∅⟩] ∧
    params.E.IsQuorum ({0} : Finset (Fin 1)) ∧ ¬ params.E.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide

/-- Selection moves F to the older entry and keeps the higher unready entry. -/
example : (certificateSelection params 2).chosen olderChoice =
      some ⟨2, progressBlock, {0}⟩ ∧
    (certificateFinality params 2 olderChoice).F = progressBlock ∧
    (certificateFinality params 2 olderChoice).h_F = 2 ∧
    (certificateFinality params 2 olderChoice.parent).F = .genesis ∧
    (certificateSelection params 2).afterPrune olderChoice = [⟨3, birth1, ∅⟩] := by decide

def birth3 : FGBlock (Fin 1) :=
  .node birth2 4 ⟨104⟩ 0 [⟨0, .vote 4 birth2.root false, none⟩]

def afterEviction : FGBlock (Fin 1) := .node birth3 5 ⟨105⟩ 0 []

set_option exponentiation.threshold 4096 in
/-- Pruning keeps both old entries. The third append then evicts the oldest. -/
example : (certificateSelection params 2).before birth3 =
      [⟨2, progressBlock, ∅⟩, ⟨3, birth1, ∅⟩] ∧
    (certificateSelection params 2).afterPrune birth3 =
      [⟨2, progressBlock, ∅⟩, ⟨3, birth1, ∅⟩] ∧
    (derive params 2 birth3).W = [⟨3, birth1, ∅⟩, ⟨4, birth2, ∅⟩] := by decide

set_option exponentiation.threshold 4096 in
/-- The evicted key is absent in both phases of the next block and has no coverage. -/
example :
    (∀ e ∈ (certificateSelection params 2).before afterEviction,
      ¬ (e.j = 2 ∧ e.X = progressBlock)) ∧
    (∀ e ∈ (certificateSelection params 2).afterPrune afterEviction,
      ¬ (e.j = 2 ∧ e.X = progressBlock)) ∧
    ¬ (2 ≤ (certificateFinality params 2 afterEviction).h_F) ∧
    ¬ FGBlock.Preceq progressBlock (certificateFinality params 2 afterEviction).F := by decide

end AvailableChain.FGSA.Window.Tests.Selection
end
