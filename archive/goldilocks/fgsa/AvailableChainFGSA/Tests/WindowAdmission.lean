module
public import AvailableChainFGSA.Proofs.Admission -- shake: keep (examples)
public import AvailableChainFGSA.Proofs.EmissionFields -- shake: keep (examples)

set_option linter.privateModule false

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.AdmissionTests

open AvailableChain.SimplexFG hiding derive on_block

private abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def wire (h : Nat) (X : FGBlock (Fin 1))
    (fp : Option FinalityPair := none) : RowWire 1 :=
  ⟨.seat .fg 0, .vote ⟨.vote h X.root false, fp⟩⟩

private def packed (P : FGBlock (Fin 1)) (s : Slot) (rows : List (RowWire 1)) :
    FGBlock (Fin 1) :=
  .node P s ⟨s + 1⟩ (packInner 0 rows) (rows.filterMap RowWire.toRow?)

private def first : FGBlock (Fin 1) := packed .genesis 1 [wire 1 .genesis]
private def second : FGBlock (Fin 1) := packed first 2 [wire 2 first]
private def third : FGBlock (Fin 1) := packed second 3 [wire 3 second]
private def stale : RowWire 1 := wire 3 second (some ⟨2, first.root⟩)
private def child : FGBlock (Fin 1) := packed third 4 [stale]
private def nfirst : NamedProposal 1 := namedProposal p .genesis 1 0 [] [] [wire 1 .genesis]
private def nsecond : NamedProposal 1 := namedProposal p nfirst 2 0 [] [] [wire 2 first]
private def nthird : NamedProposal 1 := namedProposal p nsecond 3 0 [] [] [wire 3 second]
private def nchild (rows : List (RowWire 1)) : NamedProposal 1 :=
  namedProposal p nthird 4 0 [] [] rows
private def before : FGSA.State 1 :=
  { (FGSA.initial 1) with
    fg := [first, second, third].foldl (on_block p 2) SimplexFG.Store.init
    proposals := [⟨.proposer 1, .proposal nfirst⟩, ⟨.proposer 2, .proposal nsecond⟩,
      ⟨.proposer 3, .proposal nthird⟩]
    base := { (FGSA.initial 1).base with
      now := 100
      blocks := [.genesis, eraseFG first, eraseFG second, eraseFG third] } }

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- Useful stale rows pass actual admission on the window parent. -/
example : blockAccepted p before 4 (nchild [stale]) third = true := by decide +kernel

/-- Unmatched stale, future-height, and wrong-current-entry rows fail admission. -/
example :
    let bad := wire 3 second (some ⟨1, genesisRoot⟩)
    let future := wire 5 third
    let wrong := wire 4 first (some ⟨2, first.root⟩)
    rowsValidForParent p third 4 [bad] = false ∧
    rowsValidForParent p third 4 [future] = false ∧
    rowsValidForParent p third 4 [wrong] = false ∧
    blockAccepted p before 4 (nchild [bad]) third = false ∧
    blockAccepted p before 4 (nchild [future]) third = false ∧
    blockAccepted p before 4 (nchild [wrong]) third = false := by
  decide +kernel

/-- Both rows use the same parent. The first row's quorum does not advance the validation state. -/
example :
    let rows := [wire 4 third, stale]
    blockAccepted p before 4 (nchild rows) third = true := by
  decide +kernel

/-- K = 2 evicts height 1. Finalizing the older retained entry prunes only height 2. -/
example : (derive p 2 third).W = [⟨2, first, ∅⟩, ⟨3, second, ∅⟩] ∧
    (derive p 2 child).W = [⟨3, second, ∅⟩] ∧
    (derive p 2 child).F = first ∧
    (SimplexFG.derive p.E p.cfg child).F = .genesis := by decide +kernel

/-- A current-height row can name an older entry. Finality precedes target append. -/
example :
    let row := wire 4 third (some ⟨2, first.root⟩)
    let B := packed third 4 [row]
    blockAccepted p before 4 (nchild [row]) third = true ∧
    heightMatch (parentFoldState p 4 third) (row.payload.toRow 0) = true ∧
    (derive p 2 B).F = first ∧ (derive p 2 B).J = third ∧
    (derive p 2 B).W = [⟨3, second, ∅⟩, ⟨4, third, ∅⟩] := by decide +kernel

/-- Actual composite admission advances F from an older retained certificate. -/
example : (admitBlock p before 4 (nchild [stale])).fg.F = first ∧
    (SimplexFG.on_block p.E p.cfg before.fg child).F = .genesis := by
  decide +kernel

/-- The head-field projection reads window h_F, which differs from the old fold. -/
example : headFields p 2 child = ⟨3, second.root, 2⟩ ∧
    HeadFields.ofBlock p.E p.cfg child = ⟨3, second.root, 0⟩ := by decide +kernel

/-- The composite client reads the window finality height of its selected head. -/
example :
    let st : FGSA.State 1 := { before with
      fg := { TF := {child}, F := child, J := child, h_j := 3, h_max := 4 }
      base := { before.base with blocks := [eraseFG child] } }
    (fgInputs p st).2.h_F = 2 := by decide +kernel

end AvailableChain.FGSA.Window.AdmissionTests
end
