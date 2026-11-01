module
public import AvailableChainFGSARun.Proofs.WindowExclusion -- shake: keep (examples)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.ExclusionTests

open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def firstRows : List (RowWire 4) :=
  [⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩,
   ⟨.seat .fg 1, .vote ⟨.vote 1 genesisRoot false, none⟩⟩,
   ⟨.seat .fg 2, .vote ⟨.vote 1 genesisRoot false, none⟩⟩]
private def first : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨2⟩ (packInner 0 firstRows) (firstRows.filterMap RowWire.toRow?)
private def row : Row (Fin 4) := ⟨3, .vote 2 first.root false, some ⟨1, genesisRoot⟩⟩
private def secondRows : List (RowWire 4) := [⟨.seat .fg 3, .vote (RowBody.ofRow row)⟩]
private def second : FGBlock (Fin 4) :=
  .node first 2 ⟨3⟩ (packInner 0 secondRows) (secondRows.filterMap RowWire.toRow?)

private def firstNamed : NamedProposal 4 :=
  .node .genesis 1 ⟨2⟩ (packBody 0 firstRows) [] [] firstRows

private def secondNamed : NamedProposal 4 :=
  .node firstNamed 2 ⟨3⟩ (packBody 0 secondRows) [] [] secondRows

private def object (s : Slot) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩

private def env : Generic.Env Unit := ⟨1, by decide, 0, by decide, fun _ _ => false⟩
private def run : V2.D.Run Unit (fgsa p unitCodec) :=
  { honest := {()}, horizon := 8,
    events := [.tick () 4, .deliver () (object 1 firstNamed) 4,
      .tick () 8, .deliver () (object 2 secondNamed) 8],
    seatOf := fun _ _ => (), input := fun _ _ => () }

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

private theorem checked : V2.D.DeliveryWellFormed env run := by
  constructor <;> intro i v o t event <;>
    cases i with
    | zero => cases event
    | succ i =>
      cases i with
      | zero => cases event; decide +kernel
      | succ i =>
        cases i with
        | zero => cases event
        | succ i =>
          cases i with
          | zero => cases event; decide +kernel
          | succ i =>
            change (none : Option (V2.Event Unit (Obj p))) = some (.deliver v o t) at event
            cases event

/-- ROOT-DIGEST W3b. Both complete packed proposals pass wire checks and actual admission.
The stored two-block chain has the decoded rows used by the transfer. -/
example : (fgsa p unitCodec).wellFormed (object 1 firstNamed) = true ∧
    (fgsa p unitCodec).wellFormed (object 2 secondNamed) = true ∧
    second ∈ (V2.D.Run.stateBefore env run 4 ()).st.fg.TF ∧
    first ∈ (V2.D.Run.stateBefore env run 4 ()).st.fg.TF ∧
    second.rows = [row] := by decide +kernel

/-- ROOT-DIGEST W3b. The model invariant supplies R6W for EVERY decoded row of the admitted second
block, read at its parent. -/
example : ∀ a ∈ secondRows.filterMap RowWire.toRow?,
    Window.r6w (Window.derive p p.K_W first) a = true := fun a ha =>
  stored_r6wW p (reachable_stateBefore env run 4 ()) first 2 ⟨3⟩
    (packInner 0 secondRows) (secondRows.filterMap RowWire.toRow?)
    (by decide +kernel) a ha

/-- ROOT-DIGEST W3b. The B1 transfer discharges both ancestor-row conditions. The fold retains the
key (1, genesis) at the stored second block; its bits are NOT written here: the
theorem shows that the exact second-block occurrence has set the signer's bit. -/
example : ∃ d ∈ (Window.derive p p.K_W second).W,
    d.j = 1 ∧ d.X = .genesis ∧ row.signer ∈ d.Q := by
  obtain ⟨d, hd, hj, hX⟩ :
      ∃ d ∈ (Window.derive p p.K_W second).W, d.j = 1 ∧ d.X = .genesis := by
    decide +kernel
  exact ⟨d, hd, hj, hX, exact_row_exclusion_checkedW env run checked 4 () second
    (by decide +kernel) 1 .genesis d hd hj hX first 2 ⟨3⟩
    (packInner 0 secondRows) (secondRows.filterMap RowWire.toRow?)
    (preceq_refl _) row (by decide +kernel) (by decide +kernel)⟩

end AvailableChain.FGSA.Run.ExclusionTests
end
