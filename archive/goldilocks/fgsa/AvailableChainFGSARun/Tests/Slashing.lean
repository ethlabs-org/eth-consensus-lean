module
public import AvailableChainFGSARun.Statements.Slashing -- shake: keep (examples)

/-! Small checks of the stored-chain evidence carrier. -/

namespace AvailableChain.FGSA.Run.Tests

open AvailableChain.SimplexFG

-- Genesis carries no row.
example (p : Params) {In : Type} (c : AppCodec In) :
    fgsaEvidence ((fgsa p c).init) = ∅ := by
  simp [fgsaEvidence, fgsa, initial, Store.init, chainRows]

-- A row held only in the pool is not stored-chain evidence.
example (p : Params) (a : RowWire p.n) :
    fgsaEvidence (⟨{ initial p.n with rowPool := [a] }, RecordOnce.initial⟩ : Node p) = ∅ := by
  simp [fgsaEvidence, initial, Store.init, chainRows]

-- A stored chain includes its parent's rows, even when its tip has no row.
example (p : Params) (a : Row (Fin p.n)) :
    fgsaEvidence (⟨{ initial p.n with fg := { Store.init with
      TF := {.node (.node .genesis 1 ⟨1⟩ 0 [a]) 2 ⟨2⟩ 0 []} } },
      RecordOnce.initial⟩ : Node p) = {a} := by
  simp [fgsaEvidence, chainRows]

end AvailableChain.FGSA.Run.Tests
