module
public import AvailableChainFGSA.Model.RowValidity
public import AvailableChainFGSA.Proofs.Carrier -- shake: keep (re-export)
public import AvailableChainKitFG.RowBits
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainFGSA.Proofs.WindowValidity -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- R6 preserves every parent field except the slot. -/
@[simp] theorem parentFoldState_slot (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).s = s := rfl

/-- All rows use the same parent state. -/
theorem rowsValidForParent_iff (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    (rows : List (RowWire p.n)) :
    rowsValidForParent p P s rows = true ↔
      ∀ a ∈ rows, Window.rowValidW (parentFoldState p s P) a = true := by
  change rows.all (Window.rowValidW (parentFoldState p s P)) = true ↔ _
  simp only [List.all_eq_true]

/-- The slot is set before the fold but cannot change the R6 height test. -/
theorem rowsValidForParent_slot_irrel (p : Params) (P : FGBlock (Fin p.n))
    (s t : Slot) (rows : List (RowWire p.n)) :
    rowsValidForParent p P s rows = rowsValidForParent p P t rows := rfl

/-- A permutation keeps the common-parent validity test. -/
theorem rowsValidForParent_perm (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    {rows rows' : List (RowWire p.n)} (h : rows.Perm rows') :
    rowsValidForParent p P s rows = rowsValidForParent p P s rows' := by
  rw [Bool.eq_iff_iff, rowsValidForParent_iff, rowsValidForParent_iff]
  simp only [h.mem_iff]

/-- The initial store has no carried-row obligation. -/
theorem rowsValidStored_initial (p : Params) : RowsValidStored p (initial p.n) := by
  intro o ho
  exact (List.not_mem_nil ho).elim

/-- Converting a vote and restoring its body is exact. -/
theorem RowPayload.ofRow_toRow {V : Type} (a : RowPayload) (i : V) :
    RowPayload.vote (RowBody.ofRow (a.toRow i)) = a := by
  cases a with | vote b => cases b; rfl

/-- A matching target or progress row retains its bit while the height keys agree. -/
theorem row_bit_persist (p : Params) (target : Bool)
    (P W : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (body : Nat)
    (rows : List (Row (Fin p.n))) (b : Row (Fin p.n))
    (ha : b ∈ rows) (hCW : FGBlock.Preceq (.node P s r_s body rows) W)
    (hm : if target then b.height_pair = .vote (heightView p P).h (heightView p P).T_h.root false
      else b.height_pair.matchesEntry (heightView p P).h (heightView p P).T_h.root = true)
    (hk : (heightView p P).h = (heightView p W).h ∧
      (heightView p P).T_h.root = (heightView p W).T_h.root) :
    b.signer ∈ (if target then (heightView p W).target_participation
      else (heightView p W).progress) := by
  have hb : ∀ B, heightView p B = KitFG.heightOf (derive p.E p.cfg B) := heightView_bridge p
  simp only [hb, KitFG.heightOf_def] at hm hk ⊢
  cases target with
  | false => exact KitFG.bit_from_row p.E p.cfg .progress P W s r_s body rows b ha hCW hm hk
  | true => exact KitFG.bit_from_row p.E p.cfg .target P W s r_s body rows b ha hCW hm hk

end AvailableChain.FGSA
end
