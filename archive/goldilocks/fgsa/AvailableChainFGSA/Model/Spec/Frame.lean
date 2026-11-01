module
public import AvailableChainFGSA.Model.Tree -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Window

@[expose] public section

namespace AvailableChain.FGSA.Spec

open AvailableChain.SimplexFG

/-- [spec 269–302, 468–495] FG state Σ, using the unchanged window representation.
Only accepted geometry belongs to this store; rejected full wires remain in `Spec.Wire`. -/
structure FGState (n : Nat) where
  accepted : Finset (FGBlock (Fin n))
  chainState : FGBlock (Fin n) → Window.State (Fin n)
  F : FGBlock (Fin n)
  J : FGBlock (Fin n)
  justifiedHeight : Nat
  maxHeight : Nat
  attestations : List (RowWire n)

/-- [spec 269–285, 468–495] Read Σ from the unchanged cumulative Lean store.
The immutable chain state is derived from each accepted block. -/
def fgStateOf (p : Params) (st : State p.n) : FGState p.n :=
  ⟨st.fg.TF, Window.derive p p.K_W, st.fg.F, st.fg.J,
    st.fg.h_j, st.fg.h_max, st.rowPool⟩

/-- [spec 306–324] The modular FG frame Φ. Well-formedness is a separate premise. -/
structure Frame (n : Nat) where
  tree : Finset (FGBlock (Fin n))
  F : FGBlock (Fin n)
  fcRoot : FGBlock (Fin n)
  allowed : Finset (FGBlock (Fin n))

/-- [spec 600–605] `fg_to_ac`, parameterized by the guarded root and height floor.
`Next.controls` supplies these in the guarded frame correspondence. -/
def frameOf (p : Params) (st : State p.n) (root : FGBlock (Fin p.n))
    (floor : Nat) (height : FGBlock (Fin p.n) → Nat) : Frame p.n :=
  let tree := st.fg.TF.filter (fun B => FGBlock.preceq st.fg.F B)
  ⟨tree, st.fg.F, root,
    tree.filter (fun B => FGBlock.preceq root B && decide (floor ≤ height B))⟩

/-- [spec 320–324, 1343–1345] The viable tree, with witnesses in the supplied tree. -/
def viableTree {n : Nat} (Φ : Frame n) (X : Finset (FGBlock (Fin n))) :
    Finset (FGBlock (Fin n)) :=
  X.filter (fun B => FGBlock.preceq Φ.fcRoot B &&
    decide (∃ W ∈ X, W ∈ Φ.allowed ∧ FGBlock.Preceq B W))

-- Generate equations in their owning model module (BUILD B3a).
private theorem fgStateOf_eq_1_export :
    type_of% (@fgStateOf.eq_1) := @fgStateOf.eq_1
private theorem frameOf_eq_1_export :
    type_of% (@frameOf.eq_1) := @frameOf.eq_1
private theorem viableTree_eq_1_export :
    type_of% (@viableTree.eq_1) := @viableTree.eq_1

end AvailableChain.FGSA.Spec
end
