module
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover

public section

/-! PC-SA [DC-WALK] adapters (pcsa34-r4.3 §5.0; plan C6). -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- Equal roots, trees, scores, and eligibility tests give equal heads. -/
theorem pcsa_headInTree_eq_of_inputs (p : Params) (src dst : State p.n)
    (cs ct : Option (PC p.n)) (Ts Tt : List Block)
    (rs ss rt st : List (GridCO.Wire p.n .root))
    (hroot : liveRoot p src cs = liveRoot p dst ct) (htree : Ts = Tt)
    (hscore : GridCO.goldfishScore src.base.blocks rs ss =
      GridCO.goldfishScore dst.base.blocks rt st)
    (helig : eligible p src rs ss = eligible p dst rt st) :
    headInTree p src cs Ts rs ss = headInTree p dst ct Tt rt st := by
  unfold headInTree
  rw [hroot, htree, hscore, helig]

/-- A PC-SA head extends its live root. -/
theorem pcsa_headInTree_extends_root (p : Params) (st : State p.n) (c : Option (PC p.n))
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    Block.Preceq (liveRoot p st c) (headInTree p st c tree raw support) := by
  exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _

/-- The head is the root or a stored tree member. -/
theorem pcsa_headInTree_mem_or_root (p : Params) (st : State p.n) (c : Option (PC p.n))
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    headInTree p st c tree raw support = liveRoot p st c ∨
      headInTree p st c tree raw support ∈ tree := by
  rcases @GridCO.ghostWalk_mem GridCO.slowLeasePolicy tree.eraseDups
    (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)
    tree.eraseDups.length (liveRoot p st c) with he | hm
  · exact Or.inl he
  · exact Or.inr (List.mem_eraseDups.mp hm)

/-- The walk covers a path with retained, eligible, strictly dominant children. -/
theorem pcsa_headInTree_covers_path (p : Params) (st : State p.n) (c : Option (PC p.n))
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (hc : Block.Compatible (liveRoot p st c) B)
    (hd : DominatedSuffix (liveRoot p st c) B tree
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) :
    Block.Preceq B (headInTree p st c tree raw support) := by
  exact walk_covers_of_dominated_suffix _ _ _ _ _ hc hd

/-- A terminal dominant path gives the exact head. -/
theorem pcsa_headInTree_exact_path (p : Params) (st : State p.n) (c : Option (PC p.n))
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) (B : Block)
    (ha : Block.Preceq (liveRoot p st c) B)
    (hd : DominatedSuffix (liveRoot p st c) B tree
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support))
    (hs : NoEligibleChild tree (eligible p st raw support) B) :
    headInTree p st c tree raw support = B := by
  exact walk_exact_of_dominated_suffix _ _ _ _ _ ha hd hs

/-- Z stays below the head. -/
theorem pcsa_headInTree_extends_Z (p : Params) (st : State p.n) (c : Option (PC p.n))
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root)) :
    Block.Preceq (eraseFG (controls p st).Z)
      (headInTree p st c tree raw support) :=
  block_preceq_trans (pcsa_liveRoot_extends_Z p st c)
    (pcsa_headInTree_extends_root p st c tree raw support)

/-- An active view target stays below the head. -/
theorem pcsa_headInTree_extends_view (p : Params) (st : State p.n) (v : PC p.n)
    (tree : List Block) (raw support : List (GridCO.Wire p.n .root))
    (hv : frameActive p st v = true) :
    Block.Preceq v.target (headInTree p st (some v) tree raw support) :=
  block_preceq_trans (pcsa_liveRoot_extends_view p st v hv)
    (pcsa_headInTree_extends_root p st (some v) tree raw support)

/-- FG ancestry lifting is reused through the FG-SA Shared import. -/
theorem pcsa_lift_walk_prefix {n : Nat} (B : SimplexFG.FGBlock (Fin n)) (a : Block)
    (ha : Block.Preceq a (eraseFG B)) :
    ∃ A, SimplexFG.FGBlock.Preceq A B ∧ eraseFG A = a := by
  simp only [pcsa_eraseFG_eq] at ha ⊢
  exact FGSA.geometry_lift_prefix B a ha

end AvailableChain.PCSA
end
