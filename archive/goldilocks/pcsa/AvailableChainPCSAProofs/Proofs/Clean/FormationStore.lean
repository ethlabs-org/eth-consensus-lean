module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainPCSAProofs.Proofs.Shared.TreeReceipt
public import AvailableChainFGSA.Proofs.WindowStore

public section

/-! Stored tree correspondence for Formation receipts and source selection. -/

namespace AvailableChain.PCSA
open AvailableChain.SimplexFG

/-- A held PC target is frame-active in a reachable stage-1 store. -/
theorem pcsa_formation_frame_active_of_target (p : Params) (st : State p.n) (C : PC p.n)
    (hReach : Reachable p st) (hFrame : Run.FrameVacuous p st)
    (hTarget : C.target ∈ st.base.blocks) : frameActive p st C = true := by
  rw [frameActive_def, pcsa_fullTree_of_frame p st hFrame]
  exact decide_eq_true ((pcsa_tree_correspondence p st hReach C.target).mp hTarget)

end AvailableChain.PCSA
end
