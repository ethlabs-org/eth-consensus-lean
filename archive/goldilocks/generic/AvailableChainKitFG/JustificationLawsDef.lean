module
public import AvailableChainKitFG.HeightCoreDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

structure FGJustificationLaws {V : Type} (H : FGHeightView V) : Prop where
  J_entry :
    ∀ C, (H (H C).J).T_h = (H C).J
  J_height :
    ∀ C, (H C).h_j ≠ 0 → (H (H C).J).h = (H C).h_j
  J_zero :
    ∀ C, (H C).h_j = 0 → (H C).J = .genesis

end AvailableChain.KitFG
end
