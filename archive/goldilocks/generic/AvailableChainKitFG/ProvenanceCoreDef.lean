module
public import AvailableChainKitFG.CertificateCoreDef
public import AvailableChainSimplexFG.Client

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [RowCodec V]

/-- The exact justified pair and finalized height used at emission. -/
def certificateHeadFields
    (H : FGHeightView V) (f : FGFinalityView V)
    (Hd : FGBlock V) : HeadFields :=
  ⟨(H Hd).h_j, (H Hd).J.root, (f Hd).h_F⟩

theorem certificateHeadFields_def
    (H : FGHeightView V) (f : FGFinalityView V) (Hd : FGBlock V) :
    certificateHeadFields H f Hd =
      ⟨(H Hd).h_j, (H Hd).J.root, (f Hd).h_F⟩ := rfl

end AvailableChain.KitFG
end
