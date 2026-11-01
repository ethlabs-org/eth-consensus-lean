module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyScope
public import AvailableChainPCSAProofs.Proofs.Shared.BodyReceipt
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! Body scope for Formation walks. Shared supplies the run scope and the
handler rule. -/

namespace AvailableChain.PCSA

/-- Accepted body predicates persist through every handler. -/
theorem pcsa_formation_process_body_scope (p : Params) (B : Block → Prop)
    (st : State p.n) (o : Wire p.n) (h : ∀ b ∈ st.base.blocks, B b)
    (ho : ∀ s N, o.decode = some (.block s N) →
      ∀ P, blockAccepted p st s N P = true → B N.erase) :
    ∀ b ∈ (process p st o).base.blocks, B b :=
  pcsa_c3_process_body_pred p B st o h (fun s N P hd _ ha => ho s N hd P ha)

end AvailableChain.PCSA
end
