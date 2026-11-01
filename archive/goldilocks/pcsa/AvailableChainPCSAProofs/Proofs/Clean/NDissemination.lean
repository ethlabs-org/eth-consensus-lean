module
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot
public import AvailableChainPCSAProofs.Proofs.Clean.NNextHead

public section

/-! C6 NDissemination: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Prior dissemination and result coverage imply current-ack dissemination to next HEADs. -/
theorem pcsa_ack_dissemination_step (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (s : Slot) (hc : SA.gateTime p.toParams s ≤ cut)
    (hpast : ∀ y H, HonestHeadAt p c E rho y s H →
      ∀ x ∈ rho.honest, ∀ i X, i < s →
        gateResultAt p c E rho x i = some (some X) → Block.Preceq X H)
    (hdis : ∀ i, i < s → ∀ y A, HonestAckAt p c E rho y i A →
      ∀ z H, HonestHeadAt p c E rho z s H → Block.Preceq A H)
    (x y : V) (B H : Block) (hB : HonestAckAt p c E rho x s B)
    (hH : HonestHeadAt p c E rho y (s + 1) H) : Block.Preceq B H := by
  apply pcsa_honestAck_next_head_of_root E rho h hF hFault x y s B H hc hB hH
  intro R hR
  exact Bool.or_eq_true_iff.mpr (Or.inl
    (pcsa_ack_next_root_below E rho h.base hF hFault s hpast hdis y x hH.1 B R hB hR))
end AvailableChain.PCSA.Run

end
