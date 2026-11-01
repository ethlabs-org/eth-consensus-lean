module
public import AvailableChainPCSAProofs.Proofs.Clean.NCounts
public import AvailableChainPCSAProofs.Proofs.Clean.NRoot

public section

/-! C6 AckResults: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Prior-result and prior-ack coverage make every bounded ack/result pair compatible. -/
theorem pcsa_ack_result_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Slot) (hc : SA.gateTime p.toParams j ≤ cut)
    (hpast : ∀ k, k ≤ j → ∀ z H, HonestHeadAt p c E rho z k H →
      ∀ y ∈ rho.honest, ∀ i X, i < k →
        gateResultAt p c E rho y i = some (some X) → Block.Preceq X H)
    (hdis : ∀ k i, k < i → i ≤ j → ∀ z B, HonestAckAt p c E rho z k B →
      ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Preceq B X)
    (s : Slot) (hs : s ≤ j) (z : V) (B : Block) (ha : HonestAckAt p c E rho z s B)
    (i : Slot) (hi : i ≤ j) (y : V) (hy : y ∈ rho.honest) (X : Block)
    (hX : gateResultAt p c E rho y i = some (some X)) : Block.Compatible B X := by
  rcases lt_trichotomy s i with hlt | heq | hgt
  · exact Bool.or_eq_true_iff.mpr (Or.inl (hdis s i hlt hi z B ha y hy X hX))
  · subst i
    have hcut : SA.gateTime p.toParams s ≤ cut := by
      apply le_trans _ hc
      change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + 6 * p.Δ
      have hle := Int.ofNat_le.mpr hs
      have hp : (0 : Int) < p.Δ := p.deltaPos
      nlinarith
    exact pcsa_honestAck_same_label_result E rho h hF hFault z y hy s B X hcut ha hX
  · obtain ⟨u, hu⟩ := pcsa_ack_has_honest_head E rho h.base hF hFault z s B ha
    exact Bool.or_eq_true_iff.mpr (Or.inr (hpast s hs u B hu y hy i X hgt hX))
end AvailableChain.PCSA.Run

end
