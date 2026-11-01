module
public import AvailableChainPCSAProofs.Proofs.Shared.GateReceipt

public section

/-! C3 composition with the open store facts as hypotheses.
This is not a proof of PCDisseminationClaim without those facts. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- Healthy delivery and the store boundaries give C3's after-ticks conclusion. -/
theorem pcsa_dissemination_of_store_facts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (hS : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (s : Slot) (r : BlockId) (Q : Finset (Fin p.n)) (hQ : pcQuorum p.n ≤ Q.card)
    (hacks : ∀ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
        (SA.earlyTime p.toParams s)) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hAdmit : ∀ y ∈ rho.honest, ∀ i ∈ Q, ∀ j t,
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i r) t →
      (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hMono : ∀ y ∈ rho.honest, ∀ j k, j ≤ k →
      (V2.D.Run.stateBefore E rho j y).st.ackPool ⊆
        (V2.D.Run.stateBefore E rho k y).st.ackPool)
    (hCollect : ∀ y ∈ rho.honest,
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target.root = r)
    (hKeep : ∀ y ∈ rho.honest,
      (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) :
    ∀ y ∈ rho.honest, ∃ C ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
      C.slot = s ∧ C.target.root = r := by
  have hp := pcsa_ack_quorum_pool_before_freeze E rho hD hS hdelta s r Q hQ hacks hc
    hAdmit hMono
  intro y hy
  obtain ⟨C, hC, hs, hr⟩ := hCollect y hy (hp.2 y hy) hQ
  exact ⟨C, hKeep y hy hC, hs, hr⟩

end AvailableChain.PCSA.Run
end
