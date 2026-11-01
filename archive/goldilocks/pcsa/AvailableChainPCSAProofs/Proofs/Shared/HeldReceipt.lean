module
public import AvailableChainPCSAProofs.Proofs.Shared.Relay

public section

/-! C3 receipt-to-pool boundary (pcsa34-r4.3 §5.2.3).
Admission and pool preservation are explicit store hypotheses. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- An honest early ack is in the receiver's strict pre-freeze pool.
The store hypotheses cover honest ack admission, including carried receipt,
and preservation through the intervening events. -/
theorem pcsa_ack_pool_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (hS : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (s : Slot) (i : Fin p.n) (r : BlockId) (y : V)
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
      (SA.earlyTime p.toParams s)) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hAdmit : ∀ j t, SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i r) t →
      (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hMono : ∀ j k, j ≤ k → (V2.D.Run.stateBefore E rho j y).st.ackPool ⊆
      (V2.D.Run.stateBefore E rho k y).st.ackPool) :
    (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.ackPool := by
  obtain ⟨t, het, htz, j, hh⟩ := pcsa_ack_handled_before_freeze E rho hD hdelta
    s i r y hi hy he hc
  have hp := hAdmit j t het htz hh
  obtain ⟨parent, hj, _⟩ := hh
  have hjz : j < V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mpr htz
  have hm := hMono (j + 1) _ (Nat.succ_le_of_lt hjz) hp
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm
  exact hm

/-- A quorum of honest early acks is in every honest pre-freeze pool.
This is the C3 network step; no awake premise is needed for the receiver. -/
theorem pcsa_ack_quorum_pool_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (hS : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (s : Slot) (r : BlockId) (Q : Finset (Fin p.n))
    (hQ : pcQuorum p.n ≤ Q.card)
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
        (V2.D.Run.stateBefore E rho k y).st.ackPool) :
    pcQuorum p.n ≤ Q.card ∧ ∀ y ∈ rho.honest, ∀ i ∈ Q,
      (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.ackPool := by
  refine ⟨hQ, ?_⟩
  intro y hy i hi
  exact pcsa_ack_pool_before_freeze E rho hD hS hdelta s i r y
    (hacks i hi).1 hy (hacks i hi).2 hc (hAdmit y hy i hi) (hMono y hy)

end AvailableChain.PCSA.Run
end
