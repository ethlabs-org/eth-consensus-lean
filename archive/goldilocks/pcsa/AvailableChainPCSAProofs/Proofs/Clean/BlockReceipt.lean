module
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt
public import AvailableChainFGSARun.Proofs.SelfDelivery

public section

/-! C6 BlockReceipt: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A body held at an inclusive read reaches every later after-ticks read within Delta. -/
theorem pcsa_body_storeAt_relay (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (T t : Time) (B : Block)
    (hc : T + E.Δ ≤ cut) (ht : T + E.Δ ≤ t)
    (hB : B ∈ (storeAt p c E rho x T).base.blocks) :
    B ∈ (storeAfterTicks p c E rho y t).base.blocks := by
  have hS := h.valid.toScheduleWellFormed
  rw [storeAfterTicks_def]
  change B ∈ (FGSA.Run.afterTicks E rho t y).st.base.blocks
  erw [FGSA.Run.afterTicks_eq_stateBefore E rho hS]
  by_cases hg : B = .genesis
  · subst B
    exact (pcsa_genesis_body_stamp E rho h.noRestart _ y).1
  · rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hS] at hB
    obtain ⟨k, hk, u, o, s, N, P, he, hd, hN, hpar, hacc, haccepted⟩ :=
      pcsa_body_receipt_origin E rho h.valid _ x B hg hB
    have hu := (V2.D.Engine.index_lt_read_length_iff hS T he).mp hk
    have huc : u + E.Δ ≤ cut := (Int.add_le_add hu (Int.le_refl E.Δ)).trans hc
    have hrecv := pcsa_body_relay_before_deadline E rho h hF hD k x y hx hy u o s N P
      he hd hpar hacc haccepted huc
    rw [hN, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hrecv
    have hut : u + E.Δ ≤ t := (Int.add_le_add hu (Int.le_refl E.Δ)).trans ht
    have hidx : V2.D.Run.idxBefore rho (u + E.Δ) ≤ FGSA.Run.afterTicksIdx rho t := by
      apply le_trans _ (FGSA.Run.preIdx_le_afterTicksIdx E rho hS t).1
      change (rho.events.filter (fun e => decide (e.time < u + E.Δ))).length ≤
        (rho.events.filter (fun e => decide (e.time < t))).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left (fun e _ hh =>
        decide_eq_true (lt_of_lt_of_le (of_decide_eq_true hh) hut))
    exact pcsa_body_stateBefore_mono E rho h.noRestart y hidx hrecv
end AvailableChain.PCSA.Run

end
