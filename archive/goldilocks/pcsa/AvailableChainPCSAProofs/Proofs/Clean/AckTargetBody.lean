module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit

public section

/-! C3 exact ack-target body before the freeze. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

omit [DecidableEq V] in
private theorem pcsa_c3_idxBefore_mono (rho : V2.D.Run V (pcsaWith m p c))
    (a b : Time) (hab : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hab)

/-- An honest positive-slot ack supplies an exact body at every node before the freeze. -/
theorem pcsa_ack_target_body_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (s : Slot) (i : Fin p.n) (r : BlockId) (hs : 0 < s)
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
      (SA.earlyTime p.toParams s)) (hz : SA.freezeTime p.toParams s ≤ cut) :
    ∃ B, B.slot = s ∧ B.root = r ∧ ∀ y ∈ rho.honest,
      B ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.base.blocks := by
  obtain ⟨k, hk, ho⟩ := he
  obtain ⟨B, hr, hn⟩ := pcsa_ack_emission_nTarget p c m E rho _ s i r _ k hk ho
  delta nTarget? at hn
  have htB := List.find?_some (p := fun b : Block => b.slot == s &&
    holdsN p (actView (clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.ack s)) i)).st (SA.earlyTime p.toParams s))) s b) hn
  have hsB : B.slot = s := beq_iff_eq.mp (Bool.and_eq_true_iff.mp htB).1
  have hmem : B ∈ (clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.ack s)) i)).st (SA.earlyTime p.toParams s)).base.blocks := by
    obtain ⟨o, _, hres⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hn)
    exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hres)).1
  have hbefore := pcsa_clock_body_scope p
    (fun b => b ∈ (V2.D.Run.stateBefore E rho k (rho.seatOf (.base (.ack s)) i)).st.base.blocks)
    _ _ (fun _ hm => hm) B hmem
  have hg : B ≠ .genesis := by
    intro hb
    have hzero : B.slot = 0 := hb ▸ rfl
    exact (Nat.ne_of_gt hs) (hsB.symm.trans hzero)
  obtain ⟨j, hjk, t, o, label, N, P, hj, hd, hB, hp, ha, hAccept⟩ :=
    pcsa_body_receipt_origin E rho h.valid k _ B hg hbefore
  have ht : t < SA.earlyTime p.toParams s := by
    by_contra hn
    have hklt := V2.D.Engine.tick_index_lt_delivery E rho h.valid.toScheduleWellFormed hk hj
      (le_of_not_gt hn)
    omega
  have htime : SA.earlyTime p.toParams s + E.Δ = SA.freezeTime p.toParams s := by
    rw [h.delta]
    change (4 * p.Δ * (s : Int) + 2 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hdeadline : t + E.Δ ≤ SA.freezeTime p.toParams s := by
    rw [← htime]
    simpa only [add_comm] using add_le_add_right (le_of_lt ht) E.Δ
  refine ⟨B, hsB, hr, ?_⟩
  intro y hy
  have hb := pcsa_body_relay_before_deadline E rho h hF hD j _ y hi hy t o label N P
    hj hd hp ha hAccept (hdeadline.trans hz)
  rw [hB, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hb
  have hm := pcsa_body_stateBefore_mono E rho h.noRestart y
    (pcsa_c3_idxBefore_mono rho _ _ hdeadline) hb
  rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hm
end AvailableChain.PCSA.Run

end
