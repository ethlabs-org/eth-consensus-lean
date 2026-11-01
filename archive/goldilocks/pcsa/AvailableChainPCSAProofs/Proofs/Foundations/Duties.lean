module
public import AvailableChainPCSARun.Model.Protocol
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainKitV2.DutyEmission

public section

/-! Ack duty timing and uniqueness (pcsa34-r4.3 A6; proof plan §5).
The clock runs the previous gate before duties. The duty list places FG
before the ack. All duties read the state after the clock. -/

namespace AvailableChain.PCSA.Run

/-- Only the ack duty uses a slot's ack signing label. -/
theorem signLabel_ack_iff (d : RunDuty) (s : Slot) :
    d.signLabel = .base (.ack s) ↔ d = .ackAction s := by
  cases d <;> dsimp only [RunDuty.signLabel] <;> simp

/-- At the early time, the FG duty, if due, precedes the ack duty. -/
theorem pcsa_duties_early (p : Params) (s : Slot) :
    duties p (SA.earlyTime p.toParams s) =
      (if p.actionTime ((s - 1) / p.R) = SA.earlyTime p.toParams s then
        [.fgAction ((s - 1) / p.R)] else []) ++ [.ackAction s] := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hs : p.slotOf (SA.earlyTime p.toParams s) = s := by
    apply pcsa_slotOf_offset p s (2 * p.Δ) (by omega) (by omega)
  have hp : SA.proposalTime p.toParams s ≠ SA.earlyTime p.toParams s := by
    change 4 * p.Δ * s ≠ 4 * p.Δ * s + 2 * p.Δ
    intro h
    linarith
  have hv : SA.voteTime p.toParams s ≠ SA.earlyTime p.toParams s := by
    change 4 * p.Δ * s + p.Δ ≠ 4 * p.Δ * s + 2 * p.Δ
    intro h
    linarith
  simp only [duties, hs, hp, hv, ite_false, ite_true, List.nil_append]

/-- The early time of the next slot is the current slot's gate time. -/
theorem earlyTime_succ_eq_gateTime (p : Params) (s : Slot) :
    SA.earlyTime p.toParams (s + 1) = SA.gateTime p.toParams s := by
  change 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
  push_cast
  ring

/-- The previous gate is complete before the early-time duties read the store. -/
theorem clock_early_succ (p : Params) (st : State p.n) (s : Slot) :
    clock p st (SA.earlyTime p.toParams (s + 1)) =
      gateStep p (clockPre p st (SA.earlyTime p.toParams (s + 1))) s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hd : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    change ((4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ) / (4 * p.Δ)).toNat = s
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]
  have hn : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ
    rw [add_sub_cancel_right]
    positivity
  rw [earlyTime_succ_eq_gateTime]
  simp only [clock, hd, hn, decide_true, BEq.rfl, Bool.and_self, ite_true]

/-- The early tick runs the previous gate first, with FG before ack in the duty list. -/
theorem early_gate_duty_order (p : Params) (st : State p.n) (s : Slot) :
    clock p st (SA.earlyTime p.toParams (s + 1)) =
        gateStep p (clockPre p st (SA.earlyTime p.toParams (s + 1))) s ∧
      duties p (SA.earlyTime p.toParams (s + 1)) =
        (if p.actionTime (s / p.R) = SA.earlyTime p.toParams (s + 1) then
          [.fgAction (s / p.R)] else []) ++ [.ackAction (s + 1)] := by
  exact ⟨clock_early_succ p st s, by simpa using pcsa_duties_early p (s + 1)⟩

/-- The ack label fixes both its duty and its emission time. -/
theorem ack_emission_duty (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : ackObj p s i r ∈ V2.D.Run.emitsAt E rho k) :
    t = SA.earlyTime p.toParams s ∧
      actWith m p c ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t)
        (.ackAction s) (rho.input x t) = some (.ack r) := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.base (.ack s)) i (.ack r)).mp ho
  have hd := (signLabel_ack_iff d s).mp hl
  subst d
  exact ⟨ht.symm, ha⟩

/-- One tick and one ack duty give one root per slot and seat. -/
theorem ack_emission_unique (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hnd : rho.events.Nodup)
    (x : V) (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time)
    (h : V2.D.Run.emits E rho x (ackObj p s i r) t)
    (h' : V2.D.Run.emits E rho x (ackObj p s i r') t') :
    r = r' ∧ t = t' ∧ t = SA.earlyTime p.toParams s := by
  obtain ⟨k, hk, ho⟩ := h
  obtain ⟨k', hk', ho'⟩ := h'
  obtain ⟨ht, ha⟩ := ack_emission_duty p c m E rho x s i r t k hk ho
  obtain ⟨ht', ha'⟩ := ack_emission_duty p c m E rho x s i r' t' k' hk' ho'
  have he : t = t' := ht.trans ht'.symm
  cases he
  have hklt := (List.getElem?_eq_some_iff.mp hk).1
  have heq : k = k' := (List.Nodup.getElem?_inj hklt hnd).mp (hk.trans hk'.symm)
  subst k'
  have hr : some (Msg.ack r : Msg p.n) = some (Msg.ack r') := ha.symm.trans ha'
  exact ⟨by simpa only [Option.some.injEq, Msg.ack.injEq] using hr, rfl, ht⟩

end AvailableChain.PCSA.Run
end
