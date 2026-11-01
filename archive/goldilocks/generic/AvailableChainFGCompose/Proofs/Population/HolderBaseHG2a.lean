module
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)

private theorem p0d5b_hg2a_action (hT : FGTimingLaws T) (r : Nat) :
    T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
  rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
  unfold FGCompose.P
  push_cast
  ring

theorem frontierSearch_hg2a_bound_core (hT : FGTimingLaws T) (G ΔF d a tU : Time)
    (hbound : LivenessBoundW T ΔF) (ha : a ≤ d + FGCompose.P T - 4 * T.delta)
    (hU : tU ≤ d - 6 * T.delta) :
    max (a + Γ T G - T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤
        d + (2 * FGCompose.P T + Γ T G - 9 * T.delta) := by
  have he : epsF T ΔF ≤ FGCompose.P T - 8 * T.delta := by
    have hk : (kappaF T ΔF : Time) ≤ T.roundSlots := by exact_mod_cast hbound.kappa_le_R
    change 4 * (kappaF T ΔF : Time) * T.delta - 8 * T.delta ≤
      4 * (T.roundSlots : Time) * T.delta - 8 * T.delta
    nlinarith [hT.delta_pos]
  apply max_le <;> linarith [hT.delta_pos]

theorem frontierSearch_hg2a_gate_cost_core (G ΔF a tU : Time) :
    max (a + Γ T G + 4 * T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G + 2 * T.delta) =
    max (a + Γ T G - T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G - 3 * T.delta) + 5 * T.delta := by
  rw [← max_add_add_right]
  congr 1 <;> ring

omit [DecidableEq V] in
theorem frontierSearch_hg2a_gap_core (hT : FGTimingLaws T) {G ΔF : Time}
    (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (r : Nat) (U : FGBlock (Fin n)) (hgst : E.t_GST ≤ (r : Time) * FGCompose.P T)
    (hhor : max (T.action r + Γ T G - T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤ rho.horizon) :
    let U_F := max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < T.proposal s ∧
      T.proposal s ≤ U_F + Γ T G ∧
      Gen.V2.Duty.HonestSlot rho I s ∧
      T.proposal s + T.delta ≤
        max (T.action r + Γ T G - T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ∧
      T.gate s ≤
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) := by
  have hF : 0 ≤ ΔF := by
    rw [hdelta] at deltaF
    linarith [hT.delta_pos]
  have hwin : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon := by
    have := (healing_promotion_gap_remainder T hT G).1
    rw [← max_add_add_right]
    obtain ⟨ha, hU⟩ := max_le_iff.mp hhor
    rw [p0d5b_hg2a_action T hT] at ha
    unfold epsF at ha
    apply max_le <;> linarith [hT.delta_pos]
  exact healing_promotion_age_gap T hT I E rho gap hF r U.slot hgst hwin

end AvailableChain.FGCompose
end
