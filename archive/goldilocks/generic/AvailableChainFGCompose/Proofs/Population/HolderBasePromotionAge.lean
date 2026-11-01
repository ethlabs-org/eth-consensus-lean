module
public import AvailableChainFGCompose.Statements.FrontierSearch
public import Mathlib.Tactic.Linarith -- shake: keep (arithmetic tactics)
public import Mathlib.Tactic.Ring -- shake: keep (ring tactic)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)

private theorem p0d5b_age_proposal (hT : FGTimingLaws T) (s : Slot) :
    T.proposal s = 4 * T.delta * (s : Time) := by rw [hT.proposal_eq]; ring

private theorem p0d5b_age_action (hT : FGTimingLaws T) (r : Nat) :
    T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
  rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
  unfold FGCompose.P
  push_cast
  ring

private theorem p0d5b_age_kappa_two (hT : FGTimingLaws T) (ΔF : Time) (hF : 0 ≤ ΔF) :
    (2 : Time) ≤ kappaF T ΔF := by
  have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
  have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
    have hd1 : (1 : Time) ≤ T.delta := hT.delta_pos
    linarith
  have hc : 6 * T.delta + ΔF ≤ (kappaF T ΔF : Time) * (4 * T.delta) := by
    delta kappaF
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
    have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
    nlinarith
  have hnat : 2 ≤ kappaF T ΔF := by
    by_contra hk
    have hk' : (kappaF T ΔF : Time) ≤ 1 := by
      exact_mod_cast (show kappaF T ΔF ≤ 1 by omega)
    nlinarith [hT.delta_pos]
  exact_mod_cast hnat

theorem promotion_age_grid_core (hT : FGTimingLaws T) (r s : Nat) (U : FGBlock (Fin n))
    (ΔF : Time)
    (hlo : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) < T.proposal s) :
    carrierTimeW T ΔF r ≤ T.proposal s ∧
    T.proposal U.slot + 2 * FGCompose.P T ≤ T.proposal s := by
  have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
  have h1 := lt_of_le_of_lt (le_max_left _ _) hlo
  have h2 := lt_of_le_of_lt (le_max_right _ _) hlo
  rw [p0d5b_age_proposal T hT] at h1 h2
  rw [p0d5b_age_proposal T hT] at h2
  have h1' : 4 * T.delta * ((r : Time) * T.roundSlots + kappaF T ΔF - 1) <
      4 * T.delta * (s : Time) := by
    change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
      4 * (kappaF T ΔF : Time) * T.delta - 4 * T.delta < 4 * T.delta * (s : Time) at h1
    convert h1 using 1; ring
  have h2' : 4 * T.delta * ((U.slot : Time) + 2 * T.roundSlots - 1) <
      4 * T.delta * (s : Time) := by
    change 4 * T.delta * (U.slot : Time) + 2 * (4 * (T.roundSlots : Time) * T.delta) -
      4 * T.delta < 4 * T.delta * (s : Time) at h2
    convert h2 using 1; ring
  have hs1 : (r : Time) * T.roundSlots + kappaF T ΔF ≤ s := by
    have hlt : (r : Time) * T.roundSlots + kappaF T ΔF - 1 < s := by nlinarith
    linarith only [Int.add_one_le_iff.mpr hlt]
  have hs2 : (U.slot : Time) + 2 * T.roundSlots ≤ s := by
    have hlt : (U.slot : Time) + 2 * T.roundSlots - 1 < s := by nlinarith
    linarith only [Int.add_one_le_iff.mpr hlt]
  rw [p0d5b_age_proposal T hT, p0d5b_age_proposal T hT]
  constructor
  · change (r : Time) * (4 * (T.roundSlots : Time) * T.delta) +
      4 * (kappaF T ΔF : Time) * T.delta ≤ 4 * T.delta * (s : Time)
    nlinarith
  · change 4 * T.delta * (U.slot : Time) + 2 * (4 * (T.roundSlots : Time) * T.delta) ≤
      4 * T.delta * (s : Time)
    nlinarith

theorem healing_promotion_age_service_tail_core (hT : FGTimingLaws T)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    {u : Time} {m r : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {l s : Slot} {U X : FGBlock (Fin n)}
    (hl : T.proposal l < (r : Time) * FGCompose.P T)
    (hrepair : ∀ v, PhaseInterval R E rho O u v m J contested → ∀ s Q,
      T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q →
      FrontierProposalService R E rho T s Q)
    (hnew : HonestProposal E rho I s (R.erase X))
    (hlo : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) < T.proposal s)
    (hhi : T.proposal s ≤
      max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
        (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + Γ T G)
    (hpgate : PhaseInterval R E rho O u (T.gate s) m J contested) :
    FrontierProposalService R E rho T s (R.erase X) ∧
      T.gate s ≤
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) := by
  have hF : 0 ≤ ΔF := by
    rw [hdelta] at deltaF
    linarith [hT.delta_pos]
  have hk := p0d5b_age_kappa_two T hT ΔF hF
  have hls : T.proposal l < T.proposal s := by
    have ht := lt_of_le_of_lt (le_max_left _ _) hlo
    change (r : Time) * FGCompose.P T + 4 * (kappaF T ΔF : Time) * T.delta -
      4 * T.delta < T.proposal s at ht
    nlinarith [hT.delta_pos]
  refine ⟨hrepair _ hpgate s (R.erase X) hls le_rfl hnew, ?_⟩
  have hgate : max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) =
      max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
        (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + Γ T G + 6 * T.delta := by
    rw [p0d5b_age_action T hT, ← max_add_add_right, ← max_add_add_right]
    unfold epsF
    congr 1 <;> ring
  rw [hgate, hT.gate_eq]
  linarith only [hhi]

end AvailableChain.FGCompose
end
