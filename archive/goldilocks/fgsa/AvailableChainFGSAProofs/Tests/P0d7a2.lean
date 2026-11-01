module
public import AvailableChainFGSAProofs.Proofs.Finality.RecordInv

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d7a2
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The approved generic premise is a conclusion of concrete reachability.
-- No root-injectivity hypothesis is added to the FG-SA run.
private theorem d7f_g0_roots (i : Nat) (x : V) (_hx : x ∈ rho.honest) :
    ViewRootInj ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg.TF := by
  rw [fgsaCoreReads_def p c]
  exact viewRootInj_TF p _ (cstoreInv_stateBefore E rho i x)

-- The reset supplies an actual high source and row, including before service starts.
private theorem d7f_g0_reset_entry (w : HealingWitness) (h0 : H0Reset p c E rho w)
    (hh : THigh p c E rho w) (z : V) (r : Nat) (D : FGBlock (Fin p.n))
    (hz : z ∈ rho.honest) (hD : actionSourceFG p c E rho z r = some (some D))
    (hheight : (heightView p D).h = w.M + 1) :
    ∃ j x a C, HonestRowAt p c E rho j x w.rStar a ∧
      actionSourceFG p c E rho x w.rStar = some (some C) ∧
      (heightView p C).h = w.M + 1 ∧ (heightView p C).T_h = (heightView p D).T_h := by
  obtain ⟨j, x, a, C, ha, _hn, hs, _he, hc⟩ := h0.fresh
  refine ⟨j, x, a, C, ha, hs, hc, ?_⟩
  exact high_source_entry_eq p c E rho w hh x z w.rStar r C D ha.1 hz hs hD
    (by rw [high_def, hc]) (by rw [high_def, hheight]) (hc.trans hheight.symm)

private theorem d7f_g0_reset_before_start (w : HealingWitness) (h : H0 p c E rho w) :
    p.actionTime w.rStar < tstar p w := by
  have hgap : w.rStar * p.R + 2 ≤ w.u := h.label ▸ h.proposal_lower
  have hd := p.deltaPos
  change SA.gateTime p.toParams (w.rStar * p.R) < SA.gateTime p.toParams w.u
  change 4 * p.Δ * (w.rStar * p.R : Nat) + 6 * p.Δ <
    4 * p.Δ * (w.u : Time) + 6 * p.Δ
  have hcast : (w.rStar * p.R : Time) + 2 ≤ w.u := by exact_mod_cast hgap
  push_cast
  nlinarith

private theorem d7f_g0_pre_service_row (w : HealingWitness) (h : H0 p c E rho w) :
    ∃ j x a C, HonestRowAt p c E rho j x w.rStar a ∧
      p.actionTime w.rStar < tstar p w ∧
      actionSourceFG p c E rho x w.rStar = some (some C) ∧
      (heightView p C).h = w.M + 1 := by
  obtain ⟨j, x, a, C, ha, _, hs, _, hc⟩ := h.fresh
  exact ⟨j, x, a, C, ha, d7f_g0_reset_before_start p c E rho w h, hs, hc⟩

#print axioms d7f_g0_reset_before_start
#print axioms d7f_g0_pre_service_row
#print axioms d7f_g0_roots
#print axioms d7f_g0_reset_entry
#print axioms AvailableChain.FGSA.Run.high_source_entry_eq
#print axioms AvailableChain.FGSA.Run.high_record_target_choice
#print axioms AvailableChain.FGSA.Run.high_entry_record_invariant
#print axioms AvailableChain.FGSA.Run.high_record_fresh_at_cut
#print axioms AvailableChain.FGSA.Run.high_target_row_covered
#print axioms AvailableChain.FGSA.Run.high_record_reset_fresh
#print axioms AvailableChain.FGSA.Run.high_record_guards_and_fresh
#print axioms AvailableChain.FGSA.Run.high_target_first_row
#print axioms AvailableChain.FGSA.Run.high_target_honest_quorum
#print axioms AvailableChain.FGSA.Run.high_target_quorum_covered
#print axioms AvailableChain.FGSA.Run.high_action_target_choice
#print axioms AvailableChain.FGSA.Run.high_record_guards_and_fresh_at_action
#print axioms AvailableChain.FGSA.Run.ff2_stored_high_qc_identity
#print axioms AvailableChain.FGSA.Run.ff2_high_qc_identity
#print axioms AvailableChain.FGSA.Run.ff2_no_high_contest
#print axioms AvailableChain.FGSA.Run.HighRecordGuard_W_def
#print axioms AvailableChain.FGSA.Run.ff2_high_record_guards

end AvailableChain.FGSA.Run.Tests.P0d7a2
end
