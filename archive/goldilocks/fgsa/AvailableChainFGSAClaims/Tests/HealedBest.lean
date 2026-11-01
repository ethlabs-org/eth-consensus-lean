module
public import AvailableChainFGSAClaims.Statements.HealedBest -- shake: keep (companion tests)

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.HealedBest

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (g : Nat)

-- A short run makes the local claim implication vacuous.
example (hshort : rho.horizon < (recoveryStart p E) + B_bestF p ΔF G g) :
    p.δt = 2 * p.R → HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    Gen.Pure.FinForm.recS.holds (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (P p) p.Δ (recoveryStart p E) rho.horizon g →
    (recoveryStart p E) + B_bestF p ΔF G g ≤ rho.horizon → HTimeBestConcl p c E rho G ΔF g := by
  intro _ _ _ _ hh
  exact (not_le_of_gt hshort hh).elim

example (hshort : rho.horizon < (recoveryStart p E) + B_bestF p ΔF G g) :
    p.δt = 2 * p.R → 1 ≤ g → HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    Gen.Pure.QualSearch (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (P p) p.Δ (recoveryStart p E) rho.horizon g →
    (recoveryStart p E) + B_bestF p ΔF G g ≤ rho.horizon → HTimeBestConcl p c E rho G ΔF g := by
  intro _ _ _ _ _ hh
  exact (not_le_of_gt hshort hh).elim

-- The companion deadline is at most the frozen H-time deadline.
example : (recoveryStart p E) + B_bestF p ΔF G g ≤ (recoveryStart p E) + B_HF p ΔF G := by
  rw [B_bestF_def]
  exact Int.add_le_add_left (min_le_right (B_heal p G g) (B_HF p ΔF G)) (recoveryStart p E)

example (h : HTimeBestConcl p c E rho G ΔF g) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < (recoveryStart p E) + B_HF p ΔF G := by
  rw [HTimeBestConcl_def] at h
  obtain ⟨w, hw, ht⟩ := h
  have hb : (recoveryStart p E) + B_bestF p ΔF G g ≤ (recoveryStart p E) + B_HF p ΔF G := by
    rw [B_bestF_def]
    exact Int.add_le_add_left (min_le_right (B_heal p G g) (B_HF p ΔF G)) (recoveryStart p E)
  exact ⟨w, hw, lt_of_lt_of_le ht hb⟩

end AvailableChain.FGSA.Run.Tests.HealedBest
end
