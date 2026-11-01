module
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal -- shake: keep

public section

namespace AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart

/-- Arithmetic replay of the two GST=21 sources. No run-validity claim is made. -/
theorem old_source_21 {V : Type} (p : Params) (E : Generic.Env V)
    (hd : p.Δ = 1) (hg : E.t_GST = 21) :
    recoveryStart p E = 30 ∧ ¬ recoveryStart p E ≤ SA.voteTime p.toParams 5 := by
  have hstart : recoveryStart p E = 30 := by
    change 4 * p.Δ *
      (((max 0 E.t_GST + 4 * p.Δ - 1) / (4 * p.Δ)).toNat : Int) + 6 * p.Δ = 30
    rw [hd, hg]
    decide
  refine ⟨hstart, ?_⟩
  change ¬ recoveryStart p E ≤ 4 * p.Δ * (5 : Int) + p.Δ
  rw [hstart, hd]
  decide

/-- The slow source at GST=1001 is before the joined-start vote domain. -/
theorem old_source_1001 {V : Type} (p : Params) (E : Generic.Env V)
    (hd : p.Δ = 1) (hg : E.t_GST = 1001) :
    recoveryStart p E = 1010 ∧ ¬ recoveryStart p E ≤ SA.voteTime p.toParams 251 := by
  have hstart : recoveryStart p E = 1010 := by
    change 4 * p.Δ *
      (((max 0 E.t_GST + 4 * p.Δ - 1) / (4 * p.Δ)).toNat : Int) + 6 * p.Δ = 1010
    rw [hd, hg]
    decide
  refine ⟨hstart, ?_⟩
  change ¬ recoveryStart p E ≤ 4 * p.Δ * (251 : Int) + p.Δ
  rw [hstart, hd]
  decide

/-- The split replay recomputes its threshold and retains the one-lease cost. -/
theorem split_source {V : Type} (p : Params) (E : Generic.Env V)
    (hd : p.Δ = 2) (hg : E.t_GST = 2002) (hk : p.k = 2) :
    recoveryStart p E = 2020 ∧ ¬ recoveryStart p E ≤ SA.voteTime p.toParams 251 ∧
    253 + p.k = 255 ∧ ρ₁ p 16 = 50 ∧
    SA.gateTime p.toParams 256 < recoveryStart p E + ρ₁ p 16 := by
  have hstart : recoveryStart p E = 2020 := by
    change 4 * p.Δ *
      (((max 0 E.t_GST + 4 * p.Δ - 1) / (4 * p.Δ)).toNat : Int) + 6 * p.Δ = 2020
    rw [hd, hg]
    decide
  have hcost : ρ₁ p 16 = 50 := by
    unfold ρ₁ L Γ
    rw [hd, hk]
    decide
  refine ⟨hstart, ?_, by rw [hk], hcost, ?_⟩
  · change ¬ recoveryStart p E ≤ 4 * p.Δ * (251 : Int) + p.Δ
    rw [hstart, hd]
    decide
  · change 4 * p.Δ * (256 : Int) + 6 * p.Δ < recoveryStart p E + ρ₁ p 16
    rw [hstart, hd, hcost]
    decide

/-- A short finite horizon gives no new joined-start phase entry. -/
theorem before_start {V : Type} (p : Params) (E : Generic.Env V) (h u : Time)
    (hh : h < recoveryStart p E) (hu : u ≤ h) : ¬ recoveryStart p E ≤ u := by
  intro hready
  exact (not_le_of_gt hh) (hready.trans hu)

end AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart

#print axioms AvailableChain.FGSA.Run.healing_proposal_gap
#print axioms AvailableChain.FGSA.Run.healing_proposal_phase_reader_floor
#print axioms AvailableChain.FGSA.Run.healing_settled_frame_ready
#print axioms AvailableChain.FGSA.Run.healing_settle_start_on
#print axioms AvailableChain.FGSA.Run.healing_attempt_settle_start
#print axioms AvailableChain.FGSA.Run.healing_promotion_source_parent
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion_terminal
#print axioms AvailableChain.FGSA.Run.frontier_hg2a_receipt
#print axioms AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart.old_source_21
#print axioms AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart.old_source_1001
#print axioms AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart.split_source
#print axioms AvailableChain.FGSA.Run.Tests.HealingH2JoinedStart.before_start

#print axioms AvailableChain.FGSA.Run.healing_capped_witness_reader_floor
