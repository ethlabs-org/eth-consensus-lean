module
public import AvailableChainSAPC.Proofs.Basic
public import AvailableChainSAPC.Statements.QuorumRecovery

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The unchanged Recovery regime derives the cap from its declared
constants. The base bundle needs no additional fault-bound premise. -/
theorem recovery_faultBound {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) (rho : Run V (sapc p))
    (hG : 0 < G)
    (hr : RecoveryRegime (sapc p) E (sapcInterface p).toInterface
      (sapcConstants p G) rho) : FaultBound (sapc p) (pcFaultCap p) rho := by
  have hbound := (sapcConstants_valid p G hG).recoveryBound_nonneg
  have htime : E.t_GST ≤ rho.horizon := by linarith [hr.horizon]
  have hfull := hr.full rfl
  have hawake : awakeAt E rho.honest E.t_GST = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact hfull v hv E.t_GST (le_refl _) htime
  have hcount := hr.participation E.t_GST (le_refl _) htime
  rw [hawake] at hcount
  have htotal : rho.honest.card + (faulty rho).card = p.n := by
    have hc : Fintype.card V = p.n := by
      simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  exact recovery_count_implies_cap p _ _ htotal hcount

/-- Full participation in the frozen contract implies the new regime. -/
theorem recovery_to_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) (rho : Run V (sapc p)) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    QuorumRecoveryRegime p G E rho := by
  have cap := recovery_faultBound p G E rho hG h
  refine ⟨h.execution, h.rootInjective, h.partialSynchrony,
    cap, ?_, h.recurrence, h.horizon⟩
  intro t lo hi
  have awake : awakeAt E rho.honest t = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact h.full rfl v hv t lo hi
  rw [awake]
  have seats : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
  have total : rho.honest.card + (faulty rho).card = p.n := by
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  exact (capped_counts p _ _ cap total).2.2.1

/-- The relative two-thirds premise follows from the absolute quorum
and cap. It is not an additional assumption. -/
theorem QuorumRecoveryRegime.participation {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {G : Time} {E : Env V} {rho : Run V (sapc p)}
    (h : QuorumRecoveryRegime p G E rho) (t : Time)
    (lo : E.t_GST ≤ t) (hi : t ≤ rho.horizon) :
    (2 / 3 : ℚ) * ((awakeAt E rho.honest t).card + (faulty rho).card) <
      ((awakeAt E rho.honest t).card : ℚ) := by
  have count := h.quorumParticipation t lo hi
  have cap := h.faultBound
  have bound := quorum_above_twice_cap p
  have strict : 2 * (faulty rho).card < (awakeAt E rho.honest t).card := by
    change (faulty rho).card ≤ pcFaultCap p at cap
    omega
  have rational : (2 : ℚ) * (faulty rho).card < (awakeAt E rho.honest t).card := by
    exact_mod_cast strict
  linarith

end AvailableChain.SAPC
end
