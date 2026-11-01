module
public import AvailableChainGridCO.Proofs.History

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} [DecidableEq V] [Fintype V]
  {p : Params} {E : Env V} {rho : Run V (gridCO p)}

omit [DecidableEq V] [Fintype V] in
/-- The hidden seat assignment fixes the size of the validator universe. -/
theorem awake_card_le_seats (t : Time) :
    (awakeAt E rho.honest t).card ≤ p.n := by
  let : Fintype V := Fintype.ofEquiv (Fin p.n) (rho.seatOf (0 : Slot))
  have hcard : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
  exact (Finset.card_le_univ _).trans_eq hcard

/-- The history-window inequality also bounds the current participants. -/
theorem etaSleepy_current_count (G t : Time)
    (h : EtaSleepy E (gridConstants p G) rho t) :
    p.θ_R * (((awakeAt E rho.honest t).card + (faulty rho).card : Nat) : ℚ) <
      ((awakeAt E rho.honest t).card : ℚ) := by
  classical
  have hsub : awakeAt E rho.honest t ⊆
      awakeInClosed E rho.honest (t - p.η) t := by
    intro v hv
    obtain ⟨hh, ha⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hh, t, by linarith [p.etaNonneg], le_refl _, ha⟩
  have hdisjoint : Disjoint (awakeAt E rho.honest t) (faulty rho) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  have hcard := Finset.card_le_card
    (Finset.union_subset_union hsub (Finset.Subset.refl (faulty rho)))
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  have hcast : (((awakeAt E rho.honest t).card + (faulty rho).card : Nat) : ℚ) ≤
      ((awakeInClosed E rho.honest (t - p.η) t ∪ faulty rho).card : ℚ) := by
    exact_mod_cast hcard
  have htheta : 0 ≤ p.θ_R := le_trans (by norm_num) p.thetaLower
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcast htheta) h

/-- The zero-fault case uses level one; positive fault counts use the
declared grid match. No stronger participation assumption is added. -/
theorem roundedLevel_gt_faults_of_etaSleepy (G t : Time)
    (h : EtaSleepy E (gridConstants p G) rho t) :
    (faulty rho).card < roundedLevel p (awakeAt E rho.honest t).card := by
  have hcount := etaSleepy_current_count G t h
  by_cases ha : (faulty rho).card = 0
  · have hpos : 0 < (awakeAt E rho.honest t).card := by
      by_contra hn
      have hz : (awakeAt E rho.honest t).card = 0 := by omega
      simp [ha, hz] at hcount
    rw [ha]
    exact lt_of_lt_of_le (by omega) (one_le_roundedLevel p _ hpos)
  · exact p.gridMatchesTheta _ _ (by omega) (awake_card_le_seats t) hcount

theorem synchronousLabel_of_sleepy (t₀ : Time)
    (h : SleepyRegime (gridCO p) E (gridInterface p) rho t₀)
    (r : Slot) (hhorizon : gateTime p r ≤ rho.horizon) :
    SynchronousLabel p E rho r := by
  have hproposal : 0 ≤ proposalTime p r :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt p.deltaPos)) (Int.natCast_nonneg r)
  have hvote : voteTime p r ≤ rho.horizon := by
    dsimp [gateTime, voteTime] at *
    linarith [p.deltaPos]
  refine ⟨h.execution, h.participation _ ?_ hvote, hhorizon, Or.inl ?_⟩
  · rw [h.start_zero]
    dsimp [voteTime]
    linarith [p.deltaPos]
  · exact ⟨by rw [h.gst_zero]; exact hproposal, h.partialSynchrony⟩

/-- The healthy prefix covers every label through the outage boundary,
including labels whose HEAD precedes the protected read. -/
theorem synchronousLabel_of_outage (G T b₀ b₁ : Time)
    (h : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G)
      rho T b₀ b₁)
    (r : Slot) (hgate : gateTime p r ≤ b₀) :
    SynchronousLabel p E rho r := by
  have hvote : voteTime p r < b₀ := by
    dsimp [gateTime, voteTime] at *
    linarith [p.deltaPos]
  have hstart : 0 ≤ voteTime p r := by
    unfold voteTime proposalTime
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (le_of_lt p.deltaPos)) (Int.natCast_nonneg _)) (le_of_lt p.deltaPos)
  exact ⟨h.execution, h.sleepyBefore _ hstart hvote,
    le_trans hgate (le_trans h.interval.2.2.1 h.interval.2.2.2),
    Or.inr ⟨b₀, hgate, h.healthy⟩⟩

theorem roundedLevel_gt_faults_of_outage (G T b₀ b₁ t : Time)
    (h : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G)
      rho T b₀ b₁) (hstart : 0 ≤ t) (hend : t < b₀) :
    (faulty rho).card < roundedLevel p (awakeAt E rho.honest t).card :=
  roundedLevel_gt_faults_of_etaSleepy G t (h.etaSleepyBefore t hstart hend)

/-- Grid CO's recovery threshold is exactly the current honest majority. -/
theorem awakeMajority_of_recovery (G t : Time)
    (h : RecoveryRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho)
    (hstart : E.t_GST ≤ t) (hend : t ≤ rho.horizon) :
    AwakeMajority E rho t := by
  have hc := h.participation t hstart hend
  change (1 / 2 : ℚ) * ((awakeAt E rho.honest t).card + (faulty rho).card) <
    ((awakeAt E rho.honest t).card : ℚ) at hc
  have : ((faulty rho).card : ℚ) < ((awakeAt E rho.honest t).card : ℚ) := by linarith
  exact_mod_cast this

theorem synchronousLabel_of_recovery (G : Time)
    (h : RecoveryRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho)
    (r : Slot) (hstart : E.t_GST ≤ proposalTime p r)
    (hend : gateTime p r ≤ rho.horizon) : SynchronousLabel p E rho r := by
  have hvstart : E.t_GST ≤ voteTime p r := by
    dsimp [voteTime]; linarith [p.deltaPos]
  have hvend : voteTime p r ≤ rho.horizon := by
    dsimp [voteTime, gateTime] at *; linarith [p.deltaPos]
  exact ⟨h.execution, awakeMajority_of_recovery G _ h hvstart hvend, hend,
    Or.inl ⟨hstart, h.partialSynchrony⟩⟩

/-- Sleepy supplies all complete labels from genesis. -/
theorem cleanThroughLabel_of_sleepy (t₀ : Time)
    (h : SleepyRegime (gridCO p) E (gridInterface p) rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon) : CleanThroughLabel p E rho r := by
  intro s hs
  exact synchronousLabel_of_sleepy t₀ h s
    (le_trans ((gateTime_le_iff p s r).mpr hs) hh)

/-- Draft 4.1 supplies the clean label prefix, including HEADs before T. -/
theorem cleanThroughLabel_of_outage (G T b₀ b₁ : Time)
    (h : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁)
    (r : Slot) (hh : gateTime p r ≤ b₀) : CleanThroughLabel p E rho r := by
  intro s hs
  exact synchronousLabel_of_outage G T b₀ b₁ h s
    (le_trans ((gateTime_le_iff p s r).mpr hs) hh)

/-- Every positive clean proposal has the preceding relay interval. -/
theorem proposalRelayReady_of_sleepy (hΔ : E.Δ = p.Δ) (t₀ : Time)
    (h : SleepyRegime (gridCO p) E (gridInterface p) rho t₀)
    (s : Slot) (hs : 0 < s) : ProposalRelayReady p E rho s := by
  refine Or.inl ⟨?_, h.partialSynchrony⟩
  rw [h.gst_zero, hΔ, zero_add]
  have hs' : (1 : Int) ≤ s := by exact_mod_cast hs
  dsimp [proposalTime]
  nlinarith [p.deltaPos]

/-- Recovery supplies proposal-view relay after its initial Δ interval. -/
theorem proposalRelayReady_of_recovery (G : Time)
    (h : RecoveryRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho)
    (s : Slot) (hs : E.t_GST + E.Δ ≤ proposalTime p s) : ProposalRelayReady p E rho s :=
  Or.inl ⟨hs, h.partialSynchrony⟩

end AvailableChain.GridCO
end
