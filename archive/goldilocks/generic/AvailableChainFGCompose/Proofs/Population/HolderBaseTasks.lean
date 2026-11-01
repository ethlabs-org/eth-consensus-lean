module
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget
public import AvailableChainFGCompose.Proofs.Population.HolderBaseGap
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGCompose.Proofs.Healing.PhaseFrame

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3. First rise, then the first height-M+1 row.
Each task composes the d5d-a phase tail with the d5c per-seed tail of the saved seed.
The saved seed's held copy and continuing local service come from the published
gate-copy and service leaves. The cut start reads the actual tick of an honest node. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

variable (chainRows : Prot.State → Block → List Wire)

theorem frontierSearch_task_bounds_core (hT : FGTimingLaws T) {G ΔF ρbar : Time}
    (hG : 4 * T.delta ≤ G) (hbound : LivenessBoundW T ΔF) (hρ : 0 ≤ ρbar) (kind : PhaseKind) :
    frontierSearch_remaining T G ΔF ρbar (2 * FGCompose.P T + Γ T G - 9 * T.delta) kind ≤
        frontierSearchRiseBudget T G ΔF ρbar ∧
    frontierSearch_remaining T G ΔF ρbar (FGCompose.P T - 4 * T.delta) kind ≤
        frontierSearchRowBudget T G ΔF ρbar ∧
    0 ≤ 2 * FGCompose.P T + Γ T G - 9 * T.delta ∧ 0 ≤ FGCompose.P T - 4 * T.delta ∧
    0 ≤ frontierSearchRiseBudget T G ΔF ρbar ∧ 0 ≤ frontierSearchRowBudget T G ΔF ρbar := by
  have hP := frontierSearch_period_bound_core T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hd := hT.delta_pos
  have hg : 0 ≤ E_gF T ΔF G ρbar := by
    unfold E_gF
    have := le_max_right (FGCompose.P T + 3 * T.delta + epsF T ΔF) (2 * FGCompose.P T - T.delta)
    linarith
  have hj : 0 ≤ E_jF T ΔF G ρbar := by
    unfold E_jF
    exact le_trans (by linarith) (le_max_right _ _)
  have hcR := frontierSearch_contest_rise_cost T hT G ΔF ρbar hbound
  have hcW := frontierSearch_contest_row_cost T ρbar
  refine ⟨?_, ?_, by linarith, by linarith, ?_, ?_⟩
  · rw [frontierSearchRiseBudget_def, ← hcR]
    cases kind <;> simp only [frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
      frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
      Nat.reduceEqDiff, ↓reduceIte] <;> linarith only [hg, hj]
  · rw [frontierSearchRowBudget_def, ← hcW]
    cases kind <;> simp only [frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
      frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
      Nat.reduceEqDiff, ↓reduceIte] <;> linarith only [hg, hj]
  · rw [frontierSearchRiseBudget_def, ← hcR]
    linarith
  · rw [frontierSearchRowBudget_def, ← hcW]
    linarith

include cert inv in
theorem frontierSearch_row_of_rise_core (hT : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    {i m : Nat} {Dl : Time} (hm : 1 ≤ m) (hrise : FrontierRiseBy R E rho i m Dl) :
    FirstHeightRowBy S E rho T D.heightPair m Dl := by
  obtain ⟨j, ev, _, hj, ht, hh, _⟩ := (FrontierRiseBy_def R E rho i m Dl).mp hrise
  obtain ⟨x, hx, hxh⟩ := Finset.lt_sup_iff.mp hh
  obtain ⟨W, hW, hWh⟩ := healing_phase_frontier_witness (R := R) (E := E) (rho := rho)
    (O := O) (Ef := Ef) (cert := cert) (inv := inv) (j + 1) x
  obtain ⟨l, z, r, a, e, hlj, ha, hn, _⟩ := cap (m - 1) (j + 1) x W ⟨hx, hW⟩
    (by simp only [Height] at *; omega)
  have hn' : namedEntry (D.heightPair a) = some (m, e) := by
    simpa only [Nat.sub_add_cancel hm] using hn
  have hcut : l < timeIdx rho ev.time := by
    have hjcut : j < timeIdx rho ev.time :=
      (V2.D.Engine.index_lt_read_length_iff hs ev.time hj).mpr le_rfl
    exact (Nat.le_of_lt_succ hlj).trans_lt hjcut
  exact frontierSearch_first_row S E rho T D.heightPair hT ⟨l, z, a, e, ha, hn'⟩
    ((frontierSearch_event_time_le E rho hs ha.2.1 hcut).trans ht)

end AvailableChain.FGCompose
end
