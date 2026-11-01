module
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGCompose.Proofs.Population.HolderBaseGap
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3. Finite phase composition.
Gap and top J are charged once, then contest repair and the tail. A saved seed keeps
the supplied tail budget and no second repair charge. The composition core takes the
per-phase result of the actual start; the full theorem supplies it from the three d5c
phase consumers. The repair allowance at each actual phase start (with its
nonnegativity and repair-start geometry) is an explicit leaf.

Terminal checkpoint (plan checkpoint 2026-10-12 §3.2, route (c)): `TerminalPromotionFact`
stays an unproved intermediate statement. No theorem here reads it. Owner: the P0zF
release ledger (class: open intermediate); it gets no completion credit. -/

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

private theorem p0d5d_frontier_mono (mono : FGRunOrderLaws E rho R) {i j : Nat}
    (hij : i ≤ j) : frontierAtIdx R E rho i ≤ frontierAtIdx R E rho j := by
  apply Finset.sup_le
  intro x hx
  exact (mono.mono i j x hx hij).2.2.trans
    (Finset.le_sup (f := fun y => (R.core (rho.stateBefore E j y)).fg.h_max) hx)

omit [DecidableEq V] in
private theorem p0d5d_lt_timeIdx (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {e : V2.Event V Prot.Object} (hk : rho.events[k]? = some e) {t : Time}
    (ht : e.time ≤ t) : k < timeIdx rho t := by
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (t + 1)).mpr (Int.lt_add_one_iff.mpr ht)
  refine hlt.trans_le ?_
  change (rho.events.filter (fun e => decide (e.time < t + 1))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (Int.lt_add_one_iff.mp (of_decide_eq_true he)))

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME rebase a first rise through earlier same-frontier events. -/
theorem frontierSearch_rise_rebase_core (mono : FGRunOrderLaws E rho R) {i j m : Nat} {D : Time}
    (hij : i ≤ j) (hf : frontierAtIdx R E rho (j + 1) ≤ m)
    (hr : FrontierRiseBy R E rho j m D) : FrontierRiseBy R E rho i m D := by
  obtain ⟨k, ev, hjk, hk, ht, hh, hcap⟩ := (FrontierRiseBy_def R E rho j m D).mp hr
  apply (FrontierRiseBy_def R E rho i m D).mpr
  refine ⟨k, ev, by omega, hk, ht, hh, ?_⟩
  intro l hil hlk
  by_cases hlj : l ≤ j + 1
  · exact (p0d5d_frontier_mono R E rho mono hlj).trans hf
  · exact hcap l (by omega) hlk

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the HG.3 rise stop supplies the first frontier rise, including equal times. -/
theorem frontierSearch_rise_of_stop_core (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat}
    {D : Time} (hf : frontierAtIdx R E rho (i + 1) ≤ m)
    (hr : FirstRiseStopBy R E rho O i m D) : FrontierRiseBy R E rho i m D := by
  obtain ⟨j, ev, hij, hj, ht, _, hh, _⟩ := (FirstRiseStopBy_def R E rho O i m D).mp hr
  exact frontierSearch_first_rise R E rho hs ⟨j, hij, p0d5d_lt_timeIdx E rho hs hj ht, hh⟩ hf

include obs cert inv justif keep in
/-- Blueprint 21:1722–1800; S5 F3, finite phase composition core.
DC: SAME gap and top J cannot repeat; a saved seed leaves the supplied tail budget.
`step` is the result of the actual phase consumer at each actual start; the protocol
keeps its own served predicate. -/
theorem frontierSearch_phase_compose_core (hT : FGTimingLaws T) (crossing : RXing R E rho O)
    (schedule : V2.D.ScheduleWellFormed E rho) (mono : FGRunOrderLaws E rho R)
    (Served : Nat → Time → Prop) {G ΔF ρbar t0 tail : Time} (hG : 4 * T.delta ≤ G)
    (hρ : 0 ≤ ρbar) (htail : 0 ≤ tail)
    (step : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind → t0 ≤ ev.time →
      ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon →
      FirstPhaseStopBy R E rho O i m (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
      FirstRiseStopBy R E rho O i m (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
      ∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget T G ΔF ρbar kind ∧
        Served m t)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind) (hdelay : t0 ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
      Served m t := by
  classical
  have hP := frontierSearch_period_bound_core T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hd := hT.delta_pos
  have hj : 0 ≤ E_jF T ΔF G ρbar := by
    unfold E_jF
    exact le_trans (by linarith) (le_max_right _ _)
  have go : ∀ n, ∀ {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind},
      2 - frontierSearch_phaseRank kind = n →
      FrontierSearchStart R E rho O T Jst i ev m kind → t0 ≤ ev.time →
      ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
      ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
        Served m t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i m ev kind hn hstart hdelay hhor
      have hfront := ((FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart).2.2.2.1
      have hb : interruptedRepairBudget T G ΔF ρbar kind + tail ≤
          frontierSearch_remaining T G ΔF ρbar tail kind := by
        cases kind <;> simp only [interruptedRepairBudget_gap_def,
          interruptedRepairBudget_topJ_def, interruptedRepairBudget_contest_def,
          frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
          frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
          Nat.reduceEqDiff, ↓reduceIte] <;> linarith
      have hpHor : ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon := by
        linarith only [hb, hhor, htail]
      rcases step i ev m kind hstart hdelay hpHor with hphase | hrise | ⟨t, hwt, ht, hserved⟩
      · obtain ⟨j, nextEv, nextKind, hij, ht, hnext, hrank⟩ :=
          frontierSearch_phase_step_of_crossing (R := R) (E := E) (rho := rho) (O := O)
            (T := T) (Jst := Jst) (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
            (justif := justif) (keep := keep) crossing mono schedule hstart hphase
        have htime : ev.time ≤ nextEv.time := by
          obtain ⟨hi, _⟩ := (FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart
          obtain ⟨hjEv, _⟩ :=
            (FrontierSearchStart_def R E rho O T Jst j nextEv m nextKind).mp hnext
          obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
          obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjEv
          have hk := (List.pairwise_iff_getElem.mp schedule.sorted) i j hil hjl hij
          rw [hie, hje] at hk
          exact V2.D.Engine.time_le_of_key_le _ _ hk
        have hcost : nextEv.time + frontierSearch_remaining T G ΔF ρbar tail nextKind ≤
            ev.time + frontierSearch_remaining T G ΔF ρbar tail kind := by
          cases kind <;> cases nextKind <;>
            simp only [frontierSearch_phaseRank_gap_def, frontierSearch_phaseRank_topJ_def,
              frontierSearch_phaseRank_contest_def] at hrank <;>
            try omega
          all_goals simp only [interruptedRepairBudget_gap_def,
            interruptedRepairBudget_topJ_def] at ht
          all_goals simp only [frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
            frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
            Nat.reduceEqDiff, ↓reduceIte]
          all_goals linarith only [ht, hj]
        have hmeasure : 2 - frontierSearch_phaseRank nextKind < n := by
          rw [← hn]
          cases kind <;> cases nextKind <;> simp only [frontierSearch_phaseRank_gap_def,
            frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def] at * <;>
            omega
        rcases ih _ hmeasure rfl hnext (hdelay.trans htime) (hcost.trans hhor) with
            hr | ⟨t, hnt, ht, hserved⟩
        · left
          have hf :=
            ((FrontierSearchStart_def R E rho O T Jst j nextEv m nextKind).mp hnext).2.2.2.1
          exact frontierSearch_rise_mono R E rho hcost
            (frontierSearch_rise_rebase_core R E rho mono hij.le hf.le hr)
        · exact Or.inr ⟨t, htime.trans hnt, ht.trans hcost, hserved⟩
      · left
        exact frontierSearch_rise_mono R E rho (by linarith only [hb, htail])
          (frontierSearch_rise_of_stop_core R O E rho schedule hfront.le hrise)
      · exact Or.inr ⟨t, hwt, by linarith only [ht, hb], hserved⟩
  exact go _ rfl hstart hdelay hhor

end AvailableChain.FGCompose
end
