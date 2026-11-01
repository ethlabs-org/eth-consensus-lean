module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTop
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchCompose

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3.
The finite phase order charges gap and top J once, then contest repair and the tail.
The first rise and the first M+1 row retain their separate complete horizon guards. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5dCmpCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private def p0d5dCmpTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5dCmpTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5dCmpTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5dCmpObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5dCmpCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5dCmpObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5dCmpCore p c) (p0d5dCmpObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5dCmpKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

omit [DecidableEq V] in
/-- Blueprint 21:1722–1800; S5 F3, allowance geometry.
DC: SAME both frozen first labels exist. The one-lease window follows from the cut delay. -/
theorem frontierSearch_repair_start (E : Generic.Env V) (G : Time) {t ρbar : Time}
    (hdelay : recoveryStart p E + 2 * P p ≤ t)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) :
    FrontierRepairStart p E G (t + 3 * p.Δ) ρbar  := by
  have hsyncDelay : E.t_GST + 2 * P p ≤ t := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hsyncDelay : E.t_GST + 2 * P p ≤ t := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  let u := t + 3 * p.Δ
  have hΔ : 1 ≤ p.Δ := p.deltaPos
  rcases hmode with he | ⟨he, hk⟩
  · subst ρbar
    have hex : ∃ s, u < SA.proposalTime p.toParams s := by
      refine ⟨u.toNat + 1, ?_⟩
      change u < 4 * p.Δ * ((u.toNat + 1 : Nat) : Time)
      push_cast
      nlinarith [Int.self_le_toNat u, Int.natCast_nonneg u.toNat]
    exact .two (Nat.find hex) (Nat.find_spec hex) (fun b hb => Nat.find_min' hex hb)
  · subst ρbar
    have hex : ∃ b, u ≤ SA.voteTime p.toParams b := by
      refine ⟨u.toNat + 1, ?_⟩
      change u ≤ 4 * p.Δ * ((u.toNat + 1 : Nat) : Time) + p.Δ
      push_cast
      nlinarith [Int.self_le_toNat u, Int.natCast_nonneg u.toNat]
    let b := Nat.find hex
    have hb : u ≤ SA.voteTime p.toParams b := Nat.find_spec hex
    have hbi : (2 : Time) * p.R < b := by
      change u ≤ 4 * p.Δ * (b : Time) + p.Δ at hb
      change E.t_GST + 2 * (4 * (p.R : Time) * p.Δ) ≤ t at hsyncDelay
      dsimp only [u] at hb
      nlinarith [E.t_GST_nonneg]
    have hbn : 2 * p.R < b := by exact_mod_cast hbi
    have hwindow : p.k ≤ b + 1 := by omega
    have hshift : ((b + 1 - p.k : Nat) : Time) = (b : Time) + 1 - p.k := by
      rw [Nat.cast_sub hwindow]
      push_cast
      rfl
    have hki : (p.k : Time) ≤ 2 * p.R + 1 := by exact_mod_cast hk
    have hsync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) := by
      change E.t_GST ≤ 4 * p.Δ * ((b + 1 - p.k : Nat) : Time) + p.Δ
      rw [hshift]
      change u ≤ 4 * p.Δ * (b : Time) + p.Δ at hb
      change E.t_GST + 2 * (4 * (p.R : Time) * p.Δ) ≤ t at hsyncDelay
      dsimp only [u] at hb
      nlinarith
    exact .one b hb (fun i hi => Nat.find_min' hex hi) hwindow hsync

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME an allowed repair charge is nonnegative under Recovery₂. -/
theorem frontierSearch_allowance_nonneg [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) : 0 ≤ ρbar := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  rcases hmode with he | ⟨he, _⟩
  · rw [he]
    change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
    have := (fgsa_gamma_bounds p G).1
    nlinarith [p.deltaPos, hrec.gapPos]
  · rw [he]
    change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
    have := (fgsa_gamma_bounds p G).1
    nlinarith [p.deltaPos, hrec.gapPos]

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME rebase a first rise through earlier same-frontier events. -/
theorem frontierSearch_rise_rebase (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho) {i j m : Nat} {D : Time} (hij : i ≤ j)
    (hf : frontierAtIdx p c E rho (j + 1) ≤ m) (hr : FrontierRiseBy p c E rho j m D) :
    FrontierRiseBy p c E rho i m D := by
  simp only [frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_rise_rebase (R := p0d5dCmpCore p c) (E := E) (rho := rho)
    ⟨mono⟩ hij hf hr

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the HG.3 rise stop supplies the first frontier rise, including equal times. -/
theorem frontierSearch_rise_of_stop (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {D : Time}
    (hf : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hr : FirstRiseStopBy p c E rho i m D) : FrontierRiseBy p c E rho i m D := by
  simp only [firstRiseStopBy_iff, frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_rise_of_stop (R := p0d5dCmpCore p c) (O := p0d5dCmpObs p c)
    (E := E) (rho := rho) hs hf hr

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the unused phase charges remain available until the terminal tail. -/
def frontierSearch_remaining (p : Params) (G ΔF ρbar tail : Time) (kind : PhaseKind) : Time :=
  (if frontierSearch_phaseRank kind = 0 then E_gF p ΔF G ρbar else 0) +
    (if frontierSearch_phaseRank kind = 2 then 0 else E_jF p ΔF G ρbar) + (ρbar + 3 * p.Δ + tail)

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the arithmetic form without a pattern equation export. -/
theorem frontierSearch_remaining_eq (p : Params) (G ΔF ρbar tail : Time) (kind : PhaseKind) :
    frontierSearch_remaining p G ΔF ρbar tail kind =
      (if frontierSearch_phaseRank kind = 0 then E_gF p ΔF G ρbar else 0) +
        (if frontierSearch_phaseRank kind = 2 then 0 else E_jF p ΔF G ρbar) +
        (ρbar + 3 * p.Δ + tail) := by
  exact Eq.refl _

/-- Blueprint 21:1722–1800; S5 F3, finite phase composition.
DC: SAME gap and top-J cannot repeat. A saved seed leaves the supplied tail budget.
All repair labels and phase advances are proved from the standing inputs. -/
theorem frontierSearch_phase_tail [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    (tail : Time) (htail : 0 ≤ tail)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : recoveryStart p E + 2 * P p ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m
      (ev.time + frontierSearch_remaining p G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤
      ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ∧ StrongServed p c E rho m t := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hrem : ∀ k, frontierSearch_remaining p G ΔF ρbar tail k =
      FGCompose.frontierSearch_remaining (p0d5dCmpTiming p) G ΔF ρbar tail (p0d5dCmpKind k) := by
    intro k
    cases k
    · change _ = FGCompose.frontierSearch_remaining (p0d5dCmpTiming p) G ΔF ρbar tail .gap
      simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
        frontierSearch_phaseRank_gap, FGCompose.frontierSearch_phaseRank_gap_def,
        Nat.reduceEqDiff, ↓reduceIte]
      rfl
    · change _ = FGCompose.frontierSearch_remaining (p0d5dCmpTiming p) G ΔF ρbar tail .topJ
      simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
        frontierSearch_phaseRank_topJ, FGCompose.frontierSearch_phaseRank_topJ_def,
        Nat.reduceEqDiff, ↓reduceIte]
      rfl
    · change _ = FGCompose.frontierSearch_remaining (p0d5dCmpTiming p) G ΔF ρbar tail .contest
      simp only [frontierSearch_remaining_eq, FGCompose.frontierSearch_remaining_def,
        frontierSearch_phaseRank_contest, FGCompose.frontierSearch_phaseRank_contest_def,
        Nat.reduceEqDiff, ↓reduceIte]
      rfl
  have hst0 : FGCompose.FrontierSearchStart (p0d5dCmpCore p c) E rho (p0d5dCmpObs p c)
      (p0d5dCmpTiming p) (recoveryStart p E) i ev m (p0d5dCmpKind kind) := by
    simp only [frontierSearchStart_iff] at hstart
    cases kind <;> exact hstart
  rw [hrem] at hhor ⊢
  simp only [frontierRiseBy_iff]
  exact FGCompose.frontierSearch_phase_compose (R := p0d5dCmpCore p c) (O := p0d5dCmpObs p c)
    (T := p0d5dCmpTiming p) (E := E) (rho := rho) (Ef := p.E) (Jst := recoveryStart p E)
    (obs := p0d5dCmpObsLaws p c) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (p0d5dCmpTimingLaws p) crossing hs ⟨mono⟩ (StrongServed p c E rho) hrec.gapPos
    (frontierSearch_allowance_nonneg E rho hrec hmode) htail
    (fun i ev m k hst hdl hph => by
      have mode := frontierSearch_repair_start E G hdl hmode
      cases k with
      | gap =>
        have h := frontier_hg3_gap E rho hrec crossing mono repair common hδ hbound perm
          rowsReceipt progressCoverage hfold faultQ honestQuorum
          ((frontierSearchStart_iff p c E rho i ev m .gap).mpr hst) mode hph
        simp only [frontierHG3Result_iff, firstPhaseStopBy_iff, firstRiseStopBy_iff] at h
        exact h
      | topJ =>
        have h := frontier_hg3_topJ E rho hrec crossing mono origin repair common hδ hbound
          perm rowsReceipt progressCoverage hfold faultQ honestQuorum
          ((frontierSearchStart_iff p c E rho i ev m .topJ).mpr hst) mode hph
        simp only [frontierHG3Result_iff, firstPhaseStopBy_iff, firstRiseStopBy_iff] at h
        exact h
      | contest =>
        have h := frontier_hg3_contest E rho hrec crossing mono repair
          ((frontierSearchStart_iff p c E rho i ev m .contest).mpr hst) mode hph
        simp only [frontierHG3Result_iff, firstPhaseStopBy_iff, firstRiseStopBy_iff] at h
        exact h)
    hst0 hdelay hhor

end AvailableChain.FGSA.Run
end
