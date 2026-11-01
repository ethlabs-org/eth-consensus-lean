module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose -- shake: keep (core reads API)
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay -- shake: keep (frozen relay API)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (frozen bound proof API)

public section

/-! Blueprint 21 H.10/HG.3/HG.5; frontier plan gaps 6 and 7.
Least events are selected only inside the finite run prefix.
Earlier rows retain their actual emission, including SO-COV coverage. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aStopCore (p : Params) {In : Type} (c : AppCodec In) :
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


private def p0d5aStopTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5aStopTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5aStopTiming p) where
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

private def p0d5aStopObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5aStopCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5aStopSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

private def p0d5aStopKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest


private theorem p0d5aStopObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5aStopCore p c) (p0d5aStopObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
/-- Blueprint 21 H.10; plan §4 closed horizon.
DC: SAME an actual event in the inclusive prefix has time at most its cut. -/
theorem frontierSearch_event_time_le (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {ev : V2.Event V (Obj p)} {deadline : Time}
    (hj : rho.events[j]? = some ev) (hcut : j < timeIdx rho deadline) :
    ev.time ≤ deadline := by
  exact FGCompose.frontierSearch_event_time_le (E := E) (rho := rho) hs hj hcut


/-- Blueprint 21 H.10 and HG.3; plan gap 6.
DC: SAME construct the least actual event in the closed deadline prefix. -/
theorem frontierSearch_first_effective_split (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (deadline : Time) :
    FirstEffectiveBy p c E rho i deadline ∨
      (∀ j, i < j → j < timeIdx rho deadline → ¬ EffectiveEvent p c E rho j) := by
  simp only [firstEffectiveBy_iff] at *
  exact FGCompose.frontierSearch_first_effective_split (R := p0d5aStopCore p c) (E := E)
    (rho := rho) (O := p0d5aStopObs p c) hs i deadline


/-- Blueprint 21 HG.3; plan Q1.
DC: SAME classify the finite first stop by its actual frontier. -/
theorem frontierSearch_classify_stop (mono : RMonoAll p c E rho)
    {i m : Nat} {deadline : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hstop : FirstEffectiveBy p c E rho i deadline) :
    FirstPhaseStopBy p c E rho i m deadline ∨
      FirstRiseStopBy p c E rho i m deadline := by
  simp only [firstEffectiveBy_iff, firstPhaseStopBy_iff, firstRiseStopBy_iff] at *
  exact FGCompose.frontierSearch_classify_stop (R := p0d5aStopCore p c) (E := E) (rho := rho)
    (O := p0d5aStopObs p c) ⟨mono⟩ hfront hstop


/-- Blueprint 21 HG.1/HG.4; plan §4.
DC: SAME first rise selection permits earlier same-frontier events. -/
theorem frontierSearch_first_rise (hs : V2.D.ScheduleWellFormed E rho)
    {i m : Nat} {deadline : Time}
    (hex : ∃ j, i < j ∧ j < timeIdx rho deadline ∧
      m < frontierAtIdx p c E rho (j + 1))
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m) :
    FrontierRiseBy p c E rho i m deadline := by
  simp only [frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_first_rise (R := p0d5aStopCore p c) (E := E)
    (rho := rho) hs hex hstart


/-- Blueprint 21 HG.4/H.11; plan §3.3.
DC: SAME select one first row from an actual emitted row. -/
theorem frontierSearch_first_row {m r : Nat} {deadline : Time}
    (hrow : HeightRow p c E rho r m) (htime : p.actionTime r ≤ deadline) :
    FirstHeightRowBy p c E rho m deadline := by
  simp only [firstHeightRowBy_iff] at *
  exact FGCompose.frontierSearch_first_row (S := p0d5aStopSafety p c) (E := E) (rho := rho)
    (T := p0d5aStopTiming p) (pair := fun a => a.payload.height_pair)
    (p0d5aStopTimingLaws p) hrow htime


/-- Blueprint 21 H.11; plan §3.3 reset minimization.
DC: SAME both repair allowances must select this same first round. -/
theorem frontierSearch_first_row_unique {m r r' : Nat}
    (hr : HeightRow p c E rho r m)
    (hfirst : ∀ s, HeightRow p c E rho s m → r ≤ s)
    (hr' : HeightRow p c E rho r' m)
    (hfirst' : ∀ s, HeightRow p c E rho s m → r' ≤ s) : r = r' := by
  exact FGCompose.frontierSearch_first_row_unique (S := p0d5aStopSafety p c) (E := E) (rho := rho)
    (T := p0d5aStopTiming p) (pair := fun a => a.payload.height_pair) hr hfirst hr' hfirst'


/-- Blueprint 21 HG.5 and IF.3(a); plan §3.3.
DC: SAME a skipped frontier supplies a real earlier honest M+1 row via RCap.
The height inequality alone is never used as a row witness. -/
theorem frontierSearch_skipped_row (cap : RCap p c E rho)
    {M i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hskip : M + 2 ≤ (heightView p W).h) :
    ∃ j z r a e, j < i ∧ HonestRowAt p c E rho j z r a ∧
      namedEntry a.payload.height_pair = some (M + 1, e) := by
  exact FGCompose.frontierSearch_skipped_row (R := p0d5aStopCore p c) (E := E) (rho := rho)
    (O := p0d5aStopObs p c) (S := p0d5aStopSafety p c)
    (T := p0d5aStopTiming p) (pair := fun a => a.payload.height_pair)
      (chainRows := fun nd B => chainWireRows nd.st B)
    cap hW hskip


omit [DecidableEq V] in
/-- Blueprint 21 HG.5. DC: SAME three phase charges in their fixed order. -/
def frontierSearch_phaseRank (kind : PhaseKind) : Nat :=
  match kind with | .gap => 0 | .topJ => 1 | .contest => 2

/-- Blueprint 21 HG.5; phase-order composition.
DC: SAME a same-frontier effective stop strictly advances the phase.
Thus the gap and top-J charge cannot be repeated at this frontier. -/
theorem frontierSearch_phase_step_of_crossing (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {kind : PhaseKind}
    {ev : V2.Event V (Obj p)} {deadline : Time}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hstop : FirstPhaseStopBy p c E rho i m deadline) :
    ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
      FrontierSearchStart p c E rho j nextEv m nextKind ∧
      frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind := by
  simp only [firstPhaseStopBy_iff, frontierSearchStart_iff] at *
  have hs0 : FGCompose.FrontierSearchStart (p0d5aStopCore p c) E rho
      (p0d5aStopObs p c) (p0d5aStopTiming p) (recoveryStart p E)
      i ev m (p0d5aStopKind kind) := by
    cases kind <;> exact hstart
  obtain ⟨j, nextEv, nextKind, hij, ht, hn, hrank⟩ :=
    FGCompose.frontierSearch_phase_step_of_crossing
      (R := p0d5aStopCore p c) (E := E) (rho := rho) (O := p0d5aStopObs p c)
      (T := p0d5aStopTiming p) (Jst := recoveryStart p E)
      (Ef := p.E) (obs := p0d5aStopObsLaws p c) (cert := fgCertificateLaws p)
      (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
      (justif := fgJustificationLaws p)
      (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
      crossing ⟨mono⟩ hs hs0 hstop
  cases nextKind with
  | gap =>
    refine ⟨j, nextEv, .gap, hij, ht, ?_, ?_⟩
    · exact hn
    · cases kind <;> exact hrank
  | topJ =>
    refine ⟨j, nextEv, .topJ, hij, ht, ?_, ?_⟩
    · exact hn
    · cases kind <;> exact hrank
  | contest =>
    refine ⟨j, nextEv, .contest, hij, ht, ?_, ?_⟩
    · exact hn
    · cases kind <;> exact hrank


/-- Blueprint 21:1592–1638; S5 H2, route step 1.
DC: SAME choose the first rise strictly before D, or cap the strict cut.
A rise at exactly D does not enter the strict prefix. Same-frontier events do not stop it. -/
theorem frontierSearch_strict_cap_or_rise
    (hs : V2.D.ScheduleWellFormed E rho) (mono : RMonoAll p c E rho)
    (i m : Nat) (D : Time) (hstart : frontierAtIdx p c E rho (i + 1) ≤ m) :
    FrontierRiseBy p c E rho i m D ∨
      (∀ k x, k ≤ V2.D.Run.idxBefore rho D → x ∈ rho.honest →
        (storeAt p c E rho k x).fg.h_max ≤ m) := by
  simp only [frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_strict_cap_or_rise (R := p0d5aStopCore p c) (E := E)
    (rho := rho) hs ⟨mono⟩ i m D hstart


omit [DecidableEq V] in
/-- Blueprint 21:1592–1638; S5 H2, route step 4.
DC: SAME an inclusive earlier read lies inside the strict later cut. -/
theorem frontierSearch_timeIdx_le_idxBefore {t D : Time} (ht : t < D) :
    timeIdx rho t ≤ V2.D.Run.idxBefore rho D := by
  exact FGCompose.frontierSearch_timeIdx_le_idxBefore (rho := rho) ht


/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME a longer deadline retains the same first rise and earlier frontier cap. -/
theorem frontierSearch_rise_mono {i m : Nat} {d D : Time} (hd : d ≤ D)
    (hr : FrontierRiseBy p c E rho i m d) : FrontierRiseBy p c E rho i m D := by
  simp only [frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_rise_mono (R := p0d5aStopCore p c) (E := E) (rho := rho) hd hr


/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME strict honest high receipt forces a first rise before the receipt deadline. -/
theorem frontierSearch_rise_of_receipt (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) {i m : Nat} {d D : Time} {x : V}
    {X : FGBlock (Fin p.n)} (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hx : x ∈ rho.honest) (hh : m + 1 ≤ (heightView p X).h)
    (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d x)
    (hd : d ≤ D) : FrontierRiseBy p c E rho i m D := by
  simp only [frontierRiseBy_iff] at *
  exact FGCompose.frontierSearch_rise_of_receipt (R := p0d5aStopCore p c) (E := E) (rho := rho)
    (O := p0d5aStopObs p c)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    hs ⟨mono⟩ hstart hx hh hheld hd


/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_gap :
    frontierSearch_phaseRank .gap = 0 := by
  exact FGCompose.frontierSearch_phaseRank_gap_def


/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_topJ :
    frontierSearch_phaseRank .topJ = 1 := by
  exact FGCompose.frontierSearch_phaseRank_topJ_def


/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_contest :
    frontierSearch_phaseRank .contest = 2 := by
  exact FGCompose.frontierSearch_phaseRank_contest_def


end AvailableChain.FGSA.Run
end
