module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose -- shake: keep (core reads API)
public import AvailableChainFGCompose.Statements.FrontierSearch
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeedDefs

-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService -- shake: keep

public section

/-! Blueprint 21 HG.3--HG.5 and H.11; frontier plan §3.3.
These are run-local conclusion contracts. Producers must use the standing
Recovery₂, RMono, RXing, RCap, RQCOrigin and exact INLINE facts.
No contract below assumes a weak-to-strong served reconstruction.
The two search tasks in H.11 are sequential: rise from M, then row at M+1. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aDefsCore (p : Params) {In : Type} (c : AppCodec In) :
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


private def p0d5aDefsTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d5aDefsObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5aDefsCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5aDefsSafety (p : Params) {In : Type} (c : AppCodec In) :
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

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 HG.1:1500--1583; plan §3.3, saved-witness gap 7.
DC: SAME all frozen seed premises, including both first-label proofs.
The cap is at the current endpoint. A later endpoint needs its own cap. -/
def StrongServed (m : Nat) (t : Time) : Prop :=
  ∃ u J contested q Q Qfg,
    recoveryStart p E ≤ u ∧ HonestProposal E rho (fgsaInterface p c) q Q ∧
    eraseFG Qfg = Q ∧ (heightView p Qfg).h = m ∧ ExactService p c E rho q Q ∧
    FrontierSeedQualification p E u q ∧ u ≤ SA.proposalTime p.toParams q ∧
    PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested ∧
    SA.gateTime p.toParams q ≤ t ∧ t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)

/-- Blueprint 21 HG.1; plan §3.3. DC: SAME the complete internal witness interface. -/
theorem strongServed_iff (m : Nat) (t : Time) : StrongServed p c E rho m t ↔
  ∃ u J contested q Q Qfg,
    recoveryStart p E ≤ u ∧ HonestProposal E rho (fgsaInterface p c) q Q ∧
    eraseFG Qfg = Q ∧ (heightView p Qfg).h = m ∧ ExactService p c E rho q Q ∧
    FrontierSeedQualification p E u q ∧ u ≤ SA.proposalTime p.toParams q ∧
    PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested ∧
    SA.gateTime p.toParams q ≤ t ∧ t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m) := Iff.rfl

/-- Blueprint 21 HG.1; plan §3.3.
DC: SAME only the strong-to-weak projection is available. -/
theorem StrongServed.toServedFrontier {m : Nat} {t : Time}
    (h : StrongServed p c E rho m t) : ServedFrontier p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, _, hp, he, hh, hs, _, _, _, hg, _, _⟩ := h
  exact ⟨q, Q, Qfg, hp, he, hh, hg, hs⟩

/-- Blueprint 21 H.10:1426--1499 and H.11:1744--1800.
DC: SAME an event start or the actual inclusive cut, without a served flag. -/
def FrontierSearchStart (i : Nat) (ev : V2.Event V (Obj p)) (m : Nat)
    (kind : PhaseKind) : Prop :=
  rho.events[i]? = some ev ∧ recoveryStart p E ≤ ev.time ∧
  (EffectiveEvent p c E rho i ∨
    ∃ rG, recoveryStart p E ≤ p.actionTime rG ∧
      (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧ timeIdx rho ev.time = i + 1) ∧
  frontierAtIdx p c E rho (i + 1) = m ∧ 1 ≤ m ∧
  AttemptPhaseAt p c E rho (i + 1) m kind

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem frontierSearchStart_iff (i : Nat) (ev : V2.Event V (Obj p)) (m : Nat)
    (kind : PhaseKind) : FrontierSearchStart p c E rho i ev m kind ↔
  rho.events[i]? = some ev ∧ recoveryStart p E ≤ ev.time ∧
  (EffectiveEvent p c E rho i ∨
    ∃ rG, recoveryStart p E ≤ p.actionTime rG ∧
      (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧ timeIdx rho ev.time = i + 1) ∧
  frontierAtIdx p c E rho (i + 1) = m ∧ 1 ≤ m ∧
  AttemptPhaseAt p c E rho (i + 1) m kind := by
  cases kind with
  | gap =>
    exact FGCompose.FrontierSearchStart_def
      (R := p0d5aDefsCore p c) (E := E) (rho := rho) (O := p0d5aDefsObs p c)
      (T := p0d5aDefsTiming p) (Jst := recoveryStart p E) i ev m .gap
  | topJ =>
    exact FGCompose.FrontierSearchStart_def
      (R := p0d5aDefsCore p c) (E := E) (rho := rho) (O := p0d5aDefsObs p c)
      (T := p0d5aDefsTiming p) (Jst := recoveryStart p E) i ev m .topJ
  | contest =>
    exact FGCompose.FrontierSearchStart_def
      (R := p0d5aDefsCore p c) (E := E) (rho := rho) (O := p0d5aDefsObs p c)
      (T := p0d5aDefsTiming p) (Jst := recoveryStart p E) i ev m .contest


/-- Blueprint 21 HG.3:1639--1696, H.6/H.6-S.
DC: SAME the one-lease arm retains its synchronous first-HEAD window. -/
def FrontierRepairAllowance (G ρbar u : Time) : Prop :=
  ρbar = ρΓ p G ∨
    (ρbar = ρ₁ p G ∧ ∃ b : Slot,
      u ≤ SA.voteTime p.toParams b ∧
      (∀ s, u ≤ SA.voteTime p.toParams s → b ≤ s) ∧
      p.k ≤ b + 1 ∧ E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))

/-- Blueprint 21 H.6/H.6-S; HG.3 plan Q2.
DC: SAME the full first-label inputs of both frozen TRepair arms. -/
inductive FrontierRepairStart (G u : Time) : Time → Prop where
  | two (β : Slot) (after : u < SA.proposalTime p.toParams β)
      (least : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b) :
      FrontierRepairStart G u (ρΓ p G)
  | one (b : Slot) (after : u ≤ SA.voteTime p.toParams b)
      (least : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
      (window : p.k ≤ b + 1)
      (sync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
      FrontierRepairStart G u (ρ₁ p G)

/-- Blueprint 21 H.10/HG.3; HG.3 plan Q1.
DC: SAME the first effective event changes the phase at the same frontier. -/
def FirstPhaseStopBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧ frontierAtIdx p c E rho (j + 1) = m ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k)

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem firstPhaseStopBy_iff (i m : Nat) (deadline : Time) :
    FirstPhaseStopBy p c E rho i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧ frontierAtIdx p c E rho (j + 1) = m ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k) := by
  exact FGCompose.FirstPhaseStopBy_def (R := p0d5aDefsCore p c) (E := E) (rho := rho)
    (O := p0d5aDefsObs p c) i m deadline


/-- Blueprint 21 H.10/HG.3; HG.3 plan Q1.
DC: SAME a rise is the first effective event of the interrupted phase. -/
def FirstRiseStopBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧ m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k)

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem firstRiseStopBy_iff (i m : Nat) (deadline : Time) : FirstRiseStopBy p c E rho i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧ m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k) := by
  exact FGCompose.FirstRiseStopBy_def (R := p0d5aDefsCore p c) (E := E) (rho := rho)
    (O := p0d5aDefsObs p c) i m deadline


/-- Blueprint 21 HG.3; HG.3 plan Q1.
DC: SAME the two first-stop arms and a complete saved seed. -/
def FrontierHG3Result (i m : Nat) (start deadline : Time) : Prop :=
  FirstPhaseStopBy p c E rho i m deadline ∨
  FirstRiseStopBy p c E rho i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServed p c E rho m t

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem frontierHG3Result_iff (i m : Nat) (start deadline : Time) :
    FrontierHG3Result p c E rho i m start deadline ↔
  FirstPhaseStopBy p c E rho i m deadline ∨
  FirstRiseStopBy p c E rho i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServed p c E rho m t := Iff.rfl

/-- Blueprint 21 H.10 terminal promotion; run 2 R2-a.
DC: SAME the conclusion of hattempt3_class0_terminal, with its standing
ports. The owner supplies healing_renewedPromotion_terminal after it lands.
This is a contract, not an axiom or a proved terminal producer. -/
def TerminalPromotionFact [Fintype V] (G ΔF : Time) : Prop :=
  Recovery₂ p c E rho G ΔF → p.δt = 2 * p.R → LivenessBoundW p ΔF →
  RMono p c E rho → RXing p c E rho → TPerm p c E rho →
  (∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
    max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
    ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF)) →
  (∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
    BatchPrem p c E rho ΔF .progress r height U X →
    (heightView p X.parent).h = height → CoveredByChild p .progress X U height) →
  foldTrichotomy p .progress →
  Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  p.E.q ≤ p.E.weightOf (honestSeats p c rho) →
  ∀ r, p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon →
    ∀ u m J contested l q Q height,
      recoveryStart p E ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
      SA.proposalTime p.toParams l < SA.proposalTime p.toParams q →
      HonestProposal E rho (fgsaInterface p c) q Q → ExactService p c E rho q Q →
      OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
      (∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) →
      (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
        rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
        ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
      (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        height + 1 ≤ (heightView p X).h ∧
        (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y))

/-- Blueprint 21 HG.3; plan §3.3 deadline interface.
DC: SAME use the frozen maxima; do not replace their definitions. -/
def interruptedRepairBudget (G ΔF ρbar : Time) (kind : PhaseKind) : Time :=
  match kind with
  | .gap => E_gF p ΔF G ρbar
  | .topJ => E_jF p ΔF G ρbar
  | .contest => ρbar + 3 * p.Δ

omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME gap deadline. -/
theorem interruptedRepairBudget_gap (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .gap = E_gF p ΔF G ρbar := by
  exact FGCompose.interruptedRepairBudget_gap_def (p0d5aDefsTiming p) G ΔF ρbar


omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME top-J deadline, including epsF. -/
theorem interruptedRepairBudget_topJ (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .topJ = E_jF p ΔF G ρbar := by
  exact FGCompose.interruptedRepairBudget_topJ_def (p0d5aDefsTiming p) G ΔF ρbar


omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME contest deadline. -/
theorem interruptedRepairBudget_contest (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .contest = ρbar + 3 * p.Δ := by
  exact FGCompose.interruptedRepairBudget_contest_def (p0d5aDefsTiming p) G ΔF ρbar


/-- Blueprint 21 H.10; plan gap 6.
DC: SAME the first actual effective event strictly after the start index. -/
def FirstEffectiveBy (i : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k)

/-- Blueprint 21 H.10; plan gap 6. DC: SAME actual first-event interface. -/
theorem firstEffectiveBy_iff (i : Nat) (deadline : Time) :
    FirstEffectiveBy p c E rho i deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k) := by
  exact FGCompose.FirstEffectiveBy_def (R := p0d5aDefsCore p c) (E := E) (rho := rho)
    (O := p0d5aDefsObs p c) i deadline


/-- Blueprint 21 HG.1 and HG.4; plan §4.
DC: SAME a first frontier rise. Same-frontier events are permitted before it. -/
def FrontierRiseBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ m)

/-- Blueprint 21 HG.1/HG.4. DC: SAME first-rise interface. -/
theorem frontierRiseBy_iff (i m : Nat) (deadline : Time) :
    FrontierRiseBy p c E rho i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ m) := by
  exact FGCompose.FrontierRiseBy_def (R := p0d5aDefsCore p c) (E := E) (rho := rho) i m deadline


/-- Blueprint 21 HG.4--HG.5 and H.11.
DC: SAME actual first honest row, including an earlier SO-COV emission. -/
def FirstHeightRowBy (m : Nat) (deadline : Time) : Prop :=
  ∃ r, HeightRow p c E rho r m ∧
    (∀ r', HeightRow p c E rho r' m → r ≤ r') ∧ p.actionTime r ≤ deadline

/-- Blueprint 21 HG.4/H.11. DC: SAME first-row interface. -/
theorem firstHeightRowBy_iff (m : Nat) (deadline : Time) :
    FirstHeightRowBy p c E rho m deadline ↔
  ∃ r, HeightRow p c E rho r m ∧
    (∀ r', HeightRow p c E rho r' m → r ≤ r') ∧ p.actionTime r ≤ deadline := by
  exact FGCompose.FirstHeightRowBy_def (S := p0d5aDefsSafety p c) (E := E) (rho := rho)
    (T := p0d5aDefsTiming p) (pair := fun a => a.payload.height_pair) m deadline


/-- Blueprint 21 HG.3; plan §3.3.
DC: SAME generic event start, full phase deadline and complete horizon guard. -/
def InterruptedRepairStatement (G ΔF ρbar : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ i ev m kind, FrontierSearchStart p c E rho i ev m kind →
    FrontierRepairAllowance p E G ρbar (ev.time + 3 * p.Δ) →
    ev.time + interruptedRepairBudget p G ΔF ρbar kind ≤ rho.horizon →
    FirstEffectiveBy p c E rho i
      (ev.time + interruptedRepairBudget p G ΔF ρbar kind) ∨
    FrontierRiseBy p c E rho i m
      (ev.time + interruptedRepairBudget p G ΔF ρbar kind) ∨
    (∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget p G ΔF ρbar kind ∧
      StrongServed p c E rho m t)

/-- Blueprint 21 HG.4; plan §3.3.
DC: SAME two independently guarded tasks from the current served start.
There is no no-effective-event premise and no second repair allowance. -/
def FrontierTailStatement (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ i ev m kind, FrontierSearchStart p c E rho i ev m kind →
    StrongServed p c E rho m ev.time →
    (ev.time + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon →
      FrontierRiseBy p c E rho i m (ev.time + (2 * P p + Γ p G - 9 * p.Δ))) ∧
    (ev.time + (P p - 4 * p.Δ) ≤ rho.horizon →
      FirstHeightRowBy p c E rho m (ev.time + (P p - 4 * p.Δ)))

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier rise task, before the H.11 second task. -/
def frontierSearchRiseBudget (G ΔF ρbar : Time) : Time :=
  E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier first-row task. -/
def frontierSearchRowBudget (G ΔF ρbar : Time) : Time :=
  E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar

/-- Blueprint 21 HG.5/H.11; plan §3.3.
DC: SAME inline cut/frontier/row cap. The second task is at M+1.
One rStar is quantified before both allowances, with each full horizon guard.
The first task also has its own independent rise horizon guard.
No reset witness, phase package, or downstream healing service is assumed. -/
def FrontierSearchStatement (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ rG u₀ M, recoveryStart p E ≤ p.actionTime rG →
    (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) → u₀ = p.actionTime (rG + 2) →
    recoveryStart p E + 2 * P p ≤ u₀ → M = honestFrontier p c E rho u₀ →
    (∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ M) →
    (∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
      u₀ + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
        M < frontierAtIdx p c E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M)) ∧
    ((∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      u₀ + frontierSearchRiseBudget p G ΔF ρbar +
        frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon) →
    ∃ rStar, HeightRow p c E rho rStar (M + 1) ∧
      (∀ r, HeightRow p c E rho r (M + 1) → rStar ≤ r) ∧
      ∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
        u₀ + frontierSearchRiseBudget p G ΔF ρbar +
          frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon →
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
          M < frontierAtIdx p c E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M) ∧
          p.actionTime rStar ≤ ev.time + frontierSearchRowBudget p G ΔF ρbar)

/-- Blueprint 21:1695–1800; S5 F2, full HG.4.
DC: SAME expose the frozen conclusion contract for its producer. -/
theorem frontierTailStatement_iff (G ΔF : Time) :
    FrontierTailStatement p c E rho G ΔF ↔
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ i ev m kind, FrontierSearchStart p c E rho i ev m kind →
    StrongServed p c E rho m ev.time →
    (ev.time + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon →
      FrontierRiseBy p c E rho i m (ev.time + (2 * P p + Γ p G - 9 * p.Δ))) ∧
    (ev.time + (P p - 4 * p.Δ) ≤ rho.horizon →
      FirstHeightRowBy p c E rho m (ev.time + (P p - 4 * p.Δ))) := Iff.rfl

/-- Blueprint 21:1695–1800; S5 F3, full HG.5.
DC: SAME expose the frozen conclusion contract for its producer. -/
theorem frontierSearchStatement_iff (G ΔF : Time) :
    FrontierSearchStatement p c E rho G ΔF ↔
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ rG u₀ M, recoveryStart p E ≤ p.actionTime rG →
    (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) → u₀ = p.actionTime (rG + 2) →
    recoveryStart p E + 2 * P p ≤ u₀ → M = honestFrontier p c E rho u₀ →
    (∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ M) →
    (∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
      u₀ + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
        M < frontierAtIdx p c E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M)) ∧
    ((∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      u₀ + frontierSearchRiseBudget p G ΔF ρbar +
        frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon) →
    ∃ rStar, HeightRow p c E rho rStar (M + 1) ∧
      (∀ r, HeightRow p c E rho r (M + 1) → rStar ≤ r) ∧
      ∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
        u₀ + frontierSearchRiseBudget p G ΔF ρbar +
          frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon →
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
          M < frontierAtIdx p c E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M) ∧
          p.actionTime rStar ≤ ev.time + frontierSearchRowBudget p G ΔF ρbar) := Iff.rfl

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen rise budget for arithmetic composition. -/
theorem frontierSearchRiseBudget_eq (G ΔF ρbar : Time) :
    frontierSearchRiseBudget p G ΔF ρbar =
      E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar := by
  exact FGCompose.frontierSearchRiseBudget_def (p0d5aDefsTiming p) G ΔF ρbar


/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen row budget for arithmetic composition. -/
theorem frontierSearchRowBudget_eq (G ΔF ρbar : Time) :
    frontierSearchRowBudget p G ΔF ρbar =
      E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar := by
  exact FGCompose.frontierSearchRowBudget_def (p0d5aDefsTiming p) G ΔF ρbar


end AvailableChain.FGSA.Run
end
