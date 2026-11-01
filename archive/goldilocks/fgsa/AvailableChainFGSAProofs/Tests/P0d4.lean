module
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt -- shake: keep (#print axioms)
public import AvailableChainFGCompose.Proofs.Healing.AttemptStop -- shake: keep (#print axioms)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d4AuditCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4AuditSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4AuditObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d4AuditCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d4AuditTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d4AuditGate (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGAttemptGateReads (fgsa p c) where
  restartTime nd := nd.st.restartTime
  preClock nd t := { nd with st := clockPre p nd.st t }
  saved nd s := (GridCO.savedGenuine nd.st.base s).map (fun b => b.getD .genesis)
  confirmation nd s := SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F)
    (actView nd.st) s
  blocked nd B := (actView nd.st).obligations.any (fun row => !Block.compatible row.1 B)
  writes nd s := fastWriteAt nd.st s

private def p0d4AuditKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4AuditTask : AttemptTask → FGCompose.AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4AuditKey (k : AttemptKey) : FGCompose.AttemptKey :=
  ⟨k.start, k.frontier, p0d4AuditKind k.phase, p0d4AuditTask k.task, k.served⟩

private theorem p0d4AuditGateResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) :
    FGCompose.AttemptGateResult E rho (p0d4AuditTiming p) (p0d4AuditGate p c) x s =
      gateResult p c E rho x s := by
  classical
  rw [FGCompose.p0d4_AttemptGateResult_def, gateResult_def, gateIn_def]
  change (preTick E rho x (SA.gateTime p.toParams s)).map _ = _
  simp only [Option.map_map]
  apply congrArg (fun f : Node p → Option Block =>
    (preTick E rho x (SA.gateTime p.toParams s)).map f)
  funext nd
  simp only [Function.comp_apply]
  change (match (clockPre p nd.st (SA.gateTime p.toParams s)).restartTime with
      | none => SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p nd.st (SA.gateTime p.toParams s)).fg.F)
          (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s
      | some w => if w ≤ slotStartZ p s then SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p nd.st (SA.gateTime p.toParams s)).fg.F)
          (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s else none) = _
  split_ifs with hg
  · cases hr : (clockPre p nd.st (SA.gateTime p.toParams s)).restartTime with
    | none => rfl
    | some w =>
      rw [hr] at hg
      change w ≤ slotStartZ p s at hg
      exact ite_eq_left hg
  · cases hr : (clockPre p nd.st (SA.gateTime p.toParams s)).restartTime with
    | none => rw [hr] at hg; exact (hg True.intro).elim
    | some w =>
      rw [hr] at hg
      change ¬ w ≤ slotStartZ p s at hg
      exact ite_eq_right hg

private theorem p0d4AuditSource (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (r : Nat) :
    (FGCompose.actionSourceFG (p0d4AuditCore p c) E rho (p0d4AuditTiming p) x r).map
      (Option.map eraseFG) = actionSource p c E rho x r := by
  change ((postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)).map
    (Option.map eraseFG) = _
  change _ = (actionSourceFG p c E rho x r).map (Option.map eraseFG)
  rw [actionSourceFG_def]

private theorem p0d4AuditEnabled (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (x : V) (s : Slot) :
    FGCompose.AttemptEnabledGate E rho (p0d4AuditTiming p) (p0d4AuditGate p c) j x s ↔
      enabledGateAt p c E rho j x s := by
  rw [FGCompose.p0d4_AttemptEnabledGate_def]
  have reads : (p0d4AuditGate p c).restartTime (rho.stateBefore E j x) =
      (storeAt p c E rho j x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ht, hw⟩ <;> refine ⟨ht, ?_⟩
  all_goals
    cases hr : (storeAt p c E rho j x).restartTime <;>
      first | trivial | (rw [hr] at hw; exact hw)

private theorem p0d4AuditCaught (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i : Nat) (t : Time) :
    FGCompose.AttemptCaughtUp E rho (p0d4AuditTiming p) (p0d4AuditGate p c) x i t ↔
      caughtUpAtIdx p c E rho x i t := by
  rw [FGCompose.p0d4_AttemptCaughtUp_def]
  have reads : (p0d4AuditGate p c).restartTime (rho.stateBefore E i x) =
      (storeAt p c E rho i x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ha, hc⟩ <;> refine ⟨ha, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4AuditEnabled E rho j x s).mp hg, hawake, hn⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4AuditEnabled E rho j x s).mpr hg, hawake, hn⟩

private theorem p0d4AuditPassed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : FGCompose.AttemptGatePassed E rho (p0d4AuditTiming p)
      (p0d4AuditGate p c) j ↔ gatePassedAt p c E rho j := by
  constructor
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4AuditEnabled E rho j x s).mp hg, ?_, h⟩
    exact Option.map_eq_none_iff.mp hs
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4AuditEnabled E rho j x s).mpr hg, ?_, h⟩
    exact Option.map_eq_none_iff.mpr hs

private theorem p0d4AuditExact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) :
    FGCompose.AttemptExactService (p0d4AuditCore p c) E rho (p0d4AuditTiming p)
      (fgsaInterface p c) (p0d4AuditGate p c) s Q ↔ ExactService p c E rho s Q  := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4AuditCaught E rho x _ _).mpr hr.2⟩
    have gates : ∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4AuditEnabled E rho j x s).mp hj, (p0d4AuditPassed E rho j).mp hp⟩
    exact ⟨(p0d4AuditGateResult E rho x s) ▸ hg, gates, hw, hs,
      fun r he => (p0d4AuditSource E rho x r) ▸ ha r he⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4AuditCaught E rho x _ _).mp hr.2⟩
    have gates : ∃ j, FGCompose.AttemptEnabledGate E rho (p0d4AuditTiming p)
        (p0d4AuditGate p c) j x s ∧
        FGCompose.AttemptGatePassed E rho (p0d4AuditTiming p) (p0d4AuditGate p c) j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4AuditEnabled E rho j x s).mpr hj, (p0d4AuditPassed E rho j).mpr hp⟩
    exact ⟨(p0d4AuditGateResult E rho x s).symm ▸ hg, gates, hw, hs,
      fun r he => (p0d4AuditSource E rho x r).symm ▸ ha r he⟩

omit [DecidableEq V] in
private theorem p0d4AuditNamed (a : NamedHeightPair) :
    FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem p0d4AuditRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0d4AuditSafety p c) E rho (p0d4AuditTiming p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0d4AuditValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} (h : AttemptValid p c E rho k) :
    FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) (p0d4AuditKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mpr hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mp hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [p0d4AuditNamed] at he
      exact hn rfl j y r a h e hj ha he

private theorem p0d4AuditEnds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} {budget : Time} :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fun a => a.payload.height_pair) (p0d4AuditKey k) budget ↔
      AttemptEndsBy p c E rho k budget := by
  rcases k with ⟨i, m, phase, task, served⟩
  constructor <;> rintro ⟨ev, hi, j, ev', hj, hn, ht, he⟩ <;>
    refine ⟨ev, hi, j, ev', hj, hn, ht, ?_⟩
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4AuditNamed _).symm ▸ hn⟩)
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4AuditNamed _) ▸ hn⟩)

omit [DecidableEq V] in
private theorem p0d4AuditBudget (G : Time) (k : AttemptKey) :
    FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) (p0d4AuditKey k) =
      attemptBudget p G k := by
  rcases k with ⟨i, m, phase, task, served⟩
  rw [FGCompose.p0d4_attemptBudget_def]
  cases task <;> cases phase <;> rfl

private def p0d4AuditOldKind : FGCompose.PhaseKind → PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4AuditOldTask : FGCompose.AttemptTask → AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4AuditOldKey (k : FGCompose.AttemptKey) : AttemptKey :=
  ⟨k.start, k.frontier, p0d4AuditOldKind k.phase, p0d4AuditOldTask k.task, k.served⟩

omit [DecidableEq V] in
private theorem p0d4AuditKeyBack (k : FGCompose.AttemptKey) :
    p0d4AuditKey (p0d4AuditOldKey k) = k := by
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> cases task <;> rfl

private theorem p0d4AuditValidBack (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : FGCompose.AttemptKey}
    (h : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) k) : AttemptValid p c E rho (p0d4AuditOldKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mp hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mpr hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [← p0d4AuditNamed] at he
      exact hn rfl j y r a h e hj ha he

#print axioms p0d4AuditGateResult
#print axioms p0d4AuditSource
#print axioms p0d4AuditExact
#print axioms p0d4AuditValid
#print axioms p0d4AuditEnds
#print axioms p0d4AuditBudget
#print axioms p0d4AuditKeyBack
#print axioms p0d4AuditValidBack
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_of_event
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_of_row
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_mono
#print axioms AvailableChain.FGSA.Run.healing_attempt_no_event
#print axioms AvailableChain.FGSA.Run.healing_attempt_inclusive_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_settle_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other
#print axioms AvailableChain.FGSA.Run.healing_progressAttempt_of
#print axioms AvailableChain.FGSA.Run.healing_progressAttempt
-- Actual FG-SA producer route. Each row wrapper constructs the certificate, store,
-- settlement, repair, opening, receipt, and promotion inputs of its extracted consumer.
-- These tests retain the original recovery premises and require an actual valid start.
section ProducerApplications
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
    (qc : RQCOrigin p c E rho)
    (repairScopes : RepairServiceScopes E rho)
    (openingScopes : OpeningServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

variable
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))

include hrec mono crossing qc repairScopes openingScopes writes rowCoverage
  hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum

private theorem p0d4AuditRaiseContest
    (k : FGCompose.AttemptKey) (ev : V2.Event V (Obj p))
    (hv : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) k)
    (hs : rho.events[k.start]? = some ev)
    (hh : ev.time + FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k ≤ rho.horizon)
    (ht : k.task = .raise) (hp : k.phase = .contest) :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fun a => a.payload.height_pair) k
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
  let ko := p0d4AuditOldKey k
  have hk := p0d4AuditKeyBack k
  have hb := p0d4AuditBudget (p := p) G ko
  change p0d4AuditKey ko = k at hk
  rw [hk] at hb
  have htask : ko.task = .raise := by
    change p0d4AuditOldTask k.task = .raise
    rw [ht]; rfl
  have hphase : ko.phase = .contest := by
    change p0d4AuditOldKind k.phase = .contest
    rw [hp]; rfl
  have result := healing_attempt_raise_contest E rho hrec mono crossing qc repairScopes
    openingScopes writes rowCoverage
    hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
    (p0d4AuditValidBack E rho hv) hs (by rwa [← hb]) htask hphase
  have he : AttemptEndsBy p c E rho ko
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
    rw [hb]
    exact result
  have h := (p0d4AuditEnds E rho).mpr he
  rwa [hk] at h

private theorem p0d4AuditRaiseOther
    (k : FGCompose.AttemptKey) (ev : V2.Event V (Obj p))
    (hv : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) k)
    (hs : rho.events[k.start]? = some ev)
    (hh : ev.time + FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k ≤ rho.horizon)
    (ht : k.task = .raise) (hp : k.phase ≠ .contest) :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fun a => a.payload.height_pair) k
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
  let ko := p0d4AuditOldKey k
  have hk := p0d4AuditKeyBack k
  have hb := p0d4AuditBudget (p := p) G ko
  change p0d4AuditKey ko = k at hk
  rw [hk] at hb
  have htask : ko.task = .raise := by
    change p0d4AuditOldTask k.task = .raise
    rw [ht]; rfl
  have hphase : ko.phase ≠ .contest := by
    change p0d4AuditOldKind k.phase ≠ .contest
    cases hkind : k.phase <;> first | exact (hp hkind).elim | intro h; cases h
  have result := healing_attempt_raise_other E rho hrec mono crossing qc repairScopes
    openingScopes writes rowCoverage
    hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
    (p0d4AuditValidBack E rho hv) hs (by rwa [← hb]) htask hphase
  have he : AttemptEndsBy p c E rho ko
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
    rw [hb]
    exact result
  have h := (p0d4AuditEnds E rho).mpr he
  rwa [hk] at h

omit hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum in
private theorem p0d4AuditFirstContest
    (k : FGCompose.AttemptKey) (ev : V2.Event V (Obj p))
    (hv : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) k)
    (hs : rho.events[k.start]? = some ev)
    (hh : ev.time + FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k ≤ rho.horizon)
    (ht : k.task = .firstRow) (hp : k.phase = .contest) :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fun a => a.payload.height_pair) k
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
  let ko := p0d4AuditOldKey k
  have hk := p0d4AuditKeyBack k
  have hb := p0d4AuditBudget (p := p) G ko
  change p0d4AuditKey ko = k at hk
  rw [hk] at hb
  have htask : ko.task = .firstRow := by
    change p0d4AuditOldTask k.task = .firstRow
    rw [ht]; rfl
  have hphase : ko.phase = .contest := by
    change p0d4AuditOldKind k.phase = .contest
    rw [hp]; rfl
  have result := healing_attempt_firstRow_contest E rho hrec mono crossing qc repairScopes
    openingScopes writes rowCoverage
    (p0d4AuditValidBack E rho hv) hs (by rwa [← hb]) htask hphase
  have he : AttemptEndsBy p c E rho ko
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
    rw [hb]
    exact result
  have h := (p0d4AuditEnds E rho).mpr he
  rwa [hk] at h

private theorem p0d4AuditFirstOther
    (k : FGCompose.AttemptKey) (ev : V2.Event V (Obj p))
    (hv : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) k)
    (hs : rho.events[k.start]? = some ev)
    (hh : ev.time + FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k ≤ rho.horizon)
    (ht : k.task = .firstRow) (hp : k.phase ≠ .contest) :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fun a => a.payload.height_pair) k
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
  let ko := p0d4AuditOldKey k
  have hk := p0d4AuditKeyBack k
  have hb := p0d4AuditBudget (p := p) G ko
  change p0d4AuditKey ko = k at hk
  rw [hk] at hb
  have htask : ko.task = .firstRow := by
    change p0d4AuditOldTask k.task = .firstRow
    rw [ht]; rfl
  have hphase : ko.phase ≠ .contest := by
    change p0d4AuditOldKind k.phase ≠ .contest
    cases hkind : k.phase <;> first | exact (hp hkind).elim | intro h; cases h
  have result := healing_attempt_firstRow_other E rho hrec mono crossing qc repairScopes
    openingScopes writes rowCoverage
    hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
    (p0d4AuditValidBack E rho hv) hs (by rwa [← hb]) htask hphase
  have he : AttemptEndsBy p c E rho ko
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
    rw [hb]
    exact result
  have h := (p0d4AuditEnds E rho).mpr he
  rwa [hk] at h

private theorem p0d4AuditProducerDispatch
    (k : FGCompose.AttemptKey) (ev : V2.Event V (Obj p))
    (hv : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) k)
    (hs : rho.events[k.start]? = some ev)
    (hh : ev.time + FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k ≤ rho.horizon) :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
      (p0d4AuditObs p c) (p0d4AuditTiming p) (fun a => a.payload.height_pair) k
      (FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) k) := by
  exact FGCompose.progressAttempt_of (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho
    (p0d4AuditObs p c) (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c)
    (fun a => a.payload.height_pair) (recoveryStart p E) G (ρΓ p G)
    (p0d4AuditRaiseContest E rho hrec mono crossing qc repairScopes openingScopes writes
      rowCoverage hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum)
    (p0d4AuditRaiseOther E rho hrec mono crossing qc repairScopes openingScopes writes
      rowCoverage hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum)
    (p0d4AuditFirstContest E rho hrec mono crossing qc repairScopes openingScopes writes
      rowCoverage)
    (p0d4AuditFirstOther E rho hrec mono crossing qc repairScopes openingScopes writes
      rowCoverage hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum)
    k ev hv hs hh

#print axioms p0d4AuditRaiseContest
#print axioms p0d4AuditRaiseOther
#print axioms p0d4AuditFirstContest
#print axioms p0d4AuditFirstOther
#print axioms p0d4AuditProducerDispatch
end ProducerApplications

end AvailableChain.FGSA.Run
end
