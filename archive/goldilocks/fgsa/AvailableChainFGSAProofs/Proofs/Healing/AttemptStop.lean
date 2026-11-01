module
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGCompose.Proofs.Healing.AttemptStop

public import AvailableChainFGSARun.Statements.Client


namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section P0d4StopAdapters

private def p0d4StopCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4StopSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4StopObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d4StopCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d4StopTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d4StopGate (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGAttemptGateReads (fgsa p c) where
  restartTime nd := nd.st.restartTime
  preClock nd t := { nd with st := clockPre p nd.st t }
  saved nd s := (GridCO.savedGenuine nd.st.base s).map (fun b => b.getD .genesis)
  confirmation nd s := SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F)
    (actView nd.st) s
  blocked nd B := (actView nd.st).obligations.any (fun row => !Block.compatible row.1 B)
  writes nd s := fastWriteAt nd.st s

private def p0d4StopKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4StopTask : AttemptTask → FGCompose.AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4StopKey (k : AttemptKey) : FGCompose.AttemptKey :=
  ⟨k.start, k.frontier, p0d4StopKind k.phase, p0d4StopTask k.task, k.served⟩

private theorem p0d4StopGateResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) :
    FGCompose.AttemptGateResult E rho (p0d4StopTiming p) (p0d4StopGate p c) x s =
      gateResult p c E rho x s := by
  classical
  rw [FGCompose.p0d4_AttemptGateResult_def, gateResult_def, gateIn_def]
  change (preTick E rho x (SA.gateTime p.toParams s)).map _ = _
  rw [Option.map_map]
  apply congrArg (fun f : Node p → Option Block =>
    (preTick E rho x (SA.gateTime p.toParams s)).map f)
  funext nd
  rw [Function.comp_apply]
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

private theorem p0d4StopSource (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (r : Nat) :
    (FGCompose.actionSourceFG (p0d4StopCore p c) E rho (p0d4StopTiming p) x r).map
      (Option.map eraseFG) = actionSource p c E rho x r := by
  change ((postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)).map
    (Option.map eraseFG) = _
  change _ = (actionSourceFG p c E rho x r).map (Option.map eraseFG)
  rw [actionSourceFG_def]

private theorem p0d4StopEnabled (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (x : V) (s : Slot) :
    FGCompose.AttemptEnabledGate E rho (p0d4StopTiming p) (p0d4StopGate p c) j x s ↔
      enabledGateAt p c E rho j x s := by
  rw [FGCompose.p0d4_AttemptEnabledGate_def]
  have reads : (p0d4StopGate p c).restartTime (rho.stateBefore E j x) =
      (storeAt p c E rho j x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ht, hw⟩ <;> refine ⟨ht, ?_⟩
  all_goals
    cases hr : (storeAt p c E rho j x).restartTime <;>
      first | trivial | (rw [hr] at hw; exact hw)

private theorem p0d4StopCaught (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i : Nat) (t : Time) :
    FGCompose.AttemptCaughtUp E rho (p0d4StopTiming p) (p0d4StopGate p c) x i t ↔
      caughtUpAtIdx p c E rho x i t := by
  rw [FGCompose.p0d4_AttemptCaughtUp_def]
  have reads : (p0d4StopGate p c).restartTime (rho.stateBefore E i x) =
      (storeAt p c E rho i x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ha, hc⟩ <;> refine ⟨ha, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4StopEnabled E rho j x s).mp hg, hawake, hn⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4StopEnabled E rho j x s).mpr hg, hawake, hn⟩

private theorem p0d4StopPassed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : FGCompose.AttemptGatePassed E rho (p0d4StopTiming p)
      (p0d4StopGate p c) j ↔ gatePassedAt p c E rho j := by
  constructor
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4StopEnabled E rho j x s).mp hg, ?_, h⟩
    exact Option.map_eq_none_iff.mp hs
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4StopEnabled E rho j x s).mpr hg, ?_, h⟩
    exact Option.map_eq_none_iff.mpr hs

private theorem p0d4StopExact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) :
    FGCompose.AttemptExactService (p0d4StopCore p c) E rho (p0d4StopTiming p)
      (fgsaInterface p c) (p0d4StopGate p c) s Q ↔ ExactService p c E rho s Q  := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4StopCaught E rho x _ _).mpr hr.2⟩
    have gates : ∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4StopEnabled E rho j x s).mp hj, (p0d4StopPassed E rho j).mp hp⟩
    exact ⟨(p0d4StopGateResult E rho x s) ▸ hg, gates, hw, hs,
      fun r he => (p0d4StopSource E rho x r) ▸ ha r he⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4StopCaught E rho x _ _).mp hr.2⟩
    have gates : ∃ j, FGCompose.AttemptEnabledGate E rho (p0d4StopTiming p)
        (p0d4StopGate p c) j x s ∧
        FGCompose.AttemptGatePassed E rho (p0d4StopTiming p) (p0d4StopGate p c) j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4StopEnabled E rho j x s).mpr hj, (p0d4StopPassed E rho j).mpr hp⟩
    exact ⟨(p0d4StopGateResult E rho x s).symm ▸ hg, gates, hw, hs,
      fun r he => (p0d4StopSource E rho x r).symm ▸ ha r he⟩

omit [DecidableEq V] in
private theorem p0d4StopNamed (a : NamedHeightPair) :
    FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem p0d4StopRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0d4StopSafety p c) E rho (p0d4StopTiming p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0d4StopValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} (h : AttemptValid p c E rho k) :
    FGCompose.AttemptValid (p0d4StopCore p c) (p0d4StopSafety p c) E rho (p0d4StopObs p c)
      (p0d4StopTiming p) (fgsaInterface p c) (p0d4StopGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) (p0d4StopKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4StopExact E rho s Q).mpr hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4StopExact E rho s Q).mp hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [p0d4StopNamed] at he
      exact hn rfl j y r a h e hj ha he

private theorem p0d4StopEnds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} {budget : Time} :
    FGCompose.AttemptEndsBy (p0d4StopCore p c) (p0d4StopSafety p c) E rho (p0d4StopObs p c)
      (p0d4StopTiming p) (fun a => a.payload.height_pair) (p0d4StopKey k) budget ↔
      AttemptEndsBy p c E rho k budget := by
  rcases k with ⟨i, m, phase, task, served⟩
  constructor <;> rintro ⟨ev, hi, j, ev', hj, hn, ht, he⟩ <;>
    refine ⟨ev, hi, j, ev', hj, hn, ht, ?_⟩
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4StopNamed _).symm ▸ hn⟩)
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4StopNamed _) ▸ hn⟩)


end P0d4StopAdapters

public section

/-- Blueprint 21 H.10:1428–1429, 1494–1498. An earlier event stops the attempt.
No service past that event is required. -/
theorem healing_attempt_ends_of_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (heff : EffectiveEvent p c E rho j) : AttemptEndsBy p c E rho k budget := by
  exact (p0d4StopEnds E rho).mp (FGCompose.healing_attempt_ends_of_event
    (p0d4StopCore p c) (p0d4StopSafety p c) E rho (p0d4StopObs p c)
    (p0d4StopTiming p)
      (fun a => a.payload.height_pair)
      (k := p0d4StopKey k) hstart hj hnext htime heff)

/-- One later matching honest row completes the first-row task. -/
theorem healing_attempt_ends_of_row {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat} {y : V} {r : Nat}
    {a : RowWire p.n} {e : BlockId}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (htask : k.task = .firstRow) (hrow : HonestRowAt p c E rho j y r a)
    (hnamed : namedEntry a.payload.height_pair = some (k.frontier, e)) :
    AttemptEndsBy p c E rho k budget := by
  have ht : (p0d4StopKey k).task = .firstRow := by
    change p0d4StopTask k.task = .firstRow
    rw [htask]; rfl
  exact (p0d4StopEnds E rho).mp (FGCompose.healing_attempt_ends_of_row
    (p0d4StopCore p c) (p0d4StopSafety p c) E rho (p0d4StopObs p c)
    (p0d4StopTiming p)
      (fun a => a.payload.height_pair)
      (k := p0d4StopKey k) hstart hj hnext htime ht hrow
    ((p0d4StopNamed _).symm ▸ hnamed))

theorem healing_attempt_ends_mono {k : AttemptKey} {budget budget' : Time}
    (hends : AttemptEndsBy p c E rho k budget) (hbudget : budget ≤ budget') :
    AttemptEndsBy p c E rho k budget' := by
  exact (p0d4StopEnds E rho).mp (FGCompose.healing_attempt_ends_mono
    (p0d4StopCore p c) (p0d4StopSafety p c) E rho (p0d4StopObs p c)
    (p0d4StopTiming p) (fun a => a.payload.height_pair) ((p0d4StopEnds E rho).mpr hends) hbudget)

/-- A failed stopped-task bound excludes every effective event within its budget. -/
theorem healing_attempt_no_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget) :
    ¬ EffectiveEvent p c E rho j := by
  exact FGCompose.healing_attempt_no_event (p0d4StopCore p c) (p0d4StopSafety p c) E rho
    (p0d4StopObs p c)
    (p0d4StopTiming p) (fun a => a.payload.height_pair)
    (k := p0d4StopKey k) hstart
    (fun h => hstop ((p0d4StopEnds E rho).mp h)) hj hnext htime

/-- The second frozen start arm is required when the start event is not effective.
This extracts that arm; it makes no settlement claim. -/
theorem healing_attempt_inclusive_start {k : AttemptKey}
    (hvalid : AttemptValid p c E rho k) (hne : ¬ EffectiveEvent p c E rho k.start) :
    ∃ ev rG, rho.events[k.start]? = some ev ∧ recoveryStart p E ≤ ev.time ∧
      recoveryStart p E ≤ p.actionTime rG ∧
      (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 := by
  exact FGCompose.healing_attempt_inclusive_start (p0d4StopCore p c)
    (p0d4StopSafety p c) E rho (p0d4StopObs p c) (p0d4StopTiming p)
    (fgsaInterface p c) (p0d4StopGate p c) (fun a => a.payload.height_pair)
    (recoveryStart p E) (p0d4StopValid E rho hvalid) hne

end
end AvailableChain.FGSA.Run
