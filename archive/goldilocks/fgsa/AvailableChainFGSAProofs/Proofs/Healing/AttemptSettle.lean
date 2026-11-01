module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle -- shake: keep (frozen settlement)
public import AvailableChainFGCompose.Proofs.Healing.AttemptSettle


namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

variable (mono : RMonoAll p c E rho)

variable (readyCut : ∀ t, recoveryStart p E ≤ t →
  E.t_GST ≤ slotStartZ p (((slotAt p t : Slot) : Int) - 1))

variable (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
  rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
  frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
  PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))

section P0d4SettCorrespondence
omit [Fintype V]
variable {p : Params} {c : AppCodec In}
private def p0d4SettCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4SettSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4SettObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d4SettCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d4SettTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d4SettGate (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGAttemptGateReads (fgsa p c) where
  restartTime nd := nd.st.restartTime
  preClock nd t := { nd with st := clockPre p nd.st t }
  saved nd s := (GridCO.savedGenuine nd.st.base s).map (fun b => b.getD .genesis)
  confirmation nd s := SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F)
    (actView nd.st) s
  blocked nd B := (actView nd.st).obligations.any (fun row => !Block.compatible row.1 B)
  writes nd s := fastWriteAt nd.st s

private def p0d4SettKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4SettTask : AttemptTask → FGCompose.AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4SettKey (k : AttemptKey) : FGCompose.AttemptKey :=
  ⟨k.start, k.frontier, p0d4SettKind k.phase, p0d4SettTask k.task, k.served⟩

private theorem p0d4SettGateResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) :
    FGCompose.AttemptGateResult E rho (p0d4SettTiming p) (p0d4SettGate p c) x s =
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

private theorem p0d4SettSource (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (r : Nat) :
    (FGCompose.actionSourceFG (p0d4SettCore p c) E rho (p0d4SettTiming p) x r).map
      (Option.map eraseFG) = actionSource p c E rho x r := by
  change ((postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)).map
    (Option.map eraseFG) = _
  change _ = (actionSourceFG p c E rho x r).map (Option.map eraseFG)
  rw [actionSourceFG_def]

private theorem p0d4SettEnabled (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (x : V) (s : Slot) :
    FGCompose.AttemptEnabledGate E rho (p0d4SettTiming p) (p0d4SettGate p c) j x s ↔
      enabledGateAt p c E rho j x s := by
  rw [FGCompose.p0d4_AttemptEnabledGate_def]
  have reads : (p0d4SettGate p c).restartTime (rho.stateBefore E j x) =
      (storeAt p c E rho j x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ht, hw⟩ <;> refine ⟨ht, ?_⟩
  all_goals
    cases hr : (storeAt p c E rho j x).restartTime <;>
      first | trivial | (rw [hr] at hw; exact hw)

private theorem p0d4SettCaught (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i : Nat) (t : Time) :
    FGCompose.AttemptCaughtUp E rho (p0d4SettTiming p) (p0d4SettGate p c) x i t ↔
      caughtUpAtIdx p c E rho x i t := by
  rw [FGCompose.p0d4_AttemptCaughtUp_def]
  have reads : (p0d4SettGate p c).restartTime (rho.stateBefore E i x) =
      (storeAt p c E rho i x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ha, hc⟩ <;> refine ⟨ha, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4SettEnabled E rho j x s).mp hg, hawake, hn⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4SettEnabled E rho j x s).mpr hg, hawake, hn⟩

private theorem p0d4SettPassed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : FGCompose.AttemptGatePassed E rho (p0d4SettTiming p)
      (p0d4SettGate p c) j ↔ gatePassedAt p c E rho j := by
  constructor
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4SettEnabled E rho j x s).mp hg, ?_, h⟩
    exact Option.map_eq_none_iff.mp hs
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4SettEnabled E rho j x s).mpr hg, ?_, h⟩
    exact Option.map_eq_none_iff.mpr hs

private theorem p0d4SettExact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) :
    FGCompose.AttemptExactService (p0d4SettCore p c) E rho (p0d4SettTiming p)
      (fgsaInterface p c) (p0d4SettGate p c) s Q ↔ ExactService p c E rho s Q  := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4SettCaught E rho x _ _).mpr hr.2⟩
    have gates : ∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4SettEnabled E rho j x s).mp hj, (p0d4SettPassed E rho j).mp hp⟩
    exact ⟨(p0d4SettGateResult E rho x s) ▸ hg, gates, hw, hs,
      fun r he => (p0d4SettSource E rho x r) ▸ ha r he⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4SettCaught E rho x _ _).mp hr.2⟩
    have gates : ∃ j, FGCompose.AttemptEnabledGate E rho (p0d4SettTiming p)
        (p0d4SettGate p c) j x s ∧
        FGCompose.AttemptGatePassed E rho (p0d4SettTiming p) (p0d4SettGate p c) j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4SettEnabled E rho j x s).mpr hj, (p0d4SettPassed E rho j).mpr hp⟩
    exact ⟨(p0d4SettGateResult E rho x s).symm ▸ hg, gates, hw, hs,
      fun r he => (p0d4SettSource E rho x r).symm ▸ ha r he⟩

omit [DecidableEq V] in
private theorem p0d4SettNamed (a : NamedHeightPair) :
    FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem p0d4SettRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0d4SettSafety p c) E rho (p0d4SettTiming p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0d4SettValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} (h : AttemptValid p c E rho k) :
    FGCompose.AttemptValid (p0d4SettCore p c) (p0d4SettSafety p c) E rho (p0d4SettObs p c)
      (p0d4SettTiming p) (fgsaInterface p c) (p0d4SettGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) (p0d4SettKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4SettExact E rho s Q).mpr hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4SettExact E rho s Q).mp hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [p0d4SettNamed] at he
      exact hn rfl j y r a h e hj ha he

end P0d4SettCorrespondence

section P0d4SettLaws
omit [Fintype V]

private theorem p0d4SettCoreEq (p : Params) {In : Type} (c : AppCodec In) :
    p0d4SettCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm

private theorem p0d4SettCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d4SettCore p c) := by
  rw [p0d4SettCoreEq]
  exact fgsaCoreLaws p c

private theorem p0d4SettObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d4SettCore p c) (p0d4SettObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private theorem p0d4SettTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d4SettTiming p) where
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

private theorem p0d4SettWitness {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d4SettCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d4SettReceipts {i m : Nat} {deadline : Time}
    (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d4SettCore p c) E rho (p0d4SettObs p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d4SettWitness p c E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d4SettWitness p c E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
      p0d4SettWitness p c E rho hrC, p0d4SettWitness p c E rho hrW⟩

end P0d4SettLaws

public section

include mono readyCut heldServices

/-! H-ATTEMPT-2 CUT. These lemmas supply settlement for each budget row.
They retain the RXing input of H.8. They do not assert a complete row bound.
The AttemptValid start disjunction is not used, so its inclusive-cut arm
needs no effective event and no new settlement premise. -/

/-- ROOT-DIGEST W2b. H.8 settlement for either frozen AttemptValid start arm. -/
theorem healing_attempt_settle_start
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  have result := FGCompose.healing_attempt_settle_start
    (R := p0d4SettCore p c) (S := p0d4SettSafety p c) (E := E) (rho := rho)
    (O := p0d4SettObs p c) (T := p0d4SettTiming p) (I := fgsaInterface p c)
    (A := p0d4SettGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4SettObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4SettTimingLaws p) (coreLaws := p0d4SettCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    hrec.base.valid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d4SettReceipts p c E rho (heldServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    crossing (p0d4SettValid E rho hvalid) hstart hu hv hquiet
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> exact result

/-- Settlement for the raise / contest row, including the cut start. -/
theorem healing_attempt_raise_contest_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .raise) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  have result := FGCompose.healing_attempt_raise_contest_settle
    (R := p0d4SettCore p c) (S := p0d4SettSafety p c) (E := E) (rho := rho)
    (O := p0d4SettObs p c) (T := p0d4SettTiming p) (I := fgsaInterface p c)
    (A := p0d4SettGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4SettObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4SettTimingLaws p) (coreLaws := p0d4SettCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    hrec.base.valid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d4SettReceipts p c E rho (heldServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    crossing (p0d4SettValid E rho hvalid) hstart hu hv hquiet
    (by change p0d4SettTask k.task = _; rw [_htask]; rfl)
    (by change p0d4SettKind k.phase = .contest; rw [_hphase]; rfl)
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> exact result

/-- Settlement for the raise / other row, including the cut start. -/
theorem healing_attempt_raise_other_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .raise) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  have result := FGCompose.healing_attempt_raise_other_settle
    (R := p0d4SettCore p c) (S := p0d4SettSafety p c) (E := E) (rho := rho)
    (O := p0d4SettObs p c) (T := p0d4SettTiming p) (I := fgsaInterface p c)
    (A := p0d4SettGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4SettObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4SettTimingLaws p) (coreLaws := p0d4SettCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    hrec.base.valid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d4SettReceipts p c E rho (heldServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    crossing (p0d4SettValid E rho hvalid) hstart hu hv hquiet
    (by change p0d4SettTask k.task = _; rw [_htask]; rfl)
    (by
      change p0d4SettKind k.phase ≠ .contest
      cases hp : k.phase <;> first | exact (_hphase hp).elim | intro h; cases h)
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> exact result

/-- Settlement for the firstRow / contest row, including the cut start. -/
theorem healing_attempt_firstRow_contest_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .firstRow) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  have result := FGCompose.healing_attempt_firstRow_contest_settle
    (R := p0d4SettCore p c) (S := p0d4SettSafety p c) (E := E) (rho := rho)
    (O := p0d4SettObs p c) (T := p0d4SettTiming p) (I := fgsaInterface p c)
    (A := p0d4SettGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4SettObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4SettTimingLaws p) (coreLaws := p0d4SettCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    hrec.base.valid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d4SettReceipts p c E rho (heldServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    crossing (p0d4SettValid E rho hvalid) hstart hu hv hquiet
    (by change p0d4SettTask k.task = _; rw [_htask]; rfl)
    (by change p0d4SettKind k.phase = .contest; rw [_hphase]; rfl)
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> exact result

/-- Settlement for the firstRow / other row, including the cut start. -/
theorem healing_attempt_firstRow_other_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .firstRow) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  have result := FGCompose.healing_attempt_firstRow_other_settle
    (R := p0d4SettCore p c) (S := p0d4SettSafety p c) (E := E) (rho := rho)
    (O := p0d4SettObs p c) (T := p0d4SettTiming p) (I := fgsaInterface p c)
    (A := p0d4SettGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4SettObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4SettTimingLaws p) (coreLaws := p0d4SettCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    hrec.base.valid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d4SettReceipts p c E rho (heldServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    crossing (p0d4SettValid E rho hvalid) hstart hu hv hquiet
    (by change p0d4SettTask k.task = _; rw [_htask]; rfl)
    (by
      change p0d4SettKind k.phase ≠ .contest
      cases hp : k.phase <;> first | exact (_hphase hp).elim | intro h; cases h)
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> exact result

end
end AvailableChain.FGSA.Run
