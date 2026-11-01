module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptBudget -- shake: keep (frozen budget)
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptStop
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneRepair

public import AvailableChainFGCompose.Proofs.Healing.AttemptRows


namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section P0d4RowsReadAdapters

private def p0d4RowsCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4RowsSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d4RowsObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d4RowsCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d4RowsTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d4RowsGate (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGAttemptGateReads (fgsa p c) where
  restartTime nd := nd.st.restartTime
  preClock nd t := { nd with st := clockPre p nd.st t }
  saved nd s := (GridCO.savedGenuine nd.st.base s).map (fun b => b.getD .genesis)
  confirmation nd s := SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F)
    (actView nd.st) s
  blocked nd B := (actView nd.st).obligations.any (fun row => !Block.compatible row.1 B)
  writes nd s := fastWriteAt nd.st s

private def p0d4RowsKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4RowsTask : AttemptTask → FGCompose.AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4RowsKey (k : AttemptKey) : FGCompose.AttemptKey :=
  ⟨k.start, k.frontier, p0d4RowsKind k.phase, p0d4RowsTask k.task, k.served⟩

private theorem p0d4RowsGateResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) :
    FGCompose.AttemptGateResult E rho (p0d4RowsTiming p) (p0d4RowsGate p c) x s =
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

private theorem p0d4RowsSource (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (r : Nat) :
    (FGCompose.actionSourceFG (p0d4RowsCore p c) E rho (p0d4RowsTiming p) x r).map
      (Option.map eraseFG) = actionSource p c E rho x r := by
  change ((postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)).map
    (Option.map eraseFG) = _
  change _ = (actionSourceFG p c E rho x r).map (Option.map eraseFG)
  rw [actionSourceFG_def]

private theorem p0d4RowsEnabled (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (x : V) (s : Slot) :
    FGCompose.AttemptEnabledGate E rho (p0d4RowsTiming p) (p0d4RowsGate p c) j x s ↔
      enabledGateAt p c E rho j x s := by
  rw [FGCompose.p0d4_AttemptEnabledGate_def]
  have reads : (p0d4RowsGate p c).restartTime (rho.stateBefore E j x) =
      (storeAt p c E rho j x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ht, hw⟩ <;> refine ⟨ht, ?_⟩
  all_goals
    cases hr : (storeAt p c E rho j x).restartTime <;>
      first | trivial | (rw [hr] at hw; exact hw)

private theorem p0d4RowsCaught (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (i : Nat) (t : Time) :
    FGCompose.AttemptCaughtUp E rho (p0d4RowsTiming p) (p0d4RowsGate p c) x i t ↔
      caughtUpAtIdx p c E rho x i t := by
  rw [FGCompose.p0d4_AttemptCaughtUp_def]
  have reads : (p0d4RowsGate p c).restartTime (rho.stateBefore E i x) =
      (storeAt p c E rho i x).restartTime := rfl
  rw [reads]
  constructor <;> rintro ⟨ha, hc⟩ <;> refine ⟨ha, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4RowsEnabled E rho j x s).mp hg, hawake, hn⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hc
      obtain ⟨s, j, hw, ht, hj, hg, hawake, hn⟩ := hc
      exact ⟨s, j, hw, ht, hj, (p0d4RowsEnabled E rho j x s).mpr hg, hawake, hn⟩

private theorem p0d4RowsPassed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : FGCompose.AttemptGatePassed E rho (p0d4RowsTiming p)
      (p0d4RowsGate p c) j ↔ gatePassedAt p c E rho j := by
  constructor
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4RowsEnabled E rho j x s).mp hg, ?_, h⟩
    exact Option.map_eq_none_iff.mp hs
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, (p0d4RowsEnabled E rho j x s).mpr hg, ?_, h⟩
    exact Option.map_eq_none_iff.mpr hs

private theorem p0d4RowsExact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) :
    FGCompose.AttemptExactService (p0d4RowsCore p c) E rho (p0d4RowsTiming p)
      (fgsaInterface p c) (p0d4RowsGate p c) s Q ↔ ExactService p c E rho s Q  := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4RowsCaught E rho x _ _).mpr hr.2⟩
    have gates : ∃ j, enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4RowsEnabled E rho j x s).mp hj, (p0d4RowsPassed E rho j).mp hp⟩
    exact ⟨(p0d4RowsGateResult E rho x s) ▸ hg, gates, hw, hs,
      fun r he => (p0d4RowsSource E rho x r) ▸ ha r he⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx
      ⟨hr.1, (p0d4RowsCaught E rho x _ _).mp hr.2⟩
    have gates : ∃ j, FGCompose.AttemptEnabledGate E rho (p0d4RowsTiming p)
        (p0d4RowsGate p c) j x s ∧
        FGCompose.AttemptGatePassed E rho (p0d4RowsTiming p) (p0d4RowsGate p c) j := by
      obtain ⟨j, hj, hp⟩ := hp
      exact ⟨j, (p0d4RowsEnabled E rho j x s).mpr hj, (p0d4RowsPassed E rho j).mpr hp⟩
    exact ⟨(p0d4RowsGateResult E rho x s).symm ▸ hg, gates, hw, hs,
      fun r he => (p0d4RowsSource E rho x r).symm ▸ ha r he⟩

omit [DecidableEq V] in
private theorem p0d4RowsNamed (a : NamedHeightPair) :
    FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem p0d4RowsRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0d4RowsSafety p c) E rho (p0d4RowsTiming p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0d4RowsValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} (h : AttemptValid p c E rho k) :
    FGCompose.AttemptValid (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) (p0d4RowsKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4RowsExact E rho s Q).mpr hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4RowsExact E rho s Q).mp hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [p0d4RowsNamed] at he
      exact hn rfl j y r a h e hj ha he

private theorem p0d4RowsEnds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} {budget : Time} :
    FGCompose.AttemptEndsBy (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fun a => a.payload.height_pair) (p0d4RowsKey k) budget ↔
      AttemptEndsBy p c E rho k budget := by
  rcases k with ⟨i, m, phase, task, served⟩
  constructor <;> rintro ⟨ev, hi, j, ev', hj, hn, ht, he⟩ <;>
    refine ⟨ev, hi, j, ev', hj, hn, ht, ?_⟩
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4RowsNamed _).symm ▸ hn⟩)
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4RowsNamed _) ▸ hn⟩)

omit [DecidableEq V] in
private theorem p0d4RowsBudget (G : Time) (k : AttemptKey) :
    FGCompose.attemptBudget (p0d4RowsTiming p) G (ρΓ p G) (p0d4RowsKey k) =
      attemptBudget p G k := by
  rcases k with ⟨i, m, phase, task, served⟩
  rw [FGCompose.p0d4_attemptBudget_def]
  cases task <;> cases phase <;> rfl

section P0d4RowLaws
variable (p : Params) (c : AppCodec In) (E : Generic.Env V)
  (rho : V2.D.Run V (fgsa p c))
private theorem p0d4RowsCoreEq (p : Params) {In : Type} (c : AppCodec In) :
    p0d4RowsCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm

private theorem p0d4RowsCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d4RowsCore p c) := by
  rw [p0d4RowsCoreEq]
  exact fgsaCoreLaws p c

private theorem p0d4RowsObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d4RowsCore p c) (p0d4RowsObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private theorem p0d4RowsTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d4RowsTiming p) where
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

private theorem p0d4RowsWitness {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d4RowsCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d4RowsReceipts {i m : Nat} {deadline : Time}
    (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d4RowsCore p c) E rho (p0d4RowsObs p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d4RowsWitness p c E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d4RowsWitness p c E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
      p0d4RowsWitness p c E rho hrC, p0d4RowsWitness p c E rho hrW⟩

end P0d4RowLaws

section P0d4RowAdapters
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
private theorem p0d4RowsPhase (u v : Time) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) :
    FGCompose.PhaseInterval (p0d4RowsCore p c) E rho (p0d4RowsObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  have reads (i : Nat) (x : V) :
      (p0d4RowsObs p c).controls (V2.D.Run.stateBefore E rho i x) = R_at p c E rho i x := by
    change FGSA.controls p (storeAt p c E rho i x) = frameR p (storeAt p c E rho i x)
    exact (frameR_def p _).symm
  constructor <;> rintro ⟨hu, hv, hm, h⟩ <;> refine ⟨hu, hv, hm, ?_⟩ <;> intro i x hi hv hx
  · cases J <;> exact (reads i x) ▸ h i x hi hv hx
  · cases J <;> exact (reads i x).symm ▸ h i x hi hv hx

private theorem p0d4RowsHonestSeats :
    Finset.univ.filter (fun i => FGCompose.safetyHolder (p0d4RowsSafety p c) rho i
      ∈ rho.honest) = honestSeats p c rho := by
  classical
  rw [honestSeats_def]
  apply Finset.filter_congr
  intro i _
  rw [FGCompose.safetyHolder_def]
  rfl

private theorem p0d4RowsCovered (r : Nat) (Q : Block) :
    FGCompose.OpeningCovered (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho
      (heightView p) (p0d4RowsTiming p) (fun a => a.payload.height_pair) r Q ↔
      OpeningCovered p c E rho r Q := by
  constructor
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, _, hQ, hr, ha, hn⟩ := h x hx
    have hK' : actionSourceFG p c E rho x r = some (some K) := hK
    have hnd' : postClock E rho x (p.actionTime r) = some nd := hnd
    rw [actionSourceFG_def, hnd'] at hK'
    have hs : fgSource p nd.st = some K := Option.some.inj hK'
    have hm : K ∈ fullTree p nd.st :=
      (Finset.mem_filter.mp (pickPair_some_spec _ _ hs).1).1
    exact ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha,
      (p0d4RowsNamed _) ▸ hn⟩
  · intro h x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha,
      (p0d4RowsNamed _).symm ▸ hn⟩

private theorem p0d4RowsRepairAfter (l : Slot) (v : Time) :
    FGCompose.AttemptRepairAfter (p0d4RowsCore p c) E rho (p0d4RowsTiming p)
      (fgsaInterface p c) (p0d4RowsGate p c) l v ↔ RepairAfter p c E rho l v := by
  constructor <;> intro h s Q hl hd hQ
  · exact (p0d4RowsExact E rho s Q).mp (h s Q hl hd hQ)
  · exact (p0d4RowsExact E rho s Q).mpr (h s Q hl hd hQ)
end P0d4RowAdapters

end P0d4RowsReadAdapters

public section

private theorem attempt_period_bounds (p : Params) : 8 * p.Δ ≤ P p := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
  nlinarith [p.deltaPos]

private theorem attempt_honest_nonempty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn := card_eq_n_of_linked hrec.base.linked
  have hc : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hle := Finset.card_le_univ rho.honest
    rw [hn] at hle
    omega
  have hf := hrec.fault
  have hp := p.nPos
  exact Finset.card_pos.mp (by omega)

omit [DecidableEq V] in
private theorem attempt_time_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {ev : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) {D : Time} (hD : i < timeIdx rho D) : ev.time ≤ D := by
  have he : rho.events.filter (fun e => decide (e.time < D + 1)) =
      rho.events.filter (fun e => decide (e.time ≤ D)) :=
    List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
  have hiD : i < V2.D.Run.idxBefore rho (D + 1) := by
    rw [V2.D.Run.idxBefore_def, he]
    exact hD
  exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi (D + 1)).mp hiD)

private theorem attempt_quiet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : AttemptKey} {ev : V2.Event V (Obj p)}
    {budget : Time} (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget) :
    ∀ j, k.start < j → j < timeIdx rho (ev.time + budget) →
      ¬ EffectiveEvent p c E rho j := by
  intro j hj hcut
  have hjlen : j < rho.events.length := hcut.trans_le (List.length_filter_le _ _)
  have hev := List.getElem?_eq_getElem hjlen
  exact healing_attempt_no_event E rho hstart hstop hj hev
    (attempt_time_le E rho hs hev hcut)

private theorem attempt_row_of_covered [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (htask : k.task = .firstRow) (hr : p.actionTime r ≤ ev.time + budget)
    (hcovered : OpeningCovered p c E rho r Q)
    (hentry : OpeningEntry p c E rho r k.frontier) : AttemptEndsBy p c E rho k budget := by
  obtain ⟨x, hx⟩ := attempt_honest_nonempty E rho hrec
  obtain ⟨K, nd, j, rSent, a, _hnd, hK, _hmem, _hQ, hrr, ha, hn⟩ := hcovered x hx
  obtain ⟨e, he⟩ := hentry
  have hn' : namedEntry a.payload.height_pair = some (k.frontier, e) := by
    obtain ⟨hh, ht⟩ := he x K hx hK
    rwa [hh, ht] at hn
  have hj : k.start < j := by
    by_contra h
    obtain ⟨_, _, _, _, _, _, _, _, hnone⟩ := hvalid
    exact hnone htask j x rSent a k.frontier e (Nat.le_of_not_gt h) ha hn' rfl
  have hsend : p.actionTime rSent ≤ p.actionTime r := by
    rw [actionTime_periodW, actionTime_periodW]
    have hrr' : (rSent : Time) ≤ r := by exact_mod_cast hrr
    have hP := attempt_period_bounds p
    nlinarith [p.deltaPos]
  exact healing_attempt_ends_of_row E rho hstart hj ha.2.1 (hsend.trans hr) htask ha hn'

section Rows
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


include hrec mono crossing qc repairScopes openingScopes writes rowCoverage

omit openingScopes rowCoverage in
private theorem p0d4RowsRepair :
    FGCompose.AttemptRepairService (p0d4RowsCore p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c)
      (recoveryStart p E) G (ρΓ p G) p.k := by
  intro hgap u v m J contested hgst hp β hβ hmin
  have hrepair := healing_tRepair E rho hrec mono crossing qc repairScopes writes
  have h := (hrepair G u v m J contested (healing_proposal_gap hrec) hgap hgst
    ((p0d4RowsPhase E rho u v m J contested).mp hp)).1
    β hβ hmin
  refine ⟨(p0d4RowsRepairAfter E rho _ _).mpr h.1, ?_⟩
  intro hv
  obtain ⟨s, Q, hl, hd, hQ, he⟩ := h.2 hv
  exact ⟨s, Q, hl, hd, hQ, (p0d4RowsExact E rho s Q).mpr he⟩

omit qc repairScopes in
private theorem p0d4RowsOpening :
    FGCompose.AttemptOpeningService (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho
      (p0d4RowsObs p c) (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) := by
  intro u m J contested q Q Qfg r hgst hQ heq hexact hu hqr hp
  have he := (p0d4RowsExact E rho q Q).mp hexact
  exact ⟨(p0d4RowsCovered E rho r Q).mpr (common_opening_covered E rho hrec mono
    crossing openingScopes writes rowCoverage hgst hQ heq he hu hqr
    ((p0d4RowsPhase E rho _ _ _ _ _).mp hp)),
    common_sources_extend_and_cap E rho hrec mono crossing openingScopes writes
      hgst hQ heq he hu hqr ((p0d4RowsPhase E rho _ _ _ _ _).mp hp)⟩

omit qc repairScopes rowCoverage in
private theorem p0d4RowsNextOpening :
    FGCompose.AttemptNextOpeningService (p0d4RowsCore p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c) (recoveryStart p E) := by
  intro u m J contested q Q Qfg r hgst hQ heq hexact hu hqr hp y K hy hK
  exact common_next_sources_extend_and_cap E rho hrec mono crossing openingScopes writes
    hgst hQ heq ((p0d4RowsExact E rho q Q).mp hexact) hu hqr
    ((p0d4RowsPhase E rho _ _ _ _ _).mp hp) hy hK

omit mono qc repairScopes openingScopes writes rowCoverage in
private theorem p0d4RowsFloor :
    FGCompose.AttemptProposalFloor (p0d4RowsCore p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fgsaInterface p c) (recoveryStart p E) := by
  intro u v m J contested q Q Qfg hgst hp hu hd hQ heq
  have hpold := (p0d4RowsPhase E rho u v m J contested).mp hp
  have hQfg : eraseFG Qfg = Q := heq
  -- The parent floor does not use exact service; the old proof's last argument is unused.
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨hH, hc, _⟩ := hpold.2.2.2 j x
    (healing_support_idxBefore_le p c E rho hS hj hu)
    (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hd)).le hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent, hQfg]))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]; exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rwa [hH', hc', he] at hlo

omit mono crossing qc repairScopes openingScopes writes rowCoverage in
private theorem p0d4RowsGateCopy :
    FGCompose.AttemptGateCopy (p0d4RowsCore p c) E rho (p0d4RowsObs p c)
      (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c) (recoveryStart p E) := by
  intro u v m J contested q Q Qfg hgst hp hu hd hQ heq hexact
  have hS := hrec.base.valid.toScheduleWellFormed
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨i, K, hi, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hS
    ((p0d4RowsExact E rho q Q).mp hexact) (hd.trans hp.2.1) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (hGST.trans hu) (hd.trans hp.2.1))
  have he : K = Qfg := eraseFG_injective (heK.trans heq.symm)
  subst K
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  exact ⟨i, _, healing_support_idxBefore_le p c E rho hS hi (hu.trans hqg),
    (healing_phase_lt_timeIdx p c E rho hS hi hd).le, hQ.1.2, hK⟩

omit mono crossing qc repairScopes openingScopes writes rowCoverage in
private theorem p0d4RowsCarrier (q : Slot) (Q : Block)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hg : recoveryStart p E ≤ SA.proposalTime p.toParams q)
    (he : FGCompose.AttemptExactService (p0d4RowsCore p c) E rho (p0d4RowsTiming p)
      (fgsaInterface p c) (p0d4RowsGate p c) q Q)
    (hh : SA.gateTime p.toParams q ≤ rho.horizon) : ∃ Qfg : FGBlock (Fin p.n), eraseFG Qfg = Q := by
  have hGST : E.t_GST ≤ SA.proposalTime p.toParams q := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨i, Qfg, hi, hm, heq⟩ := healing_rise_one_gate_copy p c E rho
    hrec.base.valid.toScheduleWellFormed ((p0d4RowsExact E rho q Q).mp he) hh hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 hGST hh)
  exact ⟨Qfg, heq⟩

omit mono qc repairScopes openingScopes writes rowCoverage in
private theorem attempt_proposal_heights
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u D m J contested)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams q ≤ D)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (heq : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q) :
    (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ m := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hui := healing_support_idxBefore_le p c E rho hS hj hu
  have hjD := (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hgate)).le
  obtain ⟨hH, hc, _hr⟩ := hp.2.2.2 j x hui hjD hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent, heq]))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]
    exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rw [hH', hc', he] at hlo
  have hparent : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  refine ⟨hlo.trans ((fgCertificateLaws p).height.h_mono hparent), ?_⟩
  obtain ⟨i, K, hi, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgate.trans hp.2.1) hx
    (healing_recovery_gate_reader hrec hx (by
      change E.t_GST ≤ SA.proposalTime p.toParams q
      exact hGST.trans hu) (hgate.trans hp.2.1))
  have hKe : K = Qfg := eraseFG_injective (heK.trans heq.symm)
  subst K
  have hui' := healing_support_idxBefore_le p c E rho hS hi (hu.trans hqg)
  have hiD := (healing_phase_lt_timeIdx p c E rho hS hi hgate).le
  have hcap := (hp.2.2.2 i x hui' hiD hx).1
  exact hcap ▸ healing_phase_height_le p c E rho hK

private theorem attempt_repair_opening
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget)
    (hhor : ev.time + budget ≤ rho.horizon)
    (hbudget : ev.time + 3 * p.Δ + ρΓ p G + (P p - 4 * p.Δ) ≤ ev.time + budget) :
    ∃ (β q : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n)) (r : Nat)
      (root : Option (FGBlock (Fin p.n))) (contested : Bool),
      let u := ev.time + 3 * p.Δ
      PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) ∧
      recoveryStart p E ≤ u ∧ u ≤ SA.proposalTime p.toParams q ∧
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q ∧
      SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q ∧
      eraseFG Qfg = Q ∧
      (if contested then k.frontier else k.frontier - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ k.frontier ∧
      q ≤ r * p.R ∧ p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) ∧
      OpeningCovered p c E rho r Q ∧
      (∀ v, PhaseInterval p c E rho u v k.frontier root contested →
        RepairAfter p c E rho (β + 2 * p.k - 1) v) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hP := attempt_period_bounds p
  have huD : ev.time + 3 * p.Δ ≤ ev.time + budget := by
    have hΓ : 0 ≤ Γ p G := by
      have := (fgsa_gamma_bounds p G).1
      linarith [hrec.gapPos, p.deltaPos]
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    have hρ : 0 ≤ ρΓ p G := by
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  obtain ⟨J, hp, _hframe⟩ := healing_attempt_settle_start p c E rho mono
    (fun _ ht => healing_ready_read_cutoff E ht)
    (healing_phase_witness_receipts_recovery E rho hrec) crossing hrec
    hvalid hstart huD hhor (attempt_quiet E rho hS hstart hstop)
  let u := ev.time + 3 * p.Δ
  have hsettled : ∃ (root : Option (FGBlock (Fin p.n))) (contested : Bool),
      PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) := by
    refine ⟨_, _, hp, ?_⟩
    cases k.phase with
    | gap => constructor <;> intro h <;> cases h
    | topJ => constructor <;> intro h <;> cases h
    | contest => exact ⟨fun _ => rfl, fun _ => rfl⟩
  obtain ⟨root, contested, hp, hcont⟩ := hsettled
  have hgst0 : recoveryStart p E ≤ ev.time := by
    obtain ⟨ev0, hi0, hgst0, _⟩ := hvalid
    have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
    exact he ▸ hgst0
  have hgst : recoveryStart p E ≤ u := by dsimp only [u]; linarith [p.deltaPos]
  obtain ⟨β, hβ, hmin⟩ := healing_rise_one_grid p u
  have hrepair := healing_tRepair E rho hrec mono crossing qc repairScopes writes
  have hafter := ((hrepair G u _ _ root contested
      (healing_proposal_gap hrec) hrec.gapPos hgst hp).1 β hβ hmin).1
  obtain ⟨q, Q, hq, hgate, hQ, hexact⟩ :=
    ((hrepair G u _ _ root contested
      (healing_proposal_gap hrec) hrec.gapPos hgst hp).1 β hβ hmin).2
      (by dsimp only [u]; linarith [p.deltaPos])
  have hβl : β ≤ β + 2 * p.k - 1 := by
    have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
  have hβI : (β : Time) ≤ ((β + 2 * p.k - 1 : Nat) : Time) := by exact_mod_cast hβl
  have hβt : SA.proposalTime p.toParams β ≤
      SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Time) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Time)
    nlinarith [p.deltaPos]
  have huq := hβ.le.trans (hβt.trans hq.le)
  have hgateD : SA.gateTime p.toParams q ≤ ev.time + budget := by
    dsimp only [u] at hgate
    linarith [p.deltaPos]
  obtain ⟨_i, Qfg, _hi, _hK, heq⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgateD.trans hhor) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (by
      change E.t_GST ≤ SA.proposalTime p.toParams q
      have hGST : E.t_GST ≤ u := by
        have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos]
      exact hGST.trans huq) (hgateD.trans hhor))
  obtain ⟨hlo, hhi⟩ := attempt_proposal_heights E rho hrec crossing
    hgst hp huq hgateD hQ heq hexact
  have hex : ∃ r, q ≤ r * p.R := by
    refine ⟨q, le_mul_of_one_le_right (Nat.zero_le q) ?_⟩
    exact le_trans (by decide : 1 ≤ (2 : Nat)) p.RLarge
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) q r hqr hfirst
  have har : p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) := by linarith
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hur : u ≤ p.actionTime r := by linarith
  have hpr := opening_phase_restrict E rho hp hur (har.trans hbudget)
  have hc := common_opening_covered E rho hrec mono crossing openingScopes writes rowCoverage hgst
    hQ heq hexact huq hqr hpr
  refine ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, ?_⟩
  intro v hv
  exact ((hrepair G u v _ root contested
    (healing_proposal_gap hrec) hrec.gapPos hgst hv).1 β hβ hmin).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / contest, with the standing ports and exact INLINE bodies.
The SO producer is rowPermission_covered. Both AttemptValid start arms are covered. -/
theorem healing_attempt_firstRow_contest
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  have result := FGCompose.healing_attempt_firstRow_contest
    (R := p0d4RowsCore p c) (S := p0d4RowsSafety p c) (E := E) (rho := rho)
    (O := p0d4RowsObs p c) (T := p0d4RowsTiming p) (I := fgsaInterface p c)
    (A := p0d4RowsGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4RowsObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4RowsTimingLaws p) (coreLaws := p0d4RowsCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    (hs := hrec.base.valid.toScheduleWellFormed) (mono := ⟨mono⟩) (hdelta := hrec.base.delta)
    (gst := by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    (awake := hrec.awake)
    (joinedTick := fun _ _ _ hy hi hh hc => healing_recovery_joinedNow hrec hy hi hh hc)
    (readyCut := fun _ ht => healing_ready_read_cutoff E ht)
    (heldServices := fun j e m hj hr hm hf hh => p0d4RowsReceipts p c E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (receiptHeld := fun W d y hy hr => healing_held_block_receipt_on p c E rho
      hrec.base.valid hrec.base.receiptIdealization W d y hy hr)
    (G := G) (repairAllowance := ρΓ p G) (leaseSlots := p.k) (leaseLarge := p.kLarge)
    (allowanceNonneg := by
      have hΓ : 0 ≤ Γ p G := by
        have := (fgsa_gamma_bounds p G).1
        linarith [hrec.gapPos, p.deltaPos]
      have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos])
    (gapPos := hrec.gapPos)
    (repair := p0d4RowsRepair E rho hrec mono crossing qc repairScopes writes)
    (opening := p0d4RowsOpening E rho hrec mono crossing openingScopes writes rowCoverage)
    (proposalFloor := p0d4RowsFloor E rho hrec crossing)
    (gateCopy := p0d4RowsGateCopy E rho hrec)
    (exactCarrier := p0d4RowsCarrier E rho hrec)
    (crossing := crossing)
    (honestNonempty := attempt_honest_nonempty E rho hrec)
    (k := p0d4RowsKey k) (p0d4RowsValid E rho hvalid) hstart
    (by rwa [p0d4RowsBudget G k])
    (by change p0d4RowsTask k.task = _; rw [htask]; rfl)
    (by change p0d4RowsKind k.phase = .contest; rw [hphase]; rfl)
  rw [p0d4RowsBudget G k] at result
  exact (p0d4RowsEnds E rho).mp result

omit [Fintype V] hrec mono crossing qc repairScopes openingScopes writes rowCoverage in
private theorem attempt_row_of_high_source
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (htask : k.task = .firstRow) (hr : p.actionTime r ≤ ev.time + budget)
    (hcovered : OpeningCovered p c E rho r Q)
    {x : V} {K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hh : (heightView p K).h = k.frontier) : AttemptEndsBy p c E rho k budget := by
  obtain ⟨L, nd, j, rSent, a, _hnd, hL, _hmem, _hQ, hrr, ha, hn⟩ := hcovered x hx
  have he : L = K := Option.some.inj (Option.some.inj (hL.symm.trans hK))
  subst L
  rw [hh] at hn
  have hj : k.start < j := by
    by_contra h
    obtain ⟨_, _, _, _, _, _, _, _, hnone⟩ := hvalid
    exact hnone htask j x rSent a k.frontier _ (Nat.le_of_not_gt h) ha hn rfl
  have hsend : p.actionTime rSent ≤ p.actionTime r := by
    rw [actionTime_periodW, actionTime_periodW]
    have hrr' : (rSent : Time) ≤ r := by exact_mod_cast hrr
    have hP := attempt_period_bounds p
    nlinarith [p.deltaPos]
  exact healing_attempt_ends_of_row E rho hstart hj ha.2.1 (hsend.trans hr) htask ha hn

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

include hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum

omit qc repairScopes rowCoverage in
private theorem p0d4RowsRenewed :
    FGCompose.AttemptRenewedPromotion (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho
      (p0d4RowsObs p c) (p0d4RowsTiming p) (fgsaInterface p c) (p0d4RowsGate p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) G := by
  intro r hh u m J contested l q Q height hgst hp hu hqr hl hQ hexact he hc hrepair
  have h := healing_renewedPromotion E rho hrec (healing_self_proposal_service hrec)
    hδ hbound mono crossing
    (healing_tPerm E rho hrec mono crossing writes openingScopes.permanence)
    rowsReceipt
    progressCoverage hfold faultQ honestQuorum r hh u m J contested l q Q height
    hgst
    ((p0d4RowsPhase E rho _ _ _ _ _).mp hp) hu hqr hl hQ ((p0d4RowsExact E rho q Q).mp hexact) he
    ((p0d4RowsCovered E rho r Q).mp hc)
    (fun v hv => (p0d4RowsRepairAfter E rho l v).mp
      (hrepair v ((p0d4RowsPhase E rho _ _ _ _ _).mpr hv)))
  rcases h with h | ⟨s, X, hX, hs, hlo, hhi, hhX, hr, hgate⟩
  · exact Or.inl h
  · refine Or.inr ⟨s, X, hX, hs, hlo, hhi, hhX, hr, ?_⟩
    intro hp
    obtain ⟨he, hd⟩ := hgate ((p0d4RowsPhase E rho _ _ _ _ _).mp hp)
    exact ⟨(p0d4RowsExact E rho s _).mpr he, hd⟩

omit qc repairScopes rowCoverage in
private theorem p0d4RowsTerminal :
    FGCompose.AttemptTerminalPromotion (p0d4RowsCore p c) (p0d4RowsSafety p c) E rho
      (p0d4RowsObs p c) (p0d4RowsTiming p) (fgsaInterface p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) G := by
  intro r hh u m J contested q Q height hgst hp hu hqr he hc
  exact healing_renewedPromotion_terminal E rho hrec
    (healing_self_proposal_service hrec) hδ hbound mono crossing
    (healing_tPerm E rho hrec mono crossing writes openingScopes.permanence)
    rowsReceipt progressCoverage hfold faultQ
    honestQuorum r hh u m J contested q Q height hgst
    ((p0d4RowsPhase E rho _ _ _ _ _).mp hp) hu hqr he
    ((p0d4RowsCovered E rho r Q).mp hc)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / gap or topJ, with standing ports and the exact INLINE facts.
The low-entry branch uses renewed promotion within its existing gate horizon. -/
theorem healing_attempt_firstRow_other
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  have result := FGCompose.healing_attempt_firstRow_other
    (R := p0d4RowsCore p c) (S := p0d4RowsSafety p c) (E := E) (rho := rho)
    (O := p0d4RowsObs p c) (T := p0d4RowsTiming p) (I := fgsaInterface p c)
    (A := p0d4RowsGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4RowsObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4RowsTimingLaws p) (coreLaws := p0d4RowsCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    (hs := hrec.base.valid.toScheduleWellFormed) (mono := ⟨mono⟩) (hdelta := hrec.base.delta)
    (gst := by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    (awake := hrec.awake)
    (joinedTick := fun _ _ _ hy hi hh hc => healing_recovery_joinedNow hrec hy hi hh hc)
    (readyCut := fun _ ht => healing_ready_read_cutoff E ht)
    (heldServices := fun j e m hj hr hm hf hh => p0d4RowsReceipts p c E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (receiptHeld := fun W d y hy hr => healing_held_block_receipt_on p c E rho
      hrec.base.valid hrec.base.receiptIdealization W d y hy hr)
    (G := G) (repairAllowance := ρΓ p G) (leaseSlots := p.k) (leaseLarge := p.kLarge)
    (allowanceNonneg := by
      have hΓ : 0 ≤ Γ p G := by
        have := (fgsa_gamma_bounds p G).1
        linarith [hrec.gapPos, p.deltaPos]
      have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos])
    (gapPos := hrec.gapPos)
    (repair := p0d4RowsRepair E rho hrec mono crossing qc repairScopes writes)
    (opening := p0d4RowsOpening E rho hrec mono crossing openingScopes writes rowCoverage)
    (proposalFloor := p0d4RowsFloor E rho hrec crossing)
    (gateCopy := p0d4RowsGateCopy E rho hrec)
    (exactCarrier := p0d4RowsCarrier E rho hrec)
    (crossing := crossing)
    (honestNonempty := attempt_honest_nonempty E rho hrec)
    (faultQ := faultQ) (honestQuorum := by rwa [p0d4RowsHonestSeats rho])
    (renewed := fun _ _ => p0d4RowsRenewed E rho hrec mono crossing openingScopes writes
      hδ hbound rowsReceipt progressCoverage hfold
      faultQ honestQuorum)
    (nextOpening := p0d4RowsNextOpening E rho hrec mono crossing openingScopes writes)
    (k := p0d4RowsKey k) (p0d4RowsValid E rho hvalid) hstart
    (by rwa [p0d4RowsBudget G k])
    (by change p0d4RowsTask k.task = _; rw [htask]; rfl)
    (by
      change p0d4RowsKind k.phase ≠ .contest
      cases hp : k.phase <;> first | exact (hphase hp).elim | intro h; cases h)
  rw [p0d4RowsBudget G k] at result
  exact (p0d4RowsEnds E rho).mp result

omit qc rowCoverage in
omit repairScopes qc rowCoverage in
private theorem attempt_terminal_contradiction
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget u : Time}
    {root : Option (FGBlock (Fin p.n))} {contested : Bool} {q r : Nat} {Q : Block}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget)
    (hp : PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested)
    (hu : ev.time + 3 * p.Δ ≤ u) (hgst : recoveryStart p E ≤ u)
    (huq : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (he : OpeningEntry p c E rho r k.frontier)
    (hc : OpeningCovered p c E rho r Q)
    (hterminal : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ ev.time + budget) :
    False := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hP := attempt_period_bounds p
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  have hur : u ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change u ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrD : p.actionTime r ≤ ev.time + budget := by linarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur hrD
  have perm := healing_tPerm E rho hrec mono crossing writes openingScopes.permanence
  rcases healing_renewedPromotion_terminal E rho hrec (healing_self_proposal_service hrec)
      hδ hbound mono crossing perm
      rowsReceipt progressCoverage hfold faultQ honestQuorum r (hterminal.trans hp.2.1)
      u k.frontier root contested q Q k.frontier hgst hpr huq hqr he hc
      with hevent | hcarrier
  · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
    have hsi : k.start < V2.D.Run.idxBefore rho (p.actionTime r) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hstart _).mpr (by
        change ev.time < p.actionTime r
        linarith [p.deltaPos])
    have hj : k.start < i := hsi.trans_le ((preIdx_le_afterTicksIdx E rho hS _).1.trans hi)
    exact hstop (healing_attempt_ends_of_event E rho hstart hj hev'
      (ht.trans hterminal) heff)
  · obtain ⟨s, X, _hnew, _hslot, hslo, hshi, hh, y, hy, hheld⟩ := hcarrier
    let d := SA.proposalTime p.toParams s + p.Δ
    have ha := actionTime_periodW p r
    have hud : u ≤ d := by dsimp only [d]; linarith [p.deltaPos]
    have hdD : d ≤ ev.time + budget := by dsimp only [d]; linarith
    change X ∈ (V2.D.Run.stateBeforeTime E rho d y).st.fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hS] at hheld
    have hcap := (hp.2.2.2 (V2.D.Run.idxBefore rho d) y
      (healing_phase_idxBefore_mono p c rho hud)
      (healing_phase_idx_le_time p c rho hdD) hy).1
    have hle := healing_phase_height_le p c E rho hheld
    change (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.h_max = k.frontier at hcap
    rw [hcap] at hle
    simp only [Height] at hh hle
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / contest, with the standing ports and exact INLINE bodies.
Terminal promotion uses the first high opening within the frozen budget. -/
theorem healing_attempt_raise_contest
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  have result := FGCompose.healing_attempt_raise_contest
    (R := p0d4RowsCore p c) (S := p0d4RowsSafety p c) (E := E) (rho := rho)
    (O := p0d4RowsObs p c) (T := p0d4RowsTiming p) (I := fgsaInterface p c)
    (A := p0d4RowsGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4RowsObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4RowsTimingLaws p) (coreLaws := p0d4RowsCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    (hs := hrec.base.valid.toScheduleWellFormed) (mono := ⟨mono⟩) (hdelta := hrec.base.delta)
    (gst := by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    (awake := hrec.awake)
    (joinedTick := fun _ _ _ hy hi hh hc => healing_recovery_joinedNow hrec hy hi hh hc)
    (readyCut := fun _ ht => healing_ready_read_cutoff E ht)
    (heldServices := fun j e m hj hr hm hf hh => p0d4RowsReceipts p c E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (receiptHeld := fun W d y hy hr => healing_held_block_receipt_on p c E rho
      hrec.base.valid hrec.base.receiptIdealization W d y hy hr)
    (G := G) (repairAllowance := ρΓ p G) (leaseSlots := p.k) (leaseLarge := p.kLarge)
    (allowanceNonneg := by
      have hΓ : 0 ≤ Γ p G := by
        have := (fgsa_gamma_bounds p G).1
        linarith [hrec.gapPos, p.deltaPos]
      have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos])
    (gapPos := hrec.gapPos)
    (repair := p0d4RowsRepair E rho hrec mono crossing qc repairScopes writes)
    (opening := p0d4RowsOpening E rho hrec mono crossing openingScopes writes rowCoverage)
    (proposalFloor := p0d4RowsFloor E rho hrec crossing)
    (gateCopy := p0d4RowsGateCopy E rho hrec)
    (exactCarrier := p0d4RowsCarrier E rho hrec)
    (crossing := crossing)
    (faultQ := faultQ) (honestQuorum := by rwa [p0d4RowsHonestSeats rho])
    (terminal := fun _ _ => p0d4RowsTerminal E rho hrec mono crossing openingScopes writes
      hδ hbound rowsReceipt progressCoverage hfold
      faultQ honestQuorum)
    (k := p0d4RowsKey k) (p0d4RowsValid E rho hvalid) hstart
    (by rwa [p0d4RowsBudget G k])
    (by change p0d4RowsTask k.task = _; rw [htask]; rfl)
    (by change p0d4RowsKind k.phase = .contest; rw [hphase]; rfl)
  rw [p0d4RowsBudget G k] at result
  exact (p0d4RowsEnds E rho).mp result

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / gap or topJ, with the standing ports and exact INLINE bodies.
The low pivot uses existing gate service. Terminal promotion then uses a high opening. -/
theorem healing_attempt_raise_other
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  have result := FGCompose.healing_attempt_raise_other
    (R := p0d4RowsCore p c) (S := p0d4RowsSafety p c) (E := E) (rho := rho)
    (O := p0d4RowsObs p c) (T := p0d4RowsTiming p) (I := fgsaInterface p c)
    (A := p0d4RowsGate p c) (pair := fun a => a.payload.height_pair)
    (Jst := recoveryStart p E) (Ef := p.E) (obs := p0d4RowsObsLaws p c)
    (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (hT := p0d4RowsTimingLaws p) (coreLaws := p0d4RowsCoreLaws p c)
    (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    (hs := hrec.base.valid.toScheduleWellFormed) (mono := ⟨mono⟩) (hdelta := hrec.base.delta)
    (gst := by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    (awake := hrec.awake)
    (joinedTick := fun _ _ _ hy hi hh hc => healing_recovery_joinedNow hrec hy hi hh hc)
    (readyCut := fun _ ht => healing_ready_read_cutoff E ht)
    (heldServices := fun j e m hj hr hm hf hh => p0d4RowsReceipts p c E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (receiptHeld := fun W d y hy hr => healing_held_block_receipt_on p c E rho
      hrec.base.valid hrec.base.receiptIdealization W d y hy hr)
    (G := G) (repairAllowance := ρΓ p G) (leaseSlots := p.k) (leaseLarge := p.kLarge)
    (allowanceNonneg := by
      have hΓ : 0 ≤ Γ p G := by
        have := (fgsa_gamma_bounds p G).1
        linarith [hrec.gapPos, p.deltaPos]
      have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos])
    (gapPos := hrec.gapPos)
    (repair := p0d4RowsRepair E rho hrec mono crossing qc repairScopes writes)
    (opening := p0d4RowsOpening E rho hrec mono crossing openingScopes writes rowCoverage)
    (proposalFloor := p0d4RowsFloor E rho hrec crossing)
    (gateCopy := p0d4RowsGateCopy E rho hrec)
    (exactCarrier := p0d4RowsCarrier E rho hrec)
    (crossing := crossing)
    (faultQ := faultQ) (honestQuorum := by rwa [p0d4RowsHonestSeats rho])
    (renewed := fun _ _ => p0d4RowsRenewed E rho hrec mono crossing openingScopes writes
      hδ hbound rowsReceipt progressCoverage hfold
      faultQ honestQuorum)
    (nextOpening := p0d4RowsNextOpening E rho hrec mono crossing openingScopes writes)
    (terminal := fun _ _ => p0d4RowsTerminal E rho hrec mono crossing openingScopes writes
      hδ hbound rowsReceipt progressCoverage hfold
      faultQ honestQuorum)
    (k := p0d4RowsKey k) (p0d4RowsValid E rho hvalid) hstart
    (by rwa [p0d4RowsBudget G k])
    (by change p0d4RowsTask k.task = _; rw [htask]; rfl)
    (by
      change p0d4RowsKind k.phase ≠ .contest
      cases hp : k.phase <;> first | exact (hphase hp).elim | intro h; cases h)
  rw [p0d4RowsBudget G k] at result
  exact (p0d4RowsEnds E rho).mp result

end Rows
end
end AvailableChain.FGSA.Run
