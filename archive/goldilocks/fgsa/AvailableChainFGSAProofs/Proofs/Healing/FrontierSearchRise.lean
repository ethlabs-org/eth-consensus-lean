module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a -- shake: keep (re-export read by Tests/HealingH2ServiceAxioms)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise

public section

/-! Blueprint 21 HG.4:1695–1720; S5 F2.
The saved entry and first opening give the frozen rise guard.
INLINE writes and rowCoverage are the same inputs as healing_frontierTail_row. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cRiseCore (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem p0d5cRiseCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cRiseCore p c) := by
  have h : p0d5cRiseCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cRiseTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cRiseTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cRiseTiming p) where
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

private def p0d5cRiseObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cRiseCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cRiseObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cRiseCore p c) (p0d5cRiseObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cRiseSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5cRiseSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5cRiseDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

private def p0d5cRiseWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5cRiseSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5cRiseSigner
  decode_height a u ha := by
    delta p0d5cRiseSafety at ha
    rw [p0d5cRiseDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5cRiseSafety at ha
    rw [p0d5cRiseDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5cRiseSafety at ha
    rw [p0d5cRiseDecodeRow ha]
    rfl

private def p0d5cRiseDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5cRiseDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5cRiseDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5cRiseDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5cRisePayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5cRiseSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5cRiseSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5cRiseSigner; simp
  | proposer s => delta p0d5cRiseSigner; simp
  | seat label j => cases label <;> delta p0d5cRiseSigner <;> simp

private def p0d5cRiseWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5cRiseR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5cRiseWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5cRiseWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5cRiseKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private abbrev p0d5cRisePair (a : RowWire p.n) : NamedHeightPair := a.payload.height_pair

private theorem p0d5cRisePhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5cRiseCore p c) E rho (p0d5cRiseObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

omit [DecidableEq V] in
private theorem p0d5cRiseSeed_iff (E : Generic.Env V) {u : Time} {q : Slot} :
    FGCompose.FrontierSeedQualification (p0d5cRiseTiming p) p.k E.t_GST u q ↔
      FrontierSeedQualification p E u q :=
  (frontierSeedQualification_iff p E u q).symm

private theorem p0d5cRiseStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (h : FrontierSearchStart p c E rho i ev m kind) :
    FGCompose.FrontierSearchStart (p0d5cRiseCore p c) E rho (p0d5cRiseObs p c) (p0d5cRiseTiming p)
      (recoveryStart p E) i ev m (p0d5cRiseKind kind) := by
  have h' := (frontierSearchStart_iff p c E rho i ev m kind).mp h
  cases kind <;> exact h'


section p0d5cRiseD5b
variable [Fintype V]


omit [Fintype V] in
private abbrev p0d5cRiseBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5cRiseCore p c) (p0d5cRiseSafety p c) (p0d5cRiseObs p c)
    (p0d5cRiseTiming p) E rho (fgsaInterface p c) (p0d5cRiseWire p c) p.E
    p0d5cRiseDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5cRiseCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cRiseDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5cRisePayload o s N ((p0d5cRiseDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5cRiseBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5cRiseBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5cRiseCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5cRiseSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5cRiseFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5cRiseFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5cRiseSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5cRiseSafety p c
  have linked : Function.Injective (FGCompose.safetyHolder S rho) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hsub : (FGCompose.historyFaulty S rho).image (FGCompose.safetyHolder S rho) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hc := (Finset.card_image_of_injective _ linked).symm.trans_le
    (Finset.card_le_card hsub)
  have hw : p.E.weightOf (FGCompose.historyFaulty S rho) =
      (FGCompose.historyFaulty S rho).card := by
    delta Electorate.weightOf
    simp only [show ∀ i, p.E.weight i = 1 from fun _ => rfl, Finset.sum_const,
      smul_eq_mul, mul_one]
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt faultQ.lt

-- Proposal leaf: the actual carrier and the post-clock parent read (PromotionCarrier route).
private theorem p0d5cRiseRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5cRiseCore p c) (p0d5cRiseSafety p c) E rho
      (p0d5cRiseObs p c) (fgsaInterface p c) p0d5cRiseDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5cRiseWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cRiseDecode NamedProposal.erase NamedProposal.rows) s
      (eraseFG X) rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧ _
  rw [hXQ]
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, hrows⟩ :=
    healing_promotion_proposal_read p c E rho hrec.base.valid.toScheduleWellFormed hQX
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v)
    (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : Q.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk Q N.rows = true := by
    rw [hb, hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : Q ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st Q.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  have hXeq : X = fgBlock P Q N.rows :=
    eraseFG_injective (hXQ.trans (eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok).symm)
  subst hXeq
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  have hdec : p0d5cRiseDecode o = some (s, N) :=
    (p0d5cRiseDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5cRiseR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5cRiseSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5cRiseOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5cRiseCore p c) E rho (p0d5cRiseObs p c) (fgsaInterface p c)
      := by
  intro s X height U hnew _ hpar hUP i W hW hn
  obtain ⟨Y, he, _, _, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hnew
  have hYX : Y = X := eraseFG_injective he
  subst Y
  have hinv := (storeBundle_of_reachable p st
    (healing_promotion_proposal_reachable p c E rho hst)).cstore
  have hparent : X.parent ∈ st.fg.TF := ((fgBlockOf_spec p st hinv _ _).mp hlookup).1
  exact healing_rows_above_entry_at_height p st
    (healing_promotion_proposal_reachable p c E rho hst) .progress height U X.parent
    hparent hpar hUP i W hW hn

omit [Fintype V] in
-- Row leaf: honest rows decode and carry their holder's seat (linked seats).
private theorem p0d5cRiseRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5cRiseSafety p c) E rho (p0d5cRiseTiming p)
      (p0d5cRiseWire p c) := by
  refine ⟨?_, ?_⟩
  · intro j x r a hrow
    obtain ⟨i, hauth⟩ := honestRow_auth p c rho E base.valid hrow
    cases a with
    | mk auth payload =>
      change auth = .seat .fg i at hauth
      subst auth
      exact ⟨_, rfl⟩
  · intro i j r a hrow
    obtain ⟨i', hauth⟩ := honestRow_auth p c rho E base.valid hrow
    have hseat : rho.seatOf (.base .fg) i' = rho.seatOf (.base .fg) i := by
      have hem := hrow.2.2
      cases a with
      | mk auth body =>
        change auth = .seat .fg i' at hauth
        subst auth
        exact ((fgsa_emitsAt_row E rho j _ _ hrow.2.1 i' body).mp hem).2.1
    have hii : i' = i := (base.linked.toCStar (.base .fg) trivial).1 hseat
    subst i'
    exact (p0d5cRiseSigner_iff a i).mpr hauth

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5cRiseSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5cRiseCore p c) E rho (p0d5cRiseTiming p)
      (fgsaInterface p c) := by
  intro s hslot hgsts hhor
  change E.t_GST + 4 * p.Δ ≤ SA.proposalTime p.toParams s at hgsts
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    change E.t_GST + 4 * p.Δ ≤ 4 * p.Δ * (s : Int) at hgsts
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    linarith
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ hws he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hwgst : w ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart _ hslot.2 j w hj (lt_of_not_ge hn)
        ((hws.trans hhor).trans_lt (lt_add_of_pos_right _ (by decide)))
    exact hwgst.trans hcut
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot (by linarith [p.deltaPos]) hhor hjoin
  exact ⟨X, hnew, hXslot⟩

omit [Fintype V] in
-- Source transfer leaf: healing_promotion_source_parent (TPerm at the source body).
private theorem p0d5cRiseSourceParent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (perm : TPerm p c E rho) :
    FGCompose.PromotionSourceParent (p0d5cRiseCore p c) E rho (p0d5cRiseObs p c) (p0d5cRiseTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested r s X x K hready hphase hu hgate hs hnew hx hK
  have hp := healing_promotion_source_parent E rho perm hready
    ((p0d5cRisePhase_iff E rho).mp hphase) hu hgate hx hK hs hnew
  change Block.Preceq (eraseFG K) (eraseFG X).parent at hp
  rw [eraseFG_parent] at hp
  exact eraseFG_preceq_iff.mp hp

omit [Fintype V] in
private theorem p0d5cRiseCovered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5cRiseCore p c) (p0d5cRiseSafety p c) E rho
      (heightView p) (p0d5cRiseTiming p) (p0d5cRiseWire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d5cRiseParentSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, N, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : N.erase = eraseFG W := Option.some.inj hb
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [hQ, eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem p0d5cRiseAncestorSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s root body rows ih =>
      by_cases he : U = .node P s root body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (p0d5cRiseParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5cRiseAncestor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hUK : FGBlock.Preceq U K) : U.slot ≤ K.slot := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact p0d5cRiseAncestorSlot E rho hrec.base.valid i x hs hUK


-- Receipt leaf, cap form: healing_promotion_first_receipt_of_frontierCap with the
-- existing self-proposal receiver service.
private theorem p0d5cRiseCapReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.PromotionCapReceipt (p0d5cRiseCore p c) E rho (p0d5cRiseObs p c) (p0d5cRiseTiming p)
      (fgsaInterface p c) := by
  intro m s Qfg X hnew hgst hQX hcap hQm hhor
  exact healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂ crossing
    (healing_self_proposal_service hrec s) hnew hgst hQX hcap hQm hhor


end p0d5cRiseD5b

-- Stored-slot leaf of an honest proposal's own slot (repair_proposal_slot).
private theorem p0d5cRiseProposalSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    ∀ q Q K, HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cRiseCore p c).erase K = Q →
      K.slot = q := by
  intro q Q K hQ he
  have h := repair_proposal_slot E rho hQ
  rw [← he] at h
  change (eraseFG K).slot = q at h
  rwa [eraseFG_slot] at h

-- Continuing local service of the frozen exact-service seed (TFrontier).
private theorem p0d5cRiseLocal (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (frontier : TFrontier p c E rho) {u : Time} {m q : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested) :
    ∀ v, SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cRiseCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cRiseCore p c) (p0d5cRiseSafety p c) E rho (p0d5cRiseObs
        p c)
        (p0d5cRiseTiming p) (fgsaInterface p c) p0d5cRisePair q Q Qfg m v := by
  intro v hg hv hcap
  obtain ⟨htransfer, hrepair, hopen⟩ := frontier u v m J contested q Q Qfg hready hQ he hh
    hexact ((frontierSeedQualification_iff p E u q).mp hseed) hu hp hg hv hcap
  refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
  · intro s B hqs hgate hprop
    exact (hrepair s B hqs hgate hprop).1
  · intro r hqr hrt
    obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
    refine ⟨?_, hent, hheight, htime⟩
    intro x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ', hr, ha, hn⟩ := hcov x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ', hr, ha, hn⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, saved-seed rise tail.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
No phase after the saved gate or horizon beyond the frozen rise guard is assumed. -/
theorem healing_frontierTail_rise_of_seed [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {t : Time}
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hserved : StrongServed p c E rho m t)
    (hhor : t + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (t + (2 * P p + Γ p G - 9 * p.Δ)) := by
  obtain ⟨u, J, contested, q, Q, Qfg, hgst, hQ, he, hQm, hexact,
    hseed, hu, hp, hqt, hth, _⟩ := (strongServed_iff p c E rho m t).mp hserved
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨iq, W, _, hW, hWe⟩ := healing_rise_one_gate_copy p c E rho hs hexact
    (hqt.trans hth) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 ((hJst.trans hgst).trans hu) (hqt.trans hth))
  have hWQ : W = Qfg := eraseFG_injective (hWe.trans he.symm)
  subst W
  have h := FGCompose.healing_frontierTail_rise_of_seed (p0d5cRiseCore p c) (p0d5cRiseSafety p c)
    (p0d5cRiseObs p c) (p0d5cRiseTiming p) E rho (fgsaInterface p c) (p0d5cRiseWire p c) p.E
      p0d5cRiseDecode
    NamedProposal.erase NamedProposal.rows (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5cRiseWindow (parentFoldState p s H)) (recoveryStart p E)
    (fgCertificateLaws p) (fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1) (p0d5cRiseTimingLaws p) hs
    (p0d5cRiseFault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) hJst ⟨mono⟩ (fun X => eraseFG_parent X)
    (fun A B h => eraseFG_preceq_iff.mp h) (p0d5cRiseSlot E rho hrec)
    (p0d5cRiseRead E rho hrec.toRecovery₂) (p0d5cRiseOrder E rho hrec.toRecovery₂)
    (p0d5cRiseRowSigner E rho hrec.base) (p0d5cRiseCapReceipt E rho hrec crossing) hδ ⟨hbound.1⟩
    rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5cRiseBatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5cRiseFoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    (fun r x y K L hx hy hK hL he => rootScope_eq hrec.base.idealization
      (rootScope_entry (rootScope_source hx hK)) (rootScope_entry (rootScope_source hy hL)) he)
    (fun r x K hx hK => healing_source_slot p c E rho hx hK)
    (fun r x K A _ hK hAK => p0d5cRiseAncestor E rho hrec.toRecovery₂ hK hAK)
    (fun i x A K hK hAK => p0d5cRiseAncestorSlot E rho hrec.base.valid i x hK hAK)
    (p0d5cRiseProposalSlot E rho) hgst hQ he hQm hu hqt ⟨iq, _, hW⟩
    (p0d5cRiseLocal E rho frontier hgst hQ he hQm hexact hseed hu hp) hstart hhor
  exact (frontierRiseBy_iff p c E rho i m _).mpr h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, HG.4 rise.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
No phase after the saved gate or horizon beyond the frozen rise guard is assumed. -/
theorem healing_frontierTail_rise [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hserved : StrongServed p c E rho m ev.time)
    (hhor : ev.time + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (ev.time + (2 * P p + Γ p G - 9 * p.Δ)) := by
  have hf := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.1
  exact healing_frontierTail_rise_of_seed E rho hrec hδ hbound mono crossing
    frontier
    rowsReceipt progressCoverage hfold faultQ honestQuorum hf.le hserved hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, full HG.4.
DC: SAME combine the capped rise and run-1 exact-height row under their separate guards. -/
theorem healing_frontierTail [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
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
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    : FrontierTailStatement p c E rho G ΔF := by
  apply (frontierTailStatement_iff p c E rho G ΔF).mpr
  intro hδ hbound i ev m kind hstart hserved
  exact ⟨fun hhor => healing_frontierTail_rise E rho hrec hδ hbound mono crossing
      (frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage)
      rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hserved hhor,
    fun hhor => healing_frontierTail_row E rho hrec mono crossing cap scopeProducer writes
      rowCoverage
      hserved hhor⟩

end AvailableChain.FGSA.Run
end
