module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a -- shake: keep (producers)
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSAProofs.Proofs.Shared.HealingFixture -- shake: keep (fixture)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5bTstCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bTstTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5bTstTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5bTstTiming p) where
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

private def p0d5bTstObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5bTstCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5bTstSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bTstSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5bTstDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def p0d5bTstWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5bTstSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5bTstSigner
  decode_height a u ha := by
    delta p0d5bTstSafety at ha
    rw [p0d5bTstDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5bTstSafety at ha
    rw [p0d5bTstDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5bTstSafety at ha
    rw [p0d5bTstDecodeRow ha]
    rfl

private def p0d5bTstDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5bTstDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5bTstDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5bTstDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5bTstPayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5bTstSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5bTstSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5bTstSigner; simp
  | proposer s => delta p0d5bTstSigner; simp
  | seat label j => cases label <;> delta p0d5bTstSigner <;> simp

private def p0d5bTstWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5bTstR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5bTstWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5bTstWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section p0d5bTstBridge
variable [Fintype V]

omit [Fintype V] in
private abbrev p0d5bTstBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5bTstCore p c) (p0d5bTstSafety p c) (p0d5bTstObs p c)
    (p0d5bTstTiming p) E rho (fgsaInterface p c) (p0d5bTstWire p c) p.E
    p0d5bTstDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5bTstCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bTstDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5bTstPayload o s N ((p0d5bTstDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5bTstBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5bTstBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5bTstCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5bTstSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5bTstFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5bTstFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5bTstSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5bTstSafety p c
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
private theorem p0d5bTstRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5bTstCore p c) (p0d5bTstSafety p c) E rho
      (p0d5bTstObs p c) (fgsaInterface p c) p0d5bTstDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5bTstWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bTstDecode NamedProposal.erase NamedProposal.rows) s
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
  have hdec : p0d5bTstDecode o = some (s, N) :=
    (p0d5bTstDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5bTstR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5bTstSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5bTstOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5bTstCore p c) E rho (p0d5bTstObs p c) (fgsaInterface p c) := by
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
private theorem p0d5bTstRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5bTstSafety p c) E rho (p0d5bTstTiming p)
      (p0d5bTstWire p c) := by
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
    exact (p0d5bTstSigner_iff a i).mpr hauth

omit [Fintype V] in
private theorem p0d5bTstPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5bTstCore p c) E rho (p0d5bTstObs p c) u v m J
      contested ↔ PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5bTstSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5bTstCore p c) E rho (p0d5bTstTiming p)
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
private theorem p0d5bTstSourceParent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (perm : TPerm p c E rho) :
    FGCompose.PromotionSourceParent (p0d5bTstCore p c) E rho (p0d5bTstObs p c) (p0d5bTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested r s X x K hready hphase hu hgate hs hnew hx hK
  have hp := healing_promotion_source_parent E rho perm hready
    ((p0d5bTstPhase_iff E rho).mp hphase) hu hgate hx hK hs hnew
  change Block.Preceq (eraseFG K) (eraseFG X).parent at hp
  rw [eraseFG_parent] at hp
  exact eraseFG_preceq_iff.mp hp

-- Receipt leaf, phase form: healing_promotion_first_receipt with its receiver service.
private theorem p0d5bTstReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x)) :
    FGCompose.PromotionPhaseReceipt (p0d5bTstCore p c) E rho (p0d5bTstObs p c) (p0d5bTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested s X hready hnew hut hpD
  exact healing_promotion_first_receipt E rho hrec crossing (services s) hnew hut hready
    ((p0d5bTstPhase_iff E rho).mp hpD)

omit [Fintype V] in
private theorem p0d5bTstCovered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5bTstCore p c) (p0d5bTstSafety p c) E rho
      (heightView p) (p0d5bTstTiming p) (p0d5bTstWire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

private theorem p0d5bTstNonempty (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hf := hrec.fault
  rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
  have := p.nPos
  omega

omit [Fintype V] in
private theorem p0d5bTstParentSlot (E : Generic.Env V)
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
private theorem p0d5bTstAncestorSlot (E : Generic.Env V)
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
          (p0d5bTstParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5bTstAncestor (E : Generic.Env V)
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
    exact p0d5bTstAncestorSlot E rho hrec.base.valid i x hs hUK

-- Receipt leaf, cap form: healing_promotion_first_receipt_of_frontierCap with the
-- existing self-proposal receiver service.
private theorem p0d5bTstCapReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.PromotionCapReceipt (p0d5bTstCore p c) E rho (p0d5bTstObs p c) (p0d5bTstTiming p)
      (fgsaInterface p c) := by
  intro m s Qfg X hnew hgst hQX hcap hQm hhor
  exact healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂ crossing
    (healing_self_proposal_service hrec s) hnew hgst hQX hcap hQm hhor

end p0d5bTstBridge

/-! P0d5b G0. Every supplier-boundary leaf of FrontierMaturity is produced by its
existing FG-SA producer from the frozen hypotheses; none is assumed. -/

-- G0 (producer-backed leaves): recovery, crossing, permanence and the receiver
-- service give all seven leaves and the faulty-weight bound.
private theorem p0d5bTstLeaves [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) (perm : TPerm p c E rho)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    FGCompose.PromotionSlotProposal (p0d5bTstCore p c) E rho (p0d5bTstTiming p)
      (fgsaInterface p c) ∧
    FGCompose.PromotionProposalRead (p0d5bTstCore p c) (p0d5bTstSafety p c) E rho
      (p0d5bTstObs p c) (fgsaInterface p c) p0d5bTstDecode NamedProposal.erase
      NamedProposal.rows (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5bTstWindow (parentFoldState p s H)) ∧
    FGCompose.PromotionRowOrder (p0d5bTstCore p c) E rho (p0d5bTstObs p c)
      (fgsaInterface p c) ∧
    FGCompose.PromotionRowSigner (p0d5bTstSafety p c) E rho (p0d5bTstTiming p)
      (p0d5bTstWire p c) ∧
    FGCompose.PromotionSourceParent (p0d5bTstCore p c) E rho (p0d5bTstObs p c)
      (p0d5bTstTiming p) (fgsaInterface p c) (recoveryStart p E) ∧
    FGCompose.PromotionPhaseReceipt (p0d5bTstCore p c) E rho (p0d5bTstObs p c)
      (p0d5bTstTiming p) (fgsaInterface p c) (recoveryStart p E) ∧
    FGCompose.PromotionCapReceipt (p0d5bTstCore p c) E rho (p0d5bTstObs p c)
      (p0d5bTstTiming p) (fgsaInterface p c) ∧
    p.E.weightOf (FGCompose.historyFaulty (p0d5bTstSafety p c) rho) < p.E.q :=
  ⟨p0d5bTstSlot E rho hrec, p0d5bTstRead E rho hrec.toRecovery₂,
    p0d5bTstOrder E rho hrec.toRecovery₂, p0d5bTstRowSigner E rho hrec.base,
    p0d5bTstSourceParent E rho perm,
    p0d5bTstReceipt E rho hrec.toRecovery₂ crossing services,
    p0d5bTstCapReceipt E rho hrec crossing, p0d5bTstFault rho hrec.base faultQ⟩

-- G0 (fold and coverage): the proved fold producer gives the generic fold advance, and a
-- generic progress batch is the frozen batch at the same reads.
private theorem p0d5bTstFoldProduced (p : Params) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt :=
  p0d5bTstFoldAdvance (fgsa_foldTrichotomy_progress p)

/-- The run of Tests.NonVacuity.HealingRun.run, written out: the same params, env, gap,
deltaF and the same 311-batch events (ticks 0..310), with horizon 310 (HealingRun.horizon).
HealingRun.nvRecovery and nvPerm are stated for exactly this run; HealingFixture.mkRun alone keeps
horizon 304, which no schedule with tick 310 satisfies. -/
private abbrev p0d5bFixtureRun : V2.D.Run (Fin 1) (fgsa HealingFixture.params unitCodec) :=
  { HealingFixture.mkRun (HealingFixture.runPrefix 311).1 with horizon := 310 }

-- Guard: the horizon is 310, and the last batch index of the 311-prefix (tick time 310) is
-- within it; the 304-horizon pairing fails the same check.
private theorem p0d5bFixtureRunHorizon :
    p0d5bFixtureRun.horizon = 310 ∧ (List.range 311).getLast? = some 310 ∧
      ((310 : Nat) : Time) ≤ p0d5bFixtureRun.horizon ∧ ¬ ((310 : Nat) : Time) ≤
        HealingFixture.horizon :=
  ⟨rfl, by decide, by decide, by decide⟩

-- G0 (strongest proved partial): on the fixture run, with its recovery regime (proved as
-- Tests.NonVacuity.HealingRun.nvRecovery; a Tests module cannot be imported, TEST-USE),
-- the gap slot and the construction and proposal-read leaves give an actual non-genesis
-- selected proposal with its actual carrier and post-clock parent read.
private theorem p0d5bTstFixtureProposal
    (hrec : RecoverySleep₂ HealingFixture.params unitCodec HealingFixture.env
      p0d5bFixtureRun HealingFixture.gap HealingFixture.deltaF) :
    ∃ s X, HonestProposal HealingFixture.env p0d5bFixtureRun
        (fgsaInterface HealingFixture.params unitCodec) s (eraseFG X) ∧ X.slot = s ∧
      X ≠ .genesis ∧
      (∃ rows, FGCompose.HonestCarrier HealingFixture.env p0d5bFixtureRun
        (fgsaInterface HealingFixture.params unitCodec)
        (FGCompose.kernelCarrier p0d5bTstDecode NamedProposal.erase NamedProposal.rows)
        s (eraseFG X) rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧
      ∃ nd, FGCompose.proposalStateAt HealingFixture.env p0d5bFixtureRun
        (fgsaInterface HealingFixture.params unitCodec) s = some nd ∧
        FGSA.fgBlockOf nd.st (eraseFG X).parent = some X.parent := by
  have hd := HealingFixture.params.deltaPos
  obtain ⟨s, hlo, hhi, hslot⟩ := hrec.gap
    (HealingFixture.env.t_GST + 4 * HealingFixture.params.Δ) (by linarith)
    (by
      change 0 + 4 * HealingFixture.params.Δ + 4 ≤ 310
      have : HealingFixture.params.Δ = 1 := rfl
      rw [this]
      decide)
  rw [proposalTime_fgsa] at hlo hhi
  have hhor : SA.proposalTime HealingFixture.params.toParams s ≤ p0d5bFixtureRun.horizon := by
    have : HealingFixture.params.Δ = 1 := rfl
    change _ ≤ 310
    change _ ≤ 0 + 4 * HealingFixture.params.Δ + 4 at hhi
    rw [this] at hhi
    linarith
  obtain ⟨X, hnew, hXs⟩ := p0d5bTstSlot _ _ hrec s hslot hlo.le hhor
  obtain ⟨hcar, nd, hnd, hpar, _⟩ := p0d5bTstRead _ _ hrec.toRecovery₂ s X hnew hXs
  refine ⟨s, X, hnew, hXs, ?_, hcar, nd, hnd, hpar⟩
  intro hg
  have h0 := hslot.1
  rw [← hXs, hg] at h0
  exact absurd h0 (by decide)

-- G0 (fixture leaves): on the same run, the row-order and row-signer leaves come from
-- the recovery regime, and the source-transfer leaf from the run's proved TPerm
-- (Tests.NonVacuity.HealingRun.nvPerm; a premise here for the same TEST-USE reason).
private theorem p0d5bTstFixtureLeaves
    (hrec : RecoverySleep₂ HealingFixture.params unitCodec HealingFixture.env
      p0d5bFixtureRun HealingFixture.gap HealingFixture.deltaF)
    (perm : TPerm HealingFixture.params unitCodec HealingFixture.env p0d5bFixtureRun) :
    FGCompose.PromotionRowOrder (p0d5bTstCore HealingFixture.params unitCodec)
      HealingFixture.env p0d5bFixtureRun (p0d5bTstObs HealingFixture.params unitCodec)
      (fgsaInterface HealingFixture.params unitCodec) ∧
    FGCompose.PromotionRowSigner (p0d5bTstSafety HealingFixture.params unitCodec)
      HealingFixture.env p0d5bFixtureRun (p0d5bTstTiming HealingFixture.params)
      (p0d5bTstWire HealingFixture.params unitCodec) ∧
    FGCompose.PromotionSourceParent (p0d5bTstCore HealingFixture.params unitCodec)
      HealingFixture.env p0d5bFixtureRun (p0d5bTstObs HealingFixture.params unitCodec)
      (p0d5bTstTiming HealingFixture.params) (fgsaInterface HealingFixture.params unitCodec)
      (recoveryStart HealingFixture.params HealingFixture.env) :=
  ⟨p0d5bTstOrder _ _ hrec.toRecovery₂, p0d5bTstRowSigner _ _ hrec.base,
    p0d5bTstSourceParent _ _ perm⟩

#print axioms p0d5bTstLeaves
#print axioms p0d5bTstBatchFrom
#print axioms p0d5bTstFoldProduced
#print axioms p0d5bTstFixtureProposal
#print axioms p0d5bTstFixtureLeaves
#print axioms p0d5bFixtureRunHorizon
end AvailableChain.FGSA.Run
end
