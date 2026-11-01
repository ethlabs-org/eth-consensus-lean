module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAge -- shake: keep (receipt producers)
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchHG2a

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! Blueprint 21 HG.2a_F:1592--1640 and HG.4:1695--1720; HG4-RISE F1.
The result contract stops at a rise. Same-frontier events do not stop it.
The gap adapter reuses the existing slot producer. S5 H2 proves the
height and strict receipt fields from the saved rows and frontier cap.
HG.1 source preservation: `frontier_service` (FrontierService:307).
No fixed phase after the saved gate is assumed by the result contract. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5bHg2Core (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bHg2Timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5bHg2TimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5bHg2Timing p) where
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

private def p0d5bHg2Obs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5bHg2Core p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5bHg2Safety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bHg2Signer {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5bHg2DecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def p0d5bHg2Wire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5bHg2Safety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5bHg2Signer
  decode_height a u ha := by
    delta p0d5bHg2Safety at ha
    rw [p0d5bHg2DecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5bHg2Safety at ha
    rw [p0d5bHg2DecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5bHg2Safety at ha
    rw [p0d5bHg2DecodeRow ha]
    rfl

private def p0d5bHg2Decode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5bHg2Decode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5bHg2Decode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5bHg2Decode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5bHg2Payload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5bHg2Signer_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5bHg2Signer a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5bHg2Signer; simp
  | proposer s => delta p0d5bHg2Signer; simp
  | seat label j => cases label <;> delta p0d5bHg2Signer <;> simp

private def p0d5bHg2Window {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5bHg2R6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5bHg2Window w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5bHg2Window
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section p0d5bHg2Bridge
variable [Fintype V]

omit [Fintype V] in
private abbrev p0d5bHg2Batch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5bHg2Core p c) (p0d5bHg2Safety p c) (p0d5bHg2Obs p c)
    (p0d5bHg2Timing p) E rho (fgsaInterface p c) (p0d5bHg2Wire p c) p.E
    p0d5bHg2Decode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5bHg2CarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bHg2Decode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5bHg2Payload o s N ((p0d5bHg2Decode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5bHg2BatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5bHg2Batch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5bHg2CarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5bHg2Signer_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5bHg2FoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5bHg2Fault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5bHg2Safety p c) rho) < p.E.q := by
  classical
  let S := p0d5bHg2Safety p c
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
private theorem p0d5bHg2Read (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5bHg2Core p c) (p0d5bHg2Safety p c) E rho
      (p0d5bHg2Obs p c) (fgsaInterface p c) p0d5bHg2Decode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5bHg2Window (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bHg2Decode NamedProposal.erase NamedProposal.rows) s
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
  have hdec : p0d5bHg2Decode o = some (s, N) :=
    (p0d5bHg2Decode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5bHg2R6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5bHg2Safety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5bHg2Order (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5bHg2Core p c) E rho (p0d5bHg2Obs p c) (fgsaInterface p c) := by
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
private theorem p0d5bHg2RowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5bHg2Safety p c) E rho (p0d5bHg2Timing p)
      (p0d5bHg2Wire p c) := by
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
    exact (p0d5bHg2Signer_iff a i).mpr hauth

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5bHg2Slot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5bHg2Core p c) E rho (p0d5bHg2Timing p)
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
private theorem p0d5bHg2Covered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5bHg2Core p c) (p0d5bHg2Safety p c) E rho
      (heightView p) (p0d5bHg2Timing p) (p0d5bHg2Wire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d5bHg2ParentSlot (E : Generic.Env V)
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
private theorem p0d5bHg2AncestorSlot (E : Generic.Env V)
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
          (p0d5bHg2ParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5bHg2Ancestor (E : Generic.Env V)
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
    exact p0d5bHg2AncestorSlot E rho hrec.base.valid i x hs hUK

-- Receipt leaf, cap form: healing_promotion_first_receipt_of_frontierCap with the
-- existing self-proposal receiver service.
private theorem p0d5bHg2CapReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.PromotionCapReceipt (p0d5bHg2Core p c) E rho (p0d5bHg2Obs p c) (p0d5bHg2Timing p)
      (fgsaInterface p c) := by
  intro m s Qfg X hnew hgst hQX hcap hQm hhor
  exact healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂ crossing
    (healing_self_proposal_service hrec s) hnew hgst hQX hcap hQm hhor

end p0d5bHg2Bridge

/-- Blueprint 21:1592--1640; HG4-RISE F1.
DC: SAME the saved entry's terminal result: a first rise or a strict honest
high receipt. The producer is frontier_hg2a_receipt. -/
def FrontierHG2aResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin p.n)) : Prop :=
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  FrontierRiseBy p c E rho i m D ∨
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      m + 1 ≤ (heightView p X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) D y

/-- Blueprint 21:1592–1640; S5 F2.
DC: SAME expose the capped receipt result for the frozen rise tail. -/
theorem frontierHG2aResult_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin p.n)) :
    FrontierHG2aResult E rho G ΔF i m r U ↔
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  FrontierRiseBy p c E rho i m D ∨
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      m + 1 ≤ (heightView p X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) D y := Iff.rfl


omit [DecidableEq V] in
/-- Blueprint 21:1695--1720; HG4-RISE F1/F2.
DC: SAME the capped entry and first-opening bounds fit the fixed HG.4 guard.
The epsF bound follows from the frozen LivenessBoundW field. -/
theorem frontierSearch_hg2a_bound (p : Params) (G ΔF d a tU : Time)
    (hbound : LivenessBoundW p ΔF) (ha : a ≤ d + P p - 4 * p.Δ)
    (hU : tU ≤ d - 6 * p.Δ) :
    max (a + Γ p G - p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G - 3 * p.Δ) ≤ d + (2 * P p + Γ p G - 9 * p.Δ) := by
  exact FGCompose.frontierSearch_hg2a_bound (p0d5bHg2Timing p) (p0d5bHg2TimingLaws p)
    G ΔF d a tU ⟨hbound.1⟩ ha hU

omit [DecidableEq V] in
/-- Blueprint 21:1592--1640; HG4-RISE F1 STOP evidence.
DC: SAME the existing service budget is 5Δ after the terminal budget.
This identity does not give a larger horizon to the terminal task. -/
theorem frontierSearch_hg2a_gate_cost (p : Params) (G ΔF a tU : Time) :
    max (a + Γ p G + 4 * p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G + 2 * p.Δ) =
    max (a + Γ p G - p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G - 3 * p.Δ) + 5 * p.Δ := by
  exact FGCompose.frontierSearch_hg2a_gate_cost (p0d5bHg2Timing p) G ΔF a tU

/-- Blueprint 21:1592--1640; HG4-RISE F1, slot component only.
DC: SAME reuse healing_promotion_age_gap (PromotionArithmetic:257).
GUP r2: the rounded bound supplies the full G window from the terminal guard.
This produces an honest slot; it does not assert promotion or receipt. -/
theorem frontierSearch_hg2a_gap [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (r : Nat) (U : FGBlock (Fin p.n)) (hgst : E.t_GST ≤ (r : Time) * P p)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.proposalTime p.toParams s + p.Δ ≤
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) := by
  exact FGCompose.frontierSearch_hg2a_gap (p0d5bHg2Timing p) E rho (fgsaInterface p c)
    (p0d5bHg2TimingLaws p) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) r U hgst hhor

/-- ROOT-DIGEST W2b. Blueprint 21:1592–1640; S5 H2, route steps 1–8.
DC: SAME the saved seed supplies source transfer only through the proposal read.
The strict cap supplies receipt compatibility through t_X+Δ.
The seed binders are the frozen StrongServed fields; r is an opening after q. -/
theorem frontier_hg2a_receipt [Fintype V] (E : Generic.Env V)
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
    {u : Time} {i m r q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg U : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hQm : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqr : q ≤ r * p.R) (hU : U = (heightView p Qfg).T_h)
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ rho.horizon) :
    FrontierHG2aResult E rho G ΔF i m r U := by
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have h := FGCompose.frontier_hg2a_receipt (p0d5bHg2Core p c)
    (p0d5bHg2Safety p c) (p0d5bHg2Obs p c) (p0d5bHg2Timing p) E rho (fgsaInterface p c)
    (p0d5bHg2Wire p c) p.E p0d5bHg2Decode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5bHg2Window (parentFoldState p s H)) (fgCertificateLaws p).height
    (p0d5bHg2TimingLaws p) hrec.base.valid.toScheduleWellFormed
    (p0d5bHg2Fault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) hJst ⟨mono⟩
    (fun i j hij x B hB => (fgsa_store_durable p c E rho hij x).1 hB)
    (fun X => eraseFG_parent X) (fun A B h => eraseFG_preceq_iff.mp h)
    (p0d5bHg2Slot E rho hrec) (p0d5bHg2Read E rho hrec.toRecovery₂)
    (p0d5bHg2Order E rho hrec.toRecovery₂) (p0d5bHg2RowSigner E rho hrec.base)
    (p0d5bHg2CapReceipt E rho hrec crossing) hδ ⟨hbound.1⟩ rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5bHg2BatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5bHg2FoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    hready hQ he hQm hu hqr hU
    (fun t hg hth hcap => by
      obtain ⟨htransfer, hrepair, hopen⟩ := frontier u t m J contested q Q Qfg hready hQ he
        hQm hexact ((frontierSeedQualification_iff p E u q).mp hseed) hu hp hg hth hcap
      refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
      · intro s B hqs hgate hprop
        exact (hrepair s B hqs hgate hprop).1
      · intro r' hqr' hrt
        obtain ⟨hcov, hent, hheight, htime⟩ := hopen r' hqr' hrt
        exact ⟨p0d5bHg2Covered E rho hcov, hent, hheight, htime⟩)
    (fun x y K L hx hy hK hL he => rootScope_eq hrec.base.idealization
      (rootScope_entry (rootScope_source hx hK)) (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d5bHg2Ancestor E rho hrec.toRecovery₂ hK hAK)
    hstart hhor
  obtain hrise | hhigh := (FGCompose.FrontierHG2aResult_def (p0d5bHg2Core p c) E rho
    (p0d5bHg2Obs p c) (p0d5bHg2Timing p) (fgsaInterface p c) G ΔF i m r U).mp h
  · exact Or.inl ((frontierRiseBy_iff p c E rho i m _).mpr hrise)
  · exact Or.inr hhigh

end AvailableChain.FGSA.Run
end
