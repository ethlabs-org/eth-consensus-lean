module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionSource -- shake: keep (leaf producers)
public import AvailableChainFGCompose.Proofs.Healing.PromotionAge

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5bAgeCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bAgeTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5bAgeTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5bAgeTiming p) where
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

private def p0d5bAgeObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5bAgeCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5bAgeSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bAgeSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5bAgeDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def p0d5bAgeWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5bAgeSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5bAgeSigner
  decode_height a u ha := by
    delta p0d5bAgeSafety at ha
    rw [p0d5bAgeDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5bAgeSafety at ha
    rw [p0d5bAgeDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5bAgeSafety at ha
    rw [p0d5bAgeDecodeRow ha]
    rfl

private def p0d5bAgeDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5bAgeDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5bAgeDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5bAgeDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5bAgePayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5bAgeSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5bAgeSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5bAgeSigner; simp
  | proposer s => delta p0d5bAgeSigner; simp
  | seat label j => cases label <;> delta p0d5bAgeSigner <;> simp

private def p0d5bAgeWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5bAgeR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5bAgeWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5bAgeWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

omit [Fintype V] in
private abbrev p0d5bAgeBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5bAgeCore p c) (p0d5bAgeSafety p c) (p0d5bAgeObs p c)
    (p0d5bAgeTiming p) E rho (fgsaInterface p c) (p0d5bAgeWire p c) p.E
    p0d5bAgeDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5bAgeCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bAgeDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5bAgePayload o s N ((p0d5bAgeDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5bAgeBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5bAgeBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5bAgeCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5bAgeSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5bAgeFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5bAgeFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5bAgeSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5bAgeSafety p c
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
private theorem p0d5bAgeRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5bAgeCore p c) (p0d5bAgeSafety p c) E rho
      (p0d5bAgeObs p c) (fgsaInterface p c) p0d5bAgeDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5bAgeWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bAgeDecode NamedProposal.erase NamedProposal.rows) s
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
  have hdec : p0d5bAgeDecode o = some (s, N) :=
    (p0d5bAgeDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5bAgeR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5bAgeSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5bAgeOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5bAgeCore p c) E rho (p0d5bAgeObs p c) (fgsaInterface p c) := by
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
private theorem p0d5bAgeRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5bAgeSafety p c) E rho (p0d5bAgeTiming p)
      (p0d5bAgeWire p c) := by
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
    exact (p0d5bAgeSigner_iff a i).mpr hauth

omit [Fintype V] in
private theorem p0d5bAgePhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5bAgeCore p c) E rho (p0d5bAgeObs p c) u v m J
      contested ↔ PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5bAgeSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5bAgeCore p c) E rho (p0d5bAgeTiming p)
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
private theorem p0d5bAgeSourceParent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (perm : TPerm p c E rho) :
    FGCompose.PromotionSourceParent (p0d5bAgeCore p c) E rho (p0d5bAgeObs p c) (p0d5bAgeTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested r s X x K hready hphase hu hgate hs hnew hx hK
  have hp := healing_promotion_source_parent E rho perm hready
    ((p0d5bAgePhase_iff E rho).mp hphase) hu hgate hx hK hs hnew
  change Block.Preceq (eraseFG K) (eraseFG X).parent at hp
  rw [eraseFG_parent] at hp
  exact eraseFG_preceq_iff.mp hp

-- Receipt leaf, phase form: healing_promotion_first_receipt with its receiver service.
private theorem p0d5bAgeReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
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
    FGCompose.PromotionPhaseReceipt (p0d5bAgeCore p c) E rho (p0d5bAgeObs p c) (p0d5bAgeTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested s X hready hnew hut hpD
  exact healing_promotion_first_receipt E rho hrec crossing (services s) hnew hut hready
    ((p0d5bAgePhase_iff E rho).mp hpD)

omit [Fintype V] in
private theorem p0d5bAgeCovered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5bAgeCore p c) (p0d5bAgeSafety p c) E rho
      (heightView p) (p0d5bAgeTiming p) (p0d5bAgeWire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

private theorem p0d5bAgeNonempty (E : Generic.Env V)
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
private theorem p0d5bAgeParentSlot (E : Generic.Env V)
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
private theorem p0d5bAgeAncestorSlot (E : Generic.Env V)
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
          (p0d5bAgeParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5bAgeAncestor (E : Generic.Env V)
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
    exact p0d5bAgeAncestorSlot E rho hrec.base.valid i x hs hUK

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME the strict age trigger gives the carrier and maturity grid bounds. -/
theorem promotion_age_grid (r s : Nat) (U : FGBlock (Fin p.n)) (ΔF : Time)
    (hlo : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) <
      SA.proposalTime p.toParams s) :
    carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s ∧
    SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s := by
  exact FGCompose.promotion_age_grid (p0d5bAgeTiming p) (p0d5bAgeTimingLaws p) r s U ΔF hlo

/-- Blueprint 21:1592–1638; S5 H1, receipt half of persistent-phase HG.2.
DC: SAME the receipt half ends at t_X+Δ and uses the terminal budget.
The repair label and repair continuation belong only to the service tail. -/
theorem healing_promotion_age_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (crossing : RXing p c E rho) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R)) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ v, PhaseInterval p c E rho u v m J contested →
        max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon →
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ v →
        let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
        ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          U_F < SA.proposalTime p.toParams s ∧ SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
          SA.proposalTime p.toParams s + p.Δ ≤
            max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
              (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) := by
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨U, hU, hUslot, h⟩ := FGCompose.healing_promotion_age_receipt (p0d5bAgeCore p c)
    (p0d5bAgeSafety p c) (p0d5bAgeObs p c) (p0d5bAgeTiming p) E rho (fgsaInterface p c)
    (p0d5bAgeWire p c) p.E p0d5bAgeDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5bAgeWindow (parentFoldState p s H)) (fgCertificateLaws p).height
    (p0d5bAgeTimingLaws p) hrec.base.valid.toScheduleWellFormed
    (p0d5bAgeFault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) hJst
    (p0d5bAgeNonempty E rho hrec.toRecovery₂) (p0d5bAgeSlot E rho hrec)
    (p0d5bAgeRead E rho hrec.toRecovery₂) (p0d5bAgeOrder E rho hrec.toRecovery₂)
    (p0d5bAgeRowSigner E rho hrec.base) (p0d5bAgeSourceParent E rho perm)
    (p0d5bAgeReceipt E rho hrec.toRecovery₂ crossing services) hδ ⟨hbound.1⟩ rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5bAgeBatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5bAgeFoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    (m := m) (J := J) (contested := contested) hentry (p0d5bAgeCovered E rho hcovered)
    (fun x y K L hx hy hK hL he => rootScope_eq hrec.base.idealization
      (rootScope_entry (rootScope_source hx hK)) (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d5bAgeAncestor E rho hrec.toRecovery₂ hK hAK)
    hready hstart hu
  refine ⟨U, hU, hUslot, ?_⟩
  intro v hp hwin hbudget
  exact h v ((p0d5bAgePhase_iff E rho).mpr hp) hwin hbudget

/-- Blueprint 21:1592–1638; S5 H1, service tail of persistent-phase HG.2.
DC: SAME service alone uses repair continuation and the phase through the gate.
The gate budget is the original HG.2b_F maximum. -/
theorem healing_promotion_age_service_tail (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {u : Time} {m r : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {l s : Slot} {U X : FGBlock (Fin p.n)}
    (hl : SA.proposalTime p.toParams l < (r : Time) * P p)
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hlo : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) <
      SA.proposalTime p.toParams s)
    (hhi : SA.proposalTime p.toParams s ≤
      max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
        (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + Γ p G)
    (hpgate : PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested) :
    ExactService p c E rho s (eraseFG X) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s := by
    have ht := lt_of_le_of_lt (le_max_left _ _) hlo
    rw [betaF_def] at ht
    nlinarith [p.deltaPos]
  refine ⟨healing_promotion_continuing_service E rho hrepair hls hnew hpgate, ?_⟩
  exact (FGCompose.healing_promotion_age_service_tail (p0d5bAgeCore p c) (p0d5bAgeObs p c)
    (p0d5bAgeTiming p) E rho (fgsaInterface p c) (p0d5bAgeTimingLaws p) (G := G)
    hrec.deltaF hrec.base.delta hl
    (fun v hv s Q hls hg hQ => (hrepair v ((p0d5bAgePhase_iff E rho).mp hv) s Q hls hg hQ).1)
    hnew hlo hhi ((p0d5bAgePhase_iff E rho).mpr hpgate)).2

/-- Blueprint 21:1592–1638; r3 A5, persistent-phase HG.2.
DC: SAME the age trigger uses q = U.slot for the actual fixed starting entry.
The full G window and a phase through the gate budget are explicit local
premises. First receipt remains strict and block delay remains Δ. -/
theorem healing_promotion_age_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (crossing : RXing p c E rho) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {l : Slot} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hl : SA.proposalTime p.toParams l < (r : Time) * P p)
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ v, PhaseInterval p c E rho u v m J contested →
        max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon →
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ v →
        let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
        ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          U_F < SA.proposalTime p.toParams s ∧ SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
          SA.proposalTime p.toParams s + p.Δ ≤
            max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
              (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ∧
          (PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
            ExactService p c E rho s (eraseFG X) ∧
            SA.gateTime p.toParams s ≤
              max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
                (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ)) := by
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨U, hU, hUslot, h⟩ := FGCompose.healing_promotion_age_service (p0d5bAgeCore p c)
    (p0d5bAgeSafety p c) (p0d5bAgeObs p c) (p0d5bAgeTiming p) E rho (fgsaInterface p c)
    (p0d5bAgeWire p c) p.E p0d5bAgeDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5bAgeWindow (parentFoldState p s H)) (fgCertificateLaws p).height
    (p0d5bAgeTimingLaws p) hrec.base.valid.toScheduleWellFormed
    (p0d5bAgeFault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) hJst
    (p0d5bAgeNonempty E rho hrec.toRecovery₂) (p0d5bAgeSlot E rho hrec)
    (p0d5bAgeRead E rho hrec.toRecovery₂) (p0d5bAgeOrder E rho hrec.toRecovery₂)
    (p0d5bAgeRowSigner E rho hrec.base) (p0d5bAgeSourceParent E rho perm)
    (p0d5bAgeReceipt E rho hrec.toRecovery₂ crossing services) hδ ⟨hbound.1⟩ rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5bAgeBatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5bAgeFoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    (m := m) (J := J) (contested := contested) hentry (p0d5bAgeCovered E rho hcovered)
    (fun x y K L hx hy hK hL he => rootScope_eq hrec.base.idealization
      (rootScope_entry (rootScope_source hx hK)) (rootScope_entry (rootScope_source hy hL)) he)
    (fun x K hx hK => healing_source_slot p c E rho hx hK)
    (fun x K A _ hK hAK => p0d5bAgeAncestor E rho hrec.toRecovery₂ hK hAK)
    hready hstart hu hl
    (fun v hv s Q hls hg hQ => (hrepair v ((p0d5bAgePhase_iff E rho).mp hv) s Q hls hg hQ).1)
  refine ⟨U, hU, hUslot, ?_⟩
  intro v hp hwin hbudget
  obtain ⟨s, X, hnew, hslot, hlo, hhi, hh, hr, ht, _⟩ :=
    h v ((p0d5bAgePhase_iff E rho).mpr hp) hwin hbudget
  exact ⟨s, X, hnew, hslot, hlo, hhi, hh, hr, ht, fun hpgate =>
    healing_promotion_age_service_tail E rho hrec.toRecovery₂ hl hrepair hnew hlo hhi hpgate⟩

end AvailableChain.FGSA.Run
end
