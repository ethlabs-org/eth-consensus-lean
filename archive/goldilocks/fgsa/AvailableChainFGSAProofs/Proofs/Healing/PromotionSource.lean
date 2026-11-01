module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows -- shake: keep (row source)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt -- shake: keep (row time)
public import AvailableChainFGCompose.Proofs.Healing.PromotionSource
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5bSrcCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bSrcTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5bSrcTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5bSrcTiming p) where
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

private def p0d5bSrcObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5bSrcCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5bSrcSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5bSrcSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5bSrcDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def p0d5bSrcWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5bSrcSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5bSrcSigner
  decode_height a u ha := by
    delta p0d5bSrcSafety at ha
    rw [p0d5bSrcDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5bSrcSafety at ha
    rw [p0d5bSrcDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5bSrcSafety at ha
    rw [p0d5bSrcDecodeRow ha]
    rfl

private def p0d5bSrcDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5bSrcDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5bSrcDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5bSrcDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5bSrcPayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5bSrcSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5bSrcSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5bSrcSigner; simp
  | proposer s => delta p0d5bSrcSigner; simp
  | seat label j => cases label <;> delta p0d5bSrcSigner <;> simp

private def p0d5bSrcWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5bSrcR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5bSrcWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5bSrcWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

omit [Fintype V] in
private abbrev p0d5bSrcBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5bSrcCore p c) (p0d5bSrcSafety p c) (p0d5bSrcObs p c)
    (p0d5bSrcTiming p) E rho (fgsaInterface p c) (p0d5bSrcWire p c) p.E
    p0d5bSrcDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5bSrcCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bSrcDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5bSrcPayload o s N ((p0d5bSrcDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5bSrcBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5bSrcBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5bSrcCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5bSrcSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5bSrcFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5bSrcFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5bSrcSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5bSrcSafety p c
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
private theorem p0d5bSrcRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5bSrcCore p c) (p0d5bSrcSafety p c) E rho
      (p0d5bSrcObs p c) (fgsaInterface p c) p0d5bSrcDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5bSrcWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5bSrcDecode NamedProposal.erase NamedProposal.rows) s
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
  have hdec : p0d5bSrcDecode o = some (s, N) :=
    (p0d5bSrcDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5bSrcR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5bSrcSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5bSrcOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5bSrcCore p c) E rho (p0d5bSrcObs p c) (fgsaInterface p c) := by
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
private theorem p0d5bSrcRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5bSrcSafety p c) E rho (p0d5bSrcTiming p)
      (p0d5bSrcWire p c) := by
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
    exact (p0d5bSrcSigner_iff a i).mpr hauth

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME fixed opening rows, saved entry, and parent path at the proposal read.
The time fields are local grid and horizon facts. No phase is stored here. -/
structure PromotionSourceAt (p : Params) (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (r height : Nat)
    (U : FGBlock (Fin p.n)) (s : Slot) (X : FGBlock (Fin p.n)) : Prop where
  entry : EntryAt p U height
  parentPath : FGBlock.Preceq U X.parent
  proposal : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)
  slot : X.slot = s
  sync : E.t_GST ≤ p.actionTime r
  carrier : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s
  age : SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s
  horizon : SA.proposalTime p.toParams s ≤ rho.horizon
  rows : ∀ x ∈ rho.honest, ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
    NamesEntry p .progress a height U

/-- ROOT-DIGEST W2b. Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME progress uses the fixed rows and source path at the proposal read.
The core has no phase, permanence, repair, or service endpoint premise. -/
theorem promotion_age_advance_of_source (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {U X : FGBlock (Fin p.n)} {s : Slot}
    (src : PromotionSourceAt p c E rho ΔF r height U s X)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho)) :
    height + 1 ≤ (heightView p X).h := by
  exact FGCompose.promotion_age_advance_of_source (p0d5bSrcCore p c) (p0d5bSrcSafety p c)
    (p0d5bSrcObs p c) (p0d5bSrcTiming p) E rho (fgsaInterface p c) (p0d5bSrcWire p c) p.E
    p0d5bSrcDecode NamedProposal.erase NamedProposal.rows (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5bSrcWindow (parentFoldState p s H)) (fgCertificateLaws p).height
    (p0d5bSrcTimingLaws p) hrec.base.valid.toScheduleWellFormed
    (p0d5bSrcFault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    ⟨src.entry, src.parentPath, src.proposal, src.slot, src.sync, src.carrier, src.age,
      src.horizon, src.rows⟩ hδ ⟨hbound.1⟩ rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5bSrcBatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5bSrcFoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    (p0d5bSrcRead E rho hrec) (p0d5bSrcOrder E rho hrec) (p0d5bSrcRowSigner E rho hrec.base)


end AvailableChain.FGSA.Run
end
