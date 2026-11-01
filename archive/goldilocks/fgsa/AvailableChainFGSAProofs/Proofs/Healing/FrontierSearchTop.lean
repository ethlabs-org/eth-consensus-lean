module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchGap
public import AvailableChainFGSAProofs.Proofs.Healing.Descent
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportFrame

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop

public section

/-! Blueprint 21 HG.3 top J. The fixed entry age must come from the
accepted carrier at the actual start, including the inclusive cut. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cTopCore (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem p0d5cTopCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cTopCore p c) := by
  have h : p0d5cTopCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cTopTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cTopTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cTopTiming p) where
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

private def p0d5cTopObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cTopCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cTopObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cTopCore p c) (p0d5cTopObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cTopSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5cTopSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5cTopDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def p0d5cTopWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5cTopSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5cTopSigner
  decode_height a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl

private def p0d5cTopDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5cTopDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5cTopDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5cTopDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5cTopPayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5cTopSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5cTopSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5cTopSigner; simp
  | proposer s => delta p0d5cTopSigner; simp
  | seat label j => cases label <;> delta p0d5cTopSigner <;> simp

private def p0d5cTopWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5cTopR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5cTopWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5cTopWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section p0d5cTopD5b
variable [Fintype V]

omit [Fintype V] in
private theorem p0d5cTopParentSlot (E : Generic.Env V)
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
private theorem p0d5cTopAncestorSlot (E : Generic.Env V)
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
          (p0d5cTopParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5cTopAncestor (E : Generic.Env V)
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
    exact p0d5cTopAncestorSlot E rho hrec.base.valid i x hs hUK



end p0d5cTopD5b

-- Justified-source leaf: the frozen QC origin (Descent).
private theorem p0d5cTopJustified [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (origin : RQCOrigin p c E rho) :
    ∀ i x, x ∈ rho.honest → ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ FGCompose.HonestRowAt (p0d5cTopSafety p c) E rho (p0d5cTopTiming p) j y
        r a ∧
        actionSourceFG p c E rho y r = some (some K) ∧
        (heightView p K).T_h = ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.J := by
  intro i x hx hj
  obtain ⟨K, _, ⟨j, y, r, a, hji, ha, hK, _⟩, _, hT, _⟩ :=
    healing_justified_source (hroots := hrec.base.idealization) p c E rho
      hrec.base.valid.toScheduleWellFormed origin hx hj
  exact ⟨j, y, r, a, K, hji, ha, hK, hT⟩



private theorem frontierSearch_top_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME an accepted nonzero J has an
actual earlier honest source; its slot is at least 6Δ before the start. -/
theorem frontierSearch_initial_J_age [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (origin : RQCOrigin p c E rho)
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho (i + 1) x).fg.h_j ≠ 0) :
    SA.proposalTime p.toParams (storeAt p c E rho (i + 1) x).fg.J.slot ≤
      ev.time - 6 * p.Δ := by
  exact FGCompose.frontierSearch_initial_J_age (p0d5cTopCore p c) (p0d5cTopSafety p c)
      (p0d5cTopObs p c)
    (p0d5cTopTiming p) E rho p.E (fgCertificateLaws p) (p0d5cTopTimingLaws p)
    hrec.base.valid.toScheduleWellFormed (p0d5cTopJustified E rho hrec origin)
    (fun r x K hx hK => healing_source_slot p c E rho hx hK)
    (fun r x K A _ hK hAK => p0d5cTopAncestor E rho hrec.toRecovery₂ hK hAK) hi hx hj

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME a low proposal in this phase
has the current top J as its height entry. This is a path-plateau proof. -/
private theorem frontierSearch_top_low_entry [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF u D : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {m q : Nat} {J Qfg : FGBlock (Fin p.n)} {Q : Block}
    (hp : PhaseInterval p c E rho u D m (some J) false)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (he : eraseFG Qfg = Q)
    (huq : u ≤ SA.proposalTime p.toParams q) (hg : SA.gateTime p.toParams q ≤ D)
    (hlow : (heightView p Qfg).h = m - 1) : (heightView p Qfg).T_h = J := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _, hst, _, _, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (rho.stateBefore E j x) (SA.proposalTime p.toParams q)).st
  have hx := hQ.1.2
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 j x
    (healing_support_idxBefore_le p c E rho hs hj huq)
    (healing_phase_lt_timeIdx p c E rho hs hj (hqg.trans hg)).le hx
  have hframe := healing_phase_frame p c E rho crossing (J := some J)
    (contested := false) hx hp.2.2.1 hH hc hr
  have hne : (fullTree p st).Nonempty := by
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, hB, heB⟩ := healing_proposal_full_witness p c E rho hs hQ hst hne
  have hBQ : B = Qfg.parent := eraseFG_injective
    (heB.trans (by rw [← eraseFG_parent, he]))
  have hZ : (controls p st).Z = J := by
    change (if (controls p st).rootIsJ then st.fg.J else st.fg.F) = J
    have hr' : (controls p st).rootIsJ = true ∧ (controls p st).J = J := by
      change (KitFG.treeStoreControlsView (heightView p) st.fg).rootIsJ = true ∧
        (KitFG.treeStoreControlsView (heightView p) st.fg).J = J
      rw [hfg]
      exact hr
    rw [hr'.1]
    exact hr'.2
  have hJB : FGBlock.Preceq J B := by
    have ht := ((KitFG.mem_filteredFromView _ _ _ _).mp hB).2.2.1
    exact hZ ▸ ht
  have hPQ : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  have hJQ : FGBlock.Preceq J Qfg := KitFG.preceq_trans (hBQ ▸ hJB) hPQ
  obtain ⟨C, _, _, hjC, hJC⟩ := (storeBundle_stateBefore E rho j x).cstore.fg.pair.1
  have htop : (storeAt p c E rho j x).fg.h_j + 1 = m := hframe.2.2.2.1.2.2.2.1
  have hjC' : (heightView p C).h_j = m - 1 := by
    change (storeAt p c E rho j x).fg.h_j = (heightView p C).h_j at hjC
    simp only [Height] at *
    omega
  have hCJ : (heightView p C).J = J := hJC.symm.trans hr.2
  have hJheight : (heightView p J).h = m - 1 := by
    rw [← hCJ, (fgJustificationLaws p).J_height C]
    · exact hjC'
    · have hpos := (fgCertificateLaws p).height.one_le_h Qfg
      simp only [Height] at *
      omega
  have hJe : (heightView p J).T_h = J := by
    rw [← hCJ]
    exact (fgJustificationLaws p).J_entry C
  exact ((fgCertificateLaws p).height.entry_plateau hJQ (hJheight.trans hlow.symm)).symm.trans hJe

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME the settled root is the
accepted top carrier's J at the start. Its earlier row fixes the entry age. -/
private theorem frontierSearch_top_seed_age [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF D : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    (origin : RQCOrigin p c E rho)
    {i m : Nat} {ev : V2.Event V (Obj p)} {J : FGBlock (Fin p.n)}
    (hstart : FrontierSearchStart p c E rho i ev m .topJ)
    (hquiet : ∀ j, i < j → j < timeIdx rho D → ¬ EffectiveEvent p c E rho j)
    (hp : PhaseInterval p c E rho (ev.time + 3 * p.Δ) D m (some J) false) :
    ∀ q Q Qfg, HonestProposal E rho (fgsaInterface p c) q Q →
      eraseFG Qfg = Q → ev.time + 3 * p.Δ ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ D → (heightView p Qfg).h = m - 1 →
      SA.proposalTime p.toParams (heightView p Qfg).T_h.slot ≤ ev.time - 6 * p.Δ := by
  intro q Q Qfg hQ he huq hgate hlow
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hi, hgst, _, hfront, hm, ht, hnc⟩ :=
    (frontierSearchStart_iff p c E rho i ev m .topJ).mp hstart
  have hwin := healing_phase_window_all p c E rho mono hfront hquiet
  obtain ⟨j, N, _, hq, hem, _, _, _, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hQ
  let y := V2.D.proposerOf rho (fgsaInterface p c) q
  have hy := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hcut : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ j :=
    healing_support_idxBefore_le p c E rho hs hq (by
      change ev.time + p.Δ ≤ SA.proposalTime p.toParams q
      linarith only [huq, p.deltaPos])
  have hiCut : i + 1 ≤ V2.D.Run.idxBefore rho (ev.time + p.Δ) :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr
      (lt_add_of_pos_right _ p.deltaPos))
  have hjD : j ≤ timeIdx rho D :=
    (healing_phase_lt_timeIdx p c E rho hs hq (hqg.trans hgate)).le
  have hcutD : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ timeIdx rho D := hcut.trans hjD
  have hreceiptHor : ev.time + p.Δ ≤ rho.horizon := by
    linarith [p.deltaPos, hp.1, hp.2.1]
  have hawake := hrec.awake y hy (ev.time + p.Δ) (by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]) hreceiptHor
  have hjoin : joinedNow p (clock p (storeAt p c E rho j y)
      (SA.proposalTime p.toParams q)) = true := by
    rw [(V2.D.Run.step_tick_eq E rho hq).2] at hem
    exact ((fgsa_emits_proposal E rho _ y _ q _).mp hem).2.2.2.1
  obtain ⟨x, C, ⟨hx, hC⟩, hh, hj, hJ, hReceipt⟩ :=
    (healing_phase_witness_receipts_recovery E rho hrec
      i ev m hi hgst hm hfront hreceiptHor).top ht
  have hFcut : FGBlock.Preceq
      (storeAt p c E rho (V2.D.Run.idxBefore rho (ev.time + p.Δ)) y).fg.F C :=
    frontier_F_below_all E rho crossing hy
      ((healing_phase_local_le_frontier p c E rho hy).trans_eq
        (hwin _ hiCut hcutD).1) hx hiCut hC hh.ge
  have hservice := hReceipt.atRead j y (SA.proposalTime p.toParams q) hy hq hjoin
      (by linarith only [huq, p.deltaPos]) (by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
        exact eraseFG_preceq hFcut)
  have hCcut := healing_held_block_receipt_on p c E rho hrec.base.valid
    hrec.base.receiptIdealization C (ev.time + p.Δ) y hy
    hservice
  change C ∈ (rho.stateBeforeTime E (ev.time + p.Δ) y).st.fg.TF at hCcut
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hCcut
  have hCj := (fgsa_store_durable p c E rho hcut y).1 hCcut
  obtain ⟨hHj, htopj, hJj⟩ := healing_phase_top_node p c E rho crossing hy hCj hh hj
    (hwin j (hiCut.trans hcut) hjD).1.le
  obtain ⟨_, hc, hr⟩ := hp.2.2.2 j y
    (healing_support_idxBefore_le p c E rho hs hq huq) hjD hy
  have hJC : FGBlock.Preceq (storeAt p c E rho j y).fg.J C := by
    by_contra hn
    change (decide ((storeAt p c E rho j y).fg.h_max =
      (storeAt p c E rho j y).fg.h_j + 1) && decide (∃ W ∈ (storeAt p c E rho j y).fg.TF,
        FGBlock.Preceq (storeAt p c E rho j y).fg.F W ∧
        (heightView p W).h = (storeAt p c E rho j y).fg.h_max ∧
        ¬ FGBlock.Preceq (storeAt p c E rho j y).fg.J W)) = false at hc
    rcases Bool.and_eq_false_iff.mp hc with h | h
    · exact of_decide_eq_false h (hHj.trans htopj.symm)
    · exact of_decide_eq_false h ⟨C, hCj,
        (healing_phase_frontier_root p c E rho crossing hy hCj (hh.trans hHj.symm)).1,
        hh.trans hHj.symm, hn⟩
  have hJJ : J = (storeAt p c E rho (i + 1) x).fg.J :=
    hr.2.symm.trans ((hJj hJC).trans hJ)
  have hj0 : (storeAt p c E rho (i + 1) x).fg.h_j ≠ 0 := by
    have hm2 := (fgCertificateLaws p).height.one_le_h Qfg
    have hlocalTop := (healing_phase_top_node p c E rho crossing hx hC hh hj hfront.le).2.1
    simp only [Height] at *
    omega
  have hage := frontierSearch_initial_J_age E rho hrec origin hi hx hj0
  have heJ := frontierSearch_top_low_entry E rho hrec crossing hp hQ he huq hgate hlow
  rw [heJ, hJJ]
  exact hage

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 gap. DC: SAME finish repair in a quiet settled phase.
The entry-age input is local to this helper. The public producer must prove it
from the actual start carrier and RQCOrigin. -/
private theorem frontierSearch_top_phase [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar w u D : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {J : FGBlock (Fin p.n)} {m : Nat} (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u D m (some J) false)
    (mode : FrontierRepairStart p E G u ρbar)
    (hrepairBudget : u + ρbar ≤ D)
    (hopeningBudget : u + ρbar + P p + Γ p G + epsF p ΔF ≤ D)
    (hentryBudget : w + 2 * P p + Γ p G - 4 * p.Δ ≤ D)
    (hentryAge : ∀ q Q Qfg, HonestProposal E rho (fgsaInterface p c) q Q →
      eraseFG Qfg = Q → u ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ D → (heightView p Qfg).h = m - 1 →
      SA.proposalTime p.toParams (heightView p Qfg).T_h.slot ≤ w - 6 * p.Δ) :
    ∃ t, u ≤ t ∧ t ≤ D ∧ StrongServed p c E rho m t := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  simp only [Time, Height] at *
  have hP := frontierSearch_period_bound p
  have hΓ := (fgsa_gamma_bounds p G).1
  have hbudget0 := hrepairBudget
  obtain ⟨q, Q, hseed, hgate, hQ, hexact⟩ := frontierSearch_repair_seed E rho repair
    (healing_proposal_gap hrec) hrec.gapPos hready hp mode hbudget0
  have huq := frontierSearch_seed_after E hseed
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hgateD := hgate.trans hbudget0
  obtain ⟨iq, Qfg, hiq, hQmem, hErase⟩ := healing_rise_one_gate_copy p c E rho
    hrec.base.valid.toScheduleWellFormed hexact (hgateD.trans hp.2.1) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (hGST.trans huq) (hgateD.trans hp.2.1))
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights E rho hrec crossing hready hp huq hgateD
    hQ hErase hexact
  by_cases hhigh : (heightView p Qfg).h = m
  · exact ⟨_, huq.trans hqg, hgateD,
      frontierSearch_save_seed E rho hready hp hseed hQ hErase hhigh hexact hgateD⟩
  have hlow : (heightView p Qfg).h = m - 1 := by
    have hlo' : m - 1 ≤ (heightView p Qfg).h := by simpa using hlo
    exact Nat.le_antisymm (Nat.le_sub_one_of_lt (lt_of_le_of_ne hhi hhigh)) hlo'
  have hex : ∃ r, q ≤ r * p.R := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ p.R from (by decide : 1 ≤ 2).trans p.RLarge)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) q r hqr hfirst
  have har : p.actionTime r ≤ u + ρbar + (P p - 4 * p.Δ) := by linarith
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have heps0 := epsF_nonneg p ΔF hF
  have harD : p.actionTime r ≤ D := by linarith [hrec.gapPos, p.deltaPos]
  have hur : u ≤ p.actionTime r := by linarith
  have hpr := frontierSearch_phase_cut E rho hp hur harD
  obtain ⟨_, _, hc, _, _, hlowOr⟩ := common u m (some J) false q Q Qfg r hready hQ hErase
    hexact huq hqr hfirst hpr
  obtain ⟨l, hlq, hrepair⟩ := frontierSearch_seed_repair E rho repair (healing_proposal_gap hrec)
    hrec.gapPos
    hready hseed (m := m) (J := some J) (contested := false)
  have huvote : u ≤ SA.voteTime p.toParams (r * p.R) := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ
    change u ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrl : SA.proposalTime p.toParams l < (r : Time) * P p := by
    have ht : SA.proposalTime p.toParams q ≤ (r : Time) * P p := by
      have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
      change 4 * p.Δ * (q : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
      push_cast at hqrI
      nlinarith [p.deltaPos]
    exact hlq.trans_le ht
  have hstart : E.t_GST ≤ (r : Time) * P p := by
    have ha := actionTime_periodW p r
    have htg : SA.gateTime p.toParams q = SA.proposalTime p.toParams q + 6 * p.Δ := rfl
    linarith
  have finish {s : Slot} {X : FGBlock (Fin p.n)}
      (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
      (hlater : p.actionTime r < SA.proposalTime p.toParams s)
      (hsD : SA.gateTime p.toParams s ≤ D) (hh : m ≤ (heightView p X).h) :
      ∃ t, u ≤ t ∧ t ≤ D ∧ StrongServed p c E rho m t := by
    have hut : u ≤ SA.proposalTime p.toParams s := hur.trans hlater.le
    have hps := frontierSearch_phase_cut E rho hp
      (by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos]) hsD
    have hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s := by
      have ha := actionTime_periodW p r
      linarith [p.deltaPos]
    have hs := hrepair _ hps s _ hls le_rfl hnew
    have hheights := frontierSearch_proposal_heights E rho hrec crossing hready hp hut
      hsD hnew rfl hs
    have hh' : (heightView p X).h = m := Nat.le_antisymm hheights.2 hh
    have htq : SA.proposalTime p.toParams q < SA.proposalTime p.toParams s := by
      linarith
    exact ⟨_, by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos],
      hsD, frontierSearch_save_seed E rho hready hp (tfSeed_later p E hseed htq)
        hnew rfl hh' hs hsD⟩
  rcases hlowOr hlow with he | ⟨⟨x, K, hx, hK, hKh⟩, _⟩
  · let x := V2.D.proposerOf rho (fgsaInterface p c) q
    have hx : x ∈ rho.honest := hQ.1.2
    obtain ⟨K, nd, j, rSent, a, _, hK, _, hQK, _, _, _⟩ := hc x hx
    have hKheight := (he.choose_spec x K hx hK).1
    have hQKfg : FGBlock.Preceq Qfg K := frontierSearch_top_lift (hErase ▸ hQK)
    have hKU : (heightView p K).T_h = (heightView p Qfg).T_h :=
      ((fgCertificateLaws p).height.entry_plateau hQKfg (hlow.trans hKheight.symm)).symm
    let U := (heightView p Qfg).T_h
    have hage : SA.proposalTime p.toParams U.slot ≤ w - 6 * p.Δ :=
      hentryAge q Q Qfg hQ hErase huq hgateD hlow
    have hgateBudget : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
        (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ D := by
      apply max_le
      · linarith
      · linarith
    have hwindow : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
        (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon := by
      have ha := actionTime_periodW p r
      have heps := betaF_le_period p ΔF hbound
      apply le_trans _ hp.2.1
      rw [← max_add_add_right]
      apply max_le
      · have hg := (le_max_left _ _).trans hgateBudget
        rw [epsF_def] at hg
        linarith [p.deltaPos]
      · linarith [p.deltaPos]
    obtain ⟨s, X, hnew, _, hlater, hsD, hh⟩ := frontierSearch_age_service E rho hrec
      hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum he hc
      ⟨x, K, hx, hK, hKU⟩ hready hstart huvote hp hwindow hgateBudget
    apply finish hnew hlater hsD
    simpa only [Nat.sub_add_cancel hp.2.2.1] using hh
  · let b := (r : Time) * P p + 4 * p.Δ
    have hbGST : E.t_GST ≤ b := by dsimp only [b]; linarith [p.deltaPos]
    have hbhor : b + G ≤ rho.horizon := by
      apply le_trans _ hp.2.1
      dsimp only [b]
      have ha := actionTime_periodW p r
      linarith [p.deltaPos]
    obtain ⟨s, hloS, hhiS, hslotS⟩ := hrec.gap b hbGST hbhor
    rw [proposalTime_fgsa] at hloS hhiS
    have hsD : SA.gateTime p.toParams s ≤ D := by
      have ha := actionTime_periodW p r
      change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D
      dsimp only [b] at hhiS
      linarith
    have hsHor : SA.proposalTime p.toParams s ≤ rho.horizon := by
      change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hsD
      linarith [p.deltaPos, hp.2.1]
    have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
      have hlo := hloS
      dsimp only [b] at hlo
      change (r : Time) * P p + 4 * p.Δ < 4 * p.Δ * (s : Int) at hlo
      change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
      nlinarith [p.deltaPos]
    have hjoin := healing_recovery_restart_cutoff hrec hslotS.2 hsHor hcut
    obtain ⟨X, hnew, hXs, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂ hslotS
      (hbGST.trans hloS.le) hsHor hjoin
    have hslabel : r * p.R + 2 ≤ s := by
      dsimp only [b] at hloS
      change (r : Time) * (4 * (p.R : Time) * p.Δ) + 4 * p.Δ <
        4 * p.Δ * (s : Time) at hloS
      have hz : ((r * p.R : Nat) : Time) + 1 < s := by push_cast; nlinarith [p.deltaPos]
      exact_mod_cast Int.add_one_le_iff.mpr hz
    have hat : p.actionTime r < SA.proposalTime p.toParams s := by
      have ha := actionTime_periodW p r
      have hz : ((r * p.R + 2 : Nat) : Time) ≤ s := by exact_mod_cast hslabel
      change 4 * p.Δ * (s : Time) > _
      push_cast at hz
      change p.actionTime r = (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ at ha
      have hm := mul_le_mul_of_nonneg_left hz
        (show 0 ≤ 4 * p.Δ by linarith only [p.deltaPos])
      nlinarith only [hm, ha, p.deltaPos]
    have hpts := frontierSearch_phase_cut E rho hp (hur.trans hat.le)
      (by change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hsD
          linarith only [hsD, p.deltaPos])
    have hparent := healing_promotion_source_parent E rho perm hready hpts huvote hat.le
      hx hK hslabel hnew
    have hpath : FGBlock.Preceq K X.parent := frontierSearch_top_lift
      ((eraseFG_parent X) ▸ hparent)
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact KitFG.preceq_refl _
      | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
    have hh : m ≤ (heightView p X).h := by
      have hKP := (fgCertificateLaws p).height.h_mono hpath
      have hPXh := (fgCertificateLaws p).height.h_mono hPX
      exact (hKh ▸ hKP).trans hPXh
    exact finish hnew hat hsD hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J; run 2 R2-b.
DC: SAME keep both E_jF branches. The actual accepted J supplies its age;
no ExactService-to-seed reconstruction or E_jF collapse is used. -/
theorem frontier_hg3_topJ [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) (monoAll : RMonoAll p
      c E rho)
    (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .topJ)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_jF p ΔF G ρbar ≤ rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time (ev.time + E_jF p ΔF G ρbar) := by
  apply (frontierHG3Result_iff p c E rho i m ev.time _).mpr
  have hsched := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (frontierSearchStart_iff p c E rho i ev m .topJ).mp hstart
  have hρ : 0 ≤ ρbar := by
    have hG := (fgsa_gamma_bounds p G).1
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    cases mode with
    | two =>
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
    | one =>
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
  have hP := frontierSearch_period_bound p
  have hG : 4 * p.Δ ≤ Γ p G := hrec.gapPos.trans (fgsa_gamma_bounds p G).1
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have heps := epsF_nonneg p ΔF hF
  have hleft : ev.time + 3 * p.Δ + ρbar + P p + Γ p G + epsF p ΔF ≤
      ev.time + E_jF p ΔF G ρbar := by
    change _ ≤ ev.time + max _ _
    have hb := le_max_left (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF)
      (2 * P p + Γ p G - 4 * p.Δ)
    linarith only [hb]
  have hright : ev.time + 2 * P p + Γ p G - 4 * p.Δ ≤
      ev.time + E_jF p ΔF G ρbar := by
    change _ ≤ ev.time + max _ _
    have hb := le_max_right (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF)
      (2 * P p + Γ p G - 4 * p.Δ)
    linarith only [hb]
  have hrepair : ev.time + 3 * p.Δ + ρbar ≤ ev.time + E_jF p ΔF G ρbar := by
    have hnonneg : 0 ≤ P p + Γ p G + epsF p ΔF := by
      linarith only [hP, hG, heps, p.deltaPos]
    calc
      _ ≤ ev.time + 3 * p.Δ + ρbar + (P p + Γ p G + epsF p ΔF) :=
        le_add_of_nonneg_right hnonneg
      _ ≤ _ := by convert hleft using 1; ring
  rcases frontierSearch_first_effective_split p c E rho hsched i
      (ev.time + E_jF p ΔF G ρbar) with hstop | hquiet
  · rcases frontierSearch_classify_stop p c E rho monoAll hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hsettle : ev.time + 3 * p.Δ ≤ ev.time + E_jF p ΔF G ρbar :=
    (le_add_of_nonneg_right hρ).trans hrepair
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (hroots := hrec.base.receiptIdealization)
    p c E rho crossing hrec.base.valid monoAll hrec
    (fun _ ht => healing_ready_read_cutoff E ht)
    (healing_phase_witness_receipts_recovery E rho hrec) i ev _ m .topJ hi hgst0
    hsettle hhor hm hfront hkind hquiet
  have hgst : recoveryStart p E ≤ ev.time + 3 * p.Δ := by linarith [p.deltaPos]
  have hage := frontierSearch_top_seed_age E rho hrec crossing monoAll origin
    hstart hquiet hp
  obtain ⟨t, hut, htD, hs⟩ := frontierSearch_top_phase E rho hrec crossing repair common
    hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum hgst hp mode
    hrepair hleft hright hage
  exact Or.inr (Or.inr ⟨t, by linarith [p.deltaPos], htD, hs⟩)

end AvailableChain.FGSA.Run
end
