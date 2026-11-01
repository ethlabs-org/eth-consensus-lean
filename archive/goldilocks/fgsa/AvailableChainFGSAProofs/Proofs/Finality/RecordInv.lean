module
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSARun.Proofs.ClientTrace
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSA.Proofs.EmissionFields
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGCompose.Proofs.Finality.RecordInv
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d7f_observations (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def d7f_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7f_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7f_timing p) where
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

private def d7f_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7f_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7f_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private def d7f_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7f_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def p c] at ha
    rw [d7f_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def p c] at ha
    rw [d7f_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def p c] at ha
    rw [d7f_decode p ha]
    rfl

private def d7f_stored_carrier (p : Params) (nd : Node p) (B : FGBlock (Fin p.n))
    (wire : RowWire p.n) : Prop :=
  ∃ s N, N.erase = eraseFG B ∧
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧ wire ∈ N.rows

private def d7f_source_service (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (y : V) (r : Nat) (C : FGBlock (Fin p.n)) : Prop :=
  ∃ G, gateResult p c E rho y (r * p.R) = some (some G) ∧
    Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)

private theorem d7f_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7f_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def p c]; rfl

private theorem d7f_postClock_eq (x : V) (t : Time) :
    FGCompose.postClock E rho x t = postClock E rho x t :=
  (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1.symm

private theorem d7f_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7f_timing p) x r =
      actionSourceFG p c E rho x r := by rw [fgsaCoreReads_def p c]; rfl

private theorem d7f_entry_eq (a : NamedHeightPair) : FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem d7f_chain (w : HealingWitness) (h : THigh p c E rho w) (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (d7f_observations p c)
      (d7f_timing p) E rho (d7f_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [fgsaCoreReads_def p c] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem d7f_reflect (A B : FGBlock (Fin p.n))
    (h : Block.Preceq ((fgsaCoreReads p c).erase A) ((fgsaCoreReads p c).erase B)) :
    FGBlock.Preceq A B := by
  rw [fgsaCoreReads_def p c] at h
  exact eraseFG_preceq_iff.mp h

private theorem d7f_fg (nd : (fgsa p c).State) : ((fgsaCoreReads p c).core nd).fg = nd.st.fg := by
  rw [fgsaCoreReads_def p c]

private theorem d7f_erase (C : FGBlock (Fin p.n)) :
    (fgsaCoreReads p c).erase C = eraseFG C := by
  rw [fgsaCoreReads_def p c]

private theorem d7f_qc (h : RQCOrigin p c E rho) :
    FGCompose.RQCOrigin (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7f_observations p c) (d7f_timing p) (d7f_stored_carrier p)
      (d7f_source_service p c E rho) p.E := by
  have heq : FGCompose.RQCOrigin (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7f_observations p c) (d7f_timing p) (d7f_stored_carrier p)
      (d7f_source_service p c E rho) p.E = RQCOrigin p c E rho := by
    dsimp only [FGCompose.RQCOrigin, RQCOrigin, d7f_stored_carrier, d7f_source_service]
    simp only [d7f_fg, d7f_source_eq, fgsaSafetyReads_def p c, exists_and_left]
    rfl
  exact heq.symm ▸ h


private theorem d7f_head :
    FGCompose.HighRecordHead (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7f_observations p c) E rho := by
  intro i x t _hx
  dsimp only [d7f_observations]
  rw [fgsaCoreReads_def p c, fgsaSafetyReads_def p c]
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
  have hs := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t
  cases hk : fgBlockOf st (fgHead p st) with
  | none =>
    left
    change (fgInputs p st).2 = _
    change (match fgBlockOf st (fgHead p st) with
      | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
    rw [hk]
  | some K =>
    right
    have hK := ((fgBlockOf_spec p st hs _ K).mp hk).1
    change K ∈ (FGSA.clock p _ _).fg.TF at hK
    rw [FGSA.clock_fg] at hK
    refine ⟨K, hK, ?_⟩
    change (fgInputs p st).2 = _
    rw [FGSA.fgInputs_headFields p st K hk]

private theorem d7f_emission :
    FGCompose.HighRecordEmission (fgsaSafetyReads p c) (d7f_timing p) E rho p.E p.cfg := by
  intro j x r a u ha hd
  rw [d7f_row_eq] at ha
  rw [fgsaSafetyReads_def p c] at hd ⊢
  rw [d7f_decode p hd] at ha
  obtain ⟨_, _, _, _, hsend⟩ := (fgsa_emitsAt_row E rho j x _ ha.2.1 u.signer
    (.vote ⟨u.height_pair, u.finality_pair⟩)).mp ha.2.2
  exact (fgsa_attest_decode _ _ u.signer _ hsend).symm

private theorem d7f_own_row (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
    (ho : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleasedAt E rho x i) :
    ∃ r, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i ∧
      (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
        (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body := by
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · rename_i hnode
    have hem := (List.mem_filter.mp ho).1
    cases hi : rho.events[i]? with
    | none => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
    | some ev =>
      cases ev with
      | restart z t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | deliver z o t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | tick z t =>
        have hz : z = x := by simpa only [hi, Option.map_some, V2.Event.node,
          Option.some.injEq] using hnode
        subst z
        obtain ⟨_, _, r, hr, ha⟩ := (fgsa_emitsAt_row E rho i x t hi seat body).mp hem
        exact ⟨r, by simp only [hr], hem, hr ▸ ha⟩
  · cases ho

private theorem d7f_own :
    FGCompose.HighRecordOwnOrigin (fgsaSafetyReads p c) (d7f_timing p) E rho := by
  rw [FGCompose.HighRecordOwnOrigin_def]
  intro j x o u hx ho hd
  rw [fgsaSafetyReads_def p c] at hd
  rcases o with ⟨auth, msg⟩
  cases auth with
  | none => cases msg <;> cases hd
  | seat label seat =>
    cases label with
    | prop s => cases msg <;> cases hd
    | base label =>
      cases label with
      | head s => cases msg <;> cases hd
      | fg =>
        cases msg with
        | head B => cases hd
        | proposal N => cases hd
        | row body =>
          obtain ⟨r, hj, hem, _⟩ := d7f_own_row p c E rho j x seat body ho
          refine ⟨r, ⟨.seat .fg seat, body⟩, ?_, ?_⟩
          · rw [d7f_row_eq]; exact ⟨hx, hj, hem⟩
          · rw [fgsaSafetyReads_def p c]; exact hd

private theorem d7f_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7f_observations p c) (d7f_timing p) E rho (d7f_wire p c) := by
  intro j x r a entry ha hn
  rw [d7f_row_eq] at ha
  change FGCompose.namedEntry a.payload.height_pair = some entry at hn
  rw [d7f_entry_eq] at hn
  obtain ⟨C, hs, he⟩ := h j x r a entry ha hn
  exact ⟨C, (d7f_source_eq p c E rho x r).symm ▸ hs, he⟩

private theorem d7f_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (fgsaSafetyReads p c) (d7f_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7f_record (nd : Node p) : (fgsaSafetyReads p c).record nd = nd.record := by
  rw [fgsaSafetyReads_def p c]

private theorem d7f_clock (nd : (fgsa p c).State) (t : Time) :
    ((fgsa p c).clock nd t).st = FGSA.clock p nd.st t := rfl

omit [DecidableEq V] in
private theorem d7f_cut (t : Time) : FGCompose.afterTicksIdx rho t = afterTicksIdx rho t := rfl

private theorem d7f_high (w : HealingWitness) (C : FGBlock (Fin p.n)) :
    FGCompose.high (fgsaCoreReads p c) (d7f_observations p c) (d7f_point p w).reset C =
      high p w C := rfl

private theorem d7f_store (i : Nat) (x : V) (_hx : x ∈ rho.honest) :
    KitFG.FGStoreInvariant (d7f_observations p c).height (d7f_observations p c).finality
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  dsimp only [d7f_observations]
  rw [fgsaCoreReads_def p c]
  exact (cstoreInv_stateBefore E rho i x).fg

private theorem d7f_roots (i : Nat) (x : V) (_hx : x ∈ rho.honest) :
    ViewRootInj ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg.TF := by
  rw [fgsaCoreReads_def p c]
  exact viewRootInj_TF p _ (cstoreInv_stateBefore E rho i x)

private theorem d7f_observation_laws :
    FGCompose.FGObservationLaws (fgsaCoreReads p c) (d7f_observations p c) where
  controls_eq nd := by
    dsimp only [d7f_observations]
    rw [fgsaCoreReads_def p c]; rfl
  viable_eq nd X := by
    dsimp only [d7f_observations]
    rw [fgsaCoreReads_def p c]; rfl

private theorem d7f_height_row_eq (r h : Nat) :
    FGCompose.HeightRow (fgsaSafetyReads p c) E rho (d7f_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) r h =
      HeightRow p c E rho r h := by
  dsimp only [FGCompose.HeightRow, HeightRow] at *
  simp only [d7f_row_eq, d7f_entry_eq]

private theorem d7f_mu_eq :
    FGCompose.muOf (fgsaSafetyReads p c) E rho (d7f_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      muOf p c E rho := by
  unfold FGCompose.muOf FGCompose.oldRowHeights muOf oldRowHeights
  simp only [d7f_row_eq, d7f_entry_eq]
  rfl

private theorem d7f_reset (w : HealingWitness) (h : H0Reset p c E rho w) :
    FGCompose.H0Reset (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7f_observations p c) (d7f_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E)
      (d7f_point p w).reset := by
  refine ⟨h.rG_after, h.rG_first, h.cut, ?_, ?_, ?_,
    h.cut_lower, h.cut_upper, ?_, ?_, h.label, ?_, h.synchronous⟩
  · have hf := h.frontier
    dsimp only [d7f_point, FGCompose.honestFrontier, honestFrontier] at hf ⊢
    simpa only [d7f_fg] using hf
  · dsimp only [d7f_point] at *
    simpa only [d7f_row_eq, d7f_entry_eq] using h.rowCap
  · dsimp only [d7f_point] at *
    simpa only [d7f_mu_eq] using h.mu_le
  · dsimp only [d7f_point] at *
    simpa only [d7f_height_row_eq] using h.reset_row
  · dsimp only [d7f_point] at *
    simpa only [d7f_height_row_eq] using h.reset_first
  · have hf := h.fresh
    dsimp only [d7f_point] at *
    simp only [d7f_row_eq, d7f_entry_eq, d7f_source_eq] at hf ⊢
    dsimp only [d7f_observations] at *
    simpa only [d7f_erase] using hf

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:841–879: high honest sources at one height have one entry.
DC: INTENTIONAL: H1 supplies compatibility; height plateau supplies the entry. -/
theorem high_source_entry_eq (w : HealingWitness) (hhigh : THigh p c E rho w)
    (x z : V) (r s : Nat) (C D : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (hz : z ∈ rho.honest)
    (hC : actionSourceFG p c E rho x r = some (some C))
    (hD : actionSourceFG p c E rho z s = some (some D))
    (hc : high p w C) (hd : high p w D)
    (heq : (heightView p C).h = (heightView p D).h) :
    (heightView p C).T_h = (heightView p D).T_h := by
  exact FGCompose.high_source_entry_eq (d7f_chain p c E rho w hhigh)
    (fgCertificateLaws p) (d7f_reflect p c) x z r s C D hx hz
    ((d7f_source_eq p c E rho x r).symm ▸ hC)
    ((d7f_source_eq p c E rho z s).symm ▸ hD) hc hd heq

private noncomputable def recordInv_entry (y : Nat) : BlockId := by
  classical
  exact if h : ∃ x r C, x ∈ rho.honest ∧
      actionSourceFG p c E rho x r = some (some C) ∧ (heightView p C).h = y
    then (heightView p (Classical.choose (Classical.choose_spec
      (Classical.choose_spec h)))).T_h.root else genesisRoot

private theorem recordInv_entry_source (w : HealingWitness) (hh : THigh p c E rho w)
    (x : V) (r : Nat) (C : FGBlock (Fin p.n)) (hx : x ∈ rho.honest)
    (hs : actionSourceFG p c E rho x r = some (some C)) (hc : high p w C) :
    recordInv_entry p c E rho (heightView p C).h = (heightView p C).T_h.root := by
  classical
  unfold recordInv_entry
  split_ifs with h
  · obtain ⟨hz, hD, heq⟩ := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))
    exact congrArg FGBlock.root (high_source_entry_eq p c E rho w hh _ x _ r _ C
      hz hx hD hs (by simpa only [high_def, heq] using hc) hc heq)
  · exact (h ⟨x, r, C, hx, hs, rfl⟩).elim

private theorem recordInv_height_pair_some_def (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair) : height_pair Λ (some (y, T)) fp =
      if Λ.timeout y then .vote y T true else
        match own_lock Λ y fp with
        | some locked => if locked = T then .vote y T false else .empty
        | none => match Λ.target y with
          | some recorded => if recorded = T then .vote y T false else .vote y T true
          | none => .vote y T false := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: the three record guards give a target, including the own lock.
DC: Protocol/ValidatorClient.lean:216–229, height-pair branches. -/
theorem high_record_target_choice (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair)
    (ht : Λ.target y = none ∨ Λ.target y = some T)
    (hn : Λ.timeout y = false)
    (hl : Λ.lock y = none ∨ Λ.lock y = some T)
    (hf : ∀ f, fp = some f → f.height = y → f.target = T) :
    height_pair Λ (some (y, T)) fp = .vote y T false := by
  exact FGCompose.high_record_target_choice Λ y T fp ht hn hl hf

private def recordInv_good (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce) : Prop :=
  ∀ y, M + 1 ≤ y →
    (Λ.target y = none ∨ Λ.target y = some (entry y)) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some (entry y)) ∧
    ∀ b ∈ Λ.sent, ∀ T timeout, b.1 = .vote y T timeout → T = entry y ∧ timeout = false

private theorem recordInv_finality_source (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (t : Time) (Λ : Record) (fp : FinalityPair)
    (hx : x ∈ rho.honest)
    (hf : finality_pair Λ (fgInputs p
      (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t)).2 = some fp)
    (hy : w.M + 1 ≤ fp.height) :
    fp.target = recordInv_entry p c E rho fp.height := by
  classical
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
  have hs := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t
  cases hk : fgBlockOf st (fgHead p st) with
  | none =>
    have hfields : (fgInputs p st).2 = ⟨0, genesisRoot, 0⟩ := by
      change (match fgBlockOf st (fgHead p st) with
        | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
      rw [hk]
    change finality_pair Λ (fgInputs p st).2 = some fp at hf
    rw [hfields] at hf
    delta finality_pair at hf
    simp only [Nat.lt_irrefl, false_and, ite_false] at hf
    cases hf
  | some K =>
    change finality_pair Λ (fgInputs p st).2 = some fp at hf
    rw [FGSA.fgInputs_headFields p st K hk] at hf
    obtain ⟨hheight, hroot, _, _⟩ := KitFG.provenance_finalityRow_of_heightLaws p.E
      (heightView p) (finalityView p) (fgCertificateLaws p).height Λ K fp hf
    have hK := ((fgBlockOf_spec p st hs _ K).mp hk).1
    change K ∈ (FGSA.clock p _ _).fg.TF at hK
    rw [FGSA.clock_fg] at hK
    have hnz : (heightView p K).h_j ≠ 0 := by simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := (fgCertificateLaws p).height.justification_certificate K hnz
    have hw' : ∀ k, ∃ W a, k ∈ Q → FGBlock.Preceq W K ∧ a ∈ W.rows ∧
        a.signer = k ∧ a.height_pair = .vote (heightView p K).h_j
          (heightView p K).J.root false := by
      intro k
      by_cases h : k ∈ Q
      · obtain ⟨W, a, ha⟩ := hw k h
        exact ⟨W, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun hk => (h hk).elim⟩
    choose W a ha using hw'
    obtain ⟨k, hkQ, z, r, wire, hb, hd, _, C, G, hC, hn, _⟩ :=
      (hqc i x K hx hK).2.1 Q (fun k => (W k, a k)) hnz hQ ha
    have hname : namedEntry (a k).height_pair =
        some ((heightView p K).h_j, (heightView p K).J.root) := by
      rw [(ha k hkQ).2.2.2]; rfl
    rw [hname] at hn
    have heq := Option.some.inj hn
    have hyC : (heightView p C).h = fp.height :=
      (congrArg Prod.fst heq).symm.trans hheight.symm
    have hTC : (heightView p K).J.root = (heightView p C).T_h.root :=
      congrArg Prod.snd heq
    obtain ⟨j, _, hj⟩ := hb
    have hentry := recordInv_entry_source p c E rho w hh z r C hj.1 hC
      (by rw [high_def, hyC]; exact hy)
    rw [hyC] at hentry
    exact hroot.trans (hTC.trans hentry.symm)

private theorem recordInv_write (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce)
    (a : Row (Fin p.n)) (hg : recordInv_good M entry Λ)
    (hh : ∀ y T timeout, a.height_pair = .vote y T timeout → M + 1 ≤ y →
      T = entry y ∧ timeout = false)
    (hf : ∀ f, a.finality_pair = some f → M + 1 ≤ f.height → f.target = entry f.height) :
    recordInv_good M entry (record_row_once Λ a) := by
  intro y hy
  obtain ⟨ht, hn, hl, hb⟩ := hg y hy
  have hf' : ∀ f, a.finality_pair = some f → f.height = y → f.target = entry y := by
    intro f hfp hfy
    simpa only [hfy] using hf f hfp (hfy ▸ hy)
  have hlock : own_lock Λ.toRecord y a.finality_pair = none ∨
      own_lock Λ.toRecord y a.finality_pair = some (entry y) := by
    cases hp : a.finality_pair with
    | none => simpa only [own_lock, hp] using hl
    | some f =>
      by_cases he : f.height = y
      · right; simp only [own_lock, he, ite_true, hf' f hp he]
      · simpa only [own_lock, hp, he, ite_false] using hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord a).target y = none ∨
      (record_row Λ.toRecord a).target y = some (entry y)
    rcases a with ⟨seat, pair, fp⟩
    cases pair with
    | empty => cases fp <;> simpa [record_row, Record.with_lock] using ht
    | vote g T timeout =>
      by_cases he : y = g
      · subst g
        obtain ⟨rfl, rfl⟩ := hh y T timeout rfl hy
        cases fp <;> simp only [record_row, Record.with_lock]
        all_goals
          by_cases htarget : Λ.target y = none
          · simp [htarget, Record.with_target]
          · simpa [htarget] using ht
      · cases timeout <;> cases fp <;> simp only [record_row] <;>
          (try split) <;> simpa [Record.with_lock, Record.with_timeout,
            Record.with_target, he] using ht
  · change (record_row Λ.toRecord a).timeout y = false
    apply KitFG.record_row_timeout_false_of_ne _ _ hn
    intro T hp
    have := (hh y T true hp hy).2
    cases this
  · exact (KitFG.record_row_lock Λ.toRecord a y) ▸ hlock
  · intro b hmem T timeout hpair
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh y T timeout hpair hy
    · exact hb b hmem T timeout hpair

private theorem recordInv_released_pair (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (r : Nat) (seat : Fin p.n) (body : RowPayload)
    (hx : x ∈ rho.honest)
    (ha : (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
      (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body)
    (hg : recordInv_good w.M (recordInv_entry p c E rho)
      (V2.D.Run.stateBefore E rho i x).record)
    (y : Nat) (T : BlockId) (timeout : Bool)
    (hp : body.height_pair = .vote y T timeout) (hy : w.M + 1 ≤ y)
    (hsource : ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
      (heightView p C).h = y ∧ (heightView p C).T_h.root = T) :
    T = recordInv_entry p c E rho y ∧ timeout = false := by
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
  let Λ := (V2.D.Run.stateBefore E rho i x).record
  have hd := (fgsa_attest_decode st Λ seat body ha).symm
  change (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
    some (body.toRow seat) at hd
  obtain ⟨g, U, tm, hpair, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hd
  have hhp := congrArg Row.height_pair he
  change body.height_pair = .vote g U tm at hhp
  rw [hp] at hhp
  cases hhp
  rw [FGSA.attest_source_heightView] at hpair
  have hfields := KitFG.height_pair_vote_fields hpair
  rw [hfields] at hpair
  obtain ⟨C, hs, hc, ht⟩ := hsource
  have hentry := recordInv_entry_source p c E rho w hh x r C hx hs
    (by rw [high_def, hc]; exact hy)
  rw [hc, ht] at hentry
  obtain ⟨htr, hto, hlock, _⟩ := hg y hy
  have hchoice := high_record_target_choice Λ.toRecord y T
    (finality_pair Λ.toRecord (fgInputs p st).2)
    (by simpa only [hentry] using htr) hto (by simpa only [hentry] using hlock)
    (by
      intro fp hf hfy
      have hfroot := recordInv_finality_source p c E rho w hh hqc i x (p.actionTime r)
        Λ.toRecord fp hx hf (hfy ▸ hy)
      rw [hfy, hentry] at hfroot
      exact hfroot)
  rw [hchoice] at hpair
  cases hpair
  exact ⟨hentry.symm, rfl⟩

private theorem recordInv_released_finality (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (r : Nat) (seat : Fin p.n) (body : RowPayload)
    (hx : x ∈ rho.honest)
    (ha : (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
      (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body)
    (f : FinalityPair) (hf : body.finality_pair = some f) (hy : w.M + 1 ≤ f.height) :
    f.target = recordInv_entry p c E rho f.height := by
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
  let Λ := (V2.D.Run.stateBefore E rho i x).record
  have hd := (fgsa_attest_decode st Λ seat body ha).symm
  change (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
    some (body.toRow seat) at hd
  obtain ⟨_, _, _, _, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hd
  have hfp := congrArg Row.finality_pair he
  change body.finality_pair = _ at hfp
  rw [hf] at hfp
  exact recordInv_finality_source p c E rho w hh hqc i x (p.actionTime r) Λ.toRecord f
    hx (Option.filter_eq_some_iff.mp hfp.symm).1 hy

private theorem recordInv_own_row (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
    (ho : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleasedAt E rho x i) :
    ∃ r, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i ∧
      (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
        (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body := by
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · rename_i hnode
    have hem := (List.mem_filter.mp ho).1
    cases hi : rho.events[i]? with
    | none => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
    | some ev =>
      cases ev with
      | restart z t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | deliver z o t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | tick z t =>
        have hz : z = x := by simpa only [hi, Option.map_some, V2.Event.node,
          Option.some.injEq] using hnode
        subst z
        obtain ⟨_, _, r, hr, ha⟩ := (fgsa_emitsAt_row E rho i x t hi seat body).mp hem
        exact ⟨r, by simp only [hr], hem, hr ▸ ha⟩
  · cases ho

private theorem recordInv_all (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (i : Nat) (x : V) (hx : x ∈ rho.honest) :
    recordInv_good w.M (recordInv_entry p c E rho)
      (V2.D.Run.stateBefore E rho i x).record := by
  induction i with
  | zero =>
    rw [ownRecord_fold_run]
    simp only [V2.D.Engine.ownReleased_self]
    change recordInv_good w.M (recordInv_entry p c E rho) RecordOnce.initial
    intro y _
    exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | succ i ih =>
    have hstep : (V2.D.Run.stateBefore E rho (i + 1) x).record =
        (V2.D.Engine.ownReleasedAt E rho x i).foldl (recordRow? p)
          (V2.D.Run.stateBefore E rho i x).record := by
      have hls : V2.D.Engine.ownReleased E rho x 0 (i + 1) =
          V2.D.Engine.ownReleased E rho x 0 i ++ V2.D.Engine.ownReleasedAt E rho x i :=
        V2.D.Engine.ownReleased_succ E rho x (Nat.zero_le i)
      calc
        _ = (V2.D.Engine.ownReleased E rho x 0 (i + 1)).foldl
            (recordRow? p) RecordOnce.initial := ownRecord_fold_run E rho (i + 1) x
        _ = (V2.D.Engine.ownReleased E rho x 0 i ++ V2.D.Engine.ownReleasedAt E rho x i).foldl
            (recordRow? p) RecordOnce.initial := congrArg
              (fun ls : List (Obj p) => ls.foldl (recordRow? p) RecordOnce.initial) hls
        _ = (V2.D.Engine.ownReleasedAt E rho x i).foldl (recordRow? p)
            ((V2.D.Engine.ownReleased E rho x 0 i).foldl (recordRow? p) RecordOnce.initial) :=
          List.foldl_append
        _ = _ := congrArg (fun Λ => (V2.D.Engine.ownReleasedAt E rho x i).foldl
          (recordRow? p) Λ) (ownRecord_fold_run E rho i x).symm
    rw [hstep]
    have preserve : ∀ o ∈ V2.D.Engine.ownReleasedAt E rho x i, ∀ Λ,
        recordInv_good w.M (recordInv_entry p c E rho) Λ →
        recordInv_good w.M (recordInv_entry p c E rho) (recordRow? p Λ o) := by
      intro o ho Λ hg
      rcases o with ⟨auth, msg⟩
      cases auth with
      | none => exact hg
      | seat label seat =>
        cases label with
        | prop s => exact hg
        | base label =>
          cases label with
          | head s => exact hg
          | fg =>
            cases msg with
            | head B => exact hg
            | proposal N => exact hg
            | row body =>
              obtain ⟨r, hj, hem, ha⟩ := recordInv_own_row p c E rho i x seat body ho
              apply recordInv_write p _ _ Λ (body.toRow seat) hg
              · intro y T timeout hp hy
                change body.height_pair = .vote y T timeout at hp
                have hn : namedEntry body.height_pair = some (y, T) := by rw [namedEntry_def, hp]
                obtain ⟨C, hs, heq⟩ := hnames i x r _ _ ⟨hx, hj, hem⟩ hn
                have hc := (congrArg Prod.fst heq).symm
                have ht := (congrArg Prod.snd heq).symm
                exact recordInv_released_pair p c E rho w hh hqc i x r seat body hx ha ih
                  y T timeout hp hy ⟨C, hs, hc, ht⟩
              · exact recordInv_released_finality p c E rho w hh hqc i x r seat body hx ha
    have foldGood (ls : List (Obj p)) (hls : ls ⊆ V2.D.Engine.ownReleasedAt E rho x i)
        (Λ : RecordOnce) (hg : recordInv_good w.M (recordInv_entry p c E rho) Λ) :
        recordInv_good w.M (recordInv_entry p c E rho) (ls.foldl (recordRow? p) Λ) := by
      induction ls generalizing Λ with
      | nil => exact hg
      | cons o ls ih =>
        exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
          (preserve o (hls List.mem_cons_self) Λ hg)
    exact foldGood _ (List.Subset.refl _) _ ih

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879 (FF2): all actual writes preserve the high-entry guards.
DC: INTENTIONAL: H1 and QC origin replace a fixed-root window premise.
Old records rest on THigh .1 over all rounds, not on H0.
The prefix starts at the initial durable record and includes pre-GST writes. -/
theorem high_entry_record_invariant (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∃ entry : Nat → BlockId,
      (∀ x r C, x ∈ rho.honest →
        actionSourceFG p c E rho x r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      (∀ i x y, x ∈ rho.honest → w.M + 1 ≤ y →
        let Λ := (V2.D.Run.stateBefore E rho i x).record
        (Λ.target y = none ∨ Λ.target y = some (entry y)) ∧ Λ.timeout y = false ∧
        (Λ.lock y = none ∨ Λ.lock y = some (entry y)) ∧
        ∀ b ∈ Λ.sent, ∀ T timeout, b.1 = .vote y T timeout →
          T = entry y ∧ timeout = false) := by
  obtain ⟨entry, hsource, hrecord⟩ := FGCompose.high_entry_record_invariant
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
  refine ⟨entry, ?_, ?_⟩
  · dsimp only [d7f_observations, d7f_point, FGCompose.high] at *
    simpa only [d7f_source_eq, high_def]
      using hsource
  · intro i x y hx hy
    simpa only [fgsaSafetyReads_def p c] using hrecord i x hx y hy

private def recordInv_fresh (y : Nat) (Λ : RecordOnce) : Prop :=
  Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
    ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout

private theorem recordInv_fresh_write (y : Nat) (Λ : RecordOnce)
    (a : Row (Fin p.n)) (hg : recordInv_fresh y Λ)
    (hh : ∃ g T timeout, a.height_pair = .vote g T timeout ∧ g < y)
    (hf : ∀ f, a.finality_pair = some f → f.height < y) :
    recordInv_fresh y (record_row_once Λ a) := by
  obtain ⟨g, T, timeout, hp, hgy⟩ := hh
  rcases a with ⟨seat, pair, fp⟩
  dsimp only at hp
  subst pair
  obtain ⟨ht, hn, hl, hb⟩ := hg
  have hne : y ≠ g := by simp only [Height] at *; omega
  have hlock : own_lock Λ.toRecord y fp = none := by
    cases fp with
    | none => exact hl
    | some f =>
      have hfy : f.height ≠ y := by have := hf f rfl; simp only [Height] at *; omega
      change (if f.height = y then some f.target else Λ.lock y) = none
      rw [ite_eq_right hfy]
      exact hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).target y = none
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using ht
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).timeout y = false
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using hn
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).lock y = none
    rw [KitFG.record_row_lock]
    exact hlock
  · intro b hm U tm he
    rcases List.mem_cons.mp hm with rfl | hm
    · have := (NamedHeightPair.vote.inj he).1
      simp only [Height] at *; omega
    · exact hb b hm U tm he

private theorem recordInv_own_origin (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
    (ho : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleased E rho x 0 i) :
    ∃ j r, j < i ∧ rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho j ∧
      (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r))
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some body := by
  rw [V2.D.Engine.ownReleased_def] at ho
  obtain ⟨j, hj, ho⟩ := List.mem_flatMap.mp ho
  have hji : j < i := by simpa using hj
  obtain ⟨r, hr, hem, ha⟩ := recordInv_own_row p c E rho j x seat body ho
  exact ⟨j, r, hji, hr, hem, ha⟩

private theorem recordInv_rowHeight_def (a : RowWire p.n) : rowHeight a =
    NamedHeightPair.casesOn (motive := fun _ => Option Nat) a.payload.height_pair
      none (fun h _ _ => some h) := by
  rw [rowHeight_def]
  cases a.payload.height_pair <;> rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:886–909,1228–1254: no earlier row at or above y leaves y fresh.
DC: INTENTIONAL: durable actual-write history, including restart and suppression. -/
theorem high_record_fresh_at_cut (i : Nat) (x : V) (y : Nat) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout := by
  have h := FGCompose.high_record_fresh_at_cut (D := d7f_wire p c)
    (fgsaSafetyClientLaws p c) (d7f_emission p c E rho) (d7f_own p c E rho) i x y hx
    (by simpa only [d7f_row_eq, d7f_rowHeight_eq] using hbefore)
  dsimp only [FGCompose.HighRecordFresh] at *
  simpa only [fgsaSafetyReads_def p c] using h

private theorem recordInv_once_target (st : State p.n) (Λ : RecordOnce)
    (seat : Fin p.n) (y : Nat) (T : BlockId)
    (hp : height_pair Λ.toRecord
      ((fgInputs p st).1.map (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
      (finality_pair Λ.toRecord (fgInputs p st).2) = .vote y T false)
    (hsent : ∀ b ∈ Λ.sent, ∀ U timeout, b.1 = .vote y U timeout → U = T ∧ timeout = false) :
    (∃ body, (attest p st Λ seat).1 = some body ∧ body.height_pair = .vote y T false) ∨
      ∃ b ∈ Λ.sent, b.1 = .vote y T false := by
  by_cases hs : sameHeightOnce Λ y T false = true
  · right
    obtain ⟨⟨pair, fp⟩, hm, hpair⟩ := List.any_eq_true.mp hs
    cases pair with
    | empty => cases hpair
    | vote g U timeout =>
      change (decide (g = y) && (!false || decide (U = T))) = true at hpair
      have hg : g = y := of_decide_eq_true (Bool.and_eq_true_iff.mp hpair).1
      subst g
      obtain ⟨rfl, rfl⟩ := hsent _ hm U timeout rfl
      exact ⟨_, hm, rfl⟩
  · let a : Row (Fin p.n) := ⟨seat, .vote y T false,
      (finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < y))⟩
    by_cases hm : a.onceKey ∈ Λ.sent
    · exact Or.inr ⟨a.onceKey, hm, rfl⟩
    · left
      refine ⟨.vote (RowBody.ofRow a), ?_, rfl⟩
      have ha : (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
          some a := by
        rw [createRowOnce_def]
        dsimp only
        rw [FGSA.attest_source_heightView, hp]
        simp only [hs, Bool.false_eq_true, ite_false]
        change (if a.onceKey ∈ Λ.sent then (none, Λ) else
          (some a, record_row_once Λ a)).1 = some a
        rw [ite_eq_right hm]
      change Option.map (fun a => RowPayload.vote (RowBody.ofRow a))
        (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 = _
      rw [ha]; rfl

private theorem recordInv_sent_origin (ls : List (Obj p)) (Λ : RecordOnce)
    (b : NamedHeightPair × Option FinalityPair) (hm : b ∈ (ls.foldl (recordRow? p) Λ).sent) :
    b ∈ Λ.sent ∨ ∃ seat body, ofRow p ⟨.seat .fg seat, body⟩ ∈ ls ∧
      (body.height_pair, body.finality_pair) = b := by
  induction ls generalizing Λ with
  | nil => exact Or.inl hm
  | cons o ls ih =>
    rcases ih (recordRow? p Λ o) hm with hold | ⟨seat, body, hm, he⟩
    · rcases o with ⟨auth, msg⟩
      cases auth with
      | none => exact Or.inl hold
      | seat label seat =>
        cases label with
        | prop s => exact Or.inl hold
        | base label =>
          cases label with
          | head s => exact Or.inl hold
          | fg =>
            cases msg with
            | head B => exact Or.inl hold
            | proposal N => exact Or.inl hold
            | row body =>
              rcases List.mem_cons.mp hold with he | hold
              · exact Or.inr ⟨seat, body, List.mem_cons_self, he.symm⟩
              · exact Or.inl hold
    · exact Or.inr ⟨seat, body, List.mem_cons_of_mem _ hm, he⟩

private theorem recordInv_complete (i : Nat) (x : V) (r : Nat)
    (seat : Fin p.n) (body : RowPayload)
    (hj : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hem : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    RowComplete p c rho x ⟨.seat .fg seat, body⟩ := by
  obtain ⟨_, hseat, _, _, hb⟩ := (fgsa_emitsAt_row E rho i x _ hj seat body).mp hem
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, hbody⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨h, T, timeout, hp, he, _, _, _⟩ :=
      KitFG.createRowOnce_released p.E p.cfg _ ⟨0, p.nPos⟩ _ _ ha
    rw [FGSA.attest_source_heightView] at hp
    have hf := KitFG.height_pair_vote_fields hp
    obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
    have heh := congrArg Prod.fst hc
    change (heightView p C).h = h at heh
    have hpos : 1 ≤ h := heh ▸ (fgCertificateLaws p).height.one_le_h C
    rw [← hbody, he]
    change (decide (1 ≤ h) &&
      ((finality_pair _ _).filter (fun fp => decide (fp.height < h))
        |>.map (fun fp => decide (fp.height < h))).getD true) = true
    cases hfp : finality_pair _ _ with
    | none => simp [hpos, Option.filter]
    | some fp => by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]
  · rw [RowSigner_def]
    exact ⟨seat, rfl, hseat⟩

omit [DecidableEq V] in
private theorem d7f_holder (k : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho k = rho.seatOf (.base .fg) k := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def p c]
  rfl

private theorem d7f_honest_eq :
    Finset.univ.filter (fun k => FGCompose.safetyHolder (fgsaSafetyReads p c) rho k ∈
      rho.honest) = honestSeats p c rho := by
  ext k
  simp only [honestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.of_eq (congrArg (fun x : V => x ∈ rho.honest) (d7f_holder p c rho k))

omit [DecidableEq V] in
private theorem d7f_signer_eq (a : RowWire p.n) (x : V) :
    FGCompose.RowSigner (fgsaSafetyReads p c) rho (d7f_signer p) a x =
      RowSigner p c rho a x := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => dsimp only [FGCompose.RowSigner, RowSigner, d7f_signer]; simp
  | proposer s => dsimp only [FGCompose.RowSigner, RowSigner, d7f_signer]; simp
  | seat label i =>
    cases label
    all_goals dsimp only [FGCompose.RowSigner, RowSigner, d7f_signer]
    all_goals simp [FGCompose.safetyHolder_def]
    rw [fgsaSafetyReads_def p c]
    rfl

omit [DecidableEq V] in
private theorem d7f_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7f_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  change (_ ∧ _) = (_ ∧ _)
  rw [d7f_signer_eq]

private theorem d7f_src (nd : (fgsa p c).State) :
    ((fgsaSafetyReads p c).inputs nd).1 = (fgsaCoreReads p c).source nd := by
  rw [fgsaCoreReads_def p c, fgsaSafetyReads_def p c]
  rfl

private theorem d7f_height (C : FGBlock (Fin p.n)) :
    ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root) =
      (((d7f_observations p c).height C).h, ((d7f_observations p c).height C).T_h.root) := by
  dsimp only [d7f_observations]
  rw [heightView_bridge p C]
  rfl

private theorem d7f_enabled (r : Nat) :
    (fgsaSafetyReads p c).enabled ((d7f_timing p).action r) = true := by
  rw [fgsaSafetyReads_def p c]
  change decide (p.actionTime ((p.slotOf (p.actionTime r) - 1) / p.R) = p.actionTime r) = true
  have hslot : p.slotOf (p.actionTime r) = r * p.R + 1 :=
    (fgsa_postClock_slot (c := c) (fgsa p c).init _).2.symm.trans
      (fgsa_gate_slot (c := c) _ (r * p.R))
  rw [hslot]
  simp [Nat.mul_div_cancel r (show 0 < p.R by have := p.RLarge; omega)]

private theorem d7f_wire_laws :
    FGCompose.FGRowPermissionWireLaws (fgsaSafetyReads p c)
      (fun a => FGCompose.namedEntry ((d7f_wire p c).heightPair a)) where
  decoded_wire := by
    intro o u hd
    rw [fgsaSafetyReads_def p c] at hd
    rcases o with ⟨auth, msg⟩
    cases msg with
    | head b => cases hd
    | proposal N => cases hd
    | row body =>
      cases auth with
      | none => cases hd
      | seat l i =>
        cases l with
        | prop s => cases hd
        | base l =>
          cases l with
          | head s => cases hd
          | fg =>
            refine ⟨⟨.seat .fg i, body⟩, ?_, ?_, ?_⟩
            · rw [fgsaSafetyReads_def p c]; rfl
            · rw [fgsaSafetyReads_def p c]; exact hd
            cases body with
            | vote b =>
              have hu := Option.some.inj hd
              subst u
              cases b.height_pair <;> rfl

private theorem d7f_emitted_seat (j : Nat) (x : V) (r : Nat) (a : RowWire p.n)
    (ha : HonestRowAt p c E rho j x r a) : ∃ seat, a.auth = .seat .fg seat := by
  have hm := ha.2.2
  rw [(V2.D.Run.step_tick_eq E rho ha.2.1).2] at hm
  change ofRow p a ∈ (if E.awake x (p.actionTime r) then
    (duties p (p.actionTime r)).flatMap (fun d =>
      (rho.ownSeats (RunDuty.signLabel d) x).filterMap (fun seat =>
        ((fgsa p c).act ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
          (p.actionTime r)) d (rho.input x (p.actionTime r))).map
            (fun m => ⟨.seat (RunDuty.signLabel d) seat, m⟩))) ++ [] else []) at hm
  split at hm
  · rw [List.append_nil] at hm
    obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨seat, _, hm⟩ := List.mem_filterMap.mp hm
    obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.mp hm
    have hbody : m = .row a.payload := congrArg (fun o : Obj p => o.payload) he
    cases d with
    | fgAction q =>
      have hauth := congrArg (fun o : Obj p => o.auth) he
      change .seat (.base .fg) seat = ofAuth p a.auth at hauth
      cases a with
      | mk auth payload =>
        cases auth with
        | none => cases hauth
        | proposer s => cases hauth
        | seat label k =>
          cases label with
          | head s => cases hauth
          | fg => exact ⟨k, rfl⟩
    | headAction s =>
      change (if joinedNow p _ then some (.head _) else none) = some m at hm
      split at hm
      · have h := (Option.some.inj hm).trans hbody
        cases h
      · cases hm
    | propAction s =>
      change (if joinedNow p _ then (propose p _ s).map (withApp p _) else none) = some m at hm
      split at hm
      · obtain ⟨msg, hmsg, hmap⟩ := Option.map_eq_some_iff.mp hm
        unfold propose at hmsg
        split at hmsg
        · cases hmsg
        · obtain ⟨N, _, hn⟩ := Option.map_eq_some_iff.mp hmsg
          subst msg
          have h := hmap.trans hbody
          cases h
      · cases hm
  · cases hm

private theorem d7f_complete :
    ∀ j x r a, FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7f_timing p) j x r a →
      ∃ u, (fgsaSafetyReads p c).decode a = some u ∧
        FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7f_wire p c).signer
          RowWire.valid x a := by
  intro j x r a ha
  rw [d7f_row_eq] at ha
  obtain ⟨seat, hauth⟩ := d7f_emitted_seat p c E rho j x r a ha
  rcases a with ⟨auth, body⟩
  change auth = .seat .fg seat at hauth
  subst auth
  refine ⟨body.toRow seat, ?_, ?_⟩
  · rw [fgsaSafetyReads_def p c]; rfl
  · change FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7f_signer p) RowWire.valid x _
    rw [d7f_complete_eq]
    exact recordInv_complete p c E rho j x r seat body ha.2.1 ha.2.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:886–915 (SO-COV): an earlier or current complete target covers the action.
DC: INTENTIONAL: FF2 proves the target bit; both send-once checks use durable content. -/
theorem high_target_row_covered (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hhigh : high p w C) (hawake : E.awake x (p.actionTime r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      RowComplete p c rho x a ∧
      a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have h := FGCompose.high_target_row_covered
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (d7f_src p c) (d7f_height p c)
    (fgsaSafetyClientLaws p c) (d7f_emission p c E rho) (d7f_own p c E rho)
    (d7f_names p c E rho hnames) (d7f_complete p c E rho) (d7f_wire_laws p c)
    e (by intro k; rw [fgsaSafetyReads_def p c]; exact he k) (d7f_timing_laws p) hS
    (d7f_enabled p c)
    x hx r C ((d7f_source_eq p c E rho x r).symm ▸ hsource) hhigh hawake
  dsimp only [d7f_observations, d7f_wire] at *
  simpa only [d7f_row_eq, d7f_complete_eq p c rho] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: the raw H0 cut has no high target, timeout, lock, or sent row.
DC: INTENTIONAL: the inclusive raw cut uses H0's emission cap, including old sends. -/
theorem high_record_reset_fresh (w : HealingWitness) (h0 : H0Reset p c E rho w)
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (hx : x ∈ rho.honest)
    (y : Nat) (hy : w.M + 1 ≤ y) :
    let Λ := (V2.D.Run.stateBefore E rho (afterTicksIdx rho w.u₀) x).record
    Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout := by
  have h := FGCompose.high_record_reset_fresh (D := d7f_wire p c)
    (fgsaSafetyClientLaws p c) (d7f_emission p c E rho) (d7f_own p c E rho)
    (d7f_point p w).reset (recoveryStart p E) (d7f_reset p c E rho w h0) hs x hx y hy
  dsimp only [FGCompose.HighRecordFresh, d7f_point] at *
  simpa only [fgsaSafetyReads_def p c, d7f_cut] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879,1228–1254: the exact K-ROWS record premise at a prefix cut.
DC: INTENTIONAL: FF2 at y and durable freshness at y+1 share the actual record. -/
theorem high_record_guards_and_fresh (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C))
    (y : Nat) (hheight : (heightView p C).h = y) (hy : w.M + 1 ≤ y)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y + 1) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    (Λ.target y = none ∨ Λ.target y = some (heightView p C).T_h.root) ∧
      Λ.timeout y = false ∧
      (Λ.lock y = none ∨ Λ.lock y = some (heightView p C).T_h.root) ∧
      Λ.target (y + 1) = none ∧ Λ.timeout (y + 1) = false ∧ Λ.lock (y + 1) = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote (y + 1) T timeout := by
  have h := FGCompose.high_record_guards_and_fresh
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
    z r C hz ((d7f_source_eq p c E rho z r).symm ▸ hsource) y hheight hy i x hx
    (by simpa only [d7f_row_eq, d7f_rowHeight_eq] using hbefore)
  dsimp only [FGCompose.HighRecordFresh, d7f_observations] at *
  simpa only [FGCompose.HighRecordGuard_W, fgsaSafetyReads_def p c, and_assoc] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:886–909,1208–1211: the first high target cannot be suppressed.
DC: INTENTIONAL: an earlier covering send contradicts the strict raw height cap. -/
theorem high_target_first_row (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hhigh : high p w C) (hawake : E.awake x (p.actionTime r) = true)
    (hbefore : ∀ j q a h, q < r → HonestRowAt p c E rho j x q a →
      rowHeight a = some h → h < (heightView p C).h) :
    ∃ j a, HonestRowAt p c E rho j x r a ∧ RowComplete p c rho x a ∧
      a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have h := FGCompose.high_target_first_row
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (d7f_src p c) (d7f_height p c)
    (fgsaSafetyClientLaws p c) (d7f_emission p c E rho) (d7f_own p c E rho)
    (d7f_names p c E rho hnames) (d7f_complete p c E rho) (d7f_wire_laws p c)
    e (by intro k; rw [fgsaSafetyReads_def p c]; exact he k) (d7f_timing_laws p) hS
    (d7f_enabled p c)
    x hx r C ((d7f_source_eq p c E rho x r).symm ▸ hsource) hhigh hawake
    (by
      dsimp only [d7f_observations]
      simpa only [d7f_row_eq, d7f_rowHeight_eq] using hbefore)
  dsimp only [d7f_observations, d7f_wire] at *
  simpa only [d7f_row_eq, d7f_complete_eq p c rho] using h

private theorem recordInv_honestSeats_mem (i : Fin p.n) :
    i ∈ honestSeats p c rho ↔ rho.seatOf (.base .fg) i ∈ rho.honest := by
  rw [honestSeats_def p c rho]
  simpa only [Finset.mem_univ, true_and] using
    (@Finset.mem_filter (Fin p.n) (fun k => rho.seatOf (.base .fg) k ∈ rho.honest)
      (fun k => Classical.propDecidable (rho.seatOf (.base .fg) k ∈ rho.honest)) Finset.univ i)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:886–915: the Recovery fault bound supplies an honest unit-weight quorum.
DC: INTENTIONAL: linked fixed FG seats transport honest identity cardinality. -/
theorem high_target_honest_quorum [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3) :
    p.E.IsQuorum (honestSeats p c rho) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have h := FGCompose.high_target_honest_quorum (S := fgsaSafetyReads p c) e
    (by intro k; rw [fgsaSafetyReads_def p c]; exact he k) (fgsaSafetyUnitLaws p) hf
  exact (congrArg p.E.IsQuorum (d7f_honest_eq p c rho)).mp h

private theorem d7f_held_before_eq (x : V) (a : RowWire p.n) (d : Time) :
    FGCompose.HeldBefore (fgsaCoreReads p c) E rho
      (fun nd => FGSA.blockWireRows nd.st) x a d = HeldBefore p c E rho x a d := by
  rw [fgsaCoreReads_def p c]
  rfl

private theorem d7f_receipt (deltaF : Time) (h : TRowsReceipt p c E rho deltaF) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7f_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF := by
  dsimp only [FGCompose.TRowsReceipt] at *
  simp only [d7f_row_eq, d7f_held_before_eq]
  dsimp only [TRowsReceipt, d7f_timing] at *
  simpa only [] using h

private theorem d7f_signer_seat (a : RowWire p.n) (k : Fin p.n) :
    d7f_signer p a = some k ↔ a.auth = .seat .fg k := by
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => dsimp only [d7f_signer] at *; simp []
  | proposer s => dsimp only [d7f_signer] at *; simp []
  | seat label j => cases label <;> (dsimp only [d7f_signer] at *; simp [])

private theorem d7f_fault_weight [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (fgsaSafetyReads p c) rho) < p.E.q := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have holder (k : Fin p.n) : FGCompose.safetyHolder (fgsaSafetyReads p c) rho k = e k :=
    (d7f_holder p c rho k).trans (he k)
  have hset : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
      (Gen.V2.Duty.faulty rho).map e.symm.toEmbedding := by
    delta FGCompose.historyFaulty
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map]
    rw [holder k]
    constructor
    · intro hk
      exact ⟨e k, by simpa [Gen.V2.Duty.faulty_def] using hk, e.symm_apply_apply k⟩
    · rintro ⟨x, hx, hxk⟩
      have hxk' : e.symm x = k := hxk
      have hex : e k = x := by rw [← hxk', e.apply_symm_apply]
      rw [hex]
      simpa [Gen.V2.Duty.faulty_def] using hx
  rw [(fgsaSafetyUnitLaws p).weight, hset, Finset.card_map, (fgsaSafetyUnitLaws p).quorum]
  exact hf.lt

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:886–915: each honest quorum seat has a complete target and its exact receipt.
DC: INTENTIONAL: strict max(emission,GST)+ΔF receipt includes old suppressed sends. -/
theorem high_target_quorum_covered [Fintype V] (G ΔF : Time)
    (hrec : Recovery₂ p c E rho G ΔF) (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hreceipt : TRowsReceipt p c E rho ΔF)
    (r : Nat) (C : FGBlock (Fin p.n)) (hhigh : high p w C)
    (hsource : ∀ x ∈ rho.honest, actionSourceFG p c E rho x r = some (some C))
    (hGST : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + ΔF ≤ rho.horizon) :
    p.E.IsQuorum (honestSeats p c rho) ∧
      ∃ rows : Fin p.n → RowWire p.n, ∀ i ∈ honestSeats p c rho, ∃ j rSent,
        rSent ≤ r ∧
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) rSent (rows i) ∧
        RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
        (rows i).auth = .seat .fg i ∧
        (rows i).payload.height_pair =
          .vote (heightView p C).h (heightView p C).T_h.root false ∧
        ∀ x ∈ rho.honest, HeldBefore p c E rho x (rows i)
          (max (p.actionTime rSent) E.t_GST + ΔF) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hrec.base.linked
  have h := FGCompose.high_target_quorum_covered
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (d7f_src p c) (d7f_height p c)
    (fgsaSafetyClientLaws p c) (d7f_emission p c E rho) (d7f_own p c E rho)
    (d7f_names p c E rho hnames) (d7f_complete p c E rho) (d7f_wire_laws p c)
    e (by intro k; rw [fgsaSafetyReads_def p c]; exact he k)
    (d7f_timing_laws p) hrec.base.valid.toScheduleWellFormed
    (d7f_enabled p c)
    (fgsaSafetyUnitLaws p) hrec.fault (fun nd => FGSA.blockWireRows nd.st) ΔF
    (E.Δ_pos.trans_le hrec.deltaF).le (d7f_receipt p c E rho ΔF hreceipt)
    hrec.awake r C hhigh
    (by simpa only [d7f_source_eq] using hsource) hGST hhor
  obtain ⟨hQ, rows, hrows⟩ := h
  refine ⟨(congrArg p.E.IsQuorum (d7f_honest_eq p c rho)).mp hQ, rows, ?_⟩
  intro i hi
  obtain ⟨j, rSent, hr, ha, hcomplete, hauth, hp, hheld⟩ :=
    hrows i ((d7f_honest_eq p c rho).symm ▸ hi)
  have hseat := d7f_holder p c rho i
  refine ⟨j, rSent, hr, ?_, ?_, ?_, hp, ?_⟩
  · exact hseat ▸ (d7f_row_eq p c E rho j rSent _ (rows i)).mp ha
  · exact hseat ▸ (d7f_complete_eq p c rho _ (rows i)).mp hcomplete
  · exact (d7f_signer_seat p (rows i) i).mp hauth
  · intro x hx
    exact (d7f_held_before_eq p c E rho x (rows i) _).mp (hheld x hx)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: FF2 selects a high target with the actual head's own lock.
DC: Protocol/ValidatorClient.lean:216–229; the head target QC fixes its lock. -/
theorem high_action_target_choice (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C)) (hhigh : high p w C)
    (i : Nat) (x : V) (t : Time) (hx : x ∈ rho.honest) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
    height_pair Λ.toRecord (some ((heightView p C).h, (heightView p C).T_h.root))
      (finality_pair Λ.toRecord (FGSA.fgInputs p st).2) =
      .vote (heightView p C).h (heightView p C).T_h.root false := by
  have h := FGCompose.high_action_target_choice
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
    z r C hz ((d7f_source_eq p c E rho z r).symm ▸ hsource) hhigh i x t hx
  change _ at h
  dsimp only [d7f_observations] at *
  simpa only [fgsaSafetyReads_def p c, d7f_clock] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879,1256–1263: the K-ROWS record guards at the actual action read.
DC: INTENTIONAL: the round cut becomes a prefix cut by strict tick time;
clock_rec transports all seven fields to the postClock record. -/
theorem high_record_guards_and_fresh_at_action (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hs : V2.D.ScheduleWellFormed E rho)
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C))
    (y : Nat) (hheight : (heightView p C).h = y) (hy : w.M + 1 ≤ y)
    (q : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, r < q → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y + 1) :
    ∀ nd, postClock E rho x (p.actionTime q) = some nd →
      (nd.record.target y = none ∨ nd.record.target y = some (heightView p C).T_h.root) ∧
      nd.record.timeout y = false ∧
      (nd.record.lock y = none ∨ nd.record.lock y = some (heightView p C).T_h.root) ∧
      nd.record.target (y + 1) = none ∧ nd.record.timeout (y + 1) = false ∧
      nd.record.lock (y + 1) = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote (y + 1) T timeout := by
  have h := FGCompose.high_record_guards_and_fresh_at_action
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
    (d7f_timing_laws p) hs z r C hz ((d7f_source_eq p c E rho z r).symm ▸ hsource)
    y hheight hy q x hx
    (by simpa only [d7f_row_eq, d7f_rowHeight_eq] using hbefore)
  dsimp only [FGCompose.HighRecordFresh, d7f_observations, d7f_timing] at *
  simpa only [FGCompose.HighRecordGuard_W, fgsaSafetyReads_def p c, d7f_postClock_eq,
    and_assoc] using h

private theorem recordInv_honest_pair (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (j : Nat) (x : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (ha : HonestRowAt p c E rho j x r wire) (hd : wire.toRow? = some a)
    (y : Nat) (T : BlockId) (hn : namedEntry a.height_pair = some (y, T))
    (hy : w.M + 1 ≤ y) :
    a.height_pair = .vote y (recordInv_entry p c E rho y) false := by
  cases hp : a.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote g U timeout =>
    rw [hp] at hn
    rw [namedEntry_def] at hn
    have he : (g, U) = (y, T) := Option.some.inj hn
    cases he
    rcases wire with ⟨auth, body⟩
    cases auth with
    | none => cases hd
    | proposer s => cases hd
    | seat label seat =>
      cases label with
      | head s => cases hd
      | fg =>
        have he := Option.some.inj hd
        have hb : body.height_pair = .vote y T timeout :=
          (congrArg Row.height_pair he).trans hp
        obtain ⟨_, _, _, _, hsend⟩ :=
          (fgsa_emitsAt_row E rho j x (p.actionTime r) ha.2.1 seat body).mp ha.2.2
        have hnwire : namedEntry body.height_pair = some (y, T) := by rw [namedEntry_def, hb]
        obtain ⟨C, hs, hc⟩ := hnames j x r _ _ ha hnwire
        obtain ⟨hroot, htimeout⟩ := recordInv_released_pair p c E rho w hh hqc j x r
          seat body ha.1 hsend (recordInv_all p c E rho w hh hqc hnames j x ha.1)
          y T timeout hb hy ⟨C, hs, (congrArg Prod.fst hc).symm,
            (congrArg Prod.snd hc).symm⟩
        rw [hroot, htimeout]

private theorem recordInv_qc_source (w : HealingWitness) (hh : THigh p c E rho w)
    (i : Nat) (z : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (C : FGBlock (Fin p.n)) (y : Nat) (T : BlockId)
    (hb : HonestRowBefore p c E rho i z r wire)
    (hs : actionSourceFG p c E rho z r = some (some C))
    (hn : namedEntry a.height_pair = some ((heightView p C).h, (heightView p C).T_h.root))
    (hp : namedEntry a.height_pair = some (y, T)) (hy : w.M + 1 ≤ y) :
    z ∈ rho.honest ∧ high p w C ∧ (heightView p C).h = y ∧
      T = (heightView p C).T_h.root ∧ T = recordInv_entry p c E rho y := by
  obtain ⟨j, _, ha⟩ := hb
  have he := Option.some.inj (hn.symm.trans hp)
  have hc : (heightView p C).h = y := congrArg Prod.fst he
  have ht : T = (heightView p C).T_h.root := (congrArg Prod.snd he).symm
  have hhigh : high p w C := by rw [high_def, hc]; exact hy
  have hentry := recordInv_entry_source p c E rho w hh z r C ha.1 hs hhigh
  rw [hc] at hentry
  exact ⟨ha.1, hhigh, hc, ht, ht.trans hentry.symm⟩

private theorem recordInv_quorum_honest [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (Q : Finset (Fin p.n)) (hQ : p.E.IsQuorum Q) :
    ∃ k ∈ Q, rho.seatOf (.base .fg) k ∈ rho.honest := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have he' : ∀ j : Fin p.n, rho.seatOf (.base .fg) j = e j := he
  let F := (Gen.V2.Duty.faulty rho).map e.symm.toEmbedding
  have hcap : p.E.toWeights.weightOf F < p.E.toWeights.q := by
    have hq : p.E.toWeights.q = Gen.Pure.qF p.n := KitFG.unit_toWeights_q p.n
    rw [hq]
    have hc : p.E.toWeights.weightOf F = (Gen.V2.Duty.faulty rho).card := by
      rw [KitFG.toWeights_weightOf]
      change (∑ _ ∈ F, (1 : Nat)) = _
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_map, F]
    rw [hc]
    exact hf.lt
  obtain ⟨k, hk, hn⟩ := Gen.Pure.quorum_honest p.E.toWeights F
    ((KitFG.isQuorum_toWeights_iff p.E Q).mpr hQ) hcap
  refine ⟨k, hk, ?_⟩
  rw [he']
  by_contra hh
  apply hn
  exact Finset.mem_map.mpr ⟨e k, by simpa [Gen.V2.Duty.faulty_def] using hh,
    e.symm_apply_apply k⟩

private theorem recordInv_decoded_height (wire : RowWire p.n) (a : Row (Fin p.n))
    (hd : wire.toRow? = some a) : wire.payload.height_pair = a.height_pair := by
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label seat =>
    cases label with
    | head s => cases hd
    | fg => exact congrArg Row.height_pair (Option.some.inj hd)

private theorem recordInv_honest_finality (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (j : Nat) (x : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (ha : HonestRowAt p c E rho j x r wire) (hd : wire.toRow? = some a)
    (fp : FinalityPair) (hf : a.finality_pair = some fp) (hy : w.M + 1 ≤ fp.height) :
    fp.target = recordInv_entry p c E rho fp.height := by
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label seat =>
    cases label with
    | head s => cases hd
    | fg =>
      have hbody : body.finality_pair = some fp :=
        (congrArg Row.finality_pair (Option.some.inj hd)).trans hf
      obtain ⟨_, _, _, _, hsend⟩ :=
        (fgsa_emitsAt_row E rho j x (p.actionTime r) ha.2.1 seat body).mp ha.2.2
      exact recordInv_released_finality p c E rho w hh hqc j x r seat body ha.1
        hsend fp hbody hy

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:876–879: every high target, progress, or finality QC in cumulative TF has one identity.
DC: INTENTIONAL: honest row origins include delayed disclosures and pre-GST writes.
There is no carrier-height guard; matchesEntry permits either timeout bit. -/
theorem ff2_stored_high_qc_identity [Fintype V] (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hOrigin : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
      ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
        wire.auth = .seat .fg a.signer ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG p c E rho z r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      ∀ i x W, HeldAt p c E rho i x W →
        (∀ y T (Q : Finset (Fin p.n)),
          w.M + 1 ≤ y → p.E.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
            a.height_pair.matchesEntry y T = true) →
          T = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = y ∧ T = (heightView p C).T_h.root ∧
            ∃ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
              a.height_pair = .vote y (entry y) false) ∧
        (∀ fp (Q : Finset (Fin p.n)), w.M + 1 ≤ fp.height → p.E.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧ a.finality_pair = some fp) →
          fp.target = entry fp.height) := by
  have horigin : ∀ i x W, FGCompose.HeldAt (fgsaCoreReads p c) E rho i x W →
      ∀ a ∈ chainRows W, ∃ (wire : RowWire p.n) (r : Nat),
        (fgsaSafetyReads p c).decode wire = some a ∧ (d7f_wire p c).signer wire = some a.signer ∧
        ∀ z, FGCompose.RowSigner (fgsaSafetyReads p c) rho (d7f_wire p c).signer wire z →
          z ∈ rho.honest → FGCompose.HonestRowBefore (fgsaSafetyReads p c) E rho
            (d7f_timing p) i z r wire := by
    intro i x W hW a ha
    have hW' : HeldAt p c E rho i x W := by
      dsimp only [FGCompose.HeldAt, HeldAt, storeAt] at *
      simpa only [d7f_fg] using hW
    obtain ⟨wire, r, hd, hauth, ho⟩ := hOrigin i x W hW' a ha
    refine ⟨wire, r, ?_, ?_, ?_⟩
    · rw [fgsaSafetyReads_def p c]; exact hd
    · change d7f_signer p wire = some a.signer
      exact (d7f_signer_seat p wire a.signer).mpr hauth
    · intro z hz hhonest
      have hz' : RowSigner p c rho wire z := (d7f_signer_eq p c rho wire z).mp hz
      obtain ⟨j, hji, hj⟩ := ho z hz' hhonest
      exact ⟨j, hji, (d7f_row_eq p c E rho j r z wire).symm ▸ hj⟩
  have h := FGCompose.ff2_stored_high_qc_identity
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
    (d7f_fault_weight p c rho hL hf) horigin
  simp only [d7f_source_eq, d7f_high] at h
  dsimp only [FGCompose.HeldAt, HeldAt, d7f_observations, d7f_point, storeAt] at *
  simpa only [d7f_fg] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:876–879: selected high progress, target, and finality QCs have one identity.
DC: INTENTIONAL: the earlier target QC supplies the finality identity.
All prefixes and all cumulative TF blocks are included; the record induction
also makes the selected honest progress witness a target. -/
theorem ff2_high_qc_identity (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG p c E rho z r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
        (∀ y X (Q : Finset (Fin p.n))
            (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
          w.M + 1 ≤ y → y < (heightView p W).h →
          FGBlock.Preceq X W → (heightView p X).h = y → p.E.IsQuorum Q →
          (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
            (rows k).2.signer = k ∧
            (rows k).2.height_pair.matchesEntry y X.root = true) →
          X.root = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = y ∧ X.root = (heightView p C).T_h.root ∧
            ∃ k ∈ Q, (rows k).2.height_pair = .vote y (entry y) false) ∧
        (w.M + 1 ≤ (heightView p W).h_j →
          (heightView p W).J.root = entry (heightView p W).h_j ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = (heightView p W).h_j ∧
            (heightView p W).J.root = (heightView p C).T_h.root) ∧
        (w.M + 1 ≤ (finalityView p W).h_F →
          (finalityView p W).F.root = entry (finalityView p W).h_F ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = (finalityView p W).h_F ∧
            (finalityView p W).F.root = (heightView p C).T_h.root) := by
  have h := FGCompose.ff2_high_qc_identity
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames) (d7f_store p c E rho)
  simp only [d7f_source_eq, d7f_high] at h
  dsimp only [d7f_observations, d7f_point, storeAt] at *
  simpa only [d7f_fg] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:876–879,917–921: a high contest is impossible at every honest prefix.
DC: INTENTIONAL: QC identity covers every stored contest witness, including
blocks disclosed late in cumulative TF. -/
theorem ff2_no_high_contest (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
      let R := FGSA.controls p (storeAt p c E rho i x)
      R.contest = true → R.H ≤ w.M + 1 := by
  have h := FGCompose.ff2_no_high_contest
    (d7f_chain p c E rho w hh) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hqc) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
    (d7f_store p c E rho) (d7f_observation_laws p c) (d7f_roots p c E rho)
  dsimp only [d7f_observations, d7f_point, storeAt] at *
  simpa only [] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: the three high record guards used by K-MID and K-ROWS.
DC: INTENTIONAL: this predicate only names the proved record fields. -/
abbrev HighRecordGuard_W {n : Nat} (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) : Prop :=
  (Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some U.root)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: the equation for the high record guard.
DC: INTENTIONAL: the three durable record fields. -/
theorem HighRecordGuard_W_def {n : Nat} (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) :
    HighRecordGuard_W Λ y U =
      ((Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
        (Λ.lock y = none ∨ Λ.lock y = some U.root)) :=
  FGCompose.HighRecordGuard_W_def Λ y U

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:841–879: FF2 through the K-ROWS plan's common telescope, without A or m.
DC: INTENTIONAL: the thin adapter uses H1 over all rounds and QC origin. -/
theorem ff2_high_record_guards [Fintype V] (G ΔF : Time) (pt : KernelPt)
    (_hδ : p.δt = 2 * p.R) (hK : KernelPrem_W p c G ΔF E rho pt)
    (_hFG : FGFoundation p c E rho) (_hCert : RCert p c E rho)
    (hQC : RQCOrigin p c E rho) (_hXing : RXing p c E rho)
    (_hTiming : TimingContract p c E rho)
    (hNames : ∀ j x r a, HonestRowAt p c E rho j x r a →
      ∃ e C H, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some H) ∧
        Block.Preceq (eraseFG C) H ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    ∀ a r C, a ∈ rho.honest → actionSourceFG p c E rho a r = some (some C) →
      high p pt.w C → ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
        HighRecordGuard_W (V2.D.Run.stateBefore E rho i x).record
          (heightView p C).h (heightView p C).T_h := by
  have hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) := by
    intro j x r a e ha he
    obtain ⟨e', C, H, he', hs, hc, _⟩ := hNames j x r a ha
    have heq := Option.some.inj (he.symm.trans he')
    exact ⟨C, hs, heq.trans hc⟩
  have h := FGCompose.ff2_high_record_guards
    (d7f_chain p c E rho pt.w hK.input.t.h1) (fgCertificateLaws p) (d7f_reflect p c)
    (d7f_qc p c E rho hQC) (d7f_head p c E rho) (fgsaSafetyClientLaws p c)
    (d7f_emission p c E rho) (d7f_own p c E rho) (d7f_names p c E rho hnames)
  dsimp only [d7f_point, d7f_observations, FGCompose.high] at *
  simpa only [d7f_source_eq, high_def, fgsaSafetyReads_def p c,
    FGCompose.HighRecordGuard_W, HighRecordGuard_W] using h

end AvailableChain.FGSA.Run
