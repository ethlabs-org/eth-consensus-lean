module
public import AvailableChainFGSAProofs.Proofs.Finality.Middle
public import AvailableChainFGSAProofs.Proofs.Finality.RecordInv -- shake: keep (record guards)

public import AvailableChainFGCompose.Proofs.Finality.RowsRecords

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

private def d7a4rr_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a4rr_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a4rr_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a4rr_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a4rr_w_Old := FGSA.Window.State
private abbrev d7a4rr_w_New := SimplexFG.Window.State

private def d7a4rr_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a4rr_w_toWindow {V : Type} (w : d7a4rr_w_Old V) : d7a4rr_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a4rr_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a4rr_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a4rr_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a4rr_w_state_eq {V : Type} (w : d7a4rr_w_Old V) :
    d7a4rr_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a4rr_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a4rr_w_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a4rr_w_toEntry e).j = e.j ∧ (d7a4rr_w_toEntry e).X = e.X ∧ (d7a4rr_w_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a4rr_w_state_fields {V : Type} (w : d7a4rr_w_Old V) :
    (d7a4rr_w_toWindow w).L = w.L ∧ (d7a4rr_w_toWindow w).s = w.s ∧
    (d7a4rr_w_toWindow w).h = w.h ∧ (d7a4rr_w_toWindow w).T_h = w.T_h ∧
    (d7a4rr_w_toWindow w).target_participation = w.target_participation ∧
    (d7a4rr_w_toWindow w).progress = w.progress ∧ (d7a4rr_w_toWindow w).W = w.W.map
      d7a4rr_w_toEntry ∧
    (d7a4rr_w_toWindow w).J = w.J ∧ (d7a4rr_w_toWindow w).h_j = w.h_j ∧
    (d7a4rr_w_toWindow w).F = w.F ∧ (d7a4rr_w_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a4rr_w_initial_eq {V : Type} :
    d7a4rr_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a4rr_w_foldRow_eq (w : d7a4rr_w_Old V) (a : Row V) :
    d7a4rr_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a4rr_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a4rr_w_toEntry =
      (w.W.map d7a4rr_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a4rr_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a4rr_w_state_eq] using
        congrArg (fun es => ({ d7a4rr_w_toWindow w with W := es } : d7a4rr_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a4rr_w_state_eq] <;> rw [bits] <;> simp_all [d7a4rr_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a4rr_w_rows_eq (rs : List (Row V)) (w : d7a4rr_w_Old V) :
    d7a4rr_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a4rr_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a4rr_w_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rr_w_advance_eq (w : d7a4rr_w_Old V) :
    d7a4rr_w_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a4rr_w_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rr_w_greatest_eq (E : Electorate V) (w : d7a4rr_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a4rr_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a4rr_w_toWindow w) := by
  classical
  let oldStep := fun (best : Option (FGSA.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  let newStep := fun (best : Option (SimplexFG.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have step (best) (e) :
      (oldStep best e).map d7a4rr_w_toEntry = newStep (best.map d7a4rr_w_toEntry)
      (d7a4rr_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a4rr_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a4rr_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a4rr_w_toEntry =
        (es.map d7a4rr_w_toEntry).foldl newStep (best.map d7a4rr_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a4rr_w_toWindow w) =
      (w.W.map d7a4rr_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rr_w_finalize_eq (E : Electorate V) (w : d7a4rr_w_Old V) :
    d7a4rr_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a4rr_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a4rr_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a4rr_w_state_eq, d7a4rr_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a4rr_w_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a4rr_w_toEntry =
      (es.map d7a4rr_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a4rr_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a4rr_w_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rr_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a4rr_w_Old V) :
    d7a4rr_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a4rr_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a4rr_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a4rr_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a4rr_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a4rr_w_state_eq, d7a4rr_w_entry_eq, List.map_drop]

private theorem d7a4rr_w_transition_eq (p : Params) (K : Nat) (w : d7a4rr_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a4rr_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a4rr_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a4rr_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a4rr_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a4rr_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a4rr_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a4rr_w_toWindow where
  initial := d7a4rr_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a4rr_w_transition_eq p K

private theorem d7a4rr_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a4rr_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a4rr_w_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a4rr_w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a4rr_w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a4rr_w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a4rr_w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7a4rr_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7a4rr_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7a4rr_timing p) where
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

private theorem d7a4rr_action_eq (p : Params) (q : Nat) :
    (d7a4rr_timing p).action q = p.actionTime q := rfl

private def d7a4rr_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def d7a4rr_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a4rr_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a4rr_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a4rr_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rr_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rr_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rr_decode p ha]
    rfl

private theorem d7a4rr_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a4rr_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

private theorem d7a4rr_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a4rr_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a4rr_reads_eq]; rfl

private theorem d7a4rr_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a4rr_reads_eq]
  rfl

private def d7a4rr_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7a4rr_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (fgsaSafetyReads p c) (d7a4rr_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7a4rr_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (fgsaSafetyReads p c) (d7a4rr_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7a4rr_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

omit [DecidableEq V] in
private theorem d7a4rr_holder (i : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem d7a4rr_faulty_eq : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [d7a4rr_holder]
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private def d7a4rr_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7a4rr_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7a4rr_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private def d7a4rr_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7a4rr_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7a4rr_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7a4rr_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7a4rr_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, msg⟩
  cases auth with
  | none => cases hd
  | seat label i =>
    cases label with
    | base label => cases label <;> cases msg <;> cases hd
    | prop v =>
      cases msg with
      | head Q => cases hd
      | row body => cases hd
      | proposal M =>
        have he := Input.block.inj (Option.some.inj hd)
        cases he.2
        rfl

private theorem d7a4rr_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
    (hem : V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
      (V2.D.proposalTime (fgsaInterface p c) s)) (hpay : o.payload = .proposal N) :
    (toWire p o).decode = some (.block s N) := by
  obtain ⟨j, hj, hem⟩ := hem
  change rho.events[j]? = some (.tick _ (SA.proposalTime p.toParams s)) at hj
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨auth, m⟩ := o
  dsimp only at hpay
  subst m
  cases auth with
  | none =>
    change (⟨.none, _⟩ : Obj p) ∈ (if E.awake _ _ then
      (duties p _).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) _).filterMap
        (fun i => ((fgsa p c).act ((fgsa p c).clock _ _) d (rho.input _ _)).map
          (fun m => ⟨.seat (RunDuty.signLabel d) i, m⟩))) ++ [] else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    · exact (List.not_mem_nil hem).elim
  | seat label seat =>
    obtain ⟨_, _, d, hl, ht, hm⟩ :=
      (V2.D.Engine.mem_tick_seat_iff E rho _ _ _ label seat _).mp hem
    cases d with
    | headAction v =>
      change (if joinedNow p _ then some (Msg.head _) else none) = some (.proposal N) at hm
      split_ifs at hm; cases hm
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
      obtain ⟨body, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    | propAction s' =>
      have hss : s' = s := by
        change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
        have hΔ : (0 : Int) < p.Δ := p.deltaPos
        have he : (s' : Int) = s := by nlinarith
        exact_mod_cast he
      subst s'
      change RunLabel.prop s = label at hl
      subst label
      rfl

private theorem d7a4rr_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4rr_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7a4rr_proposal_payload p o s N ((d7a4rr_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7a4rr_decodeProposal_iff p o s N).mpr
      (d7a4rr_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7a4rr_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a4rr_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a4rr_signer; simp
  | proposer s => delta d7a4rr_signer; simp
  | seat label j => cases label <;> delta d7a4rr_signer <;> simp

private theorem d7a4rr_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7a4rr_wire p c).heightPair) (d7a4rr_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] in
private theorem d7a4rr_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7a4rr_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a4rr_signer_iff, d7a4rr_holder]

private theorem d7a4rr_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4rr_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  rw [TRowsReceipt_def]
  delta FGCompose.TRowsReceipt FGCompose.HeldBefore HeldBefore
  simp only [d7a4rr_row_eq, d7a4rr_reads_eq]
  rfl

private theorem d7a4rr_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.ValidForParent E rho (fgsaInterface p c) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) s Q a =
      ValidForParent p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hread, hparent, hrow⟩
    exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · rintro ⟨st, H, hread, hparent, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, H, hnd, hparent, hrow⟩

private theorem d7a4rr_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.HeightMatch E rho (fgsaInterface p c)
      (fun a : RowWire p.n => FGCompose.namedEntry a.payload.height_pair)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root)) s Q a =
      HeightMatch p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hread, hparent, hrow⟩
    exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · rintro ⟨st, H, hread, hparent, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, H, hnd, hparent, hrow⟩

private abbrev d7a4rr_Batch (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4rr_observations p c)
    (d7a4rr_timing p) E rho (fgsaInterface p c) (d7a4rr_wire p c) p.E
    (d7a4rr_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF (d7a4rr_kind k) q y U X

private def d7a4rr_ac (w : HealingWitness) : FGCompose.FGACServiceReads V where
  honest x := x ∈ rho.honest
  proposal := HonestProposal E rho (fgsaInterface p c)
  proposalTime := SA.proposalTime p.toParams
  voteTime := SA.voteTime p.toParams
  gateTime := SA.gateTime p.toParams
  gateLabel q := q * p.R
  actionHeadLabel q := q * p.R + 1
  actionTime := p.actionTime
  proposalScope s _ := w.sStar + 2 ≤ s
  sourceScope x r B := ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
    eraseFG C = B ∧ high p w C
  headScope x s := joinedAt p E rho x s (SA.voteTime p.toParams s)
  gateScope x s := confirmedReaderAtIdx p c E rho x
    (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s)
  actionScope x q := ∃ nd, postClock E rho x (p.actionTime q) = some nd
  headAtLabel := headAtLabel p c E rho
  actionHead x q := (postClock E rho x (p.actionTime q)).map
    (fun nd => (fgBlockOf nd.st (fgHead p nd.st)).map eraseFG)
  gate := gateResult p c E rho
  source := actionSource p c E rho
  parent := proposalHeadAt p c E rho
  gateFloor x s := (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F)
  frame x q B := ∀ nd, postClock E rho x (p.actionTime q) = some nd →
    ∃ D, eraseFG D = B ∧ D ∈ nd.st.fg.TF ∧
      FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h
  below := Block.Preceq

private theorem d7a4rr_honestProposal_eq (s : Slot) (Q : Block) :
    FGCompose.HonestProposal E rho (fgsaInterface p c) s Q =
      HonestProposal E rho (fgsaInterface p c) s Q := rfl

private theorem d7a4rr_opening_eq (s : Slot) (A : Block) (X : FGBlock (Fin p.n)) :
    FGCompose.OpeningCarrier_W (d7a4rr_decodeProposal p) NamedProposal.erase NamedProposal.rows
      (fun nd : Node p => FGSA.parentFG nd.st) FGSA.fgBlock E rho (fgsaInterface p c)
      s A X = OpeningCarrier_W p c E rho s A X := by
  apply propext
  rw [OpeningCarrier_W_def]
  constructor
  · rintro ⟨o, N, nd, Par, he, hN, hd, hnd, hpar, hfg⟩
    refine ⟨o, N, nd.st, Par, he, hN, (d7a4rr_decodeProposal_iff p o s N).mp hd, ?_, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _
    rw [hnd]
    rfl
  · rintro ⟨o, N, st, Par, he, hN, hd, hst, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _ at hst
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨o, N, nd, Par, he, hN, (d7a4rr_decodeProposal_iff p o s N).mpr hd, hnd, hpar, hfg⟩

private theorem d7a4rr_exact (w : HealingWitness) (s : Slot) (Q : Block)
    (h : ExactService p c E rho s Q) :
    FGCompose.KernelExactService (d7a4rr_ac p c E rho w) rho.horizon s Q := by
  refine ⟨h.1, ?_⟩
  intro hh x hx hc
  have hgate := h.2 hh x hx hc
  exact ⟨hgate.1, hgate.2.2.2.2⟩

private theorem d7a4rr_batch_to [Fintype V] (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) (h : BatchPrem p c E rho ΔF k q y U X) :
    d7a4rr_Batch p c E rho ΔF k q y U X := by
  refine ⟨h.base.valid.toScheduleWellFormed, ?_, h.deltaF,
    (d7a4rr_receipt_eq p c E rho ΔF).mpr h.rowsReceipt, h.horizon, ?_, h.after,
    ?_, h.entry, h.path, ?_⟩
  · rw [d7a4rr_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  · simpa only [d7a4rr_carrier_eq, d7a4rr_reads_eq, fgsaSafetyReads_def] using h.carrier
  · simp only [d7a4rr_holder]
    obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mp (hh hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, (d7a4rr_row_eq p c E rho j r _ a).mpr ha,
      (d7a4rr_signer_iff p a i).mpr hsign, (d7a4rr_namesEntry p c k a y U).mpr hn, ht, htime,
      ?_, ?_⟩
    · rw [d7a4rr_reads_eq]
      exact (d7a4rr_validParent_eq p c E rho _ _ a).mpr hv
    · rw [d7a4rr_reads_eq]
      exact (d7a4rr_heightMatch_eq p c E rho _ _ a).mpr hm
  · simp only [d7a4rr_holder]
    intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mpr hi) W hW
      (by simpa only [d7a4rr_rowNames] using hr)

private abbrev d7a4rr_Middle (ΔF : Time) (pt : KernelPt) (A : Block) :=
  FGCompose.KernelMiddleWitness_W (fgsaCoreReads p c) (fgsaSafetyReads p c)
    (d7a4rr_observations p c) (d7a4rr_timing p) E rho (fgsaInterface p c) (d7a4rr_wire p c) p.E
    (d7a4rr_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) FGSA.fgBlock RowWire.valid
    (d7a4rr_ac p c E rho pt.w) p.cfg p.K_W ΔF (d7a4rr_point p pt.w) ⟨pt.r⟩ A

private theorem d7a4rr_fg (nd : (fgsa p c).State) : ((fgsaCoreReads p c).core nd).fg = nd.st.fg :=
    by
  rw [d7a4rr_reads_eq p c]

private theorem d7a4rr_erase (C : FGBlock (Fin p.n)) :
    (fgsaCoreReads p c).erase C = eraseFG C := by
  rw [d7a4rr_reads_eq p c]

private theorem d7a4rr_roundSlots_eq : (d7a4rr_timing p).roundSlots = p.R := rfl

omit [DecidableEq V] in
private theorem d7a4rr_cut_eq (t : Time) : FGCompose.afterTicksIdx rho t =
    afterTicksIdx rho t := rfl

private theorem d7a4rr_storeAt_eq (i : Nat) (x : V) :
    storeAt p c E rho i x = (V2.D.Run.stateBefore E rho i x).st := rfl

private theorem d7a4rr_chain_eq [Fintype V] (X : FGBlock (Fin p.n)) (cut : Time) :
    FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho X cut =
      ChainRowsBefore p c E rho X cut := by rw [d7a4rr_reads_eq]; rfl

private def d7a4rr_middle_to [Fintype V] (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) : d7a4rr_Middle p c E rho ΔF pt A where
  A₀ := m.A₀
  B := m.B
  U := m.U
  X_D := m.X_D
  cD := m.cD
  d := m.d
  opening := m.opening
  eraseA := by simpa only [d7a4rr_reads_eq] using m.eraseA
  carrierA := by
    have h := m.carrierA
    exact (d7a4rr_opening_eq p c E rho _ _ _).mpr h
  carrierB := by
    have h := m.carrierB
    rw [d7a4rr_erase]
    exact (d7a4rr_opening_eq p c E rho _ _ _).mpr h
  carrierD := by
    have h := m.carrierD
    rw [d7a4rr_erase]
    exact (d7a4rr_opening_eq p c E rho _ _ _).mpr h
  honestB :=
    by simpa only [d7a4rr_erase, d7a4rr_honestProposal_eq, d7a4rr_roundSlots_eq] using m.honestB
  honestD := by simpa only [d7a4rr_erase, d7a4rr_honestProposal_eq] using m.honestD
  slotA := m.slotA
  slotB := m.slotB
  slotD := m.slotD
  earlySlot := m.earlySlot
  heightA := m.heightA
  highA := m.highA
  heightB := m.heightB
  entryB := m.entryB
  freshEntry := m.freshEntry
  strictAU := m.strictAU
  pathUB := m.pathUB
  freshSlot := m.freshSlot
  parentAB := m.parentAB
  parentBD := m.parentBD
  sourceA := by simpa only [d7a4rr_source_eq] using m.sourceA
  sourceB := by simpa only [d7a4rr_source_eq] using m.sourceB
  serviceD := by
    rw [d7a4rr_erase]
    exact d7a4rr_exact p c E rho pt.w _ _ m.serviceD
  heightD := m.heightD
  justifiedD := m.justifiedD
  justifiedHeightD := m.justifiedHeightD
  pendingD := by
    rw [← d7a4rr_w_derive_eq]
    exact m.pendingD
  retainedD := (d7a4rr_w_retained_eq p _ _ _).mpr m.retainedD
  noFirstHeight := by
    simpa only [d7a4rr_row_eq, d7a4rr_rowHeight_eq, d7a4rr_event_eq, d7a4rr_action_eq]
      using m.noFirstHeight
  noSecondHeight := by
    simpa only [d7a4rr_row_eq, d7a4rr_rowHeight_eq, d7a4rr_event_eq, d7a4rr_action_eq]
      using m.noSecondHeight
  noEarlyFinality := by
    simpa only [d7a4rr_row_eq, d7a4rr_finHeight_eq, d7a4rr_event_eq, d7a4rr_action_eq]
      using m.noEarlyFinality
  chainA := by simpa only [d7a4rr_chain_eq, d7a4rr_action_eq] using m.chainA
  chainB := by simpa only [d7a4rr_chain_eq, d7a4rr_action_eq] using m.chainB
  chainD := by simpa only [d7a4rr_chain_eq, d7a4rr_action_eq] using m.chainD
  freshD := {
    schedule := m.freshD.base.valid.toScheduleWellFormed
    fault_weight := by
      rw [d7a4rr_faulty_eq]
      exact kmid_faulty_weight p c E rho m.freshD.base m.freshD.faultQ
    cut := m.freshD.cut
    early := m.freshD.early
    rows := by simpa only [d7a4rr_chain_eq] using m.freshD.rows
    noNextRow := by
      simpa only [d7a4rr_row_eq, d7a4rr_rowHeight_eq, d7a4rr_event_eq, d7a4rr_action_eq]
        using m.freshD.noNextRow
    noFinRow := by
      simpa only [d7a4rr_row_eq, d7a4rr_finHeight_eq, d7a4rr_event_eq, d7a4rr_action_eq]
        using m.freshD.noFinRow }
  noMixedD := m.noMixedD
  batchB := fun hp => d7a4rr_batch_to p c E rho ΔF .target _ _ _ _ (m.batchB hp)
  batchD := fun hp => d7a4rr_batch_to p c E rho ΔF .target _ _ _ _ (m.batchD hp)
  targetsB := by
    intro x hx
    obtain ⟨j, a, ha, hc, hn⟩ := m.targetsB x hx
    exact ⟨j, a, (d7a4rr_row_eq p c E rho j _ x a).mpr ha,
      (d7a4rr_complete_eq p c rho x a).mpr hc,
      (d7a4rr_namesEntry p c .target a _ _).mpr hn⟩
  actionsInRun := m.actionsInRun
  capThroughBAction := fun i x W hi hcut hh =>
    m.capThroughBAction i x W hi hcut ((d7a4rr_held_eq p c E rho i x W).mp hh)
  capThroughFinalAction := fun i x W hi hcut hh =>
    m.capThroughFinalAction i x W hi hcut ((d7a4rr_held_eq p c E rho i x W).mp hh)
  finalityThroughFinalAction := fun i x W hi hcut hh =>
    m.finalityThroughFinalAction i x W hi hcut ((d7a4rr_held_eq p c E rho i x W).mp hh)
  heldDAtFinalAction := by
    simpa only [d7a4rr_fg, d7a4rr_storeAt_eq, d7a4rr_action_eq, d7a4rr_cut_eq]
      using m.heldDAtFinalAction
  heldAAtEnd := by
    simpa only [d7a4rr_fg, d7a4rr_storeAt_eq] using m.heldAAtEnd

private def d7a4rr_f_stored_carrier (p : Params) (nd : Node p) (B : FGBlock (Fin p.n))
    (wire : RowWire p.n) : Prop :=
  ∃ s N, N.erase = eraseFG B ∧
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧ wire ∈ N.rows

private def d7a4rr_f_source_service (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (y : V) (r : Nat) (C : FGBlock (Fin p.n)) : Prop :=
  ∃ G, gateResult p c E rho y (r * p.R) = some (some G) ∧
    Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)

private theorem d7a4rr_f_postClock_eq (x : V) (t : Time) :
    FGCompose.postClock E rho x t = postClock E rho x t :=
  (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1.symm

private theorem d7a4rr_f_entry_eq (a : NamedHeightPair) : FGCompose.namedEntry a = namedEntry a :=
    by
  cases a <;> rfl

private theorem d7a4rr_f_chain (w : HealingWitness) (h : THigh p c E rho w) (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (d7a4rr_observations p c)
      (d7a4rr_timing p) E rho (d7a4rr_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [d7a4rr_reads_eq p c] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem d7a4rr_f_reflect (A B : FGBlock (Fin p.n))
    (h : Block.Preceq ((fgsaCoreReads p c).erase A) ((fgsaCoreReads p c).erase B)) :
    FGBlock.Preceq A B := by
  rw [d7a4rr_reads_eq p c] at h
  exact eraseFG_preceq_iff.mp h

private theorem d7a4rr_f_qc (h : RQCOrigin p c E rho) :
    FGCompose.RQCOrigin (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7a4rr_observations p c) (d7a4rr_timing p) (d7a4rr_f_stored_carrier p)
      (d7a4rr_f_source_service p c E rho) p.E := by
  have heq : FGCompose.RQCOrigin (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (d7a4rr_observations p c) (d7a4rr_timing p) (d7a4rr_f_stored_carrier p)
      (d7a4rr_f_source_service p c E rho) p.E = RQCOrigin p c E rho := by
    dsimp only [FGCompose.RQCOrigin, RQCOrigin, d7a4rr_f_stored_carrier, d7a4rr_f_source_service]
    simp only [d7a4rr_fg, d7a4rr_source_eq, fgsaSafetyReads_def p c, exists_and_left]
    rfl
  exact heq.symm ▸ h

private theorem d7a4rr_f_head :
    FGCompose.HighRecordHead (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a4rr_observations p c) E rho := by
  intro i x t _hx
  dsimp only [d7a4rr_observations]
  rw [d7a4rr_reads_eq p c, fgsaSafetyReads_def p c]
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

private theorem d7a4rr_f_emission :
    FGCompose.HighRecordEmission (fgsaSafetyReads p c) (d7a4rr_timing p) E rho p.E p.cfg := by
  intro j x r a u ha hd
  rw [d7a4rr_row_eq] at ha
  rw [fgsaSafetyReads_def p c] at hd ⊢
  rw [d7a4rr_decode p hd] at ha
  obtain ⟨_, _, _, _, hsend⟩ := (fgsa_emitsAt_row E rho j x _ ha.2.1 u.signer
    (.vote ⟨u.height_pair, u.finality_pair⟩)).mp ha.2.2
  exact (fgsa_attest_decode _ _ u.signer _ hsend).symm

private theorem d7a4rr_f_own_row (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
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

private theorem d7a4rr_f_own :
    FGCompose.HighRecordOwnOrigin (fgsaSafetyReads p c) (d7a4rr_timing p) E rho := by
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
          obtain ⟨r, hj, hem, _⟩ := d7a4rr_f_own_row p c E rho j x seat body ho
          refine ⟨r, ⟨.seat .fg seat, body⟩, ?_, ?_⟩
          · rw [d7a4rr_row_eq]; exact ⟨hx, hj, hem⟩
          · rw [fgsaSafetyReads_def p c]; exact hd

private theorem d7a4rr_f_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a4rr_observations p c) (d7a4rr_timing p) E rho (d7a4rr_wire p c) := by
  intro j x r a entry ha hn
  rw [d7a4rr_row_eq] at ha
  change FGCompose.namedEntry a.payload.height_pair = some entry at hn
  rw [d7a4rr_f_entry_eq] at hn
  obtain ⟨C, hs, he⟩ := h j x r a entry ha hn
  exact ⟨C, (d7a4rr_source_eq p c E rho x r).symm ▸ hs, he⟩

end

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} {pt : KernelPt} {A : Block}
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

omit [Fintype V] in
/-- Paper 22:1224–1225,1259–1263: an event-time cut bounds earlier action rows.
DC: INTENTIONAL: the generic cut is supplied by K-MID at height d+2. -/
theorem rowsPrem_earlier_height (q y : Nat)
    (hcut : ∀ j x r a h t, HonestRowAt p c E rho j x r a → rowHeight a = some h →
      y ≤ h → eventTime rho j = some t → p.actionTime q ≤ t) :
    ∀ j x r a h, r < q →
      HonestRowAt p c E rho j x r a → rowHeight a = some h → h < y := by
  have result := FGCompose.rowsPrem_earlier_height
    (S := fgsaSafetyReads p c) (D := d7a4rr_wire p c) (E := E) (rho := rho)
    (d7a4rr_timing_laws p) q y
    (by simpa only [d7a4rr_row_eq, d7a4rr_rowHeight_eq, d7a4rr_event_eq,
      d7a4rr_action_eq] using hcut)
  simpa only [d7a4rr_row_eq, d7a4rr_rowHeight_eq] using result

/-- Paper 22:841–879,1256–1263: P6 supplies the seven K-ROWS record guards.
DC: INTENTIONAL: FF2 at the actual B source and strict own history at height d+2. -/
theorem rowsPrem_action_record (hK : KernelPrem_W p c G ΔF E rho pt)
    (hQC : RQCOrigin p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      (nd.record.target (m.d + 1) = none ∨ nd.record.target (m.d + 1) = some m.U.root) ∧
      nd.record.timeout (m.d + 1) = false ∧
      (nd.record.lock (m.d + 1) = none ∨ nd.record.lock (m.d + 1) = some m.U.root) ∧
      nd.record.target (m.d + 2) = none ∧ nd.record.timeout (m.d + 2) = false ∧
      nd.record.lock (m.d + 2) = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote (m.d + 2) T timeout := by
  have result := FGCompose.rowsPrem_action_record (d7a4rr_middle_to p c E rho ΔF pt A m)
    (d7a4rr_f_chain p c E rho pt.w hK.input.t.h1) (fgCertificateLaws p)
    (d7a4rr_f_reflect p c) (d7a4rr_f_qc p c E rho hQC) (d7a4rr_f_head p c E rho)
    (fgsaSafetyClientLaws p c) (d7a4rr_f_emission p c E rho) (d7a4rr_f_own p c E rho)
    (d7a4rr_f_names p c E rho hNames) (d7a4rr_timing_laws p)
    hK.set.base.valid.toScheduleWellFormed
  intro x nd hx hnd
  have guards := result x nd hx hnd
  dsimp only [d7a4rr_middle_to] at guards
  rw [fgsaSafetyReads_def p c] at guards
  change FGCompose.HighRecordGuard_W nd.record (m.d + 1) m.U ∧
    FGCompose.HighRecordFresh (m.d + 2) nd.record at guards
  exact ⟨guards.1.1, guards.1.2.1, guards.1.2.2, guards.2⟩

end AvailableChain.FGSA.Run
end
