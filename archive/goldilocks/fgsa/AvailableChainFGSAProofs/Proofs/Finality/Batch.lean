module
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads
public import AvailableChainFGSARun.Proofs.WindowExclusion
public import AvailableChainFGSAClaims.Statements.Fold -- shake: keep (FinRowNames statement)

public import AvailableChainFGSAProofs.Proofs.Finality.RowsRecords -- shake: keep (record wrappers)
public import AvailableChainFGCompose.Proofs.Finality.Batch

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGSA.Window (CoveredW)

private def d7a4b_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a4b_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a4b_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a4b_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a4b_w_Old := FGSA.Window.State
private abbrev d7a4b_w_New := SimplexFG.Window.State

private def d7a4b_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a4b_w_toWindow {V : Type} (w : d7a4b_w_Old V) : d7a4b_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a4b_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a4b_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a4b_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a4b_w_state_eq {V : Type} (w : d7a4b_w_Old V) :
    d7a4b_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a4b_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a4b_w_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a4b_w_toEntry e).j = e.j ∧ (d7a4b_w_toEntry e).X = e.X ∧ (d7a4b_w_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a4b_w_state_fields {V : Type} (w : d7a4b_w_Old V) :
    (d7a4b_w_toWindow w).L = w.L ∧ (d7a4b_w_toWindow w).s = w.s ∧
    (d7a4b_w_toWindow w).h = w.h ∧ (d7a4b_w_toWindow w).T_h = w.T_h ∧
    (d7a4b_w_toWindow w).target_participation = w.target_participation ∧
    (d7a4b_w_toWindow w).progress = w.progress ∧ (d7a4b_w_toWindow w).W = w.W.map
      d7a4b_w_toEntry ∧
    (d7a4b_w_toWindow w).J = w.J ∧ (d7a4b_w_toWindow w).h_j = w.h_j ∧
    (d7a4b_w_toWindow w).F = w.F ∧ (d7a4b_w_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a4b_w_initial_eq {V : Type} :
    d7a4b_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a4b_w_foldRow_eq (w : d7a4b_w_Old V) (a : Row V) :
    d7a4b_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a4b_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a4b_w_toEntry =
      (w.W.map d7a4b_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a4b_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a4b_w_state_eq] using
        congrArg (fun es => ({ d7a4b_w_toWindow w with W := es } : d7a4b_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a4b_w_state_eq] <;> rw [bits] <;> simp_all [d7a4b_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a4b_w_rows_eq (rs : List (Row V)) (w : d7a4b_w_Old V) :
    d7a4b_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a4b_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a4b_w_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4b_w_advance_eq (w : d7a4b_w_Old V) :
    d7a4b_w_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a4b_w_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4b_w_greatest_eq (E : Electorate V) (w : d7a4b_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a4b_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a4b_w_toWindow w) := by
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
      (oldStep best e).map d7a4b_w_toEntry = newStep (best.map d7a4b_w_toEntry)
      (d7a4b_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a4b_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a4b_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a4b_w_toEntry =
        (es.map d7a4b_w_toEntry).foldl newStep (best.map d7a4b_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a4b_w_toWindow w) =
      (w.W.map d7a4b_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4b_w_finalize_eq (E : Electorate V) (w : d7a4b_w_Old V) :
    d7a4b_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a4b_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a4b_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a4b_w_state_eq, d7a4b_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a4b_w_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a4b_w_toEntry =
      (es.map d7a4b_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a4b_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a4b_w_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4b_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a4b_w_Old V) :
    d7a4b_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a4b_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a4b_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a4b_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a4b_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a4b_w_state_eq, d7a4b_w_entry_eq, List.map_drop]

private theorem d7a4b_w_transition_eq (p : Params) (K : Nat) (w : d7a4b_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a4b_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a4b_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a4b_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a4b_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a4b_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a4b_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a4b_w_toWindow where
  initial := d7a4b_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a4b_w_transition_eq p K

private theorem d7a4b_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a4b_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a4b_w_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a4b_w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a4b_w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a4b_w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a4b_w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7a4b_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7a4b_timing_eq (p : Params) : d7a4b_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private theorem d7a4b_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7a4b_timing p) where
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

private theorem d7a4b_action_eq (p : Params) (q : Nat) :
    (d7a4b_timing p).action q = p.actionTime q := rfl

private def d7a4b_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d7a4b_observations_eq : d7a4b_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

private def d7a4b_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a4b_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a4b_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a4b_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4b_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4b_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4b_decode p ha]
    rfl

private theorem d7a4b_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a4b_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

private theorem d7a4b_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a4b_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a4b_reads_eq]; rfl

private theorem d7a4b_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a4b_reads_eq]
  rfl

private theorem d7a4b_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (fgsaSafetyReads p c) (d7a4b_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7a4b_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (fgsaSafetyReads p c) (d7a4b_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7a4b_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

omit [DecidableEq V] in
private theorem d7a4b_holder (i : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem d7a4b_faulty_eq : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [d7a4b_holder]
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private def d7a4b_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7a4b_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7a4b_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private def d7a4b_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7a4b_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7a4b_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7a4b_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7a4b_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem d7a4b_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

private theorem d7a4b_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4b_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7a4b_proposal_payload p o s N ((d7a4b_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7a4b_decodeProposal_iff p o s N).mpr
      (d7a4b_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7a4b_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a4b_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a4b_signer; simp
  | proposer s => delta d7a4b_signer; simp
  | seat label j => cases label <;> delta d7a4b_signer <;> simp

private theorem d7a4b_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7a4b_wire p c).heightPair) (d7a4b_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] in
private theorem d7a4b_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7a4b_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a4b_signer_iff, d7a4b_holder]

private theorem d7a4b_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4b_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  rw [TRowsReceipt_def]
  delta FGCompose.TRowsReceipt FGCompose.HeldBefore HeldBefore
  simp only [d7a4b_row_eq, d7a4b_reads_eq]
  rfl

private theorem d7a4b_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a4b_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a4b_w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a4b_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4b_w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a4b_w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a4b_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4b_w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a4b_w_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7a4b_w_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7a4b_w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega


private theorem d7a4b_held (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a ↔ heldAtProposal p c E rho s a := by
  constructor
  · rintro ⟨nd, hn, ha⟩
    refine ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hn, rfl⟩, ?_⟩
    rw [d7a4b_reads_eq] at ha
    exact ha
  · rintro ⟨st, hs, ha⟩
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    rw [d7a4b_reads_eq]
    exact ha

private theorem d7a4b_selection (h : TRowsSelect p c E rho) :
    FGCompose.TRowsSelect (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4b_timing p)
      (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4b_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) := by
  intro s Q rows j x r a hc ha hv hh
  rcases h s Q rows j x r a ((d7a4b_carrier_eq p c E rho _ _ _).mp hc)
    ((d7a4b_row_eq p c E rho j r x a).mp ha)
    ((d7a4b_validParent_eq p c E rho _ _ _).mp hv)
    ((d7a4b_held p c E rho _ _).mp hh) with hm | hp
  · exact Or.inl hm
  · obtain ⟨st, hs, hm⟩ := hp
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact Or.inr ⟨nd, hn, hm⟩

private theorem d7a4b_occurrence (s : Slot) (Q : Block) (H : FGBlock (Fin p.n))
    (nd : Node p) (a : RowWire p.n) (u : Row (Fin p.n))
    (hn : FGCompose.proposalStateAt E rho (fgsaInterface p c) s = some nd)
    (hp : FGSA.fgBlockOf nd.st Q.parent = some H)
    (hm : a ∈ FGSA.chainWireRows nd.st Q.parent) (hd : RowWire.toRow? a = some u) :
    ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows := by
  have hs : proposalStateAt p c E rho s = some nd.st :=
    Option.map_eq_some_iff.mpr ⟨nd, hn, rfl⟩
  obtain ⟨k, hk⟩ := batch_proposal_read p c E rho s nd.st hs
  have bundle := storeBundle_postClock E rho k
    (V2.D.proposerOf rho (fgsaInterface p c) s) (V2.D.proposalTime (fgsaInterface p c) s)
  rw [hk] at hp hm
  have he := ((fgBlockOf_spec p _ bundle.cstore _ H).mp hp).2
  rw [← he] at hm
  exact rowService_chain_occurrence p _ bundle.meta H a u hd hm

private theorem d7a4b_r6w (w : Window.State (Fin p.n)) (a : Row (Fin p.n)) :
    SimplexFG.Window.r6w (d7a4b_w_toWindow w) a = Window.r6w w a := by
  cases hp : a.height_pair <;> cases hf : a.finality_pair <;>
    simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
    SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
    SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7a4b_w_state_eq, List.any_map, Function.comp_def, d7a4b_w_entry_eq, hp, hf]
  rfl

private theorem d7a4b_valid (hv : V2.D.ExecutionValid E rho) (X : FGBlock (Fin p.n))
    (parent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
      FGSA.fgBlockOf st (eraseFG X).parent = some X.parent) :
    ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
          (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W B) a = true := by
  obtain ⟨st, hs, hp⟩ := parent
  obtain ⟨k, rfl⟩ := batch_proposal_read p c E rho X.slot st hs
  have bundle := storeBundle_postClock E rho k
    (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
    (V2.D.proposalTime (fgsaInterface p c) X.slot)
  have stored := ((fgBlockOf_spec p _ bundle.cstore _ X.parent).mp hp).1
  change X.parent ∈ (clock p _ _).fg.TF at stored
  rw [clock_fg] at stored
  intro B s root body rs hb a ha
  have h := stored_chain_rowsValidW E rho hv.toDeliveryWellFormed k _ X.parent stored
    B s root body rs hb a ha
  refine ⟨h.1, ?_⟩
  rw [← d7a4b_w_derive_eq, d7a4b_r6w]
  exact h.2

private theorem d7a4b_decode_wire (a : RowWire p.n) (i : Fin p.n)
    (h : d7a4b_signer p a = some i) : ∃ u, RowWire.toRow? a = some u := by
  have ha := (d7a4b_signer_iff p a i).mp h
  cases a with
  | mk auth payload =>
    dsimp only at ha
    subst auth
    exact ⟨payload.toRow i, rfl⟩

private theorem d7a4b_child_eq (X U : FGBlock (Fin p.n)) (y : Nat) :
    FGCompose.FinalityCoveredByChild_W p.E p.cfg p.K_W X U y =
      FinalityCoveredByChild_W p X U y := by
  apply propext
  unfold FGCompose.FinalityCoveredByChild_W
  rw [← d7a4b_w_derive_eq, FinalityCoveredByChild_W_def]
  change (∃ e ∈ (Window.derive p p.K_W X.parent).W.map d7a4b_w_toEntry,
    e.j = y ∧ e.X = U ∧ ∃ Q, p.E.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ e.Q ∨ ∃ row ∈ X.rows, FGCompose.FinRowNames row i y U) ↔ _
  delta FGCompose.FinRowNames
  simp only [List.mem_map, FinRowNames_def]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hy, hU, Q, hQ, hi⟩
    exact ⟨d, hd, hy, hU, Q, hQ, hi⟩
  · rintro ⟨d, hd, hy, hU, Q, hQ, hi⟩
    exact ⟨d7a4b_w_toEntry d, ⟨d, hd, rfl⟩, hy, hU, Q, hQ, hi⟩

private def d7a4b_rowValid (w : SimplexFG.Window.State (Fin p.n))
    (a : RowWire p.n) : Bool :=
  a.toRow?.isSome && (a.toRow?.map (SimplexFG.Window.r6w w)).getD false

private theorem d7a4b_rowValid_eq (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    d7a4b_rowValid p (d7a4b_w_toWindow w) a = Window.rowValidW w a := by
  unfold d7a4b_rowValid
  rw [Window.rowValidW_def]
  cases hd : a.toRow? with
  | none => rfl
  | some row => simp only [Option.isSome_some, Option.map_some, Option.getD_some,
      Bool.true_and, d7a4b_r6w]

private theorem d7a4b_parentState (s : Slot) (B : FGBlock (Fin p.n)) :
    KitFG.Window.parentState p.E p.cfg p.K_W B s =
      d7a4b_w_toWindow (parentFoldState p s B) := by
  rw [KitFG.Window.parentState_def, ← d7a4b_w_derive_eq]
  rfl

private theorem d7a4b_batch_to [Fintype V] (ΔF : Time) (q y : Nat)
    (U X : FGBlock (Fin p.n)) (h : FinalityBatchPrem_W p c E rho ΔF q y U X) :
    FGCompose.FinalityBatchPrem_W (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a4b_timing p) E rho (fgsaInterface p c) (d7a4b_wire p c) p.E p.cfg p.K_W
      RowWire.valid
      (FGCompose.kernelCarrier (d7a4b_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) (d7a4b_rowValid p)
      ΔF q y U X := by
  refine ⟨h.base.valid.toScheduleWellFormed, ?_, h.deltaF,
    (d7a4b_receipt_eq p c E rho ΔF).mpr h.rowsReceipt, ?_, h.after, h.horizon,
    ?_, ?_, ?_, ?_⟩
  · rw [d7a4b_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  · simpa only [d7a4b_carrier_eq, d7a4b_reads_eq, fgsaSafetyReads_def] using h.carrier
  · obtain ⟨st, hs, hp⟩ := h.parent
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    simpa only [d7a4b_reads_eq] using hp
  · rw [← d7a4b_w_height_eq]
    exact h.birth
  · simpa only [d7a4b_w_retained_eq, d7a4b_w_covered_eq] using h.retainedOrCovered
  · obtain ⟨Q, hh, hq, hw⟩ := h.batch
    simp only [d7a4b_holder]
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mp (hh hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, a, ha, hc, hs, hn, hr, hheld, hv⟩ := hw i hi
    refine ⟨j, a, (d7a4b_row_eq p c E rho j q _ a).mpr ha,
      (d7a4b_complete_eq p c rho _ a).mpr hc, (d7a4b_signer_iff p a i).mpr hs,
      hn, ?_, (d7a4b_held p c E rho _ _).mpr hheld, ?_⟩
    · delta HeldBefore rowHeld at hr
      delta FGCompose.HeldBefore FGCompose.rowHeld
      simpa only [d7a4b_reads_eq, d7a4b_timing_eq] using hr
    · intro hret
      obtain ⟨hr, hv⟩ := hv ((d7a4b_w_retained_eq p _ _ _).mp hret)
      refine ⟨?_, ?_⟩
      · rw [d7a4b_parentState, d7a4b_rowValid_eq]
        exact hr
      · rw [d7a4b_reads_eq]
        exact (d7a4b_validParent_eq p c E rho _ _ _).mpr hv

end

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22 I6/R7:697–703, 715–728, 1265–1289:
a finality row sets the retained bit or is
carried.
DC: INTENTIONAL exact signed row selection and checked W history; the caller
supplies T-ROWS selection so this Finality proof does not depend on Foundations. -/
theorem finalityRow_bit_or_carried_W
    (hv : V2.D.ExecutionValid E rho) (hsel : TRowsSelect p c E rho)
    (X U : FGBlock (Fin p.n)) (y : Nat) (wireRows : List (RowWire p.n))
    (hc : HonestCarrier p c E rho X.slot (eraseFG X) wireRows)
    (hrows : X.rows = wireRows.filterMap RowWire.toRow?)
    (hparent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
      FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (e : Window.Entry (Fin p.n)) (he : e ∈ (Window.derive p p.K_W X.parent).W)
    (hej : e.j = y) (heX : e.X = U)
    (i : Fin p.n) (j r : Nat) (a : RowWire p.n)
    (ha : HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a)
    (hauth : a.auth = .seat .fg i) (hnames : FinalityNames p a y U)
    (hvalid : ValidForParent p c E rho X.slot (eraseFG X) a)
    (hheld : heldAtProposal p c E rho X.slot a) :
    i ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames p row i y U := by
  have entry : d7a4b_w_toEntry e ∈
      (SimplexFG.Window.derive p.E p.cfg p.K_W X.parent).W := by
    rw [← d7a4b_w_derive_eq]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have parent : ∃ nd, FGCompose.proposalStateAt E rho (fgsaInterface p c) X.slot = some nd ∧
      FGSA.fgBlockOf nd.st (eraseFG X).parent = some X.parent := by
    obtain ⟨st, hs, hp⟩ := hparent
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨nd, hn, hp⟩
  have result := FGCompose.finalityRow_bit_or_carried_W
    (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4b_timing p) E rho (fgsaInterface p c)
    (d7a4b_wire p c) p.E p.cfg p.K_W
    (FGCompose.kernelCarrier (d7a4b_decodeProposal p) NamedProposal.erase NamedProposal.rows)
    (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st) (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (d7a4b_selection p c E rho hsel) (d7a4b_w_nonempty p) p.kWLarge
    (by
      intro a i h
      change d7a4b_signer p a = some i at h
      rw [fgsaSafetyReads_def]
      exact d7a4b_decode_wire p a i h)
    (by
      intro s Q H nd a u hn hp hm hd
      rw [fgsaSafetyReads_def] at hd
      exact d7a4b_occurrence p c E rho s Q H nd a u hn hp hm hd)
    X U y wireRows (by
      rw [d7a4b_reads_eq]
      exact (d7a4b_carrier_eq p c E rho _ _ _).mpr hc)
    (by simpa only [fgsaSafetyReads_def] using hrows)
    (by simpa only [d7a4b_reads_eq] using parent)
    (d7a4b_valid p c E rho hv X hparent) (d7a4b_w_toEntry e) entry hej heX i j r a
    (by simpa only [d7a4b_holder, d7a4b_row_eq] using ha)
    ((d7a4b_signer_iff p a i).mpr hauth) hnames
    (by rw [d7a4b_reads_eq]; exact (d7a4b_validParent_eq p c E rho _ _ _).mpr hvalid)
    ((d7a4b_held p c E rho _ _).mpr hheld)
  revert result
  delta FGCompose.FinRowNames
  intro result
  simpa only [FinRowNames_def, d7a4b_w_entry_eq] using result

variable [Fintype V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22 I6/R7:697–703, 715–728, 1265–1289: a finality batch gives prior parent coverage
or quorum coverage of the same retained entry by the child.
DC: INTENTIONAL W coverage separates the covered and retained cases; T-ROWS
selection is an explicit input for later discharge in Assembly. -/
theorem finalityBatchCoverage_W_of_tRowsSelect (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : FinalityBatchPrem_W p c E rho ΔF q y U X) :
    CoveredW p X.parent y U ∨ FinalityCoveredByChild_W p X U y := by
  have result := FGCompose.finalityBatchCoverage_W_of_tRowsSelect
    (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4b_timing p) E rho (fgsaInterface p c)
    (d7a4b_wire p c) p.E p.cfg p.K_W
    (FGCompose.kernelCarrier (d7a4b_decodeProposal p) NamedProposal.erase NamedProposal.rows)
    (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st) (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (d7a4b_selection p c E rho hsel) (d7a4b_w_nonempty p) p.kWLarge
    (by
      intro a i h
      change d7a4b_signer p a = some i at h
      rw [fgsaSafetyReads_def]
      exact d7a4b_decode_wire p a i h)
    (by
      intro s Q H nd a u hn hp hm hd
      rw [fgsaSafetyReads_def] at hd
      exact d7a4b_occurrence p c E rho s Q H nd a u hn hp hm hd) (d7a4b_rowValid p) RowWire.valid
    ΔF q y U X (d7a4b_batch_to p c E rho ΔF q y U X h)
    (d7a4b_valid p c E rho h.base.valid X h.parent)
  simpa only [d7a4b_w_covered_eq, d7a4b_child_eq] using result

end AvailableChain.FGSA.Run
end
