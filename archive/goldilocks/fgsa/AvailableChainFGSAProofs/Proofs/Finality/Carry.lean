module
public import AvailableChainFGSAProofs.Proofs.Finality.Batch -- shake: keep (batch wrappers)
public import AvailableChainFGSAClaims.Statements.Phases -- shake: keep (carriage statements)

public import AvailableChainFGCompose.Proofs.Finality.Carry

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGSA.Window (RetainedW CoveredW)

private def d7a4c_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a4c_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a4c_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a4c_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a4c_w_Old := FGSA.Window.State
private abbrev d7a4c_w_New := SimplexFG.Window.State

private def d7a4c_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a4c_w_toWindow {V : Type} (w : d7a4c_w_Old V) : d7a4c_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a4c_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a4c_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a4c_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a4c_w_state_eq {V : Type} (w : d7a4c_w_Old V) :
    d7a4c_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a4c_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a4c_w_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a4c_w_toEntry e).j = e.j ∧ (d7a4c_w_toEntry e).X = e.X ∧ (d7a4c_w_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a4c_w_state_fields {V : Type} (w : d7a4c_w_Old V) :
    (d7a4c_w_toWindow w).L = w.L ∧ (d7a4c_w_toWindow w).s = w.s ∧
    (d7a4c_w_toWindow w).h = w.h ∧ (d7a4c_w_toWindow w).T_h = w.T_h ∧
    (d7a4c_w_toWindow w).target_participation = w.target_participation ∧
    (d7a4c_w_toWindow w).progress = w.progress ∧ (d7a4c_w_toWindow w).W = w.W.map
      d7a4c_w_toEntry ∧
    (d7a4c_w_toWindow w).J = w.J ∧ (d7a4c_w_toWindow w).h_j = w.h_j ∧
    (d7a4c_w_toWindow w).F = w.F ∧ (d7a4c_w_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a4c_w_initial_eq {V : Type} :
    d7a4c_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a4c_w_foldRow_eq (w : d7a4c_w_Old V) (a : Row V) :
    d7a4c_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a4c_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a4c_w_toEntry =
      (w.W.map d7a4c_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a4c_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a4c_w_state_eq] using
        congrArg (fun es => ({ d7a4c_w_toWindow w with W := es } : d7a4c_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a4c_w_state_eq] <;> rw [bits] <;> simp_all [d7a4c_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a4c_w_rows_eq (rs : List (Row V)) (w : d7a4c_w_Old V) :
    d7a4c_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a4c_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a4c_w_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4c_w_advance_eq (w : d7a4c_w_Old V) :
    d7a4c_w_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a4c_w_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4c_w_greatest_eq (E : Electorate V) (w : d7a4c_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a4c_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a4c_w_toWindow w) := by
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
      (oldStep best e).map d7a4c_w_toEntry = newStep (best.map d7a4c_w_toEntry)
      (d7a4c_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a4c_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a4c_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a4c_w_toEntry =
        (es.map d7a4c_w_toEntry).foldl newStep (best.map d7a4c_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a4c_w_toWindow w) =
      (w.W.map d7a4c_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4c_w_finalize_eq (E : Electorate V) (w : d7a4c_w_Old V) :
    d7a4c_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a4c_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a4c_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a4c_w_state_eq, d7a4c_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a4c_w_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a4c_w_toEntry =
      (es.map d7a4c_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a4c_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a4c_w_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4c_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a4c_w_Old V) :
    d7a4c_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a4c_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a4c_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a4c_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a4c_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a4c_w_state_eq, d7a4c_w_entry_eq, List.map_drop]

private theorem d7a4c_w_transition_eq (p : Params) (K : Nat) (w : d7a4c_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a4c_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a4c_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a4c_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a4c_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a4c_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a4c_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a4c_w_toWindow where
  initial := d7a4c_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a4c_w_transition_eq p K

private theorem d7a4c_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a4c_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a4c_w_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a4c_w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a4c_w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a4c_w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a4c_w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7a4c_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7a4c_timing_eq (p : Params) : d7a4c_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private theorem d7a4c_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7a4c_timing p) where
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

private theorem d7a4c_action_eq (p : Params) (q : Nat) :
    (d7a4c_timing p).action q = p.actionTime q := rfl

private def d7a4c_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d7a4c_observations_eq : d7a4c_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

private def d7a4c_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a4c_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a4c_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a4c_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4c_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4c_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4c_decode p ha]
    rfl

private theorem d7a4c_heightPair (a : RowWire p.n) :
    (d7a4c_wire p c).heightPair a = a.payload.height_pair := rfl

private theorem d7a4c_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a4c_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

private theorem d7a4c_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a4c_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a4c_reads_eq]; rfl

private theorem d7a4c_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a4c_reads_eq]
  rfl

private theorem d7a4c_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (fgsaSafetyReads p c) (d7a4c_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7a4c_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (fgsaSafetyReads p c) (d7a4c_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7a4c_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

omit [DecidableEq V] in
private theorem d7a4c_holder (i : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem d7a4c_faulty_eq : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [d7a4c_holder]
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private def d7a4c_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7a4c_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7a4c_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private def d7a4c_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7a4c_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7a4c_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7a4c_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7a4c_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem d7a4c_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

private theorem d7a4c_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4c_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7a4c_proposal_payload p o s N ((d7a4c_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7a4c_decodeProposal_iff p o s N).mpr
      (d7a4c_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7a4c_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a4c_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a4c_signer; simp
  | proposer s => delta d7a4c_signer; simp
  | seat label j => cases label <;> delta d7a4c_signer <;> simp

private theorem d7a4c_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7a4c_wire p c).heightPair) (d7a4c_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] in
private theorem d7a4c_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7a4c_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a4c_signer_iff, d7a4c_holder]

private theorem d7a4c_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4c_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  rw [TRowsReceipt_def]
  delta FGCompose.TRowsReceipt FGCompose.HeldBefore HeldBefore
  simp only [d7a4c_row_eq, d7a4c_reads_eq]
  rfl

private theorem d7a4c_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a4c_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a4c_w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a4c_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4c_w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a4c_w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a4c_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4c_w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a4c_w_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7a4c_w_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7a4c_w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega


private theorem d7a4c_held (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a ↔ heldAtProposal p c E rho s a := by
  constructor
  · rintro ⟨nd, hn, ha⟩
    refine ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hn, rfl⟩, ?_⟩
    rw [d7a4c_reads_eq] at ha
    exact ha
  · rintro ⟨st, hs, ha⟩
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    rw [d7a4c_reads_eq]
    exact ha

private theorem d7a4c_selection (h : TRowsSelect p c E rho) :
    FGCompose.TRowsSelect (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4c_timing p)
      (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4c_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) := by
  intro s Q rows j x r a hc ha hv hh
  rcases h s Q rows j x r a ((d7a4c_carrier_eq p c E rho _ _ _).mp hc)
    ((d7a4c_row_eq p c E rho j r x a).mp ha)
    ((d7a4c_validParent_eq p c E rho _ _ _).mp hv)
    ((d7a4c_held p c E rho _ _).mp hh) with hm | hp
  · exact Or.inl hm
  · obtain ⟨st, hs, hm⟩ := hp
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact Or.inr ⟨nd, hn, hm⟩

private theorem d7a4c_occurrence (s : Slot) (Q : Block) (H : FGBlock (Fin p.n))
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

private theorem d7a4c_r6w (w : Window.State (Fin p.n)) (a : Row (Fin p.n)) :
    SimplexFG.Window.r6w (d7a4c_w_toWindow w) a = Window.r6w w a := by
  cases hp : a.height_pair <;> cases hf : a.finality_pair <;>
    simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
    SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
    SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7a4c_w_state_eq, List.any_map, Function.comp_def, d7a4c_w_entry_eq, hp, hf]
  rfl

private theorem d7a4c_valid (hv : V2.D.ExecutionValid E rho) (X : FGBlock (Fin p.n))
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
  rw [← d7a4c_w_derive_eq, d7a4c_r6w]
  exact h.2

private theorem d7a4c_decode_wire (a : RowWire p.n) (i : Fin p.n)
    (h : d7a4c_signer p a = some i) : ∃ u, RowWire.toRow? a = some u := by
  have ha := (d7a4c_signer_iff p a i).mp h
  cases a with
  | mk auth payload =>
    dsimp only at ha
    subst auth
    exact ⟨payload.toRow i, rfl⟩

private theorem d7a4c_child_eq (X U : FGBlock (Fin p.n)) (y : Nat) :
    FGCompose.FinalityCoveredByChild_W p.E p.cfg p.K_W X U y =
      FinalityCoveredByChild_W p X U y := by
  apply propext
  unfold FGCompose.FinalityCoveredByChild_W
  rw [← d7a4c_w_derive_eq, FinalityCoveredByChild_W_def]
  change (∃ e ∈ (Window.derive p p.K_W X.parent).W.map d7a4c_w_toEntry,
    e.j = y ∧ e.X = U ∧ ∃ Q, p.E.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ e.Q ∨ ∃ row ∈ X.rows, FGCompose.FinRowNames row i y U) ↔ _
  delta FGCompose.FinRowNames
  simp only [List.mem_map, FinRowNames_def]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hy, hU, Q, hQ, hi⟩
    exact ⟨d, hd, hy, hU, Q, hQ, hi⟩
  · rintro ⟨d, hd, hy, hU, Q, hQ, hi⟩
    exact ⟨d7a4c_w_toEntry d, ⟨d, hd, rfl⟩, hy, hU, Q, hQ, hi⟩

private def d7a4c_rowValid (w : SimplexFG.Window.State (Fin p.n))
    (a : RowWire p.n) : Bool :=
  a.toRow?.isSome && (a.toRow?.map (SimplexFG.Window.r6w w)).getD false

private theorem d7a4c_rowValid_eq (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    d7a4c_rowValid p (d7a4c_w_toWindow w) a = Window.rowValidW w a := by
  unfold d7a4c_rowValid
  rw [Window.rowValidW_def]
  cases hd : a.toRow? with
  | none => rfl
  | some row => simp only [Option.isSome_some, Option.map_some, Option.getD_some,
      Bool.true_and, d7a4c_r6w]

private theorem d7a4c_parentState (s : Slot) (B : FGBlock (Fin p.n)) :
    KitFG.Window.parentState p.E p.cfg p.K_W B s =
      d7a4c_w_toWindow (parentFoldState p s B) := by
  rw [KitFG.Window.parentState_def, ← d7a4c_w_derive_eq]
  rfl

private theorem d7a4c_stale (s : Slot) (B : FGBlock (Fin p.n)) (row : Row (Fin p.n)) :
    SimplexFG.Window.staleUseful (KitFG.Window.parentState p.E p.cfg p.K_W B s) row =
      Window.staleUseful (parentFoldState p s B) row := by
  rw [d7a4c_parentState]
  cases hp : row.height_pair <;> cases hf : row.finality_pair <;>
    simp only [SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7a4c_w_state_eq, List.any_map, Function.comp_def, d7a4c_w_entry_eq, hp, hf]
  rfl

private theorem d7a4c_validFor (s : Slot) (B : FGBlock (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW (parentFoldState p s B) a =
      (((fgsaSafetyReads p c).decode a).isSome &&
        (((fgsaSafetyReads p c).decode a).map
          (SimplexFG.Window.r6w (KitFG.Window.parentState p.E p.cfg p.K_W B s))).getD false) := by
  rw [d7a4c_parentState, ← d7a4c_rowValid_eq, fgsaSafetyReads_def]
  rfl

private def d7a4c_terminal_to [Fintype V] (ΔF : Time) (q y : Nat)
    (A U X : FGBlock (Fin p.n)) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    FGCompose.TerminalCarriagePrem_W (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a4c_observations p c) (d7a4c_timing p) E rho (fgsaInterface p c)
      (d7a4c_wire p c) p.E p.cfg p.K_W RowWire.valid
      (FGCompose.kernelCarrier (d7a4c_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st) ΔF q y A U X where
  schedule := h.base.valid.toScheduleWellFormed
  fault_weight := by
    rw [d7a4c_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  deltaF := h.deltaF
  carrier := by
    simpa only [d7a4c_carrier_eq, d7a4c_reads_eq, fgsaSafetyReads_def] using h.carrier
  parent := by
    obtain ⟨st, hs, hp⟩ := h.parent
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    simpa only [d7a4c_reads_eq] using hp
  path := h.path
  freshHeight := h.freshHeight
  retainedOrCovered := by
    simpa only [d7a4c_w_retained_eq, d7a4c_w_covered_eq] using h.retainedOrCovered
  horizon := h.horizon
  seats := h.seats
  rows := h.rows
  fresh := by
    obtain ⟨hh, hq, hs⟩ := (FreshFinalityRows_W_def p c E rho q y U h.seats h.rows).mp h.fresh
    refine ⟨?_, hq, ?_⟩
    · intro i hi
      rw [d7a4c_holder]
      exact (kmid_honestSeats_mem p c rho i).mp (hh hi)
    · intro i hi
      rw [d7a4c_holder]
      obtain ⟨j, C, ha, hc, hsign, hheight, hn, hsrc, hCh, hearlier⟩ := hs i hi
      refine ⟨j, C, (d7a4c_row_eq p c E rho j q _ _).mpr ha,
        (d7a4c_complete_eq p c rho _ _).mpr hc, (d7a4c_signer_iff p _ i).mpr hsign,
        hheight, hn, ?_, hCh, ?_⟩
      · rw [d7a4c_source_eq]
        exact hsrc
      · intro j' r a height hr ha hh
        exact hearlier j' r a height hr ((d7a4c_row_eq p c E rho _ _ _ _).mp ha) hh
  heightEntry := h.heightEntry
  receipt := by
    intro i hi
    refine ⟨?_, (d7a4c_held p c E rho _ _).mpr (h.receipt i hi).2⟩
    have hr := (h.receipt i hi).1
    revert hr
    delta HeldBefore rowHeld FGCompose.HeldBefore FGCompose.rowHeld
    intro hr
    simpa only [d7a4c_reads_eq, d7a4c_timing_eq] using hr

end

private theorem carry_parent_height (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).h = (heightView p P).h := by
  exact (Window.parentState_height_entry p p.K_W P s).1

private theorem carry_parent_entry (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).T_h = (heightView p P).T_h := by
  exact (Window.parentState_height_entry p p.K_W P s).2

private theorem carry_decode (p : Params) (a : RowWire p.n) (i : Fin p.n)
    (hauth : a.auth = .seat .fg i) : a.toRow? = some (a.payload.toRow i) := by
  obtain ⟨auth, body⟩ := a
  dsimp only at hauth
  subst auth
  rfl

private theorem carry_payload_pairs (p : Params) (a : RowWire p.n) (i : Fin p.n) :
    (a.payload.toRow i).height_pair = a.payload.height_pair ∧
      (a.payload.toRow i).finality_pair = a.payload.finality_pair := by
  cases a.payload
  exact ⟨rfl, rfl⟩

/-- Paper 22:1265–1289: a retained certificate below the source height gives
the stale R6W arm after the parent crosses that source height.
DC: INTENTIONAL W retention; the certificate and source heights differ,
but the source height need not be the certificate height plus one. -/
private theorem carry_staleUseful (p : Params) (P U : FGBlock (Fin p.n)) (s : Slot)
    (y rowH : Nat) (a : RowWire p.n) (i : Fin p.n)
    (hauth : a.auth = .seat .fg i) (hheight : rowHeight a = some rowH)
    (hnames : FinalityNames p a y U) (hbelow : y < rowH)
    (hcrossed : rowH < (heightView p P).h) (hretained : RetainedW p P y U) :
    ∃ row, a.toRow? = some row ∧
      Window.staleUseful (parentFoldState p s P) row = true ∧
      row.finality_pair = some ⟨y, U.root⟩ := by
  let row := a.payload.toRow i
  have hpairs := carry_payload_pairs p a i
  have hpair : row.finality_pair = some ⟨y, U.root⟩ := by
    rw [FinalityNames_def] at hnames
    exact hpairs.2.trans hnames
  have hwindow : Window.windowMatch (parentFoldState p s P) row = true := by
    obtain ⟨e, he, hej, heX⟩ := (Window.RetainedW_def p P y U).mp hretained
    rw [Window.windowMatch_def, List.any_eq_true]
    refine ⟨e, he, ?_⟩
    simp only [hej, heX, hpair, decide_true]
  refine ⟨row, carry_decode p a i hauth, ?_, hpair⟩
  rw [Window.staleUseful_def, hpair, hpairs.1]
  rw [rowHeight_def] at hheight
  cases hh : a.payload.height_pair with
  | empty => rw [hh] at hheight; cases hheight
  | vote k T timeout =>
      rw [hh] at hheight
      have hk := Option.some.inj hheight
      simp only [hk, carry_parent_height, hbelow, hcrossed, and_self,
        decide_true, hwindow, Bool.true_and]

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
/-- Paper 22:1250–1254, 1265–1289, 1993–2008: carriage with independent
certificate and source heights, including the Tail stale R6W arm.
DC: INTENTIONAL W retention and exact bitmap; the certificate height is
below the source height, with no successor-height requirement. -/
theorem terminalCarriage_general_W (hv : V2.D.ExecutionValid E rho)
    (hsel : TRowsSelect p c E rho) (q y sourceH : Nat) (A U X : FGBlock (Fin p.n))
    (hbelow : y < sourceH)
    (carrier : ∃ wireRows, HonestCarrier p c E rho X.slot (eraseFG X) wireRows ∧
      X.rows = wireRows.filterMap RowWire.toRow?)
    (parent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
      fgBlockOf st (eraseFG X).parent = some X.parent)
    (path : FGBlock.Preceq A X.parent) (sourceHeight : (heightView p A).h = sourceH)
    (retainedOrCovered : RetainedW p X.parent y U ∨ CoveredW p X.parent y U)
    (S : Finset (Fin p.n)) (rows : Fin p.n → RowWire p.n) (quorum : p.E.IsQuorum S)
    (emitted : ∀ i ∈ S, ∃ j,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
      (rows i).auth = .seat .fg i ∧ rowHeight (rows i) = some sourceH ∧
      FinalityNames p (rows i) y U)
    (heightEntry : ∀ i ∈ S,
      namedEntry (rows i).payload.height_pair = some (sourceH, (heightView p A).T_h.root))
    (held : ∀ i ∈ S, heldAtProposal p c E rho X.slot (rows i)) :
    CoveredW p X.parent y U ∨
      ((∀ i ∈ S,
        ValidForParent p c E rho X.slot (eraseFG X) (rows i) ∧
        ((heightView p X.parent).h = sourceH ∧
          HeightMatch p c E rho X.slot (eraseFG X) (rows i) ∨
         ∃ row rowH, (rows i).toRow? = some row ∧
           rowHeight (rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
       FinalityCoveredByChild_W p X U y) := by
  have parent' : ∃ nd, FGCompose.proposalStateAt E rho (fgsaInterface p c) X.slot = some nd ∧
      FGSA.fgBlockOf nd.st (eraseFG X).parent = some X.parent := by
    obtain ⟨st, hs, hp⟩ := parent
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨nd, hn, hp⟩
  have result := FGCompose.terminalCarriage_general_W
    (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4c_timing p) E rho (fgsaInterface p c)
    (d7a4c_wire p c) p.E p.cfg p.K_W
    (FGCompose.kernelCarrier (d7a4c_decodeProposal p) NamedProposal.erase NamedProposal.rows)
    (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st) (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (d7a4c_selection p c E rho hsel) (d7a4c_w_nonempty p) p.kWLarge
    (by
      intro a i h
      change d7a4c_signer p a = some i at h
      rw [fgsaSafetyReads_def]
      exact d7a4c_decode_wire p a i h)
    (by
      intro s Q H nd a u hn hp hm hd
      rw [fgsaSafetyReads_def] at hd
      exact d7a4c_occurrence p c E rho s Q H nd a u hn hp hm hd)
    (heightView p) (fgCertificateLaws p).height (d7a4c_w_height_eq p)
    (fun _ s B => ((parentFoldState p s B).h, (parentFoldState p s B).T_h.root))
    (by intro nd s B; rw [carry_parent_height, carry_parent_entry])
    (fun _ s B a => d7a4c_validFor p c s B a) q y sourceH A U X hbelow
    (by simpa only [d7a4c_carrier_eq, d7a4c_reads_eq, fgsaSafetyReads_def] using carrier)
    (by simpa only [d7a4c_reads_eq] using parent')
    (d7a4c_valid p c E rho hv X parent) path sourceHeight
    (by simpa only [d7a4c_w_retained_eq, d7a4c_w_covered_eq] using retainedOrCovered)
    S rows quorum
    (by
      intro i hi
      obtain ⟨j, ha, hs, hh, hn⟩ := emitted i hi
      refine ⟨j, ?_, (d7a4c_signer_iff p _ i).mpr hs, hh, hn⟩
      simpa only [d7a4c_holder, d7a4c_row_eq] using ha)
    heightEntry (fun i hi => (d7a4c_held p c E rho _ _).mpr (held i hi))
  simpa only [d7a4c_w_covered_eq, d7a4c_child_eq, d7a4c_validParent_eq,
    d7a4c_heightPair, d7a4c_heightMatch_eq, d7a4c_rowHeight_eq, d7a4c_w_retained_eq, d7a4c_stale,
    d7a4c_reads_eq, fgsaSafetyReads_def] using result

/-- Paper 22:1250–1254, 1265–1289: specialize general carriage to the fresh
terminal rows, with certificate height y and source height y + 1.
DC: INTENTIONAL both R6W arms and separate prior coverage; Assembly supplies
T-ROWS selection without a global receipt premise. -/
theorem terminalCarriage_W_of_tRowsSelect (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    CoveredW p X.parent y U ∨
      ((∀ i ∈ h.seats,
        ValidForParent p c E rho X.slot (eraseFG X) (h.rows i) ∧
        ((heightView p X.parent).h = y + 1 ∧
          HeightMatch p c E rho X.slot (eraseFG X) (h.rows i) ∨
         ∃ row rowH, (h.rows i).toRow? = some row ∧
           rowHeight (h.rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
       FinalityCoveredByChild_W p X U y) := by
  let h' := d7a4c_terminal_to p c E rho ΔF q y A U X h
  have result := FGCompose.terminalCarriage_W_of_tRowsSelect
    (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4c_timing p) E rho (fgsaInterface p c)
    (d7a4c_wire p c) p.E p.cfg p.K_W
    (FGCompose.kernelCarrier (d7a4c_decodeProposal p) NamedProposal.erase NamedProposal.rows)
    (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st) (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (d7a4c_selection p c E rho hsel) (d7a4c_w_nonempty p) p.kWLarge
    (by
      intro a i hs
      change d7a4c_signer p a = some i at hs
      rw [fgsaSafetyReads_def]
      exact d7a4c_decode_wire p a i hs)
    (by
      intro s Q H nd a u hn hp hm hd
      rw [fgsaSafetyReads_def] at hd
      exact d7a4c_occurrence p c E rho s Q H nd a u hn hp hm hd)
    (d7a4c_observations p c)
    (by simpa only [d7a4c_observations_eq] using (fgCertificateLaws p).height)
    (d7a4c_w_height_eq p)
    (fun _ s B => ((parentFoldState p s B).h, (parentFoldState p s B).T_h.root))
    (by intro nd s B; rw [carry_parent_height, carry_parent_entry]; rfl)
    (fun _ s B a => d7a4c_validFor p c s B a) RowWire.valid ΔF q y A U X h'
    (d7a4c_valid p c E rho h.base.valid X h.parent)
  revert result
  dsimp only [h']
  delta d7a4c_terminal_to
  intro result
  simpa only [d7a4c_observations_eq,
    d7a4c_w_covered_eq, d7a4c_child_eq, d7a4c_validParent_eq,
    d7a4c_heightPair, d7a4c_heightMatch_eq, d7a4c_rowHeight_eq, d7a4c_w_retained_eq, d7a4c_stale,
    d7a4c_reads_eq, fgsaSafetyReads_def] using result

end AvailableChain.FGSA.Run
end
