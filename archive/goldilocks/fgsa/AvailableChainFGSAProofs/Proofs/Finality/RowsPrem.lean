module
public import AvailableChainFGSAProofs.Proofs.Finality.Rows -- shake: keep (frozen row wrappers)
public import AvailableChainFGSAProofs.Proofs.Finality.RowsBatch
public import AvailableChainFGSAProofs.Proofs.Finality.RowsRecords

public import AvailableChainFGCompose.Proofs.Finality.RowsPrem

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

private def d7a4rp_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a4rp_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a4rp_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a4rp_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a4rp_w_Old := FGSA.Window.State
private abbrev d7a4rp_w_New := SimplexFG.Window.State

private def d7a4rp_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a4rp_w_toWindow {V : Type} (w : d7a4rp_w_Old V) : d7a4rp_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a4rp_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a4rp_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a4rp_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a4rp_w_state_eq {V : Type} (w : d7a4rp_w_Old V) :
    d7a4rp_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a4rp_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a4rp_w_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a4rp_w_toEntry e).j = e.j ∧ (d7a4rp_w_toEntry e).X = e.X ∧ (d7a4rp_w_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a4rp_w_state_fields {V : Type} (w : d7a4rp_w_Old V) :
    (d7a4rp_w_toWindow w).L = w.L ∧ (d7a4rp_w_toWindow w).s = w.s ∧
    (d7a4rp_w_toWindow w).h = w.h ∧ (d7a4rp_w_toWindow w).T_h = w.T_h ∧
    (d7a4rp_w_toWindow w).target_participation = w.target_participation ∧
    (d7a4rp_w_toWindow w).progress = w.progress ∧ (d7a4rp_w_toWindow w).W = w.W.map
      d7a4rp_w_toEntry ∧
    (d7a4rp_w_toWindow w).J = w.J ∧ (d7a4rp_w_toWindow w).h_j = w.h_j ∧
    (d7a4rp_w_toWindow w).F = w.F ∧ (d7a4rp_w_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a4rp_w_initial_eq {V : Type} :
    d7a4rp_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a4rp_w_foldRow_eq (w : d7a4rp_w_Old V) (a : Row V) :
    d7a4rp_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a4rp_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a4rp_w_toEntry =
      (w.W.map d7a4rp_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a4rp_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a4rp_w_state_eq] using
        congrArg (fun es => ({ d7a4rp_w_toWindow w with W := es } : d7a4rp_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a4rp_w_state_eq] <;> rw [bits] <;> simp_all [d7a4rp_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a4rp_w_rows_eq (rs : List (Row V)) (w : d7a4rp_w_Old V) :
    d7a4rp_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a4rp_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a4rp_w_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rp_w_advance_eq (w : d7a4rp_w_Old V) :
    d7a4rp_w_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a4rp_w_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rp_w_greatest_eq (E : Electorate V) (w : d7a4rp_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a4rp_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a4rp_w_toWindow w) := by
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
      (oldStep best e).map d7a4rp_w_toEntry = newStep (best.map d7a4rp_w_toEntry)
      (d7a4rp_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a4rp_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a4rp_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a4rp_w_toEntry =
        (es.map d7a4rp_w_toEntry).foldl newStep (best.map d7a4rp_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a4rp_w_toWindow w) =
      (w.W.map d7a4rp_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rp_w_finalize_eq (E : Electorate V) (w : d7a4rp_w_Old V) :
    d7a4rp_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a4rp_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a4rp_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a4rp_w_state_eq, d7a4rp_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a4rp_w_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a4rp_w_toEntry =
      (es.map d7a4rp_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a4rp_w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a4rp_w_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4rp_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a4rp_w_Old V) :
    d7a4rp_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a4rp_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a4rp_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a4rp_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a4rp_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a4rp_w_state_eq, d7a4rp_w_entry_eq, List.map_drop]

private theorem d7a4rp_w_transition_eq (p : Params) (K : Nat) (w : d7a4rp_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a4rp_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a4rp_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a4rp_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a4rp_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a4rp_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a4rp_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a4rp_w_toWindow where
  initial := d7a4rp_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a4rp_w_transition_eq p K

private theorem d7a4rp_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a4rp_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a4rp_w_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a4rp_w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a4rp_w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a4rp_w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a4rp_w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7a4rp_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7a4rp_timing_eq (p : Params) : d7a4rp_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private theorem d7a4rp_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7a4rp_timing p) where
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

private theorem d7a4rp_action_eq (p : Params) (q : Nat) :
    (d7a4rp_timing p).action q = p.actionTime q := rfl

private def d7a4rp_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d7a4rp_observations_eq : d7a4rp_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

private def d7a4rp_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a4rp_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a4rp_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a4rp_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rp_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rp_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a4rp_decode p ha]
    rfl

private theorem d7a4rp_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a4rp_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

private theorem d7a4rp_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a4rp_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a4rp_reads_eq]; rfl

private theorem d7a4rp_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a4rp_reads_eq]
  rfl

private def d7a4rp_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7a4rp_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (fgsaSafetyReads p c) (d7a4rp_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7a4rp_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (fgsaSafetyReads p c) (d7a4rp_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7a4rp_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

omit [DecidableEq V] in
private theorem d7a4rp_holder (i : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem d7a4rp_faulty_eq : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [d7a4rp_holder]
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private def d7a4rp_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7a4rp_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7a4rp_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private def d7a4rp_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7a4rp_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7a4rp_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7a4rp_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7a4rp_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem d7a4rp_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

private theorem d7a4rp_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a4rp_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7a4rp_proposal_payload p o s N ((d7a4rp_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7a4rp_decodeProposal_iff p o s N).mpr
      (d7a4rp_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7a4rp_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a4rp_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a4rp_signer; simp
  | proposer s => delta d7a4rp_signer; simp
  | seat label j => cases label <;> delta d7a4rp_signer <;> simp

private theorem d7a4rp_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7a4rp_wire p c).heightPair) (d7a4rp_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] in
private theorem d7a4rp_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7a4rp_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a4rp_signer_iff, d7a4rp_holder]

private theorem d7a4rp_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a4rp_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  rw [TRowsReceipt_def]
  delta FGCompose.TRowsReceipt FGCompose.HeldBefore HeldBefore
  simp only [d7a4rp_row_eq, d7a4rp_reads_eq]
  rfl

private theorem d7a4rp_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a4rp_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private abbrev d7a4rp_Batch (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a4rp_observations p c)
    (d7a4rp_timing p) E rho (fgsaInterface p c) (d7a4rp_wire p c) p.E
    (d7a4rp_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF (d7a4rp_kind k) q y U X

private def d7a4rp_ac (w : HealingWitness) : FGCompose.FGACServiceReads V where
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

private theorem d7a4rp_honestProposal_eq (s : Slot) (Q : Block) :
    FGCompose.HonestProposal E rho (fgsaInterface p c) s Q =
      HonestProposal E rho (fgsaInterface p c) s Q := rfl

private theorem d7a4rp_opening_eq (s : Slot) (A : Block) (X : FGBlock (Fin p.n)) :
    FGCompose.OpeningCarrier_W (d7a4rp_decodeProposal p) NamedProposal.erase NamedProposal.rows
      (fun nd : Node p => FGSA.parentFG nd.st) FGSA.fgBlock E rho (fgsaInterface p c)
      s A X = OpeningCarrier_W p c E rho s A X := by
  apply propext
  rw [OpeningCarrier_W_def]
  constructor
  · rintro ⟨o, N, nd, Par, he, hN, hd, hnd, hpar, hfg⟩
    refine ⟨o, N, nd.st, Par, he, hN, (d7a4rp_decodeProposal_iff p o s N).mp hd, ?_, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _
    rw [hnd]
    rfl
  · rintro ⟨o, N, st, Par, he, hN, hd, hst, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _ at hst
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨o, N, nd, Par, he, hN, (d7a4rp_decodeProposal_iff p o s N).mpr hd, hnd, hpar, hfg⟩

private theorem d7a4rp_exact (w : HealingWitness) (s : Slot) (Q : Block)
    (h : ExactService p c E rho s Q) :
    FGCompose.KernelExactService (d7a4rp_ac p c E rho w) rho.horizon s Q := by
  refine ⟨h.1, ?_⟩
  intro hh x hx hc
  have hgate := h.2 hh x hx hc
  exact ⟨hgate.1, hgate.2.2.2.2⟩

private theorem d7a4rp_batch_to [Fintype V] (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) (h : BatchPrem p c E rho ΔF k q y U X) :
    d7a4rp_Batch p c E rho ΔF k q y U X := by
  refine ⟨h.base.valid.toScheduleWellFormed, ?_, h.deltaF,
    (d7a4rp_receipt_eq p c E rho ΔF).mpr h.rowsReceipt, h.horizon, ?_, h.after,
    ?_, h.entry, h.path, ?_⟩
  · rw [d7a4rp_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  · simpa only [d7a4rp_carrier_eq, d7a4rp_reads_eq, fgsaSafetyReads_def] using h.carrier
  · simp only [d7a4rp_holder]
    obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mp (hh hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, (d7a4rp_row_eq p c E rho j r _ a).mpr ha,
      (d7a4rp_signer_iff p a i).mpr hsign, (d7a4rp_namesEntry p c k a y U).mpr hn, ht, htime,
      ?_, ?_⟩
    · rw [d7a4rp_reads_eq]
      exact (d7a4rp_validParent_eq p c E rho _ _ a).mpr hv
    · rw [d7a4rp_reads_eq]
      exact (d7a4rp_heightMatch_eq p c E rho _ _ a).mpr hm
  · simp only [d7a4rp_holder]
    intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mpr hi) W hW
      (by simpa only [d7a4rp_rowNames] using hr)

private abbrev d7a4rp_Middle (ΔF : Time) (pt : KernelPt) (A : Block) :=
  FGCompose.KernelMiddleWitness_W (fgsaCoreReads p c) (fgsaSafetyReads p c)
    (d7a4rp_observations p c) (d7a4rp_timing p) E rho (fgsaInterface p c) (d7a4rp_wire p c) p.E
    (d7a4rp_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) FGSA.fgBlock RowWire.valid
    (d7a4rp_ac p c E rho pt.w) p.cfg p.K_W ΔF (d7a4rp_point p pt.w) ⟨pt.r⟩ A

private theorem d7a4rp_fg (nd : (fgsa p c).State) : ((fgsaCoreReads p c).core nd).fg = nd.st.fg :=
    by
  rw [d7a4rp_reads_eq p c]

private theorem d7a4rp_erase (C : FGBlock (Fin p.n)) :
    (fgsaCoreReads p c).erase C = eraseFG C := by
  rw [d7a4rp_reads_eq p c]

private theorem d7a4rp_roundSlots_eq : (d7a4rp_timing p).roundSlots = p.R := rfl

omit [DecidableEq V] in
private theorem d7a4rp_cut_eq (t : Time) : FGCompose.afterTicksIdx rho t =
    afterTicksIdx rho t := rfl

private theorem d7a4rp_storeAt_eq (i : Nat) (x : V) :
    storeAt p c E rho i x = (V2.D.Run.stateBefore E rho i x).st := rfl

private theorem d7a4rp_chain_eq [Fintype V] (X : FGBlock (Fin p.n)) (cut : Time) :
    FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho X cut =
      ChainRowsBefore p c E rho X cut := by rw [d7a4rp_reads_eq]; rfl

private def d7a4rp_middle_to [Fintype V] (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) : d7a4rp_Middle p c E rho ΔF pt A where
  A₀ := m.A₀
  B := m.B
  U := m.U
  X_D := m.X_D
  cD := m.cD
  d := m.d
  opening := m.opening
  eraseA := by simpa only [d7a4rp_reads_eq] using m.eraseA
  carrierA := by
    have h := m.carrierA
    exact (d7a4rp_opening_eq p c E rho _ _ _).mpr h
  carrierB := by
    have h := m.carrierB
    rw [d7a4rp_erase]
    exact (d7a4rp_opening_eq p c E rho _ _ _).mpr h
  carrierD := by
    have h := m.carrierD
    rw [d7a4rp_erase]
    exact (d7a4rp_opening_eq p c E rho _ _ _).mpr h
  honestB :=
    by simpa only [d7a4rp_erase, d7a4rp_honestProposal_eq, d7a4rp_roundSlots_eq] using m.honestB
  honestD := by simpa only [d7a4rp_erase, d7a4rp_honestProposal_eq] using m.honestD
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
  sourceA := by simpa only [d7a4rp_source_eq] using m.sourceA
  sourceB := by simpa only [d7a4rp_source_eq] using m.sourceB
  serviceD := by
    rw [d7a4rp_erase]
    exact d7a4rp_exact p c E rho pt.w _ _ m.serviceD
  heightD := m.heightD
  justifiedD := m.justifiedD
  justifiedHeightD := m.justifiedHeightD
  pendingD := by
    rw [← d7a4rp_w_derive_eq]
    exact m.pendingD
  retainedD := (d7a4rp_w_retained_eq p _ _ _).mpr m.retainedD
  noFirstHeight := by
    simpa only [d7a4rp_row_eq, d7a4rp_rowHeight_eq, d7a4rp_event_eq, d7a4rp_action_eq]
      using m.noFirstHeight
  noSecondHeight := by
    simpa only [d7a4rp_row_eq, d7a4rp_rowHeight_eq, d7a4rp_event_eq, d7a4rp_action_eq]
      using m.noSecondHeight
  noEarlyFinality := by
    simpa only [d7a4rp_row_eq, d7a4rp_finHeight_eq, d7a4rp_event_eq, d7a4rp_action_eq]
      using m.noEarlyFinality
  chainA := by simpa only [d7a4rp_chain_eq, d7a4rp_action_eq] using m.chainA
  chainB := by simpa only [d7a4rp_chain_eq, d7a4rp_action_eq] using m.chainB
  chainD := by simpa only [d7a4rp_chain_eq, d7a4rp_action_eq] using m.chainD
  freshD := {
    schedule := m.freshD.base.valid.toScheduleWellFormed
    fault_weight := by
      rw [d7a4rp_faulty_eq]
      exact kmid_faulty_weight p c E rho m.freshD.base m.freshD.faultQ
    cut := m.freshD.cut
    early := m.freshD.early
    rows := by simpa only [d7a4rp_chain_eq] using m.freshD.rows
    noNextRow := by
      simpa only [d7a4rp_row_eq, d7a4rp_rowHeight_eq, d7a4rp_event_eq, d7a4rp_action_eq]
        using m.freshD.noNextRow
    noFinRow := by
      simpa only [d7a4rp_row_eq, d7a4rp_finHeight_eq, d7a4rp_event_eq, d7a4rp_action_eq]
        using m.freshD.noFinRow }
  noMixedD := m.noMixedD
  batchB := fun hp => d7a4rp_batch_to p c E rho ΔF .target _ _ _ _ (m.batchB hp)
  batchD := fun hp => d7a4rp_batch_to p c E rho ΔF .target _ _ _ _ (m.batchD hp)
  targetsB := by
    intro x hx
    obtain ⟨j, a, ha, hc, hn⟩ := m.targetsB x hx
    exact ⟨j, a, (d7a4rp_row_eq p c E rho j _ x a).mpr ha,
      (d7a4rp_complete_eq p c rho x a).mpr hc,
      (d7a4rp_namesEntry p c .target a _ _).mpr hn⟩
  actionsInRun := m.actionsInRun
  capThroughBAction := fun i x W hi hcut hh =>
    m.capThroughBAction i x W hi hcut ((d7a4rp_held_eq p c E rho i x W).mp hh)
  capThroughFinalAction := fun i x W hi hcut hh =>
    m.capThroughFinalAction i x W hi hcut ((d7a4rp_held_eq p c E rho i x W).mp hh)
  finalityThroughFinalAction := fun i x W hi hcut hh =>
    m.finalityThroughFinalAction i x W hi hcut ((d7a4rp_held_eq p c E rho i x W).mp hh)
  heldDAtFinalAction := by
    simpa only [d7a4rp_fg, d7a4rp_storeAt_eq, d7a4rp_action_eq, d7a4rp_cut_eq]
      using m.heldDAtFinalAction
  heldAAtEnd := by
    simpa only [d7a4rp_fg, d7a4rp_storeAt_eq] using m.heldAAtEnd

private theorem d7a4rp_f_postClock_eq (x : V) (t : Time) :
    FGCompose.postClock E rho x t = postClock E rho x t :=
  (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1.symm

private theorem d7a4rp_f_entry_eq (a : NamedHeightPair) : FGCompose.namedEntry a = namedEntry a :=
    by
  cases a <;> rfl

private theorem d7a4rp_f_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a4rp_observations p c) (d7a4rp_timing p) E rho (d7a4rp_wire p c) := by
  intro j x r a entry ha hn
  rw [d7a4rp_row_eq] at ha
  change FGCompose.namedEntry a.payload.height_pair = some entry at hn
  rw [d7a4rp_f_entry_eq] at hn
  obtain ⟨C, hs, he⟩ := h j x r a entry ha hn
  exact ⟨C, (d7a4rp_source_eq p c E rho x r).symm ▸ hs, he⟩
private theorem d7a4rp_w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a4rp_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4rp_w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a4rp_w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a4rp_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4rp_w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a4rp_w_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7a4rp_w_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7a4rp_w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega


private theorem d7a4rp_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'


private theorem d7a4rp_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (d7a4rp_ac p c E rho w) (d7a4rp_point p w)
      (recoveryStart p E) rho.horizon where
  source_chain := by
    intro x y r q C D hx hy hc hd _ _ _ _
    obtain ⟨C', hs, he, hh⟩ := hc
    obtain ⟨D', ht, hf, hk⟩ := hd
    subst C D
    exact (h1 x y r q C' D' hx hy hs ht hh hk).1
  exact_head := by
    intro s Q x hQ hs _ hh hx hr
    exact (h3 s Q hQ hs).1 hh x hx hr
  exact_gate := by
    intro s Q x hQ hs _ hh hx hr
    exact ((h3 s Q hQ hs).2 hh x hx hr).1
  opening_source := by
    intro q Q x hQ hs _ hh hx _ hr
    exact ((h3 (q * p.R) Q hQ hs).2 hh x hx hr).2.2.2.2 q rfl
  proposal_later_head := by
    intro s Q x i H hQ hs _ hx hr hi _ hH
    exact h2p s Q hQ hs x i H ⟨hx, hr⟩ hi hH
  source_next_head := by
    intro y r C x i H hy hc _ _ hx hr hi _ hH
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact (h2a y r C' hy hs hh).1 x i H ⟨hx, hr⟩ hi hH
  covered_source := by
    intro s Q q x _ _ _ hne _ _ ht hs hGST hheads hfloor hx _ hframe
    have hcover : ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y (q * p.R) = some H ∧ Block.Preceq Q H := by
      intro y hy
      obtain ⟨H, _, hH, hQ⟩ := hheads y hy
      exact ⟨H, hH, hQ⟩
    have hF : ∀ y st, y ∈ rho.honest → gateIn p c E rho y (q * p.R) = some st →
        Block.Preceq (eraseFG st.fg.F) Q := by
      intro y st hy hst
      exact hfloor y (eraseFG st.fg.F) hy (by
        change (gateIn p c E rho y (q * p.R)).map _ = _
        rw [hst, Option.map_some])
    obtain ⟨_, _, nd, d, hnd, hwrite, hlease, _, hlive⟩ :=
      h6 (q * p.R) Q hs hGST ht.2 hne hcover hF x hx
    obtain ⟨D, hD, hmem, hFD, hZD, hlo⟩ := hframe nd hnd
    obtain ⟨j, _, hclock⟩ := d7a4rp_clock_read p c E rho x (p.actionTime q) nd hnd
    have hkept : D ∈ domainR p nd.st (treeT p nd.st) := by
      rw [domainR_def, treeT_def, frameR_def]
      exact (KitFG.mem_filteredFromView (heightView p) _ _ D).mpr
        ⟨hmem, hFD, hZD, D, hmem, KitFG.preceq_refl D, hlo⟩
    have hround : p.round (nd.st.slot p) = q := by
      rw [← hclock]
      exact (fgsa_action_slot_round (c := c) _ q).2
    have hnow : nd.st.base.now = p.actionTime q := by
      rw [← hclock]
      exact (fgsa_postClock_slot (c := c) _ _).1
    have hserved : eraseFG D ∈ sourceCandidates p nd.st := by
      rw [sourceCandidates_def, hround, hD]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwrite,
        by rw [hlease]; exact decide_eq_true (hnow ▸ hlive)⟩
    rw [← hclock] at hkept hserved
    obtain ⟨C, hsource, hDC⟩ := openingSource_extends_served E rho j x q D hkept hserved
    change FGSA.fgSource p (((fgsa p c).clock _ _).st) = some C at hsource
    rw [hclock] at hsource
    refine ⟨eraseFG C, ?_, ?_⟩
    · change actionSource p c E rho x q = some (some (eraseFG C))
      change postClock E rho x (p.actionTime q) = some nd at hnd
      delta actionSource
      simp only [actionSourceFG_def, hnd, Option.map_some, hsource]
    · change Block.Preceq Q (eraseFG C)
      rw [← hD]
      exact eraseFG_preceq hDC
  parent_transfer := by
    intro x r C s Q hx hc _ _ hQ _ hgap _
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact h2 x r C' s Q hx hs hh hQ hgap

private theorem d7a4rp_source_service (w : HealingWitness) (q opening : Nat)
    (D : FGBlock (Fin p.n)) (hx : V) (hhonest : hx ∈ rho.honest)
    (hbefore : opening ≤ q * p.R) (hstart : w.sStar + 2 ≤ opening)
    (hproposal : HonestProposal E rho (fgsaInterface p c) opening (eraseFG D))
    (hcovered : opening < q * p.R → ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x (q * p.R) = some H ∧ Block.Preceq (eraseFG D) H) (h3 : H3 p c E rho w)
    (h6 : H6GateService p c E rho w)
    (hGST : recoveryStart p E ≤ SA.voteTime p.toParams (q * p.R))
    (hhor : p.actionTime q ≤ rho.horizon) (hne : eraseFG D ≠ .genesis)
    (_hheads : ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x (q * p.R) = some H)
    (_hjoined : ∀ x ∈ rho.honest,
      joinedAt p E rho x (q * p.R) (SA.voteTime p.toParams (q * p.R)))
    (hconfirmed : confirmedReaderAtIdx p c E rho hx
      (afterTicksIdx rho (SA.gateTime p.toParams opening))
      (SA.gateTime p.toParams opening))
    (hFgate : ∀ x st, x ∈ rho.honest → gateIn p c E rho x (q * p.R) = some st →
      Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hframe : ∀ nd, postClock E rho hx (p.actionTime q) = some nd →
      D ∈ nd.st.fg.TF ∧ FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h) :
    FGCompose.FGSourceService (fgsaCoreReads p c) E rho hx (p.actionTime q)
      opening (q * p.R) D := by
  constructor
  · intro heq
    have hexact := ((h3 opening (eraseFG D) hproposal hstart).2
      (by simpa only [heq, Params.actionTime] using hhor) hx hhonest hconfirmed).2.2.2.2
      q heq
    change (actionSourceFG p c E rho hx q).map (Option.map eraseFG) =
      some (some (eraseFG D)) at hexact
    obtain ⟨source, hs, he⟩ := Option.map_eq_some_iff.mp hexact
    obtain ⟨C, hC, hCe⟩ := Option.map_eq_some_iff.mp he
    have hCD : C = D := eraseFG_injective hCe
    subst C
    rw [hC] at hs
    rw [actionSourceFG_def] at hs
    obtain ⟨nd, hnd, hsource⟩ := Option.map_eq_some_iff.mp hs
    rw [d7a4rp_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, hnd, hsource⟩
  · intro hlt
    have hcover := hcovered hlt
    obtain ⟨_hresult, _hpassed, nd, d, hnd, hwrite, hlease, _hdeadline, hlive⟩ :=
      h6 (q * p.R) (eraseFG D) ((Nat.le_add_right w.sStar 2).trans
        (hstart.trans hbefore)) hGST hhor hne hcover hFgate hx hhonest
    obtain ⟨j, _hj, hclock⟩ := d7a4rp_clock_read p c E rho hx (p.actionTime q) nd hnd
    have hf := hframe nd hnd
    have hkept : D ∈ domainR p nd.st (treeT p nd.st) := by
      rw [domainR_def, treeT_def, frameR_def]
      exact (KitFG.mem_filteredFromView (heightView p) _ _ D).mpr
        ⟨hf.1, hf.2.1, hf.2.2.1, D, hf.1, KitFG.preceq_refl D, hf.2.2.2⟩
    have hround : p.round (nd.st.slot p) = q := by
      rw [← hclock]
      exact (fgsa_action_slot_round (c := c) _ q).2
    have hnow : nd.st.base.now = p.actionTime q := by
      rw [← hclock]
      exact (fgsa_postClock_slot (c := c) _ _).1
    have hserved : eraseFG D ∈ sourceCandidates p nd.st := by
      rw [sourceCandidates_def, hround]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwrite,
        by rw [hlease]; exact decide_eq_true (hnow ▸ hlive)⟩
    have hkept' := hkept
    have hserved' := hserved
    rw [← hclock] at hkept' hserved'
    obtain ⟨C, hsource, hDC⟩ := openingSource_extends_served E rho j hx q D hkept' hserved'
    change FGSA.fgSource p (((fgsa p c).clock _ _).st) = some C at hsource
    rw [hclock] at hsource
    rw [d7a4rp_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, C, hnd, hsource, hDC⟩

private def d7a4rp_makeWire (row : Row (Fin p.n)) : RowWire p.n :=
  ⟨.seat .fg row.signer, .vote ⟨row.height_pair, row.finality_pair⟩⟩

private theorem d7a4rp_release (i : Fin p.n) (q : Nat) (nd : Node p) (row : Row (Fin p.n))
    (hnd : FGCompose.postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd)
    (awake : E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true)
    (released : (createRowOnce p.E p.cfg nd.record i (fgInputs p nd.st).1
      (fgInputs p nd.st).2).1 = some row) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base .fg) i) (p.actionTime q)) ∧
      ofRow p (d7a4rp_makeWire p row) ∈ V2.D.Run.emitsAt E rho j := by
  rw [← (fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1] at hnd
  obtain ⟨j, hj, hclock⟩ := d7a4rp_clock_read p c E rho _ _ nd hnd
  obtain ⟨_, _, _, _, shape, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg nd.record i _ _ released
  have signer : row.signer = i := congrArg Row.signer shape
  refine ⟨j, hj, ?_⟩
  change ofRow p ⟨.seat .fg row.signer, .vote ⟨row.height_pair, row.finality_pair⟩⟩ ∈ _
  rw [signer]
  apply (fgsa_emitsAt_row E rho j _ _ hj i _).mpr
  refine ⟨awake, rfl, q, rfl, ?_⟩
  have record : (V2.D.Run.stateBefore E rho j (rho.seatOf (.base .fg) i)).record =
      nd.record := (clock_rec (c := c) _ _).symm.trans (congrArg Node.record hclock)
  rw [show FGSA.clock p _ _ = nd.st from congrArg Node.st hclock, record]
  rw [attest_signer_irrel _ _ ⟨0, p.nPos⟩ i]
  change (createRowOnce p.E p.cfg nd.record i (fgInputs p nd.st).1
    (fgInputs p nd.st).2).1.map (fun a => RowPayload.vote (RowBody.ofRow a)) = _
  rw [released]
  rfl


end

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

include hK in
/-- Paper 22:1228–1254: K-ROWS T1 at the actual action read. P1, P2 and P3 feed the
full action walk; K-MID's held caps through the action bound its head fields.
DC: INTENTIONAL: height plateau and finality lag from K-MID; no exact head body. -/
theorem rowsPrem_pending_head
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ∃ H : FGBlock (Fin p.n),
        FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧ FGBlock.Preceq m.X_D H ∧
        (heightView p H).h = m.d + 2 ∧ (heightView p H).J = m.U ∧
        (heightView p H).h_j = m.d + 1 ∧ (finalityView p H).h_F < m.d + 1 ∧
        (heightView p H).T_h = (heightView p m.X_D).T_h := by
  have reads : ∀ x nd,
      FGCompose.postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho
        (FGCompose.afterTicksIdx rho (p.actionTime (pt.r + 2))) x)).fg =
          ((fgsaCoreReads p c).core nd).fg := by
    intro x nd hnd
    rw [d7a4rp_f_postClock_eq] at hnd
    have h := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
      x _ nd hnd
    simpa only [d7a4rp_fg, d7a4rp_storeAt_eq, d7a4rp_cut_eq] using congrArg (fun st => st.fg) h
  have selected : ∀ x nd, x ∈ rho.honest →
      FGCompose.postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ∃ H, (fgsaCoreReads p c).finalityHead nd = some H ∧
        H ∈ ((fgsaCoreReads p c).core nd).fg.TF ∧
        Block.Preceq (eraseFG m.X_D) (eraseFG H) := by
    intro x nd hx hnd
    rw [d7a4rp_f_postClock_eq] at hnd
    obtain ⟨j, _, hclock⟩ := d7a4rp_clock_read p c E rho x _ nd hnd
    have hinv : CStoreInv p nd.st := by
      rw [← hclock]
      exact (storeBundle_postClock E rho j x _).cstore
    have hread := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
      x _ nd hnd
    have hwb := rowsPrem_action_walk_batch p c E rho hK m hServices hQC hXing hNames
      x nd hx hnd
    have hcover := (hK.services.walk _ x ((pt.r + 2) * p.R + 1) _ _ m.X_D _ _ hx hwb.1
      (by rw [hread]; exact rowsPrem_full_domain p c E rho hK m hQC hXing hNames x nd hx hnd)
      (by
        rw [hread]
        exact rowsPrem_liveRoot_compatible p c E rho hK m hQC hXing hNames x nd hx hnd)
      (by rw [hread]; exact hwb.2.1)).1
    rw [hread, ← hwb.2.2] at hcover
    obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
    rw [d7a4rp_reads_eq]
    exact ⟨H, (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩, hH,
      by simpa only [hHe] using hcover⟩
  have result := FGCompose.rowsPrem_pending_head (d7a4rp_middle_to p c E rho ΔF pt A m)
    (by simpa only [d7a4rp_observations_eq] using (fgCertificateLaws p).height)
    (by simpa only [d7a4rp_observations_eq] using heightView_bridge p) reads
    (fun x nd hx hnd => by
      obtain ⟨H, hH, hm, _⟩ := selected x nd hx hnd
      exact ⟨H, hH, hm⟩)
    (by
      intro x nd hx hnd H hH
      obtain ⟨B, hB, _, hp⟩ := selected x nd hx hnd
      have he := Option.some.inj (hB.symm.trans hH)
      subst B
      delta d7a4rp_middle_to
      simpa only [d7a4rp_reads_eq] using hp)
    (by
      intro nd B C _ _ hp
      rw [d7a4rp_reads_eq] at hp
      exact eraseFG_preceq_iff.mp hp)
  revert result
  delta d7a4rp_middle_to
  intro result
  simpa only [d7a4rp_observations_eq, d7a4rp_timing_eq,
    d7a4rp_f_postClock_eq, d7a4rp_reads_eq] using result

include hK in
/-- Paper 22:1256–1257,1667–1700: K-ROWS source step at the actual action read.
P4 gives the gate guard and P5 the source filter guards for the H3/H6 split.
DC: INTENTIONAL: deepest fresh FG-SA selector; height plateau fixes the same entry. -/
theorem rowsPrem_action_source
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x ∈ rho.honest, ∃ nd C,
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq m.X_D C ∧
      (heightView p C).h = m.d + 2 ∧ (heightView p C).T_h = (heightView p m.X_D).T_h := by
  have service : ∀ x ∈ rho.honest,
      FGCompose.FGSourceService (fgsaCoreReads p c) E rho x (p.actionTime (pt.r + 2))
        m.cD ((pt.r + 2) * p.R) m.X_D := by
    intro x hx
    obtain ⟨_, hκ2, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
    have hs := hK.set.base.valid.toScheduleWellFormed
    have hrD : pt.r * p.R ≤ m.cD := by
      have := m.earlySlot.1
      have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
      omega
    have hne : eraseFG m.X_D ≠ .genesis := by
      intro h
      have hslot := m.slotD
      rw [eraseFG_eq_genesis.mp h] at hslot
      have h0 : (0 : Nat) = m.cD := hslot
      have := m.earlySlot.1
      omega
    have hGSTq : E.t_GST ≤ SA.voteTime p.toParams ((pt.r + 2) * p.R) := by
      refine hGST.trans ?_
      have hle := kmid_slot_scale_le p (Nat.mul_le_mul_right p.R
        (show pt.r ≤ pt.r + 2 by omega))
      have hd := p.deltaPos
      change 4 * p.Δ * ((pt.r * p.R : Nat) : Time) ≤
        4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Time) + p.Δ
      linarith
    have hheads : ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y ((pt.r + 2) * p.R) = some H := by
      intro y hy
      have hvt : ((4 * ((pt.r + 2) * p.R) + 1 : Nat) : Time) * p.Δ =
          SA.voteTime p.toParams ((pt.r + 2) * p.R) := by
        change ((4 * ((pt.r + 2) * p.R) + 1 : Nat) : Int) * p.Δ =
          4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Int) + p.Δ
        push_cast
        ring
      obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hK.set.base.delta y hy _
        (hvt ▸ (kmid_slot_horizon hK le_rfl).2.1)
        (hvt ▸ hK.set.awake y hy _ hGSTq (kmid_slot_horizon hK le_rfl).2.1)
      rw [hvt] at hk
      have hH : headAtLabel p c E rho y ((pt.r + 2) * p.R) =
          some (FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
            (SA.voteTime p.toParams ((pt.r + 2) * p.R))).st ((pt.r + 2) * p.R)) := by
        change (postClock E rho y (SA.voteTime p.toParams ((pt.r + 2) * p.R))).map
          (fun nd => FGSA.headVote p nd.st ((pt.r + 2) * p.R)) = _
        rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
        rfl
      exact ⟨_, hH⟩
    have hservices := d7a4rp_service_laws p c E rho pt.w hK.input.t.h1 hK.input.t.h2
      hK.input.ac.h2' hK.input.ac.h2A hK.input.ac.h3 hK.input.ac.h6
    have hserviceStart : (d7a4rp_point p pt.w).serviceStart ≤
        (d7a4rp_ac p c E rho pt.w).proposalTime m.cD := by
      have hstart := hK.start
      rw [kmid_period_eq] at hstart
      exact hstart.trans (kmid_slot_scale_le p hrD)
    have hcovered : m.cD < (pt.r + 2) * p.R → ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y ((pt.r + 2) * p.R) = some H ∧
          Block.Preceq (eraseFG m.X_D) H := by
      intro hlt y hy
      obtain ⟨H, hH⟩ := hheads y hy
      refine ⟨H, hH, ?_⟩
      exact hservices.proposal_later_head m.cD (eraseFG m.X_D) y _ H
        m.honestD (hs2.trans hrD) hserviceStart hy
        (kmid_window_joined hK (Nat.mul_le_mul_right p.R (by omega)) le_rfl hy)
        (Nat.succ_le_of_lt hlt) (kmid_slot_horizon hK le_rfl).2.1 hH
    exact d7a4rp_source_service p c E rho pt.w (pt.r + 2) m.cD m.X_D x hx
      m.earlySlot.2 (hs2.trans hrD) m.honestD hcovered hK.input.ac.h3 hK.input.ac.h6
      (by
        apply finality_recoveryStart_le_vote p E ((pt.r + 2) * p.R) (by
          have hR2 := (kmid_kernel_bounds hK).2.2.2.1
          have hle : p.R ≤ (pt.r + 2) * p.R := by rw [Nat.add_mul]; omega
          exact hR2.trans hle)
        have hsync := hK.input.wit.synchronous
        have hstart := hK.start
        rw [kmid_period_eq] at hstart
        have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
          exact_mod_cast hK.input.wit.proposal_lower
        have hR : 2 ≤ p.R := (kmid_kernel_bounds hK).2.2.2.1
        have hle := kmid_slot_scale_le p (show pt.r * p.R + 2 ≤ (pt.r + 2) * p.R by
          rw [Nat.add_mul]; omega)
        change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
        change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
        change E.t_GST ≤ 4 * p.Δ * (_ - 2)
        push_cast at hle hstart ⊢
        nlinarith [p.deltaPos]) m.actionsInRun hne hheads
      (fun y hy => kmid_window_joined hK
        (Nat.mul_le_mul_right p.R (by omega)) le_rfl hy)
      (kmid_window_confirmed hK (by omega) (by
        have hle := kmid_slot_scale_le p m.earlySlot.2
        have hh := m.actionsInRun
        rw [kmid_actionTime_eq] at hh
        change 4 * p.Δ * (m.cD : Int) + 6 * p.Δ ≤ rho.horizon
        linarith) hx) (rowsPrem_F_below_D_at_gate p c E rho hK m hXing)
      (fun nd hnd => by
        have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
        exact ⟨hf.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2⟩)
  have result := FGCompose.rowsPrem_action_source (d7a4rp_middle_to p c E rho ΔF pt A m)
    (fgsaCoreLaws p c)
    (by simpa only [d7a4rp_observations_eq] using (fgCertificateLaws p).height)
    (by
      intro x nd hnd
      rw [d7a4rp_action_eq, d7a4rp_f_postClock_eq] at hnd
      have hr := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
        x _ nd hnd
      simpa only [d7a4rp_fg, d7a4rp_storeAt_eq, d7a4rp_cut_eq, d7a4rp_action_eq]
        using congrArg (fun st => st.fg) hr)
    service
  revert result
  delta d7a4rp_middle_to
  intro result
  simpa only [d7a4rp_observations_eq, d7a4rp_timing_eq,
    d7a4rp_f_postClock_eq, d7a4rp_reads_eq] using result

include hK in
/-- Paper 22:1256–1263: K-ROWS fresh rows at the actual action. The source step, the
pending head fields and P6's record guards give one complete fresh row per honest seat.
DC: INTENTIONAL: durable record and both send-once checks; source ancestry fixes the entry. -/
theorem rowsPrem_fresh_rows
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (S : Finset (Fin p.n)) (hS : S ⊆ honestSeats p c rho) (hQ : p.E.IsQuorum S) :
    ∃ rows : Fin p.n → RowWire p.n,
      FreshFinalityRows_W p c E rho (pt.r + 2) (m.d + 1) m.U S rows ∧
      (∀ i ∈ S, namedEntry (rows i).payload.height_pair =
        some (m.d + 2, (heightView p m.X_D).T_h.root)) ∧
      (∀ i ∈ S, (rows i).payload.height_pair =
        NamedHeightPair.vote (m.d + 2) (heightView p m.X_D).T_h.root false) := by
  obtain ⟨_, _, _, _, _, hGST, _⟩ := kmid_kernel_bounds hK
  have hhonest : ∀ i ∈ S, rho.seatOf (.base .fg) i ∈ rho.honest := by
    intro i hi
    classical
    have hm := hS hi
    unfold honestSeats at hm
    exact (Finset.mem_filter.mp hm).2
  have hGSTa : E.t_GST ≤ p.actionTime (pt.r + 2) := by
    refine hGST.trans ?_
    have hle := kmid_slot_scale_le p (Nat.mul_le_mul_right p.R
      (show pt.r ≤ pt.r + 2 by omega))
    have hd := p.deltaPos
    change 4 * p.Δ * ((pt.r * p.R : Nat) : Time) ≤
      4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Time) + 6 * p.Δ
    linarith
  have result := FGCompose.rowsPrem_fresh_rows (d7a4rp_middle_to p c E rho ΔF pt A m)
    (by simpa only [d7a4rp_observations_eq] using (fgCertificateLaws p).height)
    (by simpa only [d7a4rp_observations_eq] using heightView_bridge p)
    (d7a4rp_makeWire p)
    (by intro row; rw [fgsaSafetyReads_def]; rfl)
    (by
      intro i y U B
      change (decide (1 ≤ y + 1) && decide (y < y + 1)) = true
      simp only [Nat.le_add_left, Nat.lt_succ_self, decide_true, Bool.and_self])
    (by intro nd; rw [d7a4rp_reads_eq, fgsaSafetyReads_def]; rfl)
    (by
      intro i q nd row hn hw hr
      simp only [fgsaSafetyReads_def] at hr
      simp only [d7a4rp_holder, d7a4rp_action_eq] at hn hw
      obtain ⟨j, hj, he⟩ := d7a4rp_release p c E rho i q nd row hn hw hr
      refine ⟨j, ?_, ?_⟩
      · simpa only [d7a4rp_holder, d7a4rp_action_eq] using hj
      · rw [fgsaSafetyReads_def]
        exact he)
    (by
      delta d7a4rp_middle_to
      simpa only [d7a4rp_observations_eq, d7a4rp_timing_eq,
        d7a4rp_reads_eq, d7a4rp_f_postClock_eq]
        using rowsPrem_action_source p c E rho hK m hQC hXing hNames)
    (by
      delta d7a4rp_middle_to
      simpa only [d7a4rp_observations_eq, d7a4rp_timing_eq,
        d7a4rp_reads_eq, d7a4rp_f_postClock_eq]
        using rowsPrem_pending_head p c E rho hK m hServices hQC hXing hNames)
    (by
      intro nd H hH
      rw [d7a4rp_reads_eq] at hH
      simpa only [fgsaSafetyReads_def, d7a4rp_observations_eq,
        certificateHeadFields_def] using fgInputs_headFields p nd.st H hH)
    (by
      intro x nd hx hn
      rw [d7a4rp_action_eq, d7a4rp_f_postClock_eq] at hn
      obtain ⟨ht, hto, hl, htn, hton, hln, hsent⟩ :=
        rowsPrem_action_record p c E rho m hK hQC hNames x nd hx hn
      delta d7a4rp_middle_to
      simp only [fgsaSafetyReads_def]
      exact ⟨⟨ht, hto, hl⟩, htn, hton, hln, hsent⟩)
    (d7a4rp_timing_laws p) S
    (by simpa only [d7a4rp_holder] using hhonest) hQ
    (fun x hx => hK.set.awake x hx _ hGSTa m.actionsInRun)
  obtain ⟨rows, fresh, entry, pair⟩ := result
  refine ⟨rows, ?_, entry, pair⟩
  rw [FreshFinalityRows_W_def]
  delta FGCompose.FreshFinalityRows_W at fresh
  simp only [d7a4rp_holder] at fresh
  obtain ⟨_, _, seat⟩ := fresh
  refine ⟨hS, hQ, ?_⟩
  intro i hi
  obtain ⟨j, C, ha, hc, hsign, hh, hn, hsrc, hCh, hearlier⟩ := seat i hi
  refine ⟨j, C, (d7a4rp_row_eq p c E rho j _ _ _).mp ha,
    (d7a4rp_complete_eq p c rho _ _).mp hc, (d7a4rp_signer_iff p _ i).mp hsign,
    hh, hn, (d7a4rp_source_eq p c E rho _ _) ▸ hsrc, hCh, ?_⟩
  intro j' r a h hr ha hh
  exact hearlier j' r a h hr ((d7a4rp_row_eq p c E rho j' r _ a).mpr ha) hh

include hK in
/-- Paper 22:1265–1289: held blocks through the next action cut have height at most d+3.
Emitted names put each earlier honest row at its action source; K-MID caps that source.
DC: INTENTIONAL: held/read causal cap; Assembly supplies the causal-origin bound. -/
theorem rowsPrem_anchor_cap
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (p.actionTime (pt.r + 3)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ m.d + 3 := by
  have result := FGCompose.rowsPrem_anchor_cap (d7a4rp_middle_to p c E rho ΔF pt A m)
    (fgsaCoreLaws p c) (d7a4rp_timing_laws p) hK.set.base.valid.toScheduleWellFormed
    (d7a4rp_f_names p c E rho hNames) (by
      intro cut b i x W hi hh hrows
      apply hcapBefore cut b i x W hi ((d7a4rp_held_eq p c E rho i x W).mp hh)
      intro j z r a u h B timeout ha hu hp ht
      apply hrows j z r a u h B timeout ((d7a4rp_row_eq p c E rho j r z a).mpr ha)
      · simpa only [fgsaSafetyReads_def] using hu
      · exact hp
      · exact ht)
  revert result
  delta d7a4rp_middle_to
  intro result
  simpa only [d7a4rp_observations_eq, d7a4rp_timing_eq,
    d7a4rp_held_eq] using result

/-- Paper 22:1265–1289: the anchor carrier keeps the actual pending key or is covered.
DC: INTENTIONAL: W retention with K_W ≥ 2 at K-MID's retained D; no acceptance claim. -/
theorem rowsPrem_anchor_retained_or_covered (P : FGBlock (Fin p.n))
    (hDP : FGBlock.Preceq m.X_D P) (hcap : (heightView p P).h ≤ m.d + 3) :
    Window.RetainedW p P (m.d + 1) m.U ∨ Window.CoveredW p P (m.d + 1) m.U := by
  have result := FGCompose.rowsPrem_anchor_retained_or_covered
    (d7a4rp_middle_to p c E rho ΔF pt A m) (by
      simpa only [d7a4rp_observations_eq, KitFG.Window.heightView_def]
        using d7a4rp_w_height_eq p)
    (d7a4rp_w_nonempty p) p.kWLarge P hDP hcap
  revert result
  delta d7a4rp_middle_to
  intro result
  simpa only [d7a4rp_w_retained_eq, d7a4rp_w_covered_eq] using result

end AvailableChain.FGSA.Run
end
