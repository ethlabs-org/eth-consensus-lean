module
public import AvailableChainFGCompose.Proofs.Finality.Joined
public import AvailableChainFGCompose.Proofs.Finality.Local
public import AvailableChainFGSAProofs.Proofs.Assembly.Healing
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival
public import AvailableChainFGSAProofs.Proofs.Finality.Forward
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Finality.Receipt
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers
public import AvailableChainFGSAProofs.Proofs.Finality.RowsBatch
public import AvailableChainFGSAProofs.Proofs.Finality.RowsFrame
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGSAProofs.Proofs.Shared.Gate
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads
public meta import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (cached prefix checks)

set_option linter.privateModule false
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

/-! P0d7c: the generic finality chain on one bounded FG-SA run, through private test
adapters. Part 1 (namespace AvailableChain.FGSA.Run): private fieldwise instances of the
generic reads and the producers of every generic kernel argument from FG-SA facts. The
`d7n_*` block is copied verbatim from Proofs/Finality/Middle.lean (private there). -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

section

private abbrev d7nw_Old := FGSA.Window.State
private abbrev d7nw_New := SimplexFG.Window.State

private def d7nw_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7nw_toWindow {V : Type} (w : d7nw_Old V) : d7nw_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7nw_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7nw_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7nw_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7nw_state_eq {V : Type} (w : d7nw_Old V) :
    d7nw_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7nw_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7nw_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7nw_toEntry e).j = e.j ∧ (d7nw_toEntry e).X = e.X ∧ (d7nw_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7nw_state_fields {V : Type} (w : d7nw_Old V) :
    (d7nw_toWindow w).L = w.L ∧ (d7nw_toWindow w).s = w.s ∧
    (d7nw_toWindow w).h = w.h ∧ (d7nw_toWindow w).T_h = w.T_h ∧
    (d7nw_toWindow w).target_participation = w.target_participation ∧
    (d7nw_toWindow w).progress = w.progress ∧ (d7nw_toWindow w).W = w.W.map
      d7nw_toEntry ∧
    (d7nw_toWindow w).J = w.J ∧ (d7nw_toWindow w).h_j = w.h_j ∧
    (d7nw_toWindow w).F = w.F ∧ (d7nw_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7nw_initial_eq {V : Type} :
    d7nw_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7nw_foldRow_eq (w : d7nw_Old V) (a : Row V) :
    d7nw_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7nw_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7nw_toEntry =
      (w.W.map d7nw_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7nw_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7nw_state_eq] using
        congrArg (fun es => ({ d7nw_toWindow w with W := es } : d7nw_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7nw_state_eq] <;> rw [bits] <;> simp_all [d7nw_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7nw_rows_eq (rs : List (Row V)) (w : d7nw_Old V) :
    d7nw_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7nw_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7nw_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7nw_advance_eq (w : d7nw_Old V) :
    d7nw_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7nw_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7nw_greatest_eq (E : Electorate V) (w : d7nw_Old V) :
    (FGSA.Window.greatestReady E w).map d7nw_toEntry =
      SimplexFG.Window.greatestReady E (d7nw_toWindow w) := by
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
      (oldStep best e).map d7nw_toEntry = newStep (best.map d7nw_toEntry)
      (d7nw_toEntry e) := by
    dsimp [oldStep, newStep, d7nw_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7nw_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7nw_toEntry =
        (es.map d7nw_toEntry).foldl newStep (best.map d7nw_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7nw_toWindow w) =
      (w.W.map d7nw_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7nw_finalize_eq (E : Electorate V) (w : d7nw_Old V) :
    d7nw_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7nw_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7nw_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7nw_state_eq, d7nw_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7nw_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7nw_toEntry =
      (es.map d7nw_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7nw_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7nw_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7nw_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7nw_Old V) :
    d7nw_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7nw_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7nw_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7nw_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7nw_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7nw_state_eq, d7nw_entry_eq, List.map_drop]

private theorem d7nw_transition_eq (p : Params) (K : Nat) (w : d7nw_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7nw_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7nw_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7nw_events_eq, SimplexFG.Window.transition_def]
  have h := d7nw_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7nw_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7nw_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7nw_toWindow where
  initial := d7nw_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7nw_transition_eq p K

private theorem d7nw_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7nw_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7nw_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d7n_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7n_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7n_timing p) where
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

private theorem d7n_action_eq (p : Params) (q : Nat) :
    (d7n_timing p).action q = p.actionTime q := rfl

private theorem d7n_reads_eq : fgsaCoreReads p c =
    { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
      erase := eraseFG
      source := fun nd => FGSA.fgSource p nd.st
      headVote := fun nd s => FGSA.headVote p nd.st s
      finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
      proposalFG := (fgsaCoreReads p c).proposalFG } :=
  congrArg (fun reads => { reads with proposalFG := (fgsaCoreReads p c).proposalFG })
    (fgsaCoreReads_def p c)

private def d7n_safety (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem d7nw_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7nw_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7nw_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7nw_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7nw_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7nw_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7nw_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7nw_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7nw_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7nw_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7n_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def d7n_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7n_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7n_wire : FGCompose.FGHistoryWireReads (d7n_safety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7n_signer p
  decode_height a u ha := by
    delta d7n_safety at ha
    rw [d7n_decode p ha]
    rfl
  decode_finality a u ha := by
    delta d7n_safety at ha
    rw [d7n_decode p ha]
    rfl
  decode_signer a u ha := by
    delta d7n_safety at ha
    rw [d7n_decode p ha]
    rfl

private theorem d7n_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (d7n_safety p c) E rho (d7n_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by delta d7n_safety; rfl

private theorem d7n_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7n_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7n_reads_eq]; rfl

private theorem d7n_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7n_reads_eq]
  rfl

private def d7n_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7n_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) : FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c)
      (d7n_observations p c) (d7n_timing p) E rho (fgsaInterface p c)
      (d7n_point p w) horizon := by
  intro x r C hx hsrc hhigh _ s Q hQ _ hgap
  change FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7n_timing p) x r =
    some (some C) at hsrc
  rw [d7n_source_eq, d7n_reads_eq] at *
  exact h x r C s Q hx hsrc hhigh hQ hgap

private theorem d7n_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (d7n_safety p c) (d7n_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7n_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (d7n_safety p c) (d7n_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7n_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

private theorem d7n_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (d7n_safety p c)
      (d7n_observations p c) (d7n_timing p) E rho (d7n_wire p c) := by
  intro j x r a e ha he
  rw [d7n_row_eq] at ha
  obtain ⟨C, hC, hpair⟩ := h j x r a e ha he
  exact ⟨C, (d7n_source_eq p c E rho x r).trans hC, hpair⟩

private theorem d7n_emitted_seat (j : Nat) (x : V) (r : Nat) (a : RowWire p.n)
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

private theorem d7n_emission :
    FGCompose.HighRecordEmission (d7n_safety p c) (d7n_timing p) E rho p.E p.cfg := by
  intro j x r a u ha hd
  rw [d7n_row_eq] at ha
  change a.toRow? = some u at hd
  have hsend := (kmid_row_action p c E rho ha).2
  have hj : (attest p
      ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
      (V2.D.Run.stateBefore E rho j x).record u.signer).1 = some a.payload := by
    rw [← attest_signer_irrel _ _ ⟨0, p.nPos⟩ u.signer]
    exact hsend
  obtain ⟨row, hrow, hp⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨_, _, _, _, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg _ u.signer _ _ hrow
  have hwire : RowWire.toRow? (⟨.seat .fg u.signer, a.payload⟩ : RowWire p.n) = some u := by
    rw [d7n_decode p hd]
    rfl
  have heq : row = u := by
    rw [← hp, he] at hwire
    rw [he]
    exact Option.some.inj hwire
  exact heq ▸ hrow

private theorem d7n_decoded : ∀ j x r a,
    FGCompose.HonestRowAt (d7n_safety p c) E rho (d7n_timing p) j x r a →
    ∃ u, (d7n_safety p c).decode a = some u := by
  intro j x r a ha
  obtain ⟨seat, hs⟩ := d7n_emitted_seat p c E rho j x r a
    ((d7n_row_eq p c E rho j r x a).mp ha)
  refine ⟨⟨seat, a.payload.height_pair, a.payload.finality_pair⟩, ?_⟩
  rcases a with ⟨auth, ⟨body⟩⟩
  dsimp only at hs
  subst auth
  rfl

private theorem d7n_tree_restore : FGCompose.FGTreeRestoreLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [d7n_reads_eq]
  exact congrArg (fun st => st.TF) (acRestart_fg p nd.st t)

private theorem d7n_tree_keep : FGCompose.FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [(d7n_tree_restore p c).restart_eq]

private theorem d7n_faulty_eq : FGCompose.historyFaulty (d7n_safety p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [FGCompose.safetyHolder_def]
  delta d7n_safety
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private theorem d7n_origin
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
    HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
      ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    FGCompose.RawHistoryOrigin (fgsaCoreReads p c)
    (d7n_safety p c) E rho (d7n_timing p) (d7n_wire p c) := by
  intro i x B hh u hu
  rw [d7n_held_eq] at hh
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := horigin i x B hh u hu
  refine ⟨a, r, ?_, ?_, k, o, t, hki, hk, ?_⟩
  · delta d7n_safety
    exact ha
  · change d7n_signer p a = some u.signer
    rw [d7n_decode p ha]
    rfl
  · intro z hz hhonest
    obtain ⟨seat, hseat, hholder⟩ := hz
    have hseat' : a.auth = .seat .fg seat := by
      change d7n_signer p a = some seat at hseat
      rw [d7n_decode p ha] at hseat ⊢
      have eq := Option.some.inj hseat
      rw [eq]
    have hholder' : rho.seatOf (.base .fg) seat = z := by
      change FGCompose.safetyHolder (d7n_safety p c) rho seat = z at hholder
      rw [FGCompose.safetyHolder_def] at hholder
      delta d7n_safety at hholder
      exact hholder
    obtain ⟨⟨j, hji, hj⟩, hrt⟩ := he z ⟨seat, hseat', hholder'⟩ hhonest
    exact ⟨⟨j, hji, (d7n_row_eq p c E rho j r z a).mpr hj⟩, hrt⟩

private def d7n_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7n_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7n_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private theorem d7n_validRows (st : State p.n) (hr : Reachable p st) :
    ∀ X ∈ st.fg.TF, ∀ row ∈ X.rows,
      SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W X.parent) row = true := by
  intro X hX row hrow
  cases X with
  | genesis => exact (List.not_mem_nil hrow).elim
  | node Q t root x rs =>
    have hv := stored_r6wW p hr Q t root x rs hX row hrow
    change SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W Q) row = true
    rw [← d7nw_derive_eq]
    cases hp : row.height_pair <;> cases hf : row.finality_pair <;>
      simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
      SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
      SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
      d7nw_state_eq, d7nw_entry_eq, List.any_map, Function.comp_def, hp, hf,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff, List.any_eq_true, decide_eq_true_eq] at hv ⊢
    all_goals first | exact hv | skip
    rcases hv with hm | ⟨h, e, he, hpair⟩
    · exact Or.inl hm
    · exact Or.inr ⟨h, e, he, decide_eq_true hpair⟩

private def d7n_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7n_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7n_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7n_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7n_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem d7n_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

private theorem d7n_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7n_proposal_payload p o s N ((d7n_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7n_decodeProposal_iff p o s N).mpr
      (d7n_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7n_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7n_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7n_signer; simp
  | proposer s => delta d7n_signer; simp
  | seat label j => cases label <;> delta d7n_signer <;> simp

private theorem d7n_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7n_wire p c).heightPair) (d7n_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] in
private theorem d7n_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (d7n_safety p c) rho (d7n_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7n_signer_iff, FGCompose.safetyHolder_def]
  delta d7n_safety
  rfl

private theorem d7n_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (d7n_safety p c) E rho (d7n_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  delta FGCompose.TRowsReceipt
  rw [TRowsReceipt_def]
  delta FGCompose.HeldBefore HeldBefore
  rw [d7n_reads_eq]
  simp only [d7n_row_eq]
  rfl

private theorem d7n_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7n_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private abbrev d7n_Batch (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (fgsaCoreReads p c) (d7n_safety p c) (d7n_observations p c)
    (d7n_timing p) E rho (fgsaInterface p c) (d7n_wire p c) p.E
    (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF (d7n_kind k) q y U X

private theorem d7n_batch_from [Fintype V] (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (k : RowKind) (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : d7n_Batch p c E rho ΔF k q y U X) : BatchPrem p c E rho ΔF k q y U X := by
  refine ⟨base, faultQ, h.deltaF, (d7n_receipt_eq p c E rho ΔF).mp h.rowsReceipt,
    h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · have hc := h.carrier
    rw [d7n_reads_eq] at hc
    dsimp only [d7n_safety] at hc
    simpa only [d7n_carrier_eq] using hc
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ?_, (d7n_signer_iff p a i).mp hsign,
      (d7n_namesEntry p c k a y U).mp hn, ht, htime, ?_, ?_⟩
    · exact (d7n_row_eq p c E rho j r _ a).mp ha
    · rw [d7n_reads_eq] at hv
      exact (d7n_validParent_eq p c E rho _ _ a).mp hv
    · rw [d7n_reads_eq] at hm
      exact (d7n_heightMatch_eq p c E rho _ _ a).mp hm
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW
      (by simpa only [d7n_rowNames] using hr)

private theorem d7n_matching_valid (s : Slot) (H : FGBlock (Fin p.n))
    (a : RowWire p.n) (hv : a.valid = true)
    (hm : FGCompose.namedEntry a.payload.height_pair =
      some ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root)) :
    Window.rowValidW (parentFoldState p s H) a = true := by
  have ha : ∃ i, a.auth = .seat .fg i := by
    rcases a with ⟨auth, body⟩
    cases auth with
    | none => cases hv
    | proposer v => cases hv
    | seat label i => cases label with
      | head v => cases hv
      | fg => exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := ha
  refine (Window.rowValidW_iff _ a).mpr ⟨_, kmid_wire_toRow p hi, Or.inl ?_⟩
  rw [Window.heightMatch_def]
  cases hp : a.payload.height_pair with
  | empty => rw [hp] at hm; cases hm
  | vote h root timeout =>
    rw [hp] at hm
    have eq := Option.some.inj hm
    simp only [NamedHeightPair.matchesEntry, (Prod.mk.inj eq).1, (Prod.mk.inj eq).2,
      and_self, decide_true, eq_self]

private def d7n_ac (w : HealingWitness) : FGCompose.FGACServiceReads V where
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

private theorem d7n_head_eq (x : V) (s : Slot) :
    FGCompose.headAtLabel (fgsaCoreReads p c) E rho (d7n_timing p) x s =
      headAtLabel p c E rho x s := by rw [d7n_reads_eq]; rfl

private theorem d7n_honestProposal_eq (s : Slot) (Q : Block) :
    FGCompose.HonestProposal E rho (fgsaInterface p c) s Q =
      HonestProposal E rho (fgsaInterface p c) s Q := rfl

private theorem d7n_opening_eq (s : Slot) (A : Block) (X : FGBlock (Fin p.n)) :
    FGCompose.OpeningCarrier_W (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows
      (fun nd : Node p => FGSA.parentFG nd.st) FGSA.fgBlock E rho (fgsaInterface p c)
      s A X = OpeningCarrier_W p c E rho s A X := by
  apply propext
  rw [OpeningCarrier_W_def]
  constructor
  · rintro ⟨o, N, nd, Par, he, hN, hd, hnd, hpar, hfg⟩
    refine ⟨o, N, nd.st, Par, he, hN, (d7n_decodeProposal_iff p o s N).mp hd, ?_, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _
    rw [hnd]
    rfl
  · rintro ⟨o, N, st, Par, he, hN, hd, hst, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _ at hst
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨o, N, nd, Par, he, hN, (d7n_decodeProposal_iff p o s N).mpr hd, hnd, hpar, hfg⟩

private theorem d7n_exact (w : HealingWitness) (s : Slot) (Q : Block)
    (h : ExactService p c E rho s Q) :
    FGCompose.KernelExactService (d7n_ac p c E rho w) rho.horizon s Q := by
  refine ⟨h.1, ?_⟩
  intro hh x hx hc
  have hgate := h.2 hh x hx hc
  exact ⟨hgate.1, hgate.2.2.2.2⟩

private theorem d7n_batch_to [Fintype V] (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) (h : BatchPrem p c E rho ΔF k q y U X) :
    d7n_Batch p c E rho ΔF k q y U X := by
  refine ⟨h.base.valid.toScheduleWellFormed, ?_, h.deltaF,
    (d7n_receipt_eq p c E rho ΔF).mpr h.rowsReceipt, h.horizon, ?_, h.after,
    ?_, h.entry, h.path, ?_⟩
  · rw [d7n_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  · have hc := h.carrier
    delta d7n_safety
    rw [d7n_reads_eq]
    simpa only [d7n_carrier_eq] using hc
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mp (hh hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, (d7n_row_eq p c E rho j r _ a).mpr ha,
      (d7n_signer_iff p a i).mpr hsign, (d7n_namesEntry p c k a y U).mpr hn, ht, htime,
      ?_, ?_⟩
    · rw [d7n_reads_eq]
      exact (d7n_validParent_eq p c E rho _ _ a).mpr hv
    · rw [d7n_reads_eq]
      exact (d7n_heightMatch_eq p c E rho _ _ a).mpr hm
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mpr hi) W hW
      (by simpa only [d7n_rowNames] using hr)

private abbrev d7n_Middle (ΔF : Time) (pt : KernelPt) (A : Block) :=
  FGCompose.KernelMiddleWitness_W (fgsaCoreReads p c) (d7n_safety p c)
    (d7n_observations p c) (d7n_timing p) E rho (fgsaInterface p c) (d7n_wire p c) p.E
    (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) FGSA.fgBlock RowWire.valid
    (d7n_ac p c E rho pt.w) p.cfg p.K_W ΔF (d7n_point p pt.w) ⟨pt.r⟩ A


private theorem d7n_fg (nd : (fgsa p c).State) : ((fgsaCoreReads p c).core nd).fg = nd.st.fg := by
  rw [d7n_reads_eq p c]

private theorem d7n_erase (C : FGBlock (Fin p.n)) :
    (fgsaCoreReads p c).erase C = eraseFG C := by
  rw [d7n_reads_eq p c]

private theorem d7n_roundSlots_eq : (d7n_timing p).roundSlots = p.R := rfl

omit [DecidableEq V] in
private theorem d7n_cut_eq (t : Time) : FGCompose.afterTicksIdx rho t =
    afterTicksIdx rho t := rfl

private theorem d7n_storeAt_eq (i : Nat) (x : V) :
    storeAt p c E rho i x = (V2.D.Run.stateBefore E rho i x).st := rfl

private theorem d7n_chain_eq [Fintype V] (X : FGBlock (Fin p.n)) (cut : Time) :
    FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho X cut =
      ChainRowsBefore p c E rho X cut := by rw [d7n_reads_eq]; rfl

private def d7n_middle_to [Fintype V] (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) : d7n_Middle p c E rho ΔF pt A where
  A₀ := m.A₀
  B := m.B
  U := m.U
  X_D := m.X_D
  cD := m.cD
  d := m.d
  opening := m.opening
  eraseA := (d7n_erase p c m.A₀).trans m.eraseA
  carrierA := by
    have h := m.carrierA
    exact (d7n_opening_eq p c E rho _ _ _).mpr h
  carrierB := by
    have h := m.carrierB
    rw [d7n_erase]
    exact (d7n_opening_eq p c E rho _ _ _).mpr h
  carrierD := by
    have h := m.carrierD
    rw [d7n_erase]
    exact (d7n_opening_eq p c E rho _ _ _).mpr h
  honestB := by simpa only [d7n_erase, d7n_honestProposal_eq, d7n_roundSlots_eq] using m.honestB
  honestD := by simpa only [d7n_erase, d7n_honestProposal_eq] using m.honestD
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
  sourceA := by simpa only [d7n_source_eq] using m.sourceA
  sourceB := by simpa only [d7n_source_eq] using m.sourceB
  serviceD := by
    rw [d7n_erase]
    exact d7n_exact p c E rho pt.w _ _ m.serviceD
  heightD := m.heightD
  justifiedD := m.justifiedD
  justifiedHeightD := m.justifiedHeightD
  pendingD := by
    rw [← d7nw_derive_eq]
    exact m.pendingD
  retainedD := (d7nw_retained_eq p _ _ _).mpr m.retainedD
  noFirstHeight := by
    simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq] using m.noFirstHeight
  noSecondHeight := by
    simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq] using m.noSecondHeight
  noEarlyFinality := by
    simpa only [d7n_row_eq, d7n_finHeight_eq, d7n_event_eq, d7n_action_eq] using m.noEarlyFinality
  chainA := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainA
  chainB := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainB
  chainD := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainD
  freshD := {
    schedule := m.freshD.base.valid.toScheduleWellFormed
    fault_weight := by
      rw [d7n_faulty_eq]
      exact kmid_faulty_weight p c E rho m.freshD.base m.freshD.faultQ
    cut := m.freshD.cut
    early := m.freshD.early
    rows := by simpa only [d7n_chain_eq] using m.freshD.rows
    noNextRow := by
      simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq]
        using m.freshD.noNextRow
    noFinRow := by
      simpa only [d7n_row_eq, d7n_finHeight_eq, d7n_event_eq, d7n_action_eq]
        using m.freshD.noFinRow }
  noMixedD := m.noMixedD
  batchB := fun hp => d7n_batch_to p c E rho ΔF .target _ _ _ _ (m.batchB hp)
  batchD := fun hp => d7n_batch_to p c E rho ΔF .target _ _ _ _ (m.batchD hp)
  targetsB := by
    intro x hx
    obtain ⟨j, a, ha, hc, hn⟩ := m.targetsB x hx
    exact ⟨j, a, (d7n_row_eq p c E rho j _ x a).mpr ha,
      (d7n_complete_eq p c rho x a).mpr hc,
      (d7n_namesEntry p c .target a _ _).mpr hn⟩
  actionsInRun := m.actionsInRun
  capThroughBAction := fun i x W hi hcut hh =>
    m.capThroughBAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mp hh)
  capThroughFinalAction := fun i x W hi hcut hh =>
    m.capThroughFinalAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mp hh)
  finalityThroughFinalAction := fun i x W hi hcut hh =>
    m.finalityThroughFinalAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mp hh)
  heldDAtFinalAction := by
    simpa only [d7n_fg, d7n_storeAt_eq, d7n_action_eq, d7n_cut_eq] using m.heldDAtFinalAction
  heldAAtEnd := by
    simpa only [d7n_fg, d7n_storeAt_eq] using m.heldAAtEnd

private def d7n_middle_from [Fintype V] (G ΔF : Time) (pt : KernelPt) (A : Block)
    (hK : KernelPrem_W p c G ΔF E rho pt) (m : d7n_Middle p c E rho ΔF pt A) :
    KernelMiddleWitness_W p c E rho ΔF pt A where
  A₀ := m.A₀
  B := m.B
  U := m.U
  X_D := m.X_D
  cD := m.cD
  d := m.d
  opening := m.opening
  eraseA := (d7n_erase p c m.A₀).symm.trans m.eraseA
  carrierA := by
    have h := m.carrierA
    exact (d7n_opening_eq p c E rho _ _ _).mp h
  carrierB := by
    have h := m.carrierB
    rw [d7n_erase] at h
    exact (d7n_opening_eq p c E rho _ _ _).mp h
  carrierD := by
    have h := m.carrierD
    rw [d7n_erase] at h
    exact (d7n_opening_eq p c E rho _ _ _).mp h
  honestB := by simpa only [d7n_erase, d7n_honestProposal_eq, d7n_roundSlots_eq] using m.honestB
  honestD := by simpa only [d7n_erase, d7n_honestProposal_eq] using m.honestD
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
  sourceA := by simpa only [d7n_source_eq] using m.sourceA
  sourceB := by simpa only [d7n_source_eq] using m.sourceB
  serviceD := by
    apply kmid_window_exact hK
    · simpa only [d7n_erase, d7n_honestProposal_eq] using m.honestD
    · have h := m.earlySlot.1
      have hlo := Nat.mul_le_mul_right p.R (Nat.le_succ pt.r)
      exact hlo.trans (Nat.le_trans (Nat.le_add_right _ _) h)
  heightD := m.heightD
  justifiedD := m.justifiedD
  justifiedHeightD := m.justifiedHeightD
  pendingD := by
    have h := m.pendingD
    rw [← d7nw_derive_eq] at h
    exact h
  retainedD := (d7nw_retained_eq p _ _ _).mp m.retainedD
  noFirstHeight := by
    simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq] using m.noFirstHeight
  noSecondHeight := by
    simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq] using m.noSecondHeight
  noEarlyFinality := by
    simpa only [d7n_row_eq, d7n_finHeight_eq, d7n_event_eq, d7n_action_eq] using m.noEarlyFinality
  chainA := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainA
  chainB := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainB
  chainD := by simpa only [d7n_chain_eq, d7n_action_eq] using m.chainD
  freshD := {
    base := hK.set.base
    faultQ := hK.set.faultQ
    cut := m.freshD.cut
    early := m.freshD.early
    rows := by simpa only [d7n_chain_eq] using m.freshD.rows
    noNextRow := by
      simpa only [d7n_row_eq, d7n_rowHeight_eq, d7n_event_eq, d7n_action_eq]
        using m.freshD.noNextRow
    noFinRow := by
      simpa only [d7n_row_eq, d7n_finHeight_eq, d7n_event_eq, d7n_action_eq]
        using m.freshD.noFinRow }
  noMixedD := m.noMixedD
  batchB := fun hp =>
    d7n_batch_from p c E rho ΔF hK.set.base hK.set.faultQ .target _ _ _ _ (m.batchB hp)
  batchD := fun hp =>
    d7n_batch_from p c E rho ΔF hK.set.base hK.set.faultQ .target _ _ _ _ (m.batchD hp)
  targetsB := by
    intro x hx
    obtain ⟨j, a, ha, hc, hn⟩ := m.targetsB x hx
    exact ⟨j, a, (d7n_row_eq p c E rho j _ x a).mp ha,
      (d7n_complete_eq p c rho x a).mp hc,
      (d7n_namesEntry p c .target a _ _).mp hn⟩
  actionsInRun := m.actionsInRun
  capThroughBAction := fun i x W hi hcut hh =>
    m.capThroughBAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mpr hh)
  capThroughFinalAction := fun i x W hi hcut hh =>
    m.capThroughFinalAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mpr hh)
  finalityThroughFinalAction := fun i x W hi hcut hh =>
    m.finalityThroughFinalAction i x W hi hcut ((d7n_held_eq p c E rho i x W).mpr hh)
  heldDAtFinalAction := by
    simpa only [d7n_fg, d7n_storeAt_eq, d7n_action_eq, d7n_cut_eq] using m.heldDAtFinalAction
  heldAAtEnd := by
    simpa only [d7n_fg, d7n_storeAt_eq] using m.heldAAtEnd


private theorem d7n_entry_eq (a : NamedHeightPair) : FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem d7n_height_row_eq (r h : Nat) :
    FGCompose.HeightRow (d7n_safety p c) E rho (d7n_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) r h =
      HeightRow p c E rho r h := by
  dsimp only [FGCompose.HeightRow, HeightRow] at *
  simp only [d7n_row_eq, d7n_entry_eq]

private theorem d7n_mu_eq :
    FGCompose.muOf (d7n_safety p c) E rho (d7n_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      muOf p c E rho := by
  unfold FGCompose.muOf FGCompose.oldRowHeights muOf oldRowHeights
  simp only [d7n_row_eq, d7n_entry_eq]
  rfl

private theorem d7n_reset (w : HealingWitness) (h : H0Reset p c E rho w) :
    FGCompose.H0Reset (fgsaCoreReads p c) (d7n_safety p c) E rho
      (d7n_observations p c) (d7n_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E)
      (d7n_point p w).reset := by
  refine ⟨h.rG_after, h.rG_first, h.cut, ?_, ?_, ?_,
    h.cut_lower, h.cut_upper, ?_, ?_, h.label, ?_, h.synchronous⟩
  · have hf := h.frontier
    dsimp only [d7n_point, FGCompose.honestFrontier, honestFrontier] at hf ⊢
    simpa only [d7n_fg] using hf
  · dsimp only [d7n_point] at *
    simpa only [d7n_row_eq, d7n_entry_eq] using h.rowCap
  · dsimp only [d7n_point] at *
    simpa only [d7n_mu_eq] using h.mu_le
  · dsimp only [d7n_point] at *
    simpa only [d7n_height_row_eq] using h.reset_row
  · dsimp only [d7n_point] at *
    simpa only [d7n_height_row_eq] using h.reset_first
  · have hf := h.fresh
    dsimp only [d7n_point] at *
    simp only [d7n_row_eq, d7n_entry_eq, d7n_source_eq] at hf ⊢
    dsimp only [d7n_observations] at *
    simpa only [d7n_erase] using hf

private theorem d7n_empty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem d7n_kernel [Fintype V] {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) (hδ : p.δt = 2 * p.R) :
    FGCompose.KernelPrem_W (d7n_timing p) ΔF rho.horizon (d7n_point p pt.w)
      ⟨pt.r⟩ (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.E.q
      (p.E.weightOf (Finset.univ \ FGCompose.historyFaulty (d7n_safety p c) rho))
      p.cfg.timeoutDelay p.K_W where
  bound := ⟨hK.bound.kappa_le_R⟩
  window := hK.window
  start := hK.start
  hhor := hK.hhor
  honest_quorum := by
    have eq : Finset.univ \ FGCompose.historyFaulty (d7n_safety p c) rho =
        honestSeats p c rho := by
      rw [d7n_faulty_eq]
      ext i
      simp
    rw [eq]
    exact kmid_honest_quorum p c rho hK.set.base.linked hK.set.fault
  timeout_eq := hδ
  capacity_ge := p.kWLarge

private theorem d7n_carrier {s : Slot} {Q : Block}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hp : FGCompose.HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ X : FGBlock (Fin p.n), (fgsaCoreReads p c).erase X = Q ∧
      FGCompose.OpeningCarrier_W (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows
        (fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent) FGSA.fgBlock
        E rho (fgsaInterface p c) s Q X ∧ X.slot = s ∧
      (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
        (FGCompose.kernelCarrier (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows)
        s Q rows ∧ X.rows = rows.filterMap (d7n_safety p c).decode) ∧
      ∃ nd, FGCompose.proposalStateAt E rho (fgsaInterface p c) s = some nd ∧
        FGSA.fgBlockOf nd.st Q.parent = some X.parent ∧
        X.parent ∈ ((fgsaCoreReads p c).core nd).fg.TF := by
  obtain ⟨X, he, hc, hslot, hrows, st, hst, hlookup, hparent⟩ :=
    kmid_opening_carrier p c E rho hs hp
  change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = some st at hst
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨X, ?_, (d7n_opening_eq p c E rho _ _ _).mpr hc, hslot, ?_, nd, hnd, hlookup, ?_⟩
  · rw [d7n_reads_eq]
    exact he
  · delta d7n_safety
    simpa only [d7n_carrier_eq] using hrows
  · rw [d7n_reads_eq]
    exact hparent

private theorem d7n_proposal_reachable (s : Slot) (nd : Node p)
    (hnd : FGCompose.proposalStateAt E rho (fgsaInterface p c) s = some nd) :
    Reachable p nd.st :=
  kmid_proposal_reachable p c E rho (Option.map_eq_some_iff.mpr ⟨nd, hnd, rfl⟩)


end

/-! Part 1b: further private adapters at the same instances. Copied from the private
sections of Proofs/Finality/{RowsPrem,RowsRecords,Carry,Receipt,Accept,RestoreReads}.lean
with the instance names of the block above. -/

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7n_safety_def : d7n_safety p c =
    { proposalErase := safetyProposalErase p
      proposalRows := safetyProposalRows p
      encode := ofRow p
      decode := RowWire.toRow?
      decodeObject := decodeRowObject p
      fgLabel := .base .fg
      fgSeats := Equiv.refl _
      record := Node.record
      inputs := fun nd => fgInputs p nd.st
      enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
      finalizedOut := finalizedOut } := rfl

private theorem d7n_safety_eq : d7n_safety p c = fgsaSafetyReads p c :=
  (d7n_safety_def p c).trans (fgsaSafetyReads_def p c).symm

private theorem d7n_timing_eq (p : Params) : d7n_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private theorem d7n_observations_eq : d7n_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

omit [DecidableEq V] in
private theorem d7n_holder (i : Fin p.n) :
    FGCompose.safetyHolder (d7n_safety p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, d7n_safety_def p c]
  rfl

private theorem d7n_f_postClock_eq (x : V) (t : Time) :
    FGCompose.postClock E rho x t = postClock E rho x t :=
  (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1.symm

private theorem d7n_f_entry_eq (a : NamedHeightPair) : FGCompose.namedEntry a = namedEntry a :=
    by
  cases a <;> rfl


private theorem d7nw_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7nw_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7n_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'


private theorem d7n_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (d7n_ac p c E rho w) (d7n_point p w)
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
    obtain ⟨j, _, hclock⟩ := d7n_clock_read p c E rho x (p.actionTime q) nd hnd
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

private theorem d7n_source_service (w : HealingWitness) (q opening : Nat)
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
    rw [d7n_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, hnd, hsource⟩
  · intro hlt
    have hcover := hcovered hlt
    obtain ⟨_hresult, _hpassed, nd, d, hnd, hwrite, hlease, _hdeadline, hlive⟩ :=
      h6 (q * p.R) (eraseFG D) ((Nat.le_add_right w.sStar 2).trans
        (hstart.trans hbefore)) hGST hhor hne hcover hFgate hx hhonest
    obtain ⟨j, _hj, hclock⟩ := d7n_clock_read p c E rho hx (p.actionTime q) nd hnd
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
    rw [d7n_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, C, hnd, hsource, hDC⟩

private def d7n_makeWire (row : Row (Fin p.n)) : RowWire p.n :=
  ⟨.seat .fg row.signer, .vote ⟨row.height_pair, row.finality_pair⟩⟩

private theorem d7n_release (i : Fin p.n) (q : Nat) (nd : Node p) (row : Row (Fin p.n))
    (hnd : FGCompose.postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd)
    (awake : E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true)
    (released : (createRowOnce p.E p.cfg nd.record i (fgInputs p nd.st).1
      (fgInputs p nd.st).2).1 = some row) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base .fg) i) (p.actionTime q)) ∧
      ofRow p (d7n_makeWire p row) ∈ V2.D.Run.emitsAt E rho j := by
  rw [← (fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1] at hnd
  obtain ⟨j, hj, hclock⟩ := d7n_clock_read p c E rho _ _ nd hnd
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


private def d7n_f_stored_carrier (p : Params) (nd : Node p) (B : FGBlock (Fin p.n))
    (wire : RowWire p.n) : Prop :=
  ∃ s N, N.erase = eraseFG B ∧
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧ wire ∈ N.rows

private def d7n_f_source_service (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (y : V) (r : Nat) (C : FGBlock (Fin p.n)) : Prop :=
  ∃ G, gateResult p c E rho y (r * p.R) = some (some G) ∧
    Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)

private theorem d7n_f_chain (w : HealingWitness) (h : THigh p c E rho w) (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (d7n_observations p c)
      (d7n_timing p) E rho (d7n_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [d7n_reads_eq p c] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem d7n_f_reflect (A B : FGBlock (Fin p.n))
    (h : Block.Preceq ((fgsaCoreReads p c).erase A) ((fgsaCoreReads p c).erase B)) :
    FGBlock.Preceq A B := by
  rw [d7n_reads_eq p c] at h
  exact eraseFG_preceq_iff.mp h

private theorem d7n_f_qc (h : RQCOrigin p c E rho) :
    FGCompose.RQCOrigin (fgsaCoreReads p c) (d7n_safety p c) E rho
      (d7n_observations p c) (d7n_timing p) (d7n_f_stored_carrier p)
      (d7n_f_source_service p c E rho) p.E := by
  have heq : FGCompose.RQCOrigin (fgsaCoreReads p c) (d7n_safety p c) E rho
      (d7n_observations p c) (d7n_timing p) (d7n_f_stored_carrier p)
      (d7n_f_source_service p c E rho) p.E = RQCOrigin p c E rho := by
    dsimp only [FGCompose.RQCOrigin, RQCOrigin, d7n_f_stored_carrier, d7n_f_source_service]
    simp only [d7n_fg, d7n_source_eq, d7n_safety_def p c, exists_and_left]
    rfl
  exact heq.symm ▸ h

private theorem d7n_f_head :
    FGCompose.HighRecordHead (fgsaCoreReads p c) (d7n_safety p c)
      (d7n_observations p c) E rho := by
  intro i x t _hx
  dsimp only [d7n_observations]
  rw [d7n_reads_eq p c, d7n_safety_def p c]
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

private theorem d7n_f_emission :
    FGCompose.HighRecordEmission (d7n_safety p c) (d7n_timing p) E rho p.E p.cfg := by
  intro j x r a u ha hd
  rw [d7n_row_eq] at ha
  rw [d7n_safety_def p c] at hd ⊢
  rw [d7n_decode p hd] at ha
  obtain ⟨_, _, _, _, hsend⟩ := (fgsa_emitsAt_row E rho j x _ ha.2.1 u.signer
    (.vote ⟨u.height_pair, u.finality_pair⟩)).mp ha.2.2
  exact (fgsa_attest_decode _ _ u.signer _ hsend).symm

private theorem d7n_f_own_row (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
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

private theorem d7n_f_own :
    FGCompose.HighRecordOwnOrigin (d7n_safety p c) (d7n_timing p) E rho := by
  rw [FGCompose.HighRecordOwnOrigin_def]
  intro j x o u hx ho hd
  rw [d7n_safety_def p c] at hd
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
          obtain ⟨r, hj, hem, _⟩ := d7n_f_own_row p c E rho j x seat body ho
          refine ⟨r, ⟨.seat .fg seat, body⟩, ?_, ?_⟩
          · rw [d7n_row_eq]; exact ⟨hx, hj, hem⟩
          · rw [d7n_safety_def p c]; exact hd

private theorem d7n_f_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (d7n_safety p c)
      (d7n_observations p c) (d7n_timing p) E rho (d7n_wire p c) := by
  intro j x r a entry ha hn
  rw [d7n_row_eq] at ha
  change FGCompose.namedEntry a.payload.height_pair = some entry at hn
  rw [d7n_f_entry_eq] at hn
  obtain ⟨C, hs, he⟩ := h j x r a entry ha hn
  exact ⟨C, (d7n_source_eq p c E rho x r).symm ▸ hs, he⟩

private theorem d7n_held (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a ↔ heldAtProposal p c E rho s a := by
  constructor
  · rintro ⟨nd, hn, ha⟩
    refine ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hn, rfl⟩, ?_⟩
    rw [d7n_reads_eq] at ha
    exact ha
  · rintro ⟨st, hs, ha⟩
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    rw [d7n_reads_eq]
    exact ha

private theorem d7n_selection (h : TRowsSelect p c E rho) :
    FGCompose.TRowsSelect (fgsaCoreReads p c) (d7n_safety p c) E rho (d7n_timing p)
      (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7n_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) := by
  intro s Q rows j x r a hc ha hv hh
  rcases h s Q rows j x r a ((d7n_carrier_eq p c E rho _ _ _).mp hc)
    ((d7n_row_eq p c E rho j r x a).mp ha)
    ((d7n_validParent_eq p c E rho _ _ _).mp hv)
    ((d7n_held p c E rho _ _).mp hh) with hm | hp
  · exact Or.inl hm
  · obtain ⟨st, hs, hm⟩ := hp
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact Or.inr ⟨nd, hn, hm⟩

private theorem d7n_occurrence (s : Slot) (Q : Block) (H : FGBlock (Fin p.n))
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

private theorem d7n_r6w (w : Window.State (Fin p.n)) (a : Row (Fin p.n)) :
    SimplexFG.Window.r6w (d7nw_toWindow w) a = Window.r6w w a := by
  cases hp : a.height_pair <;> cases hf : a.finality_pair <;>
    simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
    SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
    SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7nw_state_eq, List.any_map, Function.comp_def, d7nw_entry_eq, hp, hf]
  rfl

private theorem d7n_decode_wire (a : RowWire p.n) (i : Fin p.n)
    (h : d7n_signer p a = some i) : ∃ u, RowWire.toRow? a = some u := by
  have ha := (d7n_signer_iff p a i).mp h
  cases a with
  | mk auth payload =>
    dsimp only at ha
    subst auth
    exact ⟨payload.toRow i, rfl⟩

private def d7n_rowValid (w : SimplexFG.Window.State (Fin p.n))
    (a : RowWire p.n) : Bool :=
  a.toRow?.isSome && (a.toRow?.map (SimplexFG.Window.r6w w)).getD false

private theorem d7n_rowValid_eq (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    d7n_rowValid p (d7nw_toWindow w) a = Window.rowValidW w a := by
  unfold d7n_rowValid
  rw [Window.rowValidW_def]
  cases hd : a.toRow? with
  | none => rfl
  | some row => simp only [Option.isSome_some, Option.map_some, Option.getD_some,
      Bool.true_and, d7n_r6w]

private theorem d7n_parentState (s : Slot) (B : FGBlock (Fin p.n)) :
    KitFG.Window.parentState p.E p.cfg p.K_W B s =
      d7nw_toWindow (parentFoldState p s B) := by
  rw [KitFG.Window.parentState_def, ← d7nw_derive_eq]
  rfl

private theorem d7n_stale (s : Slot) (B : FGBlock (Fin p.n)) (row : Row (Fin p.n)) :
    SimplexFG.Window.staleUseful (KitFG.Window.parentState p.E p.cfg p.K_W B s) row =
      Window.staleUseful (parentFoldState p s B) row := by
  rw [d7n_parentState]
  cases hp : row.height_pair <;> cases hf : row.finality_pair <;>
    simp only [SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7nw_state_eq, List.any_map, Function.comp_def, d7nw_entry_eq, hp, hf]
  rfl

private theorem d7n_validFor (s : Slot) (B : FGBlock (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW (parentFoldState p s B) a =
      (((d7n_safety p c).decode a).isSome &&
        (((d7n_safety p c).decode a).map
          (SimplexFG.Window.r6w (KitFG.Window.parentState p.E p.cfg p.K_W B s))).getD false) := by
  rw [d7n_parentState, ← d7n_rowValid_eq, d7n_safety_def p c]
  rfl

private theorem d7n_core_fg (nd : (fgsa p c).State) :
    ((fgsaCoreReads p c).core nd).fg = nd.st.fg := by
  rw [d7n_reads_eq]

private theorem d7n_inv (i : Nat) (x : V) :
    KitFG.FGStoreInvariant (d7n_observations p c).height (d7n_observations p c).finality
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  rw [d7n_core_fg]
  exact (cstoreInv_stateBefore E rho i x).fg


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC: INTENTIONAL window finality projection, using the owner's equations. -/
private theorem accept_finality (W : FGBlock (Fin p.n)) :
    (finalityView p W).F = (Window.derive p p.K_W W).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

private theorem d7nw_update_eq (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    Window.update_finality p p.K_W st B =
      SimplexFG.Window.update_finality p.E p.cfg p.K_W st B := by
  have hv : ∀ st : SimplexFG.Store (Fin p.n),
      Window.acceptViable p p.K_W st = SimplexFG.Window.acceptViable p.E p.cfg p.K_W st := by
    intro st
    simp only [Window.acceptViable_def, SimplexFG.Window.acceptViable_def, ← d7nw_derive_eq,
      d7nw_state_eq]
  simp only [Window.update_finality_def, SimplexFG.Window.update_finality_def,
    ← d7nw_derive_eq, d7nw_state_eq, hv]


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC: INTENTIONAL actual receipt and ancestor-closed inserted tree. -/
private theorem accept_ready (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (t : Time)
    (hr : Ready_W p c E rho i x W t) :
    (storeAt p c E rho (i + 1) x).fg =
      Window.update_finality p p.K_W
        { (storeAt p c E rho i x).fg with TF := insert W (storeAt p c E rho i x).fg.TF } W ∧
    (Window.derive p p.K_W W).F ∈ insert W (storeAt p c E rho i x).fg.TF := by
  classical
  rw [Ready_W_def] at hr
  obtain ⟨o, s, N, P, he, heN, hd, hNamed, hp, ha, hw⟩ := hr
  let st := storeAt p c E rho i x
  have hI : CStoreInv p st := cstoreInv_stateBefore E rho i x
  have hPT := ((parentFG_spec st (eraseFG W) P).mp hp).1
  have hparent : W.parent = P := by rw [← hw, fgBlock_parent]
  have hclosed : ∀ B ∈ insert W st.fg.TF, B.parent ∈ insert W st.fg.TF := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.mem_insert_of_mem (hparent ▸ hPT)
    · exact Finset.mem_insert_of_mem (hI.fg.closed B hB)
  have hFW : FGBlock.Preceq (Window.derive p p.K_W W).F W := by
    rw [← accept_finality p W]
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified W)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry W)
        ((fgCertificateLaws p).height.entry_preceq W))
  refine ⟨?_, KitFG.ancestor_closed_of_parent_closed _ hclosed W
    (Finset.mem_insert_self _ _) _ hFW⟩
  have hstep : storeAt p c E rho (i + 1) x = FGSA.process p st (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  rw [hstep]
  change (match (toWire p o).decode with
    | some (.vote r j b) => admitHead p st r j b
    | some (.row _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block r M) => admitBlock p st r M
    | none => st).fg = _
  rw [hd]
  dsimp only
  obtain ⟨pool, hpool, _⟩ := admitBlock_accepted_eq p st s N P hNamed (heN ▸ hp) ha
  rw [hpool]
  dsimp only
  split_ifs
  · rw [fg_on_block_accepts p st s N P (heN ▸ hp) ha, hw]
  · rw [reconcile_fg, fg_on_block_accepts p st s N P (heN ▸ hp) ha, hw]


private theorem d7n_durable : FGCompose.FGFinalityDurableLaws (fgsaCoreReads p c) := by
  rw [d7n_reads_eq]
  refine ⟨fun X => fgsa_monoAlong_preceq_F p c X, fun nd t => ?_⟩
  change (acRestart p nd.st t).fg.F = nd.st.fg.F
  rw [acRestart_fg]

private theorem d7n_accepts_eq (x : V) (X : FGBlock (Fin p.n)) (d : Time) :
    FGCompose.AcceptsFinalBefore (fgsaCoreReads p c) E rho x X d =
      AcceptsFinalBefore p c E rho x X d := by
  rw [d7n_reads_eq]
  rfl

/-- The selected handler equation, in the shared window form. -/
private theorem d7n_step :
    FGCompose.AcceptStep_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
      (fun i x W t => Ready_W p c E rho i x W t) := by
  rw [d7n_reads_eq]
  intro i x W t _hx hr
  obtain ⟨he, hm⟩ := accept_ready p c E rho i x W t hr
  refine ⟨?_, ?_⟩
  · change (storeAt p c E rho (i + 1) x).fg = _
    rw [he, d7nw_update_eq]
    rfl
  · rw [← d7nw_derive_eq]
    exact hm

private def d7n_delivery [Fintype V] {W U : FGBlock (Fin p.n)} {a₀ d : Time}
    (h : BlockDelivery_W p c E rho W U a₀ d) :
    FGCompose.BlockDelivery_W (fgsaCoreReads p c) E rho
      (fun i x W t => Ready_W p c E rho i x W t) W U a₀ d where
  selected x hx := ⟨(h.selected x hx).index, (h.selected x hx).time⟩
  witness x hx := by
    obtain ⟨h1, h2, h3⟩ := h.witness x hx
    refine ⟨h1, h2, ?_⟩
    rw [d7n_reads_eq]
    exact h3

private theorem d7n_rowHeld_eq (nd : (fgsa p c).State) (a : RowWire p.n) :
    FGCompose.rowHeld (fgsaCoreReads p c) (fun nd => FGSA.blockWireRows nd.st) nd a =
      rowHeld p nd.st a := by
  rw [d7n_reads_eq]
  rfl

/-- Held rows are cumulative along the run, including restore. -/
private theorem d7n_held_durable (i j : Nat) (x : V) (a : RowWire p.n) (hij : i ≤ j)
    (h : rowHeld p (storeAt p c E rho i x) a) : rowHeld p (storeAt p c E rho j x) a := by
  have hcumul := fgsa_store_durable p c E rho hij x
  rcases h with hp | hb
  · exact Or.inl (hcumul.2.2.2.subset hp)
  · right
    change a ∈ allBlockRows _ at hb
    change a ∈ allBlockRows _
    unfold allBlockRows at hb ⊢
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
    obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
    exact List.mem_flatten.mpr ⟨xs,
      List.mem_filterMap.mpr ⟨w, hcumul.2.2.1.subset hw, hdec⟩, ha⟩

/-- The clock keeps the row pool and the proposals. -/
private theorem d7n_held_clock (st : State p.n) (t : Time) (a : RowWire p.n)
    (h : rowHeld p st a) : rowHeld p (FGSA.clock p st t) a := by
  rcases h with hp | hb
  · left
    rw [clock_rowPool]
    exact hp
  · right
    change a ∈ allBlockRows _ at hb
    change a ∈ allBlockRows (FGSA.clock p st _)
    unfold allBlockRows at hb ⊢
    rw [clock_proposals]
    exact hb



end

/-! Part 2: the generic kernel from the FG-SA kernel premise, with every argument produced. -/

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
private theorem receipt_stored_block (i : Nat) (x : V) (C : FGBlock (Fin p.n))
    (hC : C ∈ (storeAt p c E rho i x).fg.TF) (hne : C ≠ .genesis) :
    FinalityBlock p c E rho C := by
  obtain ⟨wire, ⟨hwire, hblock⟩, _hunique⟩ :=
    (storeBundle_stateBefore E rho i x).meta.treeWire C hC hne
  obtain ⟨j, o, t, _hji, he, hto, ⟨s, N, hp, ha⟩, _hr⟩ :=
    stored_proposal_delivered E rho i x wire hwire
  have hw : wire = ⟨.proposer s, .proposal N⟩ := by
    rw [← hto]
    change (⟨toAuth p o.auth, o.payload⟩ : Wire p.n) = _
    rw [hp, ha]
    rfl
  rw [hw] at hblock
  have hb : N.erase = eraseFG C := Option.some.inj hblock
  rw [FinalityBlock_def]
  exact ⟨o, N, hp, Or.inr ⟨x, t, List.mem_of_getElem? he⟩,
    hb ▸ Gen.Pure.block_preceq_refl _⟩

omit [Fintype V] in
private theorem receipt_ready_block (i : Nat) (x : V) (X : FGBlock (Fin p.n))
    (t : Time) (hready : Ready_W p c E rho i x X t) : FinalityBlock p c E rho X := by
  obtain ⟨o, s, N, P, he, heN, hd, _hNamed, _hp, _ha, _hX⟩ :=
    (Ready_W_def p c E rho i x X t).mp hready
  have hp := congrArg Signed.payload (decode_eq_block.mp hd)
  change o.payload = Msg.proposal N at hp
  rw [FinalityBlock_def]
  exact ⟨o, N, hp, Or.inr ⟨x, t, List.mem_of_getElem? he⟩,
    by rw [heN]; exact Gen.Pure.block_preceq_refl _⟩

/-- The action supply for every generic middle witness, from the FG-SA row producers at
the FG-SA image of that witness (same X_D, cD, U, d). -/
private theorem d7c_action {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (m₀ : d7n_Middle p c E rho ΔF pt A) :
    FGCompose.KernelActionSupply_W (fgsaCoreReads p c) (d7n_safety p c)
      (d7n_observations p c) (d7n_timing p) E rho (fgsaInterface p c) (d7n_wire p c) p.E
      m₀ := by
  let m' : KernelMiddleWitness_W p c E rho ΔF pt A := d7n_middle_from p c E rho G ΔF pt A hK m₀
  have reads : ∀ x nd,
      FGCompose.postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho
        (FGCompose.afterTicksIdx rho (p.actionTime (pt.r + 2))) x)).fg =
          ((fgsaCoreReads p c).core nd).fg := by
    intro x nd hnd
    rw [d7n_f_postClock_eq] at hnd
    have h := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
      x _ nd hnd
    simpa only [d7n_fg, d7n_storeAt_eq, d7n_cut_eq] using congrArg (fun st => st.fg) h
  have selected : ∀ x nd, x ∈ rho.honest →
      FGCompose.postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ∃ H, (fgsaCoreReads p c).finalityHead nd = some H ∧
        H ∈ ((fgsaCoreReads p c).core nd).fg.TF ∧
        Block.Preceq (eraseFG m'.X_D) (eraseFG H) := by
    intro x nd hx hnd
    rw [d7n_f_postClock_eq] at hnd
    obtain ⟨j, _, hclock⟩ := d7n_clock_read p c E rho x _ nd hnd
    have hinv : CStoreInv p nd.st := by
      rw [← hclock]
      exact (storeBundle_postClock E rho j x _).cstore
    have hread := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
      x _ nd hnd
    have hwb := rowsPrem_action_walk_batch p c E rho hK m' hServices hQC hXing hNames
      x nd hx hnd
    have hcover := (hK.services.walk _ x ((pt.r + 2) * p.R + 1) _ _ m'.X_D _ _ hx hwb.1
      (by rw [hread]; exact rowsPrem_full_domain p c E rho hK m' hQC hXing hNames x nd hx hnd)
      (by
        rw [hread]
        exact rowsPrem_liveRoot_compatible p c E rho hK m' hQC hXing hNames x nd hx hnd)
      (by rw [hread]; exact hwb.2.1)).1
    rw [hread, ← hwb.2.2] at hcover
    obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
    rw [d7n_reads_eq]
    exact ⟨H, (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩, hH,
      by simpa only [hHe] using hcover⟩
  have service : ∀ x ∈ rho.honest,
      FGCompose.FGSourceService (fgsaCoreReads p c) E rho x (p.actionTime (pt.r + 2))
        m'.cD ((pt.r + 2) * p.R) m'.X_D := by
    intro x hx
    obtain ⟨_, hκ2, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
    have hs := hK.set.base.valid.toScheduleWellFormed
    have hrD : pt.r * p.R ≤ m'.cD := by
      have := m'.earlySlot.1
      have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
      omega
    have hne : eraseFG m'.X_D ≠ .genesis := by
      intro h
      have hslot := m'.slotD
      rw [eraseFG_eq_genesis.mp h] at hslot
      have h0 : (0 : Nat) = m'.cD := hslot
      have := m'.earlySlot.1
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
    have hservices := d7n_service_laws p c E rho pt.w hK.input.t.h1 hK.input.t.h2
      hK.input.ac.h2' hK.input.ac.h2A hK.input.ac.h3 hK.input.ac.h6
    have hserviceStart : (d7n_point p pt.w).serviceStart ≤
        (d7n_ac p c E rho pt.w).proposalTime m'.cD := by
      have hstart := hK.start
      rw [kmid_period_eq] at hstart
      exact hstart.trans (kmid_slot_scale_le p hrD)
    have hcovered : m'.cD < (pt.r + 2) * p.R → ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y ((pt.r + 2) * p.R) = some H ∧
          Block.Preceq (eraseFG m'.X_D) H := by
      intro hlt y hy
      obtain ⟨H, hH⟩ := hheads y hy
      refine ⟨H, hH, ?_⟩
      exact hservices.proposal_later_head m'.cD (eraseFG m'.X_D) y _ H
        m'.honestD (hs2.trans hrD) hserviceStart hy
        (kmid_window_joined hK (Nat.mul_le_mul_right p.R (by omega)) le_rfl hy)
        (Nat.succ_le_of_lt hlt) (kmid_slot_horizon hK le_rfl).2.1 hH
    exact d7n_source_service p c E rho pt.w (pt.r + 2) m'.cD m'.X_D x hx
      m'.earlySlot.2 (hs2.trans hrD) m'.honestD hcovered hK.input.ac.h3 hK.input.ac.h6
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
        nlinarith [p.deltaPos]) m'.actionsInRun hne hheads
      (fun y hy => kmid_window_joined hK
        (Nat.mul_le_mul_right p.R (by omega)) le_rfl hy)
      (kmid_window_confirmed hK (by omega) (by
        have hle := kmid_slot_scale_le p m'.earlySlot.2
        have hh := m'.actionsInRun
        rw [kmid_actionTime_eq] at hh
        change 4 * p.Δ * (m'.cD : Int) + 6 * p.Δ ≤ rho.horizon
        linarith) hx) (rowsPrem_F_below_D_at_gate p c E rho hK m' hXing)
      (fun nd hnd => by
        have hf := rowsPrem_action_frame p c E rho hK m' hQC hXing hNames x nd hx hnd
        exact ⟨hf.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2⟩)
  refine ⟨reads, service, fun x nd hx hnd => ?_, fun x nd hx hnd H hH => ?_⟩
  · obtain ⟨H, hH, hm, _⟩ := selected x nd hx hnd
    exact ⟨H, hH, hm⟩
  · obtain ⟨B, hB, _, hp⟩ := selected x nd hx hnd
    have he := Option.some.inj (hB.symm.trans hH)
    subst B
    rw [d7n_erase, d7n_erase]
    exact hp


omit [Fintype V] in
/-- Every `H ∈ TF` of a proposer read has valid stored rows on its whole path. -/
private theorem d7c_pathValid (hv : V2.D.ExecutionValid E rho) (s : Slot) (nd : Node p)
    (hnd : FGCompose.proposalStateAt E rho (fgsaInterface p c) s = some nd)
    (H : FGBlock (Fin p.n)) (hH : H ∈ ((fgsaCoreReads p c).core nd).fg.TF) :
    ∀ B s' root body rs, FGBlock.Preceq (.node B s' root body rs) H → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
          (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W B) a = true := by
  have hs : proposalStateAt p c E rho s = some nd.st :=
    Option.map_eq_some_iff.mpr ⟨nd, hnd, rfl⟩
  obtain ⟨k, hk⟩ := batch_proposal_read p c E rho s nd.st hs
  have hH' : H ∈ nd.st.fg.TF := (d7n_fg p c nd) ▸ hH
  rw [hk] at hH'
  change H ∈ (clock p _ _).fg.TF at hH'
  rw [clock_fg] at hH'
  intro B s' root body rs hb a ha
  have h := stored_chain_rowsValidW E rho hv.toDeliveryWellFormed k _ H hH'
    B s' root body rs hb a ha
  refine ⟨h.1, ?_⟩
  rw [← d7nw_derive_eq, d7n_r6w]
  exact h.2

/-- The generic kernel `FGCompose.finality_kernel_W_of` at the FG-SA instances, from the
FG-SA kernel premise and the FG-SA suppliers of the frozen kernel. Every generic argument
is produced here; nothing about the conclusion is assumed. -/
private theorem d7c_kernel
    (hServices : FinalityActionReceipts p c E rho) (G ΔF : Time)
    (hδ : p.δt = 2 * p.R) (pt : KernelPt)
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FGCompose.KernelConclusion_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (d7n_timing p) (fgsaInterface p c) (d7n_decodeProposal p) NamedProposal.erase
      NamedProposal.rows (fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock ΔF pt.r := by
  have hs := hK.set.base.valid.toScheduleWellFormed
  have hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) := by
    intro j x r a e ha he
    obtain ⟨C, hc, hn, _⟩ := hEmittedSource j x r a e ha he
    exact ⟨C, hc, hn⟩
  have hF : 0 ≤ ΔF := by
    have h1 := hK.set.deltaF
    have h2 := hK.set.base.delta
    linarith [p.deltaPos]
  have lower : (d7n_timing p).proposal ((d7n_point p pt.w).reset.sStar + 2) ≤
      (d7n_point p pt.w).serviceStart := by
    have h := kmid_slot_scale_le p hK.input.wit.proposal_lower
    change 4 * p.Δ * ((pt.w.sStar + 2 : Nat) : Time) ≤
      4 * p.Δ * (pt.w.u : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have hG := (kmid_kernel_bounds hK).2.2.2.2.2.1
  have hGa : E.t_GST ≤ p.actionTime (pt.r + 2) :=
    hG.trans (kmid_proposal_le_action p (Nat.mul_le_mul_right p.R (by omega)))
  obtain ⟨_, hTdl, _⟩ := FGCompose.kernel_terminal_bounds_W (d7n_timing p)
    (d7n_timing_laws p) (pt.r + 2) ⟨hK.bound.kappa_le_R⟩ hF hGa
  have hThor : SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) ≤
      rho.horizon := by
    have hh := hK.hhor
    have hd := p.deltaPos
    change SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) + p.Δ =
      kernelDeadlineW p ΔF (pt.r + 2) at hTdl
    linarith
  exact FGCompose.finality_kernel_W_of
    (R := fgsaCoreReads p c) (S := d7n_safety p c) (O := d7n_observations p c)
    (T := d7n_timing p) (L := d7n_timing_laws p) (E := E) (rho := rho)
    (I := fgsaInterface p c) (D := d7n_wire p c) (Ef := p.E)
    (decodeProposal := d7n_decodeProposal p) (bodyErase := NamedProposal.erase)
    (bodyRows := NamedProposal.rows) (blockWireRows := fun nd => FGSA.blockWireRows nd.st)
    (chainWireRows := fun nd => FGSA.chainWireRows nd.st)
    (parentFG := fun nd => FGSA.fgBlockOf nd.st)
    (parentHeight := fun _ s H =>
      ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (validFor := fun _ s H => Window.rowValidW (parentFoldState p s H))
    (makeFG := FGSA.fgBlock) (valid := RowWire.valid) (ac := d7n_ac p c E rho pt.w)
    (cfg := p.cfg) (K := p.K_W) (ΔF := ΔF) (sp := d7n_point p pt.w) (pt := ⟨pt.r⟩)
    (Jst := recoveryStart p E)
    (CL := fgsaCoreLaws p c) (HL := fgsaHeadLaws p c E rho)
    (keep := d7n_tree_keep p c) (restore := d7n_tree_restore p c)
    (hc := fgCertificateLaws p)
    (heightBridge := heightView_bridge p) (height_eq := d7nw_height_eq p)
    (finality_eq := d7nw_finality_eq p) (hne := d7n_empty p)
    (target := by
      intro y U X hX hU hp hc hn
      exact fgsa_justifyAt p y U X hX hU hp hc hn)
    (foldTarget := by
      intro y U X hX hU hp hc
      exact (fgsa_foldTrichotomy_target p y U X hX hU hp hc (fun h => by cases h)).1)
    (noMixed := fgsa_noMixedMaturity p)
    (honestSlot := Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    (hK := d7n_kernel p c E rho hK hδ)
    (run := {
      schedule := hs
      fault_weight := by
        rw [d7n_faulty_eq]
        exact kmid_faulty_weight p c E rho hK.set.base hK.set.faultQ
      deltaF := hK.set.deltaF
      linked := (hK.set.base.linked.toCStar (.base .fg) trivial).1
      awake := hK.set.awake })
    (hreset := lower) (hGSTstart := hK.input.wit.after_gst)
    (reset := d7n_reset p c E rho pt.w hK.input.wit.toH0Reset)
    (history := d7n_transfer p c E rho pt.w hK.input.t.h2 rho.horizon)
    (chain := fun horizon => d7n_f_chain p c E rho pt.w hK.input.t.h1 horizon)
    (reflect := by
      intro X Y h
      rw [d7n_erase, d7n_erase] at h
      exact eraseFG_preceq_iff.mp h)
    (parent := by intro X; rw [d7n_erase, d7n_erase]; exact (eraseFG_parent X).symm)
    (hOrigin := d7n_origin p c E rho horigin)
    (emission := d7n_emission p c E rho) (decoded := d7n_decoded p c E rho)
    (receipt := (d7n_receipt_eq p c E rho ΔF).mpr hK.input.t.rows.receipt)
    (honest_slot := fun _ hs => ⟨_, hs.2⟩)
    (proposal := fun s hs hlo hhi => kmid_window_proposal hK hs hlo hhi)
    (terminalProposal := by
      intro hslot
      have hlo : pt.r * p.R ≤ (pt.r + 2) * p.R + kappaF p ΔF :=
        (Nat.mul_le_mul_right p.R (show pt.r ≤ pt.r + 2 by omega)).trans
          (Nat.le_add_right _ _)
      exact kmid_honest_proposal_exists p c E rho hs hK.set.base.delta _ hslot
        (finality_recovery_joined p c E rho hK.set hslot.2
          (kmid_window_join_cut hK hlo) (kmid_slot_gst hK hlo) hThor) hThor)
    (carrier := fun _ _ hp => d7n_carrier p c E rho hs hp)
    (exactService := fun s Q hp hlo =>
      d7n_exact p c E rho pt.w s Q (kmid_window_exact hK hp hlo))
    (source_read := by
      intro s Q r x hex hh hv hx hlo
      exact (hex.2 hh x hx (kmid_window_confirmed hK hlo hh hx)).2 r hv)
    (source_eq := by
      intro x r
      change actionSource p c E rho x r = _
      rw [d7n_source_eq, d7n_reads_eq]
      rfl)
    (head_read := by
      intro s Q x hex hlo hhi hx
      rw [d7n_head_eq]
      exact hex.1 (kmid_slot_horizon hK hhi).2.1 x hx (kmid_window_joined hK hlo hhi hx))
    (head_held := by
      intro s X x hh
      exact FGCompose.head_held (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
        (fgsaHeadLaws p c E rho) hh)
    (slot_chain := by
      intro i x X hX
      rw [d7n_fg] at hX
      exact kmid_stored_slotChain p c E rho hK.set.base.valid i x X hX)
    (closed := by
      intro s nd hnd
      rw [d7n_fg]
      exact (storeInvariant p nd.st (d7n_proposal_reachable p c E rho s nd hnd)).fg.closed)
    (roots := by
      intro s nd hnd
      rw [d7n_fg]
      exact viewRootInj_TF p nd.st
        (storeInvariant p nd.st (d7n_proposal_reachable p c E rho s nd hnd)))
    (validRows := by
      intro s nd hnd
      rw [d7n_fg]
      exact d7n_validRows p nd.st (d7n_proposal_reachable p c E rho s nd hnd))
    (parentEq := by
      intro nd s X
      have h := kmid_parentFold_height p s X
      exact Prod.ext h.1 (congrArg FGBlock.root h.2))
    (matchValid := fun _ s X a hv hm => d7n_matching_valid p s X a hv hm)
    (hBatch := by
      intro q y U X h hp
      exact hBatch c E rho q y U X
        (d7n_batch_from p c E rho ΔF hK.set.base hK.set.faultQ .target q y U X h) hp)
    (hSOCOVTarget := by
      intro x hx r C hsrc hhigh hawake
      rw [d7n_source_eq] at hsrc
      obtain ⟨j, rSent, a, hr, ha, hc, hp⟩ := high_target_row_covered p c E rho pt.w
        hK.input.t.h1 hQC hNames hK.set.base.linked hs x hx r C hsrc hhigh hawake
      exact ⟨j, rSent, a, hr, (d7n_row_eq p c E rho j rSent x a).mpr ha,
        (d7n_complete_eq p c rho x a).mpr hc, hp⟩)
    (action := fun _ m => d7c_action p c E rho hK hServices hQC hXing hNames m)
    (makeWire := d7n_makeWire p)
    (wireDecode := by intro row; rw [d7n_safety_def p c]; rfl)
    (wireValid := by
      intro i y U B
      change (decide (1 ≤ y + 1) && decide (y < y + 1)) = true
      simp only [Nat.le_add_left, Nat.lt_succ_self, decide_true, Bool.and_self])
    (client := by intro nd; rw [d7n_reads_eq, d7n_safety_def p c]; rfl)
    (release := by
      intro i q nd row hn hw hr
      simp only [d7n_safety_def p c] at hr
      simp only [d7n_holder, d7n_action_eq] at hn hw
      obtain ⟨j, hj, he⟩ := d7n_release p c E rho i q nd row hn hw hr
      refine ⟨j, ?_, ?_⟩
      · simpa only [d7n_holder, d7n_action_eq] using hj
      · rw [d7n_safety_def p c]
        exact he)
    (fields := by
      intro nd H hH
      rw [d7n_reads_eq] at hH
      simpa only [d7n_safety_def p c, d7n_observations_eq,
        certificateHeadFields_def] using fgInputs_headFields p nd.st H hH)
    (hQC := d7n_f_qc p c E rho hQC)
    (recordHead := d7n_f_head p c E rho)
    (clientLaws := (d7n_safety_eq p c).symm ▸ fgsaSafetyClientLaws p c)
    (own := d7n_f_own p c E rho)
    (hsel := d7n_selection p c E rho hsel)
    (decode := by
      intro a i hsig
      change d7n_signer p a = some i at hsig
      rw [d7n_safety_def p c]
      exact d7n_decode_wire p a i hsig)
    (occurrence := by
      intro s Q H nd a u hn hp hm hd
      rw [d7n_safety_def p c] at hd
      exact d7n_occurrence p c E rho s Q H nd a u hn hp hm hd)
    (validFor_eq := fun _ s B a => d7n_validFor p c s B a)
    (pathValid := fun s nd hnd H hH =>
      d7c_pathValid p c E rho hK.set.base.valid s nd hnd H hH)
    (dutyTime := fun _ => rfl)
    (rowDurable := fun i j x a hij h => by
      rw [d7n_rowHeld_eq] at h ⊢
      exact d7n_held_durable p c E rho i j x a hij h)
    (rowClock := fun nd t a h => by
      rw [d7n_rowHeld_eq] at h ⊢
      exact d7n_held_clock p nd.st t a h)
    (ready := fun i x W t => Ready_W p c E rho i x W t)
    (step := d7n_step p c E rho) (durable := d7n_durable p c)
    (inv := fun i x _ => d7n_inv p c E rho i x)
    (finBlock := FinalityBlock p c E rho)
    (hI3 := fun C W hC hW => hI3 ⟨hK.set.base, hK.set.fault⟩ C W _ _ _ _ hC hW
      ((FinalityFinalizedAt_def p C _ _).mpr ⟨rfl, rfl⟩)
      ((FinalityFinalizedAt_def p W _ _).mpr ⟨rfl, rfl⟩))
    (readyBlock := fun i x X t h => receipt_ready_block p c E rho i x X t h)
    (stored := fun i x C hC hne => receipt_stored_block p c E rho i x C
      (by rw [d7n_core_fg] at hC; exact hC) hne)
    (rootScope := by
      intro i x hx C k u r a B hC hrow hsrc hroot
      rw [d7n_core_fg] at hC
      rw [d7n_source_eq] at hsrc
      exact rootScope_eq hK.set.base.idealization
        (rootScope_justified (rootScope_store hx hC))
        (rootScope_entry (rootScope_source ((d7n_row_eq p c E rho k r u a).mp hrow).1 hsrc))
        hroot)
    (hStrat := by
      intro j z W hz hW J hJ hne
      rw [d7n_core_fg] at hW
      obtain ⟨u, r, a, hrow, hn⟩ := hStrat j z W hz hW J (by
        rw [certified_def]
        exact hJ) hne
      obtain ⟨k, hk, hrow⟩ := (HonestRowBefore_def p c E rho j u r a).mp hrow
      refine ⟨u, r, a, ⟨k, hk, (d7n_row_eq p c E rho k r u a).mpr hrow⟩, ?_⟩
      have he : FGCompose.namedEntry a.payload.height_pair =
          namedEntry a.payload.height_pair := by
        cases a.payload.height_pair <;> rfl
      change FGCompose.namedEntry a.payload.height_pair = _
      rw [he]
      exact hn)
    (hEmittedSource := by
      intro j z r a e hrow he
      obtain ⟨C, hsrc, hC, hT⟩ := hEmittedSource j z r a e
        ((d7n_row_eq p c E rho j r z a).mp hrow)
        (by rw [← d7n_f_entry_eq]; exact he)
      exact ⟨C, by rw [d7n_source_eq]; exact hsrc, hC, hT⟩)
    (hcapBefore := by
      intro cut b j z W hj hW hrow
      rw [d7n_held_eq] at hW
      exact hcapBefore cut b j z W hj hW (fun k u r a row h B timeout ha hd hp hlt =>
        hrow k u r a row h B timeout ((d7n_row_eq p c E rho k r u a).mpr ha)
          (by rw [d7n_safety_def p c]; exact hd) hp hlt))
    (delivery := by
      intro X U rows hcar hgst hhor hfinal
      obtain ⟨d⟩ := receipt_delivery p c E rho G ΔF hK.set X U rows
        (by
          have hc := (d7n_carrier_eq p c E rho _ _ _).mp hcar
          rw [d7n_erase] at hc
          exact hc) hgst hhor
        (by
          have h := hfinal
          rw [← d7nw_derive_eq] at h
          exact h) hI3
      exact ⟨d7n_delivery p c E rho d⟩)

omit [DecidableEq V] [Fintype V] in
private theorem forward_timeIdx_le_gate {t a : Time} (hta : t < a) :
    timeIdx rho t ≤ afterTicksIdx rho a := by
  change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
    (rho.events.filter (cutPred a)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
    (Or.inl (lt_of_le_of_lt (of_decide_eq_true he) hta)))

private theorem forward_output_le {ΔF t : Time} {w : HealingWitness} {r : Nat} {A : Block}
    (hrec : Recovery₂ p c E rho G ΔF)
    (hs : V2.D.ScheduleWellFormed E rho) (input : HealingInput p c E rho w ΔF)
    (start : tstar p w ≤ t) (htr : t ≤ (r : Time) * P p)
    (ex : ExactService p c E rho (r * p.R) A)
    (hhor : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      Block.Preceq (V2.D.Run.readAt E rho t x).st.base.stableRecord A := by
  have hta : t < p.actionTime r := by
    rw [kmid_period_eq] at htr
    rw [kmid_actionTime_eq]
    have := p.deltaPos
    linarith
  have hidx := forward_timeIdx_le_gate p c rho hta
  have hsuffix : HealSuffix p c rho (tstar p w) (afterTicksIdx rho (p.actionTime r)) :=
    ⟨(fgsa_healSuffix_timeIdx E rho hs start).1.trans hidx,
      List.length_filter_le _ _⟩
  intro x hx
  have hstartHor : tstar p w ≤ rho.horizon := start.trans (htr.trans (by
    rw [kmid_period_eq]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) ≤ rho.horizon
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤ rho.horizon at hhor
    linarith [p.deltaPos]))
  have hmono := input.healed.2.1 _ _ x
    (fgsa_healSuffix_timeIdx E rho hs start) hsuffix hidx
    (finality_input_suffix_confirmed p c E rho hrec input hx
      (fgsa_healSuffix_timeIdx E rho hs start) hstartHor)
    (finality_input_suffix_confirmed p c E rho hrec input hx hsuffix hstartHor)
  have hreader := finality_recovery_confirmed p c E rho hrec hx (r * p.R) _ _
    (by
      have hsync := input.wit.synchronous
      have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
        exact_mod_cast input.wit.proposal_lower
      have hst := start.trans htr
      rw [kmid_period_eq] at hst
      change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ _ at hst
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * _
      nlinarith [p.deltaPos]) le_rfl hhor
    (fun j hj => kmid_tick_lt_afterTicks p c E rho hs hj le_rfl)
  have hstable := (ex.2 hhor x hx hreader).2.2.2.1
  rw [afterTicks_eq_stateBefore E rho hs] at hstable
  have hout := fgsa_outputAt_eq_S_at E rho hs (fgsaInterface p c).stable
    (by simp) x t
  change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ at hout
  rw [hout]
  exact hstable ▸ hmono

/-- The generic forward witness `FGCompose.forward_witness_FE_of` at the FG-SA instances.
The kernel supplier is the generic kernel `d7c_kernel` at the same witness; no kernel
conclusion is assumed. The guarded `opening` premise is produced here from the join cut
(tstar ≤ t ≤ r·P) and the recovery regime. -/
private theorem d7c_forward
    (hServices : FinalityActionReceipts p c E rho) (G ΔF : Time) (g : Nat)
    (w : HealingWitness) (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FGCompose.ForwardWitness_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (d7n_timing p) (fgsaInterface p c) (d7n_decodeProposal p) NamedProposal.erase
      NamedProposal.rows (fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) ΔF g (d7n_point p w)
      pt.t := by
  have hrec₂ := h.set.core.toRecovery₂
  have hs := h.set.core.base.valid.toScheduleWellFormed
  have hF : 0 ≤ ΔF := by
    have h1 := hrec₂.deltaF
    have h2 := hrec₂.base.delta
    linarith [p.deltaPos]
  have lower : (d7n_timing p).proposal ((d7n_point p w).reset.sStar + 2) ≤
      (d7n_point p w).serviceStart := by
    have hl := kmid_slot_scale_le p h.input.wit.proposal_lower
    change 4 * p.Δ * ((w.sStar + 2 : Nat) : Time) ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have ht : 0 < pt.t := by
    have hd := p.deltaPos
    have hu := Int.natCast_nonneg w.u
    have hst := h.start
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ pt.t at hst
    nlinarith
  have hquorum : p.E.q ≤
      p.E.weightOf (Finset.univ \ FGCompose.historyFaulty (d7n_safety p c) rho) := by
    have eq : Finset.univ \ FGCompose.historyFaulty (d7n_safety p c) rho =
        honestSeats p c rho := by
      rw [d7n_faulty_eq]
      ext i
      simp
    rw [eq]
    exact kmid_honest_quorum p c rho hrec₂.base.linked hrec₂.fault
  exact FGCompose.forward_witness_FE_of
    (R := fgsaCoreReads p c) (S := d7n_safety p c) (O := d7n_observations p c)
    (T := d7n_timing p) (L := d7n_timing_laws p) (E := E) (rho := rho)
    (I := fgsaInterface p c) (D := d7n_wire p c) (Ef := p.E)
    (decodeProposal := d7n_decodeProposal p) (bodyErase := NamedProposal.erase)
    (bodyRows := NamedProposal.rows)
    (parentFG := fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
    (makeFG := FGSA.fgBlock) (Jst := recoveryStart p E) (recurStart := recoveryStart p E)
    (sp := d7n_point p w)
    (honestSlot := Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    (fgQuorum := p.E.q)
    (fgHonestWeight :=
      p.E.weightOf (Finset.univ \ FGCompose.historyFaulty (d7n_safety p c) rho))
    (timeoutSlots := p.cfg.timeoutDelay) (capacity := p.K_W)
    (bound := ⟨h.set.bound.kappa_le_R⟩) (hF0 := hF) (recur := h.set.recur)
    (hrecur := (finality_healing_recoveryStart p c E rho h.input).trans h.start)
    (ht := ht) (start := h.start) (hhor := h.hhor) (hreset := lower)
    (hGSTstart := h.input.wit.after_gst) (honest_quorum := hquorum)
    (timeout_eq := hδ) (capacity_ge := p.kWLarge)
    (kernel := fun r hKg => d7c_kernel p c E rho hServices G ΔF hδ ⟨w, r⟩
      { set := hrec₂, bound := h.set.bound, window := hKg.window, start := hKg.start
        hhor := hKg.hhor, input := h.input
        services := fgsa_coreServices E rho hrec₂.base w (finality_vote_receipts hrec₂) }
      hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore)
    (opening := by
      intro r hslot htr hh
      have htr' : pt.t ≤ (r : Time) * P p := htr
      have hst := h.start.trans htr'
      rw [kmid_period_eq] at hst
      have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
        exact_mod_cast h.input.wit.proposal_lower
      have hsync := h.input.wit.synchronous
      change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) at hst
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      have hcut : E.t_GST ≤ slotStartZ p (((r * p.R : Nat) : Int) - 1) := by
        change E.t_GST ≤ 4 * p.Δ * (((r * p.R : Nat) : Int) - 1)
        nlinarith [p.deltaPos]
      have hG : E.t_GST ≤ SA.proposalTime p.toParams (r * p.R) := by
        change E.t_GST ≤ 4 * p.Δ * ((r * p.R : Nat) : Int)
        nlinarith [p.deltaPos]
      exact kmid_honest_proposal_exists p c E rho hs hrec₂.base.delta _ hslot
        (finality_recovery_joined p c E rho hrec₂ hslot.2 hcut hG hh) hh)
    (reset := d7n_reset p c E rho w h.input.wit.toH0Reset)
    (history := d7n_transfer p c E rho w h.input.t.h2 rho.horizon)
    (height := (fgCertificateLaws p).height)
    (reflect := by
      intro X Y hXY
      rw [d7n_erase, d7n_erase] at hXY
      exact eraseFG_preceq_iff.mp hXY)
    (parent := by intro X; rw [d7n_erase, d7n_erase]; exact (eraseFG_parent X).symm)

/-- The generic local liveness `FGCompose.finality_liveness_of_forward_W` at the FG-SA
instances, from the generic forward witness of `d7c_forward`. The AC output read is the
actual stable record. -/
private theorem d7c_liveness
    (hServices : FinalityActionReceipts p c E rho) (G ΔF : Time) (g : Nat)
    (w : HealingWitness) (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FGCompose.FinalityLivenessConcl_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (fun nd : Node p => nd.st.base.stableRecord) pt.t
      (pt.t + FGCompose.W_W (d7n_timing p) ΔF g) := by
  have hrec₂ := h.set.core.toRecovery₂
  have hs := h.set.core.base.valid.toScheduleWellFormed
  have hgapOf : ∀ r : Nat, pt.t ≤ (r : Time) * P p → w.sStar + 2 ≤ r * p.R := by
    intro r htr
    have hst := h.start.trans htr
    rw [kmid_period_eq] at hst
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) at hst
    have hlow := h.input.wit.proposal_lower
    have hd := p.deltaPos
    have hu : (w.u : Time) < ((r * p.R : Nat) : Time) := by nlinarith
    have hu' : w.u < r * p.R := by exact_mod_cast hu
    exact hlow.trans hu'.le
  exact FGCompose.finality_liveness_of_forward_W
    (R := fgsaCoreReads p c) (O := d7n_observations p c)
    (T := d7n_timing p) (E := E) (rho := rho)
    (I := fgsaInterface p c) (Ef := p.E)
    (decodeProposal := d7n_decodeProposal p) (bodyErase := NamedProposal.erase)
    (bodyRows := NamedProposal.rows)
    (parentFG := fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
    (makeFG := FGSA.fgBlock) (sp := d7n_point p w)
    (honestSlot := Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    (output := fun nd : Node p => nd.st.base.stableRecord)
    (CL := fgsaCoreLaws p c) (durable := d7n_durable p c) (hs := hs)
    (hc := fgCertificateLaws p)
    (reflect := by
      intro X Y hXY
      rw [d7n_erase, d7n_erase] at hXY
      exact eraseFG_preceq_iff.mp hXY)
    (eraseMono := by
      intro X Y hXY
      rw [d7n_erase, d7n_erase]
      exact eraseFG_preceq hXY)
    (outputBelow := by
      intro r A htr hA hD
      have hgate : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon := by
        have hd := p.deltaPos
        have hk := Int.natCast_nonneg (kappaF p ΔF)
        change (((r + 2 : Nat) : Time)) * P p + betaF p ΔF + p.Δ ≤ rho.horizon at hD
        rw [kmid_period_eq, betaF_def] at hD
        change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ ≤ rho.horizon
        have hle := kmid_slot_scale_le p
          (Nat.mul_le_mul_right p.R (show r ≤ r + 2 by omega))
        have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
        have he : ((((r + 2) * p.R : Nat)) : Time) = ((r * p.R : Nat) : Time) + 2 * p.R := by
          push_cast
          ring
        nlinarith
      exact forward_output_le p c E rho hrec₂ hs h.input h.start htr
        (h.input.ac.h3 (r * p.R) A hA (hgapOf r htr)) hgate)
    (finalBelow := by
      intro x hx
      have hstartHor : tstar p w ≤ rho.horizon := h.start.trans
        ((le_add_of_nonneg_right (finality_window_nonneg p ΔF g)).trans h.hhor)
      have hout := fgsa_outputAt_eq_S_at E rho hs (fgsaInterface p c).stable
        (by simp) x pt.t
      change (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord = _ at hout
      have hread := V2.D.Engine.readAt_eq_stateBefore hs pt.t
      have hFS := h.input.healed.2.2.1 _ x x
        (fgsa_healSuffix_timeIdx E rho hs h.start) hx
        (finality_input_suffix_confirmed p c E rho hrec₂ h.input hx
          (fgsa_healSuffix_timeIdx E rho hs h.start) hstartHor)
      rw [d7n_erase, d7n_fg]
      change Block.Preceq (eraseFG (V2.D.Run.readAt E rho pt.t x).st.fg.F)
        (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord
      rw [hout, hread]
      exact hFS)
    (hf := d7c_forward p c E rho hServices G ΔF g w hδ pt h hsel horigin hBatch hQC hXing
      hI3 hStrat hEmittedSource hcapBefore)

/-- `d7c_kernel` with the FG-SA suppliers of the frozen kernel produced from `Recovery₂`
(the same public producers as Assembly/Finality.fgsa_finalityKernel_W). -/
private theorem d7c_kernelOfRecovery (G ΔF : Time) (hδ : p.δt = 2 * p.R) (pt : KernelPt)
    (hK : KernelPrem_W p c G ΔF E rho pt) :
    FGCompose.KernelConclusion_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (d7n_timing p) (fgsaInterface p c) (d7n_decodeProposal p) NamedProposal.erase
      NamedProposal.rows (fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock ΔF pt.r := by
  have hR := hK.set
  refine d7c_kernel p c E rho
    (finality_action_receipts hR (fun D x => fgsa_target_service_genesis E rho D x))
    G ΔF hδ pt hK (fgsa_tRowsSelect p c E rho hR.base.valid)
    (held_chain_row_origin_before p c E rho hR.base.valid.toUnforgeableSignatures
      hR.base.valid.toScheduleWellFormed)
    (fgsa_batchCoverage p ΔF .target) ?_ ?_ ?_ ?_ ?_ ?_
  · exact sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hR.base, hR.faultQ⟩
      (fgsa_rStore p c E rho)
  · exact fgsa_rXing (hroots := hR.base.idealization) p c E rho hR.base.linked
      hR.faultX_count_rec hR.base.valid.toUnforgeableSignatures
  · intro hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · have hs := sourceDiscipline_strat p c E rho
      (pt := ()) ⟨hR.base, hR.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hR.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hR.base.linked hR.base.valid
        hR.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hR.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- `d7c_liveness` with the same suppliers produced from the recovery regime. -/
private theorem d7c_livenessOfRecovery (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt) :
    FGCompose.FinalityLivenessConcl_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (fun nd : Node p => nd.st.base.stableRecord) pt.t
      (pt.t + FGCompose.W_W (d7n_timing p) ΔF g) := by
  have hR := h.set.core.toRecovery₂
  refine d7c_liveness p c E rho
    (finality_action_receipts hR (fun D x => fgsa_target_service_genesis E rho D x))
    G ΔF g w hδ pt h (fgsa_tRowsSelect p c E rho hR.base.valid)
    (held_chain_row_origin_before p c E rho hR.base.valid.toUnforgeableSignatures
      hR.base.valid.toScheduleWellFormed)
    (fgsa_batchCoverage p ΔF .target) ?_ ?_ ?_ ?_ ?_ ?_
  · exact sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hR.base, hR.faultQ⟩
      (fgsa_rStore p c E rho)
  · exact fgsa_rXing (hroots := hR.base.idealization) p c E rho hR.base.linked
      hR.faultX_count_rec hR.base.valid.toUnforgeableSignatures
  · intro hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · have hs := sourceDiscipline_strat p c E rho
      (pt := ()) ⟨hR.base, hR.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hR.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hR.base.linked hR.base.valid
        hR.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hR.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- `d7c_forward` with the same suppliers produced from the recovery regime. -/
private theorem d7c_forwardOfRecovery (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt) :
    FGCompose.ForwardWitness_W (fgsaCoreReads p c) E rho (d7n_observations p c)
      (d7n_timing p) (fgsaInterface p c) (d7n_decodeProposal p) NamedProposal.erase
      NamedProposal.rows (fun (nd : Node p) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) ΔF g (d7n_point p w)
      pt.t := by
  have hR := h.set.core.toRecovery₂
  refine d7c_forward p c E rho
    (finality_action_receipts hR (fun D x => fgsa_target_service_genesis E rho D x))
    G ΔF g w hδ pt h (fgsa_tRowsSelect p c E rho hR.base.valid)
    (held_chain_row_origin_before p c E rho hR.base.valid.toUnforgeableSignatures
      hR.base.valid.toScheduleWellFormed)
    (fgsa_batchCoverage p ΔF .target) ?_ ?_ ?_ ?_ ?_ ?_
  · exact sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hR.base, hR.faultQ⟩
      (fgsa_rStore p c E rho)
  · exact fgsa_rXing (hroots := hR.base.idealization) p c E rho hR.base.linked
      hR.faultX_count_rec hR.base.valid.toUnforgeableSignatures
  · intro hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · have hs := sourceDiscipline_strat p c E rho
      (pt := ()) ⟨hR.base, hR.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hR.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hR.base.linked hR.base.valid
        hR.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hR.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

end AvailableChain.FGSA.Run

/-! Part 3: the bounded run. The fixture and prefix proofs through `nvHealingInput` are copied
verbatim from Tests/NonVacuity/HealingClaims.lean (one honest node, ExecutionValid, horizon
310); test-to-test imports are forbidden. Only the namespace changes; no public section, so
the copy adds no inventory entries. The application section at the end is new. -/
namespace AvailableChain.FGSA.Run.Tests.P0d7c

/-- S5 NV6: S5 fixture: one honest node, positive horizon, and unchanged SA clocks.
DC: SAME canonical fixture and cached prefix proof. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 310

theorem params_delta : params.Δ = 1 := rfl
theorem params_n : params.n = 1 := rfl
theorem params_k : params.k = 2 := rfl
theorem params_eta : params.η = 0 := rfl
theorem params_R : params.R = 3 := rfl
theorem params_timeout : params.δt = 6 := rfl
theorem params_window : params.K_W = 2 := rfl
theorem env_delta : env.Δ = params.Δ := rfl
theorem env_gst : env.t_GST = 0 := rfl
theorem env_awake (v : Fin 1) (t : Time) : env.awake v t = true := rfl
theorem deltaF_value : deltaF = 3 := rfl
theorem gap_value : gap = 4 := rfl
theorem horizon_value : horizon = 310 := rfl
theorem horizon_pos : 0 < horizon := by decide
theorem deltaF_lower : env.Δ ≤ deltaF := by decide
theorem gap_lower : 4 * params.Δ ≤ gap := by decide

theorem kappaF_value : kappaF params deltaF = 3 := by decide
theorem betaF_value : betaF params deltaF = 12 := by decide
theorem epsF_value : epsF params deltaF = 4 := by decide
theorem period_value : P params = 12 := by decide
theorem gamma_value : Γ params gap = 4 := by decide
theorem lease_value : L params = 7 := by decide
theorem rhoGamma_value : ρΓ params gap = 26 := by decide
theorem rhoOne_value : ρ₁ params gap = 21 := by decide
theorem short_k : params.k ≤ 2 * params.R + 1 := by decide
theorem Eg_two_value : E_gF params deltaF gap (ρΓ params gap) = 53 := by decide
theorem Eg_one_value : E_gF params deltaF gap (ρ₁ params gap) = 48 := by decide
theorem Ej_two_value : E_jF params deltaF gap (ρΓ params gap) = 49 := by decide
theorem Ej_one_value : E_jF params deltaF gap (ρ₁ params gap) = 44 := by decide
theorem Bc_two_value : B_cF params deltaF gap (ρΓ params gap) = 48 := by decide
theorem Bc_one_value : B_cF params deltaF gap (ρ₁ params gap) = 43 := by decide
theorem Dc_two_value : D_cF params (ρΓ params gap) = 37 := by decide
theorem Dc_one_value : D_cF params (ρ₁ params gap) = 32 := by decide
theorem reset_two_value : B_resetF params deltaF gap (ρΓ params gap) = 325 := by decide
theorem reset_one_value : B_resetF params deltaF gap (ρ₁ params gap) = 295 := by decide
theorem reset_value : B'_resetF params deltaF gap = 295 := by decide
theorem healing_two_value : B_H2F params deltaF gap = 333 := by decide
theorem healing_one_value : B_H1F params deltaF gap = 303 := by decide
theorem healing_value : B_HF params deltaF gap = 303 := by decide

theorem healing_strict_horizon : B_HF params deltaF gap < horizon := by decide
theorem healing_horizon : recoveryStart params env + B_HF params deltaF gap ≤ horizon := by decide
theorem reset_horizon :
    recoveryStart params env + B'_resetF params deltaF gap ≤ horizon := by decide
theorem reset_full_horizon :
    recoveryStart params env + B'_resetF params deltaF gap +
        Γ params gap + 4 * params.Δ ≤ horizon := by
  decide
theorem reset_full_budget : B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ = 303 := by
  decide
theorem action_three_value : params.actionTime 3 = 42 := by decide
theorem renewed_three_budget :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ = 66 := by decide
theorem renewed_three_horizon :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ ≤ horizon := by decide

theorem livenessBound : LivenessBoundW params deltaF := ⟨by decide⟩

section EmissionHelpers
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

theorem nv_rows_clock (st : State p.n) (t : Time)
    (h : EmissionRowsValid st) : EmissionRowsValid (FGSA.clock p st t) := by
  constructor
  · rw [clock_rowPool]; exact h.1
  · rw [clock_proposals]; exact h.2

theorem nv_rows_admit (st : State p.n) (a : RowWire p.n)
    (h : EmissionRowsValid st) (ha : a.valid = true) :
    EmissionRowsValid (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem nv_rows_fold (rows : List (RowWire p.n)) (st : State p.n)
    (h : EmissionRowsValid st) (hr : ∀ a ∈ rows, a.valid = true) :
    EmissionRowsValid (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (nv_rows_admit st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem nv_rows_process (st : State p.n) (o : Obj p)
    (h : EmissionRowsValid st) (hw : (fgsa p c).wellFormed o = true) :
    EmissionRowsValid (FGSA.process p st (toWire p o)) := by
  change FGSA.wellFormed p (toWire p o) = true at hw
  unfold FGSA.process
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row i body =>
      have he := decode_eq_row.mp hd
      rw [he] at hw ⊢
      exact nv_rows_admit _ _ h hw
    | block s N =>
      have hr : ∀ a ∈ N.rows, a.valid = true := by
        unfold FGSA.wellFormed at hw
        rw [hd] at hw
        intro a ha
        exact List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 a ha
      change EmissionRowsValid (admitBlock p st s N)
      unfold admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply nv_rows_fold _ _ _ hr
            have hs : EmissionRowsValid
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] } := by
              refine ⟨h.1, ?_⟩
              intro w hw s' M hd'
              rcases List.mem_append.mp hw with hm | hm
              · exact h.2 w hm s' M hd'
              · have hew := List.mem_singleton.mp hm
                subst w
                change some (Input.block s N) = some (Input.block s' M) at hd'
                cases hd'
                exact hr
            split
            · exact hs
            · constructor
              · rw [(reconcile_frame _).2.2.1]; exact hs.1
              · rw [(reconcile_frame _).2.1]; exact hs.2
          · exact h

theorem nv_attest_valid (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (body : RowPayload) (hbody : (attest p st Λ j).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh := congrArg Prod.fst hc
  change (derive p.E p.cfg C).h = h at heh
  have hpos : 1 ≤ h := heh ▸ KitFG.one_le_h p.E p.cfg C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < h))
      |>.map (fun fp => decide (fp.height < h))).getD true) = true
  cases hfp : finality_pair Λ.toRecord (fgInputs p st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

theorem nv_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, N, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s N hd a hm

theorem nv_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

theorem nv_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  simp only [FGSA.wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, NamedProposal.raw, NamedProposal.support, NamedProposal.rows]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := nv_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (nv_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

theorem nv_proposal_shape (st : State p.n) (s : Slot) (app : Nat)
    (N : NamedProposal p.n)
    (ha : (propose p st s).map (withApp p app) = some (.proposal N)) :
    N.erase = proposalBlock p
      (getHead p st (proposerVotes st s) (proposerSupport st s)) s app
      N.raw N.support N.rows ∧
      N.raw = (proposerVotes st s).filterMap liftHead? ∧
      N.support = (proposerSupport st s).filterMap liftHead? ∧
      N.rows = proposalRows p st
        (getHead p st (proposerVotes st s) (proposerSupport st s)) := by
  unfold propose at ha
  split at ha
  · cases ha
  · simp only [Option.map_map] at ha
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp ha
    have hN := Msg.proposal.inj he
    subst N
    have heP := (namedByErase?_sound st _ P hP).2
    refine ⟨?_, rfl, rfl, rfl⟩
    rw [namedProposal_erase, heP]
    rfl

theorem nv_wire_cases (o : Obj p) (hw : (fgsa p c).wellFormed o = true) :
    (∃ s j b, o = ofHead p ⟨.seat (.head s) j, b⟩) ∨
    (∃ j body, o = ofRow p ⟨.seat .fg j, body⟩) ∨
    (∃ s N, o = (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p)) := by
  cases hd : (toWire p o).decode with
  | none => change FGSA.wellFormed p (toWire p o) = true at hw
            simp only [FGSA.wellFormed, hd] at hw
            cases hw
  | some m =>
    have hinj := (toWireEquiv p).injective
    have he (w : Wire p.n) (h : toWire p o = w) : o = ofWire p w := by
      apply hinj
      exact h.trans ((toWireEquiv p).right_inv w).symm
    cases m with
    | vote s j b => exact Or.inl ⟨s, j, b, he _ (decode_eq_vote.mp hd)⟩
    | row j body => exact Or.inr (Or.inl ⟨j, body, he _ (decode_eq_row.mp hd)⟩)
    | block s N => exact Or.inr (Or.inr ⟨s, N, he _ (decode_eq_block.mp hd)⟩)

theorem nv_liftHead (w : GridCO.Wire p.n .root) (a : HeadWire p.n) (ha : liftHead? w = some a) :
    baseVote a = w ∧ ∃ s j b, a = ⟨.seat (.head s) j, b⟩ := by
  obtain ⟨auth, m⟩ := w
  cases auth with
  | seat s j =>
    cases m with
    | head b =>
      change some (⟨.seat (.head s) j, b⟩ : HeadWire p.n) = some a at ha
      cases ha
      exact ⟨rfl, s, j, b, rfl⟩
    | proposal => change none = some a at ha; cases ha
  | proposer => cases m <;> change none = some a at ha <;> cases ha
  | none => cases m <;> change none = some a at ha <;> cases ha

theorem nv_handles_carries (st : State p.n) (o o' : Obj p) (hh : handlesS p st o o') :
    o = o' ∨ carriesS p o o' := by
  rcases hh with he | hh
  · exact Or.inl he
  · right
    cases hd : (toWire p o).decode with
    | none => simp only [hd] at hh
    | some m =>
      cases m with
      | vote | row => simp only [hd] at hh
      | block s N =>
        rw [hd] at hh
        have he := congrArg Signed.payload (decode_eq_block.mp hd)
        change o.payload = .proposal N at he
        rw [carriesS, he]
        exact hh.2.imp_right (fun h => Or.inr h)

theorem nv_carries_payload (o o' : Obj p) (N : NamedProposal p.n)
    (he : o.payload = .proposal N)
    (hc : o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.support.map (ofHead p) ∨
      o' ∈ N.rows.map (ofRow p)) : carriesS p o o' := by
  rw [carriesS, he]
  exact hc
end EmissionHelpers

open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine

abbrev Object := (fgsa params unitCodec).Object
abbrev Event := V2.Event (Fin 1) Object
abbrev FixtureNode := (fgsa params unitCodec).State

def mkRun (es : List Event) : V2.D.Run (Fin 1) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- One tick, then one delivery of each released object, in release order. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- The cached node avoids a repeated fold of all preceding events. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 311).1

theorem runPrefix_zero : runPrefix 0 = ([], (fgsa params unitCodec).init) := rfl

theorem runPrefix_succ (n : Nat) : runPrefix (n + 1) = batch (runPrefix n) n := by
  simp [runPrefix, List.range_succ, List.foldl_append]

theorem duties_length (t : Time) : (duties params t).length ≤ 1 := by
  have hp : SA.proposalTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) := rfl
  have hv : SA.voteTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) + 1 := rfl
  have ha : params.actionTime ((params.slotOf t - 1) / params.R) =
      12 * (((params.slotOf t - 1) / params.R : Nat) : Time) + 6 := by
    change 4 * ((((params.slotOf t - 1) / params.R) * 3 : Nat) : Time) + 6 = _
    push_cast
    ring
  have hpa (a b : Time) : 4 * a ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  have hva (a b : Time) : 4 * a + 1 ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  simp only [duties, hp, hv, ha]
  split_ifs <;> simp_all
  · exact hpa (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)
  · exact hva (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)

theorem ownSeats_single (d : RunDuty) :
    (mkRun []).ownSeats (RunDuty.signLabel d) 0 = [⟨0, by cases d <;> exact Nat.one_pos⟩] := by
  cases d <;> change (List.finRange 1).filter (fun _ => decide ((0 : Fin 1) = 0)) = [0]
  all_goals decide

theorem released_length (nd : FixtureNode) (t : Time) :
    (V2.D.tick env (mkRun []) nd 0 t).2.length ≤ 1 := by
  change (((duties params t).flatMap (fun d =>
    ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun i =>
      ((fgsa params unitCodec).act ((fgsa params unitCodec).clock nd t) d ()).map
        (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Object))))) ++ []).length ≤ 1
  rw [List.append_nil]
  have h := duties_length t
  cases he : duties params t with
  | nil => simp
  | cons d ds =>
    have hds : ds = [] := by simpa [he] using h
    rw [hds]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ownSeats_single,
      List.filterMap_cons, List.filterMap_nil]
    split <;> simp

theorem prefix_events_time (n : Nat) :
    ∀ e ∈ (runPrefix n).1, ∃ m < n, e.time = (m : Time) ∧
      (e = .tick 0 (m : Time) ∨ ∃ o, e = .deliver 0 o (m : Time)) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    intro e he
    simp only [batch, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (he | he) | ⟨o, _, he⟩
    · obtain ⟨m, hm, ht, he⟩ := ih e he
      exact ⟨m, by omega, ht, he⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inl rfl⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inr ⟨o, rfl⟩⟩

theorem prefix_ticks (n m : Nat) (hm : m < n) : .tick 0 (m : Time) ∈ (runPrefix n).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [runPrefix_succ]
    by_cases hmn : m < n
    · exact List.mem_append_left _ (List.mem_append_left _ (ih hmn))
    · have he : m = n := by omega
      subst m
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem prefix_mono {n m : Nat} (h : n ≤ m) :
    (runPrefix n).1.IsPrefix (runPrefix m).1 := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact List.prefix_refl _
  | succ m ih =>
    by_cases hn : n ≤ m
    · apply (ih hn).trans
      rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.append_assoc]
      exact List.prefix_append _ _
    · have : n = m + 1 := by omega
      subst n; exact List.prefix_refl _

theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ t => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd) t
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  cases e with
  | restart w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | tick w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | deliver w o t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl

theorem fold_deliveries (os : List Object) (nd : FixtureNode) (t : Time) :
    (os.map (fun o => (.deliver 0 o t : Event))).foldl
        (V2.D.World.step env (mkRun [])) (fun _ => nd) =
      fun _ => os.foldl (fgsa params unitCodec).process nd := by
  induction os generalizing nd with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_constant]
    exact ih _

/-- The cached node equals the engine fold, for every prefix length. -/
theorem prefix_cached (n : Nat) :
    (runPrefix n).1.foldl (V2.D.World.step env (mkRun [])) V2.D.World.init =
      fun _ => (runPrefix n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runPrefix_succ]
    simp only [batch, List.foldl_append, ih]
    rw [List.foldl_cons, List.foldl_nil, step_constant, fold_deliveries]

def batchEvents (n : Nat) : List Event :=
  [.tick 0 (n : Time)] ++
    (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2.map
      (fun o => .deliver 0 o (n : Time))

theorem prefix_flat (n : Nat) :
    (runPrefix n).1 = (List.range n).flatMap batchEvents := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runPrefix_succ, batch, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, batchEvents]
    rw [← ih, List.append_assoc]

theorem tick_at (n : Nat) (hn : n < 311) :
    run.events[(runPrefix n).1.length]? = some (.tick 0 (n : Time)) := by
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 311 by omega)
  change (runPrefix 311).1[(runPrefix n).1.length]? = _
  rw [← he, runPrefix_succ]
  simp [batch, List.append_assoc]

theorem state_before_tick (n : Nat) (hn : n < 311) :
    V2.D.Run.stateBefore env run (runPrefix n).1.length = fun _ => (runPrefix n).2 := by
  obtain ⟨tail, he⟩ := prefix_mono (show n ≤ 311 by omega)
  unfold V2.D.Run.stateBefore
  change ((runPrefix 311).1.take (runPrefix n).1.length).foldl
      (V2.D.World.step env run) V2.D.World.init = _
  rw [← he]
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact prefix_cached n

theorem emits_at_tick (n : Nat) (hn : n < 311) :
    V2.D.Run.emitsAt env run (runPrefix n).1.length =
      (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  rw [V2.D.Run.emitsAt, tick_at n hn, state_before_tick n hn]
  rfl

theorem immediate_delivery (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    run.events[(runPrefix n).1.length + 1]? = some (.deliver 0 o (n : Time)) := by
  have hos : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = [o] := by
    have hl := released_length (runPrefix n).2 (n : Time)
    cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
    | nil => simp [he] at ho
    | cons a as =>
      have has : as = [] := by simpa [he] using hl
      rw [he, has] at ho
      rw [has]
      exact (List.mem_singleton.mp ho) ▸ rfl
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 311 by omega)
  change (runPrefix 311).1[(runPrefix n).1.length + 1]? = _
  rw [← he, runPrefix_succ]
  simp [batch, hos, List.append_assoc]

theorem prefix_strict (n : Nat) :
    (runPrefix n).1.Pairwise (fun e f => e.key < f.key) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    dsimp only [batch]
    rw [List.append_assoc, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · have hl := released_length (runPrefix n).2 (n : Time)
      cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
      | nil => simp
      | cons o os =>
        have hos : os = [] := by simpa [he] using hl
        rw [hos]
        simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.lt_iff]
    · intro e he f hf
      obtain ⟨m, hm, ht, _⟩ := prefix_events_time n e he
      have hft : f.time = (n : Time) := by
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hf
        rcases hf with rfl | ⟨o, _, rfl⟩ <;> rfl
      apply Prod.Lex.lt_iff.mpr
      left
      change e.time < f.time
      rw [ht, hft]
      exact_mod_cast hm

theorem nvSchedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := le_of_lt horizon_pos
  sorted := (prefix_strict 311).imp (fun h => le_of_lt h)
  nodup := by
    have hne : run.events.Pairwise (fun e f => e ≠ f) :=
      (prefix_strict 311).imp (fun h he => by rw [he] at h; exact lt_irrefl _ h)
    exact hne
  in_horizon := by
    intro e he
    obtain ⟨m, hm, ht, _⟩ := prefix_events_time 311 e he
    rw [ht]
    change 0 ≤ (m : Time) ∧ (m : Time) ≤ 310
    exact ⟨Int.natCast_nonneg m, by dsimp only [Time] at *; omega⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    obtain ⟨m, _, ht, _⟩ := prefix_events_time 311 (.tick v t) he
    exact ⟨m, by simpa only [V2.Event.time, env, Int.mul_one] using ht⟩
  tick_total := by
    intro v _ t _ ht hh _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 310 at hh
    have he : t = (t.toNat : Time) := (Int.toNat_of_nonneg ht).symm
    rw [he]
    exact prefix_ticks 311 t.toNat (by dsimp only [Time] at *; omega)

theorem noRestart : V2.D.NoRestart run := by
  intro i v t hi
  obtain ⟨_, _, _, he⟩ := prefix_events_time 311 (.restart v t) (List.mem_of_getElem? hi)
  rcases he with he | ⟨o, he⟩ <;> cases he

set_option maxHeartbeats 2000000 in
-- Index uniqueness uses the symbolic prefix proof through the concrete run type.
theorem delivery_source {i : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) :
    ∃ n : Nat, n < 311 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length + 1 ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  have hm := List.mem_of_getElem? hi
  rw [show run.events = (runPrefix 311).1 from rfl, prefix_flat] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 311 := List.mem_range.mp hn
  simp only [batchEvents, List.mem_append, List.mem_singleton, List.mem_map] at hm
  rcases hm with he | ⟨a, ha, he⟩
  · cases he
  · cases he
    have hd := immediate_delivery n hn' o ha
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
    have hij : i = (runPrefix n).1.length + 1 :=
      (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
    exact ⟨n, hn', rfl, hij, ha⟩

theorem tick_source {i : Nat} {v : Fin 1} {t : Time}
    (hi : run.events[i]? = some (.tick v t)) :
    ∃ n : Nat, n < 311 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length := by
  obtain ⟨n, hn, ht, _⟩ := prefix_events_time 311 (.tick v t) (List.mem_of_getElem? hi)
  change t = (n : Time) at ht
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hd := tick_at n hn
  rw [← ht] at hd
  obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
  exact ⟨n, hn, ht,
    (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)⟩

theorem emitted_wire (n : Nat) (hn : n < 311)
    (hr : EmissionRowsValid (runPrefix n).2.st) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    (fgsa params unitCodec).wellFormed o = true := by
  have hi := tick_at n hn
  have hc := state_before_tick n hn
  obtain ⟨auth, m⟩ := o
  cases auth with
  | none =>
    change (⟨.none, m⟩ : Object) ∈
      (duties params (n : Time)).flatMap (fun d =>
        ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun j =>
          ((fgsa params unitCodec).act ((fgsa params unitCodec).clock (runPrefix n).2
            (n : Time)) d ()).map (fun m => ⟨.seat (RunDuty.signLabel d) j, m⟩))) ++ [] at ho
    rw [List.append_nil] at ho
    obtain ⟨d, _, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨j, _, ho⟩ := List.mem_filterMap.mp ho
    obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp ho
    cases he
  | seat l j =>
    obtain ⟨_, _, d, hl, ht, ha⟩ :=
      (mem_tick_seat_iff env (mkRun []) (runPrefix n).2 0 (n : Time) l j m).mp ho
    change RunDuty.signLabel d = l at hl
    cases d with
    | headAction s =>
      change RunLabel.base (.head s) = l at hl
      subst l
      have he : .head (headVote params
          (FGSA.clock params (runPrefix n).2.st (n : Time)) s).root = m :=
        by
          change (if joinedNow params (clock params (runPrefix n).2.st (n : Time)) then
            some (.head (headVote params
              (clock params (runPrefix n).2.st (n : Time)) s).root) else none) = some m at ha
          split at ha
          · exact Option.some.inj ha
          · cases ha
      subst m
      rfl
    | fgAction r =>
      change RunLabel.base .fg = l at hl
      subst l
      change (attest params (FGSA.clock params (runPrefix n).2.st (n : Time))
        (runPrefix n).2.record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact nv_attest_valid _ _ _ _ hb
    | propAction s =>
      change RunLabel.prop s = l at hl
      subst l
      change SA.proposalTime params.toParams s = (n : Time) at ht
      change (if joinedNow params (clock params (runPrefix n).2.st (n : Time)) then
        (propose params (clock params (runPrefix n).2.st (n : Time)) s).map
          (withApp params 0) else none) = some m at ha
      have ha : (propose params (clock params (runPrefix n).2.st (n : Time)) s).map
          (withApp params 0) = some m := by
        split at ha
        · exact ha
        · cases ha
      have hs0 : 0 < s := by
        by_contra hh
        have hs : s = 0 := Nat.eq_zero_of_not_pos hh
        subst s
        change none = some m at ha
        cases ha
      have hp := fgsa_propose_parent_lt env run nvSchedule (ht.symm ▸ hi) hs0
      rw [hc] at hp
      rw [ht] at hp
      exact nv_proposal_wf _ s 0 (nv_rows_clock _ _ hr) hp ha

theorem prefix_rows (n : Nat) (hn : n ≤ 311) : EmissionRowsValid (runPrefix n).2.st := by
  induction n with
  | zero => exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim⟩
  | succ n ih =>
    have hn' : n < 311 := by omega
    have hr := ih (by omega)
    have hw := emitted_wire n hn' hr
    rw [runPrefix_succ]
    dsimp only [batch]
    have hclock : EmissionRowsValid
        (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1.st := by
      exact (tick_st (c := unitCodec) env (mkRun []) (runPrefix n).2 0 (n : Time)).symm ▸
        nv_rows_clock _ _ hr
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1 = nd at *
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = os at *
    induction os generalizing nd with
    | nil => exact hclock
    | cons a os ih =>
      rw [List.foldl_cons]
      exact ih _ (nv_rows_process nd.st a hclock (hw a (List.mem_cons_self ..)))
        (fun o ho => hw o (List.mem_cons_of_mem a ho))

theorem wire : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).wellFormed o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  exact emitted_wire n hn (prefix_rows n (by omega)) o ho

/-- A delivered proposal is the exact release at its cached tick. -/
theorem nv_delivery_origin {x : Fin 1} {o : Object} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    ∃ n : Nat, n < 311 ∧ ∃ s : Slot,
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 ∧
      o = ofWire params ⟨.proposer s, .proposal N⟩ ∧
      N.slot = s ∧ SA.proposalTime params.toParams s = (n : Time) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  rcases nv_wire_cases o (wire i x o t hi) with ⟨s, j, B, he⟩ | ⟨j, body, he⟩ |
    ⟨s, B, he⟩
  · rw [he] at hp; cases hp
  · rw [he] at hp; cases hp
  · rw [he] at hp
    cases Msg.proposal.inj hp
    subst o
    have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    refine ⟨n, hn, s, ho, rfl, ?_, ha.2.1⟩
    rw [← named_erase_slot, hb]
    rfl

/-- W2's emission equation supplies the small delivered root. -/
theorem nv_delivery_root {x : Fin 1} {o : Object} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    N.root = ⟨N.slot + 1⟩ := by
  obtain ⟨n, hn, s, ho, rfl, _, _⟩ := nv_delivery_origin hd hp
  exact emitted_proposal_slot_root env run (fun _ => rfl)
    (runPrefix n).1.length 0 (n : Time) s N (tick_at n hn)
    ((emits_at_tick n hn).symm ▸ ho)

/-- Equal slots give equal cached ticks, objects, and recursive named proposals. -/
theorem nv_delivery_unique {x y : Fin 1} {o o' : Object} {t u : Time}
    {N M : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N)
    (hd' : V2.Event.deliver y o' u ∈ run.events) (hp' : o'.payload = .proposal M)
    (hs : N.slot = M.slot) : N = M := by
  obtain ⟨n, hn, s, ho, _, hb, ht⟩ := nv_delivery_origin hd hp
  obtain ⟨m, _, s', ho', _, hB, ht'⟩ := nv_delivery_origin hd' hp'
  have hss : s = s' := hb.symm.trans (hs.trans hB)
  have hnm : n = m := by
    have hh := ht.symm.trans (hss ▸ ht')
    exact_mod_cast hh
  subst m
  have hl := released_length (runPrefix n).2 (n : Time)
  have he : o = o' := by
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = os at *
    cases os with
    | nil => cases ho
    | cons a as =>
      have hnil : as = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hl
        omega
      subst as
      exact (List.mem_singleton.mp ho).trans (List.mem_singleton.mp ho').symm
  rw [he, hp'] at hp
  exact (Msg.proposal.inj hp).symm

/-- Each exact delivered parent was held before its actual emission. -/
theorem nvParents : ∀ x o t N,
    V2.Event.deliver x o t ∈ run.events → o.payload = .proposal N →
    ∃ i y, N.parent ∈ (V2.D.Run.stateBefore env run i y).st.namedBodies := by
  intro x o t N hd hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  obtain ⟨j, hj⟩ := emitted_payload_parent_stored env run
    ⟨(runPrefix n).1.length, tick_at n hn, (emits_at_tick n hn).symm ▸ ho⟩ hp
  exact ⟨j, 0, hj⟩

/-- Named origin and exact payload uniqueness prove the premise before Base₂. -/
theorem nvRoots : NamedRootCollisionFree params unitCodec env run where
  root_injective := by
    intro B C hB hC A D hA hD he
    have hAs : NamedProposalInRun params unitCodec env run A := by
      rcases hA with hA | hA
      · exact namedScope_ancestor env run hB hA
      · exact namedScope_ancestor env run hC hA
    have hDs : NamedProposalInRun params unitCodec env run D := by
      rcases hD with hD | hD
      · exact namedScope_ancestor env run hB hD
      · exact namedScope_ancestor env run hC hD
    rcases namedProposalInRun_genesis_or_delivered env run nvParents hAs with rfl | hA
    · rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · rfl
      · obtain ⟨x, o, t, hd, hp⟩ := hD
        have hr := nv_delivery_root hd hp
        have hh := congrArg BlockId.value (he.trans hr)
        change 0 = D.slot + 1 at hh
        exact (Nat.succ_ne_zero _ hh.symm).elim
    · obtain ⟨x, o, t, hd, hp⟩ := hA
      have hr := nv_delivery_root hd hp
      rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · have hh := congrArg BlockId.value (hr.symm.trans he)
        change A.slot + 1 = 0 at hh
        exact (Nat.succ_ne_zero _ hh).elim
      · obtain ⟨y, o', u, hd', hp'⟩ := hD
        have hr' := nv_delivery_root hd' hp'
        apply nv_delivery_unique hd hp hd' hp'
        have hh := congrArg BlockId.value (hr.symm.trans (he.trans hr'))
        change A.slot + 1 = D.slot + 1 at hh
        exact Nat.add_right_cancel hh

theorem state_delivery_store (n : Nat) (hn : n < 311) :
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st =
      FGSA.clock params (runPrefix n).2.st (n : Time) := by
  have hs := (V2.D.Run.step_tick_eq env run (tick_at n hn)).1
  rw [state_before_tick n hn] at hs
  exact (congrArg Node.st hs).trans
    (tick_st (c := unitCodec) env run (runPrefix n).2 0 (n : Time))

theorem emitted_deps (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    depsS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = true := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ | ⟨s, N, rfl⟩
  · rfl
  · rfl
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    have hm := ha.2.2.2.2
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    unfold propose at hm
    split at hm
    · cases hm
    · simp only [Option.map_map] at hm
      obtain ⟨P, hP, heN⟩ := Option.map_eq_some_iff.mp hm
      have hN := Msg.proposal.inj heN
      subst N
      have hs := namedByErase?_sound st _ P hP
      have hc := (storeBundle_postClock env run (runPrefix n).1.length 0 (n : Time)).cstore
      rw [state_before_tick n hn] at hc
      let H := getHead params st (proposerVotes st s) (proposerSupport st s)
      obtain ⟨B, hB, he⟩ := (hc.baseTree H).mp (getHead_stored params st hc _ _)
      have hl := (fgBlockOf_spec params st hc H B).mpr ⟨hB, he⟩
      change (decide (P ∈ st.namedBodies) && (fgBlockOf st P.erase).isSome) = true
      rw [hs.2, hl]
      simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
      exact hs.1

theorem deps : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore env run i v) o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change depsS params _ o = true
  rw [state_delivery_store n hn]
  exact emitted_deps n hn o ho

theorem earlier_batch {i n : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) (hin : i < (runPrefix n).1.length) :
    ∃ m : Nat, m < n ∧ m < 311 ∧ t = (m : Time) ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 := by
  obtain ⟨m, hm, ht, he, ho⟩ := delivery_source hi
  refine ⟨m, ?_, hm, ht, ho⟩
  by_contra hh
  have hl := (prefix_mono (Nat.le_of_not_gt hh)).length_le
  omega

theorem carried_from_state (n : Nat) (hn : n < 311) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') :
    (∃ s j b, o' = ofHead params ⟨.seat (.head s) j, b⟩ ∧
      (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes) ∨
    (∃ a : RowWire params.n, o' = ofRow params a ∧
      (a ∈ (runPrefix n).2.st.rowPool ∨
        ∃ w ∈ (runPrefix n).2.st.proposals, ∃ s N,
          w.decode = some (.block s N) ∧ a ∈ N.rows)) := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, N, rfl⟩
  · exact hc.elim
  · exact hc.elim
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨_, hraw, hsup, hrows⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    have heads (xs : List (HeadWire params.n))
        (hxs : ∀ a ∈ xs, a ∈ (proposerVotes st s).filterMap liftHead?)
        (hc' : o' ∈ xs.map (ofHead params)) :
        ∃ r j B, o' = ofHead params ⟨.seat (.head r) j, B⟩ ∧
          (⟨.seat r j, .head B⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes := by
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp (hxs a hm)
      obtain ⟨he, r, j, B, rfl⟩ := nv_liftHead w a hl
      have hpool : w ∈ st.base.votes := (List.mem_filter.mp hw).1
      rw [← he] at hpool
      change (⟨.seat r j, .head B⟩ : GridCO.Wire params.n .root) ∈
        (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes at hpool
      rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hpool
      exact ⟨r, j, B, rfl, hpool⟩
    rcases hc with hc | hc | hc
    · left
      rw [hraw] at hc
      exact heads _ (fun _ h => h) hc
    · left
      rw [hsup] at hc
      exact heads _ (nv_proposal_votes st s).2 hc
    · right
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc
      rw [hrows, proposalRows_eq_proposalRowsFor] at hm
      have horigin := proposalRowsFor_origin params st (st.slot params) _ a hm
      rcases horigin with hm | ⟨w, hw, r, M, hd, hm⟩
      · rw [clock_rowPool] at hm
        exact ⟨a, rfl, Or.inl hm⟩
      · rw [clock_proposals] at hw
        exact ⟨a, rfl, Or.inr ⟨w, hw, r, M, hd, hm⟩⟩

def EarlierEmitted (n : Nat) (o : Object) : Prop :=
  ∃ m : Nat, m < n ∧ m < 311 ∧
    o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2

theorem handled_before (n : Nat)
    (past : ∀ m : Nat, m < n → m < 311 → ∀ o o' : Object,
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 →
      carriesS params o o' → EarlierEmitted m o')
    (j : Nat) (hj : j < (runPrefix n).1.length) (o : Object) (t : Time)
    (hh : V2.D.Run.handlesAt env run j 0 o t) : EarlierEmitted n o := by
  obtain ⟨parent, he, hh⟩ := hh
  obtain ⟨m, hmn, hm, _, ho⟩ := earlier_batch he hj
  rcases nv_handles_carries _ parent o hh with rfl | hc
  · exact ⟨m, hmn, hm, ho⟩
  · obtain ⟨k, hkm, hk, ho'⟩ := past m hmn hm parent o ho hc
    exact ⟨k, hkm.trans hmn, hk, ho'⟩

theorem carried_authentic (n : Nat) (hn : n < 311) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') : EarlierEmitted n o' := by
  induction n using Nat.strong_induction_on generalizing o o' with
  | h n ih =>
    have past := fun m hm => ih m hm
    have hbefore := handled_before n past
    rcases carried_from_state n hn o o' ho hc with ⟨s, j, b, rfl, hm⟩ |
      ⟨a, rfl, hm | ⟨w, hw, s, N, hd, hm⟩⟩
    · have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
          (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
        rw [state_before_tick n hn]
        exact hm
      rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
      obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
      dsimp only at he
      subst v
      obtain ⟨i, hi, t, ha, _⟩ := fgsa_vote_stamp_source env run noRestart (runPrefix n).1.length
        0 s j b stamp hstamp
      exact hbefore i hi _ t ha.1
    · have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
        rw [state_before_tick n hn]
        exact hm
      obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
      exact hbefore i hi _ t hh
    · have hp : w ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.proposals := by
        rw [state_before_tick n hn]
        exact hw
      obtain ⟨i, parent, t, hi, he, hwire, _, _⟩ :=
        stored_proposal_delivered env run (runPrefix n).1.length 0 w hp
      have hpay := congrArg Signed.payload (hwire.trans (decode_eq_block.mp hd))
      change parent.payload = .proposal N at hpay
      have hcarry : carriesS params parent (ofRow params a) := by
        exact nv_carries_payload parent _ N hpay
          (Or.inr (Or.inr (List.mem_map.mpr ⟨a, hm, rfl⟩)))
      obtain ⟨m, hmn, hmb, _, hem⟩ := earlier_batch he hi
      obtain ⟨k, hkm, hkb, hek⟩ := past m hmn hmb parent (ofRow params a) hem hcarry
      exact ⟨k, hkm.trans hmn, hkb, hek⟩

theorem head_pool_authentic (n : Nat) (hn : n < 311) (s : Slot) (j : Fin params.n) (b : BlockId)
    (hm : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈ (runPrefix n).2.st.base.votes) :
    EarlierEmitted n (ofHead params ⟨.seat (.head s) j, b⟩) := by
  have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
      (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
    rw [state_before_tick n hn]
    exact hm
  rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
  obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
  dsimp only at he
  subst v
  obtain ⟨i, hi, t, ha, _⟩ :=
    fgsa_vote_stamp_source env run noRestart (runPrefix n).1.length 0 s j b stamp hstamp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t ha.1

theorem row_pool_authentic (n : Nat) (hn : n < 311) (a : RowWire params.n)
    (hm : a ∈ (runPrefix n).2.st.rowPool) : EarlierEmitted n (ofRow params a) := by
  have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
    rw [state_before_tick n hn]
    exact hm
  obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t hh

theorem prefix_length_strict {m n : Nat} (h : m < n) :
    (runPrefix m).1.length < (runPrefix n).1.length := by
  have hs : (runPrefix m).1.length < (runPrefix (m + 1)).1.length := by
    rw [runPrefix_succ]
    simp only [batch, List.length_append, List.length_singleton, List.length_map]
    omega
  exact hs.trans_le (prefix_mono (show m + 1 ≤ n by omega)).length_le

theorem emitted_fresh (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    processedS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = false := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, N, rfl⟩
  · change decide ((⟨.seat s j, .head b⟩ : GridCO.Wire params.n .root) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes) = false
    apply decide_eq_false
    intro hm
    rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := head_pool_authentic n hn s j b hm
    have ht := ((fgsa_emits_head env (mkRun []) (runPrefix n).2 0 (n : Time) s j b).mp ho).2.1
    have hm' := ((fgsa_emits_head env (mkRun []) (runPrefix m).2 0 (m : Time) s j b).mp hem).2.1
    have he : (m : Time) = (n : Time) := hm'.symm.trans ht
    have hne : m = n := by exact_mod_cast he
    omega
  · change decide ((⟨.seat .fg j, body⟩ : RowWire params.n) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).rowPool) = false
    apply decide_eq_false
    intro hm
    rw [clock_rowPool] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := row_pool_authentic n hn ⟨.seat .fg j, body⟩ hm
    obtain ⟨_, _, r, _, ha⟩ := (fgsa_emits_row env (mkRun []) (runPrefix n).2
      0 (n : Time) j body).mp ho
    have hsent := fgsa_row_sent_before env run 0 j body (prefix_length_strict hmn)
      (m : Time) (tick_at m hmb) ((emits_at_tick m hmb).symm ▸ hem)
    rw [state_before_tick n hn] at hsent
    exact attest_some_fresh _ _ _ _ ha hsent
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal N)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 N ha.2.2.2.2
    have hs0 : 0 < s := by
      by_contra hh
      have he : s = 0 := Nat.eq_zero_of_not_pos hh
      subst s
      have hnone := ha.2.2.2.2
      change (none : Option (Msg params.n)) = some (Msg.proposal N) at hnone
      cases hnone
    have ht := ha.2.1
    have hg := (fgsa_stored_block_slots env run nvSchedule (ht.symm ▸ tick_at n hn) hs0).2.2.2
    rw [state_before_tick n hn, ht] at hg
    change decide (∃ B ∈ (FGSA.clock params (runPrefix n).2.st (n : Time)).fg.TF,
      B.root = N.root) = false
    apply decide_eq_false
    rintro ⟨B, hB, hroot⟩
    have hc := cstoreInv_stateBefore env run (runPrefix n).1.length 0
    have hm : B ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.fg.TF := by
      rw [state_before_tick n hn]
      simpa only [clock_fg] using hB
    have hBs := rootBlockInRun_held env run (Finset.mem_univ 0)
      (runPrefix n).1.length ((hc.baseTree _).mpr ⟨B, hm, rfl⟩)
    have hbs := rootBlockInRun_delivered env run
      (List.mem_of_getElem? (immediate_delivery n hn _ ho)) rfl
    have he : eraseFG B = N.erase := rootBlockInRun_eq env run nvRoots hBs hbs
      ((eraseFG_root B).trans (hroot.trans (named_erase_root N).symm))
    have hslot : B.slot = s := (eraseFG_slot B).symm.trans
      ((congrArg Block.slot he).trans (by rw [hb]; rfl))
    have hh := hg B hB
    rw [hslot] at hh
    exact lt_irrefl s hh

theorem fgp_fresh : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore env run i v) o = false := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change processedS params _ o = false
  rw [state_delivery_store n hn]
  exact emitted_fresh n hn o ho

theorem nvExecution : V2.D.ExecutionValid env run where
  tick_awake := by intros; rfl
  deliver_awake := by intros; rfl
  restart_awake := by intros; rfl
  wake_restart := by intro v hv t ht hh hw; cases hw.2
  toScheduleWellFormed := nvSchedule
  wire := wire
  deps := deps
  fresh := fgp_fresh
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(n : Time), le_rfl, (runPrefix n).1.length, tick_at n hn,
      (emits_at_tick n hn).symm ▸ ho⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    obtain ⟨m, hmn, hm, hem⟩ := carried_authentic n hn o o' ho hc
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(m : Time), by exact_mod_cast hmn.le, (runPrefix m).1.length, tick_at m hm,
      (emits_at_tick m hm).symm ▸ hem⟩

/-- Every honest emission is delivered immediately in this concrete run. -/
theorem nvReceiptRoots : NamedReceiptRootCollisionFree params unitCodec env run := by
  have scope (A : NamedProposal params.n)
      (h : NamedProposalReceiptScope params unitCodec env run A) :
      NamedProposalInRun params unitCodec env run A := by
    rcases h with h | ⟨v, hv, o, t, N, ⟨i, hi, ho⟩, hp, hAN⟩
    · exact h
    · obtain ⟨n, hn, rfl, rfl⟩ := tick_source hi
      rw [emits_at_tick n hn] at ho
      exact ⟨N, Or.inl ⟨0, o, (n : Time),
        List.mem_of_getElem? (immediate_delivery n hn o ho), hp⟩, hAN⟩
  intro A B hA hB he
  exact nvRoots.root_injective A B (scope A hA) (scope B hB)
    A B (Or.inl ((named_preceq_refl _))) (Or.inr ((named_preceq_refl _))) he

theorem base : Base₂ params unitCodec env run where
  valid := nvExecution
  receiptIdealization := nvReceiptRoots
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    rcases l with (_ | _) | _
    · exact hl.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hl.elim
  cstar := by
    intro l hl
    rcases l with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hl.elim
    · exact hl.elim
  restartsAtWakes := by
    intro v t h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact (noRestart i v t hi).elim
  delta := env_delta

theorem honest_slot {s : Slot} (hs : 0 < s) :
    Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  rw [Gen.V2.Duty.HonestSlot_def]
  exact ⟨hs, Finset.mem_univ _⟩

theorem proposer_gap (t : Time) (ht : env.t_GST ≤ t) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + gap ∧
      Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  change 0 ≤ t at ht
  dsimp only [Time] at *
  have he : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  refine ⟨t.toNat / 4 + 1, ?_, ?_, honest_slot (by dsimp only [Slot]; omega)⟩
  · change t < 4 * ((t.toNat / 4 + 1 : Nat) : Time)
    dsimp only [Time] at *
    omega
  · change 4 * ((t.toNat / 4 + 1 : Nat) : Time) ≤ t + 4
    dsimp only [Time] at *
    omega

theorem fault_value : (Gen.V2.Duty.faulty run).card = 0 := by
  rw [Gen.V2.Duty.faulty_def]
  change (Finset.univ \ Finset.univ : Finset (Fin 1)).card = 0
  simp

/-- An honest emission has reached its own admission clock. -/
theorem emitted_admission (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    fgsaAdmissionTime params o ≤ (n : Time) := by
  rcases nv_wire_cases o (emitted_wire n hn (prefix_rows n (by omega)) o ho) with
    ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ | ⟨s, N, rfl⟩
  · have ht := ((fgsa_emits_head env (mkRun []) (runPrefix n).2 0
      (n : Time) s j b).mp ho).2.1
    change 4 * (s : Time) + 1 = (n : Time) at ht
    change 4 * (s : Time) ≤ (n : Time)
    dsimp [Time] at *
    omega
  · change (0 : Time) ≤ (n : Time)
    positivity
  · have ht := ((fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0
      (n : Time) s (.proposal N)).mp ho).2.1
    exact ht.le

/-- Immediate self-delivery processes or permanently excludes the emitted object. -/
theorem emitted_settled (n : Nat) (hn : n < 311) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    (fgsa params unitCodec).processed
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 2) 0) o = true ∨
    (fgsa params unitCodec).excludes
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 2) 0) o = true := by
  have hd := immediate_delivery n hn o ho
  have ht : fgsaTimely params
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0) o := by
    change fgsaAdmissionTime params o ≤
      (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st.base.now
    rw [state_delivery_store n hn]
    rw [(clock_vn (runPrefix n).2.st (n : Time)).2]
    exact emitted_admission n hn o ho
  have hp := (fgsaAcceptance params unitCodec).accepts
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0) o o
    (cstoreInv_stateBefore env run _ 0) (Or.inl rfl)
    (wire _ 0 o (n : Time) hd) (deps _ 0 o (n : Time) hd) ht
  rw [V2.D.Run.stateBefore_succ env run hd]
  exact hp

theorem sync : Gen.V2.Duty.PartialSynchronyBy env run (fgsaDelay env.Δ deltaF) where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, ho⟩ w _ a hta _ had _ _ _ hExcl
    obtain ⟨n, hn, rfl, rfl⟩ := tick_source hi
    rw [emits_at_tick n hn] at ho
    have hw : w = 0 := Subsingleton.elim _ _
    subst w
    by_cases he : (n : Time) = a
    · right
      exact ⟨(n : Time), he.symm.le, he ▸ had, (runPrefix n).1.length + 1,
        o, immediate_delivery n hn o ho, Or.inl rfl⟩
    · left
      obtain hp | hx := emitted_settled n hn o ho
      · refine ⟨(runPrefix n).1.length + 2, ?_, hp⟩
        have hk := (index_lt_actionCut_iff nvSchedule
        (immediate_delivery n hn o ho) a).mpr (Or.inl (lt_of_le_of_ne hta he))
        omega
      · have hidx := (Gen.V2.Duty.index_lt_idxBefore_iff nvSchedule
          (immediate_delivery n hn o ho) _).mpr (hta.trans_lt had)
        change (runPrefix n).1.length + 1 <
          V2.D.Run.idxBefore run (max a env.t_GST + fgsaDelay env.Δ deltaF o) at hidx
        have hx' := (fgsaHooks params unitCodec).excludes_stable env run nvSchedule 0 o
          ((runPrefix n).1.length + 2)
          (V2.D.Run.idxBefore run (max a env.t_GST + fgsaDelay env.Δ deltaF o))
          (by omega)
          (noRestart.restartFree 0 _ _) hx
        rw [Gen.V2.Duty.stateBefore_idxBefore env run _ nvSchedule] at hx'
        exact Bool.noConfusion (hx'.symm.trans hExcl)
  relay_accepted := by
    intro v _ i o t ha w _ a hta _ had _ _ _ _
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    by_cases he : t = a
    · right
      exact ⟨t, he.symm.le, he ▸ had, i, ha.1⟩
    · left
      refine ⟨i + 1, ?_, ha.2.2⟩
      obtain ⟨o', hi, _⟩ := ha.1
      have hk := (index_lt_actionCut_iff nvSchedule hi a).mpr
        (Or.inl (lt_of_le_of_ne hta he))
      omega

theorem nvRecovery : RecoverySleep₂ params unitCodec env run gap deltaF where
  sync := sync
  deltaF := deltaF_lower
  gap := by intro t ht _; exact proposer_gap t ht
  base := base
  fault := by rw [fault_value]; decide
  awake := by intros; rfl
  gapPos := gap_lower
  suffixNoRestart := by intro x hx i t hi; exact (noRestart i x t hi).elim
  joinedGap := by
    intro t ht hh
    obtain ⟨s, hts, hst, hs⟩ := proposer_gap t (by
      change (0 : Time) ≤ t
      change (6 : Time) ≤ t at ht
      dsimp only [Time] at *
      omega)
    refine ⟨s, hts, hst, hs, ?_⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro u _ _ hw; cases hw.2
    · intro u _ _ hu
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
      exact (noRestart i _ u hi).elim

theorem healingSet : HealingSet params unitCodec env run gap deltaF := nvRecovery

theorem healingPrem {Pt : Type} (pt : Pt) :
    HealingPrem params unitCodec gap deltaF env run pt := ⟨healingSet, livenessBound⟩

theorem healingTimePrem : HealingTimePrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), healing_horizon⟩

theorem resetArrivalPrem : ResetArrivalPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_horizon⟩

theorem resetArrivalFullPrem : ResetArrivalFullPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_full_horizon⟩

theorem renewedPromotionPrem : RenewedPromotionPrem params unitCodec gap deltaF env run ⟨3⟩ :=
  ⟨healingPrem (⟨3⟩ : PtR), renewed_three_horizon⟩

-- NV4 uses the same fixture and the prefix invariants above.
def actionNode (r : Nat) : FixtureNode :=
  (fgsa params unitCodec).clock (runPrefix (params.actionTime r).toNat).2
    (params.actionTime r)

def rowAtAction (r : Nat) : Option RowPayload :=
  (attest params (actionNode r).st (actionNode r).record ⟨0, params.nPos⟩).1

def sourceAtAction (r : Nat) : Option (FGBlock (Fin params.n)) :=
  (fgInputs params (actionNode r).st).1

def rowEntry (r : Nat) : Option (Nat × BlockId) :=
  (rowAtAction r).bind (fun a => namedEntry a.height_pair)

-- These evaluations use at most 43 ticks, through cached nodes.

/-- S5 NV6: The time filter of any longer prefix gives the same shorter prefix.
DC: SAME canonical fixture and cached prefix proof. -/
theorem prefix_cut (n m : Nat) (hn : n ≤ m) :
    (runPrefix m).1.filter (fun e => decide (e.time < (n : Time))) = (runPrefix n).1 := by
  induction m generalizing n with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.filter_append, List.filter_append, ih n hnm]
      have ht : decide ((m : Time) < (n : Time)) = false := by
        apply decide_eq_false
        exact not_lt.mpr (by exact_mod_cast hnm)
      have hd : ((V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2.map
          (fun o => (.deliver 0 o (m : Time) : Event))).filter
            (fun e => decide (e.time < (n : Time))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
        change ¬ decide ((m : Time) < (n : Time)) = true
        rw [ht]
        decide
      rw [hd]
      simp only [List.filter_cons, List.filter_nil]
      change ((runPrefix n).1 ++
        (if decide ((m : Time) < (n : Time)) = true then [.tick 0 (m : Time)] else [])) ++ [] = _
      rw [ht]
      simp
    · have he : n = m + 1 := by omega
      subst n
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨k, hk, ht, _⟩ := prefix_events_time (m + 1) e he
      rw [ht]
      exact decide_eq_true (by exact_mod_cast hk)

/-- S5 NV6: The inclusive read at tick n is the cached node after tick n.
DC: SAME canonical fixture and cached prefix proof. -/
theorem read_prefix (n : Nat) (hn : n < 311) :
    V2.D.Run.readAt env run (n : Time) = fun _ => (runPrefix (n + 1)).2 := by
  have hp : run.events.filter (fun e => decide (e.time ≤ (n : Time))) =
      (runPrefix (n + 1)).1 := by
    have he : (fun e : Event => decide (e.time ≤ (n : Time))) =
        (fun e : Event => decide (e.time < ((n + 1 : Nat) : Time))) := by
      funext e
      have hp : e.time ≤ (n : Time) ↔ e.time < ((n + 1 : Nat) : Time) := by
        dsimp only [Time]
        push_cast
        omega
      exact decide_eq_decide.mpr hp
    rw [he]
    exact prefix_cut (n + 1) 311 (by omega)
  unfold V2.D.Run.readAt
  rw [hp]
  exact prefix_cached (n + 1)

theorem frontier_cached (n : Nat) (hn : n < 311) :
    honestFrontier params unitCodec env run (n : Time) = (runPrefix (n + 1)).2.st.fg.h_max := by
  unfold honestFrontier
  rw [read_prefix n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix (n + 1)).2.st.fg.h_max) = _
  simp

theorem frontier_idx_cached (n : Nat) (hn : n < 311) :
    frontierAtIdx params unitCodec env run (runPrefix n).1.length =
      (runPrefix n).2.st.fg.h_max := by
  unfold frontierAtIdx storeAt
  rw [state_before_tick n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix n).2.st.fg.h_max) = _
  simp

set_option maxHeartbeats 2000000 in
-- The kernel checks the cached state after the first 31 ticks.
theorem nvCachedFrontier : (runPrefix 31).2.st.fg.h_max = 2 := by decide +kernel

theorem nvFrontier : honestFrontier params unitCodec env run 30 = 2 :=
  (frontier_cached 30 (by decide)).trans nvCachedFrontier

theorem nvFrontierAtIdx : frontierAtIdx params unitCodec env run (runPrefix 31).1.length = 2 :=
  (frontier_idx_cached 31 (by decide)).trans nvCachedFrontier

theorem action_read (r : Nat) (hr : (params.actionTime r).toNat < 311) :
    postClock env run 0 (params.actionTime r) = some (actionNode r) := by
  have ht : ((params.actionTime r).toNat : Time) = params.actionTime r := by
    apply Int.toNat_of_nonneg
    change 0 ≤ 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1
    omega
  have he := tick_at (params.actionTime r).toNat hr
  rw [ht] at he
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event params unitCodec env run nvSchedule he,
    Option.map_some, state_before_tick (params.actionTime r).toNat hr]
  rfl

theorem source_read (r : Nat) (hr : (params.actionTime r).toNat < 311) :
    actionSourceFG params unitCodec env run 0 r = some (sourceAtAction r) := by
  rw [actionSourceFG_def, action_read r hr]
  rfl

-- The reset source and wire come from the round-3 action itself.
def resetSource : FGBlock (Fin params.n) := (sourceAtAction 3).getD .genesis
def resetRow : RowWire params.n :=
  ⟨.seat .fg ⟨0, params.nPos⟩, (rowAtAction 3).getD (.vote ⟨.empty, none⟩)⟩

def w : HealingWitness :=
  ⟨0, 30, 2, 3, 9, eraseFG resetSource, 0, .genesis⟩

set_option maxHeartbeats 2000000 in
-- The kernel checks the source at tick 42, using its cached prefix.
theorem nvSourceHeight : (sourceAtAction 3).map (fun C => (heightView params C).h) = some 3 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete source slot at tick 42.
theorem nvSourceSlot : resetSource.slot = 9 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete row and source entry at tick 42.
theorem nvResetRowFields :
    namedEntry resetRow.payload.height_pair =
      some (3, (heightView params resetSource).T_h.root) := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete wire emission at tick 42.
theorem nvResetEmissionWire :
    toWire params (ofRow params resetRow) ∈
      (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2.map (toWire params) := by
  decide +kernel

theorem nvResetEmission :
    ofRow params resetRow ∈ (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2 := by
  obtain ⟨o, ho, he⟩ := List.mem_map.mp nvResetEmissionWire
  have heq : o = ofRow params resetRow := (toWireEquiv params).injective he
  exact heq ▸ ho

theorem nvSource : sourceAtAction 3 = some resetSource := by
  have h := nvSourceHeight
  cases he : sourceAtAction 3 with
  | none => rw [he] at h; cases h
  | some C => simp only [resetSource, he, Option.getD_some]

theorem nvResetHeight : (heightView params resetSource).h = 3 := by
  have h := nvSourceHeight
  rw [nvSource] at h
  exact Option.some.inj h

theorem nvHonestResetRow :
    HonestRowAt params unitCodec env run (runPrefix 42).1.length 0 3 resetRow := by
  refine ⟨Finset.mem_univ _, tick_at 42 (by decide), ?_⟩
  rw [emits_at_tick 42 (by decide)]
  exact nvResetEmission

set_option maxHeartbeats 2000000 in
-- The kernel checks only the first three action prefixes.
theorem nvEarlySourceHeights :
    ((sourceAtAction 0).map (fun C => (heightView params C).h),
     (sourceAtAction 1).map (fun C => (heightView params C).h),
     (sourceAtAction 2).map (fun C => (heightView params C).h)) =
      (none, some 1, some 2) := by decide +kernel

/-- S5 NV6: Every named honest row in rounds 0--2 has height at most 2.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvEarlyRowCap {j : Nat} {y : Fin 1} {r h : Nat} {a : RowWire params.n} {e : BlockId}
    (ha : HonestRowAt params unitCodec env run j y r a)
    (he : namedEntry a.payload.height_pair = some (h, e)) (hr : r < 3) : h ≤ 2 := by
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : (params.actionTime r).toNat < 311 := by
    change (4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1).toNat < 311
    push_cast
    omega
  obtain ⟨C, _, hC, hh, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read r hb] at hC
  have hs : (sourceAtAction r).map (fun C => (heightView params C).h) = some h := by
    rw [Option.some.inj hC]
    exact congrArg some hh.symm
  have h0 : (sourceAtAction 0).map (fun C => (heightView params C).h) = none :=
    congrArg Prod.fst nvEarlySourceHeights
  have h1 : (sourceAtAction 1).map (fun C => (heightView params C).h) = some 1 :=
    congrArg (fun z => z.2.1) nvEarlySourceHeights
  have h2 : (sourceAtAction 2).map (fun C => (heightView params C).h) = some 2 :=
    congrArg (fun z => z.2.2) nvEarlySourceHeights
  have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [h0] at hs
    cases hs
  · rw [h1] at hs
    have hh' : h = 1 := (Option.some.inj hs).symm
    omega
  · rw [h2] at hs
    have hh' : h = 2 := (Option.some.inj hs).symm
    omega

theorem nvRowCap : ∀ j y r a h e t,
    HonestRowAt params unitCodec env run j y r a →
    run.events[j]? = some (.tick y t) → t ≤ 30 →
    namedEntry a.payload.height_pair = some (h, e) → h ≤ 2 := by
  intro j y r a h e t ha ht hcut he
  have heq : params.actionTime r = t :=
    (V2.Event.tick.inj (Option.some.inj (ha.2.1.symm.trans ht))).2
  have hr : r < 3 := by
    rw [← heq] at hcut
    change 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1 ≤ 30 at hcut
    push_cast at hcut
    omega
  exact nvEarlyRowCap ha he hr

/-- S5 NV6: With GST zero, no source vote is strictly before GST.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvOldRowsEmpty : oldRowHeights params unitCodec env run = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro h ⟨j, y, r, a, e, ha, he, ht⟩
  change 4 * 1 * ((r * 3 : Nat) : Int) + 1 < 6 at ht
  have hr : r = 0 := by push_cast at ht; omega
  subst r
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  obtain ⟨C, _, hC, _, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read 0 (by decide)] at hC
  have hn : sourceAtAction 0 = none := by decide +kernel
  rw [hn] at hC
  cases hC

theorem nvMu : muOf params unitCodec env run = 1 := by
  rw [muOf_def, nvOldRowsEmpty]
  simp

theorem nvHeightRow : HeightRow params unitCodec env run 3 3 :=
  ⟨(runPrefix 42).1.length, 0, resetRow, (heightView params resetSource).T_h.root,
    nvHonestResetRow, nvResetRowFields⟩

theorem nvResetFirst : ∀ r, HeightRow params unitCodec env run r 3 → 3 ≤ r := by
  rintro r ⟨j, y, a, e, ha, he⟩
  by_contra hn
  have h := nvEarlyRowCap ha he (by omega)
  omega

-- Keep the concrete witness terms closed during the final structure assembly.
attribute [irreducible] resetSource resetRow

theorem nvFresh : ∃ j y, ∃ (a : RowWire params.n) (C : FGBlock (Fin params.n)),
    HonestRowAt params unitCodec env run j y 3 a ∧
    namedEntry a.payload.height_pair = some (3, (heightView params C).T_h.root) ∧
    actionSourceFG params unitCodec env run y 3 = some (some C) ∧
    eraseFG C = eraseFG resetSource ∧ (heightView params C).h = 3 := by
  have hs : actionSourceFG params unitCodec env run 0 3 = some (some resetSource) :=
    (source_read 3 (by decide)).trans (congrArg some nvSource)
  exact ⟨(runPrefix 42).1.length, 0, resetRow, resetSource, nvHonestResetRow,
    nvResetRowFields, hs, Eq.refl _, nvResetHeight⟩

set_option maxHeartbeats 2000000 in
-- The assembly checks the concrete witness after the short-prefix source proof.
/-- S5 NV6: All 13 reset fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset : H0Reset params unitCodec env run w where
  rG_after := by decide
  rG_first := by intro r _; exact Nat.zero_le r
  cut := by decide
  frontier := nvFrontier.symm
  rowCap := nvRowCap
  mu_le := by change muOf params unitCodec env run ≤ 2; rw [nvMu]; decide
  cut_lower := by decide
  cut_upper := by decide
  reset_row := nvHeightRow
  reset_first := nvResetFirst
  label := rfl
  fresh := nvFresh
  synchronous := by decide

-- NV5 evaluates only proposal prefixes through tick 52.
def proposalObjects (s : Slot) : List Object :=
  (V2.D.tick env (mkRun []) (runPrefix (4 * s)).2 0 (4 * (s : Time))).2

def proposalBlocks (s : Slot) : List Block :=
  (proposalObjects s).filterMap (fun o => (fgsaInterface params unitCodec).block o.payload)

/-- S5 NV6: The chain is in child-to-parent order; each node records its slot and body.
DC: SAME canonical fixture and cached prefix proof. -/
def parentChain : Block → List (Slot × Nat)
  | .genesis => [(0, 0)]
  | .node B s _ x => (s, x) :: parentChain B

def firstProposal : Block := (proposalBlocks 11).headD .genesis

def w' : HealingWitness := { w with u := 11, QStar := firstProposal }

set_option maxHeartbeats 2000000 in
-- The kernel compares the cached proposal and reset-source prefixes.
/-- S5 NV6: The block of the first proposal has C* as its second parent.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvFirstParents : firstProposal.parent.parent = eraseFG resetSource := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks ancestry through the cached prefixes at ticks 42 and 44.
theorem nvSourcePrefix : Block.Preceq (eraseFG resetSource) firstProposal := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the block emitted from the cached state at tick 44.
theorem nvFirstMember : firstProposal ∈ proposalBlocks 11 := by decide +kernel

/-- S5 NV6: A cached block emission is an honest proposal of the complete run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem honestProposal_of_cached {s : Slot} {B : Block} (hs : 0 < s)
    (hn : 4 * s < 311) (hB : B ∈ proposalBlocks s) :
    HonestProposal env run (fgsaInterface params unitCodec) s B := by
  obtain ⟨o, ho, hb⟩ := List.mem_filterMap.mp hB
  refine ⟨⟨hs, Finset.mem_univ _⟩, o, ?_, hb⟩
  refine ⟨(runPrefix (4 * s)).1.length, ?_, ?_⟩
  · change run.events[(runPrefix (4 * s)).1.length]? = some (.tick 0 (4 * (s : Time)))
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using tick_at (4 * s) hn
  · rw [emits_at_tick (4 * s) hn]
    simpa only [proposalObjects, Nat.cast_mul, Nat.cast_ofNat] using ho

/-- S5 NV6: w' changes only the proposal slot and block in the copied NV4 witness.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset' : H0Reset params unitCodec env run w' where
  rG_after := nvH0Reset.rG_after
  rG_first := nvH0Reset.rG_first
  cut := nvH0Reset.cut
  frontier := nvH0Reset.frontier
  rowCap := nvH0Reset.rowCap
  mu_le := nvH0Reset.mu_le
  cut_lower := nvH0Reset.cut_lower
  cut_upper := nvH0Reset.cut_upper
  reset_row := nvH0Reset.reset_row
  reset_first := nvH0Reset.reset_first
  label := nvH0Reset.label
  fresh := nvH0Reset.fresh
  synchronous := nvH0Reset.synchronous

theorem nvProposalLower : w'.sStar + 2 ≤ w'.u := by decide

-- Keep the evaluated block closed during proposal and H0 assembly.
attribute [irreducible] firstProposal

theorem nvProposal : HonestProposal env run (fgsaInterface params unitCodec) w'.u w'.QStar := by
  change HonestProposal env run (fgsaInterface params unitCodec) 11 firstProposal
  exact honestProposal_of_cached (by decide) (by decide) nvFirstMember

theorem nvProposalFirst : ∀ v Q, w'.sStar + 2 ≤ v →
    HonestProposal env run (fgsaInterface params unitCodec) v Q → w'.u ≤ v := by
  intro v Q hv _
  exact hv

theorem nvAfterGST : env.t_GST ≤ tstar params w' := by decide

/-- S5 NV6: All H0 fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0 : H0 params unitCodec env run w' where
  toH0Reset := nvH0Reset'
  proposal_lower := nvProposalLower
  proposal := nvProposal
  proposal_first := nvProposalFirst
  after_gst := nvAfterGST
  source_prefix := nvSourcePrefix

theorem nvClock : params.δt = 2 * params.R := by decide
theorem nvTstarValue : tstar params w' = 50 := by decide
theorem nvResetActionValue : params.actionTime w'.rStar = 42 := by decide
theorem nvTimeBudgetValue : params.actionTime w'.rStar + Γ params gap + 4 * params.Δ = 50 := by
  decide

-- Equality is allowed in the first H-time bound: 50 ≤ 42 + 4 + 4.
theorem nvTstarBound :
    tstar params w' ≤ params.actionTime w'.rStar + Γ params gap + 4 * params.Δ := by
  decide

theorem nvResetTimeStrict :
    params.actionTime w'.rStar < recoveryStart params env + B'_resetF params deltaF gap := by
  decide

-- Both horizon forms hold at 303 ≤ 310 on this run.
theorem nvFullHorizon :
    recoveryStart params env + B'_resetF params deltaF gap +
        Γ params gap + 4 * params.Δ ≤ run.horizon :=
  healing_resetFull_horizon params gap deltaF (recoveryStart params env) run.horizon healing_horizon

theorem nvTimeStrict :
    params.actionTime w'.rStar + Γ params gap + 4 * params.Δ <
      recoveryStart params env + B_HF params deltaF gap :=
  healing_time_strict_of_reset params gap deltaF (recoveryStart params env)
    (params.actionTime w'.rStar) nvResetTimeStrict


/-- S5 NV6 N1: apply the closed row permission producer to the NV3 package.
DC: SAME canonical run, action source, and row entry. -/
theorem nvRowPermission : RowPermissionAt params unitCodec env run :=
  fgsa_rowPermissionClaim params gap deltaF nvClock unitCodec env run () (healingPrem ())

/-- S5 NV6 N1: apply the closed renewed promotion producer to round 3.
DC: SAME canonical run and the proved 66 <= 310 horizon. -/
theorem nvRenewedPromotion : RenewedPromotionConcl params unitCodec env run gap 3 :=
  fgsa_renewedPromotionClaim params gap deltaF nvClock unitCodec env run ⟨3⟩
    renewedPromotionPrem

/-- S5 NV6 N1: adapt the closed reset-only statement to its claim.
DC: SAME reset-only conclusion; full H0 is a separate item. -/
theorem nvResetArrivalClaim : ResetArrivalClaim params := by
  intro G ΔF hδ V _ _ In c E rho pt h
  exact healing_resetArrivalStatement params G ΔF hδ c E rho h.set h.bound h.hhor

/-- S5 NV6 N1: apply the reset-only claim to the NV3 package.
DC: SAME canonical run and the proved 295 <= 310 horizon. -/
theorem nvResetArrival : ResetArrivalConcl params unitCodec env run gap deltaF :=
  nvResetArrivalClaim gap deltaF nvClock unitCodec env run () resetArrivalPrem

/-- S5 NV6 N1: the NV5 full witness supplies the healing input package.
DC: SAME full H0 and tstar = 50; this package is closed. -/
theorem nvHealingInputPrem : HealingInputPrem params unitCodec gap deltaF env run ⟨w'⟩ :=
  ⟨⟨healingPrem (⟨w'⟩ : PtW), nvH0⟩, by change (50 : Time) ≤ 310; decide⟩

/-- Blueprint 21 H.18–H.22; plan S5 NV7 N2: apply the closed full reset statement.
DC: SAME canonical run and the proved full reset horizon. -/
theorem nvResetArrivalFull : ∃ witness, H0 params unitCodec env run witness ∧
    params.actionTime witness.rStar < recoveryStart params env + B'_resetF params deltaF gap :=
  healing_resetArrivalFull params gap deltaF nvClock unitCodec env run
    healingSet livenessBound nvFullHorizon

/-- Blueprint 21 H.18–H.22; plan S5 NV7 N2: apply the closed HealingInputClaim.
DC: SAME canonical run and the full NV5 witness with tstar = 50. -/
theorem nvHealingInput : HealingInput params unitCodec env run w' deltaF :=
  healing_healingInputClaim params gap deltaF nvClock unitCodec env run ⟨w'⟩ nvHealingInputPrem


/-! P0d7c: the generic chain on this exact run. Witness w' (tstar = 50), ΔF = 3, g = 1,
local time t = 50, W_W = 49, local deadline 99; selected round q = r = 5 (opening slot 15,
time 60), kernel deadline 97. Horizon 310. -/

open Gen.Pure

theorem nvRunHorizon : run.horizon = horizon := rfl

/-- Copied from Tests/NonVacuity/FinalityClaims.lean: every positive slot is honest. -/
theorem nvGood (r : Nat) (hr : 1 ≤ r) :
    FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      params.R (kappaF params deltaF) r := by
  rw [FGoodE_W_def]
  refine ⟨honest_slot (by change 0 < r * 3; omega),
    honest_slot (by change 0 < (r + 1) * 3; omega),
    ⟨(r + 2) * 3, ?_, ?_, honest_slot (by change 0 < (r + 2) * 3; omega)⟩, ?_⟩
  · change (r + 1) * 3 + 3 ≤ (r + 2) * 3
    omega
  · exact le_rfl
  · apply honest_slot
    change 0 < (r + 2) * 3 + 3
    omega

/-- Copied from Tests/NonVacuity/FinalityClaims.lean: the W recurrence from recoveryStart. -/
theorem nvRecFE : FE_W params deltaF
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      (recoveryStart params env) run.horizon 1 := by
  rw [FE_W_def, RecFE_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  exact ⟨q, (by rw [InWindow_def]; exact ⟨le_rfl, Nat.lt_succ_self q⟩), nvGood q hq⟩

theorem nvFinalitySet : FinalitySet_W params unitCodec env run gap deltaF .recFE 1 := by
  refine ⟨nvRecovery, livenessBound, ?_⟩
  rw [FinFormW.holdsW_def]
  exact nvRecFE

/-- The exact values of this instance. -/
theorem chainValues : tstar params w' = 50 ∧ W_W params deltaF 1 = 49 ∧
    (50 : Time) + W_W params deltaF 1 = 99 ∧ kernelDeadlineW params deltaF (5 + 2) = 97 ∧
    (5 : Time) * P params = 60 ∧ horizon = 310 := by decide

/-- premises_sat (local finality premise): the regime with the recurrence, the same witness
w' that closes HealingInput, start 50 ≤ t = 50, and t + W_W = 99 ≤ horizon 310. -/
theorem localPrem_premises_sat :
    FinalityLivenessPrem_W params unitCodec gap deltaF .recFE 1 w' env run ⟨50⟩ :=
  ⟨nvFinalitySet, nvHealingInput, by rw [nvTstarValue], by rw [nvRunHorizon]; decide⟩

/-- premises_sat (kernel): every field of the FG-SA kernel premise for w' and round 5, from
which `d7c_kernel` produces every argument of the generic kernel. -/
theorem kernelPrem_premises_sat :
    KernelPrem_W params unitCodec gap deltaF env run ⟨w', 5⟩ where
  set := nvRecovery.toRecovery₂
  bound := livenessBound
  window := nvGood 5 (by decide)
  start := by rw [nvTstarValue]; decide
  hhor := by rw [chainValues.2.2.2.1, nvRunHorizon]; decide
  input := nvHealingInput
  services := fgsa_coreServices env run nvRecovery.base w'
    (finality_vote_receipts nvRecovery.toRecovery₂)

/-- POSITIVE 1: the generic kernel `FGCompose.finality_kernel_W_of` on this run, with every
generic argument produced by the private adapters (no assumed premise). -/
theorem kernelGeneric :
    FGCompose.KernelConclusion_W (fgsaCoreReads params unitCodec) env run
      (d7n_observations params unitCodec) (d7n_timing params)
      (fgsaInterface params unitCodec) (d7n_decodeProposal params) NamedProposal.erase
      NamedProposal.rows
      (fun (nd : Node params) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock deltaF 5 :=
  d7c_kernelOfRecovery params unitCodec env run gap deltaF nvClock ⟨w', 5⟩
    kernelPrem_premises_sat

/-- premises_sat (generic joined premise): one service point (the image of w'), the window,
the start, the deadline inside the horizon and the independent FG quorum. -/
theorem joined_premises_sat :
    FGCompose.KernelJoinedPrem (d7n_timing params) deltaF run.horizon 5
      (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec)) params.E.q
      (params.E.weightOf
        (Finset.univ \ FGCompose.historyFaulty (d7n_safety params unitCodec) run))
      params.cfg.timeoutDelay params.K_W (· = d7n_point params w') :=
  let hK := d7n_kernel params unitCodec env run kernelPrem_premises_sat nvClock
  { bound := hK.bound, window := hK.window, start := ⟨_, rfl, hK.start⟩, hhor := hK.hhor
    honest_quorum := hK.honest_quorum, timeout_eq := hK.timeout_eq
    capacity_ge := hK.capacity_ge }

/-- POSITIVE 2: the generic join `FGCompose.finality_kernel_joined_W_of`; its kernel supplier
is the generic kernel at the one service point of the joined premise. -/
theorem joinedGeneric :
    FGCompose.KernelConclusion_W (fgsaCoreReads params unitCodec) env run
      (d7n_observations params unitCodec) (d7n_timing params)
      (fgsaInterface params unitCodec) (d7n_decodeProposal params) NamedProposal.erase
      NamedProposal.rows
      (fun (nd : Node params) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock deltaF 5 :=
  FGCompose.finality_kernel_joined_W_of (fgsaCoreReads params unitCodec)
    (d7n_observations params unitCodec) (d7n_timing params) env run
    (fgsaInterface params unitCodec) (d7n_decodeProposal params) NamedProposal.erase
    NamedProposal.rows (fun (nd : Node params) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
    FGSA.fgBlock
    (fun sp hsp hKg => by
      subst hsp
      exact d7c_kernelOfRecovery params unitCodec env run gap deltaF nvClock ⟨w', 5⟩
        { set := nvRecovery.toRecovery₂, bound := livenessBound, window := hKg.window
          start := hKg.start, hhor := hKg.hhor, input := nvHealingInput
          services := fgsa_coreServices env run nvRecovery.base w'
            (finality_vote_receipts nvRecovery.toRecovery₂) })
    joined_premises_sat

/-- POSITIVE 3: the generic forward witness `FGCompose.forward_witness_FE_of` at t = 50. -/
theorem forwardGeneric :
    FGCompose.ForwardWitness_W (fgsaCoreReads params unitCodec) env run
      (d7n_observations params unitCodec) (d7n_timing params)
      (fgsaInterface params unitCodec) (d7n_decodeProposal params) NamedProposal.erase
      NamedProposal.rows
      (fun (nd : Node params) (Q : Block) => FGSA.fgBlockOf nd.st Q.parent)
      FGSA.fgBlock (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec)) deltaF 1
      (d7n_point params w') 50 :=
  d7c_forwardOfRecovery params unitCodec env run gap deltaF 1 w' nvClock ⟨50⟩
    localPrem_premises_sat

/-- POSITIVE 4: the generic local liveness `FGCompose.finality_liveness_of_forward_W` on the
generic forward witness, with the actual stable record as the AC output. -/
theorem livenessGeneric :
    FGCompose.FinalityLivenessConcl_W (fgsaCoreReads params unitCodec) env run
      (d7n_observations params unitCodec)
      (fun nd : Node params => nd.st.base.stableRecord) 50
      (50 + FGCompose.W_W (d7n_timing params) deltaF 1) :=
  d7c_livenessOfRecovery params unitCodec env run gap deltaF 1 w' nvClock ⟨50⟩
    localPrem_premises_sat

/-- The forward witness inspected: the selected round is exactly q = r = 5, the opening is an
actual honest proposal at slot 15 with its carrier above the reset frontier, U is a strict
fresh extension one certificate height above it, and every honest node accepts U strictly
before the kernel deadline 97 < 99 ≤ 310. -/
theorem forwardInspected : ∃ (A : Block) (Afg U : FGBlock (Fin params.n)) (d : Nat),
    HonestProposal env run (fgsaInterface params unitCodec) 15 A ∧ eraseFG Afg = A ∧
    (heightView params Afg).h = d ∧ w'.M + 1 ≤ d ∧
    FGBlock.Preceq Afg U ∧ Afg ≠ U ∧ (heightView params U).h = d + 1 ∧
    (∀ x ∈ run.honest, AcceptsFinalBefore params unitCodec env run x U 97) ∧
    (97 : Time) < 99 ∧ (99 : Time) ≤ run.horizon := by
  obtain ⟨q, r, A, Afg, U, d, D, htq, hqt, hr, _, _, hA, heA, _, hd, hM, hAU, hne, hU, hD,
    _, _, hacc⟩ := forwardGeneric
  have hq : q = 5 := by
    change (50 : Time) ≤ (q : Time) * 12 at htq
    change (q : Time) * 12 < 50 + 12 at hqt
    dsimp only [Time] at htq hqt
    omega
  have hr5 : r = 5 := by
    rw [InWindow_def] at hr
    omega
  subst hq hr5
  have hD97 : D = 97 := hD.trans chainValues.2.2.2.1
  subst hD97
  refine ⟨A, Afg, U, d, hA, ?_, hd, hM, hAU, hne, hU, ?_, by decide, by
    rw [nvRunHorizon]; decide⟩
  · rw [← d7n_erase]
    exact heA
  · intro x hx
    rw [← d7n_accepts_eq]
    exact hacc x hx

/-- The final witness inspected: one block strictly above the output that every honest node
read at t = 50, above every stored finality certificate, accepted by every honest node
strictly before the local deadline 99, which is inside the horizon 310. The honest set is
nonempty. -/
theorem livenessInspected : ∃ U : FGBlock (Fin params.n),
    (∀ x ∈ run.honest,
      Block.Prec (V2.D.Run.readAt env run 50 x).st.base.stableRecord (eraseFG U)) ∧
    (∀ x ∈ run.honest, AcceptsFinalBefore params unitCodec env run x U 99) ∧
    (99 : Time) ≤ run.horizon ∧ run.honest.Nonempty := by
  obtain ⟨U, hout, _, hacc⟩ := livenessGeneric
  refine ⟨U, ?_, ?_, by rw [nvRunHorizon]; decide, ⟨0, Finset.mem_univ _⟩⟩
  · intro x hx
    rw [← d7n_erase]
    exact hout x hx
  · intro x hx
    rw [← d7n_accepts_eq]
    have h := hacc x hx
    have hW : (50 : Time) + FGCompose.W_W (d7n_timing params) deltaF 1 = 99 :=
      chainValues.2.2.1
    rwa [hW] at h

#print axioms kernelPrem_premises_sat
#print axioms localPrem_premises_sat
#print axioms joined_premises_sat
#print axioms kernelGeneric
#print axioms joinedGeneric
#print axioms forwardGeneric
#print axioms livenessGeneric
#print axioms forwardInspected
#print axioms livenessInspected

end AvailableChain.FGSA.Run.Tests.P0d7c
