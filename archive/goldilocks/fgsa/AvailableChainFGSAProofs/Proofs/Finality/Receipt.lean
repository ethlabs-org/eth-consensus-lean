module
public import AvailableChainFGSAProofs.Proofs.Shared.ReceiptFacts
public import AvailableChainFGSAProofs.Proofs.Finality.Carry -- shake: keep (Kernel re-export)
public import AvailableChainFGSAProofs.Proofs.Finality.RestoreReads
public import AvailableChainFGSARun.Proofs.ProposalHistory
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSARun.Proofs.WindowExclusion
public import AvailableChainFGSAClaims.Statements.FinalityApi
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGCompose.Proofs.Finality.Receipt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Window (CoveredW)
open Gen.V2.Duty (faulty)

private def d7a5r_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a5r_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a5r_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a5r_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a5r_w_Old := FGSA.Window.State
private abbrev d7a5r_w_New := SimplexFG.Window.State

private def d7a5r_w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a5r_w_toWindow {V : Type} (w : d7a5r_w_Old V) : d7a5r_w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a5r_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a5r_w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a5r_w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a5r_w_state_eq {V : Type} (w : d7a5r_w_Old V) :
    d7a5r_w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a5r_w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a5r_w_initial_eq {V : Type} :
    d7a5r_w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a5r_w_foldRow_eq (w : d7a5r_w_Old V) (a : Row V) :
    d7a5r_w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a5r_w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a5r_w_toEntry =
      (w.W.map d7a5r_w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a5r_w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a5r_w_state_eq] using
        congrArg (fun es => ({ d7a5r_w_toWindow w with W := es } : d7a5r_w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a5r_w_state_eq] <;> rw [bits] <;> simp_all [d7a5r_w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a5r_w_rows_eq (rs : List (Row V)) (w : d7a5r_w_Old V) :
    d7a5r_w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a5r_w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a5r_w_foldRow_eq]

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5r_w_greatest_eq (E : Electorate V) (w : d7a5r_w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a5r_w_toEntry =
      SimplexFG.Window.greatestReady E (d7a5r_w_toWindow w) := by
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
      (oldStep best e).map d7a5r_w_toEntry = newStep (best.map d7a5r_w_toEntry)
      (d7a5r_w_toEntry e) := by
    dsimp [oldStep, newStep, d7a5r_w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a5r_w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a5r_w_toEntry =
        (es.map d7a5r_w_toEntry).foldl newStep (best.map d7a5r_w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a5r_w_toWindow w) =
      (w.W.map d7a5r_w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5r_w_finalize_eq (E : Electorate V) (w : d7a5r_w_Old V) :
    d7a5r_w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a5r_w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a5r_w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a5r_w_state_eq, d7a5r_w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] in
private theorem d7a5r_w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a5r_w_Old V) :
    d7a5r_w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a5r_w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a5r_w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a5r_w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a5r_w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a5r_w_state_eq, d7a5r_w_entry_eq, List.map_drop]

private theorem d7a5r_w_transition_eq (p : Params) (K : Nat) (w : d7a5r_w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a5r_w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a5r_w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a5r_w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a5r_w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a5r_w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a5r_w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a5r_w_toWindow where
  initial := d7a5r_w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a5r_w_transition_eq p K

private theorem d7a5r_w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a5r_w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a5r_w_foldMap p K).fold_eq B

end

section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a5r_w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a5r_w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a5r_w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a5r_w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7a5r_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7a5r_timing_eq (p : Params) : d7a5r_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private theorem d7a5r_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7a5r_timing p) where
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

private def d7a5r_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d7a5r_observations_eq : d7a5r_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

private def d7a5r_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a5r_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a5r_wire : FGCompose.FGHistoryWireReads (fgsaSafetyReads p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a5r_signer p
  decode_height a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a5r_decode p ha]
    rfl
  decode_finality a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a5r_decode p ha]
    rfl
  decode_signer a u ha := by
    rw [fgsaSafetyReads_def] at ha
    rw [d7a5r_decode p ha]
    rfl

private theorem d7a5r_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (d7a5r_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by rw [fgsaSafetyReads_def]; rfl

private theorem d7a5r_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a5r_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a5r_reads_eq]; rfl

private theorem d7a5r_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a5r_reads_eq]
  rfl

omit [DecidableEq V] in
private theorem d7a5r_holder (i : Fin p.n) :
    FGCompose.safetyHolder (fgsaSafetyReads p c) rho i = rho.seatOf (.base .fg) i := by
  rw [FGCompose.safetyHolder_def, fgsaSafetyReads_def]
  rfl

private theorem d7a5r_faulty_eq : FGCompose.historyFaulty (fgsaSafetyReads p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [d7a5r_holder]
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private def d7a5r_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7a5r_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7a5r_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7a5r_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7a5r_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem d7a5r_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

private theorem d7a5r_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a5r_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7a5r_proposal_payload p o s N ((d7a5r_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7a5r_decodeProposal_iff p o s N).mpr
      (d7a5r_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7a5r_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a5r_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a5r_signer; simp
  | proposer s => delta d7a5r_signer; simp
  | seat label j => cases label <;> delta d7a5r_signer <;> simp

omit [DecidableEq V] in
private theorem d7a5r_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (fgsaSafetyReads p c) rho (d7a5r_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a5r_signer_iff, d7a5r_holder]

private theorem d7a5r_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private theorem d7a5r_w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a5r_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a5r_w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a5r_w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a5r_w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a5r_w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a5r_w_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7a5r_w_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7a5r_w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega


private theorem d7a5r_held (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a ↔ heldAtProposal p c E rho s a := by
  constructor
  · rintro ⟨nd, hn, ha⟩
    refine ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hn, rfl⟩, ?_⟩
    rw [d7a5r_reads_eq] at ha
    exact ha
  · rintro ⟨st, hs, ha⟩
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    rw [d7a5r_reads_eq]
    exact ha

private theorem d7a5r_selection (h : TRowsSelect p c E rho) :
    FGCompose.TRowsSelect (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (d7a5r_timing p)
      (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7a5r_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) := by
  intro s Q rows j x r a hc ha hv hh
  rcases h s Q rows j x r a ((d7a5r_carrier_eq p c E rho _ _ _).mp hc)
    ((d7a5r_row_eq p c E rho j r x a).mp ha)
    ((d7a5r_validParent_eq p c E rho _ _ _).mp hv)
    ((d7a5r_held p c E rho _ _).mp hh) with hm | hp
  · exact Or.inl hm
  · obtain ⟨st, hs, hm⟩ := hp
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact Or.inr ⟨nd, hn, hm⟩

private theorem d7a5r_occurrence (s : Slot) (Q : Block) (H : FGBlock (Fin p.n))
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

private theorem d7a5r_r6w (w : Window.State (Fin p.n)) (a : Row (Fin p.n)) :
    SimplexFG.Window.r6w (d7a5r_w_toWindow w) a = Window.r6w w a := by
  cases hp : a.height_pair <;> cases hf : a.finality_pair <;>
    simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
    SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
    SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
    SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
    d7a5r_w_state_eq, List.any_map, Function.comp_def, d7a5r_w_entry_eq, hp, hf]
  rfl

private theorem d7a5r_valid (hv : V2.D.ExecutionValid E rho) (X : FGBlock (Fin p.n))
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
  rw [← d7a5r_w_derive_eq, d7a5r_r6w]
  exact h.2

private theorem d7a5r_decode_wire (a : RowWire p.n) (i : Fin p.n)
    (h : d7a5r_signer p a = some i) : ∃ u, RowWire.toRow? a = some u := by
  have ha := (d7a5r_signer_iff p a i).mp h
  cases a with
  | mk auth payload =>
    dsimp only at ha
    subst auth
    exact ⟨payload.toRow i, rfl⟩

private def d7a5r_rowValid (w : SimplexFG.Window.State (Fin p.n))
    (a : RowWire p.n) : Bool :=
  a.toRow?.isSome && (a.toRow?.map (SimplexFG.Window.r6w w)).getD false

private theorem d7a5r_rowValid_eq (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    d7a5r_rowValid p (d7a5r_w_toWindow w) a = Window.rowValidW w a := by
  unfold d7a5r_rowValid
  rw [Window.rowValidW_def]
  cases hd : a.toRow? with
  | none => rfl
  | some row => simp only [Option.isSome_some, Option.map_some, Option.getD_some,
      Bool.true_and, d7a5r_r6w]

private theorem d7a5r_parentState (s : Slot) (B : FGBlock (Fin p.n)) :
    KitFG.Window.parentState p.E p.cfg p.K_W B s =
      d7a5r_w_toWindow (parentFoldState p s B) := by
  rw [KitFG.Window.parentState_def, ← d7a5r_w_derive_eq]
  rfl

private theorem d7a5r_validFor (s : Slot) (B : FGBlock (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW (parentFoldState p s B) a =
      (((fgsaSafetyReads p c).decode a).isSome &&
        (((fgsaSafetyReads p c).decode a).map
          (SimplexFG.Window.r6w (KitFG.Window.parentState p.E p.cfg p.K_W B s))).getD false) := by
  rw [d7a5r_parentState, ← d7a5r_rowValid_eq, fgsaSafetyReads_def]
  rfl

private def d7a5r_terminal_to [Fintype V] (ΔF : Time) (q y : Nat)
    (A U X : FGBlock (Fin p.n)) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    FGCompose.TerminalCarriagePrem_W (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (d7a5r_observations p c) (d7a5r_timing p) E rho (fgsaInterface p c)
      (d7a5r_wire p c) p.E p.cfg p.K_W RowWire.valid
      (FGCompose.kernelCarrier (d7a5r_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st) ΔF q y A U X where
  schedule := h.base.valid.toScheduleWellFormed
  fault_weight := by
    rw [d7a5r_faulty_eq]
    exact kmid_faulty_weight p c E rho h.base h.faultQ
  deltaF := h.deltaF
  carrier := by
    simpa only [d7a5r_carrier_eq, d7a5r_reads_eq, fgsaSafetyReads_def] using h.carrier
  parent := by
    obtain ⟨st, hs, hp⟩ := h.parent
    obtain ⟨nd, hn, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨nd, hn, ?_⟩
    simpa only [d7a5r_reads_eq] using hp
  path := h.path
  freshHeight := h.freshHeight
  retainedOrCovered := by
    simpa only [d7a5r_w_retained_eq, d7a5r_w_covered_eq] using h.retainedOrCovered
  horizon := h.horizon
  seats := h.seats
  rows := h.rows
  fresh := by
    obtain ⟨hh, hq, hs⟩ := (FreshFinalityRows_W_def p c E rho q y U h.seats h.rows).mp h.fresh
    refine ⟨?_, hq, ?_⟩
    · intro i hi
      rw [d7a5r_holder]
      exact (kmid_honestSeats_mem p c rho i).mp (hh hi)
    · intro i hi
      rw [d7a5r_holder]
      obtain ⟨j, C, ha, hc, hsign, hheight, hn, hsrc, hCh, hearlier⟩ := hs i hi
      refine ⟨j, C, (d7a5r_row_eq p c E rho j q _ _).mpr ha,
        (d7a5r_complete_eq p c rho _ _).mpr hc, (d7a5r_signer_iff p _ i).mpr hsign,
        hheight, hn, ?_, hCh, ?_⟩
      · rw [d7a5r_source_eq]
        exact hsrc
      · intro j' r a height hr ha hh
        exact hearlier j' r a height hr ((d7a5r_row_eq p c E rho _ _ _ _).mp ha) hh
  heightEntry := h.heightEntry
  receipt := by
    intro i hi
    refine ⟨?_, (d7a5r_held p c E rho _ _).mpr (h.receipt i hi).2⟩
    have hr := (h.receipt i hi).1
    revert hr
    delta HeldBefore rowHeld FGCompose.HeldBefore FGCompose.rowHeld
    intro hr
    simpa only [d7a5r_reads_eq, d7a5r_timing_eq] using hr

end

private theorem d7a5r_parent_height (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).h = (heightView p P).h := by
  exact (Window.parentState_height_entry p p.K_W P s).1

private theorem d7a5r_parent_entry (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).T_h = (heightView p P).T_h := by
  exact (Window.parentState_height_entry p p.K_W P s).2


section
variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a5r_core_fg (nd : (fgsa p c).State) :
    ((fgsaCoreReads p c).core nd).fg = nd.st.fg := by
  rw [d7a5r_reads_eq]

private theorem d7a5r_inv (i : Nat) (x : V) :
    KitFG.FGStoreInvariant (d7a5r_observations p c).height (d7a5r_observations p c).finality
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  rw [d7a5r_core_fg]
  exact (cstoreInv_stateBefore E rho i x).fg

private theorem d7a5r_obs_finality :
    (d7a5r_observations p c).finality = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  rw [d7a5r_observations_eq]
  exact d7a5r_w_finality_eq p

private def d7a5r_point (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7a5r_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) : FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c)
      (d7a5r_observations p c) (d7a5r_timing p) E rho (fgsaInterface p c)
      (d7a5r_point p w) horizon := by
  intro x r C hx hsrc hhigh _ s Q hQ _ hgap
  change FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7a5r_timing p) x r =
    some (some C) at hsrc
  rw [d7a5r_source_eq, d7a5r_reads_eq] at *
  exact h x r C s Q hx hsrc hhigh hQ hgap

private theorem d7a5r_insert (i : Nat) (x : V) (X : FGBlock (Fin p.n)) :
    (FGCompose.receiptInsert_W (fgsaCoreReads p c) E rho p.E p.cfg p.K_W i x X).h_max =
      max (storeAt p c E rho i x).fg.h_max (heightView p X).h := by
  change max ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg.h_max
    (SimplexFG.Window.derive p.E p.cfg p.K_W X).h = _
  rw [d7a5r_core_fg, ← d7a5r_w_derive_eq]
  rfl

end

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1286–1305: the kernel supplies the execution, fault bound and horizon.
DC: INTENTIONAL local W deadline, with separate row delay and no GST healing bound. -/
theorem receipt_kernel_fields (G ΔF : Time) (pt : KernelPt)
    (h : KernelPrem_W p c G ΔF E rho pt) :
    BaseSet p c E rho ∧ (faulty rho).card ≤ (p.n - 1) / 3 ∧
      kernelDeadlineW p ΔF (pt.r + 2) ≤ rho.horizon :=
  ⟨h.set.base, h.set.fault, h.hhor⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1286–1289: carriage gives a finalized descendant in both branches.
DC: INTENTIONAL greatest-ready W fold; prior coverage is a separate branch.
The fold proves only carrier finality. It does not prove receipt or guards. -/
theorem receipt_finalized_of_carriage (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin p.n))
    (hne : X ≠ .genesis) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    FGBlock.Preceq U (Window.derive p p.K_W X).F := by
  have r := FGCompose.receipt_finalized_of_carriage
    (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a5r_timing p) E rho (fgsaInterface p c)
    (d7a5r_wire p c) p.E p.cfg p.K_W
    (FGCompose.kernelCarrier (d7a5r_decodeProposal p) NamedProposal.erase NamedProposal.rows)
    (fun nd => FGSA.chainWireRows nd.st) (fun nd => FGSA.blockWireRows nd.st)
    (fun nd => FGSA.fgBlockOf nd.st) (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (d7a5r_selection p c E rho hsel) (d7a5r_w_nonempty p) p.kWLarge
    (by
      intro a i hs
      change d7a5r_signer p a = some i at hs
      rw [fgsaSafetyReads_def]
      exact d7a5r_decode_wire p a i hs)
    (by
      intro s Q H nd a u hn hp hm hd
      rw [fgsaSafetyReads_def] at hd
      exact d7a5r_occurrence p c E rho s Q H nd a u hn hp hm hd)
    (d7a5r_observations p c)
    (by simpa only [d7a5r_observations_eq] using (fgCertificateLaws p).height)
    (d7a5r_w_height_eq p)
    (fun _ s B => ((parentFoldState p s B).h, (parentFoldState p s B).T_h.root))
    (by intro nd s B; rw [d7a5r_parent_height, d7a5r_parent_entry]; rfl)
    (fun _ s B a => d7a5r_validFor p c s B a) RowWire.valid ΔF q y A U X hne
    (d7a5r_terminal_to p c E rho ΔF q y A U X h)
    (d7a5r_valid p c E rho h.base.valid X h.parent)
  rw [← d7a5r_w_derive_eq] at r
  exact r

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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1145–1146, 1296: I3 compares F before carrier admission.
DC: INTENTIONAL W certificate agreement. Assembly supplies I3 from Foundations;
the honest emission supplies the carrier block before Ready exists. -/
theorem receipt_finCmp_of_block (base : BaseSet p c E rho)
    (faultBound : (faulty rho).card ≤ (p.n - 1) / 3)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (i : Nat) (x : V) (X U : FGBlock (Fin p.n))
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hblock : FinalityBlock p c E rho X) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F U ∨
      FGBlock.Preceq U (storeAt p c E rho i x).fg.F := by
  have r := FGCompose.receipt_finCmp_of_block (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
    (d7a5r_w_nonempty p) p.kWLarge (d7a5r_observations p c) (d7a5r_obs_finality p c)
    (FinalityBlock p c E rho)
    (fun C W hC hW => hI3 ⟨base, faultBound⟩ C W _ _ _ _ hC hW
      ((FinalityFinalizedAt_def p C _ _).mpr ⟨rfl, rfl⟩)
      ((FinalityFinalizedAt_def p W _ _).mpr ⟨rfl, rfl⟩))
    i x (d7a5r_inv p c E rho i x)
    (fun C hC hne => receipt_stored_block p c E rho i x C
      (by rw [d7a5r_core_fg] at hC; exact hC) hne)
    X U (by rw [← d7a5r_w_derive_eq]; exact hfinal) hblock
  rw [d7a5r_core_fg] at r
  exact r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1145–1146, 1296: I3 compares F at this same Ready event.
DC: INTENTIONAL W certificate agreement. Assembly supplies I3 from Foundations;
the Finality lane uses only its explicit safety-premise supplier. -/
theorem receipt_finCmp (base : BaseSet p c E rho)
    (faultBound : (faulty rho).card ≤ (p.n - 1) / 3)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (i : Nat) (x : V) (X U : FGBlock (Fin p.n)) (t : Time)
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hready : Ready_W p c E rho i x X t) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F U ∨
      FGBlock.Preceq U (storeAt p c E rho i x).fg.F := by
  have r := FGCompose.receipt_finCmp (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
    (d7a5r_w_nonempty p) p.kWLarge (d7a5r_observations p c) (d7a5r_obs_finality p c)
    (fun i x X t => Ready_W p c E rho i x X t) (FinalityBlock p c E rho)
    (fun C W hC hW => hI3 ⟨base, faultBound⟩ C W _ _ _ _ hC hW
      ((FinalityFinalizedAt_def p C _ _).mpr ⟨rfl, rfl⟩)
      ((FinalityFinalizedAt_def p W _ _).mpr ⟨rfl, rfl⟩))
    i x (d7a5r_inv p c E rho i x)
    (fun C hC hne => receipt_stored_block p c E rho i x C
      (by rw [d7a5r_core_fg] at hC; exact hC) hne)
    X U t (receipt_ready_block p c E rho i x X t)
    (by rw [← d7a5r_w_derive_eq]; exact hfinal) hready
  rw [d7a5r_core_fg] at r
  exact r

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1290–1302: the pre-next-action cap bounds the inserted h_max.
DC: INTENTIONAL W receipt insert, with height views and the shared causal cap.
The receiver and carrier use the same selected event index. -/
theorem receipt_cap (ΔF : Time) (q y i : Nat) (x : V) (X : FGBlock (Fin p.n))
    (t : Time) (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hv : V2.D.ExecutionValid E rho)
    (hheight : y + 1 ≤ (heightView p X).h)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    (receiptInsert_W p c E rho i x X).h_max ≤ (heightView p X).h + 1 := by
  have r := FGCompose.receipt_cap (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a5r_timing p) E
    rho p.E p.cfg p.K_W (d7a5r_observations p c) (d7a5r_w_height_eq p) (d7a5r_timing_laws p)
    hv.toScheduleWellFormed ΔF q y i x X t hx ⟨hbound.kappa_le_R⟩ ht hbefore
    (d7a5r_inv p c E rho i x) hheight
    (by
      intro cut b j z W hj hW hrow
      rw [d7a5r_held_eq] at hW
      exact hcapBefore cut b j z W hj hW (fun k u r a row h B timeout ha hd hp hlt =>
        hrow k u r a row h B timeout ((d7a5r_row_eq p c E rho k r u a).mpr ha)
          (by rw [fgsaSafetyReads_def]; exact hd) hp hlt))
    (by
      intro j z r a row h B timeout ha hd hp hlt
      exact hrows j z r a row h B timeout ((d7a5r_row_eq p c E rho j r z a).mp ha)
        (by rw [fgsaSafetyReads_def] at hd; exact hd) hp hlt)
  rw [d7a5r_insert, ← d7a5r_w_derive_eq] at r
  rw [receiptInsert_W_def]
  exact r

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1294–1296: the separate finality lag excludes a higher receiver certificate.
DC: INTENTIONAL W F carrier at the pre-handler read; Assembly supplies finality lag.
This height bound does not produce delivery or cached-J source provenance. -/
theorem receipt_receiver_finalityLag (ΔF : Time) (q y i : Nat) (x : V) (t : Time)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hv : V2.D.ExecutionValid E rho)
    (hfinalityLag : ∀ (r k j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      0 < k → j ≤ V2.D.Run.idxBefore rho (p.actionTime (r + 1)) →
      HeldAt p c E rho j z W →
      (∀ l u s a row T timeout, HonestRowAt p c E rho l u s a →
        RowWire.toRow? a = some row → row.height_pair = .vote k T timeout →
        ¬ p.actionTime s < p.actionTime r) → (finalityView p W).h_F < k)
    (hrowsEarlier : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1) :
    ∃ C, HeldAt p c E rho i x C ∧
      (finalityView p C).F = (storeAt p c E rho i x).fg.F ∧
      (finalityView p C).h_F < y + 1 := by
  obtain ⟨C, hC, hF, hlag⟩ := FGCompose.receipt_receiver_finalityLag (fgsaCoreReads p c)
    (fgsaSafetyReads p c) (d7a5r_timing p) E rho (d7a5r_observations p c)
    (d7a5r_timing_laws p) hv.toScheduleWellFormed ΔF q y i x t hx ⟨hbound.kappa_le_R⟩ ht
    hbefore (d7a5r_inv p c E rho i x)
    (by
      intro r k j z W hk hj hW hrow
      rw [d7a5r_held_eq] at hW
      exact hfinalityLag r k j z W hk hj hW (fun l u s a row B timeout ha hd hp =>
        hrow l u s a row B timeout ((d7a5r_row_eq p c E rho l s u a).mpr ha)
          (by rw [fgsaSafetyReads_def]; exact hd) hp))
    (by
      intro j z r a row h B timeout ha hd hp hlt
      exact hrowsEarlier j z r a row h B timeout ((d7a5r_row_eq p c E rho j r z a).mp ha)
        (by rw [fgsaSafetyReads_def] at hd; exact hd) hp hlt)
  rw [d7a5r_held_eq] at hC
  rw [d7a5r_core_fg] at hF
  exact ⟨C, hC, hF, hlag⟩

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1297–1302: the h_j = y case has its cached anchor on the carrier path.
DC: INTENTIONAL W cached-J guard. This does not produce source provenance;
Per-height justification uniqueness must prove the cached equality in this case. -/
theorem receipt_jPath_of_cached_anchor (i : Nat) (x : V) (X U : FGBlock (Fin p.n))
    (hcached : (storeAt p c E rho i x).fg.J = U) (hpath : FGBlock.Preceq U X.parent) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  have r := FGCompose.receipt_jPath_of_cached_anchor (fgsaCoreReads p c) E rho p.E p.cfg p.K_W
    i x X U (by rw [d7a5r_core_fg]; exact hcached) hpath
  rw [d7a5r_core_fg, ← d7a5r_w_derive_eq] at r
  exact r

private theorem receipt_proposal_checks (s : Slot) (N : NamedProposal p.n) :
    FGSA.wellFormed p ⟨.proposer s, .proposal N⟩ =
      (N.erase != .genesis && s == N.erase.slot && decide (N.erase.parent.slot < N.erase.slot) &&
        N.raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == N.erase.slot
          | none => false) &&
        N.support.all (fun v => decide (v ∈ N.raw)) && N.rows.all RowWire.valid &&
        contentOk p N.erase N.raw N.support N.rows) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1294–1296, 995–1002: a checked delivery admits the actual carrier.
DC: INTENTIONAL selected W handler; R6 checks every carried row against its parent. -/
theorem receipt_ready_of_delivery (G ΔF : Time) (hrec : Recovery₂ p c E rho G ΔF)
    (i : Nat) (x : V) (X : FGBlock (Fin p.n)) (t : Time)
    (o : Obj p) (N : NamedProposal p.n) (heN : N.erase = eraseFG X)
    (he : rho.events[i]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block X.slot N))
    (htrigger : Gen.V2.Duty.Trigger E rho o (SA.proposalTime p.toParams X.slot))
    (ht : SA.proposalTime p.toParams X.slot ≤ t)
    (hF : FGBlock.Preceq (storeAt p c E rho i x).fg.F X) :
    Ready_W p c E rho i x X t := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hD := hrec.base.valid.toDeliveryWellFormed
  have hwf := hD.wire i x o t he
  change FGSA.wellFormed p (toWire p o) = true at hwf
  have hw := decode_eq_block.mp hd
  have hwf' : FGSA.wellFormed p ⟨.proposer X.slot,
      .proposal N⟩ = true := hw ▸ hwf
  have hdeps := hD.deps i x o t he
  change depsS p (storeAt p c E rho i x) o = true at hdeps
  dsimp only [depsS] at hdeps
  rw [hd] at hdeps
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp hdeps).2
  have hPe := ((FGSA.parentFG_spec _ _ P).mp hP).2
  have hchecks := hwf'
  rw [receipt_proposal_checks, heN] at hchecks
  simp only [Bool.and_eq_true] at hchecks
  obtain ⟨⟨⟨⟨⟨⟨hb, _hs⟩, _hps⟩, _hraw⟩, _hsup⟩, _hrvalid⟩, hok⟩ := hchecks
  have hbne : eraseFG X ≠ .genesis := by simpa using hb
  have hparent : eraseFG X.parent = (eraseFG X).parent := by
    cases X with
    | genesis => rfl
    | node P s root body rs => rfl
  rw [heN] at hPe
  have hPX : P = X.parent := FGSA.eraseFG_injective (hPe.trans hparent.symm)
  subst P
  have hX : FGSA.fgBlock X.parent (eraseFG X) N.rows = X :=
    FGSA.eraseFG_injective (FGSA.eraseFG_fgBlock hbne hparent N.rows (contentOk_rowsOk hok))
  have hvalid := fgsa_trigger_rowsValid E rho o _ X.slot N
    htrigger hd (storeAt p c E rho i x) X.parent hP
  have hfresh := hD.fresh i x o t he
  change processedS p (storeAt p c E rho i x) o = false at hfresh
  dsimp only [processedS] at hfresh
  rw [hd] at hfresh
  have htime : 0 ≤ SA.proposalTime p.toParams X.slot := by
    change 0 ≤ 4 * p.Δ * (X.slot : Int)
    exact mul_nonneg (mul_nonneg (by decide) (le_of_lt p.deltaPos)) (Int.natCast_nonneg _)
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams X.slot) := by
    refine ⟨4 * X.slot, ?_⟩
    change 4 * p.Δ * (X.slot : Int) = _
    rw [hrec.base.delta]
    push_cast
    ring
  have htimely := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hrec.base.valid he hpub htime ht
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at htimely
  have hslot : (eraseFG X).slot ≤ (storeAt p c E rho i x).slot p := by
    change 4 * p.Δ * (X.slot : Int) ≤ (storeAt p c E rho i x).base.now at htimely
    rw [FGSA.eraseFG_slot]
    exact (fgsa_slot_threshold_iff p _ (htime.trans htimely) X.slot).mpr htimely
  have hacc : FGSA.blockAccepted p (storeAt p c E rho i x) X.slot
      N X.parent = true := by
    rw [FGSA.blockAccepted_of_wellFormed p _ _ N X.parent hwf', heN, hX]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨⟨⟨hslot, by simpa only [← heN, named_erase_root] using
      of_decide_eq_false hfresh⟩, hF⟩, by simpa only [heN] using hvalid⟩
  exact (Ready_W_def p c E rho i x X t).mpr ⟨o, X.slot, N, X.parent, he, heN, hd,
    (Bool.and_eq_true_iff.mp hdeps).1, by simpa only [heN] using hP, hacc,
    by simpa only [heN] using hX⟩

omit [Fintype V] in
private theorem receipt_proposer_honest (s : Slot) (B : Block)
    (h : HonestProposal E rho (fgsaInterface p c) s B) :
    V2.D.proposerOf rho (fgsaInterface p c) s ∈ rho.honest := by
  exact ((Gen.V2.Duty.HonestSlot_def rho (fgsaInterface p c) s).mp h.1).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1294–1296: I3 and C1 give a selected covered-or-admitted event.
DC: INTENTIONAL W delivery with strict broadcast time and dependency admission.
The fold supplies only hfinal; it does not supply delivery or guards. -/
theorem receipt_delivery (G ΔF : Time) (hrec : Recovery₂ p c E rho G ΔF)
    (X U : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hcarrier : HonestCarrier p c E rho X.slot (eraseFG X) rows)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot)
    (hhor : SA.proposalTime p.toParams X.slot + p.Δ ≤ rho.horizon)
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true) :
    Nonempty (BlockDelivery_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (SA.proposalTime p.toParams X.slot + p.Δ)) := by
  classical
  obtain ⟨hproposal, o, N, hem, hpayload, heN, hNrows⟩ :=
    (HonestCarrier_def p c E rho _ _ rows).mp hcarrier
  change Obj p at o
  have hhon := receipt_proposer_honest p c E rho _ _ hproposal
  have hd : (toWire p o).decode = some (.block X.slot N) := by
    obtain ⟨j, hj, ho⟩ := hem
    change rho.events[j]? = some (.tick
      (V2.D.proposerOf rho (fgsaInterface p c) X.slot) (SA.proposalTime p.toParams X.slot)) at hj
    have hawake : E.awake (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
        (SA.proposalTime p.toParams X.slot) = true := by
      exact hrec.awake _ hhon _ hgst
        ((le_of_lt (lt_add_of_pos_right _ p.deltaPos)).trans hhor)
    have hwf := honest_emit_wellFormed E rho hrec.base.valid.toDeliveryWellFormed
      hrec.base.valid.toScheduleWellFormed j _ _ hj hhon hawake o ho
    change FGSA.wellFormed p (toWire p o) = true at hwf
    cases o with
    | mk auth payload =>
      dsimp only at hpayload
      subst payload
      cases auth with
      | none => cases hwf
      | seat label seat =>
        cases label with
        | base label => cases label <;> cases hwf
        | prop s =>
          change FGSA.wellFormed p ⟨.proposer s, .proposal N⟩ = true at hwf
          rw [receipt_proposal_checks, heN] at hwf
          simp only [Bool.and_eq_true] at hwf
          have hs := beq_iff_eq.mp hwf.1.1.1.1.1.2
          rw [FGSA.eraseFG_slot] at hs
          subst s
          rfl
  have htrigger : Gen.V2.Duty.Trigger E rho o (SA.proposalTime p.toParams X.slot) :=
    Or.inl ⟨_, hhon, hem⟩
  have hblock : FinalityBlock p c E rho X := by
    rw [FinalityBlock_def]
    exact ⟨o, N, hpayload, Or.inl ⟨_, _, hem⟩,
      by rw [heN]; exact Gen.Pure.block_preceq_refl _⟩
  let a := SA.proposalTime p.toParams X.slot
  let D := a + p.Δ
  have hdelay : max a E.t_GST + fgsaDelay E.Δ ΔF o = D := by
    rw [max_eq_left hgst]
    have heq : fgsaDelay E.Δ ΔF o = p.Δ := by
      rw [fgsaDelay_def, hpayload, hrec.base.delta]
    rw [heq]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hFD : FGBlock.Preceq (Window.derive p p.K_W X).F X := by
    rw [← receipt_finality]
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified X)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry X)
        ((fgCertificateLaws p).height.entry_preceq X))
  have hwitness : ∀ x ∈ rho.honest, ∃ i t,
      eventTime rho i = some t ∧ t < D ∧
      (FGBlock.Preceq U (storeAt p c E rho (i + 1) x).fg.F ∨
        (a ≤ t ∧ Ready_W p c E rho i x X t)) := by
    intro x hx
    have hread := Gen.V2.Duty.stateBefore_idxBefore E rho D hS
    have hcmp := receipt_finCmp_of_block p c E rho hrec.base hrec.fault hI3
      (V2.D.Run.idxBefore rho D) x X U hfinal hblock
    by_cases hcovered : FGBlock.Preceq U
        (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.F
    · have hapos : 0 ≤ a := by
        change 0 ≤ 4 * p.Δ * (X.slot : Int)
        exact mul_nonneg (mul_nonneg (by decide) (le_of_lt p.deltaPos)) (Int.natCast_nonneg _)
      have hpub : V2.PublicTime E a := by
        refine ⟨4 * X.slot, ?_⟩
        change 4 * p.Δ * (X.slot : Int) = _
        rw [hrec.base.delta]
        push_cast
        ring
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hS.tick_total x hx a hpub hapos
          ((le_of_lt (lt_add_of_pos_right a p.deltaPos)).trans hhor)
          (hrec.awake x hx a hgst
            ((le_of_lt (lt_add_of_pos_right a p.deltaPos)).trans hhor)))
      have hjD := (Gen.V2.Duty.index_lt_idxBefore_iff hS hj D).mpr
        (by change a < a + p.Δ; exact lt_add_of_pos_right _ p.deltaPos)
      have hlen : V2.D.Run.idxBefore rho D ≤ rho.events.length := by
        rw [V2.D.Run.idxBefore_def]
        exact List.length_filter_le ..
      have hn : 0 < V2.D.Run.idxBefore rho D := by omega
      let i := V2.D.Run.idxBefore rho D - 1
      have hil : i < rho.events.length := by dsimp only [i]; omega
      have he := List.getElem?_eq_getElem hil
      refine ⟨i, rho.events[i].time, ?_, ?_, Or.inl ?_⟩
      · rw [eventTime_def, he]
        rfl
      · exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp (by dsimp only [i]; omega)
      · have hi : i + 1 = V2.D.Run.idxBefore rho D := by dsimp only [i]; omega
        rwa [hi]
    · have hFU := hcmp.resolve_right hcovered
      have hFX : FGBlock.Preceq (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.F X :=
        KitFG.preceq_trans hFU (KitFG.preceq_trans hfinal hFD)
      have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho D x) o = false := by
        change excludesS p (V2.D.Run.stateBeforeTime E rho D x).st o = false
        have hc : Block.compatible (eraseFG X)
            (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) = true := by
          rw [← hread]
          exact Bool.or_eq_true_iff.mpr (Or.inr (FGSA.eraseFG_preceq hFX))
        dsimp only [excludesS]
        rw [hd]
        simp only [blockExcluded, activeCompatible, heN, hc, Bool.not_true, Bool.false_or]
        exact fgsa_trigger_invalid_false E rho o a X.slot N
          htrigger hd _
      have ha : 0 ≤ a := by
        change 0 ≤ 4 * p.Δ * (X.slot : Int)
        exact mul_nonneg (mul_nonneg (by decide) p.deltaPos.le) (Int.natCast_nonneg _)
      have hservice := hrec.sync.broadcast_emitted _ hhon o a hem x hx a le_rfl ha
        (by dsimp only; rw [hdelay]; exact lt_add_of_pos_right a p.deltaPos)
        (by dsimp only; rw [hdelay]; exact hhor)
        (by dsimp only; rw [hdelay]; exact hhor)
        (fun u hau hud => hrec.awake x hx u (hgst.trans hau)
          (hud.le.trans (by dsimp only; rw [hdelay]; exact hhor)))
        (by dsimp only; rw [hdelay]; exact hNX)
      have hhandled : V2.D.HandledBetween E rho x o a D := by
        rcases hservice with hpast | hh
        · have ho : o = ofWire p ⟨.proposer X.slot, .proposal N⟩ := by
            apply toWire_injective
            rw [toWire_ofWire]
            exact decode_eq_block.mp hd
          have hscope := emitted_proposal_history_in_scope E rho hrec.base.receiptIdealization
            hhon hx X.slot N (ho ▸ hem) (ho ▸ hpast)
          obtain ⟨j, hj, hemit⟩ := hem
          obtain ⟨k, hk, hp⟩ := hpast
          have hcut : V2.D.Run.actionCut rho a ≤ j := by
            by_contra hn
            have h := (V2.D.Engine.index_lt_actionCut_iff hS hj a).mp
              (Nat.lt_of_not_ge hn)
            simp [V2.Event.time, V2.Event.phase] at h
            change a < a at h
            exact (lt_irrefl a) h
          have hf := fgsa_emitted_proposal_no_prior_processed E rho hrec.base.valid
            hrec.base.idealization hj X.slot N (ho ▸ hemit) hscope k (hk.trans hcut) x
          rw [← ho, hp] at hf
          cases hf
        · simpa only [hdelay] using hh
      obtain ⟨t, hat, htD, i, envelope, he, hh⟩ := hhandled
      have hdirect : envelope = o := by
        rcases hh with h | h
        · exact h
        · cases hd' : (toWire p envelope).decode with
          | none => simp only [hd'] at h
          | some m =>
            cases m with
            | vote => simp only [hd'] at h
            | row => simp only [hd'] at h
            | block s M =>
              rw [hd'] at h
              rcases h.2 with h | h
              · obtain ⟨wire, _, hw⟩ := List.mem_map.mp h
                have hdw := congrArg Wire.decode (congrArg (toWire p) hw)
                rw [toWire_ofHead, hd] at hdw
                cases wire with
                | mk auth body =>
                  rcases auth with (⟨(_ | _), _⟩ | _ | _) <;> simp [Wire.decode] at hdw
              · obtain ⟨wire, _, hw⟩ := List.mem_map.mp h
                have hdw := congrArg Wire.decode (congrArg (toWire p) hw)
                rw [toWire_ofRow, hd] at hdw
                cases wire with
                | mk auth body =>
                  rcases auth with (⟨(_ | _), _⟩ | _ | _) <;> simp [Wire.decode] at hdw
      subst envelope
      have htD' : t < D := htD
      have hiD := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mpr htD'
      have hmono := fgsa_monoAlong_preceq_F p c (storeAt p c E rho i x).fg.F
      rw [Gen.V2.Duty.MonoAlong_def] at hmono
      have hFF := V2.D.Engine.stateBefore_stable_restore _ hmono.1 hmono.2.1
        hmono.2.2 E rho (Nat.le_of_lt hiD) x
        (finality_restore_preceq_F p c (storeAt p c E rho i x).fg.F)
        (KitFG.preceq_refl _)
      have hFiX := KitFG.preceq_trans hFF hFX
      refine ⟨i, t, ?_, htD', Or.inr ⟨hat, ?_⟩⟩
      · rw [eventTime_def, he]
        rfl
      · exact receipt_ready_of_delivery p c E rho G ΔF hrec i x X t o N heN
          he hd htrigger hat hFiX
  choose index time witness using hwitness
  exact ⟨{ selected := fun x hx => ⟨index x hx, time x hx⟩, witness := witness }⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1297–1302: a high cached J is on the terminal carrier path.
DC: INTENTIONAL W cached pair and action-source ancestry. Stratification and
emitted-name provenance are explicit Foundations inputs; H2 supplies the path. -/
theorem receipt_jPath (hroots : NamedRootCollisionFree p c E rho) (ΔF : Time) (q y i : Nat) (x :
    V) (A U X : FGBlock (Fin p.n))
    (t : Time) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X)
    (w : HealingWitness) (hinput : HealingInput p c E rho w ΔF)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hanchor : (heightView p A).h_j = y) (hfloor : w.M + 1 ≤ y)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  have hproposal := ((HonestCarrier_def p c E rho _ _ rows).mp hcarrier).1
  have hM : 1 ≤ w.M := by
    have hmu := hinput.wit.mu_le
    rw [muOf_def] at hmu
    exact (le_max_left 1 _).trans hmu
  have r := FGCompose.receipt_jPath (fgsaCoreReads p c) (fgsaSafetyReads p c) (d7a5r_timing p)
    E rho (fgsaInterface p c) p.E p.cfg p.K_W (d7a5r_observations p c)
    (d7a5r_w_height_eq p) (d7a5r_w_nonempty p) p.kWLarge (d7a5r_timing_laws p)
    h.base.valid.toScheduleWellFormed (fun a => FGCompose.namedEntry a.payload.height_pair)
    (by
      intro A B hAB
      rw [d7a5r_reads_eq] at hAB
      exact eraseFG_preceq_iff.mp hAB)
    (by
      intro B
      rw [d7a5r_reads_eq]
      exact (FGSA.eraseFG_parent B).symm)
    ΔF q y i x A X t h.deltaF h.path
    (by rw [d7a5r_reads_eq]; exact hproposal) h.horizon.2 (d7a5r_point p w) hM
    (d7a5r_transfer p c E rho w hinput.t.h2 rho.horizon) hx ⟨hbound.kappa_le_R⟩ ht hbefore
    hslot hanchor hfloor (d7a5r_inv p c E rho i x)
    (by
      intro j z W hz hW J hJ hne
      rw [d7a5r_core_fg] at hW
      obtain ⟨u, r, a, hrow, hn⟩ := hStrat j z W hz hW J (by
        rw [certified_def]
        exact hJ) hne
      obtain ⟨k, hk, hrow⟩ := (HonestRowBefore_def p c E rho j u r a).mp hrow
      refine ⟨u, r, a, ⟨k, hk, (d7a5r_row_eq p c E rho k r u a).mpr hrow⟩, ?_⟩
      have he : FGCompose.namedEntry a.payload.height_pair = namedEntry a.payload.height_pair := by
        cases a.payload.height_pair <;> rfl
      rw [he]
      exact hn)
    (by
      intro j z r a e hrow he
      obtain ⟨C, hsrc, hC, hT⟩ := hEmittedSource j z r a e
        ((d7a5r_row_eq p c E rho j r z a).mp hrow)
        (by rw [← he]; cases a.payload.height_pair <;> rfl)
      exact ⟨C, by rw [d7a5r_source_eq]; exact hsrc, hC, hT⟩)
    (by
      intro C k u r a B hC hrow hsrc hroot
      rw [d7a5r_core_fg] at hC
      rw [d7a5r_source_eq] at hsrc
      exact rootScope_eq hroots (rootScope_justified (rootScope_store hx hC))
        (rootScope_entry (rootScope_source ((d7a5r_row_eq p c E rho k r u a).mp hrow).1 hsrc))
        hroot)
  rw [d7a5r_core_fg, ← d7a5r_w_derive_eq] at r
  exact r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1286–1305: the terminal carrier gives every AcceptPrem_W field.
DC: INTENTIONAL local W receipt and same-event guards. The final action is
q = pt.r + 2; Assembly supplies the stated Foundations and K-MID inputs. -/
theorem receipt_acceptPrem_W (G ΔF : Time) (pt : KernelPt)
    (hkernel : KernelPrem_W p c G ΔF E rho pt) (y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF (pt.r + 2) y A U X)
    (hslot : X.slot = (pt.r + 2) * p.R + kappaF p ΔF)
    (hne : X ≠ .genesis) (hsel : TRowsSelect p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hanchor : (heightView p A).h_j = y) (hfloor : pt.w.M + 1 ≤ y)
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
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (pt.r + 2 + 1) → h ≤ y + 1) :
    Nonempty (AcceptPrem_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF (pt.r + 2))) := by
  have hdeadline : SA.proposalTime p.toParams X.slot + p.Δ =
      kernelDeadlineW p ΔF (pt.r + 2) := by
    rw [hslot, ← fgsa_grid_sa_proposalTime, fgsa_grid_carrier_timeW,
      carrierTimeW_def, kernelDeadlineW_def]
  have hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot := by
    have hFpos := E.Δ_pos.trans_le h.deltaF
    have hmax := le_max_right (p.actionTime (pt.r + 2)) E.t_GST
    have hhor := h.horizon.1
    simp only [Time] at hmax hhor hFpos ⊢
    omega
  have hfinal := receipt_finalized_of_carriage p c E rho hsel ΔF (pt.r + 2) y A U X hne h
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  obtain ⟨delivery⟩ := receipt_delivery p c E rho G ΔF hkernel.set X U rows hcarrier hgst
    (hdeadline ▸ hkernel.hhor) hfinal hI3
  rw [hdeadline] at delivery
  have hheight : y + 1 ≤ (heightView p X).h := by
    rw [← h.freshHeight]
    exact (fgCertificateLaws p).height.h_mono
      (KitFG.preceq_trans h.path (receipt_parent_path p X))
  refine ⟨{ base := hkernel.set.base
            faultBound := hkernel.set.fault
            finalized := hfinal
            deliver := delivery
            horizon := hkernel.hhor
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ } }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp p c E rho hkernel.set.base hkernel.set.fault hI3
      (delivery.selected x hx).index x X U (delivery.selected x hx).time hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_jPath (hroots := hkernel.set.base.idealization) p c E rho ΔF (pt.r + 2) y
      (delivery.selected x hx).index x A U X
      (delivery.selected x hx).time h pt.w hkernel.input hx hkernel.bound hw.1 hw.2.1
      hslot hanchor hfloor hStrat hEmittedSource
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap p c E rho ΔF (pt.r + 2) y (delivery.selected x hx).index x X
      (delivery.selected x hx).time hx hkernel.bound hw.1 hw.2.1 hkernel.set.base.valid
      hheight hcapBefore hrows

end AvailableChain.FGSA.Run
end
