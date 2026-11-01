module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Proofs.Finality.Rows
public import AvailableChainKitFG.WindowTransport -- shake: keep (RowsPrem fold_eq route)
public import AvailableChainKitFG.ClientOnceSafety -- shake: keep (RowsPrem release route)
public import AvailableChainFGCompose.Proofs.ServiceTransport
public import AvailableChainFGSAProofs.Proofs.Shared.Gate
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSA.Proofs.EmissionFields
public import AvailableChainKitFG.HeightHistoryTransfer -- shake: keep (height history route)
public import AvailableChainFGSA.Proofs.WindowRetention -- shake: keep (Receipt window route)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

private def d7a4r_proposalFG (p : Params) {In : Type} (c : AppCodec In) :=
  (fgsaCoreReads p c).proposalFG

private theorem d7a4r_reads_eq (p : Params) {In : Type} (c : AppCodec In) :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a4r_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a4r_proposalFG p c })
    (fgsaCoreReads_def p c)

section

private abbrev d7a4w_Old := FGSA.Window.State
private abbrev d7a4w_New := SimplexFG.Window.State

private def d7a4w_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7a4w_toWindow {V : Type} (w : d7a4w_Old V) : d7a4w_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7a4w_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7a4w_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7a4w_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7a4w_state_eq {V : Type} (w : d7a4w_Old V) :
    d7a4w_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7a4w_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7a4w_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7a4w_toEntry e).j = e.j ∧ (d7a4w_toEntry e).X = e.X ∧ (d7a4w_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7a4w_state_fields {V : Type} (w : d7a4w_Old V) :
    (d7a4w_toWindow w).L = w.L ∧ (d7a4w_toWindow w).s = w.s ∧
    (d7a4w_toWindow w).h = w.h ∧ (d7a4w_toWindow w).T_h = w.T_h ∧
    (d7a4w_toWindow w).target_participation = w.target_participation ∧
    (d7a4w_toWindow w).progress = w.progress ∧ (d7a4w_toWindow w).W = w.W.map
      d7a4w_toEntry ∧
    (d7a4w_toWindow w).J = w.J ∧ (d7a4w_toWindow w).h_j = w.h_j ∧
    (d7a4w_toWindow w).F = w.F ∧ (d7a4w_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7a4w_initial_eq {V : Type} :
    d7a4w_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7a4w_foldRow_eq (w : d7a4w_Old V) (a : Row V) :
    d7a4w_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7a4w_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7a4w_toEntry =
      (w.W.map d7a4w_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7a4w_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7a4w_state_eq] using
        congrArg (fun es => ({ d7a4w_toWindow w with W := es } : d7a4w_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7a4w_state_eq] <;> rw [bits] <;> simp_all [d7a4w_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7a4w_rows_eq (rs : List (Row V)) (w : d7a4w_Old V) :
    d7a4w_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7a4w_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7a4w_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4w_advance_eq (w : d7a4w_Old V) :
    d7a4w_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7a4w_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4w_greatest_eq (E : Electorate V) (w : d7a4w_Old V) :
    (FGSA.Window.greatestReady E w).map d7a4w_toEntry =
      SimplexFG.Window.greatestReady E (d7a4w_toWindow w) := by
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
      (oldStep best e).map d7a4w_toEntry = newStep (best.map d7a4w_toEntry)
      (d7a4w_toEntry e) := by
    dsimp [oldStep, newStep, d7a4w_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7a4w_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7a4w_toEntry =
        (es.map d7a4w_toEntry).foldl newStep (best.map d7a4w_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7a4w_toWindow w) =
      (w.W.map d7a4w_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4w_finalize_eq (E : Electorate V) (w : d7a4w_Old V) :
    d7a4w_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7a4w_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7a4w_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7a4w_state_eq, d7a4w_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7a4w_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7a4w_toEntry =
      (es.map d7a4w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7a4w_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7a4w_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7a4w_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7a4w_Old V) :
    d7a4w_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7a4w_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7a4w_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7a4w_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7a4w_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7a4w_state_eq, d7a4w_entry_eq, List.map_drop]

private theorem d7a4w_transition_eq (p : Params) (K : Nat) (w : d7a4w_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7a4w_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7a4w_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7a4w_events_eq, SimplexFG.Window.transition_def]
  have h := d7a4w_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7a4w_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7a4w_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7a4w_toWindow where
  initial := d7a4w_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7a4w_transition_eq p K

private theorem d7a4w_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7a4w_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7a4w_foldMap p K).fold_eq B

end

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7a4w_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7a4w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4w_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7a4w_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7a4w_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7a4w_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7a4w_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7a4w_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7a4w_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7a4w_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private theorem d7a4w_covered_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.CoveredW p.E p.cfg p.K_W B y U = Window.CoveredW p B y U := by
  unfold KitFG.Window.CoveredW
  rw [← d7a4w_derive_eq p p.K_W B, Window.CoveredW_def]
  rfl

private theorem d7a4w_nonempty : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega


private theorem rows_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'

private def c2_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem c2_timing_eq (p : Params) : c2_timing p =
    { delta := p.Δ
      roundSlots := p.R
      proposal := SA.proposalTime p.toParams
      vote := SA.voteTime p.toParams
      early := SA.earlyTime p.toParams
      freeze := SA.freezeTime p.toParams
      release := SA.releaseTime p.toParams
      gate := SA.gateTime p.toParams
      action := p.actionTime } := rfl

private def c2_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private def c2_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem c2_observations_eq : c2_observations p c =
    { height := heightView p
      finality := finalityView p
      controls := fun nd => FGSA.controls p nd.st
      viable := fun nd X => domainR p nd.st X } := rfl

private def c2_reads (w : HealingWitness) : FGCompose.FGACServiceReads V where
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

private def d7a4r_safety (p : Params) {In : Type} (c : AppCodec In) :
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

private def d7a4r_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7a4r_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7a4r_wire : FGCompose.FGHistoryWireReads (d7a4r_safety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7a4r_signer p
  decode_height a u ha := by
    delta d7a4r_safety at ha
    rw [d7a4r_decode p ha]
    rfl
  decode_finality a u ha := by
    delta d7a4r_safety at ha
    rw [d7a4r_decode p ha]
    rfl
  decode_signer a u ha := by
    delta d7a4r_safety at ha
    rw [d7a4r_decode p ha]
    rfl

private theorem d7a4r_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (d7a4r_safety p c) E rho (c2_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by delta d7a4r_safety; rfl

private theorem d7a4r_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (c2_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7a4r_reads_eq]; rfl

private theorem d7a4r_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7a4r_reads_eq]
  rfl

private theorem d7a4r_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7a4r_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7a4r_signer; simp
  | proposer s => delta d7a4r_signer; simp
  | seat label j => cases label <;> delta d7a4r_signer <;> simp

omit [DecidableEq V] in
private theorem d7a4r_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (d7a4r_safety p c) rho (d7a4r_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7a4r_signer_iff, FGCompose.safetyHolder_def]
  delta d7a4r_safety
  rfl

private def d7a4r_makeWire (row : Row (Fin p.n)) : RowWire p.n :=
  ⟨.seat .fg row.signer, .vote ⟨row.height_pair, row.finality_pair⟩⟩

private theorem d7a4r_release (i : Fin p.n) (q : Nat) (nd : Node p) (row : Row (Fin p.n))
    (hnd : FGCompose.postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd)
    (awake : E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true)
    (released : (createRowOnce p.E p.cfg nd.record i (fgInputs p nd.st).1
      (fgInputs p nd.st).2).1 = some row) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base .fg) i) (p.actionTime q)) ∧
      ofRow p (d7a4r_makeWire p row) ∈ V2.D.Run.emitsAt E rho j := by
  rw [← (fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1] at hnd
  obtain ⟨j, hj, hclock⟩ := rows_clock_read p c E rho _ _ nd hnd
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

private theorem c2_observation_laws (w : HealingWitness) :
    FGCompose.FGACServiceObservationLaws (c2_reads p c E rho w) (c2_timing p)
      (fgsaCoreReads p c) (c2_observations p c) E rho (fgsaInterface p c)
      (gateResult p c E rho)
      (fun x s => (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F))
      (proposalHeadAt p c E rho) (fun s _ => w.sStar + 2 ≤ s)
      (fun x r B => ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        eraseFG C = B ∧ high p w C)
      (fun x s => joinedAt p E rho x s (SA.voteTime p.toParams s))
      (fun x s => confirmedReaderAtIdx p c E rho x
        (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s))
      (fun x q => ∃ nd, postClock E rho x (p.actionTime q) = some nd) where
  honest_eq _ := Iff.rfl
  proposal_eq _ _ := Iff.rfl
  proposal_time _ := rfl
  duty_time _ := rfl
  vote_time _ := rfl
  gate_time _ := rfl
  action_time _ := rfl
  gate_label _ := rfl
  action_head_label _ := rfl
  head_eq _ _ := by rw [d7a4r_reads_eq]; rfl
  action_head_eq _ _ := by rw [d7a4r_reads_eq]; rfl
  source_eq x q := by
    rw [d7a4r_reads_eq]
    change ((postClock E rho x (p.actionTime q)).map
      (fun nd => FGSA.fgSource p nd.st)).map (Option.map eraseFG) = _
    rw [Option.map_map]
    rfl
  gate_eq _ _ := rfl
  parent_eq _ := rfl
  floor_eq _ _ := rfl
  below_eq _ _ := Iff.rfl
  proposal_scope _ _ := Iff.rfl
  source_scope _ _ _ := Iff.rfl
  head_scope _ _ := Iff.rfl
  gate_scope _ _ := Iff.rfl
  action_scope _ _ := Iff.rfl
  frame_eq _ _ _ := by
    dsimp only [c2_observations_eq, c2_reads]
    rw [d7a4r_reads_eq]
    rfl

private theorem c2_history_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c) (c2_observations p c)
      (c2_timing p) E rho (fgsaInterface p c) (c2_point p w) horizon := by
  intro x r C hx hC hh _ v Q hQ _ hgap
  rw [d7a4r_reads_eq] at hC ⊢
  exact h x r C v Q hx hC hh hQ hgap

private theorem c2_history_chain (w : HealingWitness) (h : THigh p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (c2_observations p c)
      (c2_timing p) E rho (c2_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [d7a4r_reads_eq] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem c2_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (c2_reads p c E rho w) (c2_point p w)
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
    obtain ⟨j, _, hclock⟩ := rows_clock_read p c E rho x (p.actionTime q) nd hnd
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
      simp only [actionSourceFG, hnd, Option.map_some, hsource]
    · change Block.Preceq Q (eraseFG C)
      rw [← hD]
      exact eraseFG_preceq hDC
  parent_transfer := by
    intro x r C s Q hx hc _ _ hQ _ hgap _
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact h2 x r C' s Q hx hs hh hQ hgap

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the full action walk covers D and keeps the pending fields.
DC: INTENTIONAL: height plateau and a separate finality-lag bound; no exact head body. -/
private theorem rows_pending_action_head
    (k : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U)
    (hDj : (heightView p D).h_j = y)
    (hcap : ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1)
    (hfin : ∀ B ∈ nd.st.fg.TF, (finalityView p B).h_F < y) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧
      (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧
      (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h := by
  obtain ⟨j, _hj, hclock⟩ := rows_clock_read p c E rho x (p.actionTime q) nd hnd
  have hinv : CStoreInv p nd.st := by
    rw [← hclock]
    exact (storeBundle_postClock E rho j x (p.actionTime q)).cstore
  have hcover := (hwalk k x (q * p.R + 1) raw support D seats m hx hcount
    (by simpa only [hread] using hD) (by simpa only [hread] using hcompat)
    (by simpa only [hread] using hbatch)).1
  rw [hread, ← hhead] at hcover
  obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
  have hdecode := (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩
  have result := FGCompose.pending_action_head_capped (fgsaCoreReads p c)
    (c2_observations p c) p.E p.cfg (fgCertificateLaws p).height (heightView_bridge p)
    y D U nd (by rw [d7a4r_reads_eq]; exact ⟨H, hdecode, hH⟩)
    (by
      intro B hB
      rw [d7a4r_reads_eq] at hB ⊢
      have heq := Option.some.inj (hdecode.symm.trans hB)
      subst B
      simpa only [hHe] using hcover)
    (by
      intro A B _ _ hp
      rw [d7a4r_reads_eq] at hp
      exact eraseFG_preceq_iff.mp hp)
    (by rw [d7a4r_reads_eq]; exact (Finset.filter_subset _ _) hD)
    hDh hDJ hDj (by simpa only [c2_observations_eq, d7a4r_reads_eq] using hcap)
    (by simpa only [c2_observations_eq, d7a4r_reads_eq] using hfin)
  simp only [c2_observations_eq, d7a4r_reads_eq] at result
  exact result

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the full action walk covers D; held caps bound its head fields.
DC: INTENTIONAL: public form of the capped walk step; the caller supplies both caps. -/
theorem pending_action_head_capped
    (k : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U)
    (hDj : (heightView p D).h_j = y)
    (hcap : ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1)
    (hfin : ∀ B ∈ nd.st.fg.TF, (finalityView p B).h_F < y) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧
      (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧
      (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h :=
  rows_pending_action_head p c E rho k x q y D U nd raw support seats m hx hnd hread hwalk
    hhead hcount hD hcompat hbatch hDh hDJ hDj hcap hfin

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1236–1239,1667–1687: translate the strict causal cap to a held domain.
DC: INTENTIONAL: height-only cap through a TF inclusion at the actual read. -/
theorem pending_action_domain_cap
    (before : Nat) (x : V) (q y : Nat) (nd : Node p)
    (hx : x ∈ rho.honest)
    (hfgread : nd.st.fg.TF ⊆ (storeAt p c E rho before x).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (p.actionTime q))
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hrows : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1) :
    ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1 := by
  have result := FGCompose.pending_action_domain_cap (fgsaCoreReads p c)
    (d7a4r_safety p c) (c2_observations p c) (c2_timing p) E rho before x q y nd hx
    (by rw [d7a4r_reads_eq]; exact hfgread) hbefore
    (by
      intro cut b i z W hi hW rows
      rw [d7a4r_held_eq] at hW
      apply hcapBefore cut b i z W hi hW
      intro j z r a u h B timeout ha hu hp ht
      exact rows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mpr ha) hu hp ht)
    (by
      intro j z r a u h B timeout ha hu hp ht
      exact hrows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mp ha) hu hp ht)
  simp only [c2_observations_eq, d7a4r_reads_eq] at result
  exact result

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the actual full action walk has the pending fields.
DC: INTENTIONAL: separate held-domain causal cap and finality lag, with read-index bridges. -/
theorem pending_action_head
    (k before : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hfgread : nd.st.fg.TF ⊆ (storeAt p c E rho before x).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (p.actionTime q))
    (hq : 0 < q)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U) (hDj : (heightView p D).h_j = y)
    (hDfin : (finalityView p D).h_F < y)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hfinalityLag : ∀ (r y i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      0 < y → i ≤ V2.D.Run.idxBefore rho (p.actionTime (r + 1)) →
      HeldAt p c E rho i x W →
      (∀ j z s a u T timeout, HonestRowAt p c E rho j z s a →
        RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
        ¬ p.actionTime s < p.actionTime r) → (finalityView p W).h_F < y)
    (hrows : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1)
    (hnoRow : ∀ j z r a u T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
      ¬ p.actionTime r < p.actionTime (q - 1)) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧ FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧ (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧ (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h := by
  obtain ⟨j, _hj, hclock⟩ := rows_clock_read p c E rho x (p.actionTime q) nd hnd
  have hinv : CStoreInv p nd.st := by
    rw [← hclock]
    exact (storeBundle_postClock E rho j x (p.actionTime q)).cstore
  have hcover := (hwalk k x (q * p.R + 1) raw support D seats m hx hcount
    (by simpa only [hread] using hD) (by simpa only [hread] using hcompat)
    (by simpa only [hread] using hbatch)).1
  rw [hread, ← hhead] at hcover
  obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
  have hdecode := (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩
  have result := FGCompose.pending_action_head (fgsaCoreReads p c)
    (d7a4r_safety p c) (c2_observations p c) (c2_timing p) E rho
    p.E p.cfg (fgCertificateLaws p).height (heightView_bridge p)
    before x q y D U nd hx (by rw [d7a4r_reads_eq]; exact hfgread) hbefore hq
    (by rw [d7a4r_reads_eq]; exact ⟨H, hdecode, hH⟩)
    (by
      intro B hB
      rw [d7a4r_reads_eq] at hB ⊢
      have heq := Option.some.inj (hdecode.symm.trans hB)
      subst B
      simpa only [hHe] using hcover)
    (by
      intro A B _ _ hp
      rw [d7a4r_reads_eq] at hp
      exact eraseFG_preceq_iff.mp hp)
    (by rw [d7a4r_reads_eq]; exact (Finset.filter_subset _ _) hD)
    hDh hDJ hDj hDfin
    (by
      intro cut b i z W hi hW rows
      rw [d7a4r_held_eq] at hW
      apply hcapBefore cut b i z W hi hW
      intro j z r a u h B timeout ha hu hp ht
      exact rows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mpr ha) hu hp ht)
    (by
      intro r y i z W hy hi hW rows
      rw [d7a4r_held_eq] at hW
      apply hfinalityLag r y i z W hy hi hW
      intro j z r a u B timeout ha hu hp ht
      exact rows j z r a u B timeout ((d7a4r_row_eq p c E rho j r z a).mpr ha) hu hp ht)
    (by
      intro j z r a u h B timeout ha hu hp ht
      exact hrows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mp ha) hu hp ht)
    (by
      intro j z r a u B timeout ha hu hp ht
      exact hnoRow j z r a u B timeout ((d7a4r_row_eq p c E rho j r z a).mp ha) hu hp ht)
  simp only [c2_observations_eq, d7a4r_reads_eq] at result
  exact result

private theorem d7a4r_source_service (w : HealingWitness) (q opening : Nat)
    (D : FGBlock (Fin p.n)) (hx : V) (hhonest : hx ∈ rho.honest)
    (hbefore : opening ≤ q * p.R) (hstart : w.sStar + 2 ≤ opening)
    (hproposal : HonestProposal E rho (fgsaInterface p c) opening (eraseFG D))
    (h2 : H2Prime p c E rho w) (h3 : H3 p c E rho w)
    (h6 : H6GateService p c E rho w)
    (hGST : recoveryStart p E ≤ SA.voteTime p.toParams (q * p.R))
    (hhor : p.actionTime q ≤ rho.horizon) (hne : eraseFG D ≠ .genesis)
    (hheads : ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x (q * p.R) = some H)
    (hjoined : ∀ x ∈ rho.honest,
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
    rw [d7a4r_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, hnd, hsource⟩
  · intro hlt
    have hcover : ∀ x ∈ rho.honest, ∃ H,
        headAtLabel p c E rho x (q * p.R) = some H ∧ Block.Preceq (eraseFG D) H := by
      have covered := FGCompose.service_head_coverage (A := c2_reads p c E rho w)
        hheads hjoined (fun x H hx hr hH =>
          h2 opening (eraseFG D) hproposal hstart x (q * p.R) H ⟨hx, hr⟩
            (Nat.succ_le_of_lt hlt) hH)
      intro x hx
      obtain ⟨H, _, hH, hDH⟩ := covered x hx
      exact ⟨H, hH, hDH⟩
    obtain ⟨_hresult, _hpassed, nd, d, hnd, hwrite, hlease, _hdeadline, hlive⟩ :=
      h6 (q * p.R) (eraseFG D) ((Nat.le_add_right w.sStar 2).trans
        (hstart.trans hbefore)) hGST hhor hne hcover hFgate hx hhonest
    obtain ⟨j, _hj, hclock⟩ := rows_clock_read p c E rho hx (p.actionTime q) nd hnd
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
    rw [d7a4r_reads_eq, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact ⟨nd, C, hnd, hsource, hDC⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1256–1263, 1667–1687: H3 supplies the exact source at c = z;
H2′ and H6 supply a covering source at c < z, with the full filter guards.
DC: INTENTIONAL: deepest fresh FG-SA selector; height plateau fixes the same entry. -/
theorem finality_action_source (w : HealingWitness) (q y opening : Nat)
    (D : FGBlock (Fin p.n)) (hx : V) (hhonest : hx ∈ rho.honest)
    (hbefore : opening ≤ q * p.R) (hstart : w.sStar + 2 ≤ opening)
    (hproposal : HonestProposal E rho (fgsaInterface p c) opening (eraseFG D))
    (h2 : H2Prime p c E rho w) (h3 : H3 p c E rho w)
    (h6 : H6GateService p c E rho w)
    (hGST : recoveryStart p E ≤ SA.voteTime p.toParams (q * p.R))
    (hhor : p.actionTime q ≤ rho.horizon) (hne : eraseFG D ≠ .genesis)
    (hheads : ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x (q * p.R) = some H)
    (hjoined : ∀ x ∈ rho.honest,
      joinedAt p E rho x (q * p.R) (SA.voteTime p.toParams (q * p.R)))
    (hconfirmed : confirmedReaderAtIdx p c E rho hx
      (afterTicksIdx rho (SA.gateTime p.toParams opening))
      (SA.gateTime p.toParams opening))
    (hFgate : ∀ x st, x ∈ rho.honest → gateIn p c E rho x (q * p.R) = some st →
      Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hframe : ∀ nd, postClock E rho hx (p.actionTime q) = some nd →
      D ∈ nd.st.fg.TF ∧ FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h)
    (hDh : (heightView p D).h = y + 1)
    (hcap : ∀ nd, postClock E rho hx (p.actionTime q) = some nd →
      ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1) :
    ∃ nd C, postClock E rho hx (p.actionTime q) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq D C ∧
      (heightView p C).h = y + 1 ∧ (heightView p C).T_h = (heightView p D).T_h := by
  have service := d7a4r_source_service p c E rho w q opening D hx hhonest hbefore
    hstart hproposal h2 h3 h6 hGST hhor hne hheads hjoined hconfirmed hFgate hframe
  have hcap' : ∀ nd, FGCompose.postClock E rho hx (p.actionTime q) = some nd →
      ∀ B ∈ ((fgsaCoreReads p c).core nd).fg.TF, (heightView p B).h ≤ y + 1 := by
    rw [d7a4r_reads_eq]
    rw [← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact hcap
  have h := FGCompose.finality_action_source (fgsaCoreReads p c) (c2_observations p c)
    (c2_timing p) E rho (fgsaCoreLaws p c) p.E (fgCertificateLaws p).height hx q y opening D
    service hbefore hDh hcap'
  simp only [c2_observations_eq, c2_timing_eq, d7a4r_reads_eq] at h
  rw [← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1] at h
  exact h

private theorem rows_release (y : Nat) (U C : FGBlock (Fin p.n))
    (st : State p.n) (Λ : RecordOnce)
    (hsource : FGSA.fgSource p st = some C) (hC : (heightView p C).h = y + 1)
    (hfields : (FGSA.fgInputs p st).2.h_j = y ∧
      (FGSA.fgInputs p st).2.J = U.root ∧ (FGSA.fgInputs p st).2.h_F < y)
    (hrecord : (Λ.target y = none ∨ Λ.target y = some U.root) ∧
      Λ.timeout y = false ∧ (Λ.lock y = none ∨ Λ.lock y = some U.root) ∧
      Λ.target (y + 1) = none ∧ Λ.timeout (y + 1) = false ∧
      Λ.lock (y + 1) = none ∧
      (∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ NamedHeightPair.vote (y + 1) T timeout)) :
    (attest p st Λ ⟨0, p.nPos⟩).1 =
      some (.vote ⟨.vote (y + 1) (heightView p C).T_h.root false, some ⟨y, U.root⟩⟩) := by
  obtain ⟨ht, hto, hl, htn, hton, hln, hsent⟩ := hrecord
  have hfp : finality_pair Λ.toRecord (FGSA.fgInputs p st).2 = some ⟨y, U.root⟩ := by
    delta finality_pair
    simp only [hfields.1, hfields.2.1, hfields.2.2, ht, hto, hl,
      and_self, ↓reduceIte]
  have hsrc : (FGSA.fgInputs p st).1 = some C := hsource
  have hhp : height_pair Λ.toRecord
      ((FGSA.fgInputs p st).1.map
        (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
      (some ⟨y, U.root⟩) = .vote (y + 1) (heightView p C).T_h.root false := by
    simp only [hsrc, Option.map_some, hC, height_pair, own_lock, hton, Bool.false_eq_true,
      ↓reduceIte, show y ≠ y + 1 from Nat.ne_of_lt (Nat.lt_succ_self y), hln, htn]
  have hsame : sameHeightOnce Λ (y + 1) (heightView p C).T_h.root false = false := by
    delta sameHeightOnce
    rw [List.any_eq_false]
    intro b hb
    cases hh : b.1 with
    | empty => simp only [Bool.false_eq_true, not_false_eq_true]
    | vote h T timeout =>
        have hne : h ≠ y + 1 := by
          intro he
          exact hsent b hb T timeout
            (hh.trans (congrArg (fun k => NamedHeightPair.vote k T timeout) he))
        simp only [hne, decide_false, Bool.false_and, Bool.false_eq_true,
          not_false_eq_true]
  have hkey : (NamedHeightPair.vote (y + 1) (heightView p C).T_h.root false,
      some (FinalityPair.mk y U.root)) ∉ Λ.sent := by
    intro hm
    exact hsent _ hm _ false rfl
  dsimp only [attest]
  rw [createRowOnce_def, attest_source_heightView, hfp]
  dsimp only
  rw [hhp]
  delta Row.onceKey RowBody.ofRow
  simp only [hsame, Bool.false_eq_true, ↓reduceIte,
    Option.filter_some, Nat.lt_succ_self, decide_true, hkey, Option.map_some]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1256–1263: awake actions release the same complete fresh rows and entry.
DC: INTENTIONAL: durable record and both send-once checks; source ancestry fixes the entry. -/
theorem fresh_unanimous_rows
    (q y : Nat) (D U : FGBlock (Fin p.n))
    (S : Finset (Fin p.n))
    (hS : S ⊆ honestSeats p c rho) (hQ : p.E.IsQuorum S)
    (hDh : (heightView p D).h = y + 1)
    (hreads : ∀ i ∈ S, ∃ nd C,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd ∧
      E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true ∧
      FGSA.fgSource p nd.st = some C ∧
      FGBlock.Preceq D C ∧ (heightView p C).h = y + 1)
    (hfields : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (FGSA.fgInputs p nd.st).2.h_j = y ∧
      (FGSA.fgInputs p nd.st).2.J = U.root ∧
      (FGSA.fgInputs p nd.st).2.h_F < y)
    (hrecord : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (nd.record.target y = none ∨ nd.record.target y = some U.root) ∧
      nd.record.timeout y = false ∧
      (nd.record.lock y = none ∨ nd.record.lock y = some U.root) ∧
      nd.record.target (y + 1) = none ∧
      nd.record.timeout (y + 1) = false ∧
      nd.record.lock (y + 1) = none ∧
      (∀ b ∈ nd.record.sent, ∀ T timeout,
        b.1 ≠ NamedHeightPair.vote (y + 1) T timeout))
    (hearlier : ∀ i ∈ S, ∀ j r a h, r < q →
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a →
      rowHeight a = some h → h < y + 1) :
    ∃ rows : Fin p.n → RowWire p.n,
      FreshFinalityRows_W p c E rho q y U S rows ∧
      (∀ i ∈ S, namedEntry (rows i).payload.height_pair =
        some (y + 1, (heightView p D).T_h.root)) ∧
      (∀ i ∈ S, (rows i).payload.height_pair =
        NamedHeightPair.vote (y + 1) (heightView p D).T_h.root false) := by
  classical
  have honest : ∀ i ∈ S, rho.seatOf (.base .fg) i ∈ rho.honest := by
    intro i hi
    exact (Finset.mem_filter.mp (hS hi)).2
  have result := FGCompose.fresh_unanimous_rows (fgsaCoreReads p c) (d7a4r_safety p c)
    (c2_observations p c) (c2_timing p) E rho (d7a4r_wire p c) p.E p.cfg RowWire.valid
    (fgCertificateLaws p).height (heightView_bridge p) (d7a4r_makeWire p)
    (fun _ => rfl)
    (by
      intro i y U B
      change (decide (1 ≤ y + 1) && decide (y < y + 1)) = true
      simp only [Nat.le_add_left, Nat.lt_succ_self, decide_true, Bool.and_self])
    (by intro nd; rw [d7a4r_reads_eq]; rfl)
    (by
      intro i q nd row hn hw hr
      exact d7a4r_release p c E rho i q nd row hn hw hr)
    q y D U S honest hQ hDh
    (by
      intro i hi
      obtain ⟨nd, C, hn, hw, hs, path, hh⟩ := hreads i hi
      refine ⟨nd, C, ?_, hw, ?_, path, hh⟩
      · exact (fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1 ▸ hn
      · rw [d7a4r_reads_eq]; exact hs)
    (by
      intro i hi nd hn
      exact hfields i hi nd ((fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1 ▸ hn))
    (by
      intro i hi nd hn
      obtain ⟨ht, hto, hl, htn, hton, hln, hsent⟩ :=
        hrecord i hi nd ((fgsa_eventReads_eq_compose E rho _ _).2.2.2.2.2.1 ▸ hn)
      exact ⟨⟨ht, hto, hl⟩, htn, hton, hln, hsent⟩)
    (by
      intro i hi j r a h hr ha hh
      exact hearlier i hi j r a h hr ((d7a4r_row_eq p c E rho j r _ a).mp ha) hh)
  obtain ⟨rows, fresh, entry, pair⟩ := result
  refine ⟨rows, ?_, entry, pair⟩
  rw [FreshFinalityRows_W_def]
  obtain ⟨_, _, seat⟩ := fresh
  refine ⟨hS, hQ, ?_⟩
  intro i hi
  obtain ⟨j, C, ha, hc, hsign, hh, hn, hsrc, hCh, hearlier⟩ := seat i hi
  refine ⟨j, C, (d7a4r_row_eq p c E rho j q _ _).mp ha,
    (d7a4r_complete_eq p c rho _ _).mp hc, (d7a4r_signer_iff p _ i).mp hsign,
    hh, hn, (d7a4r_source_eq p c E rho _ q) ▸ hsrc, hCh, ?_⟩
  intro j' r a h hr ha hh
  exact hearlier j' r a h hr ((d7a4r_row_eq p c E rho j' r _ a).mpr ha) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: bound held blocks through the next action cut.
DC: INTENTIONAL: held/read causal cap; Assembly supplies the causal-origin bound. -/
theorem actual_anchor_cap
    (q y : Nat)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V)
        (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hrows : ∀ j x r a u h T timeout,
      HonestRowAt p c E rho j x r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ y + 2 := by
  have result := FGCompose.actual_anchor_cap (fgsaCoreReads p c) (d7a4r_safety p c)
    (c2_observations p c) (c2_timing p) E rho q y
    (by
      intro cut b i x W hi hW rows
      rw [d7a4r_held_eq] at hW
      apply hcapBefore cut b i x W hi hW
      intro j z r a u h B timeout ha hu hp ht
      exact rows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mpr ha) hu hp ht)
    (by
      intro j z r a u h B timeout ha hu hp ht
      exact hrows j z r a u h B timeout ((d7a4r_row_eq p c E rho j r z a).mp ha) hu hp ht)
  simpa only [d7a4r_held_eq, c2_timing_eq, c2_observations_eq] using result

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: keep the actual anchor key, or cover it by finality.
DC: INTENTIONAL: W retention with K_W ≥ 2; retention does not imply acceptance. -/
theorem actual_anchor_retained_or_covered
    (y : Nat) (D U P : FGBlock (Fin p.n))
    (hDP : FGBlock.Preceq D P)
    (hret : Window.RetainedW p D y U)
    (hcap : (heightView p P).h ≤ y + 2) :
    Window.RetainedW p P y U ∨ Window.CoveredW p P y U := by
  have result := FGCompose.actual_anchor_retained_or_covered p.E p.cfg p.K_W
    (d7a4w_nonempty p) p.kWLarge y D U P hDP ((d7a4w_retained_eq p D U y).mpr hret)
    (by simpa only [KitFG.Window.heightView_def, ← d7a4w_height_eq p] using hcap)
  simpa only [d7a4w_retained_eq, d7a4w_covered_eq] using result

end AvailableChain.FGSA.Run
end
