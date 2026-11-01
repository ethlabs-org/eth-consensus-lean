module
public import AvailableChainFGCompose.Proofs.Finality.Middle
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Finality.History -- shake: keep (window transport)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- FINAL 22:1171–1226 (F1–F5). The opening, middle, fresh entry and early carrier
of one forward window, with the raw cuts that later kernel steps reuse.
DC: INTENTIONAL: the W kernel keeps its chosen witnesses as data. -/
structure KernelMiddleWitness_W
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block) where
  A₀ : FGBlock (Fin p.n)
  B : FGBlock (Fin p.n)
  U : FGBlock (Fin p.n)
  X_D : FGBlock (Fin p.n)
  cD : Slot
  d : Nat

  opening : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A
  eraseA : eraseFG A₀ = A
  carrierA : OpeningCarrier_W p c E rho (pt.r * p.R) A A₀
  carrierB : OpeningCarrier_W p c E rho ((pt.r + 1) * p.R) (eraseFG B) B
  carrierD : OpeningCarrier_W p c E rho cD (eraseFG X_D) X_D
  honestB : HonestProposal E rho (fgsaInterface p c) ((pt.r + 1) * p.R) (eraseFG B)
  honestD : HonestProposal E rho (fgsaInterface p c) cD (eraseFG X_D)
  slotA : A₀.slot = pt.r * p.R
  slotB : B.slot = (pt.r + 1) * p.R
  slotD : X_D.slot = cD
  earlySlot : (pt.r + 1) * p.R + kappaF p ΔF ≤ cD ∧ cD ≤ (pt.r + 2) * p.R

  heightA : (heightView p A₀).h = d
  highA : pt.w.M + 1 ≤ d
  heightB : (heightView p B).h = d + 1
  entryB : (heightView p B).T_h = U
  freshEntry : EntryAt p U (d + 1)
  strictAU : FGBlock.Preceq A₀ U ∧ A₀ ≠ U
  pathUB : FGBlock.Preceq U B
  freshSlot : pt.r * p.R < U.slot ∧ U.slot ≤ (pt.r + 1) * p.R
  parentAB : FGBlock.Preceq A₀ B.parent
  parentBD : FGBlock.Preceq B X_D.parent

  sourceA : ∀ x ∈ rho.honest,
    actionSourceFG p c E rho x pt.r = some (some A₀)
  sourceB : ∀ x ∈ rho.honest,
    actionSourceFG p c E rho x (pt.r + 1) = some (some B)
  serviceD : ExactService p c E rho cD (eraseFG X_D)

  heightD : (heightView p X_D).h = d + 2
  justifiedD : (heightView p X_D).J = U
  justifiedHeightD : (heightView p X_D).h_j = d + 1
  pendingD : (Window.derive p p.K_W X_D).h_F < d + 1
  retainedD : Window.RetainedW p X_D (d + 1) U

  noFirstHeight : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → rowHeight a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 1) ≤ t
  noSecondHeight : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → rowHeight a = some h →
    d + 2 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 2) ≤ t
  noEarlyFinality : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → finHeight a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 2) ≤ t

  chainA : ChainRowsBefore p c E rho A₀ (p.actionTime pt.r)
  chainB : ChainRowsBefore p c E rho B (p.actionTime (pt.r + 1))
  chainD : ChainRowsBefore p c E rho X_D (p.actionTime (pt.r + 2))
  freshD : FreshPrem p c E rho (pt.r + 1) (d + 1) X_D
  noMixedD : NoMixedOnPath p X_D (d + 1)

  batchB : (heightView p B.parent).h = d →
    BatchPrem p c E rho ΔF .target pt.r d (heightView p A₀).T_h B
  batchD : (heightView p X_D.parent).h = d + 1 →
    BatchPrem p c E rho ΔF .target (pt.r + 1) (d + 1) U X_D

  targetsB : ∀ x ∈ rho.honest, ∃ j a,
    HonestRowAt p c E rho j x (pt.r + 1) a ∧
    RowComplete p c rho x a ∧ NamesEntry p .target a (d + 1) U

  actionsInRun : p.actionTime (pt.r + 2) ≤ rho.horizon
  capThroughBAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
    HeldAt p c E rho i x W → (heightView p W).h ≤ d + 1
  capThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 2)) →
    HeldAt p c E rho i x W → (heightView p W).h ≤ d + 2
  finalityThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 2)) →
    HeldAt p c E rho i x W → (finalityView p W).h_F < d + 1
  heldDAtFinalAction : ∀ x ∈ rho.honest,
    X_D ∈ (storeAt p c E rho (afterTicksIdx rho (p.actionTime (pt.r + 2))) x).fg.TF
  heldAAtEnd : ∀ x ∈ rho.honest,
    A₀ ∈ (storeAt p c E rho rho.events.length x).fg.TF

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

/-- FINAL 22:1171–1226 (F1–F5). The kernel opening, middle block, fresh entry and early
carrier, with their raw history. The Foundation facts are explicit inputs.
DC: INTENTIONAL: Assembly supplies the source names, raw origin, batch coverage and the
FF2 target coverage. -/
theorem kernel_opening_and_middle
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (pt : KernelPt)
    (hδ : p.δt = 2 * p.R)
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (A : Block)
    (hA : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A) :
    Nonempty (KernelMiddleWitness_W p c E rho ΔF pt A) := by
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
  obtain ⟨m⟩ := FGCompose.kernel_opening_and_middle
    (R := fgsaCoreReads p c) (S := d7n_safety p c) (O := d7n_observations p c)
    (T := d7n_timing p) (L := d7n_timing_laws p) (E := E) (rho := rho)
    (I := fgsaInterface p c) (D := d7n_wire p c) (Ef := p.E)
    (decodeProposal := d7n_decodeProposal p) (bodyErase := NamedProposal.erase)
    (bodyRows := NamedProposal.rows) (blockWireRows := fun nd => FGSA.blockWireRows nd.st)
    (parentFG := fun nd => FGSA.fgBlockOf nd.st)
    (parentHeight := fun _ s H =>
      ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (validFor := fun _ s H => Window.rowValidW (parentFoldState p s H))
    (makeFG := FGSA.fgBlock) (valid := RowWire.valid) (ac := d7n_ac p c E rho pt.w)
    (cfg := p.cfg) (K := p.K_W) (ΔF := ΔF) (sp := d7n_point p pt.w) (pt := ⟨pt.r⟩) (A := A)
    (CL := fgsaCoreLaws p c) (HL := fgsaHeadLaws p c E rho)
    (keep := d7n_tree_keep p c) (restore := d7n_tree_restore p c)
    (hs := hK.set.base.valid.toScheduleWellFormed) (hc := fgCertificateLaws p)
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
    (hK := d7n_kernel p c E rho hK hδ) (hF0 := hF) (deltaF := hK.set.deltaF)
    (hreset := lower) (hGSTstart := hK.input.wit.after_gst)
    (reset := d7n_reset p c E rho pt.w hK.input.wit.toH0Reset)
    (history := d7n_transfer p c E rho pt.w hK.input.t.h2 rho.horizon)
    (reflect := by
      intro X Y h
      rw [d7n_erase, d7n_erase] at h
      exact eraseFG_preceq_iff.mp h)
    (parent := by intro X; rw [d7n_erase, d7n_erase]; exact (eraseFG_parent X).symm)
    (hNames := d7n_names p c E rho hNames) (hOrigin := d7n_origin p c E rho hOrigin)
    (emission := d7n_emission p c E rho) (decoded := d7n_decoded p c E rho)
    (hweight := by
      rw [d7n_faulty_eq]
      exact kmid_faulty_weight p c E rho hK.set.base hK.set.faultQ)
    (linked := (hK.set.base.linked.toCStar (.base .fg) trivial).1)
    (receipt := (d7n_receipt_eq p c E rho ΔF).mpr hK.input.t.rows.receipt)
    (awake := hK.set.awake)
    (honest_slot := fun _ hs => ⟨_, hs.2⟩)
    (proposal := fun s hs hlo hhi => kmid_window_proposal hK hs hlo hhi)
    (carrier := fun _ _ hp => d7n_carrier p c E rho hK.set.base.valid.toScheduleWellFormed hp)
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
      intro x hx r C hs hhigh hawake
      rw [d7n_source_eq] at hs
      obtain ⟨j, rSent, a, hr, ha, hc, hp⟩ := hSOCOVTarget x hx r C hs hhigh hawake
      exact ⟨j, rSent, a, hr, (d7n_row_eq p c E rho j rSent x a).mpr ha,
        (d7n_complete_eq p c rho x a).mpr hc, hp⟩)
    (hA := hA)
  exact ⟨d7n_middle_from p c E rho G ΔF pt A hK m⟩

/-- FINAL 22:1199–1206 (F2). The fresh entry of the middle block, as kept in the witness.
DC: INTENTIONAL: a projection, not a new choice of the fresh entry. -/
theorem kernel_middle_fresh_U
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) :
    FGBlock.Preceq m.A₀ m.U ∧ m.A₀ ≠ m.U ∧
    (heightView p m.U).h = (heightView p m.A₀).h + 1 ∧
    FGBlock.Preceq m.U m.B := by
  exact FGCompose.kernel_middle_fresh_U (m := d7n_middle_to p c E rho ΔF pt A m)

/-- FINAL 22:1218–1226 (F5). The pending justification of the early carrier.
DC: INTENTIONAL: a projection, not a new choice of the pending pair. -/
theorem kernel_middle_early_justification
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) :
    (heightView p m.X_D).h = m.d + 2 ∧
    (heightView p m.X_D).J = m.U ∧
    (heightView p m.X_D).h_j = m.d + 1 ∧
    (Window.derive p p.K_W m.X_D).h_F < m.d + 1 ∧
    Window.RetainedW p m.X_D (m.d + 1) m.U := by
  have h := FGCompose.kernel_middle_early_justification
    (m := d7n_middle_to p c E rho ΔF pt A m)
  rw [← d7nw_derive_eq, d7nw_retained_eq] at h
  exact h

/-- FINAL 22:1265–1304. An honest source at action q+2 is at most d+2 high. Its own
action tick is a held read before the read-phase cut of that action.
DC: INTENTIONAL: the receipt Assembly reads the round-(q+2) source cap here. -/
theorem kernel_middle_source_cap
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x (pt.r + 2) = some (some C)) :
    (heightView p C).h ≤ m.d + 2 := by
  exact FGCompose.kernel_middle_source_cap (m := d7n_middle_to p c E rho ΔF pt A m)
    (CL := fgsaCoreLaws p c) (hs := hs) (hx := hx)
    (hsrc := (d7n_source_eq p c E rho x (pt.r + 2)).trans hsrc)

end AvailableChain.FGSA.Run
end
