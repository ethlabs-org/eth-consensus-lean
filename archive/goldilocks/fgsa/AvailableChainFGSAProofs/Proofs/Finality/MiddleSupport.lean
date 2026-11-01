module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Proofs.Restart -- shake: keep (P0a restart API)
public import AvailableChainFGSAProofs.Proofs.Finality.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Finality.TickRead -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (frozen bounds API)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGSA.Proofs.WindowAdmissionInvariant
public import AvailableChainKitFG.CausalCapCore -- shake: keep (causal cap API)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

private def d7m_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7m_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (d7m_timing p) where
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

section

private abbrev d7mw_Old := FGSA.Window.State
private abbrev d7mw_New := SimplexFG.Window.State

private def d7mw_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def d7mw_toWindow {V : Type} (w : d7mw_Old V) : d7mw_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map d7mw_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem d7mw_entry_eq {V : Type} (e : FGSA.Window.Entry V) :
    d7mw_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem d7mw_state_eq {V : Type} (w : d7mw_Old V) :
    d7mw_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map d7mw_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem d7mw_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (d7mw_toEntry e).j = e.j ∧ (d7mw_toEntry e).X = e.X ∧ (d7mw_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem d7mw_state_fields {V : Type} (w : d7mw_Old V) :
    (d7mw_toWindow w).L = w.L ∧ (d7mw_toWindow w).s = w.s ∧
    (d7mw_toWindow w).h = w.h ∧ (d7mw_toWindow w).T_h = w.T_h ∧
    (d7mw_toWindow w).target_participation = w.target_participation ∧
    (d7mw_toWindow w).progress = w.progress ∧ (d7mw_toWindow w).W = w.W.map
      d7mw_toEntry ∧
    (d7mw_toWindow w).J = w.J ∧ (d7mw_toWindow w).h_j = w.h_j ∧
    (d7mw_toWindow w).F = w.F ∧ (d7mw_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem d7mw_initial_eq {V : Type} :
    d7mw_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem d7mw_foldRow_eq (w : d7mw_Old V) (a : Row V) :
    d7mw_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (d7mw_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map d7mw_toEntry =
      (w.W.map d7mw_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [d7mw_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, d7mw_state_eq] using
        congrArg (fun es => ({ d7mw_toWindow w with W := es } : d7mw_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [d7mw_state_eq] <;> rw [bits] <;> simp_all [d7mw_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem d7mw_rows_eq (rs : List (Row V)) (w : d7mw_Old V) :
    d7mw_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (d7mw_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, d7mw_foldRow_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7mw_advance_eq (w : d7mw_Old V) :
    d7mw_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (d7mw_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem d7mw_greatest_eq (E : Electorate V) (w : d7mw_Old V) :
    (FGSA.Window.greatestReady E w).map d7mw_toEntry =
      SimplexFG.Window.greatestReady E (d7mw_toWindow w) := by
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
      (oldStep best e).map d7mw_toEntry = newStep (best.map d7mw_toEntry)
      (d7mw_toEntry e) := by
    dsimp [oldStep, newStep, d7mw_entry_eq]
    split_ifs <;> cases best <;> simp_all [d7mw_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map d7mw_toEntry =
        (es.map d7mw_toEntry).foldl newStep (best.map d7mw_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (d7mw_toWindow w) =
      (w.W.map d7mw_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem d7mw_finalize_eq (E : Electorate V) (w : d7mw_Old V) :
    d7mw_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (d7mw_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← d7mw_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [d7mw_state_eq, d7mw_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem d7mw_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map d7mw_toEntry =
      (es.map d7mw_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map d7mw_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, d7mw_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem d7mw_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      d7mw_Old V) :
    d7mw_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (d7mw_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← d7mw_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change d7mw_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (d7mw_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      d7mw_state_eq, d7mw_entry_eq, List.map_drop]

private theorem d7mw_transition_eq (p : Params) (K : Nat) (w : d7mw_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    d7mw_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (d7mw_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, d7mw_events_eq, SimplexFG.Window.transition_def]
  have h := d7mw_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { d7mw_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem d7mw_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) d7mw_toWindow where
  initial := d7mw_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := d7mw_transition_eq p K

private theorem d7mw_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    d7mw_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (d7mw_foldMap p K).fold_eq B

end

/-! ### Step group A: the round clock -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. The action clock in slot units.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_actionTime_eq (p : Params) (r : Nat) :
    p.actionTime r = 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ :=
  FGCompose.kmid_actionTime_eq (d7m_timing p) (d7m_timing_laws p) r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220,923–944. Positive delay and round length order the actions.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_action_strictMono (p : Params) : StrictMono p.actionTime :=
  FGCompose.kmid_action_strictMono (d7m_timing p) (d7m_timing_laws p)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. Slot times are monotone in the slot.
DC: INTENTIONAL: FG-SA slot times use the 4Δ grid. -/
theorem kmid_slot_scale_le (p : Params) {a b : Nat} (h : a ≤ b) :
    4 * p.Δ * (a : Time) ≤ 4 * p.Δ * (b : Time) :=
  FGCompose.kmid_slot_scale_le (d7m_timing p) (d7m_timing_laws p) h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. Slot times are strictly monotone in the slot.
DC: INTENTIONAL: FG-SA slot times use the 4Δ grid. -/
theorem kmid_slot_scale_lt (p : Params) {a b : Nat} (h : a < b) :
    4 * p.Δ * (a : Time) < 4 * p.Δ * (b : Time) :=
  FGCompose.kmid_slot_scale_lt (d7m_timing p) (d7m_timing_laws p) h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. The row delay fits in κ slots.
DC: INTENTIONAL: the row delay fixes κ. -/
theorem kmid_kappa_cover (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    6 * p.Δ + ΔF ≤ 4 * p.Δ * (kappaF p ΔF : Time) :=
  FGCompose.kmid_kappa_cover (d7m_timing p) (d7m_timing_laws p) ΔF hF

/-! ### Step group A: the actual opening, middle and early proposals -/

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem d7m_reads_eq : fgsaCoreReads p c =
    { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
      erase := eraseFG
      source := fun nd => FGSA.fgSource p nd.st
      headVote := fun nd s => FGSA.headVote p nd.st s
      finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
      proposalFG := (fgsaCoreReads p c).proposalFG } :=
  congrArg (fun reads => { reads with proposalFG := (fgsaCoreReads p c).proposalFG })
    (fgsaCoreReads_def p c)

private theorem d7m_action_eq (p : Params) (q : Nat) :
    (d7m_timing p).action q = p.actionTime q := rfl

private def d7m_safety (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem d7mw_height_eq :
    heightView p = KitFG.Window.certificateHeight p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectHeight (d7mw_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7mw_derive_eq, KitFG.Window.certificateHeight_def]

private theorem d7mw_finality_eq :
    finalityView p = KitFG.Window.certificateFinality p.E p.cfg p.K_W := by
  funext B
  change KitFG.Window.projectFinality (d7mw_toWindow (FGSA.Window.derive p p.K_W B)) = _
  rw [d7mw_derive_eq, KitFG.Window.certificateFinality_def]

private theorem d7mw_retained_eq (B U : FGBlock (Fin p.n)) (y : Nat) :
    KitFG.Window.RetainedW p.E p.cfg p.K_W B y U = Window.RetainedW p B y U := by
  apply propext
  unfold KitFG.Window.RetainedW
  rw [← d7mw_derive_eq p p.K_W B, Window.RetainedW_def]
  change (∃ e ∈ (Window.derive p p.K_W B).W.map d7mw_toEntry, e.j = y ∧ e.X = U) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hey, heU⟩
    exact ⟨d, hd, hey, heU⟩
  · rintro ⟨d, hd, hdy, hdU⟩
    exact ⟨d7mw_toEntry d, ⟨d, hd, rfl⟩, hdy, hdU⟩

private def d7m_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def d7m_signer (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem d7m_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

private def d7m_wire : FGCompose.FGHistoryWireReads (d7m_safety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := d7m_signer p
  decode_height a u ha := by
    delta d7m_safety at ha
    rw [d7m_decode p ha]
    rfl
  decode_finality a u ha := by
    delta d7m_safety at ha
    rw [d7m_decode p ha]
    rfl
  decode_signer a u ha := by
    delta d7m_safety at ha
    rw [d7m_decode p ha]
    rfl

private theorem d7m_row_eq (j r : Nat) (x : V) (a : RowWire p.n) :
    FGCompose.HonestRowAt (d7m_safety p c) E rho (d7m_timing p) j x r a =
      HonestRowAt p c E rho j x r a := by delta d7m_safety; rfl

private theorem d7m_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7m_timing p) x r =
      actionSourceFG p c E rho x r := by rw [d7m_reads_eq]; rfl

private theorem d7m_held_eq (i : Nat) (x : V) (B : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x B = HeldAt p c E rho i x B := by
  rw [d7m_reads_eq]
  rfl

private def d7m_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private theorem d7m_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) : FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c)
      (d7m_observations p c) (d7m_timing p) E rho (fgsaInterface p c)
      (d7m_point p w) horizon := by
  intro x r C hx hsrc hhigh _ s Q hQ _ hgap
  change FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (d7m_timing p) x r =
    some (some C) at hsrc
  rw [d7m_source_eq, d7m_reads_eq] at *
  exact h x r C s Q hx hsrc hhigh hQ hgap

private theorem d7m_rowHeight_eq (a : RowWire p.n) :
    FGCompose.historyRowHeight (d7m_safety p c) (d7m_wire p c) a = rowHeight a := by
  rw [rowHeight_def]
  rfl

private theorem d7m_finHeight_eq (a : RowWire p.n) :
    FGCompose.historyFinHeight (d7m_safety p c) (d7m_wire p c) a = finHeight a := by
  rw [finHeight_def]
  rfl

omit [DecidableEq V] in
private theorem d7m_event_eq (j : Nat) : FGCompose.eventTime rho j = eventTime rho j := rfl

private theorem d7m_names
    (h : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    FGCompose.HighRecordNames (fgsaCoreReads p c) (d7m_safety p c)
      (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c) := by
  intro j x r a e ha he
  rw [d7m_row_eq] at ha
  obtain ⟨C, hC, hpair⟩ := h j x r a e ha he
  exact ⟨C, (d7m_source_eq p c E rho x r).trans hC, hpair⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180. A joined honest proposer at a positive slot emits its
block.
DC: INTENTIONAL: the FG-SA proposer duty always builds a block at a positive slot. -/
theorem kmid_honest_proposal_exists (hs : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hjoined : joinedAt p E rho (V2.D.proposerOf rho (fgsaInterface p c) s) s
      (SA.proposalTime p.toParams s))
    (hh : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ b, HonestProposal E rho (fgsaInterface p c) s b := by
  obtain ⟨B, hB, _⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs hΔ hslot
    hjoined.1 hjoined.2.2 hh
  exact ⟨B, hB⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180. The emitted proposal object and its post-clock proposer
read.
DC: INTENTIONAL: FG-SA reads the proposal tick of the actual signed wire. -/
theorem kmid_proposal_read (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ j N, N.erase = b ∧ rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho j ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        b = proposalBlock p (proposerHead p st s) s (c.app (rho.input
          (V2.D.proposerOf rho (fgsaInterface p c) s) (SA.proposalTime p.toParams s))) N.raw
              N.support
            (proposalRows p st (proposerHead p st s)) ∧
        N.rows = proposalRows p st (proposerHead p st s) :=
  proposal_read_named p c E rho hs hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180,585–598. The FG block of an honest proposal, with its stored
parent.
DC: INTENTIONAL: the emitted wire, proposer read, parent and decoded rows give one block. -/
theorem kmid_opening_carrier (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ Bfg : FGBlock (Fin p.n), eraseFG Bfg = b ∧ OpeningCarrier_W p c E rho s b Bfg ∧
      Bfg.slot = s ∧
      (∃ rows, HonestCarrier p c E rho s b rows ∧ Bfg.rows = rows.filterMap RowWire.toRow?) ∧
      ∃ st, proposalStateAt p c E rho s = some st ∧
        FGSA.fgBlockOf st b.parent = some Bfg.parent ∧ Bfg.parent ∈ st.fg.TF := by
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, _hrows⟩ := kmid_proposal_read p c E rho hs hp
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v) (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : b.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk b N.rows = true := by
    rw [hb, _hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : b ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st b.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  refine ⟨fgBlock P b N.rows, eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok,
    (OpeningCarrier_W_def p c E rho s b _).mpr
      ⟨o, N, st, P, hemit, heN, rfl, hst, hlook, rfl⟩, ?_,
    ⟨N.rows, ⟨hp, o, N, hemit, rfl, heN, rfl⟩, rfl⟩, st, hst, hlook, hP⟩
  rw [fgBlock_slot, hb]
  rfl

/-! ### Step group A: erased identity and ancestry -/

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. FG roots are content hashes; erasure is injective.
DC: INTENTIONAL: the flat FG wire keeps one erasure. -/
theorem kmid_eraseFG_inj {A B : FGBlock (Fin p.n)} (h : eraseFG A = eraseFG B) : A = B :=
  eraseFG_injective h

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. Erased ancestry lifts to FG ancestry.
DC: INTENTIONAL: the flat FG wire keeps one erasure. -/
theorem kmid_lift_preceq {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  FGCompose.kmid_lift_preceq eraseFG (fun _ _ h => eraseFG_preceq_iff.mp h) h

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. A block's parent precedes it, also at genesis.
DC: SAME chain order. -/
theorem kmid_parent_preceq (B : FGBlock (Fin p.n)) : FGBlock.Preceq B.parent B :=
  FGCompose.kmid_parent_preceq B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1188–1197. H3 at an action slot fixes the FG action source.
DC: INTENTIONAL: the erased H3 source lifts by root identity. -/
theorem kmid_source_of_exact {v : Slot} {X : FGBlock (Fin p.n)}
    (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.gateTime p.toParams v ≤ rho.horizon) (r : Nat) (hv : v = r * p.R) :
    ∀ x ∈ rho.honest,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) →
      actionSourceFG p c E rho x r = some (some X) := by
  intro x hx hreader
  have hs := ((hex.2 hh x hx hreader).2.2.2.2) r hv
  have h := FGCompose.kmid_source_of_exact (fgsaCoreReads p c) (d7m_timing p) E rho
    (fgsaCoreLaws p c) (X := X) (x := x) (r := r) (by
      rw [d7m_source_eq, d7m_reads_eq]
      exact hs)
  rw [d7m_source_eq] at h
  exact h

/-! ### Step group B: raw row heights -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. The empty pair has no height; a height names an entry.
DC: INTENTIONAL: the wire height is optional for an empty pair. -/
theorem kmid_rowHeight_entry (a : RowWire p.n) (h : Nat) (hh : rowHeight a = some h) :
    ∃ e, namedEntry a.payload.height_pair = some (h, e) := by
  have hdef : rowHeight a =
      (match a.payload.height_pair with | .empty => none | .vote h _ _ => some h) := rowHeight_def a
  rw [hdef] at hh
  cases hp : a.payload.height_pair with
  | empty => rw [hp] at hh; cases hh
  | vote k e timeout =>
    rw [hp] at hh
    have hk : k = h := Option.some.inj hh
    subst k
    exact ⟨e, by rw [namedEntry_def]⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. An honest row height is its action source height.
DC: INTENTIONAL: the source-discipline name channel is an explicit input. -/
theorem kmid_row_source_height
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {h : Nat}
    (ha : HonestRowAt p c E rho j x r a) (hh : rowHeight a = some h) :
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ h = (heightView p C).h :=
  by
  have hh' : FGCompose.historyRowHeight (d7m_safety p c) (d7m_wire p c) a = some h := hh
  obtain ⟨C, hC, he⟩ := FGCompose.kmid_row_source_height (fgsaCoreReads p c)
    (d7m_safety p c) (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c)
    (d7m_names p c E rho hnames) ((d7m_row_eq p c E rho j r x a).mpr ha) hh'
  exact ⟨C, (d7m_source_eq p c E rho x r).symm.trans hC, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. Rows before the opening action stay at or below its height.
DC: INTENTIONAL: H2 transfers every high earlier source below the opening parent. -/
theorem kmid_rows_below_opening (w : HealingWitness) (h2 : TCarrier p c E rho w)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (q : Nat) (A₀ : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (q * p.R) (eraseFG A₀))
    (hhigh : w.M + 1 ≤ (heightView p A₀).h) :
    ∀ j x r a h, r < q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ (heightView p A₀).h  := by
  intro j x r a h hr ha hh
  let horizon := max (p.actionTime q) (SA.proposalTime p.toParams (q * p.R))
  exact FGCompose.kmid_rows_below_opening (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) (d7m_timing_laws p) E rho
    (fgsaInterface p c) (d7m_wire p c) p.E (d7m_point p w) horizon
    (d7m_transfer p c E rho w h2 horizon) (d7m_names p c E rho hnames)
    (fgCertificateLaws p).height (by
      intro A B h
      rw [d7m_reads_eq] at h
      exact eraseFG_preceq_iff.mp h)
    (by intro B; rw [d7m_reads_eq]; exact (eraseFG_parent B).symm) q A₀
    (by rw [d7m_reads_eq]; exact hA) (le_max_left _ _) (le_max_right _ _)
    hhigh j x r a h hr ((d7m_row_eq p c E rho j r x a).mpr ha) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. Rows at an action with a fixed source have that source height.
DC: INTENTIONAL: the source-discipline name channel is an explicit input. -/
theorem kmid_rows_at_source
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (r : Nat) (X : FGBlock (Fin p.n))
    (hsrc : ∀ x ∈ rho.honest, actionSourceFG p c E rho x r = some (some X)) :
    ∀ j x a h, HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h = (heightView p X).h :=
  by
  intro j x a h ha hh
  exact FGCompose.kmid_rows_at_source (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c)
    (d7m_names p c E rho hnames) r X
    (fun x hx => (d7m_source_eq p c E rho x r).trans (hsrc x hx)) j x a h
    ((d7m_row_eq p c E rho j r x a).mpr ha) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:946–956. An honest row is the client output of its action tick.
DC: INTENTIONAL: the run uses event-indexed emission. -/
private theorem d7m_emitted_action {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      (attest p
        ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some a.payload := by
  obtain ⟨_, hj, hem⟩ := (HonestRowAt_def p c E rho _ _ _ _).mp ha
  refine ⟨hj, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  change ofRow p a ∈ (if E.awake x (p.actionTime r) then
    (duties p (p.actionTime r)).flatMap (fun d =>
      (rho.ownSeats (RunDuty.signLabel d) x).filterMap (fun i =>
        (act p c ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r))
          d (rho.input x (p.actionTime r))).map
            (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
      ([] : List (Obj p)) else []) at hem
  split at hem
  · rw [List.append_nil] at hem
    obtain ⟨d, _, hem⟩ := List.mem_flatMap.mp hem
    obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
    obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
    have hp : m = .row a.payload := congrArg V2.Signed.payload ho
    subst m
    cases d with
    | headAction s =>
      change (if joinedNow p _ then some (Msg.head _) else none) =
        some (Msg.row a.payload) at hm
      split at hm <;> cases hm
    | fgAction r' =>
      change (attest p _ _ _).1.map Msg.row = some (.row a.payload) at hm
      obtain ⟨payload, hb, he⟩ := Option.map_eq_some_iff.mp hm
      have heq : payload = a.payload := Msg.row.inj he
      subst payload
      dsimp only [fgsa] at hb ⊢
      exact hb
    | propAction s =>
      change (if joinedNow p _ then (propose p _ s).map (withApp p _) else none) =
        some (.row a.payload) at hm
      split at hm
      · obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨_, _, _, _, heq, _, _⟩ := rowsOk_withApp _ _ _ (by rw [hm]; exact congrArg some he)
        cases heq
      · cases hm
  · exact (List.not_mem_nil hem).elim

private theorem d7m_emitted_seat (j : Nat) (x : V) (r : Nat) (a : RowWire p.n)
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

private theorem d7m_emission :
    FGCompose.HighRecordEmission (d7m_safety p c) (d7m_timing p) E rho p.E p.cfg := by
  intro j x r a u ha hd
  rw [d7m_row_eq] at ha
  change a.toRow? = some u at hd
  have hsend := (d7m_emitted_action p c E rho ha).2
  have hj : (attest p
      ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
      (V2.D.Run.stateBefore E rho j x).record u.signer).1 = some a.payload := by
    rw [← attest_signer_irrel _ _ ⟨0, p.nPos⟩ u.signer]
    exact hsend
  obtain ⟨row, hrow, hp⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨_, _, _, _, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg _ u.signer _ _ hrow
  have hwire : RowWire.toRow? (⟨.seat .fg u.signer, a.payload⟩ : RowWire p.n) = some u := by
    rw [d7m_decode p hd]
    rfl
  have heq : row = u := by
    rw [← hp, he] at hwire
    rw [he]
    exact Option.some.inj hwire
  exact heq ▸ hrow

private theorem d7m_decoded : ∀ j x r a,
    FGCompose.HonestRowAt (d7m_safety p c) E rho (d7m_timing p) j x r a →
    ∃ u, (d7m_safety p c).decode a = some u := by
  intro j x r a ha
  obtain ⟨seat, hs⟩ := d7m_emitted_seat p c E rho j x r a
    ((d7m_row_eq p c E rho j r x a).mp ha)
  refine ⟨⟨seat, a.payload.height_pair, a.payload.finality_pair⟩, ?_⟩
  rcases a with ⟨auth, ⟨body⟩⟩
  dsimp only at hs
  subst auth
  rfl

theorem kmid_row_action {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      (attest p
        ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some a.payload := by
  obtain ⟨u, hu⟩ := d7m_decoded p c E rho j x r a
    ((d7m_row_eq p c E rho j r x a).mpr ha)
  obtain ⟨tick, he⟩ := FGCompose.kmid_row_action (d7m_safety p c) (d7m_timing p)
    E rho p.E p.cfg (d7m_emission p c E rho)
    ((d7m_row_eq p c E rho j r x a).mpr ha) hu
  refine ⟨tick, ?_⟩
  change a.toRow? = some u at hu
  rw [d7m_decode p hu]
  rw [attest_signer_irrel _ _ ⟨0, p.nPos⟩ u.signer]
  change Option.map _ _ = _
  dsimp only [d7m_safety, d7m_timing] at he
  rw [he]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958. An honest row has a height, and its finality height is smaller.
DC: SAME client filter of the finality pair below the height pair. -/
theorem kmid_row_fin_lt {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    ∃ h, rowHeight a = some h ∧ ∀ f, finHeight a = some f → f < h := by
  exact FGCompose.kmid_row_fin_lt (d7m_safety p c) (d7m_timing p) E rho
    (d7m_wire p c) p.E p.cfg (d7m_emission p c E rho) (d7m_decoded p c E rho)
    ((d7m_row_eq p c E rho j r x a).mpr ha)

variable [Fintype V]

/-! ### Step group E: held chains through the actual HEAD read -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. A tick at the cut time is before the read-phase cut.
DC: INTENTIONAL: event phases order ticks before same-time deliveries. -/
theorem kmid_tick_lt_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t' t : Time} (hi : rho.events[i]? = some (.tick v t')) (ht : t' ≤ t) :
    i < afterTicksIdx rho t :=
  FGCompose.kmid_tick_lt_afterTicks E rho hs hi ht

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1226,954–956. The exact HEAD read holds its block at the tick index.
DC: INTENTIONAL: the stored HEAD target is the admitted FG block. -/
theorem kmid_head_held {v : Slot}
    {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v)) :
    ∃ i, rho.events[i]? = some (.tick x (SA.voteTime p.toParams v)) ∧
      X ∈ (V2.D.Run.stateBefore E rho i x).st.fg.TF := by
  have hhead := hex.1 hh x hx hjoined
  change (postClock E rho x (SA.voteTime p.toParams v)).map
    (fun nd => FGSA.headVote p nd.st v) = some (eraseFG X) at hhead
  have hhead' : (FGCompose.postClock E rho x (SA.voteTime p.toParams v)).map
      (fun nd => (fgsaCoreReads p c).headVote nd v) = some ((fgsaCoreReads p c).erase X) := by
    rw [d7m_reads_eq, ← (fgsa_eventReads_eq_compose E rho x _).2.2.2.2.2.1]
    exact hhead
  have h := FGCompose.head_held (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
    (fgsaHeadLaws p c E rho) hhead'
  rw [d7m_reads_eq] at h
  exact h

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1265–1304. The FG action source is a stored block of the read state.
DC: INTENTIONAL: the joint source picks from the filtered stored tree. -/
theorem kmid_source_mem_TF {st : State p.n} {C : FGBlock (Fin p.n)}
    (h : FGSA.fgSource p st = some C) : C ∈ st.fg.TF := by
  have hsrc : (fgsaCoreReads p unitCodec).source ⟨st, RecordOnce.initial⟩ = some C := by
    rw [d7m_reads_eq]
    exact h
  have hm := FGCompose.source_mem_TF (fgsaCoreReads p unitCodec) (fgsaCoreLaws p unitCodec) hsrc
  rw [d7m_reads_eq] at hm
  exact hm

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1265–1304. An honest action source is held at its own action tick,
before the read-phase cut of that action. DC: INTENTIONAL: the run reads the source
at the post-clock state of the action tick. -/
theorem kmid_source_held_at_tick (hs : V2.D.ScheduleWellFormed E rho) {x : V} {r : Nat}
    {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ i, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      i < afterTicksIdx rho (p.actionTime r) ∧ HeldAt p c E rho i x C :=
  by
  obtain ⟨i, hi, hcut, hheld⟩ := FGCompose.kmid_source_held_at_tick (fgsaCoreReads p c)
    (d7m_timing p) E rho (fgsaCoreLaws p c) hs hx
    ((d7m_source_eq p c E rho x r).trans hsrc)
  exact ⟨i, hi, hcut, (d7m_held_eq p c E rho i x C).mp hheld⟩

omit [Fintype V] in
private theorem kmid_tree_restore : FGCompose.FGTreeRestoreLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [d7m_reads_eq]
  exact congrArg (fun st => st.TF) (acRestart_fg p nd.st t)

omit [Fintype V] in
private theorem kmid_tree_keep : FGCompose.FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [(kmid_tree_restore p c).restart_eq]

omit [Fintype V] in
private theorem kmid_head_read {v : Slot} {X : FGBlock (Fin p.n)}
    (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v)) :
    (FGCompose.postClock E rho x (SA.voteTime p.toParams v)).map
      (fun nd => (fgsaCoreReads p c).headVote nd v) = some ((fgsaCoreReads p c).erase X) := by
  rw [d7m_reads_eq, ← (fgsa_eventReads_eq_compose E rho x _).2.2.2.2.2.1]
  exact hex.1 hh x hx hjoined

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956,1226. The exact HEAD read gives raw chain rows before a later cut.
DC: INTENTIONAL: an actual honest strict-before read holds every carrier. -/
theorem kmid_chainRows_of_head (hs : V2.D.ScheduleWellFormed E rho)
    {v : Slot} {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v))
    (cut : Time) (hcut : SA.voteTime p.toParams v < cut) :
    ChainRowsBefore p c E rho X cut := by
  have h := FGCompose.kmid_chainRows_of_head (fgsaCoreReads p c) (d7m_timing p) E rho
    (fgsaCoreLaws p c)
    (fgsaHeadLaws p c E rho) hs (kmid_tree_restore p c) x hx
    (kmid_head_read p c E rho hex hh x hx hjoined) cut hcut
  rw [FGCompose.ChainRowsBefore_def, d7m_reads_eq] at h
  exact h

omit [Fintype V] in
/-- The joined HEAD target remains in durable storage at each later cut. -/
theorem kmid_head_held_from (hs : V2.D.ScheduleWellFormed E rho)
    {v : Slot} {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v))
    (k : Nat) (t : Time) (ht : SA.voteTime p.toParams v ≤ t) (hk : afterTicksIdx rho t ≤ k) :
    X ∈ (storeAt p c E rho k x).fg.TF := by
  have h := FGCompose.kmid_head_held_from (fgsaCoreReads p c) (d7m_timing p) E rho
    (fgsaCoreLaws p c)
    (fgsaHeadLaws p c E rho) hs (kmid_tree_keep p c) x
    (kmid_head_read p c E rho hex hh x hx hjoined) k t ht hk
  rw [d7m_reads_eq] at h
  exact h

omit [Fintype V] in
private theorem d7m_faulty_eq : FGCompose.historyFaulty (d7m_safety p c) rho =
    Finset.univ \ honestSeats p c rho := by
  classical
  unfold FGCompose.historyFaulty
  simp only [FGCompose.safetyHolder_def]
  delta d7m_safety
  ext i
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, kmid_honestSeats_mem]
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:948–958. Linked unit-weight seats bound the faulty weight.
DC: INTENTIONAL: FG-SA uses linked seats. -/
theorem kmid_faulty_weight (base : BaseSet p c E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (Finset.univ \ honestSeats p c rho) < p.E.q := by
  rw [← d7m_faulty_eq]
  apply FGCompose.kmid_faulty_weight (d7m_safety p c) rho p.E
    (base.linked.toCStar (.base .fg) trivial).1 (fun _ => rfl)
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  rw [hq]
  exact hQ.lt

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:948–958. A seat outside the faulty set is honest.
DC: INTENTIONAL: FG-SA uses linked seats. -/
theorem kmid_honest_seat (u : Row (Fin p.n))
    (hf : u.signer ∉ Finset.univ \ honestSeats p c rho) :
    rho.seatOf (.base .fg) u.signer ∈ rho.honest := by
  exact FGCompose.kmid_honest_seat (d7m_safety p c) rho u
    (by rw [d7m_faulty_eq]; exact hf)

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. Decode the exact signed wire payload.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
theorem kmid_wire_decode {a : RowWire p.n} {u : Row (Fin p.n)}
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

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. The emission tick gives its exact action time.
DC: INTENTIONAL: the run uses event-indexed emission. -/
theorem kmid_event_time {j r : Nat} {z : V} {a : RowWire p.n}
    (hj : HonestRowAt p c E rho j z r a) :
    eventTime rho j = some (p.actionTime r) :=
  FGCompose.kmid_event_time (d7m_safety p c) (d7m_timing p) E rho
    ((d7m_row_eq p c E rho j r z a).mpr hj)

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. A matching pair has the stated wire height.
DC: INTENTIONAL: the wire height is optional for an empty pair. -/
theorem kmid_matching_height {u : Row (Fin p.n)} {a : RowWire p.n}
    {y : Nat} {T : BlockId} (ha : a.toRow? = some u)
    (hm : u.height_pair.matchesEntry y T = true) : rowHeight a = some y :=
  by
  apply FGCompose.kmid_matching_height (d7m_safety p unitCodec)
    (d7m_wire p unitCodec) _ hm
  delta d7m_safety
  exact ha

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. Deliveries before the read-phase cut are strictly earlier.
DC: INTENTIONAL: event phases order ticks before same-time deliveries. -/
theorem kmid_delivery_before_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {t t' : Time} {x : V} {o : (fgsa p c).Object}
    (hk : k < afterTicksIdx rho t) (he : rho.events[k]? = some (.deliver x o t')) :
    t' < t :=
  FGCompose.kmid_delivery_before_afterTicks E rho hs hk he

variable (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
    HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
      ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

omit [Fintype V] in
include horigin in
private theorem d7m_origin : FGCompose.RawHistoryOrigin (fgsaCoreReads p c)
    (d7m_safety p c) E rho (d7m_timing p) (d7m_wire p c) := by
  intro i x B hh u hu
  rw [d7m_held_eq] at hh
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := horigin i x B hh u hu
  refine ⟨a, r, ?_, ?_, k, o, t, hki, hk, ?_⟩
  · delta d7m_safety
    exact ha
  · change d7m_signer p a = some u.signer
    rw [d7m_decode p ha]
    rfl
  · intro z hz hhonest
    obtain ⟨seat, hseat, hholder⟩ := hz
    have hseat' : a.auth = .seat .fg seat := by
      change d7m_signer p a = some seat at hseat
      rw [d7m_decode p ha] at hseat ⊢
      have eq := Option.some.inj hseat
      rw [eq]
    have hholder' : rho.seatOf (.base .fg) seat = z := by
      change FGCompose.safetyHolder (d7m_safety p c) rho seat = z at hholder
      rw [FGCompose.safetyHolder_def] at hholder
      delta d7m_safety at hholder
      exact hholder
    obtain ⟨⟨j, hji, hj⟩, hrt⟩ := he z ⟨seat, hseat', hholder'⟩ hhonest
    exact ⟨⟨j, hji, (d7m_row_eq p c E rho j r z a).mpr hj⟩, hrt⟩

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–938. A held chain has no crossing above its honest row bound.
DC: INTENTIONAL: timed raw origin replaces a selected-pool bound. -/
theorem kmid_held_height_le (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (hheld : HeldAt p c E rho i x B)
    (hbefore : ∀ k o t, k < i → rho.events[k]? = some (.deliver x o t) → t < cut) :
    (heightView p B).h ≤ m + 1 := by
  exact FGCompose.kmid_held_height_le (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c) p.E
    (fgCertificateLaws p) (d7m_origin p c E rho horigin)
    (by rw [d7m_faulty_eq]; exact kmid_faulty_weight p c E rho base faultQ) m cut
    (by simpa only [d7m_row_eq, d7m_rowHeight_eq, d7m_event_eq] using hrows) i x B
    ((d7m_held_eq p c E rho i x B).mpr hheld) hbefore

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. The cap holds through the read phase of the cut, before deliveries.
DC: INTENTIONAL: event phases make same-time rows undeliverable before the read. -/
theorem kmid_held_cap_afterTicks (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 := by
  exact FGCompose.kmid_held_cap_afterTicks (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c) p.E
    (fgCertificateLaws p) (d7m_origin p c E rho horigin) base.valid.toScheduleWellFormed
    (by rw [d7m_faulty_eq]; exact kmid_faulty_weight p c E rho base faultQ) m cut
    (by simpa only [d7m_row_eq, d7m_rowHeight_eq, d7m_event_eq] using hrows) i x B hcut
    ((d7m_held_eq p c E rho i x B).mpr hheld)

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958,1224–1226. No held finality certificate at or above y before the cut.
DC: INTENTIONAL: the active W certificate supplies the exact finality height. -/
theorem kmid_held_finality_afterTicks (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (y : Nat) (cut : Time)
    (hy : 0 < y)
    (hrows : ∀ j z r a f t, HonestRowAt p c E rho j z r a →
      finHeight a = some f → eventTime rho j = some t → t < cut → f < y)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt p c E rho i x W) :
    (finalityView p W).h_F < y := by
  exact FGCompose.kmid_held_finality_afterTicks (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) E rho (d7m_wire p c) p.E
    (fgCertificateLaws p) (d7m_origin p c E rho horigin) base.valid.toScheduleWellFormed
    (by rw [d7m_faulty_eq]; exact kmid_faulty_weight p c E rho base faultQ) y cut hy
    (by simpa only [d7m_row_eq, d7m_finHeight_eq, d7m_event_eq] using hrows) i x W hcut
    ((d7m_held_eq p c E rho i x W).mpr hheld)

/-! ### Step group C: the height batch at a parent that stays -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The parent fold state reads the parent's height entry.
DC: INTENTIONAL: R6W reads the window parent state with the child slot. -/
private theorem kmid_parentFold_eq (s : Slot) (H : FGBlock (Fin p.n)) :
    parentFoldState p s H = Window.parentState p p.K_W H s := rfl

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The parent fold state has the height and entry of the height view.
DC: INTENTIONAL: R6W reads the window parent state with the child slot. -/
theorem kmid_parentFold_height (s : Slot) (H : FGBlock (Fin p.n)) :
    (parentFoldState p s H).h = (heightView p H).h ∧
      (parentFoldState p s H).T_h = (heightView p H).T_h := by
  have h := FGCompose.kmid_parentFold_height p.E p.cfg p.K_W s H
  rw [kmid_parentFold_eq, Window.parentState_def, heightView_def, Window.projectHeight_def]
  change (SimplexFG.Window.derive p.E p.cfg p.K_W H).h =
      (SimplexFG.Window.derive p.E p.cfg p.K_W H).h ∧
    (SimplexFG.Window.derive p.E p.cfg p.K_W H).T_h =
      (SimplexFG.Window.derive p.E p.cfg p.K_W H).T_h at h
  rw [← d7mw_derive_eq] at h
  exact h

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The decoded row of a seat-authenticated wire.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
theorem kmid_wire_toRow {a : RowWire p.n} {i : Fin p.n} (ha : a.auth = .seat .fg i) :
    a.toRow? = some ⟨i, a.payload.height_pair, a.payload.finality_pair⟩ := by
  rcases a with ⟨auth, ⟨body⟩⟩
  dsimp only at ha
  subst auth
  rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–603. A post-clock proposer read is reachable.
DC: INTENTIONAL: the proposer read is an indexed post-clock state. -/
theorem kmid_proposal_reachable {s : Slot} {st : State p.n}
    (hs : proposalStateAt p c E rho s = some st) : Reachable p st := by
  change (postClock E rho _ _).map (·.st) = some st at hs
  rw [postClock_def, preTick_def] at hs
  cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hk] at hs; cases hs
  | some k =>
      rw [hk] at hs
      rw [← Option.some.inj hs]
      exact reachable_postClock E rho k _ _

private def d7m_kind : RowKind → FGCompose.RowKind
  | .target => .target
  | .progress => .progress

private theorem d7m_rowNames (k : RowKind) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FGCompose.RowNames (d7m_kind k) row i y U = RowNames p k row i y U := by
  cases k <;> rfl

private theorem d7m_validRows (st : State p.n) (hr : Reachable p st) :
    ∀ X ∈ st.fg.TF, ∀ row ∈ X.rows,
      SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W X.parent) row = true := by
  intro X hX row hrow
  cases X with
  | genesis => exact (List.not_mem_nil hrow).elim
  | node Q t root x rs =>
    have hv := stored_r6wW p hr Q t root x rs hX row hrow
    change SimplexFG.Window.r6w (SimplexFG.Window.derive p.E p.cfg p.K_W Q) row = true
    rw [← d7mw_derive_eq]
    cases hp : row.height_pair <;> cases hf : row.finality_pair <;>
      simp only [SimplexFG.Window.r6w_def, Window.r6w_def,
      SimplexFG.Window.heightMatch_def, Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, Window.staleUseful_def,
      SimplexFG.Window.windowMatch_def, Window.windowMatch_def,
      d7mw_state_eq, d7mw_entry_eq, List.any_map, Function.comp_def, hp, hf,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff, List.any_eq_true, decide_eq_true_eq] at hv ⊢
    all_goals first | exact hv | skip
    rcases hv with hm | ⟨h, e, he, hpair⟩
    · exact Or.inl hm
    · exact Or.inr ⟨h, e, he, decide_eq_true hpair⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:583–610. Rows on a stored chain that name an entry lie above that
entry,
when the chain stays at the entry height. DC: INTENTIONAL: stored R6W validity. -/
theorem kmid_rows_above_entry (st : State p.n) (hr : Reachable p st)
    (k : RowKind) (y : Nat) (U P : FGBlock (Fin p.n)) (hP : P ∈ st.fg.TF)
    (hPh : (heightView p P).h = y) (hUP : FGBlock.Preceq U P) :
    ∀ i W, FGBlock.Preceq W P → (∃ row ∈ W.rows, RowNames p k row i y U) →
      FGBlock.Preceq U W.parent := by
  have h := FGCompose.kmid_rows_above_entry (fgsaCoreReads p unitCodec)
    (d7m_observations p unitCodec)
    p.E p.cfg p.K_W (fgCertificateLaws p).height (d7mw_height_eq p)
    (⟨st, RecordOnce.initial⟩ : Node p) (by
      rw [d7m_reads_eq]
      exact (storeInvariant p st hr).fg.closed)
    (by
      rw [d7m_reads_eq]
      exact viewRootInj_TF p st (storeInvariant p st hr))
    (by rw [d7m_reads_eq]; exact d7m_validRows p st hr)
    (d7m_kind k) y U P (by rw [d7m_reads_eq]; exact hP) hPh hUP
  simpa only [d7m_rowNames] using h

/-! ### Step group D: slot chains of stored blocks -/

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:43–54,1056–1059. A stored accepted block has a smaller parent slot.
DC: INTENTIONAL: accepted proposal validity supplies strict parent-slot growth. -/
theorem kmid_stored_parent_slot (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (v : V) (C : Block)
    (hm : C ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks) (hg : C ≠ .genesis) :
    C.parent.slot < C.slot := by
  obtain ⟨w, hw, hb, j, o, t, -, hd, ho, -⟩ := fgsa_stored_block_origin E rho i v C hm hg
  obtain ⟨r, N, rfl, -⟩ := (metaInv_stateBefore E rho i v).wireTree w hw
  have hQ : N.erase = C := Option.some.inj hb
  rw [← hQ]
  have hf := hE.wire j v o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  exact of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:43–54,1056–1059. A stored FG block has increasing slots along its chain.
DC: INTENTIONAL: accepted proposal validity supplies strict parent-slot growth. -/
theorem kmid_stored_slotChain (hE : V2.D.ExecutionValid E rho) (i : Nat) (v : V)
    (X : FGBlock (Fin p.n)) (hX : X ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF) :
    SlotChain X := by
  intro W hW hg
  have hinv := cstoreInv_stateBefore E rho i v
  have hWm := ancestor_closed_of_parent_closed _ hinv.fg.closed X hX W hW
  have hb : eraseFG W ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks :=
    (hinv.baseTree _).mpr ⟨W, hWm, rfl⟩
  have hlt := kmid_stored_parent_slot p c E rho hE i v (eraseFG W) hb
    (fun h => hg (eraseFG_eq_genesis.mp h))
  rwa [eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:43–54. Slots do not decrease along a slot chain.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
theorem kmid_slot_le_of_preceq {W X : FGBlock (Fin p.n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) : W.slot ≤ X.slot :=
  FGCompose.kmid_slot_le_of_preceq hX hW

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:43–54. A strict ancestor has a strictly smaller slot.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
theorem kmid_slot_lt_of_strict {W X : FGBlock (Fin p.n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) (hne : W ≠ X) : W.slot < X.slot :=
  FGCompose.kmid_slot_lt_of_strict hX hW hne

private def d7m_decodeProposal (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem d7m_decodeProposal_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    d7m_decodeProposal p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold d7m_decodeProposal
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem d7m_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

omit [Fintype V] in
private theorem d7m_decode_emitted (s : Slot) (o : Obj p) (N : NamedProposal p.n)
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

omit [Fintype V] in
private theorem d7m_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier (d7m_decodeProposal p) NamedProposal.erase NamedProposal.rows)
      s Q rows = HonestCarrier p c E rho s Q rows := by
  apply propext
  constructor
  · rintro ⟨hp, o, hemit, N, hd, he, hr⟩
    exact ⟨hp, o, N, hemit,
      d7m_proposal_payload p o s N ((d7m_decodeProposal_iff p o s N).mp hd), he, hr⟩
  · rintro ⟨hp, o, N, hemit, hpay, he, hr⟩
    exact ⟨hp, o, hemit, N, (d7m_decodeProposal_iff p o s N).mpr
      (d7m_decode_emitted p c E rho s o N hemit hpay), he, hr⟩

private theorem d7m_signer_iff (a : RowWire p.n) (i : Fin p.n) :
    d7m_signer p a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta d7m_signer; simp
  | proposer s => delta d7m_signer; simp
  | seat label j => cases label <;> delta d7m_signer <;> simp

private theorem d7m_namesEntry (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) :
    FGCompose.NamesEntry (pair := (d7m_wire p c).heightPair) (d7m_kind k) a y U =
      NamesEntry p k a y U := by cases k <;> rfl

omit [DecidableEq V] [Fintype V] in
private theorem d7m_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (d7m_safety p c) rho (d7m_signer p) RowWire.valid x a =
      RowComplete p c rho x a := by
  unfold FGCompose.RowComplete FGCompose.RowSigner RowComplete RowSigner
  simp only [d7m_signer_iff, FGCompose.safetyHolder_def]
  delta d7m_safety
  rfl

omit [Fintype V] in
private theorem d7m_receipt_eq (deltaF : Time) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (d7m_safety p c) E rho (d7m_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF = TRowsReceipt p c E rho deltaF := by
  delta FGCompose.TRowsReceipt
  rw [TRowsReceipt_def]
  delta FGCompose.HeldBefore HeldBefore
  rw [d7m_reads_eq]
  simp only [d7m_row_eq]
  rfl

omit [Fintype V] in
private theorem d7m_validParent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

omit [Fintype V] in
private theorem d7m_heightMatch_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
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

private abbrev d7m_Batch (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (fgsaCoreReads p c) (d7m_safety p c) (d7m_observations p c)
    (d7m_timing p) E rho (fgsaInterface p c) (d7m_wire p c) p.E
    (d7m_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF (d7m_kind k) q y U X

private theorem d7m_batch_from (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (k : RowKind) (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : d7m_Batch p c E rho ΔF k q y U X) : BatchPrem p c E rho ΔF k q y U X := by
  refine ⟨base, faultQ, h.deltaF, (d7m_receipt_eq p c E rho ΔF).mp h.rowsReceipt,
    h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · have hc := h.carrier
    rw [d7m_reads_eq] at hc
    dsimp only [d7m_safety] at hc
    simpa only [d7m_carrier_eq] using hc
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ?_, (d7m_signer_iff p a i).mp hsign,
      (d7m_namesEntry p c k a y U).mp hn, ht, htime, ?_, ?_⟩
    · exact (d7m_row_eq p c E rho j r _ a).mp ha
    · rw [d7m_reads_eq] at hv
      exact (d7m_validParent_eq p c E rho _ _ a).mp hv
    · rw [d7m_reads_eq] at hm
      exact (d7m_heightMatch_eq p c E rho _ _ a).mp hm
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW
      (by simpa only [d7m_rowNames] using hr)

private theorem d7m_matching_valid (s : Slot) (H : FGBlock (Fin p.n))
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

/-! ### Step group C: the honest batch of a stored parent -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:583–610,886–915. Complete honest target rows at a stored parent form a
batch.
DC: SAME height coverage; INTENTIONAL: complete earlier-or-current send-once witnesses. -/
theorem kmid_batchPrem (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (deltaF : E.Δ ≤ ΔF) (receipt : TRowsReceipt p c E rho ΔF)
    (q y : Nat) (U X : FGBlock (Fin p.n))
    (horizon : max (p.actionTime q) E.t_GST + ΔF ≤ SA.proposalTime p.toParams X.slot ∧
      SA.proposalTime p.toParams X.slot ≤ rho.horizon)
    (carrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows ∧
      X.rows = rows.filterMap RowWire.toRow?)
    (st : State p.n) (hst : proposalStateAt p c E rho X.slot = some st)
    (hlook : FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (hparTF : X.parent ∈ st.fg.TF)
    (after : q * p.R + 2 ≤ X.slot) (entry : EntryAt p U y)
    (path : FGBlock.Preceq U X.parent) (hpar : (heightView p X.parent).h = y)
    (rows : ∀ x ∈ rho.honest, ∃ j r a, r ≤ q ∧ HonestRowAt p c E rho j x r a ∧
      RowComplete p c rho x a ∧ NamesEntry p .target a y U) :
    BatchPrem p c E rho ΔF .target q y U X := by
  change (FGCompose.proposalStateAt E rho (fgsaInterface p c) X.slot).map Node.st =
    some st at hst
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
  have hr := kmid_proposal_reachable p c E rho hst
  apply d7m_batch_from p c E rho ΔF base faultQ .target q y U X
  refine FGCompose.kmid_batchPrem (fgsaCoreReads p c) (d7m_safety p c)
    (d7m_observations p c) (d7m_timing p) E rho (fgsaInterface p c) (d7m_wire p c)
    p.E p.cfg p.K_W (fgCertificateLaws p).height (d7mw_height_eq p)
    (d7m_decodeProposal p) NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) RowWire.valid ΔF
    base.valid.toScheduleWellFormed ?_ ?_ ?_ deltaF
    ((d7m_receipt_eq p c E rho ΔF).mpr receipt) q y U X horizon ?_ nd hnd
    (by rw [d7m_reads_eq]; exact hlook)
    (by rw [d7m_reads_eq]; exact hparTF)
    (by rw [d7m_reads_eq]; exact (storeInvariant p nd.st hr).fg.closed)
    (by rw [d7m_reads_eq]; exact viewRootInj_TF p nd.st (storeInvariant p nd.st hr))
    (by rw [d7m_reads_eq]; exact d7m_validRows p nd.st hr)
    ?_ (fun a hv hm => d7m_matching_valid p X.slot X.parent a hv hm)
    after entry path hpar ?_
  · rw [d7m_faulty_eq]
    exact kmid_faulty_weight p c E rho base faultQ
  · exact (base.linked.toCStar (.base .fg) trivial).1
  · have eq : Finset.univ \ FGCompose.historyFaulty (d7m_safety p c) rho =
        honestSeats p c rho := by
      rw [d7m_faulty_eq]
      ext i
      simp
    rw [eq]
    exact kmid_honest_quorum p c rho base.linked hfault
  · delta d7m_safety
    rw [d7m_reads_eq]
    simpa only [d7m_carrier_eq] using carrier
  · have h := kmid_parentFold_height p X.slot X.parent
    exact Prod.ext h.1 (congrArg FGBlock.root h.2)
  · intro x hx
    obtain ⟨j, r, a, hr, ha, hc, hn⟩ := rows x hx
    exact ⟨j, r, a, hr, (d7m_row_eq p c E rho j r x a).mpr ha,
      (d7m_complete_eq p c rho x a).mpr hc, (d7m_namesEntry p c .target a y U).mpr hn⟩

/-! ### Step group A: kernel clock bounds -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A round count of periods is the slot clock of its first slot.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_period_eq (r : Nat) :
    (r : Time) * P p = 4 * p.Δ * ((r * p.R : Nat) : Time) :=
  FGCompose.kmid_period_eq (d7m_timing p) r

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177,1199–1211. Kernel clock facts from the kernel premise.
DC: INTENTIONAL: the W kernel uses the row delay ΔF. -/
theorem kmid_kernel_bounds {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) :
    0 ≤ ΔF ∧ 2 ≤ kappaF p ΔF ∧ kappaF p ΔF ≤ p.R ∧ 2 ≤ p.R ∧
      pt.w.sStar + 2 ≤ pt.r * p.R ∧
      E.t_GST ≤ SA.proposalTime p.toParams (pt.r * p.R) ∧
      p.actionTime (pt.r + 2) ≤ rho.horizon := by
  have hF : 0 ≤ ΔF := by
    have h1 := hK.set.deltaF
    have h2 := hK.set.base.delta
    linarith [p.deltaPos]
  have lower : (d7m_timing p).proposal ((d7m_point p pt.w).reset.sStar + 2) ≤
      (d7m_point p pt.w).serviceStart := by
    have h := kmid_slot_scale_le p hK.input.wit.proposal_lower
    change 4 * p.Δ * ((pt.w.sStar + 2 : Nat) : Time) ≤
      4 * p.Δ * (pt.w.u : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  exact FGCompose.kmid_kernel_bounds (d7m_timing p) (d7m_timing_laws p)
    (sp := d7m_point p pt.w) (pt := ⟨pt.r⟩) ⟨hK.bound.kappa_le_R⟩
    hK.start hK.hhor hF lower hK.input.wit.after_gst

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177. Every slot read up to the window end is inside the run.
DC: INTENTIONAL: the W kernel horizon covers its window reads. -/
theorem kmid_slot_horizon {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} (hs : s ≤ (pt.r + 2) * p.R) :
    SA.proposalTime p.toParams s ≤ rho.horizon ∧ SA.voteTime p.toParams s ≤ rho.horizon ∧
      SA.gateTime p.toParams s ≤ rho.horizon :=
  FGCompose.kmid_slot_horizon (d7m_timing p) (d7m_timing_laws p)
    (kmid_kernel_bounds hK).2.2.2.2.2.2 hs

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177. Every slot read from the opening on is after GST.
DC: INTENTIONAL: the W kernel starts after GST. -/
theorem kmid_slot_gst {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} (hs : pt.r * p.R ≤ s) :
    E.t_GST ≤ SA.proposalTime p.toParams s :=
  FGCompose.kmid_slot_gst (d7m_timing p) (d7m_timing_laws p)
    (kmid_kernel_bounds hK).2.2.2.2.2.1 hs

omit [Fintype V] in
/-- The healing witness starts after the approved recovery start. -/
theorem finality_healing_recoveryStart {ΔF : Time} {w : HealingWitness}
    (input : HealingInput p c E rho w ΔF) : recoveryStart p E ≤ tstar p w := by
  have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
    exact_mod_cast input.wit.proposal_lower
  have hsync := input.wit.synchronous
  have hrec := finality_recoveryStart_le_vote p E (w.u + 1)
    ((Nat.le_add_left 2 w.sStar).trans
      (input.wit.proposal_lower.trans (Nat.le_add_right w.u 1))) (by
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * (((w.u + 1 : Nat) : Int) - 2)
      push_cast
      nlinarith [p.deltaPos])
  apply hrec.trans
  change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
    4 * p.Δ * (w.u : Int) + 6 * p.Δ
  push_cast
  linarith [p.deltaPos]

/-- The healing gate supplies a confirmed reader at every index in its suffix. -/
theorem finality_input_suffix_confirmed {G ΔF : Time} {w : HealingWitness}
    (hrec : Recovery₂ p c E rho G ΔF) (input : HealingInput p c E rho w ΔF)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hsuf : HealSuffix p c rho (tstar p w) i) (hhor : tstar p w ≤ rho.horizon) :
    confirmedReaderIdx p c E rho x i := by
  apply finality_recovery_confirmedIdx p c E rho hrec hx w.u i
    (by
      have hsync := input.wit.synchronous
      have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
        exact_mod_cast input.wit.proposal_lower
      change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * (w.u : Int)
      nlinarith [p.deltaPos]) hhor
  intro j hj
  have hjlt := kmid_tick_lt_afterTicks p c E rho hrec.base.valid.toScheduleWellFormed
    hj le_rfl
  have hg : isGateTime p (tstar p w) = true :=
    (isGateTime_iff p _).mpr ⟨w.u, rfl⟩
  have hstart : afterTicksIdx rho (tstar p w) ≤ i := by
    simpa only [HealSuffix_def, healStart_def, hg, ite_true] using hsuf.1
  exact hjlt.trans_le hstart

variable {p c E rho} in
/-- A window suffix contains the enabled healing gate and its wake events. -/
theorem kmid_suffix_confirmed {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hsuf : HealSuffix p c rho (tstar p pt.w) i)
    (hhor : tstar p pt.w ≤ rho.horizon) : confirmedReaderIdx p c E rho x i := by
  apply finality_recovery_confirmedIdx p c E rho hK.set hx pt.w.u i
    (by
      have hsync := hK.input.wit.synchronous
      have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
        exact_mod_cast hK.input.wit.proposal_lower
      change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * (pt.w.u : Int)
      nlinarith [p.deltaPos]) hhor
  intro j hj
  have hjlt := kmid_tick_lt_afterTicks p c E rho hK.set.base.valid.toScheduleWellFormed
    hj le_rfl
  have hstart : afterTicksIdx rho (tstar p pt.w) ≤ i := by
    have hg : isGateTime p (tstar p pt.w) = true :=
      (isGateTime_iff p _).mpr ⟨pt.w.u, rfl⟩
    simpa only [HealSuffix_def, healStart_def, hg, ite_true] using hsuf.1
  exact hjlt.trans_le hstart

variable {p c E rho} in
/-- The healing start supplies the full previous-slot join cutoff. -/
theorem kmid_window_join_cut {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
  have hstart := hK.start
  rw [kmid_period_eq] at hstart
  have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
    exact_mod_cast hK.input.wit.proposal_lower
  have hsync := hK.input.wit.synchronous
  have hle := kmid_slot_scale_le p hlo
  change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
  change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  nlinarith [p.deltaPos]

variable {p c E rho} in
/-- Every honest window voter has the duty join guard. -/
theorem kmid_window_joined {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) (hhi : s ≤ (pt.r + 2) * p.R)
    {x : V} (hx : x ∈ rho.honest) :
    joinedAt p E rho x s (SA.voteTime p.toParams s) :=
  finality_recovery_joined p c E rho hK.set hx (kmid_window_join_cut hK hlo)
    ((kmid_slot_gst hK hlo).trans (by
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      linarith [p.deltaPos])) (kmid_slot_horizon hK hhi).2.1

variable {p c E rho} in
/-- The window gate has run for each honest confirmed reader. -/
theorem kmid_window_confirmed {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) :
    confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
      (SA.gateTime p.toParams s) := by
  apply finality_recovery_confirmed p c E rho hK.set hx s _ _
    (kmid_slot_gst hK hlo) le_rfl hhor
  intro j hj
  exact kmid_tick_lt_afterTicks p c E rho hK.set.base.valid.toScheduleWellFormed hj le_rfl

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1171–1180. An honest window slot has an actual honest proposal.
DC: INTENTIONAL: the FG-SA proposer duty always builds a block at a positive slot. -/
theorem kmid_window_proposal {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hlo : pt.r * p.R ≤ s) (hhi : s ≤ (pt.r + 2) * p.R) :
    ∃ b, HonestProposal E rho (fgsaInterface p c) s b := by
  have hh := (kmid_slot_horizon hK hhi).1
  have hcut := kmid_window_join_cut hK hlo
  exact kmid_honest_proposal_exists p c E rho hK.set.base.valid.toScheduleWellFormed
    hK.set.base.delta s hslot
    (finality_recovery_joined p c E rho hK.set hslot.2 hcut (kmid_slot_gst hK hlo) hh) hh

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1188–1197. H3 serves every honest window proposal.
DC: INTENTIONAL: the healed AC service is an explicit input. -/
theorem kmid_window_exact {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} {b : Block}
    (hb : HonestProposal E rho (fgsaInterface p c) s b) (hlo : pt.r * p.R ≤ s) :
    ExactService p c E rho s b :=
  hK.input.ac.h3 s b hb ((kmid_kernel_bounds hK).2.2.2.2.1.trans hlo)

/-! ### Step group B: raw cuts from round bounds -/

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. A round-indexed row bound is a raw cut at the next action.
DC: INTENTIONAL: an honest row has the exact time of its action tick. -/
theorem kmid_rows_cut (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ m) :
    (∀ j x r a h t, HonestRowAt p c E rho j x r a → rowHeight a = some h → m + 1 ≤ h →
      eventTime rho j = some t → p.actionTime (Q + 1) ≤ t) ∧
    (∀ j z r a h t, HonestRowAt p c E rho j z r a → rowHeight a = some h →
      eventTime rho j = some t → t < p.actionTime (Q + 1) → h ≤ m) := by
  simpa only [d7m_row_eq, d7m_rowHeight_eq, d7m_event_eq, d7m_action_eq] using
    FGCompose.kmid_rows_cut (d7m_safety p c)
    (d7m_timing p) (d7m_timing_laws p) E rho (d7m_wire p c) m Q
    (by simpa only [d7m_row_eq, d7m_rowHeight_eq] using hrow)

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958. A round-indexed row bound caps the finality heights below it.
DC: SAME client filter of the finality pair below the height pair. -/
theorem kmid_fin_cut (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ m) :
    (∀ j x r a f t, HonestRowAt p c E rho j x r a → finHeight a = some f → m ≤ f →
      eventTime rho j = some t → p.actionTime (Q + 1) ≤ t) ∧
    (∀ j z r a f t, HonestRowAt p c E rho j z r a → finHeight a = some f →
      eventTime rho j = some t → t < p.actionTime (Q + 1) → f < m) := by
  simpa only [d7m_row_eq, d7m_finHeight_eq, d7m_event_eq, d7m_action_eq] using
    FGCompose.kmid_fin_cut (d7m_safety p c)
    (d7m_timing p) (d7m_timing_laws p) E rho (d7m_wire p c) p.E p.cfg
    (d7m_emission p c E rho) (d7m_decoded p c E rho) m Q
    (by simpa only [d7m_row_eq, d7m_rowHeight_eq] using hrow)

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A HEAD read at or before a round's first slot precedes its action.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_vote_lt_action {s : Slot} {r : Nat} (h : s ≤ r * p.R) :
    SA.voteTime p.toParams s < p.actionTime r :=
  FGCompose.kmid_vote_lt_action (d7m_timing p) (d7m_timing_laws p) h

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A proposal at or before a round's first slot precedes its action.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_proposal_le_action {s : Slot} {r : Nat} (h : s ≤ r * p.R) :
    SA.proposalTime p.toParams s ≤ p.actionTime r :=
  FGCompose.kmid_proposal_le_action (d7m_timing p) (d7m_timing_laws p) h

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:886–915,1199–1211. Rows of an action are received before a proposal κ slots later.
DC: INTENTIONAL: the W kernel uses the row delay ΔF. -/
theorem kmid_batch_horizon {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {r : Nat} {s : Slot}
    (hG : E.t_GST ≤ p.actionTime r) (hs : r * p.R + kappaF p ΔF ≤ s)
    (hs' : s ≤ (pt.r + 2) * p.R) :
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ rho.horizon :=
  FGCompose.kmid_batch_horizon (d7m_timing p) (d7m_timing_laws p)
    (kmid_kernel_bounds hK).1 (kmid_kernel_bounds hK).2.2.2.2.2.2 hG hs hs'

end AvailableChain.FGSA.Run
end
