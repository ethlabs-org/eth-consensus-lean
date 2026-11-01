module
public import AvailableChainFGSA.Proofs.WindowHeightBridge -- shake: keep (re-export)
public import AvailableChainFGSA.Statements.WindowCertificate
public import AvailableChainKitFG.FrameBridge -- shake: keep (re-export)
public import AvailableChainKitFG.ProvenanceCoreDef

public import AvailableChainKitFG.WindowReaders
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

section

private abbrev wread_Old := FGSA.Window.State
private abbrev wread_New := SimplexFG.Window.State

private def wread_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def wread_toWindow {V : Type} (w : wread_Old V) : wread_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map wread_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem wread_entry_eq {V : Type} (e : Entry V) :
    wread_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem wread_state_eq {V : Type} (w : wread_Old V) :
    wread_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map wread_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem wread_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (wread_toEntry e).j = e.j ∧ (wread_toEntry e).X = e.X ∧ (wread_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem wread_state_fields {V : Type} (w : wread_Old V) :
    (wread_toWindow w).L = w.L ∧ (wread_toWindow w).s = w.s ∧
    (wread_toWindow w).h = w.h ∧ (wread_toWindow w).T_h = w.T_h ∧
    (wread_toWindow w).target_participation = w.target_participation ∧
    (wread_toWindow w).progress = w.progress ∧ (wread_toWindow w).W = w.W.map wread_toEntry ∧
    (wread_toWindow w).J = w.J ∧ (wread_toWindow w).h_j = w.h_j ∧
    (wread_toWindow w).F = w.F ∧ (wread_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wread_initial_eq {V : Type} :
    wread_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem wread_row_eq (w : wread_Old V) (a : Row V) :
    wread_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (wread_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map wread_toEntry =
      (w.W.map wread_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [wread_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, wread_state_eq] using
        congrArg (fun es => ({ wread_toWindow w with W := es } : wread_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [wread_state_eq] <;> rw [bits] <;> simp_all [wread_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem wread_rows_eq (rs : List (Row V)) (w : wread_Old V) :
    wread_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (wread_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, wread_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wread_advance_eq (w : wread_Old V) :
    wread_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (wread_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem wread_greatest_eq (E : Electorate V) (w : wread_Old V) :
    (FGSA.Window.greatestReady E w).map wread_toEntry =
      SimplexFG.Window.greatestReady E (wread_toWindow w) := by
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
      (oldStep best e).map wread_toEntry = newStep (best.map wread_toEntry) (wread_toEntry e) := by
    dsimp [oldStep, newStep, wread_entry_eq]
    split_ifs <;> cases best <;> simp_all [wread_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map wread_toEntry =
        (es.map wread_toEntry).foldl newStep (best.map wread_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (wread_toWindow w) =
      (w.W.map wread_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem wread_finalize_eq (E : Electorate V) (w : wread_Old V) :
    wread_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (wread_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← wread_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [wread_state_eq, wread_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem wread_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map wread_toEntry =
      (es.map wread_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map wread_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, wread_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wread_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : wread_Old V) :
    wread_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (wread_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← wread_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change wread_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (wread_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      wread_state_eq, wread_entry_eq, List.map_drop]

private theorem wread_transition_eq (p : Params) (K : Nat) (w : wread_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    wread_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (wread_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, wread_events_eq, SimplexFG.Window.transition_def]
  have h := wread_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { wread_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem wread_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) wread_toWindow where
  initial := wread_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := wread_transition_eq p K

private theorem wread_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wread_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (wread_foldMap p K).fold_eq B

end

private theorem wread_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem wread_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (wread_toWindow (derive p K B)) = _
  rw [wread_derive_eq, KitFG.Window.certificateHeight_def]

private theorem wread_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (wread_toWindow (derive p K B)) = _
  rw [wread_derive_eq, KitFG.Window.certificateFinality_def]

variable (p : Params) (K : Nat)

/-- The window hOf read equals the old read on the same arguments. -/
theorem window_hOf_eq (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (projectHeight (derive p K B)).h =
      hOf p.E p.cfg B := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_hOf_eq p.E p.cfg K hK B

/-- The window frontier read equals the old read on the same arguments. -/
theorem window_frontier_eq (hK : 2 ≤ K) (blocks : View (Fin p.n)) :
    frontierView (fun B => projectHeight (derive p K B)) blocks =
      frontier p.E p.cfg blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_frontier_eq p.E p.cfg K hK blocks

/-- The window lexMax read equals the old read on the same arguments. -/
theorem window_lexMax_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    lexMaxView (fun B => projectHeight (derive p K B)) F blocks =
      lexMax p.E p.cfg F blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_lexMax_eq p.E p.cfg K hK F blocks

/-- The window filteredFrom read equals the old read on the same arguments. -/
theorem window_filteredFrom_eq (hK : 2 ≤ K) (c : Controls (Fin p.n))
    (blocks : Finset (FGBlock (Fin p.n))) :
    filteredFromView (fun B => projectHeight (derive p K B)) c blocks =
      filteredFrom p.E p.cfg c blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_filteredFrom_eq p.E p.cfg K hK c blocks

/-- The window storeControls read equals the old read on the same arguments. -/
theorem window_storeControls_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n)) :
    storeControlsView (fun B => projectHeight (derive p K B)) st =
      storeControls p.E p.cfg st := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_storeControls_eq p.E p.cfg K hK st

/-- The window storeFrame read equals the old read on the same arguments. -/
theorem window_storeFrame_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n))
    (blocks : Finset (FGBlock (Fin p.n))) :
    storeFrameView (fun B => projectHeight (derive p K B)) st blocks =
      storeFrame p.E p.cfg st blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_storeFrame_eq p.E p.cfg K hK st blocks

/-- The window fjControls read equals the old read on the same arguments. -/
theorem window_fjControls_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    fjControlsView (fun B => projectHeight (derive p K B)) F blocks =
      fjControls p.E p.cfg F blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_fjControls_eq p.E p.cfg K hK F blocks

/-- The window fjFrame read equals the old read on the same arguments. -/
theorem window_fjFrame_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    fjFrameView (fun B => projectHeight (derive p K B)) F blocks =
      fjFrame p.E p.cfg F blocks := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_fjFrame_eq p.E p.cfg K hK F blocks

/-- The direct window head fields equal the certificate head fields. -/
theorem headFields_eq_certificateHeadFields (Hd : FGBlock (Fin p.n)) :
    headFields p K Hd =
      certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd := by
  simpa only [← wread_height_eq, ← wread_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wread_derive_eq, wread_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def, KitFG.Window.headFields_def, headFields_def]
          using
    KitFG.Window.headFields_eq_certificateHeadFields p.E p.cfg K Hd

#print axioms wread_entry_eq
#print axioms wread_state_eq
#print axioms wread_entry_fields
#print axioms wread_state_fields
#print axioms wread_initial_eq
#print axioms wread_row_eq
#print axioms wread_rows_eq
#print axioms wread_advance_eq
#print axioms wread_greatest_eq
#print axioms wread_finalize_eq
#print axioms wread_append_eviction_eq
#print axioms wread_events_eq
#print axioms wread_transition_eq
#print axioms wread_foldMap
#print axioms wread_derive_eq
#print axioms wread_empty_not_quorum
#print axioms wread_height_eq
#print axioms wread_finality_eq

end AvailableChain.FGSA.Window
end
