module
public import AvailableChainFGSA.Proofs.WindowCertificates -- shake: keep (re-export)
public import AvailableChainKitFG.SelectionCore -- shake: keep (re-export)

public import AvailableChainKitFG.WindowSelection
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

section

private abbrev wsel_Old := FGSA.Window.State
private abbrev wsel_New := SimplexFG.Window.State

private def wsel_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def wsel_toWindow {V : Type} (w : wsel_Old V) : wsel_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map wsel_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem wsel_entry_eq {V : Type} (e : Entry V) :
    wsel_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem wsel_state_eq {V : Type} (w : wsel_Old V) :
    wsel_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map wsel_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem wsel_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (wsel_toEntry e).j = e.j ∧ (wsel_toEntry e).X = e.X ∧ (wsel_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem wsel_state_fields {V : Type} (w : wsel_Old V) :
    (wsel_toWindow w).L = w.L ∧ (wsel_toWindow w).s = w.s ∧
    (wsel_toWindow w).h = w.h ∧ (wsel_toWindow w).T_h = w.T_h ∧
    (wsel_toWindow w).target_participation = w.target_participation ∧
    (wsel_toWindow w).progress = w.progress ∧ (wsel_toWindow w).W = w.W.map wsel_toEntry ∧
    (wsel_toWindow w).J = w.J ∧ (wsel_toWindow w).h_j = w.h_j ∧
    (wsel_toWindow w).F = w.F ∧ (wsel_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wsel_initial_eq {V : Type} :
    wsel_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem wsel_row_eq (w : wsel_Old V) (a : Row V) :
    wsel_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (wsel_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map wsel_toEntry =
      (w.W.map wsel_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [wsel_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, wsel_state_eq] using
        congrArg (fun es => ({ wsel_toWindow w with W := es } : wsel_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [wsel_state_eq] <;> rw [bits] <;> simp_all [wsel_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem wsel_rows_eq (rs : List (Row V)) (w : wsel_Old V) :
    wsel_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (wsel_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, wsel_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wsel_advance_eq (w : wsel_Old V) :
    wsel_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (wsel_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem wsel_greatest_eq (E : Electorate V) (w : wsel_Old V) :
    (FGSA.Window.greatestReady E w).map wsel_toEntry =
      SimplexFG.Window.greatestReady E (wsel_toWindow w) := by
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
      (oldStep best e).map wsel_toEntry = newStep (best.map wsel_toEntry) (wsel_toEntry e) := by
    dsimp [oldStep, newStep, wsel_entry_eq]
    split_ifs <;> cases best <;> simp_all [wsel_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map wsel_toEntry =
        (es.map wsel_toEntry).foldl newStep (best.map wsel_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (wsel_toWindow w) =
      (w.W.map wsel_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem wsel_finalize_eq (E : Electorate V) (w : wsel_Old V) :
    wsel_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (wsel_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← wsel_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [wsel_state_eq, wsel_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem wsel_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map wsel_toEntry =
      (es.map wsel_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map wsel_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, wsel_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wsel_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : wsel_Old V) :
    wsel_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (wsel_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← wsel_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change wsel_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (wsel_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      wsel_state_eq, wsel_entry_eq, List.map_drop]

private theorem wsel_transition_eq (p : Params) (K : Nat) (w : wsel_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    wsel_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (wsel_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, wsel_events_eq, SimplexFG.Window.transition_def]
  have h := wsel_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { wsel_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem wsel_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) wsel_toWindow where
  initial := wsel_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := wsel_transition_eq p K

private theorem wsel_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wsel_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (wsel_foldMap p K).fold_eq B

end

private theorem wsel_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem wsel_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (wsel_toWindow (derive p K B)) = _
  rw [wsel_derive_eq, KitFG.Window.certificateHeight_def]

private theorem wsel_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (wsel_toWindow (derive p K B)) = _
  rw [wsel_derive_eq, KitFG.Window.certificateFinality_def]

private theorem wsel_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wsel_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { wsel_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [wsel_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { wsel_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [wsel_derive_eq]

private theorem wsel_selection_eq (p : Params) (K : Nat) :
    certificateSelection p K = KitFG.Window.certificateSelection p.E p.cfg K := by
  rw [certificateSelection_def, KitFG.Window.certificateSelection_def]
  congr 1
  · funext B
    rw [← wsel_folded_eq]
    simp only [wsel_state_eq, List.map_map, Function.comp_def,
      KitFG.Window.projectCertEntry_def, wsel_entry_eq]
    rfl
  · funext B
    rw [← wsel_folded_eq, ← wsel_greatest_eq]
    simp only [Option.map_map, Function.comp_def,
      KitFG.Window.projectCertEntry_def, wsel_entry_eq]
    rfl
  · funext B
    rw [← wsel_folded_eq, ← wsel_finalize_eq]
    simp only [wsel_state_eq, List.map_map, Function.comp_def,
      KitFG.Window.projectCertEntry_def, wsel_entry_eq]
    rfl

/-- [spec 1222–1227] The window supplies the core selection laws; KitFG derives coverage. -/
theorem windowSelectionLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGSelectionLaws p.E (certificateHeight p K) (certificateFinality p K)
      (certificateSelection p K) := by
  simpa only [← wsel_height_eq, ← wsel_finality_eq, ← wsel_selection_eq] using
    KitFG.Window.windowSelectionLaws p.E p.cfg K (wsel_empty_not_quorum p) hK

/-- [design §5] Height and finality bounds complete the generic certificate constructor. -/
theorem windowCertificateLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGCertificateLaws p.E (certificateHeight p K) (certificateFinality p K) := by
  simpa only [← wsel_height_eq, ← wsel_finality_eq, ← wsel_selection_eq] using
    KitFG.Window.windowCertificateLaws p.E p.cfg K (wsel_empty_not_quorum p) hK

/-- [design §5] Assemble the certificate and selection laws. -/
theorem windowChainCertificate (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGChainCertificate p.E (certificateHeight p K) (certificateFinality p K)
      (certificateSelection p K) := by
  simpa only [← wsel_height_eq, ← wsel_finality_eq, ← wsel_selection_eq] using
    KitFG.Window.windowChainCertificate p.E p.cfg K (wsel_empty_not_quorum p) hK

#print axioms wsel_entry_eq
#print axioms wsel_state_eq
#print axioms wsel_entry_fields
#print axioms wsel_state_fields
#print axioms wsel_initial_eq
#print axioms wsel_row_eq
#print axioms wsel_rows_eq
#print axioms wsel_advance_eq
#print axioms wsel_greatest_eq
#print axioms wsel_finalize_eq
#print axioms wsel_append_eviction_eq
#print axioms wsel_events_eq
#print axioms wsel_transition_eq
#print axioms wsel_foldMap
#print axioms wsel_derive_eq
#print axioms wsel_empty_not_quorum
#print axioms wsel_height_eq
#print axioms wsel_finality_eq
#print axioms wsel_folded_eq
#print axioms wsel_selection_eq

end AvailableChain.FGSA.Window
end
