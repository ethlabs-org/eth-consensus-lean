module
public import AvailableChainFGSA.Statements.WindowCertificate -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.WindowInvariant -- shake: keep (re-export)

public import AvailableChainKitFG.WindowCertificates
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

section

private abbrev wcert_Old := FGSA.Window.State
private abbrev wcert_New := SimplexFG.Window.State

private def wcert_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def wcert_toWindow {V : Type} (w : wcert_Old V) : wcert_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map wcert_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem wcert_entry_eq {V : Type} (e : Entry V) :
    wcert_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem wcert_state_eq {V : Type} (w : wcert_Old V) :
    wcert_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map wcert_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem wcert_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (wcert_toEntry e).j = e.j ∧ (wcert_toEntry e).X = e.X ∧ (wcert_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem wcert_state_fields {V : Type} (w : wcert_Old V) :
    (wcert_toWindow w).L = w.L ∧ (wcert_toWindow w).s = w.s ∧
    (wcert_toWindow w).h = w.h ∧ (wcert_toWindow w).T_h = w.T_h ∧
    (wcert_toWindow w).target_participation = w.target_participation ∧
    (wcert_toWindow w).progress = w.progress ∧ (wcert_toWindow w).W = w.W.map wcert_toEntry ∧
    (wcert_toWindow w).J = w.J ∧ (wcert_toWindow w).h_j = w.h_j ∧
    (wcert_toWindow w).F = w.F ∧ (wcert_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wcert_initial_eq {V : Type} :
    wcert_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem wcert_row_eq (w : wcert_Old V) (a : Row V) :
    wcert_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (wcert_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map wcert_toEntry =
      (w.W.map wcert_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [wcert_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, wcert_state_eq] using
        congrArg (fun es => ({ wcert_toWindow w with W := es } : wcert_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [wcert_state_eq] <;> rw [bits] <;> simp_all [wcert_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem wcert_rows_eq (rs : List (Row V)) (w : wcert_Old V) :
    wcert_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (wcert_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, wcert_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wcert_advance_eq (w : wcert_Old V) :
    wcert_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (wcert_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem wcert_greatest_eq (E : Electorate V) (w : wcert_Old V) :
    (FGSA.Window.greatestReady E w).map wcert_toEntry =
      SimplexFG.Window.greatestReady E (wcert_toWindow w) := by
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
      (oldStep best e).map wcert_toEntry = newStep (best.map wcert_toEntry) (wcert_toEntry e) := by
    dsimp [oldStep, newStep, wcert_entry_eq]
    split_ifs <;> cases best <;> simp_all [wcert_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map wcert_toEntry =
        (es.map wcert_toEntry).foldl newStep (best.map wcert_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (wcert_toWindow w) =
      (w.W.map wcert_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem wcert_finalize_eq (E : Electorate V) (w : wcert_Old V) :
    wcert_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (wcert_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← wcert_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [wcert_state_eq, wcert_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem wcert_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map wcert_toEntry =
      (es.map wcert_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map wcert_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, wcert_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wcert_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : wcert_Old V) :
    wcert_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (wcert_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← wcert_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change wcert_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (wcert_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      wcert_state_eq, wcert_entry_eq, List.map_drop]

private theorem wcert_transition_eq (p : Params) (K : Nat) (w : wcert_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    wcert_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (wcert_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, wcert_events_eq, SimplexFG.Window.transition_def]
  have h := wcert_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { wcert_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem wcert_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) wcert_toWindow where
  initial := wcert_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := wcert_transition_eq p K

private theorem wcert_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wcert_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (wcert_foldMap p K).fold_eq B

end

private theorem wcert_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem wcert_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (wcert_toWindow (derive p K B)) = _
  rw [wcert_derive_eq, KitFG.Window.certificateHeight_def]

private theorem wcert_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (wcert_toWindow (derive p K B)) = _
  rw [wcert_derive_eq, KitFG.Window.certificateFinality_def]

private theorem wcert_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wcert_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { wcert_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [wcert_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { wcert_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [wcert_derive_eq]

/-- Birth uses only the height fields supplied by the landed bridge. -/
theorem justificationBirth_window_iff_simplex (p : Params) (K : Nat) (hK : 2 ≤ K)
    (C : FGBlock (Fin p.n)) (j : Height) (X : FGBlock (Fin p.n)) :
    JustificationBirth p.E (certificateHeight p K) C j X ↔
      JustificationBirth p.E (simplexHeightView p.E p.cfg) C j X := by
  simpa only [← wcert_height_eq, ← wcert_finality_eq] using
    KitFG.Window.justificationBirth_window_iff_simplex p.E p.cfg K hK C j X

/-- [bp §3.1–3.2] Every retained entry has a birth on this chain and exact
finality rows strictly after that birth. A new entry has no bits. -/
theorem window_entry_origin (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n))
    (he : e ∈ (derive p K B).W) : EntryOriginAt p K B e := by
  have hm : wcert_toEntry e ∈ (SimplexFG.Window.derive p.E p.cfg K B).W := by
    rw [← wcert_derive_eq]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  simpa only [KitFG.Window.EntryOriginAt_def, EntryOriginAt_def,
    ← wcert_height_eq, wcert_entry_eq] using
    KitFG.Window.window_entry_origin p.E p.cfg K hK B (wcert_toEntry e) hm

/-- [spec 1220–1227] An entry available to finality was born strictly
before this block; rows in its birth block cannot set its bits. -/
theorem window_prefinal_entry_origin (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n))
    (he : e ∈ (certificateFolded p K B).W) :
    ∃ C, StrictPrefix C B ∧
      JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have hm : wcert_toEntry e ∈ (KitFG.Window.certificateFolded p.E p.cfg K B).W := by
    rw [← wcert_folded_eq]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  simpa only [KitFG.Window.EntryOriginAt_def, EntryOriginAt_def,
    ← wcert_height_eq, wcert_entry_eq] using
    KitFG.Window.window_prefinal_entry_origin p.E p.cfg K hK B (wcert_toEntry e) hm

#print axioms wcert_entry_eq
#print axioms wcert_state_eq
#print axioms wcert_entry_fields
#print axioms wcert_state_fields
#print axioms wcert_initial_eq
#print axioms wcert_row_eq
#print axioms wcert_rows_eq
#print axioms wcert_advance_eq
#print axioms wcert_greatest_eq
#print axioms wcert_finalize_eq
#print axioms wcert_append_eviction_eq
#print axioms wcert_events_eq
#print axioms wcert_transition_eq
#print axioms wcert_foldMap
#print axioms wcert_derive_eq
#print axioms wcert_empty_not_quorum
#print axioms wcert_height_eq
#print axioms wcert_finality_eq
#print axioms wcert_folded_eq

end AvailableChain.FGSA.Window
end
