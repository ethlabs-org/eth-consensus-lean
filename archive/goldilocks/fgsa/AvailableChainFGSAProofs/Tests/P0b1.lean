module
public import AvailableChainFGSA.Model.WindowStore
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainKitFG.WindowTransport
public import AvailableChainSimplexFG.WindowStore

set_option linter.privateModule false

namespace AvailableChain.FGSA.Tests.P0b1

open AvailableChain.SimplexFG

private abbrev Old := FGSA.Window.State
private abbrev New := SimplexFG.Window.State

private def toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def toWindow {V : Type} (w : Old V) : New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (toEntry e).j = e.j ∧ (toEntry e).X = e.X ∧ (toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem state_fields {V : Type} (w : Old V) :
    (toWindow w).L = w.L ∧ (toWindow w).s = w.s ∧
    (toWindow w).h = w.h ∧ (toWindow w).T_h = w.T_h ∧
    (toWindow w).target_participation = w.target_participation ∧
    (toWindow w).progress = w.progress ∧ (toWindow w).W = w.W.map toEntry ∧
    (toWindow w).J = w.J ∧ (toWindow w).h_j = w.h_j ∧
    (toWindow w).F = w.F ∧ (toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem initial_eq {V : Type} :
    toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem row_eq (w : Old V) (a : Row V) :
    toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map toEntry =
      (w.W.map toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [toEntry, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row, SimplexFG.Window.process_row,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, toWindow] using
        congrArg (fun es => ({ toWindow w with W := es } : New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row, SimplexFG.Window.process_row,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [toWindow] <;> rw [bits] <;> simp_all [toWindow]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem rows_eq (rs : List (Row V)) (w : Old V) :
    toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem advance_eq (w : Old V) :
    toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem greatest_eq (E : Electorate V) (w : Old V) :
    (FGSA.Window.greatestReady E w).map toEntry =
      SimplexFG.Window.greatestReady E (toWindow w) := by
  classical
  let oldStep := fun (best : Option (FGSA.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best
  let newStep := fun (best : Option (SimplexFG.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best
  have step (best) (e) :
      (oldStep best e).map toEntry = newStep (best.map toEntry) (toEntry e) := by
    dsimp [oldStep, newStep, toEntry]
    split_ifs <;> cases best <;> simp_all [toEntry]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map toEntry =
        (es.map toEntry).foldl newStep (best.map toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  convert fold w.W none using 1 <;>
    simp only [FGSA.Window.greatestReady, SimplexFG.Window.greatestReady, toWindow]
  · congr 2
    funext best e
    cases best <;> rfl
  · congr 1
    funext best e
    cases best <;> rfl

omit [DecidableEq V] [RowCodec V] in
private theorem finalize_eq (E : Electorate V) (w : Old V) :
    toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (toWindow w) := by
  unfold FGSA.Window.finalizeWindow SimplexFG.Window.finalizeWindow
  rw [← greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [toWindow, toEntry, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map toEntry =
      (es.map toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, toEntry]

omit [DecidableEq V] [RowCodec V] in
private theorem events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : Old V) :
    toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (toWindow w) := by
  unfold FGSA.Window.process_height_events SimplexFG.Window.process_height_events
  rw [← finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height, SimplexFG.Window.advance_height,
      toWindow, toEntry, List.map_drop]

private theorem transition_eq (p : Params) (K : Nat) (w : Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (toWindow w) B rs := by
  rw [FGSA.Window.transition_def, events_eq, SimplexFG.Window.transition_def]
  have h := rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) toWindow where
  initial := initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := transition_eq p K

private theorem derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (foldMap p K).fold_eq B

private theorem p0b1_height_eq (p : Params) (B : FGBlock (Fin p.n)) :
    FGSA.heightView p B = KitFG.Window.heightView p.E p.cfg p.K_W B :=
  (foldMap p p.K_W).foldMap_height_eq B

private theorem p0b1_finality_eq (p : Params) (B : FGBlock (Fin p.n)) :
    FGSA.finalityView p B = KitFG.Window.finalityView p.E p.cfg p.K_W B :=
  (foldMap p p.K_W).foldMap_finality_eq B

private theorem accept_eq (p : Params) (K : Nat) (st : Store (Fin p.n)) :
    FGSA.Window.acceptViable p K st = SimplexFG.Window.acceptViable p.E p.cfg K st := by
  simp only [FGSA.Window.acceptViable, SimplexFG.Window.acceptViable, ← derive_eq, toWindow]

private theorem update_eq (p : Params) (K : Nat)
    (st : Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    FGSA.Window.update_finality p K st B =
      SimplexFG.Window.update_finality p.E p.cfg K st B := by
  simp only [FGSA.Window.update_finality, SimplexFG.Window.update_finality,
    ← derive_eq, toWindow, ← accept_eq]

private theorem on_block_eq (p : Params) (K : Nat)
    (st : Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    FGSA.Window.on_block p K st B = SimplexFG.Window.on_block p.E p.cfg K st B := by
  simp only [FGSA.Window.on_block, SimplexFG.Window.on_block, ← update_eq]

#print axioms entry_fields
#print axioms state_fields
#print axioms initial_eq
#print axioms row_eq
#print axioms rows_eq
#print axioms advance_eq
#print axioms greatest_eq
#print axioms finalize_eq
#print axioms append_eviction_eq
#print axioms events_eq
#print axioms transition_eq
#print axioms foldMap
#print axioms derive_eq
#print axioms p0b1_height_eq
#print axioms p0b1_finality_eq
#print axioms accept_eq
#print axioms update_eq
#print axioms on_block_eq

end AvailableChain.FGSA.Tests.P0b1
