module
public import AvailableChainFGSA.Statements.WindowHeight -- shake: keep (re-export)
public import AvailableChainKitFG.HeightLaws -- shake: keep (re-export)
public import AvailableChainKitFG.WindowHeightBridge
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev hb_Old := FGSA.Window.State
private abbrev hb_New := SimplexFG.Window.State

private def hb_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def hb_toWindow {V : Type} (w : hb_Old V) : hb_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map hb_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem hb_entry_eq {V : Type} (e : Entry V) :
    hb_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem hb_state_eq {V : Type} (w : hb_Old V) :
    hb_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map hb_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem hb_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (hb_toEntry e).j = e.j ∧ (hb_toEntry e).X = e.X ∧ (hb_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem hb_state_fields {V : Type} (w : hb_Old V) :
    (hb_toWindow w).L = w.L ∧ (hb_toWindow w).s = w.s ∧
    (hb_toWindow w).h = w.h ∧ (hb_toWindow w).T_h = w.T_h ∧
    (hb_toWindow w).target_participation = w.target_participation ∧
    (hb_toWindow w).progress = w.progress ∧ (hb_toWindow w).W = w.W.map hb_toEntry ∧
    (hb_toWindow w).J = w.J ∧ (hb_toWindow w).h_j = w.h_j ∧
    (hb_toWindow w).F = w.F ∧ (hb_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hb_initial_eq {V : Type} :
    hb_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem hb_row_eq (w : hb_Old V) (a : Row V) :
    hb_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (hb_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map hb_toEntry =
      (w.W.map hb_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [hb_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, hb_state_eq] using
        congrArg (fun es => ({ hb_toWindow w with W := es } : hb_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [hb_state_eq] <;> rw [bits] <;> simp_all [hb_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem hb_rows_eq (rs : List (Row V)) (w : hb_Old V) :
    hb_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (hb_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, hb_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem hb_advance_eq (w : hb_Old V) :
    hb_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (hb_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem hb_greatest_eq (E : Electorate V) (w : hb_Old V) :
    (FGSA.Window.greatestReady E w).map hb_toEntry =
      SimplexFG.Window.greatestReady E (hb_toWindow w) := by
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
      (oldStep best e).map hb_toEntry = newStep (best.map hb_toEntry) (hb_toEntry e) := by
    dsimp [oldStep, newStep, hb_entry_eq]
    split_ifs <;> cases best <;> simp_all [hb_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map hb_toEntry =
        (es.map hb_toEntry).foldl newStep (best.map hb_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (hb_toWindow w) =
      (w.W.map hb_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem hb_finalize_eq (E : Electorate V) (w : hb_Old V) :
    hb_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (hb_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← hb_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [hb_state_eq, hb_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem hb_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map hb_toEntry =
      (es.map hb_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map hb_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, hb_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem hb_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : hb_Old V) :
    hb_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (hb_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← hb_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change hb_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (hb_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      hb_state_eq, hb_entry_eq, List.map_drop]

private theorem hb_transition_eq (p : Params) (K : Nat) (w : hb_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    hb_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (hb_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, hb_events_eq, SimplexFG.Window.transition_def]
  have h := hb_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { hb_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem hb_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) hb_toWindow where
  initial := hb_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := hb_transition_eq p K

private theorem hb_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    hb_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (hb_foldMap p K).fold_eq B

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- The old height projection reads the same eight copied fields. -/
private theorem hb_project_eq (w : hb_Old V) :
    projectHeight w = KitFG.Window.projectHeight (hb_toWindow w) := rfl

/-- [bp.heightBridge.v1] The raw window evaluator refines the height fold
on the same block tree. Capacity does not affect this projection. -/
theorem heightRefinement (p : Params) (K : Nat) (hK : 2 ≤ K) :
    HeightFoldRefinement p.E p.cfg projectHeight initial (transition p K) (derive p K) := by
  have h := KitFG.Window.heightRefinement p.E p.cfg K hK
  refine ⟨?_, rfl, fun _ _ _ _ _ => rfl, ?_⟩
  · exact h.initial_height
  · intro w σ B rs heq
    rw [hb_project_eq, hb_transition_eq]
    exact h.step_height (hb_toWindow w) σ B rs heq

/-- [bp.heightBridge.v1] Lift the step refinement over the original tree. -/
theorem windowHeightBridge (p : Params) (K : Nat) (hK : 2 ≤ K) :
    HeightBridge p.E p.cfg (fun B => projectHeight (derive p K B)) := by
  intro B
  simpa only [← hb_derive_eq, ← hb_project_eq] using
    KitFG.Window.windowHeightBridge p.E p.cfg K hK B

/-- The bridge transfers all height laws and their row certificates. -/
theorem windowHeightLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGHeightLaws p.E (fun B => projectHeight (derive p K B)) := by
  have heq : (fun B => projectHeight (derive p K B)) =
      (fun B => KitFG.Window.projectHeight (SimplexFG.Window.derive p.E p.cfg K B)) := by
    funext B
    rw [hb_project_eq, hb_derive_eq]
  rw [heq]
  exact KitFG.Window.windowHeightLaws p.E p.cfg K hK

#print axioms hb_entry_fields
#print axioms hb_state_fields
#print axioms hb_initial_eq
#print axioms hb_row_eq
#print axioms hb_rows_eq
#print axioms hb_advance_eq
#print axioms hb_greatest_eq
#print axioms hb_finalize_eq
#print axioms hb_append_eviction_eq
#print axioms hb_events_eq
#print axioms hb_transition_eq
#print axioms hb_foldMap
#print axioms hb_derive_eq
#print axioms hb_project_eq

#print axioms hb_entry_eq
#print axioms hb_state_eq

end AvailableChain.FGSA.Window
end
