module
public import AvailableChainFGSA.Proofs.WindowRetention -- shake: keep (re-export)
public import AvailableChainFGSA.Statements.WindowEntries
public import AvailableChainFGSA.Statements.FinalityView

public import AvailableChainKitFG.WindowTerminal
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

section

private abbrev b3terminal_Old := FGSA.Window.State
private abbrev b3terminal_New := SimplexFG.Window.State

private def b3terminal_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def b3terminal_toWindow {V : Type} (w : b3terminal_Old V) : b3terminal_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map b3terminal_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem b3terminal_entry_eq {V : Type} (e : Entry V) :
    b3terminal_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem b3terminal_state_eq {V : Type} (w : b3terminal_Old V) :
    b3terminal_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map b3terminal_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem b3terminal_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (b3terminal_toEntry e).j = e.j ∧ (b3terminal_toEntry e).X = e.X ∧ (b3terminal_toEntry e).Q =
      e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem b3terminal_state_fields {V : Type} (w : b3terminal_Old V) :
    (b3terminal_toWindow w).L = w.L ∧ (b3terminal_toWindow w).s = w.s ∧
    (b3terminal_toWindow w).h = w.h ∧ (b3terminal_toWindow w).T_h = w.T_h ∧
    (b3terminal_toWindow w).target_participation = w.target_participation ∧
    (b3terminal_toWindow w).progress = w.progress ∧ (b3terminal_toWindow w).W = w.W.map
      b3terminal_toEntry ∧
    (b3terminal_toWindow w).J = w.J ∧ (b3terminal_toWindow w).h_j = w.h_j ∧
    (b3terminal_toWindow w).F = w.F ∧ (b3terminal_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem b3terminal_initial_eq {V : Type} :
    b3terminal_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3terminal_row_eq (w : b3terminal_Old V) (a : Row V) :
    b3terminal_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (b3terminal_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map b3terminal_toEntry =
      (w.W.map b3terminal_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [b3terminal_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, b3terminal_state_eq] using
        congrArg (fun es => ({ b3terminal_toWindow w with W := es } : b3terminal_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [b3terminal_state_eq] <;> rw [bits] <;> simp_all [b3terminal_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem b3terminal_rows_eq (rs : List (Row V)) (w : b3terminal_Old V) :
    b3terminal_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (b3terminal_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, b3terminal_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3terminal_advance_eq (w : b3terminal_Old V) :
    b3terminal_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (b3terminal_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3terminal_greatest_eq (E : Electorate V) (w : b3terminal_Old V) :
    (FGSA.Window.greatestReady E w).map b3terminal_toEntry =
      SimplexFG.Window.greatestReady E (b3terminal_toWindow w) := by
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
      (oldStep best e).map b3terminal_toEntry = newStep (best.map b3terminal_toEntry)
      (b3terminal_toEntry e) := by
    dsimp [oldStep, newStep, b3terminal_entry_eq]
    split_ifs <;> cases best <;> simp_all [b3terminal_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map b3terminal_toEntry =
        (es.map b3terminal_toEntry).foldl newStep (best.map b3terminal_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (b3terminal_toWindow w) =
      (w.W.map b3terminal_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem b3terminal_finalize_eq (E : Electorate V) (w : b3terminal_Old V) :
    b3terminal_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (b3terminal_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← b3terminal_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [b3terminal_state_eq, b3terminal_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem b3terminal_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map b3terminal_toEntry =
      (es.map b3terminal_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map b3terminal_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, b3terminal_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3terminal_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      b3terminal_Old V) :
    b3terminal_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (b3terminal_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← b3terminal_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change b3terminal_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (b3terminal_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      b3terminal_state_eq, b3terminal_entry_eq, List.map_drop]

private theorem b3terminal_transition_eq (p : Params) (K : Nat) (w : b3terminal_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    b3terminal_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (b3terminal_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, b3terminal_events_eq, SimplexFG.Window.transition_def]
  have h := b3terminal_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { b3terminal_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem b3terminal_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) b3terminal_toWindow where
  initial := b3terminal_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := b3terminal_transition_eq p K

private theorem b3terminal_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3terminal_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (b3terminal_foldMap p K).fold_eq B

end

private theorem b3terminal_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem b3terminal_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (b3terminal_toWindow (derive p K B)) = _
  rw [b3terminal_derive_eq, KitFG.Window.certificateHeight_def]

private theorem b3terminal_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (b3terminal_toWindow (derive p K B)) = _
  rw [b3terminal_derive_eq, KitFG.Window.certificateFinality_def]

private theorem b3terminal_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3terminal_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { b3terminal_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [b3terminal_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { b3terminal_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [b3terminal_derive_eq]

private theorem b3terminal_exists_map {V : Type} (xs : List (Entry V))
    (P : SimplexFG.Window.Entry V → Prop) :
    (∃ e ∈ xs.map b3terminal_toEntry, P e) ↔ ∃ e ∈ xs, P (b3terminal_toEntry e) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hp⟩; exact ⟨d, hd, hp⟩
  · rintro ⟨d, hd, hp⟩; exact ⟨b3terminal_toEntry d, ⟨d, hd, rfl⟩, hp⟩

private theorem b3terminal_filter_length {V : Type} (xs : List (Entry V)) (y : Nat) :
    ((xs.map b3terminal_toEntry).filter (fun e => decide (y < e.j))).length =
      (xs.filter (fun e => decide (y < e.j))).length := by
  rw [List.filter_map]
  delta b3terminal_toEntry
  simp only [Function.comp_def, List.length_map]

private theorem b3terminal_r6w_eq {V : Type} [RowCodec V]
    (w : State V) (a : Row V) :
    SimplexFG.Window.r6w (b3terminal_toWindow w) a = r6w w a := by
  delta SimplexFG.Window.r6w r6w SimplexFG.Window.heightMatch heightMatch
    SimplexFG.Window.staleUseful staleUseful SimplexFG.Window.windowMatch windowMatch
  rcases a with ⟨i, hp, fp⟩
  cases hp <;> cases fp <;> dsimp only <;>
    simp only [b3terminal_state_eq, List.any_map, Function.comp_def, b3terminal_entry_eq]
  all_goals rfl

private theorem b3terminal_mem_map {V : Type} (e : Entry V) (xs : List (Entry V)) :
    b3terminal_toEntry e ∈ xs.map b3terminal_toEntry ↔ e ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, eq⟩
    have same : d = e := by cases d; cases e; cases eq; rfl
    exact same ▸ hd
  · intro he; exact ⟨e, he, rfl⟩

/-- Terminal scalar bounds at the active finality and height views preserve
the key. The supplier uses the bounds at each intermediate child. -/
theorem terminal_retained_scalarW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (above : (finalityView p P).h_F < y)
    (near : (heightView p P).h_j < y + p.K_W) : RetainedW p P y U := by
  have result := KitFG.Window.terminal_retained_scalarW p.E
    p.cfg
    p.K_W
    (b3terminal_empty_not_quorum p)
    p.kWLarge
    A
    P
    hAP
    y
    U
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using retained)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using near)
  simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- Fewer than K newer births up to the terminal parent preserve the key.
The finite set can overestimate the births; certificate heights need no gap bound. -/
theorem terminal_retained_birthsW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (above : (finalityView p P).h_F < y)
    (births : Finset (FGBlock (Fin p.n))) (few : births.card < p.K_W)
    (cover : ∀ C j X, FGBlock.Preceq C P → y < j →
      JustificationBirth p.E (certificateHeight p p.K_W) C j X → C ∈ births) :
    RetainedW p P y U := by
  have result := KitFG.Window.terminal_retained_birthsW p.E
    p.cfg
    p.K_W
    (b3terminal_empty_not_quorum p)
    p.kWLarge
    A
    P
    hAP
    y
    U
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using retained)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    births
    few
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using cover)
  simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- A finality deletion covers the key. The same scalar bound also excludes
capacity eviction, without a premise that finality stays below the key. -/
theorem terminal_retained_or_coveredW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (near : (heightView p P).h_j < y + p.K_W) :
    RetainedW p P y U ∨ CoveredW p P y U := by
  have result := KitFG.Window.terminal_retained_or_coveredW p.E
    p.cfg
    p.K_W
    (b3terminal_empty_not_quorum p)
    p.kWLarge
    A
    P
    hAP
    y
    U
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using retained)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using near)
  simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- The paper causal cap permits at most one greater certificate height.
The active window's capacity and retained-or-covered supplier close F8-W. -/
theorem terminalRetentionW (p : Params) :
    ∀ (A P : FGBlock (Fin p.n)) (d : Nat) (U : FGBlock (Fin p.n))
      (q : Nat) (terminal : Time),
      FGBlock.Preceq A P → RetainedW p A (d + 1) U →
      ((heightView p A).h_j, (heightView p A).J) = (d + 1, U) →
      terminal < p.actionTime (q + 1) →
      (terminal < p.actionTime (q + 1) → (heightView p P).h ≤ d + 3) →
      RetainedW p P (d + 1) U ∨ CoveredW p P (d + 1) U := by
  intro A P d U q terminal ancestry retained latest noNext causal
  have result := KitFG.Window.terminalRetentionW p.E p.cfg p.K_W
    (b3terminal_empty_not_quorum p) p.kWLarge A P d U ancestry
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using retained)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using latest)
    (by simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using causal noNext)
  simpa only [KitFG.Window.RetainedW_def, KitFG.Window.CoveredW_def,
    KitFG.Window.EntryBitW_def, RetainedW_def, CoveredW_def, EntryBitW_def,
    heightView_def, finalityView_def, certificateHeight_def, projectHeight_def,
    ← b3terminal_derive_eq, ← b3terminal_height_eq, ←
      b3terminal_finality_eq,
    ← b3terminal_folded_eq, ← b3terminal_finalize_eq, b3terminal_state_fields,
    b3terminal_entry_fields,
    b3terminal_mem_map, b3terminal_exists_map, List.forall_mem_map, b3terminal_filter_length,
      List.length_map,
    b3terminal_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

#print axioms b3terminal_toEntry
#print axioms b3terminal_toWindow
#print axioms b3terminal_entry_eq
#print axioms b3terminal_state_eq
#print axioms b3terminal_entry_fields
#print axioms b3terminal_state_fields
#print axioms b3terminal_initial_eq
#print axioms b3terminal_row_eq
#print axioms b3terminal_rows_eq
#print axioms b3terminal_advance_eq
#print axioms b3terminal_greatest_eq
#print axioms b3terminal_finalize_eq
#print axioms b3terminal_append_eviction_eq
#print axioms b3terminal_events_eq
#print axioms b3terminal_transition_eq
#print axioms b3terminal_foldMap
#print axioms b3terminal_derive_eq
#print axioms b3terminal_empty_not_quorum
#print axioms b3terminal_height_eq
#print axioms b3terminal_finality_eq
#print axioms b3terminal_folded_eq
#print axioms b3terminal_exists_map
#print axioms b3terminal_filter_length
#print axioms b3terminal_r6w_eq
#print axioms b3terminal_mem_map

end AvailableChain.FGSA.Window
end
