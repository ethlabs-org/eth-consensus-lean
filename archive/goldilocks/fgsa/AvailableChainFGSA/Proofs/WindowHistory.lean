module
public import AvailableChainFGSA.Proofs.WindowCertificates -- shake: keep (re-export)

public import AvailableChainKitFG.WindowHistory
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

variable {V : Type} [DecidableEq V] [RowCodec V]

section

private abbrev b3history_Old := FGSA.Window.State
private abbrev b3history_New := SimplexFG.Window.State

private def b3history_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def b3history_toWindow {V : Type} (w : b3history_Old V) : b3history_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map b3history_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem b3history_entry_eq {V : Type} (e : Entry V) :
    b3history_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem b3history_state_eq {V : Type} (w : b3history_Old V) :
    b3history_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map b3history_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem b3history_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (b3history_toEntry e).j = e.j ∧ (b3history_toEntry e).X = e.X ∧ (b3history_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem b3history_state_fields {V : Type} (w : b3history_Old V) :
    (b3history_toWindow w).L = w.L ∧ (b3history_toWindow w).s = w.s ∧
    (b3history_toWindow w).h = w.h ∧ (b3history_toWindow w).T_h = w.T_h ∧
    (b3history_toWindow w).target_participation = w.target_participation ∧
    (b3history_toWindow w).progress = w.progress ∧ (b3history_toWindow w).W = w.W.map
      b3history_toEntry ∧
    (b3history_toWindow w).J = w.J ∧ (b3history_toWindow w).h_j = w.h_j ∧
    (b3history_toWindow w).F = w.F ∧ (b3history_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem b3history_initial_eq {V : Type} :
    b3history_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3history_row_eq (w : b3history_Old V) (a : Row V) :
    b3history_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (b3history_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map b3history_toEntry =
      (w.W.map b3history_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [b3history_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, b3history_state_eq] using
        congrArg (fun es => ({ b3history_toWindow w with W := es } : b3history_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [b3history_state_eq] <;> rw [bits] <;> simp_all [b3history_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem b3history_rows_eq (rs : List (Row V)) (w : b3history_Old V) :
    b3history_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (b3history_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, b3history_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3history_advance_eq (w : b3history_Old V) :
    b3history_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (b3history_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3history_greatest_eq (E : Electorate V) (w : b3history_Old V) :
    (FGSA.Window.greatestReady E w).map b3history_toEntry =
      SimplexFG.Window.greatestReady E (b3history_toWindow w) := by
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
      (oldStep best e).map b3history_toEntry = newStep (best.map b3history_toEntry)
      (b3history_toEntry e) := by
    dsimp [oldStep, newStep, b3history_entry_eq]
    split_ifs <;> cases best <;> simp_all [b3history_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map b3history_toEntry =
        (es.map b3history_toEntry).foldl newStep (best.map b3history_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (b3history_toWindow w) =
      (w.W.map b3history_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem b3history_finalize_eq (E : Electorate V) (w : b3history_Old V) :
    b3history_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (b3history_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← b3history_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [b3history_state_eq, b3history_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem b3history_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map b3history_toEntry =
      (es.map b3history_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map b3history_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, b3history_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3history_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      b3history_Old V) :
    b3history_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (b3history_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← b3history_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change b3history_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (b3history_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      b3history_state_eq, b3history_entry_eq, List.map_drop]

private theorem b3history_transition_eq (p : Params) (K : Nat) (w : b3history_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    b3history_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (b3history_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, b3history_events_eq, SimplexFG.Window.transition_def]
  have h := b3history_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { b3history_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem b3history_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) b3history_toWindow where
  initial := b3history_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := b3history_transition_eq p K

private theorem b3history_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3history_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (b3history_foldMap p K).fold_eq B

end

private theorem b3history_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem b3history_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (b3history_toWindow (derive p K B)) = _
  rw [b3history_derive_eq, KitFG.Window.certificateHeight_def]

private theorem b3history_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (b3history_toWindow (derive p K B)) = _
  rw [b3history_derive_eq, KitFG.Window.certificateFinality_def]

private theorem b3history_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3history_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { b3history_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [b3history_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { b3history_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [b3history_derive_eq]

private theorem b3history_exists_map {V : Type} (xs : List (Entry V))
    (P : SimplexFG.Window.Entry V → Prop) :
    (∃ e ∈ xs.map b3history_toEntry, P e) ↔ ∃ e ∈ xs, P (b3history_toEntry e) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hp⟩; exact ⟨d, hd, hp⟩
  · rintro ⟨d, hd, hp⟩; exact ⟨b3history_toEntry d, ⟨d, hd, rfl⟩, hp⟩

private theorem b3history_filter_length {V : Type} (xs : List (Entry V)) (y : Nat) :
    ((xs.map b3history_toEntry).filter (fun e => decide (y < e.j))).length =
      (xs.filter (fun e => decide (y < e.j))).length := by
  rw [List.filter_map]
  delta b3history_toEntry
  simp only [Function.comp_def, List.length_map]

private theorem b3history_r6w_eq {V : Type} [RowCodec V]
    (w : State V) (a : Row V) :
    SimplexFG.Window.r6w (b3history_toWindow w) a = r6w w a := by
  delta SimplexFG.Window.r6w r6w SimplexFG.Window.heightMatch heightMatch
    SimplexFG.Window.staleUseful staleUseful SimplexFG.Window.windowMatch windowMatch
  rcases a with ⟨i, hp, fp⟩
  cases hp <;> cases fp <;> dsimp only <;>
    simp only [b3history_state_eq, List.any_map, Function.comp_def, b3history_entry_eq]
  all_goals rfl

private theorem b3history_mem_map {V : Type} (e : Entry V) (xs : List (Entry V)) :
    b3history_toEntry e ∈ xs.map b3history_toEntry ↔ e ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, eq⟩
    have same : d = e := by cases d; cases e; cases eq; rfl
    exact same ▸ hd
  · intro he; exact ⟨e, he, rfl⟩

private theorem final_fields (p : Params) (w : State (Fin p.n)) :
    (finalizeWindow p.E w).h = w.h ∧
    (finalizeWindow p.E w).T_h = w.T_h ∧
    (finalizeWindow p.E w).h_j = w.h_j ∧
    (finalizeWindow p.E w).J = w.J ∧
    (finalizeWindow p.E w).W =
      w.W.filter (fun e => decide ((finalizeWindow p.E w).h_F < e.j)) := by
  rw [finalizeWindow_def]
  cases greatestReady p.E w <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem events_finality (p : Params) (K : Nat) (w : State (Fin p.n)) :
    (process_height_events p.E p.cfg K w).F = (finalizeWindow p.E w).F ∧
    (process_height_events p.E p.cfg K w).h_F = (finalizeWindow p.E w).h_F := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Every nonzero finalized pair was born on this chain, including pairs
whose older entries have already left the window. -/
theorem window_final_birth (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (hnz : (derive p K B).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C B ∧ JustificationBirth p.E (certificateHeight p K)
      C (derive p K B).h_F (derive p K B).F := by
  have result := KitFG.Window.window_final_birth p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    B
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hnz)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

private theorem birth_geometry (p : Params) (K : Nat) (hK : 2 ≤ K)
    {C X : FGBlock (Fin p.n)} {j : Height}
    (hb : JustificationBirth p.E (certificateHeight p K) C j X) :
    FGBlock.Preceq X C ∧ (certificateHeight p K X).h = j ∧
      (certificateHeight p K X).T_h = X := by
  have laws : FGHeightLaws p.E (certificateHeight p K) := windowHeightLaws p K hK
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb.2.2.1]
    apply preceq_trans (laws.entry_preceq C.parent)
    cases C with
    | genesis => exact preceq_refl _
    | node P s r_s x rs => exact preceq_parent_node P s r_s x rs
  · rw [← hb.2.2.1, laws.entry_same_height, hb.2.1]
  · rw [← hb.2.2.1, laws.entry_idem]

private theorem birth_order (p : Params) (K : Nat) (hK : 2 ≤ K)
    {B C D X Y : FGBlock (Fin p.n)} {j k : Height}
    (hC : FGBlock.Preceq C B) (hD : FGBlock.Preceq D B)
    (hbC : JustificationBirth p.E (certificateHeight p K) C j X)
    (hbD : JustificationBirth p.E (certificateHeight p K) D k Y)
    (hjk : j ≤ k) : FGBlock.Preceq X Y := by
  have c := birth_geometry p K hK hbC
  have d := birth_geometry p K hK hbD
  rcases preceq_total_of_common (preceq_trans c.1 hC) (preceq_trans d.1 hD) with h | h
  · exact h
  · have laws : FGHeightLaws p.E (certificateHeight p K) := windowHeightLaws p K hK
    have hm := laws.h_mono h
    have heq : (certificateHeight p K Y).h = (certificateHeight p K X).h := by
      change (certificateHeight p K Y).h ≤ (certificateHeight p K X).h at hm
      rw [d.2.1, c.2.1] at hm ⊢
      exact Nat.le_antisymm hm hjk
    have ht := laws.entry_plateau h heq
    change (certificateHeight p K Y).T_h = (certificateHeight p K X).T_h at ht
    rw [c.2.2, d.2.2] at ht
    rw [ht]
    exact preceq_refl _

/-- [bp §3.1; bp 22 I7] Every old key at or below finality is covered, even if
capacity removed it earlier. Birth order supplies the ancestry claim. -/
theorem window_le_hF_covered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (hle : e.j ≤ (derive p K B).h_F) : FGBlock.Preceq e.X (derive p K B).F := by
  have result := KitFG.Window.window_le_hF_covered p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    A
    B
    hAB
    (b3history_toEntry e)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hle)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- [bp §3.1; bp 22 I7] The absent-key form of `window_le_hF_covered`. Absence is
not used; the form matches the COVERED case of `window_entry_history`. -/
theorem window_absent_le_hF_covered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X)
    (hle : e.j ≤ (derive p K B).h_F) : FGBlock.Preceq e.X (derive p K B).F := by
  have result := KitFG.Window.window_absent_le_hF_covered p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    A
    B
    hAB
    (b3history_toEntry e)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using gone)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hle)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- At B an absent key that is not covered is strictly above finality.
This does not assert that it stays uncovered at later blocks. -/
theorem window_evicted_above_hF (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X)
    (uncovered : ¬ (e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F)) :
    (derive p K B).h_F < e.j := by
  have result := KitFG.Window.window_evicted_above_hF p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    A
    B
    hAB
    (b3history_toEntry e)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using gone)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using uncovered)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- [bp §3.1] Retention at both ends forbids a gap and preserves all bits. -/
theorem window_retained_bits_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B C : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) (hBC : FGBlock.Preceq B C)
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K A).W) (hd : d ∈ (derive p K C).W)
    (hj : d.j = e.j) (hX : d.X = e.X) :
    ∃ b ∈ (derive p K B).W, b.j = e.j ∧ b.X = e.X ∧ e.Q ⊆ b.Q ∧ b.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_bits_mono p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    A
    B
    C
    hAB
    hBC
    (b3history_toEntry e)
    (b3history_toEntry d)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hd)
    hj
    hX
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- [spec 605–607] A step keeps the latest pair unless it crosses a target
quorum. Pruning does not clear the pair; a capacity append writes a new pair. -/
theorem window_latest_pair_kept (p : Params) (K : Nat)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n))) :
    let B := FGBlock.node P s r_s x rs
    let w := certificateFolded p K B
    ((derive p K B).h_j = (derive p K P).h_j ∧
      (derive p K B).J = (derive p K P).J ∧
      targetQuorum p.E (finalizeWindow p.E w) = false) ∨
    ((derive p K B).h_j = (derive p K P).h ∧
      (derive p K B).J = (derive p K P).T_h ∧
      targetQuorum p.E (finalizeWindow p.E w) = true) := by
  have result := KitFG.Window.window_latest_pair_kept p.E
    p.cfg
    K
    P
    s
    r_s
    x
    rs
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

omit [RowCodec V] in
private theorem drop_oldest (K : Nat) (xs : List (Entry V))
    (new e : Entry V) (hcap : xs.length ≤ K)
    (hord : (xs ++ [new]).Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X))
    (he : e ∈ xs) (gone : e ∉ (xs ++ [new]).drop ((xs ++ [new]).length - K)) :
    ((xs ++ [new]).drop ((xs ++ [new]).length - K)).length = K ∧
    ∀ d ∈ (xs ++ [new]).drop ((xs ++ [new]).length - K), e.j < d.j := by
  have hlen : (xs ++ [new]).length = K + 1 := by
    simp only [List.length_append, List.length_singleton]
    by_contra h
    have hz : (xs ++ [new]).length - K = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    exact gone (by simpa only [hz, List.drop_zero] using List.mem_append_left [new] he)
  have hdrop : (xs ++ [new]).length - K = 1 := by omega
  rw [hdrop] at gone ⊢
  constructor
  · simp only [List.length_drop]; omega
  · cases xs with
    | nil => simp at he
    | cons a xs =>
        have hea : e = a := by
          rcases List.mem_cons.mp he with h | h
          · exact h
          · exact (gone (by simpa using List.mem_append_left [new] h)).elim
        subst e
        change (a :: (xs ++ [new])).Pairwise _ at hord
        exact fun d hd => ((List.pairwise_cons.mp hord).1 d hd).1

private theorem node_evicted (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (gone : ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive p K (.node P s r_s x rs)).h_F < e.j) :
    (derive p K (.node P s r_s x rs)).W.length = K ∧
    ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j := by
  let B := FGBlock.node P s r_s x rs
  let w := certificateFolded p K B
  let f := finalizeWindow p.E w
  let d := rs.foldl (fun e a => window_addBit a e) e
  have ff := window_fold_fields rs { derive p K P with s := s }
  have dk := window_fold_entry rs e
  have fin := final_fields p w
  have ef := events_finality p K w
  have dw : d ∈ w.W := by
    change d ∈ (rs.foldl process_row { derive p K P with s := s }).W
    rw [ff.1]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have df : d ∈ f.W := by
    rw [fin.2.2.2.2, List.mem_filter]
    refine ⟨dw, decide_eq_true ?_⟩
    rw [← ef.2, dk.1]
    exact above
  have cap : f.W.length ≤ K := by
    rw [fin.2.2.2.2]
    refine (List.length_filter_le _ _).trans ?_
    change (rs.foldl process_row { derive p K P with s := s }).W.length ≤ K
    rw [ff.1, List.length_map]
    exact window_capacity p K hK P
  have ord : f.W.Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [fin.2.2.2.2]
    apply List.Pairwise.filter
    change (rs.foldl process_row { derive p K P with s := s }).W.Pairwise _
    rw [ff.1, List.pairwise_map]
    exact (window_ordered p K hK P).imp (fun {a b} h => by
      simpa only [(window_fold_entry rs a).1, (window_fold_entry rs a).2.1,
        (window_fold_entry rs b).1, (window_fold_entry rs b).2.1] using h)
  have fh : w.h = (derive p K P).h := ff.2.1
  have fT : w.T_h = (derive p K P).T_h := ff.2.2.1
  have newer : ∀ a ∈ f.W, a.j < f.h ∧ FGBlock.Preceq a.X f.T_h := by
    intro a ha
    have haw := (List.mem_filter.mp (fin.2.2.2.2 ▸ ha)).1
    change a ∈ (rs.foldl process_row { derive p K P with s := s }).W at haw
    rw [ff.1, List.mem_map] at haw
    obtain ⟨c, hc, rfl⟩ := haw
    have cb := window_bounds p K hK P c hc
    have laws := windowHeightLaws p K hK
    exact ⟨by rw [(window_fold_entry rs c).1, fin.1, fh]
              exact cb.2.1.trans_lt (laws.justified_below_height P),
      by rw [(window_fold_entry rs c).2.1, fin.2.1, fT]
         exact preceq_trans cb.2.2.2 (laws.justified_preceq_entry P)⟩
  have appendOrd : (f.W ++ [Entry.mk f.h f.T_h ∅]).Pairwise
      (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [List.pairwise_append]
    exact ⟨ord, by simp, fun a ha b hb => List.mem_singleton.mp hb ▸ newer a ha⟩
  change (process_height_events p.E p.cfg K w).W.length = K ∧
    ∀ d ∈ (process_height_events p.E p.cfg K w).W, e.j < d.j
  change ¬ ∃ d ∈ (process_height_events p.E p.cfg K w).W, _ at gone
  rw [process_height_events_def] at gone ⊢
  dsimp only at gone ⊢
  split_ifs at gone ⊢ with ht hp
  · have gd : d ∉ (f.W ++ [Entry.mk f.h f.T_h ∅]).drop
        ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) := by
      intro hd
      exact gone ⟨d, hd, dk.1, dk.2.1⟩
    obtain ⟨hl, hn⟩ := drop_oldest K f.W _ d cap appendOrd df gd
    exact ⟨hl, fun a ha => dk.1 ▸ hn a ha⟩
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim

/-- A capacity removal leaves exactly K newer entries. Each has a birth
strictly after the removed entry's birth on the same chain. -/
theorem window_evicted_has_K_newer (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (gone : ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive p K (.node P s r_s x rs)).h_F < e.j) :
    (derive p K (.node P s r_s x rs)).W.length = K ∧
    ∃ C, FGBlock.Preceq C P ∧
      JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
      ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j ∧
        ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
          JustificationBirth p.E (certificateHeight p K) D d.j d.X := by
  have result := KitFG.Window.window_evicted_has_K_newer p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    P
    s
    r_s
    x
    rs
    (b3history_toEntry e)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using gone)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

private theorem first_removal (p : Params) (K : Nat)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) :
    ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
      (∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact (gone ⟨e, he, rfl, rfl⟩).elim
  | node P s r_s x rs ih =>
      by_cases ha : A = .node P s r_s x rs
      · subst A
        exact (gone ⟨e, he, rfl, rfl⟩).elim
      · have hAP := preceq_parent_of_preceq_node hAB ha
        by_cases hp : ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X
        · exact ⟨P, s, r_s, x, rs, hAP, preceq_refl _, hp, gone⟩
        · obtain ⟨R, t, r_t, y, rows, hAR, hRP, hr, hg⟩ := ih hAP hp
          exact ⟨R, t, r_t, y, rows, hAR, preceq_node_of_preceq s r_s x rs hRP, hr, hg⟩

/-- [07-F entry] The cases refer to B's state and are exclusive by key
presence and coverage. A later finalization can cover an earlier eviction. -/
theorem window_entry_history (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W) :
    (∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q) ∨
    ((¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) ∧
      e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F) ∨
    ((¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ (e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F) ∧
      (derive p K B).h_F < e.j ∧
      ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
        (∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X) ∧
        (¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X) ∧
        (derive p K (.node P s r_s x rs)).W.length = K ∧
        ∃ C, FGBlock.Preceq C P ∧
          JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
          ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j ∧
            ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
              JustificationBirth p.E (certificateHeight p K) D d.j d.X) := by
  have result := KitFG.Window.window_entry_history p.E
    p.cfg
    K
    (b3history_empty_not_quorum p)
    hK
    A
    B
    hAB
    (b3history_toEntry e)
    (by simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
  simpa only [← b3history_derive_eq, ← b3history_height_eq, ← b3history_finality_eq,
    ← b3history_folded_eq, ← b3history_finalize_eq, b3history_state_fields, b3history_entry_fields,
    b3history_mem_map, b3history_exists_map, List.forall_mem_map, b3history_filter_length,
      List.length_map,
    b3history_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

#print axioms b3history_toEntry
#print axioms b3history_toWindow
#print axioms b3history_entry_eq
#print axioms b3history_state_eq
#print axioms b3history_entry_fields
#print axioms b3history_state_fields
#print axioms b3history_initial_eq
#print axioms b3history_row_eq
#print axioms b3history_rows_eq
#print axioms b3history_advance_eq
#print axioms b3history_greatest_eq
#print axioms b3history_finalize_eq
#print axioms b3history_append_eviction_eq
#print axioms b3history_events_eq
#print axioms b3history_transition_eq
#print axioms b3history_foldMap
#print axioms b3history_derive_eq
#print axioms b3history_empty_not_quorum
#print axioms b3history_height_eq
#print axioms b3history_finality_eq
#print axioms b3history_folded_eq
#print axioms b3history_exists_map
#print axioms b3history_filter_length
#print axioms b3history_r6w_eq
#print axioms b3history_mem_map

end AvailableChain.FGSA.Window
end
