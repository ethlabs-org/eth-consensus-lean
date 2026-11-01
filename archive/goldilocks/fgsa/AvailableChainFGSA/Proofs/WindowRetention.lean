module
public import AvailableChainFGSA.Proofs.WindowLiveness

public import AvailableChainKitFG.WindowRetention
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

section

private abbrev b3retention_Old := FGSA.Window.State
private abbrev b3retention_New := SimplexFG.Window.State

private def b3retention_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def b3retention_toWindow {V : Type} (w : b3retention_Old V) : b3retention_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map b3retention_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem b3retention_entry_eq {V : Type} (e : Entry V) :
    b3retention_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem b3retention_state_eq {V : Type} (w : b3retention_Old V) :
    b3retention_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map b3retention_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem b3retention_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (b3retention_toEntry e).j = e.j ∧ (b3retention_toEntry e).X = e.X ∧ (b3retention_toEntry e).Q
      = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem b3retention_state_fields {V : Type} (w : b3retention_Old V) :
    (b3retention_toWindow w).L = w.L ∧ (b3retention_toWindow w).s = w.s ∧
    (b3retention_toWindow w).h = w.h ∧ (b3retention_toWindow w).T_h = w.T_h ∧
    (b3retention_toWindow w).target_participation = w.target_participation ∧
    (b3retention_toWindow w).progress = w.progress ∧ (b3retention_toWindow w).W = w.W.map
      b3retention_toEntry ∧
    (b3retention_toWindow w).J = w.J ∧ (b3retention_toWindow w).h_j = w.h_j ∧
    (b3retention_toWindow w).F = w.F ∧ (b3retention_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem b3retention_initial_eq {V : Type} :
    b3retention_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3retention_row_eq (w : b3retention_Old V) (a : Row V) :
    b3retention_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (b3retention_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map b3retention_toEntry =
      (w.W.map b3retention_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [b3retention_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, b3retention_state_eq] using
        congrArg (fun es => ({ b3retention_toWindow w with W := es } : b3retention_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [b3retention_state_eq] <;> rw [bits] <;> simp_all [b3retention_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem b3retention_rows_eq (rs : List (Row V)) (w : b3retention_Old V) :
    b3retention_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (b3retention_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, b3retention_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3retention_advance_eq (w : b3retention_Old V) :
    b3retention_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (b3retention_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3retention_greatest_eq (E : Electorate V) (w : b3retention_Old V) :
    (FGSA.Window.greatestReady E w).map b3retention_toEntry =
      SimplexFG.Window.greatestReady E (b3retention_toWindow w) := by
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
      (oldStep best e).map b3retention_toEntry = newStep (best.map b3retention_toEntry)
      (b3retention_toEntry e) := by
    dsimp [oldStep, newStep, b3retention_entry_eq]
    split_ifs <;> cases best <;> simp_all [b3retention_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map b3retention_toEntry =
        (es.map b3retention_toEntry).foldl newStep (best.map b3retention_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (b3retention_toWindow w) =
      (w.W.map b3retention_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem b3retention_finalize_eq (E : Electorate V) (w : b3retention_Old V) :
    b3retention_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (b3retention_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← b3retention_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [b3retention_state_eq, b3retention_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem b3retention_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map b3retention_toEntry =
      (es.map b3retention_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map b3retention_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, b3retention_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3retention_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      b3retention_Old V) :
    b3retention_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (b3retention_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← b3retention_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change b3retention_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (b3retention_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      b3retention_state_eq, b3retention_entry_eq, List.map_drop]

private theorem b3retention_transition_eq (p : Params) (K : Nat) (w : b3retention_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    b3retention_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (b3retention_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, b3retention_events_eq, SimplexFG.Window.transition_def]
  have h := b3retention_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { b3retention_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem b3retention_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) b3retention_toWindow where
  initial := b3retention_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := b3retention_transition_eq p K

private theorem b3retention_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3retention_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (b3retention_foldMap p K).fold_eq B

end

private theorem b3retention_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem b3retention_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (b3retention_toWindow (derive p K B)) = _
  rw [b3retention_derive_eq, KitFG.Window.certificateHeight_def]

private theorem b3retention_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (b3retention_toWindow (derive p K B)) = _
  rw [b3retention_derive_eq, KitFG.Window.certificateFinality_def]

private theorem b3retention_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3retention_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { b3retention_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [b3retention_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { b3retention_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [b3retention_derive_eq]

private theorem b3retention_exists_map {V : Type} (xs : List (Entry V))
    (P : SimplexFG.Window.Entry V → Prop) :
    (∃ e ∈ xs.map b3retention_toEntry, P e) ↔ ∃ e ∈ xs, P (b3retention_toEntry e) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hp⟩; exact ⟨d, hd, hp⟩
  · rintro ⟨d, hd, hp⟩; exact ⟨b3retention_toEntry d, ⟨d, hd, rfl⟩, hp⟩

private theorem b3retention_filter_length {V : Type} (xs : List (Entry V)) (y : Nat) :
    ((xs.map b3retention_toEntry).filter (fun e => decide (y < e.j))).length =
      (xs.filter (fun e => decide (y < e.j))).length := by
  rw [List.filter_map]
  delta b3retention_toEntry
  simp only [Function.comp_def, List.length_map]

private theorem b3retention_r6w_eq {V : Type} [RowCodec V]
    (w : State V) (a : Row V) :
    SimplexFG.Window.r6w (b3retention_toWindow w) a = r6w w a := by
  delta SimplexFG.Window.r6w r6w SimplexFG.Window.heightMatch heightMatch
    SimplexFG.Window.staleUseful staleUseful SimplexFG.Window.windowMatch windowMatch
  rcases a with ⟨i, hp, fp⟩
  cases hp <;> cases fp <;> dsimp only <;>
    simp only [b3retention_state_eq, List.any_map, Function.comp_def, b3retention_entry_eq]
  all_goals rfl

private theorem b3retention_mem_map {V : Type} (e : Entry V) (xs : List (Entry V)) :
    b3retention_toEntry e ∈ xs.map b3retention_toEntry ↔ e ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, eq⟩
    have same : d = e := by cases d; cases e; cases eq; rfl
    exact same ▸ hd
  · intro he; exact ⟨e, he, rfl⟩

/-- Latest justification height keeps its value or increases at a target crossing. -/
theorem window_hj_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) :
    (derive p K A).h_j ≤ (derive p K B).h_j := by
  have result := KitFG.Window.window_hj_mono p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    A
    B
    hAB
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

private theorem retentionHeight_count (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (y : Nat) (S : Finset Nat)
    (cover : ∀ d ∈ (derive p K B).W, y < d.j → d.j ∈ S) :
    ((derive p K B).W.filter (fun d => decide (y < d.j))).length ≤ S.card := by
  let xs := (derive p K B).W.filter (fun d => decide (y < d.j))
  have ord : (xs.map Entry.j).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact ((window_ordered p K hK B).filter _).imp (fun h => h.1)
  have sub : (xs.map Entry.j).toFinset ⊆ S := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    obtain ⟨hd, hy⟩ := List.mem_filter.mp hd
    exact cover d hd (of_decide_eq_true hy)
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup ord.nodup, List.length_map] at count
  exact count

/-- [plan item 12] Finality below the key and a latest height below y + K
keep the key and all its bits. The step bounds follow by monotonicity. -/
theorem window_retained_of_scalar (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (above : (derive p K P).h_F < e.j)
    (near : (derive p K P).h_j < e.j + K) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_of_scalar p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    A
    P
    hAP
    (b3retention_toEntry e)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using near)
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- A key remains with all its bits, or finality covers it, when the latest
justification height is less than its height plus K. -/
theorem window_retained_or_covered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (near : (derive p K P).h_j < e.j + K) :
    (∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q) ∨
      (e.j ≤ (derive p K P).h_F ∧ FGBlock.Preceq e.X (derive p K P).F) := by
  have result := KitFG.Window.window_retained_or_covered p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    A
    P
    hAP
    (b3retention_toEntry e)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using near)
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

private theorem retentionBirth_entry (p : Params) (K : Nat) (hK : 2 ≤ K)
    (C : FGBlock (Fin p.n)) (j : Nat) (X : FGBlock (Fin p.n))
    (birth : JustificationBirth p.E (certificateHeight p K) C j X) :
    (Entry.mk j X ∅) ∈ (derive p K C).W := by
  cases C with
  | genesis => exact (birth.1 rfl).elim
  | node P s r_s x rs =>
      have hp : (derive p K P).h = j := birth.2.1
      have hcj : (derive p K (.node P s r_s x rs)).h_j = j := birth.2.2.2.1
      have hcX : (derive p K (.node P s r_s x rs)).J = X := birth.2.2.2.2.1
      have ht : targetQuorum p.E
          (finalizeWindow p.E (certificateFolded p K (.node P s r_s x rs))) = true := by
        rcases window_latest_pair_kept p K P s r_s x rs with kept | crossed
        · have below := (windowHeightLaws p K hK).justified_below_height P
          change (derive p K P).h_j < (derive p K P).h at below
          rw [← kept.1, hcj, hp] at below
          exact (Nat.lt_irrefl j below).elim
        · exact crossed.2.2
      have latest : (derive p K (.node P s r_s x rs)).h_j =
          (finalizeWindow p.E (certificateFolded p K (.node P s r_s x rs))).h ∧
          (derive p K (.node P s r_s x rs)).J =
          (finalizeWindow p.E (certificateFolded p K (.node P s r_s x rs))).T_h := by
        change (process_height_events p.E p.cfg K
            (certificateFolded p K (.node P s r_s x rs))).h_j = _ ∧
          (process_height_events p.E p.cfg K
            (certificateFolded p K (.node P s r_s x rs))).J = _
        rw [process_height_events_def, ite_eq_left ht]
        exact ⟨rfl, rfl⟩
      have hj := latest.1.symm.trans hcj
      have hX := latest.2.symm.trans hcX
      obtain ⟨_, older, appended, _, _⟩ := window_target_appended_newest p K hK P s r_s x rs ht
      rw [hj, hX] at appended
      rw [appended]
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- [bp 01:161–173] R3 and R6W place each exact row after the key's birth.
Retention then preserves the row's bit through B. -/
theorem window_exact_row_no_missing_effect (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (y : Nat) (U : FGBlock (Fin p.n))
    (d : Entry (Fin p.n)) (hd : d ∈ (derive p K B).W)
    (hj : d.j = y) (hX : d.X = U)
    (valid : ∀ P s r_s x rs, FGBlock.Preceq (.node P s r_s x rs) B → ∀ a ∈ rs,
      (RowBody.ofRow a).valid = true ∧ r6w (derive p K P) a = true)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (hCB : FGBlock.Preceq (.node P s r_s x rs) B)
    (a : Row (Fin p.n)) (ha : a ∈ rs)
    (hpair : a.finality_pair = some ⟨y, U.root⟩) : a.signer ∈ d.Q := by
  have result := KitFG.Window.window_exact_row_no_missing_effect p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    B
    y
    U
    (b3retention_toEntry d)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hd)
    hj
    hX
    (by
      intro P s r_s x rs hCB a ha
      obtain ⟨hr3, hr6⟩ := valid P s r_s x rs hCB a ha
      refine ⟨?_, ?_⟩
      · cases a with
        | mk i hp fp =>
            cases hp <;> exact hr3
      · simpa only [← b3retention_derive_eq, b3retention_r6w_eq] using hr6)
    P
    s
    r_s
    x
    rs
    hCB
    a
    ha
    hpair
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- [plan item 12] A finite set covers all births with certificate height
above the protected key up to P. Fewer than K such births prevents eviction.
The set may overestimate the births; no gap in certificate heights is required. -/
theorem window_retained_of_few_births (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (above : (derive p K P).h_F < e.j)
    (births : Finset (FGBlock (Fin p.n))) (few : births.card < K)
    (cover : ∀ C j X, FGBlock.Preceq C P → e.j < j →
      JustificationBirth p.E (certificateHeight p K) C j X → C ∈ births) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_of_few_births p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    A
    P
    hAP
    (b3retention_toEntry e)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    births
    few
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using cover)
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- [bp 22:1265–1272] A latest retained height survives at most one later
birth while finality stays below it. This is a fold fact with explicit bounds. -/
theorem window_retained_fresh_one_newer (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (latest : e.j = (derive p K A).h_j)
    (above : (derive p K P).h_F < e.j)
    (births : Finset (FGBlock (Fin p.n))) (one : births.card ≤ 1)
    (cover : ∀ C j X, StrictPrefix A C → FGBlock.Preceq C P →
      JustificationBirth p.E (certificateHeight p K) C j X → C ∈ births) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_fresh_one_newer p.E
    p.cfg
    K
    (b3retention_empty_not_quorum p)
    hK
    A
    P
    hAP
    (b3retention_toEntry e)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using latest)
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    births
    one
    (by simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using cover)
  simpa only [← b3retention_derive_eq, ← b3retention_height_eq, ← b3retention_finality_eq,
    ← b3retention_folded_eq, ← b3retention_finalize_eq, b3retention_state_fields,
    b3retention_entry_fields,
    b3retention_mem_map, b3retention_exists_map, List.forall_mem_map, b3retention_filter_length,
      List.length_map,
    b3retention_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

#print axioms b3retention_toEntry
#print axioms b3retention_toWindow
#print axioms b3retention_entry_eq
#print axioms b3retention_state_eq
#print axioms b3retention_entry_fields
#print axioms b3retention_state_fields
#print axioms b3retention_initial_eq
#print axioms b3retention_row_eq
#print axioms b3retention_rows_eq
#print axioms b3retention_advance_eq
#print axioms b3retention_greatest_eq
#print axioms b3retention_finalize_eq
#print axioms b3retention_append_eviction_eq
#print axioms b3retention_events_eq
#print axioms b3retention_transition_eq
#print axioms b3retention_foldMap
#print axioms b3retention_derive_eq
#print axioms b3retention_empty_not_quorum
#print axioms b3retention_height_eq
#print axioms b3retention_finality_eq
#print axioms b3retention_folded_eq
#print axioms b3retention_exists_map
#print axioms b3retention_filter_length
#print axioms b3retention_r6w_eq
#print axioms b3retention_mem_map

end AvailableChain.FGSA.Window
end
