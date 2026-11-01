module
public import AvailableChainFGSA.Proofs.WindowHistory -- shake: keep (re-export)

public import AvailableChainKitFG.WindowLiveness
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

variable {V : Type} [DecidableEq V] [RowCodec V]

section

private abbrev b3liveness_Old := FGSA.Window.State
private abbrev b3liveness_New := SimplexFG.Window.State

private def b3liveness_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def b3liveness_toWindow {V : Type} (w : b3liveness_Old V) : b3liveness_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map b3liveness_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem b3liveness_entry_eq {V : Type} (e : Entry V) :
    b3liveness_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem b3liveness_state_eq {V : Type} (w : b3liveness_Old V) :
    b3liveness_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map b3liveness_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem b3liveness_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (b3liveness_toEntry e).j = e.j ∧ (b3liveness_toEntry e).X = e.X ∧ (b3liveness_toEntry e).Q =
      e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem b3liveness_state_fields {V : Type} (w : b3liveness_Old V) :
    (b3liveness_toWindow w).L = w.L ∧ (b3liveness_toWindow w).s = w.s ∧
    (b3liveness_toWindow w).h = w.h ∧ (b3liveness_toWindow w).T_h = w.T_h ∧
    (b3liveness_toWindow w).target_participation = w.target_participation ∧
    (b3liveness_toWindow w).progress = w.progress ∧ (b3liveness_toWindow w).W = w.W.map
      b3liveness_toEntry ∧
    (b3liveness_toWindow w).J = w.J ∧ (b3liveness_toWindow w).h_j = w.h_j ∧
    (b3liveness_toWindow w).F = w.F ∧ (b3liveness_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem b3liveness_initial_eq {V : Type} :
    b3liveness_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3liveness_row_eq (w : b3liveness_Old V) (a : Row V) :
    b3liveness_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (b3liveness_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map b3liveness_toEntry =
      (w.W.map b3liveness_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [b3liveness_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, b3liveness_state_eq] using
        congrArg (fun es => ({ b3liveness_toWindow w with W := es } : b3liveness_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [b3liveness_state_eq] <;> rw [bits] <;> simp_all [b3liveness_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem b3liveness_rows_eq (rs : List (Row V)) (w : b3liveness_Old V) :
    b3liveness_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (b3liveness_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, b3liveness_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3liveness_advance_eq (w : b3liveness_Old V) :
    b3liveness_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (b3liveness_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3liveness_greatest_eq (E : Electorate V) (w : b3liveness_Old V) :
    (FGSA.Window.greatestReady E w).map b3liveness_toEntry =
      SimplexFG.Window.greatestReady E (b3liveness_toWindow w) := by
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
      (oldStep best e).map b3liveness_toEntry = newStep (best.map b3liveness_toEntry)
      (b3liveness_toEntry e) := by
    dsimp [oldStep, newStep, b3liveness_entry_eq]
    split_ifs <;> cases best <;> simp_all [b3liveness_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map b3liveness_toEntry =
        (es.map b3liveness_toEntry).foldl newStep (best.map b3liveness_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (b3liveness_toWindow w) =
      (w.W.map b3liveness_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem b3liveness_finalize_eq (E : Electorate V) (w : b3liveness_Old V) :
    b3liveness_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (b3liveness_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← b3liveness_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [b3liveness_state_eq, b3liveness_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem b3liveness_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map b3liveness_toEntry =
      (es.map b3liveness_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map b3liveness_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, b3liveness_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem b3liveness_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w :
      b3liveness_Old V) :
    b3liveness_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (b3liveness_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← b3liveness_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change b3liveness_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (b3liveness_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      b3liveness_state_eq, b3liveness_entry_eq, List.map_drop]

private theorem b3liveness_transition_eq (p : Params) (K : Nat) (w : b3liveness_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    b3liveness_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (b3liveness_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, b3liveness_events_eq, SimplexFG.Window.transition_def]
  have h := b3liveness_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { b3liveness_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B }
      = _
  rw [h]
  rfl

private theorem b3liveness_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) b3liveness_toWindow where
  initial := b3liveness_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := b3liveness_transition_eq p K

private theorem b3liveness_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3liveness_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (b3liveness_foldMap p K).fold_eq B

end

private theorem b3liveness_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem b3liveness_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (b3liveness_toWindow (derive p K B)) = _
  rw [b3liveness_derive_eq, KitFG.Window.certificateHeight_def]

private theorem b3liveness_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (b3liveness_toWindow (derive p K B)) = _
  rw [b3liveness_derive_eq, KitFG.Window.certificateFinality_def]

private theorem b3liveness_folded_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    b3liveness_toWindow (certificateFolded p K B) =
      KitFG.Window.certificateFolded p.E p.cfg K B := by
  rw [certificateFolded_def, KitFG.Window.certificateFolded_def]
  change { b3liveness_toWindow (B.rows.foldl process_row { derive p K B.parent with s := B.slot })
    with L := B } = _
  rw [b3liveness_rows_eq]
  change { B.rows.foldl SimplexFG.Window.process_row
    { b3liveness_toWindow (derive p K B.parent) with s := B.slot } with L := B } = _
  rw [b3liveness_derive_eq]

private theorem b3liveness_exists_map {V : Type} (xs : List (Entry V))
    (P : SimplexFG.Window.Entry V → Prop) :
    (∃ e ∈ xs.map b3liveness_toEntry, P e) ↔ ∃ e ∈ xs, P (b3liveness_toEntry e) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨d, hd, rfl⟩, hp⟩; exact ⟨d, hd, hp⟩
  · rintro ⟨d, hd, hp⟩; exact ⟨b3liveness_toEntry d, ⟨d, hd, rfl⟩, hp⟩

private theorem b3liveness_filter_length {V : Type} (xs : List (Entry V)) (y : Nat) :
    ((xs.map b3liveness_toEntry).filter (fun e => decide (y < e.j))).length =
      (xs.filter (fun e => decide (y < e.j))).length := by
  rw [List.filter_map]
  delta b3liveness_toEntry
  simp only [Function.comp_def, List.length_map]

private theorem b3liveness_r6w_eq {V : Type} [RowCodec V]
    (w : State V) (a : Row V) :
    SimplexFG.Window.r6w (b3liveness_toWindow w) a = r6w w a := by
  delta SimplexFG.Window.r6w r6w SimplexFG.Window.heightMatch heightMatch
    SimplexFG.Window.staleUseful staleUseful SimplexFG.Window.windowMatch windowMatch
  rcases a with ⟨i, hp, fp⟩
  cases hp <;> cases fp <;> dsimp only <;>
    simp only [b3liveness_state_eq, List.any_map, Function.comp_def, b3liveness_entry_eq]
  all_goals rfl

private theorem b3liveness_mem_map {V : Type} (e : Entry V) (xs : List (Entry V)) :
    b3liveness_toEntry e ∈ xs.map b3liveness_toEntry ↔ e ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, eq⟩
    have same : d = e := by cases d; cases e; cases eq; rfl
    exact same ▸ hd
  · intro he; exact ⟨e, he, rfl⟩

private def livenessAddBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem livenessAddBit_key (a : Row V) (e : Entry V) :
    (livenessAddBit a e).j = e.j ∧ (livenessAddBit a e).X = e.X := by
  unfold livenessAddBit
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem livenessAddBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (livenessAddBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  unfold livenessAddBit
  split_ifs with h <;> simp [h, eq_comm, or_comm]

private theorem livenessRow_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (livenessAddBit a) ∧
    (process_row w a).h = w.h := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨rfl, rfl⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨rfl, rfl⟩

private theorem livenessFold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W =
      w.W.map (fun e => rs.foldl (fun e a => livenessAddBit a e) e) ∧
    (rs.foldl process_row w).h = w.h := by
  induction rs generalizing w with
  | nil => simp
  | cons a rs ih =>
      have h := livenessRow_fields w a
      have t := ih (process_row w a)
      simpa only [List.foldl_cons, t.1, h.1, List.map_map, Function.comp_def,
        t.2, h.2] using (show True ∧ True from ⟨trivial, trivial⟩)

private theorem livenessFold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => livenessAddBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  induction rs generalizing e with
  | nil => simp
  | cons a rs ih =>
      have h := ih (livenessAddBit a e)
      have k := livenessAddBit_key a e
      simp only [List.foldl_cons]
      refine ⟨h.1.trans k.1, h.2.1.trans k.2, ?_⟩
      intro i
      rw [h.2.2, livenessAddBit_bits, k.1, k.2]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

omit [DecidableEq V] [RowCodec V] in
private theorem livenessFinal_fields [Fintype V] (E : Electorate V) (w : State V) :
    (finalizeWindow E w).h = w.h ∧ (finalizeWindow E w).W ⊆ w.W := by
  rw [finalizeWindow_def]
  cases greatestReady E w <;> exact ⟨rfl, fun _ h => (List.mem_filter.mp h).1⟩

omit [DecidableEq V] [RowCodec V] in
private theorem livenessEvents_old [Fintype V] (E : Electorate V) (cfg : FGConfig)
    (K : Nat) (w : State V) (d : Entry V)
    (hd : d ∈ (process_height_events E cfg K w).W) (hj : d.j < w.h) :
    d ∈ w.W := by
  have ff := livenessFinal_fields E w
  rw [process_height_events_def] at hd
  dsimp only at hd
  split_ifs at hd
  · simp only [advance_height_def] at hd
    rcases List.mem_append.mp (List.mem_of_mem_drop hd) with hd | hd
    · exact ff.2 hd
    · have heq := List.mem_singleton.mp hd
      have hj' : d.j = w.h := by simp only [heq, ff.1]
      exact (Nat.ne_of_lt hj hj').elim
  · exact ff.2 hd
  · exact ff.2 hd

/-- Every row with the exact finality pair adds its bit to a retained entry.
The height pair and the R6W arm do not restrict this effect. -/
theorem window_bit_add_of_row (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (hd : d ∈ (derive p K (.node P s r_s x rs)).W)
    (hj : d.j = e.j) (hX : d.X = e.X)
    (a : Row (Fin p.n)) (ha : a ∈ rs)
    (hpair : a.finality_pair = some ⟨e.j, e.X.root⟩) : a.signer ∈ d.Q := by
  have result := KitFG.Window.window_bit_add_of_row p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    P
    s
    r_s
    x
    rs
    (b3liveness_toEntry e)
    (b3liveness_toEntry d)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hd)
    hj
    hX
    a
    ha
    hpair
  simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- Retention at both ends preserves old bits and all exact-pair row bits
carried strictly after A. This statement is independent of the latest J. -/
theorem window_bits_accumulate (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A C : FGBlock (Fin p.n)) (hAC : FGBlock.Preceq A C)
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (hd : d ∈ (derive p K C).W) (hj : d.j = e.j) (hX : d.X = e.X) :
    e.Q ⊆ d.Q ∧ ∀ B, StrictPrefix A B → FGBlock.Preceq B C →
      ∀ a ∈ B.rows, a.finality_pair = some ⟨e.j, e.X.root⟩ → a.signer ∈ d.Q := by
  have result := KitFG.Window.window_bits_accumulate p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    A
    C
    hAC
    (b3liveness_toEntry e)
    (b3liveness_toEntry d)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hd)
    hj
    hX
  simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- A quorum of old bits and later row bits finalizes a prefix that covers
the retained pair. A greater ready height can win the same finality test. -/
theorem window_finalize_of_accumulated_quorum (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (hd : d ∈ (derive p K P).W) (hj : d.j = e.j) (hX : d.X = e.X)
    (Q : Finset (Fin p.n)) (hQ : p.E.IsQuorum Q)
    (hcover : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ B, StrictPrefix A B ∧
      FGBlock.Preceq B (.node P s r_s x rs) ∧ ∃ a ∈ B.rows,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) :
    FGBlock.Preceq e.X (derive p K (.node P s r_s x rs)).F ∧
      e.j ≤ (derive p K (.node P s r_s x rs)).h_F := by
  have result := KitFG.Window.window_finalize_of_accumulated_quorum p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    A
    P
    hAP
    s
    r_s
    x
    rs
    (b3liveness_toEntry e)
    (b3liveness_toEntry d)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using hd)
    hj
    hX
    Q
    hQ
    hcover
  simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- The exact target branch appends the current height and target after
finality pruning. The appended entry is last and has the greatest height. -/
theorem window_target_appended_newest (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (ht : targetQuorum p.E
      (finalizeWindow p.E (certificateFolded p K (.node P s r_s x rs))) = true) :
    let B := FGBlock.node P s r_s x rs
    let f := finalizeWindow p.E (certificateFolded p K B)
    let new : Entry (Fin p.n) := ⟨f.h, f.T_h, ∅⟩
    (derive p K B).W = (f.W ++ [new]).drop ((f.W ++ [new]).length - K) ∧
      ∃ older, (derive p K B).W = older ++ [new] ∧
        (∀ d ∈ older, d.j < new.j) ∧ (derive p K B).h_F < new.j := by
  have result := KitFG.Window.window_target_appended_newest p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    P
    s
    r_s
    x
    rs
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using ht)
  simp only [← b3liveness_derive_eq, ← b3liveness_folded_eq,
    ← b3liveness_finalize_eq, b3liveness_state_fields] at result
  let back (e : SimplexFG.Window.Entry (Fin p.n)) : Entry (Fin p.n) := ⟨e.j, e.X, e.Q⟩
  obtain ⟨older, shape, ordered, above⟩ := result.2
  refine ⟨?_, older.map back, ?_, ?_, above⟩
  · have h := congrArg (List.map back) result.1
    simpa [back, List.map_drop, List.map_append, List.map_map, Function.comp_def,
      b3liveness_entry_eq] using h
  · have h := congrArg (List.map back) shape
    simpa [back, List.map_append, List.map_map, Function.comp_def,
      b3liveness_entry_eq] using h
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact ordered e he

/-- Above current finality, fewer than K newer entries prevents eviction. -/
theorem window_retained_of_few_newer (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (above : (derive p K (.node P s r_s x rs)).h_F < e.j)
    (few : ((derive p K (.node P s r_s x rs)).W.filter (fun d => decide (e.j < d.j))).length < K) :
    ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_of_few_newer p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    P
    s
    r_s
    x
    rs
    (b3liveness_toEntry e)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using above)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using few)
  simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

/-- Apply the current-state finality and capacity bounds at each child
strictly after A. The same entry key remains, and its bits only increase. -/
theorem window_retained_along (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A C : FGBlock (Fin p.n)) (hAC : FGBlock.Preceq A C)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (bounds : ∀ P s r_s x rs, FGBlock.Preceq A P → FGBlock.Preceq (.node P s r_s x rs) C →
      (derive p K (.node P s r_s x rs)).h_F < e.j ∧
        ((derive p K (.node P s r_s x rs)).W.filter (fun d => decide (e.j < d.j))).length < K) :
    ∃ d ∈ (derive p K C).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have result := KitFG.Window.window_retained_along p.E
    p.cfg
    K
    (b3liveness_empty_not_quorum p)
    hK
    A
    C
    hAC
    (b3liveness_toEntry e)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using he)
    (by simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using bounds)
  simpa only [← b3liveness_derive_eq, ← b3liveness_height_eq, ← b3liveness_finality_eq,
    ← b3liveness_folded_eq, ← b3liveness_finalize_eq, b3liveness_state_fields,
    b3liveness_entry_fields,
    b3liveness_mem_map, b3liveness_exists_map, List.forall_mem_map, b3liveness_filter_length,
      List.length_map,
    b3liveness_r6w_eq, SimplexFG.Window.targetQuorum_def, targetQuorum_def] using result

#print axioms b3liveness_toEntry
#print axioms b3liveness_toWindow
#print axioms b3liveness_entry_eq
#print axioms b3liveness_state_eq
#print axioms b3liveness_entry_fields
#print axioms b3liveness_state_fields
#print axioms b3liveness_initial_eq
#print axioms b3liveness_row_eq
#print axioms b3liveness_rows_eq
#print axioms b3liveness_advance_eq
#print axioms b3liveness_greatest_eq
#print axioms b3liveness_finalize_eq
#print axioms b3liveness_append_eviction_eq
#print axioms b3liveness_events_eq
#print axioms b3liveness_transition_eq
#print axioms b3liveness_foldMap
#print axioms b3liveness_derive_eq
#print axioms b3liveness_empty_not_quorum
#print axioms b3liveness_height_eq
#print axioms b3liveness_finality_eq
#print axioms b3liveness_folded_eq
#print axioms b3liveness_exists_map
#print axioms b3liveness_filter_length
#print axioms b3liveness_r6w_eq
#print axioms b3liveness_mem_map

end AvailableChain.FGSA.Window
end
