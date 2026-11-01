module
public import AvailableChainFGSA.Model.WindowStore
public import AvailableChainFGSA.Proofs.WindowInvariant -- shake: keep (re-export)
public import AvailableChainKitFG.Correspondence -- shake: keep (re-export)
public import AvailableChainKitFG.StoreSafety -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.WindowSelection -- shake: keep (re-export)

public import AvailableChainKitFG.WindowStore
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block
open AvailableChain.KitFG

section

private abbrev wstore_Old := FGSA.Window.State
private abbrev wstore_New := SimplexFG.Window.State

private def wstore_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def wstore_toWindow {V : Type} (w : wstore_Old V) : wstore_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map wstore_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem wstore_entry_eq {V : Type} (e : Entry V) :
    wstore_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem wstore_state_eq {V : Type} (w : wstore_Old V) :
    wstore_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map wstore_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem wstore_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (wstore_toEntry e).j = e.j ∧ (wstore_toEntry e).X = e.X ∧ (wstore_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem wstore_state_fields {V : Type} (w : wstore_Old V) :
    (wstore_toWindow w).L = w.L ∧ (wstore_toWindow w).s = w.s ∧
    (wstore_toWindow w).h = w.h ∧ (wstore_toWindow w).T_h = w.T_h ∧
    (wstore_toWindow w).target_participation = w.target_participation ∧
    (wstore_toWindow w).progress = w.progress ∧ (wstore_toWindow w).W = w.W.map wstore_toEntry ∧
    (wstore_toWindow w).J = w.J ∧ (wstore_toWindow w).h_j = w.h_j ∧
    (wstore_toWindow w).F = w.F ∧ (wstore_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wstore_initial_eq {V : Type} :
    wstore_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem wstore_row_eq (w : wstore_Old V) (a : Row V) :
    wstore_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (wstore_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map wstore_toEntry =
      (w.W.map wstore_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [wstore_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, wstore_state_eq] using
        congrArg (fun es => ({ wstore_toWindow w with W := es } : wstore_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [wstore_state_eq] <;> rw [bits] <;> simp_all [wstore_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem wstore_rows_eq (rs : List (Row V)) (w : wstore_Old V) :
    wstore_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (wstore_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, wstore_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wstore_advance_eq (w : wstore_Old V) :
    wstore_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (wstore_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem wstore_greatest_eq (E : Electorate V) (w : wstore_Old V) :
    (FGSA.Window.greatestReady E w).map wstore_toEntry =
      SimplexFG.Window.greatestReady E (wstore_toWindow w) := by
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
      (oldStep best e).map wstore_toEntry = newStep (best.map wstore_toEntry) (wstore_toEntry e)
        := by
    dsimp [oldStep, newStep, wstore_entry_eq]
    split_ifs <;> cases best <;> simp_all [wstore_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map wstore_toEntry =
        (es.map wstore_toEntry).foldl newStep (best.map wstore_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (wstore_toWindow w) =
      (w.W.map wstore_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem wstore_finalize_eq (E : Electorate V) (w : wstore_Old V) :
    wstore_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (wstore_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← wstore_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [wstore_state_eq, wstore_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem wstore_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map wstore_toEntry =
      (es.map wstore_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map wstore_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, wstore_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wstore_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : wstore_Old V) :
    wstore_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (wstore_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← wstore_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change wstore_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (wstore_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      wstore_state_eq, wstore_entry_eq, List.map_drop]

private theorem wstore_transition_eq (p : Params) (K : Nat) (w : wstore_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    wstore_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (wstore_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, wstore_events_eq, SimplexFG.Window.transition_def]
  have h := wstore_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { wstore_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem wstore_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) wstore_toWindow where
  initial := wstore_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := wstore_transition_eq p K

private theorem wstore_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wstore_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (wstore_foldMap p K).fold_eq B

end

private theorem wstore_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem wstore_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (wstore_toWindow (derive p K B)) = _
  rw [wstore_derive_eq, KitFG.Window.certificateHeight_def]

private theorem wstore_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (wstore_toWindow (derive p K B)) = _
  rw [wstore_derive_eq, KitFG.Window.certificateFinality_def]

private theorem wstore_accept_eq (p : Params) (K : Nat) (st : SimplexFG.Store (Fin p.n)) :
    acceptViable p K st = SimplexFG.Window.acceptViable p.E p.cfg K st := by
  simp only [acceptViable_def, SimplexFG.Window.acceptViable_def, ← wstore_derive_eq,
    wstore_state_eq]

private theorem wstore_update_eq (p : Params) (K : Nat)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    update_finality p K st B = SimplexFG.Window.update_finality p.E p.cfg K st B := by
  simp only [update_finality_def, SimplexFG.Window.update_finality_def,
    ← wstore_derive_eq, wstore_state_eq, wstore_accept_eq]

private theorem wstore_on_block_eq (p : Params) (K : Nat) :
    on_block p K = SimplexFG.Window.on_block p.E p.cfg K := by
  funext st B
  simp only [on_block_def, SimplexFG.Window.on_block_def, wstore_update_eq]

variable (p : Params) (K : Nat)

/-- The acceptance filter agrees because it reads only height. -/
theorem acceptViable_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n)) :
    acceptViable p K st = SimplexFG.acceptViable p.E p.cfg st := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.acceptViable_eq p.E p.cfg K hK st

/-- A finality update keeps the supplied tree. -/
theorem window_update_finality_TF
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).TF = st.TF := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_update_finality_TF p.E p.cfg K st B

/-- A finality update takes the maximum of the stored and derived heights. -/
theorem window_update_finality_h_max
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_max = max st.h_max ((derive p K B).h) := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_update_finality_h_max p.E p.cfg K st B

/-- A finality update selects the compatible greater justification pair. -/
theorem window_update_finality_pair
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    ((update_finality p K st B).h_j, (update_finality p K st B).J) =
      if FGBlock.Preceq st.F (derive p K B).J ∧
          lexKey (st.h_j, st.J) < lexKey ((derive p K B).h_j, (derive p K B).J)
        then ((derive p K B).h_j, (derive p K B).J) else (st.h_j, st.J) := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_update_finality_pair p.E p.cfg K st B

/-- A finality update keeps F or accepts a stored compatible derived finalization. -/
theorem window_update_finality_F_cases
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).F = st.F ∨
      (FGBlock.Preceq st.F (derive p K B).F ∧ (derive p K B).F ∈ st.TF ∧
        FGBlock.Preceq (derive p K B).F (update_finality p K st B).J ∧
        (update_finality p K st B).F = (derive p K B).F) := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_update_finality_F_cases p.E p.cfg K st B

/-- One update from the same input has the same maximum height. -/
theorem update_finality_h_max_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_max = (SimplexFG.update_finality p.E p.cfg st B).h_max := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.update_finality_h_max_eq p.E p.cfg K hK st B

/-- One update from the same input has the same selected justification. -/
theorem update_finality_J_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).J = (SimplexFG.update_finality p.E p.cfg st B).J := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.update_finality_J_eq p.E p.cfg K hK st B

/-- One update from the same input has the same justification height. -/
theorem update_finality_h_j_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_j = (SimplexFG.update_finality p.E p.cfg st B).h_j := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.update_finality_h_j_eq p.E p.cfg K hK st B

/-- The refusal tests and tree insertion agree for one step. -/
theorem on_block_TF_eq
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (on_block p K st B).TF = (SimplexFG.on_block p.E p.cfg st B).TF := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.on_block_TF_eq p.E p.cfg K st B

/-- Genesis satisfies every window store field. -/
theorem windowStoreInvariant_init :
    FGStoreInvariant (fun B => projectHeight (derive p K B)) (certificateFinality p K)
      SimplexFG.Store.init := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.windowStoreInvariant_init p.E p.cfg K

/-- Insertion and the three cache steps preserve the structural invariant. -/
theorem windowStoreInvariant_accept (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (h : FGStoreInvariant (fun B => projectHeight (derive p K B))
      (certificateFinality p K) st) (hpar : B.parent ∈ st.TF)
    (hroots : StoreStepRoots st B) :
    FGStoreInvariant (fun B => projectHeight (derive p K B)) (certificateFinality p K)
      (update_finality p K { st with TF := insert B st.TF } B) := by
  have hg := KitFG.Window.windowStoreInvariant_accept p.E p.cfg K (wstore_empty_not_quorum p) hK
    st B
  simp only [← wstore_update_eq, ← wstore_finality_eq,
    ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def] at hg
  exact hg h hpar hroots

theorem window_on_block_of_refused (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot) :
    on_block p K st B = st := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_on_block_of_refused p.E p.cfg K st B hc

theorem window_on_block_of_accepted (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hc : ¬ (B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot)) :
    on_block p K st B = update_finality p K { st with TF := insert B st.TF } B := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_on_block_of_accepted p.E p.cfg K st B hc

theorem window_on_block_F_mono
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    FGBlock.Preceq st.F (on_block p K st B).F := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_on_block_F_mono p.E p.cfg K st B

theorem windowStoreInvariant_on_block (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (h : FGStoreInvariant (fun B => projectHeight (derive p K B))
      (certificateFinality p K) st) (hroots : StoreStepRoots st B) :
    FGStoreInvariant (fun B => projectHeight (derive p K B)) (certificateFinality p K)
      (on_block p K st B) := by
  have hg := KitFG.Window.windowStoreInvariant_on_block p.E p.cfg K (wstore_empty_not_quorum p) hK
    st B
  simp only [← wstore_on_block_eq, ← wstore_finality_eq,
    ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def] at hg
  exact hg h hroots

theorem window_on_block_TF_subset
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    st.TF ⊆ (on_block p K st B).TF := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.window_on_block_TF_subset p.E p.cfg K st B

/-- Window store safety uses its structural invariant as the good-state predicate. -/
theorem windowStoreSafety (hK : 2 ≤ K) :
    FGStoreSafety p.E (fun B => projectHeight (derive p K B)) (certificateFinality p K)
      (id : SimplexFG.Store (Fin p.n) → SimplexFG.Store (Fin p.n))
      (fun _ B => (projectHeight (derive p K B), certificateFinality p K B))
      SimplexFG.Store.init (on_block p K)
      (FGStoreInvariant (fun B => projectHeight (derive p K B)) (certificateFinality p K))
        StoreStepRoots := by
  simpa only [← wstore_accept_eq, ← wstore_update_eq, ← wstore_on_block_eq, ← wstore_height_eq, ←
    wstore_finality_eq, KitFG.Window.certificateHeight_def, certificateHeight_def,
      KitFG.Window.certificateFinality_def,
      ← wstore_derive_eq, wstore_state_eq, KitFG.Window.projectHeight_def,
        KitFG.Window.projectFinality_def, projectHeight_def, certificateHeight_def,
      certificateFinality_def,
          projectFinality_def] using
    KitFG.Window.windowStoreSafety p.E p.cfg K (wstore_empty_not_quorum p) hK

#print axioms wstore_entry_eq
#print axioms wstore_state_eq
#print axioms wstore_entry_fields
#print axioms wstore_state_fields
#print axioms wstore_initial_eq
#print axioms wstore_row_eq
#print axioms wstore_rows_eq
#print axioms wstore_advance_eq
#print axioms wstore_greatest_eq
#print axioms wstore_finalize_eq
#print axioms wstore_append_eviction_eq
#print axioms wstore_events_eq
#print axioms wstore_transition_eq
#print axioms wstore_foldMap
#print axioms wstore_derive_eq
#print axioms wstore_empty_not_quorum
#print axioms wstore_height_eq
#print axioms wstore_finality_eq
#print axioms wstore_accept_eq
#print axioms wstore_update_eq
#print axioms wstore_on_block_eq

end AvailableChain.FGSA.Window
end
