module
public import AvailableChainFGSA.Proofs.WindowCertificates -- shake: keep (re-export)
public import AvailableChainKitFG.ProvenanceCore -- shake: keep (re-export)
public import AvailableChainKitFG.CrossingCore -- shake: keep (re-export)

public import AvailableChainKitFG.WindowProvenance
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

section

private abbrev wprov_Old := FGSA.Window.State
private abbrev wprov_New := SimplexFG.Window.State

private def wprov_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def wprov_toWindow {V : Type} (w : wprov_Old V) : wprov_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map wprov_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem wprov_entry_eq {V : Type} (e : Entry V) :
    wprov_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem wprov_state_eq {V : Type} (w : wprov_Old V) :
    wprov_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map wprov_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem wprov_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (wprov_toEntry e).j = e.j ∧ (wprov_toEntry e).X = e.X ∧ (wprov_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem wprov_state_fields {V : Type} (w : wprov_Old V) :
    (wprov_toWindow w).L = w.L ∧ (wprov_toWindow w).s = w.s ∧
    (wprov_toWindow w).h = w.h ∧ (wprov_toWindow w).T_h = w.T_h ∧
    (wprov_toWindow w).target_participation = w.target_participation ∧
    (wprov_toWindow w).progress = w.progress ∧ (wprov_toWindow w).W = w.W.map wprov_toEntry ∧
    (wprov_toWindow w).J = w.J ∧ (wprov_toWindow w).h_j = w.h_j ∧
    (wprov_toWindow w).F = w.F ∧ (wprov_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem wprov_initial_eq {V : Type} :
    wprov_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem wprov_row_eq (w : wprov_Old V) (a : Row V) :
    wprov_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (wprov_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map wprov_toEntry =
      (w.W.map wprov_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [wprov_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, wprov_state_eq] using
        congrArg (fun es => ({ wprov_toWindow w with W := es } : wprov_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [wprov_state_eq] <;> rw [bits] <;> simp_all [wprov_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem wprov_rows_eq (rs : List (Row V)) (w : wprov_Old V) :
    wprov_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (wprov_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, wprov_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wprov_advance_eq (w : wprov_Old V) :
    wprov_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (wprov_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem wprov_greatest_eq (E : Electorate V) (w : wprov_Old V) :
    (FGSA.Window.greatestReady E w).map wprov_toEntry =
      SimplexFG.Window.greatestReady E (wprov_toWindow w) := by
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
      (oldStep best e).map wprov_toEntry = newStep (best.map wprov_toEntry) (wprov_toEntry e) := by
    dsimp [oldStep, newStep, wprov_entry_eq]
    split_ifs <;> cases best <;> simp_all [wprov_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map wprov_toEntry =
        (es.map wprov_toEntry).foldl newStep (best.map wprov_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (wprov_toWindow w) =
      (w.W.map wprov_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

omit [DecidableEq V] [RowCodec V] in
private theorem wprov_finalize_eq (E : Electorate V) (w : wprov_Old V) :
    wprov_toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (wprov_toWindow w) := by
  rw [FGSA.Window.finalizeWindow_def, SimplexFG.Window.finalizeWindow_def]
  rw [← wprov_greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [wprov_state_eq, wprov_entry_eq, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem wprov_append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map wprov_toEntry =
      (es.map wprov_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map wprov_toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, wprov_entry_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem wprov_events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : wprov_Old V) :
    wprov_toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (wprov_toWindow w) := by
  rw [FGSA.Window.process_height_events_def, SimplexFG.Window.process_height_events_def]
  rw [← wprov_finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change wprov_toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (wprov_toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height_def, SimplexFG.Window.advance_height_def,
      wprov_state_eq, wprov_entry_eq, List.map_drop]

private theorem wprov_transition_eq (p : Params) (K : Nat) (w : wprov_Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    wprov_toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (wprov_toWindow w) B rs := by
  rw [FGSA.Window.transition_def, wprov_events_eq, SimplexFG.Window.transition_def]
  have h := wprov_rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { wprov_toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem wprov_foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) wprov_toWindow where
  initial := wprov_initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := wprov_transition_eq p K

private theorem wprov_derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    wprov_toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (wprov_foldMap p K).fold_eq B

end

private theorem wprov_empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem wprov_height_eq (p : Params) (K : Nat) :
    certificateHeight p K = KitFG.Window.certificateHeight p.E p.cfg K := by
  funext B
  change KitFG.Window.projectHeight (wprov_toWindow (derive p K B)) = _
  rw [wprov_derive_eq, KitFG.Window.certificateHeight_def]

private theorem wprov_finality_eq (p : Params) (K : Nat) :
    certificateFinality p K = KitFG.Window.certificateFinality p.E p.cfg K := by
  funext B
  change KitFG.Window.projectFinality (wprov_toWindow (derive p K B)) = _
  rw [wprov_derive_eq, KitFG.Window.certificateFinality_def]

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_entry (p : Params) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (C : FGBlock (Fin p.n)) (fp : Option FinalityPair)
    (h : Height) (T : BlockId) (t : Bool)
    (hemit : height_pair Λ
      (some ((certificateHeight p K C).h, (certificateHeight p K C).T_h.root)) fp = .vote h T t) :
    h = (certificateHeight p K C).h ∧ T = (certificateHeight p K C).T_h.root ∧
      FGBlock.Preceq (certificateHeight p K C).T_h C := by
  have hg := KitFG.Window.window_provenance_entry p.E p.cfg K hK Λ C fp h T t
  rw [← wprov_height_eq] at hg
  exact hg hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityRow (p : Params) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (Hd : FGBlock (Fin p.n)) (pair : FinalityPair)
    (hemit : finality_pair Λ (certificateHeadFields (certificateHeight p K)
      (certificateFinality p K) Hd) = some pair) :
    pair.height = (certificateHeight p K Hd).h_j ∧ pair.target = (certificateHeight p K Hd).J.root ∧
      (certificateFinality p K Hd).h_F < pair.height ∧ TargetQCAt p.E Hd pair.height
      (certificateHeight p K Hd).J := by
  have hg := KitFG.Window.window_provenance_finalityRow p.E p.cfg K hK Λ Hd pair
  rw [← wprov_height_eq, ← wprov_finality_eq] at hg
  exact hg hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityQC (p : Params) (K : Nat) (hK : 2 ≤ K)
    (faulty : Finset (Fin p.n)) (hcap : p.E.weightOf faulty < p.E.q)
    (rows : Finset (Row (Fin p.n))) (Q : Finset (Fin p.n))
    (hQ : p.E.IsQuorum Q) (pair : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some pair)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some pair →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields (certificateHeight p K)
      (certificateFinality p K) Hd) = some pair) :
    ∃ Hd, pair.height = (certificateHeight p K Hd).h_j ∧
      pair.target = (certificateHeight p K Hd).J.root ∧
      TargetQCAt p.E Hd pair.height (certificateHeight p K Hd).J := by
  have hg := KitFG.Window.window_provenance_finalityQC p.E p.cfg K hK faulty hcap rows Q hQ pair
    hrows
  rw [← wprov_height_eq, ← wprov_finality_eq] at hg
  exact hg hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_crossing_quorum_ne_justified (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B W : FGBlock (Fin p.n)) (hroot : RootInjectiveOn B W)
    (hJ : (certificateHeight p K B).h_j ≠ 0)
    (hW : (certificateHeight p K B).h_j < (certificateHeight p K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight p K B).J W) :
    ∃ X : FGBlock (Fin p.n), X.root ≠ (certificateHeight p K B).J.root ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (certificateHeight p K B).h_j X.root = true := by
  have hg := KitFG.Window.window_exists_crossing_quorum_ne_justified p.E p.cfg K hK B W hroot
  rw [← wprov_height_eq] at hg
  exact hg hJ hW hnot

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_honest_timeout_of_crossing (p : Params) (K : Nat) (hK : 2 ≤ K)
    (faulty : Finset (Fin p.n))
    (B W : FGBlock (Fin p.n)) (hroot : RootInjectiveOn B W)
    (hcap : p.E.weightOf faulty + p.E.totalWeight < 2 * p.E.q)
    (hJ : (certificateHeight p K B).h_j ≠ 0)
    (hW : (certificateHeight p K B).h_j < (certificateHeight p K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight p K B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (certificateHeight p K B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair =
          .vote (certificateHeight p K B).h_j (certificateHeight p K B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair = .vote (certificateHeight p K B).h_j X true) := by
  have hg := KitFG.Window.window_exists_honest_timeout_of_crossing p.E p.cfg K hK faulty B W hroot
    hcap
  rw [← wprov_height_eq] at hg
  exact hg hJ hW hnot hhonest

/-- An honest row names the latest pair of its signer's head at emission. On the
including chain, that pair can be an older retained entry. Such an entry gains bits
from any admitted row with that exact pair, through either R6W arm. The head read is
independent of the retained entries. Emission also checks the client record. -/
theorem window_headFields_latest (p : Params) (K : Nat)
    (Hd : FGBlock (Fin p.n)) (Λ : Record) :
    certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd =
      ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩ ∧
    finality_pair Λ (certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd) =
      (if (derive p K Hd).h_F < (derive p K Hd).h_j ∧
          (Λ.target (derive p K Hd).h_j = none ∨
            Λ.target (derive p K Hd).h_j = some (derive p K Hd).J.root) ∧
          Λ.timeout (derive p K Hd).h_j = false ∧
          (Λ.lock (derive p K Hd).h_j = none ∨
            Λ.lock (derive p K Hd).h_j = some (derive p K Hd).J.root) then
        some ⟨(derive p K Hd).h_j, (derive p K Hd).J.root⟩ else none) := by
  simpa only [← wprov_height_eq, ← wprov_finality_eq, KitFG.Window.certificateHeight_def,
      certificateHeight_def,
    KitFG.Window.certificateFinality_def, ← wprov_derive_eq, wprov_state_eq,
      KitFG.Window.projectHeight_def, KitFG.Window.projectFinality_def, projectHeight_def,
        certificateFinality_def, projectFinality_def] using
    KitFG.Window.window_headFields_latest p.E p.cfg K Hd Λ

#print axioms wprov_entry_eq
#print axioms wprov_state_eq
#print axioms wprov_entry_fields
#print axioms wprov_state_fields
#print axioms wprov_initial_eq
#print axioms wprov_row_eq
#print axioms wprov_rows_eq
#print axioms wprov_advance_eq
#print axioms wprov_greatest_eq
#print axioms wprov_finalize_eq
#print axioms wprov_append_eviction_eq
#print axioms wprov_events_eq
#print axioms wprov_transition_eq
#print axioms wprov_foldMap
#print axioms wprov_derive_eq
#print axioms wprov_empty_not_quorum
#print axioms wprov_height_eq
#print axioms wprov_finality_eq

end AvailableChain.FGSA.Window
end
