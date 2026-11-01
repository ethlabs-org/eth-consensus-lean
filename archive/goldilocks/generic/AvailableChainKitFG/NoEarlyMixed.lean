module
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- A crossing before the entry matures must justify that entry at the
parent's height. This statement needs no slot order along the chain. -/
theorem no_mixed_cross_before_maturity (E : Electorate V) (cfg : FGConfig)
    {U X : FGBlock V} (y : Height) (hX : X ≠ .genesis)
    (hUX : FGBlock.Preceq U X.parent)
    (hU : (derive E cfg U).h = y) (hentry : (derive E cfg U).T_h = U)
    (hparent : (derive E cfg X.parent).h = y)
    (hearly : X.slot < U.slot + cfg.timeoutDelay)
    (hcross : (derive E cfg X).h = y + 1) :
    (derive E cfg X).J = U ∧ (derive E cfg X).h_j = y := by
  have hT := (entry_eq_on_plateau E cfg hUX (hU.trans hparent.symm)).symm.trans hentry
  cases X with
  | genesis => exact (hX rfl).elim
  | node p s r_s x rs =>
      obtain ⟨-, hh, hfoldT, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      change (derive E cfg p).h = y at hparent
      change (derive E cfg p).T_h = U at hT
      rw [derive_node, process_height_events_eq] at hcross ⊢
      split_ifs at hcross ⊢ with ht hp
      · exact ⟨((afterFin_T_h E _).trans hfoldT).trans hT,
          ((afterFin_h E _).trans hh).trans hparent⟩
      · simp only [progReady, ht, Bool.false_or, Bool.and_eq_true,
          decide_eq_true_eq] at hp
        rw [afterFin_T_h, afterFin_s, hfoldT, foldRows_s, hT] at hp
        exact (Nat.not_le_of_lt hearly hp.1).elim
      · have hstay := ((afterFin_h E _).trans hh).trans hparent
        rw [hstay] at hcross
        simp only [Height] at *; omega

/-- The first edge above `y` on the path from `D` to `P` has parent height
`y` and child height `y + 1`. This is the public first-crossing interface. -/
theorem first_height_crossing_edge (E : Electorate V) (cfg : FGConfig)
    {D P : FGBlock V} (y : Height) (hDP : FGBlock.Preceq D P)
    (hD : (derive E cfg D).h = y) (hP : y < (derive E cfg P).h) :
    ∃ C : FGBlock V, C ≠ .genesis ∧ FGBlock.Preceq D C.parent ∧
      FGBlock.Preceq C P ∧ (derive E cfg C.parent).h = y ∧
      (derive E cfg C).h = y + 1 := by
  induction P with
  | genesis =>
      obtain rfl := preceq_genesis.mp hDP
      simp only [Height] at *; omega
  | node p s r_s x rs ih =>
      have hne : D ≠ .node p s r_s x rs := by
        intro heq
        subst D
        simp only [Height] at *; omega
      have hDp := preceq_parent_of_preceq_node hDP hne
      by_cases hp : y < (derive E cfg p).h
      · obtain ⟨C, hC, hDC, hCp, hCy, hnext⟩ := ih hDp hp
        exact ⟨C, hC, hDC, preceq_node_of_preceq s r_s x rs hCp, hCy, hnext⟩
      · have hlow := h_mono E cfg hDp
        have hpy : (derive E cfg p).h = y := by simp only [Height] at *; omega
        refine ⟨.node p s r_s x rs, by simp, hDp, preceq_refl _, hpy, ?_⟩
        rcases derive_node_height_cases E cfg p s r_s x rs with hstay | hnext
        · simp only [Height] at *; omega
        · simp only [Height] at *; omega

/-- A crossing has an honest matching row on its chain when faulty weight
is below quorum. The row can be in a strict ancestor of the crossing. -/
theorem crossing_honest_matching_row (E : Electorate V) (cfg : FGConfig)
    (faulty : Finset V) {C : FGBlock V} (y : Height) (hC : C ≠ .genesis)
    (hparent : (derive E cfg C.parent).h = y)
    (hcross : (derive E cfg C).h = y + 1) (hcap : E.weightOf faulty < E.q) :
    ∃ W : FGBlock V, ∃ a : Row V, FGBlock.Preceq W C ∧ a ∈ W.rows ∧
      a.signer ∉ faulty ∧
      a.height_pair.matchesEntry y (derive E cfg C.parent).T_h.root = true := by
  cases C with
  | genesis => exact (hC rfl).elim
  | node p s r_s x rs =>
      change (derive E cfg p).h = y at hparent
      obtain ⟨Q, hQ, hw⟩ := crossing_matching_quorum E cfg p s r_s x rs
        (by simp only [Height] at *; omega)
      obtain ⟨i, hi, hhonest⟩ := honest_in_quorum E faulty hQ hcap
      obtain ⟨W, a, hW, ha, hsigner, hmatch⟩ := hw i hi
      rw [hparent] at hmatch
      exact ⟨W, a, hW, ha, hsigner ▸ hhonest, hmatch⟩

/-- A path with equal endpoint heights keeps `J` and `h_j`. Finality can
advance on the same path. -/
theorem justification_eq_on_plateau (E : Electorate V) (cfg : FGConfig)
    {D P : FGBlock V} (hDP : FGBlock.Preceq D P)
    (hh : (derive E cfg D).h = (derive E cfg P).h) :
    (derive E cfg P).J = (derive E cfg D).J ∧
      (derive E cfg P).h_j = (derive E cfg D).h_j := by
  induction P with
  | genesis =>
      obtain rfl := preceq_genesis.mp hDP
      exact ⟨rfl, rfl⟩
  | node p s r_s x rs ih =>
      by_cases hsame : D = .node p s r_s x rs
      · subst D
        exact ⟨rfl, rfl⟩
      · have hDp := preceq_parent_of_preceq_node hDP hsame
        have hlow := h_mono E cfg hDp
        have hhigh := h_mono E cfg (preceq_parent_node p s r_s x rs)
        have hpar : (derive E cfg p).h = (derive E cfg (.node p s r_s x rs)).h := by
          simp only [Height] at *; omega
        obtain ⟨hJ, hj⟩ := ih hDp (hh.trans hpar.symm)
        obtain ⟨-, hfold, -, hfoldJ, hfoldj, -⟩ :=
          foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
        rw [derive_node, process_height_events_eq] at hpar ⊢
        split_ifs at hpar ⊢
        · change (derive E cfg p).h = (afterFin E _).h + 1 at hpar
          rw [afterFin_h, hfold] at hpar
          simp only [Height] at *; omega
        · change (derive E cfg p).h = (afterFin E _).h + 1 at hpar
          rw [afterFin_h, hfold] at hpar
          simp only [Height] at *; omega
        · exact ⟨((afterFin_J E _).trans hfoldJ).trans hJ,
            ((afterFin_h_j E _).trans hfoldj).trans hj⟩

end AvailableChain.KitFG
