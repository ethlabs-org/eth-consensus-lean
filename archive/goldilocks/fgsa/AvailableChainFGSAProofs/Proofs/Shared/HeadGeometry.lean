module
public import AvailableChainFGSA.Proofs.Head.Walk
public import AvailableChainFGSA.Proofs.StoreBundle

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. P3 F1b.5; bp02 §7, ap.headReachesLo.v6 clauses 1–3.
Class (iii), store geometry. DC: Goldfish/Walk.lean:197 `ghost_step_none`
and :433 `ghost_reaches` give the walk ingredients.
INTENTIONAL: FJ's low-parent eligibility and filtered witness imply the
height bound; DC has no FJ band (bp02 §7). No run premise is needed. -/
theorem fgsa_headReachesLo (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (raw support : List (GridCO.Wire p.n .root))
    (hst : Reachable p st) (hsub : X ⊆ st.fg.TF)
    (hclosed : ∀ B ∈ X, ∀ A, FGBlock.Preceq A B → A ∈ X) :
    let D := filteredFrom p.E p.cfg (controls p st) X
    let A := liveRoot p st
    let H := headInTree p st (erasedList st D) raw support
    ((∃ B ∈ D, eraseFG B = A) ∨
        (∃ B ∈ D, (eraseFG B).parent? = some A ∧ eligible p st raw support (eraseFG B) = true) →
      ∃ B ∈ D, eraseFG B = H ∧ (controls p st).lo ≤ hOf p.E p.cfg B) ∧
    ((¬ ∃ B ∈ D, eraseFG B = A) →
      (∀ B ∈ D, (eraseFG B).parent? = some A → eligible p st raw support (eraseFG B) = false) →
      H = A) ∧
    (A = eraseFG (controls p st).Z → D.Nonempty → (controls p st).Z ∈ D) := by
  dsimp only
  let D := filteredFrom p.E p.cfg (controls p st) X
  let tree := erasedList st D
  let H := headInTree p st tree raw support
  have hi := (storeBundle_of_reachable p st hst).cstore
  have hmem : ∀ b, b ∈ tree ↔ ∃ B ∈ D, eraseFG B = b := by
    intro b
    constructor
    · intro hb
      exact of_decide_eq_true (List.mem_filter.mp hb).2
    · rintro ⟨B, hB, rfl⟩
      exact List.mem_filter.mpr ⟨(hi.baseTree _).mpr
        ⟨B, hsub ((KitFG.mem_filteredFrom_of_bridge
          p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mp hB).1, rfl⟩,
        decide_eq_true ⟨B, hB, rfl⟩⟩
  have hterminal := fgsa_headInTree_noEligibleChild p st hi X hsub hclosed raw support
  refine ⟨?_, ?_, ?_⟩
  · intro hstart
    have hh : H ∈ tree := by
      rcases fgsa_headInTree_mem_or_anchor p st tree raw support with he | hm
      · change H = liveRoot p st at he
        rcases hstart with ha | ⟨B, hB, hp, hel⟩
        · rw [he]
          exact (hmem _).mpr ha
        · have ht := hterminal (eraseFG B) ((hmem _).mpr ⟨B, hB, rfl⟩)
            (by change (eraseFG B).parent? = some H; rw [he]; exact hp)
          rw [hel] at ht
          cases ht
      · exact hm
    obtain ⟨B, hB, he⟩ := (hmem H).mp hh
    refine ⟨B, hB, he, ?_⟩
    by_contra hn
    have hlow : hOf p.E p.cfg B < (controls p st).lo := Nat.lt_of_not_ge hn
    obtain ⟨hBX, hFB, hZB, W, hWX, hBW, hlo⟩ :=
      (KitFG.mem_filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mp hB
    have hlowH : (heightView p B).h < (controls p st).lo := by
      simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf]
        using hlow
    have hne : B ≠ W := by intro h; subst W; simp only [Height] at *; omega
    obtain ⟨C, hp, hng, hCW⟩ := KitFG.child_toward hBW hne
    have hBC : FGBlock.Preceq B C := by
      cases C with
      | genesis => exact False.elim (hng rfl)
      | node P s root r rs =>
        change P = B at hp
        subst P
        exact KitFG.preceq_parent_node _ _ _ _ _
    have hC : C ∈ D := (KitFG.mem_filteredFrom_of_bridge
      p.E p.cfg (heightView p) (heightView_bridge p) _ _ C).mpr
      ⟨hclosed W hWX C hCW, KitFG.preceq_trans hFB hBC,
        KitFG.preceq_trans hZB hBC, W, hWX, hCW, hlo⟩
    have hparent : (eraseFG C).parent? = some H := by
      cases C with
      | genesis => exact False.elim (hng rfl)
      | node P s root r rs =>
        change P = B at hp
        change some (eraseFG P) = some H
        rw [hp, he]
    have hel : eligible p st raw support (eraseFG C) = true := by
      have hf : ∃ P ∈ st.fg.TF, eraseFG P = (eraseFG C).parent ∧
          hOf p.E p.cfg P < (controls p st).lo :=
        ⟨B, hsub hBX, by rw [eraseFG_parent, hp], hlow⟩
      rw [fgsa_eligible_eq]
      simp only [hf, decide_true, Bool.true_or]
    have ht := hterminal (eraseFG C) ((hmem _).mpr ⟨C, hC, rfl⟩) hparent
    rw [hel] at ht
    cases ht
  · intro _ hnone
    apply walk_exact_of_dominated_suffix _ _ _ _ _ (block_preceq_refl _)
    · intro C hAC hCA
      have hp := (Bool.and_eq_true_iff.mp hAC).2
      have he := block_preceq_antisymm hp hCA
      subst C
      have hn := (Bool.and_eq_true_iff.mp hAC).1
      have hd : decide (liveRoot p st = liveRoot p st) = true := decide_eq_true rfl
      rw [hd] at hn
      cases hn
    · intro b hb hp
      obtain ⟨B, hB, rfl⟩ := (hmem b).mp hb
      exact hnone B hB hp
  · intro _ hne
    apply KitFG.filteredFrom_Z_mem p.E p.cfg _ X hclosed _ hne
    unfold Controls.Z
    split
    · exact hi.fg.FJ
    · exact KitFG.preceq_refl _

end AvailableChain.FGSA.Run
