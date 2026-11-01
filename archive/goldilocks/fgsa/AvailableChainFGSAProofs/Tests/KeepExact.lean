module
public import AvailableChainFGSAProofs.Proofs.Shared.KeepExact -- shake: keep (pivot axiom audit)

set_option linter.privateModule false

/-! R-F1b rounds 1 and 2. These private tests use the exact quantified
`hancestry` binder of `exactHead_of_pivot_ancestry` and its Gen path kernel.
The empty target fails membership; the score tie fails the root conjunct.
No store invariant, row, or extra axiom is used. -/
namespace AvailableChain.FGSA.Run.Tests.KeepExact
open AvailableChain.Gen.Pure

-- All walk premises after the proposed start-only generalization hold,
-- but neither target coverage nor exactness holds.
theorem upperStartEmptyTreeCounterexample (P : Block)
    (hstrict : Block.Prec .genesis P) (score score' : Block → Nat)
    (elig elig' : Block → Bool) :
    (Block.Preceq .genesis P ∧ Block.Preceq P P) ∧
    Block.Preceq .genesis .genesis ∧
    DominatedSuffix P .genesis [] score elig ∧
    DominatedSuffix .genesis .genesis [] score' elig' ∧
    Block.Preceq P (GridCO.ghost P [] score elig) ∧
    SuffixPersists .genesis P [] [] score elig elig' ∧
    SuffixReflects .genesis P [] [] elig elig' ∧
    SuffixScoresAgree .genesis P [] score score' elig' ∧
    P = P ∧ AnchorClosed .genesis [] ∧ NoEligibleChild [] elig' P ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [] score' elig') ∧
    GridCO.ghost .genesis [] score' elig' ≠ P := by
  have hne : P ≠ .genesis := by
    intro he
    subst P
    simp [Block.Prec, Block.prec] at hstrict
  have hnot : ¬ Block.Preceq P .genesis := by
    intro h
    have he : P = .genesis := of_decide_eq_true h
    exact hne he
  have hd (A : Block) : DominatedSuffix A .genesis [] score elig := by
    intro C hAC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec, Block.preceq] at hAC
  refine ⟨⟨?_, block_preceq_refl _⟩, block_preceq_refl _, hd P, ?_,
    block_preceq_refl _, ?_, ?_, ?_, rfl, ?_, ?_, hnot, Ne.symm hne⟩
  · exact block_genesis_preceq P
  · intro C hAC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec] at hAC
  · intro X C _ _ hs _
    cases hs
  · intro X C _ _ hm
    cases hm
  · intro X C _ _ hm
    cases hm
  · intro B hm
    cases hm
  · intro C hm
    cases hm

#print axioms upperStartEmptyTreeCounterexample

-- The proposed ancestry premise excludes the round-1 empty target.
-- Membership, before eligibility or maximality, is already impossible.
theorem emptyTargetAncestryPremiseFails (P : Block)
    (hstrict : Block.Prec .genesis P) (score : Block → Nat) (elig : Block → Bool) :
    ¬ (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧ C ∈ ([] : List Block) ∧
        elig C = true ∧ ∀ D ∈ ([] : List Block), D.parent? = some X →
          elig D = true → score D ≤ score C ∧
          (score D = score C → D.root ≤ C.root)) := by
  intro hancestry
  obtain ⟨C, _, _, hmem, _, _⟩ := hancestry .genesis (block_preceq_refl _) hstrict
  cases hmem

#print axioms emptyTargetAncestryPremiseFails

-- P and its rival have equal score. The rival has the greater root.
private def P : Block := .node .genesis 1 ⟨1⟩ 0
private def D : Block := .node .genesis 1 ⟨2⟩ 1

example : P.root < D.root := by decide
example : GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true) = D := by decide

-- This is the literal ancestry premise: target membership, eligibility,
-- and maximal score. It does not specify which child wins a score tie.
theorem maximalScoreAncestryCounterexample :
    (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [P, D], B.parent? = some X →
          (fun _ : Block => true) B = true → (0 : Nat) ≤ 0) ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true)) ∧
    GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true) ≠ P := by
  refine ⟨?_, by decide, by decide⟩
  intro X _ hXP
  have hX : X = .genesis := by
    by_cases he : X = P
    · subst X; simp [Block.Prec, Block.prec] at hXP
    · have hp : Block.preceq X P = true := (Bool.and_eq_true_iff.mp hXP).2
      have hh : X = P ∨ X = .genesis := by
        simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hp)
      exact hh.resolve_left he
  subst X
  exact ⟨P, rfl, block_preceq_refl _, by simp, rfl, by intros; omega⟩

#print axioms maximalScoreAncestryCounterexample

private theorem belowP (X : Block) (hXP : Block.Prec X P) : X = .genesis := by
  by_cases he : X = P
  · subst X; simp [Block.Prec, Block.prec] at hXP
  · have hp : Block.preceq X P = true := (Bool.and_eq_true_iff.mp hXP).2
    have hh : X = P ∨ X = .genesis := by
      simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hp)
    exact hh.resolve_left he

-- Both start disjunctions and all old walk premises still hold.
-- T = genesis, source start = P, target start = T, Q = P.
-- The target includes genesis so AnchorClosed also holds.
theorem maximalScoreAllWalkPremisesCounterexample :
    (Block.Preceq .genesis P ∧ Block.Preceq P P) ∧
    Block.Preceq .genesis .genesis ∧ Block.Preceq .genesis P ∧
    DominatedSuffix P .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ∧
    DominatedSuffix .genesis .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ∧
    Block.Preceq P (GridCO.ghost P [.genesis, P, D] (fun _ => 0) (fun _ => true)) ∧
    SuffixPersists .genesis P [.genesis, P, D] [.genesis, P, D]
      (fun _ => 0) (fun _ => true) (fun _ => true) ∧
    SuffixReflects .genesis P [.genesis, P, D] [.genesis, P, D]
      (fun _ => true) (fun _ => true) ∧
    SuffixScoresAgree .genesis P [.genesis, P, D] (fun _ => 0) (fun _ => 0) (fun _ => true) ∧
    (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [.genesis, P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [.genesis, P, D], B.parent? = some X →
          (fun _ : Block => true) B = true → (0 : Nat) ≤ 0) ∧
    P = P ∧ AnchorClosed .genesis [.genesis, P, D] ∧
    NoEligibleChild [.genesis, P, D] (fun _ => true) P ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true)) ∧
    GridCO.ghost .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ≠ P := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, ?_, ?_, by decide,
    ?_, ?_, ?_, ?_, rfl, ?_, ?_, by decide, by decide⟩
  · intro C hPC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec, Block.preceq, P] at hPC
  · intro C hTC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec] at hTC
  · intro X C _ hXP hs _
    have hX := belowP X hXP
    subst X
    have hsD : GridCO.ghostStep [.genesis, P, D] (fun _ => 0) (fun _ => true)
        .genesis = some D := by decide
    rw [hsD] at hs
    have he := Option.some.inj hs
    subst C
    exact ⟨by simp, rfl⟩
  · intro X C _ _ hm _ hel
    exact ⟨hm, hel⟩
  · rw [SuffixScoresAgree_def]; intros; rfl
  · intro X _ hXP
    have hX := belowP X hXP
    subst X
    exact ⟨P, rfl, block_preceq_refl _, by simp, rfl, by intros; omega⟩
  · intro B hB _ C _ hCB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB ⊢
    rcases hB with rfl | rfl | rfl
    · exact Or.inl (of_decide_eq_true hCB)
    · have hh : C = P ∨ C = .genesis := by
        simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCB)
      rcases hh with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · have hh : C = D ∨ C = .genesis := by
        simpa only [D, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCB)
      rcases hh with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
  · intro C hC hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl <;> cases hp

#print axioms maximalScoreAllWalkPremisesCounterexample

-- The full ancestry premise in the new theorem excludes the round-2 witness.
-- All numerical scores are equal. D wins because its root is greater.
theorem rootTieAncestryPremiseFails :
    ¬ (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [.genesis, P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [.genesis, P, D], B.parent? = some X →
          (fun _ : Block => true) B = true →
          (0 : Nat) ≤ 0 ∧ ((0 : Nat) = 0 → B.root ≤ C.root)) := by
  intro hancestry
  obtain ⟨C, hp, hCP, _, _, hbest⟩ :=
    hancestry .genesis (block_preceq_refl _) (by decide)
  have hC : C = P := by
    have hh : C = P ∨ C = .genesis := by
      simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCP)
    rcases hh with he | rfl
    · exact he
    · cases hp
  subst C
  have hbad := (hbest D (by simp) rfl rfl).2 rfl
  exact (by decide : ¬ D.root ≤ P.root) hbad

#print axioms rootTieAncestryPremiseFails
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry

namespace HighStart
open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def c : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def f : FGBlock (Fin 1) := .node c 2 ⟨3⟩ 0 []
private def p : FGBlock (Fin 1) := .node f 3 ⟨4⟩ 0 []
private def q : FGBlock (Fin 1) := .node p 4 ⟨5⟩ 0 []
private def T : Block := .genesis
private def C : Block := eraseFG c
private def F : Block := eraseFG f
private def P : Block := eraseFG p
private def Q : Block := eraseFG q

-- RD-1 geometry. The raw tree retains the trunk; the target domain removes it.
private def st : State 1 :=
  { initial 1 with
    base := { (initial 1).base with blocks := [T, C, F, P, Q] }
    fg := { TF := {.genesis, c, f, p, q}, F := f, J := f, h_j := 0, h_max := 1 } }

private def votes : List (GridCO.Wire 1 .root) := [⟨.seat 4 0, .head Q.root⟩]

private theorem geometry :
    Block.Prec T C ∧ Block.Prec C F ∧ Block.Prec F P ∧ Block.Prec P Q ∧
    liveRoot params st = F ∧
    erasedList st (domainR params st st.fg.TF) = [F, P, Q] ∧
    (∀ B ∈ [F, P, Q], GridCO.goldfishScore st.base.blocks votes votes B = 1 ∧
      eligible params st votes votes B = true) := by decide +kernel

private theorem between (X : Block) (hFX : Block.Preceq F X)
    (hXP : Block.Prec X P) : X = F := by
  have hne : X ≠ P := by
    intro he
    subst X
    simp [Block.Prec, Block.prec] at hXP
  have hXF : Block.Preceq X F := by
    have h := (Bool.and_eq_true_iff.mp hXP).2
    change (decide (X = P) || Block.preceq X F) = true at h
    exact (Bool.or_eq_true_iff.mp h).resolve_left (by simpa using hne)
  exact block_preceq_antisymm hXF hFX

-- The new premise holds although C is absent from the target domain.
private theorem ancestry :
    ∀ X, Block.Preceq T X → Block.Preceq (liveRoot params st) X → Block.Prec X P →
      ∃ B, B.parent? = some X ∧ Block.Preceq B P ∧
        B ∈ erasedList st (domainR params st st.fg.TF) ∧
        eligible params st votes votes B = true ∧
        ∀ D ∈ erasedList st (domainR params st st.fg.TF), D.parent? = some X →
          eligible params st votes votes D = true →
          GridCO.goldfishScore st.base.blocks votes votes D ≤
            GridCO.goldfishScore st.base.blocks votes votes B ∧
          (GridCO.goldfishScore st.base.blocks votes votes D =
            GridCO.goldfishScore st.base.blocks votes votes B → D.root ≤ B.root) := by
  intro X _ hFX hXP
  have hroot : liveRoot params st = F := geometry.2.2.2.2.1
  rw [hroot] at hFX
  obtain rfl := between X hFX hXP
  refine ⟨P, rfl, block_preceq_refl _, ?_⟩
  decide +kernel

-- Apply the exact-head theorem itself, with no lower-prefix obligation.
private theorem exactHead :
    headInTree params st (erasedList st (domainR params st st.fg.TF)) votes votes = Q := by
  apply exactHead_of_pivot_ancestry params st st.fg.TF votes votes T P Q
    (by decide +kernel) (Or.inr (by decide +kernel)) (by decide +kernel) ancestry
  · right
    decide +kernel
  · change ∀ B ∈ [F, P, Q], B.parent? = some Q → eligible params st votes votes B = false
    decide +kernel

#print axioms geometry
#print axioms ancestry
#print axioms exactHead

end HighStart

-- Gen positive case: genesis < P < target, with P as the walk anchor.
private theorem intermediateAnchorReanchor :
    let target := Block.node P 2 ⟨6⟩ 0
    Block.Prec .genesis P ∧ Block.Prec P target ∧
      GridCO.ghost P [P, target] (fun _ => 1) (fun _ => true) =
        GridCO.ghost target [P, target] (fun _ => 1) (fun _ => true) := by
  dsimp only
  refine ⟨by decide, by decide, ?_⟩
  apply walk_reanchor_of_best_ancestry _ _ _ _ _ (by decide) (by decide)
  exact walk_best_ancestry_of_cover _ _ _ _ _ (by decide)

#print axioms intermediateAnchorReanchor

end AvailableChain.FGSA.Run.Tests.KeepExact
