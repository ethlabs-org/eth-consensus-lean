module
public import AvailableChainPCSAProofs.Proofs.Shared.RetainedWalk
public import AvailableChainGridCO.Proofs.StoreFacts

public section

/-! C6 RetainedProposal: concrete receipt and count support. -/
namespace AvailableChain.PCSA
open Gen.Pure
private theorem retained_prec_iff (A B : Block) :
    Block.Prec A B ↔ A ≠ B ∧ Block.Preceq A B := by
  change ((!decide (A = B) && Block.preceq A B) = true ↔
    A ≠ B ∧ Block.preceq A B = true)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
private theorem retained_parent_prefix (A C : Block) (hp : C.parent? = some A) :
    Block.Preceq A C := by
  cases C with
  | genesis => cases hp
  | node P s r app =>
    have he := Option.some.inj hp
    subst A
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
private theorem retained_prefix_parent (C B : Block) (hc : Block.Preceq C B) (hn : C ≠ B) :
    Block.Preceq C B.parent := by
  cases B with
  | genesis => exact hc
  | node P s r app =>
    change (decide (C = .node P s r app) || Block.preceq C P) = true at hc
    exact (Bool.or_eq_true_iff.mp hc).resolve_left (fun he => hn (of_decide_eq_true he))
private theorem retained_between_child (parent proposal C : Block)
    (hp : proposal.parent? = some parent) (hPC : Block.Prec parent C)
    (hCP : Block.Preceq C proposal) : C = proposal := by
  by_contra hn
  have hCparent := retained_prefix_parent C proposal hCP hn
  have he : proposal.parent = parent := by
    cases proposal with
    | genesis => cases hp
    | node Q s r app => exact Option.some.inj hp
  rw [he] at hCparent
  exact (retained_prec_iff parent C).mp hPC |>.1
    (block_preceq_antisymm ((retained_prec_iff parent C).mp hPC).2 hCparent)
/-- Equal concrete walk inputs and a retained parent path select the unique new proposal. -/
theorem pcsa_retained_proposal_walk (sourceRoot targetRoot parent proposal : Block)
    (sourceTree targetTree : List Block) (sourceScore targetScore : Block → Nat)
    (sourceEligible targetEligible : Block → Bool)
    (hsrcRoots : ∀ A ∈ sourceTree, ∀ B ∈ sourceTree, A.root = B.root → A = B)
    (hsrcClosed : AnchorClosed sourceRoot sourceTree)
    (hdstRoots : ∀ A ∈ targetTree, ∀ B ∈ targetTree, A.root = B.root → A = B)
    (hsource : GridCO.ghost sourceRoot sourceTree sourceScore sourceEligible = parent)
    (hsrcParent : Block.Preceq sourceRoot parent) (hdstParent : Block.Preceq targetRoot parent)
    (hrootPath : Block.Preceq sourceRoot targetRoot ∨
      Block.Preceq sourceRoot (GridCO.ghost targetRoot targetTree targetScore targetEligible))
    (hparent : proposal.parent? = some parent)
    (hproposal : proposal ∈ targetTree) (hproposalEligible : targetEligible proposal = true)
    (hpath : ∀ C, Block.Preceq C parent → C ∈ targetTree)
    (htree : ∀ C ∈ targetTree, C = proposal ∨ C ∈ sourceTree)
    (hscores : ∀ C, sourceScore C = targetScore C)
    (heligible : ∀ C, sourceEligible C = targetEligible C)
    (hstop : NoEligibleChild targetTree targetEligible proposal) :
    GridCO.ghost targetRoot targetTree targetScore targetEligible = proposal := by
  have persists (cut : Block) : SuffixPersists cut parent sourceTree targetTree
      sourceScore sourceEligible targetEligible := by
    intro X C _ _ hs hc
    exact ⟨hpath C hc, (heligible C).symm.trans
      (GridCO.ghostStep_child sourceTree sourceScore sourceEligible X C hs).2.2⟩
  have reflects (cut : Block) : SuffixReflects cut parent sourceTree targetTree
      sourceEligible targetEligible := by
    intro X C _ hxp hc hp he
    rcases htree C hc with rfl | hm
    · have hX : X = parent := Option.some.inj (hp.symm.trans hparent)
      exact ((retained_prec_iff X parent).mp hxp).1 hX |>.elim
    · exact ⟨hm, (heligible C).trans he⟩
  have scores (cut : Block) : SuffixScoresAgree cut parent targetTree sourceScore targetScore
      targetEligible := by
    intro X C _ _ _ _ _
    exact (hscores C).symm
  have hcover : Block.Preceq parent (GridCO.ghost targetRoot targetTree targetScore
    targetEligible) := by
    by_cases hsrcDst : Block.Preceq sourceRoot targetRoot
    · apply walk_covers_of_retained_transport sourceRoot targetRoot targetRoot parent
        sourceTree targetTree sourceScore targetScore sourceEligible targetEligible hdstRoots
        (by rw [hsource]; exact block_preceq_refl _) hsrcDst (block_preceq_refl _) hdstParent
        ?_ (persists _) (reflects _) (scores _)
      intro X hr hx
      have hX := block_preceq_antisymm hr ((retained_prec_iff X targetRoot).mp hx).2
      exact ((retained_prec_iff X targetRoot).mp hx).1 hX.symm |>.elim
    · have hsrcCovered := hrootPath.resolve_left hsrcDst
      have hdstSrc := (block_preceq_total_of_common hsrcParent hdstParent).resolve_left hsrcDst
      exact walk_covers_of_retained_transport sourceRoot targetRoot sourceRoot parent
        sourceTree targetTree sourceScore targetScore sourceEligible targetEligible hdstRoots
        (by rw [hsource]; exact block_preceq_refl _) (block_preceq_refl _) hdstSrc hsrcParent
        (walk_best_ancestry_of_cover targetRoot sourceRoot targetTree targetScore targetEligible
          hsrcCovered) (persists _) (reflects _) (scores _)
  have hsplice := walk_reanchor_of_best_ancestry targetRoot parent targetTree targetScore
    targetEligible hdstRoots hdstParent
    (walk_best_ancestry_of_cover targetRoot parent targetTree targetScore targetEligible hcover)
  rw [hsplice]
  apply walk_exact_of_dominated_suffix parent proposal targetTree targetScore targetEligible
    (retained_parent_prefix parent proposal hparent) ?_ hstop
  intro C hPC hCP
  have hC : C = proposal := retained_between_child parent proposal C hparent hPC hCP
  subst C
  refine ⟨hproposal, hproposalEligible, ?_⟩
  intro D hD hDp hDe hne
  rcases htree D hD with hEq | hmem
  · exact (hne hEq).elim
  · have hnone := walk_noEligibleChild_of_anchorClosed sourceRoot sourceTree sourceScore
      sourceEligible hsrcRoots hsrcClosed D hmem
    rw [hsource] at hnone
    have hzero := hnone (hDp.trans hparent)
    rw [heligible D, hDe] at hzero
    cases hzero
end AvailableChain.PCSA

end
