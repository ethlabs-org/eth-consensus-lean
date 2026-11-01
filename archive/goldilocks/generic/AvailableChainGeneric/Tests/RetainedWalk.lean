module
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.Gen.Pure.Tests.RetainedWalk

open AvailableChain GridCO

def trunk : Block := .node .genesis 1 ⟨2⟩ 1
def trunkPeer : Block := .node .genesis 1 ⟨1⟩ 0
def endpoint : Block := .node trunk 2 ⟨4⟩ 1
def endpointPeer : Block := .node trunk 2 ⟨3⟩ 0
def fullTree : List Block := [.genesis, trunkPeer, trunk, endpointPeer, endpoint]
def retainedTree : List Block := [endpointPeer, endpoint]
def score (_ : Block) : Nat := 7
def eligible (_ : Block) : Bool := true

-- Both prefixes use the root tie when the scores are equal.
theorem retained_walk_root_ties :
    score trunkPeer = score trunk ∧ trunkPeer.root < trunk.root ∧
    ghostStep fullTree score eligible .genesis = some trunk ∧
    score endpointPeer = score endpoint ∧ endpointPeer.root < endpoint.root ∧
    ghostStep retainedTree score eligible trunk = some endpoint := by decide +kernel

-- Reverse list order also selects the greater root.
theorem retained_walk_tie_reverse_list :
    ghostStep [endpoint, endpointPeer] score eligible trunk = some endpoint := by decide +kernel

-- Strict score dominance cannot supply this test case.
theorem retained_walk_tie_not_dominated :
    ¬ DominatedSuffix trunk endpoint retainedTree score eligible := by
  intro h
  have hbest := (h endpoint (by decide) (by decide)).2.2
  have hlt := hbest endpointPeer (by decide) rfl rfl (by decide)
  exact (Nat.lt_irrefl 7) hlt

-- This suffix has one parent, so its local fields reduce to the splice.
theorem retained_walk_suffix_parent (X : Block)
    (hAX : Block.Preceq trunk X) (hXP : Block.Prec X endpoint) : X = trunk := by
  have hXA : Block.Preceq X trunk := by
    by_cases he : X = endpoint
    · subst X
      exact ((show ¬ Block.Prec endpoint endpoint by decide) hXP).elim
    · change (!decide (X = endpoint) &&
        (decide (X = endpoint) || Block.preceq X trunk)) = true at hXP
      change Block.preceq X trunk = true
      simpa [he] using hXP
  exact block_preceq_antisymm hXA hAX

theorem retained_walk_suffix_fields (sourceTree targetTree : List Block)
    (hstep : ghostStep sourceTree score eligible trunk = some endpoint)
    (hmem : endpoint ∈ targetTree)
    (hreflect : ∀ C ∈ targetTree, C.parent? = some trunk → C ∈ sourceTree) :
    SuffixPersists trunk endpoint sourceTree targetTree score eligible eligible ∧
    SuffixReflects trunk endpoint sourceTree targetTree eligible eligible ∧
    SuffixScoresAgree trunk endpoint targetTree score score eligible := by
  refine ⟨?_, ?_, ?_⟩
  · intro X C hAX hXP hs _
    rw [retained_walk_suffix_parent X hAX hXP, hstep] at hs
    cases hs
    exact ⟨hmem, rfl⟩
  · intro X C hAX hXP hm hp _
    rw [retained_walk_suffix_parent X hAX hXP] at hp
    exact ⟨hreflect C hm hp, rfl⟩
  · intro _ _ _ _ _ _ _
    rfl

-- Source start precedes target start. Both stored trunk blocks are removed.
theorem retained_walk_removed_trunk_transport :
    Block.Preceq .genesis trunk ∧ Block.Preceq trunk trunk ∧
    Block.Preceq trunk endpoint ∧ BestAncestry trunk trunk retainedTree score eligible ∧
    SuffixPersists trunk endpoint fullTree retainedTree score eligible eligible ∧
    SuffixReflects trunk endpoint fullTree retainedTree eligible eligible ∧
    SuffixScoresAgree trunk endpoint retainedTree score score eligible := by
  obtain ⟨hp, hr, hs⟩ := retained_walk_suffix_fields fullTree retainedTree
    (by decide +kernel) (by decide) (by
      intro C hm _
      simp only [retainedTree, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> simp [fullTree])
  exact ⟨by decide, by decide, by decide,
    walk_best_ancestry_of_cover trunk trunk retainedTree score eligible (by decide +kernel),
    hp, hr, hs⟩

theorem retained_walk_source_before_target :
    Block.Prec .genesis trunk ∧ trunk ∉ retainedTree ∧ .genesis ∉ retainedTree ∧
    Block.Preceq endpoint (ghost trunk retainedTree score eligible) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  obtain ⟨hsc, htc, hcp, hprefix, hp, hr, hs⟩ := retained_walk_removed_trunk_transport
  exact walk_covers_of_retained_transport .genesis trunk trunk endpoint
    fullTree retainedTree score score eligible eligible
    (by decide +kernel) (by decide +kernel) hsc htc hcp hprefix hp hr hs

-- Target start precedes source start. The target's nonempty prefix uses the root tie.
theorem retained_walk_lower_target_transport :
    Block.Preceq trunk trunk ∧ Block.Preceq .genesis trunk ∧
    Block.Preceq trunk endpoint ∧ BestAncestry .genesis trunk fullTree score eligible ∧
    SuffixPersists trunk endpoint retainedTree fullTree score eligible eligible ∧
    SuffixReflects trunk endpoint retainedTree fullTree eligible eligible ∧
    SuffixScoresAgree trunk endpoint fullTree score score eligible := by
  obtain ⟨hp, hr, hs⟩ := retained_walk_suffix_fields retainedTree fullTree
    (by decide +kernel) (by decide) (by
      intro C hm hp
      simp only [fullTree, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      · cases hp
      · cases hp
      · cases hp
      · simp [retainedTree]
      · simp [retainedTree])
  exact ⟨by decide, by decide, by decide,
    walk_best_ancestry_of_cover .genesis trunk fullTree score eligible (by decide +kernel),
    hp, hr, hs⟩

theorem retained_walk_target_before_source :
    Block.Prec .genesis trunk ∧
    Block.Preceq endpoint (ghost .genesis fullTree score eligible) := by
  refine ⟨by decide, ?_⟩
  obtain ⟨hsc, htc, hcp, hprefix, hp, hr, hs⟩ := retained_walk_lower_target_transport
  exact walk_covers_of_retained_transport trunk .genesis trunk endpoint
    retainedTree fullTree score score eligible eligible
    (by decide +kernel) (by decide +kernel) hsc htc hcp hprefix hp hr hs

-- An interval from a block to itself has no strict interior.
theorem retained_walk_self_interval (A X : Block)
    (hAX : Block.Preceq A X) (hXA : Block.Prec X A) : False := by
  have hXA' : Block.Preceq X A := (Bool.and_eq_true_iff.mp hXA).2
  have he := block_preceq_antisymm hAX hXA'
  subst X
  simp [Block.Prec, Block.prec] at hXA

theorem retained_walk_self_best (A : Block) (tree : List Block) :
    BestAncestry A A tree score eligible := by
  intro X hAX hXA
  exact (retained_walk_self_interval A X hAX hXA).elim

theorem retained_walk_self_suffix (A : Block) (sourceTree targetTree : List Block) :
    SuffixPersists A A sourceTree targetTree score eligible eligible ∧
    SuffixReflects A A sourceTree targetTree eligible eligible ∧
    SuffixScoresAgree A A targetTree score score eligible := by
  refine ⟨?_, ?_, ?_⟩
  · intro X C hAX hXA
    exact (retained_walk_self_interval A X hAX hXA).elim
  · intro X C hAX hXA
    exact (retained_walk_self_interval A X hAX hXA).elim
  · intro X C hAX hXA
    exact (retained_walk_self_interval A X hAX hXA).elim

-- Target start = cut = parent. The target prefix and tree are empty.
theorem retained_walk_zero_length_prefix :
    Block.Preceq endpoint (ghost endpoint [] score eligible) := by
  obtain ⟨hp, hr, hs⟩ := retained_walk_self_suffix endpoint retainedTree []
  exact walk_covers_of_retained_transport trunk endpoint endpoint endpoint
    retainedTree [] score score eligible eligible (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (retained_walk_self_best endpoint []) hp hr hs

-- The source result is strictly after parent. This exercises coverage, with cut = parent.
theorem retained_walk_source_coverage :
    Block.Prec trunk (ghost .genesis fullTree score eligible) ∧
    Block.Preceq trunk (ghost trunk [] score eligible) := by
  refine ⟨by decide +kernel, ?_⟩
  obtain ⟨hp, hr, hs⟩ := retained_walk_self_suffix trunk fullTree []
  exact walk_covers_of_retained_transport .genesis trunk trunk trunk
    fullTree [] score score eligible eligible (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (retained_walk_self_best trunk []) hp hr hs

-- Source start = parent. The target still has a nonempty best-order prefix.
theorem retained_walk_source_at_parent :
    Block.Preceq endpoint (ghost trunk retainedTree score eligible) := by
  obtain ⟨hp, hr, hs⟩ := retained_walk_self_suffix endpoint [] retainedTree
  exact walk_covers_of_retained_transport endpoint trunk endpoint endpoint
    [] retainedTree score score eligible eligible (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide)
    (walk_best_ancestry_of_cover trunk endpoint retainedTree score eligible (by decide +kernel))
    hp hr hs

-- Both trees are empty. All four blocks are the same anchor.
theorem retained_walk_empty_trees :
    Block.Preceq .genesis (ghost .genesis [] score eligible) := by
  obtain ⟨hp, hr, hs⟩ := retained_walk_self_suffix .genesis [] []
  exact walk_covers_of_retained_transport .genesis .genesis .genesis .genesis
    [] [] score score eligible eligible (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (retained_walk_self_best .genesis []) hp hr hs

-- Restrict and join a two-edge path. Both edges use equal-score root ties.
theorem retained_walk_best_split_join : BestAncestry .genesis endpoint fullTree score eligible := by
  have h : BestAncestry .genesis endpoint fullTree score eligible :=
    walk_best_ancestry_of_cover .genesis endpoint fullTree score eligible (by decide +kernel)
  obtain ⟨hab, hbc⟩ := bestAncestry_restrict .genesis trunk endpoint fullTree score eligible
    h (by decide) (by decide)
  exact bestAncestry_concat .genesis trunk endpoint fullTree score eligible
    hab hbc (by decide) (by decide)

-- A target prefix that loses the root tie cannot satisfy BestAncestry.
theorem retained_walk_losing_target_prefix :
    ¬ BestAncestry .genesis trunkPeer fullTree score eligible := by
  intro h
  have he := walk_reanchor_of_best_ancestry .genesis trunkPeer fullTree score eligible
    (by decide +kernel) (by decide) h
  exact (show ghost .genesis fullTree score eligible ≠
    ghost trunkPeer fullTree score eligible by decide +kernel) he

-- A single eligible child has a strictly dominated suffix and a best-order path.
theorem retained_walk_dominated_adapter :
    BestAncestry trunk endpoint [endpoint] score eligible := by
  apply bestAncestry_of_dominatedSuffix
  intro C hAC hCE
  have he : C = endpoint := by
    by_contra hne
    have hCp : Block.Prec C endpoint := by
      change (!decide (C = endpoint) && Block.preceq C endpoint) = true
      simp only [hne, decide_false, Bool.not_false, Bool.true_and]
      exact hCE
    have hC := retained_walk_suffix_parent C (Bool.and_eq_true_iff.mp hAC).2 hCp
    subst C
    exact (retained_walk_self_interval trunk trunk (block_preceq_refl _) hAC)
  subst C
  refine ⟨by decide, rfl, ?_⟩
  intro D hm _ _ hne
  exact (hne (List.mem_singleton.mp hm)).elim

end AvailableChain.Gen.Pure.Tests.RetainedWalk
