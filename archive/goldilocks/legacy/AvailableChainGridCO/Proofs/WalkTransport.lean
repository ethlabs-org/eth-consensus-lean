module
public import AvailableChainGridCO.Proofs.Walk

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

/- The list version of the reference `ProposalWalkTransportCore.lean`.
The selected child must persist, every eligible target child must come
from the source, and scores must agree. Anchors can move backwards only
when a separate path to the common pivot is available. -/

private def rankLE (score : Block → Nat) (A B : Block) : Prop :=
  score A ≤ score B ∧ (score A = score B → A.root ≤ B.root)

private theorem rank_refl (score : Block → Nat) (A : Block) : rankLE score A A :=
  ⟨le_refl _, fun _ => le_refl _⟩

private theorem rank_trans (score : Block → Nat) (A B C : Block)
    (hab : rankLE score A B) (hbc : rankLE score B C) : rankLE score A C := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro he
  have hab0 := hab.1
  have hbc0 := hbc.1
  have hab' : score A = score B := by omega
  have hbc' : score B = score C := by omega
  exact (hab.2 hab').trans (hbc.2 hbc')

private def choose (score : Block → Nat) (best : Option Block) (B : Block) : Option Block :=
  match best with
  | none => some B
  | some A =>
      if score A < score B || (score A == score B && A.root < B.root)
      then some B else best

private theorem choose_bounds (score : Block → Nat) (best : Option Block) (B C : Block)
    (h : choose score best B = some C) :
    rankLE score B C ∧ ∀ A, best = some A → rankLE score A C := by
  cases best with
  | none => cases h; exact ⟨rank_refl _ _, by simp⟩
  | some A =>
      simp only [choose] at h
      split at h
      · rename_i hlt
        cases h
        refine ⟨rank_refl _ _, ?_⟩
        intro D hd
        cases hd
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hlt
        rcases hlt with hs | ⟨hs, hr⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨hs.le, fun _ => hr.le⟩
      · rename_i hlt
        cases h
        refine ⟨?_, ?_⟩
        · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq] at hlt
          push Not at hlt
          exact ⟨hlt.1, fun he => hlt.2 he.symm⟩
        · intro D hd
          cases hd
          exact rank_refl _ _

private theorem fold_bounds (score : Block → Nat) (xs : List Block)
    (best : Option Block) (C : Block) (h : xs.foldl (choose score) best = some C) :
    (∀ A, best = some A → rankLE score A C) ∧
      ∀ A ∈ xs, rankLE score A C := by
  induction xs generalizing best with
  | nil => exact ⟨by intro A ha; cases ha; cases h; exact rank_refl _ _, by simp⟩
  | cons B xs ih =>
      have hi := ih (choose score best B) h
      have hex : ∃ D, choose score best B = some D := by
        cases best <;> simp only [choose]
        · exact ⟨B, rfl⟩
        · split <;> exact ⟨_, rfl⟩
      obtain ⟨D, hd⟩ := hex
      have hb := choose_bounds score best B D hd
      refine ⟨fun A ha => rank_trans score A D C (hb.2 A ha) (hi.1 D hd), ?_⟩
      intro A ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact rank_trans score _ D C hb.1 (hi.1 D hd)
      · exact hi.2 A ha

/-- A selected child maximizes score, then root, among eligible siblings. -/
theorem ghostStep_best (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block)
    (h : ghostStep tree score eligible anchor = some C) :
    ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D ≤ score C ∧ (score D = score C → D.root ≤ C.root) := by
  let children := tree.filter (fun B => B.parent? == some anchor && eligible B)
  change (match children.foldl (choose score) none with
    | none => none
    | some B => if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C at h
  cases hf : children.foldl (choose score) none with
  | none => simp [hf] at h
  | some B =>
      simp only [hf] at h
      split at h
      · contradiction
      · cases h
        intro D hd hp he
        exact (fold_bounds score children none _ hf).2 D
          (List.mem_filter.mpr ⟨hd, by simp [hp, he]⟩)

/-- Unique roots make a maximal eligible child the selected child.
This includes equal-score ties, with the greatest root selected. -/
theorem ghostStep_of_best (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block) (hroot : RootInjectiveBelow tree)
    (hc : C ∈ tree) (hp : C.parent? = some anchor) (he : eligible C = true)
    (hbest : ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D ≤ score C ∧ (score D = score C → D.root ≤ C.root)) :
    ghostStep tree score eligible anchor = some C := by
  cases hs : ghostStep tree score eligible anchor with
  | none =>
      have hf := (ghostStep_none_iff_of_rootInjective tree score eligible anchor hroot).mp hs
        C hc hp
      rw [he] at hf
      contradiction
  | some D =>
      have hd := ghostStep_child tree score eligible anchor D hs
      have hDC := hbest D hd.1 hd.2.1 hd.2.2
      have hCD := ghostStep_best tree score eligible anchor D hs C hc hp he
      have hscore : score D = score C := Nat.le_antisymm hDC.1 hCD.1
      have heq := hroot D C ⟨D, hd.1, block_preceq_self D⟩
        ⟨C, hc, block_preceq_self C⟩ (le_antisymm (hDC.2 hscore) (hCD.2 hscore.symm))
      subst D
      rfl

/-- Restriction to reflected candidates preserves a selected child when
it remains eligible and the scores of retained candidates agree. -/
theorem ghostStep_transport_of_subset (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (anchor C : Block) (hroot : RootInjectiveBelow targetTree)
    (hsource : ghostStep sourceTree sourceScore sourceEligible anchor = some C)
    (hkeep : C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ D ∈ targetTree, D.parent? = some anchor → targetEligible D = true →
      D ∈ sourceTree ∧ sourceEligible D = true)
    (hscore : ∀ D ∈ targetTree, D.parent? = some anchor → targetEligible D = true →
      targetScore D = sourceScore D) :
    ghostStep targetTree targetScore targetEligible anchor = some C := by
  have hc := ghostStep_child sourceTree sourceScore sourceEligible anchor C hsource
  apply ghostStep_of_best targetTree targetScore targetEligible anchor C hroot
    hkeep.1 hc.2.1 hkeep.2
  intro D hd hp he
  have hr := hreflect D hd hp he
  rw [hscore D hd hp he, hscore C hkeep.1 hc.2.1 hkeep.2]
  exact ghostStep_best sourceTree sourceScore sourceEligible anchor C hsource D hr.1 hp hr.2

/-- Removing duplicate entries does not change the selected child. -/
theorem ghostStep_eraseDups (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) (hroot : RootInjectiveBelow tree) :
    ghostStep tree.eraseDups score eligible anchor = ghostStep tree score eligible anchor := by
  have hr : RootInjectiveBelow tree.eraseDups := by
    intro A B hA hB he
    obtain ⟨C, hc, hAC⟩ := hA
    obtain ⟨D, hd, hBD⟩ := hB
    exact hroot A B ⟨C, List.mem_eraseDups.mp hc, hAC⟩
      ⟨D, List.mem_eraseDups.mp hd, hBD⟩ he
  cases hs : ghostStep tree score eligible anchor with
  | none =>
      apply (ghostStep_none_iff_of_rootInjective _ _ _ _ hr).mpr
      intro B hb hp
      exact (ghostStep_none_iff_of_rootInjective _ _ _ _ hroot).mp hs B
        (List.mem_eraseDups.mp hb) hp
  | some C =>
      have hc := ghostStep_child tree score eligible anchor C hs
      exact ghostStep_transport_of_subset tree tree.eraseDups score score eligible eligible
        anchor C hr hs ⟨List.mem_eraseDups.mpr hc.1, hc.2.2⟩
        (fun D hd _ he => ⟨List.mem_eraseDups.mp hd, he⟩) (by intros; rfl)

private theorem prefix_depth (A B : Block) (h : Block.Preceq A B) : A.depth ≤ B.depth := by
  induction B with
  | genesis => have : A = .genesis := by simpa [Block.Preceq, Block.preceq] using h
               subst A; rfl
  | node P s r_s id ih =>
      obtain he | hp : A = .node P s r_s id ∨ Block.Preceq A P := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using h
      · subst A; rfl
      · exact (ih hp).trans (Nat.le_succ _)

private theorem prefix_eq_of_depth (A B : Block) (h : Block.Preceq A B)
    (hd : B.depth ≤ A.depth) : A = B := by
  cases B with
  | genesis => simpa [Block.Preceq, Block.preceq] using h
  | node P s r_s id =>
      obtain he | hp : A = .node P s r_s id ∨ Block.Preceq A P := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using h
      · exact he
      · have := prefix_depth A P hp
        change P.depth + 1 ≤ A.depth at hd
        omega

private theorem child_depth (A C : Block) (h : C.parent? = some A) :
    C.depth = A.depth + 1 := by
  cases C <;> simp_all [Block.parent?, Block.depth]

private theorem parent_prefix (A C : Block) (h : C.parent? = some A) :
    Block.Preceq A C := by
  cases C with
  | genesis => simp [Block.parent?] at h
  | node P s r_s id =>
      have he : P = A := by simpa [Block.parent?] using h
      subst P
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_self A))

/-- Every strict intermediate ancestor of a walk result has a selected
next child on the same path. No root premise is needed for this direction. -/
theorem ghostWalk_step_towards_result (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (A H X : Block)
    (hwalk : ghostWalk tree score eligible fuel A = H)
    (hAX : Block.Preceq A X) (hXH : Block.Preceq X H) (hne : X ≠ H) :
    ∃ C, ghostStep tree score eligible X = some C ∧ Block.Preceq C H := by
  induction fuel generalizing A with
  | zero =>
      change A = H at hwalk
      subst H
      exact (hne (prefix_eq_of_depth X A hXH (prefix_depth A X hAX))).elim
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible A with
      | none =>
          simp only [ghostWalk, hs] at hwalk
          subst H
          exact (hne (prefix_eq_of_depth X A hXH (prefix_depth A X hAX))).elim
      | some C =>
          have hw : ghostWalk tree score eligible fuel C = H := by
            simpa only [ghostWalk, hs] using hwalk
          have hCH : Block.Preceq C H := by
            rw [← hw]
            exact ghostWalk_extends tree score eligible fuel C
          by_cases hXA : X = A
          · subst X; exact ⟨C, hs, hCH⟩
          · apply ih C hw ?_
            rcases Bool.or_eq_true_iff.mp (ancestors_compatible C X H hCH hXH) with hCX | hXC
            · exact hCX
            · have hAd : A.depth < X.depth := by
                have hd := prefix_depth A X hAX
                have hneq : X.depth ≠ A.depth := by
                  intro he
                  exact hXA (prefix_eq_of_depth A X hAX he.le).symm
                omega
              have hCd := child_depth A C (ghostStep_child tree score eligible A C hs).2.1
              have he := prefix_eq_of_depth X C hXC (by omega)
              rw [he]
              exact block_preceq_self C

/-- The public GHOST result supplies a next step at each strict ancestor
on its path. Duplicate removal is transparent under the root premise. -/
theorem ghost_step_towards_result (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (A H X : Block) (hroot : RootInjectiveBelow tree)
    (hwalk : ghost A tree score eligible = H)
    (hAX : Block.Preceq A X) (hXH : Block.Preceq X H) (hne : X ≠ H) :
    ∃ C, ghostStep tree score eligible X = some C ∧ Block.Preceq C H := by
  obtain ⟨C, hs, hc⟩ := ghostWalk_step_towards_result tree.eraseDups score eligible
    tree.eraseDups.length A H X hwalk hAX hXH hne
  rw [ghostStep_eraseDups tree score eligible X hroot] at hs
  exact ⟨C, hs, hc⟩

private theorem walk_covers_steps (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (base B : Block)
    (hstep : ∀ X, Block.Preceq base X → Block.Preceq X B → X ≠ B →
      ∃ C, ghostStep tree score eligible X = some C ∧ Block.Preceq C B)
    (fuel : Nat) (A : Block) (hbase : Block.Preceq base A) (ha : Block.Preceq A B)
    (hf : B.depth ≤ A.depth + fuel) : Block.Preceq B (ghostWalk tree score eligible fuel A) := by
  induction fuel generalizing A with
  | zero =>
      have he := prefix_eq_of_depth A B ha (by simpa using hf)
      subst A
      exact block_preceq_self _
  | succ fuel ih =>
      by_cases he : A = B
      · subst A; exact ghostWalk_extends tree score eligible _ B
      · obtain ⟨C, hs, hCB⟩ := hstep A hbase ha he
        have hchild := ghostStep_child tree score eligible A C hs
        have hd := child_depth A C hchild.2.1
        have hAC := parent_prefix A C hchild.2.1
        rw [ghostWalk, hs]
        exact ih C (prefix_trans base A C hbase hAC) hCB (by omega)

/-- Selected path steps suffice for coverage; the stored path bounds fuel. -/
theorem ghost_covers_of_steps (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (A B : Block) (hroot : RootInjectiveBelow tree)
    (ha : Block.Preceq A B)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (hstep : ∀ X, Block.Preceq A X → Block.Preceq X B → X ≠ B →
      ∃ C, ghostStep tree score eligible X = some C ∧ Block.Preceq C B) :
    Block.Preceq B (ghost A tree score eligible) := by
  apply walk_covers_steps tree.eraseDups score eligible A B ?_
    tree.eraseDups.length A (block_preceq_self A) ha
    ((depth_le_ghost_fuel tree B hpath).trans (Nat.le_add_left _ _))
  intro X hAX hXB hne
  obtain ⟨C, hs, hc⟩ := hstep X hAX hXB hne
  exact ⟨C, (ghostStep_eraseDups tree score eligible X hroot).trans hs, hc⟩

/-- A source walk transfers to a new tree. Candidate retention, candidate
reflection, and score equality are explicit. The target anchor is on the
source path; this theorem does not infer that fact from compatibility. -/
theorem ghost_transport_covers (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (sourceAnchor targetAnchor H : Block)
    (hsourceRoot : RootInjectiveBelow sourceTree) (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : ghost sourceAnchor sourceTree sourceScore sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor targetAnchor ∧ Block.Preceq targetAnchor H)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C H → C ∈ targetTree)
    (hkeep : ∀ X C, Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ghostStep sourceTree sourceScore sourceEligible X = some C → Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X D, Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      D ∈ targetTree → D.parent? = some X → targetEligible D = true →
      D ∈ sourceTree ∧ sourceEligible D = true)
    (hscore : ∀ D, D ∈ sourceTree → D ∈ targetTree → targetScore D = sourceScore D) :
    Block.Preceq H (ghost targetAnchor targetTree targetScore targetEligible) := by
  apply ghost_covers_of_steps targetTree targetScore targetEligible targetAnchor H
    htargetRoot hanchors.2 hpath
  intro X hAX hXH hne
  obtain ⟨C, hs, hCH⟩ := ghost_step_towards_result sourceTree sourceScore sourceEligible
    sourceAnchor H X hsourceRoot hsource
    (prefix_trans sourceAnchor targetAnchor X hanchors.1 hAX) hXH hne
  refine ⟨C, ?_, hCH⟩
  apply ghostStep_transport_of_subset sourceTree targetTree sourceScore targetScore
    sourceEligible targetEligible X C htargetRoot hs (hkeep X C hAX hXH hne hs hCH)
    (hreflect X · hAX hXH hne)
  intro D hd hp he
  exact hscore D (hreflect X D hAX hXH hne hd hp he).1 hd

/-- A high-score prefix transfers even if the target tree has extra
eligible blocks. Each extra block must score below the path. SA-PC uses
this form for F4, where private paths can score only through equivocators. -/
theorem ghost_prefix_of_score_transport (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (threshold : Nat) (B : Block)
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Block.Preceq B (ghost .genesis sourceTree sourceScore sourceEligible))
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ targetTree)
    (hhigh : ∀ C, C ≠ .genesis → Block.Preceq C B → threshold < sourceScore C)
    (hscore : ∀ C, targetScore C = sourceScore C)
    (helig : ∀ C, targetEligible C = sourceEligible C)
    (hreflect : ∀ C ∈ targetTree, C ≠ .genesis →
      threshold < targetScore C → C ∈ sourceTree) :
    Block.Preceq B (ghost .genesis targetTree targetScore targetEligible) := by
  apply ghost_covers_of_steps targetTree targetScore targetEligible .genesis B htargetRoot
    (genesis_prefix B) hpath
  intro X _ hXB hne
  let H := ghost .genesis sourceTree sourceScore sourceEligible
  have hXH : Block.Preceq X H := prefix_trans _ _ _ hXB hsource
  have hneH : X ≠ H := by
    intro he
    have hBX : Block.Preceq B X := he ▸ hsource
    exact hne (prefix_eq_of_depth X B hXB (prefix_depth B X hBX))
  obtain ⟨C, hs, hCH⟩ := ghost_step_towards_result sourceTree sourceScore sourceEligible
    .genesis H X hsourceRoot rfl (genesis_prefix X) hXH hneH
  have hc := ghostStep_child sourceTree sourceScore sourceEligible X C hs
  have hn : C ≠ .genesis := by intro he; simp [he, Block.parent?] at hc
  have hCB : Block.Preceq C B := by
    rcases Bool.or_eq_true_iff.mp (ancestors_compatible C B H hCH hsource) with h | h
    · exact h
    · have hXd : X.depth < B.depth := by
        have hd := prefix_depth X B hXB
        have hnot : ¬ B.depth ≤ X.depth := fun h => hne (prefix_eq_of_depth X B hXB h)
        omega
      have hCd := child_depth X C hc.2.1
      have he := prefix_eq_of_depth B C h (by omega)
      exact he ▸ block_preceq_self C
  refine ⟨C, ?_, hCB⟩
  apply ghostStep_of_best targetTree targetScore targetEligible X C htargetRoot
    (hpath C hn hCB) hc.2.1 ((helig C).trans hc.2.2)
  intro D hd hp he
  by_cases hD : threshold < targetScore D
  · rw [hscore D, hscore C]
    exact ghostStep_best sourceTree sourceScore sourceEligible X C hs D
      (hreflect D hd (by intro eq; simp [eq, Block.parent?] at hp) hD)
      hp ((helig D).symm.trans he)
  · have hC : threshold < targetScore C := (hscore C).symm ▸ hhigh C hn hCB
    exact ⟨by omega, by omega⟩

/-- A fresh child is adopted after a transported proposal walk. At the
parent, it is the only eligible child. At earlier ancestors, old choices
must persist and every new eligible candidate must reflect to the source.
The target anchor may be any ancestor of the source's terminal parent
when `sourceAnchor` is genesis. This is the release-safe form. -/
theorem ghost_adopts_fresh_child (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (sourceAnchor targetAnchor parent B : Block)
    (hsourceRoot : RootInjectiveBelow sourceTree) (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : ghost sourceAnchor sourceTree sourceScore sourceEligible = parent)
    (hanchors : Block.Preceq sourceAnchor targetAnchor ∧ Block.Preceq targetAnchor parent)
    (hparent : B.parent? = some parent)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ targetTree)
    (hB : B ∈ targetTree) (heligB : targetEligible B = true)
    (honly : ∀ D ∈ targetTree, D.parent? = some parent → targetEligible D = true → D = B)
    (hkeep : ∀ X C, Block.Preceq targetAnchor X → Block.Preceq X parent → X ≠ parent →
      ghostStep sourceTree sourceScore sourceEligible X = some C → Block.Preceq C parent →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X D, Block.Preceq targetAnchor X → Block.Preceq X parent → X ≠ parent →
      D ∈ targetTree → D.parent? = some X → targetEligible D = true →
      D ∈ sourceTree ∧ sourceEligible D = true)
    (hscore : ∀ D, D ∈ sourceTree → D ∈ targetTree → targetScore D = sourceScore D) :
    Block.Preceq B (ghost targetAnchor targetTree targetScore targetEligible) := by
  have hPB := parent_prefix parent B hparent
  apply ghost_covers_of_steps targetTree targetScore targetEligible targetAnchor B htargetRoot
    (prefix_trans targetAnchor parent B hanchors.2 hPB) hpath
  intro X hAX hXB hneB
  have hXP : Block.Preceq X parent := by
    cases B with
    | genesis => simp [Block.parent?] at hparent
    | node P s r_s id =>
        have he : P = parent := by simpa [Block.parent?] using hparent
        subst P
        simpa [Block.Preceq, Block.preceq, hneB] using hXB
  by_cases hXP' : X = parent
  · subst X
    refine ⟨B, ?_, block_preceq_self B⟩
    apply ghostStep_of_best targetTree targetScore targetEligible parent B htargetRoot hB
      hparent heligB
    intro D hd hp he
    rw [honly D hd hp he]
    exact ⟨le_refl _, fun _ => le_refl _⟩
  · obtain ⟨C, hs, hCP⟩ := ghost_step_towards_result sourceTree sourceScore sourceEligible
      sourceAnchor parent X hsourceRoot hsource
      (prefix_trans sourceAnchor targetAnchor X hanchors.1 hAX) hXP hXP'
    refine ⟨C, ?_, prefix_trans C parent B hCP hPB⟩
    apply ghostStep_transport_of_subset sourceTree targetTree sourceScore targetScore
      sourceEligible targetEligible X C htargetRoot hs (hkeep X C hAX hXP hXP' hs hCP)
      (hreflect X · hAX hXP hXP')
    intro D hd hp he
    exact hscore D (hreflect X D hAX hXP hXP' hd hp he).1 hd

/-- Moving the anchor along the same ordinary walk preserves its terminal
result. This justifies removal of a constraint already on that walk. -/
theorem ghost_reanchor (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (sourceAnchor targetAnchor H : Block)
    (hroot : RootInjectiveBelow tree)
    (hclosed : ∀ B ∈ tree, ∀ A, A ≠ .genesis → Block.Preceq A B → A ∈ tree)
    (hsource : ghost sourceAnchor tree score eligible = H)
    (hanchors : Block.Preceq sourceAnchor targetAnchor ∧ Block.Preceq targetAnchor H)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C H → C ∈ tree) :
    ghost targetAnchor tree score eligible = H := by
  have hcover := ghost_transport_covers tree tree score score eligible eligible
    sourceAnchor targetAnchor H hroot hroot hsource hanchors hpath
    (fun X C _ _ _ hs _ =>
      ⟨(ghostStep_child tree score eligible X C hs).1,
        (ghostStep_child tree score eligible X C hs).2.2⟩)
    (fun _ D _ _ _ hd _ he => ⟨hd, he⟩) (by intros; rfl)
  by_contra hne
  obtain ⟨C, hc, _⟩ := ghost_step_towards_result tree score eligible targetAnchor
    (ghost targetAnchor tree score eligible) H hroot rfl hanchors.2 hcover (Ne.symm hne)
  have hstop := ghost_result_no_eligible_child tree score eligible sourceAnchor hroot hclosed
  have hchild := ghostStep_child tree score eligible H C hc
  have hf := hstop C hchild.1 (by rw [hsource]; exact hchild.2.1)
  rw [hchild.2.2] at hf
  contradiction

end AvailableChain.GridCO
end
