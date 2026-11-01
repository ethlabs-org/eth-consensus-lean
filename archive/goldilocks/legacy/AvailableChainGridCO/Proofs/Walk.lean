module
public import AvailableChainGridCO.Proofs.RecordSlots
public import AvailableChainGridCO.Proofs.Roots -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

/- These lemmas port the strict-domination argument in verified-consensus
Goldfish/Walk.lean. The list fold and its explicit tie check replace the
source's finite-set argmax. No root-injectivity assumption is needed when
the score inequality is strict. -/

private def chooseChild (score : Block → Nat) (best : Option Block) (b : Block) :
    Option Block :=
  match best with
  | none => some b
  | some old =>
      if score old < score b || (score old == score b && old.root < b.root)
      then some b else best

private theorem chooseChild_origin (score : Block → Nat) (best : Option Block) (b : Block) :
    chooseChild score best b = best ∨ chooseChild score best b = some b := by
  cases best <;> simp only [chooseChild]
  · exact Or.inr True.intro
  · split <;> simp_all

private theorem fold_choose_keeps (score : Block → Nat) (C : Block) (xs : List Block)
    (hdom : ∀ D ∈ xs, D ≠ C → score D < score C) :
    xs.foldl (chooseChild score) (some C) = some C := by
  induction xs with
  | nil => rfl
  | cons D xs ih =>
      have hd : chooseChild score (some C) D = some C := by
        by_cases he : D = C
        · subst D; simp [chooseChild]
        · have hlt := hdom D (by simp) he
          simp [chooseChild, Nat.not_lt_of_ge (Nat.le_of_lt hlt), Nat.ne_of_gt hlt]
      rw [List.foldl_cons, hd]
      exact ih (fun E hE => hdom E (List.mem_cons_of_mem D hE))

private theorem fold_choose_dominates (score : Block → Nat) (C : Block)
    (xs : List Block) (best : Option Block)
    (hbest : ∀ D, best = some D → D = C ∨ score D < score C)
    (hC : C ∈ xs) (hdom : ∀ D ∈ xs, D ≠ C → score D < score C) :
    xs.foldl (chooseChild score) best = some C := by
  induction xs generalizing best with
  | nil => simp at hC
  | cons D xs ih =>
      rw [List.foldl_cons]
      by_cases he : D = C
      · subst D
        have hc : chooseChild score best C = some C := by
          cases best with
          | none => rfl
          | some old =>
              rcases hbest old rfl with rfl | hlt
              · simp [chooseChild]
              · simp [chooseChild, hlt]
        rw [hc]
        exact fold_choose_keeps score C xs (fun E hE => hdom E (by simp [hE]))
      · apply ih (chooseChild score best D) ?_ ?_ (fun E hE => hdom E (by simp [hE]))
        · intro E hE
          rcases chooseChild_origin score best D with hold | hnew
          · exact hbest E (hold.symm.trans hE)
          · have hDE := Option.some.inj (hnew.symm.trans hE)
            subst E
            exact Or.inr (hdom D (by simp) he)
        · exact (List.mem_cons.mp hC).resolve_left (Ne.symm he)

/-- Strict score dominance selects the specified child. The duplicate-root
tie check cannot reject this step. -/
theorem ghostStep_of_strict_dominance (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor child : Block)
    (hm : child ∈ tree) (hp : child.parent? = some anchor) (he : eligible child = true)
    (hd : ∀ other ∈ tree, other.parent? = some anchor → eligible other = true →
      other ≠ child → score other < score child) :
    ghostStep tree score eligible anchor = some child := by
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  have hmem : child ∈ children := List.mem_filter.mpr ⟨hm, by simp [hp, he]⟩
  have hdom : ∀ other ∈ children, other ≠ child → score other < score child := by
    intro other ho hn
    obtain ⟨hot, hcond⟩ := List.mem_filter.mp ho
    have ⟨hpar, helig⟩ := Bool.and_eq_true_iff.mp hcond
    exact hd other hot (by simpa using hpar) helig hn
  have hfold := fold_choose_dominates score child children none (by simp) hmem hdom
  have htie : children.any (fun c => c != child && score c == score child &&
      c.root == child.root) = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    obtain ⟨c, hcm, htest⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at htest
    have := hdom c hcm htest.1.1
    omega
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some b => if children.any (fun c => c != b && score c == score b && c.root == b.root)
        then none else some b) = some child
  rw [hfold]
  simp only [htie, Bool.false_eq_true, ↓reduceIte]

private theorem prefix_depth (A B : Block) (h : Block.Preceq A B) : A.depth ≤ B.depth := by
  induction B with
  | genesis => have : A = .genesis := by simpa [Block.Preceq, Block.preceq] using h
               subst A; rfl
  | node P s r_s id ih =>
      obtain he | hp : A = .node P s r_s id ∨ Block.Preceq A P := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using h
      · subst A; rfl
      · exact le_trans (ih hp) (Nat.le_succ _)

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

private theorem path_child (A B : Block) (h : Block.Preceq A B) (hne : A ≠ B) :
    ∃ C, C.parent? = some A ∧ Block.Preceq C B := by
  induction B with
  | genesis => exact (hne (by simpa [Block.Preceq, Block.preceq] using h)).elim
  | node P s r_s id ih =>
      have hp : Block.Preceq A P := by
        simpa [Block.Preceq, Block.preceq, hne] using h
      by_cases he : A = P
      · subst P
        exact ⟨.node A s r_s id, rfl, block_preceq_self _⟩
      · obtain ⟨C, hc, hcp⟩ := ih hp he
        exact ⟨C, hc, Bool.or_eq_true_iff.mpr (Or.inr hcp)⟩

private def pathNodes : Block → List Block
  | .genesis => []
  | b@(.node parent _ _ _) => b :: pathNodes parent

private theorem pathNodes_spec (B : Block) :
    (pathNodes B).length = B.depth ∧ (pathNodes B).Nodup ∧
      ∀ C ∈ pathNodes B, C ≠ .genesis ∧ Block.Preceq C B := by
  induction B with
  | genesis => simp [pathNodes, Block.depth]
  | node P s r_s id ih =>
      refine ⟨by simpa [pathNodes, Block.depth] using congrArg Nat.succ ih.1, ?_, ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, ih.2.1⟩
        intro hmem
        have := prefix_depth _ _ (ih.2.2 _ hmem).2
        change P.depth + 1 ≤ P.depth at this
        omega
      · intro C hc
        rcases List.mem_cons.mp hc with rfl | hp
        · exact ⟨by simp, block_preceq_self _⟩
        · exact ⟨(ih.2.2 C hp).1, Bool.or_eq_true_iff.mpr (Or.inr (ih.2.2 C hp).2)⟩

/-- A stored path fits within the duplicate-free GHOST fuel budget. -/
theorem depth_le_ghost_fuel (tree : List Block) (B : Block)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree) :
    B.depth ≤ tree.eraseDups.length := by
  rw [← (pathNodes_spec B).1]
  rw [← List.toFinset_card_of_nodup (pathNodes_spec B).2.1,
    ← List.toFinset_card_of_nodup (eraseDups_nodup tree)]
  apply Finset.card_le_card
  intro C hC
  have hc := (pathNodes_spec B).2.2 C (List.mem_toFinset.mp hC)
  exact List.mem_toFinset.mpr (List.mem_eraseDups.mpr (hpath C hc.1 hc.2))

/-- A strict best child along each part of the stored target path drives
GHOST through the target. Later descent can only extend it. -/
theorem ghostWalk_covers_path (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (B : Block)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (helig : ∀ C, C ≠ .genesis → Block.Preceq C B → eligible C = true)
    (hdom : ∀ C, C ≠ .genesis → Block.Preceq C B → ∀ D ∈ tree,
      D.parent? = C.parent? → eligible D = true → D ≠ C → score D < score C)
    (fuel : Nat) (anchor : Block) (ha : Block.Preceq anchor B)
    (hf : B.depth ≤ anchor.depth + fuel) :
    Block.Preceq B (ghostWalk tree score eligible fuel anchor) := by
  induction fuel generalizing anchor with
  | zero =>
      have := prefix_eq_of_depth anchor B ha (by simpa using hf)
      subst anchor
      exact block_preceq_self _
  | succ fuel ih =>
      by_cases he : anchor = B
      · subst anchor
        exact ghostWalk_extends tree score eligible (fuel + 1) B
      · obtain ⟨C, hpar, hCB⟩ := path_child anchor B ha he
        have hn : C ≠ .genesis := by intro hz; simp [hz, Block.parent?] at hpar
        have hdepth : C.depth = anchor.depth + 1 := by
          cases C with
          | genesis => contradiction
          | node parent s r_s id =>
              have heq : parent = anchor := by simpa [Block.parent?] using hpar
              subst parent; rfl
        have hs := ghostStep_of_strict_dominance tree score eligible anchor C
          (hpath C hn hCB) hpar (helig C hn hCB) (by
            intro D hd hp he hnD
            exact hdom C hn hCB D hd (hp.trans hpar.symm) he hnD)
        rw [ghostWalk, hs]
        exact ih C hCB (by omega)

/-- The transfer walk contains the target once its stored path is eligible
and strictly dominates each competing child. Root compatibility is only
one of these premises. -/
theorem ghost_covers_of_path_dominance (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor B : Block)
    (hcompatible : Block.Compatible anchor B)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (helig : ∀ C, C ≠ .genesis → Block.Preceq C B → eligible C = true)
    (hdom : ∀ C, C ≠ .genesis → Block.Preceq C B → ∀ D ∈ tree,
      D.parent? = C.parent? → eligible D = true → D ≠ C → score D < score C) :
    Block.Preceq B (ghost anchor tree score eligible) := by
  rcases Bool.or_eq_true_iff.mp hcompatible with ha | hb
  · exact ghostWalk_covers_path tree.eraseDups score eligible B
      (fun C hn hp => List.mem_eraseDups.mpr (hpath C hn hp)) helig
      (fun C hn hp D hd => hdom C hn hp D (List.mem_eraseDups.mp hd))
      _ anchor ha (le_trans (depth_le_ghost_fuel tree B hpath) (Nat.le_add_left _ _))
  · exact prefix_trans B anchor _ hb (ghost_extends anchor tree score eligible)

/-- The same transfer condition for the executable ordinary fork choice. -/
theorem forkChoice_covers_of_path_dominance {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (Wire n)) (current : Slot) (B : Block)
    (hcompatible : Block.Compatible (liveRoot st) B)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (helig : ∀ C, C ≠ .genesis → Block.Preceq C B →
      goldfishEligible st.blocks raw support current C = true)
    (hdom : ∀ C, C ≠ .genesis → Block.Preceq C B → ∀ D ∈ tree,
      D.parent? = C.parent? → goldfishEligible st.blocks raw support current D = true →
      D ≠ C → goldfishScore st.blocks raw support D < goldfishScore st.blocks raw support C) :
    Block.Preceq B (forkChoice st tree raw support current) :=
  ghost_covers_of_path_dominance tree _ _ (liveRoot st) B hcompatible hpath helig hdom

/-- A walk result either stays at its anchor or passes the eligibility test. -/
theorem ghostWalk_eligible (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block) :
    ghostWalk tree score eligible fuel anchor = anchor ∨
      eligible (ghostWalk tree score eligible fuel anchor) = true := by
  induction fuel generalizing anchor with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => exact Or.inl (by simp [ghostWalk, hs])
      | some child =>
          rw [ghostWalk, hs]
          change ghostWalk tree score eligible fuel child = anchor ∨
            eligible (ghostWalk tree score eligible fuel child) = true
          rcases ih child with he | hh
          · apply Or.inr
            rw [he]
            exact (ghostStep_child tree score eligible anchor child hs).2.2
          · exact Or.inr hh

/-- Different children of the same parent are incompatible. -/
theorem siblings_incompatible (B C : Block) (hp : B.parent? = C.parent?)
    (hne : B ≠ C) : Block.compatible B C = false := by
  have hd : B.depth = C.depth := by
    cases B <;> cases C <;> simp_all [Block.parent?, Block.depth]
  apply Bool.eq_false_iff.mpr
  intro hc
  rcases Bool.or_eq_true_iff.mp hc with hb | hc
  · exact hne (prefix_eq_of_depth B C hb (le_of_eq hd.symm))
  · exact hne (prefix_eq_of_depth C B hc (le_of_eq hd)).symm

private theorem fold_choose_origin (score : Block → Nat) (xs : List Block)
    (best : Option Block) (B : Block)
    (h : xs.foldl (chooseChild score) best = some B) : best = some B ∨ B ∈ xs := by
  induction xs generalizing best with
  | nil => exact Or.inl h
  | cons C xs ih =>
      rcases ih (chooseChild score best C) h with hc | hb
      · rcases chooseChild_origin score best C with hold | hnew
        · exact Or.inl (hold.symm.trans hc)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj (hc.symm.trans hnew))))
      · exact Or.inr (List.mem_cons_of_mem C hb)

private theorem fold_choose_some (score : Block → Nat) (xs : List Block) (B : Block) :
    ∃ C, xs.foldl (chooseChild score) (some B) = some C := by
  induction xs generalizing B with
  | nil => exact ⟨B, rfl⟩
  | cons C xs ih =>
      rw [List.foldl_cons]
      rcases chooseChild_origin score (some B) C with hold | hnew
      · rw [hold]; exact ih B
      · rw [hnew]; exact ih C

/-- Draft 4.2 rules out a duplicate-root tie at the selected child. -/
theorem ghostStep_eq_fold_of_rootInjective (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) (hroot : RootInjectiveBelow tree) :
    ghostStep tree score eligible anchor =
      (tree.filter (fun b => b.parent? == some anchor && eligible b)).foldl
        (fun best b => match best with
          | none => some b
          | some old => if score old < score b || (score old == score b && old.root < b.root)
              then some b else best) none := by
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some b => if children.any (fun c => c != b && score c == score b && c.root == b.root)
        then none else some b) = children.foldl (chooseChild score) none
  cases hb : children.foldl (chooseChild score) none with
  | none => rfl
  | some B =>
      have hB : B ∈ children := (fold_choose_origin score children none B hb).resolve_left
        (by simp)
      have htie : children.any
          (fun c => c != B && score c == score B && c.root == B.root) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨C, hC, hc⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
        exact hc.1.1 (hroot C B
          ⟨C, (List.mem_filter.mp hC).1, block_preceq_self C⟩
          ⟨B, (List.mem_filter.mp hB).1, block_preceq_self B⟩ hc.2)
      simp [htie]

/-- With unique roots, GHOST stops exactly when it has no eligible child. -/
theorem ghostStep_none_iff_of_rootInjective (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) (hroot : RootInjectiveBelow tree) :
    ghostStep tree score eligible anchor = none ↔
      ∀ B ∈ tree, B.parent? = some anchor → eligible B = false := by
  rw [ghostStep_eq_fold_of_rootInjective tree score eligible anchor hroot]
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  change children.foldl (chooseChild score) none = none ↔ _
  have hempty : children.foldl (chooseChild score) none = none ↔ children = [] := by
    cases hc : children with
    | nil => simp
    | cons B xs =>
        obtain ⟨C, hC⟩ := fold_choose_some score xs B
        change xs.foldl (chooseChild score) (some B) = none ↔ B :: xs = []
        simp [hC]
  rw [hempty]
  constructor
  · intro he B hB hp
    apply Bool.eq_false_iff.mpr
    intro hb
    have hm : B ∈ children := List.mem_filter.mpr ⟨hB, by simp [hp, hb]⟩
    rw [he] at hm
    exact List.not_mem_nil hm
  · intro h
    apply List.filter_eq_nil_iff.mpr
    intro B hB
    by_cases hp : B.parent? = some anchor
    · simp [hp, h B hB hp]
    · simp [hp]

/-- A walk with enough depth budget ends at a terminal block. -/
theorem ghostWalk_terminal_of_depth_bound (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (hroot : RootInjectiveBelow tree)
    (fuel : Nat) (anchor : Block)
    (hdepth : ∀ B ∈ tree, B.depth ≤ anchor.depth + fuel) :
    ghostStep tree score eligible (ghostWalk tree score eligible fuel anchor) = none := by
  induction fuel generalizing anchor with
  | zero =>
      apply (ghostStep_none_iff_of_rootInjective tree score eligible anchor hroot).mpr
      intro B hB hp
      have hd : B.depth = anchor.depth + 1 := by
        cases B <;> simp_all [Block.parent?, Block.depth]
      have hh := hdepth B hB
      omega
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => simp [ghostWalk, hs]
      | some child =>
          rw [ghostWalk, hs]
          have hchild := ghostStep_child tree score eligible anchor child hs
          have hd : child.depth = anchor.depth + 1 := by
            cases child <;> simp_all [Block.parent?, Block.depth]
          apply ih child
          intro B hB
          have hh := hdepth B hB
          omega

/-- Prefix closure provides enough fuel. Root uniqueness then makes the
ordinary GHOST result maximal among eligible children, as in the reference. -/
theorem ghost_result_no_eligible_child (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) (hroot : RootInjectiveBelow tree)
    (hclosed : ∀ B ∈ tree, ∀ A, A ≠ .genesis → Block.Preceq A B → A ∈ tree) :
    ∀ B ∈ tree, B.parent? = some (ghost anchor tree score eligible) → eligible B = false := by
  have hroot' : RootInjectiveBelow tree.eraseDups := by
    intro A C hA hC he
    obtain ⟨B, hB, hAB⟩ := hA
    obtain ⟨D, hD, hCD⟩ := hC
    exact hroot A C ⟨B, List.mem_eraseDups.mp hB, hAB⟩
      ⟨D, List.mem_eraseDups.mp hD, hCD⟩ he
  have hterminal := ghostWalk_terminal_of_depth_bound tree.eraseDups score eligible hroot'
    tree.eraseDups.length anchor (by
      intro B hB
      exact (depth_le_ghost_fuel tree B (hclosed B (List.mem_eraseDups.mp hB))).trans
        (Nat.le_add_left _ _))
  intro B hB hp
  exact (ghostStep_none_iff_of_rootInjective tree.eraseDups score eligible
    _ hroot').mp hterminal B (List.mem_eraseDups.mpr hB) hp

end AvailableChain.GridCO
end
