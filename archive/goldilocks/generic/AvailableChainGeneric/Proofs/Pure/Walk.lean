module
public import AvailableChainGeneric.Statements.Pure.Walk
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainGridCO.Model.Walk -- shake: keep (re-export)

namespace AvailableChain.Gen.Pure

open AvailableChain GridCO

-- Helpers use the module default private scope. Only the final API is public.

-- This notation expands to the model fold. It adds no definition.
-- port: AvailableChainGridCO/Proofs/Walk.lean:19–25
set_option quotPrecheck false in
local notation "chooseChild" => fun (score : Block → Nat) (best : Option Block) (b : Block) =>
  match best with
  | none => some b
  | some old =>
      if score old < score b || (score old == score b && old.root < b.root)
      then some b else best

-- port: AvailableChainGridCO/Proofs/Walk.lean:27–32
theorem walk_aux_chooseChild_origin (score : Block → Nat) (best : Option Block) (b : Block) :
    chooseChild score best b = best ∨ chooseChild score best b = some b := by
  cases best <;> dsimp only
  · exact Or.inr rfl
  · split <;> simp_all


-- port: AvailableChainGridCO/Proofs/Walk.lean:33–46
theorem walk_aux_fold_choose_keeps (score : Block → Nat) (C : Block) (xs : List Block)
    (hdom : ∀ D ∈ xs, D ≠ C → score D < score C) :
    xs.foldl (chooseChild score) (some C) = some C := by
  induction xs with
  | nil => rfl
  | cons D xs ih =>
      have hd : chooseChild score (some C) D = some C := by
        by_cases he : D = C
        · subst D; simp
        · have hlt := hdom D (by simp) he
          simp [Nat.not_lt_of_ge (Nat.le_of_lt hlt), Nat.ne_of_gt hlt]
      rw [List.foldl_cons, hd]
      exact ih (fun E hE => hdom E (List.mem_cons_of_mem D hE))


-- port: AvailableChainGridCO/Proofs/Walk.lean:47–75
theorem walk_aux_fold_choose_dominates (score : Block → Nat) (C : Block)
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
              · simp
              · simp [hlt]
        rw [hc]
        exact walk_aux_fold_choose_keeps score C xs (fun E hE => hdom E (by simp [hE]))
      · apply ih (chooseChild score best D) ?_ ?_ (fun E hE => hdom E (by simp [hE]))
        · intro E hE
          rcases walk_aux_chooseChild_origin score best D with hold | hnew
          · exact hbest E (hold.symm.trans hE)
          · have hDE := Option.some.inj (hnew.symm.trans hE)
            subst E
            exact Or.inr (hdom D (by simp) he)
        · exact (List.mem_cons.mp hC).resolve_left (Ne.symm he)


-- port: AvailableChainGridCO/Proofs/Walk.lean:78–105
theorem walk_aux_ghostStep_of_strict_dominance (tree : List Block) (score : Block → Nat)
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
  have hfold := walk_aux_fold_choose_dominates score child children none (by simp) hmem hdom
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
  change (if children.any (fun c => c != child && score c == score child &&
    c.root == child.root) then none else some child) = some child
  rw [htie]
  rfl

-- port: AvailableChainGridCO/Proofs/Walk.lean:273–283
theorem walk_aux_fold_choose_origin (score : Block → Nat) (xs : List Block)
    (best : Option Block) (B : Block)
    (h : xs.foldl (chooseChild score) best = some B) : best = some B ∨ B ∈ xs := by
  induction xs generalizing best with
  | nil => exact Or.inl h
  | cons C xs ih =>
      rcases ih (chooseChild score best C) h with hc | hb
      · rcases walk_aux_chooseChild_origin score best C with hold | hnew
        · exact Or.inl (hold.symm.trans hc)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj (hc.symm.trans hnew))))
      · exact Or.inr (List.mem_cons_of_mem C hb)

-- port: AvailableChainGridCO/Proofs/Walk.lean:285–293
theorem walk_aux_fold_choose_some (score : Block → Nat) (xs : List Block) (B : Block) :
    ∃ C, xs.foldl (chooseChild score) (some B) = some C := by
  induction xs generalizing B with
  | nil => exact ⟨B, rfl⟩
  | cons C xs ih =>
      rw [List.foldl_cons]
      rcases walk_aux_chooseChild_origin score (some B) C with hold | hnew
      · rw [hold]; exact ih B
      · rw [hnew]; exact ih C

-- port: AvailableChainGridCO/Proofs/Walk.lean:296–323
/-- ROOT-DIGEST W1b: use tree root uniqueness for the tie test. -/
theorem walk_aux_ghostStep_eq_fold_of_rootInjective (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) :
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
      have hB : B ∈ children := (walk_aux_fold_choose_origin score children none B hb).resolve_left
        (by simp)
      have htie : children.any
          (fun c => c != B && score c == score B && c.root == B.root) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨C, hC, hc⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
        exact hc.1.1 (hroot C (List.mem_filter.mp hC).1 B
          (List.mem_filter.mp hB).1 hc.2)
      change (if children.any (fun c => c != B && score c == score B && c.root == B.root)
        then none else some B) = some B
      rw [htie]
      rfl

-- port: AvailableChainGridCO/Proofs/Walk.lean:326–353
/-- ROOT-DIGEST W1b: use root uniqueness only on the given tree. -/
theorem walk_aux_ghostStep_none_iff_of_rootInjective (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) :
    ghostStep tree score eligible anchor = none ↔
      ∀ B ∈ tree, B.parent? = some anchor → eligible B = false := by
  rw [walk_aux_ghostStep_eq_fold_of_rootInjective tree score eligible anchor hroot]
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  change children.foldl (chooseChild score) none = none ↔ _
  have hempty : children.foldl (chooseChild score) none = none ↔ children = [] := by
    cases hc : children with
    | nil => simp
    | cons B xs =>
        obtain ⟨C, hC⟩ := walk_aux_fold_choose_some score xs B
        change xs.foldl (chooseChild score) (some B) = none ↔ B :: xs = []
        simp only [hC, reduceCtorEq]
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
/-- ROOT-DIGEST W1b: no eligible child makes the filtered candidate list empty. -/
theorem walk_aux_ghostStep_none_of_noEligibleChild (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block)
    (hstop : NoEligibleChild tree eligible anchor) :
    ghostStep tree score eligible anchor = none := by
  have hempty : tree.filter (fun B => B.parent? == some anchor && eligible B) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro B hB
    by_cases hp : B.parent? = some anchor
    · simp [hp, hstop B hB hp]
    · simp [hp]
  change (match (tree.filter (fun B => B.parent? == some anchor && eligible B)).foldl
    (chooseChild score) none with
    | none => none
    | some B => if (tree.filter (fun C => C.parent? == some anchor && eligible C)).any
        (fun C => C != B && score C == score B && C.root == B.root)
        then none else some B) = none
  rw [hempty]
  rfl

-- port: AvailableChainGridCO/Proofs/StoreFacts.lean:32–73
/-- ROOT-DIGEST W1b: read the successful selection branch directly. -/
theorem walk_aux_ghostStep_child (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor child : Block)
    (hstep : ghostStep tree score eligible anchor = some child) :
    child ∈ tree ∧ child.parent? = some anchor ∧ eligible child = true := by
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some B => if children.any (fun C => C != B && score C == score B && C.root == B.root)
        then none else some B) = some child at hstep
  cases hf : children.foldl (chooseChild score) none with
  | none =>
      rw [hf] at hstep
      change none = some child at hstep
      contradiction
  | some B =>
      rw [hf] at hstep
      change (if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some child at hstep
      split at hstep
      · contradiction
      · cases hstep
        have hm := (walk_aux_fold_choose_origin score children none child hf).resolve_left
          (by simp)
        obtain ⟨ht, hp⟩ := List.mem_filter.mp hm
        obtain ⟨hpar, he⟩ := Bool.and_eq_true_iff.mp hp
        exact ⟨ht, by simpa using hpar, he⟩

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:200–202
theorem walk_aux_child_depth (A C : Block) (h : C.parent? = some A) :
    C.depth = A.depth + 1 := by
  cases C with
  | genesis => change none = some A at h; contradiction
  | node P s r_s id =>
      change some P = some A at h
      cases Option.some.inj h
      rfl

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:204–211
theorem walk_aux_parent_prefix (A C : Block) (h : C.parent? = some A) :
    Block.Preceq A C := by
  cases C with
  | genesis => change none = some A at h; contradiction
  | node P s r_s id =>
      change some P = some A at h
      cases Option.some.inj h
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

-- Use direct branch reduction so model equations are not exported here.
theorem walk_aux_walk_none {tree : List Block} {score : Block → Nat}
    {eligible : Block → Bool} {fuel : Nat} {anchor : Block}
    (hs : ghostStep tree score eligible anchor = none) :
    ghostWalk tree score eligible (fuel + 1) anchor = anchor := by
  change (match ghostStep tree score eligible anchor with
    | none => anchor
    | some C => ghostWalk tree score eligible fuel C) = anchor
  rw [hs]

theorem walk_aux_walk_some {tree : List Block} {score : Block → Nat}
    {eligible : Block → Bool} {fuel : Nat} {anchor child : Block}
    (hs : ghostStep tree score eligible anchor = some child) :
    ghostWalk tree score eligible (fuel + 1) anchor = ghostWalk tree score eligible fuel child := by
  change (match ghostStep tree score eligible anchor with
    | none => anchor
    | some C => ghostWalk tree score eligible fuel C) = ghostWalk tree score eligible fuel child
  rw [hs]

-- port: AvailableChainGridCO/Proofs/StoreFacts.lean:239–252
theorem walk_aux_ghostWalk_extends (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block) :
    Block.Preceq anchor (ghostWalk tree score eligible fuel anchor) := by
  induction fuel generalizing anchor with
  | zero => exact block_preceq_refl anchor
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => rw [walk_aux_walk_none hs]; exact block_preceq_refl anchor
      | some child =>
          rw [walk_aux_walk_some hs]
          exact block_preceq_trans (walk_aux_parent_prefix anchor child
            (walk_aux_ghostStep_child tree score eligible anchor child hs).2.1) (ih child)

-- port: AvailableChainGridCO/Proofs/Walk.lean:243–260
theorem walk_aux_ghostWalk_eligible (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block) :
    ghostWalk tree score eligible fuel anchor = anchor ∨
      eligible (ghostWalk tree score eligible fuel anchor) = true := by
  induction fuel generalizing anchor with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => exact Or.inl (walk_aux_walk_none hs)
      | some child =>
          rw [walk_aux_walk_some hs]
          rcases ih child with he | hh
          · apply Or.inr
            rw [he]
            exact (walk_aux_ghostStep_child tree score eligible anchor child hs).2.2
          · exact Or.inr hh

-- port: AvailableChainGridCO/Proofs/Walk.lean:263–272
theorem walk_aux_siblings_incompatible (B C : Block) (hp : B.parent? = C.parent?)
    (hne : B ≠ C) : Block.compatible B C = false := by
  have hd : B.depth = C.depth := by
    cases B with
    | genesis =>
        cases C with
        | genesis => rfl
        | node P s r_s id => change none = some P at hp; contradiction
    | node P s r_s id =>
        cases C with
        | genesis => change some P = none at hp; contradiction
        | node Q t r_t jd =>
            change some P = some Q at hp
            cases Option.some.inj hp
            rfl
  apply Bool.eq_false_iff.mpr
  intro hc
  rcases Bool.or_eq_true_iff.mp hc with hb | hc
  · exact hne (prefix_eq_of_depth B C hb (le_of_eq hd.symm))
  · exact hne (prefix_eq_of_depth C B hc (le_of_eq hd)).symm


theorem walk_aux_prec_iff (A B : Block) :
    Block.Prec A B ↔ A ≠ B ∧ Block.Preceq A B := by
  change ((!decide (A = B) && Block.preceq A B) = true ↔
    A ≠ B ∧ Block.preceq A B = true)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]

-- Adapt the stored-path count to vertices strictly after the anchor.
-- port: AvailableChainGridCO/Proofs/Walk.lean:165–174
theorem walk_aux_suffix_depth_le_card (anchor target : Block) (S : Finset Block)
    (ha : Block.Preceq anchor target)
    (hpath : ∀ C, Block.Prec anchor C → Block.Preceq C target → C ∈ S) :
    target.depth ≤ anchor.depth + S.card := by
  induction target generalizing S with
  | genesis =>
      have he : anchor = .genesis := of_decide_eq_true ha
      subst anchor
      change 0 ≤ 0 + S.card
      omega
  | node P s r_s id ih =>
      by_cases he : anchor = .node P s r_s id
      · subst anchor
        omega
      · have hp : Block.Preceq anchor P := by
          change (decide (anchor = Block.node P s r_s id) || Block.preceq anchor P) = true at ha
          exact (Bool.or_eq_true_iff.mp ha).resolve_left (by simpa using he)
        have hm := hpath (.node P s r_s id) ((walk_aux_prec_iff _ _).mpr ⟨he, ha⟩)
          (block_preceq_refl _)
        have hd := ih (S.erase (.node P s r_s id)) hp (by
          intro C hAC hCP
          apply Finset.mem_erase.mpr
          refine ⟨?_, hpath C hAC (Bool.or_eq_true_iff.mpr (Or.inr hCP))⟩
          intro hC
          have hc := prefix_depth C P hCP
          rw [hC] at hc
          change P.depth + 1 ≤ P.depth at hc
          omega)
        have hcard := Finset.card_erase_add_one hm
        change P.depth + 1 ≤ anchor.depth + S.card
        omega

theorem walk_aux_suffix_depth_le_fuel (anchor target : Block) (tree : List Block)
    (ha : Block.Preceq anchor target)
    (hpath : ∀ C, Block.Prec anchor C → Block.Preceq C target → C ∈ tree) :
    target.depth ≤ anchor.depth + tree.eraseDups.length := by
  have hd := walk_aux_suffix_depth_le_card anchor target tree.eraseDups.toFinset ha (by
    intro C hAC hCT
    exact List.mem_toFinset.mpr (List.mem_eraseDups.mpr (hpath C hAC hCT)))
  have hc := List.toFinset_card_le tree.eraseDups
  omega

-- Adapt path dominance to the suffix after base.
-- port: AvailableChainGridCO/Proofs/Walk.lean:178–209
theorem walk_aux_ghostWalk_covers_path (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (base target : Block)
    (hdom : DominatedSuffix base target tree score eligible)
    (fuel : Nat) (anchor : Block) (hbase : Block.Preceq base anchor)
    (ha : Block.Preceq anchor target) (hf : target.depth ≤ anchor.depth + fuel) :
    Block.Preceq target (ghostWalk tree score eligible fuel anchor) := by
  induction fuel generalizing anchor with
  | zero =>
      have he := prefix_eq_of_depth anchor target ha (by simpa using hf)
      subst anchor
      exact block_preceq_refl _
  | succ fuel ih =>
      by_cases he : anchor = target
      · subst anchor
        exact walk_aux_ghostWalk_extends tree score eligible (fuel + 1) target
      · obtain ⟨C, hp, hCT⟩ := path_child anchor target ha he
        have hd := walk_aux_child_depth anchor C hp
        have hAC := walk_aux_parent_prefix anchor C hp
        have hBC : Block.Prec base C := (walk_aux_prec_iff _ _).mpr ⟨by
          intro heq
          have hh := prefix_depth base anchor hbase
          rw [heq] at hh
          omega, block_preceq_trans hbase hAC⟩
        obtain ⟨hm, hel, hbest⟩ := hdom C hBC hCT
        have hs := walk_aux_ghostStep_of_strict_dominance tree score eligible anchor C hm hp hel (by
          intro D hD hpar hE hne
          exact hbest D hD (hpar.trans hp.symm) hE hne)
        rw [walk_aux_walk_some hs]
        exact ih C (block_preceq_trans hbase hAC) hCT (by omega)

-- port: AvailableChainGridCO/Proofs/Walk.lean:214–227
theorem walk_aux_ghost_covers_of_path_dominance (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hcompatible : Block.Compatible anchor target)
    (hdom : DominatedSuffix anchor target tree score eligible) :
    Block.Preceq target (ghost anchor tree score eligible) := by
  rcases Bool.or_eq_true_iff.mp hcompatible with ha | hb
  · apply walk_aux_ghostWalk_covers_path tree.eraseDups score eligible anchor target
      (fun C hAC hCT => ⟨List.mem_eraseDups.mpr (hdom C hAC hCT).1,
        (hdom C hAC hCT).2.1,
        fun D hD => (hdom C hAC hCT).2.2 D (List.mem_eraseDups.mp hD)⟩)
      _ anchor (block_preceq_refl _) ha
      (walk_aux_suffix_depth_le_fuel anchor target tree ha (fun C hAC hCT => (hdom C hAC hCT).1))
  · exact block_preceq_trans hb (walk_aux_ghostWalk_extends _ _ _ _ _)

-- The depth bound is needed only for descendants of each recursive anchor.
-- port: AvailableChainGridCO/Proofs/Walk.lean:356–380
/-- ROOT-DIGEST W1b: exclude children with the structural depth bound. -/
theorem walk_aux_ghostWalk_terminal_of_depth_bound (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block)
    (hdepth : DescendantDepthBound anchor tree fuel) :
    ghostStep tree score eligible (ghostWalk tree score eligible fuel anchor) = none := by
  induction fuel generalizing anchor with
  | zero =>
      apply walk_aux_ghostStep_none_of_noEligibleChild tree score eligible anchor
      intro B hB hp
      have hd := walk_aux_child_depth anchor B hp
      have hh := hdepth B hB (walk_aux_parent_prefix anchor B hp)
      omega
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => rw [walk_aux_walk_none hs]; exact hs
      | some child =>
          rw [walk_aux_walk_some hs]
          have hc := walk_aux_ghostStep_child tree score eligible anchor child hs
          have hd := walk_aux_child_depth anchor child hc.2.1
          apply ih child
          intro B hB hCB
          have hh := hdepth B hB (block_preceq_trans
            (walk_aux_parent_prefix anchor child hc.2.1) hCB)
          omega

-- port: AvailableChainGridCO/Proofs/Walk.lean:384–401
/-- ROOT-DIGEST W1b: restrict the tree premise to eraseDups. -/
theorem walk_aux_ghost_result_no_eligible_child (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) (hclosed : AnchorClosed anchor tree) :
    NoEligibleChild tree eligible (ghost anchor tree score eligible) := by
  have ht := walk_aux_ghostWalk_terminal_of_depth_bound tree.eraseDups score eligible
    tree.eraseDups.length anchor (by
      intro B hB hAB
      apply walk_aux_suffix_depth_le_fuel anchor B tree hAB
      intro C hAC hCB
      exact hclosed B (List.mem_eraseDups.mp hB) hAB C ((walk_aux_prec_iff _ _).mp hAC).2 hCB)
  intro B hB hp
  exact (walk_aux_ghostStep_none_iff_of_rootInjective tree.eraseDups score eligible _
    (fun A hA B hB => hroot A (List.mem_eraseDups.mp hA) B (List.mem_eraseDups.mp hB))).mp ht
    B (List.mem_eraseDups.mpr hB) hp

-- The rank is score first, then root. The notation adds no definition.
set_option quotPrecheck false in
local notation "rankLE" => fun (score : Block → Nat) (A B : Block) =>
  score A ≤ score B ∧ (score A = score B → A.root ≤ B.root)

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:21–22
theorem walk_aux_rank_refl (score : Block → Nat) (A : Block) : rankLE score A A :=
  ⟨le_refl _, fun _ => le_refl _⟩

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:24–32
theorem walk_aux_rank_trans (score : Block → Nat) (A B C : Block)
    (hab : rankLE score A B) (hbc : rankLE score B C) : rankLE score A C := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro he
  have hab0 := hab.1
  have hbc0 := hbc.1
  have hab' : score A = score B := by omega
  have hbc' : score B = score C := by omega
  exact (hab.2 hab').trans (hbc.2 hbc')

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:41–68
theorem walk_aux_choose_bounds (score : Block → Nat) (best : Option Block) (B C : Block)
    (h : chooseChild score best B = some C) :
    rankLE score B C ∧ ∀ A, best = some A → rankLE score A C := by
  cases best with
  | none => cases h; exact ⟨walk_aux_rank_refl _ _, by simp⟩
  | some A =>
      dsimp only at h
      split at h
      · rename_i hlt
        cases h
        refine ⟨walk_aux_rank_refl _ _, ?_⟩
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
          exact walk_aux_rank_refl _ _

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:70–88
theorem walk_aux_fold_bounds (score : Block → Nat) (xs : List Block)
    (best : Option Block) (C : Block) (h : xs.foldl (chooseChild score) best = some C) :
    (∀ A, best = some A → rankLE score A C) ∧
      ∀ A ∈ xs, rankLE score A C := by
  induction xs generalizing best with
  | nil => exact ⟨by intro A ha; cases ha; cases h; exact walk_aux_rank_refl _ _, by simp⟩
  | cons B xs ih =>
      have hi := ih (chooseChild score best B) h
      have hex : ∃ D, chooseChild score best B = some D := by
        cases best <;> dsimp only
        · exact ⟨B, rfl⟩
        · split <;> exact ⟨_, rfl⟩
      obtain ⟨D, hd⟩ := hex
      have hb := walk_aux_choose_bounds score best B D hd
      refine ⟨fun A ha => walk_aux_rank_trans score A D C (hb.2 A ha) (hi.1 D hd), ?_⟩
      intro A ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact walk_aux_rank_trans score _ D C hb.1 (hi.1 D hd)
      · exact hi.2 A ha

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:91–110
theorem walk_aux_ghostStep_best (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block)
    (h : ghostStep tree score eligible anchor = some C) :
    ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D ≤ score C ∧ (score D = score C → D.root ≤ C.root) := by
  let children := tree.filter (fun B => B.parent? == some anchor && eligible B)
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some B => if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C at h
  cases hf : children.foldl (chooseChild score) none with
  | none =>
      rw [hf] at h
      change none = some C at h
      contradiction
  | some B =>
      rw [hf] at h
      change (if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C at h
      split at h
      · contradiction
      · cases h
        intro D hd hp he
        exact (walk_aux_fold_bounds score children none _ hf).2 D
          (List.mem_filter.mpr ⟨hd, by simp [hp, he]⟩)

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:114–134
/-- ROOT-DIGEST W1b: compare roots only for stored candidates. -/
theorem walk_aux_ghostStep_of_best (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B)
    (hc : C ∈ tree) (hp : C.parent? = some anchor) (he : eligible C = true)
    (hbest : ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D ≤ score C ∧ (score D = score C → D.root ≤ C.root)) :
    ghostStep tree score eligible anchor = some C := by
  cases hs : ghostStep tree score eligible anchor with
  | none =>
      have hf := (walk_aux_ghostStep_none_iff_of_rootInjective tree score eligible anchor
        hroot).mp hs
        C hc hp
      rw [he] at hf
      contradiction
  | some D =>
      have hd := walk_aux_ghostStep_child tree score eligible anchor D hs
      have hDC := hbest D hd.1 hd.2.1 hd.2.2
      have hCD := walk_aux_ghostStep_best tree score eligible anchor D hs C hc hp he
      have hscore : score D = score C := Nat.le_antisymm hDC.1 hCD.1
      have heq := hroot D hd.1 C hc
        (le_antisymm (hDC.2 hscore) (hCD.2 hscore.symm))
      subst D
      rfl

/-- ROOT-DIGEST W1b: a successful step has no distinct child with the same selected key. -/
theorem walk_aux_ghostStep_unique (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block)
    (h : ghostStep tree score eligible anchor = some C) :
    ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D = score C → D.root = C.root → D = C := by
  let children := tree.filter (fun B => B.parent? == some anchor && eligible B)
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some B => if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C at h
  cases hf : children.foldl (chooseChild score) none with
  | none =>
      rw [hf] at h
      change none = some C at h
      contradiction
  | some B =>
      rw [hf] at h
      change (if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C at h
      split at h
      · contradiction
      · rename_i hno
        cases h
        intro D hd hp he hs hr
        by_contra hn
        have ht : children.any
            (fun D => D != C && score D == score C && D.root == C.root) = true := by
          apply List.any_eq_true.mpr
          exact ⟨D, List.mem_filter.mpr ⟨hd, by simp [hp, he]⟩, by simp [hn, hs, hr]⟩
        exact hno ht

/-- ROOT-DIGEST W1b: a unique greatest child is selected without a global root premise. -/
theorem walk_aux_ghostStep_of_unique_best (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor C : Block)
    (hc : C ∈ tree) (hp : C.parent? = some anchor) (he : eligible C = true)
    (hbest : ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D ≤ score C ∧ (score D = score C → D.root ≤ C.root))
    (hunique : ∀ D ∈ tree, D.parent? = some anchor → eligible D = true →
      score D = score C → D.root = C.root → D = C) :
    ghostStep tree score eligible anchor = some C := by
  let children := tree.filter (fun B => B.parent? == some anchor && eligible B)
  have hC : C ∈ children := List.mem_filter.mpr ⟨hc, by simp [hp, he]⟩
  have hex : ∃ B, children.foldl (chooseChild score) none = some B := by
    cases hs : children with
    | nil => simp [hs] at hC
    | cons D xs => exact walk_aux_fold_choose_some score xs D
  obtain ⟨B, hf⟩ := hex
  have hB := (walk_aux_fold_choose_origin score children none B hf).resolve_left (by simp)
  obtain ⟨hb, hcond⟩ := List.mem_filter.mp hB
  have ⟨hpar, helig⟩ := Bool.and_eq_true_iff.mp hcond
  have hpar' : B.parent? = some anchor := by simpa using hpar
  have hBC := hbest B hb hpar' helig
  have hCB := (walk_aux_fold_bounds score children none B hf).2 C hC
  have hs : score B = score C := le_antisymm hBC.1 hCB.1
  have hr : B.root = C.root := le_antisymm (hBC.2 hs) (hCB.2 hs.symm)
  have hEq := hunique B hb hpar' helig hs hr
  subst B
  have htie : children.any
      (fun D => D != C && score D == score C && D.root == C.root) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨D, hd, hkey⟩ := List.any_eq_true.mp ht
    obtain ⟨hdt, hdcond⟩ := List.mem_filter.mp hd
    have ⟨hdp, hde⟩ := Bool.and_eq_true_iff.mp hdcond
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hkey
    exact hkey.1.1 (hunique D hdt (by simpa using hdp) hde hkey.1.2 hkey.2)
  change (match children.foldl (chooseChild score) none with
    | none => none
    | some B => if children.any (fun D => D != B && score D == score B && D.root == B.root)
        then none else some B) = some C
  rw [hf]
  change (if children.any (fun D => D != C && score D == score C && D.root == C.root)
    then none else some C) = some C
  rw [htie]
  rfl

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:138–154
/-- ROOT-DIGEST W1b: transfer the selected key and its unique child. -/
theorem walk_aux_ghostStep_transport_of_subset (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (anchor C : Block)
    (hsource : ghostStep sourceTree sourceScore sourceEligible anchor = some C)
    (hkeep : C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ D ∈ targetTree, D.parent? = some anchor → targetEligible D = true →
      D ∈ sourceTree ∧ sourceEligible D = true)
    (hscore : ∀ D ∈ targetTree, D.parent? = some anchor → targetEligible D = true →
      targetScore D = sourceScore D) :
    ghostStep targetTree targetScore targetEligible anchor = some C := by
  have hc := walk_aux_ghostStep_child sourceTree sourceScore sourceEligible anchor C hsource
  apply walk_aux_ghostStep_of_unique_best targetTree targetScore targetEligible anchor C
    hkeep.1 hc.2.1 hkeep.2
  · intro D hd hp he
    have hr := hreflect D hd hp he
    rw [hscore D hd hp he, hscore C hkeep.1 hc.2.1 hkeep.2]
    exact walk_aux_ghostStep_best sourceTree sourceScore sourceEligible anchor C
      hsource D hr.1 hp hr.2
  · intro D hd hp he hs hr
    have hD := hreflect D hd hp he
    have hs' : sourceScore D = sourceScore C := by
      rw [← hscore D hd hp he, ← hscore C hkeep.1 hc.2.1 hkeep.2]
      exact hs
    exact walk_aux_ghostStep_unique sourceTree sourceScore sourceEligible anchor C hsource
      D hD.1 hp hD.2 hs' hr

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:157–176
/-- ROOT-DIGEST W1b: transfer successful steps in both directions. -/
theorem walk_aux_ghostStep_eraseDups (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) :
    ghostStep tree.eraseDups score eligible anchor = ghostStep tree score eligible anchor := by
  cases hs : ghostStep tree score eligible anchor with
  | none =>
      cases hd : ghostStep tree.eraseDups score eligible anchor with
      | none => rfl
      | some C =>
          have hc := walk_aux_ghostStep_child tree.eraseDups score eligible anchor C hd
          have hb := walk_aux_ghostStep_transport_of_subset tree.eraseDups tree
            score score eligible eligible anchor C hd
            ⟨List.mem_eraseDups.mp hc.1, hc.2.2⟩
            (fun D hD _ he => ⟨List.mem_eraseDups.mpr hD, he⟩) (by intros; rfl)
          rw [hs] at hb
          contradiction
  | some C =>
      have hc := walk_aux_ghostStep_child tree score eligible anchor C hs
      exact walk_aux_ghostStep_transport_of_subset tree tree.eraseDups score score eligible eligible
        anchor C hs ⟨List.mem_eraseDups.mpr hc.1, hc.2.2⟩
        (fun D hd _ he => ⟨List.mem_eraseDups.mp hd, he⟩) (by intros; rfl)

-- Every selected child is a new strict descendant. Count only those candidates.
/-- ROOT-DIGEST W1b: exclude children with the structural count bound. -/
theorem walk_aux_ghostWalk_terminal_of_card (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block)
    (hcard : (tree.toFinset.filter (fun C => Block.Prec anchor C)).card ≤ fuel) :
    ghostStep tree score eligible (ghostWalk tree score eligible fuel anchor) = none := by
  induction fuel generalizing anchor with
  | zero =>
      apply walk_aux_ghostStep_none_of_noEligibleChild tree score eligible anchor
      intro C hC hp
      have hd := walk_aux_child_depth anchor C hp
      have hm : C ∈ tree.toFinset.filter (fun C => Block.Prec anchor C) := by
        apply Finset.mem_filter.mpr
        refine ⟨List.mem_toFinset.mpr hC,
          (walk_aux_prec_iff _ _).mpr ⟨?_, walk_aux_parent_prefix _ _ hp⟩⟩
        intro he
        rw [← he] at hd
        omega
      have hh := Finset.card_pos.mpr ⟨C, hm⟩
      omega
  | succ fuel ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none => rw [walk_aux_walk_none hs]; exact hs
      | some child =>
          rw [walk_aux_walk_some hs]
          apply ih child
          have hc := walk_aux_ghostStep_child tree score eligible anchor child hs
          have hd := walk_aux_child_depth anchor child hc.2.1
          let S := tree.toFinset.filter (fun C => Block.Prec anchor C)
          have hm : child ∈ S := by
            apply Finset.mem_filter.mpr
            refine ⟨List.mem_toFinset.mpr hc.1,
              (walk_aux_prec_iff _ _).mpr ⟨?_, walk_aux_parent_prefix _ _ hc.2.1⟩⟩
            intro he
            rw [← he] at hd
            omega
          have hsub : tree.toFinset.filter (fun C => Block.Prec child C) ⊆ S.erase child := by
            intro C hC
            obtain ⟨ht, hprec⟩ := Finset.mem_filter.mp hC
            obtain ⟨hne, hchild⟩ := (walk_aux_prec_iff _ _).mp hprec
            apply Finset.mem_erase.mpr
            refine ⟨Ne.symm hne, Finset.mem_filter.mpr ⟨ht, (walk_aux_prec_iff _ _).mpr ⟨?_,
              block_preceq_trans (walk_aux_parent_prefix _ _ hc.2.1) hchild⟩⟩⟩
            intro he
            have hh := prefix_depth child C hchild
            rw [← he] at hh
            omega
          have hle := Finset.card_le_card hsub
          have hdrop := Finset.card_erase_add_one hm
          change S.card ≤ fuel + 1 at hcard
          omega

theorem walk_aux_ghost_terminal (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) :
    ghostStep tree.eraseDups score eligible (ghost anchor tree score eligible) = none := by
  apply walk_aux_ghostWalk_terminal_of_card
  exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)

theorem walk_aux_ghostWalk_of_terminal (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor : Block)
    (hs : ghostStep tree score eligible anchor = none) :
    ghostWalk tree score eligible fuel anchor = anchor := by
  cases fuel with
  | zero => rfl
  | succ fuel => exact walk_aux_walk_none hs

theorem walk_aux_ghostWalk_terminal_unique (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (m n : Nat) (anchor : Block)
    (hm : ghostStep tree score eligible (ghostWalk tree score eligible m anchor) = none)
    (hn : ghostStep tree score eligible (ghostWalk tree score eligible n anchor) = none) :
    ghostWalk tree score eligible m anchor = ghostWalk tree score eligible n anchor := by
  induction m generalizing n anchor with
  | zero =>
      exact (walk_aux_ghostWalk_of_terminal tree score eligible n anchor hm).symm
  | succ m ih =>
      cases hs : ghostStep tree score eligible anchor with
      | none =>
          rw [walk_aux_ghostWalk_of_terminal _ _ _ _ _ hs,
            walk_aux_ghostWalk_of_terminal _ _ _ _ _ hs]
      | some C =>
          cases n with
          | zero => change ghostStep tree score eligible anchor = none at hn; simp [hs] at hn
          | succ n =>
              rw [walk_aux_walk_some hs] at hm
              rw [walk_aux_walk_some hs] at hn
              rw [walk_aux_walk_some hs, walk_aux_walk_some hs]
              exact ih n C hm hn

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:215–251
theorem walk_aux_ghostWalk_step_towards_result (tree : List Block) (score : Block → Nat)
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
          rw [walk_aux_walk_none hs] at hwalk
          subst H
          exact (hne (prefix_eq_of_depth X A hXH (prefix_depth A X hAX))).elim
      | some C =>
          have hw : ghostWalk tree score eligible fuel C = H := by
            simpa only [walk_aux_walk_some hs] using hwalk
          have hCH : Block.Preceq C H := by
            rw [← hw]
            exact walk_aux_ghostWalk_extends tree score eligible fuel C
          by_cases hXA : X = A
          · subst X; exact ⟨C, hs, hCH⟩
          · apply ih C hw ?_
            rcases block_preceq_total_of_common hCH hXH with hCX | hXC
            · exact hCX
            · have hAd : A.depth < X.depth := by
                have hd := prefix_depth A X hAX
                have hneq : X.depth ≠ A.depth := by
                  intro he
                  exact hXA (prefix_eq_of_depth A X hAX he.le).symm
                omega
              have hCd := walk_aux_child_depth A C
                (walk_aux_ghostStep_child tree score eligible A C hs).2.1
              have he := prefix_eq_of_depth X C hXC (by omega)
              rw [he]
              exact block_preceq_refl C

theorem walk_aux_child_prefix_of_common (X C B H : Block)
    (hp : C.parent? = some X) (hXB : Block.Prec X B)
    (hCH : Block.Preceq C H) (hBH : Block.Preceq B H) : Block.Preceq C B := by
  rcases block_preceq_total_of_common hCH hBH with hCB | hBC
  · exact hCB
  · have hd := walk_aux_child_depth X C hp
    obtain ⟨hne, hXB⟩ := (walk_aux_prec_iff _ _).mp hXB
    have hXd := prefix_depth X B hXB
    have hlt : X.depth < B.depth := by
      have hn : ¬ B.depth ≤ X.depth := fun hh => hne (prefix_eq_of_depth X B hXB hh)
      omega
    have he := prefix_eq_of_depth B C hBC (by omega)
    rw [he]
    exact block_preceq_refl C

theorem walk_aux_same_child_of_common (C D H : Block) (hp : C.parent? = D.parent?)
    (hCH : Block.Preceq C H) (hDH : Block.Preceq D H) : C = D := by
  by_contra hne
  have hf := walk_aux_siblings_incompatible C D hp hne
  have ht := block_compatible_of_common hCH hDH
  change Block.compatible C D = true at ht
  rw [hf] at ht
  contradiction

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:253–263
theorem walk_aux_ghost_step_towards_prefix (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor target X : Block)
    (hcover : Block.Preceq target (ghost anchor tree score eligible))
    (hAX : Block.Preceq anchor X) (hXT : Block.Prec X target) :
    ∃ C, ghostStep tree.eraseDups score eligible X = some C ∧ Block.Preceq C target := by
  obtain ⟨hne, hXT'⟩ := (walk_aux_prec_iff _ _).mp hXT
  have hXH := block_preceq_trans hXT' hcover
  have hneH : X ≠ ghost anchor tree score eligible := by
    intro he
    exact hne (block_preceq_antisymm hXT' (he ▸ hcover))
  obtain ⟨C, hs, hCH⟩ := walk_aux_ghostWalk_step_towards_result tree.eraseDups score eligible
    tree.eraseDups.length anchor _ X rfl hAX hXH hneH
  exact ⟨C, hs, walk_aux_child_prefix_of_common X C target _
    (walk_aux_ghostStep_child _ _ _ _ _ hs).2.1 hXT hCH hcover⟩

theorem walk_aux_ghostWalk_reanchor_terminal (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel otherFuel : Nat) (anchor target : Block)
    (ha : Block.Preceq anchor target)
    (hcover : Block.Preceq target (ghostWalk tree score eligible fuel anchor))
    (ht : ghostStep tree score eligible (ghostWalk tree score eligible fuel anchor) = none)
    (ho : ghostStep tree score eligible (ghostWalk tree score eligible otherFuel target) = none) :
    ghostWalk tree score eligible fuel anchor = ghostWalk tree score eligible otherFuel target := by
  induction fuel generalizing anchor with
  | zero =>
      have he := block_preceq_antisymm ha hcover
      subst anchor
      exact walk_aux_ghostWalk_terminal_unique tree score eligible 0 otherFuel target ht ho
  | succ fuel ih =>
      by_cases he : anchor = target
      · subst anchor
        exact walk_aux_ghostWalk_terminal_unique tree score eligible (fuel + 1)
          otherFuel target ht ho
      · cases hs : ghostStep tree score eligible anchor with
        | none =>
            rw [walk_aux_walk_none hs] at hcover
            exact (he (block_preceq_antisymm ha hcover)).elim
        | some C =>
            rw [walk_aux_walk_some hs] at hcover ht ⊢
            apply ih C ?_ hcover ht
            exact walk_aux_child_prefix_of_common anchor C target _
              (walk_aux_ghostStep_child _ _ _ _ _ hs).2.1 ((walk_aux_prec_iff _ _).mpr ⟨he, ha⟩)
              (walk_aux_ghostWalk_extends _ _ _ _ _) hcover

-- port: AvailableChainGridCO/Proofs/WalkTransport.lean:265–284
theorem walk_aux_walk_covers_steps (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (base target : Block)
    (hstep : ∀ X, Block.Preceq base X → Block.Prec X target →
      ∃ C, ghostStep tree score eligible X = some C ∧ Block.Preceq C target)
    (fuel : Nat) (anchor : Block) (hbase : Block.Preceq base anchor)
    (ha : Block.Preceq anchor target) (hf : target.depth ≤ anchor.depth + fuel) :
    Block.Preceq target (ghostWalk tree score eligible fuel anchor) := by
  induction fuel generalizing anchor with
  | zero =>
      have he := prefix_eq_of_depth anchor target ha (by simpa using hf)
      subst anchor
      exact block_preceq_refl _
  | succ fuel ih =>
      by_cases he : anchor = target
      · subst anchor
        exact walk_aux_ghostWalk_extends tree score eligible _ target
      · obtain ⟨C, hs, hCT⟩ := hstep anchor hbase ((walk_aux_prec_iff _ _).mpr ⟨he, ha⟩)
        have hc := walk_aux_ghostStep_child tree score eligible anchor C hs
        have hd := walk_aux_child_depth anchor C hc.2.1
        rw [walk_aux_walk_some hs]
        exact ih C (block_preceq_trans hbase (walk_aux_parent_prefix _ _ hc.2.1)) hCT (by omega)

theorem walk_aux_source_suffix_selected (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hcover : Block.Preceq target (ghost anchor tree score eligible))
    (C : Block) (hAC : Block.Prec anchor C) (hCT : Block.Preceq C target) :
    ∃ X, C.parent? = some X ∧ Block.Preceq anchor X ∧ Block.Prec X target ∧
      ghostStep tree score eligible X = some C := by
  obtain ⟨hne, hAC'⟩ := (walk_aux_prec_iff _ _).mp hAC
  cases C with
  | genesis => exact (hne (of_decide_eq_true hAC')).elim
  | node X s r_s id =>
      have hAX : Block.Preceq anchor X := by
        change (decide (anchor = Block.node X s r_s id) || Block.preceq anchor X) = true at hAC'
        exact (Bool.or_eq_true_iff.mp hAC').resolve_left (by simpa using hne)
      have hXT : Block.Prec X target := by
        apply (walk_aux_prec_iff _ _).mpr
        refine ⟨?_, block_preceq_trans (walk_aux_parent_prefix X (.node X s r_s id) rfl) hCT⟩
        intro he
        have hd := prefix_depth (.node X s r_s id) target hCT
        rw [← he] at hd
        change X.depth + 1 ≤ X.depth at hd
        omega
      obtain ⟨D, hs, hDT⟩ := walk_aux_ghost_step_towards_prefix tree score eligible anchor target X
        hcover hAX hXT
      have hd := walk_aux_ghostStep_child _ _ _ _ _ hs
      have he := walk_aux_same_child_of_common D (.node X s r_s id) target hd.2.1 hDT hCT
      subst D
      exact ⟨X, rfl, hAX, hXT,
        (walk_aux_ghostStep_eraseDups tree score eligible X).symm.trans hs⟩

public section

/-- Strict dominance on the suffix makes the result cover the target. -/
theorem walk_covers_of_dominated_suffix_statement : WalkCoversOfDominatedSuffixStatement := by
  rw [WalkCoversOfDominatedSuffixStatement_def]
  exact walk_aux_ghost_covers_of_path_dominance

/-- An eligible anchor gives an eligible result that covers the target. -/
theorem walk_covers_of_dominated_suffix_of_anchor_eligible_statement :
    WalkCoversOfDominatedSuffixOfAnchorEligibleStatement := by
  rw [WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def]
  intro anchor target tree score eligible hcomp hdom hel
  refine ⟨walk_covers_of_dominated_suffix_statement anchor target tree score eligible
    hcomp hdom, ?_⟩
  rcases walk_aux_ghostWalk_eligible tree.eraseDups score eligible
    tree.eraseDups.length anchor with he | he
  · change eligible (ghostWalk tree.eraseDups score eligible tree.eraseDups.length anchor) = true
    rw [he]
    exact hel
  · exact he

/-- A bound on descendant depth gives a terminal result with the stated fuel. -/
theorem walk_terminal_of_descendant_depth_bound_statement :
    WalkTerminalOfDescendantDepthBoundStatement := by
  rw [WalkTerminalOfDescendantDepthBoundStatement_def]
  intro anchor tree score eligible fuel hdepth
  exact walk_aux_ghostWalk_terminal_of_depth_bound tree score eligible fuel anchor hdepth

/-- ROOT-DIGEST W1b: closure and tree root uniqueness exclude eligible children at the result. -/
theorem walk_noEligibleChild_of_anchorClosed_statement :
    WalkNoEligibleChildOfAnchorClosedStatement := by
  rw [WalkNoEligibleChildOfAnchorClosedStatement_def]
  exact walk_aux_ghost_result_no_eligible_child

/-- Moving the anchor along a dominated suffix preserves the result. -/
theorem walk_reanchor_of_dominated_suffix_statement :
    WalkReanchorOfDominatedSuffixStatement := by
  rw [WalkReanchorOfDominatedSuffixStatement_def]
  intro anchor target tree score eligible ha hdom
  have hcomp : Block.Compatible anchor target := Bool.or_eq_true_iff.mpr (Or.inl ha)
  have hcover := walk_covers_of_dominated_suffix_statement anchor target tree score eligible
    hcomp hdom
  exact walk_aux_ghostWalk_reanchor_terminal tree.eraseDups score eligible tree.eraseDups.length
    tree.eraseDups.length anchor target ha hcover
    (walk_aux_ghost_terminal anchor tree score eligible)
    (walk_aux_ghost_terminal target tree score eligible)

/-- ROOT-DIGEST W1b: a dominated suffix with no eligible child gives the exact result. -/
theorem walk_exact_of_dominated_suffix_statement : WalkExactOfDominatedSuffixStatement := by
  rw [WalkExactOfDominatedSuffixStatement_def]
  intro anchor target tree score eligible ha hdom hstop
  rw [walk_reanchor_of_dominated_suffix_statement anchor target tree score eligible ha hdom]
  apply walk_aux_ghostWalk_of_terminal
  apply walk_aux_ghostStep_none_of_noEligibleChild tree.eraseDups score eligible target
  intro C hC hp
  exact hstop C (List.mem_eraseDups.mp hC) hp

/-- A walk from an ancestor cannot pass through an ineligible child. -/
theorem walk_avoids_unsupported_child_statement : WalkAvoidsUnsupportedChildStatement := by
  rw [WalkAvoidsUnsupportedChildStatement_def]
  intro anchor parent child tree score eligible ha hp hel hcover
  have hd := walk_aux_child_depth parent child hp
  have hPC : Block.Prec parent child := (walk_aux_prec_iff _ _).mpr ⟨by
    intro he
    rw [← he] at hd
    omega, walk_aux_parent_prefix _ _ hp⟩
  obtain ⟨C, hs, hCC⟩ := walk_aux_ghost_step_towards_prefix tree score eligible anchor child parent
    hcover ha hPC
  have hc := walk_aux_ghostStep_child _ _ _ _ _ hs
  have he := prefix_eq_of_depth C child hCC (by rw [hd, walk_aux_child_depth _ _ hc.2.1])
  subst C
  rw [hel] at hc
  cases hc.2.2

/-- Suffix persistence, reflection, and score agreement transfer source coverage. -/
theorem ghost_transfer_sfx_statement : GhostTransferSfxStatement := by
  rw [GhostTransferSfxStatement_def]
  intro anchor target sourceTree targetTree sourceScore targetScore sourceEligible targetEligible
    ha hcover hkeep hreflect hscore
  have hpath : ∀ C, Block.Prec anchor C → Block.Preceq C target → C ∈ targetTree := by
    intro C hAC hCT
    obtain ⟨X, _, hAX, hXT, hs⟩ := walk_aux_source_suffix_selected anchor target sourceTree
      sourceScore sourceEligible hcover C hAC hCT
    exact (hkeep X C hAX hXT hs hCT).1
  apply walk_aux_walk_covers_steps targetTree.eraseDups targetScore targetEligible anchor target ?_
    targetTree.eraseDups.length anchor (block_preceq_refl _) ha
    (walk_aux_suffix_depth_le_fuel anchor target targetTree ha hpath)
  intro X hAX hXT
  obtain ⟨C, hs, hCT⟩ := walk_aux_ghost_step_towards_prefix sourceTree sourceScore sourceEligible
    anchor target X hcover hAX hXT
  have hs' : ghostStep sourceTree sourceScore sourceEligible X = some C :=
    (walk_aux_ghostStep_eraseDups sourceTree sourceScore sourceEligible X).symm.trans hs
  refine ⟨C, ?_, hCT⟩
  rw [walk_aux_ghostStep_eraseDups targetTree targetScore targetEligible X]
  exact walk_aux_ghostStep_transport_of_subset sourceTree targetTree sourceScore targetScore
    sourceEligible targetEligible X C hs' (hkeep X C hAX hXT hs' hCT)
    (hreflect X · hAX hXT) (hscore X · hAX hXT)

/-- A dominated suffix gives coverage, also when the target precedes the anchor. -/
theorem walk_covers_of_dominated_suffix (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hcomp : Block.Compatible anchor target)
    (hdom : DominatedSuffix anchor target tree score eligible) :
    Block.Preceq target (ghost anchor tree score eligible) :=
  walk_covers_of_dominated_suffix_statement anchor target tree score eligible hcomp hdom

/-- A terminal target is the exact result of the dominated suffix. -/
theorem walk_exact_of_dominated_suffix (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) (ha : Block.Preceq anchor target)
    (hdom : DominatedSuffix anchor target tree score eligible)
    (hstop : NoEligibleChild tree eligible target) : ghost anchor tree score eligible = target :=
  walk_exact_of_dominated_suffix_statement anchor target tree score eligible ha hdom hstop

/-- An anchor on the dominated suffix gives the same result. -/
theorem walk_reanchor_of_dominated_suffix (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) (ha : Block.Preceq anchor target)
    (hdom : DominatedSuffix anchor target tree score eligible) :
    ghost anchor tree score eligible = ghost target tree score eligible :=
  walk_reanchor_of_dominated_suffix_statement anchor target tree score eligible ha hdom

/-- An ineligible child cannot be covered from an ancestor of its parent. -/
theorem walk_avoids_unsupported_child (anchor parent child : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) (ha : Block.Preceq anchor parent)
    (hp : child.parent? = some parent) (hel : eligible child = false) :
    ¬ Block.Preceq child (ghost anchor tree score eligible) :=
  walk_avoids_unsupported_child_statement anchor parent child tree score eligible ha hp hel

/-- An eligible anchor gives eligible coverage of the dominated suffix. -/
theorem walk_covers_of_dominated_suffix_of_anchor_eligible (anchor target : Block)
    (tree : List Block) (score : Block → Nat) (eligible : Block → Bool)
    (hcomp : Block.Compatible anchor target)
    (hdom : DominatedSuffix anchor target tree score eligible) (hel : eligible anchor = true) :
    Block.Preceq target (ghost anchor tree score eligible) ∧
      eligible (ghost anchor tree score eligible) = true :=
  walk_covers_of_dominated_suffix_of_anchor_eligible_statement anchor target tree score eligible
    hcomp hdom hel

/-- A bound for stored descendants supplies enough fuel for a terminal result. -/
theorem walk_terminal_of_descendant_depth_bound (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) (fuel : Nat)
    (hdepth : DescendantDepthBound anchor tree fuel) :
    ghostStep tree score eligible (ghostWalk tree score eligible fuel anchor) = none :=
  walk_terminal_of_descendant_depth_bound_statement anchor tree score eligible fuel hdepth

/-- ROOT-DIGEST W1b: closure and tree root uniqueness exclude eligible children of the result. -/
theorem walk_noEligibleChild_of_anchorClosed (anchor : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) (hclosed : AnchorClosed anchor tree) :
    ∀ B ∈ tree, B.parent? = some (ghost anchor tree score eligible) → eligible B = false :=
  walk_noEligibleChild_of_anchorClosed_statement anchor tree score eligible hroot hclosed

/-- Source coverage transfers with the three local suffix premises. -/
theorem ghost_transfer_sfx (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool)
    (ha : Block.Preceq anchor target)
    (hcover : Block.Preceq target (ghost anchor sourceTree sourceScore sourceEligible))
    (hkeep : SuffixPersists anchor target sourceTree targetTree sourceScore
      sourceEligible targetEligible)
    (hreflect : SuffixReflects anchor target sourceTree targetTree sourceEligible targetEligible)
    (hscore : SuffixScoresAgree anchor target targetTree sourceScore targetScore targetEligible) :
    Block.Preceq target (ghost anchor targetTree targetScore targetEligible) :=
  ghost_transfer_sfx_statement anchor target sourceTree targetTree sourceScore targetScore
    sourceEligible targetEligible ha hcover hkeep hreflect hscore


/-- ROOT-DIGEST W1b: root uniqueness on the selected tree. Class (iii), selected-path composition.
DC: Goldfish/Walk.lean:433 `ghost_reaches`.
INTENTIONAL: GLY G10/G33 (RP01 R1 P5) compose walks through path score/root order.
Reanchor on the target's ancestry; no strict score gap is required. -/
theorem walk_reanchor_of_best_ancestry (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hroot : ∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B)
    (ha : Block.Preceq anchor target)
    (hancestry : ∀ X, Block.Preceq anchor X → Block.Prec X target →
      ∃ C, C.parent? = some X ∧ Block.Preceq C target ∧ C ∈ tree ∧
        eligible C = true ∧ ∀ D ∈ tree, D.parent? = some X → eligible D = true →
          score D ≤ score C ∧ (score D = score C → D.root ≤ C.root)) :
    ghost anchor tree score eligible = ghost target tree score eligible := by
  have hpath : ∀ C, Block.Prec anchor C → Block.Preceq C target → C ∈ tree := by
    intro C hAC hCT
    obtain ⟨hne, hAC'⟩ := (walk_aux_prec_iff _ _).mp hAC
    cases C with
    | genesis => exact (hne (of_decide_eq_true hAC')).elim
    | node X s r_s id =>
        have hAX : Block.Preceq anchor X := by
          change (decide (anchor = Block.node X s r_s id) || Block.preceq anchor X) = true at hAC'
          exact (Bool.or_eq_true_iff.mp hAC').resolve_left (by simpa using hne)
        have hXT : Block.Prec X target := by
          apply (walk_aux_prec_iff _ _).mpr
          refine ⟨?_, block_preceq_trans (walk_aux_parent_prefix X (.node X s r_s id) rfl) hCT⟩
          intro he
          have hd := prefix_depth (.node X s r_s id) target hCT
          rw [← he] at hd
          change X.depth + 1 ≤ X.depth at hd
          omega
        obtain ⟨D, hp, hDT, hm, _, _⟩ := hancestry X hAX hXT
        exact walk_aux_same_child_of_common D (.node X s r_s id) target hp hDT hCT ▸ hm
  have hc : Block.Preceq target (ghost anchor tree score eligible) := by
    apply walk_aux_walk_covers_steps tree.eraseDups score eligible anchor target ?_
      tree.eraseDups.length anchor (block_preceq_refl _) ha
      (walk_aux_suffix_depth_le_fuel anchor target tree ha hpath)
    intro X hAX hXT
    obtain ⟨C, hp, hCT, hm, hel, hbest⟩ := hancestry X hAX hXT
    refine ⟨C, ?_, hCT⟩
    rw [walk_aux_ghostStep_eraseDups]
    exact walk_aux_ghostStep_of_best tree score eligible X C hroot hm hp hel hbest
  exact walk_aux_ghostWalk_reanchor_terminal tree.eraseDups score eligible tree.eraseDups.length
    tree.eraseDups.length anchor target ha hc
    (walk_aux_ghost_terminal anchor tree score eligible)
    (walk_aux_ghost_terminal target tree score eligible)

/-- Class (iii), selected-path extraction. DC: ProposalWalkTransportCore.lean:162
`ghost_transport_of_source` extracts source steps. SAME path ingredient, with the
score/root order made explicit (GLY G11, RP14 R1 core). -/
theorem walk_best_ancestry_of_cover (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hcover : Block.Preceq target (ghost anchor tree score eligible)) :
    ∀ X, Block.Preceq anchor X → Block.Prec X target →
      ∃ C, C.parent? = some X ∧ Block.Preceq C target ∧ C ∈ tree ∧
        eligible C = true ∧ ∀ D ∈ tree, D.parent? = some X → eligible D = true →
          score D ≤ score C ∧ (score D = score C → D.root ≤ C.root) := by
  intro X hAX hXT
  obtain ⟨C, hs, hCT⟩ := walk_aux_ghost_step_towards_prefix tree score eligible
    anchor target X hcover hAX hXT
  rw [walk_aux_ghostStep_eraseDups] at hs
  obtain ⟨hm, hp, hel⟩ := walk_aux_ghostStep_child tree score eligible X C hs
  exact ⟨C, hp, hCT, hm, hel, walk_aux_ghostStep_best tree score eligible X C hs⟩

end

end AvailableChain.Gen.Pure

namespace AvailableChain.Gen.Pure

open AvailableChain GridCO

public section

/-- Class (iii). DC: additive (no DC counterpart); reason: split the named
best-order path at a common ancestor for retained-domain callers. -/
theorem bestAncestry_restrict (a b c : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (h : BestAncestry a c tree score eligible)
    (hab : Block.Preceq a b) (hbc : Block.Preceq b c) :
    BestAncestry a b tree score eligible ∧ BestAncestry b c tree score eligible := by
  constructor
  · intro X hAX hXB
    obtain ⟨hne, hXb⟩ := (walk_aux_prec_iff X b).mp hXB
    have hXC : Block.Prec X c := (walk_aux_prec_iff X c).mpr ⟨by
      intro he
      subst X
      exact hne (block_preceq_antisymm hXb hbc), block_preceq_trans hXb hbc⟩
    obtain ⟨C, hp, hCc, hm, hel, hbest⟩ := h X hAX hXC
    exact ⟨C, hp, walk_aux_child_prefix_of_common X C b c hp hXB hCc hbc,
      hm, hel, hbest⟩
  · intro X hBX hXC
    exact h X (block_preceq_trans hab hBX) hXC

/-- Class (iii). DC: additive (no DC counterpart); reason: join two named
best-order paths without a strict score gap. -/
theorem bestAncestry_concat (a b c : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hab : BestAncestry a b tree score eligible)
    (hbc : BestAncestry b c tree score eligible)
    (_hAB : Block.Preceq a b) (hBC : Block.Preceq b c) :
    BestAncestry a c tree score eligible := by
  intro X hAX hXC
  by_cases hBX : Block.Preceq b X
  · exact hbc X hBX hXC
  · have hXc := ((walk_aux_prec_iff X c).mp hXC).2
    have hXb := (block_preceq_total_of_common hXc hBC).resolve_right hBX
    have hXB : Block.Prec X b := (walk_aux_prec_iff X b).mpr ⟨by
      intro he
      subst X
      exact hBX (block_preceq_refl b), hXb⟩
    obtain ⟨C, hp, hCb, hm, hel, hbest⟩ := hab X hAX hXB
    exact ⟨C, hp, block_preceq_trans hCb hBC, hm, hel, hbest⟩

/-- Class (iii). DC: additive (no DC counterpart); reason: adapt strict
suffix dominance to the named score/root path order. -/
theorem bestAncestry_of_dominatedSuffix (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool)
    (hdom : DominatedSuffix anchor target tree score eligible) :
    BestAncestry anchor target tree score eligible := by
  intro X hAX hXT
  obtain ⟨hne, hXt⟩ := (walk_aux_prec_iff X target).mp hXT
  obtain ⟨C, hp, hCT⟩ := path_child X target hXt hne
  have hAC : Block.Prec anchor C := (walk_aux_prec_iff anchor C).mpr ⟨by
    intro he
    have hd := walk_aux_child_depth X C hp
    have hle := prefix_depth anchor X hAX
    rw [he] at hle
    omega, block_preceq_trans hAX (walk_aux_parent_prefix X C hp)⟩
  obtain ⟨hm, hel, hbest⟩ := hdom C hAC hCT
  refine ⟨C, hp, hCT, hm, hel, ?_⟩
  intro B hB hpar hE
  by_cases he : B = C
  · subst B
    exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩
  · have hlt := hbest B hB (hpar.trans hp.symm) hE he
    exact ⟨Nat.le_of_lt hlt, fun heq => (Nat.ne_of_lt hlt heq).elim⟩

/-- ROOT-DIGEST W1b: use root uniqueness on the target tree. Class (iii).
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/ProposalWalkTransportCore.lean:162,259;
DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: compose the two best-order prefixes with retained suffix transport.
The per-reader splice gives G11 coverage with the existing list fuel. -/
theorem walk_covers_of_retained_transport
    (sourceAnchor targetAnchor cut parent : Block)
    (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat)
    (sourceEligible targetEligible : Block → Bool)
    (htargetRoot : ∀ A ∈ targetTree, ∀ B ∈ targetTree, A.root = B.root → A = B)
    (hsource : Block.Preceq parent (ghost sourceAnchor sourceTree sourceScore sourceEligible))
    (source_cut : Block.Preceq sourceAnchor cut)
    (target_cut : Block.Preceq targetAnchor cut)
    (cut_parent : Block.Preceq cut parent)
    (target_prefix : BestAncestry targetAnchor cut targetTree targetScore targetEligible)
    (persists : SuffixPersists cut parent sourceTree targetTree
      sourceScore sourceEligible targetEligible)
    (reflects : SuffixReflects cut parent sourceTree targetTree sourceEligible targetEligible)
    (scores : SuffixScoresAgree cut parent targetTree sourceScore targetScore targetEligible) :
    Block.Preceq parent (ghost targetAnchor targetTree targetScore targetEligible) := by
  have hcut := block_preceq_trans cut_parent hsource
  have hsource_splice := walk_aux_ghostWalk_reanchor_terminal sourceTree.eraseDups
    sourceScore sourceEligible sourceTree.eraseDups.length sourceTree.eraseDups.length
    sourceAnchor cut source_cut hcut
    (walk_aux_ghost_terminal sourceAnchor sourceTree sourceScore sourceEligible)
    (walk_aux_ghost_terminal cut sourceTree sourceScore sourceEligible)
  change ghost sourceAnchor sourceTree sourceScore sourceEligible =
    ghost cut sourceTree sourceScore sourceEligible at hsource_splice
  have hsource_cut : Block.Preceq parent (ghost cut sourceTree sourceScore sourceEligible) := by
    rw [← hsource_splice]
    exact hsource
  have htarget_splice := walk_reanchor_of_best_ancestry targetAnchor cut
    targetTree targetScore targetEligible htargetRoot target_cut target_prefix
  rw [htarget_splice]
  exact ghost_transfer_sfx cut parent sourceTree targetTree sourceScore targetScore
    sourceEligible targetEligible cut_parent hsource_cut persists reflects scores

/-- Class (iii).
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/ProposalWalkTransportCore.lean:162,259;
DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: prove the universal Generic statement for per-reader G11 coverage.
ROOT-DIGEST W1c: the statement supplies target-tree root uniqueness. -/
theorem walk_covers_of_retained_transport_statement :
    WalkCoversOfRetainedTransportStatement := by
  rw [WalkCoversOfRetainedTransportStatement_def]
  exact walk_covers_of_retained_transport

end

end AvailableChain.Gen.Pure
