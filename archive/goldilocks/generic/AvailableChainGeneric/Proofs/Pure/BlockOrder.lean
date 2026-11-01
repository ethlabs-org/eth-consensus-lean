module
public import AvailableChainModel.Objects.Blocks
public import Mathlib.Data.List.Nodup -- shake: keep (re-export)
public import Mathlib.Data.Finset.Max

public section

namespace AvailableChain.Gen.Pure

-- Source: AvailableChainFGSA/Proofs/BlockAncestry.lean:14–131 (E-1, D07).
-- Use branch reduction to keep model equations out of this proof interface.
/-- [helper] `B ⪯ B`. -/
theorem block_preceq_refl (B : Block) : Block.Preceq B B := by
  cases B with
  | genesis => rfl
  | node p s r_s r =>
      change (decide (Block.node p s r_s r = Block.node p s r_s r) || Block.preceq (.node p s r_s
        r) p) = true
      simp only [decide_true, Bool.true_or]
/-- [helper] `⪯` is transitive. -/
theorem block_preceq_trans {A B C : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C := by
  induction C with
  | genesis =>
      change decide (B = Block.genesis) = true at h₂
      simp only [decide_eq_true_eq] at h₂
      subst h₂
      exact h₁
  | node p s r_s r ih =>
      change (decide (B = Block.node p s r_s r) || Block.preceq B p) = true at h₂
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h₂
      change Block.preceq A (Block.node p s r_s r) = true
      rcases h₂ with h | h
      · subst h
        exact h₁
      · have hAp : Block.preceq A p = true := ih h
        change (decide (A = Block.node p s r_s r) || Block.preceq A p) = true
        simp only [hAp, Bool.or_true]
/-- [helper] `⪯` is antisymmetric. -/
theorem block_preceq_antisymm {A B : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B A) :
    A = B := by
  have hle : ∀ {X Y : Block}, Block.Preceq X Y → X.depth ≤ Y.depth := by
    intro X Y h
    induction Y with
    | genesis =>
        change decide (X = Block.genesis) = true at h
        simp only [decide_eq_true_eq] at h
        subst h
        exact Nat.le_refl _
    | node p s r_s r ih =>
        change (decide (X = Block.node p s r_s r) || Block.preceq X p) = true at h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · subst h
          exact Nat.le_refl _
        · have := ih h
          change X.depth ≤ p.depth + 1
          omega
  have heq : ∀ {X Y : Block}, Block.Preceq X Y → Y.depth ≤ X.depth → X = Y := by
    intro X Y h hd
    induction Y with
    | genesis =>
        change decide (X = Block.genesis) = true at h
        simp only [decide_eq_true_eq] at h
        exact h
    | node p s r_s r _ =>
        change (decide (X = Block.node p s r_s r) || Block.preceq X p) = true at h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · exact h
        · exfalso
          have h1 := hle h
          change p.depth + 1 ≤ X.depth at hd
          omega
  exact heq h₁ (hle h₂)
/-- [helper] Genesis precedes every block. -/
theorem block_genesis_preceq (B : Block) : Block.Preceq .genesis B := by
  induction B with
  | genesis => exact block_preceq_refl _
  | node p s r_s r ih =>
      change Block.preceq .genesis p = true at ih
      change (decide (Block.genesis = Block.node p s r_s r) || Block.preceq .genesis p) = true
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ih
/-- [helper] Two ancestors of one block are comparable. -/
theorem block_preceq_total_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Preceq A B ∨ Block.Preceq B A := by
  induction W with
  | genesis =>
      change decide (A = Block.genesis) = true at hA
      change decide (B = Block.genesis) = true at hB
      simp only [decide_eq_true_eq] at hA hB
      subst hA
      subst hB
      exact Or.inl (block_preceq_refl _)
  | node p s r_s r ih =>
      change (decide (A = Block.node p s r_s r) || Block.preceq A p) = true at hA
      change (decide (B = Block.node p s r_s r) || Block.preceq B p) = true at hB
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hA hB
      rcases hA with hA | hA
      · rcases hB with hB | hB
        · subst hA; subst hB; exact Or.inl (block_preceq_refl _)
        · subst hA
          refine Or.inr ?_
          change Block.preceq B (Block.node p s r_s r) = true
          change (decide (B = Block.node p s r_s r) || Block.preceq B p) = true
          simp only [hB, Bool.or_true]
      · rcases hB with hB | hB
        · subst hB
          refine Or.inl ?_
          change Block.preceq A (Block.node p s r_s r) = true
          change (decide (A = Block.node p s r_s r) || Block.preceq A p) = true
          simp only [hA, Bool.or_true]
        · exact ih hA hB
/-- [helper] `compatible` is commutative. -/
theorem block_compatible_comm (A B : Block) : Block.compatible A B = Block.compatible B A := by
  unfold Block.compatible
  exact Bool.or_comm _ _
/-- [helper] Two blocks below one block are compatible. -/
theorem block_compatible_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Compatible A B := by
  unfold Block.Compatible Block.compatible
  simp only [Bool.or_eq_true]
  exact block_preceq_total_of_common hA hB
/-- [helper] bp01 §5 item 5: a block that conflicts with `X` conflicts with every
descendant of `X`. -/
theorem block_incompatible_of_preceq {b X Y : Block} (hbX : ¬ Block.Compatible b X)
    (hXY : Block.Preceq X Y) : ¬ Block.Compatible b Y := by
  intro hbY
  apply hbX
  unfold Block.Compatible Block.compatible at hbY
  simp only [Bool.or_eq_true] at hbY
  rcases hbY with hbY | hYb
  · exact block_compatible_of_common hbY hXY
  · have hXb := block_preceq_trans hXY hYb
    unfold Block.Compatible Block.compatible
    simp only [Bool.or_eq_true]
    exact Or.inr hXb
/-- [helper] If `A ⪯ C` and `C` is compatible with `F`, then `A` is compatible
with `F`. -/
theorem block_compatible_of_preceq_compatible {A C F : Block} (hAC : Block.Preceq A C)
    (hCF : Block.Compatible C F) : Block.Compatible A F := by
  unfold Block.Compatible Block.compatible at hCF
  simp only [Bool.or_eq_true] at hCF
  rcases hCF with hCF | hFC
  · have hAF := block_preceq_trans hAC hCF
    unfold Block.Compatible Block.compatible
    simp only [Bool.or_eq_true]
    exact Or.inl hAF
  · exact block_compatible_of_common hAC hFC

-- Source: AvailableChainGridCO/Proofs/Walk.lean:107–162 (E-1, D07).
theorem prefix_depth (A B : Block) (h : Block.Preceq A B) : A.depth ≤ B.depth := by
  induction B with
  | genesis => have : A = .genesis := by exact of_decide_eq_true h
               subst A; rfl
  | node P s r_s id ih =>
      obtain he | hp : A = .node P s r_s id ∨ Block.Preceq A P := by
        change (decide (A = Block.node P s r_s id) || Block.preceq A P) = true at h
        exact (Bool.or_eq_true_iff.mp h).imp of_decide_eq_true (fun hp => hp)
      · subst A; rfl
      · exact le_trans (ih hp) (Nat.le_succ _)

theorem prefix_eq_of_depth (A B : Block) (h : Block.Preceq A B)
    (hd : B.depth ≤ A.depth) : A = B := by
  cases B with
  | genesis => exact of_decide_eq_true h
  | node P s r_s id =>
      obtain he | hp : A = .node P s r_s id ∨ Block.Preceq A P := by
        change (decide (A = Block.node P s r_s id) || Block.preceq A P) = true at h
        exact (Bool.or_eq_true_iff.mp h).imp of_decide_eq_true (fun hp => hp)
      · exact he
      · have := prefix_depth A P hp
        change P.depth + 1 ≤ A.depth at hd
        omega

theorem path_child (A B : Block) (h : Block.Preceq A B) (hne : A ≠ B) :
    ∃ C, C.parent? = some A ∧ Block.Preceq C B := by
  induction B with
  | genesis => exact (hne (by exact of_decide_eq_true h)).elim
  | node P s r_s id ih =>
      have hp : Block.Preceq A P := by
        change (decide (A = Block.node P s r_s id) || Block.preceq A P) = true at h
        exact (Bool.or_eq_true_iff.mp h).resolve_left (by simpa only [decide_eq_true_eq] using hne)
      by_cases he : A = P
      · subst P
        exact ⟨.node A s r_s id, rfl, block_preceq_refl _⟩
      · obtain ⟨C, hc, hcp⟩ := ih hp he
        exact ⟨C, hc, Bool.or_eq_true_iff.mpr (Or.inr hcp)⟩

def pathNodes : Block → List Block
  | .genesis => []
  | b@(.node parent _ _ _) => b :: pathNodes parent

theorem pathNodes_spec (B : Block) :
    (pathNodes B).length = B.depth ∧ (pathNodes B).Nodup ∧
      ∀ C ∈ pathNodes B, C ≠ .genesis ∧ Block.Preceq C B := by
  induction B with
  | genesis =>
      change ([] : List Block).length = 0 ∧ ([] : List Block).Nodup ∧
        ∀ C ∈ ([] : List Block), C ≠ .genesis ∧ Block.Preceq C .genesis
      simp only [List.length_nil, List.nodup_nil, List.not_mem_nil, false_implies,
        implies_true, and_self]
  | node P s r_s id ih =>
      change (Block.node P s r_s id :: pathNodes P).length = P.depth + 1 ∧
        (Block.node P s r_s id :: pathNodes P).Nodup ∧
        ∀ C ∈ Block.node P s r_s id :: pathNodes P,
          C ≠ .genesis ∧ Block.Preceq C (.node P s r_s id)
      refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ ih.1, ?_, ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, ih.2.1⟩
        intro hmem
        have := prefix_depth _ _ (ih.2.2 _ hmem).2
        change P.depth + 1 ≤ P.depth at this
        omega
      · intro C hc
        rcases List.mem_cons.mp hc with rfl | hp
        · exact ⟨by simp, block_preceq_refl _⟩
        · exact ⟨(ih.2.2 C hp).1, Bool.or_eq_true_iff.mpr (Or.inr (ih.2.2 C hp).2)⟩

-- Source: TS/codex/scratch/a0-s1-reuse-map.md:678 (GLY G09; S1a RP24:1556).
/-- [helper] [GLY G09] A block compatible with two conflicting blocks
precedes both of them. -/
theorem two_conflicts {E J B : Block} (hEJ : ¬ Block.Compatible E J)
    (hE : Block.Compatible E B) (hJ : Block.Compatible J B) :
    Block.Preceq B E ∧ Block.Preceq B J := by
  have hBJcomp : Block.Compatible B J := by
    simpa only [Block.Compatible, block_compatible_comm J B] using hJ
  have hBE : Block.Preceq B E := by
    have hcases := hE
    unfold Block.Compatible Block.compatible at hcases
    simp only [Bool.or_eq_true] at hcases
    rcases hcases with hEB | hBE
    · exact (hEJ (block_compatible_of_preceq_compatible hEB hBJcomp)).elim
    · exact hBE
  have hBJ : Block.Preceq B J := by
    unfold Block.Compatible Block.compatible at hJ
    simp only [Bool.or_eq_true] at hJ
    rcases hJ with hJB | hBJ
    · apply False.elim
      apply hEJ
      unfold Block.Compatible Block.compatible
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_trans hJB hBE))
    · exact hBJ
  exact ⟨hBE, hBJ⟩

-- Source: TS/codex/scratch/a0-s1-reuse-map.md:679–680 (GLY G09; S3d AF-15).
/-- [helper] [GLY G09] A nonempty finite set of pairwise compatible blocks
has a member that follows every member. S3d calls this
`exists_deepest_of_pairwise_compatible`. -/
theorem deepest_of_compatible (S : Finset Block) (hne : S.Nonempty)
    (hc : ∀ x ∈ S, ∀ y ∈ S, Block.Compatible x y) :
    ∃ M ∈ S, ∀ x ∈ S, Block.Preceq x M := by
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image S Block.depth hne
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hcomp := hc x hx M hM
  unfold Block.Compatible Block.compatible at hcomp
  simp only [Bool.or_eq_true] at hcomp
  rcases hcomp with hxM | hMx
  · exact hxM
  · have heq := prefix_eq_of_depth M x hMx (hmax x hx)
    subst M
    exact block_preceq_refl x

end AvailableChain.Gen.Pure
