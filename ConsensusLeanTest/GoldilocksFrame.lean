module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FrameClaims
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Tauto
@[expose] public section

/-! # Witnesses for the Goldilocks Common and Frame statements

On `Spec/Common` and `Spec/Frame`, labelled by kind (CONTRIBUTING "Statements"):

* (a) `frameOK_Φ₀`, `frameOK_Φ₁`: well-formed frames exist (the hypotheses of the G0.4 (frame)
  statements), one with a single block and one with a fork choice root above `F`.
* (a) `step_Φ₀_Φ₁`: a step that adds a block and keeps `F` (the hypothesis of
  `FrameStepAddsBlock`).
* (a) `step_Φ₁_Φ₂`: a step that moves `F` to the parent of the new block, so that genesis
  leaves the tree.
* (a) `seq_hyps`: a frame sequence `Φ₀, Φ₁, Φ₂, Φ₂, …` with its trees in the coherent set
  `U = {g, b₁, b₂}` and a rooted first frame (the hypotheses of `FrameRetention`,
  `FrameNeverReturns` and `FrameEntersOnce`). -/

namespace Consensus.Goldilocks.Test

/-- A block among one validator, with no payloads. -/
abbrev B1 := Block 1 Unit Unit

/-- Genesis: root `0`, slot `0`, no parent. -/
def g : B1 := ⟨0, none, 0, 0, 0, (), ()⟩
/-- Block `1` on genesis, slot `1`. -/
def b₁ : B1 := ⟨1, some 0, 1, 0, 0, (), ()⟩
/-- Block `2` on block `1`, slot `2`. -/
def b₂ : B1 := ⟨2, some 1, 2, 0, 0, (), ()⟩

/-- The genesis frame. -/
def Φ₀ : Frame 1 Unit Unit := ⟨{g}, g, g, {g}⟩
/-- After accepting `b₁`: `F = g`, the fork choice root `b₁`. -/
def Φ₁ : Frame 1 Unit Unit := ⟨{g, b₁}, g, b₁, {b₁}⟩
/-- After accepting `b₂` with `F` moved to `b₁`: genesis leaves the tree. -/
def Φ₂ : Frame 1 Unit Unit := ⟨{b₁, b₂}, b₁, b₂, {b₂}⟩

/-- The sequence `Φ₀, Φ₁, Φ₂, Φ₂, …`. -/
def seq : Nat → Frame 1 Unit Unit
  | 0 => Φ₀
  | 1 => Φ₁
  | _ + 2 => Φ₂

/-- A parent edge inside `S` gives ancestry. -/
theorem edge {S : Set B1} {B C : B1} (hB : B ∈ S) (hC : C ∈ S) (h : C.parent = B.root) :
    Anc S B C :=
  Relation.ReflTransGen.single ⟨hB, hC, h⟩

/-- Genesis has no strict ancestor. -/
theorem anc_g {S : Set B1} {A : B1} (h : Anc S A g) : A = g := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨P, _, ⟨_, _, he⟩⟩
  · exact h.symm
  · simp [g] at he

/-- `{g, b₁, b₂}` is coherent. -/
theorem coherent_U : Coherent ({g, b₁, b₂} : Set B1) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all [g, b₁, b₂]
  · intro x hx y hy h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all [g, b₁, b₂]

/-- Every subset of `{g, b₁, b₂}` is coherent. -/
theorem coherent_sub {S : Set B1} (hS : S ⊆ {g, b₁, b₂}) : Coherent S :=
  ⟨coherent_U.1.mono hS, fun B hB C hC h => coherent_U.2 B (hS hB) C (hC |> hS) h⟩

/-- (a) The genesis frame is well formed. -/
theorem frameOK_Φ₀ : FrameOK Φ₀ where
  coherent := coherent_sub (by simp [Φ₀])
  finite := Set.finite_singleton g
  rooted := ⟨rfl, fun C hC => by rw [Set.mem_singleton_iff.mp hC]; exact Relation.ReflTransGen.refl⟩
  fcRoot_mem := rfl
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := le_rfl
  fcRoot_anc_viableHeads := fun W hW => by
    rw [Set.mem_singleton_iff.mp hW]; exact Relation.ReflTransGen.refl

/-- (a) A well-formed frame whose fork choice root is above `F`. -/
theorem frameOK_Φ₁ : FrameOK Φ₁ where
  finite := (Set.finite_singleton b₁).insert g
  coherent := coherent_sub (by intro x; simp [Φ₁]; tauto)
  rooted := ⟨by simp [Φ₁], fun C hC => by
    rcases hC with rfl | hC
    · exact Relation.ReflTransGen.refl
    · rw [Set.mem_singleton_iff.mp hC]; exact edge (by simp [Φ₁]) (by simp [Φ₁]) rfl⟩
  fcRoot_mem := by simp [Φ₁]
  F_anc_fcRoot := edge (by simp [Φ₁]) (by simp [Φ₁]) rfl
  viableHeads_subset := by simp [Φ₁]
  fcRoot_anc_viableHeads := fun W hW => by
    rw [Set.mem_singleton_iff.mp hW]; exact Relation.ReflTransGen.refl

/-- (a) `Φ₀ ⊑_{b₁} Φ₁`: the step adds `b₁` and keeps `F = g`. -/
theorem step_Φ₀_Φ₁ : FrameStep Φ₀ b₁ Φ₁ where
  new := by simp [Φ₀, g, b₁]
  parent_mem := ⟨g, rfl, rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := edge (S := insert b₁ Φ₀.tree) (B := g) (by simp [Φ₀]) (by simp) rfl
  tree_eq := by
    ext X
    simp only [Φ₀, Φ₁, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr rfl, Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inl rfl, edge (by simp) (by simp) rfl⟩
    · rintro ⟨h, -⟩; tauto

/-- (a) `Φ₁ ⊑_{b₂} Φ₂`: the step adds `b₂` and moves `F` to `b₁`, so genesis leaves. -/
theorem step_Φ₁_Φ₂ : FrameStep Φ₁ b₂ Φ₂ where
  new := by simp [Φ₁, g, b₁, b₂]
  parent_mem := ⟨b₁, by simp [Φ₁], rfl⟩
  F_anc_F' := edge (S := insert b₂ Φ₁.tree) (B := g) (C := b₁) (by simp [Φ₁]) (by simp [Φ₁]) rfl
  F'_anc_B := edge (S := insert b₂ Φ₁.tree) (B := b₁) (by simp [Φ₁]) (by simp) rfl
  tree_eq := by
    ext X
    simp only [Φ₁, Φ₂, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inr rfl), Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inl rfl, edge (by simp) (by simp) rfl⟩
    · rintro ⟨h | h | h, hA⟩
      · exact Or.inr h
      · subst h
        have := anc_g hA
        exact absurd this (by simp [g, b₁])
      · exact Or.inl h

/-- (a) The hypotheses of `FrameRetention`, `FrameNeverReturns` and `FrameEntersOnce` hold
together. -/
theorem seq_hyps : FrameSeqIn seq {g, b₁, b₂} := by
  refine ⟨frameSeq_iff.mpr ?_, frameOK_Φ₀.rooted, fun i => ?_, coherent_U⟩
  · intro i
    rcases i with _ | _ | i
    · exact Or.inr ⟨b₁, step_Φ₀_Φ₁⟩
    · exact Or.inr ⟨b₂, step_Φ₁_Φ₂⟩
    · exact Or.inl rfl
  · rcases i with _ | _ | i <;> intro x <;> simp [seq, Φ₀, Φ₁, Φ₂] <;> tauto

end Consensus.Goldilocks.Test

end
