module
public import ConsensusLeanTest.GoldilocksFrame
@[expose] public section

/-! # Rejections for the Goldilocks frame-sequence statements

`FrameNeverReturns` and `FrameEntersOnce` (`Statements/Frame.lean`) assume `FrameSeqIn Φ U`: the
frames evolve by steps, the first frame is rooted, every tree lies in `U`, and `U` is coherent.
`GoldilocksFrame` shows these premises hold together (`seq_hyps`). Labelled by kind (CONTRIBUTING
"Statements"):

* (r) `frameNeverReturns_needs_coherent`, `frameEntersOnce_needs_coherent`: the sequence
  `Φ₀, Φ₁, Ψ₂, Ψ₃, Ψ₄, Ψ₄, …` evolves by steps and starts rooted, and its trees lie in
  `{g, b₁, c, d}`, which is not coherent because `d` reuses genesis's root `0`. The step to `Ψ₂`
  moves `F` to the fork `c`, so `b₁` leaves. `d` is added on `c`, and `b₁`, whose parent root `0`
  is now `d`'s, is added again on `d`. So `b₁` returns, and it enters at steps `0` and `3`.
* (r) `frameNeverReturns_needs_rooted`: the sequence `Τ₀, Φ₁, Τ₂, Τ₃, Τ₃, …` evolves by steps,
  and its trees lie in the coherent set `{g, b₁, y, x}`, but the first frame `{g, x}` is not
  rooted: `x`'s parent `y` is not yet in it. The step to `Φ₁` keeps `F = g`, so `x` leaves (it
  does not extend `g`); after `y` arrives, `x` is added again on `y` and returns. -/

namespace Consensus.Goldilocks.Test.FrameRejection

/-- A fork on genesis: root `3`, slot `1`. -/
def c : B1 := ⟨3, some 0, 1, 0, 0, (), ()⟩
/-- A block on `c` that reuses genesis's root `0`, slot `2`. -/
def d : B1 := ⟨0, some 3, 2, 0, 0, (), ()⟩
/-- A block on `b₁`: root `4`, slot `2`. -/
def y : B1 := ⟨4, some 1, 2, 0, 0, (), ()⟩
/-- A block on `y`: root `5`, slot `3`. -/
def x : B1 := ⟨5, some 4, 3, 0, 0, (), ()⟩

/-- After accepting `c` with `F` moved to `c`: `g` and `b₁` leave. -/
def Ψ₂ : Frame 1 Unit Unit := ⟨{c}, c, c, {c}⟩
/-- After accepting `d` on `c`. -/
def Ψ₃ : Frame 1 Unit Unit := ⟨{c, d}, c, c, {c}⟩
/-- After accepting `b₁` again, on `d`. -/
def Ψ₄ : Frame 1 Unit Unit := ⟨{c, d, b₁}, c, c, {c}⟩

/-- The sequence `Φ₀, Φ₁, Ψ₂, Ψ₃, Ψ₄, Ψ₄, …`. -/
def σ : Nat → Frame 1 Unit Unit
  | 0 => Φ₀
  | 1 => Φ₁
  | 2 => Ψ₂
  | 3 => Ψ₃
  | _ + 4 => Ψ₄

/-- An unrooted first frame: `x` is in it without its parent `y`. -/
def Τ₀ : Frame 1 Unit Unit := ⟨{g, x}, g, g, {g}⟩
/-- After accepting `y` on `b₁`. -/
def Τ₂ : Frame 1 Unit Unit := ⟨{g, b₁, y}, g, b₁, {b₁}⟩
/-- After accepting `x` again, on `y`. -/
def Τ₃ : Frame 1 Unit Unit := ⟨{g, b₁, y, x}, g, b₁, {b₁}⟩

/-- The sequence `Τ₀, Φ₁, Τ₂, Τ₃, Τ₃, …`. -/
def τ : Nat → Frame 1 Unit Unit
  | 0 => Τ₀
  | 1 => Φ₁
  | 2 => Τ₂
  | _ + 3 => Τ₃

/-- A strict ancestor inside `S` lies below a parent edge inside `S`. -/
theorem anc_cases {S : Set B1} {A C : B1} (h : Anc S A C) :
    A = C ∨ ∃ P ∈ S, C.parent = some P.root ∧ Anc S A P := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨P, hAP, hP, -, hCP⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨P, hP, hCP, hAP⟩

/-- `c` is not an ancestor of `b₁` inside `{c, g, b₁}`: `b₁`'s parent there is `g`. -/
theorem not_anc_c_b₁ : ¬ Anc (insert c ({g, b₁} : Set B1)) c b₁ := by
  intro h
  rcases anc_cases h with h | ⟨P, hP, hp, hA⟩
  · simp [c, b₁] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl
  · simp [c, b₁] at hp
  · exact absurd (anc_g hA) (by simp [c, g])
  · simp [b₁] at hp

/-- `g` is not an ancestor of `x` inside a set whose roots are `0`, `1` and `5`. -/
theorem not_anc_g_x {S : Set B1} (hS : S ⊆ {g, b₁, x}) : ¬ Anc S g x := by
  intro h
  rcases anc_cases h with h | ⟨P, hP, hp, -⟩
  · simp [g, x] at h
  rcases (by simpa using hS hP : P = g ∨ P = b₁ ∨ P = x) with rfl | rfl | rfl <;>
    simp [x, g, b₁] at hp

theorem step_Φ₁_Ψ₂ : FrameStep Φ₁ c Ψ₂ where
  new := by simp [Φ₁, g, b₁, c]
  parent_mem := ⟨g, by simp [Φ₁], rfl⟩
  F_anc_F' := edge (S := insert c Φ₁.tree) (B := g) (by simp [Φ₁]) (by simp [Ψ₂]) rfl
  F'_anc_B := Relation.ReflTransGen.refl
  tree_eq := by
    ext X
    simp only [Φ₁, Ψ₂, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨Or.inl rfl, Relation.ReflTransGen.refl⟩
    · rintro ⟨rfl | rfl | rfl, hA⟩
      · rfl
      · exact absurd (anc_g hA) (by simp [c, g])
      · exact absurd hA not_anc_c_b₁

theorem step_Ψ₂_Ψ₃ : FrameStep Ψ₂ d Ψ₃ where
  new := by simp [Ψ₂, c, d]
  parent_mem := ⟨c, rfl, rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := edge (S := insert d Ψ₂.tree) (B := c) (by simp [Ψ₂]) (by simp) rfl
  tree_eq := by
    ext X
    simp only [Ψ₂, Ψ₃, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr rfl, Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inl rfl, edge (by simp) (by simp) rfl⟩
    · rintro ⟨h, -⟩; tauto

theorem step_Ψ₃_Ψ₄ : FrameStep Ψ₃ b₁ Ψ₄ where
  new := by simp [Ψ₃, c, d, b₁]
  parent_mem := ⟨d, by simp [Ψ₃], rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := (edge (B := c) (C := d) (by simp [Ψ₃]) (by simp [Ψ₃]) rfl).trans
    (edge (by simp [Ψ₃]) (by simp) rfl)
  tree_eq := by
    ext X
    simp only [Ψ₃, Ψ₄, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hcd : Anc (insert b₁ ({c, d} : Set B1)) c d := edge (by simp) (by simp) rfl
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inr (Or.inr rfl), hcd⟩
      · exact ⟨Or.inl rfl, hcd.trans (edge (by simp) (by simp) rfl)⟩
    · rintro ⟨h, -⟩; tauto

theorem step_Τ₀_Φ₁ : FrameStep Τ₀ b₁ Φ₁ where
  new := by simp [Τ₀, g, b₁, x]
  parent_mem := ⟨g, by simp [Τ₀], rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := edge (S := insert b₁ Τ₀.tree) (B := g) (by simp [Τ₀]) (by simp) rfl
  tree_eq := by
    ext X
    simp only [Τ₀, Φ₁, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inl rfl, edge (by simp) (by simp) rfl⟩
    · rintro ⟨rfl | rfl | rfl, hA⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd hA (not_anc_g_x (by intro z; simp; tauto))

theorem step_Φ₁_Τ₂ : FrameStep Φ₁ y Τ₂ where
  new := by simp [Φ₁, g, b₁, y]
  parent_mem := ⟨b₁, by simp [Φ₁], rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := (edge (B := g) (C := b₁) (by simp [Φ₁]) (by simp [Φ₁]) rfl).trans
    (edge (by simp [Φ₁]) (by simp) rfl)
  tree_eq := by
    ext X
    simp only [Φ₁, Τ₂, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hgb : Anc (insert y ({g, b₁} : Set B1)) g b₁ := edge (by simp) (by simp) rfl
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inr (Or.inr rfl), hgb⟩
      · exact ⟨Or.inl rfl, hgb.trans (edge (by simp) (by simp) rfl)⟩
    · rintro ⟨h, -⟩; tauto

theorem step_Τ₂_Τ₃ : FrameStep Τ₂ x Τ₃ where
  new := by simp [Τ₂, g, b₁, y, x]
  parent_mem := ⟨y, by simp [Τ₂], rfl⟩
  F_anc_F' := Relation.ReflTransGen.refl
  F'_anc_B := ((edge (B := g) (C := b₁) (by simp [Τ₂]) (by simp [Τ₂]) rfl).trans
    (edge (C := y) (by simp [Τ₂]) (by simp [Τ₂]) rfl)).trans (edge (by simp [Τ₂]) (by simp) rfl)
  tree_eq := by
    ext X
    simp only [Τ₂, Τ₃, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hgb : Anc (insert x ({g, b₁, y} : Set B1)) g b₁ := edge (by simp) (by simp) rfl
    have hgy : Anc (insert x ({g, b₁, y} : Set B1)) g y := hgb.trans (edge (by simp) (by simp) rfl)
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), Relation.ReflTransGen.refl⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hgb⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hgy⟩
      · exact ⟨Or.inl rfl, hgy.trans (edge (by simp) (by simp) rfl)⟩
    · rintro ⟨h, -⟩; tauto

/-- `σ` evolves by steps. -/
theorem seq_σ : FrameSeq σ := fun i => by
  rcases i with _ | _ | _ | _ | i
  · exact Or.inr ⟨b₁, step_Φ₀_Φ₁⟩
  · exact Or.inr ⟨c, step_Φ₁_Ψ₂⟩
  · exact Or.inr ⟨d, step_Ψ₂_Ψ₃⟩
  · exact Or.inr ⟨b₁, step_Ψ₃_Ψ₄⟩
  · exact Or.inl rfl

/-- `σ`'s trees lie in `{g, b₁, c, d}`. -/
theorem subset_σ : ∀ i, (σ i).tree ⊆ ({g, b₁, c, d} : Set B1) := fun i => by
  rcases i with _ | _ | _ | _ | i <;> intro z <;> simp [σ, Φ₀, Φ₁, Ψ₂, Ψ₃, Ψ₄] <;> tauto

/-- `{g, b₁, c, d}` is not coherent: `g` and `d` share root `0`. -/
theorem not_coherent_σ : ¬ Coherent ({g, b₁, c, d} : Set B1) := fun h => by
  have hgd : g = d :=
    h.1 (by simp : g ∈ ({g, b₁, c, d} : Set B1)) (by simp : d ∈ ({g, b₁, c, d} : Set B1)) rfl
  simp [g, d] at hgd

/-- (r) The coherence of `U` is needed for `FrameNeverReturns`: `σ` evolves by steps, its first
frame is rooted and its trees lie in `U = {g, b₁, c, d}`; `U` is not coherent, and `b₁`, in the
tree at `1`, is not in the tree at `2` but is in the tree at `4`. -/
theorem frameNeverReturns_needs_coherent :
    FrameSeq σ ∧ (σ 0).Rooted ∧ (∀ i, (σ i).tree ⊆ ({g, b₁, c, d} : Set B1)) ∧
      ¬ Coherent ({g, b₁, c, d} : Set B1) ∧
      1 ≤ 2 ∧ 2 ≤ 4 ∧ b₁ ∈ (σ 1).tree ∧ ¬ (b₁ ∉ (σ 2).tree → b₁ ∉ (σ 4).tree) :=
  ⟨seq_σ, frameOK_Φ₀.rooted, subset_σ, not_coherent_σ, by decide, by decide, by simp [σ, Φ₁],
    fun h => h (by simp [σ, Ψ₂, c, b₁]) (by simp [σ, Ψ₄])⟩

/-- (r) The coherence of `U` is needed for `FrameEntersOnce`: on the same `σ` and `U`, the steps
at `0` and at `3` both add `b₁`. -/
theorem frameEntersOnce_needs_coherent :
    FrameSeq σ ∧ (σ 0).Rooted ∧ (∀ i, (σ i).tree ⊆ ({g, b₁, c, d} : Set B1)) ∧
      ¬ Coherent ({g, b₁, c, d} : Set B1) ∧
      FrameStep (σ 0) b₁ (σ (0 + 1)) ∧ FrameStep (σ 3) b₁ (σ (3 + 1)) ∧ (0 : Nat) ≠ 3 :=
  ⟨seq_σ, frameOK_Φ₀.rooted, subset_σ, not_coherent_σ, step_Φ₀_Φ₁, step_Ψ₃_Ψ₄, by decide⟩

/-- `{g, b₁, y, x}` is coherent. -/
theorem coherent_τ : Coherent ({g, b₁, y, x} : Set B1) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      simp_all [g, b₁, y, x]
  · intro p hp q hq h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      simp_all [g, b₁, y, x]

/-- (r) The rootedness of the first frame is needed for `FrameNeverReturns`: `τ` evolves by steps
and its trees lie in the coherent set `U = {g, b₁, y, x}`; its first frame is not rooted, and
`x`, in the tree at `0`, is not in the tree at `1` but is in the tree at `3`. -/
theorem frameNeverReturns_needs_rooted :
    FrameSeq τ ∧ ¬ (τ 0).Rooted ∧ (∀ i, (τ i).tree ⊆ ({g, b₁, y, x} : Set B1)) ∧
      Coherent ({g, b₁, y, x} : Set B1) ∧
      0 ≤ 1 ∧ 1 ≤ 3 ∧ x ∈ (τ 0).tree ∧ ¬ (x ∉ (τ 1).tree → x ∉ (τ 3).tree) := by
  refine ⟨fun i => ?_, fun h => ?_, fun i => ?_, coherent_τ, by decide, by decide,
    by simp [τ, Τ₀], fun h => h (by simp [τ, Φ₁, g, b₁, x]) (by simp [τ, Τ₃])⟩
  · rcases i with _ | _ | _ | i
    · exact Or.inr ⟨b₁, step_Τ₀_Φ₁⟩
    · exact Or.inr ⟨y, step_Φ₁_Τ₂⟩
    · exact Or.inr ⟨x, step_Τ₂_Τ₃⟩
    · exact Or.inl rfl
  · exact not_anc_g_x (by intro z; simp [τ, Τ₀]; tauto) (h.2 x (by simp [τ, Τ₀]))
  · rcases i with _ | _ | _ | i <;> intro z <;> simp [τ, Τ₀, Φ₁, Τ₂, Τ₃] <;> tauto

end Consensus.Goldilocks.Test.FrameRejection

end
