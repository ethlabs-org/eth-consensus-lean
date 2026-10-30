module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore
@[expose] public section

/-! # Witnesses for the Goldilocks FGStore statements (part 1)

On `Spec/FG/Store`, labelled by kind (CONTRIBUTING "Statements"):

* (a) `init_reachable`: the initial FG state is reachable (the hypothesis of every part-1
  statement).
* (a) `accepts_b₁`: from the initial state the store accepts a block on genesis, so the
  hypotheses of `TreeGrows`, `FinalizedMonotone` and `AcceptIsFrameStep` (a reachable state
  and an accepted block) hold together; the result is reachable. -/

namespace Consensus.Goldilocks.Store.Test

/-- One validator, `Δ = 1`, slot `s` starts at `s`, genesis root `0`, `δ_t = 2`. -/
def P₁ : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  proposer _ := ⟨0, Nat.one_pos⟩
  genesisRoot := 0
  δt := 2

/-- A block on genesis: root `1`, slot `1`, no attestations. -/
def b₁ : NodeBlock P₁ Unit := ⟨1, some 0, 1, ⟨0, Nat.one_pos⟩, [], ()⟩

/-- (a) The initial FG state is reachable. -/
theorem init_reachable : (Store.init (P := P₁) ()).Reachable () := Relation.ReflTransGen.refl

/-- (a) The initial state accepts `b₁`, and the result is reachable. -/
theorem accepts_b₁ :
    ∃ st', (Store.init (P := P₁) ()).onBlock b₁ = some st' ∧ st'.Reachable () := by
  have hg : P₁.genesisBlock () ∈ (Store.init (P := P₁) ()).tree := by
    change (Store.init (P := P₁) ()).blocks (P₁.genesisBlock ()).root = some (P₁.genesisBlock ())
    simp [Store.init, Params.genesisBlock, P₁]
  have hanc : Goldilocks.Anc (insert b₁ (Store.init (P := P₁) ()).tree)
      (Store.init (P := P₁) ()).F b₁ :=
    Relation.ReflTransGen.single ⟨Or.inr hg, Or.inl rfl, rfl⟩
  have hst : ∃ σ', P₁.fg.stateTransition ((Store.init (P := P₁) ()).σ 0) b₁.fgView = some σ' := by
    apply Option.isSome_iff_exists.mp
    simp only [FG.FGParams.stateTransition]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl,
      by simp [Block.fgView, b₁, Store.init, FG.ChainState.init],
      fun a ha => by cases ha⟩)]
    rfl
  obtain ⟨σ', hσ'⟩ := hst
  have hon : ∃ st', (Store.init (P := P₁) ()).onBlock b₁ = some st' := by
    apply Option.isSome_iff_exists.mp
    simp only [onBlock, b₁]
    have hneg : ¬ (((Store.init (P := P₁) ()).blocks 1).isSome = true ∨
        ((Store.init (P := P₁) ()).blocks 0).isNone = true ∨
        ¬ Goldilocks.Anc (insert b₁ (Store.init (P := P₁) ()).tree)
          (Store.init (P := P₁) ()).F b₁) := by
      simp [Store.init, P₁]; exact hanc
    simp only [b₁] at hneg
    simp only [hneg, ↓reduceIte]
    simp only [b₁] at hσ'
    split <;> simp_all
  obtain ⟨st', h⟩ := hon
  exact ⟨st', h, Relation.ReflTransGen.single (Or.inl ⟨b₁, h⟩)⟩

end Consensus.Goldilocks.Store.Test

end
