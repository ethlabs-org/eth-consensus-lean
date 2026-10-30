module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace
@[expose] public section

/-! # Witnesses for the Goldilocks FGStore statements (part 1)

On `Spec/FG/Store`, labelled by kind (CONTRIBUTING "Statements"):

* (a) `init_reachable`: the initial FG state is reachable (the hypothesis of every part-1
  statement).
* (a) `accepts_b₁`: from the initial state the store accepts a block on genesis, so the
  hypotheses of `TreeGrows`, `FinalizedMonotone` and `AcceptIsFrameStep` (a reachable state
  and an accepted block) hold together; the result is reachable.
* (a) `idle_localRun`: an FG trace with no FG call is an `FGLocalRun` for one honest validator
  (the trace hypothesis of `FinalizedSafety` and `QuorumFreeEntries` is satisfiable). -/

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

/-- An FG trace in which no FG call happens: every cut is a stutter at time `0`. -/
noncomputable def idleTrace : FGTrace P₁ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node _ := ⟨0, Nat.one_pos⟩
  time _ := 0
  event _ := 0
  pos _ := 0
  label _ := none
  post _ := (Store.init (), FG.Record.empty)
  awake _ _ := True

/-- Every state of the idle trace is the initial one. -/
theorem idleTrace_state (y : Fin P₁.n) (i : Nat) :
    idleTrace.state y i = (Store.init (), FG.Record.empty) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Trace.state]
    simp only [idleTrace, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    exact ih

/-- (a) The idle trace is an `FGLocalRun` for the honest set `{0}` inside `{genesis}`. -/
theorem idle_localRun :
    FGLocalRun () {⟨0, Nat.one_pos⟩} {P₁.genesisBlock ()} idleTrace where
  coherent := ⟨Set.injOn_singleton _ _, fun B hB C hC h => by
    simp only [Set.mem_singleton_iff] at hB hC; subst hB; subst hC
    simp [Params.genesisBlock] at h⟩
  init _ _ := rfl
  exec i ℓ h := by simp [idleTrace] at h
  tree_subset y _ i := by
    intro B hB
    rw [FGTrace.store, idleTrace_state] at hB
    change (Store.init (P := P₁) ()).blocks B.root = some B at hB
    simp only [Store.init] at hB
    split at hB
    · exact Set.mem_singleton_iff.mpr (Option.some_inj.mp hB).symm
    · exact absurd hB (by simp)
  time_nonneg _ := le_rfl
  time_mono _ _ _ := le_rfl
  attest_public y _ i src signed h := by simp [Trace.CallAt, idleTrace] at h
  own_first y _ i B h := by simp [Trace.CallAt, idleTrace] at h
  attest_order y _ j src signed h := by simp [Trace.CallAt, idleTrace] at h
  own_payload y _ i B h := by simp [Trace.CallAt, idleTrace] at h
  unforgeable y _ i a h := by
    obtain ⟨ℓ, hℓ, -⟩ := h; simp [Trace.CallAt, idleTrace] at hℓ

end Consensus.Goldilocks.Store.Test

end
