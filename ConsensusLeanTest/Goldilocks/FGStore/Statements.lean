module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
@[expose] public section

/-! # Witnesses for the Goldilocks FGStore statements (part 1)

On `Spec/FG/Store`, labelled by kind (CONTRIBUTING "Statements"):

* (a) `init_reachable`: the initial FG state is reachable (the hypothesis of every part-1
  statement).
* (a) `accepts_b₁`: from the initial state the store accepts a block on genesis, so the
  hypotheses of `TreeGrows`, `FinalizedMonotone` and `AcceptIsFrameStep` (a reachable state
  and an accepted block) hold together; the result is reachable.
* (a) `idle_localRun`: an FG trace with no FG call is an `FGLocalRun` for one honest validator
  (the trace hypothesis of `FinalizedSafety` and `QuorumFreeEntries` is satisfiable).
* (a) `relay_localRun`: an n = 2 FG trace with labelled cuts is an `FGLocalRun`, so the laws are
  exercised: validator `0` accepts its own proposal, signs in `attest` and processes its own
  attestation; validator `1` accepts the relayed proposal; the copy relayed back to validator `0`
  is refused as a duplicate (an FG cut after the own acceptance at the same time). -/

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
  genesisRoot := 0
  δt := 2

/-- A block on genesis: root `1`, slot `1`, no attestations. -/
def b₁ : NodeBlock P₁ Unit := ⟨1, some 0, 1, ⟨0, Nat.one_pos⟩, 0, [], ()⟩

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
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨
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

/-- Two validators, `Δ = 1`, slot `s` starts at `s`, validator `0` proposes every slot, genesis
root `0`, `δ_t = 2`. -/
def P₂ : Params where
  n := 2
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 2

/-- Validator `0` of `P₂`. -/
def v₀ : Fin P₂.n := ⟨0, Nat.two_pos⟩

/-- Validator `1` of `P₂`. -/
def v₁ : Fin P₂.n := ⟨1, Nat.one_lt_two⟩

/-- The two validators of `P₂` differ. -/
theorem v₀_ne_v₁ : v₀ ≠ v₁ := by decide

/-- Validator `0`'s proposal of slot `1` on genesis: root `1`, no attestations. -/
def B₂ : NodeBlock P₂ Unit := ⟨1, some 0, 1, v₀, 0, [], ()⟩

/-- The chain state of `B₂`: the initial one at slot `1` with latest block `B₂` (no quorum, so
no height event). -/
def σB₂ : FG.ChainState P₂.fg.n := { FG.ChainState.init P₂.fg with s := 1, L := 1 }

/-- The FG state after accepting `B₂` on the initial state: `B₂` and its chain state added. -/
def stB₂ : Store P₂ Unit :=
  { Store.init () with
    blocks := Function.update (Store.init (P := P₂) ()).blocks 1 (some B₂)
    σ := Function.update (Store.init (P := P₂) ()).σ 1 σB₂ }

/-- Validator `0`'s attestation with source `B₂`: the target vote for genesis at height `1`, no
finality pair. -/
def a₂ : FG.Att P₂.n := ⟨v₀, 1, 0, false, none⟩

/-- Validator `0`'s record after signing `a₂`. -/
def Λ₂ : FG.Record := FG.Record.empty.recordAtt a₂

/-- `state_transition` of `B₂` from the genesis state gives `σB₂`. -/
theorem stateTransition_B₂ :
    P₂.fg.stateTransition ((Store.init (P := P₂) ()).σ 0) B₂.fgView = some σB₂ := rfl

/-- The initial FG state accepts `B₂`, with post-state `stB₂`. -/
theorem onBlock_init_B₂ : (Store.init (P := P₂) ()).onBlock B₂ = some stB₂ := by
  have hg : P₂.genesisBlock () ∈ (Store.init (P := P₂) ()).tree := by
    change (Store.init (P := P₂) ()).blocks (P₂.genesisBlock ()).root = some (P₂.genesisBlock ())
    simp [Store.init, Params.genesisBlock, P₂]
  have hanc : Goldilocks.Anc (insert B₂ (Store.init (P := P₂) ()).tree)
      (Store.init (P := P₂) ()).F B₂ :=
    Relation.ReflTransGen.single ⟨Or.inr hg, Or.inl rfl, rfl⟩
  have hneg : ¬ (((Store.init (P := P₂) ()).blocks B₂.root).isSome = true ∨
      ((Store.init (P := P₂) ()).blocks 0).isNone = true ∨
      ¬ Goldilocks.Anc (insert B₂ (Store.init (P := P₂) ()).tree)
        (Store.init (P := P₂) ()).F B₂) := by
    rintro (h | h | h)
    · simp [Store.init, B₂, P₂] at h
    · simp [Store.init, P₂] at h
    · exact h hanc
  unfold onBlock
  split
  · next h => cases h
  next pr h =>
  cases h
  simp only [hneg, ↓reduceIte]
  split
  · next h => rw [stateTransition_B₂] at h; cases h
  next σ' h =>
  rw [stateTransition_B₂] at h; cases h
  change some ((updateFinality stB₂ σB₂).addAtts []) = some stB₂
  have hJ : stB₂.blocks (@FG.ChainState.J P₂.n σB₂) = some (P₂.genesisBlock ()) := rfl
  have hF : stB₂.blocks (@FG.ChainState.F P₂.n σB₂) = some (P₂.genesisBlock ()) := rfl
  have hlex : ¬ LexLt (stB₂.hj, stB₂.J.root)
      (@FG.ChainState.hj P₂.n σB₂, @FG.ChainState.J P₂.n σB₂) := by
    simp [LexLt, stB₂, Store.init, σB₂, FG.ChainState.init, Params.genesisBlock, Params.fg, P₂]
  simp only [updateFinality]
  simp only [hJ, hlex, and_false, ↓reduceIte]
  simp only [hF]
  split
  · next h => exact absurd (by split <;> (try split) <;> rfl) h.2.1
  · rfl

/-- Validator `0` signs `a₂` with source `B₂` on `stB₂` and the empty record. -/
theorem attest_stB₂ : stB₂.attest FG.Record.empty v₀ B₂ = some (a₂, Λ₂) := rfl

/-- The FG state of validator `0` after accepting `B₂` and processing its own `a₂`. -/
def stBa₂ : Store P₂ Unit := stB₂.onAttestation a₂

/-- `stBa₂` refuses the relayed copy of `B₂`: its root is held. -/
theorem onBlock_stBa₂_B₂ : stBa₂.onBlock B₂ = none := by
  have hheld : (stBa₂.blocks B₂.root).isSome = true := rfl
  unfold onBlock
  split
  · rfl
  · simp only [hheld, true_or, ↓reduceIte]

/-- The n = 2 trace at time `1`: validator `0` accepts its own proposal `B₂` (cut `0`), attests
with source `B₂` and signs `a₂` (cut `1`), processes `a₂` (cut `2`); validator `1` accepts the
relayed `B₂` (cut `3`); validator `0` refuses the copy relayed back (cut `4`); then stutters. -/
def tr₂ : FGTrace P₂ Unit where
  init _ := (Store.init (), FG.Record.empty)
  node i := if i = 3 then v₁ else v₀
  time _ := 1
  event
    | 0 | 1 | 2 => 0
    | 3 => 1
    | _ => 2
  pos
    | 1 => 1
    | 2 => 2
    | _ => 0
  label
    | 0 => some (.block B₂ true)
    | 1 => some (.attest B₂ (some a₂))
    | 2 => some (.attestation a₂)
    | 3 => some (.block B₂ true)
    | 4 => some (.block B₂ false)
    | _ => none
  post
    | 0 => (stB₂, FG.Record.empty)
    | 1 => (stB₂, Λ₂)
    | 3 => (stB₂, FG.Record.empty)
    | _ => (stBa₂, Λ₂)
  awake _ _ := True

/-- The states of `tr₂` before the labelled cuts of their node. -/
theorem tr₂_state :
    tr₂.state v₀ 1 = (stB₂, FG.Record.empty) ∧ tr₂.state v₀ 2 = (stB₂, Λ₂) ∧
      tr₂.state v₀ 4 = (stBa₂, Λ₂) ∧ tr₂.state v₁ 3 = (Store.init (), FG.Record.empty) := by
  simp [Trace.state, tr₂, v₀_ne_v₁, v₀_ne_v₁.symm]

/-- Every post-state of `tr₂` holds the blocks of `stB₂`. -/
theorem tr₂_post_blocks (i : Nat) : (tr₂.post i).1.blocks = stB₂.blocks := by
  rcases i with _ | _ | _ | _ | i <;> rfl

/-- Every FG state of `tr₂` holds the blocks of the initial state or those of `stB₂`. -/
theorem tr₂_state_blocks (y : Fin P₂.n) (i : Nat) :
    (tr₂.store y i).blocks = (Store.init ()).blocks ∨ (tr₂.store y i).blocks = stB₂.blocks := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [FGTrace.store, Trace.state]
    split
    · exact Or.inr (tr₂_post_blocks i)
    · exact ih

/-- (a) `tr₂` is an `FGLocalRun` for the honest set `{0, 1}` inside `{genesis, B₂}`: an own
proposal accepted first, an `attest` call that signs after it, the own attestation processed,
the proposal relayed to validator `1`, and the copy relayed back refused as a duplicate. -/
theorem relay_localRun :
    FGLocalRun () {v₀, v₁} {P₂.genesisBlock (), B₂} tr₂ where
  coherent := by
    refine ⟨?_, ?_⟩
    · rintro B (rfl | rfl) C (rfl | rfl) h <;> simp_all [B₂, Params.genesisBlock, P₂]
    · rintro B (rfl | rfl) C (rfl | rfl) h <;> simp_all [B₂, Params.genesisBlock, P₂]
  init _ _ := rfl
  exec i ℓ h _ := by
    obtain ⟨h1, h2, h4, h3⟩ := tr₂_state
    rcases i with _ | _ | _ | _ | _ | i <;> simp only [tr₂, Option.some.injEq,
      reduceCtorEq] at h <;> subst h
    · exact Or.inl ⟨rfl, onBlock_init_B₂, rfl⟩
    · change FGLabel.Step v₀ (tr₂.state v₀ 1) _ (stB₂, Λ₂)
      rw [h1]
      exact ⟨rfl, by rw [attest_stB₂]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₀ (tr₂.state v₀ 2) _ (stBa₂, Λ₂)
      rw [h2]
      rfl
    · change FGLabel.Step v₁ (tr₂.state v₁ 3) _ (stB₂, FG.Record.empty)
      rw [h3]
      exact Or.inl ⟨rfl, onBlock_init_B₂, rfl⟩
    · change FGLabel.Step v₀ (tr₂.state v₀ 4) _ (stBa₂, Λ₂)
      rw [h4]
      exact Or.inr ⟨rfl, onBlock_stBa₂_B₂, rfl⟩
  tree_subset y _ i := by
    intro B hB
    change (tr₂.store y i).blocks B.root = some B at hB
    rcases tr₂_state_blocks y i with h | h <;> rw [h] at hB
    · simp only [Store.init] at hB
      split at hB
      · exact Or.inl (Option.some_inj.mp hB).symm
      · cases hB
    · by_cases h1 : B.root = 1
      · simp only [stB₂, h1, Function.update_self, Option.some.injEq] at hB
        exact Or.inr hB.symm
      · simp only [stB₂, ne_eq, h1, not_false_eq_true, Function.update_of_ne, Store.init] at hB
        split at hB
        · exact Or.inl (Option.some_inj.mp hB).symm
        · cases hB
  time_nonneg _ := zero_le_one
  time_mono _ _ _ := le_rfl
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y _ i B h hp _ k hk ℓ hk' := by
    rcases i with _ | _ | _ | _ | _ | i <;>
      dsimp only [Trace.CallAt, tr₂] at h <;>
      simp only [Option.some.injEq, FGLabel.block.injEq, reduceCtorEq, and_true, and_false] at h
    · omega
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hp v₀_ne_v₁
  attest_order y _ j src signed h i ℓ hij hi _ := by
    rcases j with _ | _ | _ | _ | _ | j <;>
      dsimp only [Trace.CallAt, tr₂] at h <;>
      simp only [Option.some.injEq, FGLabel.attest.injEq, reduceCtorEq, and_false] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain rfl : i = 0 := by omega
    simp only [Trace.CallAt, tr₂, Option.some.injEq] at hi
    exact ⟨B₂, true, hi.2.symm, rfl, rfl⟩
  own_payload y _ i B h _ _ a ha := by
    rcases i with _ | _ | _ | _ | _ | i <;>
      dsimp only [Trace.CallAt, tr₂] at h <;>
      simp only [Option.some.injEq, FGLabel.block.injEq, reduceCtorEq, and_true, and_false] at h
    all_goals (obtain ⟨-, rfl⟩ := h; simp [B₂] at ha)
  unforgeable y _ i a h _ := by
    obtain ⟨ℓ, hℓ, ha⟩ := h
    rcases i with _ | _ | _ | _ | _ | i <;>
      dsimp only [Trace.CallAt, tr₂] at hℓ <;>
      simp only [Option.some.injEq, reduceCtorEq, and_false] at hℓ <;>
      obtain ⟨-, rfl⟩ := hℓ <;> simp [FGLabel.processed, B₂] at ha
    subst ha
    exact ⟨1, by omega, B₂, rfl, rfl⟩

end Consensus.Goldilocks.Store.Test

end
