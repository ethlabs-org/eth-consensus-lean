module
public import ConsensusLeanTest.Goldilocks.FG.Faulty
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
@[expose] public section

/-! # A finalization with a faulty validator in the quorum, under `FinalizedSafety`'s premises

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), at `n = 4` with honest set `{0, 1, 2}`
and faulty validator `3` (`P₄`, `H₄` of `Goldilocks/FG/Faulty`; `q = 3`).

The trace `ffTr` runs the FG of honest validators `0` and `1` (validator `2` is silent). The
faulty validator `3` proposes three blocks `B₁, B₂, B₃` (slots `1, 2, 3`, a chain on genesis),
each carrying the target votes of `0`, `1` and `3` for the current entry: `B₁` justifies genesis
at height `1`, `B₂` justifies `B₁` at height `2`, and `B₃`, whose votes carry the finality pair
`(2, B₁)`, finalizes `B₁`. The honest votes are those that `fg_attest` returns at honest
`attest` cuts; validator `3`'s votes are free. Validator `3` also sends honest validator `0` a
target vote for another root at height `1`.

* `faulty_finalization_localRun`: `ffTr` is an `FGLocalRun` inside `{genesis, B₁, B₂, B₃}`.
* `faulty_finalizes`: honest validator `0` finalizes the non-genesis block `B₁`.
* `finality_quorum_needs_v₃`: the finality bits that finalize `B₁` are exactly `{0, 1, 3}`, and
  the honest signers `{0, 1}` are fewer than `q`; `honest_votes_do_not_finalize`: without
  validator `3`'s vote, `B₃`'s transition finalizes only genesis.
* `faulty_finalizer_equivocates`: validator `3` has a slashable pair (E2) in validator `0`'s pool.
* `faulty_finalization_safety`: `FinalizedSafety`'s conclusion on `ffTr`, with `B₁` finalized.

| cut (= time) | node | label | effect |
|---|---|---|---|
| 0, 1 | 0, 1 | `attest` genesis | sign `vote₁` (height `1`, genesis, no finality pair) |
| 2, 3 | 0, 1 | `block B₁` accepted | `J = genesis`, `h_j = 1` |
| 4, 5 | 0, 1 | `attest B₁` | sign `vote₂` (height `2`, `B₁`, finality pair `(1, genesis)`) |
| 6, 7 | 0, 1 | `block B₂` accepted | `J = B₁`, `h_j = 2` |
| 8, 9 | 0, 1 | `attest B₂` | sign `vote₃` (height `3`, `B₂`, finality pair `(2, B₁)`) |
| 10 | 0 | `block B₃` accepted | `J = B₂`, `h_j = 3`, `F = B₁` |
| 11 | 0 | `attestation equiv₃` | validator `3`'s conflicting height-`1` vote enters the pool |
-/

namespace Consensus.Goldilocks.FaultyFinalizationWitness

open FG
open FaultyWitness (P₄ H₄ H₄_faults v₀ v₃)

/-- Honest validator `1`. -/
def v₁ : Fin P₄.n := ⟨1, by decide⟩

/-- The faulty validator is not honest. -/
theorem v₃_not_mem : v₃ ∉ H₄ := fun h => absurd (show v₃.val < 3 from h) (by decide)

/-- Validator `0` is honest. -/
theorem v₀_mem : v₀ ∈ H₄ := show v₀.val < 3 by decide

/-- Validator `1` is honest. -/
theorem v₁_mem : v₁ ∈ H₄ := show v₁.val < 3 by decide

/-- A target vote of `v` at height `h` for root `T`, with finality pair `f`. -/
def vote (v : Fin P₄.n) (h T : Nat) (f : Option (Nat × Nat)) : Att P₄.n := ⟨v, h, T, false, f⟩

/-- The vote for genesis (root `0`) at height `1`, no finality pair. -/
def vote₁ (v : Fin P₄.n) : Att P₄.n := vote v 1 0 none

/-- The vote for `B₁` (root `1`) at height `2`, finality pair `(1, genesis)`. -/
def vote₂ (v : Fin P₄.n) : Att P₄.n := vote v 2 1 (some (1, 0))

/-- The vote for `B₂` (root `2`) at height `3`, finality pair `(2, B₁)`. -/
def vote₃ (v : Fin P₄.n) : Att P₄.n := vote v 3 2 (some (2, 1))

/-- The faulty validator's conflicting vote for root `5` at height `1`. -/
def equiv₃ : Att P₄.n := vote v₃ 1 5 none

/-- Genesis. -/
abbrev G : NodeBlock P₄ Unit := P₄.genesisBlock ()

/-- The faulty validator's block of slot `1` on genesis, with the height-`1` votes of `0, 1, 3`. -/
def B₁ : NodeBlock P₄ Unit := ⟨1, some 0, 1, v₃, 0, [vote₁ v₀, vote₁ v₁, vote₁ v₃], ()⟩

/-- The faulty validator's block of slot `2` on `B₁`, with the height-`2` votes of `0, 1, 3`. -/
def B₂ : NodeBlock P₄ Unit := ⟨2, some 1, 2, v₃, 0, [vote₂ v₀, vote₂ v₁, vote₂ v₃], ()⟩

/-- The faulty validator's block of slot `3` on `B₂`, with the height-`3` votes of `0, 1, 3`. -/
def B₃ : NodeBlock P₄ Unit := ⟨3, some 2, 3, v₃, 0, [vote₃ v₀, vote₃ v₁, vote₃ v₃], ()⟩

/-- The blocks of the run. -/
def U : Set (NodeBlock P₄ Unit) := {G, B₁, B₂, B₃}

/-- The chain state of `B₁`. -/
def σ₁ : ChainState P₄.n :=
  (P₄.fg.stateTransition (ChainState.init P₄.fg) B₁.fgView).getD (ChainState.init P₄.fg)

/-- The chain state of `B₂`. -/
def σ₂ : ChainState P₄.n := (P₄.fg.stateTransition σ₁ B₂.fgView).getD σ₁

/-- The chain state of `B₃`. -/
def σ₃ : ChainState P₄.n := (P₄.fg.stateTransition σ₂ B₃.fgView).getD σ₂

/-- The initial FG state. -/
abbrev s₀ : Store P₄ Unit := Store.init ()

/-- The FG state after `B₁`: `J = genesis` at `h_j = 1`, `h_max = 2`. -/
def s₁ : Store P₄ Unit :=
  ({ s₀ with blocks := Function.update s₀.blocks 1 (some B₁), σ := Function.update s₀.σ 1 σ₁,
             hmax := 2, J := G, hj := 1 } : Store P₄ Unit).addAtts B₁.fgPayload

/-- The FG state after `B₂`: `J = B₁` at `h_j = 2`, `h_max = 3`. -/
def s₂ : Store P₄ Unit :=
  ({ s₁ with blocks := Function.update s₁.blocks 2 (some B₂), σ := Function.update s₁.σ 2 σ₂,
             hmax := 3, J := B₁, hj := 2 } : Store P₄ Unit).addAtts B₂.fgPayload

/-- The FG state after `B₃`: `J = B₂` at `h_j = 3`, `h_max = 4`, and `F = B₁`. -/
def s₃ : Store P₄ Unit :=
  ({ s₂ with blocks := Function.update s₂.blocks 3 (some B₃), σ := Function.update s₂.σ 3 σ₃,
             hmax := 4, J := B₂, hj := 3, F := B₁ } : Store P₄ Unit).addAtts B₃.fgPayload

/-- Validator `0`'s FG state after processing the conflicting vote `equiv₃`. -/
def s₄ : Store P₄ Unit := s₃.onAttestation equiv₃

/-- The record of validator `v` after signing `vote₁ v`. -/
def rec₁ (v : Fin P₄.n) : Record := Record.empty.recordAtt (vote₁ v)

/-- The record of validator `v` after signing `vote₁ v` and `vote₂ v`. -/
def rec₂ (v : Fin P₄.n) : Record := (rec₁ v).recordAtt (vote₂ v)

/-- The record of validator `v` after signing `vote₁ v`, `vote₂ v` and `vote₃ v`. -/
def rec₃ (v : Fin P₄.n) : Record := (rec₂ v).recordAtt (vote₃ v)

/-! ## The handlers on the concrete states -/

/-- `state_transition` accepts `B₁` on the genesis state. -/
theorem stateTransition_B₁ :
    P₄.fg.stateTransition (s₀.σ 0) B₁.fgView = some σ₁ := rfl

/-- `state_transition` accepts `B₂` on `σ₁`. -/
theorem stateTransition_B₂ : P₄.fg.stateTransition (s₁.σ 1) B₂.fgView = some σ₂ := rfl

/-- `state_transition` accepts `B₃` on `σ₂`. -/
theorem stateTransition_B₃ : P₄.fg.stateTransition (s₂.σ 2) B₃.fgView = some σ₃ := rfl

/-- `fg_attest` of validator `v` with source genesis on the initial state: `vote₁ v`. -/
theorem attest_s₀ (v : Fin P₄.n) : s₀.attest Record.empty v G = some (vote₁ v, rec₁ v) := rfl

/-- `fg_attest` of validator `v` with source `B₁` after `B₁` and `vote₁ v`: `vote₂ v`. -/
theorem attest_s₁ (v : Fin P₄.n) : s₁.attest (rec₁ v) v B₁ = some (vote₂ v, rec₂ v) := rfl

/-- `fg_attest` of validator `v` with source `B₂` after `B₂` and `vote₂ v`: `vote₃ v`. -/
theorem attest_s₂ (v : Fin P₄.n) : s₂.attest (rec₂ v) v B₂ = some (vote₃ v, rec₃ v) := rfl

/-- Processing attestations keeps the blocks. -/
theorem addAtts_blocks (st : Store P₄ Unit) (l : List (Att P₄.n)) :
    (st.addAtts l).blocks = st.blocks := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l
  rw [h]

/-- A block's ancestry inside a set from a parent edge and the ancestry of the parent. -/
theorem anc_tail {S : Set (NodeBlock P₄ Unit)} {X Y Z : NodeBlock P₄ Unit}
    (h : Goldilocks.Anc S X Y) (hY : Y ∈ S) (hZ : Z ∈ S) (hp : Z.parent = some Y.root) :
    Goldilocks.Anc S X Z :=
  Relation.ReflTransGen.tail h ⟨hY, hZ, hp⟩

open Classical in
/-- `fg_on_block` accepts a block whose tests pass, with the post-state that `update_finality`
gives followed by the block's attestations. -/
theorem onBlock_of {st st' : Store P₄ Unit} {B : NodeBlock P₄ Unit} {pr : Nat}
    {σ' : ChainState P₄.n} (hp : B.parent = some pr) (hnew : st.blocks B.root = none)
    (hpr : (st.blocks pr).isSome) (hanc : Goldilocks.Anc (insert B st.tree) st.F B)
    (hσ : P₄.fg.stateTransition (st.σ pr) B.fgView = some σ')
    (hu : Store.updateFinality
      { st with blocks := Function.update st.blocks B.root (some B)
                σ := Function.update st.σ B.root σ' } σ' = st') :
    st.onBlock B = some (st'.addAtts B.fgPayload) := by
  unfold Store.onBlock
  simp only [hp, hnew, Option.isSome_none, Option.isNone_iff_eq_none,
    Option.isSome_iff_ne_none.mp hpr, hanc, Bool.false_eq_true, not_true_eq_false, or_self,
    ↓reduceIte, hσ, hu]

open Classical in
/-- `update_finality` that raises `h_max`, moves `Σ.J` to `X` and keeps `Σ.F`. -/
theorem updateFinality_J (st : Store P₄ Unit) (σ : ChainState P₄.n) {X : NodeBlock P₄ Unit}
    (hX : st.blocks σ.J = some X) (hJ : st.Anc st.F X)
    (hlex : Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) (hF : st.blocks σ.F = some st.F) :
    st.updateFinality σ = { st with hmax := max st.hmax σ.h, J := X, hj := σ.hj } := by
  unfold Store.updateFinality
  dsimp only
  rw [hX]
  dsimp only
  split_ifs with h₁
  · dsimp only
    rw [hF]
    dsimp only
    split_ifs with h₂
    · exact absurd rfl h₂.2.1
    · rfl
  · exact absurd ⟨hJ, hlex⟩ h₁

open Classical in
/-- `update_finality` that raises `h_max`, moves `Σ.J` to `X` and `Σ.F` to `Y`. -/
theorem updateFinality_JF (st : Store P₄ Unit) (σ : ChainState P₄.n) {X Y : NodeBlock P₄ Unit}
    (hX : st.blocks σ.J = some X) (hJ : st.Anc st.F X)
    (hlex : Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) (hY : st.blocks σ.F = some Y)
    (hFY : st.Anc st.F Y) (hne : st.F ≠ Y) (hYX : st.Anc Y X)
    (hv : ({ st with hmax := max st.hmax σ.h, J := X, hj := σ.hj } :
      Store P₄ Unit).HasViableDescendant Y) :
    st.updateFinality σ = { st with hmax := max st.hmax σ.h, J := X, hj := σ.hj, F := Y } := by
  unfold Store.updateFinality
  dsimp only
  rw [hX]
  dsimp only
  split_ifs with h₁
  · dsimp only
    rw [hY]
    dsimp only
    split_ifs with h₂
    · rfl
    · exact absurd ⟨hFY, hne, hYX, hv⟩ h₂
  · exact absurd ⟨hJ, hlex⟩ h₁

/-- A block held under its root is in the tree. -/
theorem mem_tree {st : Store P₄ Unit} {B : NodeBlock P₄ Unit} (h : st.blocks B.root = some B) :
    B ∈ st.tree := h

/-- The head height floor is at most `h_max`. -/
theorem headHeightFloor_le (st : Store P₄ Unit) : st.headHeightFloor ≤ st.hmax := by
  unfold Store.headHeightFloor
  split_ifs <;> omega

/-- The FG state when `B₁` and its chain state are added to `s₀`, before `update_finality`. -/
def u₁ : Store P₄ Unit :=
  { s₀ with blocks := Function.update s₀.blocks B₁.root (some B₁)
            σ := Function.update s₀.σ B₁.root σ₁ }

/-- The FG state when `B₂` and its chain state are added to `s₁`, before `update_finality`. -/
def u₂ : Store P₄ Unit :=
  { s₁ with blocks := Function.update s₁.blocks B₂.root (some B₂)
            σ := Function.update s₁.σ B₂.root σ₂ }

/-- The FG state when `B₃` and its chain state are added to `s₂`, before `update_finality`. -/
def u₃ : Store P₄ Unit :=
  { s₂ with blocks := Function.update s₂.blocks B₃.root (some B₃)
            σ := Function.update s₂.σ B₃.root σ₃ }

/-- The initial FG state accepts `B₁`: `update_finality` moves `Σ.J` to genesis at `h_j = 1`. -/
theorem onBlock_B₁ : s₀.onBlock B₁ = some s₁ := by
  have hu : u₁.updateFinality σ₁ = { u₁ with hmax := max u₁.hmax σ₁.h, J := G, hj := σ₁.hj } :=
    updateFinality_J u₁ σ₁ rfl .refl (Or.inl (by decide)) rfl
  exact onBlock_of (pr := 0) rfl rfl rfl
    (.single ⟨Or.inr (mem_tree rfl), Or.inl rfl, rfl⟩) stateTransition_B₁ hu

/-- `s₁` accepts `B₂`: `update_finality` moves `Σ.J` to `B₁` at `h_j = 2`. -/
theorem onBlock_B₂ : s₁.onBlock B₂ = some s₂ := by
  have hu : u₂.updateFinality σ₂ = { u₂ with hmax := max u₂.hmax σ₂.h, J := B₁, hj := σ₂.hj } :=
    updateFinality_J u₂ σ₂ rfl (.single ⟨mem_tree rfl, mem_tree rfl, rfl⟩)
      (Or.inl (by decide)) rfl
  exact onBlock_of (pr := 1) rfl rfl rfl
    (anc_tail (Y := B₁) (.single ⟨Or.inr (mem_tree rfl), Or.inr (mem_tree rfl), rfl⟩)
      (Or.inr (mem_tree rfl)) (Or.inl rfl) rfl) stateTransition_B₂ hu

/-- `s₂` accepts `B₃`: `update_finality` moves `Σ.J` to `B₂` at `h_j = 3` and `Σ.F` to `B₁`,
which has the viable descendant `B₃`. -/
theorem onBlock_B₃ : s₂.onBlock B₃ = some s₃ := by
  have hG : G ∈ u₃.tree := mem_tree rfl
  have h₁ : B₁ ∈ u₃.tree := mem_tree rfl
  have h₂ : B₂ ∈ u₃.tree := mem_tree rfl
  have hGB₁ : u₃.Anc u₃.F B₁ := .single ⟨hG, h₁, rfl⟩
  have hB₁B₂ : u₃.Anc B₁ B₂ := .single ⟨h₁, h₂, rfl⟩
  have hv : ({ u₃ with hmax := max u₃.hmax σ₃.h, J := B₂, hj := σ₃.hj } :
      Store P₄ Unit).HasViableDescendant B₁ :=
    ⟨B₃, mem_tree rfl, anc_tail hB₁B₂ h₂ (mem_tree rfl) rfl,
      (headHeightFloor_le _).trans (by decide)⟩
  have hu : u₃.updateFinality σ₃ =
      { u₃ with hmax := max u₃.hmax σ₃.h, J := B₂, hj := σ₃.hj, F := B₁ } :=
    updateFinality_JF u₃ σ₃ rfl (hGB₁.tail ⟨h₁, h₂, rfl⟩) (Or.inl (by decide)) rfl hGB₁
      (fun h => absurd (congrArg Block.root h) (by decide)) hB₁B₂ hv
  exact onBlock_of (pr := 2) rfl rfl rfl
    (anc_tail (Y := B₂) (anc_tail (Y := B₁)
      (.single ⟨Or.inr (mem_tree rfl), Or.inr (mem_tree rfl), rfl⟩)
      (Or.inr (mem_tree rfl)) (Or.inr (mem_tree rfl)) rfl) (Or.inr (mem_tree rfl))
      (Or.inl rfl) rfl) stateTransition_B₃ hu

/-! ## The trace -/

/-- The `n = 4` trace (cut `i` at time `i`): honest validators `0` and `1` sign `vote₁` on the
initial state (cuts `0, 1`), accept `B₁` (cuts `2, 3`), sign `vote₂` (cuts `4, 5`), accept `B₂`
(cuts `6, 7`) and sign `vote₃` (cuts `8, 9`); validator `0` accepts `B₃` (cut `10`) and
processes `equiv₃` (cut `11`); then it stutters. -/
def ffTr : FGTrace P₄ Unit where
  init _ := (Store.init (), Record.empty)
  node
    | 1 | 3 | 5 | 7 | 9 => v₁
    | _ => v₀
  time i := i
  event i := i
  pos _ := 0
  label
    | 0 => some (.attest G (some (vote₁ v₀)))
    | 1 => some (.attest G (some (vote₁ v₁)))
    | 2 | 3 => some (.block B₁ true)
    | 4 => some (.attest B₁ (some (vote₂ v₀)))
    | 5 => some (.attest B₁ (some (vote₂ v₁)))
    | 6 | 7 => some (.block B₂ true)
    | 8 => some (.attest B₂ (some (vote₃ v₀)))
    | 9 => some (.attest B₂ (some (vote₃ v₁)))
    | 10 => some (.block B₃ true)
    | 11 => some (.attestation equiv₃)
    | _ => none
  post
    | 0 => (s₀, rec₁ v₀)
    | 1 => (s₀, rec₁ v₁)
    | 2 => (s₁, rec₁ v₀)
    | 3 => (s₁, rec₁ v₁)
    | 4 => (s₁, rec₂ v₀)
    | 5 => (s₁, rec₂ v₁)
    | 6 => (s₂, rec₂ v₀)
    | 7 => (s₂, rec₂ v₁)
    | 8 => (s₂, rec₃ v₀)
    | 9 => (s₂, rec₃ v₁)
    | 10 => (s₃, rec₃ v₀)
    | _ => (s₄, rec₃ v₀)
  awake _ _ := True

/-- The states of validators `0` and `1` before their labelled cuts, and validator `0`'s state
after the last one. -/
theorem ffTr_state :
    ffTr.state v₀ 0 = (s₀, Record.empty) ∧ ffTr.state v₁ 1 = (s₀, Record.empty) ∧
      ffTr.state v₀ 2 = (s₀, rec₁ v₀) ∧ ffTr.state v₁ 3 = (s₀, rec₁ v₁) ∧
      ffTr.state v₀ 4 = (s₁, rec₁ v₀) ∧ ffTr.state v₁ 5 = (s₁, rec₁ v₁) ∧
      ffTr.state v₀ 6 = (s₁, rec₂ v₀) ∧ ffTr.state v₁ 7 = (s₁, rec₂ v₁) ∧
      ffTr.state v₀ 8 = (s₂, rec₂ v₀) ∧ ffTr.state v₁ 9 = (s₂, rec₂ v₁) ∧
      ffTr.state v₀ 10 = (s₂, rec₃ v₀) ∧ ffTr.state v₀ 11 = (s₃, rec₃ v₀) ∧
      ffTr.state v₀ 12 = (s₄, rec₃ v₀) := by
  simp [Trace.state, ffTr, v₀, v₁]

/-- Every block cut of `ffTr` is of a block that the faulty validator proposes. -/
theorem ffTr_block_proposer {i : Nat} {B : NodeBlock P₄ Unit} {acc : Bool}
    (h : ffTr.label i = some (.block B acc)) : B.proposer = v₃ := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp [ffTr] at h <;> obtain ⟨rfl, -⟩ := h <;> rfl

/-- Every FG state of validator `0` or `1` in `ffTr` holds blocks of `U` only. -/
theorem ffTr_tree (y : Fin P₄.n) (i : Nat) : (ffTr.store y i).tree ⊆ U := by
  have h₀ : ∀ B : NodeBlock P₄ Unit, s₀.blocks B.root = some B → B ∈ U := by
    intro B hB
    simp only [Store.init] at hB
    split at hB
    · exact Or.inl (Option.some_inj.mp hB).symm
    · cases hB
  have h₁ : ∀ B : NodeBlock P₄ Unit, s₁.blocks B.root = some B → B ∈ U := by
    intro B hB
    simp only [s₁, addAtts_blocks, Function.update_apply] at hB
    split at hB
    · exact Or.inr (Or.inl (Option.some_inj.mp hB).symm)
    · exact h₀ B hB
  have h₂ : ∀ B : NodeBlock P₄ Unit, s₂.blocks B.root = some B → B ∈ U := by
    intro B hB
    simp only [s₂, addAtts_blocks, Function.update_apply] at hB
    split at hB
    · exact Or.inr (Or.inr (Or.inl (Option.some_inj.mp hB).symm))
    · exact h₁ B hB
  have h₃ : ∀ B : NodeBlock P₄ Unit, s₃.blocks B.root = some B → B ∈ U := by
    intro B hB
    simp only [s₃, addAtts_blocks, Function.update_apply] at hB
    split at hB
    · exact Or.inr (Or.inr (Or.inr (Option.some_inj.mp hB).symm))
    · exact h₂ B hB
  have hpost : ∀ i, ∀ B : NodeBlock P₄ Unit, (ffTr.post i).1.blocks B.root = some B → B ∈ U := by
    intro i B hB
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    · exact h₀ B hB
    · exact h₀ B hB
    · exact h₁ B hB
    · exact h₁ B hB
    · exact h₁ B hB
    · exact h₁ B hB
    · exact h₂ B hB
    · exact h₂ B hB
    · exact h₂ B hB
    · exact h₂ B hB
    · exact h₃ B hB
    · exact h₃ B (by simpa [ffTr, s₄, FaultyWitness.onAttestation_blocks] using hB)
  intro B hB
  change (ffTr.store y i).blocks B.root = some B at hB
  induction i with
  | zero => exact h₀ B hB
  | succ i ih =>
    rw [FGTrace.store, Trace.state] at hB
    split at hB
    · exact hpost i B hB
    · exact ih hB

/-- (a) `ffTr` is an `FGLocalRun` for the honest set `{0, 1, 2}` inside `U`: every honest vote
is what `fg_attest` returns at an earlier `attest` cut of its signer, every block is accepted
by `fg_on_block`, and the faulty validator proposes every block. -/
theorem faulty_finalization_localRun : FGLocalRun () H₄ U ffTr where
  coherent := by
    refine ⟨?_, ?_⟩
    · rintro B (rfl | rfl | rfl | rfl) C (rfl | rfl | rfl | rfl) h <;>
        simp_all [B₁, B₂, B₃, Params.genesisBlock, P₄]
    · rintro B (rfl | rfl | rfl | rfl) C (rfl | rfl | rfl | rfl) h <;>
        simp_all [B₁, B₂, B₃, Params.genesisBlock, P₄]
  init _ _ := rfl
  exec i ℓ h _ := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := ffTr_state
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp only [ffTr, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · change FGLabel.Step v₀ (ffTr.state v₀ 0) _ (s₀, rec₁ v₀)
      rw [h0]; exact ⟨rfl, by rw [attest_s₀]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₁ (ffTr.state v₁ 1) _ (s₀, rec₁ v₁)
      rw [h1]; exact ⟨rfl, by rw [attest_s₀]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 2) _ (s₁, rec₁ v₀)
      rw [h2]; exact Or.inl ⟨rfl, onBlock_B₁, rfl⟩
    · change FGLabel.Step v₁ (ffTr.state v₁ 3) _ (s₁, rec₁ v₁)
      rw [h3]; exact Or.inl ⟨rfl, onBlock_B₁, rfl⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 4) _ (s₁, rec₂ v₀)
      rw [h4]; exact ⟨rfl, by rw [attest_s₁]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₁ (ffTr.state v₁ 5) _ (s₁, rec₂ v₁)
      rw [h5]; exact ⟨rfl, by rw [attest_s₁]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 6) _ (s₂, rec₂ v₀)
      rw [h6]; exact Or.inl ⟨rfl, onBlock_B₂, rfl⟩
    · change FGLabel.Step v₁ (ffTr.state v₁ 7) _ (s₂, rec₂ v₁)
      rw [h7]; exact Or.inl ⟨rfl, onBlock_B₂, rfl⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 8) _ (s₂, rec₃ v₀)
      rw [h8]; exact ⟨rfl, by rw [attest_s₂]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₁ (ffTr.state v₁ 9) _ (s₂, rec₃ v₁)
      rw [h9]; exact ⟨rfl, by rw [attest_s₂]; exact ⟨rfl, rfl⟩⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 10) _ (s₃, rec₃ v₀)
      rw [h10]; exact Or.inl ⟨rfl, onBlock_B₃, rfl⟩
    · change FGLabel.Step v₀ (ffTr.state v₀ 11) _ (s₄, rec₃ v₀)
      rw [h11]; rfl
  tree_subset y _ i := ffTr_tree y i
  time_nonneg i := Int.natCast_nonneg i
  time_mono _ _ h := Int.ofNat_le.mpr h
  attest_public _ _ _ _ _ _ := one_dvd _
  own_first y hy i B h hp := absurd ((ffTr_block_proposer h.2).symm.trans hp ▸ hy) v₃_not_mem
  attest_order y _ j src signed h i ℓ hij hi hti := by
    change (i : Int) = j at hti
    omega
  own_payload y hy i B h hp := absurd ((ffTr_block_proposer h.2).symm.trans hp ▸ hy) v₃_not_mem
  unforgeable y _ i a h ha := by
    obtain ⟨ℓ, hℓ, hp⟩ := h
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [Trace.CallAt, ffTr] at hℓ <;> obtain ⟨-, rfl⟩ := hℓ <;>
      simp only [FGLabel.processed, B₁, B₂, B₃, List.mem_cons, List.not_mem_nil,
        or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;>
      first
        | exact absurd ha v₃_not_mem
        | exact ⟨0, by omega, G, rfl, rfl⟩
        | exact ⟨1, by omega, G, rfl, rfl⟩
        | exact ⟨4, by omega, B₁, rfl, rfl⟩
        | exact ⟨5, by omega, B₁, rfl, rfl⟩
        | exact ⟨8, by omega, B₂, rfl, rfl⟩
        | exact ⟨9, by omega, B₂, rfl, rfl⟩

/-! ## The finalization and the faulty validator's part in it -/

/-- Validator `0`'s FG state from cut `12` on is `s₄`: it has no labelled cut after cut `11`. -/
theorem ffTr_state_tail (k : Nat) : ffTr.state v₀ (12 + k) = (s₄, rec₃ v₀) := by
  induction k with
  | zero => exact ffTr_state.2.2.2.2.2.2.2.2.2.2.2.2
  | succ k ih =>
    rw [← Nat.add_assoc, Trace.state, ih]
    have hl : ffTr.label (12 + k) = none := by
      rw [Nat.add_comm]
      rfl
    simp [hl]

/-- (a) Honest validator `0` finalizes the non-genesis block `B₁`, proposed by the faulty
validator, at cut `10`, and keeps it finalized for the rest of the run. -/
theorem faulty_finalizes :
    v₀ ∈ H₄ ∧ (ffTr.store v₀ 10).F = G ∧ (ffTr.store v₀ 11).F = B₁ ∧
      (∀ i, 11 ≤ i → (ffTr.store v₀ i).F = B₁) ∧ B₁.root ≠ P₄.genesisRoot ∧
      B₁.proposer = v₃ := by
  have h11 : (ffTr.store v₀ 11).F = B₁ := by
    rw [FGTrace.store, ffTr_state.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  refine ⟨v₀_mem, ?_, h11, fun i hi => ?_, by decide, rfl⟩
  · rw [FGTrace.store, ffTr_state.2.2.2.2.2.2.2.2.2.2.1]; rfl
  · obtain rfl | hi := hi.eq_or_lt
    · exact h11
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      rw [FGTrace.store, ffTr_state_tail]
      rfl

/-- (a) The faulty validator's vote is necessary for the finalization. In validator `0`'s FG
state after `B₃`, the chain state of `B₃` finalizes `B₁` (`F = B₁.root`) through the finality
bits at height `2`, set by the votes of `B₃` with finality pair `(2, B₁)`: they are exactly
`{0, 1, 3}`, a quorum (`q = 3`). Without the faulty validator `3`, the honest signers `{0, 1}`
are fewer than `q`. -/
theorem finality_quorum_needs_v₃ :
    ((ffTr.store v₀ 11).σ B₃.root).F = B₁.root ∧ ((ffTr.store v₀ 11).σ B₃.root).hF = 2 ∧
      ((ffTr.store v₀ 11).σ B₃.root).fin 2 = {v₀, v₁, v₃} ∧ P₄.fg.q = 3 ∧
      vote₃ v₃ ∈ B₃.fgPayload ∧ (vote₃ v₃).fin = some (2, B₁.root) ∧ v₃ ∉ H₄ ∧
      (((ffTr.store v₀ 11).σ B₃.root).fin 2).erase v₃ = {v₀, v₁} ∧
      ({v₀, v₁} : Finset (Fin P₄.n)).card < P₄.fg.q := by
  rw [FGTrace.store, ffTr_state.2.2.2.2.2.2.2.2.2.2.2.1]
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, v₃_not_mem, by decide,
    by decide⟩

/-- (a) The counterfactual: `state_transition` of `B₃` on `B₂`'s chain state finalizes `B₁`,
and the same block without the faulty validator's vote finalizes only genesis. -/
theorem honest_votes_do_not_finalize :
    (P₄.fg.stateTransition ((ffTr.store v₀ 10).σ B₂.root) B₃.fgView).map (·.F) =
        some B₁.root ∧
      (P₄.fg.stateTransition ((ffTr.store v₀ 10).σ B₂.root)
        ({ B₃ with fgPayload := B₃.fgPayload.filter (fun a : Att P₄.n => a.val ≠ v₃) } :
          NodeBlock P₄ Unit).fgView).map (·.F) =
        some P₄.genesisRoot := by
  rw [FGTrace.store, ffTr_state.2.2.2.2.2.2.2.2.2.2.1]
  exact ⟨by decide, by decide⟩

/-- (a) The faulty validator equivocates: its vote for genesis at height `1`, counted in `B₁`'s
justification of genesis, and its vote for root `5` at height `1` are slashable (E2), and both
are in honest validator `0`'s pool after cut `11`. -/
theorem faulty_finalizer_equivocates :
    v₀ ∈ H₄ ∧ v₃ ∉ H₄ ∧ (vote₁ v₃).val = v₃ ∧ equiv₃.val = v₃ ∧
      e2 (vote₁ v₃) equiv₃ ∧ slashable (vote₁ v₃) equiv₃ ∧ vote₁ v₃ ∈ B₁.fgPayload ∧
      vote₁ v₃ ∈ (ffTr.store v₀ 12).atts ∧ equiv₃ ∈ (ffTr.store v₀ 12).atts := by
  rw [FGTrace.store, ffTr_state.2.2.2.2.2.2.2.2.2.2.2.2]
  exact ⟨v₀_mem, v₃_not_mem, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- `FinalizedSafety`'s conclusion on `ffTr`: the finalized tips of any two honest nodes at any
two cuts are compatible, while validator `0` has finalized `B₁`; so every honest finalized tip
is compatible with `B₁`. -/
theorem faulty_finalization_safety :
    (ffTr.store v₀ 11).F = B₁ ∧
      (∀ y ∈ H₄, ∀ z ∈ H₄, ∀ i j, Compatible U (ffTr.store y i).F (ffTr.store z j).F) ∧
      ∀ z ∈ H₄, ∀ j, Compatible U B₁ (ffTr.store z j).F := by
  have hs := Store.finalized_safety (P := P₄) (ACP := Unit) () H₄ U ffTr
    faulty_finalization_localRun H₄_faults
  refine ⟨faulty_finalizes.2.2.1, hs, fun z hz j => ?_⟩
  rw [← faulty_finalizes.2.2.1]
  exact hs v₀ v₀_mem z hz 11 j

end Consensus.Goldilocks.FaultyFinalizationWitness

end
