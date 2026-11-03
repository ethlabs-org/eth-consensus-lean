module
public import ConsensusLean
@[expose] public section

/-! # Two conflicting finalizing chains, at the FG store of the Goldilocks node

The FG-store half of `GoldilocksConflictRun` (the run-level rejection of `FinalizedSafe` without
its fault bound). Six validators (`n = 6`, `q = 4`, `2q − n = 2`), `Δ = 2`, `t_s = 8s`,
`k = c = 2`, genesis root `0`. Validator `0` proposes two chains on genesis, each of three
blocks with an empty AC payload:

* chain A (`c = true`), roots `1, 2, 3`; chain B (`c = false`), roots `11, 12, 13`;
* block `i` of a chain (slot `i`) carries the target votes of validators `0, 1, 2, 3` (all faulty
  in the run) for its parent at height `i`, with the finality pair `(i − 1, ·)` of the block
  below the parent from height `2` on (the chain shape of `GoldilocksAccountableTightness`).

From the initial store, `fg_on_block` accepts the three blocks of either chain in order
(`onBlock₁`, `onBlock₂`, `onBlock₃`) and the third finalizes the first (`F_s₃`); the store-level
step lemmas are those of `GoldilocksFaultyFinalizationWitness`, stated for any parameters. The
block digest `dg6` maps each of the six block contents to its root and every other content
(genesis's included) to `0`: it is injective on the seven blocks (`dg6_blk`), the two first
blocks being told apart by their input. -/

namespace Consensus.Goldilocks.ConflictRun


open FG

/-- Six validators, `Δ = 2`, `t_s = 8s`, genesis root `0`, `δt = 2`. -/
abbrev P6 : Params where
  n := 6
  hn := by decide
  Δ := 2
  hΔ := by decide
  slotTime := fun s => 8 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 8 * (a : Int) < 8 * (b : Int); omega
  slotTime_public := fun s => ⟨4 * (s : Int), by ring⟩
  genesisRoot := 0
  δt := 2

/-- The SA parameters: `P6` with `k = c = 2`. -/
abbrev sp6 : SA.SAParams where
  toParams := P6
  slotTime_eq := fun s => by change 8 * (s : Int) = 4 * 2 * s; ring
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

/-- A replay order for restarts. -/
noncomputable abbrev ro6 : SA.ReplayOrder sp6 (List (Att sp6.n)) := SA.ReplayOrder.choice sp6

/-- The node's AC. -/
noncomputable abbrev Nd : NodeAC P6 := goldilocksNode sp6 ro6

/-- The blocks of the node. -/
abbrev Blk : Type := NodeBlock P6 (SA.Payload 6)

/-- The proposer of every slot, faulty validator `0`. -/
abbrev v0 : Fin 6 := 0

/-- The quorum signers, all faulty in the run. -/
def signers : List (Fin 6) := [0, 1, 2, 3]

/-- The target votes of the signers at height `h` for root `T`, with finality pair `f`. -/
def tvs (h T : Nat) (f : Option (Nat × Nat)) : List (Att 6) :=
  signers.map fun v => ⟨v, h, T, false, f⟩

/-- The roots of a chain: `1, 2, 3` for chain A, `11, 12, 13` for chain B. -/
def rt (c : Bool) (i : Nat) : Nat := if c then i else 10 + i

/-- The FG payload of block `i` of chain `c`. -/
def atts (c : Bool) : Nat → List (Att 6)
  | 1 => tvs 1 0 none
  | 2 => tvs 2 (rt c 1) (some (1, 0))
  | _ => tvs 3 (rt c 2) (some (2, rt c 1))

/-- The parent root of block `i` of chain `c`. -/
def par (c : Bool) (i : Nat) : Nat := if i = 1 then 0 else rt c (i - 1)

/-- The input of chain `c`'s blocks: `0` for chain A, `1` for chain B (the first blocks of the
two chains differ only there; no handler reads it). -/
def inp (c : Bool) : Nat := if c then 0 else 1

/-- Block `i` of chain `c`: slot `i`, proposer `0`, empty AC payload. -/
def blk (c : Bool) (i : Nat) : Blk := ⟨rt c i, some (par c i), i, v0, inp c, atts c i, ([], [])⟩

/-- Genesis. -/
abbrev G : Blk := P6.genesisBlock ([], [])

theorem G_eq_genesis : G = P6.genesisBlock Nd.genesisPayload := rfl

/-- The chain whose blocks carry input `x`. -/
def chainOf (x : Nat) : Bool := x == 0

theorem chainOf_inp (c : Bool) : chainOf (inp c) = c := by cases c <;> rfl

open Classical in
/-- The digest: each block content of the two chains to its root, everything else to `0`. -/
noncomputable def dg6 : Digest (List (Att 6)) (SA.Payload 6) := fun pr s x a p =>
  if s ∈ [1, 2, 3] ∧ (pr, s, x, a, p) =
      (some (par (chainOf x) s), s, inp (chainOf x), atts (chainOf x) s, (([], []) : SA.Payload 6))
  then rt (chainOf x) s else 0

theorem dg6_blk (c : Bool) {i : Nat} (hi : i ∈ [1, 2, 3]) :
    dg6 (some (par c i)) i (inp c) (atts c i) ([], []) = rt c i := by
  simp only [dg6, chainOf_inp, and_true, hi, ↓reduceIte]

theorem dg6_none (s x : Nat) (a : List (Att 6)) (p : SA.Payload 6) : dg6 none s x a p = 0 := by
  simp [dg6]

theorem blk_rootOk (c : Bool) {i : Nat} (hi : i ∈ [1, 2, 3]) : (blk c i).RootOk dg6 :=
  (dg6_blk c hi).symm

/-! ## Store-level steps (as in `GoldilocksFaultyFinalizationWitness`, any parameters) -/

section Steps

variable {P : Params} {ACP : Type}

theorem addAtts_blocks (st : Store P ACP) (l : List (Att P.n)) :
    (st.addAtts l).blocks = st.blocks := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l
  rw [h]

theorem addAtts_F (st : Store P ACP) (l : List (Att P.n)) : (st.addAtts l).F = st.F := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l
  rw [h]

theorem anc_tail {S : Set (NodeBlock P ACP)} {X Y Z : NodeBlock P ACP}
    (h : Goldilocks.Anc S X Y) (hY : Y ∈ S) (hZ : Z ∈ S) (hp : Z.parent = some Y.root) :
    Goldilocks.Anc S X Z :=
  Relation.ReflTransGen.tail h ⟨hY, hZ, hp⟩

open Classical in
theorem onBlock_of {st st' : Store P ACP} {B : NodeBlock P ACP} {pr : Nat}
    {σ' : ChainState P.n} (hp : B.parent = some pr) (hnew : st.blocks B.root = none)
    (hpr : (st.blocks pr).isSome) (hanc : Goldilocks.Anc (insert B st.tree) st.F B)
    (hσ : P.fg.stateTransition (st.σ pr) B.fgView = some σ')
    (hu : Store.updateFinality
      { st with blocks := Function.update st.blocks B.root (some B)
                σ := Function.update st.σ B.root σ' } σ' = st') :
    st.onBlock B = some (st'.addAtts B.fgPayload) := by
  unfold Store.onBlock
  simp only [hp, hnew, Option.isSome_none, Option.isNone_iff_eq_none,
    Option.isSome_iff_ne_none.mp hpr, hanc, Bool.false_eq_true, not_true_eq_false, or_self,
    ↓reduceIte, hσ, hu]

open Classical in
theorem updateFinality_J (st : Store P ACP) (σ : ChainState P.n) {X : NodeBlock P ACP}
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
theorem updateFinality_JF (st : Store P ACP) (σ : ChainState P.n) {X Y : NodeBlock P ACP}
    (hX : st.blocks σ.J = some X) (hJ : st.Anc st.F X)
    (hlex : Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) (hY : st.blocks σ.F = some Y)
    (hFY : st.Anc st.F Y) (hne : st.F ≠ Y) (hYX : st.Anc Y X)
    (hv : ({ st with hmax := max st.hmax σ.h, J := X, hj := σ.hj } :
      Store P ACP).HasViableDescendant Y) :
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

theorem mem_tree {st : Store P ACP} {B : NodeBlock P ACP} (h : st.blocks B.root = some B) :
    B ∈ st.tree := h

theorem headHeightFloor_le (st : Store P ACP) : st.headHeightFloor ≤ st.hmax := by
  unfold Store.headHeightFloor
  split_ifs <;> omega

end Steps

/-! ## The stores of one chain -/

/-- The chain state of block `1` of chain `c`. -/
def σ₁ (c : Bool) : ChainState 6 :=
  (P6.fg.stateTransition (ChainState.init P6.fg) (blk c 1).fgView).getD (ChainState.init P6.fg)

/-- The chain state of block `2`. -/
def σ₂ (c : Bool) : ChainState 6 := (P6.fg.stateTransition (σ₁ c) (blk c 2).fgView).getD (σ₁ c)

/-- The chain state of block `3`. -/
def σ₃ (c : Bool) : ChainState 6 := (P6.fg.stateTransition (σ₂ c) (blk c 3).fgView).getD (σ₂ c)

/-- The initial FG store. -/
abbrev s₀ : Store P6 (SA.Payload 6) := Store.init ([], [])

/-- `s₀` with block `1` and its chain state, before `update_finality`. -/
def u₁ (c : Bool) : Store P6 (SA.Payload 6) :=
  { s₀ with blocks := Function.update s₀.blocks (blk c 1).root (some (blk c 1))
            σ := Function.update s₀.σ (blk c 1).root (σ₁ c) }

/-- The store after block `1`: `J = genesis` at `h_j = 1`. -/
def s₁ (c : Bool) : Store P6 (SA.Payload 6) :=
  ({ u₁ c with hmax := max (u₁ c).hmax (σ₁ c).h, J := G, hj := (σ₁ c).hj } :
    Store P6 (SA.Payload 6)).addAtts (blk c 1).fgPayload

/-- `s₁` with block `2`, before `update_finality`. -/
def u₂ (c : Bool) : Store P6 (SA.Payload 6) :=
  { s₁ c with blocks := Function.update (s₁ c).blocks (blk c 2).root (some (blk c 2))
              σ := Function.update (s₁ c).σ (blk c 2).root (σ₂ c) }

/-- The store after block `2`: `J` = block `1` at `h_j = 2`. -/
def s₂ (c : Bool) : Store P6 (SA.Payload 6) :=
  ({ u₂ c with hmax := max (u₂ c).hmax (σ₂ c).h, J := blk c 1, hj := (σ₂ c).hj } :
    Store P6 (SA.Payload 6)).addAtts (blk c 2).fgPayload

/-- `s₂` with block `3`, before `update_finality`. -/
def u₃ (c : Bool) : Store P6 (SA.Payload 6) :=
  { s₂ c with blocks := Function.update (s₂ c).blocks (blk c 3).root (some (blk c 3))
              σ := Function.update (s₂ c).σ (blk c 3).root (σ₃ c) }

/-- The store after block `3`: `J` = block `2` at `h_j = 3`, and `F` = block `1`. -/
def s₃ (c : Bool) : Store P6 (SA.Payload 6) :=
  ({ u₃ c with hmax := max (u₃ c).hmax (σ₃ c).h, J := blk c 2, hj := (σ₃ c).hj, F := blk c 1 } :
    Store P6 (SA.Payload 6)).addAtts (blk c 3).fgPayload

attribute [irreducible] s₁ s₂ s₃

/-! Field projections: `addAtts` changes only the pool. -/

section Fields

variable {P : Params} {ACP : Type} (st : Store P ACP) (l : List (Att P.n))

theorem addAtts_σ : (st.addAtts l).σ = st.σ := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l; rw [h]
theorem addAtts_J : (st.addAtts l).J = st.J := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l; rw [h]
theorem addAtts_hj : (st.addAtts l).hj = st.hj := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l; rw [h]
theorem addAtts_hmax : (st.addAtts l).hmax = st.hmax := by
  obtain ⟨atts, h⟩ := st.addAtts_eq l; rw [h]

end Fields

@[simp] theorem s₀_blocks (r : Nat) : s₀.blocks r = if r = 0 then some G else none := rfl

@[simp] theorem s₀_F : s₀.F = G := rfl

@[simp] theorem G_root : G.root = 0 := rfl

theorem s₁_blocks (c : Bool) :
    (s₁ c).blocks = Function.update s₀.blocks (rt c 1) (some (blk c 1)) := by
  rw [s₁, addAtts_blocks]; rfl
theorem s₁_σ (c : Bool) : (s₁ c).σ = Function.update s₀.σ (rt c 1) (σ₁ c) := by
  rw [s₁, addAtts_σ]; rfl
theorem s₁_F (c : Bool) : (s₁ c).F = G := by rw [s₁, addAtts_F]; rfl
theorem s₁_J (c : Bool) : (s₁ c).J = G := by rw [s₁, addAtts_J]
theorem s₁_hj (c : Bool) : (s₁ c).hj = (σ₁ c).hj := by rw [s₁, addAtts_hj]
theorem s₁_hmax (c : Bool) : (s₁ c).hmax = max 1 (σ₁ c).h := by rw [s₁, addAtts_hmax]; rfl

theorem s₂_blocks (c : Bool) :
    (s₂ c).blocks = Function.update (s₁ c).blocks (rt c 2) (some (blk c 2)) := by
  rw [s₂, addAtts_blocks]; rfl
theorem s₂_σ (c : Bool) : (s₂ c).σ = Function.update (s₁ c).σ (rt c 2) (σ₂ c) := by
  rw [s₂, addAtts_σ]; rfl
theorem s₂_F (c : Bool) : (s₂ c).F = G := by rw [s₂, addAtts_F]; exact s₁_F c
theorem s₂_J (c : Bool) : (s₂ c).J = blk c 1 := by rw [s₂, addAtts_J]
theorem s₂_hj (c : Bool) : (s₂ c).hj = (σ₂ c).hj := by rw [s₂, addAtts_hj]
theorem s₂_hmax (c : Bool) : (s₂ c).hmax = max (max 1 (σ₁ c).h) (σ₂ c).h := by
  rw [s₂, addAtts_hmax]; exact congrArg (max · _) (s₁_hmax c)

theorem s₃_blocks (c : Bool) :
    (s₃ c).blocks = Function.update (s₂ c).blocks (rt c 3) (some (blk c 3)) := by
  rw [s₃, addAtts_blocks]; rfl

/-- The chain-state numbers the finality updates read. -/
theorem σ_numbers (c : Bool) :
    Store.LexLt (0, 0) ((σ₁ c).hj, (σ₁ c).J) ∧ (σ₁ c).J = 0 ∧ (σ₁ c).F = 0 ∧
    Store.LexLt ((σ₁ c).hj, 0) ((σ₂ c).hj, (σ₂ c).J) ∧ (σ₂ c).J = rt c 1 ∧ (σ₂ c).F = 0 ∧
    Store.LexLt ((σ₂ c).hj, rt c 1) ((σ₃ c).hj, (σ₃ c).J) ∧ (σ₃ c).J = rt c 2 ∧
      (σ₃ c).F = rt c 1 ∧ max (max (max 1 (σ₁ c).h) (σ₂ c).h) (σ₃ c).h ≤ (σ₃ c).h := by
  simp only [Store.LexLt]
  cases c <;> decide +kernel

theorem stateTransition₁ (c : Bool) :
    P6.fg.stateTransition (s₀.σ 0) (blk c 1).fgView = some (σ₁ c) := by
  cases c <;> rfl

theorem stateTransition₂ (c : Bool) :
    P6.fg.stateTransition ((s₁ c).σ (rt c 1)) (blk c 2).fgView = some (σ₂ c) := by
  rw [s₁_σ, Function.update_self]
  cases c <;> rfl

theorem stateTransition₃ (c : Bool) :
    P6.fg.stateTransition ((s₂ c).σ (rt c 2)) (blk c 3).fgView = some (σ₃ c) := by
  rw [s₂_σ, Function.update_self]
  cases c <;> rfl

theorem rt_ne (c : Bool) : rt c 1 ≠ 0 ∧ rt c 2 ≠ 0 ∧ rt c 3 ≠ 0 ∧ rt c 1 ≠ rt c 2 ∧
    rt c 1 ≠ rt c 3 ∧ rt c 2 ≠ rt c 3 := by
  cases c <;> decide

/-- The initial store accepts block `1`. -/
theorem onBlock₁ (c : Bool) : s₀.onBlock (blk c 1) = some (s₁ c) := by
  unfold s₁
  obtain ⟨h1, -, -, -, -, -⟩ := rt_ne c
  obtain ⟨hl, hJ, hF, -⟩ := σ_numbers c
  have hu : (u₁ c).updateFinality (σ₁ c) =
      { u₁ c with hmax := max (u₁ c).hmax (σ₁ c).h, J := G, hj := (σ₁ c).hj } :=
    updateFinality_J (u₁ c) (σ₁ c) (by rw [hJ]; simp [u₁, blk, h1.symm])
      .refl hl (by rw [hF]; simp [u₁, blk, h1.symm])
  exact onBlock_of (pr := 0) rfl (by simp [blk, h1]) rfl
    (.single ⟨Or.inr (mem_tree rfl), Or.inl rfl, rfl⟩) (stateTransition₁ c) hu

/-- `s₁` accepts block `2`. -/
theorem onBlock₂ (c : Bool) : (s₁ c).onBlock (blk c 2) = some (s₂ c) := by
  rw [s₂.eq_1]
  obtain ⟨h1, h2, -, h12, -, -⟩ := rt_ne c
  obtain ⟨-, -, -, hl, hJ, hF, -⟩ := σ_numbers c
  have hb : ∀ r, (u₂ c).blocks r =
      Function.update (Function.update s₀.blocks (rt c 1) (some (blk c 1))) (rt c 2)
        (some (blk c 2)) r := fun r => by simp [u₂, s₁_blocks, blk]
  have hG : G ∈ (u₂ c).tree := by
    change (u₂ c).blocks 0 = some G; rw [hb]; simp [h1.symm, h2.symm]
  have h₁ : blk c 1 ∈ (u₂ c).tree := by
    change (u₂ c).blocks (rt c 1) = some _; rw [hb]; simp [h12]
  have hu : (u₂ c).updateFinality (σ₂ c) =
      { u₂ c with hmax := max (u₂ c).hmax (σ₂ c).h, J := blk c 1, hj := (σ₂ c).hj } := by
    refine updateFinality_J (u₂ c) (σ₂ c) (by rw [hJ]; exact h₁) ?_ ?_ ?_
    · change Goldilocks.Anc _ (s₁ c).F _
      rw [s₁_F]; exact .single ⟨hG, h₁, by simp [blk, par]⟩
    · change Store.LexLt ((s₁ c).hj, (s₁ c).J.root) _
      rw [s₁_hj, s₁_J]; exact hl
    · change (u₂ c).blocks (σ₂ c).F = some (s₁ c).F
      rw [hF, s₁_F]; exact hG
  have hG' : G ∈ insert (blk c 2) (s₁ c).tree :=
    Or.inr (by change (s₁ c).blocks 0 = some G; rw [s₁_blocks]; simp [h1.symm])
  have h₁' : blk c 1 ∈ insert (blk c 2) (s₁ c).tree :=
    Or.inr (by change (s₁ c).blocks (rt c 1) = some _; rw [s₁_blocks]; simp)
  refine onBlock_of (pr := rt c 1) (by simp [blk, par]) ?_ ?_ ?_ (stateTransition₂ c) hu
  · change (s₁ c).blocks (rt c 2) = none
    rw [s₁_blocks]; simp [h12.symm, h2]
  · rw [s₁_blocks]; simp
  · rw [s₁_F]
    exact anc_tail (Y := blk c 1) (.single ⟨hG', h₁', by simp [blk, par]⟩) h₁' (Or.inl rfl)
      (by simp [blk, par])

/-- `s₂` accepts block `3`, which finalizes block `1`. -/
theorem onBlock₃ (c : Bool) : (s₂ c).onBlock (blk c 3) = some (s₃ c) := by
  rw [s₃.eq_1]
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := rt_ne c
  obtain ⟨-, -, -, -, -, -, hl, hJ, hF, hh⟩ := σ_numbers c
  have hb : ∀ r, (u₃ c).blocks r =
      Function.update (Function.update (Function.update s₀.blocks (rt c 1) (some (blk c 1)))
        (rt c 2) (some (blk c 2))) (rt c 3) (some (blk c 3)) r := fun r => by
    simp [u₃, s₂_blocks, s₁_blocks, blk]
  have hG : G ∈ (u₃ c).tree := by
    change (u₃ c).blocks 0 = some G; rw [hb]; simp [h1.symm, h2.symm, h3.symm]
  have h₁ : blk c 1 ∈ (u₃ c).tree := by
    change (u₃ c).blocks (rt c 1) = some _; rw [hb]; simp [h12, h13]
  have h₂ : blk c 2 ∈ (u₃ c).tree := by
    change (u₃ c).blocks (rt c 2) = some _; rw [hb]; simp [h23]
  have h₃ : blk c 3 ∈ (u₃ c).tree := by
    change (u₃ c).blocks (rt c 3) = some _; rw [hb]; simp
  have hFu : (u₃ c).F = G := s₂_F c
  have hGB₁ : (u₃ c).Anc (u₃ c).F (blk c 1) := by
    rw [hFu]; exact .single ⟨hG, h₁, by simp [blk, par]⟩
  have hB₁B₂ : (u₃ c).Anc (blk c 1) (blk c 2) := .single ⟨h₁, h₂, by simp [blk, par]⟩
  have hσ₃ : (u₃ c).σ (blk c 3).root = σ₃ c := Function.update_self _ _ _
  have hv : ({ u₃ c with hmax := max (u₃ c).hmax (σ₃ c).h, J := blk c 2, hj := (σ₃ c).hj } :
      Store P6 (SA.Payload 6)).HasViableDescendant (blk c 1) := by
    have hanc : (u₃ c).Anc (blk c 1) (blk c 3) := anc_tail hB₁B₂ h₂ h₃ (by simp [blk, par])
    have hle : max (u₃ c).hmax (σ₃ c).h ≤ ((u₃ c).σ (blk c 3).root).h := by
      have hhm : (u₃ c).hmax = (s₂ c).hmax := by unfold u₃; rfl
      rw [hσ₃, hhm, s₂_hmax]; exact hh
    exact ⟨blk c 3, h₃, hanc, (headHeightFloor_le _).trans hle⟩
  have hu : (u₃ c).updateFinality (σ₃ c) =
      { u₃ c with hmax := max (u₃ c).hmax (σ₃ c).h, J := blk c 2, hj := (σ₃ c).hj,
                  F := blk c 1 } := by
    refine updateFinality_JF (u₃ c) (σ₃ c) (by rw [hJ]; exact h₂)
      (hGB₁.tail ⟨h₁, h₂, by simp [blk, par]⟩) ?_ (by rw [hF]; exact h₁) hGB₁ ?_ hB₁B₂ hv
    · change Store.LexLt ((s₂ c).hj, (s₂ c).J.root) _
      rw [s₂_hj, s₂_J]; exact hl
    · rw [hFu]; intro h
      exact h1 (congrArg Block.root h).symm
  have hG' : G ∈ insert (blk c 3) (s₂ c).tree := Or.inr (by
    change (s₂ c).blocks 0 = some G; rw [s₂_blocks, s₁_blocks]; simp [h1.symm, h2.symm])
  have h₁' : blk c 1 ∈ insert (blk c 3) (s₂ c).tree := Or.inr (by
    change (s₂ c).blocks (rt c 1) = some _; rw [s₂_blocks, s₁_blocks]; simp [h12])
  have h₂' : blk c 2 ∈ insert (blk c 3) (s₂ c).tree := Or.inr (by
    change (s₂ c).blocks (rt c 2) = some _; rw [s₂_blocks]; simp)
  refine onBlock_of (pr := rt c 2) (by simp [blk, par]) ?_ ?_ ?_ (stateTransition₃ c) hu
  · change (s₂ c).blocks (rt c 3) = none
    rw [s₂_blocks, s₁_blocks]; simp [h13.symm, h23.symm, h3]
  · rw [s₂_blocks]; simp
  · rw [s₂_F]
    exact anc_tail (Y := blk c 2) (anc_tail (Y := blk c 1)
      (.single ⟨hG', h₁', by simp [blk, par]⟩) h₁' h₂' (by simp [blk, par])) h₂' (Or.inl rfl)
      (by simp [blk, par])

/-- The store after the third block has finalized the first. -/
theorem F_s₃ (c : Bool) : (s₃ c).F = blk c 1 := by
  rw [s₃, addAtts_F]

end Consensus.Goldilocks.ConflictRun

end
