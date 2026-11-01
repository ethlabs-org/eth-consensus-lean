module
public import AvailableChainSimplexFG.Frame

@[expose] public section

namespace AvailableChain.SimplexFG

/-- [pin fj.frame.v4] The FG part of a node store (DC-fj). `TF` is the ONE admitted,
parent-closed tree (the spec's `Σ.T`, Trees paragraph, alfs4 lines 352–371;
initialization 474–482; DC `consensus.tex` 1720–1739). The spec admits a block
B only if `F ⪯ B` at that time (line 354); this history is NOT formalized (no
ghost field records it), and no lemma needs it. The tree is cumulative: no block is
deleted when F advances. There is no raw tree. `F`, `J`, `h_j` and `h_max` are
DC's live caches; they are the frame controls. `h_max` only grows (DC line
864). The field keeps the name `TF` so that the pinned statements do not
change. -/
structure Store (V : Type) where
  TF : Finset (FGBlock V)
  F : FGBlock V
  J : FGBlock V
  h_j : Height
  h_max : Height
  deriving DecidableEq

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V] (E : Electorate V)
  (cfg : FGConfig)

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- [pin fj.frame.v4] The initial store (alfs4 lines 474–482): the genesis tree,
`F = J = genesis`, `h_j = 0`, `h_max = 1`. -/
def Store.init : Store V := ⟨{.genesis}, .genesis, .genesis, 0, 1⟩

/-- [pin fj.frame.v4] DC's acceptance viability on the admitted tree (`viable_tree(Σ)`,
"acceptance only", alfs4 lines 996–1002): the band start is `h_max − 1`, also in
a contest. -/
def acceptViable (st : Store V) : Finset (FGBlock V) :=
  st.TF.filter (fun B => FGBlock.preceq st.F B &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq B W ∧ st.h_max - 1 ≤ hOf E cfg W))

/-- [pin fj.frame.v4] `update_finality`, DC form (alfs4 lines 847–860: no F basis, no J
carrier). The spec takes `σ = Σ.σ[B]`; here `σ = derive B`. After an F advance
the spec calls `reconcile_with_finality` (lines 862–882), which writes only SA
fields (leases, fastWrite, saved results, S); it is not in this module. -/
def update_finality (st : Store V) (B : FGBlock V) : Store V :=
  let σ := derive E cfg B
  let st := { st with h_max := max st.h_max σ.h }
  let st := if FGBlock.preceq st.F σ.J && decide (lexKey (st.h_j, st.J) < lexKey (σ.h_j, σ.J))
    then { st with J := σ.J, h_j := σ.h_j } else st
  if FGBlock.preceq st.F σ.F && decide (st.F ≠ σ.F) && FGBlock.preceq σ.F st.J &&
      decide (σ.F ∈ acceptViable E cfg st)
    then { st with F := σ.F } else st

/-- [pin fj.frame.v4] `on_block`, FG part (alfs4 lines 792–817; DC `consensus.tex` 1720–1739).
In the spec's order, it refuses a block that is already in the tree or whose
parent is not in the tree (lines 794–795), a block with `F ⋠ B` (line 796), and
a block whose slot is not greater than its parent's slot (line 798: the spec
makes DC's `assert B.parent.slot < B.slot` of `state_transition`, DC
`consensus.tex` lines 791 and 2220, a refusal). Each refusal comes before the
block's state is computed (lines 806–807)
or its objects are unpacked: the store does not change. Otherwise the block
enters the tree (line 808) and `update_finality` runs (line 812).
FG admission input contract (the caller passes only blocks that satisfy it;
`on_block` does not test it): (1) the future-slot bound `B.slot ≤ Σ.s` (line
794; the node's slot is not in `Store`); (2) the slot-`B.slot` proposer
signature (lines 798–799); (3) the row-round check (lines 802–805; DC §7, "no
row from the block's future"; `Row` has no round field). Each item can
refuse a block that this function accepts. No lemma of this plan uses them: the
lemmas quantify over all `StoreInv` stores and all blocks, so they stay sound
for the stores of the spec. The vote and row pools are the AP's. -/
def on_block (st : Store V) (B : FGBlock V) : Store V :=
  if B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot then st
  else update_finality E cfg { st with TF := insert B st.TF } B

/-- [pin fj.frame.v4] The frame controls of ALFS: DC's live caches, with the
contest over the full admitted tree (`fg_contest`, `band_floor`, `get_fg_root`,
alfs4 lines 970–986, 1004–1011). -/
def storeControls (st : Store V) : Controls V :=
  ⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, hOf E cfg W = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩

/-- [pin fj.frame.v4] The ALFS filtered tree of a block set:
`get_filtered_block_tree_from(Σ, blocks)` (alfs4 lines 1013–1020); with
`blocks = TF`, `get_filtered_block_tree(Σ)` (lines 1021–1025). -/
def storeFrame (st : Store V) (blocks : Finset (FGBlock V)) : Finset (FGBlock V) :=
  filteredFrom E cfg (storeControls E cfg st) blocks

omit [Fintype V] [RowCodec V] in
/-- [pin fj.frame.v4] The active view `act(Σ) = {B ∈ Σ.T : B ⪯ Σ.F or Σ.F ⪯ B}` (alfs4 line 358;
r161 §2). AP interface only: only the SA base reads it. It is a view, not a
deletion: `TF` keeps every block. No FG definition or lemma reads it. -/
def activeView (st : Store V) : Finset (FGBlock V) :=
  st.TF.filter (fun B => FGBlock.compatible B st.F)

/-! ### Review Focus 2: the invariant is necessary

A stale store: `B1` is in the tree, but `h_max` and the pair are those of
`{genesis}`. It violates `StoreInv` (Kit). Its controls give `lo = 1 − 1 = 0`;
the controls of its tree give `H = 2`, `lo = 1`. -/

/-- [helper] A store with stale caches (it violates `StoreInv`). -/
def stStale : Store (Fin 4) := ⟨{.genesis, B1}, .genesis, .genesis, 0, 1⟩

/-- The stale caches and the controls of the tree give different `lo`. -/
example : (storeControls E4 cfg1 stStale).lo = 0 ∧
    (fjControls E4 cfg1 stStale.F stStale.TF).lo = 1 ∧
    storeControls E4 cfg1 stStale ≠ fjControls E4 cfg1 stStale.F stStale.TF := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have hlo := congrArg Controls.lo h
  revert hlo
  decide

/-! ### Review Focus 5 and ALFS: a contested store (reachable)

`stC` is reached by `on_block` from `Store.init` with the blocks of the
contest test of Frame.lean (Review Focus 1): `B1a`, `childA`, `B1b`, `Y`, `X`. No block carries a
finality pair, so `F = genesis`. The pair is `(2, B1a)` (from `childA`), and `Y`
(height 3) does not extend `B1a`: the store is contested, `lo = H = 3`. -/

/-- [helper] The contested store, reached by `on_block`. -/
def stC : Store (Fin 4) := [B1a, childA, B1b, Y, X].foldl (on_block E4 cfg1) Store.init

/-- The caches of `stC`, field by field. (The derived `DecidableEq Store` does
not reduce when the two trees are one set in a different insertion order: it
casts along `TF = TF'`, which holds only as a proposition. So the fields are
compared one by one.) -/
example : stC.TF = {.genesis, B1a, childA, B1b, Y, X} ∧ stC.F = .genesis ∧
    stC.J = B1a ∧ stC.h_j = 2 ∧ stC.h_max = 3 := by
  decide +kernel

/-- On the reachable store `stC`, the live caches are the controls of its tree
(the central lemma `storeControls_eq_fjControls`, Kit). -/
example : (storeControls E4 cfg1 stC).H = (fjControls E4 cfg1 stC.F stC.TF).H ∧
    (storeControls E4 cfg1 stC).j = (fjControls E4 cfg1 stC.F stC.TF).j ∧
    (storeControls E4 cfg1 stC).J = (fjControls E4 cfg1 stC.F stC.TF).J ∧
    (storeControls E4 cfg1 stC).contest = (fjControls E4 cfg1 stC.F stC.TF).contest := by
  decide +kernel

/-- Review Focus 5: in a contest, acceptance viability (band start `H − 1 = 2`)
holds `X` (height 2), and the filtered tree (band start `lo = 3`) does not. -/
example : (storeControls E4 cfg1 stC).contest = true ∧ hOf E4 cfg1 X = 2 ∧
    X ∈ acceptViable E4 cfg1 stC ∧ X ∉ storeFrame E4 cfg1 stC stC.TF := by
  decide +kernel

/-- The frozen-tree form: over the smaller set without `Y`, the store controls
(contest, `Z = genesis`, `lo = 3`) drop `X`; the controls of that set (no
contest, `Z = B1a`, `lo = 2`) keep it. The controls come from the store, not
from the set. -/
example : X ∉ storeFrame E4 cfg1 stC {.genesis, B1a, childA, B1b, X} ∧
    X ∈ (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, X}).D := by
  decide +kernel

/-- The empty frozen domain (Astra K01; ldp L6): the store is contested
(`lo = H = 3`), and every block of the frozen set is below height 3. -/
example : storeFrame E4 cfg1 stC {.genesis, B1a, B1b, X} = ∅ := by
  decide +kernel

/-! ### Review Focus 7: refusal (alfs4 lines 794–798) and the active view

`B1`, `B2`, `B3` are Astra's G02 chain (TwoChanges.lean reuses them). `B2` (slot 2)
carries three targets for `(2, B1)`: state height 3, pair `(2, B1)`. `B3`
(slot 3) carries three timeouts for `(3, B2)`, each with the finality pair
`(2, B1)`: state height 4, and it finalizes `B1`. `B1'` (slot 2, parent
genesis) carries three targets at height 1 for genesis: it conflicts with `B1`.
Each block has body `0`, and each row names a derived root. With the same
content, `B2` is `childA` of Frame.lean and `B1'` is `B1c`: a block is its
content. -/

def B2 : FGBlock (Fin 4) :=
  .node B1 2 ⟨10⟩ 0 [rowAt 2 B1.root false 0, rowAt 2 B1.root false 1, rowAt 2 B1.root false 2]

/-- [helper] A timeout row for `(3, B2)` with the finality pair `(2, B1)`. -/
def rowB3 (i : Fin 4) : Row (Fin 4) := ⟨i, .vote 3 B2.root true, some ⟨2, B1.root⟩⟩

def B3 : FGBlock (Fin 4) := .node B2 3 ⟨11⟩ 0 [rowB3 0, rowB3 1, rowB3 2]

def B1' : FGBlock (Fin 4) := .node .genesis 2 ⟨12⟩ 0 [rowT 0, rowT 1, rowT 2]

/-- The G02 chain: `B2` justifies `B1` at height 2; `B3` reaches height 4 and
finalizes `B1`. -/
example : (derive E4 cfg1 B2).h = 3 ∧ (derive E4 cfg1 B2).h_j = 2 ∧
    (derive E4 cfg1 B2).J = B1 ∧ (derive E4 cfg1 B3).h = 4 ∧
    (derive E4 cfg1 B3).F = B1 ∧ (derive E4 cfg1 B3).h_F = 2 := by
  decide +kernel

/-- [helper] The reachable store after `B1`, `B2`, `B3`. -/
def stF : Store (Fin 4) := [B1, B2, B3].foldl (on_block E4 cfg1) Store.init

/-- `B3` finalizes `B1`, and `update_finality` accepts it (field by field, as
for `stC`). -/
example : stF.TF = {.genesis, B1, B2, B3} ∧ stF.F = B1 ∧ stF.J = B1 ∧ stF.h_j = 2 ∧
    stF.h_max = 4 := by
  decide +kernel

/-- Refusal of `F ⋠ B` (alfs4 line 796): `B1'` is new, its parent is in the tree,
and its slot is greater than its parent's slot, but `B1 ⋠ B1'`. Only the F test
refuses it: the store does not change, and `B1'` is not stored. -/
example : B1' ∉ stF.TF ∧ B1'.parent ∈ stF.TF ∧ ¬ FGBlock.Preceq stF.F B1' ∧
    B1'.parent.slot < B1'.slot ∧
    on_block E4 cfg1 stF B1' = stF ∧ B1' ∉ (on_block E4 cfg1 stF B1').TF := by
  decide +kernel

/-- Refusal of a block that is already in the tree (alfs4 line 794). -/
example : on_block E4 cfg1 stF B2 = stF := by
  decide +kernel

/-- Refusal of a block whose parent is not in the tree (alfs4 line 795). -/
example : on_block E4 cfg1 Store.init B2 = Store.init := by
  decide

/-- [helper] The reachable store after `B1`. -/
def st1 : Store (Fin 4) := on_block E4 cfg1 Store.init B1

/-- [helper] A child of `B1` at slot 1, the slot of `B1`. -/
def Bs : FGBlock (Fin 4) := .node B1 1 ⟨13⟩ 0 []

/-- The parent-slot refusal (alfs4 line 798; DC `consensus.tex` 791 and 2220):
`Bs` is new, its parent `B1` is in the tree, and it extends `F = genesis`, but
its slot is not greater than its parent's slot. The store does not change. -/
example : B1 ∈ st1.TF ∧ st1.F = .genesis ∧ Bs ∉ st1.TF ∧
    FGBlock.Preceq st1.F Bs ∧ on_block E4 cfg1 st1 Bs = st1 := by
  decide

/-- [helper] The reachable store after `B1'`, `B1`, `B2`, `B3`: `B1'` enters
while `F = genesis`. -/
def stAct : Store (Fin 4) := [B1', B1, B2, B3].foldl (on_block E4 cfg1) Store.init

/-- The active view (alfs4 line 358): `B1'` stays in the tree after F moves to
`B1`, but it is not in the active view. -/
example : stAct.F = B1 ∧ (stAct.h_j, stAct.J) = (2, B1) ∧ stAct.h_max = 4 ∧
    B1' ∈ stAct.TF ∧ B1' ∉ activeView stAct ∧
    FGBlock.genesis ∈ activeView stAct ∧ B1 ∈ activeView stAct ∧
    B2 ∈ activeView stAct ∧ B3 ∈ activeView stAct := by
  decide +kernel

end AvailableChain.SimplexFG
end
