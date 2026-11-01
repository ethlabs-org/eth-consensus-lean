module
public import AvailableChainSimplexFG.ChainState
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Prod.Lex

@[expose] public section

namespace AvailableChain.SimplexFG

/-- A view: a finite set of blocks (r148 §2 `V`). -/
abbrev View (V : Type) := Finset (FGBlock V)

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V] (E : Electorate V)
  (cfg : FGConfig)

/-- The state height of a block (`σ[W].h`, r148 §2). -/
def hOf (W : FGBlock V) : Height := (derive E cfg W).h

/-- `H = max({1} ∪ {h(W) : W ∈ V})` (r148 §2 `FJ_FRAME`). -/
def frontier (Vw : View V) : Height := Vw.sup (hOf E cfg) ⊔ 1

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] Roots identify view ancestors.
The selector proofs use this local premise. The model does not assume it. -/
def ViewRootInj (Vw : View V) : Prop :=
  ∀ X Y, (∃ W ∈ Vw, FGBlock.Preceq X W) → (∃ W ∈ Vw, FGBlock.Preceq Y W) →
    X.root = Y.root → X = Y

/-- The lex key `(h_j, J.root)`. -/
def lexKey (p : Height × FGBlock V) : Lex (ℕ × ℕ) := toLex (p.1, p.2.root.value)

/-- The frame controls (ALFS: DC's live caches). The root and the band floor
are functions of them (r148 FJ_FRAME table). -/
structure Controls (V : Type) where
  F : FGBlock V
  H : Height
  j : Height
  J : FGBlock V
  contest : Bool

namespace Controls
/-- [pin fj.frame.v4] The uncontested phase: the root is J (the root test of
`get_fg_root`, alfs4 lines 1004–1011). -/
def rootIsJ (c : Controls V) : Bool := decide (c.H = c.j + 1) && !c.contest
/-- [pin fj.frame.v4] The FG root: J in the uncontested phase, else F
(`get_fg_root`, alfs4 lines 1004–1011). -/
def Z (c : Controls V) : FGBlock V := if c.rootIsJ then c.J else c.F
/-- [pin fj.frame.v4] The band floor: H in a contest, else H − 1 (`band_floor`,
alfs4 lines 978–986). -/
def lo (c : Controls V) : Height := if c.contest then c.H else c.H - 1
end Controls

structure Frame (V : Type) where
  F : FGBlock V
  H : Height
  j : Height
  J : FGBlock V
  Z : FGBlock V
  lo : Height
  D : Finset (FGBlock V)
  contest : Bool

section Pick

variable {α : Type} [DecidableEq α]

-- port: DC/DecoupledConsensusModel/Objects/Blocks.lean:286-293
instance decidableExistsUniqueMem (T : Finset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∃! a, a ∈ T ∧ p a) :=
  decidable_of_iff (∃ a ∈ T, p a ∧ ∀ b ∈ T, p b → b = a) <| by
    constructor
    · rintro ⟨a, haT, hpa, huniq⟩
      exact ⟨a, ⟨haT, hpa⟩, fun b hb => huniq b hb.1 hb.2⟩
    · rintro ⟨a, ⟨haT, hpa⟩, huniq⟩
      exact ⟨a, haT, hpa, fun b hbT hpb => huniq b ⟨hbT, hpb⟩⟩

-- port: DC/DecoupledConsensusModel/Objects/Blocks.lean:295-301
/-- The unique member of `T` satisfying `p`, or `none` when there is no such
member or more than one. Computable, and total without a choice principle. -/
def pickPair (T : Finset α) (p : α → Bool) : Option α :=
  if h : ∃! a, a ∈ T ∧ p a = true then
    some (T.choose (fun a => p a = true) h)
  else
    none

end Pick

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
The lex-greatest `(h_j, J)` over `W ∈ Vw` with `F ⪯ σ[W].J`, or `(0, genesis)`
if there is none (r148 §2 `FJ_FRAME`, the `(j, J)` line). The candidates are the
image of `Vw`, so two carriers of one pair count once; `pickPair` (DC's
`pickUnique?`) returns `none` when no candidate or more than one candidate has
the greatest key, and `lexMax` then falls back. Under `ViewRootInj`, equal
keys identify equal pairs, so only an empty candidate set gives the fallback. -/
def lexMax (F : FGBlock V) (Vw : View V) : Height × FGBlock V :=
  let candidates : Finset (Height × FGBlock V) :=
    (Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)).image
      (fun W => ((derive E cfg W).h_j, (derive E cfg W).J))
  let key := candidates.sup lexKey
  (pickPair candidates (fun p => decide (lexKey p = key))).getD (0, .genesis)

/-- [pin fj.frame.v1] The controls of one block set (r148 §2 FJ_FRAME, R1 view
form): H, the lex pair with `F ⪯ J`, and the contest at `H = j+1` when a
height-H block does not extend J. -/
def fjControls (F : FGBlock V) (Vw : View V) : Controls V :=
  let H := frontier E cfg Vw
  let p := lexMax E cfg F Vw
  ⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
    decide (∃ W ∈ Vw, hOf E cfg W = H ∧ ¬ FGBlock.Preceq p.2 W)⟩

/-- [pin fj.frame.v4] The filtered tree of any block set under given controls
(`get_filtered_block_tree_from(Σ, blocks)` with `viable_tree_from`, alfs4 lines
988–994, 1013–1020). -/
def filteredFrom (c : Controls V) (blocks : Finset (FGBlock V)) : Finset (FGBlock V) :=
  blocks.filter (fun B => FGBlock.preceq c.F B && FGBlock.preceq c.Z B &&
    decide (∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ hOf E cfg W))

/-- [pin fj.frame.v1] The special case: controls and filtered tree from one
block set. -/
def fjFrame (F : FGBlock V) (Vw : View V) : Frame V :=
  let c := fjControls E cfg F Vw
  ⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFrom E cfg c Vw, c.contest⟩

/-- Review Focus 3: a genesis-only view. -/
example : (fjFrame E4 cfg1 .genesis {.genesis}).H = 1 ∧
    (fjFrame E4 cfg1 .genesis {.genesis}).Z = .genesis ∧
    (fjFrame E4 cfg1 .genesis {.genesis}).lo = 0 ∧
    (fjFrame E4 cfg1 .genesis {.genesis}).D = {.genesis} := by decide
/-- After B1: H = 2, j = 1, J = genesis, no contest, root J, lo = 1. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1}).contest = false ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1}).lo = 1 := by decide

/-- After B1 the root is `J = genesis`, and both blocks have a witness of height
≥ `lo = 1` (B1 itself, at height 2), so D holds both blocks. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1}).J = .genesis ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1}).Z = .genesis ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1}).D = {.genesis, B1} := by decide
/-- Genesis is its own witness under the controls of `{genesis, B1}`
(`h(genesis) = 1 ≥ lo = 1`), even over the smaller block set `{genesis}`. -/
example : filteredFrom E4 cfg1 (fjControls E4 cfg1 .genesis {.genesis, B1})
    {.genesis} = {.genesis} := by decide

/-! ### Review Focus 4: the lex order

`B1a` is `B1` (slot 1, parent genesis, body `0`, three target rows at height 1
for genesis). `B1b` is its sibling with body `1`: the same rows, a different
block, so a different root. `childA`/`childB` (body `0`) each carry three
target rows at height 2 for their own parent's root, so they justify
`B1a`/`B1b` at height 2. -/

def B1a : FGBlock (Fin 4) := B1
def B1b : FGBlock (Fin 4) := .node .genesis 1 ⟨2⟩ 1 [rowT 0, rowT 1, rowT 2]

/-- [helper] A target or timeout row at height `h` for `target`. -/
def rowAt (h : Height) (target : BlockId) (timeout : Bool) (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote h target timeout, none⟩

def childA : FGBlock (Fin 4) :=
  .node B1a 2 ⟨4⟩ 0 [rowAt 2 B1a.root false 0, rowAt 2 B1a.root false 1, rowAt 2 B1a.root false 2]
def childB : FGBlock (Fin 4) :=
  .node B1b 2 ⟨5⟩ 0 [rowAt 2 B1b.root false 0, rowAt 2 B1b.root false 1, rowAt 2 B1b.root false 2]

/-- `B1b` justifies genesis at height 1, like `B1a`. -/
example : (derive E4 cfg1 B1b).h = 2 ∧ (derive E4 cfg1 B1b).h_j = 1 ∧
    (derive E4 cfg1 B1b).J = .genesis := by decide
/-- `childA` justifies `B1a` at height 2. -/
example : (derive E4 cfg1 childA).h = 3 ∧ (derive E4 cfg1 childA).h_j = 2 ∧
    (derive E4 cfg1 childA).J = B1a := by decide
/-- `childB` justifies `B1b` at height 2. -/
example : (derive E4 cfg1 childB).h = 3 ∧ (derive E4 cfg1 childB).h_j = 2 ∧
    (derive E4 cfg1 childB).J = B1b := by decide

/-- The root order of the two entries: `B1a.root < B1b.root`. -/
example : B1a.root.value < B1b.root.value := by decide

/-- `(2, B1a)` and `(2, B1b)` are two different justified entries at height 2;
the frame selects the greater root, `B1b`. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1a, B1b, childA, childB}).j = 2 ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, B1b, childA, childB}).J = B1b := by
  decide +kernel

/-! ### ROOT-DIGEST W1: finite root assignment (DC scoped roots)

The fixture assigns different small roots to B1a and B1c. This is a property
of these values. It is not a property of arbitrary FGBlock values. -/

def B1c : FGBlock (Fin 4) := .node .genesis 2 ⟨3⟩ 0 [rowT 0, rowT 1, rowT 2]
def childC : FGBlock (Fin 4) :=
  .node B1c 3 ⟨6⟩ 0 [rowAt 2 B1c.root false 0, rowAt 2 B1c.root false 1, rowAt 2 B1c.root false 2]

/-- `B1c` justifies genesis at height 1, like `B1a`, and is a different block. -/
example : (derive E4 cfg1 B1c).h = 2 ∧ (derive E4 cfg1 B1c).h_j = 1 ∧
    (derive E4 cfg1 B1c).J = .genesis ∧ B1a ≠ B1c := by decide
/-- `childC` justifies `B1c` at height 2. -/
example : (derive E4 cfg1 childC).h = 3 ∧ (derive E4 cfg1 childC).h_j = 2 ∧
    (derive E4 cfg1 childC).J = B1c := by decide

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
The explicit finite IDs give different roots to B1a and B1c. -/
example : B1a.root ≠ B1c.root := by decide

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
`ViewRootInj` holds on this explicit finite view. -/
example : ViewRootInj ({.genesis, B1a, B1c, childA, childC} : View (Fin 4)) :=
  by
    intro A B hA hB h
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
      FGBlock.Preceq, FGBlock.preceq, B1a, B1, B1c, childA, childC,
      Bool.or_eq_true, decide_eq_true_eq] at hA hB
    simp only [or_assoc] at hA hB
    rcases hA with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rcases hB with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      first | rfl | simp only [FGBlock.root, genesisRoot, BlockId.mk.injEq,
        Nat.reduceEqDiff] at h

/-- The root order of the two entries: `B1a.root < B1c.root`. -/
example : B1a.root.value < B1c.root.value := by decide

/-- No fallback: the selector finds one pair with the greatest key, `(2, B1c)`. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1a, B1c, childA, childC}).j = 2 ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, B1c, childA, childC}).J = B1c := by
  decide +kernel

/-! ### Review Focus 1: the contest changes both viability and `lo`

`Y` reaches height 3 through a mature timeout (two target rows and one timeout
at height 2 for `B1b`), without justifying `B1b`; it does not extend `J = B1a`,
so it is a contest witness at `H = j + 1 = 3`. `X` is a child of `B1a` with no
rows, so its state height stays at 2: in the view with `Y`, `X`'s only witness
(itself) has height `2 < lo = 3` and `X ∉ D`; in the view without `Y`, `lo =
H − 1 = 2` and `X ∈ D`, since `X` extends `J = B1a`. -/

def Y : FGBlock (Fin 4) :=
  .node B1b 2 ⟨7⟩ 0 [rowAt 2 B1b.root false 0, rowAt 2 B1b.root false 1, rowAt 2 B1b.root true 2]
def X : FGBlock (Fin 4) := .node B1a 3 ⟨8⟩ 0 []

/-- `Y` reaches height 3 by a mature progress quorum (two targets, one
timeout), without a target quorum: it does not justify `B1b` (`J`, `h_j` stay
at genesis, 1). -/
example : (derive E4 cfg1 Y).h = 3 ∧ (derive E4 cfg1 Y).h_j = 1 ∧
    (derive E4 cfg1 Y).J = .genesis := by decide
/-- `X` has no rows: its state height stays at its parent `B1a`'s height. -/
example : (derive E4 cfg1 X).h = 2 ∧ (derive E4 cfg1 X).h_j = 1 ∧
    (derive E4 cfg1 X).J = .genesis := by decide

/-- Contested: `Y` (height 3) does not extend `J = B1a`, so `contest = true`,
`Z = F`, `lo = H = 3`; `X`'s only witness has height 2, so `X ∉ D`. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, Y, X}).contest = true ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, Y, X}).Z = .genesis ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, Y, X}).lo = 3 ∧
    X ∉ (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, Y, X}).D := by
  decide +kernel
/-- Uncontested (the same blocks without `Y`): `contest = false`, `Z = J =
B1a`, `lo = H − 1 = 2`; `X` extends `J` and its witness (itself) has height
`2 ≥ lo`, so `X ∈ D`. -/
example : (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, X}).contest = false ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, X}).Z = B1a ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, X}).lo = 2 ∧
    X ∈ (fjFrame E4 cfg1 .genesis {.genesis, B1a, childA, B1b, X}).D := by
  decide +kernel

end AvailableChain.SimplexFG
end
