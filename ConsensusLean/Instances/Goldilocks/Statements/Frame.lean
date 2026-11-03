module
public import ConsensusLean.Instances.Goldilocks.Spec.Frame

@[expose] public section

/-! # Goldilocks: frame statements

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks#21), the
frame-level consequences of nodes G0.3 (frame) and G0.4 (frame), against `Spec/Frame`:

* G0.4 (frame): in a well-formed frame `viable_ancestor(Φ, B)` exists and is unique for
  `B ∈ Φ.tree`, and it is `B` itself when `B` is viable or `B ⪯ fc_root`; the viable tree of a
  set is closed under ancestors down to `fc_root` within that set; the tree is parent-closed
  down to `Φ.F`.
* G0.3 (frame): a step adds exactly the new block; along a sequence of frames that evolves by
  steps, a block of an earlier tree that extends a later finalized tip is in the later tree,
  a block that leaves the tree never returns, and each block enters at most once.

The sequence statements are about the blocks of all the frames of the sequence, so they assume
that the union of the trees lies in one coherent set `U` (at a node, the accepted tree: its
roots are injective by the duplicate-root test of `fg_on_block`, and slots increase by the
assertion of `state_transition`), and that the first frame is rooted. `FrameNeverReturns` needs
both: without coherence a block that left comes back under a reused root, and without the rooted
first frame a block of the first tree whose parent is missing leaves and comes back once the
parent arrives (`ConsensusLeanTest/GoldilocksFrameRejection.lean`:
`frameNeverReturns_needs_coherent`, `frameNeverReturns_needs_rooted`). `FrameEntersOnce` needs
coherence (`frameEntersOnce_needs_coherent`). Every frame after a step is rooted at its new
`Φ.F`, so a block added by a step cannot be added again; `frame_statements` proves it through
`FrameNeverReturns`, which uses both premises. Statements only: no proofs here. -/

namespace Consensus.Goldilocks

/-- **G0.4 (frame), `viable_ancestor` exists.** In a well-formed frame, every block of the tree
has exactly one viable ancestor, and the function `viableAncestor` returns it. -/
def ViableAncestorExists : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Frame n FGP ACP) (B : Block n FGP ACP),
    FrameOK Φ → B ∈ Φ.tree →
      Φ.IsViableAncestor B (Φ.viableAncestor B) ∧
      ∀ A, Φ.IsViableAncestor B A → A = Φ.viableAncestor B

/-- **G0.4 (frame), `viable_ancestor` of a candidate.** In a well-formed frame, a block that is
viable or at or below `fc_root` is its own viable ancestor. -/
def ViableAncestorSelf : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Frame n FGP ACP) (B : Block n FGP ACP),
    FrameOK Φ → (B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) → Φ.viableAncestor B = B

/-- **G0.4 (frame), the viable tree is closed under ancestors down to `fc_root`.** An ancestor,
in `S`, of a block of the viable tree of `S` that extends `fc_root` is in that viable tree. -/
def ViableTreeAncestorClosed : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Frame n FGP ACP) (S : Set (Block n FGP ACP))
    (A B : Block n FGP ACP),
    B ∈ Φ.viableTree S → A ∈ S → Φ.Anc Φ.fcRoot A → Φ.Anc A B → A ∈ Φ.viableTree S

/-- **G0.4 (frame), parent-closed down to `Φ.F`.** In a well-formed frame, every block of the
tree other than `Φ.F` has its parent in the tree, at a smaller slot. -/
def FrameParentClosed : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Frame n FGP ACP) (C : Block n FGP ACP),
    FrameOK Φ → C ∈ Φ.tree → C ≠ Φ.F →
      ∃ P ∈ Φ.tree, C.parent = some P.root ∧ P.slot < C.slot

/-- **G0.3 (frame), a step adds exactly the new block.** After `Φ ⊑_B Φ'`, `B ∈ Φ'.tree` and
every block of `Φ'.tree` is `B` or a block of `Φ.tree`. -/
def FrameStepAddsBlock : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ Φ' : Frame n FGP ACP) (B : Block n FGP ACP),
    FrameStep Φ B Φ' → B ∈ Φ'.tree ∧ ∀ X ∈ Φ'.tree, X = B ∨ X ∈ Φ.tree

/-- **G0.3 (frame), retention.** Along a frame sequence whose trees lie in a coherent set `U`
and whose first frame is rooted: a block of the tree at `i` that extends the finalized tip at
`j ≥ i` (inside `U`) is in the tree at `j`. -/
def FrameRetention : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Nat → Frame n FGP ACP) (U : Set (Block n FGP ACP)),
    FrameSeqIn Φ U →
    ∀ i j, i ≤ j → ∀ X ∈ (Φ i).tree, Anc U (Φ j).F X → X ∈ (Φ j).tree

/-- **G0.3 (frame), a block that leaves the tree never returns.** Under the hypotheses of
`FrameRetention`: a block of the tree at `i` that is not in the tree at `j ≥ i` is not in the tree
at any `k ≥ j`. -/
def FrameNeverReturns : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Nat → Frame n FGP ACP) (U : Set (Block n FGP ACP)),
    FrameSeqIn Φ U →
    ∀ i j k, i ≤ j → j ≤ k → ∀ X ∈ (Φ i).tree, X ∉ (Φ j).tree → X ∉ (Φ k).tree

/-- **G0.3 (frame), each block enters at most once.** Under the hypotheses of `FrameRetention`: if
the steps at `i` and at `j` both add the block `B`, then `i = j`. -/
def FrameEntersOnce : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (Φ : Nat → Frame n FGP ACP) (U : Set (Block n FGP ACP)),
    FrameSeqIn Φ U →
    ∀ i j (B : Block n FGP ACP),
      FrameStep (Φ i) B (Φ (i + 1)) → FrameStep (Φ j) B (Φ (j + 1)) → i = j

/-- The frame statements. -/
structure FrameStatements : Prop where
  viableAncestorExists : ViableAncestorExists
  viableAncestorSelf : ViableAncestorSelf
  viableTreeAncestorClosed : ViableTreeAncestorClosed
  parentClosed : FrameParentClosed
  stepAddsBlock : FrameStepAddsBlock
  retention : FrameRetention
  neverReturns : FrameNeverReturns
  entersOnce : FrameEntersOnce

end Consensus.Goldilocks

end
