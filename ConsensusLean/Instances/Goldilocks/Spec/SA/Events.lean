module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Trace

@[expose] public section

/-! # Goldilocks SA: events and honest objects over SA traces

The vocabulary of the AC step statements (claims §"L1: components / Available chain"), over an
AC trace of `goldilocksSA`:

* **Events inside calls.** A vote is an emission (`VoteAt`, with its call's label). A fast lock
  of slot `s` on `B` is written by the fast test of the confirmation update of slot `s` (the tick
  at `t_s + 6Δ` of a joined node, vetoed or not; over the path blocks no live lock vetoes;
  `FastUpdateAt`) or by an
  optimistic confirmation (`OptimisticLockAt`), which runs inside a call at its receipt (after
  the admission of an `on_message` vote or of an `on_block` block's votes) and after the own vote's
  admission; each comes with its **counted votes**. `ResultAt` is the result of
  `get_confirmation` at an update (fast, slow, vetoed or not), with the votes it counts;
  `ToFGAt` is a block that `ac_to_fg` returns; `ProposalAt` is a proposal and its payload.
* **Honest objects** (`HonestObjects`): the run facts about honest signers that the AC trace
  contract does not carry (claims §"Runs": signatures are unforgeable; the slot proposer, the
  paper's `state_transition` assertion, is in the model the run law `LocalRun.proposerCredential`):
  every vote of an honest validator that an honest node holds, in its pools or in a block of its
  frame, was emitted by that validator's node at an earlier cut; every block of an honest frame
  other than genesis has the slot's proposer; and an honest proposer has at most one block per slot
  in the honest frames. `ACRun` bundles them with `ACLocalRun`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- The vote `v`'s head extends `B` inside `U`. -/
def VoteExtends (U : Set (Blk sp.n FGP)) (v : Vote sp.n) (B : Blk sp.n FGP) : Prop :=
  ∃ Hd ∈ U, Hd.root = v.head ∧ Anc U B Hd

/-- `y` casts the vote of emission `e` at cut `i`, a call with label `ℓ`. -/
def CastAt (tr : SATrace sp FGP ro) (y : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksSA sp FGP ro))
    (e : Em sp FGP) : Prop :=
  tr.CallAt y i ℓ ∧ e ∈ ℓ.emits

/-- At the vote of emission `e` (a call with frame `ℓ.frame`), `B` is in the viable tree of the
voter block tree of slot `σ`, or at or below `fc_root`. -/
def ViableAtVote (ℓ : ACLabel (goldilocksSA sp FGP ro)) (e : Em sp FGP) (σ : Nat)
    (B : Blk sp.n FGP) :
    Prop :=
  B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame σ) ∨ ℓ.frame.Anc B ℓ.frame.fcRoot

/-- Every honest vote of slot `σ` at a cut before `i` extends `B`. -/
def EarlierVotesExtend (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (i σ : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x ∈ H, ∀ j < i, ∀ e, VoteAt tr x j e → e.msg.slot = σ → VoteExtends U e.msg B

/-- The update of slot `s` of `x` runs at cut `i`: `x`'s tick at `t_s + 6Δ`, joined. -/
def UpdateAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) :
    Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .tick ∧ tr.time i = sp.ts s + 6 * sp.Δ ∧
    joined sp (tr.state x i) (tr.time i)

/-- **The result of an update** (A1.8's origin): the update of slot `s` of `x` at cut `i`
returns `C ≠ ⊥` (fast, slow, vetoed or not); `CV` are the votes it counts for `C`. -/
def ResultAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat) (C : Blk sp.n FGP)
    (CV : Set (Vote sp.n)) : Prop :=
  ∃ ℓ, UpdateAt tr x i s ℓ ∧ getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
    CV = fastCounted sp (tr.state x i) ℓ.frame s C

/-- **A fast lock written by the fast test** of the update of slot `s` at cut `i` of `x`, on the
block `B` the test selects (vetoed or not; over the path blocks no live lock vetoes), with the
counted votes `CV` (the counted validators are at least half of the committee). -/
def FastUpdateAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP)
    (CV : Set (Vote sp.n)) : Prop :=
  ∃ ℓ C, UpdateAt tr x i s ℓ ∧ getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
    deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
      ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
      FastTest sp (tr.state x i) ℓ.frame s X} = some B ∧
    CV = fastCounted sp (tr.state x i) ℓ.frame s B

/-- The states at which the call of `x` at cut `i` (label `ℓ`) runs the optimistic check: after
the admission of an `on_message` vote, after the receipt of an `on_block` block, and after the
admission of each own vote. -/
def OptimisticPoint (tr : SATrace sp FGP ro) (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) (A : SAState sp.n) : Prop :=
  tr.CallAt x i ℓ ∧
    ((∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state x i) (tr.time i) m) ∨
     (∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state x i) (tr.time i) B) ∨
     (∃ e ∈ ℓ.emits, A = admitVote sp e.readPoint (tr.time i) e.msg))

/-- **A fast lock written by an optimistic confirmation** of slot `s` at cut `i` of `x`, on the
block `B` it selects, with the counted votes `CV` (its slot-`s` pool votes whose head extends
`B`, equivocators included; at least three quarters of the committee as validators). -/
def OptimisticLockAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP)
    (CV : Set (Vote sp.n)) : Prop :=
  ∃ ℓ A, OptimisticPoint tr x i ℓ A ∧ sp.slot (tr.time i) = s ∧
    optimisticSelect sp A ℓ.frame (tr.time i) = some B ∧
    CV = {v | v ∈ A.pool s ∧ AncR ℓ.frame B v.head}

/-- A fast lock of slot `s` on `B` with counted votes `CV`, written at cut `i` of `x`, by either
origin. -/
def FastLockAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP)
    (CV : Set (Vote sp.n)) : Prop :=
  FastUpdateAt tr x i s B CV ∨ OptimisticLockAt tr x i s B CV

/-- `ac_to_fg` at cut `i` of `x` returns `C`. -/
def ToFGAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksSA sp FGP ro))
    (C : Blk sp.n FGP) : Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .toFG ∧ (acToFG sp (tr.state x i) ℓ.frame (tr.time i)).2 = some C

/-- `ac_proposal` at cut `i` of `x` returns a proposal with payload `p`. -/
def ProposalAt (tr : SATrace sp FGP ro) (x : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro))
    (p : Payload sp.n) : Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .proposal ∧
    ∃ d, (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, p)

/-- The blocks of the frames of the honest nodes' calls. -/
def HonestFrameBlock (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (B : Blk sp.n FGP) : Prop :=
  ∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ B ∈ ℓ.frame.tree

/-- **Honest objects**: the run facts about honest signers over an AC trace (unforgeable vote
and block signatures; the slot proposer, supplied by the run law `LocalRun.proposerCredential`,
not by FG acceptance). -/
structure HonestObjects (selectedProposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop where
  /-- A vote of an honest validator in an honest node's pool before cut `i` was emitted by that
  validator's node at an earlier cut. -/
  pool_vote : ∀ y ∈ H, ∀ i σ, ∀ v ∈ (tr.state y i).pool σ, v.val ∈ H →
    ∃ j < i, ∃ e, VoteAt tr v.val j e ∧ e.msg = v
  /-- A vote of an honest validator that an honest node receives (an `on_message` call at cut
  `i`) was emitted by that validator's node at an earlier cut. -/
  message_vote : ∀ y ∈ H, ∀ i ℓ v, tr.CallAt y i ℓ → ℓ.call = .message v → v.val ∈ H →
    ∃ j < i, ∃ e, VoteAt tr v.val j e ∧ e.msg = v
  /-- A vote of an honest validator carried by a block of an honest node's frame at cut `i` was
  emitted by that validator's node at an earlier cut. -/
  carried_vote : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ∀ B ∈ ℓ.frame.tree, ∀ v ∈ blockVotes B,
    v.val ∈ H → ∃ j < i, ∃ e, VoteAt tr v.val j e ∧ e.msg = v
  /-- Every block of an honest frame other than genesis has its slot's proposer. -/
  proposer : ∀ B, HonestFrameBlock tr H B → B.root ≠ sp.genesisRoot →
    B.proposer = selectedProposer B.slot
  /-- An honest proposer has at most one block per slot in the honest frames. -/
  one_block : ∀ B B', HonestFrameBlock tr H B → HonestFrameBlock tr H B' → B.proposer ∈ H →
    B.proposer = B'.proposer → B.slot = B'.slot → B = B'

/-- An AC trace of the SA with its contract and the honest-object facts. -/
structure ACRun (selectedProposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) : Prop where
  /-- The AC trace contract. -/
  localRun : ACLocalRun (goldilocksSA sp FGP ro) H U tr
  /-- The honest-object facts. -/
  honest : HonestObjects selectedProposer tr H

end Consensus.Goldilocks.SA

end
