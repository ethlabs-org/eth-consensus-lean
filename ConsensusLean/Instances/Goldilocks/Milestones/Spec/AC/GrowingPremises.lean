module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Growing

@[expose] public section

/-! # AC traces under growing faults: premises and honest objects

The AC premises and honest-object facts (`Spec/AC/Premises`, `Spec/AC/Events`) for a time-indexed
honest set `H`:

* `HonestFrameBlockAt`, `EarlierVotesExtendAt`, `Growing.Carry`: the frame blocks, votes and
  `Carry` premise of nodes honest at the cut read;
* `Growing.HonestObjects`: votes whose signer is honest at the reading cut were emitted by it;
  frame blocks carry their slot's proposer; and a proposer honest at both reading cuts has one
  block per slot in the frames read (a proposer compromised later can sign a second block of an
  earlier slot, and that block is excluded only while the proposer is honest);
* `Growing.ACRun`: `Growing.ACLocalRun` with `Growing.HonestObjects`. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams}

/-- The blocks of the frames of the calls of nodes honest at the call. -/
def HonestFrameBlockAt (tr : GTrace sp FGP) (H : Time → Set (Fin sp.n)) (B : Blk sp.n FGP) :
    Prop :=
  ∃ y i ℓ, y ∈ H (tr.time i) ∧ tr.CallAt y i ℓ ∧ B ∈ ℓ.frame.tree

/-- Every vote of slot `σ` cast before cut `i` by a node honest at its cast extends `B`. -/
def EarlierVotesExtendAt (tr : GTrace sp FGP) (H : Time → Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (i σ : Nat) (B : Blk sp.n FGP) : Prop :=
  ∀ x j, j < i → x ∈ H (tr.time j) → ∀ e, VoteAt tr x j e → e.msg.slot = σ → VoteExtends U e.msg B

namespace Growing

/-- **Honest objects under growing faults**: the run facts about signers honest at the reading
cut. -/
structure HonestObjects (selectedProposer : Nat → Fin sp.n)
    (tr : GTrace sp FGP) (H : Time → Set (Fin sp.n)) : Prop where
  /-- A vote whose validator is honest at cut `i`, in the pool of a node honest at cut `i`, was
  emitted by that validator's node at an earlier cut. -/
  pool_vote : ∀ y i σ, y ∈ H (tr.time i) → ∀ v ∈ (tr.state y i).pool σ, v.val ∈ H (tr.time i) →
    ∃ j < i, ∃ e, VoteAt tr v.val j e ∧ e.msg = v
  /-- A vote whose validator is honest at the receipt, received by a node honest then, was
  emitted by that validator's node at an earlier cut. -/
  message_vote : ∀ y i ℓ v, y ∈ H (tr.time i) → tr.CallAt y i ℓ → ℓ.call = .message v →
    v.val ∈ H (tr.time i) → ∃ j < i, ∃ e, VoteAt tr v.val j e ∧ e.msg = v
  /-- Every block of the frame of a node honest at the call, other than genesis, has its slot's
  proposer. -/
  proposer : ∀ B, HonestFrameBlockAt tr H B → B.root ≠ sp.genesisRoot →
    B.proposer = selectedProposer B.slot
  /-- A proposer honest at both reading cuts has at most one block per slot in the frames read at
  them. -/
  one_block : ∀ y i ℓ B y' i' ℓ' B', y ∈ H (tr.time i) → tr.CallAt y i ℓ → B ∈ ℓ.frame.tree →
    y' ∈ H (tr.time i') → tr.CallAt y' i' ℓ' → B' ∈ ℓ'.frame.tree →
    B.proposer ∈ H (max (tr.time i) (tr.time i')) → B.proposer = B'.proposer →
    B.slot = B'.slot → B = B'

/-- An AC trace of the AC with its contract, from the AC starts `ini`, and the honest-object
facts under growing faults. -/
structure ACRun (selectedProposer : Nat → Fin sp.n)
    (tr : GTrace sp FGP) (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (ini : Fin sp.n → ACState sp.n := fun _ => (goldilocksAC sp FGP).initial) : Prop where
  /-- The AC trace contract. -/
  localRun : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksAC sp FGP) H U tr ini
  /-- The honest-object facts. -/
  honest : HonestObjects selectedProposer tr H
  /-- The AC starts are starts up to the vote permission. -/
  vstart : ∀ y, VoteStart sp.genesisRoot (ini y)

end Growing

end Consensus.Goldilocks.AC

end
