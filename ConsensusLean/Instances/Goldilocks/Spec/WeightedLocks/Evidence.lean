module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Store

@[expose] public section

/-! # Weighted locks and the evidence release

The stored lock of the evidence-release rule keeps its weight: a lock `(B, j, f, e)` with the
root of the block it was written on (its origin) and its weight `W`, for each block root the
number of validators the confirmation that wrote it counted for that block (`0` off the chain of
the written block; the writes are in `WeightedLocks.Writes`). No step changes `W` or the origin:
a move changes only the block (`wlockStore`), so two writes with different weights are two locks,
even on the same block, slot, bit and expiry.

**Evidence.** In a view against the slot-`s` votes, the evidence against `Y` is the equivocators of
the view's votes and the validators with a slot-`s` support vote whose head (in the tree) does not
extend `Y` (`evidence`). Absent validators and unresolved votes count for nothing.

**The release** (`evidenceStage`, the stage after the parent's unlock): a lock of a slot below `s`
whose parent unlock target is `T` moves to the deepest block `Y ⪯ T` of the tree whose evidence is
below the lock's weight at `Y`, or to `Φ.F` when there is none (`evidenceTarget`). The candidate's
unlock is `unlockW`, the parent's `unlock` followed by this stage on the same view; the parent's
threshold, half of the committee as opponents, stays the first stage, so a lock is never above the
parent's. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable (sp : SAParams) {FGP : Type}

/-- A lock with its weight: the lock, the root of the block it was written on, and the weight by
block root. -/
structure WLock where
  /-- The lock as the parent stores it. -/
  lock : Lock
  /-- The root of the block the lock was written on. -/
  origin : Nat
  /-- The weight, by block root. -/
  weight : Nat → Nat

/-- The store of weighted locks: forgotten to the lock, moved by changing the lock's block (the
origin and the weight travel with it). -/
abbrev wlockStore : LockStore where
  Lk := WLock
  lock := WLock.lock
  withBlock w r := { w with lock := { w.lock with block := r } }

/-- `live_locks` on weighted locks. -/
def liveLocksW (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) : Set WLock :=
  wlockStore.liveLocks sp L Φ t

/-- The evidence against `Y` in a view against the slot-`s` votes: the equivocators of its votes
and the validators with a slot-`s` support vote whose head (in the tree) does not extend `Y`. -/
def evidence (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (Y : Blk sp.n FGP) : Set (Fin sp.n) :=
  equivocators V.votes ∪ {i | ∃ x ∈ V.support, x.val = i ∧ (x.slot : Int) = s ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ ¬ Φ.Anc Y H}

/-- The blocks the release may keep a lock of weight `w` on, at or below `T`: those whose
evidence is below the weight. -/
def keepable (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock) (T : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {Y | Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ (evidence sp Φ V s Y).ncard < w.weight Y.root}

/-- Where the release moves a lock of weight `w` from `T`: the deepest keepable block at or below
`T`, or `Φ.F`. -/
noncomputable def evidenceTarget (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (T : Blk sp.n FGP) : Blk sp.n FGP :=
  (deepest Φ (keepable sp Φ V s w T)).getD Φ.F

/-- The release as an unlock stage (no context). -/
noncomputable def evidenceStage : UnlockStage sp wlockStore Unit where
  target _ Φ V s w T := evidenceTarget sp Φ V s w T

/-- The candidate's `unlock` (`E ∘ unlock`): every live lock of a slot below `s` moves to the
evidence target of its parent unlock target; the others keep their place. -/
noncomputable def unlockW (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : Set WLock :=
  wlockStore.unlockWith sp (evidenceStage sp) () L Φ t s V

end Consensus.Goldilocks.EvidenceRelease

end
