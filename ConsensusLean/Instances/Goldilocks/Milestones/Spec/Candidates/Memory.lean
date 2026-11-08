module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Actions

@[expose] public section

/-! # Lock memory and working rows: the Goldilocks family's state measures

The measures the Tier A lock-memory statements read (`Statements/Comparison/Cost`), fixed here
for the Goldilocks family and read off a node's own state at a time `t`:

* `lockMemory A t`: the locks the parent's state stores that are unexpired at `t`
  (`slot(t) ≤ expiry`, `Lock.LiveAt`), counted in `ℕ∞` (`encard`), so an infinite store is
  `⊤`, not `0`. It reads the store, not the frame: a stored unexpired lock whose block is not in
  the current frame is still held. An expired lock also stays in the store until the next
  write, but the readers of the locks do not see it: `live_locks(locks, Φ, t)` (`liveLocks`),
  their blocks, the conflict test, the fast expiry and the unlock depend on the unexpired ones
  only, and `liveLocks` is an image of them, so it is at most this count at every frame whose
  roots are injective on its tree (the sanity theorems, `Lemmas/Candidates/Memory`).
* `lockMemoryW X t`: the same for the weighted locks of evidence-release's state (the state it
  stores; its parent's `locks` are their forgotten image).
* `workingRows w A t`, `workingCountRows w X t` and their counts `savedMemory w A t`,
  `countMemory w X t`: the **working saved rows** at formation width `w`, the slots `j` with
  `slot(t) − max w 1 ≤ j` that hold a saved confirmation (`saved j ≠ ⊥`), and for
  evidence-release a nonzero saved count for some root. These are the rows a later update can
  still read: the update of slot `s` reads the saved results of `s − w < j < s` for its slow
  lock (`newLocksM`) and, for evidence-release, the saved counts of `s − max w 1 < j ≤ s` for its
  slow weight (`slowWeightW`), and the next update at `t` is of slot `slot(t) − 1` or later. The
  window has no upper end: that no row of a slot `≥ slot(t)` is saved is part of the claims
  (`Statements/Comparison/Cost`). They count rows, not stored bytes and not roots per row; the
  rows below the window are still in the state, and are not counted.

Definitions only. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- The locks of `L` unexpired at `t`. -/
def heldLocks (L : Set Lock) (t : Time) : Set Lock := {l | l ∈ L ∧ l.LiveAt sp t}

/-- **The lock memory** of a parent's state at `t`: its stored locks unexpired at `t`, in `ℕ∞`. -/
noncomputable def lockMemory {n : Nat} (A : SAState n) (t : Time) : ℕ∞ :=
  (heldLocks sp A.locks t).encard

/-- The working saved rows of a parent's state at formation width `w` at `t`: the slots `j` with
`slot(t) − max w 1 ≤ j` holding a saved confirmation. -/
def workingRows {n : Nat} (w : Nat) (A : SAState n) (t : Time) : Set Int :=
  {j | (sp.slot t : Int) - (max w 1 : Nat) ≤ j ∧ A.saved j ≠ none}

/-- **The working saved-row count** of a parent's state at formation width `w` at `t`, in
`ℕ∞`. -/
noncomputable def savedMemory {n : Nat} (w : Nat) (A : SAState n) (t : Time) : ℕ∞ :=
  (workingRows sp w A t).encard

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable (sp : SAParams)

/-- The weighted locks of `W` unexpired at `t`. -/
def heldWLocks (W : Set WLock) (t : Time) : Set WLock := {w | w ∈ W ∧ w.lock.LiveAt sp t}

/-- **The lock memory** of evidence-release's state at `t`: its stored weighted locks unexpired
at `t`, in `ℕ∞`. -/
noncomputable def lockMemoryW {n : Nat} (X : WState n) (t : Time) : ℕ∞ :=
  (heldWLocks sp X.wlocks t).encard

/-- The working saved-count rows of evidence-release's state at formation width `w` at `t`: the
slots `j` with `slot(t) − max w 1 ≤ j` holding a nonzero saved count for some root. -/
def workingCountRows {n : Nat} (w : Nat) (X : WState n) (t : Time) : Set Int :=
  {j | (sp.slot t : Int) - (max w 1 : Nat) ≤ j ∧ ∃ r, X.counts j r ≠ 0}

/-- **The working saved-count row count** of evidence-release's state at formation width `w` at
`t`, in rows (not roots per row), in `ℕ∞`. -/
noncomputable def countMemory {n : Nat} (w : Nat) (X : WState n) (t : Time) : ℕ∞ :=
  (workingCountRows sp w X t).encard

end Consensus.Goldilocks.EvidenceRelease

end
