module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Views

@[expose] public section

/-! # Goldilocks SA: locks and unlocking

fgsa-spec.tex §"Locks" (Figure "Goldilocks: locks and unlocking"). A lock `(B, j, f)` is live at
`t` when `slot(t) ≤ j + k` and `B ∈ Φ.tree`; every rule reads the locks through `live_locks`,
which moves each live lock back to its viable ancestor (`Frame.viableAncestor`, the frame-level
definition of claims G0.4 (frame), which fgsa-spec §"Locks" also gives). The anchor is the
deepest live lock block or `fc_root`; a live lock vetoes a block that conflicts with its block;
`add_locks` returns the live locks of the stored set and the new locks together; `unlock`
against the slot-`s` votes of a view moves each live lock of a slot below `s` back to its
deepest ancestor (at or above `Φ.F`) with fewer than half of the committee as opponents, or to
`Φ.F`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- `live_locks(locks, Φ, t)`: the live locks, each moved back to its viable ancestor. -/
def liveLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) : Set Lock :=
  {l' | ∃ l ∈ L, ∃ B ∈ Φ.tree, B.root = l.block ∧ sp.slot t ≤ l.slot + sp.k ∧
    l' = ⟨(Φ.viableAncestor B).root, l.slot, l.fast⟩}

/-- The blocks of the live locks (the locked blocks are their ancestors). -/
def liveLockBlocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.tree ∧ ∃ l ∈ liveLocks sp L Φ t, l.block = B.root}

/-- `conflicts_with_lock(locks, Φ, t, C)`: `C` conflicts with the block of a live lock. -/
def conflictsWithLock (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (C : Blk sp.n FGP) : Prop :=
  ∃ B ∈ liveLockBlocks sp L Φ t, ¬ Compatible Φ.tree C B

/-- `get_anchor(𝒜, Φ, t)`: the deepest block of the live lock blocks and `fc_root`. -/
noncomputable def getAnchor (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  (deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})).getD Φ.fcRoot

/-- `add_locks(locks, Φ, t, s, N)`: the live locks of the stored set with the new locks
`(B, s, f)` for `(B, f) ∈ N` (blocks by root). -/
def addLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) (N : Set (Nat × Bool)) :
    Set Lock :=
  liveLocks sp (L ∪ {l | ∃ p ∈ N, l = ⟨p.1, s, p.2⟩}) Φ t

/-- The opponents of `B'` in a view against the slot-`s` votes: the equivocators of its votes
and the validators with a slot-`s` support vote whose head (in the tree) conflicts with `B'`. -/
def opponents (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B' : Blk sp.n FGP) : Set (Fin sp.n) :=
  equivocators V.votes ∪ {i | ∃ x ∈ V.support, x.val = i ∧ (x.slot : Int) = s ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ ¬ Compatible Φ.tree H B'}

/-- Where `unlock` moves a lock on `B` against the slot-`s` votes of `V`: the deepest `B'` of
the tree with `B' ⪯ B` and `2 · |opponents(B')| < |committee| = n`, or `Φ.F`. -/
noncomputable def unlockTarget (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B : Blk sp.n FGP) :
    Blk sp.n FGP :=
  (deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n}).getD Φ.F

/-- `unlock(locks, Φ, t, s, votes, support_votes)`: every live lock (moved back) of a slot below
`s` is moved to its `unlockTarget`; the locks of slot `s` or later keep their place; slots and
fast bits are kept; locks that are not live are dropped. -/
noncomputable def unlock (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n) :
    Set Lock :=
  {l' | ∃ l ∈ liveLocks sp L Φ t, ∃ B ∈ Φ.tree, B.root = l.block ∧
    l' = if (l.slot : Int) < s then ⟨(unlockTarget sp Φ V s B).root, l.slot, l.fast⟩ else l}

end Consensus.Goldilocks.SA

end
