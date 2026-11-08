module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation

@[expose] public section

/-! # Goldilocks lock rules: write modes

A lock rule of the Goldilocks family keeps the SA's confirmation machinery and changes which locks
it writes. A **write mode** fixes the three write choices:

* `fastArm`: whether the confirmation update of slot `s` writes the fast lock of its path (the
  deepest unvetoed block with half of the committee or more);
* `optimistic`: whether the optimistic confirmation of the current slot runs (its fast lock and its
  record);
* `width`: the formation width of the update's slow lock, which is written on the deepest unvetoed
  block of the path that the saved results of the previous `width − 1` slots extend.

The slow lock of slot `s` still lives through `s + k` and the fast expiry is `fastExpiry` at
every mode. The parent's writes are the mode `WriteMode.parent sp = ⟨true, true, k⟩`;
`WriteMode.slowOnly w opt` writes no fast lock at the update, with the optimistic write on or off.

`updateConfirmationM` and `optimisticConfirmationM` are written once, uniformly in the mode, from
the parent's selection primitives (`getConfirmation`, `FastTest`, `optimisticSelect`, `deepest`,
`addLocks`, `fastExpiry`, `updateLatestConfirmed`); neither calls `updateConfirmation` or
`optimisticConfirmation`, which are unchanged. That they agree with the parent's at the parent's
mode is a theorem (`Lemmas/AC/WriteMode`), and it certifies the parent's mode only: each other mode
is read back against the rule it models on its own. -/

namespace Consensus.Goldilocks.SA

/-- Which locks a lock rule writes: the update's regular fast arm, the optimistic confirmation
(its lock and its record), and the slow lock's formation width. -/
structure WriteMode where
  /-- The confirmation update writes its fast lock. -/
  fastArm : Bool
  /-- The optimistic confirmation runs. -/
  optimistic : Bool
  /-- The slow lock's formation width (the update of slot `s` reads the saved results of the
  slots `s − width + 1, …, s − 1`). -/
  width : Nat

/-- The parent's writes: both fast writes, and slow locks of width `k`. -/
def WriteMode.parent (sp : SAParams) : WriteMode := ⟨true, true, sp.k⟩

/-- Slow-only writes at width `w`: no fast lock at the update; the optimistic confirmation on when
`opt`. -/
def WriteMode.slowOnly (w : Nat) (opt : Bool) : WriteMode := ⟨false, opt, w⟩

variable {FGP : Type} (sp : SAParams)

open Classical in
/-- The new locks of the update of slot `s` at mode `m` whose result is `C`, as triples (block,
fast bit, expiry), reading the saved results `sv` and, for the fast expiry, the stored locks `L`:
the fast lock on the deepest block of the result's path that passes the fast test and conflicts
with no live lock, when `m.fastArm`; the slow lock on the deepest such block that the saved
results of the previous `m.width − 1` slots extend. The update reads its own saved results (with
`C` saved at `s`) and its own locks. -/
noncomputable def newLocksM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) (C : Blk sp.n FGP) (sv : Int → Option Nat) (L : Set Lock) :
    Set (Nat × Bool × Nat) :=
  let path := {B | B ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t B}
  let slow := fun B : Blk sp.n FGP => ∀ j : Int, (s : Int) - m.width < j → j < s →
    ∃ S ∈ Φ.tree, sv j = some S.root ∧ Φ.Anc B S
  let D := match m.fastArm with
    | true => deepest Φ {B | B ∈ path ∧ FastTest sp A Φ s B}
    | false => none
  let X := deepest Φ {B | B ∈ path ∧ slow B}
  {p | (∃ B, D = some B ∧ p = (B.root, true, fastExpiry sp L Φ t s)) ∨
    (∃ B, X = some B ∧ p = (B.root, false, s + sp.k))}

open Classical in
/-- `update_confirmation(𝒜, Φ, t, s)` at mode `m`: the result is saved (also when vetoed), the
record moves to it unless a live lock vetoes it, and the locks get `newLocksM`. -/
noncomputable def updateConfirmationM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : SAState sp.n :=
  let C := getConfirmation sp A Φ s
  let A₁ := { A with saved := Function.update A.saved s (C.map Block.root) }
  match C with
  | none => A₁
  | some C =>
    let A₂ := if conflictsWithLock sp A₁.locks Φ t C then A₁ else updateLatestConfirmed sp A₁ Φ C
    { A₂ with locks := addLocks sp A₂.locks Φ t s (newLocksM sp m A Φ t s C A₁.saved A₂.locks) }

/-- `optimistic_confirmation(𝒜, Φ, t)` at mode `m`: when `m.optimistic`, a fast lock of slot
`slot(t)` on the block of `optimisticSelect` and the record; otherwise nothing. -/
noncomputable def optimisticConfirmationM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : SAState sp.n :=
  match m.optimistic with
  | false => A
  | true =>
    match optimisticSelect sp A Φ t with
    | none => A
    | some B =>
      updateLatestConfirmed sp
        { A with locks := addLocks sp A.locks Φ t (sp.slot t)
                    {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))} } Φ B

end Consensus.Goldilocks.SA

end
