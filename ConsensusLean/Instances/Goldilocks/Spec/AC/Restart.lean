module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions

@[expose] public section

/-! # Goldilocks AC: restart

goldilocks-spec.tex §"Joining and restart" (Figure "Goldilocks: restart"): a restart keeps the locks
and `latest_confirmed` and the installed voting permission, resets every other field, and
sets `restart_time` to the time of the restart. Genesis is stamped `⊥`, every other root in
`Φ.tree` is stamped with that time, and roots outside the tree are stamped `⊤`. No votes
are admitted or emitted. The retained `ReplayOrder` parameter does not affect the result. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

/-- `l` lists the blocks of `Φ.tree` other than genesis once each, every parent (in the list)
before its children. -/
def ParentOrderAt {n : Nat} (genesisRoot : Nat) (Φ : Frm n FGP)
    (l : List (Blk n FGP)) : Prop :=
  l.Nodup ∧ (∀ B, B ∈ l ↔ B ∈ Φ.tree ∧ B.root ≠ genesisRoot) ∧
    ∀ i j (hi : i < l.length) (hj : j < l.length), l[i].parent = some l[j].root → j < i

/-- A replay order for restarts: for each restart time and frame, a list of the blocks to replay,
which is a parent-order enumeration of the tree without genesis whenever one exists (at a
well-formed frame one does). The spec fixes only that parents come before their children; the
order of siblings is free (the replay only stamps blocks, so it does not change the state); the
AC stays parametric in the order and the statements quantify over every replay order. -/
structure ReplayOrderData (n genesisRoot : Nat) (FGP : Type) where
  /-- The blocks a restart at time `t` with frame `Φ` replays, in order. -/
  order : Time → Frm n FGP → List (Blk n FGP)
  /-- The order is a parent-order enumeration whenever there is one. -/
  parentOrder : ∀ t Φ, (∃ l, ParentOrderAt genesisRoot Φ l) →
    ParentOrderAt genesisRoot Φ (order t Φ)

/-- Replay order depends only on the validator count and genesis root. -/
abbrev ReplayOrder (sp : ACParams) (FGP : Type) := ReplayOrderData sp.n sp.genesisRoot FGP

set_option linter.unusedVariables false in
/-- `ac_restart(𝒜, Φ, t)`: bulk stamp the held non-genesis roots and emit nothing.
The retained `ro` and `self` parameters do not affect the result. -/
noncomputable def acRestart (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) := by
  classical
  exact ({ ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time)
    mayVote := A.mayVote,
    blockStamp := fun q => if q = sp.genesisRoot then ⊥
      else if InTree Φ q then ETime.of t else ⊤ }, [])

end Consensus.Goldilocks.AC

end
