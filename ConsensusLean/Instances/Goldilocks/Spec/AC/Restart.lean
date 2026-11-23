module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions

@[expose] public section

/-! # Goldilocks AC: restart

goldilocks-spec.tex §"Joining and restart" (Figure "Goldilocks: restart"): a restart keeps the locks
and `latest_confirmed`, resets every other field, sets `restart_time` to the time of the
restart, and calls `ac_on_block` at that time for every block of `Φ.tree` other than genesis,
in parent order. The replay only stamps the blocks: a block's declared head votes are not
admitted, and the node is not joined at its restart time, so no check or vote runs. The spec
does not fix the order of siblings; the restart still takes the order as a parameter
(`ReplayOrder`), and the AC and its statements are parametric in it. -/

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

/-- `ac_restart(𝒜, Φ, t)` at validator `self`, replaying in the order `ro`: the replay's
emissions are returned (there are none: the node is not joined at `t`, claims A0.7). -/
noncomputable def acRestart (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) :=
  let A' : ACState sp.n := { ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time)
    mayVote := A.mayVote }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlock sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (A', [])

end Consensus.Goldilocks.AC

end
