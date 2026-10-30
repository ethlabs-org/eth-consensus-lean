module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions

@[expose] public section

/-! # Goldilocks SA: restart

fgsa-spec.tex §"Joining and restart" (Figure "Goldilocks: restart"): a restart keeps the locks
and `latest_confirmed`, resets every other field, sets `restart_time` to the time of the
restart, and calls `ac_on_block` at that time for every block of `Φ.tree` other than genesis,
in parent order. The spec does not fix the order of siblings, which matters (with three or more
votes of one validator on sibling blocks, the order decides which two pass the cap, and the
pool order); so the restart takes the order as a parameter (`ReplayOrder`), and the SA and its
statements are parametric in it (fradamt-agent/goldilocks#26). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- `l` lists the blocks of `Φ.tree` other than genesis once each, every parent (in the list)
before its children. -/
def ParentOrder (Φ : Frm sp.n FGP) (l : List (Blk sp.n FGP)) : Prop :=
  l.Nodup ∧ (∀ B, B ∈ l ↔ B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) ∧
    ∀ i j (hi : i < l.length) (hj : j < l.length), l[i].parent = some l[j].root → j < i

/-- A replay order for restarts: for each restart time and frame, a list of the blocks to replay,
which is a parent-order enumeration of the tree without genesis whenever one exists (at a
well-formed frame one does). The spec fixes only that parents come before their children; the
order of siblings is free and matters (with three or more votes of one validator on sibling
blocks it decides which two pass the two-vote cap, and the pool order), so the SA is
parametric in the order and the statements quantify over every replay order. -/
structure ReplayOrder (sp : SAParams) (FGP : Type) where
  /-- The blocks a restart at time `t` with frame `Φ` replays, in order. -/
  order : Time → Frm sp.n FGP → List (Blk sp.n FGP)
  /-- The order is a parent-order enumeration whenever there is one. -/
  parentOrder : ∀ t Φ, (∃ l, ParentOrder sp Φ l) → ParentOrder sp Φ (order t Φ)

open Classical in
/-- One replay order: a chosen parent-order enumeration (`[]` if there is none). -/
noncomputable def ReplayOrder.choice : ReplayOrder sp FGP where
  order := fun _ Φ => if h : ∃ l, ParentOrder sp Φ l then h.choose else []
  parentOrder := fun _ Φ h => by simp only [h, ↓reduceDIte]; exact h.choose_spec

/-- `ac_restart(𝒜, Φ, t)` at validator `self`, replaying in the order `ro`: the replay's
emissions are returned (there are none: the node is not joined at `t`, claims A0.7). -/
noncomputable def acRestart (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time) }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlock sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (A', [])

end Consensus.Goldilocks.SA

end
