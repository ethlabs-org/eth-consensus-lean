module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Writes
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Restart

@[expose] public section

/-! # The evidence-release SA: state and node actions

The SA of the evidence-release rule: Goldilocks' SA (goldilocks-spec.tex §"Available chain:
Goldilocks", `Spec/SA`) with weighted locks. Every rule is the parent's except the unlock and the
lock writes.

* **State** (`WState`): the parent's state `ac`, the stored weighted locks `wlocks`, and the saved
  counts `counts` (the count of each slot's update, by root, for the slow-lock weights). Every
  handler keeps `ac.locks` equal to the forgotten image of `wlocks` (`withLocks`), so every rule
  that reads the locks (the anchor, the veto, the fast expiry, the FG candidates) reads the parent's
  locks of the stored set.
* **Unlock** (`unlockState`): `unlockW` (the parent's `unlock`, then the evidence release) on the
  stored weighted locks, at the same two places as the parent: before the vote of slot `s > 0`,
  against the slot-`(s − 1)` votes of the merged view, and in `ac_proposal`, against the whole
  slot-`(s − 1)` pool view.
* **Writes**: the update of slot `s` (`updateConfirmationW`) saves its count, then writes the
  parent's new locks with their weights (`updateLocksW`); the optimistic confirmation
  (`optimisticConfirmationW`) writes its lock with the optimistic count (`optimisticLocksW`). The
  other fields are the parent's update and optimistic confirmation.
* **Restart** (`acRestartW`): as the parent's (the locks and the record are kept, the rest is
  initial, the replay goes through `acOnBlockW`); the weighted locks are kept, and the saved counts
  are dropped with the saved results.

The emissions record the weighted state at their read point. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

/-- The evidence-release SA state: the parent's state, the stored weighted locks and the saved
counts. -/
structure WState (n : Nat) where
  /-- The parent's state; its `locks` are the forgotten image of `wlocks`. -/
  ac : SAState n
  /-- The stored weighted locks. -/
  wlocks : Set WLock
  /-- The saved counts: the count of the update of each slot, by root, saved at every update with
  or without a result (`0`: none since the last restart). -/
  counts : Int → Nat → Nat

/-- The initial state: the parent's, no weighted lock, no saved count. -/
def WState.initial {n : Nat} (g : Nat) : WState n where
  ac := SAState.initial g
  wlocks := ∅
  counts := fun _ _ => 0

variable {FGP : Type} (sp : SAParams)

/-- An emission of the evidence-release SA. -/
abbrev EmW (sp : SAParams) (FGP : Type) :=
  Emission sp.n FGP (Payload sp.n) (WState sp.n) (Vote sp.n)

/-- The state with the stored weighted locks `W`, and the parent's locks their forgotten image. -/
def withLocks (X : WState sp.n) (A : SAState sp.n) (W : Set WLock) : WState sp.n :=
  { X with ac := { A with locks := WLock.lock '' W }, wlocks := W }

/-- The unlock on the weighted state, against the slot-`s` votes of `V`. -/
noncomputable def unlockState (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : WState sp.n :=
  withLocks sp X X.ac (unlockW sp X.wlocks Φ t s V)

/-- `optimistic_confirmation` with the weighted write. -/
noncomputable def optimisticConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n :=
  withLocks sp X (optimisticConfirmation sp X.ac Φ t) (optimisticLocksW sp X.wlocks X.ac Φ t)

/-- `update_confirmation` of slot `s` with the weighted write: the slot's count is saved, then
the parent's new locks are written with their weights. -/
noncomputable def updateConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    WState sp.n :=
  { withLocks sp X (updateConfirmation sp X.ac Φ t s) (updateLocksW sp X.wlocks X.ac X.counts Φ t s)
    with counts := saveCount sp X.counts X.ac Φ s }

open Classical in
/-- `try_vote` at validator `self` on the weighted state: the parent's, with the weighted
unlock. -/
noncomputable def tryVoteW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t ∨ X.ac.votedSlot = s ∨ sp.ts s + sp.Δ < t then (X, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (X, [])
  else
    let V := mergedVoteView sp X.ac Φ s
    let X₁ := if 0 < s then unlockState sp X Φ t ((s : Int) - 1) V else X
    let dom := voteDomain sp X₁.ac Φ s
    let H := getHead sp X₁.ac Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let X₂ := { X₁ with ac := { X₁.ac with votedSlot := s } }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let X₃ := optimisticConfirmationW sp { X₂ with ac := admitVote sp X₂.ac t vote } Φ t
    (X₃, [{ msg := vote, readPoint := X₂,
            head := some { head := H, start := getAnchor sp X₁.ac Φ t, dom := dom } }])

/-- `ac_on_message` at validator `self` on the weighted state. -/
noncomputable def acOnMessageW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : WState sp.n × List (EmW sp FGP) :=
  tryVoteW sp self (optimisticConfirmationW sp { X with ac := admitVote sp X.ac t v } Φ t) Φ t

/-- `ac_on_block` at validator `self` on the weighted state. -/
noncomputable def acOnBlockW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : WState sp.n × List (EmW sp FGP) :=
  tryVoteW sp self (optimisticConfirmationW sp { X with ac := blockReceipt sp X.ac t B } Φ t) Φ t

open Classical in
/-- `ac_on_tick` at validator `self` on the weighted state. -/
noncomputable def acOnTickW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t then (X, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteW sp self X Φ t else (X, [])
    let X₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationW sp r.1 Φ t (s - 1)
      else r.1
    (X₂, r.2)

open Classical in
/-- `ac_proposal` on the weighted state: the parent's, with the weighted unlock against the
whole slot-`(s−1)` pool view. -/
noncomputable def acProposalW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp X.ac t then (X, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList X.ac Φ (s - 1) ⊤
    let V := View.ofLists p
    let X₁ := unlockState sp X Φ t (s - 1) V
    let H := getHead sp X₁.ac Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (X₁, some (⟨H, getAnchor sp X₁.ac Φ t, Φ.tree⟩, p))

/-- `ac_to_fg` on the weighted state: the parent's. -/
noncomputable def acToFGW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × Option (Blk sp.n FGP) :=
  let r := acToFG sp X.ac Φ t
  ({ X with ac := r.1 }, r.2)

/-- `ac_restart` at validator `self` on the weighted state, replaying in the order `ro`: the
parent's restart, with the weighted locks kept and the saved counts dropped. -/
noncomputable def acRestartW (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : WState sp.n × List (EmW sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  let X' : WState sp.n := { ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlockW sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (X', [])

end Consensus.Goldilocks.EvidenceRelease

end
