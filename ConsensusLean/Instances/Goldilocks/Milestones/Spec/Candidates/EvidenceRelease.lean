module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.WeightedWrites
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Instance

@[expose] public section

/-! # The evidence-release SA at a write mode

The handlers of the weighted-lock SA (`Spec/WeightedLocks/Actions`) at a write mode `m`, written
once and uniformly in the mode, for an unlock stage `E` with context `c` as there: every handler is
evidence-release's except the writes, which are the mode's on the parent's state
(`updateConfirmationM`, `optimisticConfirmationM`) and on the weighted locks (`updateLocksWM`,
`optimisticLocksWM`, `Candidates/WeightedWrites`).

* `optimisticConfirmationWM`, `updateConfirmationWM`: the writes at mode `m` (the update saves its
  count first, at every mode);
* `tryVoteEM`, `acOnMessageEM`, `acOnBlockEM`, `acOnTickEM`, `acRestartEM`: the handlers that
  write; `ac_proposal` (`acProposalE`) and `ac_to_fg` (`acToFGW`) write nothing and are
  evidence-release's;
* `evidenceReleaseSAM`: the SA at mode `m`, at evidence-release's stage.

No definition tests whether the mode is the parent's; that the parent's mode gives
evidence-release's SA is a theorem (`Lemmas/Candidates/EvidenceRelease`). Definitions only. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {FGP : Type} (sp : SAParams)

/-- `optimistic_confirmation` at mode `m`, with the weighted write. -/
noncomputable def optimisticConfirmationWM (m : WriteMode) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : WState sp.n :=
  withLocks sp X (optimisticConfirmationM sp m X.ac Φ t) (optimisticLocksWM sp m X.wlocks X.ac Φ t)

/-- `update_confirmation` of slot `s` at mode `m`, with the weighted write: the slot's count is
saved, then the mode's new locks are written with their weights. -/
noncomputable def updateConfirmationWM (m : WriteMode) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : WState sp.n :=
  { withLocks sp X (updateConfirmationM sp m X.ac Φ t s)
      (updateLocksWM sp m X.wlocks X.ac X.counts Φ t s)
    with counts := saveCount sp X.counts X.ac Φ s }

section Generic

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) (m : WriteMode)

open Classical in
/-- `try_vote` at validator `self` at mode `m`: evidence-release's, with the mode's optimistic
write. -/
noncomputable def tryVoteEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t ∨ X.ac.votedSlot = s ∨ sp.ts s + sp.Δ < t then (X, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (X, [])
  else
    let V := mergedVoteView sp X.ac Φ s
    let X₁ := if 0 < s then unlockStateE sp E c X Φ t ((s : Int) - 1) V else X
    let dom := voteDomain sp X₁.ac Φ s
    let H := getHead sp X₁.ac Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let X₂ := { X₁ with ac := { X₁.ac with votedSlot := s } }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let X₃ := optimisticConfirmationWM sp m { X₂ with ac := admitVote sp X₂.ac t vote } Φ t
    (X₃, [{ msg := vote, readPoint := X₂,
            head := some { head := H, start := getAnchor sp X₁.ac Φ t, dom := dom } }])

/-- `ac_on_message` at validator `self` at mode `m`. -/
noncomputable def acOnMessageEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) : WState sp.n × List (EmW sp FGP) :=
  tryVoteEM sp E c m self
    (optimisticConfirmationWM sp m { X with ac := admitVote sp X.ac t v } Φ t) Φ t

/-- `ac_on_block` at validator `self` at mode `m`. -/
noncomputable def acOnBlockEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : WState sp.n × List (EmW sp FGP) :=
  tryVoteEM sp E c m self
    (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t) Φ t

open Classical in
/-- `ac_on_tick` at validator `self` at mode `m`. -/
noncomputable def acOnTickEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t then (X, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteEM sp E c m self X Φ t else (X, [])
    let X₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationWM sp m r.1 Φ t (s - 1)
      else r.1
    (X₂, r.2)

/-- `ac_restart` at validator `self` at mode `m`, replaying in the order `ro`: evidence-release's
restart, with the replay through `acOnBlockEM`. -/
noncomputable def acRestartEM (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : WState sp.n × List (EmW sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  let X' : WState sp.n := { ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlockEM sp E c m self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (X', [])

end Generic

/-- **The evidence-release SA at mode `m`**, with the restart replay order `ro`: the SA of
`evidenceReleaseSA` with the handlers at mode `m`, at evidence-release's stage. -/
@[reducible] noncomputable def evidenceReleaseSAM (m : WriteMode) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACInterface sp.toParams FGP where
  State := WState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun X v => v ∈ X.ac.pool v.slot
  genesisPayload := ([], [])
  initial := WState.initial sp.genesisRoot
  onMessage := acOnMessageEM sp (evidenceStage sp) () m
  onBlock := acOnBlockEM sp (evidenceStage sp) () m
  onTick := acOnTickEM sp (evidenceStage sp) () m
  proposal := acProposalW sp
  toFG := acToFGW sp
  confirmed := fun X => acConfirmed sp X.ac
  head := fun X => acHead sp X.ac
  restart := acRestartEM sp (evidenceStage sp) () m ro

end Consensus.Goldilocks.EvidenceRelease

end
