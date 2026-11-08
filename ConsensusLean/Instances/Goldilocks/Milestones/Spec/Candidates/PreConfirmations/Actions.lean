module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.EvidenceRelease
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Instance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.Store
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.PreConfirmations.OneRelease

@[expose] public section

/-! # ½ pre-confirmations over a lock rule at a write mode: handlers and the SA

The PC layer (`Candidates/PreConfirmations/Store`) on the weighted-lock SA at a write mode `m`
with an unlock stage `E` and context `c` (`Candidates/EvidenceRelease`).

**The core skeleton with a start** (`tryVoteEMAt`, `acOnMessageEMAt`, `acOnBlockEMAt`,
`acOnTickEMAt`, `acProposalEAt`, `acRestartEMAt`, `stepEMAt`): the weighted handlers at mode `m`
with the block where each head walk starts given by `st` (a function of the state after the
unlock, the view and its slot) instead of the parent's anchor. With `st` the parent's anchor
(`parentStart`) they are the handlers of `Candidates/EvidenceRelease` (a lemma, by definition).
The PC adds no write mechanism to the core: every core write is one of the same update functions,
applied to the PC-selected vote. The writes are **not** in general equal to the core's at the
parent's start: a different start can give a different head of the own vote, which is admitted to
the pool before the optimistic confirmation of the same call, so the pool, the optimistic lock and
its weight, `latestConfirmed` and, at later updates, the saved rows and counts may differ.
`callStartPC` names the start of each call (the PC start of the store evaluated after the call's
record and before the walk, `walkStorePC`).

**The PC handlers** (state `PCState`: the core's weighted state and the PC store):
* `tryVotePC`: the core's `try_vote` with the walk from the PC start of the store evaluated at the
  call; when it votes, the evaluated store is kept, the own vote is recorded, and the acks of
  `ackSends` are emitted after the vote and admitted at once (`onAck`);
* `ac_on_message` of a vote: the vote is recorded, then the core's receipt and the PC `try_vote`;
  of an ack: `onAck` on the store, the core unchanged, nothing emitted;
* `ac_on_block`: the payload's votes (not the support entries) are recorded, then the core's
  receipt and the PC `try_vote`;
* `ac_on_tick`: the core's tick with the PC `try_vote`; after the update of slot `s − 1`, the ack
  decision of that slot (`decideAck`) on the store;
* `ac_proposal`: the core's proposal with the walk from the PC start, keeping the evaluated store;
* `ac_to_fg`: the core's, the store unchanged;
* `ac_head`, `ac_confirmed`: the core's with the walk from the PC start of the store evaluated at
  the read (not kept);
* `ac_restart`: the core's restart (locks, weights and record kept) with an empty store, replaying
  through the PC `ac_on_block`.

**The SA** `preConfSAM sp E c m FGP ro`, generic in the stage. Its two named variants at
`slowOnly k true` are `halfPCEvidenceSA` (evidence-release's stage) and `halfPCOneReleaseSA` (the
one release, `oneReleaseStage`). Neither is a full candidate: the clean-view fast path is not
modelled. Definitions only. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable {FGP : Type} (sp : SAParams)

/-- The state: the core's weighted state and the PC store. -/
structure PCState (n : Nat) where
  /-- The core's weighted state. -/
  core : WState n
  /-- The PC store. -/
  store : PCStore n

/-- The initial state: the core's and the empty store. -/
def PCState.initial {n : Nat} (g : Nat) : PCState n := ⟨WState.initial g, PCStore.empty⟩

/-- The messages: votes and acks. -/
abbrev PCMsg (n : Nat) := Vote n ⊕ Ack n

/-- An emission of the PC SA. -/
abbrev EmPC (sp : SAParams) (FGP : Type) :=
  Emission sp.n FGP (Payload sp.n) (PCState sp.n) (PCMsg sp.n)

/-- A core emission with the store `P` at its read point. -/
def liftEm (P : PCStore sp.n) (e : EmW sp FGP) : EmPC sp FGP :=
  ⟨.inl e.msg, ⟨e.readPoint, P⟩, e.head⟩

/-- A start function: where a head walk starts, from the state after the unlock, the view and its
slot. -/
abbrev StartFn (sp : SAParams) (FGP : Type) := SAState sp.n → View sp.n → Int → Blk sp.n FGP

/-- The parent's start: the parent's anchor. -/
noncomputable def parentStart (Φ : Frm sp.n FGP) (t : Time) : StartFn sp FGP :=
  fun A _ _ => getAnchor sp A Φ t

/-- The PC start of the store `P`. -/
noncomputable def pcStartFn (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) : StartFn sp FGP :=
  pcStart sp P Φ t

section Core

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) (m : WriteMode)

open Classical in
/-- `try_vote` at mode `m` with the walk from `st` (`tryVoteEM` with the start given). -/
noncomputable def tryVoteEMAt (st : StartFn sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t ∨ X.ac.votedSlot = s ∨ sp.ts s + sp.Δ < t then (X, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (X, [])
  else
    let V := mergedVoteView sp X.ac Φ s
    let X₁ := if 0 < s then unlockStateE sp E c X Φ t ((s : Int) - 1) V else X
    let dom := voteDomain sp X₁.ac Φ s
    let a := st X₁.ac V ((s : Int) - 1)
    let H := headFrom sp a Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let X₂ := { X₁ with ac := { X₁.ac with votedSlot := s } }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let X₃ := optimisticConfirmationWM sp m { X₂ with ac := admitVote sp X₂.ac t vote } Φ t
    (X₃, [{ msg := vote, readPoint := X₂, head := some { head := H, start := a, dom := dom } }])

/-- `ac_on_message` of a vote at mode `m` with the walk from `st`. -/
noncomputable def acOnMessageEMAt (st : StartFn sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) : WState sp.n × List (EmW sp FGP) :=
  tryVoteEMAt sp E c m st self
    (optimisticConfirmationWM sp m { X with ac := admitVote sp X.ac t v } Φ t) Φ t

/-- `ac_on_block` at mode `m` with the walk from `st`. -/
noncomputable def acOnBlockEMAt (st : StartFn sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) : WState sp.n × List (EmW sp FGP) :=
  tryVoteEMAt sp E c m st self
    (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t) Φ t

open Classical in
/-- `ac_on_tick` at mode `m` with the walk from `st`. -/
noncomputable def acOnTickEMAt (st : StartFn sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : WState sp.n × List (EmW sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.ac t then (X, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteEMAt sp E c m st self X Φ t else (X, [])
    let X₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationWM sp m r.1 Φ t (s - 1)
      else r.1
    (X₂, r.2)

open Classical in
/-- `ac_proposal` with the walk from `st` (`acProposalE` with the start given). -/
noncomputable def acProposalEAt (st : StartFn sp FGP) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : WState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp X.ac t then (X, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList X.ac Φ (s - 1) ⊤
    let V := View.ofLists p
    let X₁ := unlockStateE sp E c X Φ t (s - 1) V
    let a := st X₁.ac V (s - 1)
    let H := headFrom sp a Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (X₁, some (⟨H, a, Φ.tree⟩, p))

/-- `ac_restart` at mode `m` with the walk of each replayed vote from `st` (`acRestartEM` with the
start given). -/
noncomputable def acRestartEMAt (st : StartFn sp FGP) (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) : WState sp.n × List (EmW sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  let X' : WState sp.n := { ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlockEMAt sp E c m st self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (X', [])

/-- A call of the core at mode `m` with the walk from `st`, on the parent's calls. -/
noncomputable def stepEMAt (ro : ReplayOrder sp FGP) (st : StartFn sp FGP) (self : Fin sp.n)
    (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → WState sp.n × List (EmW sp FGP)
  | .tick => acOnTickEMAt sp E c m st self X Φ t
  | .proposal => ((acProposalEAt sp E c st X Φ t).1, [])
  | .toFG => ((acToFGW sp X Φ t).1, [])
  | .message v => acOnMessageEMAt sp E c m st self X Φ t v
  | .block B => acOnBlockEMAt sp E c m st self X Φ t B
  | .restart => acRestartEMAt sp E c m st ro self X Φ t

end Core

section PC

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) (m : WriteMode)

open Classical in
/-- The PC `try_vote` at `self`: the core's with the walk from the PC start of the store evaluated
at the call. When it votes (its voted slot becomes the current slot), the evaluated store is kept,
the own vote is recorded, and the acks of `ackSends` follow the vote and are admitted at once. -/
noncomputable def tryVotePC (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    PCState sp.n × List (EmPC sp FGP) :=
  let s := sp.slot t
  let Q := refresh sp X.store Φ t
  let r := tryVoteEMAt sp E c m (pcStartFn sp Q Φ t) self X.core Φ t
  if X.core.ac.votedSlot ≠ s ∧ r.1.ac.votedSlot = s then
    let Q₁ := recordVotes sp Q t (r.2.map Emission.msg)
    let as := ackSends sp Q self s
    let Q₂ := as.foldl (fun P a => onAck sp P t a) Q₁
    (⟨r.1, Q₂⟩, r.2.map (liftEm sp Q) ++ as.map fun a => ⟨.inr a, ⟨r.1, Q₂⟩, none⟩)
  else (⟨r.1, X.store⟩, r.2.map (liftEm sp X.store))

/-- The PC `ac_on_message`: a vote is recorded, then the core's receipt (admission and the
optimistic confirmation at mode `m`) and the PC `try_vote`; an ack goes to `onAck`, and the core
is unchanged. -/
noncomputable def acOnMessagePC (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : PCMsg sp.n → PCState sp.n × List (EmPC sp FGP)
  | .inl v => tryVotePC sp E c m self
      ⟨optimisticConfirmationWM sp m { X.core with ac := admitVote sp X.core.ac t v } Φ t,
        recordVote sp X.store t v⟩ Φ t
  | .inr a => (⟨X.core, onAck sp X.store t a⟩, [])

/-- The PC `ac_on_block`: the payload's votes are recorded, then the core's receipt and the PC
`try_vote`. -/
noncomputable def acOnBlockPC (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : PCState sp.n × List (EmPC sp FGP) :=
  tryVotePC sp E c m self
    ⟨optimisticConfirmationWM sp m { X.core with ac := blockReceipt sp X.core.ac t B } Φ t,
      recordVotes sp X.store t (blockVotes B)⟩ Φ t

open Classical in
/-- The PC `ac_on_tick`: the core's tick with the PC `try_vote`, and after the update of slot
`s − 1` the ack decision of that slot. -/
noncomputable def acOnTickPC (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    PCState sp.n × List (EmPC sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp X.core.ac t then (X, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVotePC sp E c m self X Φ t else (X, [])
    if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then
      let X₂ := updateConfirmationWM sp m r.1.core Φ t (s - 1)
      (⟨X₂, decideAck sp r.1.store X₂.ac Φ t (s - 1)⟩, r.2)
    else r

open Classical in
/-- The PC `ac_proposal`: the core's with the walk from the PC start of the evaluated store, which
is kept. -/
noncomputable def acProposalPC (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    PCState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp X.core.ac t then (X, none)
  else
    let Q := refresh sp X.store Φ t
    let r := acProposalEAt sp E c (pcStartFn sp Q Φ t) X.core Φ t
    (⟨r.1, Q⟩, r.2)

/-- The PC `ac_to_fg`: the core's; the store is unchanged. -/
noncomputable def acToFGPC (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    PCState sp.n × Option (Blk sp.n FGP) :=
  let r := acToFGW sp X.core Φ t
  (⟨r.1, X.store⟩, r.2)

/-- The PC `ac_head`: the walk of the full viable tree with the latest view, from the PC start of
the store evaluated at the read. -/
noncomputable def acHeadPC (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  let V := latestView sp X.core.ac Φ t
  headFrom sp (pcStart sp (refresh sp X.store Φ t) Φ t X.core.ac V.1 V.2) Φ t
    (Φ.viableTree Φ.tree) V.1 V.2

open Classical in
/-- The PC `ac_confirmed`: the parent's, with the PC head. -/
noncomputable def acConfirmedPC (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  let C := (lookup Φ X.core.ac.latestConfirmed).getD Φ.F
  let H := acHeadPC sp X Φ t
  (deepest Φ {Y | Y ∈ Φ.tree ∧ Φ.Anc Y C ∧ Φ.Anc Y H}).getD Φ.F

/-- The PC `ac_restart` at `self`, replaying in the order `ro`: the core's restart with an empty
store, replaying through the PC `ac_on_block`. -/
noncomputable def acRestartPC (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : PCState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : PCState sp.n × List (EmPC sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.core.ac.locks, latestConfirmed := X.core.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  let X' : PCState sp.n := ⟨{ ac := A', wlocks := X.core.wlocks, counts := fun _ _ => 0 },
    PCStore.empty⟩
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlockPC sp E c m self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (X', [])

/-- The store a walking call reads its start from: the store evaluated at the call after the
call's record (the received vote, or the accepted block's payload votes) and before the walk. -/
noncomputable def walkStorePC {ro : ReplayOrder sp FGP} (X : PCState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksSA sp FGP ro).Call → PCStore sp.n
  | .message v => refresh sp (recordVote sp X.store t v) Φ t
  | .block B => refresh sp (recordVotes sp X.store t (blockVotes B)) Φ t
  | _ => refresh sp X.store Φ t

/-- The start of the walks of a call: the PC start of `walkStorePC` for the walking calls; the
parent's anchor for a restart (whose replay runs on an emptied store, with no key). -/
noncomputable def callStartPC {ro : ReplayOrder sp FGP} (X : PCState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksSA sp FGP ro).Call → StartFn sp FGP
  | .restart => parentStart sp Φ t
  | k => pcStartFn sp (walkStorePC sp X Φ t k) Φ t

end PC

/-- **The ½-PC SA** over the weighted-lock core at mode `m` with the unlock stage `E` and context
`c`, with the restart replay order `ro`. -/
@[reducible] noncomputable def preConfSAM {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)
    (m : WriteMode) (FGP : Type) (ro : ReplayOrder sp FGP) : ACInterface sp.toParams FGP where
  State := PCState sp.n
  Msg := PCMsg sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun X msg => match msg with
    | .inl v => v ∈ X.core.ac.pool v.slot
    | .inr a => a.val ∈ X.store.acks a.slot a.target a.j
  genesisPayload := ([], [])
  initial := PCState.initial sp.genesisRoot
  onMessage := acOnMessagePC sp E c m
  onBlock := acOnBlockPC sp E c m
  onTick := acOnTickPC sp E c m
  proposal := acProposalPC sp E c
  toFG := acToFGPC sp
  confirmed := acConfirmedPC sp
  head := acHeadPC sp
  restart := acRestartPC sp E c m ro

/-- The ½-PC layer on the slow-only core with the optimistic lock (`slowOnly k true`) and
evidence-release's stage. -/
@[reducible] noncomputable def halfPCEvidenceSA (FGP : Type) (ro : ReplayOrder sp FGP) :
    ACInterface sp.toParams FGP :=
  preConfSAM sp (evidenceStage sp) () (WriteMode.slowOnly sp.k true) FGP ro

/-- The ½-PC layer on the slow-only core with the optimistic lock (`slowOnly k true`) and the one
release (`oneReleaseStage`). -/
@[reducible] noncomputable def halfPCOneReleaseSA (FGP : Type) (ro : ReplayOrder sp FGP) :
    ACInterface sp.toParams FGP :=
  preConfSAM sp (oneReleaseStage sp) () (WriteMode.slowOnly sp.k true) FGP ro

end Consensus.Goldilocks.PreConfirmations

end
