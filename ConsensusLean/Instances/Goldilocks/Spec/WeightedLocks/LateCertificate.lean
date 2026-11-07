module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Actions

@[expose] public section

/-! # The late-certificate SA: evidence-release with an arrival archive

The SA of the late-certificate rule: evidence-release's SA (`WeightedLocks.Actions`) with an
archive of received votes in the state and one more stage in the unlock. Every rule is
evidence-release's except these:

* **The archive** (`Archive`, `archiveRecord`): every vote the node receives (on its own, in a
  block's payload, or its own vote) of a slot that has begun (`x.slot ≤ slot(t)`), with the time it
  first received it so, at most two distinct per validator and slot (the pool's cap; in the pool's
  window the archive and the pool hold the same votes). A vote of a
  future slot is refused, as the pool refuses it, and is not archived; received again once its slot
  has begun, that receipt is its first. The committee of every slot is `V` (`SA.State`), so the
  committee test holds by typing. The pool and its admission window are unchanged; a vote too old
  for the pool is held in the archive only. The archive is volatile: a restart drops it.
* **Formation slots** (`firstSlot`): the first slot `a` of a lock's formation is read off the
  stored lock: its own slot `j` for a fast or optimistic lock, `j − k + 1` for a slow lock (its `k`
  saved confirmations, the window of its weight). No step changes `j` or the fast bit, so no step
  changes `a`.
* **The late certificate** (`lateSet`, `HasCert`): for a slot `i` and a block `Y`, the validators
  with an archived slot-`i` vote first received at or after `t_i + 2Δ` whose head is a block of the
  tree of slot at most `i` that does not extend `Y` (each validator once); slot `i` has a
  certificate when some archived slot-`i` vote is late and resolved so.
* **The stage** (`lateTarget`, `certStageW`): after evidence-release's release, on the same call,
  a lock held since its formation began (`restart_time ≤ t_a`, `Eligible`) moves on to the deepest
  block `Y` of the tree at or below the release's target whose late certificate is below the lock's
  weight at `Y` for every formation slot with a certificate (`CertPass`), or to `Φ.F`; any other
  lock keeps its place. The stage reads the archive's first-receipt times and the time of the last
  restart (`CertCtx`, `certCtx`).
* **Handlers.** A receipt archives the vote (or the block's payload votes) before
  evidence-release's handler runs with the candidate's stage, reading the archive so far; the votes
  the handler emits are archived after it. The restart drops the archive, replays as
  evidence-release's restart does with the candidate's stage, and archives the replayed blocks'
  payload votes at the restart's time. The replay does not unlock: its state's restart time is
  `t > t_{slot(t) − 1}`, so the node is not joined. Were it to, a lock it could move is of a slot
  below `slot(t) − 1`, so its formation began before the restart and the stage keeps it.

**One difference from evidence-release's interface**: `holdsMsg` also holds the archived votes.
A vote too old for the pool that the node archives is accepted, so it is forwarded once like every
accepted object; evidence-release holds only its pool. This includes a vote that arrived only in a
block's payload, which the rule forwards only with the block, as the parent's interface holds the
payload votes its pool admits. Holding it strengthens what a run-level delivery premise asks:
the trace's `SyncAC` then asks every honest node to process the vote as a message
(`ACTrace.ProcessAt`: a message call or the node's own emission), which the relay of the block
does not supply, also in the trivial frame. No trace refinement to the rule's forwarding and no
read equivalence is proved. The lemmas about this SA do not use `SyncAC`; a transfer of a
run-level route to it needs a bridge for this difference or a cleared source-aware forwarding.

The emissions record the state at their read point, with the archive as it stood when the
handler ran. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {FGP : Type} (sp : SAParams)

/-- The archive: the votes the node has received of a slot that had begun, each with the time it
first received it so (at most two distinct per validator and slot), in the order of receipt. -/
abbrev Archive (n : Nat) := List (Vote n × Time)

/-- The first-receipt time of an archived vote (`none`: not archived). -/
def Archive.arrival {n : Nat} (arr : Archive n) (x : Vote n) : Option Time :=
  (arr.find? fun p => p.1 = x).map Prod.snd

/-- A receipt of `x` at `t`: archived with time `t` unless it is already archived, its slot has not
begun (`slot(t) < x.slot`: refused, as the pool refuses it), or the archive holds two distinct
votes of its validator for its slot. -/
def archiveRecord (arr : Archive sp.n) (t : Time) (x : Vote sp.n) : Archive sp.n :=
  if x ∈ arr.map Prod.fst ∨ sp.slot t < x.slot ∨
      2 ≤ (arr.filter fun p => p.1.val = x.val ∧ p.1.slot = x.slot).length then arr
  else arr ++ [(x, t)]

/-- The receipts of a list of votes at `t`, in order. -/
def archiveAll (arr : Archive sp.n) (t : Time) (vs : List (Vote sp.n)) : Archive sp.n :=
  vs.foldl (fun a v => archiveRecord sp a t v) arr

/-- The arrival record the stage reads: the first-receipt time of each archived vote, and the time
of the latest restart. -/
structure CertCtx (n : Nat) where
  /-- The first-receipt time of an archived vote (`none`: not archived). -/
  arrival : Vote n → Option Time
  /-- The time of the latest restart (`⊥`: none). -/
  restart : WithBot Time

/-- The late certificate of slot `i` against `Y`: the validators with an archived slot-`i` vote
first received at or after `t_i + 2Δ` whose head, a block of the tree of slot at most `i`, does not
extend `Y`. -/
def lateSet (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (i : Int) (Y : Blk sp.n FGP) :
    Set (Fin sp.n) :=
  {v | ∃ x τ, ctx.arrival x = some τ ∧ x.val = v ∧ (x.slot : Int) = i ∧
    sp.ts i + 2 * sp.Δ ≤ τ ∧ ∃ H ∈ Φ.tree, H.root = x.head ∧ (H.slot : Int) ≤ i ∧ ¬ Φ.Anc Y H}

/-- Slot `i` has a late certificate: an archived slot-`i` vote first received at or after
`t_i + 2Δ`, with its head a block of the tree of slot at most `i`. -/
def HasCert (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (i : Int) : Prop :=
  ∃ x τ, ctx.arrival x = some τ ∧ (x.slot : Int) = i ∧ sp.ts i + 2 * sp.Δ ≤ τ ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ (H.slot : Int) ≤ i

/-- The first slot of the formation of a lock written in slot `j`: `j` for a fast or optimistic
lock, `j − k + 1` for a slow lock. -/
def firstSlot (k : Nat) (l : Lock) : Int :=
  if l.fast then (l.slot : Int) else (l.slot : Int) - k + 1

/-- `Y` passes the late-certificate test for the weighted lock `w` with first formation slot `a`:
for every formation slot `i ∈ [a, j]` with a certificate, the certificate against `Y` is below the
lock's weight at `Y`. -/
def CertPass (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (a : Int) (w : WLock) (Y : Blk sp.n FGP) :
    Prop :=
  ∀ i : Int, a ≤ i → i ≤ w.lock.slot → HasCert sp ctx Φ i →
    (lateSet sp ctx Φ i Y).ncard < w.weight Y.root

/-- The node has held a lock with first formation slot `a` since its formation began: no restart
after `t_a`. -/
def Eligible (ctx : CertCtx sp.n) (a : Int) : Prop :=
  ctx.restart ≤ ((sp.ts a : Time) : WithBot Time)

open Classical in
/-- Where the stage moves `w` (first formation slot `a`) from `T`: for an eligible lock the deepest
block of the tree at or below `T` that passes, or `Φ.F`; any other lock stays at `T`. -/
noncomputable def lateTarget (ctx : CertCtx sp.n) (Φ : Frm sp.n FGP) (a : Int) (w : WLock)
    (T : Blk sp.n FGP) : Blk sp.n FGP :=
  if Eligible sp ctx a then
    (deepest Φ {Y | Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ CertPass sp ctx Φ a w Y}).getD Φ.F
  else T

/-- The candidate's stage: evidence-release's release, then the late-certificate stage, with the
first formation slot read off the lock. -/
noncomputable def certStageW : UnlockStage sp wlockStore (CertCtx sp.n) where
  target ctx Φ V s w T :=
    lateTarget sp ctx Φ (firstSlot sp.k w.lock) w (evidenceTarget sp Φ V s w T)

/-- The late-certificate SA state: evidence-release's state and the archive. -/
structure CState (n : Nat) where
  /-- Evidence-release's state. -/
  er : WState n
  /-- The archive. -/
  arch : Archive n

/-- The initial state: evidence-release's, and an empty archive. -/
def CState.initial {n : Nat} (g : Nat) : CState n := ⟨WState.initial g, []⟩

/-- The stage's context read off the archive and the parent's state (its last restart). -/
def certCtx {n : Nat} (arr : Archive n) (A : SAState n) : CertCtx n :=
  ⟨arr.arrival, A.restartTime⟩

/-- An emission of the late-certificate SA. -/
abbrev EmC (sp : SAParams) (FGP : Type) :=
  Emission sp.n FGP (Payload sp.n) (CState sp.n) (Vote sp.n)

/-- An emission of evidence-release's handler with the archive `arr` at its read point. -/
def liftEm (arr : Archive sp.n) (e : EmW sp FGP) : EmC sp FGP :=
  ⟨e.msg, ⟨e.readPoint, arr⟩, e.head⟩

/-- `ac_on_message` at validator `self`: the receipt archives the vote, then evidence-release's
handler runs with the candidate's stage, reading the archive; the emitted votes are archived. -/
noncomputable def acOnMessageC (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : CState sp.n × List (EmC sp FGP) :=
  let arr := archiveRecord sp X.arch t v
  let r := acOnMessageE sp (certStageW sp) (certCtx arr X.er.ac) self X.er Φ t v
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- `ac_on_block` at validator `self`: the receipt archives the block's payload votes, then
evidence-release's handler runs with the candidate's stage; the emitted votes are archived. -/
noncomputable def acOnBlockC (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : CState sp.n × List (EmC sp FGP) :=
  let arr := archiveAll sp X.arch t (blockVotes B)
  let r := acOnBlockE sp (certStageW sp) (certCtx arr X.er.ac) self X.er Φ t B
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- `ac_on_tick` at validator `self`: evidence-release's, with the candidate's stage; the emitted
votes are archived. -/
noncomputable def acOnTickC (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    CState sp.n × List (EmC sp FGP) :=
  let r := acOnTickE sp (certStageW sp) (certCtx X.arch X.er.ac) self X.er Φ t
  (⟨r.1, archiveAll sp X.arch t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp X.arch))

/-- `ac_proposal`: evidence-release's, with the candidate's stage; the archive is kept. -/
noncomputable def acProposalC (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    CState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  let r := acProposalE sp (certStageW sp) (certCtx X.arch X.er.ac) X.er Φ t
  (⟨r.1, X.arch⟩, r.2)

/-- `ac_to_fg`: evidence-release's; the archive is kept. -/
noncomputable def acToFGC (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    CState sp.n × Option (Blk sp.n FGP) :=
  let r := acToFGW sp X.er Φ t
  (⟨r.1, X.arch⟩, r.2)

/-- `ac_restart` at validator `self`, replaying in the order `ro`: the archive is dropped,
evidence-release's restart replays with the candidate's stage (reading the dropped archive and the
restart at `t`), and the replayed blocks' payload votes and the emitted votes are archived at
`t`. -/
noncomputable def acRestartC (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : CState sp.n × List (EmC sp FGP) :=
  let arr := (ro.order t Φ).foldl (fun a B => archiveAll sp a t (blockVotes B)) []
  let r := acRestartE sp (certStageW sp) ⟨Archive.arrival [], (t : WithBot Time)⟩ ro self X.er Φ t
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- The late-certificate SA as an AC, with the restart replay order `ro`. Its messages, payload,
payload check, message check, genesis payload, confirmed tip and head are evidence-release's;
`holdsMsg` also holds the archived votes. -/
@[reducible] noncomputable def certRecoverySA (FGP : Type) (ro : ReplayOrder sp FGP) :
    ACInterface sp.toParams FGP where
  State := CState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun X v => v ∈ X.er.ac.pool v.slot ∨ v ∈ X.arch.map Prod.fst
  genesisPayload := ([], [])
  initial := CState.initial sp.genesisRoot
  onMessage := acOnMessageC sp
  onBlock := acOnBlockC sp
  onTick := acOnTickC sp
  proposal := acProposalC sp
  toFG := acToFGC sp
  confirmed := fun X => acConfirmed sp X.er.ac
  head := fun X => acHead sp X.er.ac
  restart := acRestartC sp ro

end Consensus.Goldilocks.LateCertificate

end
