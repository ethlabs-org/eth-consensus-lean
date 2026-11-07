module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.UpTo

@[expose] public section

/-! # Goldilocks runs under growing faults: the run model

The run model of `Spec/Run/Model` with a **time-indexed honest set** `H : Time → Set (Fin n)`:
`H t` holds the validators not compromised by `t`. Compromise is permanent, so `H` is antitone
(`Growing.LocalRun.antitone`), the milestone form of `EnvPoint.faultyAt_mono`. Every law reads
honesty at the time of the cut it constrains: a node honest at the time of a cut was honest at
every earlier cut, so its state before that cut is the result of honest steps. A node has no law
after its compromise; what its key signs from then on is adversarial input. Unforgeability reads
the signer's honesty at the processing time (the boundary of `Model.Run.Unforgeable`: a key
compromised by the delivery time signs anything, a genuine earlier object keeps its provenance).

The constant set is the special case `fun _ => H`: `Growing.LocalRun proposer dg (fun _ => H) sg
tr` is `Node.LocalRun proposer dg H sg tr` (`Growing.LocalRun.const_iff`, `Lemmas/Growing/Run`).

* `RunTrace.upTo tr d`: the prefix of a run trace through `d` (`Trace.upTo`).
* `RunTrace.HonestBlocksAt tr H`: the blocks of the trees that nodes hold at times at which they
  are honest (the reads made while honest; a later compromise removes nothing).
* `Growing.LocalRun`: the laws of `Node.LocalRun`, each at the time of its cut. -/

namespace Consensus.Goldilocks

variable {P : Params}

namespace RunTrace

variable {A : NodeAC P} (tr : RunTrace A)

/-- The prefix of a run trace through `d` (`Trace.upTo`), as a run trace. -/
abbrev upTo (d : Time) : RunTrace A := Trace.upTo tr d

/-- The blocks of the trees that nodes hold while honest: `B` is in the tree of `y` before cut
`i`, every cut before `i` is at a time `≤ t`, `t ≥ 0`, and `y` is honest at `t` (so a node faulty
from the start contributes nothing, not even its initial tree). -/
def HonestBlocksAt (H : Time → Set (Fin P.n)) : Set A.Blk :=
  {B | ∃ y i t, 0 ≤ t ∧ (∀ k < i, tr.time k ≤ t) ∧ y ∈ H t ∧ B ∈ (tr.state y i).fg.tree}

end RunTrace

namespace Growing

/-- **A run of the node under growing faults**, for the time-indexed honest set `H`, the digest
`dg` and the AC message signer map `sg`: the laws of `Node.LocalRun`, each for the nodes honest at
the time of the cut (or the time) it constrains. -/
structure LocalRun {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A) : Prop where
  /-- Compromise is permanent: a validator honest at a time was honest at every earlier time. -/
  antitone : Antitone H
  /-- Each node honest at time `0` starts from the initial node state. -/
  init : ∀ y ∈ H 0, tr.init y = Node.init A
  /-- Every labelled cut of a node honest at its time lies in the group of a top-level event. -/
  grouped : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    ∃ j e, tr.InGroup proposer dg y j i (tr.time i) e
  /-- Every labelled cut of a node honest at its time obeys the cut law. -/
  cutLaw : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    Node.CutStep y (tr.time i) (tr.state y i) c (tr.post i)
  /-- A delivery to a node honest at its time passes the wire checks. -/
  wire : ∀ y j t e, y ∈ H t → tr.GroupAt proposer dg y j t e → Node.WireOK dg e
  /-- The proposer credential of a block delivered to a node honest at the delivery time. -/
  proposerCredential : ∀ y j t B, y ∈ H t → tr.GroupAt proposer dg y j t (.block B) →
    B.proposer = proposer B.slot
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- Finitely many labelled cuts in every bounded interval. -/
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite
  /-- At one time, across the nodes honest then, restarts come before ticks and ticks before
  deliveries. -/
  phase_order : ∀ y y' j j' t e e', y ∈ H t → y' ∈ H t → tr.GroupAt proposer dg y j t e →
    tr.GroupAt proposer dg y' j' t e' → j < j' → e.phase ≤ e'.phase
  /-- A tick of a node honest at its time is at a public time. -/
  tick_public : ∀ y j t, y ∈ H t → tr.TickAt proposer dg y j t → P.IsPublic t
  /-- One tick per node and time, for a node honest at that time. -/
  tick_unique : ∀ y j j' t, y ∈ H t →
    tr.TickAt proposer dg y j t → tr.TickAt proposer dg y j' t → j = j'
  /-- A node honest and awake at a public time (from `0` on) ticks there. -/
  tick_of_awake : ∀ y t, y ∈ H t → 0 ≤ t → P.IsPublic t → tr.awake y t →
    ∃ j, tr.TickAt proposer dg y j t
  /-- A node honest at a time is awake then only within the run's horizon. -/
  awake_in_horizon : ∀ y t, y ∈ H t → tr.awake y t → tr.InHorizon t
  /-- A node honest at the time of its call is called only while awake. -/
  awake_of_call : ∀ y i, y ∈ H (tr.time i) → tr.IsCall y i → tr.awake y (tr.time i)
  /-- The first call of a node after it was asleep is a restart (honest at the call). -/
  restart_of_sleep : ∀ y i (u : Time), y ∈ H (tr.time i) → tr.IsCall y i → 0 ≤ u →
    u < tr.time i → ¬ tr.awake y u → (∀ j < i, tr.IsCall y j → tr.time j < u) →
    tr.RestartAt y i
  /-- A wake is a restart: a node asleep at `u` and awake at a later `v`, honest at `v`, restarts
  at a cut in `(u, v]`. -/
  restart_at_wake : ∀ y (u v : Time), y ∈ H v → 0 ≤ u → u < v → ¬ tr.awake y u →
    tr.awake y v → ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake (honest at the restart). -/
  sleep_of_restart : ∀ y i, y ∈ H (tr.time i) → tr.RestartAt y i →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, tr.IsCall y j → tr.time j < u
  /-- A block whose proposer is honest at the processing time, processed by a node honest then,
  is that proposer's own block, processed by the proposer at or before. -/
  block_unforgeable : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    B.proposer ∈ H (tr.time i) → ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  /-- An attestation whose signer is honest at the processing time, processed by a node honest
  then (as such or carried by a processed block), was signed by that signer at an earlier cut. -/
  att_unforgeable : ∀ y i a, y ∈ H (tr.time i) →
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) →
    a.val ∈ H (tr.time i) → ∃ j < i, tr.SignAt a.val j a
  /-- An AC message whose signer is honest at the receipt time, received by a node honest then,
  was emitted by that signer's node at an earlier cut. -/
  msg_unforgeable : ∀ y i m, y ∈ H (tr.time i) → tr.MsgCallAt y i m →
    sg m ∈ H (tr.time i) → ∃ j < i, tr.EmitAt (sg m) j m

end Growing

end Consensus.Goldilocks

end
