module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

@[expose] public section

/-! # Goldilocks runs under growing faults

`Growing.GoldilocksRun proposer dg H tr`: `GoldilocksRun` (`Spec/Run/Goldilocks`) for a
time-indexed honest set `H` (`Spec/Run/Growing/Model`). Carried-vote unforgeability reads the
signer's honesty at the processing time. At `H := fun _ => H₀` it is `GoldilocksRun proposer dg H₀
tr` (`Growing.GoldilocksRun.const_iff`, `Lemmas/Growing/Run`). -/

namespace Consensus.Goldilocks.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote blockVotes Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **A run of the Goldilocks protocol under growing faults**: a run of the node for the
time-indexed honest set `H`, the genesis root premise, and carried-vote unforgeability for signers
honest at the processing time. -/
structure GoldilocksRun (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro)
    (ini : Fin sp.n → (goldilocksNode sp ro).State := fun _ => (goldilocksNode sp ro).initial) :
    Prop
    extends Growing.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr ini where
  /-- The genesis block's root is the digest of its content. -/
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- A vote whose validator is honest at the processing time, carried by a block that a node
  honest then processes, was emitted by that validator's node at an earlier cut. -/
  carried_vote_unforgeable : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    ∀ v ∈ blockVotes B, v.val ∈ H (tr.time i) → ∃ j < i, tr.EmitAt v.val j v
  /-- The AC starts are starts up to the vote permission. -/
  vstart : ∀ y, SA.VoteStart sp.genesisRoot (ini y)

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **The run half of the committee premises** for the slot dictionary `K`: committees of
`committeeSize` members, P (`CommitteePAt`), the frames of nodes honest at the cut carry votes of
members, and the gate: a node honest at `t ≥ 0` may vote in slot `s`, before every cut whose
earlier cuts are at times `≤ t`, iff it is in the slot-`s` committee. T (`CommitteeTAt`) follows
from P and the frames on a run (`CommitteeFacts.committeeTAt`). -/
structure CommitteeFacts (K : SA.CommitteeDict sp.n) : Prop where
  hsize : ∀ s, (K.committee s).ncard = sp.committeeSize
  hP : SA.CommitteePAt K tr.projAC H
  hFrame : ∀ w c, w ∈ H (tr.time c) → ∀ C ∈ (Node.frame (tr.state w c)).tree,
    ∀ v ∈ SA.blockVotes C, v.val ∈ K.committee v.slot
  hGate : ∀ t, 0 ≤ t → ∀ x, x ∈ H t → ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s,
    ((tr.state x i).ac.mayVote s = true ↔ x ∈ K.committee s)

end Consensus.Goldilocks.Compose.Growing

end
