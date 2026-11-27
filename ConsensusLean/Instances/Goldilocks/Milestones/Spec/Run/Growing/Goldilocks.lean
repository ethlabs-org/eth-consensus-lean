module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.CommitteeRun

@[expose] public section

/-! # Goldilocks runs under growing faults

`Growing.GoldilocksRun proposer dg H tr`: `GoldilocksRun` (`Spec/Run/Goldilocks`) for a
time-indexed honest set `H` (`Spec/Run/Growing/Model`). At `H := fun _ => H₀` it is
`GoldilocksRun proposer dg H₀ tr`. -/

namespace Consensus.Goldilocks.Growing

open AC (ACParams goldilocksAC Vote Payload)

variable {sp : ACParams}

/-- **A run of the Goldilocks protocol under growing faults**: a run of the node for the
time-indexed honest set `H` and the genesis root premise. -/
structure GoldilocksRun (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp)
    (ini : Fin sp.n → (goldilocksNode sp).State := fun _ => (goldilocksNode sp).initial) :
    Prop
    extends Growing.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr ini where
  /-- The genesis block's root is the digest of its content. -/
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg
  /-- The AC starts are starts up to the vote permission. -/
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams)

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))

/-- **The run half of the committee premises** for the slot dictionary `K`: committees of
`committeeSize` members, P (`CommitteePAt`), and the gate: a node honest at `t ≥ 0` may vote in
slot `s`, before every cut whose earlier cuts are at times `≤ t`, iff it is in the slot-`s`
committee. T (`CommitteeTAt`) follows from P on a run (`CommitteeFacts.committeeTAt`): a declared
head vote counts only when the pool holds a vote of its validator for its slot. The frames are not
premised: a valid block may declare a vote of a non-member. -/
structure CommitteeFacts (K : AC.CommitteeDict sp.n) : Prop where
  hsize : ∀ s, (K.committee s).ncard = sp.committeeSize
  hP : AC.CommitteePAt K tr.projAC H
  hGate : ∀ t, 0 ≤ t → ∀ x, x ∈ H t → ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s,
    ((tr.state x i).ac.mayVote s = true ↔ x ∈ K.committee s)

end Consensus.Goldilocks.Compose.Growing

end
