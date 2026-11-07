module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model

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
    (tr : GoldilocksTrace sp ro) : Prop
    extends Growing.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr where
  /-- The genesis block's root is the digest of its content. -/
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- A vote whose validator is honest at the processing time, carried by a block that a node
  honest then processes, was emitted by that validator's node at an earlier cut. -/
  carried_vote_unforgeable : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    ∀ v ∈ blockVotes B, v.val ∈ H (tr.time i) → ∃ j < i, tr.EmitAt v.val j v

end Consensus.Goldilocks.Growing

end
