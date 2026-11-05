module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model

@[expose] public section

/-! # Goldilocks milestone vocabulary: Goldilocks runs

The part of `Spec/Run/Goldilocks` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

The Goldilocks node is `goldilocksNode sp ro` (`Spec/Run/Goldilocks`). `GoldilocksRun proposer dg H
tr` is a run of it: `Node.LocalRun` with the vote's validator as the message signer, plus
**carried-vote unforgeability**, the instance of the run's unforgeability for votes that travel in a
block's payload (claims §"Runs"; composition.tex §"Blocks"): a vote of an honest validator that an
honest node processes in a block (`blockVotes`, the votes the payload carries) was emitted by that
validator's node at an earlier cut. The generic node cannot state it: the AC interface does not say
which messages a payload carries.

A Goldilocks run also takes the genesis root: the genesis block's root is the digest `dg` of
its content (`genesis_root_ok`). composition.tex §"Blocks" makes every block's root its
content's digest; the Lean `genesisRoot` is a parameter of `Params`, so this is a premise
relating it to `dg`, taken as C0.3 takes it. The generic statements over any AC (C0.3,
`FGProjection`) keep it as their own premise. Every statement over `GoldilocksRun` has it from
the run; some restate it (`Healing.RunInclusion`, `HSShared.genesisRoot`). -/

namespace Consensus.Goldilocks

open SA (SAParams ReplayOrder goldilocksSA Vote blockVotes Payload)

variable (sp : SAParams)

/-- A run trace of the Goldilocks protocol. -/
abbrev GoldilocksTrace (ro : ReplayOrder sp (List (FG.Att sp.n))) :=
  RunTrace (goldilocksNode sp ro)

variable {sp} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **A run of the Goldilocks protocol** (claims §"Runs"): a run of the node with the SA, the
vote's validator as the signer of a message, carried-vote unforgeability, and the genesis
block's root the digest of its content. -/
structure GoldilocksRun (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) : Prop
    extends Node.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr where
  /-- The genesis block's root is the digest of its content: the premise `FGProjection` and
  C0.3 take over any AC (the Lean genesis root is a parameter). -/
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- A vote of an honest validator carried by a block that an honest node processes was emitted
  by that validator's node at an earlier cut. -/
  carried_vote_unforgeable : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B →
    ∀ v ∈ blockVotes B, v.val ∈ H → ∃ j < i, tr.EmitAt v.val j v

end Consensus.Goldilocks

end
