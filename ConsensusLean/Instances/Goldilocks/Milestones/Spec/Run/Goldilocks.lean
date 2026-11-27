module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Premises

@[expose] public section

/-! # Goldilocks milestone vocabulary: Goldilocks runs

The part of `Spec/Run/Goldilocks` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. `GoldilocksRun` takes the nodes' starts `ini` (by default the initial state) and the field
`vstart`: every start is a start up to the vote permission. It carries no committee size.

The Goldilocks node is `goldilocksNode sp` (`Spec/Run/Goldilocks`). `GoldilocksRun proposer dg H
tr` is a run of it: `Node.LocalRun` with the vote's validator as the message signer. A block
carries no vote: its declared head votes are the proposer's statement, not signed votes, so the
run's unforgeability says nothing about them (a faulty proposer may declare a vote that its
validator never signed).

A Goldilocks run also takes the genesis root: the genesis block's root is the digest `dg` of
its content (`genesis_root_ok`). composition.tex §"Blocks" makes every block's root its
content's digest; the Lean `genesisRoot` is a parameter of `Params`, so this is a premise
relating it to `dg`, taken as C0.3 takes it. The generic statements over any AC (C0.3,
`FGProjection`) keep it as their own premise. Every statement over `GoldilocksRun` has it from
the run; some restate it (`HSShared.genesisRoot`). -/

namespace Consensus.Goldilocks

open AC (ACParams goldilocksAC Vote Payload)

variable (sp : ACParams)

/-- A run trace of the Goldilocks protocol. -/
abbrev GoldilocksTrace :=
  RunTrace (goldilocksNode sp)

variable {sp}

/-- **A run of the Goldilocks protocol** (claims §"Runs"): a run of the node with the AC, the
vote's validator as the signer of a message, and the genesis block's root the digest of its
content. -/
structure GoldilocksRun (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp)
    (ini : Fin sp.n → (goldilocksNode sp).State := fun _ => (goldilocksNode sp).initial) :
    Prop
    extends Node.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr ini where
  /-- The genesis block's root is the digest of its content: the premise `FGProjection` and
  C0.3 take over any AC (the Lean genesis root is a parameter). -/
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload).RootOk dg
  /-- The AC starts are starts up to the vote permission. -/
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)

end Consensus.Goldilocks

end
