module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeInstance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks

@[expose] public section

namespace Consensus.Goldilocks

open SA (SAParams ReplayOrder CommitteeDict Vote Payload blockVotes)

/-- The generic stock composition with committee AC and the unchanged population FG. -/
noncomputable abbrev goldilocksNodeK (sp : SAParams) (K : CommitteeDict sp.n)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) : NodeAC sp.toParams :=
  SA.goldilocksSAK sp K (List (FG.Att sp.n)) ro

/-- The concrete composite trace, using the existing node and FG carriers. -/
abbrev GoldilocksTraceK (sp : SAParams) (K : CommitteeDict sp.n)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) := RunTrace (goldilocksNodeK sp K ro)

namespace Growing

variable {sp : SAParams} {K : CommitteeDict sp.n}
  {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Growing-fault execution laws for the concrete committee node. Regime bounds,
service, committee well-formedness and model correspondence remain separate obligations. -/
structure GoldilocksRunK (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTraceK sp K ro) : Prop
    extends Growing.LocalRun proposer dg H (fun v : Vote sp.n => v.val) tr where
  /-- The genesis block's root is the digest of its content. -/
  genesis_root_ok :
    (sp.toParams.genesisBlock (goldilocksNodeK sp K ro).genesisPayload).RootOk dg
  /-- Carried votes honest at processing time have an earlier concrete emission. -/
  carried_vote_unforgeable : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    ∀ v ∈ blockVotes B, v.val ∈ H (tr.time i) → ∃ j < i, tr.EmitAt v.val j v

end Growing

end Consensus.Goldilocks
