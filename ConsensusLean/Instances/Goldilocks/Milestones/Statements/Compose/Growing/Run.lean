module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing

@[expose] public section

/-! # Goldilocks runs under growing faults: the run statements (statements)

The run statements of `Statements/Compose/Run` for a time-indexed honest set `H` (antitone),
over `Growing.LocalRun` / `Growing.GoldilocksRun`: each node is honest at the time of the cut or
group it is named at, unforgeability reads the signer at the processing cut, and the projections
land in the growing-fault component contracts (`Growing.ACLocalRun`, `Growing.FGLocalRun`,
`SA.Growing.ACRun`, `SyncACAt`) inside the blocks held while honest. Joining projects, and the
count `f_d < h_t` of the run is the AC projection's at every `t` and `d`. F.4 (ready implies
joined) is proved only at a fixed honest set (`Compose.ReadyImpliesJoined`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {P : Params} {A : NodeAC P}

/-- **C0.5 under growing faults, the AC projection**, from the AC starts `ini` of the run, with
requirement 5 from each start `ini y` of a node honest at time `0` (`ACInterface.ReqPayloadFrom`;
requirement 5 itself at the default start `ini y = A.initial`). -/
def ACProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n) {ini : Fin P.n → A.State},
    (∀ y ∈ H 0, A.ReqPayloadFrom (ini y) y) →
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini →
      NoCollRun dg tr →
      Consensus.Goldilocks.Growing.ACLocalRun A H (tr.HonestBlocksAt H) tr.projAC ini

/-- **C0.5 (c) under growing faults, the FG projection**, over a run from any AC starts `ini`,
with the interface requirements at each start (those of `{ A with initial := ini y }`; at the
default start `ini y = A.initial`, `A.Requirements`). -/
def FGProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n) {ini : Fin P.n → A.State},
    (∀ y, ({ A with initial := ini y } : NodeAC P).Requirements) →
      (P.genesisBlock A.genesisPayload).RootOk dg →
      Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini → NoCollRun dg tr →
        Consensus.Goldilocks.Growing.FGLocalRun A.genesisPayload H (tr.HonestBlocksAt H)
          tr.projFG

/-- **The honest-object facts of the AC projection under growing faults.** -/
def GoldilocksACProjection : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → NoCollRun dg tr →
      SA.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H)

/-- **`Sync` projects under growing faults**, over a run from any start. -/
def SyncProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n) (ΔF a b : Time) {ini : Fin P.n → A.State},
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini → tr.SyncRunAt H ΔF a b →
      SyncACAt A H (tr.HonestBlocksAt H) a b tr.projAC

/-- **Joining and participation project under growing faults.** Joining at `t` of a node honest
at `t` is the AC projection's, and the run's count of the validators honest at `d`, awake and
joined at `t` is the AC projection's, at every `t` and `d`. -/
def JoinedProjection : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    (∀ y t, y ∈ H t →
      (tr.JoinedAt y t ↔ SA.JoinedAt tr.projAC y t) ∧
      (∀ i, tr.IsCall y i → ¬ tr.RestartAt y i → tr.time i = t →
        (tr.JoinedAt y t ↔ SA.joined sp (tr.state y i).ac t))) ∧
    ∀ t d, {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard =
      {y | y ∈ H d ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t}.ncard

end Consensus.Goldilocks.Compose.Growing

end
