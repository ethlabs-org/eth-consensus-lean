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
count `f_d < h_t` of the run is the AC projection's at every `t` and `d`.

At `H := fun _ => H₀` each statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {P : Params} {A : NodeAC P}

/-- The order facts of F.5 (run) under growing faults: the static `RunOrder` with every node
honest at the time of its cut or group. -/
structure RunOrder (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Time → Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) : Prop where
  /-- (a) The cut index respects time. -/
  time_of_lt : ∀ i j, i ≤ j → tr.time i ≤ tr.time j
  /-- (b) At one time, the groups of the nodes honest then are in phase order. -/
  phase : ∀ y y' j j' t e e', y ∈ H t → y' ∈ H t →
    tr.GroupAt proposer dg y j t e → tr.GroupAt proposer dg y' j' t e' →
    j < j' → e.phase ≤ e'.phase
  /-- (c) The cuts of a tick of a node honest at its time are `on_tick`'s cuts, in order. -/
  tick_steps : ∀ y j t x, y ∈ H t → tr.GroupAt proposer dg y j t (.tick x) →
    ∀ k, (hk : k < (Node.onTick proposer dg y (tr.state y j) t x).2.length) →
      tr.label (j + k) = some (Node.onTick proposer dg y (tr.state y j) t x).2[k]
  /-- (d) A block whose proposer is honest at the processing cut, processed by a node honest then,
  was processed by its proposer at or before, inside a tick. -/
  block_before : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    B.proposer ∈ H (tr.time i) → ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  /-- (d) An attestation whose signer is honest at the processing cut, processed by a node honest
  then, was signed at an earlier cut. -/
  att_before : ∀ y i a, y ∈ H (tr.time i) → tr.ProcessAttAt y i a → a.val ∈ H (tr.time i) →
    ∃ j < i, tr.SignAt a.val j a
  /-- (d) An AC message whose signer is honest at the receipt, received by a node honest then, was
  emitted at an earlier cut. -/
  msg_before : ∀ y i m, y ∈ H (tr.time i) → tr.MsgCallAt y i m → sg m ∈ H (tr.time i) →
    ∃ j < i, tr.EmitAt (sg m) j m
  /-- (e) Finitely many labelled cuts in every bounded interval. -/
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite

/-- **F.5 (run) under growing faults, event order.** -/
def EventOrder : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr → RunOrder proposer dg H sg tr

/-- **F.4 under growing faults, ready implies joined**, for a validator honest at `t`. -/
def ReadyImpliesJoined : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    ∀ y (t c : Time), y ∈ H t → 0 ≤ t → 8 * sp.Δ ≤ c + 1 →
      (∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t

/-- **C0.5 under growing faults, the AC projection**, from the AC starts `ini` of the run, with
requirement 5 from each start `ini y` of a node honest at time `0` (`ACInterface.ReqPayloadFrom`;
requirement 5 itself at the default start `ini y = A.initial`). -/
def ACProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n) {ini : Fin P.n → A.State},
    A.Requirements →
    (∀ y ∈ H 0, A.ReqPayloadFrom (ini y) y) →
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini →
      NoCollRun dg tr →
      Consensus.Goldilocks.Growing.ACLocalRun A H (tr.HonestBlocksAt H) tr.projAC ini

/-- **C0.5 (c) under growing faults, the FG projection.** -/
def FGProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
      Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr → NoCollRun dg tr →
        Consensus.Goldilocks.Growing.FGLocalRun A.genesisPayload H (tr.HonestBlocksAt H)
          tr.projFG

/-- **The honest-object facts of the AC projection under growing faults.** -/
def GoldilocksACProjection : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → NoCollRun dg tr →
      SA.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H)

/-- **The states of a node honest at a group are reachable configurations.** -/
def GroupStatesReachable : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n),
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr →
    ∀ y j t e, y ∈ H t → tr.GroupAt proposer dg y j t e →
      (∃ cfg : Node.Config A,
        Node.Reachable proposer dg y cfg ∧ cfg.st = tr.state y j ∧ cfg.time ≤ t) ∧
      ∃ cfg' : Node.Config A, Node.Reachable proposer dg y cfg' ∧
        cfg'.st = tr.post (j + (Node.exec proposer dg y (tr.state y j) t e).2.length - 1) ∧
        cfg'.time = t

/-- **`Sync` projects under growing faults.** -/
def SyncProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (proposer : Nat → Fin P.n) (ΔF a b : Time),
    Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr → tr.SyncRunAt H ΔF a b →
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
