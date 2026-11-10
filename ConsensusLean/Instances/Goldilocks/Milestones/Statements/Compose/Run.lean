module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.GenericPremises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Node

@[expose] public section

/-! # Goldilocks milestone Persist, part 1: runs (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex`,
the run-level composition nodes that every later run-level milestone (Persist,
Service, Healing, Regimes) reads, over the spec's own run model (`Spec/Run`):

* **F.5 (run), event order**: the cut order of a run is the order of the claims. By time; at one
  time, restarts before ticks before deliveries across the honest nodes; inside a tick, the
  steps in C0.4's order (the positions); every honest object before its honest receipts (a send
  before its receipts, which a fixed tie rule such as node id would contradict). With finiteness
  per bounded interval (`Node.LocalRun.finite`) the order is well founded, and F.5 (schema) is
  Mathlib's `WellFounded.induction` on the cut index (no declaration of its own).
* **F.4, Ready implies joined**: for the Goldilocks run (`t_s = 4Δs`), a validator honest and
  awake on `[max(0, t − c − 1), t]` with `c + 1 ≥ 8Δ` is awake and joined at `t` (the instance's
  bridge assumptions, "awake at `u` means awake throughout `(u − 1, u]`" and "a node awake at
  `0` has not restarted", hold of a run: times are integers and a restart follows a sleep).
* **C0.5's last sentence, the projections**: the AC projection of a run is an AC trace with the
  contract (`ACLocalRun`, with `U` the honest blocks of the run) and, for the Goldilocks run, the
  honest-object facts (`SA.ACRun`); the FG projection is an FG trace with its contract
  (`FGLocalRun`); the honest nodes' states at the start of every top-level event are
  `Node.Reachable` configurations; and the run premises project: `Sync` over the run gives
  `SyncAC` over the AC projection on the same window, and the joining and participation counts
  agree.

Every statement is over `Node.LocalRun` (or `GoldilocksRun`). The three projections onto
component traces (`ACProjection`, `FGProjection`, `GoldilocksACProjection`) also take `NoColl` on
the objects of the run, the blocks that occur in it and genesis (`NoCollRun`, over
`Compose.NoCollOn`); F.5 (run), F.4, `GroupStatesReachable`, `SyncProjection` and
`JoinedProjection` take none. The two projections of an arbitrary AC also take the AC's
requirements 1–5 and, for the FG projection, the genesis root, as C0.5 (a) and C0.3 do.
`docs/goldilocks-mapping.md` §"Persist" maps each statement to its node.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {P : Params} {A : NodeAC P}

/-- **F.4, Ready implies joined (D4).** In a Goldilocks run, an honest validator awake at every
integer time of `[max(0, t − c − 1), t]` with `c + 1 ≥ 8Δ` is awake and joined at `t ≥ 0`: its
latest restart is at or before `t − c − 1`, or there is none, and `t − t_{slot(t) − 1} < 8Δ`.
Times are from `0` (`t < 0` makes the awake interval empty, and no run law forces a node to be
awake before `0`). -/
def ReadyImpliesJoined : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → ∀ y ∈ H, ∀ (t c : Time), 0 ≤ t → 8 * sp.Δ ≤ c + 1 →
      (∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t

/-- **The honest-object facts hold of the Goldilocks run's AC projection** (claims §"Runs";
the premises `SA.HonestObjects` of the AC step statements): with the AC contract, `SA.ACRun`.
Every non-genesis frame block's proposer is its slot's by the run's credential law,
one block per honest proposer and slot by the proposal schedule, honest votes by the
run's unforgeability. -/
def GoldilocksACProjection : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → NoCollRun dg tr →
      SA.ACRun proposer tr.projAC H (tr.HonestBlocks H)

/-- **Joining and participation project**: in a Goldilocks run, an honest node is joined at `t`
by the run's restarts (`RunTrace.JoinedAt`) exactly when the SA's joined test on its AC state
holds at every cut at `t` other than a restart (a restart cut sets `restart_time` only in its
post-state), and the run's `h_t` and `f < h_t` are the AC projection's. -/
def JoinedProjection : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → ∀ y ∈ H, ∀ t,
      (tr.JoinedAt y t ↔ SA.JoinedAt tr.projAC y t) ∧
      (∀ i, tr.IsCall y i → ¬ tr.RestartAt y i → tr.time i = t →
        (tr.JoinedAt y t ↔ SA.joined sp (tr.state y i).ac t)) ∧
      tr.honestAwakeJoined H t = SA.honestAwakeJoined tr.projAC H t

end Consensus.Goldilocks.Compose

end
