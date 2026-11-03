module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Premises
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node

@[expose] public section

/-! # Goldilocks milestone Persist, part 1: runs (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main
`4ea71d05`), the run-level composition nodes that every later run-level milestone (Persist,
Service, Healing, Regimes) reads, over the spec's own run model (`Spec/Run`, decomposition §2 D):

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
requirements 1–5 and, for the FG projection, the genesis root, as C0.5 (a) and C0.3 do
(consensus-lean#73). `docs/goldilocks-mapping.md` §"Persist" maps each statement to its node.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {P : Params} {A : NodeAC P}

/-- `NoColl` over a run: the digest is collision free on the objects of the run (claims
§"Premises": "no two distinct objects with one digest occur in the run"), the blocks that occur
in it and genesis. Genesis is held by every node from `Store.init` but need not be the object of
a block call, so `Occurs` alone could leave it out, while C0.3 (`HonestBlockAccepted`) takes
`NoCollOn` on the tree with the own block, genesis included, for the own block's root to be new
(consensus-lean#73). Every honest tree is inside this set: `Store.onBlock` adds only the block of
its call, and nothing removes a block. -/
def NoCollRun (dg : Digest (List (FG.Att P.n)) A.Payload) (tr : RunTrace A) : Prop :=
  NoCollOn dg (insert (P.genesisBlock A.genesisPayload) {B | tr.Occurs B})

/-- The order facts of F.5 (run) over a run, for the honest validators `H`: (a) the cut index
respects time; (b) at one time, the groups are in phase order (restarts, ticks, deliveries)
across the honest nodes; (c) the cuts of a tick are its steps in C0.4's order, at consecutive
indices; (d) every honest object that an honest node processes was made by its honest maker at
an earlier cut (or, for a block, at or before: the maker processes its own block at the same
cut), so the send precedes the receipt; (e) finitely many cuts in every bounded interval. -/
structure RunOrder (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) : Prop where
  /-- (a) The cut index respects time. -/
  time_of_lt : ∀ i j, i ≤ j → tr.time i ≤ tr.time j
  /-- (b) At one time, the honest groups are in phase order. -/
  phase : ∀ y ∈ H, ∀ y' ∈ H, ∀ j j' t e e',
    tr.GroupAt proposer dg y j t e → tr.GroupAt proposer dg y' j' t e' →
    j < j' → e.phase ≤ e'.phase
  /-- (c) The cuts of an honest tick at `t` with the input `x` from `j` are `on_tick`'s cuts, in
  C0.4's order, at `j, j + 1, …`. -/
  tick_steps : ∀ y ∈ H, ∀ j t x, tr.GroupAt proposer dg y j t (.tick x) →
    ∀ k, (hk : k < (Node.onTick proposer dg y (tr.state y j) t x).2.length) →
      tr.label (j + k) = some (Node.onTick proposer dg y (tr.state y j) t x).2[k]
  /-- (d) A block of an honest proposer processed by an honest node was processed by its proposer
  at or before, inside a tick. -/
  block_before : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B → B.proposer ∈ H →
    ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  /-- (d) An attestation of an honest signer processed by an honest node was signed at an earlier
  cut. -/
  att_before : ∀ y ∈ H, ∀ i a, tr.ProcessAttAt y i a → a.val ∈ H → ∃ j < i, tr.SignAt a.val j a
  /-- (d) An AC message of an honest signer received by an honest node was emitted at an earlier
  cut. -/
  msg_before : ∀ y ∈ H, ∀ i m, tr.MsgCallAt y i m → sg m ∈ H → ∃ j < i, tr.EmitAt (sg m) j m
  /-- (e) Finitely many labelled cuts in every bounded interval. -/
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite

/-- **F.5 (run), event order.** Every run has the order facts `RunOrder`: the cut index is the
order of the claims, well founded by (e), so an invariant of cuts that holds at a cut whenever it
holds at every earlier cut holds everywhere (F.5 (schema), `WellFounded.induction` on `<`). -/
def EventOrder : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) (proposer : Nat → Fin P.n),
    Node.LocalRun proposer dg H sg tr → RunOrder proposer dg H sg tr

/-- **F.4, Ready implies joined (D4).** In a Goldilocks run, an honest validator awake at every
integer time of `[max(0, t − c − 1), t]` with `c + 1 ≥ 8Δ` is awake and joined at `t ≥ 0`: its
latest restart is at or before `t − c − 1`, or there is none, and `t − t_{slot(t) − 1} < 8Δ`.
Times are from `0` (`t < 0` makes the awake interval empty, and no run law forces a node to be
awake before `0`; consensus-lean#73). -/
def ReadyImpliesJoined : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → ∀ y ∈ H, ∀ (t c : Time), 0 ≤ t → 8 * sp.Δ ≤ c + 1 →
      (∀ u : Time, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u) →
      tr.awake y t ∧ tr.JoinedAt y t

/-- **C0.5, the AC projection of a run is an AC trace with the contract**, for the honest
validators, inside the honest blocks of the run, for an AC with requirements 1–5 (as C0.5 (a)),
under `NoColl`. Requirement 5 is needed: the own block's `ac_on_block` call must satisfy
`CallOK`, whose `validPayload` the FG does not check (the FG accepts without reading the AC
payload), so it holds only because the AC's own proposal passes `ac_valid_payload`
(consensus-lean#73). -/
def ACProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) (proposer : Nat → Fin P.n),
    A.Requirements → Node.LocalRun proposer dg H sg tr → NoCollRun dg tr →
      ACLocalRun A H (tr.HonestBlocks H) tr.projAC

/-- **C0.5 (c), the FG projection of a run is an FG trace with the contract**, with the AC's
genesis payload, inside the honest blocks of the run, for an AC with requirements 1–5 and a
genesis whose root is its digest (the premises of C0.3), under `NoColl`. Its tick-order laws
(`own_first`, `attest_order`, `own_payload`) come from C0.4 and the group law with C0.3: the own
block is accepted in its tick, so the acceptance of the own proposal is the first FG cut at its
time. The proof uses requirement 1 only for the parent of the own proposal: it extends `fc_root`,
so it is held; without that the own block can be refused at the tick, then accepted later at the
same time after its parent and a copy of it arrive, against `own_first` (consensus-lean#73).
Requirements 3 and 4 already give it (the parent is `ac_head` at the state `ac_proposal` leaves,
which extends `fc_root`; `proposalHead_of_outputs_parent` in ConsensusLeanTest), so requirement 1
adds nothing here beyond them; its vote-head clause is not used. The genesis root is taken as C0.3
takes it, so the proof is C0.3 (a refused own block is otherwise refused for ever at its node, its
root being held). Its unforgeability is the run's. -/
def FGProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) (proposer : Nat → Fin P.n),
    A.Requirements → (P.genesisBlock A.genesisPayload).RootOk dg →
      Node.LocalRun proposer dg H sg tr → NoCollRun dg tr →
        FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG

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

/-- **The honest states of a run are reachable configurations** (`Node.Reachable`, the
over-approximation of `Spec/Node` that the Compose/AnyAC statements are stated over): the state
of an honest node at the start of each of its top-level events is the state of a reachable
configuration at a time at most the event's, and so is the state after the event. -/
def GroupStatesReachable : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) (proposer : Nat → Fin P.n),
    Node.LocalRun proposer dg H sg tr → ∀ y ∈ H, ∀ j t e, tr.GroupAt proposer dg y j t e →
      (∃ cfg : Node.Config A,
        Node.Reachable proposer dg y cfg ∧ cfg.st = tr.state y j ∧ cfg.time ≤ t) ∧
      ∃ cfg' : Node.Config A, Node.Reachable proposer dg y cfg' ∧
        cfg'.st = tr.post (j + (Node.exec proposer dg y (tr.state y j) t e).2.length - 1) ∧
        cfg'.time = t

/-- **`Sync` projects**: `Sync[a, b]` over a run gives `SyncAC` over its AC projection, on the
same window, inside the honest blocks of the run (the message clause and the acceptance relay;
the run's block and attestation clauses have no AC counterpart). -/
def SyncProjection : Prop :=
  ∀ (P : Params) (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n))
    (sg : A.Msg → Fin P.n) (tr : RunTrace A) (proposer : Nat → Fin P.n) (ΔF a b : Time),
    Node.LocalRun proposer dg H sg tr → tr.SyncRun H ΔF a b →
      SyncAC A H (tr.HonestBlocks H) a b tr.projAC

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
