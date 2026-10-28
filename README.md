# The generic contract, in three layers: review guide

What it means for a protocol to be a correct consensus protocol, in three
layers, each reviewed once:

| Layer | Library | What it fixes | Lines |
|---|---|---|---|
| **L0, the problem** | `ConsensusProblem` | transactions, ledgers, three outputs; the environment (Δ, GST, awake profile, honest set, transaction submissions); safety, nesting, transaction liveness, persistence, accountability, non-framing; the claim form | ~400 |
| **L½, the model** | `ConsensusModel` | a shape-free execution model: protocol interface, engine, delivery, sleep and restarts, unforgeability, evidence, hashes; `sysOf F`, which makes any protocol family an L0 system | ~600 |
| **L1, our shape** | `ConsensusShape` | slots, one proposer per slot, full committees, block headers and chains, regimes, constants, `compile` onto L½; block-level claims `ShapeClaims`; the profile and bounds of the L0 claims | ~750 (definitions; ~1,000 with the refinement proof) |

The headline is the refinement theorem `refinement`: for every family `F` of
the shape and every finite nonempty validator type `V`,
`ShapeClaims F C → ProblemClaims (sysOf (compile ∘ F) V) (profile C) (bounds C)`.
A protocol that proves `ShapeClaims` therefore solves the L0 problem under L1's
reviewed assumptions.

Design and history: `notes/generic-interface/layers-plan.md` (and `plan.md`,
`hash-plan.md`) in the workbench, with the Astra and Opus reviews they cite.
The older single-layer contract (`AvailableChainContract*`) is being replaced
and will be removed.

## Reading order

1. **L0** (`ConsensusProblem/{Basic,Properties,Claims}`). Check that agreement,
   monotonicity, nesting, transaction liveness, persistence, accountability
   and non-framing say what they should. Every claim is `Holds S A P`: on
   valid runs satisfying `A`, `P` holds or the excuse holds. Unconditional
   claims are `HoldsAlways`. L0 cannot judge the assumptions or the excuse;
   the layers below fix them.
2. **L½** (`ConsensusModel/{Objects,Protocol,Run,Conditions,Evidence,System}`).
   It fixes the meaning of L0's abstract fields:
   - **validity** is `ExecutionValid`;
   - **reads** are the protocol's output ledgers at event cuts;
   - **evidence** is the objects an honest node has seen, convicted under the
     protocol's `conflicts` rule through the run's seat holders;
   - **the excuse** is an observed hash collision.

   Also read the statements of `ConsensusModelProofs`:
   - `sysOf_laws`;
   - `CanonicalRun`, proved as `canonical_run`: every execution premise is
     satisfiable for every protocol;
   - the lifting theorems: the collision escape adds nothing beyond the
     injective case.
3. **L1** (`ConsensusShape`):
   - `compile`, which turns our shape into an L½ protocol;
   - the regimes (participation, delivery, recurrence);
   - `Constants`;
   - `profile` and `bounds` (the assumptions and numbers that L0's claims are
     promised under), and `profile_realizable`;
   - `ShapeClaims`.

## Why the meaning is fixed below the protocol

- **No protocol-supplied premise predicate.** Every premise is environment
  vocabulary (L0), an execution condition (L½: valid execution, delivery), or
  a reviewed shape premise (L1: recurrence over the shape's slot timing). The
  execution conditions evaluate what the protocol does, but the protocol
  supplies no hook, author, decoder, schedule or hash, and evidence collection
  and conviction are fixed around its one slashing rule, `conflicts`.
  `canonical_run` makes the execution part satisfiable for every protocol.
- **Signing and keys.**
  - The engine signs. Seats are held by validators through the run's holder
    map, which is an **embedding per label**: no validator holds two seats of
    one label, so a quorum of seats is a quorum of distinct validators.
  - Accountability counts validators, with no committee premise.
- **Transaction ingress is relayed by the network.** A transaction submitted
  to an awake honest node is relayed to every honest node awake throughout a
  delivery window, including after a later wake. The scheduler chooses the
  run's `relay` field. At each tick the engine supplies the cumulative
  `mempool rho.inbox`, merging own submissions with relayed transactions;
  honest code cannot distinguish their origin. This pool survives restarts.
  Relay is otherwise unconstrained: the adversary may inject any transaction.
  L1 encodes this pool into the proposer's header payload.
- **Both output nesting pairs hold unconditionally:** `finalized ⪯ stable`
  and `stable ⪯ confirmed`, at every event cut, including restart cuts.
- **Transaction latency** is measured from `max t GST + Δ`: a transaction
  submitted to some awake honest node by `t ≥ start` must occur in every
  ready read at every `t' ≥ max t GST + Δ + D` within the horizon. The L1
  bounds `D` stay unchanged. Refinement applies `LiveFrom` at `t' − D` and
  delivery with `a = proposalTime − Δ`; `catchUp ≥ 1` supplies the required
  awake history, and `PartialSynchrony` supplies strictly earlier ingress.
- **Hashes are arbitrary run data.**
  - Escaped claims read "X, or a hash collision was observed". The collision
    scope is every item in the honest closure, under any signature, plus
    digest 0, which is reserved.
  - Honest code learns the hash only through the digests the engine passes.
  - The lifting theorems show that, for claims invariant under rehashing
    outside the observed items (which every exported claim is), the escaped
    form is equivalent to proving X for injective, nonzero hashes.
  - Collision resistance of the deployed hash (including "nothing hashes to
    0") is an assumption.
- **Outputs are pinned on both sides.**
  - Above: safety, accountable safety and nesting (L0), plus provenance (L1).
  - Below: transaction liveness (L0), plus inclusion and growth (L1).

## Residual bindings (per instance)

1. The output ledgers (and L1's chain getters) are what users read.
2. `conflicts` is the slashing rule the chain enforces.
3. The constants in L1, including the premise-side ones (catch-up, η, arming
   lags, outage budget, θ, θrec), are acceptable. Check `catchUp` first: a huge
   catch-up makes the claims about nodes that (almost) never slept. `Valid`
   requires `catchUp ≥ 1`, positive slot length and outage budget, bounds θ
   and θrec, and requires `budget ≤ η` and the fast arming lag no larger than
   the ordinary one.
4. Implementation refinement:
   - the deployed client matches the engine: signature encoding, the seat
     holder mapping (at most one seat per label per validator), structural
     carriage, the seen filter and a persisted seen log, the persisted
     `durable` state, and the cumulative own-plus-relayed mempool;
   - the hash is collision-resistant and never 0 on real items;
   - honest code uses digests only as received.

Generic, read once: **model adequacy**. Clocks; delivery strictly before the
deadline `max a GST + Δ` (with integer time, a release at `t` with `Δ = 1` must
be delivered at `t`, after the ticks), including to nodes that wake later;
restarts only at wakes; unforgeable signatures. Transaction delivery uses
strict deadlines too: an awake honest source's submission at nonnegative `τ`
is held strictly before `max a GST + Δ` for every `a ≥ τ` whose deadline is
within the horizon and whose recipient stays awake on that interval. Healthy
prefix delivery uses `a + Δ`. This assumes reliable dissemination after
acceptance even if the source subsequently sleeps. The canonical scheduler
chooses both events and eager relay, preserving every fixed assignment,
submission function and hash.

## Scope limits

- No validity, fees or throughput for transactions. Ledgers may contain
  unsubmitted transactions, and repeats are removed in L1.
- Recovery exports safety for ready readers only. Recovered liveness is an L1
  block-level field, not in L0. Recovery, and Finality which extends it,
  assume fewer than one third faulty validators and no honest wake at or
  after GST (plan Q13). Finality inherits this fault bound from Recovery.
- At L0, ledgers may contain fabricated transactions: the refutation of a
  fabricated-output family uses L1's block provenance (`outputValid`), which
  has no L0 counterpart.
- Satisfiability of the shape profiles is a theorem, `profile_realizable`: for
  every family, valid constants, nonempty finite `V` and gap `k ≥ 1`, one run
  (with an injective hash) satisfies every regime with active deadlines and a
  nonempty protected outage. It shows the premises can hold, not that a
  protocol satisfying `ShapeClaims` exists. The new Recovery fault bound and
  positive catch-up requirement need no additional realizability condition.
- The collision escape is run-wide.
- Accountability compares two reads in one run, not across runs.
- Unit weights.

## Verification

After module changes, run:

```sh
LAKE_RESTORE_ARTIFACTS=true lake build ConsensusProblem ConsensusModel ConsensusModelProofs ConsensusShape ConsensusShapeTests
lake env lean --run contract/CheckConsensusAxioms.lean
```

The audit imports every `Consensus*` source module, including tests, and checks
all their compiled declarations for dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`. Iteration 3 regression tests cover a
single submission source, sleeping sources, both nesting pairs, injected
relay content, strict deadlines, cumulative ingress across restarts, and the
Δ > 1 catch-up gap.
