# The generic contract, in three layers: review guide

What it means for a protocol to be a correct consensus protocol, in three
layers, each reviewed once:

| Layer | Library | What it fixes | Lines |
|---|---|---|---|
| **L0, the problem** | `ConsensusProblem` | transactions, ledgers, three outputs; the environment (Δ, GST, awake profile, honest set, private submissions); safety, nesting, transaction liveness, persistence, accountability, non-framing; the claim form | ~400 |
| **L½, the model** | `ConsensusModel` | a shape-free execution model: protocol interface, engine, delivery, sleep and restarts, unforgeability, evidence, hashes; `sysOf F`, which makes any protocol family an L0 system | ~600 |
| **L1, our shape** | `ConsensusShape` | slots, one proposer per slot, full committees, block headers and chains, regimes, constants, `compile` onto L½; block-level claims `ShapeClaims`; the profile and bounds of the L0 claims | ~750 |

The headline is the refinement theorem: for every family `F` of the shape,
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
     promised under);
   - `ShapeClaims`.

## Why the meaning is fixed below the protocol

- **No protocol word in any premise.** Every premise is environment
  vocabulary (L0), an execution condition (L½: valid execution, delivery), or
  a reviewed shape premise (L1: recurrence). The protocol supplies no hook,
  author, decoder, schedule, evidence predicate or hash. `canonical_run`
  makes the execution part satisfiable for every protocol.
- **Signing and keys.**
  - The engine signs. Seats are held by validators through the run's holder
    map, which is an **embedding per label**: no validator holds two seats of
    one label, so a quorum of seats is a quorum of distinct validators.
  - Accountability counts validators, with no committee premise.
- **Transactions are private per node.** The engine gives each node only its
  own submissions. L1 puts a proposer's mempool into its proposal, so a ledger
  can only contain a submitted transaction through communication.
- **Hashes are arbitrary run data.**
  - Escaped claims read "X, or a hash collision was observed". The collision
    scope is every item in the honest closure, under any signature, plus
    digest 0, which is reserved.
  - Honest code learns the hash only through the digests the engine passes.
  - The lifting theorems show that the escaped form is equivalent to proving X
    for injective, nonzero hashes.
  - Collision resistance of the deployed hash (including "nothing hashes to
    0") is an assumption.
- **Outputs are pinned on both sides.**
  - Above: safety, accountable safety and nesting (L0), plus provenance (L1).
  - Below: transaction liveness (L0), plus inclusion and growth (L1).

## Residual bindings (per instance)

1. The output ledgers (and L1's chain getters) are what users read.
2. `conflicts` is the slashing rule the chain enforces.
3. The constants in L1, including the premise-side ones (catch-up, η, arming
   lags, outage budget, θ, θrec), are acceptable.
4. Implementation refinement:
   - the deployed client matches the engine: signature encoding, the seat
     holder mapping (at most one seat per label per validator), structural
     carriage, the seen filter and a persisted seen log, the persisted
     `durable` state, and the mempool;
   - the hash is collision-resistant and never 0 on real items;
   - honest code uses digests only as received.

Generic, read once: **model adequacy**. Clocks; delivery within Δ after GST,
including to nodes that wake later; restarts only at wakes; unforgeable
signatures.

## Scope limits

- Transaction liveness needs a transaction submitted to **every** honest node.
  There is no tx gossip in the shape.
- No validity, fees or throughput for transactions. Ledgers may contain
  unsubmitted transactions, and repeats are removed in L1.
- `finalized ⪯ stable` is not promised (plan Q9). Only `stable ⪯ confirmed`.
- Recovery exports safety for ready readers only. Recovered liveness is an L1
  block-level field, not in L0. Recovery assumes no honest wake at or after
  GST (plan Q13).
- The collision escape is run-wide.
- Accountability compares two reads in one run, not across runs.
- Unit weights.
