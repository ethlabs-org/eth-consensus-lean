# The generic contract, in three layers: review guide

> **Stale (iteration 5 in progress).** This guide describes iteration 4. Layer 0
> has been replaced (capabilities, premise language, per-capability contracts;
> see `ConsensusProblem/{Basic,Properties,Premise,Atoms,Claims}.lean`) and layer 1
> is being rebuilt; the guide is rewritten at the end of iteration 5.

What it means for a protocol to be a correct consensus protocol, in three
layers, each reviewed once:

| Layer | Library | What it fixes |
|---|---|---|
| **L0, the problem** | `ConsensusProblem` | transactions, ledgers, three outputs; the environment (Δ, GST, awake profile, honest set, transaction submissions); safety, nesting, transaction liveness, persistence, accountability, non-framing; the claim form |
| **L½, the model** | `ConsensusModel` | a shape-free execution model: protocol interface, engine, delivery, sleep and restarts, unforgeability, evidence, hashes; `sysOf F`, which makes any protocol family an L0 system |
| **L1, our shape** | `ConsensusShape` | slots, one proposer per slot, full committees, block headers and chains, regimes, constants, `compile` onto L½; block-level claims `ShapeClaims`; the profile and bounds of the L0 claims |

The headline is the refinement theorem `refinement`: for every family `F` of
the shape and every finite nonempty validator type `V`,
`ShapeClaims F A C → ProblemClaims (sysOf (compile ∘ F) V) A (bounds C) (profile A)`.
A protocol that proves `ShapeClaims` therefore solves the L0 problem under L1's
reviewed assumptions.

Design and history: `notes/generic-interface/layers-plan.md` (and `plan.md`,
`hash-plan.md`) in the workbench, with the Astra and Opus reviews they cite.
The older single-layer contract (`AvailableChainContract*`) is being replaced
and will be removed.

## Reading order

1. **L0** (`ConsensusProblem/{Basic,Assumptions,Properties,Claims,Monotonicity}`). Check that agreement,
   monotonicity, nesting, transaction liveness, persistence, accountability
   and non-framing say what they should. Claims use `EnvAssumption A key ∧ Exec X key` on valid runs.
   `ClaimKey` carries recurrence gaps or outage times; L0 fixes the mapping
   to the closed `sync`, `healthyUntil`, and `recurrent` slots. Ordinary and
   fast outages have separate claims, so their branches cannot mix.
   Unconditional claims use `HoldsAlways`. Recovery and finalized
   accountability additionally allow `Slashed A.accFrac`, counting validators
   convicted by the whole honest evidence set. The layers below fix the
   interpretation of delivery, recurrence, evidence, and the collision excuse.
2. **L½** (`ConsensusModel/{Objects,Protocol,Run,Conditions,Evidence,System}`).
   It fixes the meaning of L0's abstract fields:
   - **validity** is `ExecutionValid`;
   - **reads** are the protocol's output ledgers at event cuts;
   - **evidence** is the objects an honest node has seen, convicted under the
     protocol's `conflicts` rule through the run's PKI (`signerOf`);
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
   - `profile A` (the fixed slot interpretation), `bounds C`,
     `exec_conservative`, `profile_realizable`, and `Regression`;
   - `ShapeClaims`.

## Why the meaning is fixed below the protocol

- **No protocol-supplied premise predicate.** Every premise is environment
  vocabulary (L0), an execution condition (L½: valid execution, delivery), or
  a reviewed shape premise (L1: recurrence over the shape's slot timing). The
  execution conditions evaluate what the protocol does, but the protocol
  supplies no hook, author, decoder, schedule or hash, and evidence collection
  and conviction are fixed around its one slashing rule, `conflicts`.
  `canonical_run` makes delivery satisfiable for every protocol.
  `exec_conservative` preserves every well-formed environment point admitted
  by the L0 environment premise, while choosing ready proposers. Its domain
  requires positive recurrence gaps and, for recovery/finality coverage,
  nonnegative GST. These guards do not enter `ProblemClaims` or the regimes.
- **Signing and keys.**
  - The engine signs, with the node's own key in the duty's role, and only
    if the run's selection (`sel`, admissible for the protocol's closed
    `selSpec`) contains that key. Keys map to validators through the run's
    PKI, a **bijection** `key : Fin n ≃ V`, so distinct keys are distinct
    validators. Signatures bind their role (`Auth.signed k r`).
  - `Credentials` (an execution condition): every signed object inside a
    delivered object is signed by a key selected for its role, faulty signers
    included; `Run.selected_of_observed` extends this to everything honest
    nodes observed.
  - Slashing protection is the engine's, generic over `conflicts`
    (`protects`): an own-signed candidate that conflicts with itself, or in
    either order with an own-signed object in the closure of `seen`, is not
    released. `seen` survives restarts (as an EIP-3076 slashing-protection
    database does; that the deployed client keeps it is model adequacy).
    Hence `Run.honestNeverSlashed` and L0 non-framing (`sysOf_nonFraming`)
    are theorems for every protocol, not obligations.
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
2. `conflicts` is the slashing rule the chain enforces, and the deployed
   client implements `protects` and keeps its log across restarts.
3. Check **A first**, then the service bounds in `Constants`. Use
   `Assumptions.standard catchUp eta armingLag fastArmingLag outageBudget
   stableEtaAbove recoveryReadyAbove recoveryFull`, or publish named numbers
   for every field. Standard fixes sleepy participation to ½, fast faults
   to <¼, inclusive fast-outage participation to ½, finality participation
   to >⅔, accountability to ⅓, and no wakes after GST. Timing, η-sleepiness,
   recovery participation and full-recovery policy remain explicit instance
   choices. A huge `catchUp` restricts readers to nodes that almost never slept.

   `Assumptions.WellFormed` checks domains, not correctness: positive catch-up
   and outage budget, nonnegative ready thresholds, positive fault/accountable
   fractions, and every fraction strictly below 1 (inclusive thresholds too).
   `Constants.Valid` only requires positive slot length; the previous
   `budget ≤ eta`, lag ordering, and ½-to-¾ threshold restrictions are gone.
   The positive catch-up obligation remains in `ShapeClaims`, supporting the
   relay refinement, without requiring all of `WellFormed` for correctness.

   `Assumptions.Weaker A A'` compares admitted environments componentwise
   with equal catch-up. A claim under the weaker premises `A` restricts to
   `A'`; the accountable fraction has the opposite order because it is a
   conclusion. `ProblemClaims.mono` proves this for a fixed slot interpretation.
4. Implementation refinement:
   - the deployed client matches the engine: signature encoding (binding the
     role), the PKI (one key per validator), membership proofs that realize
     `Credentials`, structural
     carriage, the seen filter and a persisted seen log, the persisted
     `durable` state, and the cumulative own-plus-relayed mempool;
   - the hash is collision-resistant on real items;
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
- Recovery exports ready-reader safety, or a collision, or `A.accFrac` of
  validators convicted. It has no fault-cap premise. Its full-participation
  and no-wake policies are explicit booleans in A. Finality adds participation
  and no fault cap; standard >⅔ readiness implies <⅓ faults. Recovered
  liveness remains an L1 block-level obligation.
- At L0, ledgers may contain fabricated transactions: the refutation of a
  fabricated-output family uses L1's block provenance (`outputValid`), which
  has no L0 counterpart.
- `profile_realizable` quantifies over every well-formed A, every family
  and service constants, and positive recurrence gaps. It chooses a large
  finite population with a **nonempty faulty set**. Each claim has a valid
  collision-free run preserving the witness environment, with ready readers,
  a ready proposal after recovery/finality startup, reachable service deadlines,
  an active recurrence window, and a transaction actually relayed to a node
  with no local submission. Both outage branches have nonempty intervals.
  The environment points satisfy `EnvPoint.WellFormed` (nonnegative horizon).
  This proves premise realizability, not existence of a correct protocol.
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

Iteration 4 tests cover the rational thresholds, named standard regimes,
weaker-premise transport, accountable escapes, and the two retained obstruction
regressions: an inclusive threshold of 1 excludes nonempty faults, and a
negative horizon cannot be covered by a valid execution.
