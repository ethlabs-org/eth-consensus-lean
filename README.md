# The generic consensus contract: review guide

What it means for a protocol to be a correct consensus protocol, in layers
that are each reviewed once, for every protocol. A protocol that is written as
a value of the generic chain shape and is `Accepted` (it proves its
`ShapeClaims`, its contract is `Realizable`, and it serves a ledger) solves the
layer-0 problem under the assumptions stated in its contract. Reviewing the
generic layers once, plus the protocol's **whole contract** (its premise
terms, starts, latencies, escapes and capability choices, not only its named
numbers) and its skeleton, is enough to know what was proved; see "What
acceptance establishes" for what that review must check.

| Layer | Library | What it fixes |
|---|---|---|
| **L0, the problem** | `ConsensusProblem` | transactions and ledgers; three capabilities (`available`, `stable`, `final`) served by the outputs of an `OutputSchema`; the environment (Δ, GST, awake profile, honest set, horizon, submissions); safety, nesting, transaction liveness, resilience, ready-reader safety, accountability, non-framing; the closed premise language; `Contract` and the headline `ProblemClaims` |
| **L½, the model** | `ConsensusModel`, `ConsensusModelProofs` | a shape-free execution model: identity (PKI), closed selection, credentials, the engine (unit ticks, delivery, sleep and restarts, slashing protection), evidence and hashes; `sysOf`, which makes every protocol family an L0 system; the proofs (`canonical_run`, `honestNeverSlashed`, `sysOf_nonFraming`, lifting) |
| **Blocks** | `ConsensusBlocks` | protocol-free building blocks, each with at least two users: `TimeGrid`, selection premises (`HonestReadyIn`, `PatternRecurrence`), chains (`Header`, linkage, provenance), payload (`encodeTxs`, `ledgerOf`) |
| **L1, the chain shape** | `ConsensusShape` | one generic `ChainShape` (skeleton + state machine), one `compile` onto L½, block-level claims `ShapeClaims`, `refinement`, coverage, the non-vacuity certificate `Contract.Realizable`, and the acceptance endpoint `Accepted` |
| **Values** | `ConsensusShape/Values` | Goldilocks, Streamlet and Tendermint as skeletons + contracts, each with a `*_realizable` certificate (no protocol proofs) |

Design and history: `repos/goldilocks/notes/generic-interface/layers-plan.md`
in the workbench (sections "Iteration 5 plan", "Iteration 5b", "Iteration 5
final design", "Decisions (Francesco, 2026-10-28)"), with the reviews it cites.

## The headline

The acceptance endpoint (`ConsensusShape/Accepted`):

```lean
structure Accepted (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  claims : ShapeClaims F K        -- proved by the protocol
  realizable : K.Realizable F     -- every premise holds in some run, with active service
  serves : O.Serves               -- a final output, or an available one

theorem Accepted.problemClaims (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    ProblemClaims (sysOf O (compiled F) V) (shapeExec F V) K
theorem Accepted.serves_and_delivers (h : Accepted F K) :
    ∃ c g, (c = .final ∨ c = .available) ∧ O.output c = some g ∧ Delivers F K g
```

`delivers` (from `ShapeClaims` and `Realizable` alone): every provided output
puts a transaction into the read of a ready honest reader that was never
submitted it (so it arrived from another node), in some valid, collision-free
run. An instance with no
service (`noService_not_accepted`), a silent service or empty outputs is
therefore not accepted, for every protocol. The underlying theorem is

```lean
theorem refinement (F : ShapeFamily O Info) (K : Contract O ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] :
    ShapeClaims F K → ProblemClaims (sysOf O (compiled F) V) (shapeExec F V) K
```

For every shape family `F`, every contract `K` and every finite validator
type `V`: chain-level claims give the L0 claims of the compiled system, with
the `progress` premise atom interpreted by the shape (`shapeExec`: pattern
recurrence of honest ready proposers on the shape's grid). The bridges are
visible: `ledgerTrace` (reads are `ledgerOf` of the output chains,
definitionally) with `ledgerOf_prefix`; `premiseBridge` (shape premises are L0
premises, definitionally); `proposalLive_txLive` (proposal liveness and partial
synchrony give transaction liveness); laws and non-framing come from L½
(`sysOf_laws`, `sysOf_nonFraming`). `refinement` is not a non-vacuity
statement (a contract with contradictory premises gets it too); `Accepted`
pairs it with `Contract.Realizable`. See "Well-formedness is not non-vacuity".

## Reading order

1. **L0** (`ConsensusProblem/`):
   - `Basic`: `Time`, `Tx`, `Ledger`, `Capability` (the names state the
     intent; what is claimed is the contract's spec), `OutputSchema`, `Env`
     (`AwakeOn`: half-open `[a, b)`; delivery reads awakeness only at the
     deadline), `EnvPoint` (readiness
     `Ready c v t`: honest and awake on the closed `[max 0 (t − c − 1), t]`,
     `AwakeOnClosed`; at a negative `t` the interval is empty, so every honest
     node is ready, which only weakens premises; `readyAt`, `ReadyAbove`,
     `ReadyOfAll`, `EtaSleepy`, `FaultsBelow`, `FaultsAtMost`, `awakeAt`,
     `AwakeOfAll`, `NotReadyAtMost`), `Trace`, `CommLog` (a run's
     communication with opaque messages: sent, received, transaction inbox),
     `System` (with `log : Run → CommLog V Obs`), `InCuts` (cut 0 included
     for `t₀ ≤ 0`).
   - `Network`: the delivery rule, verbatim: *every message an honest node
     sends at `t` is received by every honest node that is awake at
     `max(t, GST) + Δ`, by that time* (`CommLog.Delivers.msgs` for a deadline
     function `dl`; "received by that time" is `Held`: receipt at the
     deadline counts, a wake loses earlier receipts). Re-service to later
     wakers is the separate clause `Delivers.rewake`; transactions
     `Delivers.txs`/`TxHeld`. Instances `PSync g`, `SyncUntil b`,
     `OutageNet b₀ b₁`; `EagerFrom g` (the canonical log shape) meets them
     (`EagerFrom.delivers`, `.psync`, `.syncUntil`); `PSync.mono` (a later GST
     is weaker), `Delivers.reindex`, `AgreesUpTo`. Sends and submissions at
     negative times are not covered (none occur in a valid model run).
   - `Properties`: `Agree`, `Monotone`, `Safe`, `ReadySafe`, `Nested`,
     `ProtectedThrough` (resilience during *and after* the window),
     `CompatibleThrough` (defined, not advertised), `Trace.TxLive`,
     `Trace.TxLiveActive`, `Trace.AccountablySafe` (local to the two
     conflicting reads' views), `NonFraming`, `GloballySlashable`.
   - `Premise`: the closed premise language (`TimeExpr`, `EnvAtom` with the
     counting atoms `faultsBelow`, `faultsAtMost`, `readyAbove`, `readyOfAll`,
     `etaSleepy` and the participation atoms `full`, `noWake`; `Premise` with
     `truth`, `le`, `atTime`, `throughout`, `sync`, `syncUntil`, `progress`,
     `conj`), `ExecProfile`, `eval`, `Premise.WellFormed` (atom domains, and
     **no timing caps** on the horizon or the parameters: the horizon never occurs on the left of
     a `le`, in an `atTime` time or a `throughout` lower end, and a parameter
     is never bounded by a fixed time; `TimeExpr.HorizonFree`,
     `TimeExpr.Fixed`, `Premise.TimesHold.shift`), the named terms in
     namespace `Premise` (`always`, `fromGST`, `after`, `before`, `sleepy`,
     `honestMajority`, `faultsBelowThird`, `outageWindow`, `coverMajority`),
     the resilience parameters `protectedAt`, `outageStart`, `outageEnd`, the
     extremal and sleeper points with `Premise.extremal_realizable` and
     `Premise.sleeper_realizable`.
   - `Atoms`: monotonicity of the atoms and the counting step
     `EnvPoint.two_mul_card_faulty_union_lt` (used with `coverMajority`).
   - `Claims`: `SafetySpec`, `LiveSpec`, `RecoverySpec`, `CapSpec`,
     `Contract` (one `catchUp` per contract, D-1), `CapSpec.Complete`,
     `Contract.WellFormed` (also: liveness and recovery starts are
     horizon-free), `resilienceTarget`, the schema packages `BFTCore`,
     `DACore` and `Serves`, `CapClaims`, `ProblemClaims`,
     `ProblemClaims.agree_of_accountable`, `System.safe_of_escape` (an
     escaped claim with escape `α`, under non-framing and fewer than `α·n`
     faults, is unescaped).
   - `Transfer`: every prefix-based property transfers along a prefix-monotone
     map of reads (used by `refinement` with `ledgerOf`).
2. **L½** (`ConsensusModel/`): `Objects` (`Auth.signed k r` binds key and
   role), `Protocol` (`Public`, `Key`, `SelSpec` = `all | fixed | sized`,
   `Protocol`, `Family`), `Run` (the run data and the engine: `tick`,
   `candidates`, `protects`, `releaseAll`, `mempool`), `Conditions`
   (`ExecutionValid` = schedule and sleep well-formed, `Unforgeable`,
   `SelValid`, `Credentials`; `Run.log` (releases, deliveries, inboxes as an
   L0 `CommLog`), `Served` (engine holding, inclusive), and, temporarily,
   `PartialSynchrony := CommLog.PSync rho.point rho.log E.gst`,
   `HealthyPrefixDelivery := CommLog.SyncUntil …`),
   `Evidence` (`Slashable`, `HashCollision`), `System` (`sysOf`, whose `log`
   is the engine's communication tagged with the environment;
   `modelProfile`). Then the statements of `ConsensusModelProofs`:
   - `sysOf_log_faithful`, `sysOf_delivers_iff`, `Run.held_iff_served`
     (`Faithful`): the system's log is exactly the engine's releases,
     deliveries and inboxes, and on valid runs L0 holding is engine holding
     (restarts are exactly the wakes). Boundary: the log cannot invent sends
     or receipts; nothing says that handlers retain or use delivered data;
   - `canonical_run` (statement `CanonicalRun`): every PKI, admissible
     selection, submission function and hash admits a valid, partially
     synchronous run, healthy at every cut (`canonical_run_causal` adds
     causality);
   - `Run.honestNeverSlashed` and `sysOf_nonFraming` (slashing protection
     makes non-framing a theorem for every protocol), `releaseAll_eq_carried`
     (the guard is a no-op when own-signed objects never conflict);
   - `Run.selected_of_observed` (every signed object honest nodes observed is
     signed by a key selected for its role);
   - lifting: `Run.rehash_trace`, `holds_of_injective` (the collision escape
     adds nothing beyond the injective case); `sysOf_laws`. (`Objects` holds
     the shared structural facts about `parts` and `stateBefore`.)
3. **Blocks** (`ConsensusBlocks/`): `TimeGrid` (slots of `slotDeltas·Δ`),
   `Selection` (`Pattern` with `span`, `ProgressReq` with `gap : ℕ+`,
   `HonestReadyIn`, `PatternRecurrence`, `patternRecurrence_of_all`,
   `PatternRecurrence.exists_inside`), `Chains` (`ParentRef`
   with an explicit `root`, `Header` with `pos`, `input`, `info`, `Linked`,
   `PosIncreasing`, `Provenant`), `Payload` (`encodeTxs`, `ledgerOf`,
   `ledgerOf_prefix`).
4. **L1** (`ConsensusShape/`):
   - `Shape`: `Skeleton` (grid, `proposerSel`, `pollSel`, committee kinds
     with phase and selection), `ShapeRole` (`proposer s`, `duty s k`,
     `poll`), the closed `ProposalRole`, `ShapeDuty`, `ChainShape`,
     `ShapeFamily`;
   - `Compile`: `compile`, `compiled` (duties, roles, selections, the
     engine-written payload);
   - `Run`: `chainTrace`, `HonestProposal`, `ProposalLive`, `OutputValid`,
     `shapeExec`, `ShapePremise`, `premiseBridge`;
   - `Claims`: `Escaped`, `ShapeCapClaims`, `ShapeClaims`;
   - `Payload`: `honestProposal_payload` (an honest proposal's payload is the
     proposer's mempool at the release time);
   - `Refinement`: `ledgerTrace`, `proposalLive_txLive`, `refinement`;
   - `Realizable`: `coverage`, `Witness`, `ProgressActive`, `LiveActive`,
     `ResilienceActive`, `Contract.Realizable`, `witness_at`,
     `premise_realizable`, `resilience_realizable`, `active_relay`;
   - `Accepted`: `Accepted`, `Accepted.problemClaims`, `Delivers`,
     `delivers`, `Accepted.serves_and_delivers`.
5. **Values** (`ConsensusShape/Values/`): `Common` (`Affine`, `bftCore`),
   `Goldilocks` (`goldilocksSkeleton`, `GoldilocksParams`,
   `GoldilocksParams.standard`, `goldilocksContract`,
   `goldilocksContract_wellFormed`, `goldilocks_realizable`), `Streamlet`
   (`streamlet_realizable`; safety escaped by and accountable for a third),
   `Tendermint` (indexed by a fault count `m`, latency affine in `m`;
   `tendermint_realizable`).

## Why the meaning is fixed below the protocol

A protocol supplies a state machine and its numbers; it supplies no predicate
that a claim or premise evaluates.

- **Closed premise language.** Every premise is a term of `Premise`:
  environment atoms (L0 vocabulary), `sync`/`syncUntil` (fixed by the
  execution model), and `progress` (fixed by the shape: `PatternRecurrence`
  over the skeleton's proposer roles and grid). There is no disjunction or
  negation, so the environment part of a well-formed premise holds at every
  large enough extremal point (population `n ≥ N`) at which its timing
  constraints (`TimesHold`, the `le` atoms) hold
  (`Premise.extremal_realizable`). The timing constraints themselves can be
  contradictory (`contradictory_wf_not_realizable`: `1 ≤ 0` is well-formed).
- **Closed selection and identity.** Keys are `Fin n`; the run's PKI is a
  bijection `key : Fin n ≃ V`. Who acts in a role is run data `sel`, admissible
  for the protocol's closed `SelSpec` (`all`, `fixed S`, `sized m`). Honest code
  never sees `sel`, the PKI, the honest set, GST, the awake profile or the hash.
- **Credentials.** `ExecutionValid.credentials`: every signed object inside a
  delivered object is signed by a key selected for its role, faulty signers
  included (`Run.selected_of_observed` extends it to everything observed).
  Signatures bind their role, so a signature cannot be replayed in another
  duty.
- **Slashing protection in the engine.** The engine refuses an own-signed
  candidate that conflicts, under the protocol's `conflicts`, with itself or
  with an own-signed object in the closure of `seen` (`protects`); `seen`
  survives restarts. Hence `Run.honestNeverSlashed` and L0 non-framing
  (`sysOf_nonFraming`) hold for every protocol. A protocol whose `conflicts` is
  always true silences itself and fails liveness (`conflictsTrue_silent`).
- **Engine-written payload.** `compile` writes every proposal's `input :=
  encodeTxs mempool` (and a slot proposal's position `pos := s`); the mempool is
  the node's cumulative own and relayed transactions. Reads are `ledgerOf` of
  the output chains (`ledgerTrace`).
- **Closed `ProposalRole`.** Provenance (`OutputValid`) accepts a header only
  if it was seen signed as the proposer of its own position (`proposer h.pos`)
  or in the poll role. Committee signatures never make a header.
- **Poll mode (decision T).** Besides slot proposals, a shape may propose at
  any unit tick in the `poll` role, at a position (height) and with `info`
  (round) it chooses; `pollSel := .fixed ∅` disables polling and then
  `Credentials` forbids every `poll` signature (`poll_disabled_forged`). The
  engine still writes the payload (`poll_proposal_local_height`).
- **No hooks.** No protocol-supplied author, decoder, schedule, hash, premise or
  evidence collector; evidence and conviction are fixed around the one rule
  `conflicts`, and the excuse is an observed hash collision.
- **Outputs are pinned on both sides.** Above: safety, nesting, local
  accountability (L0) and provenance (`OutputValid`). Below: transaction
  liveness (L0) through `ProposalLive`.

## Well-formedness is not non-vacuity (D-24)

`Contract.WellFormed` (the first field of `ShapeClaims`) is structural: every
premise atom has its parameter in range, every escape and accountable fraction
is in `(0, 1]`, no premise caps the horizon or a parameter (`le horizon e`,
`le protectedAt zero`, `atTime horizon a` are rejected:
`horizonCap_rejected`, `protectedAtCap_rejected`, `gstCap_rejected`,
`atHorizon_rejected`), and no liveness or recovery start mentions the horizon
(`horizonStart_rejected`). So timing constraints that hold keep holding on
every longer run and for later parameters (`Premise.TimesHold.shift`): no
timing constraint restricts the claims to runs shorter than a fixed time (the
"time bomb") or to early protected reads. Participation atoms over fixed times
could still confine where an outage can happen; `Contract.Realizable` closes
that for resilience by asking for active outages at arbitrarily late
protected reads (below). A well-formed contract can still
have an unsatisfiable premise (`contradictory_wf_not_realizable`), and then its
claims say nothing.

An accepted instance (`Accepted`) is therefore:

1. `ShapeClaims F K` (proved by the protocol);
2. `Contract.Realizable F K` (a per-value certificate): every premise of every
   provided capability, for every index, has a `Witness` run (a faulty and an
   honest validator, valid, no hash collision, nobody convicted by honest
   evidence, and for each `progress` occurrence a recurrence window followed
   by the pattern's span inside the horizon, so an honest ready pattern is
   selected at in-horizon slots, `PatternRecurrence.exists_inside`), with
   active service: `LiveActive` (a transaction submitted at `t` to one awake
   honest node, and a different honest reader that was never submitted it and
   is ready at some `t'` with `max t GST + Δ + D·Δ ≤ t' ≤ horizon`, not
   necessarily at that earliest deadline; `active_relay`: in a run where
   everyone is always awake, that reader receives it by relay) and
   `ResilienceActive` (`0 ≤ T < b₀ < b₁ ≤ horizon`, an honest validator asleep
   at some time of `[b₀, b₁)`, and an honest reader awake throughout
   `[max 0 (b₀ − catch-up − 1), b₁]`), for every `k` with a protected read
   `T ≥ max 0 GST + k·Δ`, so the premise does not confine real outages to a
   bounded period;
3. `O.Serves`: a final output, or an available one.

`coverage` (generic) adds: any well-formed point, with any PKI and admissible
selection, satisfying a premise's environment and progress parts is exactly
the point, PKI and selection of a valid, collision-free, conviction-free run
satisfying the whole premise. The protocol cannot make a premise harder to
meet than its environment and progress parts.

`goldilocks_realizable` (for well-formed `GoldilocksParams`),
`streamlet_realizable` and `tendermint_realizable` hold for every family with
the value's proposer selection size and grid (Tendermint: every family). They
prove premise realizability, not the existence of a correct protocol. The
witnesses are built generically: at the extremal point (`premise_realizable`)
and, for resilience, at the sleeper point, where one honest validator sleeps
at the outage start (`resilience_realizable`; the premise's atoms must be
counting atoms).

## What acceptance establishes (and what it does not)

`Accepted F K` means **"`F` meets contract `K`"**: every claim of `K` holds,
under `K`'s premises, on every valid run, and every premise is met by some run
with active service. It does not mean "`K` is the intended consensus service".
The protocol chooses whole premise programs, not only numbers, so a reviewer
must read, for each provided capability:

- **the full premise terms**: which environment, synchrony and progress
  conditions each claim assumes. Well-formedness excludes timing caps on the
  horizon and the parameters, and realizability excludes outages confined
  relative to fixed times, but a premise may still be stronger than intended
  (for example `full` participation where a fraction was meant, safety under
  `sync`, or a resilience premise that confines the outage relative to the
  horizon or to another parameter);
- **the starts, latencies and catch-up**: from when transactions are live,
  how fast, and which readers count (a huge `catchUp` restricts readers to
  nodes that almost never slept);
- **the escapes and accountability**: which safety claims may be escaped by
  global slashability, and whether `accountable` is specified at all (it is
  optional; a `final` capability without it, or with a synchronous safety
  premise, is not "safe under asynchrony, accountable": the capability names
  state the intent, the spec states the claim);
- **the capability choices**: which capabilities are provided and which
  outputs serve them (aliasing is allowed);
- **the skeleton**: grid, proposer and committee selections, phases, and what
  `progress` premises demand of the adversarial selection (`HonestReadyIn`
  needs every selected key honest and ready).

`Contract.Realizable` is existential activity, not regime adequacy. It shows
that each premise can hold together with a faulty validator and active
service; it does not show that the premises cover the intended operating
regime; the supplied witness producers (`premise_realizable`,
`resilience_realizable`) use one faulty validator in a large population, so
the values' certificates never test the advertised fault bound; it does not
certify safety and liveness premises jointly in one run; and a resilience
witness does not show that the protected read is nonempty (liveness does,
separately). `coverage` cannot repair this:
it assumes the premise's environment and progress parts. A reviewed "service
profile" (intended regimes that provably imply the advertised premises) would
close this gap and is future work.

## Adversary model

Static and all-knowing: the honest set is fixed per run; faulty validators sign
anything with their own keys (only `Unforgeable` and `Credentials` bind them),
and the scheduler chooses the events, relay and hash within the execution
conditions. There is no adaptive corruption and no hook for it (scope limit).
Selection is run data, chosen with the honest set; hiding it from honest code
buys nothing against this adversary.

## Model-adequacy bindings (generic, read once)

- **PKI:** one key per validator, known to all (`key : Fin n ≃ V`).
- **Credentials:** the deployed membership mechanism (public committee lists,
  VRF proofs, …) is sound for the selection (`Credentials`).
- **Signatures:** unforgeable, binding key and role (`Unforgeable`,
  `Auth.signed`).
- **Slashing protection:** the deployed client implements `protects` and
  persists its seen log across restarts (as an EIP-3076 database does).
- **Durable relay:** a transaction submitted to an awake honest node at `τ`
  is held, by `max a GST + Δ`, by every honest node awake at that deadline,
  for every `a ≥ τ`, including after the source sleeps; the cumulative inbox
  survives restarts.
- **Δ known:** honest code knows `Δ` (a positive integer) and `n`.
- **Unit ticks:** every awake honest node ticks at every integer time
  (`ScheduleWellFormed`); the unit divides Δ.
- **Endpoint delivery (L0 `CommLog.PSync`):** what an honest node releases at
  `t` is held, by `max t GST + Δ` (receipt at the deadline counts), by every
  honest node awake *at* that deadline; and (re-service, `rewake`) by every
  honest node awake at `max a GST + Δ`, for every `a > t`. `SyncUntil` uses
  `a + Δ`. A message received at the deadline is processed at the next tick
  (order within one time, below); that slack is the protocol's
  (`proposalLive_txLive` absorbs it with the strict `τ > …` of
  `ProposalLive`).
- **Restarts** happen exactly at wakes; a receipt before a sleep does not serve
  after the wake.
- **Order within one time:** restarts, then ticks, then deliveries
  (`Event.phase`, `Event.keyLe`).
- **Collision resistance** of the deployed hash on real items, including
  items that honest code itself chooses (honest gossip could otherwise search
  for collisions); honest code uses digests only as received.

## Residual bindings (per instance)

1. The outputs (and L1's output chains) are what users read.
2. `conflicts` is the slashing rule the chain enforces.
3. The whole contract is the intended service ("What acceptance
   establishes"): premise terms, starts, latencies, escapes, capability
   choices, and the named numbers (catch-up, fractions, lags, budgets; for
   Goldilocks, `GoldilocksParams`, with `GoldilocksParams.standard` fixing the
   standard fractions).

## Scope limits

- No transaction validity, fees or throughput; ledgers may contain
  unsubmitted transactions.
- No probabilistic or randomized protocols, no proof of work, unit weights
  only, no non-validator readers, no responsiveness claims (unit ticks do not
  block them, but none is stated).
- No adaptive corruption.
- Gasper's partitioned selection (`part`) is deferred (decision G).
- No public schedules: `Skeleton.proposerSel` is one `SelSpec` for every slot
  and the run picks the selection adversarially, so round-robin or RANDAO
  duties are modelled as worst-case `.sized 1`, with liveness resting on a
  recurrence premise.
- No committee premise (`CommitteeHonest` is deferred): only `.all` and
  `.fixed` committee selections can support claims; a `.sized m` committee
  with `m < n` may be all faulty.
- Phases are multiples of `Δ` (`Skeleton.phase`), although ticks are unit
  ticks.
- For `pollSel := .all`, poll provenance accepts any validator's header:
  `OutputValid` is weaker for poll shapes.
- Latencies cannot depend on the population; they can depend on a fault count
  through an index and the `faultsAtMost` atom (Tendermint: round robin meets
  an honest leader within `m + 1` rounds when at most `m` are faulty).
- A Tendermint locked-value re-proposal carries the original signed header:
  the engine writes the payload of every new header.
- Resilience (`ResilienceReader`) covers readers caught up before the outage
  that stay awake, and readers caught up after it (awake throughout
  `[t − c − 1, t]` with `b₁ ≤ t − c − 1`). A reader that wakes during the
  outage is covered once it has caught up after the outage, not before:
  there is no delivery guarantee during the outage.
- The collision escape is run-wide; accountability compares two reads in one
  run, not across runs.
- At L0, ledgers may contain fabricated transactions; the refutation of a
  fabricated-output family uses L1 provenance (`fabricated`).

## FG-SA migration obligations

The Goldilocks value's committee kinds, phases and finality pattern are
placeholders until FG-SA (the `AvailableChain*` libraries) is migrated onto the
shape. The migration must discharge:

1. **Cover binding (D-17).** A validator `Ready c v b₀` at the outage start is
   covered by FG-SA's join schedule (`v ∈ coveredNodes fast b₀`, with
   `c = catchUp·Δ` covering the join window; needs `syncUntil b₀`). Then FG-SA's
   `OutageE1` (`2·|faulty ∪ W| < n`) follows from the premise term
   `coverMajority` by `EnvPoint.two_mul_card_faulty_union_lt`.
   The `etaSleepy` atom is the one atom that only Goldilocks uses (its
   before-the-window participation); the migration should try to replace it
   with `readyAbove`/`coverMajority`, as D-17 did for the during-window term.
2. **Post-window persistence.** `ProtectedThrough` asks for persistence after
   the window too, for continuously awake readers, under the post-window terms
   of the resilience premise (`sync`, GST at most `restoreLag·Δ` after the
   outage end, participation above `afterAbove` from then on).
3. **Quorums and Evidence blocks (D-13).** `quorum_inter`, equivocation (which
   compares the signed statement, not carriage) and FFG evidence, with
   `accountable_of_certs`, are added as blocks when their first users appear.

## Decisions of iteration 5 (D-n)

- **D-1 (design amendment).** One `catchUp` per `Contract`, shared by every
  claim of every capability (the final design put catch-up inside each
  liveness spec). Resilience, recovery and the D-17 cover term must use the
  same reader eligibility to compose; moving the field into `CapSpec` is a
  local change if a target needs two.
- **D-2** Progress through abstract `Prog`/`Idx` at L0; chain shapes use
  `ProgressReq` (pattern with `offsets ≠ []`, `gap : ℕ+`), admissibility by type.
- **D-3** Premise parameters `σ`; every claim quantifies all `σ`.
- **D-4** Safety (and recovery's safety half) may have a global-slashing
  escape `Option ℚ`; liveness never; local accountability is unconditional.
- **D-5** `ProtectedThrough`: during and after the window `[b₀, b₁)`; eligible
  readers (`ResilienceReader`) are caught up before the window and awake since,
  or caught up after it (Francesco, 2026-10-28).
- **D-6** A stable capability has both a resilience premise and a recovery
  spec (`CapSpec.Complete`); `final` always has monotonicity; nesting for every
  provided ordered pair.
- **D-7** Provided ⇔ specified is a claim field.
- **D-8** `Contract.WellFormed` is the first claim field.
- **D-9** `InCuts` includes cut 0 for `t₀ ≤ 0`.
- **D-10** The iteration-4 L0 machinery (assumption records, bounds, claim
  keys, fast paths, η-inclusion) is deleted; standard values are premise terms
  and contract values.
- **D-11** `restore` receives the own key.
- **D-12** `SelSpec := all | fixed | sized`; `HonestReadyIn` requires a
  nonempty, all-honest-and-ready selection; nonemptiness lemmas are
  conditional.
- **D-13** Blocks only with ≥ 2 users; Quorums/Evidence deferred.
- **D-14** L1 liveness is `ProposalLive` (keyed by the release time); the
  strict-prefix clause is dropped.
- **D-15** One proposer selection for all slots, committee kinds with phases,
  a poll selection.
- **D-16** Streamlet and Tendermint are final-only; Goldilocks keeps three
  outputs `confirmed`/`stable`/`finalized`.
- **D-17** `coverMajority` + the counting lemma replace the during-window
  η-term for FG-SA's outage bound.
- **D-18** A sixth library `ConsensusBlocks`.
- **D-19** No deadline-in-horizon premise: conclusions past the horizon are
  vacuous anyway; realizability witnesses supply reachable deadlines.
- **D-20** Every liveness and recovery premise of a shape contract contains
  `sync` (`ShapeClaims.liveSync`).
- **D-21** Phases live in the skeleton; epochs deferred.
- **D-22** Recurrence starts at time 0 (`max start 0`).
- **D-23** Protection fires on own-signed candidates only.
- **D-24** Well-formedness ≠ non-vacuity (`Contract.Realizable`).
- **D-25** Poll proposals with a closed `ProposalRole`.
- **D-26** (final review) `Accepted` = `ShapeClaims` + `Contract.Realizable` +
  `OutputSchema.Serves` is the review endpoint; `delivers` excludes silent and
  empty outputs for every protocol.
- **D-27** (final review) No timing caps on the horizon or the parameters in
  well-formed premises, and horizon-free starts (`TimesHold.shift`).
- **D-28** (final review) `ResilienceActive` requires an honest sleeper during
  the outage, at arbitrarily late protected reads; `Witness` requires an
  honest validator; `ProgressActive` counts the pattern's span.
- **D-29** (final review) `faultsAtMost m` (an absolute fault bound) lets
  latencies depend on the fault count (Tendermint); the inclusive
  `readyOfAll` flag is removed.

## Tests (`ConsensusShapeTests/`)

- `Problem`: every L0 property has teeth; `InCuts` at cut 0; relay vocabulary;
  three-output nesting; local accountability is not implied by the global
  escape (`local_vs_global`; the L0 lemmas `System.agree_of_accountable` and
  `ProblemClaims.agree_of_accountable` are in `ConsensusProblem/Claims`).
- `Premise`: named terms, atom domains (`not_wellFormed_readyOfAll_one`,
  `not_wellFormed_faultsAtMost_zero`), no caps (`horizonCap_rejected`,
  `protectedAtCap_rejected`, `gstCap_rejected`, `atHorizon_rejected`,
  `horizonStart_rejected`, `outageWindow_shift`), the extremal point, the
  cover counting step, the after-window part of resilience
  (`protected_after_window`), `provided_mismatch`.
- `Model`: relayed ingress and cumulative mempool, a forged role violates
  `Credentials` (`forged_role_invalid`), `unit_ticks`, slashing protection
  (`conflictsTrue_releases_unsigned_only`).
- `Blocks`: grids, recurrence from any start, `recurrence_has_teeth`,
  `ledgerOf`.
- `Shape`: compiled roles and duties, `poll_disabled_forged`,
  `poll_proposal_local_height`, `poll_duty_every_tick`.
- `Leaks`: protocols that do nothing (`silent`), propose without outputting
  (`proposeButGenesis`), fabricate outputs (`fabricated`) or silence
  themselves by their slashing rule (`conflictsTrue_silent`) fail
  `ShapeClaims`; the positive control `recorder_live_testK` (also with negative
  GST) meets the obligation that refutes them.
- `Realizable`: `coverage_keeps_selection`, `contradictory_wf_not_realizable`,
  `confinedOutage_not_realizable` (a well-formed resilience premise that
  confines outages to before time 100 is not realizable).
- `Controls`: two canonical runs of a Goldilocks-skeleton family at index 1,
  for `goldilocksContract` with `GoldilocksParams.standard` and arbitrary
  well-formed numbers (premise tests, not feasible performance bounds).
  `positive_controls` (everyone awake): every safety, liveness and recovery
  premise as an active witness, with a relayed submission, ready readers and
  in-horizon deadlines. `resilience_control`: the resilience premise as an
  active witness in a run where an honest validator is asleep inside the
  outage `[b₀, b₁)` while the reader stays eligible (a separate run: with
  GST 0 and full participation, recovery forbids any sleep). Every other index
  is covered by `goldilocks_realizable`.
- `Vacuity`: `zero_catchUp_not_shapeClaims`, `escape_zero_rejected` (also
  `recoveryEscape_zero_rejected`, `accountable_zero_rejected`),
  `stable_without_recovery_rejected`, `noSync_live_rejected` (also
  `noSync_recovery_rejected`), with the
  control `goldilocks_structural`; `noService_not_accepted` (no final or
  available output); `credential_forgery_excluded` (a delivered
  proposal signed by an unselected key violates `ExecutionValid`, with the
  concrete run `forgedProposal`).

## Verification

```sh
cd /srv/work/fradamt/goldilocks/generic-interface
LAKE_RESTORE_ARTIFACTS=true lake build ConsensusProblem ConsensusModel ConsensusModelProofs ConsensusBlocks ConsensusShape ConsensusShapeTests
lake env lean --run contract/CheckConsensusAxioms.lean
```

The audit imports every `Consensus*` source module under `contract/`,
including the tests, checks that the main theorems exist, and checks every
compiled declaration for axioms outside `propext`, `Classical.choice` and
`Quot.sound`. It prints `standard axioms only: true`.
