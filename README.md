# The generic consensus contract: review guide

## The definition of a good protocol

A protocol is **good** when its system `S` (with its progress reader `X`)
meets a contract `K` that supplies **only numbers**:

```lean
structure Good (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  behaviour  : Behaviour S X K                    -- the fixed property table, under fixed regimes
  adequate   : S.Adequate X                       -- the system is not vacuous
  realizable : 5 ≤ Fintype.card V → Realizable S X K  -- every regime is met, with active claims
```

(`ConsensusProblem/Good.lean`.) All three parts are L0 definitions. The
property list, the regimes, the network rule and the thresholds' admissible
range are fixed. An instance chooses only the numbers in `Params`, and a
progress requirement for each capability and index. It writes no predicate
that a claim or regime evaluates.

- **`Behaviour`** is the property table below. Each property holds on every
  valid run in its regime, unless the run's excuse holds (`System.Holds`; in
  the model the excuse is an observed hash collision). There are no other
  escapes. `Behaviour` also bundles the system's laws (`S.Laws`), the
  numbers' admissibility (`admissible`) and the schema condition (`serves`).
- **`Adequate`** rules out a system that is vacuous by construction:
  - `admits`: every environment has admissible external data;
  - `covers`: every environment point with `0 ≤ horizon`, every admissible external
    datum and every GST `g` have a valid, excuse-free run with that point.
    Its log is eager from `g`: synchronous for `g ≤ 0`, asynchronous before
    `g`, silent for `g` past the horizon. The run carries every progress
    requirement that held for the point and the data;
  - `prefixClosed`: the prefix of a valid run up to any `b ∈ [0, horizon]` is a valid run
    with the same reads, views and log up to `b`, no new excuse, and the same
    progress on windows that end by `b`.
- **`Realizable`** (at least five validators): every regime is met by a clean
  witness. A witness is valid, has no excuse, and has a faulty and an honest
  validator. The witnesses exist at every `Δ`, at every GST `g ≥ 0` (healthy: with a
  log that is silent before the GST), and for outages armed arbitrarily late.
  Each witness has active claims (the sleepy and healthy witnesses bundle
  regime, progress and `TxLiveActive` as `SleepyLive` and `HealthyLive`):
  - `TxLiveActive`: a transaction to serve, read by a different honest node
    that was never submitted it;
  - `SafeActive`: two ready readers, one of them at two cuts;
  - `OutageActive`: a ready source, a real sleeper inside the window and an
    eligible reader.

  Two **stress witnesses** exercise liveness with many honest validators
  asleep, so a progress requirement cannot quietly demand near-full
  participation. For every provided output, at *some* index:
  - `sleepyStress` (available, stable): a sleepy witness where at most
    `⌊2n/3⌋` honest validators are ever awake (never an awake
    supermajority), with `prog[0, horizon]` and `TxLiveActive`;
  - `healthyStress` (every provided output): a healthy witness from every
    GST where at most `⌊2n/3⌋ + 1` honest validators are ever awake (a
    minimal awake supermajority).

  A contract whose available progress is "at most one validator not ready"
  at every index is therefore not realizable
  (`notReadyAtMost_one_not_realizable`): a protocol that halts when two
  validators sleep is not dynamically available.

For shape protocols, `Accepted.good` (L2) proves all three parts. The good
protocols we accept are
`Good (sysOf O (compiled F) V) (shapeProgress F V) K`, for every finite `V`.

### The property table (`Behaviour`, `FinalClaims`, `DAClaims`)

Notation: `c = catchUp·Δ`; `heal(cap,i,g) = max g 0 + heal cap i·Δ`;
`ready(g) = readyFrom c g = max g 0 + c + 1`; `lat = latency cap i·Δ`;
`prog[a,b]` = the progress requirement of `cap` at index `i` on `[a, b]`;
`HC` = the excuse.

| Output | Property | Regime | Claim (`∨ HC` unless "always") |
|---|---|---|---|
| all | non-framing | always | honest validators are never convicted by honest evidence |
| all | nesting | always | `final ⪯ stable ⪯ available` in every honest read, at every cut |
| final | no rollback | always | `Monotone final 0` |
| final | accountable safety | every environment and network (premise `True`) | two conflicting honest reads convict `≥ α·n` from their own two views (local) |
| final | liveness | `Healthy g ∧ prog[ready g, horizon]` | `TxLive c final (heal(final,i,g)) lat` |
| available, stable | sleepy safety | `Sleepy` | `ReadySafe c g 0` |
| available, stable | sleepy liveness | `Sleepy ∧ prog[0, horizon]` | `TxLive c g 0 lat` |
| available, stable | healed safety ("stay in recovery") | `Healthy g ∧ prog[ready g, heal]` | `ReadySafe c g heal` |
| available, stable | healed liveness | `Healthy g ∧ prog[ready g, horizon]` | `TxLive c g heal lat` |
| stable | outage resilience | `Outage T b₀ b₁` | `ProtectedThrough c stable target T b₀ b₁` |

Derived in L0 (`Good.*`, `ConsensusProblem/Facts/Good.lean`), and in the Goldilocks sheet:

| Theorem | Statement |
|---|---|
| `final_agree` | `FaultsBelow α` ⇒ `Agree final 0 ∨ HC`, in any network |
| `final_safe_healthy` | `Healthy g` ⇒ `Safe final 0 ∨ HC` (uses `1 − φ ≤ α`) |
| `persists_final_compatible` | through an outage, the stable read at `T` and an eligible reader's final read are compatible |
| **prefix forms** `sleepySafe_prefix` | `SyncUntil b ∧ SleepyOn θ c 0 b` ⇒ `ReadySafeUpTo c g 0 b ∨ HC`: the past is safe whatever happens after `b` |
| `healedSafe_prefix` | partial synchrony with GST `g` for deadlines up to `b`, `HealthyOn φ g b`, `prog[ready, heal]` and `heal ≤ b` ⇒ `ReadySafeUpTo c g heal b ∨ HC` |
| `outage_prefix` | the outage regime up to `b` ⇒ protection at reading times in `[b₀, b]` ∨ HC |

`TxLive c g start D` covers every submission: a transaction submitted to an
awake honest node by `t` is in the `g`-read of every ready reader at every
`t' ∈ [max t start + Δ + D, horizon]`. Safety has one body,
`AgreeAmong R`/`MonotoneAmong R` for a reader predicate `R` checked at each
cut: `Agree`/`Monotone` (and `Safe`) take honest readers; `ReadySafe` takes ready readers
only: honest, and awake throughout `[max 0 (t − c − 1), t]`. A node that
has been asleep for long may still hold an old fork. `ProtectedThrough`
works as follows. Take a node **ready** at `T` and its `stable` read at `T`.
That read is a prefix of the `target` read (the available output if
provided, else the stable output) at every `t ∈ [b₀, horizon]`, for every
honest `ResilienceReader`. A `ResilienceReader` was caught up before the
window and has been awake since then, or caught up after the window
(`b₁ ≤ t − c − 1`).

An outage run is partially synchronous with GST `b₁` (`OutageNet b₀ b₁`
contains `PSync b₁`), so the after-GST rows apply with `g = b₁` when their
other premises hold.

### The network rule (`ConsensusProblem/Network.lean`)

The delivery rule, verbatim (`CommLog.Delivers.msgs`):

> every message an honest node sends at `t` is received by every honest node
> that is awake at `max(t, GST) + Δ`, by that time.

- "Received by that time" is `Held`. The node sent or received the message
  at some `t' ≤ d`, and did not wake in `(t', d]`. Receipt at the deadline
  itself counts. A restart loses earlier receipts.
- **Rewake clause** (`Delivers.rewake`, a separate named clause for the
  sleepy model): a node awake at a later deadline `dl a` (`a > t`) holds the
  message then, even if it slept in between.
- **Transactions** (`Delivers.txs`): a transaction submitted at `τ ≥ 0` to an
  awake honest node is held (`TxHeld`, in the inbox at some `τ' ∈ [0, d]`)
  by every honest node awake at `dl a`, for every `a ≥ τ`.
- Sends are covered at every time, negative ones included. Submissions are
  covered from `0`. With `SendsFromZero` (true of every valid model run),
  `PSync 0` is synchrony (`PSync.syncUntil_zero`).
- Receipt is a network service, not protocol use. In the model, what arrives
  at the deadline is first used by the node's next tick. That slack belongs
  to the protocol.

Instances: `PSync g` (deadline `max a g + Δ`), `SyncUntil b` (deadline
`a + Δ`, for deadlines up to `b`), and `OutageNet b₀ b₁ = SyncUntil b₀ ∧
PSync b₁`. Every delivery obligation (all three clauses, in every instance)
applies only when its deadline is within both the cut and the horizon: a
`SyncUntil b` with `b` past the horizon still promises nothing after the
horizon. `PSync.mono` (tests): a later GST is weaker.

`EagerFrom g` is the shape of the canonical log: every honest send at `t` is
received at every awake time in `[max t g, horizon]`, and no message is
received before `g` ("silent" refers to message receipts only:
`EagerFrom.txs` still relays transaction inboxes at once). It meets an
instance only under these hypotheses:
- `EagerFrom.delivers`: `Delivers dl cut` for any `dl` with `∀ a, max a g ≤
  dl a`;
- `EagerFrom.psync`: `PSync g'` for `g ≤ g'`;
- `EagerFrom.syncUntil`: `SyncUntil b` for every `b`, given `g ≤ 0` and
  `SendsFromZero`.

It does not imply an arbitrary `SyncUntil b` or `OutageNet b₀ b₁`. Example:
`Δ = 1`, `g = 10`, an honest send at `0` and an honest receiver awake
throughout; an eager-from-10 log may first deliver at `10`, missing the
synchronous deadline `1`.

**Forwarded adversarial messages and equivocation.** Delivery is promised
for honest sends. An honest node that re-releases an adversarial object
(forwarding it, or embedding it in its own release) makes an **honest send**,
so that object is delivered by the rule. Adversarial messages therefore get
delivery guarantees as soon as one honest node forwards them. The network is
never asked to deliver an unbounded number of equivocations that no honest
node sends: what honest nodes forward, and so how many equivocations are
relayed, is the concrete protocol's job. The model does not include a weaker
"knowledge of equivocation" service. Under that service, an honest receipt
of a message with equivocation key `κ` would only guarantee every awake
honest node the same message **or an equivocating pair with key `κ`**, so
one witness per equivocation key would suffice. That service needs a real
equivocation key or relation on messages, not just two distinct messages
that share a key. It is a later option (layers-plan, "Later option").

### The regimes, as formulas (`ConsensusProblem/Regimes.lean`)

Here `p` is the environment point (awake profile, honest set, horizon,
submissions), `L` is the run's log, `n = |V|`, `ready_t = readyAt c t` and
`faulty` is the complement of the honest set.

| Regime | Definition |
|---|---|
| `Sleepy` | `L.PSync p 0 ∧ ∀ t ∈ [0, horizon], θ·(\|ready_t\| + \|faulty\|) < \|ready_t\|` |
| `Healthy g` | `L.PSync p g ∧ ∃ H ⊆ honest, φ·n < \|H\| ∧ ∀ v ∈ H, v awake throughout [max g 0, horizon]` (one fixed set, no churn, so certificates can be formed; awake, not ready) |
| `Outage T b₀ b₁` | `OutageTimes ∧ L.OutageNet p b₀ b₁ ∧ EtaSleepyOn θ (η·Δ) c 0 horizon ∧ cover·n < \|ready_{b₀}\|` |
| `OutageTimes` | `0 ≤ T ∧ T + lag·Δ ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + budget·Δ` |
| η-sleepy at `t` (`η > 0`) | `θ·\|ready_t ∪ awakeIn [max 0 (t − η·Δ), t] ∪ faulty\| < \|ready_t\|` |

With `η = 0`, η-sleepy is plain sleepy (tests: `etaSleepyOn_zero`,
`Regime.outage_eta_zero`). For `η > 0`, every validator awake at some time
in the look-back window counts against the threshold, even one that was
never ready. For `0 ≤ θ`, `0 < η`, `0 ≤ c` and `0 ≤ t`, η-sleepy implies the
awake-count form (tests: `EtaReadyAbove.awakeForm`). The look-back is clamped at `0`: no
participation history before time `0` is assumed. The GST is a parameter of
the regimes, not of the environment. Weaker thresholds keep each regime
(tests: `Regime.*.of_le`).

### Numbers: `Params`, `standard`, `Admissible`

```lean
structure Params (Idx : Type) where
  catchUp : Nat   -- reader catch-up c = catchUp·Δ
  θ φ cover α : ℚ -- sleepy, healthy, outage cover, accountable fraction
  lag budget η : Nat                         -- outage arming lag, budget, look-back (Δ-coefficients)
  heal latency : Capability → Idx → Nat      -- heal point after max g 0; transaction latency
def Params.standard (catchUp lag budget heal latency) := ⟨catchUp, ½, ⅔, ½, ⅓, lag, budget, 0, heal, latency⟩
structure Params.Admissible (P) : Prop :=
  1 ≤ catchUp,  0 ≤ θ ≤ ½,  0 ≤ φ ≤ ⅔,  0 ≤ cover ≤ ½,  1 − φ ≤ α ≤ 1,  1 ≤ budget
```

A contract cannot buy its claims with stronger **thresholds**, because each
of `θ`, `φ`, `cover` and `α` must be at most its standard value. The healthy
regime bounds faults below `1 − φ ≤ α` (`HealthyOn.faultsBelow`).
`standard_admissible` shows that the standard numbers are admissible. The
other numbers are not bounded and carry part of the verdict: a larger
`catchUp` means fewer ready readers, a larger `lag` a later protected source,
a larger `η` a stricter outage participation condition, a small `budget` a
short outage, and larger heal points and latencies weaker claims. Any `η` is
realizable (`outage_witness`); the reviewer reads these as numbers.

### The progress slot

Leader-based progress ("an honest ready proposer in every `k` slots") cannot
be stated over the environment alone, so L0 keeps it abstract:

```lean
structure Progress (S : System V) (Prog : Type) extends External S where
  holds  : Prog → Time → Time → Time → (p : EnvPoint V) → Ext p.env → Prop  -- π c start stop
  mono   : s ≤ s' → e' ≤ e → holds π c s e p x → holds π c s' e' p x
  shrink : b ≤ p.horizon → holds π c s e p x → holds π c s e {p with horizon := b} x
  submit_irrel : holds π c s e p x → holds π c s e {p with submit := σ} x
```

By typing, `holds` reads only the environment point and the run's external
data (`External`: in the model, the PKI and the selection). It cannot read
the protocol's behaviour, and by `submit_irrel` it cannot read the
transaction submissions either: progress is about participation, never about
which transactions arrive. (Otherwise "every submission is `42`" would be a
legal requirement, and a constant ledger `[42]` that censors everything else
would pass: `censoring_progress_rejected`.)

The slot is checked, within limits:

- `Adequate.covers` transports it to the covering run.
- `Realizable` requires it to hold on every witness, and, at some index, on
  the stress witnesses with many honest validators asleep. A reader that
  never holds fails `Good` (`false_progress_not_good`); a requirement of
  near-full participation at every index fails the stress witnesses.
- What remains the instance's choice is how strong the leader requirement
  is: a recurrence gap of one slot ("an honest ready proposer in *every*
  slot") passes, because the witnesses' proposer stays awake. The reviewer
  reads the gap as a number (open: whether to require tolerance of bad
  slots).

In L2 the slot is `ProgressReq` (`ConsensusBlocks/Selection.lean`):

- `.recur ⟨pattern, gap⟩`: `PatternRecurrence`. Every window
  `(t, t + gap·slot]` from `max start 0` whose whole pattern ends by `stop`
  and by the horizon contains a start slot at which every offset's selected
  proposer is honest and ready.
- `.notReadyAtMost m`: `NotReadyOn`, at most `m` validators not ready at
  each time in the window.

`ProgressReq.Fits` requires a recurrence to sit on a skeleton with one
proposer per slot (`.sized 1`). Otherwise an all-proposer selection would
include a faulty key (`allProposers_unfit`, `allProposers_no_witness`).
`Contract.ProgressTolerant O K` asks every provided output of schema `O` to have, for every
`N`, an index whose requirement tolerates `N` validators not ready (a
recurrence always; `.notReadyAtMost m` when `N ≤ m`): this is what the
stress witnesses need (`notReadyAtMost_one_not_tolerant`).

### What an instance supplies

1. A **schema** `OutputSchema`: which outputs serve the `available`,
   `stable` and `final` capabilities (aliasing allowed; see Scope). It must
   satisfy `Serves`: a final output, or an available one.
2. A **contract** `Contract Prog`: a nonempty index type `Idx`, `params :
   Params Idx` and `progress : Capability → Idx → Prog`.
3. For a shape protocol, a **shape family** `F`: a skeleton (grid, proposer,
   poll and committee selections, phases) and a state machine.

It supplies no premise, regime, escape, network condition, hash, decoder,
author, schedule or evidence collector.

### What L0 checks and what L1 proves

`Good S X K` is **the** definition for the systems of the model,
`S = sysOf O (compiled F) V`. For an arbitrary L0 system it is a property of
an abstraction that L0 trusts. L0 alone checks the property table, the
regimes, the network rule, the numbers' range, adequacy (coverage of every
environment and GST, prefix closure) and realizability. `Adequate` and
`Realizable` exclude the vacuous forms: `Valid = ∅`, `Excuse = True`, a
progress requirement that is false, never met or met only near full
participation, a log under which no regime holds, and validity without runs
at a late GST or without silent runs.

L0 cannot check that the system is a real distributed protocol. Example: an
**oracle system** with `Valid = True`, no sends, `Excuse = False`,
`convicts = False`, and every node reading all transactions submitted to an
awake honest node by `t − Δ`, ordered by submission time. It computes its
reads from ground truth that no node has, yet it can meet every L0
condition. Likewise a
system whose `Valid` contains only eager, Byzantine-free runs passes
`Adequate`. What rules these out is what `sysOf` fixes, proved once in L1
for every protocol:

- **`Valid` is every adversarial execution**: Byzantine signers (any
  signature with their own keys), every schedule, relay and hash within the
  execution conditions.
- **Reads are local**: each output is computed by honest code from its own
  view (the engine's state machine), not from the environment.
- **The log is the real communication.** `sysOf`'s `log` is the engine's
  releases, deliveries and inboxes (`sysOf_log_faithful`,
  `sysOf_delivers_iff`). On execution-valid runs, for honest recipients
  and deadlines within the horizon, L0 `Held` agrees with engine `Run.Served`;
  honest wakes in `(0, horizon]` correspond to restarts
  (`Run.held_iff_served`). Faulty nodes have no wake/restart correspondence. **Boundary:** this
  shows that the log cannot invent sends or receipts, and that L0 delivery
  is the engine's delivery. It does not show that handlers retain or use
  delivered data (that is the protocol's behaviour, judged by the claims).
- **The excuse is an observed hash collision only.**
- **Convictions are evidence-only slashing**: `convicts` reads the evidence,
  the PKI and the protocol's `conflicts` rule.
- **The external data are external.** `sysExternal` gives the PKI (`Fin n ≃
  V`) and the selection, fixed before execution. `Admits` is the protocol's
  `SelSpec`. Honest code never sees the selection, the PKI, the honest set,
  the GST, the awake profile or the hash. L0 only knows the type of the
  external data, so this has to be proved at L1.

L1 also proves `Adequate` once (`sysOf_adequate`, from `canonical_run_from`
for every GST, including silent runs, and from `Run.truncate` for prefixes),
and non-framing (`sysOf_nonFraming`, from slashing protection in the engine).

## Layers

| Layer | Library | What it fixes |
|---|---|---|
| **L0, the problem** | `ConsensusProblem` | transactions, ledgers, capabilities and `OutputSchema`; environment points; traces and `CommLog` (opaque messages); the network rule; the properties; `Params` and the fixed regimes; `Good = Behaviour ∧ Adequate ∧ Realizable` |
| **L1, the model** | `ConsensusModel`, `ConsensusModelProofs` | a shape-free execution model: PKI, closed selection, credentials, the engine (unit ticks, delivery, sleep and restarts, slashing protection), evidence and hashes; `sysOf` (every protocol family as an L0 system, with its real log) and `sysExternal`; the proofs (`sysOf_log_faithful`, `held_iff_served`, `canonical_run_from`, `Run.truncate_*`, `sysOf_adequate`, `honestNeverSlashed`, `sysOf_nonFraming`; injective-hash lifting is checked in `ConsensusShapeTests/Lift`) |
| Blocks | `ConsensusBlocks` | protocol-free building blocks with at least two users: `TimeGrid`, `Selection` (`Pattern`, `Recurrence`, `ProgressReq`, `HonestReadyIn`, `PatternRecurrence`, `NotReadyOn`), `Chains`, `Payload` (`encodeTxs`, `ledgerOf`) |
| **L2, the shape** | `ConsensusShape` | one generic `ChainShape`, `compile` onto L1, `shapeProgress`, chain-level `ShapeClaims`, `refinement` to `Behaviour`, `coverage`, generic `regimes_realizable`, the endpoint `Accepted` with `Accepted.good` |
| Values | `ConsensusShape/Values` | Goldilocks (pinned numbers and the properties sheet); Streamlet and Tendermint are test values (`ConsensusShapeTests/Values`) |

L2's acceptance endpoint (`ConsensusShape/Accepted.lean`):

```lean
structure Accepted (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  claims : ShapeClaims F K          -- proved by the protocol
  admissible : K.params.Admissible
  serves : O.Serves
  progressFits : K.ProgressFits F
  progressTolerant : Contract.ProgressTolerant O K
theorem Accepted.good (h : Accepted F K) (V) [Fintype V] [DecidableEq V] :
    Good (sysOf O (compiled F) V) (shapeProgress F V) K
theorem Accepted.activeService (h : Accepted F K) :
    ∃ cap g, (cap = .final ∨ cap = .available) ∧ O.output cap = some g ∧ ActiveService F K cap g
```

`Accepted.good` combines three theorems. `refinement` gives `Behaviour`;
its bridges are `ledgerTrace` (reads are `ledgerOf` of the output chains)
and `proposalLive_txLive` (proposal liveness and partial synchrony give
transaction liveness). `sysOf_adequate` gives `Adequate`.
`regimes_realizable` gives `Realizable` (its stress witnesses keep keys
`1..3`, respectively `1..⌊2n/3⌋+1`, awake and the rest asleep). `ActiveService`: a final or
available output puts a relayed transaction into another honest node's
read on a clean healthy witness. A silent service or empty outputs are
therefore not accepted, for every protocol.

Design and history: `repos/goldilocks/notes/generic-interface/layers-plan.md`
in the workbench (latest: "Iteration 6: the definition of a good protocol");
the iteration-6 plan and reviews are in the run folder `iter6/`.

## Reading order

Entry points and key theorems only; the source files list the rest.

1. **L0** (`ConsensusProblem/`), definitions only: `Basic` (`Env`, `EnvPoint`,
   `Trace`, `CommLog`, `System`), `Network` (`Delivers`, `PSync`, `SyncUntil`,
   `OutageNet`, `EagerFrom`), `Properties` (the claims, with the prefix
   forms), `Regimes` (`Params`, `Regime.*`), `Good` (`Behaviour`,
   `System.Adequate`, `Realizable`, `Good`). Lemmas (not needed to read `Good`)
   are in `ConsensusProblem/Facts/`: the derived `Good.*` (with `Good.served`),
   delivery, prefix, regime and transfer lemmas.
2. **L1** (`ConsensusModel/`: `Objects`, `Protocol`, `Run`, `Conditions`,
   `System` with evidence, `sysOf` and `sysExternal`), then the proofs in
   `ConsensusModelProofs/`: `sysOf_log_faithful`, `Run.held_iff_served`,
   `canonical_run_from`, `Run.truncate_valid`, `sysOf_adequate`,
   `Run.honestNeverSlashed`, `sysOf_nonFraming`, `sysOf_laws`.
3. **Blocks** (`ConsensusBlocks/`): `TimeGrid`, `Selection`, `Chains`,
   `Payload`.
4. **L2** (`ConsensusShape/`): `Shape`, `Compile`, `Run`
   (`shapeProgress`), `Claims`, `Refinement` (`refinement`), `Realizable`
   (`ProgressReq.Fits`, `regimes_realizable`), `Accepted`
   (`Accepted.good`).
5. **Values** (`ConsensusShape/Values/`): `Goldilocks`, `GoldilocksSheet`.
   Streamlet and Tendermint: `ConsensusShapeTests/Values`.

## Why the meaning is fixed below the protocol

- **Fixed regimes, numbers only.** No premise language: the instance picks
  numbers in the admissible range and a progress requirement in the closed
  `ProgressReq`.
- **Closed selection and identity.** Keys are `Fin n`. The run's PKI is a
  bijection `Fin n ≃ V`. The selection is run data, admissible for the
  protocol's closed `SelSpec`.
- **Credentials.** Every signed object inside a delivered object is signed by
  a key selected for its role, faulty signers included
  (`Run.selected_of_observed`). Signatures bind their role.
- **Slashing protection in the engine.** The engine refuses an own-signed
  candidate that conflicts with an own-signed object it has seen; `seen`
  survives restarts. Hence `honestNeverSlashed` and non-framing hold for
  every protocol. A protocol whose `conflicts` is always true silences
  itself (`conflictsTrue_silent`).
- **Engine-written payload.** Every proposal's `input := encodeTxs mempool`.
  Reads are `ledgerOf` of the output chains.
- **Closed `ProposalRole` and poll mode.** Provenance accepts a header only
  if it was signed as the proposer of its position or in the poll role.
  `pollSel := .fixed ∅` disables polling.
- **No hooks.** There is no protocol-supplied author, decoder, schedule,
  hash, premise or evidence collector. The only rule is `conflicts`, and the
  only excuse is an observed hash collision.

## Adversary model

The adversary is static and all-knowing. The honest set is fixed per run.
Faulty validators sign anything with their own keys (only `Unforgeable` and
`Credentials` bind them). The scheduler chooses the events, relay and hash,
within the execution conditions. There is no adaptive corruption.

## Model-adequacy bindings (generic, read once)

- **PKI:** one key per validator, known to all.
- **Credentials:** the deployed membership mechanism is sound for the
  selection.
- **Signatures:** unforgeable, binding key and role.
- **Slashing protection:** the deployed client implements `protects` and
  persists its seen log across restarts (as an EIP-3076 database does).
- **Delivery:** the network rule above, for honest releases, including
  honest re-releases of adversarial objects, and for transactions (inboxes
  survive restarts).
- **Δ known; unit ticks:** honest code knows `Δ` and `n`. Every awake honest
  node ticks at every integer time.
- **Order within one time:** restarts, then ticks, then deliveries. What
  arrives at a deadline is used by the next tick. Restarts happen exactly at
  wakes.
- **Collision resistance** of the deployed hash on real items.

Per instance, the reviewer binds three things: the outputs are what users
read, `conflicts` is the slashing rule the chain enforces, and the numbers
are the intended ones.

## Scope

- **`stable := finalized` (Gasper-style) is not good** (iteration-6 decision).
  Stable must be sleepy-live (`DAClaims.sleepyLive`). A schema that aliases
  stable to final is good only if its final output is live under sleepy
  participation (`stable_alias_final_sleepy_live`). Aliasing stable to
  available is allowed (Goldilocks).
- **Non-accountable BFT is out of scope**. Final accountability is
  mandatory, for fraction `α ≥ 1 − φ` (standard ⅓), in every environment.
- **One GST and one outage per run: partially closed.** The prefix forms
  (`Good.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`) make the
  past safe before any later asynchrony. A run after an outage is a run with
  GST `b₁`. Runs with several GSTs or outages, judged as a whole, are out of
  scope.
- **Healthy means no churn.** A fixed set of more than `φ·n` honest
  validators is awake throughout from `max g 0`. A rotating ⅔ is not healthy
  (`healthy_rotating_sleeper`).
- Static adversary, equal weights, one `Δ`, no probabilistic protocols, no
  proof of work, no non-validator readers, no responsiveness claim.
- No transaction validity, fees, capacity or chain-quality bounds. Liveness
  is bounded-latency.
- No public schedules: one proposer `SelSpec` for every slot, chosen
  adversarially. Round-robin and RANDAO duties are worst-case `.sized 1`,
  with a recurrence requirement.
- No committee premise: only `.fixed` committees can support claims.
  Gasper's partitioned selection is deferred.
- Phases are multiples of `Δ`. For `pollSel := .fixed univ`, poll provenance
  accepts any validator's header.
- Tendermint's `notReadyAtMost m` is a pointwise bound. It does not by
  itself put a ready honest leader within `m + 1` rounds (an adversarial
  schedule can sleep exactly the current leader). The contract is a
  placeholder.
- The collision escape is run-wide. Accountability compares two reads in one
  run.
- The network-level "knowledge of equivocation" service is not modelled (see
  the network section).
- Recurrence progress is read as a number: a gap of one slot (an honest ready
  proposer in every slot) is accepted; whether the definition should require
  tolerance of bad proposer slots is open.

## Goldilocks

`Values/Goldilocks.lean` pins the numbers. `Values/GoldilocksSheet.lean`
states the intended properties. Neither contains protocol proofs. The
committee kinds and phases are placeholders until the FG-SA migration.

**Numbers** (round-model FG-SA, `Δ_F = Δ`, `κ = 2`, slow arming;
`FGSAParams = ⟨R, lockK, eta⟩` with `R ≥ 2`, `lockK ≥ 2`, `eta ≥ 1`):

| Number | Value |
|---|---|
| thresholds | standard: `θ = ½`, `φ = ⅔`, `cover = ½`, `α = ⅓` |
| catch-up | `18` (two slots + the `6Δ` join + one gate) |
| arming lag | `4·lockK − 4` (`L − 3Δ`) |
| outage budget | `min eta (4·lockK − 5)` (implies FG-SA's (V), `budget_implies_V`) |
| look-back `η` | `eta` (η-sleepy outage regime) |
| heal (available, stable), gap `k` | `29 + B_H^F(k)` from `max g 0` (`29 = 18 + 1 + 10`) |
| heal (final), index `gf` | `29 + B_H^F(gf·R) + W_W(gf)` |
| latency | `4k + 6`; final `4·gf·R + 6 + W_W(gf)` |
| progress | `.recur ⟨single, k⟩`; final `.recur ⟨range(3R+κ), gf·R⟩` |

The schema has two outputs: `confirmed` serves both available **and**
stable (in the round model stable = confirmed), and `finalized` serves
final. `reference_bounds` checks the formulas against the FG-SA paper's
reference numbers. `goldilocks_admissible` and `goldilocks_progressFits`
hold.

**Target.** `GoldilocksTarget F pp := GoldilocksBindings F ∧ Accepted F
(goldilocksContract pp) ∧ GoldilocksExtra F pp`. This is a reviewed target,
not a proof that FG-SA meets it. A failed feasibility gate leaves it
unproved, and it is never changed to fit FG-SA.

**The sheet** (by intended-property id):

- **§1, from `Accepted`, proved:**
  - `nested`, `finalized_monotone`, `nonFraming`, `finalized_accountable`
    (for this family's `conflicts`), `finalized_safe_below_third`;
  - `confirmed_safe_sleepy` and its `_prefix` form,
    `confirmed_safe_healed` and its `_prefix` form;
  - `confirmed_persists` (M14 closed), `outage_final_compatible`;
  - `confirmed_txLive_sleepy`, `confirmed_txLive_healed`,
    `finalized_txLive`;
  - `goldilocks_good` (realizable at every `Δ`, GST and late outage).
- **§2, the `GoldilocksExtra` fields, stated:**
  - inclusion of every honest proposal (`includeSleepy`, `includeHealed`);
  - block-level growth (`growSleepy`, `growHealed`);
  - first and recurring finality in the intended forms (`finalFirst`,
    `finalRecur`: above the ready confirmed reads at the healing cut
    `finalCut`, within `W_W`);
  - `liveDC`, `crossNest`;
  - A2 `outageWindow` (η-sleepy prefix only);
  - weak continuation (`weakSafe`, `weakCrossNest`, `weakInclude`,
    `weakGrow`; inhabited: `weakPremise_inhabited`).
- **§3, not yet stated, with reasons:** A6 (a two-run statement), fast
  arming, cut/seed uniformity, FL3/FL4, paper-only rows, HEAD, the fast path,
  leak accounting and the E1/E2 evidence binding. For the newer spec,
  `available` must bind to the confirmed record `latestConfirmed`: its
  read-time tip `ac_confirmed` can step back, which `ReadySafe` forbids.
  P-TX-SCOPE: the target goes beyond proposal inclusion, to transaction
  liveness, through the generic payload bridge.
- **Weaker than intended (accepted):** A3 (η-sleepy during the window, the η
  cap on the budget, eligible readers only), P-OUT-FIN-COMPAT before `b₀`,
  ready rather than joined readers and proposers.

**Migration obligations.** Each is a gate that the FG-SA migration must pass
against the unchanged target:

1. The healthy regime (⅔ continuously awake, no churn) vs FG-SA Recovery₂
   (all honest awake).
2. The GST shift to `max g 0` plus catch-up.
3. `Ready` at `18·Δ` ⇒ joined; ready at `b₀` ⇒ covered.
4. The outage under η-sleepy (`η = eta`), cover ½ and `PSync b₁` vs FG-SA
   `OutageE` (startup clamping, the ready ∪ awake denominator).
5. Readers caught up after the window.
6. Ready-vs-awake counting.
7. The E1/E2 evidence binding.
8. Hash, relay across sleep, and endpoint receipt (one time unit).
9. Finality liveness under ⅔-continuous participation.
10. Weak-continuation uniformity.
11. FL1/FL2 in the intended forms from FG-SA's `FirstFinalityRecFEClaim_W` /
    `FinalityLivenessGSTClaim_W` under `finRec gf`; `W_W` is shorter than one
    guarded recurrence window (`finalRecur_delay_vs_window`).
12. `CleanPrefixTruncation` vs `Adequate.prefixClosed`.

**Regime risk.** Francesco decided (2026-10-28): the outage regime is
η-sleepy with an instance look-back (`η = 0` is plain sleepy), and the
healthy regime is ⅔ continuously awake. The remaining risk is in
obligations (1), (4) and (9). FG-SA's recovery and finality proofs assume
every honest validator awake, and its outage bound is not yet bridged to
the clamped η-sleepy form. If a gate fails, Goldilocks is not good under
this definition. The target stays unproved and the question goes back to
Francesco. Neither the sheet nor the definition is weakened.

## Gap dispositions (M1–M39; `ConsensusShapeTests/Gaps.lean`)

| Gap | Disposition |
|---|---|
| M1 weak continuation | healed regime stays healthy ("stay in recovery"); sheet `weakSafe`/`weakInclude`/`weakGrow`; uniformity: obligation (10) |
| M2, M18 corruption | scope: static adversary |
| M3 FE/F4 pattern | `Pattern.range`, `finRec_span`, `range_head`; equivalence: gate F-2 |
| M4 psync mandated | by construction (`DAClaims.healed*`, `FinalClaims.live`); `healed_witness_late` |
| M5 final safety under asynchrony | `FinalClaims.accountable` has premise `True`; `Good.final_agree` |
| M6 syncUntil unchecked | removed (no premise language) |
| M7, M27 late GST, Δ | `Realizable` ∀ Δ, g ≥ 0; `healed_witness_late` (Δ = 7, GST 1000) |
| M8 trivial outage | `OutageActive`; `outage_async_log`, `outage_witness_late`, `outage_control` |
| M9 dynamic participation | sleepy regime; `sleepy_with_sleeper`; stress witnesses (`Realizable.sleepyStress`, `notReadyAtMost_one_not_realizable`) |
| M10 thresholds | `Params.Admissible`; `admissibility_rejections`, `outage_times_teeth`, `healthy_needs_two_thirds` |
| M11 wake at GST | healthy counts awake; progress from `readyFrom`; `healthy_wake_at_gst` |
| M12 inclusion | sheet `includeSleepy`, `includeHealed` |
| M13 window-only P1 | sheet `outageWindow`; `outageWindow_prefix_only` |
| M14 outage stable/finalized | closed: stable = confirmed (`stable_is_confirmed`, `confirmed_persists`); `persists_final_compatible` |
| M15, M16 pinned params, instance | `goldilocksContract`, `reference_bounds`; target unproved (migration) |
| M17 eventual liveness | scope: outside the bounded-latency interface (every claim has a latency bound `lat`; eventual-only liveness cannot be expressed) |
| M19, M26 weights, single Δ | scope |
| M20 cross-node nesting | sheet `crossNest`, `liveDC` |
| M21 recovery fault bound | `HealthyOn.faultsBelow`, `1 − φ ≤ α`; `faulty_third_not_healthy` |
| M22, M23 instance vs FG-SA, cover/budget | obligations (1)–(12); `budget_implies_V`; obligation (4) |
| M24 reader scope | ready readers for available/stable, every honest reader for final |
| M25 ready vs awake | healthy = fixed awake set; readers/progress ready; `healthy_rotating_sleeper`; obligation (6) |
| M28 recovery starts | `healPoint = max g 0 + heal·Δ`, progress from `readyFrom` |
| M29 faulty proposer witnesses | `ProgressFits`; `allProposers_unfit`, `allProposers_no_witness`, `recurrence_has_teeth` |
| M30 safety vs liveness regime | same `Healthy`; for `heal ≤ horizon`, safety window `[ready, heal]` ⊆ liveness window `[ready, horizon]` |
| M31–M33 validity, capacity, chain quality | scope |
| M34 conditional accountability | final-output accountability is unconditional; accountability for conflicting available reads is out of scope |
| M35 one GST / one outage | partially closed: prefix forms (`prefix_sync_then_async`); after an outage = GST `b₁`; rest scope |
| M36, M39 leak/HP latency, HEAD | scope; sheet §3 |
| M37 model adequacy | `Adequate` + `sysOf_adequate`, `sysOf_log_faithful`, `held_iff_served`; `silent_run_valid` |
| M38 global escape | removed: local accountability only; `local_accountability_teeth` |
| vacuous system | `Good = Behaviour ∧ Adequate ∧ Realizable`; `false_progress_not_good`, `empty_valid_not_good`, `excuse_true_not_good`, `no_admissible_not_good`; progress cannot read submissions (`censoring_progress_rejected`) or demand near-full participation (`notReadyAtMost_one_not_realizable`) |

## Tests (`ConsensusShapeTests/`)

- `Problem`: every L0 property has teeth; global slashability does not give
  local accountability (`local_accountability_teeth`).
- `Network`: the endpoint rule (`endpoint_waker`, `receipt_at_deadline`,
  `held_restart`, `negative_send_covered`), faithfulness
  (`faithful_relayedRun`, `faithful_receipt`), silent runs
  (`silent_run_valid`) and truncation (`truncate_relayedRun`).
- `Regimes`: what each regime admits and rejects (`psync_lost_message`,
  `outage_async_log`, `sleepy_with_sleeper`, `healthy_wake_at_gst`,
  `healthy_needs_two_thirds`, `faulty_third_not_healthy`,
  `outage_times_teeth`); the explanatory L0 lemmas (threshold monotonicity,
  `η = 0`, the awake-count form).
- `Good`: vacuous systems are not good; `censoring_progress_rejected`;
  `prefix_sync_then_async`;
  `healthy_rotating_sleeper`; η-sleepy history, brief wakes and startup;
  `stable_alias_final_sleepy_live`.
- `Model`, `Blocks`, `Shape`: model mechanics, recurrence, compiled roles and
  poll mode.
- `Leaks`: do-nothing, propose-but-genesis, fabricating and self-silencing
  protocols fail `ShapeClaims`; `recorder_live_testK` is the positive
  control.
- `Realizable`: `coverage_keeps_selection`, `allProposers_no_witness`, the
  rotating sleeper, `tendermint_largeIdx_prog`, `healed_witness_late`,
  `outage_witness_late` (with controls).
- `Controls`: `positive_controls`, `outage_control`, `ctrl_realizable` at
  explicit numbers.
- `Vacuity`: admissibility rejections, progress fit,
  `notReadyAtMost_one_not_realizable`, `notReadyAtMost_one_not_tolerant`,
  `credential_forgery_excluded`, `noService_not_accepted`.
- `Goldilocks`: `pp223_numbers`, `stable_is_confirmed`,
  `outageWindow_prefix_only`, `weakPremise_inhabited`.
- `Values`, `Lift`, `Support`, `Common`: the Streamlet and Tendermint values,
  injective-hash lifting, test-only lemmas and fixtures.
- `Reformulations`: each reformulated definition against its old form.
- `Gaps`: one disposition per gap row, with `example`s for the
  by-construction rows.

## Verification

```sh
cd /srv/work/fradamt/goldilocks/generic-interface
LAKE_RESTORE_ARTIFACTS=true lake build ConsensusProblem ConsensusModel ConsensusModelProofs ConsensusBlocks ConsensusShape ConsensusShapeTests
lake env lean --run contract/CheckConsensusAxioms.lean
```

The audit imports every `Consensus*` module under `contract/` (tests
included) and checks that the required theorems exist. It then checks every
compiled declaration for axioms outside `propext`, `Classical.choice` and
`Quot.sound`, and prints `standard axioms only: true`.
