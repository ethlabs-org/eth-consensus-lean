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

  A **stress witness** exercises liveness with many honest validators
  asleep, so a progress requirement cannot quietly demand near-full
  participation. For every provided available or stable output, at *some*
  index:
  - `sleepyStress`: for every validator count, a sleepy witness where at most
    two honest validators are awake at any one time (`AwakeAtMost 2`; the
    witness also has a faulty validator, and with `θ ≤ ½` two ready honest
    validators meet the sleepy threshold), with `prog[0, horizon]` and
    `TxLiveActive`.

  The healthy regime is full participation, so it has no stress witness.

  A contract whose available progress is "at most one validator not ready"
  at every index is therefore not realizable
  (`notReadyAtMost_one_not_realizable`), nor is any bound below `n − 2` at
  every index (`notReadyAtMost_below_not_realizable`): a protocol that
  needs a fixed fraction of the validators awake is not dynamically
  available.

For shape protocols, `Accepted.good` (L2) proves all three parts. The good
protocols we accept are
`Good (sysOf O (compiled F) V) (shapeProgress F V) K`, for every finite `V`.

### The property table (`Behaviour`)

Notation (the `System` accessors of `Regimes.lean`): `c = cDur = catchUp·Δ`;
`heal(cap,i,g) = max g 0 + heal cap i·Δ`; `ready(g) = max g 0 + c + 1`;
`lat = latency cap i·Δ`;
`prog[a,b]` = the progress requirement of `cap` at index `i` on `[a, b]`;
`HC` = the excuse.

| Output | Property | Regime | Claim (`∨ HC` unless "always") |
|---|---|---|---|
| all | non-framing | always | honest validators are never convicted by honest evidence |
| all | nesting | always | `final ⪯ stable ⪯ available` in every honest read, at every cut |
| final | no rollback | always | `Monotone final 0` |
| final | accountable safety | every environment and network (premise `True`) | two conflicting honest reads convict `≥ α·n` from their own two views (local) |
| all | healthy liveness (`healthyLive`) | `Healthy g ∧ prog[ready g, horizon]` (progress of that capability) | `TxLive c g heal(cap,i,g) lat` |
| available, stable | sleepy safety | `Sleepy` | `ReadySafe c g 0` |
| available, stable | sleepy liveness | `Sleepy ∧ prog[0, horizon]` | `TxLive c g 0 lat` |
| available, stable | healed safety ("stay in recovery") | `Healthy g ∧ prog[ready g, heal]` | `ReadySafe c g heal` |
| stable | outage resilience | `Outage T b₀ b₁` | `ProtectedThrough c stable target T b₀ b₁` |

One field per row (`finalAccountable`, `healthyLive`, `sleepySafe`, `sleepyLive`,
`healedSafe`, `persists`). Derived in L0 (`Good.*`,
`ConsensusProblem/Facts/Good.lean`; `Agree`, `Safe`, `FaultsBelow`,
`ReadySafeUpTo` are in `ConsensusProblem/Derived.lean`), and in the Goldilocks sheet:

| Theorem | Statement |
|---|---|
| `final_agree` | `FaultsBelow α` ⇒ `Agree final 0 ∨ HC`, in any network |
| `final_safe_healthy` | `Healthy g` ⇒ `Safe final 0 ∨ HC` (uses `β ≤ α`) |
| `persists_final_compatible` | through an outage, the stable read at `T` and an eligible reader's final read are compatible |
| **prefix forms** `sleepySafe_prefix` | `SyncUntil b ∧ SleepyOn θ c 0 b` ⇒ `ReadySafeUpTo c g 0 b ∨ HC`: the past is safe whatever happens after `b` |
| `healedSafe_prefix` | partial synchrony with GST `g` for deadlines up to `b`, `HealthyOn β g b`, `prog[ready, heal]` and `heal ≤ b` ⇒ `ReadySafeUpTo c g heal b ∨ HC` |
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

The delivery rule is Francesco's rule, normal delivery (`CommLog.Delivers.msgs`):

> every message an honest node sends at `t` is received, within the delivery
> bound, by every honest node that is awake over the delivery interval, and is
> re-served, within the bound, to nodes that wake later.

Formally, for a deadline function `dl` (`max a GST + Δ` in partial synchrony):
for every start `a ≥ t`, every honest node awake throughout `[a, dl a]` holds
the message at `dl a`. At `a = t`: a node awake over `[t, max(t, GST) + Δ]`
has it by `max(t, GST) + Δ`. At a later `a`: a node that wakes at `a` and
stays awake has it by `max(a, GST) + Δ`, not at the wake itself (no instant
re-delivery; tests `waker_within_bound`, `waker_not_instant`).

- "Has it at `d`" is `Held`. The node sent or received the message
  at some `t' ≤ d`, and did not wake in `(t', d]`. Receipt at the deadline
  itself counts. A restart loses earlier receipts.
- **Transactions** (`Delivers.txs`), the same rule: a transaction submitted at
  `τ ≥ 0` to an awake honest node is held (`TxHeld`, in the inbox at some
  `τ' ∈ [0, d]`) at `dl a` by every honest node awake throughout `[a, dl a]`,
  for every `a ≥ τ`.
- Sends are covered at every time, negative ones included. Submissions are
  covered from `0`. With `SendsFromZero` (in `Derived`; true of every valid model run),
  `PSync 0` is synchrony (`PSync.syncUntil_zero`).
- Receipt is a network service, not protocol use. In the model, what arrives
  at the deadline is first used by the node's next tick. That slack belongs
  to the protocol.

Instances: `PSync g` (deadline `max a g + Δ`), `SyncUntil b` (deadline
`a + Δ`, for deadlines up to `b`), and `OutageNet b₀ b₁ = SyncUntil b₀ ∧
PSync b₁`. Every delivery obligation (both clauses, in every instance)
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
| `System.Sleepy` | `L.PSync p 0 ∧ ∀ t ∈ [0, horizon], θ·(\|ready_t\| + \|faulty\|) < \|ready_t\|` |
| `System.Healthy g` | `L.PSync p g ∧ \|faulty\| < β·n ∧ ∀ v ∈ honest, v awake throughout [max g 0, horizon]` (full participation; awake, not ready) |
| `System.Outage T b₀ b₁` | `OutageTimes ∧ L.OutageNet p b₀ b₁ ∧ EtaSleepyOn θ (η·Δ) c 0 horizon ∧ cover·n < \|ready_{b₀}\|` |
| `OutageTimes` | `0 ≤ T ∧ T + lag·Δ ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + budget·Δ` |
| η-sleepy at `t` (`η > 0`) | `θ·\|ready_t ∪ awakeIn [max 0 (t − η·Δ), t] ∪ faulty\| < \|ready_t\|` |

With `η = 0`, η-sleepy is plain sleepy (tests: `etaSleepyOn_zero`,
`System.outage_eta_zero`). For `η > 0`, every validator awake at some time
in the look-back window counts against the threshold, even one that was
never ready. For `0 ≤ θ`, `0 < η`, `0 ≤ c` and `0 ≤ t`, η-sleepy implies the
awake-count form (tests: `EtaReadyAbove.awakeForm`). The look-back is clamped at `0`: no
participation history before time `0` is assumed. The GST is a parameter of
the regimes, not of the environment. Weaker thresholds keep each regime
(tests: `System.*.of_le`).

### Numbers: `Params`, `standard`, `Admissible`

```lean
structure Params (Idx : Type) where
  catchUp : Nat   -- reader catch-up c = catchUp·Δ
  θ β cover α : ℚ -- sleepy, healthy fault bound, outage cover, accountable fraction
  lag budget η : Nat                         -- outage arming lag, budget, look-back (Δ-coefficients)
  heal latency : Capability → Idx → Nat      -- heal point after max g 0; transaction latency
def Params.standard (catchUp lag budget heal latency) := ⟨catchUp, ½, ⅓, ½, ⅓, lag, budget, 0, heal, latency⟩
structure Params.Admissible (P) : Prop :=
  1 ≤ catchUp,  0 ≤ θ ≤ ½,  ⅓ ≤ β,  0 ≤ cover ≤ ½,  β ≤ α ≤ 1,  1 ≤ budget
```

A contract cannot buy its claims with easier **thresholds**: `θ` and `cover`
must be at most their standard values (a smaller value is a weaker regime
premise, hence a stronger claim), and the healthy fault bound `β` at least
its standard `⅓` (the premise is `|faulty| < β·n`: a larger `β` admits more
faults). Accountability requires `β ≤ α ≤ 1` (a larger `α` convicts more,
hence is stronger; at the standard `β = ⅓`, `α ≥ ⅓`), so the healthy regime
bounds faults below `β ≤ α` (`HealthyOn.faultsBelow`) and final safety holds
there (`final_safe_healthy`).
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
  the stress witness with many honest validators asleep. A reader that
  never holds fails `Good` (`false_progress_not_good`); a requirement of
  near-full participation at every index fails the stress witness.
- In L2, acceptance also asks every provided output to have an index whose
  requirement tolerates a bad (faulty or not ready) proposer slot in every
  window (`ProgressTolerant`, below). "An honest ready proposer in *every*
  slot" (`recur ⟨single, 1⟩`) is rejected (`recur_single_one_not_tolerant`).
  Beyond that, the reviewer reads the gap as a number.

In L2 the slot is `ProgressReq` (`ConsensusBlocks/Progress.lean`):

- `.recur ⟨pattern, gap⟩`: `PatternRecurrence`. Every window
  `(t, t + gap·slot]` from `max start 0` whose whole pattern ends by `stop`
  and by the horizon contains a start slot at which every offset's selected
  proposer is honest and ready.
- `.notReadyAtMost m`: `NotReadyOn`, at most `m` validators not ready at
  each time in the window.

`ProgressReq.Fits` requires a recurrence to sit on a skeleton with one
proposer per slot (`.sized 1`). Otherwise an all-proposer selection would
include a faulty key (`allProposers_unfit`, `allProposers_no_witness`).
`ProgressTolerant O K` asks every provided output of schema `O` to have, for every
`N`, an index whose requirement (`ProgressReq.Tolerates N`) tolerates `N`
validators not ready and a bad proposer slot in every window:

- `.recur ρ`: the slack `span + 2 ≤ gap` (`Recurrence.BadSlotSlack`). With
  a bad slot every `span + 2` slots, every window holds a bad slot and a
  start slot whose whole pattern is good (`patternRecurrence_of_periodic`).
  The witnesses' good proposer stays awake, so `N` does not matter.
- `.notReadyAtMost m`: `N ≤ m`. Tendermint's requirement is not slot-based:
  it bounds the validators not ready, not who leads. Its tolerant indices
  (`m ≥ n`) hold on every point, so they hold when every round-robin leader
  is faulty or asleep; the bad-slot requirement asks nothing more of it
  (`BadProposerEvery` is `True` there). Whether a round-robin protocol is
  live under such a requirement is the protocol's proof (Scope).

The sleepy stress witness needs the first half
(`notReadyAtMost_one_not_tolerant`). The second half is witnessed
semantically: `regimes_realizable` also gives
`RealizableActive.badProposer`, for every provided output, at a tolerant
index, a healthy witness from every GST under a selection where faulty key
`0` proposes one slot in every `span + 2`; every window of the requirement
holds a faulty proposer slot (`BadProposerEvery`), and progress and an active
liveness claim still hold. Gaps without slack at every index are rejected
(`recur_noSlack_not_tolerant`; `recur_single_one_bad_slots` shows why:
`recur ⟨single, 1⟩` fails once every slot has a faulty proposer).

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

## Trusted surface: what to read

To know that `Accepted F K` (or `Good`) means a good protocol, read these
definitions and statements. Everything else is proof support, checked by Lean.

1. **L0, the problem** (`ConsensusProblem/`, library `ConsensusProblem`):
   `Basic` (`Env`, `EnvPoint`, `Trace`, `CommLog`, `System`), `Network`
   (`Delivers`, `PSync`, `SyncUntil`, `OutageNet`, `EagerFrom`), `Properties`
   (the claims), `Regimes` (`Params`, `Contract`, the regimes
   `System.Sleepy/Healthy/Outage` and `System.cDur/heal/ready/lat`),
   `Good` (`Behaviour`, `System.Adequate`, `Realizable`, `Good`). Read all of
   it. Not in the trusted surface: `ConsensusProblem/Derived` (definitions
   `Good` does not read: `Agree`, `Safe`, `ReadySafeUpTo`, `FaultsBelow`,
   `SendsFromZero`, `Trace.map`) and `ConsensusProblem/Facts/` (lemmas only:
   the derived `Good.*`, with `Good.served`).
2. **L1, the model** (`ConsensusModel/`): `Objects`, `Protocol`, `Run`,
   `Conditions`, `System` (evidence, `sysOf`, `sysExternal`): the definitions
   `sysOf` exposes (a node's view `Run.ViewIdx` is the closure of its engine
   `seen` log; `Run.mem_viewIdx_iff` gives the event-index form). Key statements (`ConsensusModelProofs/`):
   `sysOf_adequate`, `sysOf_log_faithful`, `Run.held_iff_served`,
   `sysOf_nonFraming`, `sysOf_laws`.
3. **Blocks** (`ConsensusBlocks/`): `TimeGrid`, `Progress` (`Pattern`,
   `Recurrence`, `ProgressReq`, `PatternRecurrence`, `NotReadyOn`), `Chains`,
   `Payload` (`encodeTxs`, `ledgerOf` = `List.eraseDups` of the decoded
   inputs): definitions only; their lemmas are in `ConsensusBlocks/Facts`.
4. **L2, the shape** (`ConsensusShape/`): `Shape` (`ChainShape`), `Compile`,
   `Run` (`Sys`, `shapeProgress`), `Claims` (`ShapeClaims`),
   `ProgressFit` (`ProgressFits`, `ProgressTolerant`), the witness-activity
   definitions at the top of `Realizable` (`RealizableActive`), `Accepted`.
   Key statements: `refinement`, `regimes_realizable`, `Accepted.good`.

Proof support (not needed to trust the endpoint): `ConsensusProblem/Derived`
and `Facts`, `ConsensusBlocks/Facts`, `ConsensusShape/Payload` (payload
lemmas), `ConsensusShape/Service` (the checked corollary
`Accepted.activeService`, from `Accepted.good` via `Good.served`),
the rest of `ConsensusModelProofs` (canonical runs `canonical_run_from`,
truncation `Run.truncate_*`, slashing protection `honestNeverSlashed`),
`Refinement` and the rest of `Realizable` (coverage, witnesses). Values:
`ConsensusShape/Values/` (Goldilocks); Streamlet and Tendermint are test values
(`ConsensusShapeTests/Values`). Injective-hash lifting is checked in
`ConsensusShapeTests/Lift`.

L2's acceptance endpoint (`ConsensusShape/Accepted.lean`):

```lean
structure Accepted (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  claims : ShapeClaims F K          -- proved by the protocol
  admissible : K.params.Admissible
  serves : O.Serves
  progressFits : ProgressFits K F
  progressTolerant : ProgressTolerant O K
theorem Accepted.good (h : Accepted F K) (V) [Fintype V] [DecidableEq V] :
    Good (sysOf O (compiled F) V) (shapeProgress F V) K
```

`Accepted.good` combines three theorems. `refinement` gives `Behaviour`;
its bridges are `ledgerTrace` (reads are `ledgerOf` of the output chains)
and `proposalLive_txLive` (proposal liveness and partial synchrony give
transaction liveness; it needs catch-up `≥ Δ`, `Admissible.catchUp_pos`, so a
ready proposer was awake over the delivery interval before its release). `sysOf_adequate` gives `Adequate`.
`regimes_realizable` gives `RealizableActive`, hence `Realizable`
(`RealizableActive.toRealizable`; its stress witness keeps keys `1` and `2`
awake and the rest asleep; its L2-only `badProposer` witness puts a faulty
proposer slot in every progress window). Corollary
(`ConsensusShape/Service.lean`, `Accepted.activeService`): a final or
available output puts a relayed transaction into another honest node's
read on a clean healthy witness (`ActiveService`). A silent service or empty
outputs are therefore not accepted, for every protocol.

Design and history: `repos/goldilocks/notes/generic-interface/layers-plan.md`
in the workbench (latest: "Iteration 6: the definition of a good protocol");
the iteration-6 plan and reviews are in the run folder `iter6/`.

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
  Stable must be sleepy-live (`Behaviour.sleepyLive`). A schema that aliases
  stable to final is good only if its final output is live under sleepy
  participation (`stable_alias_final_sleepy_live`). Aliasing stable to
  available is allowed (Goldilocks).
- **Non-accountable BFT is out of scope**. Final accountability is
  mandatory, for fraction `α ≥ β` (standard ⅓), in every environment.
- **One GST and one outage per run: partially closed.** The prefix forms
  (`Good.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`) make the
  past safe before any later asynchrony. A run after an outage is a run with
  GST `b₁`. Runs with several GSTs or outages, judged as a whole, are out of
  scope.
- **Healthy means full participation** (Francesco, 2026-10-29). Every
  honest validator is awake throughout from `max g 0`, with fewer than `β·n`
  faulty. A rotating ⅔ is not healthy (`healthy_rotating_sleeper`), nor is a
  fixed ⅔ with one honest sleeper (`healthy_needs_full_participation`).
  Liveness with honest validators asleep is asked by the sleepy regime and
  its stress witness.
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
- `notReadyAtMost m` (Tendermint's contract, a placeholder) is a pointwise
  bound: the non-ready set may change over time, so it does not by itself put
  a ready honest round-robin leader within `m + 1` rounds (a schedule can sleep
  exactly the current leader through its round while staying within `m`). A
  round-robin proof needs a temporal leader-opportunity argument or a revised
  requirement: protocol work, not part of the definition.
- The collision escape is run-wide. Accountability compares two reads in one
  run.
- The network-level "knowledge of equivocation" service is not modelled (see
  the network section).
- Liveness premises must tolerate a bad proposer slot in every window
  (Francesco, 2026-10-29): `ProgressTolerant` asks `span + 2 ≤ gap` at some
  index of every provided output, witnessed by `RealizableActive.badProposer`.
  Beyond that, the gap is read as a number. The check is in L2 (L0 has no
  proposers): an L0 `Good` system with abstract progress is not bound by it.

## Goldilocks

`ConsensusShape/Values/Goldilocks.lean` pins the numbers (round-model FG-SA,
`Δ_F = Δ`, `κ = 2`, slow arming; `FGSAParams = ⟨R, lockK, eta⟩`):

| Number | Value |
|---|---|
| thresholds | standard (`θ = ½`, `β = ⅓`, `cover = ½`, `α = ⅓`) |
| catch-up; arming lag; budget; `η` | `18`; `4·lockK − 4`; `min eta (4·lockK − 5)`; `eta` |
| heal (available, stable), gap `k`; final, index `gf` | `29 + B_H^F(k)`; `29 + B_H^F(gf·R) + W_W(gf)` |
| latency | `4k + 6`; final `4·gf·R + 6 + W_W(gf)` |
| progress | `.recur ⟨single, k⟩`; final `.recur ⟨range(3R+κ), gf·R⟩` (tolerant indices: `k = 2`, `gf = 5`) |

`GoldilocksTarget F pp := GoldilocksBindings F ∧ Accepted F (goldilocksContract
pp) ∧ GoldilocksExtra F pp` is a reviewed target, not a proof that FG-SA meets
it; it is never changed to fit FG-SA. The sheet
(`ConsensusShape/Values/GoldilocksSheet.lean`) holds every intended-property
disposition: proved (`GoldilocksTarget.*`), stated (`GoldilocksExtraAt`
fields), not yet stated (§3), weaker than intended, and the twelve migration
obligations with the regime risk (obligations (1), (4), (9)).

## Gap dispositions

One line per gap (M1–M39 and the vacuous system), with `example`s for the
by-construction rows: `ConsensusShapeTests/Gaps.lean`.

## Tests (`ConsensusShapeTests/`)

- `Problem`: every L0 property has teeth; local accountability (`local_accountability_teeth`).
- `Network`: the delivery rule (wakers served within the bound, not instantly), faithfulness, silent runs and truncation.
- `Regimes`: what each regime admits and rejects; the explanatory L0 regime lemmas.
- `Good`: vacuous systems are not good; censoring progress, rotating sleepers, η-sleepy history.
- `Model`, `Blocks`, `Shape`: model mechanics, recurrence, compiled roles and poll mode.
- `Leaks`: do-nothing, fabricating and self-silencing protocols fail `ShapeClaims`; `recorder_live_testK` passes.
- `Realizable`: coverage, `allProposers_no_witness`, late-GST and late-outage witnesses.
- `Controls`: positive controls at explicit numbers.
- `Vacuity`: admissibility rejections, progress fit and tolerance, forgery, `noService_not_accepted`.
- `Goldilocks`: `pp223_numbers`, `stable_is_confirmed`, `outageWindow_prefix_only`, `weakPremise_inhabited`.
- `Values`, `Lift`, `Support`, `Common`: Streamlet and Tendermint, injective-hash lifting, fixtures.
- `Gaps`: the gap dispositions. `Index`: every cited name, checked to exist.

## Verification

```sh
LAKE_RESTORE_ARTIFACTS=true lake build
scripts/check.sh --no-build    # on the shared box: inside `job --mem 16G ...` (it refuses to run without RUN_DIR or CI)
```

The build checks that every cited name exists (`ConsensusShapeTests/Index`) and pins the review
theorems' types and axioms (`ConsensusShapeTests/ReviewAxioms`). `scripts/check.sh` runs the trust
checks: dependency pins, import discipline, EthLib check-decls over every declaration of every library
(axioms beyond `propext`, `Classical.choice` and `Quot.sound`, `sorry`, opaque/unsafe/extern/csimp), the
Spec surface (persisted-extension whitelist and the Spec snapshot `scripts/spec-snapshot.txt`), kernel
replay with `leanchecker`, a grep backstop, and the self-tests of every check. `lake check` and
`lake comparator` need `bwrap` and run in CI only (`.github/workflows/ci.yml`).
