# The generic consensus contract: review guide

## What this is

This project defines a good consensus protocol (`Good`), a generic execution model, and a shape layer.
The review statement is `Consensus.Review.AcceptedGood`: accepted shapes give good protocols.
Its three secondaries are `RegimesRealizable`, `LogFaithful`, and `HeldIffServed`.
`scripts/check.sh` checks the trust boundary locally and in CI: fast checks on every pull request, everything
(including kernel replay, `lake check` and the sandboxed comparator) nightly; see "Verification".
See `TRUST.md` for the assumptions and the roles of the checks.

## The review statement

`ConsensusSpec/Statements.lean` states the claim and its three secondaries verbatim below
(in namespace `Consensus.Review`, opening `Consensus.Shape`, `Consensus.Model`, and `Consensus.Blocks`):

```lean
/-- **The review statement (L2 ⇒ L0).** Every accepted shape instance is a good protocol (L0
`Good`) for every finite validator type. Exactly the type of `Consensus.Shape.Accepted.good`. -/
def AcceptedGood : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ShapeFamily O Info} {K : Contract ProgressReq}, Accepted F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Good (sysOf O (compiled F) V) (shapeProgress F V) K

/-- L2 beyond `Good`: with ≥ 5 validators, a family whose progress fits its skeleton and an
admissible, progress-tolerant contract have active witnesses, including the bad-proposer witness
that gives `ProgressTolerant` its meaning (`RealizableActive.badProposer`). `Accepted F K` carries
the three premises as fields. Exactly the type of `Consensus.Shape.regimes_realizable`. -/
def RegimesRealizable : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ShapeFamily O Info) (K : Contract ProgressReq),
    K.params.Admissible → ProgressFits K F → ProgressTolerant O K →
    ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V → RealizableActive F K V

/-- L1: the system's log is the engine's communication. Exactly the type of
`Consensus.Model.sysOf_log_faithful`. -/
def LogFaithful : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O}
    (r : (sysOf O F V).Run),
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox

/-- L1: on valid runs, for honest nodes and deadlines in the horizon, L0 `Held` is engine
`Run.Served`. Exactly the type of `Consensus.Model.Run.held_iff_served`. -/
def HeldIffServed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
    (rho : Run F E), rho.ExecutionValid → ∀ {w : V}, w ∈ rho.honest →
    ∀ (o : (protoOf F E).Object) {d : Time}, d ≤ rho.horizon →
      (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d)
```

The acceptance premise is `Consensus.Shape.Accepted`, from
`ConsensusSpec/Shape/Accepted.lean`:

```lean
structure Accepted (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : ProgressFits K F
  /-- Every provided output tolerates arbitrary numbers of validators not
  ready and a bad proposer slot in every window. -/
  progressTolerant : ProgressTolerant O K
```

`Accepted` carries the admissibility, progress-fit and progress-tolerance premises of
`RegimesRealizable`, as well as the protocol's claims and its served-output condition.
`ConsensusProofs/Review.lean` proves each review statement by its source theorem.
`ConsensusTests/ReviewAxioms.lean`, using `ConsensusTests/ReviewGuard.lean`, compiles
alpha-equality guards (including binder kinds) and `#guard_msgs` pins of the exact axiom lists
for both the review and source theorems. `ReviewGuard.checkComplete` requires every non-proof,
non-matcher constant declared in the statements module to have a review pair, including private
constants and declarations in other namespaces. The module must contain statements only.

In CI, `lake comparator --config comparator.json` compares `ConsensusChallenge.lean`
(the Spec statements with placeholder proofs) with `ConsensusProofs/Review.lean`:
matching statements, permitted axioms, sandboxed kernel replay, and identical reachable constants
in both exports to resist build-time tampering. This checks the proofs against Spec built alone;
Spec drift is checked by the snapshot diff and owner review.

`Accepted.good` combines three theorems. `refinement` gives `Behaviour`;
its bridges are `ledgerTrace` (reads are `ledgerOf` of the output chains)
and `proposalLive_txLive` (proposal liveness and partial synchrony give
transaction liveness; it needs catch-up `≥ Δ`, `Admissible.catchUp_pos`, so a
ready proposer was awake over the delivery interval before its release). `sysOf_adequate` gives `Adequate`.
`regimes_realizable` gives `RealizableActive`, hence `Realizable`
(`RealizableActive.toRealizable`; its stress witness keeps keys `1` and `2`
awake and the rest asleep; its L2-only `badProposer` witness puts a faulty
proposer slot in every progress window). Corollary
(`ConsensusProofs/Shape/Service.lean`, `Accepted.activeService`): a final or
available output puts a relayed transaction into another honest node's
read on a clean healthy witness (`ActiveService`). A silent service or empty
outputs are therefore not accepted, for every protocol.

## The definition of a good protocol

A protocol is **good** when its system `S` (with its progress reader `X`)
meets a contract `K` that supplies **only numbers**:

```lean
structure Good (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  behaviour  : Behaviour S X K                    -- the fixed property table, under fixed regimes
  adequate   : S.Adequate X                       -- the system is not vacuous
  realizable : 5 ≤ Fintype.card V → Realizable S X K  -- every regime is met, with active claims
```

(`ConsensusSpec/Problem/Good.lean`.) All three parts are L0 definitions. The
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
`ConsensusProofs/Problem/Facts/Good.lean`; `Agree`, `Safe`, `FaultsBelow`,
`ReadySafeUpTo` are in `ConsensusProofs/Problem/Derived.lean`), and in the Goldilocks sheet:

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

### The network rule (`ConsensusSpec/Problem/Network.lean`)

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

### The regimes, as formulas (`ConsensusSpec/Problem/Regimes.lean`)

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

In L2 the slot is `ProgressReq` (`ConsensusSpec/Blocks/Progress.lean`):

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

## What to read (the trusted surface)

To know what `Accepted F K` (or `Good`) means, read every file below, in this order.
The library root only collects imports.

<!-- spec-files -->

1. `ConsensusSpec/Problem/Basic.lean`: L0 vocabulary: capabilities, output schemas, environments and points, traces, communication logs and systems.
2. `ConsensusSpec/Problem/Network.lean`: Delivery and holding (`Held`, `TxHeld`), partial synchrony, synchrony up to a cut, outage networks and eager logs.
3. `ConsensusSpec/Problem/Properties.lean`: Trace claims: agreement, monotonicity, ready-reader safety, nesting, transaction liveness, resilience and local accountability.
4. `ConsensusSpec/Problem/Regimes.lean`: `Params`, `Contract`, admissible numbers, sleepy/healthy/outage regimes and the `cDur`, `heal`, `ready`, `lat` accessors.
5. `ConsensusSpec/Problem/Good.lean`: External data and progress readers, the property table (`Behaviour`), system adequacy, active claims and witnesses, `Realizable`, and `Good`.
6. `ConsensusSpec/Model/Objects.lean`: Authenticated wire objects, carried-object closure, signers, items and decidable equality.
7. `ConsensusSpec/Model/Protocol.lean`: Public parameters, closed selections, protocol interfaces, selection admissibility and families.
8. `ConsensusSpec/Model/Run.lean`: Events and their order, runs, engine state, releases, inboxes, views, slashing protection and local reads.
9. `ConsensusSpec/Model/Conditions.lean`: Signature unforgeability, valid selections, credentials, `ExecutionValid` and the engine communication log.
10. `ConsensusSpec/Model/System.lean`: Evidence-based conviction, observed hash collisions, `sysOf`, and external PKI/selection data (`sysExternal`).
11. `ConsensusSpec/Model/Served.lean`: Engine holding at a deadline (`Run.Served`), used by the `HeldIffServed` review statement.
12. `ConsensusSpec/Blocks/TimeGrid.lean`: Slots, their lengths and times, with phases measured in multiples of Δ.
13. `ConsensusSpec/Blocks/Progress.lean`: Patterns, recurrence windows, `ProgressReq`, `PatternRecurrence` and `NotReadyOn`.
14. `ConsensusSpec/Blocks/Chains.lean`: Headers and chains, explicit roots and digests, structural prefixes, linkage and provenance.
15. `ConsensusSpec/Blocks/Payload.lean`: Transaction encoding/decoding and `ledgerOf`: decoded inputs with first occurrences retained (`List.eraseDups`).
16. `ConsensusSpec/Shape/Shape.lean`: Skeletons, closed signing roles and proposal provenance, duties, `ChainShape` and `ShapeFamily`.
17. `ConsensusSpec/Shape/Compile.lean`: The compilation of skeleton duties and shape state machines to model protocols (`compiled`).
18. `ConsensusSpec/Shape/Run.lean`: Compiled systems (`Sys`), chain traces, output validity, proposal liveness and `shapeProgress`.
19. `ConsensusSpec/Shape/Claims.lean`: The chain-level safety, liveness, accountability and resilience claims (`ShapeClaims`).
20. `ConsensusSpec/Shape/ProgressFit.lean`: `ProgressFits` and `ProgressTolerant`: one proposer per recurrence slot and bad-slot/participation tolerance.
21. `ConsensusSpec/Shape/Active.lean`: Progress activity, `BadProposerEvery`, and `RealizableActive`, including its bad-proposer witness.
22. `ConsensusSpec/Shape/Accepted.lean`: The acceptance premise `Accepted`: protocol claims, admissible numbers, service, progress fit and tolerance.
23. `ConsensusSpec/Statements.lean`: The four review statements as `Prop` definitions: `AcceptedGood`, `RegimesRealizable`, `LogFaithful`, `HeldIffServed`.

<!-- /spec-files -->

Everything else is checked by Lean; `scripts/check.sh` checks the boundary:

0. **Pins:** exact toolchain, manifest, clean dependency checkouts and Lake's resolved search path match `scripts/pins.toml`.
1. **Build:** compile the four default libraries, the challenge, fixtures and check-decls; `--no-build` still checks Lake freshness.
2. **Imports:** enforce R1–R3, root coverage, library inventory and pinned-base names with `scripts/check-imports.py`.
3. **Declarations:** EthLib check-decls checks every module of every default library for extra axioms, unfinished proofs, opaque/unsafe/partial declarations, extern/implemented_by/csimp and opaque reachability; empty scopes fail.
4. **Spec surface:** check persisted extensions, diff the complete readable/structural snapshot (including pins/options), enforce theorem hygiene and constant-free parents; the `reach` report (which Spec definitions the review statements reach; not a gate) runs in `--full`, in `--changed` when step 4 runs, and in `--fast` with `--reach`.
5. **Kernel replay:** run leanchecker sequentially on every default-library leaf, one module per process after checking it has no descendants; parent modules own no constants.
6. **Review pins:** require the tests root to import the compiled alpha-equality guards and exact axiom pins.
7. **Backstop:** grep for unfinished/native proofs, kernel bypasses, Spec metacommands and unsafe lakefile options.
8. **Vendored:** verify all vendored EthLib copies against `scripts/vendor.sha256`.
9. **Comparator config:** pin challenge/solution modules, all four statement names and exactly the three standard axioms; validate the Spec-only challenge.
10. **Lake check (needs bubblewrap; skipped and listed as CI-only where `bwrap` is missing):** sandboxed build, export and kernel replay of the default targets, rejecting extra axioms.
11. **Lake comparator (needs bubblewrap, likewise):** statement/axiom matching, sandboxed replay and agreement of reachable constants between challenge and solution exports.
12. **Docs:** require the marked list above to equal every file under `ConsensusSpec/` exactly.

Checks with fixtures exercise the same code paths on positive and negative controls.
Spec drift is guarded by the snapshot diff plus owner review (`spec-approved`);
dependency drift by pins; proof validity by replay, check-decls and the CI comparator.

Proof support outside that surface: `ConsensusProofs/Problem/Derived.lean` defines
`Agree`, `Safe`, `ReadySafeUpTo`, `FaultsBelow`, `SendsFromZero` and `Trace.map`,
which `Good` does not read. `ConsensusProofs/Problem/Facts/` holds the derived `Good.*`
lemmas, including `Good.served`; `ConsensusProofs/Blocks/Facts.lean` holds the block lemmas.
`ConsensusProofs/Shape/Payload.lean` proves the payload bridges;
`ConsensusProofs/Shape/Refinement.lean`, `ConsensusProofs/Shape/Realizable.lean`,
`ConsensusProofs/Shape/Accepted.lean` and `ConsensusProofs/Shape/Service.lean` prove
refinement, coverage/witnesses, acceptance and `Accepted.activeService`.
`ConsensusProofs/Model/` proves `sysOf_adequate`, `sysOf_log_faithful`,
`Run.held_iff_served`, `sysOf_nonFraming` and `sysOf_laws`, with support for canonical runs
(`canonical_run_from`), truncation (`Run.truncate_*`), views (`Run.mem_viewIdx_iff`)
and slashing protection (`honestNeverSlashed`). A node's `Run.ViewIdx` is the closure
of its engine `seen` log; the view lemma gives the event-index form.
Injective-hash lifting is checked in `ConsensusTests/Lift.lean`.

## Layout

Lean module names are global. The directories are `ConsensusSpec/`, `ConsensusProofs/`,
`ConsensusInstances/` and `ConsensusTests/`, rather than `Spec/` etc.: a top-level `Spec`
would collide with other packages. The library name is the module prefix; namespaces stay unchanged.

| Default library / directory | Contents | Import rules |
|---|---|---|
| `ConsensusSpec/` | Trusted definitions and review statements | R1: its closure, including the root, contains only Spec project modules and the pinned base set. |
| `ConsensusProofs/` | Proofs, derived definitions, canonical runs and witnesses | R3: may import Spec and Proofs; never Instances, Tests, the challenge or fixtures. |
| `ConsensusInstances/` | Goldilocks and sheet, Bft, Streamlet, Tendermint | R3: may import Spec, Proofs and Instances; never Tests, the challenge or fixtures. |
| `ConsensusTests/` | Teeth, rejections, controls, review pins and citation index | May import the four default libraries, never the challenge or fixtures. |

R2 applies to all four: every file is reached from its library root, and no non-root module
imports a package root except in Tests. Roots and other modules with descendants own no constants.
R1's external base set is `Init`, `Std`, `Lean`, `Lake`, `Mathlib`, `Batteries`, `Aesop`, `Qq`,
`ProofWidgets`, `Plausible`, `ImportGraph`, `LeanSearchClient`; unknown names fail.
Pins establish the provenance of those names. R1 exceptions need a design review.
The inventory configuration is cross-checked against `lakefile.toml`, including default targets
and globs; module components named `Proofs` or `Exports` are refused because check-decls
exempts those names (`ConsensusProofs` is a different, unexempted component).

In `scripts/`:

- `check.sh`: the single driver, fixture self-tests and pass/fail/skip summary.
- `check-imports.py`, `boundaries.toml`: parsed imports, R1–R3 and library inventory.
- `check-pins.py`, `pins.toml`: toolchain, dependency revisions, clean checkouts and resolution checks.
- `SpecSurface.lean`, `spec-extensions.txt`, `spec-theorems.txt`, `spec-snapshot.txt`: persisted-extension policy, theorem hygiene and the reviewed Spec snapshot.
- `CheckDecls.lean`, `check_decls_baseline.txt`: EthLib declaration checker (one local performance patch, see TRUST.md) and reviewed exceptions.
- `test_check_decls.sh`, `CheckDeclsTest.lean`, `CheckDeclsTest/`, `CheckDeclsForeign.lean`: verbatim EthLib fixture suite.
- `LICENSE.EthLib`, `vendor.sha256`: CC0 licence and hashes of every vendored copy.
- `fixtures/`: import, Spec-surface, review-pin, grep, pins, docs, comparator and Lake-check controls.

The non-default libraries are `ConsensusChallenge` (`ConsensusChallenge.lean`, comparator statements
with placeholder proofs, importing Spec only), rootless `CheckFixtures` (under `scripts/fixtures/`,
each fixture a separate target), and `CheckDeclsTest` (EthLib fixtures under `scripts/`).
They may contain deliberately unfinished proofs or extra axioms; no default library imports them.
`comparator.json` connects the challenge to `ConsensusProofs/Review.lean`.

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

## Instances (`ConsensusInstances/`)

### Goldilocks

`ConsensusInstances/Goldilocks.lean` pins the numbers (round-model FG-SA,
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
(`ConsensusInstances/GoldilocksSheet.lean`) holds every intended-property
disposition: proved (`GoldilocksTarget.*`), stated (`GoldilocksExtraAt`
fields), not yet stated (§3), weaker than intended, and the twelve migration
obligations with the regime risk (obligations (1), (4), (9)).

### Bft, Streamlet and Tendermint

`ConsensusInstances/Bft.lean` supplies the common final-only schema `bftCore`, affine bounds
and `bftContract`: index `k : ℕ+`, standard thresholds, catch-up, heal point
`max g 0 + (catchUp + 1 + heal k)·Δ`, and latency `latency k` in Δ-coefficients.
Outage numbers are unused because there is no stable output.

`ConsensusInstances/Streamlet.lean` gives `2·Δ` slots, one proposer per slot, polling disabled,
and all-validator votes at phase 1. Progress is five consecutive honest ready proposers
in every window of `k` slots (`Pattern.range 5`); gap 6 supplies the tolerant index.

`ConsensusInstances/Tendermint.lean` gives a poll shape, no slot proposals or committee kinds,
and all-validator polling at every unit tick. Height is in `pos`, round in `info`; round-robin
leadership is computed locally. A locked value is re-proposed by carrying its signed header.
Progress is the pointwise `notReadyAtMost m` placeholder described in Scope.
These are values and fit/tolerance proofs, with no concrete protocol proofs.

## Tests (`ConsensusTests/`)

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
- `Lift`, `Support`, `Common`: injective-hash lifting and fixtures; the former `Values` live in `ConsensusInstances/Bft.lean`, `ConsensusInstances/Streamlet.lean` and `ConsensusInstances/Tendermint.lean`.
- `ReviewAxioms`, `ReviewGuard`: statement alpha-equality, completeness and axiom pins.
- `Gaps`: the gap dispositions. `Index`: every cited name, checked to exist.

### Gap dispositions

One line per gap (M1–M39 and the vacuous system), with `example`s for the
by-construction rows: `ConsensusTests/Gaps.lean`.

## Verification

`scripts/check.sh` has three modes; every step it does not run prints `SKIP  <step> (<reason>)`:

| Mode | Runs | Where |
|---|---|---|
| `--fast` (default) | steps 0–4, 6–9, 12: pins, build, imports, check-decls, Spec surface + snapshot diff, review pins, grep, vendored hashes, comparator config, docs; self-tests only with `--selftests`, step 4's `reach` report only with `--reach` | CI on every PR and push to main (`.github/workflows/ci.yml`, with `--selftests` when `scripts/` or the build configuration changed, `--reach` when the Spec, the challenge or `scripts/` changed) |
| `--full` | everything: the fast steps, every self-test, leanchecker replay (5), `lake check` (10), `lake comparator --paranoid` (11) | CI nightly, on demand and on `milestone*`/`release*` tags (`.github/workflows/full.yml`, clean project build) |
| `--changed [<base>]` | the fast steps restricted to what changed since `<base>` (default: merge-base with `origin/main`, uncommitted and untracked files included): build of the changed modules' downstream cone, check-decls on the affected libraries, Spec surface and comparator config only if a Spec module (or the challenge, `comparator.json`, the solution's imports) changed (otherwise only noconst of step 4), grep on the changed files; pins, imports, review pins, vendored hashes and docs in full (cheap). A change of `scripts/` or of the build configuration falls back to `--fast` (with self-tests for `scripts/`); with `--selftests` it runs `--fast --selftests` | locally, `scripts/check-changed.sh [<base>]` |

Only `--full` ends with `check.sh: ALL CHECKS PASSED`; the others end with `check.sh: PASSED (<mode> mode; ...)`.

### Local workflow

On the shared box every build and check runs in a job (replace `<name>` and `<worktree>`):

1. Iterate on one file with `lake env lean <file>` (after building its imports), or on one declaration with
   `turbo-lean check <file> --decl <name>` (a single declaration only; `lake build` stays the gate).
2. Before committing, check what changed:
   ```sh
   job --mem 16G --cpus 8 consensus-lean <name> -- bash -lc "cd <worktree> && LAKE_RESTORE_ARTIFACTS=true scripts/check-changed.sh"
   ```
3. Commit, push the `work/<agent>/<task>` branch and open a PR when ready: pushes without a PR run no CI.
   The PR runs the fast tier; the nightly full run covers replay, `lake check` and the comparator.
   Before a milestone, run the full check once (`scripts/check.sh --full` in a job, about an hour of CPU)
   or trigger `full.yml` (`gh workflow run full.yml --ref <branch>`).

`check.sh` refuses to run without `RUN_DIR` (set by `job`) or `CI`. Elsewhere: `CI=1 scripts/check.sh --full`.

The build checks every cited name (`ConsensusTests/Index.lean`) and compiles the review
type/axiom pins (`ConsensusTests/ReviewAxioms.lean`). `--no-build` skips compilation but still
uses Lake's freshness gate, so stale artifacts fail. Snapshot/extension updates fail deliberately so
their diff is reviewed; CI refuses update flags and `--no-build`, and checks that the tree stays clean.

`lake check` and `lake comparator` need bubblewrap (`bwrap`). Where it is missing, `--full` skips
them and lists them as **CI-only**; `full.yml` always runs them, with their fixtures and a guard that
fails on any skipped step. The shared box has `bwrap` (installed 2026-10-29), so a local `--full` run
executes them too. The comparator runs with `--paranoid`: the review statements' closure is replayed by
Lean's kernel and by every external kernel bundled with Lean (leanchecker-paranoid, lean4lean, nanoda,
con-leche, con-ron), about 3 minutes in CI. leanchecker replays every default-library leaf sequentially,
one module per process; never invoke it on a root or prefix with descendants.

CI caching (fast tier): Mathlib's oleans come from `lake exe cache get` (plus an actions/cache of
`.lake/packages` keyed on the manifest and toolchain); the project's `.lake/build` is an actions/cache
keyed on toolchain + manifest + commit, falling back to the PR's previous push or main's latest, so Lake
rebuilds only changed modules and their dependents. The full tier builds the project from scratch.

CI timings (GitHub-hosted runner): before the tiers, every push ran everything in about 50 minutes
(build 3, check-decls 7.5, Spec surface 3.5, self-tests 4, leanchecker replay 9.5, `lake check` 19,
comparator 1, setup 2). Fast tier (measured on PR #15, with self-tests because it changed `scripts/`):
17 minutes cold, 17 minutes with the build cache warm (setup 1.6, build 0.2, check-decls 4–7.5, Spec surface
3, self-tests 4); without self-tests, the usual PR, about 10–13 minutes. check-decls is now the largest step.

The owner-review boundary is separate from correctness. The **trusted surface** is `ConsensusSpec/**`,
`ConsensusSpec.lean`, `ConsensusChallenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
`ConsensusTests/ReviewAxioms.lean` and `ConsensusTests/ReviewGuard.lean`. The annotated git tag
`spec-approved` marks the last approved commit (4b7c5148, approved 2026-10-29); only the owner, or an
agent he explicitly authorizes, moves it. CI job `review-boundary` fails while the trusted surface differs
from that tag (it would only warn if the tag did not exist), so a PR changing it is approved by moving the
tag to the PR's head before merge. The check infrastructure (`scripts/**`, `.github/**`, `lakefile.toml`,
`lakefile.lean`, which must not exist) is owner-reviewed through `.github/CODEOWNERS` and PR review.
Reviewing the snapshot diff is the act that approves a Spec change; the comparator cannot replace that
review. `docs/spec-review.md` records what was approved and what changed since 2852f717.

Design and history: `repos/goldilocks/notes/generic-interface/layers-plan.md`
in the workbench (latest: "Iteration 6: the definition of a good protocol");
the iteration-6 plan and reviews are in the run folder `iter6/`.
