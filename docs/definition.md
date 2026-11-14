# The definition of a correct consensus protocol

This document states, in full, what the certified statements mean: the statements themselves, the definition
of a correct protocol (`CorrectProtocol`), the network rule, the regimes, the numbers a protocol supplies, what
the execution model fixes, the assumptions the model makes about the world, and the scope. The README gives
the summary; `TRUST.md` says what is trusted and what the checks guarantee.

The definition has three levels, named L0, L1 and L2 below. **L0** (`ConsensusLean/Spec/Problem/`) defines a
correct protocol for an abstract system: runs, reads, a communication log and the regimes. **L1**
(`ConsensusLean/Spec/Model/`) is the execution model: validators with keys, signatures, the engine that runs a
protocol's code, and `sysOf`, which turns a protocol into an L0 system. **L2** (`ConsensusLean/Spec/Shape/`) is
the chain shape: slots, proposers, votes and a state machine, compiled to an L1 protocol (`compiled`).

## The headline statement

`Challenge.lean` certifies nine statements: the five review statements below and, for Goldilocks, the endpoint
and headline below, the headline's explicit-excuse form `GoldilocksCorrectWithExcuses`, and the outage row at
every vote binding `PersistsWith` (the endpoint's `persists` claim for `goldilocksWith S`, every `S : BoundSetup`). The headline is `Consensus.Goldilocks.GoldilocksCorrect`, from
`ConsensusLean/Instances/Goldilocks/Statements/Obligations.lean` (in namespace `Consensus.Goldilocks`), together
with the endpoint it composes:

```lean
/-- **Goldilocks meets the obligations**, the concrete endpoint: for every setup and every
assumption set (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`), the
Goldilocks family meets the obligations as an Ebb-and-Flow protocol (its schema provides exactly
the final, stable and available capabilities; available and stable are both the `confirmed`
output) at the contract `goldilocksContract A (contract_coefficients S A)`, every number of which
is fixed above. -/
def MeetsObligations : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligationsAs .ebbAndFlow (goldilocks S) (goldilocksContract A (contract_coefficients S A))

/-- **Goldilocks is correct**, the headline statement: for every setup `S`, every assumption set
`A` (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`) and every finite
validator type `V`, the Goldilocks family, compiled and run by the general execution model
(`sysOf schema (compiled (goldilocks S)) V`, with progress read by `shapeProgress`), is an L0
`CorrectProtocol` at the contract `goldilocksContract A (contract_coefficients S A)`. It composes
`MeetsObligations` with the review statement `ObligationsSufficient`; it has their parameters and
no further hypothesis. -/
def GoldilocksCorrect : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocol (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V) (goldilocksContract A (contract_coefficients S A))
```

`Solution.lean` proves it as `fun S A V => ShapeObligations.correct (Obligations.meets_obligations S A).2 V`: the
generic statement `ObligationsSufficient` below, applied to the Goldilocks endpoint `MeetsObligations` without its
profile label (`.2`; the profile is below). The other
four certified statements are the generic ones that follow.

## The statements

`ConsensusLean/Statements/Review.lean` states the claim and its three secondaries verbatim below
(in namespace `Consensus.Review`, opening `Consensus.Shape`, `Consensus.Model`, and `Consensus.Blocks`):

```lean
/-- **The review statement (L2 ⇒ L0).** Every shape instance that meets its obligations is a correct
protocol (L0 `CorrectProtocol`) for every finite validator type. Exactly the type of
`Consensus.Shape.ShapeObligations.correct`. -/
def ObligationsSufficient : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ChainShapeFamily O Info} {K : Contract ProgressReq}, ShapeObligations F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      CorrectProtocol (sysOf O (compiled F) V) (shapeProgress F V) K

/-- L2 beyond `CorrectProtocol`: with ≥ 5 validators, a family whose progress fits its skeleton and
an admissible, progress-tolerant contract have active witnesses, including the bad-proposer witness
that gives `ProgressTolerant` its meaning (`RealizableActive.badProposer`). `ShapeObligations F K`
carries the three premises as fields. Exactly the type of `Consensus.Shape.regimes_realizable`. -/
def RegimesRealizable : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq),
    K.params.Admissible → ProgressFits K F → ProgressTolerant O K →
    ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V → RealizableActive F K V

/-- L1: the system's log is the engine's communication. Exactly the type of
`Consensus.Model.sysOf_log_faithful`. -/
def LogFaithful : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    (r : (sysOf O F V).Run),
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox

/-- L1: on valid runs, for honest nodes and deadlines in the horizon, L0 `Held` is engine
`Run.Served`. Exactly the type of `Consensus.Model.Run.held_iff_served`. -/
def HeldIffServed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}
    (rho : Run F E), rho.ExecutionValid → ∀ (o : (protoOf F E).Object) {w : V} {d : Time},
    w ∉ rho.faultyAt d → d ≤ rho.horizon →
      (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d)

/-- **The review statement on a class of runs.** ... Exactly the type of
`Consensus.Shape.ShapeObligationsOn.correct`. -/
def ObligationsSufficientOn : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ChainShapeFamily O Info} {K : Contract ProgressReq} (Q : ∀ V : Type, EnvPoint V → Prop),
    ShapeObligationsOn F K Q → ∀ (V : Type) [Fintype V] [DecidableEq V],
      CorrectProtocolOn (sysOf O (compiled F) V) (shapeProgress F V) K (Q V)
```

At `Q = fun _ p => p.ConstantFaults`, `ObligationsSufficientOn` is the review statement of the static
adversary at full strength (with, in addition, the adequacy and growth realizability of the growing-fault
system); the growing-fault statements are additional to it.

The obligations premise is `Consensus.Shape.ShapeObligations`, from
`ConsensusLean/Spec/Shape/Obligations.lean`:

```lean
structure ShapeObligations (F : ChainShapeFamily O Info) (K : Contract ProgressReq) : Prop where
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

`ShapeObligations` carries the admissibility, progress-fit and progress-tolerance premises of
`RegimesRealizable`, as well as the protocol's claims and its served-output condition.

**Profiles.** An endpoint states which standard capability set the protocol provides, as a checked
label (`ConsensusLean/Spec/Problem/Profile.lean`, `ConsensusLean/Spec/Shape/Obligations.lean`):

```lean
inductive Profile where
  | ebbAndFlow  -- final, stable and available
  | bft         -- final only
  | available   -- available and stable, no final

def Profile.Matches (p : Profile) (O : OutputSchema) : Prop :=
  ∀ cap, (O.output cap).isSome = p.provides cap

def ShapeObligationsAs (p : Profile) (F : ChainShapeFamily O Info) (K : Contract ProgressReq) : Prop :=
  p.Matches O ∧ ShapeObligations F K
```

The match is exact (a capability of the profile is provided, every other one is not) and compares
capabilities only: the output type is not fixed, outputs may alias (Goldilocks serves available and
stable by one `confirmed` output) and identifiers that serve no capability are allowed. The three
profiles are not exhaustive: an available-only schema matches none, and `ShapeObligations` and
`CorrectProtocol` apply to it unchanged. A profile is a label, not a property set: `Behaviour`
selects its rows from the schema alone, so the label adds no claim and removes none, and
`ObligationsSufficient` stays the one generic review statement. The Goldilocks endpoint is
`ShapeObligationsAs .ebbAndFlow`; the label is decided by its fixed schema, so the labelled endpoint
is equivalent to the unlabelled one.

`ShapeObligations.correct` combines three theorems. `refinement` gives `Behaviour`;
its bridges are `ledgerTrace` (reads are `ledgerOf` of the output chains)
and `proposalLive_txLive` (proposal liveness and partial synchrony give
transaction liveness; it needs catch-up `≥ ΔAC`, `Admissible.catchUp_pos`, so a
ready proposer was awake over the delivery interval before its release). `sysOf_adequate` gives `Adequate`.
`regimes_realizable` gives `RealizableActive`, hence `Realizable`
(`RealizableActive.toRealizable`; its stress witness keeps keys `1` and `2`
awake and the rest asleep; its L2-only `badProposer` witness puts a faulty
proposer slot in every progress window). Corollary
(`ConsensusLean/Main.lean`, `ShapeObligations.activeService`): a final or
available output puts a relayed transaction into another honest node's
read on a clean healthy witness (`ActiveService`). A silent service or empty
outputs therefore cannot meet the obligations, for every protocol.

## The definition of a correct protocol

A protocol is **correct** when its system `S` (with its progress reader `X`)
meets a contract `K` that supplies **only numbers**:

```lean
structure CorrectProtocol (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  behaviour  : Behaviour S X K                    -- the fixed property table, under fixed regimes
  adequate   : S.Adequate X                       -- the system is not vacuous
  realizable : 5 ≤ Fintype.card V → Realizable S X K  -- every regime is met, with active claims
```

(`ConsensusLean/Spec/Problem/CorrectProtocol.lean`.) All three parts are L0 definitions. The
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
    requirement that held for the point and the data, and preserves that
    datum's selected population at every observation time;
  - `prefixClosed`: the prefix of a valid run up to any `b ∈ [0, horizon]` is a valid run
    with the same reads, views and log up to `b`, no new excuse, and the same
    progress on windows that end by `b`. It preserves the original run's
    selected population at every time, not just times up to `b`.
- **`Realizable`** (at least five validators): every regime is met by a clean
  witness. A witness is valid, has no excuse, and has a faulty and an honest
  validator. The witnesses exist at every `ΔAC` and every FG delay `ΔFG` (healthy: every
  `ΔFG ≤ fgDelay·ΔAC`), at every GST `g ≥ 0` (healthy: with a
  log that is silent before the GST), and for outages armed arbitrarily late.
  Each witness has active claims (the sleepy and healthy witnesses bundle
  regime, progress and `TxLiveActive` as `SleepyLive` and `HealthyLive`):
  - `TxLiveActive`: a transaction to serve, read by a different honest node
    that was never submitted it;
  - `SafeActive`: two ready readers, one of them at two times;
  - `OutageActive`: a ready source, a real sleeper inside the window and a
    reader ready from the recovery point `b₁ + recovery·ΔAC`.

  A **stress witness** exercises liveness with many honest validators
  asleep, so a progress requirement cannot quietly demand near-full
  participation. For every provided available or stable output and every
  validator count, at *one* index (it may depend on the validators, not on
  `ΔAC` or `ΔFG`):
  - `sleepyStress`: at every `ΔAC` and `ΔFG`, a sleepy witness where at most
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

For shape protocols, `ShapeObligations.correct` (L2) proves all three parts. The correct
protocols we accept are
`CorrectProtocol (sysOf O (compiled F) V) (shapeProgress F V) K`, for every finite `V`.

### The property table (`Behaviour`)

Notation (the `System` accessors of `Regimes.lean`): `c = cDur = catchUp·ΔAC`;
`heal(cap,i,g) = max g 0 + heal cap i·ΔAC`; `ready(g) = max g 0 + c + 1`;
`lat = latency cap i·ΔAC`;
`prog[a,b]` = the progress requirement of `cap` at index `i` on `[a, b]`;
`HC` = the excuse.

| Output | Property | Regime | Claim (`∨ HC` unless "always") |
|---|---|---|---|
| all | non-framing | always | a validator honest at `d` is never convicted by the evidence nodes saw while honest by `d` |
| all | nesting | always | `final ⪯ stable ⪯ available` in every honest read, at every cut |
| final | no rollback | always | `Monotone final 0` |
| final | accountable safety | every environment and network (premise `True`) | two conflicting honest reads convict `≥ α·n` from their own two views (local) |
| all | healthy liveness (`healthyLive`) | `Healthy g ∧ prog[ready g, horizon]` (progress of that capability) | `TxLive c g heal(cap,i,g) lat` |
| available, stable | sleepy safety | `Sleepy` | `ReadySafe c g 0` |
| available, stable | sleepy liveness | `Sleepy ∧ prog[0, horizon]` | `TxLive c g 0 lat` |
| available, stable | healed safety ("stay in recovery") | `Healthy g ∧ prog[ready g, heal]` | `ReadySafe c g heal` |
| stable | outage resilience | `Outage T b₀ b₁` | `ProtectedReadyFrom c stable target T (b₁ + recovery·ΔAC)` |

One field per row (`finalAccountable`, `healthyLive`, `sleepySafe`, `sleepyLive`,
`healedSafe`, `persists`). Derived in L0 (`CorrectProtocol.*`,
`ConsensusLean/Lemmas/Problem/Facts/CorrectProtocol.lean`; `Agree`, `Safe`, `FaultsBelow`,
`ReadySafeUpTo` are in `ConsensusLean/Lemmas/Problem/Derived.lean`):

| Theorem | Statement |
|---|---|
| `final_agree` | `FaultsBelow α` ⇒ `Agree final 0 ∨ HC`, in any network |
| `final_safe_healthy` | `Healthy g` ⇒ `Safe final 0 ∨ HC` (uses `β ≤ α`) |
| `persists_final_compatible` | through an outage, the stable read at `T` and the final read of a reader ready from `b₁ + recovery·ΔAC` are compatible |
| **prefix forms** `sleepySafe_prefix` | `SyncUntil b ∧ SleepyOn θ c 0 b` ⇒ `ReadySafeUpTo c g 0 b ∨ HC`: the past is safe whatever happens after `b` |
| `healedSafe_prefix` | partial synchrony with GST `g` for deadlines up to `b`, `HealthyOn β g b`, `prog[ready, heal]` and `heal ≤ b` ⇒ `ReadySafeUpTo c g heal b ∨ HC` |
| `outage_prefix` | the outage regime up to `b` ⇒ protection of ready readers at reading times in `[b₁ + recovery·ΔAC, b]` ∨ HC |

`TxLive c g start D` covers every submission: a transaction submitted to an
awake honest node by `t` is in the `g`-read of every ready reader at every
`t' ∈ [max t start + ΔAC + D, horizon]`. Safety has one body,
`AgreeAmong R`/`MonotoneAmong R` for a reader predicate `R` checked at each
cut: `Agree`/`Monotone` (and `Safe`) take honest readers; `ReadySafe` takes ready readers
only: honest, and awake throughout `[max 0 (t − c − 1), t]`. A node that
has been asleep for long may still hold an old fork. `ProtectedReadyFrom`
works as follows. Take a node **ready** at `T` and its `stable` read at `T`.
That read is a prefix of the `target` read (the available output if
provided, else the stable output) at every `t ∈ [b₁ + recovery·ΔAC, horizon]`,
for every node ready at `t`. The outage regime has no absolute participation
premise: besides η-sleepy participation, no honest validator falls asleep in
the no-sleep window `[b₀ − noSleep·ΔAC, b₁ + noSleep·ΔAC]` (clamped to
`[0, horizon]`; waking is allowed), and the faulty validators with the late
wakers of that window are fewer than the honest validators awake at its start.

An outage run is partially synchronous with GST `b₁` (`OutageNet b₀ b₁`
contains `PSync b₁`), so the after-GST rows apply with `g = b₁` when their
other premises hold.

### The network rule (`ConsensusLean/Spec/Problem/Network.lean`)

The delivery rule is normal delivery (`CommLog.Delivers.msgs`):

> every message an honest node sends at `t` is received, strictly before the
> delivery bound, by every honest node that is awake over the delivery
> interval, and is re-served, strictly before the bound, to nodes that wake
> later.

The delivery interval is half-open, `[t, max(t, GST) + ΔAC)`, as in the paper's
`Sync`; on integer time "strictly before `d`" is "by `d − 1`". Formally, for a
deadline function `dl` (`max a GST + ΔAC − 1` in partial synchrony): for every
start `a ≥ t`, every honest node awake throughout `[a, dl a]` holds the message
at `dl a`. At `a = t`: a node awake over `[t, max(t, GST) + ΔAC − 1]` has it by
`max(t, GST) + ΔAC − 1`, so its tick at `max(t, GST) + ΔAC` (which runs before the
deliveries of that time) reads it. At a later `a`: a node that wakes at `a` and
stays awake has it by `max(a, GST) + ΔAC − 1`, not at the wake itself (no instant
re-delivery; tests `waker_within_bound`, `waker_not_instant`). At `ΔAC = 1` this
is same-time delivery; realizability starts at `ΔAC = ΔFG = 2` (`Realizable`), and
every behaviour claim holds at every `ΔAC ≥ 1`.

**Two bounds.** The environment has a message bound `ΔAC` and an FG attestation bound `ΔFG`
(`Env.ΔAC`, `Env.ΔFG`, both positive; neither bounds the other). The log carries
the protocol's message class (`CommLog.fgAtt`): for model runs it is filled only
from `Protocol.isFGAtt` (`Run.log`, `tagLog`, `sysOf_log_fgAtt`), so no theorem or
regime about the model can choose another one (an abstract L0 `System` fixes
its own). FG attestations are served by `Delivers.fgAtts` with their own deadline function
`dlF` (`max a GST + ΔFG − 1` in partial synchrony); every other message by
`Delivers.msgs` with `dl`, and an FG attestation is never served by `msgs`. When `ΔFG < ΔAC`,
FG attestations may overtake blocks; no statement claims a block or a vote strictly before `ΔFG`.
For Goldilocks the FG attestation objects are the standalone attestations and the relay wrappers
of attestations only; a mixed relay wrapper is delivered strictly before `ΔAC`. Every other protocol has none (`isFGAtt` defaults to
`False`), which is the single-bound model (tests `two_bound_witnesses`,
`row_held_to_row_bound`, `nonrow_held_to_message_bound`).

- "Has it at `d`" is `Held`. The node sent or received the message
  at some `t' ≤ d`, and did not wake in `(t', d]`. Receipt at the deadline
  itself counts. A restart loses earlier receipts.
- **Transactions** (`Delivers.txs`), the same rule at `dl` (bound `ΔAC`): a transaction submitted at
  `τ ≥ 0` to an awake honest node is held (`TxHeld`, in the inbox at some
  `τ' ∈ [0, d]`) at `dl a` by every honest node awake throughout `[a, dl a]`,
  for every `a ≥ τ`.
- Sends are covered at every time, negative ones included. Submissions are
  covered from `0`. With `SendsFromZero` (in `DerivedFacts`; true of every valid model run),
  `PSync 0` is synchrony (`PSync.syncUntil_zero`).
- Receipt is a network service, not protocol use. In the model, what arrives
  is processed at the delivery, which may run the protocol's delivery duties
  and release at once; a tick first reads it at the node's next tick, at the
  latest the tick at the bound itself.

Instances: `PSync g` (deadline `max a g + ΔAC − 1`, FG attestations `max a g + ΔFG − 1`),
`SyncUntil b` (deadline `a + ΔAC − 1`, FG attestations `a + ΔFG − 1`, for deadlines up to `b`), and
`OutageNet b₀ b₁ = SyncUntil b₀ ∧ PSync b₁`. Every delivery obligation (all
three clauses, in every instance)
applies only when its deadline is within both the cut and the horizon: a
`SyncUntil b` with `b` past the horizon still promises nothing after the
horizon. `PSync.mono` (tests): a later GST is weaker.

`EagerFrom g` is the shape of the canonical log: every honest send at `t` is
received at every awake time in `(max t g, horizon]`, and no message is
received before `g` ("silent" refers to message receipts only:
`EagerFrom.txs` still relays transaction inboxes at once). It meets an
instance only under these hypotheses:
- `EagerFrom.delivers`: `Delivers dl dlF cut` for any `dl`, `dlF` with
  `∀ a, max a g < dl a` and `∀ a, max a g < dlF a`;
- `EagerFrom.psync`: `PSync g'` for `g ≤ g'`;
- `EagerFrom.syncUntil`: `SyncUntil b` for every `b`, given `g ≤ 0` and
  `SendsFromZero`.

It does not imply an arbitrary `SyncUntil b` or `OutageNet b₀ b₁`. Example:
`ΔAC = 1`, `g = 10`, an honest send at `0` and an honest receiver awake
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
that share a key. It is a possible later extension.

### The regimes, as formulas (`ConsensusLean/Spec/Problem/Regimes.lean`)

Here `p` is the environment point (awake profile, honest set, horizon,
submissions), `L` is the run's log, `n = |V|`, `ready_t = readyAt c t` and
`faulty` is the complement of the honest set.

| Regime | Definition |
|---|---|
| `System.Sleepy` | `L.PSync p 0 ∧ ∀ t ∈ [0, horizon], θ·(\|ready_t\| + f_d) < \|ready_t\|` on the view retained through `d = min (t + ahead·ΔAC) horizon` (ready at `t` and honest at `d`; `f_d` compromised by `d`) |
| `System.Healthy g` | `L.PSync p g ∧ f_horizon < β·n ∧ ∀ t ∈ [max g 0, horizon], every validator honest at t is awake at t ∧ ΔFG ≤ fgDelay·ΔAC` (full participation; awake, not ready; the FG delay bound is an upper envelope, not a deadline) |
| `System.Outage T b₀ b₁` | `OutageTimes ∧ L.OutageNet p b₀ b₁ ∧ EtaSleepyOn θ (η·ΔAC) c (ahead·ΔAC) 0 horizon ∧ NoSleepOn a z ∧ CohortOn a z`, the last two on the view retained through `cohortAt = min (z + cohortAhead·ΔAC) horizon` (`a`, `z`: `outageStart`, `outageEnd`; the surviving cohort) |
| `OutageTimes` | `0 ≤ T ∧ T + lag·ΔAC ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + budget·ΔAC` |
| η-sleepy at `t` (`η > 0`) | `θ·\|ready_t ∪ awakeIn [max 0 (t − η·ΔAC), t] ∪ faulty\| < \|ready_t\|` on the same retained view (one fixed partition, so the union keeps identities) |

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
  catchUp : Nat   -- reader catch-up c = catchUp·ΔAC
  θ β cover α : ℚ -- sleepy, healthy fault bound, cover (read by no regime), accountable fraction
  lag budget η : Nat                         -- outage arming lag, budget, look-back (ΔAC-coefficients)
  noSleep recovery : Nat                     -- outage no-sleep margin C, recovery delay D (ΔAC-coefficients)
  heal latency : Capability → Idx → Nat      -- heal point after max g 0; transaction latency
  fgDelay : ℕ+                               -- healthy regime: ΔFG ≤ fgDelay·ΔAC (larger = weaker premise)
def Params.standard (catchUp lag budget heal latency) :=
  { catchUp, θ := ½, β := ⅓, cover := ½, α := ⅓, lag, budget, η := 0, noSleep := 0,
    recovery := 0, heal, latency, fgDelay := 1 }
structure Params.Admissible (P) : Prop :=
  1 ≤ catchUp,  0 ≤ θ ≤ ½,  ⅓ ≤ β,  0 ≤ cover ≤ ½,  β ≤ α ≤ 1,  1 ≤ budget
```

A contract cannot buy its claims with easier **thresholds**: `θ` and `cover`
(`cover` is read by no regime) must be at most their standard values (a smaller value is a weaker regime
premise, hence a stronger claim), and the healthy fault bound `β` at least
its standard `⅓` (the premise is `|faulty| < β·n`: a larger `β` admits more
faults). Accountability requires `β ≤ α ≤ 1` (a larger `α` convicts more,
hence is stronger; at the standard `β = ⅓`, `α ≥ ⅓`), so the healthy regime
bounds faults below `β ≤ α` (`HealthyOn.faultsBelow`) and final safety holds
there (`final_safe_healthy`).
`standard_admissible` shows that the standard numbers are admissible. The
other numbers are not bounded and carry part of the verdict: a larger
`catchUp` means fewer ready readers, a larger `lag` an earlier protected source
(`T ≤ b₀ − lag·ΔAC`, a stronger premise),
a larger `η` a stricter outage participation condition, a larger `noSleep` a
longer no-sleep window, a larger `recovery` a later protected reader, a small
`budget` a short outage, and larger heal points and latencies weaker claims. Any `η` is
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

In the model, `sysExternal` exports the PKI and the complete role selection, and
`External.selected` observes the protocol's public `participationRole` (`none`:
the whole population).
The protocol, its role query and selection specification depend only on public
delays and population size. A shape queries its `participationKind` in the slot
of the observation, retaining that historical selection at later fault charges.
`TimeGrid.slotOf` is floor division by the positive slot length, clamped to zero
for negative times. It reads the whole observation slot; `slotAt?` instead
recognizes exact boundaries after subtracting a duty's phase. Thus a duty whose
phase crosses a slot boundary need not execute in its own labelled slot.
The declared participation population may be a fixed non-universal committee.
Any correctness premise that reads it is relative to that declared population;
population-wide clauses remain separate. The instance supplier must prove that
the declared role (or shape kind) is the actual role of the votes counted by its
protocol. The public query alone does not prove this binding, and signature
mechanics do not belong in the problem definition.
No equality of execution validity or progress across awake profiles is required.

The slot is checked, within limits:

- `Adequate.covers` transports it to the covering run.
- `Realizable` requires it to hold on every witness, and, at some index
  chosen before `ΔAC` and `ΔFG`, on the stress witness with many honest
  validators asleep. A reader that
  never holds fails `CorrectProtocol` (`false_progress_not_correct`); a requirement of
  near-full participation at every index fails the stress witness.
- In L2, the shape obligations also ask every provided output to have an index whose
  requirement tolerates a bad (faulty or not ready) proposer slot in every
  window (`ProgressTolerant`, below). "An honest ready proposer in *every*
  slot" (`recur ⟨single, 1⟩`) is rejected (`recur_single_one_not_tolerant`).
  Beyond that, the reviewer reads the gap as a number.

In L2 the slot is `ProgressReq` (`ConsensusLean/Spec/Blocks/Progress.lean`):

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

`CorrectProtocol S X K` is **the** definition for the systems of the model,
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
awake honest node by `t − ΔAC`, ordered by submission time. It computes its
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

## Reading order: the trusted files

To know what `ShapeObligations F K` (or `CorrectProtocol`) means, read every file below, in this order.
The generated library root only collects imports.

<!-- spec-files -->

1. `ConsensusLean/Init.lean`: The curated imports every module elaborates under (`Mathlib.Init`, `Mathlib.Tactic.Common`); no declarations.
2. `ConsensusLean/Spec/Problem/Basic.lean`: L0 vocabulary: capabilities, output schemas, environments and points, traces, communication logs and systems.
3. `ConsensusLean/Spec/Problem/Network.lean`: Delivery and holding (`Held`, `TxHeld`), partial synchrony, synchrony up to a cut, outage networks and eager logs.
4. `ConsensusLean/Spec/Problem/Properties.lean`: Trace claims: agreement, monotonicity, ready-reader safety, nesting, transaction liveness, resilience and local accountability.
5. `ConsensusLean/Spec/Problem/Regimes.lean`: `Params`, `Contract`, admissible numbers, sleepy/healthy/outage regimes and the `cDur`, `heal`, `ready`, `lat` accessors.
6. `ConsensusLean/Spec/Problem/CorrectProtocol.lean`: External data and progress readers, the property table (`Behaviour`), system adequacy, active claims and witnesses, `Realizable`, and `CorrectProtocol`.
7. `ConsensusLean/Spec/Problem/Profile.lean`: Profiles (`ebbAndFlow`, `bft`, `available`) and `Profile.Matches`, the exact capability set of a schema.
8. `ConsensusLean/Spec/Model/Objects.lean`: Authenticated wire objects, carried-object closure, signers, items and decidable equality.
9. `ConsensusLean/Spec/Model/Protocol.lean`: Public parameters, closed selections, protocol interfaces, selection admissibility and families.
10. `ConsensusLean/Spec/Model/Run.lean`: Events and their order, runs, engine state, releases, inboxes, views, slashing protection and local reads.
11. `ConsensusLean/Spec/Model/Conditions.lean`: Signature unforgeability, valid selections, credentials, `ExecutionValid` and the engine communication log.
12. `ConsensusLean/Spec/Model/System.lean`: Evidence-based conviction, observed hash collisions, `sysOf`, and external PKI/selection data (`sysExternal`).
13. `ConsensusLean/Spec/Model/Served.lean`: Engine holding at a deadline (`Run.Served`), used by the `HeldIffServed` review statement.
14. `ConsensusLean/Spec/Blocks/TimeGrid.lean`: Slots, their lengths and times, with phases measured in multiples of ΔAC.
15. `ConsensusLean/Spec/Blocks/Progress.lean`: Patterns, recurrence windows, `ProgressReq`, `PatternRecurrence` and `NotReadyOn`.
16. `ConsensusLean/Spec/Blocks/Chains.lean`: Headers and chains, explicit roots and digests, structural prefixes, linkage and provenance.
17. `ConsensusLean/Spec/Blocks/Payload.lean`: Transaction encoding/decoding and `ledgerOf`: decoded inputs with first occurrences retained (`List.eraseDups`).
18. `ConsensusLean/Spec/Shape/Shape.lean`: Skeletons, closed signing roles and proposal provenance, duties, `ChainShape` and `ChainShapeFamily`.
19. `ConsensusLean/Spec/Shape/Compile.lean`: The compilation of skeleton duties and shape state machines to model protocols (`compiled`).
20. `ConsensusLean/Spec/Shape/Run.lean`: Compiled systems (`Sys`), chain traces, output validity, proposal liveness and `shapeProgress`.
21. `ConsensusLean/Spec/Shape/Claims.lean`: The chain-level safety, liveness, accountability and resilience claims (`ShapeClaims`).
22. `ConsensusLean/Spec/Shape/ProgressFit.lean`: `ProgressFits` and `ProgressTolerant`: one proposer per recurrence slot and bad-slot/participation tolerance.
23. `ConsensusLean/Spec/Shape/Active.lean`: Progress activity, `BadProposerEvery`, and `RealizableActive`, including its bad-proposer witness.
24. `ConsensusLean/Spec/Shape/Obligations.lean`: The obligations premise `ShapeObligations`: protocol claims, admissible numbers, service, progress fit and tolerance; its profile-labelled form `ShapeObligationsAs`.
25. `ConsensusLean/Spec/Shape/OnRuns.lean`: The obligations on a class of runs (`ShapeClaimsOnAt`, `ShapeObligationsOn`, `ShapeObligationsOnAs`): each claim restricted to the runs whose point satisfies a predicate, at constant faults the static adversary.
26. `ConsensusLean/Statements/Review.lean`: The five review statements as `Prop` definitions: `ObligationsSufficient`, `ObligationsSufficientOn`, `RegimesRealizable`, `LogFaithful`, `HeldIffServed`.

<!-- /spec-files -->

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

The adversary is all-knowing, and its set of compromised validators grows:
`EnvPoint.faultyAt t` (and `Run.faultyAt`) is monotone in `t`. A compromise is
immediate and permanent, and the adversary then holds the validator's ordinary
key. It signs anything with it, including objects that claim an earlier slot or
role, because the claimed slot is not the signing time. No forward-secure keys
and no corruption delay are modelled. A validator in `faultyAt t` is faulty for
every event stamped `t`, and a compromise changes no earlier event. From its
compromise on, a node has no engine events: what it does is adversarial
injection, which only `Unforgeable` (a signer honest at the delivery time had
released the object) and `Credentials` bind. An honest release keeps its
provenance, and a release or a submission stays owed by the network, after its
sender or recipient is compromised. A read made while honest stays protected
after its reader is compromised. The scheduler chooses the events, relay and
hash within the execution conditions. Since every lawful trace is quantified,
adaptive scheduling and corruption are covered. A probabilistic or
computational adversary is not modelled. A constant `faultyAt` is the static
adversary (`EnvPoint.ConstantFaults`).

Every participation budget is today's static count evaluated on the view
retained through the count's consumption horizon (`EnvPoint.retain`,
`EnvPoint.lookAhead`). Participation at `t` is charged with the faults of
`t + ahead·ΔAC`, and validators compromised by then do not count as support.
The outage cohort is charged at `outageEnd + cohortAhead·ΔAC`. The healthy
budget is the bound at the horizon, which by monotonicity is the bound at every
time. A recurrence's good proposer stays honest `hold·ΔAC` after its slot. A
larger window is a stronger premise. `ΔFG` enters no window.

**Certified scope.** The generic statements and the Goldilocks endpoint and
headline (`MeetsObligations`, `GoldilocksCorrect`) are certified for growing
faults.

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
- **Raw arrivals:** each delivery enters the protocol's total `process` handler
  and the communication log, regardless of dependency readiness or consensus
  admission. Buffering and retries belong to the protocol; `seen` is durable
  evidence, not a retry queue. Dependency checks still guard outgoing releases.
  The dependency-gated network escape (`not_psync_of_poisoned` in the earlier
  audit) is closed by construction: withholding a prerequisite does not exclude
  the dependent's raw arrival from valid runs or network service. Goldilocks
  processes carried parent chains in the same arrival and proves acceptance
  separately from receipt. Message and FG-attestation deadlines are unchanged.
  `Network.RawArrival.poisoned_arrival` tests a valid synchronous execution with
  an honest proposal's timely arrival and a prerequisite withheld from its recipient.
- **ΔAC, ΔFG known; unit ticks:** honest code knows `n`, `ΔAC` and `ΔFG`. Every awake honest
  node ticks at every integer time.
- **Order within one time:** restarts, then ticks, then deliveries. What
  arrives at a deadline is processed at the delivery (whose duties and gossip
  leave at that time) and read by a tick at the next tick. Restarts happen
  exactly at wakes.
- **Collision resistance** of the deployed hash on real items.

Per instance, the reviewer binds three things: the outputs are what users
read, `conflicts` is the slashing rule the chain enforces, and the numbers
are the intended ones.

## Scope

- **`stable := finalized` (Gasper-style) is not good.**
  Stable must be sleepy-live (`Behaviour.sleepyLive`). A schema that aliases
  stable to final is good only if its final output is live under sleepy
  participation (`stable_alias_final_sleepy_live`). Aliasing stable to
  available is allowed (Goldilocks).
- **Non-accountable BFT is out of scope**. Final accountability is
  mandatory, for fraction `α ≥ β` (standard ⅓), in every environment.
- **One GST and one outage per run: partially closed.** The prefix forms
  (`CorrectProtocol.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`) make the
  past safe before any later asynchrony. A run after an outage is a run with
  GST `b₁`. Runs with several GSTs or outages, judged as a whole, are out of
  scope.
- **Healthy means full participation.** Every
  honest validator is awake throughout from `max g 0`, with fewer than `β·n`
  faulty. A rotating ⅔ is not healthy (`healthy_rotating_sleeper`), nor is a
  fixed ⅔ with one honest sleeper (`healthy_needs_full_participation`).
  Liveness with honest validators asleep is asked by the sleepy regime and
  its stress witness.
- Growing compromise without delay, recovery or forward-secure keys; equal weights, two delay bounds (`ΔAC` for messages and
  transactions, `ΔFG` for FG attestations), no probabilistic protocols, no
  proof of work, no non-validator readers, no responsiveness claim.
- No transaction validity, fees, capacity or chain-quality bounds. Liveness
  is bounded-latency.
- No public schedules: one proposer `SelSpec` for every slot, chosen
  adversarially. Round-robin and RANDAO duties are worst-case `.sized 1`,
  with a recurrence requirement.
- No committee premise: only `.fixed` committees can support claims.
  Gasper's partitioned selection is deferred.
- Phases are multiples of `ΔAC`. For `pollSel := .fixed univ`, poll provenance
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
- Liveness premises must tolerate a bad proposer slot in every window:
  `ProgressTolerant` asks `span + 2 ≤ gap` at some
  index of every provided output, witnessed by `RealizableActive.badProposer`.
  Beyond that, the gap is read as a number. The check is in L2 (L0 has no
  proposers): an L0 `CorrectProtocol` system with abstract progress is not bound by it.

## Instances (`ConsensusLean/Instances/`)

### Goldilocks

The Goldilocks obligations endpoint is `Instances/Goldilocks/Statements/Obligations` (trusted surface,
protected snapshot), stated over the Spec it reaches (`Instances/Goldilocks/Spec/`, `AsChainShape.lean`). The
other milestone statements, and the Spec vocabulary only they use (traces, run premises, frame laws, the AC
requirements, the node's tick steps), are proved lemmas in the untrusted `Instances/Goldilocks/Milestones/`.
A reviewer goes from a claim to its proof in four steps: the node in
[`goldilocks-claims.tex`](../specs/goldilocks/tex/goldilocks-claims.tex), whose §"Lean status" names its Lean statement
and status; the statement; its row and modelling notes in
[`docs/goldilocks-mapping.md`](goldilocks-mapping.md), whose §"Review path" lists the statements
with their nodes; and the milestone proof `Proofs/<M>/Main.lean`, which `Solution.lean` (the endpoint) or
`ConsensusLeanTest/MilestoneAxioms.lean` (the other milestones) cites. The concrete
obligations endpoint (`Statements/Obligations`) is proved through the refinement; the other milestones
are proved directly over their own models (FG chains, AC states, the node and its runs). Milestone status: `docs/roadmap.md`.

## Shape examples (`ConsensusLean/Examples/Shape/`): Bft, Streamlet and Tendermint

These are demonstrations of `Shape`, not protocol instances, and are not on the trusted surface: no
Challenge statement reaches them.

`ConsensusLean/Examples/Shape/Bft.lean` supplies the common final-only schema `bftCore`, affine bounds
and `bftContract`: index `k : ℕ+`, standard thresholds, catch-up, heal point
`max g 0 + (catchUp + 1 + heal k)·ΔAC`, and latency `latency k` in ΔAC-coefficients.
Outage numbers are unused because there is no stable output.

`ConsensusLean/Examples/Shape/Streamlet.lean` gives `2·ΔAC` slots, one proposer per slot, polling disabled,
and all-validator votes at offset `ΔAC`. Progress is five consecutive honest ready proposers
in every window of `k` slots (`Pattern.range 5`); gap 6 supplies the tolerant index.

`ConsensusLean/Examples/Shape/Tendermint.lean` gives a poll shape, no slot proposals or committee kinds,
and all-validator polling at every unit tick. Height is in `pos`, round in `info`; round-robin
leadership is computed locally. A locked value is re-proposed by carrying its signed header.
Progress is the pointwise `notReadyAtMost m` placeholder described in Scope.
These are values and fit/tolerance proofs, with no concrete protocol proofs.
