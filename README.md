# The generic consensus contract: review guide

## What this is

This project defines a good consensus protocol (`Good`), a generic execution model, and a shape layer.
The review statement is `Consensus.Review.AcceptedGood`: accepted shapes give good protocols.
Its three secondaries are `RegimesRealizable`, `LogFaithful`, and `HeldIffServed`.
`scripts/check.sh` checks the trust boundary locally and in box CI: fast checks on observed main/non-draft PR heads, everything
(including kernel replay, `lake check` and the sandboxed comparator) nightly; see "Verification".
See `TRUST.md` for the assumptions and the roles of the checks. Milestones and their status: `docs/roadmap.md`;
design decisions: `docs/decisions.md`; how to contribute: `CONTRIBUTING.md` and `AGENTS.md`.

## The review statement

`ConsensusLean/Statements/Review.lean` states the claim and its three secondaries verbatim below
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
`ConsensusLean/Spec/Shape/Accepted.lean`:

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
`Solution.lean` proves each review statement by its source theorem, and the one instance statement
of `Challenge.lean`, the Goldilocks acceptance endpoint `Refinement.AcceptedEndpoint` (the closed
`Prop` definition of `milestone_statements_modules` in `scripts/boundaries.toml`), by its milestone
proof. Challenge certifies these five statements and nothing else (`docs/decisions.md`,
2026-11-04): the trusted surface is the generic definition of a correct protocol plus the one
instance endpoint. The other Goldilocks milestones are ordinary proved lemmas: their statements are
in the untrusted `Instances/Goldilocks/Milestones/` layers, `ConsensusLeanTest/MilestoneAxioms.lean`
states and pins each one, and check.sh step 3b gates their closure (`proved_milestone_modules`).
Which claims node each statement states, and where its mapping rows are: `docs/goldilocks-mapping.md`
§"Review path".
`ConsensusLeanTest/ReviewAxioms.lean`, using `ConsensusLeanTest/ReviewGuard.lean`, compiles
alpha-equality guards (including binder kinds) and `#guard_msgs` pins of the exact axiom lists
for both the review and source theorems. `ReviewGuard.checkComplete` requires every non-proof,
non-matcher constant declared in the statements module to have a review pair, including private
constants and declarations in other namespaces. The module must contain statements only.

In CI, `lake comparator --config comparator.json` compares `Challenge.lean`
(the Spec statements with placeholder proofs) with `Solution.lean`:
matching statements, permitted axioms, sandboxed kernel replay, and identical reachable constants
in both exports to resist build-time tampering. This checks the proofs against Spec built alone;
Spec drift is checked by the snapshot diff, committed and recorded with each change (#129).

`Accepted.good` combines three theorems. `refinement` gives `Behaviour`;
its bridges are `ledgerTrace` (reads are `ledgerOf` of the output chains)
and `proposalLive_txLive` (proposal liveness and partial synchrony give
transaction liveness; it needs catch-up `≥ Δ`, `Admissible.catchUp_pos`, so a
ready proposer was awake over the delivery interval before its release). `sysOf_adequate` gives `Adequate`.
`regimes_realizable` gives `RealizableActive`, hence `Realizable`
(`RealizableActive.toRealizable`; its stress witness keeps keys `1` and `2`
awake and the rest asleep; its L2-only `badProposer` witness puts a faulty
proposer slot in every progress window). Corollary
(`ConsensusLean/Main.lean`, `Accepted.activeService`): a final or
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

(`ConsensusLean/Spec/Problem/Good.lean`.) All three parts are L0 definitions. The
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
  validator. The witnesses exist at every `Δ` and every row bound `ΔF` (healthy: every
  `ΔF ≤ rowRatio·Δ`), at every GST `g ≥ 0` (healthy: with a
  log that is silent before the GST), and for outages armed arbitrarily late.
  Each witness has active claims (the sleepy and healthy witnesses bundle
  regime, progress and `TxLiveActive` as `SleepyLive` and `HealthyLive`):
  - `TxLiveActive`: a transaction to serve, read by a different honest node
    that was never submitted it;
  - `SafeActive`: two ready readers, one of them at two times;
  - `OutageActive`: a ready source, a real sleeper inside the window and a
    reader ready from the recovery point `b₁ + recovery·Δ`.

  A **stress witness** exercises liveness with many honest validators
  asleep, so a progress requirement cannot quietly demand near-full
  participation. For every provided available or stable output and every
  validator count, at *one* index (it may depend on the validators, not on
  `Δ` or `ΔF`):
  - `sleepyStress`: at every `Δ` and `ΔF`, a sleepy witness where at most
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
| stable | outage resilience | `Outage T b₀ b₁` | `ProtectedReadyFrom c stable target T (b₁ + recovery·Δ)` |

One field per row (`finalAccountable`, `healthyLive`, `sleepySafe`, `sleepyLive`,
`healedSafe`, `persists`). Derived in L0 (`Good.*`,
`ConsensusLean/Lemmas/Problem/Facts/Good.lean`; `Agree`, `Safe`, `FaultsBelow`,
`ReadySafeUpTo` are in `ConsensusLean/Lemmas/Problem/Derived.lean`):

| Theorem | Statement |
|---|---|
| `final_agree` | `FaultsBelow α` ⇒ `Agree final 0 ∨ HC`, in any network |
| `final_safe_healthy` | `Healthy g` ⇒ `Safe final 0 ∨ HC` (uses `β ≤ α`) |
| `persists_final_compatible` | through an outage, the stable read at `T` and the final read of a reader ready from `b₁ + recovery·Δ` are compatible |
| **prefix forms** `sleepySafe_prefix` | `SyncUntil b ∧ SleepyOn θ c 0 b` ⇒ `ReadySafeUpTo c g 0 b ∨ HC`: the past is safe whatever happens after `b` |
| `healedSafe_prefix` | partial synchrony with GST `g` for deadlines up to `b`, `HealthyOn β g b`, `prog[ready, heal]` and `heal ≤ b` ⇒ `ReadySafeUpTo c g heal b ∨ HC` |
| `outage_prefix` | the outage regime up to `b` ⇒ protection of ready readers at reading times in `[b₁ + recovery·Δ, b]` ∨ HC |

`TxLive c g start D` covers every submission: a transaction submitted to an
awake honest node by `t` is in the `g`-read of every ready reader at every
`t' ∈ [max t start + Δ + D, horizon]`. Safety has one body,
`AgreeAmong R`/`MonotoneAmong R` for a reader predicate `R` checked at each
cut: `Agree`/`Monotone` (and `Safe`) take honest readers; `ReadySafe` takes ready readers
only: honest, and awake throughout `[max 0 (t − c − 1), t]`. A node that
has been asleep for long may still hold an old fork. `ProtectedReadyFrom`
works as follows. Take a node **ready** at `T` and its `stable` read at `T`.
That read is a prefix of the `target` read (the available output if
provided, else the stable output) at every `t ∈ [b₁ + recovery·Δ, horizon]`,
for every node ready at `t`. The outage regime has no absolute participation
premise: besides η-sleepy participation, no honest validator falls asleep in
the no-sleep window `[b₀ − noSleep·Δ, b₁ + noSleep·Δ]` (clamped to
`[0, horizon]`; waking is allowed), and the faulty validators with the late
wakers of that window are fewer than the honest validators awake at its start.

An outage run is partially synchronous with GST `b₁` (`OutageNet b₀ b₁`
contains `PSync b₁`), so the after-GST rows apply with `g = b₁` when their
other premises hold.

### The network rule (`ConsensusLean/Spec/Problem/Network.lean`)

The delivery rule is Francesco's rule, normal delivery (`CommLog.Delivers.msgs`):

> every message an honest node sends at `t` is received, strictly before the
> delivery bound, by every honest node that is awake over the delivery
> interval, and is re-served, strictly before the bound, to nodes that wake
> later.

The delivery interval is half-open, `[t, max(t, GST) + Δ)`, as in the paper's
`Sync`; on integer time "strictly before `d`" is "by `d − 1`". Formally, for a
deadline function `dl` (`max a GST + Δ − 1` in partial synchrony): for every
start `a ≥ t`, every honest node awake throughout `[a, dl a]` holds the message
at `dl a`. At `a = t`: a node awake over `[t, max(t, GST) + Δ − 1]` has it by
`max(t, GST) + Δ − 1`, so its tick at `max(t, GST) + Δ` (which runs before the
deliveries of that time) reads it. At a later `a`: a node that wakes at `a` and
stays awake has it by `max(a, GST) + Δ − 1`, not at the wake itself (no instant
re-delivery; tests `waker_within_bound`, `waker_not_instant`). At `Δ = 1` this
is same-time delivery; realizability starts at `Δ = ΔF = 2` (`Realizable`), and
every behaviour claim holds at every `Δ ≥ 1`.

**Two bounds.** The environment has a message bound `Δ` and a row bound `ΔF`
(`Env.Δ`, `Env.ΔF`, both positive; neither bounds the other). The log carries
the protocol's message class (`CommLog.row`): for model runs it is filled only
from `Protocol.isRow` (`Run.log`, `tagLog`, `sysOf_log_row`), so no theorem or
regime about the model can choose another one (an abstract L0 `System` fixes
its own). Rows are served by `Delivers.rows` with their own deadline function
`dlF` (`max a GST + ΔF − 1` in partial synchrony); every other message by
`Delivers.msgs` with `dl`, and a row is never served by `msgs`. When `ΔF < Δ`,
rows may overtake blocks; no statement claims a block or a vote strictly before `ΔF`.
For Goldilocks the rows are the standalone attestations and the relay wrappers
of attestations only; a mixed relay wrapper is delivered strictly before `Δ` (owner
decision 2026-11-02). Every other protocol has no rows (`isRow` defaults to
`False`), which is the single-bound model (tests `two_bound_witnesses`,
`row_held_to_row_bound`, `nonrow_held_to_message_bound`).

- "Has it at `d`" is `Held`. The node sent or received the message
  at some `t' ≤ d`, and did not wake in `(t', d]`. Receipt at the deadline
  itself counts. A restart loses earlier receipts.
- **Transactions** (`Delivers.txs`), the same rule at `dl` (bound `Δ`): a transaction submitted at
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

Instances: `PSync g` (deadline `max a g + Δ − 1`, rows `max a g + ΔF − 1`),
`SyncUntil b` (deadline `a + Δ − 1`, rows `a + ΔF − 1`, for deadlines up to `b`), and
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

### The regimes, as formulas (`ConsensusLean/Spec/Problem/Regimes.lean`)

Here `p` is the environment point (awake profile, honest set, horizon,
submissions), `L` is the run's log, `n = |V|`, `ready_t = readyAt c t` and
`faulty` is the complement of the honest set.

| Regime | Definition |
|---|---|
| `System.Sleepy` | `L.PSync p 0 ∧ ∀ t ∈ [0, horizon], θ·(\|ready_t\| + \|faulty\|) < \|ready_t\|` |
| `System.Healthy g` | `L.PSync p g ∧ \|faulty\| < β·n ∧ ∀ v ∈ honest, v awake throughout [max g 0, horizon] ∧ ΔF ≤ rowRatio·Δ` (full participation; awake, not ready; the row ratio is an upper envelope, not a deadline) |
| `System.Outage T b₀ b₁` | `OutageTimes ∧ L.OutageNet p b₀ b₁ ∧ EtaSleepyOn θ (η·Δ) c 0 horizon ∧ NoSleepOn a z ∧ CohortOn a z` (`a`, `z`: `outageStart`, `outageEnd`) |
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
  θ β cover α : ℚ -- sleepy, healthy fault bound, cover (read by no regime), accountable fraction
  lag budget η : Nat                         -- outage arming lag, budget, look-back (Δ-coefficients)
  noSleep recovery : Nat                     -- outage no-sleep margin C, recovery delay D (Δ-coefficients)
  heal latency : Capability → Idx → Nat      -- heal point after max g 0; transaction latency
  rowRatio : ℕ+                              -- healthy regime: ΔF ≤ rowRatio·Δ (larger = weaker premise)
def Params.standard (catchUp lag budget heal latency) :=
  { catchUp, θ := ½, β := ⅓, cover := ½, α := ⅓, lag, budget, η := 0, noSleep := 0,
    recovery := 0, heal, latency, rowRatio := 1 }
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
(`T ≤ b₀ − lag·Δ`, a stronger premise),
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

The slot is checked, within limits:

- `Adequate.covers` transports it to the covering run.
- `Realizable` requires it to hold on every witness, and, at some index
  chosen before `Δ` and `ΔF`, on the stress witness with many honest
  validators asleep. A reader that
  never holds fails `Good` (`false_progress_not_good`); a requirement of
  near-full participation at every index fails the stress witness.
- In L2, acceptance also asks every provided output to have an index whose
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
The generated library root only collects imports.

<!-- spec-files -->

1. `ConsensusLean/Init.lean`: The curated imports every module elaborates under (`Mathlib.Init`, `Mathlib.Tactic.Common`); no declarations.
2. `ConsensusLean/Spec/Problem/Basic.lean`: L0 vocabulary: capabilities, output schemas, environments and points, traces, communication logs and systems.
3. `ConsensusLean/Spec/Problem/Network.lean`: Delivery and holding (`Held`, `TxHeld`), partial synchrony, synchrony up to a cut, outage networks and eager logs.
4. `ConsensusLean/Spec/Problem/Properties.lean`: Trace claims: agreement, monotonicity, ready-reader safety, nesting, transaction liveness, resilience and local accountability.
5. `ConsensusLean/Spec/Problem/Regimes.lean`: `Params`, `Contract`, admissible numbers, sleepy/healthy/outage regimes and the `cDur`, `heal`, `ready`, `lat` accessors.
6. `ConsensusLean/Spec/Problem/Good.lean`: External data and progress readers, the property table (`Behaviour`), system adequacy, active claims and witnesses, `Realizable`, and `Good`.
7. `ConsensusLean/Spec/Model/Objects.lean`: Authenticated wire objects, carried-object closure, signers, items and decidable equality.
8. `ConsensusLean/Spec/Model/Protocol.lean`: Public parameters, closed selections, protocol interfaces, selection admissibility and families.
9. `ConsensusLean/Spec/Model/Run.lean`: Events and their order, runs, engine state, releases, inboxes, views, slashing protection and local reads.
10. `ConsensusLean/Spec/Model/Conditions.lean`: Signature unforgeability, valid selections, credentials, `ExecutionValid` and the engine communication log.
11. `ConsensusLean/Spec/Model/System.lean`: Evidence-based conviction, observed hash collisions, `sysOf`, and external PKI/selection data (`sysExternal`).
12. `ConsensusLean/Spec/Model/Served.lean`: Engine holding at a deadline (`Run.Served`), used by the `HeldIffServed` review statement.
13. `ConsensusLean/Spec/Blocks/TimeGrid.lean`: Slots, their lengths and times, with phases measured in multiples of Δ.
14. `ConsensusLean/Spec/Blocks/Progress.lean`: Patterns, recurrence windows, `ProgressReq`, `PatternRecurrence` and `NotReadyOn`.
15. `ConsensusLean/Spec/Blocks/Chains.lean`: Headers and chains, explicit roots and digests, structural prefixes, linkage and provenance.
16. `ConsensusLean/Spec/Blocks/Payload.lean`: Transaction encoding/decoding and `ledgerOf`: decoded inputs with first occurrences retained (`List.eraseDups`).
17. `ConsensusLean/Spec/Shape/Shape.lean`: Skeletons, closed signing roles and proposal provenance, duties, `ChainShape` and `ShapeFamily`.
18. `ConsensusLean/Spec/Shape/Compile.lean`: The compilation of skeleton duties and shape state machines to model protocols (`compiled`).
19. `ConsensusLean/Spec/Shape/Run.lean`: Compiled systems (`Sys`), chain traces, output validity, proposal liveness and `shapeProgress`.
20. `ConsensusLean/Spec/Shape/Claims.lean`: The chain-level safety, liveness, accountability and resilience claims (`ShapeClaims`).
21. `ConsensusLean/Spec/Shape/ProgressFit.lean`: `ProgressFits` and `ProgressTolerant`: one proposer per recurrence slot and bad-slot/participation tolerance.
22. `ConsensusLean/Spec/Shape/Active.lean`: Progress activity, `BadProposerEvery`, and `RealizableActive`, including its bad-proposer witness.
23. `ConsensusLean/Spec/Shape/Accepted.lean`: The acceptance premise `Accepted`: protocol claims, admissible numbers, service, progress fit and tolerance.
24. `ConsensusLean/Statements/Review.lean`: The four review statements as `Prop` definitions: `AcceptedGood`, `RegimesRealizable`, `LogFaithful`, `HeldIffServed`.

<!-- /spec-files -->

Everything else is checked by Lean; `scripts/check.sh` checks the boundary:

0. **Pins:** exact toolchain, manifest, clean dependency checkouts and Lake's resolved search path match `scripts/pins.toml`.
1. **Build:** compile `ConsensusLean` (the default target), `ConsensusLeanTest` (what `lake test` builds), `Solution`, the challenge, check-decls and axiom-audit with `lake build --wfail --iofail` (any warning or info message fails, also one Lake replays from a built module; `warn.sorry = false` in the lakefile keeps `sorry` silent), and the deliberately bad fixtures without; `--no-build` still checks Lake freshness.
2. **Boundaries:** enforce the layer matrix, the Init chain, root coverage, library inventory and pinned-base names with `scripts/check-boundaries.py` (source-level, no build).
3. **Declarations:** EthLib check-decls runs once per library scope (`ConsensusLean`, `ConsensusLeanTest`, `Solution`), checking every module for extra axioms, unfinished proofs, opaque/unsafe/partial declarations, extern/implemented_by/csimp and opaque reachability; empty scopes fail. A `sorry` is allowed (and listed) only in the `sorry = true` layers of `scripts/boundaries.toml`, `Lemmas` and `Proofs.<M>` (foundation plan §5); anywhere else it fails.
3b. **Axiom audit:** leanprover-community/axiom-audit over the import closure of `Solution` and of the `proved_milestone_modules` (the proved milestones that are not Challenge statements) (the part proved in Solution; "certified" means a passed full tier, `docs/roadmap.md`): every declaration of `ConsensusLean` and `Solution` in it uses only `propext`, `Classical.choice` and `Quot.sound`, so a `sorry` (also through an import), `native_decide` or a declared axiom there fails. The same gate covers every declaration of `ConsensusLeanTest`: a test, witness or rejection built on an unfinished lemma proves nothing (step 7 refuses proof `example`s, which never enter the environment, so every test is a named declaration). `Solution` imports `Main` and every milestone, so all of them must be finished today; a new milestone may stay unfinished while neither `Main` nor `Solution` imports it (plan §5); the instances reach the generic library only through `Main`, and a finished instance milestone enters `Solution` through its `Proofs/<M>/Main` (the imports of `Solution.lean`). A report lists the unfinished declarations of `ConsensusLean` (those that depend on `sorryAx`): the progress metric.
4. **Spec surface:** check persisted extensions, diff the complete readable/structural snapshot (including pins/options), enforce theorem hygiene and constant-free parents; the `reach` report (which Spec definitions the review statements reach; not a gate) runs in `--full`, in `--changed` when step 4 runs, and in `--fast` with `--reach`. The protected-surface snapshot diffs the same snapshot of every default-library module that `trusted_paths` covers outside the trusted layers (the instance `Spec`, `Statements` and `Refinement/Defs.lean`) against `scripts/instance-spec-snapshot.txt`; like the Spec snapshot it fails until regenerated with `--update-snapshot` and committed. The extension and theorem policies apply to the trusted layers only (TRUST.md).
5. **Kernel replay:** run leanchecker on every leaf module of the checked libraries, one module per process after checking it has no descendants, two processes at a time (`REPLAY_JOBS`); parent modules own no constants.
6. **Review pins:** require the tests root to import the compiled alpha-equality guards and exact axiom pins.
7. **Backstop:** grep for `sorry`/`admit` outside the sorry layers (comments included; their count inside them, comments and strings removed and only as a term or tactic, is reported), proof `example`s (only a bare `example := @Name` or ``` example := ``Name ``` reference is allowed), native proofs, kernel bypasses and `debug.` options, Spec metacommands and unsafe lakefile options.
8. **Vendored:** verify all vendored EthLib copies against `scripts/vendor.sha256`.
9. **Comparator config:** pin challenge/solution modules, every statement name (the four review statements and the closed statements of the `milestone_statements_modules`, today the acceptance endpoint, each of which must have one) and exactly the three standard axioms; validate the Spec-only challenge.
10. **Lake check (needs bubblewrap; skipped and listed as CI-only where `bwrap` is missing):** sandboxed build, export and kernel replay of the default targets, rejecting extra axioms. It rejects `sorryAx` too, so it checks the default targets only while the files of the sorry layers hold no `sorry`/`admit` term or tactic outside comments and strings (an `admit`-named field, binder or projection is not one; plan §5; otherwise a NOTE and, in CI, a warning); then the checks of the part proved in Solution, the `Solution` closure, are 3b, 5 and 11. Its fixtures always run.
11. **Lake comparator (needs bubblewrap, likewise):** statement/axiom matching, sandboxed replay and agreement of reachable constants between challenge and solution exports.
12. **Docs:** require the marked list above to equal every file of the trusted layers exactly, and every `Consensus.…` name cited in `docs/roadmap.md` and `docs/goldilocks-mapping.md` to be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists.
13. **Metrics (report):** depth, downstream cones, `@[expose]` and import counts (`scripts/metrics-baseline.py`, about 2 s, no build).
14. **Rebuild canary (report; `--full`, or `--canary`, which CI passes when the build configuration changed):** a fixed proof-only edit of one module (`canary_*` in `scripts/boundaries.toml`) must leave its `.olean.hash` unchanged and every default target up to date; a regression is reported (a CI warning). Its control, a statement edit, must make the default targets stale, else the step fails.

Checks with fixtures exercise the same code paths on positive and negative controls.
Spec drift is guarded by the snapshot diffs (the Spec and the protected surface), committed and recorded with each change (#129);
dependency drift by pins; proof validity by replay, check-decls and the CI comparator.

Proof support outside that surface: `ConsensusLean/Lemmas/Problem/Derived.lean` defines
`Agree`, `Safe`, `ReadySafeUpTo` and `FaultsBelow` with their characterising lemmas (not on the trusted surface: the
Goldilocks sheet that read them is archived), and `ConsensusLean/Lemmas/Problem/DerivedFacts.lean` defines `SendsFromZero` and
`Trace.map` with theirs (not protected); `Good` reads none of them. `ConsensusLean/Lemmas/Problem/Facts/` holds the derived `Good.*`
lemmas, including `Good.served`; `ConsensusLean/Lemmas/Blocks/Facts.lean` holds the block lemmas.
`ConsensusLean/Lemmas/Shape/Payload.lean` proves the payload bridges;
`ConsensusLean/Proofs/Behaviour/Main.lean`, `ConsensusLean/Proofs/RegimesRealizable/Main.lean`,
and `ConsensusLean/Main.lean` prove
refinement, coverage/witnesses, acceptance and `Accepted.activeService`.
`ConsensusLean/Lemmas/Model/` and `ConsensusLean/Proofs/Faithful/Main.lean` prove
`sysOf_adequate`, `sysOf_log_faithful`,
`Run.held_iff_served`, `sysOf_nonFraming` and `sysOf_laws`, with support for canonical runs
(`canonical_run_from`), truncation (`Run.truncate_*`), views (`Run.mem_viewIdx_iff`)
and slashing protection (`honestNeverSlashed`). A node's `Run.ViewIdx` is the closure
of its engine `seen` log; the view lemma gives the event-index form.
Injective-hash lifting is checked in `ConsensusLeanTest/Lift.lean`.

## Layout

Lean module names are global. The main library is `ConsensusLean`; its layers are module
prefixes under `ConsensusLean/`. Namespaces and declarations stay unchanged.
The only default target is `ConsensusLean` (`defaultTargets = ["ConsensusLean"]`).
`ConsensusLeanTest` is the test library, selected by the lakefile's `testDriver` and built by
`lake test`; it is not a default target.
`Solution` and `Challenge` are single-module libraries for the comparator.
`archive/goldilocks/` is a read-only snapshot of the old Goldilocks Lean model and spec, outside every Lake target and check ([`ARCHIVE.md`](archive/goldilocks/ARCHIVE.md)).
`specs/goldilocks/tex/` is the live LaTeX spec of Goldilocks, edited here; it is outside every Lake target and check and not trusted surface: fidelity is carried by the Lean statements and `docs/goldilocks-mapping.md` ([`README.md`](specs/goldilocks/tex/README.md)).

| Layer under `ConsensusLean/` | Contents |
|---|---|
| `Init.lean` | Curated public imports: `Mathlib.Init` and `Mathlib.Tactic.Common`. |
| `Core/`, `ToMathlib/` | Trusted support; both empty for now. |
| `Spec/{Problem,Model,Blocks,Shape}/` | Trusted definitions. |
| `Statements/Review.lean` | The four review statements. |
| `Lemmas/{Problem,Model,Blocks,Shape}/` | Derived definitions, lemmas, canonical runs and witnesses. |
| `Proofs/<M>/Main.lean` | Milestones: `Behaviour`, `RegimesRealizable`, `Faithful`. |
| `Main.lean` | `Accepted.good` and `Accepted.activeService`. |
| `Instances/<P>/{Spec,Statements}/` | Goldilocks (`Spec/`: what the endpoint statement reaches; `Statements/Refinement/Accepted`: the endpoint). |
| `Instances/<P>/Milestones/` | Goldilocks milestone vocabulary and statements, not on the trusted surface (`docs/decisions.md`, 2026-11-04). |
| `Examples/Shape/` | Shape examples, not on the trusted surface: Bft, Streamlet, Tendermint as contract values. |

`Init.lean` is imported last by `Spec/Problem/Basic.lean` and `Spec/Model/Objects.lean`,
so every module reaches it. It is part of the trusted surface.
`scripts/boundaries.toml` is the one configuration of the import rules (foundation plan §2), checked
at source level by `scripts/check-boundaries.py` (module headers parsed by `lean --deps-json`; no build,
so no stale build output hides a violation). Every module is in exactly one `[[layer]]` (prefixes never
overlap); `allow` lists the layers it may import, written out in full:

| Layer | May also import |
|---|---|
| `Init`, `ToMathlib` (trusted) | Mathlib only |
| `Core` (trusted) | Init, ToMathlib |
| `Spec` (trusted) | the above, Core |
| `Statements` (trusted) | the above, Spec |
| `Lemmas` | the above, Statements |
| `Proofs.<M>` (one layer per milestone directory) | the above, Lemmas |
| `Main` | the above, every `Proofs.<M>` |
| `Examples` (Shape examples, untrusted) | Init, ToMathlib, Core, Spec |
| `Instances.Goldilocks.*` (one layer per component and level: `Spec.{Common,FG,Frame,Trace,FGStore,AC,SA,Node,Run}`, `Refinement.Defs`, `Statements.*`, `Lemmas.*`, `Proofs.<M>`, `Main`) | its row in `scripts/boundaries.toml`: no FG layer imports an AC or SA layer and no AC or SA layer an FG layer; `Statements.FG` reaches only the chain-level FG |
| `Instances.Goldilocks.Lemmas.Refinement` | its row above, including `Lemmas.Healing` for finite regime consumers and healing/final adapters; Healing cannot import Refinement |
| `Solution` | every generic layer and the closure of each finished instance milestone (today `Instances.Goldilocks.Proofs.FGSafety`, `Instances.Goldilocks.Proofs.ACBase`, `Instances.Goldilocks.Proofs.ACSteps`, `Instances.Goldilocks.Proofs.FGStore`, `Instances.Goldilocks.Proofs.ComposeAnyAC`, `Instances.Goldilocks.Proofs.Persist`, `Instances.Goldilocks.Proofs.Regimes`, `Instances.Goldilocks.Proofs.Service`, `Instances.Goldilocks.Proofs.Refinement` and `Instances.Goldilocks.Proofs.Healing`, with `Instances.Goldilocks.Lemmas.Healing`) |
| `Test` (`ConsensusLeanTest`) | everything above; library roots, import-only aggregates, `import all` |

The checker fails on: a missing, unparsable or mistyped config (missing or unknown keys included); a
module in no layer; a `Proofs/<M>/` directory without its own layer, or a milestone imported other than
through `Proofs.<M>.Main` (exception or not); an import outside `allow`, directly or through another
module's exception (printed with its path); allow lists that are cyclic, not downward-closed, or let a
trusted layer import an untrusted one; `import Mathlib`; an import of a library root or an import-only
aggregate, or `import all`, outside the tests; a module that does not reach `ConsensusLean.Init` through
public imports (except `ToMathlib` and the meta tool `ReviewGuard`); a fixture module or an unknown
top-level name; the attribute `expose` (a whole-file `@[expose]` section, on a declaration, or `attribute
[expose]`; comments and strings ignored) in a layer without `expose = true`, which only Core, Spec, Statements,
the instance Spec, Statements and `Refinement.Defs` layers, the Examples layer, the solution and the tests have (plan §3: Lemmas, Proofs, Main and ToMathlib export no
bodies; the solution and the tests are leaves, so their exposure costs no rebuild), or `expose = true` on a
Lemmas, Proofs, ToMathlib or Main layer. Lean also exports the bodies of `abbrev`s and of instances of non-`Prop`
classes without the attribute; the checker does not flag those (today `Trace.Agree` and `kv`). Its self-test (`scripts/fixtures/boundaries/cases.toml`, one case per
failure kind) runs in check.sh step 2. Today's deviations from the plan's matrix are reviewed
`[[exception]]` entries, each with its reason; today one: Goldilocks `Lemmas.Healing.ResetInv`,
`Lemmas.Healing.Recovery.Reports` and `Proofs.Healing.Main` import `Lemmas.Refinement.HealthyEffective`. An exception lets the modules under its `from` depend on the modules
under its `to` (and so on what those reach), never the importers of the `from` modules; none starts in a
trusted layer, and every `from` and `to` entry must be used.

The trusted layers' closure holds only trusted modules and the pinned base set: it cannot reach proofs,
instances, the solution, tests or fixtures (`CheckFixtures`, `CheckDeclsTest`, `Challenge`).
Every file of `ConsensusLean` and `ConsensusLeanTest` is imported by its library root. The generated
roots `ConsensusLean.lean` and `ConsensusLeanTest.lean` import every module of their library;
`check-boundaries.py` fails on an unlisted file. Regenerate them with
`lake exe mk_all --lib ConsensusLean --module` and
`lake exe mk_all --lib ConsensusLeanTest --module`.
The generated roots and other modules with descendants own no constants.
The external base set is `Init`, `Std`, `Lean`, `Lake`, `Mathlib`, `Batteries`, `Aesop`, `Qq`,
`ProofWidgets`, `Plausible`, `ImportGraph`, `LeanSearchClient`; unknown names fail.
Pins establish the provenance of those names.
The inventory configuration is cross-checked against `lakefile.toml`, including default targets
and globs. A `Proofs` component is allowed only under `ConsensusLean.Proofs` and
`ConsensusLean.Instances.Goldilocks.Proofs` (`[checks].proofs_component_prefixes`): check-decls
exempts definitions there from reaches-opaque, which is sound because no trusted layer can
reach them. `Exports` components are refused.

In `scripts/`:

- `check.sh`: the single driver, fixture self-tests and pass/fail/skip summary.
- `check-boundaries.py`, `boundaries.toml`: the layer matrix, its exceptions and the library inventory.
- `check-pins.py`, `pins.toml`: toolchain, dependency revisions, clean checkouts and resolution checks.
- `SpecSurface.lean`, `spec-extensions.txt`, `spec-theorems.txt`, `spec-snapshot.txt`, `instance-spec-snapshot.txt`: persisted-extension policy, theorem hygiene and the reviewed Spec and protected-surface snapshots.
- `CheckDecls.lean`, `check_decls_baseline.txt`: EthLib declaration checker (three local patches, see TRUST.md) and reviewed exceptions.
- `AxiomAudit.lean`, `AxiomAuditMain.lean`, `LICENSE.axiom-audit`: leanprover-community/axiom-audit v0.1.2 (verbatim; step 3b).
- `test_check_decls.sh`, `CheckDeclsTest.lean`, `CheckDeclsTest/`, `CheckDeclsForeign.lean`: verbatim EthLib fixture suite.
- `LICENSE.EthLib`, `vendor.sha256`: CC0 licence and hashes of every vendored copy.
- `fixtures/`: build (`--wfail`), boundary, `sorry` placement, axiom-audit, Spec-surface, review-pin, grep, pins, docs, comparator and Lake-check controls.
- `metrics-baseline.py`: report-only module metrics per layer of `boundaries.toml`
  (`docs/metrics-baseline.md`); step 13 prints its totals.

The fixture libraries are `Challenge` (`Challenge.lean`, comparator statements
with placeholder proofs, importing exactly `ConsensusLean.Statements.Review` and the
`milestone_statements_modules`), rootless
`CheckFixtures` (under `scripts/fixtures/`, each fixture a separate target), and `CheckDeclsTest`
(EthLib fixtures under `scripts/`).
They may contain deliberately unfinished proofs or extra axioms; no checked library reaches them.
`comparator.json` connects the challenge to `Solution.lean`.

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
- **Δ known; unit ticks:** honest code knows `n`, `Δ` and `ΔF`. Every awake honest
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
- Static adversary, equal weights, two delay bounds (`Δ` for messages and
  transactions, `ΔF` for rows), no probabilistic protocols, no
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

## Instances (`ConsensusLean/Instances/`)

### Goldilocks

The Goldilocks acceptance endpoint is `Instances/Goldilocks/Statements/Refinement/Accepted` (trusted surface,
protected snapshot), stated over the Spec it reaches (`Instances/Goldilocks/Spec/`, `Refinement/Defs.lean`). The
other milestone statements, and the Spec vocabulary only they use (traces, run premises, frame laws, the AC
requirements, the node's tick steps), are proved lemmas in the untrusted `Instances/Goldilocks/Milestones/`
(`docs/decisions.md`, 2026-11-04). A reviewer goes from a claim to its proof in four steps: the node in
[`goldilocks-claims.tex`](specs/goldilocks/tex/goldilocks-claims.tex), whose §"Lean status" names its Lean statement
and status; the statement; its row and modelling notes in
[`docs/goldilocks-mapping.md`](docs/goldilocks-mapping.md), whose §"Review path" lists the statements
with their nodes; and the milestone proof `Proofs/<M>/Main.lean`, which `Solution.lean` (the endpoint) or
`ConsensusLeanTest/MilestoneAxioms.lean` (the other milestones) cites. The concrete
acceptance endpoint (`Statements/Refinement/Accepted`) is proved through the refinement; the other milestones
are proved directly over their own models (FG chains, AC states, the node and its runs). Milestone status: `docs/roadmap.md`.

## Shape examples (`ConsensusLean/Examples/Shape/`): Bft, Streamlet and Tendermint

These are demonstrations of `Shape`, not protocol instances, and are not on the trusted surface: no
Challenge statement reaches them (`docs/decisions.md`, 2026-11-04).

`ConsensusLean/Examples/Shape/Bft.lean` supplies the common final-only schema `bftCore`, affine bounds
and `bftContract`: index `k : ℕ+`, standard thresholds, catch-up, heal point
`max g 0 + (catchUp + 1 + heal k)·Δ`, and latency `latency k` in Δ-coefficients.
Outage numbers are unused because there is no stable output.

`ConsensusLean/Examples/Shape/Streamlet.lean` gives `2·Δ` slots, one proposer per slot, polling disabled,
and all-validator votes at offset `Δ`. Progress is five consecutive honest ready proposers
in every window of `k` slots (`Pattern.range 5`); gap 6 supplies the tolerant index.

`ConsensusLean/Examples/Shape/Tendermint.lean` gives a poll shape, no slot proposals or committee kinds,
and all-validator polling at every unit tick. Height is in `pos`, round in `info`; round-robin
leadership is computed locally. A locked value is re-proposed by carrying its signed header.
Progress is the pointwise `notReadyAtMost m` placeholder described in Scope.
These are values and fit/tolerance proofs, with no concrete protocol proofs.

## Tests (`ConsensusLeanTest/`)

`lake test` builds this library, including the review pins and citation index.

- `Problem`: every L0 property has teeth; local accountability (`local_accountability_teeth`).
- `Network`: the delivery rule (wakers served strictly before the bound, not instantly), faithfulness, silent runs and truncation.
- `Regimes`: what each regime admits and rejects; the explanatory L0 regime lemmas.
- `Good`: vacuous systems are not good; censoring progress, rotating sleepers, η-sleepy history.
- `Model`, `Blocks`, `Shape`: model mechanics, recurrence, compiled roles and poll mode.
- `Leaks`: do-nothing, fabricating and self-silencing protocols fail `ShapeClaims`; `recorder_live_testK` passes.
- `Realizable`: coverage, `allProposers_no_witness`, late-GST and late-outage witnesses.
- `Controls`: positive controls at explicit numbers.
- `Vacuity`: admissibility rejections, progress fit and tolerance, forgery, `noService_not_accepted`.
- `Lift`, `Support`, `Common`: injective-hash lifting and fixtures; the former `Values` live in `ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}.lean`.
- `ReviewAxioms`, `ReviewGuard`: statement alpha-equality, completeness and axiom pins.
- `Gaps`: the gap dispositions. `Index`: every cited name, checked to exist.

### Gap dispositions

One line per gap (M1–M39 and the vacuous system), with `example`s for the
by-construction rows: `ConsensusLeanTest/Gaps.lean`.

## Verification

**CI of record is the box watcher on `ethlabs-box`; results are on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63).** GitHub Actions `check`, `full` and `notify`
are disabled by owner decision (2026-10-31, #50): billing prevents jobs from starting. Their YAML files remain
as reference; disabling them changes no check. Do not create GitHub CI subscriptions, dispatch workflows,
or report the known billing failures. A green CI result means a passing box row for the relevant commit,
not a GitHub badge. Polling can skip intermediate heads; ask the box watcher owner to queue an exact SHA
if its row is missing. The watcher comments failures on #17 (main/full) or the PR.

`scripts/check.sh` has three modes; every step it does not run prints `SKIP  <step> (<reason>)`:

| Mode | Runs | Where |
|---|---|---|
| `--fast` (default) | steps 0–4, 6–9, 12, 13: pins, build (`--wfail`), imports, check-decls, axiom audit, Spec surface + snapshot diff, review pins, grep, vendored hashes, comparator config, docs, metrics; self-tests only with `--selftests`, step 4's `reach` report only with `--reach`, the rebuild canary (14) only with `--canary` | Box watcher on observed main and non-draft PR heads (PR merged into main first), with `--selftests` when `scripts/` or the build configuration changed, `--reach` when the trusted surface or `scripts/` changed, `--canary` when the build configuration changed; review-boundary and its self-test also run; all of it in the sandbox `scripts/ci-sandbox.sh` (no network or credentials) |
| `--full` | everything: the fast steps, every self-test, leanchecker replay (5), `lake check` (10), `lake comparator --paranoid` (11), the rebuild canary (14) | Box nightly at 03:17 UTC, on demand and on `milestone*`/`release*` tags; clean project build, unsplit, with no skipped steps |
| `--changed [<base>]` | the fast steps restricted to what changed since `<base>` (default: merge-base with `origin/main`, uncommitted and untracked files included): build of the changed modules' downstream cone, check-decls on the affected libraries, the axiom audit's gates only if the closure of `Solution` (or a test module) changed and its report only if `ConsensusLean` did, Spec surface and comparator config only if a Spec module (or the challenge, `comparator.json`, the solution's imports) changed (otherwise only noconst of step 4), grep on the changed files; pins, imports, review pins, vendored hashes, docs and metrics in full (cheap). A change of `scripts/` or of the build configuration falls back to `--fast` (with self-tests for `scripts/`); with `--selftests` it runs `--fast --selftests` | locally, `scripts/check-changed.sh [<base>]` |

Only an unsplit `--full` ends with `check.sh: ALL CHECKS PASSED`; a `--split` part ends with `check.sh: PART PASSED (split <part>; ...)`, the other modes with `check.sh: PASSED (<mode> mode; ...)`.

### Local workflow

On the shared box agent builds and checks use the opt-in FIFO wrapper from their worktree:
`scripts/agent-job.py <name> -- <command...>`. It preserves cwd and arguments, admits at most two
agent jobs per user, delegates to `job --mem 16G --cpus 8 consensus-lean`, and waits for completion.
Landings and CI continue to use `job` directly, outside the agent queue.

1. Iterate on one file with `lake env lean <file>` (after building its imports), or on one declaration with
   `turbo-lean check <file> --decl <name>` (a single declaration only; `lake build` stays the gate).
   `lake build` builds `ConsensusLean` by default; `lake test` builds `ConsensusLeanTest`.
2. Before committing, check what changed:
   ```sh
   scripts/agent-job.py <name> -- bash -lc 'LAKE_RESTORE_ARTIFACTS=true scripts/check-changed.sh'
   ```
3. Commit, rebase on `origin/main` and land with `scripts/push-main.sh` (it reruns step 2 against `origin/main`
   and pushes only if it passes; a trusted-surface change needs a `Trusted-surface:` line in each commit). The box watcher
   checks main and PR heads; verify the corresponding result on #63. Docs-only changes use `--changed <base>`.
   Before a milestone or toolchain/Mathlib bump, request a full run on the exact commit from the box watcher owner.
   On the box, `systemctl --user start --no-block consensus-lean-orb-ci-full@now` checks current main;
   `scripts/orb-ci.sh --full sha <commit> [<label>]` supports an exact revision using the watcher's configured
   environment and serialized full worktree. Coordinate with its owner rather than starting a second watcher.

`check.sh` refuses to run without `RUN_DIR` (set by `job`) or `CI`. Elsewhere: `CI=1 scripts/check.sh --full`.

`lake test` checks every cited name (`ConsensusLeanTest/Index.lean`) and compiles the review
type/axiom pins (`ConsensusLeanTest/ReviewAxioms.lean`). Step 12 checks, without a build, that every name
`docs/roadmap.md` and `docs/goldilocks-mapping.md` cite is in that index (as FLT's `checkdecls`
checks its blueprint) (`scripts/check-docs.py`). `--no-build` skips compilation but still
uses Lake's freshness gate, so stale artifacts fail. Snapshot/extension updates fail deliberately so
their diff is reviewed; CI refuses update flags and `--no-build`, and checks that the tree stays clean.

`lake check` and `lake comparator` need bubblewrap (`bwrap`). Where it is missing, `--full` skips
them and lists them as **CI-only**; the box full tier always runs them, with their fixtures and a guard that
fails on any skipped step. The shared box has `bwrap` (installed 2026-10-29), so a local `--full` run
executes them too. The comparator runs with `--paranoid`: the review statements' closure is replayed by
Lean's kernel and by every external kernel bundled with Lean (leanchecker-paranoid, lean4lean, nanoda,
con-leche, con-ron), about 3 minutes in CI. leanchecker replays every leaf module of the checked
libraries, one module per process (two at a time); never invoke it on a root or prefix with descendants.

Box caching (fast tier): worktrees share pinned Lake packages and retain their project build outputs;
the watcher prunes outputs whose source modules disappeared. Lake rebuilds changed modules and dependents.
The full tier builds the project from scratch; Mathlib's prebuilt dependencies remain cached.

The review boundary is separate from correctness. The **trusted surface** is
`ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` (each as `X.lean` and `X/**`), `Challenge.lean`,
`comparator.json`, `lean-toolchain`, `lake-manifest.json`, `ConsensusLeanTest/ReviewAxioms.lean` and
`ConsensusLeanTest/ReviewGuard.lean`, and, since #38, the instance semantics and statements (`ConsensusLean/Instances/<P>/{Spec,Statements}`
as `X.lean` and `X/**`, and `Instances/<P>/Refinement/Defs.lean`, for every protocol instance `P`; today
Goldilocks). The instance paths are on the trusted surface but are not trusted layers: they are `protected`
layers, which may import only trusted and protected layers (check-boundaries.py). The Shape examples
`ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}.lean` are not instances and left the surface on 2026-11-04
(no Challenge statement reaches them; `docs/decisions.md`). So did, the same day, the Goldilocks milestone
statements other than the acceptance endpoint and the instance Spec that only they reach: they are in
`ConsensusLean/Instances/Goldilocks/Milestones/`, outside `trusted_paths` (Challenge certifies only the four review
statements and the endpoint; `docs/decisions.md`).
`Lemmas/Problem/Derived.lean`, added for the now
archived Goldilocks sheet, left the list with it (no trusted statement reads it, by a compiled type-closure walk). The
record covers the listed files' text, not everything they import. The list lives in `scripts/boundaries.toml`
(`[checks] trusted_paths`, plain paths that must cover every spec-group file), read as literal paths at HEAD and
at the base. A trusted-surface change is **recorded, not gated** (owner, 2026-11-01): it lands through
`scripts/push-main.sh` like any change; every commit touching a trusted path carries a `Trusted-surface: <what and
why>` line (`scripts/review-boundary.sh`, with fixtures, fails without it), so `git log --grep='^Trusted-surface:'`
lists them, and push-main comments each landing on [#129](https://github.com/ethlabs-org/consensus-lean/issues/129).
The annotated tag `spec-approved` (an agent approval from 2026-10-30) is retired and stays at its last commit; the
approvals made under it are in `docs/spec-review.md`. The check infrastructure (`scripts/**`, `.github/**`,
`lakefile.toml`, `lakefile.lean`, which must not exist) is not on the trusted surface: agents maintain it (`TRUST.md`).
Reading the snapshot diff is part of making a Spec change; the comparator cannot replace that
reading. `docs/spec-review.md` records what was approved and what changed since 2852f717.

Design and history: `docs/decisions.md` summarises the design decisions; the full record is in the workbench:
the index of this repository's decisions, plans and research is
`repos/goldilocks/notes/generic-interface/consensus-lean/README.md`; the earlier layer design is
`repos/goldilocks/notes/generic-interface/layers-plan.md` ("Iteration 6: the definition of a good protocol";
its plan and reviews are in the run folder `iter6/`).
