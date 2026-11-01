# available-chain — contract draft

_Draft 4.3 (2026-09-27), committee model C*. Purpose: a small Lean repo
whose engine and claims are fixed, so that any suitable protocol can be an instance if it proves the
claims. Source of the engine: verified-consensus
`DecoupledConsensusModel/Generic` (Env, ProtocolSpec, Run) and
`DecoupledConsensusStatements/Generic`._

## 1. Decisions

```text
┌────────────────────────┬─────────────────────────────────────────────────┐
│ Topic                  │ Decision                                        │
├────────────────────────┼─────────────────────────────────────────────────┤
│ Sleep                  │ Asleep nodes receive and process, but do not    │
│                        │ tick (no emission). Join rule = "listen for a   │
│                        │ while"; no state transfer is modelled.          │
│ Committees             │ Model C* (mean-field seats): every label has a  │
│                        │ committee of all n seats; the run assigns seats │
│                        │ to validators by a fresh hidden bijection per   │
│                        │ label. Claims hold for every assignment. This   │
│                        │ is the exact form of "perfectly representative" │
│                        │ (no sampling error). See §2a.                   │
│ Weights                │ Unit seats: every validator has weight 1.       │
│ Corruption             │ Static: the faulty set is fixed for the run and │
│                        │ its size is the regime's threshold. No adaptive │
│                        │ corruption.                                     │
│ Scope                  │ Outputs stable and confirmed only. No FG, no SG.│
│ Genericity             │ Generic engine and outputs. Slots, proposers,   │
│                        │ proposal times, duty labels and blocks stay in  │
│                        │ the model (not 100% generic, by choice).        │
│ Liveness               │ Through honest-proposal inclusion, as in        │
│                        │ verified-consensus.                             │
│ Sleepy start           │ GST = 0 and t₀ = 0. A later GST needs recovery. │
│ Recovery              │ An instance sets θrec and recoveryFull.         │
└────────────────────────┴─────────────────────────────────────────────────┘
```

Tradeoffs go into constants, not claims. Every design must be able to
meet every claim trivially with some constant. An instance can set its
fast arming lag equal to its general arming lag and use general P1 for
fast P1. A smaller fast lag expresses a stronger guarantee.

## 2. Engine (fixed)

- **Env:** Δ, t_GST, `awake : V → Time → Bool`. No weights (unit seats).
- **ProtocolSpec n:** `State`, `Label`, `Payload`, `init`, `clock`,
  `actTime`, `duties`, `act`, `proposalTime`, `slotsAt`, `propose`,
  `gossip`, `process`, and the delivery hooks (`wellFormed`, `depsPresent`,
  `processed`, `excludes`, `handles`, `carries`). Wire objects are
  `Signed Label n Payload` (authentication and payload). The type does not
  mention validators.
- **Run:** honest set (static corruption), horizon, event list (ticks,
  deliveries), `seatOf : Label → Fin n ≃ V`, `proposerOf : Slot → V`.
- **Step:** a tick runs `clock`; a delivery runs `process`. Emission never
  changes the state. At a tick, an awake node emits: for each label due now,
  `act st ℓ` signed with its seat of ℓ; for each of its slots due now,
  `propose st s` signed with `proposer s`; and unsigned `gossip st t`. An
  asleep node emits nothing but still receives, processes, and runs its
  clock.
- **Signatures:** an object held by an honest seat or proposer was emitted
  by it. Faulty seats and proposers sign anything at any time.
- **Delivery:** arbitrary before GST; after GST every honest emission and
  required relay causes an actual checked, dependency-ready handler call
  in less than Δ, subject to the
  receiver exclusion test. Relay starts from honest acceptance; it does
  not require receiver acceptance. A healthy prefix has the same receipt
  guarantee before b₀. Strict deadlines and horizon conditions are retained.

## 2a. Committee model C* (rules)

```text
┌────┬────────────────────────────────────────────┬───────────────────────┐
│ K  │ Rule                                       │ Where                 │
├────┼────────────────────────────────────────────┼───────────────────────┤
│ K1 │ Seat authentication per label, with a      │ Auth, Run.seatOf      │
│    │ fresh run-chosen bijection per label       │                       │
│ K2 │ No identity in honest code: no V, one      │ ProtocolSpec n        │
│    │ init, no keys; the engine signs            │                       │
│ K3 │ Emission never changes state; own objects  │ World.step            │
│    │ return only by delivery                    │                       │
│ K4 │ Unit seats                                 │ Env (no weights)      │
│ K5 │ Honest seat signs once, at actTime ℓ, if   │ duties_spec,          │
│    │ awake; faulty seats unconstrained          │ Run.emittedAt         │
│ K6 │ Committee = all n seats (absolute vs       │ Run.seatOf            │
│    │ relative thresholds use awake)             │                       │
│ K7 │ Implementation obligation: a fresh private │ not checkable in Lean │
│    │ VRF per label; a seat signs at one instant │                       │
│    │ only. Bundle same-instant duties in one    │                       │
│    │ label, or use separate labels.             │                       │
│ K8 │ Witnesses with faults, a sleeper, and two  │ Witnesses             │
│    │ distinct honest views; the accumulation    │                       │
│    │ attack must be a valid run                 │                       │
│ K9 │ Optional slack ε (finite committees)       │ later                 │
│ K10│ Disclosures: no corruption of revealed     │ this document         │
│    │ committees; joiners receive full history   │                       │
└────┴────────────────────────────────────────────┴───────────────────────┘
```

Why RLMD-GHOST is not an instance: no signature links votes of different
labels, so "latest message per validator" cannot be written. Links in
payloads are unauthenticated and faulty seats can forge them. K3 removes the
one gap of C* against real committees: a node cannot learn or use its own
seats, so it uses only what an unsampled node can compute.

## 3. Interface (what an instance exposes)

- `confirmed, stable : P.State → Block`;
- `block : P.Payload → Option Block` (the block a proposal proposes);
- `opening : Slot → Prop` for the recurrence premise.

The proposal schedule is in the protocol (`proposalTime`, `slotsAt`); the
proposer is run data. `Block` has no proposer identity. Removed: `committee`,
`proposer`, `proposedBlock`, `finalized`, and all certificate, evidence and
slashing fields.

## 4. Regimes (fixed menu; instances cannot add premises)

Notation at time t: H_t = honest validators awake at t; H_[t−η,t] = honest
validators awake at some time in [t−η, t]; A = faulty validators (static,
always counted). Weights are counts (unit seats). Under C* every committee
has the fractions of the whole set, so the premises are stated on the whole
set.

All regimes require `RootInjective E I rho`. This is the collision-resistance
premise for block roots. Its scope contains genesis and every ancestor
(including the tip itself) of a block returned by `I.block` on a delivered
or emitted payload. Within this scope, equal roots imply equal blocks.
Sleepy, Outage, and Recovery use the same predicate. StableSleepy and Fast
inherit it from Sleepy. This does not restrict the raw `Block` datatype.
Since I9 (2026-09-29), `rootInjective_all` proves it for every run; see
"Derived roots (I9)".

Outage participation premises hold at every `0 ≤ t < b₀`, including
times before the protected read `T`. The healthy prefix starts at genesis.

**η-sleepy condition with threshold θ** (TSQ type, decision A):

    w(H_t)  >  θ · w(H_[t−η,t] ∪ A)        for every t in the regime

- θ = 1/2 gives w(H_t) > w(A) + w(dropped), where dropped = H_[t−η,t] \ H_t:
  the honest validators awake now outweigh the faulty ones plus the honest
  ones that went to sleep in the last η (the FreshMajority shape).
- The instance declares θ in [1/2, 3/4]. θ = 1/2 gives the strongest
  instance claim: its threshold premise holds for the most runs. η is an
  instance parameter. The contract requires Π ≤ η.

```text
┌──────────────┬───────────────────────────────────────────────────────┐
│ Regime       │ Premise                                               │
├──────────────┼───────────────────────────────────────────────────────┤
│ Sleepy       │ GST = t₀ = 0, synchrony with receipt relay;           │
│              │ at every t, w(H_t) > w(A)                             │
│ StableSleepy │ Sleepy, and the η-sleepy condition with threshold θ   │
│ (θ, η)       │ (for the stable claims)                               │
│ Fast         │ Sleepy with full honest participation and w(A) < W/4  │
│              │ (honest > 3/4). Decided by the user.                  │
│ Outage       │ StableSleepy(θ, η) counts before b₀; healthy delivery │
│              │ and receipt relay before b₀; arbitrary delivery in    │
│              │ [b₀, b₁)                                              │
│ FastOutage   │ Outage with the fast lag instead of the general lag;  │
│              │ at least ⌈n/2⌉ honest awake at every 0 ≤ t < b₀       │
│ Recovery     │ arbitrary before GST; after GST, θrec·(h_t+a)<h_t;    │
│              │ full participation if recoveryFull; honest awake      │
│              │ opening proposer every G                              │
└──────────────┴───────────────────────────────────────────────────────┘
```

## 5. Claims (the bundle every instance proves)

```text
┌─────────────────────┬──────────┬──────────────────────────────────────────┐
│ Claim               │ Regime   │ Conclusion                               │
├─────────────────────┼──────────┼──────────────────────────────────────────┤
│ confirmedSafe       │ Sleepy   │ honest confirmed reads are compatible    │
│ stableSafe          │ Sleepy*  │ honest stable reads are compatible       │
│ monotone            │ Sleepy   │ no honest read of either output retreats │
│ nested              │ always   │ stable ⪯ confirmed at every honest read  │
│ confirmedIncluded   │ Sleepy   │ an honest proposer awake at slot s       │
│                     │          │ proposes, and its block is in every      │
│                     │          │ honest confirmed read by                 │
│                     │          │ proposalTime s + D_c                     │
│ stableIncluded      │ StableS. │ same for stable, by + D_s                │
│ stableIncludedFast  │ Fast     │ same, by + D_f (target: small)           │
│ stableResilient     │ Outage   │ a stable read at T persists through      │
│                     │          │ [b₀, b₁) if b₀ ≥ T + A and b₁ − b₀ ≤ Π   │
│ stableResilientFast │ FastOut. │ the same persistence with fast lag A_f   │
│                     │          │ and the full-prefix high count premise   │
│ recovered           │ Recovery │ the Sleepy claims hold from GST + ρ      │
└─────────────────────┴──────────┴──────────────────────────────────────────┘
```

`Sleepy*` means the plain Sleepy regime for safety. The stable inclusion
claim uses StableSleepy(θ, η).

`ExecutionValid` implies that every event has nonnegative time. Thus each
state before time zero is `P.init`. Sleepy needs no separate clean-start
field. An outage can start after a healthy prefix. Recovery can start from
an arbitrary reachable state before GST.

`nested` is cheap (an accessor can enforce it); its value is only with the
two safety claims.

## 6. Constants (the instance's output)

θ and θrec in [1/2, 3/4], recoveryFull, η, D_c, D_s, D_f, arming lags
A and A_f with 0 ≤ A_f ≤ A, budget Π ≤ η, recovery bound ρ, and
the Recovery premise parameter G (gap between honest awake opening
proposers; ρ may depend on G). All in units of Δ and regime parameters; none may depend on the run.
Protocols are compared by these constants.

## 7. Non-vacuity

- A witness execution for each regime (in `AvailableChainWitnesses`).
- An accepted-object witness with an active cross-reader relay deadline.
- A sanity instance ("always output genesis") that proves the safety claims
  and provably fails `confirmedIncluded`.

## 8. Open choices

1. DECIDED: local repo at ~/ethereum/lean/available-chain (no remote).
   Toolchain leanprover/lean4:v4.30.0-rc2 with Mathlib v4.30.0-rc2, as in
   verified-consensus and fast-confirmation: the engine ports without API
   drift, and the local Mathlib cache is reused.
2. DECIDED: fast regime = full participation and honest > 3/4.
3. DECIDED: participation drop in a separate StableSleepy(θ, η) regime
   (decision A). Each instance declares θ.
4. Time: keep verified-consensus `Time`.

## Draft 4 decisions and reasons

- Sleepy starts at time zero with GST zero. When GST is later, recovery is
  necessary. The engine and `ExecutionValid` prove the clean initial state.
- Each instance sets θ. This keeps the η-sleepy premise explicit and lets
  the instance state the strength that its proof supports.
- Recovery uses a current-count threshold θrec and an optional full
  participation flag. This permits healing after an arbitrary prefix and
  permits an instance to use relative-half participation.
- Accepted-object relay is a regime field. A handler call alone can reject
  an object, so it cannot establish cross-reader acceptance.
- There is one `AvailableChain` bundle. Grid CO uses θrec = 1/2 and
  recoveryFull = false. L* uses θrec = 3/4 and recoveryFull = true.
- Grid CO declares θ_R and proves that its grid level exceeds each faulty
  count `a ≥ 1` when `h ≤ n` and `θ_R·(h+a) < h`. The bound `h ≤ n` holds
  for an awake count in the n-validator model.

## Draft 4.1 change

The outage fields `sleepyBefore` and `etaSleepyBefore` now require their
count conditions from time zero, not from the protected read time `T`.
This applies the standing decision that Sleepy-family premises start at
genesis. It excludes the Draft 4 pending-gate counterexample described in
`GRIDCO-STATUS.md`. No other contract field or claim changed.

## Draft 4.2 change

The shared `RootInjective E I rho` premise makes collision resistance of
block roots explicit. It covers genesis, delivered and emitted proposal
blocks, and all their ancestors. This is the scope needed by the reference
`NamedRootCollisionFree` and `RootInjectiveBelow` proofs. The round-14
root-collision run does not meet this premise. See `GRIDCO-STATUS.md`,
“Resolved in Draft 4.2”. No claim or constant changed.

## Draft 4.3 change

Fast P1 is now the `stableResilientFast` field of `AvailableChain`.
`Constants.fastArmingLag` satisfies `0 ≤ fastArmingLag ≤ armingLag`.
`FastOutageRegime` extends `OutageRegime` with a constants copy that
sets only `armingLag := fastArmingLag`, and adds
`∀ t, 0 ≤ t → t < b₀ → (n+1)/2 ≤ (awakeAt E rho.honest t).card`.
Integer division gives `⌈n/2⌉`. All other outage premises and the
persistence conclusion are retained. The general lag is not an extra test.

SA and SA-PC set the fast lag to `4Δ`. Grid CO and L* set it equal to
their general lag. Grid CO derives the new field from general P1; L*
has the same conditional derivation, with its claim proofs still pending.
SA uses `fastP1_from_engine` in its complete bundle. SA-PC also uses
its own `fastP1_from_engine` in its complete bundle
`sapcContract_from_engine` (status 2026-09-29; when this change was
made, the SA-PC proof was pending). The separate SA and SA-PC
extra-claim statements are removed.

This is the one-time authorized scope extension. The base contract is
now frozen at Draft 4.3. The strong companion below is additive.

## Relay premise — 2026-09-28

The user authorized this change to Draft 4.3. `SleepyRegime`,
`OutageRegime`, `RecoveryRegime`, and `StrongArmedRegime` no longer have
an `acceptedRelay` field. Their derived regimes inherit this change.
`PartialSynchrony.relay` and `HealthyPrefixDelivery.relay` conclude
`handlesAt`: an actual handler call within the original strict Δ bound.
`DeliveryWellFormed.deps` still requires dependencies at the call.
Readiness, horizon, participation, root, and timing premises are unchanged.
All public contract conclusions and constants are unchanged.

The shared Grid CO/SA proofs derive exact block-path transport and
in-window vote membership or stamped equivocation evidence. Honest HEADs
and surviving supporters retain exact transport. Proposal agreement uses
equal participating seats, equivocating seats, scores, and eligibility;
it does not require equal raw or support vote sets. SA-PC derives exact
complete-object relay from its archive handlers. This derived theorem is
not a network premise. Its `acceptedRelay` methods are proof adapters.

This note supersedes the earlier Draft 4 decision to require universal
acceptance. The negative examples N1–N4 in the r160 receipt-relay plan
still rule out unrestricted base-vote acceptance, expired-vote transport,
and packet receipt without dependency-ready handling. No handler, delay,
or FG module changes are part of this refactor.

## Derived roots (I9) — 2026-09-29

The user decided this change (`FRAMEWORK-DESIGN.md` §12 I9). The text
of every regime, claim and constant is unchanged. `RootInjective` keeps
its definition, and each regime keeps its `rootInjective` field.

The `Block` type changed. A node has a body, not a root, and
`Block.root` computes the root from the content. `Block.root_injective`
holds for every block. Thus `RootInjective E I rho` holds for every run
(`rootInjective_all`, `AvailableChainKit/Roots.lean`). The root premise
in §4 and in the Draft 4.2 change is a theorem now, not an assumption:
any caller can fill the field with `rootInjective_all`. Removal of the
field is a later plan (plan I9 D6). The round-14 root-collision run
cannot occur.

The parent-root check is the store dependency lookup. A proposal with an
unknown parent root is a temporary missing dependency. No `excludes`
changed. No `wellFormed` of Grid CO, SA, SA-PC or L* changed. FG-SA
`wellFormed` got the content check `rowsOk` (plan I9 D9), which is not a
root check. Payloads still carry resolved blocks, so the `Interface` did
not change.

This is a lock break. 91 lines of `docs/catalog.lock` changed, because
their closure reaches `Block`. No locked declaration changed its source
text or its type.

## Strong companion (additive)

The optional companion in `AvailableChainStatements/Strong/` adds a
`StrongInterface` with a `strong : State → Block` output and
`StrongConstants` with a fault cap and inclusion delay. It changes no
existing definition, regime, constant, or field of `AvailableChain`.
There is no unconditional order between `strong` and the base outputs.

`StrongClaims` requires safety (agreement and monotonicity) under Sleepy
and the cap; inclusion under Sleepy, full honest participation, and the
cap; persistence after sound arming; and safety and inclusion after
Recovery, with the cap explicit. SA-PC sets the cap to `⌊(n−1)/3⌋` and
the strong inclusion delay to `6Δ`.

`StrongArmedRegime` requires execution validity, root injectivity,
healthy delivery with receipt relay from genesis before `b₀`,
`h_t > a` at every `0 ≤ t < b₀`, the cap, and `T + Δ ≤ b₀`.
It has no certificate-possession premise, η-sleepy premise, outage
budget, or delivery or participation premise after `b₀`. The instance
must prove sound arming from these fields. Persistence covers all
times from `b₀` through the run horizon, with no bound on that horizon.

The base bundle retains its original fault scopes. In particular,
SA-PC's base clean and outage claims have no added cap. Its unchanged
Recovery regime, with `θrec = 2/3` and `recoveryFull = true`, implies
the cap; the instance must prove that implication.
