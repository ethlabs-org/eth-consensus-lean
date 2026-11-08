# Design rationale

This file gives the reasons behind the design choices of the model and of the repository, and states only the
rules that hold now. The per-statement detail is in the mapping (`docs/goldilocks-mapping.md`) and the per-check
detail in `TRUST.md`.

## Correctness and the review statements

- **A correct protocol is a fixed property table.** The generic layers define a correct protocol
  (`CorrectProtocol`) as a fixed table of properties, each with a fixed regime; an instance supplies only numbers.
  The precise protocol properties live in the instance's statements. Reason: a reviewer reads one definition for
  every protocol, and an instance cannot tailor what "correct" means to what it can prove.
- **Three layers.** L0 is the problem (what a correct protocol is), L1 the model (a generic execution engine), L2
  the shape (a protocol skeleton compiled to the model). The network is part of L0, as a communication log, and L1
  proves once that its log is faithful (`LogFaithful`), so no instance reproves delivery.
- **Names say which is correctness and which is the obligations.** `CorrectProtocol` (with its lemmas
  `CorrectProtocol.*`) is correctness; `ShapeObligations` (`Spec/Shape/Obligations.lean`, field `.correct`) is the
  set of obligations a shape meets; the review statement `Review.ObligationsSufficient` says that meeting the
  obligations gives a correct protocol. The families are `Model.ProtocolFamily` and `Shape.ChainShapeFamily`.
- **The regimes' meaning.** Healthy means full participation with faults below ⅓. Liveness premises tolerate one
  bad proposer slot per window (`ProgressTolerant`). The sleepy stress witness keeps at most two honest validators
  awake. Available and stable monotonicity are conditional, final monotonicity is unconditional. `available` may
  bind to `ac_confirmed`.
- **Profiles are checked labels, not property sets.** `Profile` names three standard capability sets:
  `ebbAndFlow` (final, stable, available), `bft` (final only) and `available` (available and stable).
  `Profile.Matches p O` fixes the provided capabilities exactly (not a lower bound, so an all-three protocol cannot
  be reviewed as BFT), compares capabilities only (the output type is not fixed and outputs may alias: Goldilocks
  serves available and stable by `confirmed`) and is not exhaustive (an available-only schema matches no profile
  and stays covered by `ShapeObligations` and `CorrectProtocol`). An endpoint states its profile with
  `ShapeObligationsAs p F K := p.Matches O ∧ ShapeObligations F K`; the Goldilocks endpoint `MeetsObligations` is
  `ShapeObligationsAs .ebbAndFlow`, a restatement of the unlabelled endpoint since its schema decides the label.
  `CorrectProtocol`, `Behaviour`, `Realizable` and `ObligationsSufficient` are unchanged, with one generic review
  statement: the table already selects its rows from the schema. So a BFT protocol keeps final monotonicity on
  every network, final accountability in every environment and healthy liveness, and an available protocol keeps
  for its available and stable outputs sleepy safety and liveness (`sleepySafe`, `sleepyLive`), outage
  persistence of the stable output (`persists`), healthy liveness (`healthyLive`) and healed safety (`healedSafe`):
  it need not be safe under asynchrony, but it recovers after it. Reason: a
  reviewer sees the advertised capability set checked in the endpoint, while what is claimed of each capability
  stays one fixed table.
- **The ordinary regime witnesses are not gated by the provided outputs.** The `sleepy`, `healthy` and `outage`
  witnesses of `Realizable` and `RealizableActive` show that the regimes can occur and do not depend on which
  outputs are provided; they are asked at every capability and index. Only the sleepy stress witness and the
  bad-proposer witness are gated by the provided outputs. Reason: gating the ordinary witnesses by profile would
  drop non-vacuity obligations without adding a claim.
- **`stable := final` is not a correct choice**: stable must be sleepy-live.
- **The outage regime is η-sleepy, and its end acts as GST**: after an outage, every after-GST property applies.
- **Per-slot proposer selection in the skeleton.** `Skeleton.proposerSel : Slot → SelSpec n`, so that a shape can
  fix its schedule (`fun s => .fixed {p s}`) or leave the choice to the run (`fun _ => .sized 1`).
  `ProgressReq.Fits (.recur _)` is `∀ s, proposerSel s = .sized 1`: a recurrence fits only a run-chosen proposer. A
  `.fixed` schedule arm was rejected because the bad-proposer witness of `regimes_realizable` (`badSel`: a faulty
  proposer at the periodic slots `s % P = P − 1`) needs a schedule-side condition: under a round-robin schedule with
  period coprime to `P` those slots visit every validator, so the witness would need everyone faulty, and a
  constant schedule has no witness at all. With the per-slot condition `regimes_realizable` stays proved (its
  witnesses specialise the fitting hypothesis per slot). The Goldilocks skeleton uses `fun _ => .sized 1` with the
  run's proposer `runProposer`, so its `.recur` progress patterns fit.
- **A generic time grid.** `TimeGrid` supplies an absolute positive slot length, and the skeleton supplies duty
  offsets in time units. Neither depends on the network delay generically; each instance constructs them from its
  public parameters. The generic progress and realizability proofs need only a positive slot length, not scaling
  or divisibility by the delay.
- **Ordered duty batches.** A selected protocol duty returns an ordered list of candidates, all signed by its own
  key in that duty's role. `releaseAll` checks each candidate against the holdings left by the successful earlier
  candidates; a rejection does not retry or reorder the batch. This permits a same-event parent-wrapper
  publication before a child's dependency check. Shape `pollBatch` defaults to the optional poll as a zero-or-one
  list, and the other shape handlers likewise compile to zero-or-one lists. No network or realizability premise
  depends on it, and delivery clocks need no change: `lastClock_deliver` and `now_eq_lastClock` establish the
  receipt time from event order.

## Network and delivery

- **The normal-delivery rule.** An honest send at `t` is held at `dl a` by every honest node awake throughout
  `[a, dl a]`, for every `a ≥ t`; a node that wakes at `u` gets the message by its deadline from `u`.
- **Half-open delivery.** `CommLog.PSync` and `SyncUntil` hold a message strictly before the bound: deadlines
  `max a g + ΔAC − 1` and `a + ΔAC − 1` (and `− 1` for rows), the paper's `[τ, max(τ, w) + Δ)`. So the
  Goldilocks transport has the protocol delays equal to the engine delays (`Δ_p = Δ_e`, `ΔF_p = ΔF_e`;
  `Setup.params`, `protoFGDelay`). The earlier inclusive form needed `Δ_p = Δ_e + 1`, whose extra unit only
  converted the inclusive engine endpoint to the strict node endpoint and budgeted no relay delay; half-open
  delivery makes it unnecessary.
  - `Realizable` and `RealizableActive` quantify over `ΔAC > 1` and `ΔFG > 1`: at a delay of `1`, half-open
    delivery is same-time delivery, which no protocol-agnostic eager log meets. Behaviour still covers every
    delay `≥ 1`.
  - Direction: `Delivers` at `dl − 1` implies it at `dl`, so `PSync`, `SyncUntil` and `OutageNet` are strictly
    stronger premises than in the inclusive form, and with them `Sleepy`, `Healthy`, `Outage` and the prefix lemmas;
    every Behaviour row, and so `CorrectProtocol`, `ObligationsSufficient` and `MeetsObligations`, is weaker at each
    fixed delay (it covers the runs that deliver by `Δ − 1`). This is the paper's reading.
- **Two delay bounds.** `Env` and `Model.Public` carry the message bound `ΔAC` and the row bound `ΔFG`,
  both positive; neither bounds the other. The log carries the protocol's message class (`CommLog.fgAtt`, filled
  only from `Protocol.isFGAtt` by `Model.Run.log` and `Model.tagLog`). `Delivers` serves rows within
  `ΔFG` (`fgAtts`) and every other message and every transaction within `ΔAC` (`msgs`, `txs`). So no statement may
  claim a block or a vote within `ΔFG`, and when `ΔFG < ΔAC` rows may overtake blocks.
  - Only `System.Healthy` relates the two, by `ΔFG ≤ fgDelay·ΔAC` (`Params.fgDelay`, a plain `ΔAC`-coefficient: an
    upper envelope for the coefficients, never a deadline; a larger bound weakens the premise). Sleepy and Outage
    carry no ratio and so cover every `ΔFG > 0`: a weaker premise, stronger claims.
  - Goldilocks rows are the standalone attestations and the relay wrappers of attestations only. A mixed relay
    wrapper (attestations with a block or a vote) and the empty wrapper are delivered within `ΔAC`, so
    attestations bundled with a block reach the others within `ΔAC`.
- **The node-level attestation clause has no lower bound, and node premises assume `Δ ≤ Δ_F`.** `AttDeliveredBy`
  has no `τ₀ ≤ time k`: a processing of the attestation before its signing or admission counts. Reason: an honest
  node forwards an admitted attestation as the same object, and L0 counts an earlier receipt (`CommLog.Held`), so a
  node can hold it from before the admission and receive nothing after it; an attestation's processing is never
  refused and the pool keeps it, so an earlier processing is as good. Blocks and messages keep the lower bound: they
  are forwarded in fresh wrappers, and an earlier receipt of a block can be refused.
  - `SyncOn` and `SyncBefore` carry `delta_le : Δ ≤ Δ_F` (claims §"Parameters" assumes `Δ_F ≥ Δ`): an attestation
    admitted from a block leaves in the block's relay wrapper, which is not a row and is served within
    `Δ`. So the node statements built on them (`SyncRun`, `GSTRun`, `SleepyRun`, `HealthyRun`, `HSShared`, the
    Persist, Run, Service and healing rows) cover only `Δ ≤ Δ_F`, the paper's range. No proof reads `delta_le`; the
    consumers of the clause read signings only.
  - The generic L0 two-bound network stays unordered. The open transports (`PSyncTransport`, `SyncUntilTransport`,
    `SyncRunTransport`) take `Δ ≤ Δ_F` as a hypothesis; with the lower bound gone they owe no signer provenance for
    attestations.
  - `MeetsObligations` needs no `Δ ≤ Δ_F`: its closure mentions `SyncOn`/`SyncRun` only through the uninstantiated
    `SleepyWindow` disjunct of `vote_frame_of`'s service hypothesis (`Compose/Sleepy/FrameLabels`, discharged with
    the `SleepyServiceBefore` disjunct), and never constructs or reads them.
  - Rejected: restricting the clause to signings (it drops the forwarding of admitted attestations) and a local
    `max Δ Δ_F` deadline for admissions (two attestation fields).
- **A delivery is a raw arrival.** There is no delivery-readiness condition in `ExecutionValid`: a delivery is a
  raw arrival into the total `process` handler and the log, independently of dependency readiness or consensus
  admission. Buffering and retries belong to the family; there is no engine buffer, no extra event kind and no
  replay of `seen`. So valid runs only increase, Behaviour and the shape claims only strengthen, and the
  poisoned-dependency exclusion is closed by construction. Do not infer monotonicity of `CorrectProtocol` for an
  arbitrary system from that inclusion alone: its witnesses are existential. The canonical runs still prove
  `Adequate`, `Realizable` and `RealizableActive` (including `regimes_realizable`), prefix closure still uses
  truncation, and `Run.canonical_delivery_ready` proves that the canonical witnesses also satisfy the
  incoming-readiness condition. Goldilocks's carried parent-chain processing needs no admission premise.
- **Dependencies guard outgoing releases.** One monotone holdings policy governs release: the engine releases a
  candidate only when its dependencies are already held. The predicate is decidable and depends only on the
  holdings and the object, which preserves rehashing invariance; neither it nor the protocol handlers receives the
  hash function. Other instances use the unrestricted policy. The canonical scheduler keeps first releases rather
  than last duplicates, which preserves dependency order at the same timestamps.
  - Goldilocks's fresh child forwarding wrapper depends on the complete same-origin signed parent wrapper, not
    merely a raw parent hash. Carried references are recursively processed, not inert pointers. The pre-envelope
    dependency must already be held; nesting it in the current envelope does not satisfy the requirement. Unlike
    the earlier `depsS`, the policy does not require `parentFG.isSome`: accepted-parent and timely-processing
    conclusions remain protocol proof obligations, as do source/time authentication, closure to prior processing
    (or own acceptance) and the store-to-seen/no-suppressed-release joins.
  - No FIFO channel, retry queue or separate full-ancestry envelope is assumed.
- **Release at the delivery's own time.** What a delivery makes a node emit, relay or acknowledge leaves at the
  delivery's time. A protocol has `deliverDuties : Time → List Duty` (default `[]`; a skeleton lists them as
  `deliverOrder`), and `Run.step` at `.deliver v o t` runs them on the processed node and then the gossip
  `releaseAll`, as an awake tick does; `releases v o t` holds at the delivery's time through `Run.SendsAt`, and
  `Unforgeable`'s earlier send may be a delivery.
  - Reason: the protocol texts read an admission or a vote cast at a receipt as an instantaneous send ("the network
    relays each accepted object"; relay uses the acceptance time, also for an asleep receiver), the claims' proofs
    A1.2/C1.1 (`writer_pool`), A1.3 (`fastLock_same_slot`), A1.7 (`honest_vote_at_update`) and the Sleepy invariant
    rely on it, and model runs showed that release at the next awake tick, or even one unit late, breaks R.1/S1
    under a sleeping admitter, while delivery-time release had no violation. Persistence across sleep alone is not
    enough.
  - Rejected: weakening `SyncOn`/`SyncAC` to the sender's first awake time (the proofs cannot absorb it), a
    gossip-only release at deliveries (a vote cast at a receipt would still wait), and votes carrying their head
    block (a spec change for an engine defect).
  - The Goldilocks skeleton's delivery duty is one `.poll`, a drain: `fgDue` is false at every cut (set only by the
    tick's `pollPropose`), so a delivery emits at most the queued vote and the relay gossip, and
    `signed_only_in_ticks` stands.
  - `CommLog.EagerFrom.recv` is strict (`max t g < a`): the canonical schedule fixes the deliveries at `a` before
    the delivery-time releases at `a` exist, so those are served from `a + 1`. Every regime premise the witness runs
    serve (`PSync`, `SyncUntil`, `OutageNet`) is still implied (`EagerFrom.psync`).
- **Received payload objects are processed in preorder.** A delivery traverses the entire object closure,
  processing a canonical block before its carried votes and attestations. Wrappers have no canonical node event,
  and nested wrappers do not hide their contents. Payload votes get actual message calls, also when the containing
  block is refused or silently dropped: this is independent service of authenticated carried objects, not
  acceptance of the containing block. Block-before-payload preserves the block handler's priority (including any
  vote it emits); the later message handlers use the resulting state. The one-vote invariant applies to arbitrary
  same-time object lists, so one delivery poll still drains the emitted vote.
- **Finite observation coverage is separate from labelled action coverage.** `Trace.observationHorizon` defaults to
  `none` (the action-only horizon); `InHorizon` also admits a cut reaching a time covered by explicit finite
  metadata. Canonical traces set the engine horizon, clamp wakefulness to `[0, horizon]`, and stutter unlabelled at
  `horizon + 1`. Reason: action-only coverage could never supply the strictly later cut that `sleepy_read_cut`
  requires (a valid one-validator, `Δ = 2`, horizon-1 witness shows it). No engine premise, readiness condition,
  handler call, signing or duty is added; canonical labelled cuts stay bounded by the engine horizon,
  `Simulates.covered` still covers actions only, and both component projections preserve observation metadata.
  Unlabelled padding alone is not a readiness repair.
- **Pre-outage synchrony cuts off recipient deadlines, not send times.** `SyncBefore` requires service only when
  the recipient's protocol deadline, including its latest wake, is at most `b₀`. Pre-outage synchrony uses it
  instead of `SyncRun 0 (b₀ − Δ)`, which imposed obligations after arbitrary later wakes inside the outage. The
  cutoff is conservatively the protocol deadline itself: deadline `b₀` is covered, `b₀ + 1` is not. Attestation
  deadlines use `Δ_F`; strict processing bounds and send-time lower bounds are kept. Acceptance relay remains an
  explicit obligation: receipt alone cannot invent acceptance of a discarded missing-parent block.

## Adversary growth

- **Faults grow by identity.** The single source of truth is a monotone set `faultyAt t` of compromised
  validators (L0 `EnvPoint`, L1 `Run`). Counts are derived. A non-decreasing count alone would admit a mobile
  adversary that keeps every extracted key while the count stays small. Every honesty test reads the time of its
  event: a validator in `faultyAt t` is faulty for every event stamped `t`. A constant set is the static adversary.
- **Ordinary keys, immediate compromise.** From its compromise on, the adversary holds the validator's signing key.
  It can sign objects that claim an earlier slot or role, since the claimed slot is not the signing time.
  `Unforgeable` binds a signer honest at the delivery time, and `Credentials` binds every key, compromised or not.
  No forward security and no corruption delay are modelled. A delay would need corruption requests as well as
  effective compromise, and it does not stop old-key forgery once the key is extracted.
- **Charging at consumption.** An honest signature made at `t` and consumed at `d` could be counted twice if its
  signer were compromised in between and signed a conflicting object. Every participation budget is therefore the
  static count on the view retained through the consumption horizon (`EnvPoint.retain`, `lookAhead`): support at
  `t` counts only validators still honest then, against the faults of then. The windows are contract numbers.
  Larger windows are stronger premises, and `Params.Admissible` leaves them unbounded, like `catchUp`.
- **Scopes.** A read made while honest stays protected after its reader is compromised: reader predicates are
  evaluated at each cut's time. A release, or a transaction submitted to a node honest and awake at the
  submission, stays owed by the network after its sender or recipient is compromised (persistent network
  ingress). Without that, a transaction whose only recipient is compromised before dissemination could never be
  served. A recipient is served while it is honest through the deadline. Non-framing protects a validator honest
  at `d` against the evidence nodes saw while honest by `d`. Past honesty does not prevent later conviction,
  because an extracted key can sign a conflicting object.
- **Goldilocks windows.** These numbers are the windows of the growing-fault proofs' counts, read off the
  constant-fault proofs' window audit. None is a service constant:
  - sleepy look-ahead `5`: support at the participation point `t_s + Δ` of a slot's votes is last counted by the
    slot's confirmation update at `t_s + 6Δ`, whose pool admits equivocating second votes;
  - cohort look-ahead `0`: every count of the outage cohort ends by the update of label `j₀ + k`, at least `2Δ`
    before the no-sleep window's end;
  - proposer hold `1`: a proposer compromised before the slot's votes are cast can split them with a smaller-root
    second proposal (fork choice breaks score ties by the smaller root), and all votes are cast by the tick at
    `t_s + Δ`.
  The healthy budget needs no window: it is the bound at the horizon, and claims through a time `b` need only the
  faults by `b` (prefix closure). `ΔFG` enters no window. Increasing a window, or adding a premise, after the
  statements land is a statement correction, raised with a counterexample.
- **The static adversary keeps full strength.** `ShapeObligationsOn`, `CorrectProtocolOn` and
  `Review.ObligationsSufficientOn` state the obligations and correctness on a class of runs. At constant faults
  they are the static statements, so negative tests are also stated there. The growing-fault statements are
  additional. Challenge certifies the Goldilocks endpoint and headline under growing faults (`MeetsObligations`,
  `GoldilocksCorrect`, `Statements/Obligations`), proved by `Instances/Goldilocks/Proofs/Growing/Obligations`; the
  constant-fault pair (`MeetsObligationsConstant`, `GoldilocksCorrectConstant`, `Milestones/Statements/Obligations/Constant`) is an
  untrusted corollary. Each growing-fault milestone is a milestone of its own,
  `Instances/Goldilocks/Proofs/Growing/<M>`, entered through its `Main`.
- **Continuation is not part of correctness.** A hand-over after healing is a separate side property:
  `Continues` (`Instances/Goldilocks/Milestones/Spec/Continuation`, generic over `System`), stated for Goldilocks
  as `GoldilocksContinues` (`Instances/Goldilocks/Milestones/Statements/Continuation`). A run healthy from GST up
  to a hand-over time at or after the heal point is only sleepy afterwards, its corruption growing from below `β·n`
  to `⌊(n − 1)/2⌋`, with fewer than `α·n` convicted by any two honest views (the generic form of the slashable
  bound of `AvailableChain.FGSA.Run.WeakContinuationGrowthClaim`, archived at `79cdddc8`); its available and stable
  outputs stay safe and live. It is a single run with growing faults, which covers that claim's two runs (a source
  prefix and every retained-set continuation of it); no seed is fixed, because the claims are the generic
  ready-reader safety and transaction liveness. It is an untrusted milestone statement: not trusted, not in the
  spec snapshots, not reached by Challenge, and not part of `CorrectProtocol` or `GoldilocksCorrect`.

## Contract numbers

- **Assumptions are minimal, guarantees may be loose.** Loose numbers are acceptable for the latency, healing-time
  and catch-up guarantees, never as a reason to strengthen an assumption. Progress recurrence is as weak as the
  proofs allow (no consecutive honest proposers), and the same premise-minimisation rule applies to every contract
  assumption. The resilience fractions stay ⅓ and ½. These numbers are not claimed minimal.
- **Fixed assumptions, then guarantees.** `ContractAssumptions` is fixed before any coefficient is chosen and is
  independent of the outer gap `X`; the coefficients (`contract_coefficients`) are closed formulas in `k`, `δ_t`,
  `fgSlots` and `X`. The outage lag, budget, no-sleep margin and recovery delay are fixed numbers, not guarantees.
- **No ratio on the review surface.** `ContractAssumptions` takes the FG delay in slots, `fgSlots ≥ 2`, with the
  timeout `3·fgSlots ≤ δ_t`; the contract sets `fgDelay := 4·fgSlots − 6`, so healthy runs have
  `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (the paper's `c_F ≤ fgSlots`). Nothing is lost against the earlier ratio
  form (`r ≥ 1`, gap `cF r = ⌈(r + 6)/4⌉`): each contract is the ratio contract at `r = 4·fgSlots − 6`, and the
  ratio endpoint at every `r` follows by monotonicity in `fgDelay` (the test `meets_obligations_at_every_bound`,
  where `cF` now lives, off the trusted surface).
- **All time numbers are `ΔAC`-coefficients**, the node and the engine delay alike (`Δ_p = Δ_e` under half-open
  delivery). Current values:
  - catch-up `19` (`contract_catchUp`): it covers the Sleepy margin, `18ΔAC + 1 ≤ 19ΔAC` for every `ΔAC ≥ 1`. It is
    flat, not `k`-dependent: no proof needs a `k`-dependent catch-up.
  - latency `4X + 6` for available and stable (independent of `fgSlots`), `4(X + 3·fgSlots) + 1` for final: the
    final latency covers the window of span `3·fgSlots` (`finalWindow`) and one delay. The post-heal proofs do not
    consume the row-timing components of their premise bundles, which is why the nonfinal latency does not read
    `fgSlots`; this is not a theorem that removes all row assumptions.
  - heal `catchUp + M_f` (`contract_heal`), with `M_f = healMargin = 20 L_drain + 8k + 28δ_t + 28X + 56` and
    `L_drain = 2k + X` (expanded `48k + 28δ_t + 48X + 56`; heal `387` at `k = 2, X = 1, δ_t = 6`). It is the final
    route's heal bound on the key-dependent rise-round route at `λ = 2Δ` (`exists_reset_of_drain_rounds_awake`,
    `resetBoundRounds`, `healBoundCoeffRounds_at_two`), which gives a lower heal than the earlier five-window frame
    route; the untrusted reset coefficient `healthyResetCoeff = 20 L_drain + 24(δ_t + X) + 40` moves with it, and
    `M_f` also covers the nonfinal reset envelope for `δ_t ≥ 6` (`healMargin_ge_reset`, slack `4δ_t − 13`). A
    smaller heal makes `healthyLive` and `healedSafe` hold from earlier and shortens `healedSafe`'s progress window,
    so both get stronger; `Admissible` does not bound the heal, and the generic realizability witnesses give
    `SafeActive` from every start, so realizability is unaffected.
  - arming lag `4k + 6`: the label before the outage label (`k + 1½` slots before `b₀`) is fully armed by `b₀`.
  - no-sleep margin `4k + 6`: the window `[b₀ − (4k + 6)ΔAC, b₁ + (4k + 6)ΔAC]` starts by `t_{j₀ − k}` (the formation
    window of the arming lock) and ends after the restored votes of labels up to `j₀ + k`.
  - recovery delay `9`: enough for the restored votes of the locked validators to bring the confirmed read back
    above the record.
  - outage budget `4k − 5`: the bound of the obligations proof. The lock window keeps an unpolluted label for gaps
    up to `(4k − 5)Δ` (`exists_unpolluted_label`), and the restored label stays within `j₀ + k`
    (`stop ≤ t_{j₀+k} + Δ`, one tick of slack, pure time arithmetic). A larger budget weakens `OutageTimes`, so
    `persists` is stronger; no other row reads it, and `budget_pos` holds (`4k − 5 ≥ 3`). `4k − 4` would break the
    restored-label bound: at `k = 2`, `Δ = 2`, start `11` (`j₀ = 0`) the bound is `18`; `4k − 5` gives stop `≤ 17`
    and `4k − 4` gives `19 > 18`. The earlier `4k − 6` came from the node-level phase-sensitive outage condition
    (V), which went with the node-level regime rows.
  - look-back `η = 0` (`Params.standard`): see §"Regimes".
- **Catch-up is a guarantee coefficient, but its effect is mixed.** A smaller catch-up makes more validators ready
  (shorter `cDur`), which weakens the sleepy and outage participation premises, but it also starts the healthy
  progress window (`healthyLive`, `healedSafe`, `prog [ready, …]`) earlier, so a catch-up change can make those
  rows incomparable with the former ones. No-sleep `4k + 6` does not cover `catchUp + 1` for `k ≤ 3`; no proof uses
  that relation.

## Regimes

- **The generic outage is slow arming only, with no absolute-majority participation premise.** `System.Outage` has
  `NoSleepOn a z` (no honest validator falls asleep in `[a, z]`, waking allowed; `a = b₀ − noSleep·Δ`,
  `z = b₁ + noSleep·Δ`, clamped to `[0, horizon]`) and `CohortOn a z` (faulty plus late wakers fewer than the
  honest validators awake at `a`; half of all is the lemma `CohortOn.two_mul_lt`). `CorrectProtocol.persists`
  protects every `Ready` reader from `b₁ + recovery·Δ` (`ProtectedReadyFrom`). `Params` has the fields `noSleep`
  and `recovery`. `Params.cover` is kept but read by no regime.
- **The Goldilocks outage regime is plain sleepy.** `goldilocksContract` keeps `Params.standard`'s `η = 0` and has
  no look-back assumption, so `Outage`'s participation premise `EtaSleepyOn θ (η·Δ)` is plain sleepy and its window
  bound is `b₁ ≤ b₀ + budget·Δ`. Reason: the proof uses only the plain-sleepy consequence
  (`EtaReadyAbove.readyAbove`) and the budget bound, and a weaker premise makes `persists` claim more.
- **Sleepy and Outage carry no ratio** (§"Network and delivery"); only Healthy bounds `ΔFG`.
- **Node-level regime rows.** The node-level rows R.1, R.2, R.7 and R.8 (`Milestones/Statements/Regimes/{Sleepy,
  Always}`) are proved milestones, and the obligations proof uses their definitions. The node-level rows R.3–R.6
  (healed, final, outage, weak continuation) are not stated: R.3–R.5 correspond to the generic rows `healedSafe`,
  `healthyLive` (through `ShapeObligations.correct`) and `persists` of `MeetsObligations`, and R.6 (weak
  continuation) has no generic row. None of them was proved or reached by Challenge, Solution or the endpoint.
- **No cross-node nesting statement.** Cross-node compatibility follows from healed safety plus R.8's
  `OutputsNested`: a finalized read is below its node's confirmed read, which is compatible with the other ready
  confirmed read. The same-instant ancestry is false (a carrier-delay replay shows it), and a lagged ancestry is not
  stated. This does not change R.8's local nesting.

## Goldilocks model choices

### The node as a chain shape

- **The Goldilocks node as a generic shape, simulated rather than equated** (`AsChainShape`). The wire format and
  digest are the refinement's choices, not the spec's:
  - `n`-independent bodies (the family needs one body type for every parameter set; a fixed-`n` body was rejected);
  - canonical signed objects (a block's header carries the canonical objects of its payload, so the engine's view
    contains the evidence G1.5 needs);
  - a digest from the engine's hash with the genesis root as a parameter (a header naming genesis by digest is
    dropped, so `RootOk` holds by construction).
- **Step order** `[poll, poll, pollPropose, propose, poll, poll]`. The node's tick is the poll proposal step at the
  public times (a duty, so it runs only awake; putting it in `clock` was rejected since `clock` runs asleep). Two
  leading polls release the bodies queued since the last tick, so that a proposal carries only released objects
  (filtering own objects out of the proposal was rejected); the trailing polls run the FG update and drain the
  tick's vote and attestation.
- **State.** The family's state is a Goldilocks state at every proof of `1 ≤ n` (`PubState`; a `dite`/cast family
  was rejected).
- **Simulation.** `Simulates` maps engine cuts to node cuts with a monotone `ι` and relates ticks, deliveries
  (`DeliverSeq`, one group per canonical object), restarts and releases; releases and relays are related at the
  delivery time (`ReleasedFrom`, `RelayedFrom`). The proposer is the run's selection (`runProposer`), and
  `selValid_proposer` (`ConsensusLeanTest/Goldilocks/Refinement/Simulation.lean`) derives the proposer equation
  from `SelValid`, so engine-level Goldilocks theorems carry no proposer-selection hypothesis.
- **The spec block carries the engine's input.** The engine hashes the whole header `(parent, pos, input, info)`
  and `compile` writes `input := encodeTxs mempool` outside the shape's `Info`, so two engine blocks differing only
  in `input` have different hashes; without the field they would have one spec content, `RootOk` with one digest
  could not hold of both, and the refinement could not be stated faithfully. So `Common.Block` has a field
  `input : Nat`, the digest is over `(parent, slot, input, FG payload, AC payload)`, and the node's tick event
  carries the input (`Node.Event.tick x`; `mkBlock` writes it; the AC never reads it). Rejected: the input through
  the AC payload via `ACInterface.proposal`, which changes the generic AC interface, the SA payload pair and every
  proved AC file; the field leaves the AC and FG-store lemmas (generic in the block type) intact. The spec folds the
  input into the AC payload (`specs/goldilocks/tex/shared/composition.tex`: the AC fixes the encoding of its
  payload); the mapping records the field as that encoding.
- **The proposer schedule is not runtime data.** The runtime `Params` and `FGParams` have no proposer schedule:
  once receiver credential checking belongs to execution validity, `Store`, `NodeState` and `ACInterface` need not
  know the selected identity. The schedule is passed separately to node tick/proposal semantics and to the
  statements that refer to the slot proposer; the simulation supplies it from the run's selection. Genesis uses a
  fixed validator index, not the slot-zero proposer. Reason: no repeated state transports and no arbitrary schedule
  hidden in runtime data. The engine's `dutyStep` gates both state mutation and release on selection.
  Delivered-block proposer correspondence is an explicit `LocalRun.proposerCredential` obligation, including
  faulty signers, proved for the canonical simulation by `simTrace_proposerCredential` (`Lemmas/Simulation/Run`).
- **Restart replay order is proposer-independent.** It depends only on the validator count and the genesis root:
  its data enumerates a frame's non-genesis blocks in parent order, with no proposer or timing dependence. Indexing
  it by these two values, supplied from `Setup` by validator count, keeps the actual sibling order when the
  simulation parameters use the run's proposer selection. `ReplayOrder sp` is notation for this type; no state
  transport or freshly chosen replay order is needed for a different proposer schedule.
- **The publisher.** Successful block cuts, including own-proposal acceptance, enqueue signed timestamped wrappers;
  duplicate or refused calls do not. A durable node-root-to-wrapper map supplies the exact same-origin parent; the
  next selected poll drains the event queue in acceptance order through `releaseAll`, after the vote/attestation
  polling. A missing non-genesis parent produces no candidate, and a reachable-state invariant must exclude that
  case. Candidate construction is not successful publication: the publication contracts need their own
  prefix-guard and provenance proofs, and release analyses must account for the forwarding releases and their
  additions to `seen`.
- **Collision transport targets the constructed trace.** It targets the canonical trace constructed from the
  engine run, not every simulation witness: simulation coverage alone does not identify all block calls with
  engine objects. Tagged genesis roots make freshness unconditional, so neither transport nor finalized
  accountability assumes it.

### Protocol rules

- **Graded fast locks.** Each lock carries its own expiry, fixed at the write; a lock is live at `t` while
  `slot(t) ≤ l.expiry` (`Lock.LiveAt`); unlock and the move back keep it, and a restart keeps the locks. A slow lock
  of slot `s` gets `s + k`. A fast lock of slot `s` gets `fastExpiry`, `min(s + k, max(s + 2, E + c))`, with `E` the
  latest expiry of the node's live fast locks of earlier slots; it gets `s + 2` when no live fast lock of an
  earlier slot remains (a gap in fast confirmations shortens it only once those locks have expired). `c ≥ 2` is a
  parameter (`SAParams.c`, `Setup.c`, no `c ≤ k`) that no coefficient reads. The cap is at the write; "a live lock
  is recent" comes from the run invariant `l.slot + 2 ≤ l.expiry ≤ l.slot + k` (`LocksWF`). The rule's four
  choices:
  - **per-slot `E`**: `E` counts only fast locks of earlier slots (`l.slot < s`). Without it, repeated optimistic
    writes within one slot ratchet the expiry up to the cap; with it, the deadline grows by `c` per slot.
  - **`E` is not filtered by branch**: it is the node's local fast-lock history, not support for the branch, so a
    fast lock unlocked or moved back to `Φ.F` still feeds `E`, as do optimistic locks on genesis or on a common
    prefix. Such a lock vetoes nothing, and no proof reads `E` beyond the bounds `[s + 2, s + k]`, so a filter would
    add text and buy nothing.
  - **independent fast and slow writes**: over the path, the deepest fast block gets a fast lock with
    `fastExpiry` and the deepest slow block a slow lock with `s + k`, each written when it exists. The earlier form
    (a slow-qualified update's fast lock getting `s + k`, "keep the highest deadline") was dropped: the spec loses
    `lockBlock`, its conditional and the `≠ D` clause, and `SlowLockAt` loses two clauses. The outage arming uses
    the slow lock, and no statement needs the deeper fast block to live more than two slots.
  - **the veto stops only the record**: a result that conflicts with a live lock leaves `latest_confirmed`
    unchanged, but the locks are still written, over the blocks of the result's path that conflict with no live
    lock. This closes the veto branch of the outage cover base, and an unvetoed update behaves exactly as before
    (the filter is vacuous). The fast write is kept as well (over a slow-only alternative). Its pre-GST effects
    are bounded, pre-GST only, and leave `MeetsObligations` untouched: (i) the fast write is an FG source, so a
    vetoed node may lose a finality bit; this is not veto-specific, since an unvetoed node with the same pool, no
    lock and no FG view of the later block fast-locks the same ancestor and loses the same bit, while a node that
    already holds that block normalizes the lock to a compatible viable ancestor and does not; (ii) a vetoed slow
    lock may pin the node up to `k − 1` slots beyond the vetoing lock's expiry.

  `fastSelect` stays the raw test, so A1.4 (b) (`OptimisticNextUpdate`) keeps its meaning. `LocksMoveBack` states
  the shape of the new locks, and `MovesBack` also keeps the expiry (a strengthening). Through
  `FastUpdateAt`/`FastLockAt` the scope of A1.2, A1.5, A1.9, C1.1 and `RecentSourceNextVote` covers the fast locks
  of vetoed updates (their arguments read the counted votes and `Carry`, not the record). No coefficient depends on
  the rule. The LaTeX is `specs/goldilocks/tex/goldilocks-spec.tex` §"Locks" and §"Confirmation" (claims OC1).
  Witnesses at `k = 6`, `c = 2`: `ConsensusLeanTest/Goldilocks/AC/GradedLocks.lean`.
- **Full-tree fallback for an honest vote's head.** `tryVote` walks the viable tree of `SA.voteDomain`: the voter
  block tree when its viable tree in the current frame is nonempty, else the whole frame tree. `voterBlockTree`
  keeps its meaning, so `ViableAtVote` and every trusted statement are unchanged in meaning: the smallest trusted
  diff.
- **`ac_to_fg` returns only `fg_confirmed`** (or `⊥`). Nothing read the returned head: the node discards it, and
  under loose BJ the finality pair comes from `finality_pair(Λ, σ_e)` on the source's entry state. So
  `ACInterface.toFG`, `SA.acToFG` and `Node.acToFG` have no head component; requirement 1 (`ReqHeads`) has no
  returned-head clause, requirement 2 (`ReqSource`) has no "the returned head extends it", and `Compose.SourceHeld`
  has no such conjunct. No consumer of either fact existed, so they were dropped rather than restated on `ac_head`.
  The node and the family behave as before (only an unread return value went), and the LaTeX (SPEC requirements 1
  and 2, claims A0.6) agrees.
- **HS.3 is stated as its after-`r` part only.** `FrozenTreeAgreement` (`Milestones/Statements/Healing/Service`)
  states the second part of claims HS.3: with `Prop⁺(G_p)` and `t_s ≥ r`, every honest slot-`s` vote is `P` with
  its ancestry retained, and later honest votes and proposal parents extend `P`. It omits the first part (every
  honest slot-`s` vote is `P` under the explicit voter lock premise and the proposer-anchor premise, without
  `Prop⁺` or `t_s ≥ r`). This deviates from claims HS.3, which states both parts. Reasons:
  - The first part has no proof. Its route compiled except for one leaf, `voter_unlock_keeps_lock`: a voter keeps,
    through its own `unlock`, a live lock above the proposer's lock `L`. The proposer's survival of `L` does not give
    that: `opponents` counts only support votes whose head is in the frame's tree, so a voter whose `Σ.F` is below
    the proposer's can count more opponents against the same votes. `unlockTarget_frame_dependent`
    (`ConsensusLeanTest/Goldilocks/AC/UnlockFrame`) is a compiled instance of this at the lock-code level; it does
    not show that the configuration is reachable under `AgreeSetting`. No counterexample to the leaf or to the first
    part under their premises is known. A proof would need a new argument: the honest voters' locks required by the
    proposer-anchor premise would have to bound the slot-`(s − 1)` votes.
  - Nothing consumes the first part. HS.4, HS.5, HR.3 and H.4 use only the second (`frozen_tree_agreement_clean`,
    from HS.2): `ready_protected`, `consume_continue_of`, `acquired_or_changed`.
  - With the restatement HS.3 is proved (`frozen_tree_agreement`, from HS.2), and so is `PhaseServiceStatements`
    (`phase_service_statements`). Restating the proposer-anchor premise over the voter's read-point locks was
    rejected: that premise is the voter's state after its own `unlock`, nearly the step being claimed.

### Layout of the instance proofs

- **Simulation and obligations are separate closures.** The proofs split by import closure into
  `Lemmas/Simulation` (the simulation statements, namespace `Goldilocks.Simulation`, `SimulationStatements`), which
  never imports the obligations, and `Lemmas/Obligations` with `Proofs/Obligations` (namespace
  `Goldilocks.Obligations`). The field theorems of the obligations proof (`Lemmas/Obligations/Concrete`) follow
  `MeetsObligations`: `meetsObligations_*`, with the existential endpoint `meetsObligations_exists`.
  Block-acceptance names (`accepted_tree`, `accepted_in_view`, `accepted_child_decodes`, …) are a different concept.
- **The Baseline sheet and its tests were removed.** The earlier pinned properties sheet was never approved and
  was off every live path: nothing in the closure of `Challenge`, `Solution` or the obligations endpoint imported
  it. The positive controls keep their own copy of its schema and skeleton (`Tests.Controls.ctrlSchema`,
  `ctrlSkeleton`).

## Final liveness

- **Final recurrence is a good window every `X` slots.** The final pattern is a bounded window of honest ready
  proposers with a fixed internal span, repeated with an arbitrary outer gap `X` (`.recur`). `δ_t` may depend on the
  internal span, never on `X`; no local parameter may silently depend on `X`.
- **Route A, four anchors.** `finalWindow A = [0, c, 2c, 3c]` at `c = fgSlots` (span `3c`, `[0, 2, 4, 6]` at
  `fgSlots = 2`), with the timeout `3·fgSlots ≤ δ_t`. The window coverage comes from the anchor route
  (`cacheCoverage_of_anchor_window_upTo`, `Lemmas/Obligations/WindowAnchorRoute`): honest proposers only at the four
  anchors, three anchor steps of `c`, and `P₃.slot ≤ P₀.slot + δ_t`. Only this coverage lemma needs the span bound;
  the seed needs `δ_t ≥ 4`. `δ_t` is a fixed constant, independent of `X`; tolerance keeps `X = span + 2` as an
  existential witness only, and every leaf stays valid for all positive `X`. The row delay enters only through the
  rise timeout `6Δ + ΔF ≤ 4Δ·δ_t`, paid by `3c ≤ δ_t`; the transport runs at the actual protocol FG delay
  `protoFGDelay` (`FinalQuery.hsSharedUpTo`).
- **Other routes.** The first-crossing/bounded-crossing assembly (`[0, δ_t − 1, δ_t + 1, δ_t + 3]`, `δ_t ≥ 4`) is
  retired. The two-proposer route (route B) is parked: it has no proved supplier.

## Trusted surface and Challenge scope

- **Challenge certifies exactly seven statements**: the five generic review statements
  (`Review.ObligationsSufficient`, `ObligationsSufficientOn`, `RegimesRealizable`, `LogFaithful`,
  `HeldIffServed`), and the Goldilocks endpoint and headline, `MeetsObligations` and `GoldilocksCorrect`
  (§"Adversary growth"). Reason: keep the trusted surface to the generic definition
  of a correct protocol plus the one instance endpoint and its headline. The other Goldilocks milestones (M₁, FGStore, ACBase, ACSteps, Compose, Persist, Regimes,
  Service, Healing) are means to the endpoint, not claims a reviewer must read.
  - They stay proved and built as ordinary lemmas, but are not comparator roots and not trusted: their statement
    modules, and every declaration of the instance Spec that only they reach (a compiled walk of the statement
    closure of the six roots, types and definition bodies, not proofs), live with unchanged names and bodies in
    the untrusted `Instances/Goldilocks/Milestones/` layer family. It mirrors the Spec/Statements sub-layers, so the
    allow matrix carries over; it allows `@[expose]` (the statements are unfolded by their proofs and tests) and no
    `sorry`, which is why it is not `Lemmas`.
  - What the six roots reach stays in `Spec/`, `Statements/Obligations` and `AsChainShape.lean`, protected; a
    `protected` layer may import only trusted and protected layers (check-boundaries.py), so that closure cannot
    reach Milestones.
  - The milestones stay gated: `ConsensusLeanTest/MilestoneAxioms.lean` states and axiom-pins each, and check.sh
    step 3b audits the closure of the `proved_milestone_modules` like the solution's. Their mapping rows read
    "proved (lemma)".
- **The certified pair is the growing-fault pair; the constant-fault pair is a milestone statement.** The swap
  moved the growing-fault statements `MeetsObligations` and `GoldilocksCorrect` from `Statements/Growing`
  (deleted) into `Statements/Obligations`, with unchanged bodies, and renamed the Challenge, Solution and
  comparator roots from `meetsObligationsConstant` and `goldilocksCorrectConstant` to `meetsObligations` and
  `goldilocksCorrect`. The constant-fault pair, `MeetsObligationsConstant` and `GoldilocksCorrectConstant`,
  unchanged in name and body, moved from `Statements/Obligations` to the leaf
  `Milestones/Statements/Obligations/Constant`, outside the trusted surface, in the untrusted, exposed
  `Milestones.Statements.Obligations` layer.
  Reason: it is a statement no root reaches, which is what the Milestones family holds (exposed bodies, no iff
  lemmas for its proofs and tests). The layer has no declaring `Milestones/Statements/Obligations.lean`, so no
  module with descendants owns a constant (noconst). `Review.ObligationsSufficientOn` stays a root; it states
  correctness on a class of runs, which the constant-fault rejection tests use. The certified pair implies the
  constant-fault pair: `Growing.meetsObligationsConstant_of_growing` (`Proofs/Growing/Obligations/Main`) and the
  test theorem `Obligations.Test.Constant.goldilocksCorrectConstant_of_growing`
  (`ConsensusLeanTest/Goldilocks/Refinement/Constant`).
- **The headline statement `GoldilocksCorrect`** is certified next to `MeetsObligations`: for every setup,
  assumption set and finite validator type, the Goldilocks family in the general execution model is an L0
  `CorrectProtocol` at `goldilocksContract A (contract_coefficients S A)`. It is the composition of
  `MeetsObligations` with `Review.ObligationsSufficient` (proved in `Solution` by `ShapeObligations.correct` of
  `meets_obligations`), with their parameters and no further hypothesis, so it adds no trusted reach: every
  constant it mentions is already reached by those two statements. It states the protocol's correctness in one
  place, so a reader need not compose the two statements.
- **The simulation interface and canonical trace are proof-side.** The Refinement simulation interface and the
  canonical trace construction are in the non-exposed `Lemmas/Simulation/{Interface,TraceDefs}`, with
  characterising lemmas for proof consumers; the digest adapter `dgOf` and the delivery relation `DeliverSeq` sit
  beside their only users there. Collision transport still targets the trace constructed from the engine run. The
  endpoint proof uses the construction and is axiom-audited; it is not material the endpoint's statement reader must
  trust. The milestone statements and this interface are placed differently on purpose: redoing the milestone
  modules with characterising lemmas would be a large diff for no gain in review surface.
- **Protocol instance files are trusted.** Every protocol instance's `Spec`, `Statements` and `AsChainShape.lean`
  are in `trusted_paths`, and their layers are `protected`, so check-boundaries.py requires them to be covered.
  Goldilocks is the only instance.
- **The Shape examples are not on the trusted surface.** `ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}`
  form one unprotected `Examples` layer. Reason: they are demonstrations of `Shape` (contract values with fit and
  tolerance proofs), not protocol instances, and no Challenge or comparator statement reaches them (a compiled
  inventory finds all their declarations outside the statement and proof closures of the roots).
  `Blocks.Pattern.range` and the `Recurrence.BadSlotSlack` decidability instance stay in `Spec/Blocks/Progress`,
  since `Lemmas/Blocks/Facts` and the tests use them too.
- **As much as possible stays off the trusted surface**: a definition that no Challenge statement needs moves to an
  untrusted layer, keeping its name and body. `cF` (the ratio gap) is an example: it lives in a test.

## Repository, toolchain and trust checks

### Foundations

- **Own repository**, Lean and Mathlib v4.35.0. License Apache-2.0, as the Verified-zkEVM Lean libraries (ArkLib,
  CompPoly, VCVio) and Mathlib; vendored copies keep their own licences.
- **Rules about the project's structure rest on external precedent**, not on the authors' own projects.
- **One certified library** `ConsensusLean`, with layers as module prefixes and a source-level boundary checker
  with one configuration (`scripts/boundaries.toml`) instead of Mathlib's `directoryDependency`.
- **`import all` only in tests.** Whole-file `@[expose]` in Spec and Statements (and the Milestones layers); none in
  Lemmas, Proofs and `Main`, so a proof edit rebuilds one module.
- **Proof debt as in FLT and Carleson**: `sorry` only under `Lemmas/` and `Proofs/`, never an axiom; certified
  means the closure of `Solution`, audited on every change; kernel replay and the comparator run nightly and at
  milestone acceptance.
- **Depth, cones and critical path are reports, not gates**; the one-module rebuild property is a canary; chains
  are allowed inside a milestone.
- **A light roadmap with checked names** (`docs/roadmap.md`) rather than a blueprint; leanblueprint becomes worth it
  with a second instance or outside contributors. The Spec package split waits for reuse outside the project.

### Checks

- **Trust checks reuse existing tools** (EthLib check-decls, leanchecker, `#guard_msgs` axiom pins, `lake check`,
  `lake comparator`, axiom-audit) with thin glue; a home-grown checker was abandoned. turbo-lean is optional, for
  per-declaration re-checks only. `lake check` and the comparator run in a bubblewrap sandbox, which is installed
  where the full checks run (the `full` workflow and the development setup); without it they are skipped and
  listed as CI-only.
- **CI is GitHub Actions.** `check` (`.github/workflows/ci.yml`) runs the fast tier and the review boundary on
  every pull request and every push to `main`; `full` (`full.yml`) runs the full tier nightly, on
  `milestone*`/`release*` tags and on demand. Green CI is the GitHub check of the commit; full-tier certification
  is a passing `full` run of the named commit. Reason: the standard public runners are free for a public
  repository, and a fresh hosted runner is the sandbox for a head's code. PRs run on `pull_request` (never
  `pull_request_target`) with a read-only token and no secrets.
- **Commit emails are checked against a public allowlist.** `scripts/check-commit-emails.py` checks the author,
  committer and `Co-authored-by:` addresses of every new commit against `scripts/commit-emails.toml` (GitHub
  `users.noreply.github.com` addresses and the named service identities); it runs in `check` on every PR and main
  push and in `scripts/push-main.sh` before the push, and a failure names the commit and field, never the address.
  Reason: no private address is ever written to the repository or a log. CI detects an upload after the fact;
  push-main stops a landing before it.
- **Trusted-surface changes are recorded, not gated.** Every non-merge commit that touches a path of
  `trusted_paths` carries a line `Trusted-surface: <what changes and why>`, checked by `scripts/review-boundary.sh`.
  Reason: there are no review gates; the line keeps every trusted change visible and is machine-checked.
- **There is no `.github/CODEOWNERS`**: Code Owner review would be a review gate.

## Comparison properties

- **An untrusted layer of comparison profiles.** `ConsensusLean/Comparison/` states bound functions over
  environment parameters (`Bound Q := Q → WithTop ℕ`, a `ΔAC`-coefficient per point, `⊤` for no claim) and the
  claims they bound; `Proofs/Comparison/` proves its order lemmas and the defaults from the contract, and
  `Instances/Goldilocks/Milestones/Statements/Comparison/` holds the per-protocol statements. It imports only
  Init, ToMathlib, Core and Spec, is outside `trusted_paths` and holds no `sorry`. Reason: comparing two
  protocols' proved guarantees pointwise needs a fixed vocabulary of run classes and bounds, which no Challenge
  statement reaches.
- **Bound inputs are environment quantities only.** A bound reads a parameter point (incident length, fault cap,
  asynchrony class), never a run's trace or outputs, and the run class of a point mentions no bound, so two bound
  functions are compared on the same runs. Reason: a class that depends on a bound would let a candidate choose
  its own domain.
- **Monotone bounds, ordered by class inclusion.** Each parameter type has a coordinatewise order, a lemma proves
  that it implies inclusion of the run classes, and every profile requires its bounds to be monotone in it, so
  `bX ≤ bY` pointwise means "never worse". Reason: the order is not defined as inclusion itself, so the
  coordinate reading and the class reading cannot drift.
- **Coverage is a separate obligation.** For every feasible point with a finite bound, a valid, excuse-free run
  attains the environment parameters with the claim active (`HealCoverage0`). It is not a field of a profile, and
  the defaults from the contract give only the implication fields. Reason: the contract's realizability gives
  witnesses at fixed points with silent adversaries, not at every parameter value.
- **Profiles are per capability and index.** A profile is stated at the contract's `(cap, i)`, whose heal and
  latency coefficients it bounds. Reason: a bound shared by every index has no finite default for a contract whose
  heal coefficient grows with the index (Goldilocks' grows with the outer gap).
- **The protection class is the contract's outage without its arming lag, at common numbers.** `ProtClass` keeps
  `OutageNet`, η-sleepy participation, `NoSleepOn` and `CohortOn` on the retained view, and adds a lower bound `A`
  on the cohort; the budget, the windows (η, noSleep, cohortAhead, ahead), the sleepy threshold θ and the
  catch-up are coordinates of the point, so the class and the profile read no contract, and the arming lag is the
  profile's bound `ℓ`, a premise of the claim. The profile is per source output, not per index (`persists` has no
  index). Coverage is split: domain coverage asks a representative with cohort at least `A` and at most `fcap`
  faults, boundary coverage asks exact `A` and `fcap`, for `fcap < A` and `θ·(A + fcap) < A`; both ask only at
  realizable thresholds `0 ≤ θ < 1`, since the class is empty at `θ ≥ 1` (a finite bound there is a vacuous
  implication and is never ranked). Reason: numbers taken from the contract would rank two protocols on different
  classes and different ready readers; dropping `CohortOn` would drop the faults-plus-late-wakers margin, and a
  cohort of exactly `A = 0` is unattainable under it, so the contract's `persists` row is the `A = 0` column of
  domain coverage at the contract's numbers.
- **The retention offset of the cohort is fixed by the protection order.** The order lets the look-back η, the
  sleepy look-ahead and the threshold θ decrease (participation premises that strengthen as they grow), the
  catch-up decrease (a longer one leaves fewer ready validators: a stronger premise and a weaker claim) and, at a
  fixed `noSleep + cohortAhead`, the no-sleep margin decrease. Reason: a later retention point strengthens
  `CohortOn` but weakens `NoSleepOn`, which constrains only the validators honest at that point (a validator
  compromised between the two points may fall asleep inside the window), so neither direction includes the
  classes.

## Open questions

- **Sleepy row-independence.** Do the sleepy claims hold at every `ΔFG > 0`, as `System.Sleepy` (no ratio) states,
  for every family? Goldilocks's `sleepySafe`, `sleepyLive` and `persists` are proved with no ratio premise, for
  each positive `ΔFG`, in the two-bound model (`Obligations.meetsObligations_exists`, standard axioms). That model
  still imposes finite row delivery at `ΔFG`: `System.Sleepy` contains `PSync 0` and `System.Outage` contains
  `OutageNet`, whose `fgAtts` clause delivers rows by `ΔFG`. This is not independence from any row-delivery
  assumption, and it does not allow unbounded or missing delivery. Generically the question is open.
- **All-occurrences provenance.** Collision transport targets the constructed trace; provenance over all
  occurrences, including refused calls and non-honest nodes, is not stated.
- **The first part of claims HS.3** (§"Goldilocks model choices"): neither a proof nor a counterexample is known.
- **Contracts whose numbers depend on the run's delays**, rather than fixed `ΔAC`-coefficients, are deferred.
