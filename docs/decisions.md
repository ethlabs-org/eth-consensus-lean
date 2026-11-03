# Design decisions (summary)

A summary of the design record. The full record, with the reasoning, reviews and research behind each line,
is in the team workbench (private): the [consensus-lean index][index] (decisions, plans, research, experiments
since the move to this repository) and the earlier [layers plan][layers] (iterations 1–6 of the generic
definition). Coordination decisions are in this repository's issues. Each line gives the date, the decision and
where it is recorded; "Francesco" marks the owner's decisions.

[index]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/consensus-lean/README.md
[layers]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/layers-plan.md
[plan]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/consensus-lean/plans/foundation-plan.md
[validation]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/consensus-lean/research/foundation-validation.md
[rebuild]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/consensus-lean/experiments/module-system-rebuild.md
[checkers]: https://github.com/ethlabs-org/workbench/blob/goldilocks/main/repos/goldilocks/notes/generic-interface/consensus-lean/research/reuse-checkers.md

## What a good protocol is

- 2026-11-04, lead (phase 2 of half-open delivery; W2's card `cards/coefficient_tightening.md`):
  with `Δp = Δe` the Goldilocks contract numbers are the node numbers: catch-up `19`
  (`18Δ + 1 ≤ 19Δ`), latency `4X + 6` (available, stable) and `4(X + 3·cF r) + 1` (final), lag
  `4k + 6`, no-sleep `4k + 6`, recovery `9`, heal `catchUp + M_f` with
  `M_f = 24 L_drain + 8k + 52δ_t + 52X + 44` (563 at `k = 2, X = 1, δ_t = 6`, was 1312). The
  budget stays `4k − 6` (the node's phase-sensitive (V), `acceptance_outage_times`); `4k − 5`
  is optional for Francesco. Every number moves toward stronger claims except catch-up, which is
  mixed: more ready readers, but the healthy progress window (`healthyLive`, `healedSafe`,
  `prog [ready, …]`) starts `18Δ` earlier, so those rows are incomparable with the old ones
  (catch-up is a guarantee coefficient, Francesco 2026-10-31). No-sleep `4k + 6` no longer covers
  `catchUp + 1` for `k ≤ 3`; no proof uses that relation. Supersedes the numbers of the entries
  below (catch-up `37`, heal
  `catchUp + 2M + 3`, lag `8k + 12`, no-sleep `max 38 (8k + 16)`, recovery `18`).
- 2026-11-04, Francesco (option (a) of the Δ transport study, workbench
  `cards/delta_transport_study.md`; lead-approved plan `cards/delta_halfopen_plan.md`): **half-open
  delivery**. `CommLog.PSync`/`SyncUntil` hold a message strictly before the bound (deadlines
  `max a g + Δ − 1`, `a + Δ − 1`, and `− 1` for rows), the paper's `[τ, max(τ, w) + Δ)`; so the
  Goldilocks transport is `Δ_p = Δ_e` and `ΔF_p = ΔF_e` (`Setup.params`, `rowDelay`, `cF_spec`),
  superseding the #107 `Δ_p = Δ_e + 1` (2026-10-31). `Realizable` and `RealizableActive` quantify
  over `Δ > 1` and `ΔF > 1` ("just state Delta > 1"): at `Δ = 1` half-open delivery is same-time
  delivery, which no protocol-agnostic eager log meets. Behaviour still covers every `Δ ≥ 1`.
  Direction: `Delivers` at `dl − 1` implies it at `dl`, so `PSync`, `SyncUntil` and `OutageNet`
  become strictly stronger premises, and with them `Sleepy`, `Healthy`, `Outage`, the prefix
  lemmas and the Baseline healed prefix; every Behaviour row, and so `Good`, `AcceptedGood` and the
  Accepted endpoint, is weaker at each fixed `Δ` (it covers the runs that deliver by `Δ − 1`), the
  paper's reading. Phase 1 keeps every contract coefficient (they over-cover); tightening is
  phase 2.
- 2026-11-02, Francesco, lead-approved design (two-bound network, revision 3): **two delay
  bounds**. `Env` and `Public` carry the message bound `Δ` and the row bound `ΔF` (both positive,
  neither bounds the other). The log carries the protocol's message class (`CommLog.row`, filled
  only from `Protocol.isRow` by `Model.Run.log` and `Model.tagLog`); `Delivers` serves rows within
  `ΔF` (`rows`) and every other message and every transaction within `Δ` (`msgs`, `txs`; strictly
  before the bound since 2026-11-04): no statement may claim a block or vote within `ΔF`, and when
  `ΔF < Δ` rows may overtake blocks.
  Contract units option A: `Params.rowRatio r ≥ 1`; only `System.Healthy` assumes `ΔF ≤ r·Δ` (an
  upper envelope for the coefficients, never a deadline; a larger `r` weakens the premise). Sleepy
  and Outage carry no ratio and so cover every `ΔF > 0` (a weaker premise, stronger claims);
  sleepy row-independence is an audit question still open, and `η` stays as it is (its fixing is
  a separate contract change). **Inherited semantic change, lead ruling 2026-11-02:** the
  baseline sheet's weak-continuation premise (`WeakPremise`, `Statements/Baseline.lean`: healthy
  up to the heal point, without the ratio) keeps its text and gets no ratio, and its targets
  `weakSafe`, `weakInclude`, `weakGrow` (each with premise `WeakPremise ∧ gProg`) are not
  weakened. Its meaning changes: its `PSync` now holds the family's own rows (`isRow`) to
  `max a gst + ΔF` with no ratio, and its healthy part is `HealthyOn`, so the pre-heal phase is
  unbounded in `ΔF` too. It newly admits runs with `ΔF > Δ` whose rows arrive after
  `max a gst + Δ` but by `max a gst + ΔF`; at `ΔF < Δ` the row deadline is tighter, so the
  premise is not uniformly weaker; for a family without rows nothing changes. The targets keep
  their `Δ`-denominated times and must now hold with rows slower than `Δ` by any factor. They
  are targets (bare fields of `GoldilocksExtraAt`; the node-level R.6 `WeakSafe`, `WeakInclude`,
  `WeakGrow` are unproved), not proved here; `weakPremise_inhabited` is a satisfiability witness
  at `ΔF := Δ` only. Whether they hold at `ΔF ≫ Δ` was an open audit item (moot since the sheet was archived,
  2026-11-03); a plausible
  risk, not a counterexample, is that AC recovery after GST may need FG rows, now unbounded before
  `gHeal`. A counterexample would go through the believed-false process, with the statements
  unchanged. **Node level:** `SyncOn.deltaF` and `SyncBefore.deltaF` change from `Δ ≤ ΔF` to
  `0 < ΔF`, which broadens every node statement built on them (`SyncRun`, `GSTRun`, `SleepyRun`,
  `HealthyRun`, the R.6 weak premises, `HSShared`, the Persist, Run and Service rows, the healing
  statements): they now admit `ΔF < Δ`, so their claims are stronger. The claims proved in
  `Solution` remain proved (check.sh step 3b, standard axioms); the bare ones (R.6, the open
  healing statements) are targets. Goldilocks: rows are standalone attestations and relay wrappers of
  attestations only; a mixed relay wrapper (attestations with a block or a vote) and the empty
  wrapper are delivered within `Δ` (Francesco's decision 2026-11-02, option (a)), so attestations
  bundled with a block reach the others within `Δ`. Protocol row delay `ΔF_p = ΔF + 1`, as
  `Δ_p = Δ + 1` (superseded 2026-11-04 by half-open delivery: `ΔF_p = ΔF`, `Δ_p = Δ`); the FG row gap at ratio `r` is `cF r = ⌈(r + 6)/4⌉` with
  `6Δ_p + ΔF_p ≤ 4Δ_p·cF r` (`cF_spec`). **Transitional (keep-green):** the Goldilocks contract
  keeps `rowRatio = 1` (`Params.standard`), so its healthy regime still requires `ΔF ≤ Δ`, the
  case Francesco ruled out as a final state; this is not the arbitrary-ratio port, which chooses
  `r` in the acceptance assumptions, adds `3·cF r ≤ δt`, and reworks the coefficients. Card:
  workbench `two_bound_network.md`.
- 2026-11-03, Francesco's request (lead-approved; read-back T-01a19b8a): the Goldilocks catch-up is a
  flat `accepted_catchUp = 37` (was `max 37 (8k + 4)`). No proof needs `8k + 4`: with the value
  changed, the whole build failed only in tests that pinned the old formula. Effects (identical
  for `k ≤ 4`; for `k ≥ 5`): admissibility holds; heal is lower by `8k + 4 − 37` at every
  capability (`128k + 112δ_t + 160X + 224`); latency is unchanged; the ready and heal points move
  earlier by the same amount, so `[ready, heal]` keeps its length; more validators are ready
  (shorter `cDur`), so the sleepy and outage participation premises are weaker (no-sleep and
  cohort unchanged). `sleepySafe`, `sleepyLive` (L0 `TxLive`; the shape-level
  `ProposalLiveReady` also relaxes the proposer's readiness) and `persists` are stronger.
  `healthyLive` (L0 `TxLive`; the shape-level `ProposalLiveReady` also relaxes the proposer's
  readiness) has a stronger premise (under `Healthy` every honest validator is awake from
  `max g 0`, so progress on `[ready_new, horizon]` implies it on the former `[ready, horizon]`)
  and a stronger conclusion. `healedSafe` has a stronger conclusion and a premise not comparable
  with the former one (its window `[ready, heal]` shifts earlier with the same length).
- 2026-11-02, Francesco (η = 0, coefficient lane): the Goldilocks outage regime is plain sleepy.
  `AcceptanceAssumptions.lookback` is removed, `acceptanceContract` keeps `Params.standard`'s
  `η = 0`, and the outage budget is `4k − 6` (was `min(lookback, 4k − 6)`). Statement impact:
  `Outage`'s participation premise `EtaSleepyOn θ (η·Δ)` becomes plain sleepy and its window bound
  `b₁ ≤ b₀ + budget·Δ` admits windows up to `(4k − 6)·Δ` (was `min(lookback, 4k − 6)·Δ`); both
  weaken the outage premise, so `persists` claims at least as much as before. Its proof used only
  the plain-sleepy consequence (`EtaReadyAbove.readyAbove`) and `budget ≤ 4k − 6`. This applies
  to the acceptance contract; the Baseline sheet is unchanged and still pins `η = eta ≥ 1`
  (OD-23), a stronger premise, so the acceptance claim is the stronger one.
- 2026-11-02, coefficient lane (lead-approved plan): the arbitrary-ratio contract. The Goldilocks
  acceptance assumptions choose the row ratio, `AcceptanceAssumptions.rowRatio : ℕ+`, passed to
  `Params.rowRatio` by `acceptanceContract`, so its healthy regime assumes `ΔF ≤ r·Δ` for that `r`.
  With `c = cF r`: `AcceptanceAssumptions.timeout` is `3c ≤ δt` (`six_le_δt` derived),
  `finalWindow A = [0, c, 2c, 3c]` (span `3c`) and `accepted_latency .final X = 8(X + 3c) + 2`; the
  nonfinal latency `8X + 12` and `accepted_heal` are unchanged (the row delay enters the reset
  envelope only through the rise timeout `6Δ + ΔF ≤ 4Δ·δt`, paid by `3c ≤ δt`). Provenance of
  `8X + 12` (workbench `confirmed_supply_row_use_audit.md`, at 03e10e76): the post-heal proofs do
  not consume the row-timing components, although their premise bundles still contain them; this
  is not a theorem that removes all row assumptions. The protocol row delay `rowDelay` is the instantiation of
  `ΔF` (`FinalQuery.hsSharedUpTo`, the healthy-query wrapper); the transitional lift
  `rowDelay_le_of_healthy` (`ΔF ≤ Δ` at `r = 1`) is removed. At `r = 1` the contract constants
  and the window are unchanged (`c = 2`, `[0, 2, 4, 6]`, `8(X + 6) + 2`, `6 ≤ δt`) and so are the
  proved claims; the transport now runs at the actual `rowDelay`, which differs from the former
  `Δ_p` instantiation whenever `ΔF ≠ Δ`. The route-A entry below records the `r = 1` constants.
- 2026-11-02, Francesco ("1. Yes 2. we should edit the spec in consensus-lean"): the full-tree
  fallback for an honest vote's head. `tryVote` walks the viable tree of `SA.voteDomain`: the
  voter block tree when its viable tree in the current frame is nonempty, else the whole frame
  tree. `voterBlockTree` keeps its frozen meaning, so `ViableAtVote` and every trusted statement
  are unchanged in meaning (coordinator decision after the T-6daee397 fidelity read, smallest
  trusted diff). Paper: workbench `outage_restoration_s5.md` §11 (f7f7dbb), §11.5 (3828c33);
  gate review e178adef; fixture e90575ed; audit a54316c.
- 2026-11-02, Francesco: the generic outage is slow arming only, with no absolute-majority
  participation premise. `System.Outage` drops `ReadyOfAll cover` and gains, after its existing
  conjuncts, `NoSleepOn a z` (no honest validator falls asleep in `[a, z]`, waking allowed;
  `a = b₀ − noSleep·Δ`, `z = b₁ + noSleep·Δ`, clamped to `[0, horizon]`) and `CohortOn a z`
  (faulty plus late wakers fewer than the honest validators awake at `a`; half of all is the lemma
  `CohortOn.two_mul_lt`). `Good.persists` protects every `Ready` reader from `b₁ + recovery·Δ`
  (`ProtectedReadyFrom`), replacing `ResilienceReader` readers from `b₀`. New `Params` fields
  `noSleep`, `recovery`. Accepted: lag `8k+12` (`(8k+12)Δe ≥ (4k+6)Δp`, the label before the
  outage label armed by `b₀`), `noSleep = max 38 (8k+16)`, `recovery = 18`. The pinned
  `FGSAParams` sheet (node Δ) follows: lag `4·lockK + 6`, `noSleep = max 19 (4·lockK + 8)`,
  `recovery = 9`. A2 (`outageWindow`) drops `ReadyOfAll` for the same relative counts on
  `[a, min b₁ horizon]`. `Params.cover` is kept (read by no regime). The node-level R.5
  statements (`Statements/Regimes/Outage.lean`, parked, off the Solution path) are unchanged. Cards:
  workbench `outage_slow_only_delta.md`, read-backs 5d5e354 and 9f5d6a3.
- 2026-11-02, claude-mac, owner direction Francesco ([#136]): route A for final liveness.
  `finalWindow` offsets are `[0, 2, 4, 6]` (span 6), `AcceptanceAssumptions.timeout` is
  `6 ≤ δt`, and `accepted_latency .final X = 8(X+6)+2`. The window coverage comes from the anchor
  route (`cacheCoverage_of_anchor_window_upTo`, WindowAnchorRoute.lean): honest proposers only at
  the four anchors, three gap-2 anchor steps, and `P₃.slot ≤ P₀.slot + δt`. Only this coverage
  lemma needs `δt ≥ 6`; the seed needs `δt ≥ 4`. `δt` is a fixed constant, independent of the
  honest-proposer gap X; tolerance keeps X = span+2 = 8 as an existential witness only, and every
  leaf stays valid for all positive X. Francesco does not gate this decision (agents decide); his
  earlier direction was a fixed δt, changed offsets, honest proposers only at anchors. The
  independent read-back on #136 passed for the workbench cards `route_a_gap2.md`,
  `window_start_h0.md`, `anchor_row_supplier.md` and `anchor_tick_ac_producer.md`. The old
  first-crossing / bounded-crossing assembly (`[0, δt−1, δt+1, δt+3]`, `δt ≥ 4`) is retired.
  Route B has no proved supplier.

- 2026-11-01, Francesco ([#17]): final liveness uses four anchors; the two-proposer route is parked.

- 2026-10-31, coordinator (outage coefficient correctness audit after #125).
  Accepted's engine-unit arming lag is `8k−8`, and its budget is `min(η,4k−6)`.
  The former `4k−4` lag fails already at Δ_e=1, Δ_p=2. The former `4k−5`
  budget can violate phase-sensitive (V): k=2, Δ_e=8, Δ_p=9, b₀=89 gives
  remainder 35 and duration 24, totaling 59 > lifetime 54, even with node arming satisfied.
  The corrected lag uses Δ_p≤2Δ_e; the budget reserves the full phase remainder
  below 4Δ_p. A universal Lean theorem derives the unchanged node `OutageWindowTimes`
  from the concrete contract's times. This strengthens the advertised outage premises
  for correctness; it does not weaken (V), change lifetime, or prove network/participation
  transport. Positive integer engine delays and k≥2 suffice; no new caller premise.

- 2026-10-31, coordinator (#107 protocol-delay implementation; superseded 2026-11-04 by
  half-open delivery, `Δ_p = Δ_e`).
  The concrete family's `Setup.params` uses `Δ_p = Δ_e + 1`; its skeleton and node slot
  starts both use `4Δ_p`. The standalone node shape receives protocol parameters already
  chosen, so its grid uses `sp.Δ` without adding another unit. Generic network delivery,
  engine clocks, `SyncOn` and `SyncAC` are unchanged. The extra unit converts the inclusive
  engine endpoint to the strict node endpoint only; it budgets no relay delay and proves
  no actual row-production or network-to-node service obligation.

- 2026-10-31, coordinator (canonical collision transport, following #121).
  Protect the canonical trace construction in `Statements/Refinement/Trace`; keep its proofs
  in `Lemmas/Refinement/Trace`. Collision transport targets this constructed trace, not every
  arbitrary simulation witness: simulation coverage alone does not identify all block calls
  with engine objects. This deliberately narrows the transport target. Tagged genesis roots
  make freshness unconditional, so neither transport nor finalized accountability assumes it.
  All-occurrences provenance, including refused calls and non-honest nodes, remains OPEN;
  this interface correction does not prove accountability or add an Accepted premise.

- 2026-10-31, coordinator and spec read-back ([#118](https://github.com/ethlabs-org/consensus-lean/issues/118)).
  Separate finite observation coverage from labelled protocol-action coverage. `Trace.observationHorizon`
  defaults to `none` (legacy action-only horizon); `InHorizon` also admits a cut reaching a time covered
  by explicit finite metadata. Canonical traces set the engine horizon, clamp wakefulness to `[0,horizon]`,
  and stutter unlabelled at `horizon+1`. No engine premise, generic readiness condition, handler call,
  signing or duty is added. A valid one-validator, Δ=2, horizon=1 witness showed that the old filler could
  never supply the strictly later cut required by `sleepy_read_cut`.
  The horizon audit found six Healing consumers using only the retained cut/time bound, and three test
  constructors using labelled coverage (now injected into the action alternative). Canonical labelled
  cuts remain bounded by the engine horizon; `Simulates.covered` still covers actions only. Both component
  projections preserve observation metadata. Unlabelled padding alone is not a readiness repair.

- 2026-10-31, coordinator (Accepted existential guarantees, owner rule).
  Restore the concrete family acceptance root with fixed assumptions and
  existential finite catch-up, heal and latency coefficients. Standard fractions
  stay 1/3 and 1/2; final progress is the chosen local pattern at every positive
  outer gap X. The timeout package is fixed before choosing coefficients and
  independent of X. Outage lag/budget/look-back are not existential guarantees.
  Each numeric witness is a named OPEN leaf, shared by all nine claim adapters;
  admissibility, singleton progress fit and tolerance are proved separately.
  This is a proof skeleton, not a completed acceptance result, and does not
  revive the legacy consecutive-pattern or latency formulas.
  **Superseded by route A (2026-11-02, [#136], #141) for the final pattern:** the
  `finalWindow` and δt sentences below are historical; see the 2026-11-02 entry.
  Historical: current conservative `finalWindow` is [0, δt−1, δt+1, δt+3], with δt≥4;
  replace it in one place if a weaker two-anchor recurrence is proved. Its
  first-honest-descendant usable-row/earlier-justification supplier, inherited
  progress bootstrap, productive AC chain and cache acceptance remain OPEN
  (workbench healing-simple/four-anchor-window.md). The single-delivery-bound
  model maps Δ_F := Δ_p, giving c_F=ceil(7/4)=2. This is weaker than the
  intended network model: actual row delays in (Δ, Δ_F] cannot be represented
  (r9 instance-proposal §3.8). The canonical FG-row service bridge is a named
  OPEN transport obligation, not an additional Healthy premise.
- 2026-10-31, coordinator-approved ordered duty batches (#107). A selected
  protocol duty returns an ordered list of candidates, all signed by its own
  key in that duty's role. The existing `releaseAll` checks each candidate
  against the holdings left by successful earlier candidates; rejection does
  not retry or reorder the batch. This permits same-event parent-wrapper
  publication before a child's dependency check. Shape `pollBatch` defaults
  to the existing optional poll as a zero-or-one list; other shape handlers
  likewise compile to zero-or-one lists. No network or realizability premise
  changes. This interface extension is separate from installing the revised
  Goldilocks publisher. Delivery clocks need no change: `lastClock_deliver`
  and `now_eq_lastClock` already establish the receipt time from event order.
- 2026-10-31, concrete Goldilocks publisher (#107, implementation in progress).
  Successful block cuts, including own-proposal acceptance, enqueue signed
  timestamped wrappers. Duplicate/refused calls do not enqueue them. A durable
  node-root-to-wrapper map supplies the exact same-origin parent; the next
  selected poll drains the event queue in acceptance order through `releaseAll`.
  Missing non-genesis parents produce no candidate: a reachable-state invariant
  must exclude this case. Candidate construction is not successful publication;
  the five publication contracts still require actual prefix-guard and provenance
  proofs. Existing vote/attestation polling remains before the forwarding drain.
  No timing API or generic execution premise changes. The old singleton poll
  release analyses must account explicitly for forwarding releases and their
  additions to `seen`; they cannot be reused as equalities for the new batches.
- 2026-10-31, Francesco (contract assumptions versus guarantees). Loose numbers
  are acceptable for latency, healing time and catch-up guarantees, not as a reason
  to strengthen assumptions. Choose progress recurrence as weak as the proofs allow:
  no consecutive honest proposers. Final recurrence is a good window every X slots:
  two honest ready proposers separated within a bounded internal span, represented
  by a generic `.recur` pattern with gap X. X is arbitrary; δt may depend on the
  internal span, never on X. This supersedes both fixed gap 2 and the maximal
  single-proposer gap derived from δt≥a+c+g−1. Exact window offsets and service
  obligations await the healing owner's revised note.
  The family PR may leave final recurrence parameterized while that research
  continues, with δt ≥ c_F + a + k_F plus slack for fixed local service bounds;
  none of these local parameters may silently depend on outer X.
  Apply the same premise-minimization rule to the other family contract assumptions.
- 2026-10-31, coordinator-directed selected-duty repair (runtime boundary).
  Remove the proposer schedule from runtime `Params` and `FGParams`, rather than
  reindexing `Store`, `NodeState` and `ACInterface` separately. After receiver
  credential checking is assigned to execution validity, these runtime structures
  have no need to know the selected identity. Pass the schedule separately to
  node tick/proposal semantics and the statements that refer to the slot proposer;
  the simulation supplies it from the run's selection. Genesis uses a fixed
  validator index, not the slot-zero proposer. This requires propagating the
  schedule through node execution/grouping laws, but avoids repeated state
  transports and an arbitrary schedule hidden in runtime data. This is the chosen
  architecture. The migration builds with warnings treated as errors and its tests
  elaborate; trusted fidelity review and landing remain pending. The engine's
  `dutyStep` gates both state mutation and release on selection. Delivered-block
  proposer correspondence is an explicit `LocalRun.proposerCredential` obligation,
  including faulty signers; the canonical simulation supplier remained OPEN then (since proved:
  `simTrace_proposerCredential`, `Lemmas/Refinement/Run.lean`, used by `simTrace_goldilocksRun`).
- 2026-10-31, coordinator-directed selected-duty repair. Restart replay order depends
  only on validator count and genesis root: its data enumerates a frame's non-genesis
  blocks in parent order. It has no proposer or timing dependence. Indexing that data
  by these two values, and supplying it from `Setup` by validator count, preserves the
  actual sibling order when simulation parameters use the run's proposer selection.
  `ReplayOrder sp` remains notation for this proposer-independent type; no state transport
  or freshly chosen replay order is needed for a different proposer schedule.
- 2026-10-31, Francesco (coordinator-directed dependency repair). A single monotone
  holdings policy governs release and delivery. The engine releases a candidate only
  when its dependencies are already held, and valid receipts satisfy the same policy.
  The predicate is decidable and depends only on holdings and the object, preserving
  rehashing invariance; neither it nor protocol handlers receives the hash function.
  Other instances use the unrestricted policy. The canonical scheduler retains first
  releases rather than last duplicates, preserving dependency order at the same timestamps.
  Goldilocks's fresh child forwarding wrapper depends on the complete same-origin signed
  parent wrapper, not merely a raw parent hash. Carried references are recursively processed,
  not inert pointers. The pre-envelope dependency must already be held; nesting it in the
  current envelope does not satisfy that requirement. This differs from legacy `depsS`,
  which also required `parentFG.isSome`; accepted-parent and timely-processing conclusions
  remain protocol proof obligations. Source/time authentication, closure-to-prior-processing
  (or own acceptance), and store-to-seen/no-suppressed-release joins must be proved separately.
  No FIFO channel, retry queue or separate full-ancestry envelope is assumed.
- 2026-10-31, Francesco (coordinator decision, #107). The generic `TimeGrid` supplies an
  absolute positive slot length, and the skeleton supplies duty offsets in time units. Neither
  depends on network Δ generically; each instance constructs them from its public parameters.
  The generic progress and realizability proofs need only positive slot length, not scaling or
  divisibility by Δ. Existing instances retain their concrete slot and phase times.
  Goldilocks's subsequent family repair uses exactly Δ_p = Δ_e + 1, not 2Δ_e (superseded
  2026-11-04 by half-open delivery: Δ_p = Δ_e).
  Contract catch-up, heal and latency remain engine-delay coefficients; conservative numbers
  are allowed to simplify proofs, but the intended resilience fractions 1/2 and 1/3 stay fixed.
  This generic grid change does not yet change the Goldilocks family or its contract.
- 2026-10-28, Francesco ([layers plan][layers], "Iteration 6"). The generic layers define a good protocol as a
  fixed property table, each property with a fixed regime; an instance supplies only numbers. Precise protocol
  properties live in the instance's properties sheet. Layers: L0 problem, L1 model, L2 shape. The network is
  part of L0 (a communication log), and L1 proves once that its log is faithful (`LogFaithful`).
- 2026-10-28, Francesco (same). `stable := final` is not good: stable must be sleepy-live. The outage regime is
  η-sleepy; after an outage, every after-GST property applies (the outage end acts as GST).
- 2026-10-29, Francesco ([layers plan][layers], "Moved to consensus-lean"; README "Scope"). Healthy means full
  participation with faults below ⅓; liveness premises tolerate one bad proposer slot per window
  (`ProgressTolerant`); the sleepy stress witness keeps at most two honest validators awake; available and
  stable monotonicity stay conditional, final is unconditional; `available` may bind to `ac_confirmed`.
- 2026-10-28, Francesco ([layers plan][layers], "Iteration 6"). Goldilocks gets pinned numbers and a properties
  sheet now; the FG-SA migration comes later.
- 2026-10-29, claude-ethlabs ([#38]). That sheet (`Instances/Goldilocks/{Spec,Statements}/Baseline.lean`) is a
  pre-foundation baseline, **not approved**: no proof targets it until the first slice ([#10]) re-reviews it
  against the current Goldilocks spec (`docs/goldilocks-mapping.md`). The files of the instance semantics and
  statements (`Instances/<P>/{Spec,Statements}` as file and directory, `Instances/<P>/Refinement/Defs.lean`)
  join `trusted_paths`, and their layers are `protected` (check-boundaries requires the coverage), so every edit
  of those files is reviewed; the tag covers the sheet only as a frozen baseline. The Goldilocks import
  exception to `Main` is limited to the two `Baseline` modules. The sheet moved to
  `Instances/Goldilocks/{Spec,Statements}/Baseline.lean` (unchanged) so that milestone statements
  `Statements/<M>.lean` can sit beside it (check.sh step 4: a module with descendants owns no constants).
- 2026-11-03, Francesco (rule-cost sweep, workbench `cards/rule_cost_sweep.md`). **The Baseline sheet is
  archived**: `Instances/Goldilocks/{Spec,Statements}/Baseline.lean` and its tests (`ConsensusLeanTest/Goldilocks`)
  move to `archive/consensus-lean-baseline`, out of the build, the roots and the snapshots; their layers, the
  Baseline entries of the import exception to `Main` and their index entries go. It was never approved and was
  off every live path: nothing in the closure of `Challenge`, `Solution` or `Refinement.Accepted` imported it.
  The positive controls keep their own copy of its schema and skeleton (`Tests.Controls.ctrlSchema`,
  `ctrlSkeleton`). The open audit item on its weak-continuation premise is closed as moot.

## Repository, toolchain and trust checks

- 2026-10-29 ([index]). Own repository (history of goldilocks `contract/` kept); Lean and Mathlib v4.35.0;
  delivery is "normal": an honest send at `t` is held at `dl a` by every honest node awake throughout
  `[a, dl a]`, for every `a ≥ t` (wakers get messages by `u + Δ`).
- 2026-10-29 ([index], [checkers]). Trust checks reuse existing tools (EthLib check-decls, leanchecker,
  `#guard_msgs` axiom pins, `lake check`, `lake comparator`, axiom-audit) with thin glue; the home-grown
  checker was abandoned. turbo-lean is optional, for per-declaration re-checks only. bubblewrap is installed on
  the shared box, so `lake check` and the comparator run locally.
- 2026-10-29 ([index]). Rules about the project's structure must rest on external precedent, not on our own
  projects ([validation]).
- 2026-10-30 ([#41]). License Apache-2.0, as the Verified-zkEVM Lean libraries (ArkLib, CompPoly, VCVio) and
  Mathlib; vendored copies keep their own licences.

## Foundation plan (adopted 2026-10-29, all recommendations)

[The plan][plan]; adoption steps §11 are issues [#4]–[#11].

- One certified library `ConsensusLean`, layers as module prefixes, a source-level boundary checker with one
  config (`scripts/boundaries.toml`) instead of Mathlib's `directoryDependency` ([#5], [#6]).
- `import all` only in tests (D1). Whole-file `@[expose]` in Spec and Statements, none in Lemmas, Proofs and
  `Main`, so a proof edit rebuilds one module ([rebuild], [#8]).
- Proof debt as in FLT and Carleson (D4): `sorry` only under `Lemmas/` and `Proofs/`, never an axiom; certified
  means the closure of `Solution`, audited per PR; leanchecker and the comparator run nightly and at milestone
  acceptance ([#7]).
- Depth, cones and critical path are reports, not gates; the one-module rebuild property is a canary; chains
  are allowed inside a milestone ([#4], [#7]).
- A light roadmap with checked names now (`docs/roadmap.md`), leanblueprint later (trigger: a second instance or
  outside contributors). The Spec package split waits for reuse outside the project.

## Goldilocks instance

- 2026-11-03, Francesco: **`ac_to_fg` returns only `fg_confirmed`** (or `⊥`). Nothing read the
  returned head: the node discards it, and since loose BJ (goldilocks#14, 37fc02fe) the finality
  pair comes from `finality_pair(Λ, σ_e)` on the source's entry state. `ACInterface.toFG`,
  `SA.acToFG` and `Node.acToFG` lose the head component; requirement 1 (`ReqHeads`) drops the
  returned-head clause, requirement 2 (`ReqSource`) drops "the returned head extends it", and
  `Compose.SourceHeld` drops the same conjunct. A compiled scan found no consumer of either
  dropped fact, so they are dropped, not restated on `ac_head`. A0.6 (`InterfaceRequirements`) is
  weaker; the statements that assume `Requirements` are stronger (Compose/AnyAC `TipsNested`,
  `ProposalParentHeld`, `DutyHeadsHeld`; Compose/Node `ThreeTips`, `HonestBlockAccepted`,
  `ACStatesReachable`, `SourcesHeld`; Compose/Run `ACProjection`, `FGProjection`); `SourceHeld` is
  incomparable (weaker hypothesis and conclusion). The node and family S behave as before (only an
  unread return value went), and `AcceptedEndpoint` is unchanged. **The Lean is ahead of SPEC
  requirements 1 and 2 and claims A0.6** until the matching LaTeX edits land in
  `specs/goldilocks/tex/` (W1).
- 2026-10-31, coordinator-authorized R.5/OC repair ([#107](https://github.com/ethlabs-org/consensus-lean/issues/107)).
  **Pre-outage synchrony cuts off recipient deadlines, not send times.** `SyncBefore` requires
  service only when the recipient's protocol deadline, including its latest wake, is at most
  `b₀`. `OutageRun` and `OutageWindow` use it instead of `SyncRun 0 (b₀ − Δ)`; the latter still
  imposed obligations after arbitrary later wakes inside the outage. `SyncRun`, `SyncOn` and
  the generic `Outage` are unchanged. The cutoff is conservatively the protocol deadline itself,
  not its last admissible integer processing time: deadline `b₀` is covered, `b₀ + 1` is not.
  With `Δ_p = Δ_e + 1`, a qualifying protocol deadline leaves the engine endpoint at most
  `b₀ − 1` (superseded 2026-11-04: at `Δ_p = Δ_e` the half-open engine deadline itself is at most
  `b₀ − 1`). Later calls still check qualifying pre-outage deadlines; attestation deadlines use
  `Δ_F`. Strict processing bounds and send-time lower bounds are retained. This changes the
  premises of the still-unproved outage rows, not their conclusions. Acceptance relay remains
  an explicit obligation: receipt alone cannot invent acceptance of a discarded missing-parent
  block. No ancestry, Catch, R.3 or R.4 decision is encoded, and no transport proof is claimed.
- 2026-10-31, amp-orbs (architecture), transport repair under
  [#107](https://github.com/ethlabs-org/consensus-lean/issues/107).
  **Process received payload objects in preorder.** A delivery now traverses the entire object
  closure, processing a canonical block before its carried votes and attestations. Wrappers have
  no canonical node event; nested wrappers no longer hide their contents. The existing node
  handlers are unchanged, but their engine-driven invocation sequence changes: payload votes get
  actual message calls, including when the containing block is refused or silently dropped.
  This is intentional independent service of authenticated carried objects, not acceptance of the
  containing block. Block-before-payload preserves the existing block handler's priority (including
  any vote it emits); subsequent message handlers use the resulting state. The one-vote invariant
  applies to arbitrary same-time object lists, so one delivery poll still drains the emitted vote.
  This slice does not repair own-proposal payload processing, repeated-forwarding freshness under
  `Held`, or the finite-window transport. It does not weaken `SyncRun` or claim that transport is proved.
- 2026-10-31, Francesco ([#104](https://github.com/ethlabs-org/consensus-lean/issues/104), revised decision).
  **Drop cross-node nesting rather than restate it.** Remove Baseline's `crossNest` and `weakCrossNest`,
  R.3's `CrossNest` and R.6's `WeakCrossNest`, their bundle fields and the open `cross_nest_until` interface.
  Cross-node compatibility follows from `HealedSafe`/`WeakSafe` plus R.8's `OutputsNested`: a finalized
  read is below its node's confirmed read, which is compatible with the other ready confirmed read.
  The same-instant ancestry is false (#104's carrier-delay replay); lagged ancestry is not stated.
  This owner-approved target change supersedes the earlier decision to restate the Baseline fields in
  #106's lagged form. It does not change R.4's cross-time growth or R.8's local nesting.
- 2026-10-31, Francesco ([#107](https://github.com/ethlabs-org/consensus-lean/issues/107)).
  **Delivery-time relay in the generic engine; protocol delay `Δ_p = Δ_e + 1`** (the `+ 1` superseded
  2026-11-04 by half-open delivery, `Δ_p = Δ_e`; delivery-time relay stands). The extra unit absorbs
  only the inclusive engine deadline versus the strict spec deadline (`≤` versus `<`), not relay latency.
  Persistent relay at the next awake tick and even relay one unit late still break R.1 in the model;
  persistence across sleep alone is not enough. This supersedes the earlier next-tick `+1/+2` analysis and
  the proposed `Δ_p ≥ Δ_e + 2`. `SyncOn` and `SyncAC` stay unchanged. The Refinement transport from engine
  `PSync`/`SyncUntil` to spec `GSTRun`/`SyncRun` remains a proof obligation with delivery-time relay and
  the chosen delay, not a theorem supplied by this decision.
- 2026-10-30, amp-orbs (architecture), under the coordinator's criterion "the smallest trusted change that keeps
  every proved milestone's proofs intact" ([#17], Refinement). **The spec block carries the engine's input**: the
  engine hashes the whole header `(parent, pos, input, info)` and `compile` writes `input := encodeTxs mempool`
  outside the shape's `Info`, so two engine blocks differing only in `input` have different hashes but, without
  the field, one spec content; `RootOk` with one digest cannot hold of both, and the refinement cannot be stated
  faithfully. Chosen: (B) a field `input : Nat` of `Common.Block`, the digest over `(parent, slot, input, FG
  payload, AC payload)`, and the node's tick event carrying the input (`Node.Event.tick x`; `mkBlock` writes it;
  the AC never reads it). Rejected: (P) the input through the AC payload via `ACInterface.proposal`, which
  changes the generic AC interface, the SA payload pair and every `Lemmas/AC` file (16 proved files) and
  `Spec/SA`; (B) leaves `Lemmas/AC` and `Lemmas/FGStore` (generic in the block type, no block literals) intact
  and touches `Spec/Common/Block`, `Spec/Node`, `Spec/Run/Model`, the `Statements/Compose` files that pattern
  the tick, five `Lemmas/Compose` files and the Goldilocks tests. The spec folds the input into the AC payload
  (composition.tex: the AC fixes the encoding of its payload); the mapping records the field as that encoding.
- 2026-10-30, amp-orbs (architecture), Refinement statements ([#17]; `Refinement/Defs`,
  `Statements/Refinement`). **The Goldilocks node as a generic shape, simulated rather than equated.** The wire
  format and digest are the refinement's choices, not the spec's: `n`-independent bodies (the family needs one
  body type for every parameter set; a fixed-`n` body was rejected), canonical signed objects (a block's header
  carries the canonical objects of its payload, so the engine's view contains the evidence G1.5 needs), a digest
  from the engine's hash with the genesis root as a parameter (a header naming genesis by digest is dropped, so
  `RootOk` holds by construction). The step order is `[poll, poll, pollPropose, propose, poll, poll]`: the node's
  tick is the poll proposal step at the public times (a duty, so it runs only awake; putting it in `clock` was
  rejected since `clock` runs asleep), two leading polls release the bodies queued since the last tick so that a
  proposal carries only released objects (rejected: filtering own objects out of the proposal), the trailing
  polls run the FG update and drain the tick's vote and attestation. The family's state is a Goldilocks state at
  every proof of `1 ≤ n` (`FamilyState`; a `dite`/cast family was rejected). The simulation (`Simulates`) maps
  engine cuts to node cuts with a monotone `ι` and relates ticks, deliveries (`DeliverSeq`, one group per
  canonical object), restarts and releases; releases have the slack of the next awake tick (`ReleasedFrom`,
  `RelayedFrom`). Two gaps recorded, not stated: the proposer selection was a hypothesis (`SelIs`; the generic
  skeleton's `proposerSel` was one `SelSpec` for all slots, the shape cannot read the run's selection; the
  coordinator's decision: a per-slot selection in the generic skeleton as Refinement PR 3, [#93], then drop
  `SelIs`, so that engine-level Goldilocks theorems do not carry it; done, see the next entry); the network
  premises' transport
  (`Delivers` with `≤ max(a, g) + Δ` versus the spec's strict deadline; admission read as an instantaneous send
  versus the engine's relay at the next awake tick) is left to the regimes milestone.
- 2026-10-30, amp-orbs (architecture), per-slot proposer selection ([#93]; `Spec/Shape/Shape`,
  `Spec/Shape/ProgressFit`, `Refinement/Defs`). **The skeleton's proposer selection is per slot, and a
  recurrence still fits only a run-chosen proposer.** `Skeleton.proposerSel : Slot → SelSpec n`, so that a
  shape can fix its schedule (`fun s => .fixed {p s}`) or leave the choice to the run (`fun _ => .sized 1`); the
  other instances are unchanged (`fun _ => …`). `ProgressReq.Fits (.recur _)` becomes `∀ s, proposerSel s =
  .sized 1`: a `.fixed` schedule arm was rejected because the bad-proposer witness of `regimes_realizable`
  (`badSel`: a faulty proposer at the periodic slots `s % P = P − 1`) needs a schedule-side condition: under a
  round-robin schedule with period coprime to `P` those slots visit every validator, so the witness would need
  everyone faulty, and a constant schedule has no witness at all; with the lifted condition `regimes_realizable` stays proved (its witnesses specialise the
  fitting hypothesis per slot). Goldilocks' progress regimes are therefore stated in the instance (the claims'
  ready-proposer premise), not through `.recur`; its `Spec/Baseline` skeleton keeps `fun _ => .sized 1`. The
  Refinement skeleton sets `fun s => .fixed {proposer s}` (superseded by #117, ac3e8d5c: it is now `fun _ => .sized 1`
  with the run's proposer `runProposer`) and `SelIs` is dropped from `EngineSimulatesNode` and
  `FinalizedAccountable`; `selValid_proposer` (`ConsensusLeanTest/GoldilocksRefinement.lean`) derives the former
  hypothesis from `SelValid`. Baseline's `GoldilocksTarget` is not instantiated at the refinement family (its
  bindings name `goldilocksSkeleton` over `goldilocksSchema`, and a fixed schedule does not fit its `.recur`
  rows: a fixed schedule does not fit `.recur`, see above); the milestone statements are over `compiled (family S)` directly, and restating Baseline at the
  refinement skeleton is left to the first-slice re-review ([#10], [#38]) as a recorded gap.

- 2026-10-31, amp-orbs (architecture), delivery-time release in the engine ([#107], coordinator's decision
  option (a); `Spec/Model/{Protocol,Run,Conditions}`, `Spec/Shape/{Shape,Compile}`, `Spec/Problem/Network`,
  `Refinement/Defs`). **What a delivery makes a node emit, relay or acknowledge leaves at the delivery's own
  time.** A protocol has `deliverDuties : Time → List Duty` (default `[]`; a skeleton lists them as
  `deliverOrder`, default `[]`), and `Run.step` at `.deliver v o t` runs them on the processed node and then the
  gossip `releaseAll`, as an awake tick does; `releasesAt` has a deliver branch, `releases v o t` holds at the
  delivery's own time `t` through `Run.SendsAt` (a tick or a delivery of `v` at `t`), and `Unforgeable`'s
  earlier send may be a delivery. Reason: the protocol texts read an admission or a vote cast at a receipt as an
  instantaneous send (sa-protocol.tex "the network relays each accepted object"; fgsa-protocol Relay "use the
  acceptance time, also for … an asleep receiver"), the claims' proofs A1.2/C1.1 (`writer_pool`), A1.3
  (`fastLock_same_slot`) and A1.7 (`honest_vote_at_update`) and the Sleepy invariant rely on it, and the
  sa-fg-model showed that release at the next awake tick, or even one unit late, breaks R.1/S1 under a
  sleeping admitter while delivery-time release had no violation. Rejected: weakening `SyncOn`/`SyncAC` to the
  sender's first awake time (the proofs cannot absorb it), a gossip-only release at deliveries (a vote cast at a
  receipt would still wait), and votes carrying their head block (a spec change for an engine defect). The
  Goldilocks skeleton's delivery duty is one `.poll`, a drain: `fgDue` is false at every cut (set only by the
  tick's `pollPropose`), so a delivery emits at most the queued vote and the relay gossip and `signed_only_in_ticks`
  stands. `CommLog.EagerFrom.recv` becomes strict (`max t g < a`): the canonical schedule fixes the deliveries at
  `a` before the delivery-time releases at `a` exist, so those are served from `a + 1`. No `Statements/` file
  names `EagerFrom`; `Spec/Problem/Good.lean` uses it existentially (`Adequate.covers`, `HealthyLive`), so the
  strict form asks those witness runs for one receipt less (none at the send's own time), and every regime
  premise they serve (`PSync`, `SyncUntil`, `OutageNet`: deadlines at least `a + Δ`, `Δ > 0`) is still
  implied (`EagerFrom.psync`). The other instances' skeletons keep the default and rebuild unchanged. The Goldilocks `ReleasedFrom`/`RelayedFrom` and the six
  release and relay fields of `Simulates` are restated at the delivery time in a second PR.
- 2026-10-30, amp-orbs (coordinator), on the Regimes milestone (R.3). **Baseline's heal point is not raised to the
  proved bound.** The target pins `gHeal = max(g, 0) + (29 + B_H^F(k))·Δ` (from the FG-SA analysis); the only
  healing result, claims H.4, gives `T_heal = ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G_p + T_b`, far above it. R.3 is
  stated over the run at a heal point `T ≥ T_heal` (`Statements/Regimes/Healed`), with H.4's open premises (H.3
  (c)'s bridge, `(U_all)`, `(U_B)`) as named hypotheses, and with H.4's regime premises that the target lacks
  (`Catch(2Δ)`, `Prop⁺(G_p)`, the `δ_t` bound and the genesis root of `HSShared`); Baseline's `gHeal` is unchanged.
  Raising `gHeal` to H.4's bound would weaken the review target to fit the proof we have, which AGENTS.md rules out,
  and a larger proven bound is not evidence that `gHeal` is false. **Baseline R.3 at `gHeal` remains open; what is
  proved (once the proofs land) is R.3 at `T_heal` under those premises.** `gHeal` changes only with a
  counterexample (a reachable run that heals later than `gHeal`) or the owner's explicit decision (flagged to him).
  Model evidence (workbench#8 `sa-fg-model`, measured at `528a15c`, recorded in the README at `e406004`): 9,600
  `Healthy` runs (n ∈ {4, 5, 7}, k ∈ {2, 3}, δ_t ∈ {2, 3}; random, hostile and partition adversaries) all heal
  within their horizon and none after `gHeal`; the largest available heal time is 0.049·`gHeal` and the largest
  first-finality time 0.132·`gHeal`. The adversaries are not heal-delay optimizers and the horizons (128–224Δ after
  `ḡ`) are below `gHeal`, so this is no counterexample search.
- 2026-10-30, amp-orbs (spec), on the Regimes milestone (R.4), as for R.3 (coordinator's go-ahead). **R.4 is stated at
  a heal point, not at the target's numbers**: over the run at a parameter `T ≥ max(T_heal, ḡ + T_rec)` with the
  deadline `D_fin = 4Δ(W + 1 + M) + 2Δ` (claims C1.3), under R.3's premises and `UPat(W, M)` with `M ≥ M*`, the
  regime claims node O.1 is proved under (`Statements/Regimes/Final`). `UPat` is a premise the target lacks: the
  target asks for the contract's finality recurrence `gProg .final gf` only, and O.1's target for that premise has no
  statement (claims §"O.1", open). Baseline's `gHealFin`, `finalCut` and `W_W(gf)` are unchanged; **Baseline R.4 at
  its own numbers and premises remains open.**

## Process

- 2026-10-29, Francesco ([#2]). Claude (claude-ethlabs) and the Amp orbs push and merge their own green,
  reviewed PRs and are responsible for them. Process speed (build, CI, iteration, review load) is part of
  quality. Reviews are local, by model instances that did not write the change. All coordination lives in
  issues and PR threads, never in the tree.
- 2026-10-29, Francesco (`docs/spec-review.md`). The trusted surface is approved by the annotated tag
  `spec-approved`, which claude-ethlabs moves only on the owner's authorization (or for a verbatim move with
  machine-checked evidence, recorded in `docs/spec-review.md`).
- 2026-10-29, claude-ethlabs within that authority ([#21], `TRUST.md`). Check infrastructure (`scripts/`,
  `.github/`, the lakefile) is agent-reviewed: a change to what a trust check checks needs two independent
  reviews linked in the PR and a pointer on [#17]; other changes one, and a pure speedup also evidence that every
  check's verdict is unchanged (the same pass/fail on the fixtures). `.github/CODEOWNERS` names the owner for
  the trusted surface, the infrastructure and the mapping docs (plan §4), but Code Owner review is not enforced
  (enforcement through a ruleset stays open to the owner).
- 2026-10-30, Francesco ([#2]). No imitation of human review process: there are no review gates between agents.
  A subagent pass is a tool inside the author's own session. This replaces the review requirements of the
  entries above; a check-infrastructure change still carries its fixture evidence.
- 2026-10-30, Francesco ([#2]). **Nothing blocks on the owner**: he gives input and asks questions, and does not
  approve PRs, statements or tag moves; agents own every decision and record it where the work is.
  `spec-approved` stays, as an **agent approval**: an agent other than the change's author (claude-ethlabs, or
  the amp-orbs coordinator) moves it after the author's fidelity read-back and a green fast check; the tag
  message names the PR, the protected files changed and the evidence. This replaces the owner's authorization
  in the entry on `spec-approved` above. First application: #49 (`f98ed97`), moved by amp-orbs.
- 2026-11-01, Francesco ([#129]). **The `spec-approved` tag is retired while the work is active**: trusted-surface
  changes are recorded, not gated. They land through `scripts/push-main.sh` like any change; each commit touching a
  trusted path carries a `Trusted-surface: <what and why>` line (`scripts/review-boundary.sh` checks it), and
  push-main comments each landing on [#129]. This replaces the tag entries above; no PR and no second agent.
- 2026-10-30, amp-orbs (process), under that rule ([#50]). Trunk-based: after the local checks
  (`scripts/check-changed.sh`; `--fast --selftests` for `scripts/` or build-configuration changes), rebase on
  `origin/main` and push to `main`. CI runs on every push to `main`, and whoever made it red reverts at once. A PR
  only for a trusted-surface change, since the tag must cover its head before it reaches `main`. (Superseded in
  part: GitHub Actions is disabled, 2026-10-31, [#50], so box CI checks observed heads; the tag is retired,
  2026-11-01, so a trusted-surface change needs no PR.)
- 2026-11-04, lead (Francesco delegated it; rule-cost sweep item 9, workbench `cards/rule_cost_sweep.md`): **no
  owner-review enforcement**. The open "branch ruleset enforcing owner review" item ([#21], option 2) is closed: it
  contradicts "nothing blocks on the owner" (2026-10-30), and GitHub Actions is off. The step-12 check that
  `.github/CODEOWNERS` lists exactly `trusted_paths` and `codeowners_extra` (and the keys `code_owner`,
  `codeowners_extra`) is removed with its fixtures, since it guarded only that unenforced GitHub feature;
  `.github/CODEOWNERS` stays as an informational file. The trusted surface is still `trusted_paths`, recorded by
  `scripts/review-boundary.sh`; no other step-12 verdict changes.

## Open, for the owner

- Audit (two-bound network, 2026-11-02): sleepy row-independence: do the sleepy claims hold at
  every `ΔF > 0`, as `System.Sleepy` (no ratio) now states? Goldilocks's `sleepySafe`,
  `sleepyLive` and `persists` are proved with no `rowRatio` premise, for each positive `ΔF`, in
  the two-bound model (`Refinement.accepted`, standard axioms). That model still imposes finite
  row delivery at `ΔF`: `System.Sleepy` contains `PSync 0` and `System.Outage` contains
  `OutageNet`, whose `rows` clause delivers rows by `ΔF`. This is not independence from any
  row-delivery assumption, and it does not allow unbounded or missing delivery. Generically the
  question stays open.

[#129]: https://github.com/ethlabs-org/consensus-lean/issues/129
[#2]: https://github.com/ethlabs-org/consensus-lean/issues/2
[#50]: https://github.com/ethlabs-org/consensus-lean/issues/50
[#41]: https://github.com/ethlabs-org/consensus-lean/issues/41
[#4]: https://github.com/ethlabs-org/consensus-lean/issues/4
[#5]: https://github.com/ethlabs-org/consensus-lean/issues/5
[#6]: https://github.com/ethlabs-org/consensus-lean/issues/6
[#7]: https://github.com/ethlabs-org/consensus-lean/issues/7
[#8]: https://github.com/ethlabs-org/consensus-lean/issues/8
[#10]: https://github.com/ethlabs-org/consensus-lean/issues/10
[#11]: https://github.com/ethlabs-org/consensus-lean/issues/11
[#93]: https://github.com/ethlabs-org/consensus-lean/issues/93
[#107]: https://github.com/ethlabs-org/consensus-lean/issues/107
[#17]: https://github.com/ethlabs-org/consensus-lean/issues/17
[#136]: https://github.com/ethlabs-org/consensus-lean/issues/136
[#21]: https://github.com/ethlabs-org/consensus-lean/issues/21
[#38]: https://github.com/ethlabs-org/consensus-lean/issues/38
