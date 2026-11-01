# SA status

## Derived roots (I9) — 2026-09-29

Plan I9 makes block roots derived. See the dated I9 note in
`CONTRACT.md` and the I9 entry in `GRIDCO-STATUS.md`. SA reuses the
Grid CO `propose` (`Model/Protocol.lean:85`), so honest proposers use
body 0. `Block.root_injective` holds for every block, so the
`RootInjective` premise of each regime is a theorem
(`rootInjective_all`). The regime field stays; its removal is a later
plan (plan I9 D6). No SA statement and no SA model file changed.
`Tests/Axioms.lean` also prints the five Grid CO theorems of I9.

## Receipt relay — 2026-09-28

The contract now uses DC receipt relay. The previous accepted-object
regime fields are removed. The earlier round notes below describe the
old premise. See the dated relay note in `CONTRACT.md`.

The shared `ReceiptRelay` proof gives strict stamps for in-window
membership or equivocation. `Paths` proves causal checked block receipt.
`CrossView`, `Snapshot`, `TransferViews`, and `MergedViews` use the reverse
alternative to transfer surviving supporters exactly. `ScoreExtension`
and `ProposalTransport` preserve counts and scores while permitting
unequal vote sets. SA keeps the same adapter, constants, and conclusions.

Validation: `lake build` passes all 3,558 default jobs with no errors or
warnings. The public bundle, fast P1, and new receipt/score bridge
`#print axioms` checks use only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, or new axiom was added. All requested
conclusions are proved under receipt relay. No task remains open.

_2026-09-27. Contract Draft 4.3. All contract claims are proved._

`AvailableChain.SA.saContract_from_engine` in
[`Proofs/Contract.lean`](../AvailableChainSA/Proofs/Contract.lean) proves
`SAContract p G E`. No claim remains pending.

`AvailableChain.SA.fastP1_from_engine` in
[`Proofs/FastOutage.lean`](../AvailableChainSA/Proofs/FastOutage.lean)
proves the main bundle field `stableResilientFast`. The fast lag is `4Δ`.
It requires `h_t ≥ τ` at every `0 ≤ t < b₀`, with all other Outage
premises retained. It does not retain the slow lag.

## Constants and premises

The model requires `n ≥ 1`, `k ≥ 2`, `Δ > 0`, and `η ≥ 0`.
The bundle requires `G > 0` and `E.Δ = p.Δ`.

- `τ = ⌈n/2⌉ = (n+1)/2`, with integer division.
- `θ = θrec = 1/2`, `recoveryFull = false`.
- `D_c = D_s = D_f = 6Δ`.
- `L = (4k−1)Δ`, `A_slow = 4(k−1)Δ`, `A_fast = 4Δ`.
- `Π = min(η,L)` and `ρ = 2L + G + 8Δ`.

Every run premise comes from Draft 4.3, including `RootInjective`.
After I9 (2026-09-29), `RootInjective` is a theorem
(`rootInjective_all`); the field stays.
There is no added support, view, lease, or repair assumption.
Draft 4.3 adds the fast arming constant and fast P1 field.

## Rules and shared engine

The source is `slow-arming.md` §§2–5, with the clarifications in
`sa-redteam.md`, under
`/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/`.

`Model/Protocol.lean` imports the Grid CO engine. Its shared `LeasePolicy`
parameter selects Grid CO or SA. Grid CO is the default. SA selects one
release level and stores raw results in `State.genuine`, including empty
and vetoed results. A saved label cannot be overwritten. The slow test
requires every preceding label in the full window and containment of
the same prefix. The current result supplies the last label.

Stable writes do not require lease admission. Each non-genesis prefix
passes its own fast or slow test before acquisition or renewal. The
shared map keeps the maximum deadline, expires at equality before HEAD,
and releases at the same fixed threshold. Release and expiry retain
both the public record and saved history.

`Params.engine` supplies the existing parameter type through a dense-grid
adapter. That grid is unused by SA admission. It adds no SA parameter
or run premise. Both exposed outputs read the same stable record.

The clock, receipts, stamps, paths, frozen and merged views, transfer,
genuine history, clean safety, and clean inclusion proofs are shared.
The shared map proofs now accept either admission policy. Grid-specific
row-source and contract theorems remain available.

## Proof path

- `Proofs/Basic.lean` proves constant validity, nesting, the fault bound
  `a < τ`, and the exact slow-window expiry equation.
- `Proofs/Clean.lean` applies the shared clean proofs to SA. Plain Sleepy
  gives safety, monotonicity, and `6Δ` inclusion. Thus the stronger stable
  and fast inclusion regimes also satisfy the bundle.
- Shared `Proofs/RawHistory.lean` proves exact saved-result origins and
  retention at later honest inputs. It includes sleeping readers and
  empty results. Shared `RowOrigins.lean` tracks each exact deadline and
  its actual admission test.
- `Proofs/SlowWindow.lean` connects the saved window to actual raw gates.
  Same-label compatibility excludes recent conflicting writes. Older
  conflicting rows expire before the final transfer HEAD, at equality
  when necessary. Qualifying sources retain support after lease release.
- Shared `Proofs/LocalTransfer.lean` proves transfer from a reader's own
  early and frozen views without a relay premise. `Proofs/Outage.lean`
  uses it for the pending healthy HEAD. Records stay fixed until that
  pending gate completes the slow window. The new row then protects the
  prefix through the remaining outage. No prior covering lease is assumed.
- `Proofs/FastOutage.lean` proves admission at `τ` from the high honest
  count and uses the shared completed/pending lease bridge.
- `Proofs/RecoverySupport.lean` proves support for fast and slow sources.
  For a synchronous starting label `b`, all sources that can remain live
  after HEAD `b + 2k − 1` have permanent support. The shared proposal
  repair and repaired-suffix proofs then apply. `Proofs/Recovery.lean`
  proves the exact bound `2L + G + 8Δ`.
- `Proofs/Contract.lean` constructs every field of `AvailableChain`.

## Contract issues

None. No missing premise or checked counterexample was found for the
requested claims. The fast P1 field uses the full-prefix honest
count premise. General P1 handles a lease that is first written after
outage onset; it does not assume that the lease already exists at onset.

## Validation

All SA proof modules, including `saContract_from_engine`, compile.
Eight kernel-checked Boolean smoke tests pass: stable write without a
lease, fast admission at equality, slow admission, empty and missing
labels, vetoed result retention, ancestor-only renewal, release at
equality, and expiry with retained record and history.

`lake build --wfail` passes all 3,430 jobs with no warnings. This includes
`gridContract_from_engine`, the existing witnesses and smoke tests, the
new SA library, and the 68-theorem audit in `Tests/Axioms.lean`.
Every audited theorem uses at most `propext`, `Classical.choice`, and
`Quot.sound`. The audit includes both complete bundles and fast P1.

No proof remains pending. No `sorry`, `admit`, project axiom, or
`native_decide` is used. Scratch files were removed. No commits were made;
`state.md` and `log.md` were not changed.
