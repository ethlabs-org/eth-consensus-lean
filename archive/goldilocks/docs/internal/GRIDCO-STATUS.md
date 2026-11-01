# Grid CO status

_2026-09-27. Contract Draft 4.2. All contract claims are proved._

`AvailableChain.GridCO.gridContract_from_engine` in
[`Proofs/Contract.lean`](../AvailableChainGridCO/Proofs/Contract.lean) proves
`GridContract p G E`. It constructs the common `AvailableChain` bundle
from engine proofs and the contract regimes. No claim remains open.

The bundle proves safety of both outputs, monotonicity under Sleepy,
nesting, all three honest-proposal inclusion claims, outage persistence,
and recovery. Both interface outputs read the stable record. Recovery
proves safety and inclusion from `GST + ρ`; its proof also establishes
monotonicity after record repair.

## Constants and premises

Let `L = (4m−1)Δ` and `K = |grid|`.

- `θ = θ_R`, `θrec = 1/2`, `recoveryFull = false`.
- `D_c = D_s = D_f = 6Δ`.
- Arming lag `A = 4Δ`; outage budget `Π = min(η,L)`.
- Proposer gap `G`; recovery bound `ρ = K(L+Δ) + G + 10Δ`.

The theorem requires `0 < G` and `E.Δ = p.Δ`. `Params` contains the
parameter conditions: `Δ > 0`, `m ≥ 2`, `η ≥ 0`, a finite grid of levels
in `[1,n]` containing 1, `1/2 ≤ θ_R ≤ 3/4`, and `gridMatchesTheta`.
The last condition requires the rounded level to exceed the faulty count
when the declared participation threshold holds.

Each claim uses its regime from the fixed contract:

- Sleepy starts at `GST = t₀ = 0`, with awake honest count above faulty
  count, synchrony, and accepted-object relay. StableSleepy adds the
  η-sleepy condition; Fast adds full honest participation and faults below
  one quarter.
- Outage requires healthy delivery, accepted relay, and both count
  conditions from genesis to `b₀`, plus the arming lag, budget, and horizon
  bounds. Delivery during `[b₀,b₁)` is unrestricted.
- Recovery permits an arbitrary prefix. After GST it requires synchrony,
  accepted relay, awake honest count above faulty count, honest awake
  opening proposers every `G`, and a horizon through `GST + ρ`.

All regimes require valid execution and `RootInjective` on genesis and
ancestors of blocks named by delivered or emitted proposal payloads.
The internal label, receipt, support, and repair invariants are proved
from these premises. They are not additional contract assumptions.

## Resolved issues

- **Draft 4.1: healthy outage prefix.** Participation conditions now start
  at genesis. This excludes the old pending-gate run whose honest readers
  slept before the protected read.
- **Resolved in Draft 4.2: block-root uniqueness.** The shared
  `RootInjective` premise excludes the old run with distinct blocks that
  had equal roots.
- **Broadcast hook.** A carried HEAD counts as handled only if its
  containing block enters the store. Rejected envelopes cannot satisfy
  broadcast through handlers that did not run.
- **Proposal repair.** Pre-proposal constrained accessibility alone was
  insufficient: release could remove its anchor. Clean history and the
  recovery source invariant now establish the ordinary proposal parent,
  roots after release, and gate permission. The refuted F5 field and the
  `GoldfishFacts` hypothesis structure have been removed.

The regime witnesses, sanity and accumulation witnesses, and Grid CO and
L* smoke tests remain in the default build. The old proof-interface
counterexamples and conditional constructors have been removed.

- **2026-09-29: E4 permanent exclusion (plan 1b, Task 1).** `gridCO`
  (and so `sa`) now has a real `excludes`: a HEAD that is not yet stored
  is excluded when its label is before the previous slot or its seat
  already equivocates at that label. Proposals are never excluded.
  `excludes_head_iff` and `excludes_proposal` fix the definition;
  `excludes_inert` and `excludes_stable` show that `admitVote` refuses
  these HEADs for good. `excludes_stable` uses the valid schedule,
  because the old-label test needs a clock that does not move
  backwards. The five relay lemmas that used `excludes = false` by `rfl`
  now take the premise "not excluded up to the cutoff".
  `Proofs/WindowMargin.lean` proves that premise for each caller: before
  `proposalTime (r + 2)` a label-`r` HEAD is excluded only for
  equivocation, and each caller's cutoff is at most `gateTime r`. The two
  callers that relay a HEAD of any seat take the equivocation outcome
  that their conclusions already allow. No contract statement changed.
- **2026-09-29: derived roots (I9).** The honest root formula
  `s * (parent.root + 1)` is removed. A block has a body, not a root, and
  `Block.root` computes the root from the content. Honest `propose` uses
  body 0 (`Model/Protocol.lean:292`). `Block.root_injective` holds for
  every block, so the `RootInjective` premise of each regime is a theorem
  (`rootInjective_all`). The regime field stays. `rootInjectiveBelow_all`
  proves `RootInjectiveBelow` for every tree. The four lemmas of
  `Proofs/Roots.lean` that take `hroot` keep their statements; the
  removal of that premise is a later plan (plan I9 D6). The parent check
  of `admitProposal` is the dependency lookup by root
  (`blockKnown_parent_slot_iff_root`), and a proposal with an unknown
  parent leaves the state unchanged (`admitProposal_missingParent`). One
  statement changed: `honest_proposal_views` now states
  `B = .node parent s 0`. `excludes` did not change. SA gets the same
  changes. Validation after I9: `lake build --wfail` passes all 3,629
  jobs with no warnings (2026-09-29, I9 Task 11).

## Validation

`lake build --wfail` passes all 3,603 jobs with no warnings (2026-09-29,
after plan 1b), including
the new SA instance. Shared engine proofs now support either lease policy;
Grid CO keeps its original admission rule and constants. All six Grid CO
Boolean smoke checks and both L* checks pass. `#print axioms` for
`gridContract_from_engine`, the only public theorem in `Proofs/Contract.lean`,
reports only `propext`, `Classical.choice`, and `Quot.sound`.
