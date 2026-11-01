VERDICT: ADOPT WITH CONDITIONS

```text
┌─────┬──────────┬──────────────────────────────────┬──────────────────────────────────┐
│ id  │ severity │ evidence                         │ fix                              │
├─────┼──────────┼──────────────────────────────────┼──────────────────────────────────┤
│ O1  │ MAJOR    │ Design:944–946 adds an input      │ Version the new floor. Revise    │
│     │          │ floor claim. Plan1b:402–404 still │ candidateOfAc43 and the positive │
│     │          │ uses the old Candidate bridge    │ I1 witness to state explicitly   │
│     │          │ and positive I1 witness.         │ which floor they concern.        │
├─────┼──────────┼──────────────────────────────────┼──────────────────────────────────┤
│ O2  │ MAJOR    │ Design:330–336 requires           │ Reserve these interfaces in 2a, │
│     │          │ NoRestart and durable for the    │ or make lift revalidation after │
│     │          │ lift. Restart and input arrive   │ 2c a Phase 2 acceptance item.   │
│     │          │ in proposed stage 2c.            │                                  │
├─────┼──────────┼──────────────────────────────────┼──────────────────────────────────┤
│ O3  │ MINOR    │ Design:728–732 puts eligibility  │ Record the revised order and    │
│     │          │ in Phase 1. Plan1b:40 makes      │ move the deferred acceptance    │
│     │          │ plan 2 depend on 1c.             │ items explicitly to plan 1c.    │
├─────┼──────────┼──────────────────────────────────┼──────────────────────────────────┤
│ O4  │ MINOR    │ CatalogLock:52–63 excludes Kit.  │ Correct the cost argument: the  │
│     │          │ The run-extension theorem is    │ eligibility definitions need   │
│     │          │ not itself locked on first      │ lock planning; the Kit theorem │
│     │          │ write under the current rules.  │ is not a direct lock root.      │
└─────┴──────────┴──────────────────────────────────┴──────────────────────────────────┘
```

Evidence names: **Design** = [docs/FRAMEWORK-DESIGN.md](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md); **Plan1b** = [docs/plans/2026-09-29-phase1b-instances.md](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase1b-instances.md); **CatalogLock** = [scripts/CatalogLock.lean](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean).

This is a source audit. The final checked main commit was `5f65103`; the FG-SA branch was `6281e40`. I changed no files and ran no build.

**1. Phase 2 dependencies**

No specified Phase 2 result requires the deferred `Eligible` predicate, the general run-extension theorem, claim inhabitation for every horizon, or a new certificate.

- **2a — core, E1, E2 and E5:** needs dependent authentication, seat assignment, `Linked`, the atomic emission order, separation, and isolation laws. These are engine definitions and local proof obligations. They do not require a scheduler extension theorem. See [Design:97](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:97) and [Design:294](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:294). The existing sketch proves record isolation directly: [Sketch.lean:29](/Users/francesco/ethereum/lean/available-chain/AvailableChainEngineV2/Sketch.lean:29), with its tick theorem at line 66.
- **2b — lift:** needs the object/authentication translation, committee equivalences, preserved duty order, step simulation, and preservation of the relevant regimes and observations. The design explicitly separates these from certificate eligibility: [Design:330](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:330).
- **2c — restart and toy protocol:** needs restore laws, epoch semantics, rejoin conditions, and the required toy behavior. These are stated at [Design:316](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:316). Phase 2 acceptance asks for a toy Linked/self-visible/restart protocol, not its certification: [Design:731](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:731).
- **2c — I1:** needs an input claim and a counterexample run for `clockChain`. A finite witness is necessary. The general `∀ H` inhabitation theorem is not. See [Design:944](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:944) and [Cert.lean:19](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Cert.lean:19).

There is a staging dependency within Phase 2: the specified lift already mentions `NoRestart` and trivial `durable`. Its final statement must also survive the input interface added for I1. Stage 2b can precede the restart proofs, but Phase 2 must check the lift against the final engine.

The old §3 pseudocode contains `deliv : Deliverable P`. The later implementation note supersedes that shape: `Instance` has hooks, and eligibility is separate. See [Design:374](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:374) and [Instance.lean:16](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Instance.lean:16).

**2. Lift, eligibility and certification on v2**

The lift does **not** need v1 eligibility or v1 run extension. It starts with an existing v2 run and constructs its corresponding v1 run. It does not extend a prefix.

The logical directions differ:

```text
v2 regime run ──simulation──▶ v1 regime run
v1 claim holds ──transport─▶ v2 claim holds
```

This gives no existence result for v2 runs. In particular, a v1 inhabitation proof would not, by itself, establish v2 inhabitation through this direction of simulation.

“Proved separately per instance” requires two distinct kinds of evidence:

- The E4 obligations: `EmitWellFormed`, `HandlerCoverage`, `Deliverable`, and `RelayFeasible`, with the required hooks. See [Design:138](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:138).
- For each certificate and its constants, admissible regime runs with the required late trigger and deadline, for every horizon. See [Claim.lean:63](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Claim.lean:63). The current `Cert` fields are constants, validity, inhabitation and `holds`; `Eligible` is not currently a field: [Cert.lean:12](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Cert.lean:12).

These proofs can be attempted directly on v2 for lifted Grid CO, SA and SA-PC. No design rule requires a prior v1 proof. Their legacy lifts have no self-visible labels and no restarts, which simplifies the additional engine obligations. This is a valid proof route, not evidence that the obligations already hold.

Three limits apply:

1. The extension theorem must cover all regime fields and outstanding delivery obligations. The four E4 predicates alone do not establish participation, recurrence or root properties. Plan1b already requires this at [line 405](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase1b-instances.md:405).
2. Full profile certificates cannot cover every current parameter value. Persistence at zero budget has no inhabitation witness: [Standard.lean:220](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Catalog/Standard.lean:220).
3. Certification of transported legacy claims does not establish the new I1 floor. A lift that ignores the new input has no input-binding proof merely because it transports old claims.

Also, the current `Cert.pull` is not a shortcut for the proposed simulation. Its `DomainMap` requires a context **equivalence**, and its inhabitation transport uses the inverse. See [DomainMap.lean:15](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/DomainMap.lean:15) and line 58. A one-way simulation needs its own transport theorem unless that stronger equivalence is proved.

**3. I1 does not require plan 1c**

The compiled witness already includes:

- runs at every horizon: [NoInput.lean:370](/Users/francesco/ethereum/lean/available-chain/AvailableChainRegistry/Gaps/NoInput.lean:370);
- four old-floor certificates: line 379 onward;
- `clockCandidate`: line 437.

The new regression test needs a valid v2 run in the new claim’s regime, with a permitted input that the clock proposal fails to represent. It then proves failure of the new conclusion. This does not require `Candidate`, `Eligible`, or a certificate for any real protocol.

Keep the input-binding requirement in the **conclusion**. If the regime assumes that the proposal already binds the input, it can exclude the bad behavior and make the test vacuous.

O1 is a real change to the deferred plan. Today:

```lean
Candidate I := ProfileCert core I
```

The old core contains four claims: [Core.lean:94](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Catalog/Core.lean:94). The existing `ac43` relation proves precisely those four: [Relations.lean:13](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Catalog/Relations.lean:13).

After I1:

- `candidateOfAc43` can still target the **legacy** floor.
- To target the new floor, it needs the new claim’s certificate, or a versioned profile that includes that claim.
- The positive `clockInst : Candidate × Eligible` exercise must remain explicitly about the legacy floor. It cannot also be a positive witness for the repaired floor.

An input-aware Grid CO, SA or SA-PC instance needs its own new-claim proof. Old proposition transport does not supply it.

**4. Locks and Registry**

Nothing already locked requires the temporal order “1c before Phase 2.”

The lock contains `Candidate`, `core`, `Cert`, `Instance` and domain declarations. It contains no `Eligible` or general run-extension declaration. The scan rules depend on modules and declaration types, not plan order: [CatalogLock.lean:55](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean:55).

There are migration constraints:

- Add a v2 claim domain and versioned floor rather than silently change the meaning of `core.v1`. The design calls for versioned entries when a fixed layer has a gap: [Design:90](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:90).
- The Registry explicitly maps `Candidate` to v1 and the old core: [Registry.lean:335](/Users/francesco/ethereum/lean/available-chain/scripts/Registry.lean:335). Its instance-type list also names only the current `Instance` and `StrongInstance`, at line 122. V2 registration needs an explicit update.
- Preserve the historical I1 certificate and its `KNOWN-GAP` status. Its old proposition remains true.
- I9 is already approved as a separate contract and lock change: [Design:973](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:973). The Phase 2 baseline must be the audited result of that change.

The “duplicate locked work” argument is partly overstated. Eligibility definitions in locked modules need careful first definitions. `Kit.Engine` is outside the direct lock scope. Writing its theorem twice can waste proof work, but the current lock does not require that duplication.

**5. Risks of the new order**

The main cost is later evidence against vacuity, not a loss of logical soundness.

- **Longer `holds*` status.** Grid CO, SA and SA-PC remain proposition results without certificates. Keep the current labels. The MATRIX already states that `holds` can be vacuous and does not establish a `Candidate`: [MATRIX.md:7](/Users/francesco/ethereum/lean/available-chain/docs/MATRIX.md:7).
- **An empty regime can pass transport.** `holds` is an implication over regime runs: [Claim.lean:56](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Claim.lean:56). A correct simulation can therefore transport a result without showing that a useful run exists.
- **Defects can be found later.** Missing dependencies, malformed emissions, permanent temporary refusals, or impossible triggers may first appear during plan 1c. I9 removes one identified root problem; it does not prove delivery feasibility.
- **Finite witnesses reduce this risk.** For Phase 2 acceptance, I recommend checked v2 traces for each migrated real instance, including an honest proposal and the relevant output deadline. Map those traces to v1. These checks do not replace universal inhabitation. Existing finite evidence is not absent: SA-PC has a checked Sleepy run at [CleanInvariantCounterexample.lean:246](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Tests/CleanInvariantCounterexample.lean:246).
- **A v1 result can remain uncertified.** Later v2 inhabitation can supply corresponding v1 witnesses if the simulation preserves horizons and triggers. Thus a separate v1 certification project is unnecessary. Until those witnesses exist, the risk remains.
- **T7 becomes a v2 integration task.** Merging FG-SA does not establish its run adapter. Its report explicitly limits the results to local store facts: [FGSA-STORE-REPORT.md:10](/Users/francesco/worktrees/available-chain-fgsa/docs/FGSA-STORE-REPORT.md:10). T7 still needs authentication conversion, checked delivery, hooks, record order, own-row behavior and content consistency: [line 200](/Users/francesco/worktrees/available-chain-fgsa/docs/FGSA-STORE-REPORT.md:200). The documented decode-adapter route can retain the internal store API; native retyping has wider cost.

Keep plan 1c’s full acceptance criteria. Do not close eligibility because the lift or a finite trace passes.

**6. Self-delivery at emission and E5**

**Allowing ordinary self-delivery at the emission timestamp does not conflict with E5.**

Use this order:

```text
clock → compute payloads → sign → recordOwn → release
      → normal delivery to the sender at the same timestamp
```

The delivery occurs after the tick phase. It calls `process` and passes the normal wire, dependency, freshness and provenance checks. This is already permitted by the v1 event order and provenance rule: [Run.lean:30](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:30), [Conditions.lean:51](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:51), and line 77.

E5 requires `recordOwn` to preserve `base`. It permits `process` to change `base` as a function of the previous base and delivered object. Thus:

- Keep the private signing record update before release.
- Insert the row into the public pool through `process`.
- Keep AP/CStar labels non-self-visible.
- Keep the AP hook projection laws.
- Ensure that the private record update does not make the normal row delivery fail its freshness check.

No isolation law needs relaxation. The smallest design clarification is:

> `selfVisible` controls the private own-signature record. A normal delivery to the emitting node may occur at the emission timestamp, after the tick phase.

There **is** a conflict if `recordOwn` itself inserts the row into a pool that changes an AP proposal. `proposalRows` reads that pool: [Frame.lean:128](/Users/francesco/worktrees/available-chain-fgsa/AvailableChainFGSA/Model/Frame.lean:128). Hiding the pool outside the projection would then break AP payload factorization. This is the conflict described in [r201:431](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/own-row-delay.md:431).

If immediate self-processing must occur in **every** FG-SA execution, add an explicit zero-delay self-delivery condition or scheduler rule after release. Permission alone does not guarantee it. The cost is a narrower execution class and proofs that the inserted deliveries pass the checks and preserve the intended observations. R201 gives a paper construction at [line 391](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/own-row-delay.md:391); T7 must establish its Lean counterpart. No general E5 weakening is needed.

CHECK COMPLETE: 0 blocking, 2 major, 2 minor