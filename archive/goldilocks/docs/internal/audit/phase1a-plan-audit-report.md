The core representation is feasible, but the plan needs revision before execution. I found five major and three minor issues. I changed no repository file and ran no full build.

In the table, `Plan` means [docs/plans/2026-09-28-phase1a-gate-catalog.md](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-phase1a-gate-catalog.md). `Catalog/` and `Framework/` refer to `AvailableChainFramework/`; `Generic/` refers to `AvailableChainStatements/Generic/`.

```text
┌────────┬──────────┬──────────┬───────────────────────────────────────┬───────────────────────────────────┬───────────────────────────────────────┐
│ id     │ severity │ task     │ finding                               │ evidence (file:line)              │ proposed fix                          │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-01 │ MAJOR    │ 1, 9     │ The blanket Sleepy rewrite breaks     │ Plan:207; Catalog/Core.lean:47;    │ Keep prefixOrder.Point = Unit and     │
│        │          │          │ the unconditional prefix claim and   │ Generic/Claims.lean:33             │ regime = True. Change only its        │
│        │          │          │ the intended ac43 equivalence.        │                                   │ context arguments.                    │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-02 │ MAJOR    │ 6        │ An addition can change existing       │ Plan:535; Plan:536;                │ Hash complete dependency sets         │
│        │          │          │ hashes. The proposed addition test   │ scripts/CatalogLock.lean:45        │ independently of traversal order.     │
│        │          │          │ does not test this.                   │                                   │ Test actual declaration additions.    │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-03 │ MAJOR    │ 6        │ The suffix filter can leave a         │ Plan:533;                         │ Check generated-name metadata.        │
│        │          │          │ hand-written catalog claim unlocked. │ scripts/CatalogLock.lean:66        │ Always lock claim and profile         │
│        │          │          │                                       │                                   │ definitions, regardless of name.      │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-04 │ MAJOR    │ 6        │ The axiom check misses axioms used    │ Plan:534;                         │ Use collectAxioms separately from     │
│        │          │          │ only in helper theorem proofs.        │ scripts/CatalogLock.lean:40        │ hashing. Keep theorem hashes          │
│        │          │          │                                       │                                   │ independent of proofs.                │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-05 │ MAJOR    │ 5, split │ Adding proposer input alone does not  │ Plan:53; Plan:463; Plan:490        │ Specify a claim that binds the        │
│        │          │          │ reject clockChain. A new carrier also │                                   │ proposal to that input. Test its v2   │
│        │          │          │ leaves its v1 certificate intact.     │                                   │ refutation; retain the v1 witness.    │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-06 │ MINOR    │ 1        │ The stated imports do not support     │ Plan:101; Plan:158; Plan:205;      │ Import Fintype definitions in         │
│        │          │          │ the new declarations.                 │ Framework/Profile.lean:2          │ Carrier and Instance in the           │
│        │          │          │                                       │                                   │ transitional Profile module.          │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-07 │ MINOR    │ Rulings  │ Adding a field to frozen Instance     │ Plan:54;                          │ Use a new parameter record, wrapper,  │
│        │          │          │ later is not an additive change.      │ docs/FRAMEWORK-DESIGN.md:265       │ or carrier. State the chosen          │
│        │          │          │                                       │                                   │ parameter representation now.         │
├────────┼──────────┼──────────┼───────────────────────────────────────┼───────────────────────────────────┼───────────────────────────────────────┤
│ P1a-08 │ MINOR    │ 6        │ A library filter entry does not load  │ Plan:540;                         │ Use instanceLibraries for imports     │
│        │          │          │ that library into the environment.    │ scripts/Registry.lean:66           │ as well as filtering. Test a library  │
│        │          │          │                                       │                                   │ outside the Registry import closure. │
└────────┴──────────┴──────────┴───────────────────────────────────────┴───────────────────────────────────┴───────────────────────────────────────┘
```

**P1a-01 — scratch failure and contract mismatch.** Task 1 says to give *each* claim the `sleepy … t₀` regime. However, `prefixOrder.Point` is `Unit`, and its current regime is `True`. The literal application fails:

```text
Application type mismatch:
  p has type Unit
  but is expected to have type Time
```

The test is in [PrefixLiteral.lean:3](/private/tmp/phase1a-audit-20260928/PrefixLiteral.lean:3). Changing its point to `Time` would remove the type error but weaken the claim: `AvailableChain.nested` covers **every run**, including runs outside `SleepyRegime`. Thus Task 9 cannot recover that bundle field from a Sleepy-only prefix claim. Preserve the existing unconditional statement. See [Catalog/Core.lean:47](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Catalog/Core.lean:47) and [Generic/Claims.lean:33](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Claims.lean:33).

**P1a-02 — scratch result.** I copied the existing hash algorithm, applied the planned generated-name filter, and added this definition to the sorted set of locked roots:

```lean
def AvailableChain.Framework.AuditAddition : Bool :=
  Nat.testBit (Nat.succ Nat.zero) Nat.zero
```

No existing declaration changed. Nevertheless, **104 of 121 existing hashes changed**:

```text
Cert:      da8ff3110430848c -> 2cd0a57d13140cb7
ClaimSpec: 20599873e7579b03 -> 1b0285e79c968ed2
HooksSound:77906927827c2e06 -> aaf3e903491a5fc9
```

The shared memo stores incomplete hashes while it traverses cycles. The first root that reaches a cycle can therefore affect later hashes. The test is in [LockHardening.lean:73](/private/tmp/phase1a-audit-20260928/LockHardening.lean:73). Deleting a line from a scratch lock tests comparison logic; it does not test adding a declaration to the environment. M7 cannot remain deferred while Task 6 promises stable hashes under additions.

**P1a-03 — scratch counterexample.** This is a legal, hand-written catalog declaration:

```lean
def AvailableChain.Framework.Catalog.eq_def : ClaimSpec :=
  safeConfirmed
```

The planned filter reports `true` for “skip.” If no other locked declaration uses it, changing its body to `safeStable` changes the claim without changing any locked line. A certificate in the registry does not make it part of the framework lock’s dependency closure. The filter result is recorded by [LockHardening.lean:75](/private/tmp/phase1a-audit-20260928/LockHardening.lean:75). A suffix is not evidence that Lean generated a declaration.

**P1a-04 — scratch counterexample.** The following intentionally unsound declarations were confined to the scratch file:

```lean
axiom auditBadAx : False
theorem auditBadTheorem : False := auditBadAx
def auditBadDefinition : True := False.elim auditBadTheorem
```

The proposed traversal accepted `auditBadDefinition`, but `#print axioms` reported `[auditBadAx]`. The traversal visits the helper theorem’s statement and omits its proof, as required for proof-independent hashes. It therefore never reaches the axiom. See [LockHardening.lean:90](/private/tmp/phase1a-audit-20260928/LockHardening.lean:90). Keep that hash policy, but perform a separate proof-aware axiom check on every locked root.

**P1a-05 — counterexample to the proposed regression condition.** After adding an input argument, define the proposal function as `fun _ s _input => some s`. This still ignores input and emits the same clock-chain proposal. If inclusion continues to concern whatever the protocol emits, all four floor arguments remain unchanged. Moreover, adding `Carrier.v2` does not invalidate a certificate whose type uses `Carrier.v1`. This follows directly from the additive carrier approach at [Plan:53](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-phase1a-gate-catalog.md:53), contrary to the required elaboration failure at [Plan:463](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-phase1a-gate-catalog.md:463). Phase 2 needs a specified relation between run input and the proposed block, plus a refutation against the new floor. Mere elaboration failure could also result from an unrelated API change and is a poor semantic regression test.

1. **Core Lean feasibility.** With sufficient imports, the declarations elaborate: `Carrier : Type 2`, `ClaimSpec K : Type 1`, `Cert c I : Type`, `Profile.Entry K S : Type 1`, and `ProfileCert p I : Type 1`. The forward namespace declaration `Profile.Entry` works. Both `x.E` and `x.rho` work through reducible `Carrier.v1`; `strongV1` works with `Equiv.refl`. I completed and checked `pull`, `holds_pull`, `inhabited_pull`, and `ProfileCert.holdsAt` without `sorry` in [Core.lean](/private/tmp/phase1a-audit-20260928/Core.lean:225). The exact standalone `Carrier.lean` snippet fails because its sole import does not provide `Fintype`; adding `Mathlib.Data.Fintype.Defs` passes. Also, removing the `Claim → Instance` import path requires an explicit `Instance` import in the transitional `Profile` module.

2. **Claim soundness.** Apart from P1a-01, the proposed conclusions match the bundle fields. The orders have the correct directions: thresholds, history windows, arming lags and recovery bounds increase; budgets, proposer gaps and fault caps decrease; `recoveryFull` changes from false to true; exact inclusion delays remain equal. The transport guides follow these premise restrictions correctly. The late inclusion trigger closes the recorded I2 example. Persistence triggers also permit real witnesses: use a healthy run with non-genesis progress, choose `T ≥ H` after inclusion, then choose `b₀ ≥ T + lag` or `T + Δ`. Such inhabitation still needs a protocol-specific proof; `holds` alone does not supply it. See [design:291](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:291), [regimes:43](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:43), and [strong regimes:19](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Regimes.lean:19).

3. **Equivalence theorems.** Both intended equivalences are valid if `prefixOrder` remains unconditional. The reconstructed constant records do **not** make the regime structures definitionally equal by `Iff.rfl`: those structures retain the whole `Constants` argument. Field-by-field adapters work; `FastOutageRegime` also needs reconstruction of its parent `OutageRegime`. These adapters passed [Regimes.lean](/private/tmp/phase1a-audit-20260928/Regimes.lean). `Δ_pos` correctly supplies an environment over `Fin 1` from which to extract bundle validity; no run is needed for that extraction. The redundant `monotone` field follows from the two safety fields. Strong recovery validity must omit `Constants.Valid`: [StrongClaims:19](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Claims.lean:19) requires only `SC.Valid`. Its threshold transport needs nonnegative cardinality, not nonnegative `θrec`. I checked the component adapters, not the two unimplemented full profile theorems.

4. **I1 witness.** `clockChain` works under the stated v1 semantics. With `Δ = 1`, every honest node ticks at every nonnegative integer through the horizon, including asleep nodes. Since processing is the identity and the schedule is sorted, its read at time `s` is `clockBlock s`; `readAt` includes the tick at `s`. Different nodes and times produce blocks on one chain, and each node’s reads only extend. The proposer emits the scheduled payload from the post-clock state, so inclusion holds at `D = 0`. Exclusion disables broadcast obligations; `processed = false` prevents acceptance obligations. Every ancestor is another clock block, with a distinct root. The one-validator run therefore supplies late witnesses. See [Run:129](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:129), [Conditions:48](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:48), and [Conditions:106](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:106). No replacement protocol is needed.

5. **Design conformance.** Against §3, the explicit `n` and indexed `P` are v1 migration choices; `iface` plus typed carrier extensions replace `FacetBundle`; protocol parameters captured by `P` replace `pparams`; `Δ_pos` adds an instance restriction; and `deliv`, `iso`, and base-factorization obligations remain deferred. Dropping the separate `pparams` field is acceptable if the protocol value fixes the parameters and later code uses an explicit parameter interface. The promised later field addition is not compatible with freezing. Against §4, `K` replaces `needs`; `Point`, `Validators`, and `Ctx` make quantification explicit; `regime` and `conclusion` define `holds`; and `inhabited` becomes a derived definition. These are representation choices allowed by [design:265](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:265). Explicit Boolean equality does not change the order laws. Requiring a trigger at or after `H` strengthens the literal §5 eligibility condition, as the I2 correction proposes. The unversioned lock break also needs explicit approval. P1a-01 would be a further substantive contract change and must be removed.

6. **Lock and registry.** The proposed hardening does not yet close I8, M5, or M6, for the tested reasons above. M8 remains explicitly open. The dated old/new declaration list makes the breaking regeneration reviewable, but it should distinguish semantic changes from hash-format changes and generated-name removals. Later addition-only writes are consistent with “one breaking regeneration.” The new `ProfileCert` structure and explicit `Candidate` recognition work with type scanning. Pulled-claim parsing must account for both implicit carriers before the map and base claim. `KNOWN-GAP` must preserve `UNSOUND` and conditional status. `--check` can detect stale output, but cannot prove scan completeness; aliases, private certificates, and stable-id reporting remain open. The library list must also drive imports, rather than only the filter at [Registry:66](/Users/francesco/ethereum/lean/available-chain/scripts/Registry.lean:66).

7. **Scope and ordering.** The 1a/1b/2 split is reasonable, with the explorer still disabled. The explicit lock failure through Task 5 is a controlled migration state, provided approval covers it. The promised checkpoints are not executable verbatim until the Task 1 import and prefix issues are fixed. Task 6 must fix hash stability before freezing again. Phase 1b can add an eligibility bundle without editing frozen `Instance`, but must explicitly connect that bundle to search admission. Phase 2 needs an input-binding specification and a run simulation: the context `Equiv` used for facet projection is not a general substitute for the one-way lift required by [design:235](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:235). Both can be added without changing the tested generic claim types.

Verdict: REVISE  
AUDIT COMPLETE: 0 blocking, 5 major, 3 minor