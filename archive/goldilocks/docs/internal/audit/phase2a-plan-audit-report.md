VERDICT: REVISE

```text
┌─────┬──────────┬─────────────────────────────────┬───────────────────────────────────────────────────────┐
│ id  │ severity │ evidence file:line              │ fix                                                   │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A01 │ BLOCKING │ Plan:87–89; Run:127              │ Compute emission from the actual tick prefix,         │
│     │          │                                 │ including restarts at the same time.                  │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A02 │ MAJOR    │ Plan:126; Conditions:52,70       │ Fix EmitOk: require post-clock freshness, specify     │
│     │          │                                 │ the delivery position, and cover carried signatures. │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A03 │ MAJOR    │ Plan:136–138; Stable:12;         │ Add recordOwn preservation premises to the invariant │
│     │          │ Clock:175                       │ and stability lemmas before the freeze.              │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A04 │ MAJOR    │ Plan:157; Survey:723–730         │ Replace the input-erasing context equivalence with   │
│     │          │                                 │ a product equivalence or a map with a section.        │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A05 │ MAJOR    │ Plan:125,157;                   │ Supply hook proofs after prior restarts and on all   │
│     │          │ Survey:345–359,833–839           │ validator types. State the instance-lift restrictions.│
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A06 │ MAJOR    │ Plan:157; Regimes:66;            │ Prove the required n/card relation, or give a         │
│     │          │ Survey:866–872                  │ separate transport for protocols with no old labels. │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A07 │ MAJOR    │ Plan:146; CatalogLock:109,129    │ Check anchor coverage against the full engine API.   │
│     │          │                                 │ Include OutputsFactor and the missing read helpers.  │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A08 │ MAJOR    │ Plan:39–40,122,139; I9:114       │ Split Tasks 4–5. Defer interface/output laws and the  │
│     │          │                                 │ Block toy work until after I9.                       │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A09 │ MAJOR    │ Plan:157; Design:85–93           │ Put concrete lifted instances, results, and traces   │
│     │          │                                 │ in L4. Keep generic transports in Framework.         │
├─────┼──────────┼─────────────────────────────────┼───────────────────────────────────────────────────────┤
│ A10 │ MINOR    │ Plan:151; AxiomCheck:25–26       │ Add KitV2 to build and axiom-check coverage. Ensure   │
│     │          │                                 │ that the toy module is built and checked.            │
└─────┴──────────┴─────────────────────────────────┴───────────────────────────────────────────────────────┘
```

Evidence keys: [Plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase2a-engine-v2-core.md), [Survey](/Users/francesco/ethereum/lean/available-chain/claude-files/p2/survey.md), [Design](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md), [I9](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-i9-derived-roots.md), [Run](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean), [Conditions](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean), [Regimes](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean), [Stable](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/Stable.lean), [Clock](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean), [CatalogLock](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean), [AxiomCheck](/Users/francesco/ethereum/lean/available-chain/scripts/CheckFrameworkAxioms.lean).

This is a source audit of the working tree at `78e3746`, including the updated decision at Plan:44. T7 references use `a0f08c6:docs/plans/2026-09-29-fgsa-composition-t7-t1.md`. I changed no files and ran no build.

**1. E1, E2 and E5 fidelity**

E1 and E2 are represented correctly:

- Authentication depends on the label’s seat count.
- `ProtocolSpec` has no global `n`.
- All signed duties, including proposals, use `act`.
- `Run.seatOf` is a function. It permits multiple seats per validator.
- `CStar`, `Linked`, and `SingleSeat` impose separate conditions.
- Proposal labels have one seat, and `proposerOf` selects that seat’s holder.

The local `tick` definition also has the correct E5 order: clock, compute all payloads from the same post-clock state, sign, fold `recordOwn` in label/seat order, then release. The asleep branch correctly keeps the clock update and omits emission and recording.

**A01 breaks the connection between that tick and the run’s reported emission.** V1 `stateBeforeTime t` includes only events with time strictly less than `t`. V2 permits a restart at `t` before the tick. Thus these two expressions can use different states:

```text
World.step at tick(v,t): actual prefix, including restart(v,t)
planned emittedAt:      prefix strictly before t
```

For example, let the node have state `1` before `t`, let restart restore state `0`, let clock preserve state, and let `act` emit the state. The actual tick emits `0`; the planned `emittedAt` reports `1`. Sharing the function `tick` does not prevent this error.

Keep the v1 event-index argument to `emittedAt`, or introduce a phase-aware prefix that includes same-time restarts. Prove correspondence with the **actual tick event**, rather than only an equality that unfolds the planned definition. Add a restart-then-tick test.

The remaining E5 differences and qualifications are:

- **Input:** the extra `In` argument is the intended I1 extension.
- **Separation:** `F.ap ∪ F.fresh` is the correct declared family restriction. “CStar family” must mean the designated fresh family. It cannot mean every family for which `CStar` happens to hold: `Linked` implies `CStar`, yet Linked FG labels may be self-visible.
- **Isolation:** the clock, process, record, AP action, gossip, and hook projection laws are listed. `actB` must retain the same input argument. Define the AP-object restriction precisely, including the two object arguments of `handles`.
- **Outputs:** a separate `OutputsFactor` is a valid organization. Later instance assembly must require it. Merely constructing `Isolation` does not establish output isolation.
- **Restore:** deferring the law to 2c follows the agreed staging. Reserve both directions from the sketch: `restore_base` and `durable_base`. The first alone permits record-only data to enter the durable base projection.
- **Tick theorem:** the specified laws prove the stronger result
  `base (tick …).1 = clockB (base st) t`.
  Released AP payloads are not an additional dependency of the post-tick base.
- **Run-level hooks:** this remains the expressly retained design deviation, not a new departure.

**2. Are the reservations sufficient for an additive 2b/2c?**

**The data reservations are sufficient in principle. The current plan is not ready to freeze.**

Restart events, `Durable`, `durable`, `restore`, input, and local `restartFree` intervals allow later declarations for epochs, rejoin, restore laws, input claims, and restart regimes. None of these inherently needs a new core field.

Make these corrections before the freeze:

- A01: settle the emission prefix and its API.
- A02: settle the exact `EmitOk` fields and theorem conclusion.
- A03: include the required `recordOwn` premises in the Kit statements.
- A07: make the freeze cover the promised engine API.

In 2c, “generalize the Kit lemmas” must mean **add new lemmas**. Keep the frozen `NoRestart` lemmas. Add separate restore/clock laws where the new proofs need them.

Three 2b commitments also need correction. These can be fixed without changing a 2a type:

1. **The context equivalence loses input — A04.** See answer 3.
2. **A v1 hook proof does not automatically give the planned v2 hook proof — A05.** V2 hooks quantify over all scheduled runs, including intervals after an earlier restart. The survey’s legacy lift uses `restore := init`. A restarted state at a late time need not be reachable in a v1 run at that time.

   A simple counterexample has states `init`, `good`, and `bad`. Tick zero moves `init` to `good`; later ticks keep `good`. A positive-time tick from `init` moves to `bad`, and the next tick clears `bad`. Let `processed` mean “state is bad.” Every scheduled v1 honest run starts with tick zero, so its hook stability holds. A v2 restart at a positive time reaches `bad`, then clears `processed` without another restart. Its v2 hook stability fails.

   The validator-type issue is separate. With `n = 0` and a nonempty old label type, v1 runs cannot exist: committee equivalences require an empty validator type, while `proposerOf` requires a validator. V1 run-level hook fields can then hold vacuously. V2 hooks also cover non-bijective assignments.

   Scope the generic instance lift, require additional hook evidence, or choose and prove suitable legacy restart behavior. Do not weaken the epoch-correct hook interface merely to make the lift compile.

3. **Replacing `n` by `card V` needs a proof — A06.** When the old label family is empty, `CStar` gives no cardinality equation. For example, `n = 10`, `card V = 1`, and one awake honest validator satisfy the new threshold `1 ≤ 1`, but fail the old threshold `5 ≤ 1`. The regime implication required by the proposed simulation therefore fails. State the required relation or handle such protocols separately. Do not restore a global `n` to the engine.

**3. D3 and the input shape**

`ProtocolSpec (In : Type)` with `Run.input : V → Time → In` is a suitable choice for I1.

The claim domain can fix the input type independently of the protocol. The proposal duty receives the value at its holder and act time. This supports a conclusion that relates the emitted proposal to:

```lean
rho.input (proposerOf rho I s) (proposalTime I s)
```

A spec field `Input : Type` is also technically possible, but it requires an additional constraint that relates each protocol’s input type to the externally fixed input domain. Without that constraint, choosing `Unit` defeats the purpose. The type parameter makes the restriction simpler.

Per-label input would permit distinct inputs for simultaneous duties at one validator. The proposed shape gives those duties the same `In` value. That is sufficient for the stated proposer-input repair. If separate duty inputs later become necessary, a fixed structured `In` can contain them; alternatively, a per-label API must be selected before the freeze.

The type parameter alone does **not** close I1:

- The repaired floor must use a nontrivial input domain.
- The binding requirement belongs in the conclusion.
- A protocol-supplied relation `binds := True` must not suffice. Use a specified decoding relation, or laws that make distinct inputs distinguishable in the proposal.
- Input availability and proposal existence must not be hidden behind a premise that already assumes successful binding.

The forward v2-to-v1 simulation works with an ignored input parameter. **The claimed context equivalence does not.** Two runs that differ only in `input` have the same projected v1 run.

A suitable replacement is an equivalence of the form:

```text
legacy v2 contexts
    ≃ v1 contexts × (V → Time → In)
```

Alternatively, choose an input stream and prove that embedding is a section of projection. Constructing this embedding needs an input value or suitable inhabitation evidence. For `In = Empty`, the proposed certificate transport cannot manufacture v2 runs.

For certificate transport, also preserve admissibility, horizon, regimes, and late triggers. For refutation transport, prove the required reverse conclusion implication on embedded contexts. The survey’s one-way `ClaimSim.conclusion` is insufficient for that purpose.

**4. Self-delivery hypotheses and event order**

**Same-time self-delivery is consistent with the event order. The current lemma specification is incomplete.**

Restart phase 0, tick phase 1, and delivery phase 2 permit delivery at the emission timestamp. Direct signature provenance permits equality of timestamps because it requires `t' ≤ t`.

A02 has four parts:

1. **Freshness must start after clock.**  
   `recordOwn_processed` preserves the processed flag across recording. It says nothing about `clock`. “Not processed before the tick” does not imply “not processed after the tick.” Require freshness in the post-clock state, then prove preservation through the complete record fold.

2. **Specify the delivery position.**  
   “After the tick phase” permits earlier deliveries to the same receiver. Such a delivery can process `o`, or process a container that handles `o`. Post-tick freshness then no longer establishes freshness at the proposed delivery. Require no intervening receiver-changing event, or state the checks directly at the delivery prefix.

3. **Cover carried signatures.**  
   An honest emission establishes provenance for the outer signature. It does not establish provenance for every object that `P.carries` relates to it. Add the carried-signature premise, or restrict the lemma to an object class that carries nothing.

4. **Separate the predicates.**  
   `DeliveryWellFormed` contains wire, dependency, and freshness checks. Provenance belongs to `UnforgeableSignatures`. A local delivery check proves neither validity of all other events nor preservation of a complete run after insertion.

The corrected hypotheses are satisfiable. A toy can keep receipts in `base`, keep the own record separately, use a state-preserving clock, emit a previously unseen row, and carry nothing. `process` can then add the row to receipts. Check a complete finite `ExecutionValid` witness, not only the fields of `EmitOk`.

Legal delivery also does not imply acceptance: the handler may refuse it. Any claim about immediate insertion into the own pool needs its own handler proof.

**5. HooksSound and restart epochs**

The interval form is correct if:

```text
restartFree rho v i j
    means no restart of v at an index k with i ≤ k < j
```

With `i ≤ j`, this matches equality of the node’s epoch counts at `stateBefore i` and `stateBefore j`.

The endpoints matter. A restart at index `j` has not yet occurred in `stateBefore j`. A restart at index `i` does occur between `stateBefore i` and `stateBefore (i+1)` and must prevent stability across that step. Restarts of other nodes must not invalidate the interval.

The three proposed record laws are appropriate:

- `recordOwn_processed`: equality preserves both true and false.
- `recordOwn_deps`: equality prevents private recording from creating or removing receipt dependencies.
- `recordOwn_excludes`: true remains true.

The first two are stronger than monotonicity, but they fit a private own-signature record. They also support the intended freshness argument.

These laws do not specify receipt loss during restore, preservation of time-based exclusions, or rejoin obligations. Those correctly remain separate 2c laws. A05 concerns proving this sound interface for lifted protocols; it does not make the interval form wrong.

**6. Does 2a unblock T7.0–T7.9?**

**It supplies most of the required generic API. It does not support the literal T7 plan without a reviewed v2 revision.**

The survey is broadly correct that these steps do not need the v2 catalog, claim domain, general lift, or full restart regimes. It understates the following work:

- **T7.2:** needs the v2-to-store authentication adapter, proposal labels, and the new `recordOwn` implementation. These are T7 outputs, not missing engine definitions.
- **T7.4:** must prove `recordOwn_now`.
- **T7.5:** its all-runs reachability induction gains a restart case. It needs preservation by the chosen restore operation, or a stated `NoRestart` restriction.
- **T7.6:** must use the corrected emission/read bridge and the new premises of the clock lemmas.
- **T7.7:** needs all three record laws and hook stability on intervals that can follow a restart. The planned Kit supplies global `NoRestart` clock results only. That is insufficient for the full `HooksSound` fields. T7 must add suitable restore/epoch auxiliary proofs, or 2a must supply them.
- **T7.8:** depends on the repaired stability lemmas from A03.
- **T7.9:** must replace the v1 asleep-recording trace with the awake emission/record trace. A cumulative trace through the whole run needs `NoRestart`; a restart-aware trace needs epoch indexing.

A03 is substantive. Clock and process preservation of an arbitrary predicate `Q` does not imply preservation by `recordOwn`. For example, recording can change a private flag while preserving `base` and `now`. Thus the v1 statements of `stateBefore_stable`, `stateBefore_stable_clock`, and `stateBefore_invariant` need another premise. Field-origin and field-prefix lemmas need corresponding record laws. A premise that `Q` factors through `base` is another valid route.

FG-SA can begin after the corrected 2a gate and a reviewed T7 revision. Permission for self-delivery does not establish an unconditional own-row processing result; the updated Plan:44 correctly leaves that scheduler choice optional.

**7. Framework imports and the lock**

`AvailableChainFramework` **may import** `AvailableChainEngineV2`. Design §1 permits L2–L3 to depend on L0–L1. It forbids dependencies on L4–L6.

The anchor approach can produce only ADDED lock lines against the **post-I9 baseline**, because existing declarations need not change. The new module prefix is also the correct kind of prefix: the scanner tests module names.

However, **A07 prevents the anchor from establishing the stated freeze**. Mentioning a type does not reach every definition that consumes that type. The listed roots do not ensure coverage of:

- `OutputsFactor`;
- `Run.readAt` and `Run.final`;
- the output-read helper;
- derived `proposalTime` and `proposerOf` helpers.

Require a frozen API manifest and check that the anchor’s dependency closure contains each intended L0/L1 declaration. Do not assume this from a list of high-level types.

Dependencies in that closure affect the anchor’s hash. They do not automatically receive separate lock lines. Also, do not cover Kit omissions by importing `AvailableChainKitV2` into Framework: that would violate the L5 rule.

The fallback “new small locked library” would need scanner changes beyond `lockedModulePrefixes`, because `CatalogLock.locked` first rejects modules outside `frameworkLibrary`.

**A09 applies to the 2b outline:** “All in Framework” is invalid for concrete transports of `grid_holds`, Counter certificates, Sanity refutations, and concrete traces. Those depend on L4 protocol/Registry material. Put generic simulation and catalog declarations in Framework; put concrete lifted instances and results in Registry or other L4 modules.

**8. D8 and work before I9**

D8 is too broad.

```text
┌──────────┬─────────────────────────────────────────┬──────────────────────────────────────────┐
│ Task     │ Block dependency                        │ Can finish before I9 without rework?     │
├──────────┼─────────────────────────────────────────┼──────────────────────────────────────────┤
│ 0        │ Existing root imports Sketch, which     │ Layout work can. Accept I9's Sketch      │
│          │ imports Block.                          │ changes at the merge.                    │
├──────────┼─────────────────────────────────────────┼──────────────────────────────────────────┤
│ 1–2      │ New generic definitions need no Block.  │ Yes, with narrow imports.                │
├──────────┼─────────────────────────────────────────┼──────────────────────────────────────────┤
│ 4        │ OutputsFactor needs Task 3's Interface; │ Only the block-independent parts. The   │
│          │ output_tick concerns Block getters.     │ complete task depends on Task 3.         │
├──────────┼─────────────────────────────────────────┼──────────────────────────────────────────┤
│ 5: Kit   │ The selected engine lemmas are generic. │ Yes, after the corrected core and laws.  │
│          │ Their old broad imports can be removed.│                                          │
├──────────┼─────────────────────────────────────────┼──────────────────────────────────────────┤
│ 5: toy   │ Sketch's output constructs Block.node.  │ A literal port needs I9 rework. Defer it │
│          │ I9 changes its third argument.          │ or use a block-independent test first.   │
└──────────┴─────────────────────────────────────────┴──────────────────────────────────────────┘
```

I9 explicitly owns the sketch’s two block folds at [I9:114](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-i9-derived-roots.md:114). Their old `BlockId` arguments become bodies.

The worktree location follows the stated preference. The merge/rebase before block-dependent work is sound. Revise the task dependency graph so that only Tasks 0–2 and the block-independent parts of Tasks 4–5 can complete early. Run the freeze and lock checks after I9.

**9. Phase 2 acceptance preparation**

The plan assigns the three requested acceptance areas to the correct later stages, but the gate needs more precise checks.

- **Lifted finite traces, 2b:** retain checked traces for Grid CO, SA, and SA-PC. Each must include an honest proposal, the relevant output deadline, and the required execution/regime evidence. Map the trace to v1. Finite traces do not replace universal inhabitation or eligibility.
- **Registry, 2b/2c:** add support for v2 instance and strong-instance types, and for the new floor’s certificate form. The scanner currently names only v1 instance types and hard-codes the old `Candidate` interpretation. Preserve old ids, certificates, and the I1 `KNOWN-GAP` history.
- **Restart toy, 2c:** demonstrate a nontrivial restart, the restore isolation laws, receipt loss outside durable state, and a subsequent delivery that is fresh in the new epoch. The Task 5 no-restart toy does not satisfy this acceptance item.
- **I1, 2c:** refute lifted `clockChain` using a permitted nontrivial input and failure of the binding conclusion. Keep the existing `Candidate` as the legacy floor.
- **Final engine check:** check the lift and finite traces against the final 2c engine and law declarations, even if their types remain unchanged.

For 2a itself, add the same-time restart/emission regression test and a complete self-delivery execution witness. A10 also needs a concrete gate change: the current axiom checker does not scan `AvailableChainKitV2`. Add that library to its imports and scan list, add the library to the required full build, and ensure the toy is included in the build and scan.

Eligibility and the general run-extension theorem can remain in plan 1c. None of these corrections requires moving them into 2a.

AUDIT COMPLETE: 1 blocking, 8 major, 1 minor