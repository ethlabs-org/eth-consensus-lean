Source re-check at `cb33acd`. No files changed; no Lean build run.

Line keys: **P** = [revised plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase2a-engine-v2-core.md), **C** = [EngineClock](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean), **L** = [CatalogLock](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean). Severities below count the remaining defects.

```text
┌──────┬───────────┬─────────────────────────────────────────────┬─────────────────────────────────────────────┐
│ item │ status    │ evidence                                    │ fix if needed                               │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A01  │ RESOLVED  │ P84,89–91: emitsAt uses the actual tick      │ None for the original defect. See N03 for    │
│      │           │ prefix. This includes same-time restarts.   │ the emittedAt wrapper.                      │
│      │           │ The correspondence lemma and test cover it. │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A02  │ PARTLY    │ P116 fixes post-clock freshness, delivery   │ State tick/delivery indices and their time; │
│      │ MAJOR     │ position and carried objects. But it drops  │ require o ∈ emitsAt E rho i, the honest      │
│      │           │ the previous emission premise. EmitOk can   │ self-visible emitter, HooksSound, and       │
│      │           │ hold for an object never emitted. Signature │ unchanged receiver state on [i+1,j).        │
│      │           │ provenance then does not follow.            │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A03  │ PARTLY    │ P129: preserving the source predicate does  │ For field origin, require that recordOwn    │
│      │ MAJOR     │ not prevent recordOwn from adding rows.     │ adds no field rows; field equality suffices.│
│      │           │ With source predicate Q=False, preservation │ For field prefix, require                  │
│      │           │ is vacuous, but a recorded row has no clock │ field st <+: field (recordOwn st o).         │
│      │           │ origin. See C208–216.                       │ Alternatively, factor the field through     │
│      │           │                                             │ base, not merely the source predicate.      │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A04  │ RESOLVED  │ P171 retains input in the correspondence,   │ None at this outline stage. Prove the       │
│      │           │ requires input evidence, and requires the   │ transport laws in 2b.                       │
│      │           │ reverse conclusion implication.             │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A05  │ PARTLY    │ P172 requires hooks after restarts and for  │ Remove the NoRestart alternative for        │
│      │ MAJOR     │ non-bijective seat maps. But P190–192 allows │ T7.7's full HooksSound value. It can remain  │
│      │           │ NoRestart for T7.7. That cannot construct   │ on separate reachability or trace results.  │
│      │           │ the full HooksSound required by P115.       │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A06  │ RESOLVED  │ P173 requires the n/card relation for a     │ None at this outline stage.                 │
│      │           │ nonempty legacy family and a separate case  │                                             │
│      │           │ for protocols with no old labels.           │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A07  │ PARTLY    │ P156–160 supplies the manifest, value       │ Build Framework after adding the anchor.    │
│      │ MAJOR     │ anchor and coverage check. But P160–162     │ Then run coverage with the same dependency  │
│      │           │ checks coverage and the lock before it     │ rules as L132–165, followed by lock          │
│      │           │ builds the new Framework anchor. L296      │ check/write/check. Reject a missing anchor. │
│      │           │ imports built modules.                      │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A08  │ RESOLVED  │ P75,120–151 separates Kit work from         │ None for the I9 task split. Keep early      │
│      │           │ Interface, OutputsFactor and the Block toy. │ imports limited to the required modules.    │
│      │           │ Tasks 5–7 wait for I9.                      │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A09  │ RESOLVED  │ P169–170 puts generic transports in         │ None.                                       │
│      │           │ Framework and concrete instances, results   │                                             │
│      │           │ and traces in L4.                           │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ A10  │ RESOLVED  │ P72–76,147–151,162 requires EngineV2 and     │ None for coverage. Fix Task 0's creation    │
│      │           │ KitV2 build/axiom coverage, the toy, and     │ order in N01.                              │
│      │           │ KitV2 in the full default build.            │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ N01  │ NEW       │ P76 builds and scans KitV2, but P123 first  │ Create the empty AvailableChainKitV2.lean   │
│      │ MINOR     │ creates its root module in Task 4.          │ root in Task 0. Extend it in Task 4.        │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ N02  │ NEW       │ P129 permits restartFree on the lemma's     │ Use NoRestart for the clock suite and      │
│      │ MAJOR     │ interval. This does not suffice for clock   │ tick/time bridge in 2a. Local versions need │
│      │           │ lemmas. With ticks at 0,2 and a restart at  │ an initial clock bound or a suitable prefix │
│      │           │ 1 setting now=100, prefix interval [2,3)    │ condition. Add those versions in 2c.       │
│      │           │ has no restart, but now falls from 100 to 2.│                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ N03  │ NEW       │ P89 defines emittedAt using “the index”.    │ Specify the first matching tick and prove  │
│      │ MINOR     │ A raw Run can contain duplicate ticks at    │ agreement under ScheduleWellFormed; or     │
│      │           │ (v,t), with different outputs. Uniqueness   │ retain the event-index argument.           │
│      │           │ requires ScheduleWellFormed.                │                                             │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ Lock │ SUPPORTED │ P161: ADDED only is possible against the    │ Keep v1 declarations unchanged. Engine     │
│      │           │ post-I9 lock. Existing hashes depend on     │ dependencies affect the anchor hash; they  │
│      │           │ their own closures, not on new roots        │ do not receive separate lock lines. Apply  │
│      │           │ (L12–15,169–173).                          │ A07's build order.                         │
├──────┼───────────┼─────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ 0–4  │ NOT READY │ The I9 dependency is removed, but the early │ Fix N01/N03 before Tasks 0–1, A02 before    │
│      │           │ task interfaces still need corrections.     │ Task 3, and A03/N02 before Task 4. A05/A07  │
│      │           │                                             │ must be fixed before the later gate.       │
└──────┴───────────┴─────────────────────────────────────────────┴─────────────────────────────────────────────┘
```

VERDICT: REVISE

RECHECK COMPLETE: 0 blocking, 5 major, 2 minor