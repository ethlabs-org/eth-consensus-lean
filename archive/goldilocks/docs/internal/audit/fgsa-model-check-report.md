# r195 — G6 Astra model check

Verdict: **PASS WITH FIXES** for the Task 6 model scope. No new BLOCKING or MAJOR finding. Five MINOR findings concern test coverage and source anchors. No Frame test has an expected value that I judge wrong. The declared root, receipt, and client limits below still apply; this verdict does not certify an unrestricted implementation of the complete protocol.

Review date: 2026-09-29. Review target: `d5171fcb836da6496e2a2a5c9743b4888e41e756`, branch `fgsa-composition`. All repository line numbers in this report refer to that commit. Task 6 Step 4 is plan line 1625; the model-only cache constraint is plan line 234; the tree-read inventory is plan lines 349–379.

Authority: `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-2e884811.tex`. Every “spec” line number below refers to this file. I used the supplied archive, not the line numbers of the adopted revision. The eth-search skill routes a check of a known local file to direct source reads.

Method: paper check of all five model files, their called helpers, the plan inventory, and the Frame Smoke tests. I did not run Lean, Lake, or a build script. The green build at the review target is the implementer's report, not a result of this check. During the review, another writer changed the plan and tests, advanced HEAD to `e8c0ba8`, and added a Frame docstring. I kept this review on `d5171fc` and did not edit those changes. Only this report was written; no commit, state, or log update was made.

The check uses the plan's boundary: checked objects at protocol ingress; coherent stores for duty reads; current-slot arguments and scheduled ticks for protocol execution; and the declared root/content premises for comparisons across nodes. The later store proofs are obligations, not evidence already supplied by this review.

```text
┌──────────────┬─────────┬────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Class        │ Count   │ Result                                                                                         │
├──────────────┼─────────┼────────────────────────────────────────────────────────────────────────────────────────────────┤
│ BLOCKING     │ 0       │ No new blocking defect found in the stated scope.                                              │
│ MAJOR        │ 0       │ No new functional mismatch found in the stated scope.                                          │
│ MINOR        │ 5       │ N1–N5 below. Add discriminating tests and complete the source anchors.                         │
└──────────────┴─────────┴────────────────────────────────────────────────────────────────────────────────────────────────┘
```

**N1 — MINOR: the HEAD test does not distinguish a live frame from controls computed from the view.** `AvailableChainFGSA/Tests/Smoke.lean:366`; `AvailableChainFGSA/Model/Frame.lean:88`; spec 598–606, 616–646, 1219–1233. All three non-genesis blocks in `stA` have stamp 12. At slot 4, `z_3 = 15`, so `voterBlocks` is the full stored tree. Replacing the live controls with controls computed from this view gives the same result. Using the full filtered tree directly also gives the expected `b2`. Thus the test checks band eligibility, but not the live-frame or restricted-witness rules. Add a case with a late witness outside the voter view, and a case where a witness outside that view changes the live contest bit. Check that the HEAD uses the restricted witnesses and the full-store controls at the same time.

**N2 — MINOR: positive carried-support and block-row inclusion are not tested.** `AvailableChainFGSA/Tests/Smoke.lean:382`, `:396`, `:412`, `:429`; `AvailableChainFGSA/Model/Frame.lean:76`, `:108`, `:119`; spec 190–193, 423–430, 544–556, 1255–1274, 1288–1293. The carried support lists are empty in these fixtures. Deleting the carried arm of `headSupport` leaves these tests unchanged. In `stP`, all block rows are already in the pool, on the parent chain, or rejected by the two-row cap. Defining `blockWireRows` to return `[]` also passes the row-inclusion tests. Add a nonempty declared-support case, including a proposal and head outside `act(Σ)` but inside `Σ.T`. Add a case where a row refused by the pool becomes eligible for inclusion after removal of an on-chain row from the same identity/round group. Include a stored off-chain row outside the inclusion window; the present proposer test removes its old rows by the chain test as well as by the window.

**N3 — MINOR: the source and live-root tests do not establish all claimed exclusions.** `AvailableChainFGSA/Tests/Smoke.lean:350`, `:358`, `:360`, `:419`; `AvailableChainFGSA/Model/Frame.lean:22`, `:165`; spec 648–677, 1086–1098, 1327–1335. `stC0` has no older fast-write set and no slow-only live lease. A wrong source rule that falls back to either when present can pass its empty-source test. The positive source set has one member, so it does not check deepest selection. The rejected live-root target `b1'` is not stored in `stA`; testing only active membership can pass in place of the full FJ filter. Add populated forbidden fallback sources, multiple eligible fast targets, and a stored active lease target excluded by the FJ filter. Also test a live root outside the HEAD's smaller view: the walk must still start at that root.

**N4 — MINOR: several declarations do not have their own spec anchor.** `AvailableChainFGSA/Model/Frame.lean:97` has no docstring for `proposerSupport`; its spec is 1240–1243. Helper declarations also use only `[helper]`, `[J1]`, `[M2]`, or `[M3]` in several places; for example `Objects.lean:75`, `Store.lean:53`, `Handlers.lean:33`, and `Frame.lean:103` (spec 225–228/510–511, 363–366, 818–819/902–912, and 1264–1265). This does not change behavior, but does not meet the Global Constraints rule that each model definition names its spec lines. Add anchors, or explicitly mark the helper as a model representation with the associated protocol operation. The declaration tables below supply the missing mappings. Also correct the plan's Step 4 quotation anchor: the saved-resolved-flag rule is at spec 429–430, not 426–427. The later working-tree docstring is outside this pinned review.

**N5 — MINOR: the finality test does not distinguish the head state from the live caches, or test record writes.** `AvailableChainFGSA/Tests/Smoke.lean:433`, `:439`; `AvailableChainFGSA/Model/Frame.lean:176`, `:184`; spec 678–679, 1324–1326, 1346–1357, 1391–1413. In `stA`, both the live justification and the head justification are `(2, B1)`. The finalized entry height is 2, and the tested attestation has no finality pair. A wrong implementation that substitutes the live justification, or always omits the finality pair, can pass these Frame tests. Returning the unchanged record can also pass: the attestation test does not check its returned record. Add a head whose state justification differs from the live cache, a nonempty finality pair with no fast source, and checks of the changed record fields. The imported client has separate tests, but these do not check the FG-SA input connection.

The following declared differences are part of the verdict's scope. They are not new failures of the accepted plan.

D1: `Frame.lean:136` uses `s * (parent.root.value + 1)` as the proposal root. It does not ensure the distinct roots required by spec 167 and 521, or content identity for the new block in 1247. For example, a slot-4 child of genesis and a slot-2 child of the formula's slot-1 block both have root 4. DQ10 explicitly retains this formula and excludes collisions through run premises; DQ3 adds content agreement. This is a real restriction on covered runs, including honest forks. The local duplicate guard does not repair cross-node content identity. No fresh-root claim follows from this review.

D2: `Clock.lean:48` calls `SA.release`, then `GridCO.releaseCount` (`AvailableChainGridCO/Model/Protocol.lean:397`). That helper tests equivocation against all stored label-r votes. Spec 1197–1200 tests only votes stamped before `q_r`. At the first scheduled release, before same-time deliveries, the sets agree. After a late second vote and a repeated/backward call at `q_r`, they can differ: two seats with timely conflicting votes give the spec count 2; a late second vote by one seat makes the model count 1. A threshold-2 lease can then stay in the model although the spec count would release it. The plan's Task 7 Reachable docstring declares this limit. Do not claim exact release equivalence for arbitrary model states or repeated clocks.

D3: The store has the five declared model-only fields (DQ8); `σ[B]` is derived rather than stored (M1); slots are derived from time; the block wire includes its erased ancestor chain (DQ1). `wellFormed` duplicates the parent-slot and row-round acceptance checks (DQ14). `attest` returns a body and a projected record; signing, emission, and immediate own-row admission remain T7 obligations (DQ4). The omitted `σ.nj` is always false in this spec (501, 940–960); the omitted `Λ.timeouts` set is written but never read (1409–1411). These are declared representations or projections, not extra protocol rules.

D4: `parentFG`, `fgBlockOf`, and `deepest` use unique lookup. On arbitrary inconsistent stores they can return `none` where the spec assumes a unique stored block. `fgInputs` then has dummy head fields. The plan assigns root uniqueness, stored-head, and lookup proofs to Tasks 10–11. The source check found no reason these obligations fail, but this paper check does not discharge them.

The next tables cover every explicit `def`, `abbrev`, `structure`, and `inductive` declaration in `AvailableChainFGSA/Model/*.lean`. Generated constructors, projections, and deriving instances are covered with their declarations. `AGREE` means semantic agreement at the protocol boundary above; a representation change is stated in the last column. `DISAGREE` identifies an exact declared difference. An asterisk on the spec entry means that I supplied some or all of that mapping because the declaration's own docstring does not give it. All file names in these five tables are relative to `AvailableChainFGSA/Model/`.

`AvailableChainFGSA/Model/Objects.lean`

```text
┌─────────────────────────────────┬──────────────────────────┬───────────┬────────────────────────────────────────────────────────────────────────────┐
│ Line and declaration            │ Spec lines               │ Result    │ Comparison and exact difference                                            │
├─────────────────────────────────┼──────────────────────────┼───────────┼────────────────────────────────────────────────────────────────────────────┤
│ 15 Params                       │ 265–335                  │ AGREE     │ SA inheritance gives integer Δ>0, n≥1, k≥2, η≥0. R≥2, wF≥1, δt≥0 are       │
│                                 │                          │           │ added; zero timeout delay is allowed.                                      │
│ 24 Params.E                     │ 154–158                  │ AGREE     │ Unit weights on Fin p.n; 0-based indices represent the n fixed identities. │
│                                 │                          │           │ Fixed-identity binding is a caller premise.                                │
│ 26 Params.cfg                   │ 283                      │ AGREE     │ Only δt is the FG configuration.                                           │
│ 28 Params.round                 │ 209                      │ AGREE     │ Natural division by R implements floor(s/R).                               │
│ 30 Params.actionTime            │ 217–220                  │ AGREE     │ SA.gateTime(rR) = 4ΔrR + 6Δ.                                               │
│ 32 Params.slotOf                │ 711                      │ AGREE     │ Integer division, then toNat. Negative input times clamp to slot 0;        │
│                                 │                          │           │ protocol execution uses nonnegative times.                                 │
│ 36 Label                        │ 197–220*                 │ AGREE     │ Model duty tags separate a slot HEAD from a round FG action; comp §4.2     │
│                                 │                          │           │ encoding.                                                                  │
│ 43 Label.actTime                │ 197–220                  │ AGREE     │ HEAD at 4Δs+Δ; FG at 4ΔrR+6Δ. For Δ>0 the families cannot coincide.        │
│ 50 RowBody                      │ 230–237                  │ AGREE     │ Two pairs retained; identity and round are in the enclosing auth.          │
│ 56 RowBody.ofRow                │ 230–237*                 │ AGREE     │ Projects both pairs; drops the signer because the wire supplies it.        │
│ 62 RowBody.valid                │ 230–237, 505–518         │ AGREE     │ Empty or height≥1; target existence is by type. No extra finality-height   │
│                                 │                          │           │ bound is imposed.                                                          │
│ 68 HeadWire                     │ 225–228                  │ AGREE     │ Signed label and block encode seat, slot, head; wrong label constructors   │
│                                 │                          │           │ remain representable until decoding.                                       │
│ 70 RowWire                      │ 230–237                  │ AGREE     │ Signed body; round and fixed identity are encoded in the FG auth.          │
│ 75 HeadWire.decode?             │ 225–228, 510–511*        │ AGREE     │ Only HEAD seat auth succeeds. Slot, seat, and head are returned without    │
│                                 │                          │           │ resolution checks.                                                         │
│ 85 RowWire.decode?              │ 230–237, 512–513*        │ AGREE     │ Only FG seat auth succeeds; returns round, identity, body.                 │
│ 90 RowWire.round?               │ 230–231                  │ AGREE     │ Projects the decoded FG round, or none.                                    │
│ 93 RowWire.toRow?               │ 230–237                  │ AGREE     │ Keeps identity and both pairs. Round is omitted from FG state input, but   │
│                                 │                          │           │ retained in stored signed rows.                                            │
│ 96 RowWire.valid                │ 505–518                  │ AGREE     │ Decoder and the shared body predicate; same rule for standalone and        │
│                                 │                          │           │ carried rows.                                                              │
│ 102 Msg                         │ 225–263                  │ AGREE     │ Three payload forms. Flat proposal stores erased block, raw votes,         │
│                                 │                          │           │ declared support, and ordered signed rows; DQ1/DQ3 apply.                  │
│ 109 Wire                        │ 225–263                  │ AGREE     │ Auth and payload stay together; no signature-byte model.                   │
│ 112 Input                       │ 505–518, 804–857*        │ AGREE     │ Internal decoded sum; not a new wire format or a validation certificate.   │
│ 122 Wire.decode                 │ 505–518*                 │ AGREE     │ Three valid auth/payload pairs; rejects other combinations. Body checks    │
│                                 │                          │           │ are in wellFormed.                                                         │
│ 130 Wire.block?                 │ 248–255*                 │ AGREE     │ Returns a block only from a decoded proposal.                              │
│ 136 eraseFG                     │ 248–263, 381–403*        │ AGREE     │ Preserves parent, slot, root; removes rows. Structural identity agrees     │
│                                 │                          │           │ locally under root uniqueness.                                             │
│ 142 baseHead                    │ 225–228*                 │ AGREE     │ Maps HEAD seat auth to the base label; maps other auth to none through the │
│                                 │                          │           │ decoder.                                                                   │
│ 147 baseVote                    │ 225–228, 821–823*        │ AGREE     │ Wraps the decoded carried HEAD in a base vote payload; no cache read.      │
│ 150 liftHead?                   │ 1240–1249*               │ AGREE     │ Reads base accessors and reconstructs HEAD auth. Exact for valid pool      │
│                                 │                          │           │ votes; malformed base values may be dropped.                               │
│ 156 baseProposal                │ 248–255, 820–823*        │ AGREE     │ Maps raw and support votes separately. Full signed FG rows remain in       │
│                                 │                          │           │ composite metadata, not in this base projection.                           │
└─────────────────────────────────┴──────────────────────────┴───────────┴────────────────────────────────────────────────────────────────────────────┘
```

`AvailableChainFGSA/Model/Store.lean`

```text
┌─────────────────────────────────┬──────────────────────────┬───────────┬────────────────────────────────────────────────────────────────────────────┐
│ Line and declaration            │ Spec lines               │ Result    │ Comparison and exact difference                                            │
├─────────────────────────────────┼──────────────────────────┼───────────┼────────────────────────────────────────────────────────────────────────────┤
│ 20 State                        │ 339–353, 486–503         │ DISAGREE  │ Declared representation D3: two tree representations, derived σ and slot,  │
│                                 │                          │           │ five extra base fields. The required protocol data remain available.       │
│ 30 initial                      │ 486–503                  │ AGREE     │ Genesis tree and stamp 0; F=J=S=genesis; h_j=0, h_max=1; empty pools,      │
│                                 │                          │           │ leases, results, fastWrite.                                                │
│ 33 State.slot                   │ 711                      │ AGREE     │ Reads only base.now through slotOf.                                        │
│ 36 finalized                    │ 558–561, 789–802         │ AGREE     │ Returns fg.F, with full FG block data.                                     │
│ 38 confirmed                    │ 559–560                  │ AGREE     │ Returns base.stableRecord = S.                                             │
│ 40 stable                       │ 560–561                  │ AGREE     │ Exactly confirmed; no separate stable output.                              │
│ 43 activeCompatible             │ 360–361                  │ AGREE     │ Tests compatibility only. It is the predicate for a stored block; by       │
│                                 │                          │           │ itself it does not test tree membership.                                   │
│ 48 actView                      │ 363–366                  │ AGREE     │ Filters only base.blocks by compatibility with F. Keeps votes and original │
│                                 │                          │           │ stamps, including inactive-head votes.                                     │
│ 53 onView                       │ 363–366*                 │ AGREE     │ Runs a base step on actView and restores cumulative blocks. Used here only │
│                                 │                          │           │ with steps that preserve blocks.                                           │
│ 57 normalizeS                   │ 565–566, 778–781,        │ AGREE     │ Keeps S exactly when F precedes S; otherwise sets S to erased F. Creates   │
│                                 │ 890–892                  │           │ no lease or result.                                                        │
│ 66 reconcile                    │ 474–484, 874–894         │ AGREE     │ Drops conflicting leases; filters all fastWrite sets; empties conflicting  │
│                                 │                          │           │ results while keeping keys; normalizes S. Other fields stay.               │
│ 77 leaseOf                      │ 293–294                  │ AGREE     │ First matching target deadline; exact when lease keys are unique at the SA │
│                                 │                          │           │ level. D4 applies to arbitrary duplicate rows.                             │
│ 82 fastWriteAt                  │ 297–298, 457–461         │ AGREE     │ Distinguishes missing gate from an evaluated empty set. Exact with unique  │
│                                 │                          │           │ keys.                                                                      │
│ 87 blockExcluded                │ 178–182                  │ AGREE     │ Excludes only incompatibility with F. A finalized ancestor is compatible   │
│                                 │                          │           │ and is not excluded.                                                       │
└─────────────────────────────────┴──────────────────────────┴───────────┴────────────────────────────────────────────────────────────────────────────┘
```

`AvailableChainFGSA/Model/Handlers.lean`

```text
┌─────────────────────────────────┬──────────────────────────┬───────────┬────────────────────────────────────────────────────────────────────────────┐
│ Line and declaration            │ Spec lines               │ Result    │ Comparison and exact difference                                            │
├─────────────────────────────────┼──────────────────────────┼───────────┼────────────────────────────────────────────────────────────────────────────┤
│ 11 admitHead                    │ 831–842                  │ AGREE     │ GridCO.admitVote keeps current/previous labels, at most two distinct votes │
│                                 │                          │           │ per seat, and first receipt stamps.                                        │
│ 17 admitRow                     │ 433–439, 844–857         │ AGREE     │ Window test r+wF<now is the lower-bound test. Decoded (round, identity),   │
│                                 │                          │           │ full-row duplicates, cap≥2. Spec cap=2 is equivalent on valid pools.       │
│ 28 parentFG                     │ 519–522                  │ AGREE     │ Unique erased-parent lookup. Uses the full erased chain rather than root   │
│                                 │                          │           │ only; DQ1/DQ3 and D4 delimit equivalence.                                  │
│ 33 fgBlock                      │ 818–819, 902–912*        │ AGREE     │ Stored parent plus slot, root, ordered decoded rows. Invalid rows can be   │
│                                 │                          │           │ dropped here, but blockAccepted rejects them before this construction is   │
│                                 │                          │           │ admitted.                                                                  │
│ 42 blockAccepted                │ 530–536, 806–817         │ AGREE     │ All acceptance guards precede writes. Root duplicate test is stronger      │
│                                 │                          │           │ outside the spec root idealization (DQ2). Parent membership is checked by  │
│                                 │                          │           │ caller.                                                                    │
│ 60 admitBlock                   │ 804–829                  │ AGREE     │ Base insertion/stamp/votes; FG insertion and finality; save original wire; │
│                                 │                          │           │ reconcile on F change; then row handlers. Base/FG agreement requires       │
│                                 │                          │           │ coherent stores.                                                           │
│ 77 process                      │ 804–857                  │ AGREE     │ Dispatches decoded input, no ingress check. This is the handler layer, not │
│                                 │                          │           │ complete checked receipt; DQ14. Copying row auth preserves it.             │
│ 91 wellFormed                   │ 247–255, 505–518         │ DISAGREE  │ Declared DQ14 strengthening: parent-slot and row-round checks also run at  │
│                                 │                          │           │ ingress. Spec leaves them at acceptance. Refused inputs still cause no     │
│                                 │                          │           │ store writes.                                                              │
└─────────────────────────────────┴──────────────────────────┴───────────┴────────────────────────────────────────────────────────────────────────────┘
```

`AvailableChainFGSA/Model/Clock.lean`

```text
┌─────────────────────────────────┬──────────────────────────┬───────────┬────────────────────────────────────────────────────────────────────────────┐
│ Line and declaration            │ Spec lines               │ Result    │ Comparison and exact difference                                            │
├─────────────────────────────────┼──────────────────────────┼───────────┼────────────────────────────────────────────────────────────────────────────┤
│ 14 fastSet                      │ 761–775, 457–461         │ AGREE     │ Same pre-gate confirmation and whole-result veto; non-genesis prefixes     │
│                                 │                          │           │ passing τ≤prefixSupport. Caller supplies actView. Slow-only writes do not  │
│                                 │                          │           │ enter.                                                                     │
│ 25 gateStep                     │ 754–782                  │ AGREE     │ Saved label skips SA gate and fastWrite append. Fresh label uses           │
│                                 │                          │           │ slowLeasePolicy and actView; normalizeS runs in both cases.                │
│ 35 clockPre                     │ 683–694, 709–752         │ DISAGREE  │ Protocol expiry and scheduled release agree; extra                         │
│                                 │                          │           │ freeze/early/releaseSnapshot writes are D3. Release differs on arbitrary   │
│                                 │                          │           │ retimed states as D2 explains.                                             │
│ 52 clock                        │ 683–694, 709–752         │ AGREE     │ Pre-step then gate at 4Δr+6Δ; release at 4Δr+5Δ. Duties are separate pure  │
│                                 │                          │           │ reads, as M9 requires. Does not enforce once-only public ticks itself.     │
└─────────────────────────────────┴──────────────────────────┴───────────┴────────────────────────────────────────────────────────────────────────────┘
```

`AvailableChainFGSA/Model/Frame.lean`

```text
┌─────────────────────────────────┬──────────────────────────┬───────────┬────────────────────────────────────────────────────────────────────────────┐
│ Line and declaration            │ Spec lines               │ Result    │ Comparison and exact difference                                            │
├─────────────────────────────────┼──────────────────────────┼───────────┼────────────────────────────────────────────────────────────────────────────┤
│ 12 controls                     │ 616–633                  │ AGREE     │ storeControls reads F, h_max, h_j, J, and contest witnesses from full      │
│                                 │                          │           │ cumulative fg.TF.                                                          │
│ 14 fullTree                     │ 1033–1037                │ AGREE     │ storeFrame(full TF) uses live controls, F/Z ancestry, and witnesses in     │
│                                 │                          │           │ full TF.                                                                   │
│ 17 erasedList                   │ 1025–1037*               │ AGREE     │ Membership image of the FG set in base insertion order; exact with         │
│                                 │                          │           │ baseTree correspondence. Root/score order, not list order, decides a valid │
│                                 │                          │           │ walk.                                                                      │
│ 22 liveRoot                     │ 648–655, 1086–1098       │ AGREE     │ Live deadlines and full filtered membership. Fold starts at Z; all         │
│                                 │                          │           │ candidate targets extend Z, so the seed cannot defeat a deeper target.     │
│                                 │                          │           │ Greater-root ties.                                                         │
│ 32 eligible                     │ 1063–1072                │ AGREE     │ Parent state height < live lo, or strict majority, or current store slot.  │
│                                 │                          │           │ Parent lookup uses full TF. No cached resolved flag.                       │
│ 39 headInTree                   │ 1074–1107                │ AGREE     │ GHOST over the supplied tree, starting at the full-tree live root; score   │
│                                 │                          │           │ uses cumulative membership, eligible uses live controls.                   │
│ 45 getHead                      │ 1109–1114                │ AGREE     │ Passes full filtered tree to headInTree.                                   │
│ 50 proposalsAt                  │ 190–193, 1288–1293*      │ AGREE     │ Reads composite proposal metadata by block slot; no active filter, no      │
│                                 │                          │           │ base.proposals.                                                            │
│ 58 voterBlocks                  │ 598–606, 1219–1226       │ AGREE     │ Strict pre-freeze stamp OR ancestry of an admitted current-slot block,     │
│                                 │                          │           │ both in cumulative TF. No extra view arm.                                  │
│ 66 headVotes                    │ 606–612, 1283–1294       │ AGREE     │ Strict stamped pool votes union carried raw votes of all admitted          │
│                                 │                          │           │ current-slot proposals; deduplicates full base votes.                      │
│ 76 headSupport                  │ 423–430, 1286–1293       │ AGREE     │ Frozen arm resolves against current actView with both strict stamps.       │
│                                 │                          │           │ Carried arm uses original declarations, cumulative membership and valid    │
│                                 │                          │           │ head slot.                                                                 │
│ 88 headVote                     │ 1276–1302                │ AGREE     │ Slot 0 gives genesis. Otherwise filters voterBlocks with live controls,    │
│                                 │                          │           │ then walks from full-tree liveRoot. Signing/emission are outside this pure │
│                                 │                          │           │ read.                                                                      │
│ 95 proposerVotes                │ 1240–1243                │ AGREE     │ Entire previous-slot pool, including unresolved votes.                     │
│ 97 proposerSupport              │ 1240–1243*               │ AGREE     │ Current active membership and valid head slot. Stored timestamps are       │
│                                 │                          │           │ finite, so this is resolutionTime<infinity. Missing own docstring: N4.     │
│ 103 chainWireRows               │ 552–553, 1264–1265*      │ AGREE     │ Original signed rows from every stored proposal on H’s chain; rounds       │
│                                 │                          │           │ remain in the wires.                                                       │
│ 108 blockWireRows               │ 550–551, 1261–1263*      │ AGREE     │ Both block slot-round and row round must be in I. Reads original metadata  │
│                                 │                          │           │ across all admitted branches.                                              │
│ 119 proposalRows                │ 544–556, 1255–1274       │ AGREE     │ Removes chain rows and full-row duplicates; keeps pool order; adds         │
│                                 │                          │           │ distinct block rows until two per auth. On admitted FG rows auth equality  │
│                                 │                          │           │ is exactly (round, identity) equality.                                     │
│ 131 propose                     │ 1236–1253                │ DISAGREE  │ Parent, pools and rows agree at scheduled s=Σ.s>0. Root formula can        │
│                                 │                          │           │ collide (D1). Returns unsigned payload, not broadcast/self-delivery; M9/T7 │
│                                 │                          │           │ projection.                                                                │
│ 141 fgHead                      │ 1318–1323                │ AGREE     │ Current-slot raw pool, active resolved support, full filtered tree;        │
│                                 │                          │           │ independent of fast-source existence.                                      │
│ 151 fgBlockOf                   │ 1324–1326*               │ AGREE     │ Unique stored FG block by erasure; D4 covers fallback on inconsistent      │
│                                 │                          │           │ stores.                                                                    │
│ 158 deepest                     │ 260–262, 1327–1335       │ AGREE     │ Maximizes (erased depth, root). Empty returns none. Only a collision at    │
│                                 │                          │           │ the maximal key prevents a nonempty unique choice; D4.                     │
│ 165 fgSource                    │ 666–677, 1327–1335       │ AGREE     │ Current round’s opening-slot fastWrite only, full filtered membership, and │
│                                 │                          │           │ deadline strictly after now; no fallback.                                  │
│ 176 fgInputs                    │ 1315–1338                │ AGREE     │ Source is separate from finality head. HeadFields is derived from that     │
│                                 │                          │           │ head. Dummy fields are outside the coherent-store claim, D4.               │
│ 184 attest                      │ 1304–1313, 1391–1399     │ DISAGREE  │ Declared client projection D3/DQ4/M13: returns body and new record; no     │
│                                 │                          │           │ signature/round wrapper, broadcast, or own-row store write. Core pair and  │
│                                 │                          │           │ retained-record rules agree.                                               │
└─────────────────────────────────┴──────────────────────────┴───────────┴────────────────────────────────────────────────────────────────────────────┘
```

The inventory below checks all consumers in plan lines 357–378. “Agree” concerns the block set and read source; D2 still limits release equivalence outside scheduled execution.

```text
┌──────────────────────────┬───────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────┐
│ Plan consumer            │ Source and spec                                                   │ Result                                                        │
├──────────────────────────┼───────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────┤
│ Confirmation / gate      │ Clock.lean:14,25 → actView → SA.confirmation/gate; spec 363–379,  │ Agree: active blocks, genesis anchor, no FJ band. Slow        │
│                          │ 754–782, 1118–1177.                                               │ windows read genuine, not G.                                  │
│ Release / resolution     │ Clock.lean:48; Frame.lean:78 → resolvedBefore(actView); spec      │ Agree: active heads and original stamps; D2 concerns          │
│                          │ 420–432, 744–752, 973–980.                                        │ equivocation cutoff.                                          │
│ Late count /             │ GridCO.Protocol:378–383, 145–160; spec 430–431, 1041–1047,        │ Agree: signed raw votes; no active-head requirement for       │
│ equivocation             │ 1135–1145.                                                        │ participation/equivocation.                                   │
│ H / contest / frame      │ Frame.lean:12,14 → SimplexFG.Store:77–85; spec 616–646.           │ Agree: full cumulative TF and live caches.                    │
│ V_s block view           │ Frame.lean:58; spec 598–606, 1219–1226.                           │ Agree: cumulative TF, strict block stamps, current proposal   │
│                          │                                                                   │ paths.                                                        │
│ HEAD raw merge           │ Frame.lean:50,66; spec 190–193, 1283–1291.                        │ Agree: original composite proposals, even after they leave    │
│                          │                                                                   │ act.                                                          │
│ Frozen support           │ Frame.lean:76–78; spec 423–430, 1286–1287.                        │ Agree: resolves again against current act, from receipt       │
│                          │                                                                   │ stamps.                                                       │
│ Carried support          │ Frame.lean:79–84; spec 425–428, 1292–1293.                        │ Agree: cumulative head membership, valid label/slot, original │
│                          │                                                                   │ declaration.                                                  │
│ Proposal / finality head │ Frame.lean:45,97,131,141; spec 1109–1114, 1240–1246, 1318–1326.   │ Agree: full filtered tree; active support. D1 limits proposal │
│                          │                                                                   │ roots.                                                        │
│ live_root                │ Frame.lean:22; spec 648–664, 1086–1098.                           │ Agree: full filtered tree and live leases; Z only when no     │
│                          │                                                                   │ deeper target exists.                                         │
│ C_fg                     │ Frame.lean:165; spec 666–677, 1327–1335.                          │ Agree: exact rR fastWrite, live lease, full filtered tree,    │
│                          │                                                                   │ deepest by depth/root.                                        │
│ Row inclusion            │ Frame.lean:103–127; spec 544–556, 1255–1274.                      │ Agree: rowPool plus original signed rows from composite       │
│                          │                                                                   │ proposals in cumulative T.                                    │
└──────────────────────────┴───────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────┘
```

The cache and call-chain check passes. This is a data-dependence check of protocol choices and outputs. A structure copy can carry model fields, and a cache writer can read its previous value to append or advance it. Those operations do not give a duty or output a dependency on that value.

The output leaves are `finalized → st.fg.F`, `confirmed → st.base.stableRecord`, and `stable → confirmed` (`Store.lean:36–40`). No other helper is called.

The duty paths are:

- `headVote → voterBlocks → stampBlock/freezeTime`; `headVotes → votesAt/stampVote/proposalsAt/baseVote`; `headSupport → resolvedBefore(actView)` and the original carried declarations; then `storeFrame → storeControls/filteredFrom` and `headInTree`.
- `propose → proposerVotes/proposerSupport → votesAt/blockKnown(actView)`; `getHead → fullTree/headInTree`; `proposalRows → chainWireRows/blockWireRows/RowWire.round?`; and `liftHead?` through base accessors.
- `attest → fgInputs → fgSource/fgHead/fgBlockOf`; `fgSource → fullTree/fastWriteAt/leaseOf/deepest`; `fgHead → votesAt/blockKnown(actView)/getHead`; then `HeadFields.ofBlock → derive`, and `createRow → finality_pair/height_pair/record_row`.
- Shared choice path: `headInTree → liveRoot/fullTree/controls`, plus `GridCO.ghost → ghostWalk → ghostStep`, `GridCO.goldfishScore → seats/seatVotes/equivocates/headTarget?/headLabel?`, and `eligible → hOf/controls/State.slot`. These helpers read block geometry, rows, votes, stamps, live FG caches, or protocol leases. None reads a model-only field.

The imported implementations checked were `AvailableChainGridCO/Model/Protocol.lean:67–190`, `:370–481`; `AvailableChainSA/Model/Protocol.lean:68–85`; `AvailableChainSimplexFG/Store.lean:30–85`; `AvailableChainSimplexFG/Frame.lean:17–115`; and `AvailableChainSimplexFG/Client.lean:70–153`. I also read the chain transition behind `derive` (`ChainState.lean:95–172`). On a finite structural tree, each GHOST step increases depth, so the distinct-tree length supplies enough fuel. The greater root wins a score tie. GridCO stops on equal-root distinct maximal children; the spec root premise excludes that case. The extra membership and slot checks in `goldfishScore` are already satisfied by the duty-supplied support lists.

```text
┌─────────────────────┬───────────────────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────┐
│ Model-only field    │ Writers or self-maintenance                                               │ Duty/output read                                      │
├─────────────────────┼───────────────────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────┤
│ frozen              │ clockPre → onView → GridCO.freeze (:241–246), appends raw/support/domain  │ None. Frame local variables named frozen are newly    │
│                     │ snapshots.                                                                │ derived lists.                                        │
│ early               │ clockPre (:44) appends GridCO.earlyVotes, which resolves from             │ None. savedEarly (:373) is not called.                │
│                     │ votes/stamps.                                                             │                                                       │
│ releaseSnapshots    │ clockPre → SA.release → GridCO.release (:411–418), appends a snapshot.    │ None. Release count reads votes/stamps, not           │
│                     │                                                                           │ snapshots.                                            │
│ goldfishRecord      │ gateStep → SA.gate → GridCO.gate (:472), advances G from old G.           │ None. S uses stableRecord; G does not affect the      │
│                     │                                                                           │ guard, leases, or S.                                  │
│ base.proposals      │ admitBlock → GridCO.admitProposal (:324), appends the base projection.    │ None. Frame reads st.proposals, which retains full    │
│                     │                                                                           │ signed rows.                                          │
└─────────────────────┴───────────────────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────┘
```

G3 minor 4 passes through the full duty call chains. No duty reaches `GridCO.act` (actual definition at `Protocol.lean:295`), `voterView` (:251), `voterSupportView` (:257), or `voterTree` (:263), including through the SA aliases. No path reaches `frozenAt` (:235), `carriedRaw`, or `carriedSupport` in GridCO. The composite `actView` is a different function: it filters blocks for compatibility with F and does not read a freeze cache.

M11 passes for all five FG-SA model files: each p-dependent declaration uses `p.n`; no such declaration retains a free `n`. Store's section variable `n` is not used by `State.slot`. Declarations with a free `n` have no Params argument. Imported SA/GridCO helpers retain their older APIs; composite calls instantiate their n with p.n.

J1 passes as stated: the only auth pattern matches in the composite are `HeadWire.decode?` (`Objects.lean:76`), `RowWire.decode?` (:86), and `Wire.decode` (:123). `process` copies auth at `Handlers.lean:80`; it does not inspect its constructors. `proposalRows` compares auth values at `Frame.lean:126`; on admitted rows this is equality of the encoded identity/round pair. This is a dependence on the declared v1 representation, but not a fourth auth pattern match. `liftHead?` uses the permitted GridCO accessors. Imported GridCO code performs its own base-auth matches; J1 does not require rewriting that library.

The Frame hand computations below use `pT`: Δ=1, n=4, k=2, R=2, wF=1, δt=1; quorum q_F=3. The three rows in B1 justify genesis at height 1 and advance to height 2, with entry B1. B2 justifies B1 at height 2 and advances to height 3, with entry B2. B3 finalizes B1 at entry height 2, then its mature timeout quorum advances to height 4 with entry B3. Thus `stA` has `(F,J,h_j,H)=(B1,B1,2,4)`, no contest, `Z=B1`, and `lo=3`. Its full filtered tree is `{B1,B2,B3}`. These values follow from the transition, not just from the imported test assertions.

All test line numbers in this table refer to `AvailableChainFGSA/Tests/Smoke.lean` at d5171fc. The “missed error” column gives concrete wrong alternatives; it does not say that the current definition has those errors.

```text
┌──────────────────────────┬──────────────────────┬───────────────────────────────────────────────────────────────────────────┬──────────────────────────────────────────────────────────────────┐
│ Test lines               │ Spec                 │ Hand result                                                               │ Missed error or strength                                         │
├──────────────────────────┼──────────────────────┼───────────────────────────────────────────────────────────────────────────┼──────────────────────────────────────────────────────────────────┤
│ 350–351; stC0            │ 669–677              │ a_1=d_2=14. No label-2 support: fastWrite[2]=[]. No source, empty height  │ Correct. Rejects unconditional S/root fallback; no older-set or  │
│                          │                      │ pair. S=Z=b1.                                                             │ slow-lease candidate is present (N3).                            │
│ 358; stC1                │ 1327–1335            │ r=1, opening slot 2. B2 is filtered, in fastWrite[2], and 14<21.          │ Correct. Singleton does not test deepest selection; choosing any │
│                          │                      │ Source=B2.                                                                │ live lease can pass here (N3).                                   │
│ 360–362                  │ 1329                 │ Deadline=14 equals now; strict 14<14 is false. Source=none.               │ Correct. Detects replacing strict < with ≤.                      │
│ 366                      │ 1068–1071            │ At v_4=17, all block stamps 12<z_3=15. Walk starts B1; h(B1)=2<3 admits   │ Correct. Full tree and voter view coincide; wrong view           │
│                          │                      │ B2; h(B2)=3 is not <3, no votes, slot(B3)=3≠4. Stop B2.                   │ controls/full-tree filtering pass (N1).                          │
│ 368–369                  │ 260–262              │ Both blocks have depth 1. Root 9>5, so choose the slot-2 root-9 block.    │ Correct. Tests root tie only. Largest-slot or largest-root-only  │
│                          │                      │                                                                           │ selection also passes this one example.                          │
│ 382–383; stH0/stH        │ 423–430              │ b1′ stamp 8, vote stamp 9, cutoff 11. Initially raw and support include   │ Correct. Detects support on cumulative T. No saved frozen        │
│                          │                      │ vH. After F=B1, raw still includes it; active support is empty.           │ snapshot is populated; a cache-fallback bug can escape.          │
│ 396–397; stX             │ 190–193, 1290–1291   │ Carried vote stamp 12≥11 excludes it from frozen pool. X is stored but    │ Correct. Detects active filtering of proposals and omission of   │
│                          │                      │ inactive after F=B1. Composite proposal metadata still contributes vX.    │ raw proposal arm. Declared support is empty (N2).                │
│ 412–413; stP             │ 544–556, 1255–1274   │ I={0,1}. Remove B1/B2 chain rows. Keep B3 rows and q1,q2. q3 is not in    │ Correct, including order. No block-only row enters; deleting     │
│                          │                      │ pool; two identity-3 pool rows already fill its group.                    │ blockWireRows passes (N2).                                       │
│ 419–423; liveRoot        │ 648–655, 1086–1098   │ Live B2 lease gives b2; deadline 12 at now 12 is expired; unstored b1′ is │ Correct. Active-membership-only filtering can pass; no stored    │
│                          │                      │ not in the full tree, so both latter cases give b1.                       │ active-but-FJ-excluded target (N3).                              │
│ 429–430; propose         │ 1236–1274            │ At t_4=16, no slot-3 votes. Walk gives b2. Root=4×(5+1)=24. I={1,2}; B1   │ Correct for DQ10 formula. Empty vote lists miss positive         │
│                          │                      │ rows are old/on-chain, B2 rows on-chain, B3 rows remain.                  │ proposer support; omitted lower-window test can also pass this   │
│                          │                      │                                                                           │ fixture.                                                         │
│ 433–434; fgHead/fgInputs │ 1318–1326            │ At slot 3, B2 is band eligible and B3 is current-slot eligible. Head=b3;  │ Correct. Current-slot clause matters. Live and head              │
│                          │                      │ fields=(2, root(B1)=1, 2).                                                │ justification are equal here (N5).                               │
│ 439–441; attest          │ 1304–1313, 1379–1387 │ Source=B2 gives height 3, entry root 5. Head B3 gives h_j=h_F=2, so no    │ Correct. Expected expression uses derive for the root, but hand  │
│                          │                      │ finality pair. Initial record permits target (3,5,false).                 │ value is 5. No positive finality pair or record-write assertion  │
│                          │                      │                                                                           │ (N5).                                                            │
└──────────────────────────┴──────────────────────┴───────────────────────────────────────────────────────────────────────────┴──────────────────────────────────────────────────────────────────┘
```

For the read-time-resolution test, a further useful check is to populate `base.frozen` before the F advance, then keep its old resolved vote while making the current active test reject that vote. Changing all five model-only fields independently while holding protocol fields fixed must leave every duty and output unchanged. The source call-chain check establishes the intended independence; the current Smoke fixtures do not give a general cache-independence test.

The stay-close-to-DC check uses the DC contract stated in this spec's Relay and Frame text. It does not claim a separate audit of every revision of the DC repository.

```text
┌───────────────────────────────────────────────────┬────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────┐
│ Frame read or adaptation                          │ Spec authority                             │ Licensed?                                                                 │
├───────────────────────────────────────────────────┼────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────┤
│ Cumulative admitted tree; retain metadata after F │ 169–193, 355–379, 598–614                  │ Yes. This preserves DC receipt and admission-based merge behavior. No     │
│ moves                                             │                                            │ eager tree pruning was found.                                             │
│ Live H/J/F caches; full-store contest; band floor │ 616–646, 982–1037                          │ Yes. FJ changes the contested root/band explicitly. Controls never come   │
│ lo                                                │                                            │ from the restricted HEAD view. Finality acceptance keeps H−1 separately.  │
│ HEAD witnesses limited to processed view          │ 598–606, 1210–1233                         │ Yes. storeFrame receives voterBlocks; it does not intersect an            │
│                                                   │                                            │ already-filtered full tree. The frame itself remains live.                │
│ Frozen support resolves against current act       │ 420–432, 973–980, 1283–1287                │ Yes. The spec explicitly requires read-time active resolution. Cached     │
│                                                   │                                            │ support is not an allowed substitute.                                     │
│ Carried support tests full T, not act             │ 425–428, 608–613, 1292–1293                │ Yes. Explicit DC behavior. An incompatible head cannot support a tested   │
│                                                   │                                            │ descendant of F, but the original declaration remains readable.           │
│ Cumulative tree passed to GridCO.goldfishScore    │ 1039–1047; 423–428                         │ Yes for duty-supplied lists. Support is already resolved or               │
│                                                   │                                            │ carried-and-checked; raw equivocation remains unrestricted. No extra tree │
│                                                   │                                            │ cutoff is introduced.                                                     │
│ Full filtered live lease root replaces saved      │ 648–664, 1086–1107                         │ Yes, explicit change (b). The start may be outside the HEAD view. A       │
│ grade 1                                           │                                            │ compatible lease outside full FJ filtering has no choice authority.       │
│ Full-tree proposer and current-slot finality head │ 614, 1210–1213, 1240–1246, 1318–1326       │ Yes. Finality fields come from the selected head state, not from the live │
│                                                   │                                            │ lex pair or the fast source.                                              │
│ Fresh fastWrite[rR] source replaces DC source     │ 666–679, 1327–1338                         │ Yes, explicit change (b). No grade, S, old fast set, or slow-only         │
│ selection                                         │                                            │ fallback is licensed.                                                     │
│ Rows from original cumulative metadata and round  │ 544–556, 1255–1274                         │ Yes. Both candidate sources and pool priority are explicit. Ordered       │
│ window                                            │                                            │ first-fit selection chooses among permitted alternatives.                 │
│ Formula root and unsigned pure duty outputs       │ 167, 521, 1247–1252, 1299–1301, 1311       │ Root collisions: no spec license; DQ10 restricts model coverage. Pure     │
│                                                   │                                            │ output projection: plan license M9/DQ4; T7 must supply signing,           │
│                                                   │                                            │ scheduling and own-row processing.                                        │
└───────────────────────────────────────────────────┴────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────┘
```

The model's live-view definitions agree with the plan inventory and the spec under the stated boundary. N1–N5 identify the remaining review fixes. D1–D4 must stay explicit in later claims; in particular, this report gives no root-freshness theorem, no arbitrary-clock simulation theorem, and no completed run adapter.
