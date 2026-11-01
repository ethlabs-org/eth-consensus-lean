I found two blocking errors. The plan needs revision before implementation. This audit changed no files.

Evidence keys: `P` = [plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md), `R` = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md), `S` = [FG-SA spec](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex), `F` = [r148](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fj-redteam.md), `B` = [DC Blocks.lean](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusModel/Objects/Blocks.lean), `L` = [Lake library configuration](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/lake/Lake/Config/LeanLibConfig.lean). Numbers after keys are line numbers.

```text
┌─────┬──────────┬─────────┬────────────────────────────────┬──────────────────────────────┬────────────────────────────────┐
│ ID  │ Severity │ Task    │ Finding                        │ Evidence                     │ Proposed fix                   │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G01 │ BLOCKING │ 8       │ The stated finality rule drops │ P:828; S:1184                │ Restore target, timeout and    │
│     │          │         │ all record guards.             │                              │ lock guards; prove client      │
│     │          │         │                                │                              │ record safety.                 │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G02 │ BLOCKING │ 13      │ twoChanges_Fmove is false: an  │ P:1101; P:1116; F:781        │ Preserve band witnesses or     │
│     │          │         │ F move can remove members      │                              │ compare D above F′; split      │
│     │          │         │ of D.                          │                              │ the boundary case.             │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G03 │ MAJOR    │ 6–7     │ The prescribed selector does   │ P:570; B:295                 │ Define tie handling; require    │
│     │          │         │ not implement the stated       │                              │ root injectivity or provide    │
│     │          │         │ equal-key behavior.            │                              │ an explicit total order.       │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G04 │ MAJOR    │ 7       │ on_block omits FG admission    │ P:625; P:655; S:694          │ Use an admitted tree and       │
│     │          │         │ and can raise H from a         │                              │ enforce F ⪯ B at its boundary. │
│     │          │         │ rejected branch.               │                              │                                │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G05 │ MAJOR    │ 7       │ CacheInv says nothing about    │ P:681; P:708; R:743          │ Prove basis membership, F and  │
│     │          │         │ fBasis. Duty-view premises     │                              │ J carrier properties, and      │
│     │          │         │ have no producer.              │                              │ preservation.                  │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G06 │ MAJOR    │ 8–9     │ Chain finalization replaces    │ P:876; P:888; R:1875         │ Connect head fields to a block │
│     │          │         │ the required provenance of     │                              │ and prove finality-row and QC  │
│     │          │         │ emitted finality rows.         │                              │ provenance.                    │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G07 │ MAJOR    │ 13      │ Nested views replace settled   │ P:1053; P:1074; R:3009       │ State laws over evidence bits │
│     │          │         │ evidence. The effective frame  │                              │ and the normalized root; mark │
│     │          │         │ is also defined incorrectly.   │                              │ the restricted result partial. │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G08 │ MAJOR    │ 14      │ Several full pins cover only   │ P:1169; P:1172; P:1183       │ Record coverage per clause and │
│     │          │         │ part of the registered text.   │                              │ name every omitted result.     │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G09 │ MAJOR    │ 14      │ The pin checker succeeds on    │ P:1149; P:1223; P:1232       │ Reject missing or empty input; │
│     │          │         │ missing input and does not     │                              │ pin the executable spec and    │
│     │          │         │ pin the executable spec.       │                              │ exact source mappings.         │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G10 │ MAJOR    │ 1–14    │ Builds can omit new modules.   │ P:189; P:1125; P:1245; L:46 │ Maintain both root imports;    │
│     │          │         │ The final check is not a full  │                              │ check public theorem axioms;   │
│     │          │         │ project build.                 │                              │ run the full handoff build.    │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G11 │ MINOR    │ 14      │ Registry status is stale.      │ P:1196; P:1285; R:1661;     │ Add frameFeasible pins; update │
│     │          │         │ The pending entries now exist. │ R:2678                       │ headReachesLo and frameCompat. │
├─────┼──────────┼─────────┼────────────────────────────────┼──────────────────────────────┼────────────────────────────────┤
│ G12 │ MINOR    │ 4,11,12 │ The proposed geometry-helper   │ P:409; P:951; P:997;        │ Put entry geometry in Task 4; │
│     │          │         │ dependency can make an import  │ P:1037                       │ correct helper locations and   │
│     │          │         │ cycle. Some citations differ.  │                              │ list actual dependencies.      │
└─────┴──────────┴─────────┴────────────────────────────────┴──────────────────────────────┴────────────────────────────────┘
```

**G01 — The client rule permits slashable emissions.**  
Task 8 says that `hd.h_j > hd.h_F` is sufficient to emit a finality pair. The spec also requires a compatible recorded target, no recorded timeout, and a compatible lock. These checks remain necessary when NJ is removed. For example, after the client records a timeout at height `m`, a head can expose a justification at `m`. The plan’s stated rule emits its finality pair and thus creates E1 evidence against the earlier timeout. Task 8’s instruction to port DC conflicts with its explicit rule. Restore the three guards and add rejection tests for each. Port the local record invariant and preservation proofs as well. [Spec:1180](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex:1180), [DC client:160](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusModel/Protocol/ValidatorClient.lean:160).

**G02 — `twoChanges_Fmove` has a counterexample with valid entries and unique roots.**  
Use four unit-weight validators, quorum three, and `timeoutDelay = 1`. Construct this chain:

- `B1`, slot 1: three targets for `(1, genesis)`. Its state height is 2.
- `B2`, slot 2: three targets for `(2, B1)`. Its state height is 3, with justified pair `(2, B1)`.
- `B3`, slot 3: three timeouts for `(3, B2)`, each with finality pair `(2, B1)`. Its state height is 4 and it finalizes `B1`.

Take `Vw = {genesis, B1, B2, B3}`, `m = 4`, `F = genesis`, and `F′ = B1`. All hypotheses of `twoChanges_Fmove` hold; `hP` is vacuous because there is no justification at height 3. Both frames are gap frames with `lo = 3`. However, the old `D` contains genesis and the new `D` does not. An in-memory evaluation of the stated transition confirms these values.

The proof reverses ancestry: `B ⪯ W` and `F′ ⪯ W` do not imply `F′ ⪯ B`. Preserve the band witnesses, or state equality after cutting the old domain at `F′`. Also split finalization *below* `m−1` from finalization *at* `m−1`: the strict inequality in `finalLock` does not establish `hW` at equality. [Plan:1101](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:1101).

**G03 — The proposed `pickPair` port has the wrong tie behavior.**  
DC’s `pickUnique?` returns `none` when two distinct candidates satisfy the predicate. It does not choose one of them. The plan permits distinct blocks with the same greatest key and says that `pickPair` returns one. With the prescribed DC selector, two distinct height-2 entries with the same root cause fallback to `(0, genesis)`. This falsifies `fBasis_lexMax`; adding the second candidate can also falsify `lexMax_mono`. Neither theorem requires root injectivity. Specify a computable selector with the promised behavior, or make collision freedom part of the view interface and theorem hypotheses. [Plan:570](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:570), [DC selector:295](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusModel/Objects/Blocks.lean:295).

**G04 — The store boundary does not preserve FG admission.**  
The spec separates the raw tree from the FG-admitted tree. It inserts a block into the latter and calls `update_finality` only if the current `F ⪯ B`. The plan calls its tree “processed” and inserts every block passed to `on_block`; its stated precondition concerns only the parent. An off-F branch can therefore raise `h_max`, enter duty views, and change the frame. Ordinary block validity does not supply the missing FG guard. Either enforce the guard or expose an explicitly named admission operation whose contract requires it. [Spec:338](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex:338), [Spec:694](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex:694), [Plan:655](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:655).

**G05 — The F-basis lemma assumes the property that the store must establish.**  
Changing `st.fBasis` to the empty set leaves every field of `CacheInv` unchanged. Thus `CacheInv` cannot prove that a duty view closed under `fBasis` contains either required carrier. `fBasis_lexMax` only assumes that a suitable `K` exists. Add an invariant that records `fBasis ⊆ T`, an accepting carrier that finalizes the current F, and a saved J carrier whose J extends F. Prove initialization and preservation. These facts must supply the duty-view premises.

The added `hVw` and `hHF` in `fjFrame_D_nonempty` are correct and sufficient; they are not errors. The missing work is to derive them from a retained F carrier. For the later SA walk, also expose the pure geometry facts that put Z in D and give a viable child below `lo`, under ancestor closure. [Plan:681](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:681), [Review:52](/Users/francesco/ethereum/lean/available-chain/docs/audit/fg-plan-async-review.md:52).

**G06 — `provenance_finality` proves a different fact.**  
The registry concerns an emitted finality row and an arbitrary finality QC. The proposed theorem concerns a checkpoint already finalized by `derive D`. A QC need not yet be assembled into such a chain. Moreover, `HeadFields` permits arbitrary values: even with the correct record guards, the initial record can sign fields that have no known justification carrier. This interface is acceptable only with an explicit caller obligation and a theorem for `hd = HeadFields.ofBlock … Hd`.

Add the emitted-row theorem, extract the head’s target certificate, and combine it with the honest-row lemma for a QC. Keep temporal emission facts in the later composition layer and mark that remainder. The existing chain theorem is useful as a helper. Its proof guide also needs correction: a block can finalize the old J and justify a new J in the same transition, so the finalizing block need not be the required justification witness. [Registry:1873](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:1873), [Plan:876](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:876), [Spec:793](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex:793).

**G07 — Growing views do not express the registered settled-phase result.**  
Task 13 assumes `Monotone Vs`. R1 full and HEAD views need not be nested. Settling supplies persistence of the two relevant evidence bits; it does not supply inclusion between all successive views. Thus the proposed result is a restricted theorem, not full coverage of registry item 2.

The plan also defines an effective change using literal `(Z, lo)` and claims that the frame follows from the phase. The registry uses the normalized root `Ẑ = ◇` in F-root phases. Literal F can advance without an effective exclusion. Further, D can grow while phase, Z and lo stay fixed. Export a theorem over evidence presence and persistence, with the registry’s normalized frame. Keep the nested-view theorem as a partial helper. [Plan:1053](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:1053), [Registry:3004](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:3004).

**G08 — `.full` has no consistent meaning in the pin table.**  
Specific gaps remain:

- `fjFrame_lo` proves one projection equation, but its pin says `.full`.
- `accountable` and F monotonicity omit the pinned `finalized ⪯ available` accessor result. That result belongs outside this frame-only module; record the omission.
- `uniqueJust` exports general slashable evidence. It does not export the pinned E2-specific evidence or whole-run uniqueness. The review accepts the DC certificate form, but “full Lean part” must remain distinct from full registry coverage.
- `crossingNeedsTimeout` gives some timeout row. It does not identify an honest member of the target/progress intersection or prove consumption at the maturity slot.
- The Task 13 full tags remain wrong even if the false F-move theorem is removed.

Use clause-level coverage, list all associated Lean names, and name the external obligations. [Pins:1166](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:1166), [Accountability text:2528](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:2528), [Crossing text:2738](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:2738).

**G09 — The checker can report success without checking pins.**  
I ran the proposed shell body in memory with the pin input set to an empty file and then a nonexistent path. Both runs returned status 0. Failures inside the process substitution do not update `status`, and an empty extraction produces no checks. Hash-half searches also do not bind a hash to its registered source path.

All eight proposed `Src` hashes currently match. The spec and DC paper hashes also match the registry. However, neither is in the proposed `Src` list, although the spec controls executable behavior and `frameCompat` cites both. Add explicit executable-source pins, reject missing or empty input, and check exact source associations. A changed file hash requires comparison; it does not always require a new registry id. The registry requires a new id when the statement or hypotheses change. [Plan:1203](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:1203), [Registry policy:8](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:8).

**G10 — A green target build does not ensure that all planned files were checked.**  
Lake defaults to building library roots and their import closure. The plan does not consistently add later modules to the two root files; Task 14 does not add an import of `Pins.lean`. A new file, including its examples, can therefore be omitted from the target build. Require root updates at every task or configure explicit module globs.

The last “Full build” still names only the two new targets. That is suitable during parallel work, but the workspace requires the full project target before handoff. Also check the axioms of all public results, rather than only `accountable`. Add meaningful client rejection tests and a zero-delay transition test. Temporary `sorry` bodies are acceptable only before the checkpoint, as the plan already requires. [Lake:38](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/lake/Lake/Config/LeanLibConfig.lean:38), [Plan:1245](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md:1245), [Workspace rules:35](/Users/francesco/ethereum/lean/AGENTS.md:35).

For **G11**, the registry now contains `ap.headReachesLo.v1` and `fj.frameFeasible.v1`; it also records partial `frameCompat` coverage. These updates are present through registry commit `c9b5314`.

For **G12**, placing a helper in `Certificates.lean` that uses `entry_height` from `CrossingNoFinal.lean` would reverse the existing dependency. Move entry geometry into Task 4. Correct the helper references: `finalized_below_height` is in [Chain.lean:442](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:442), and `nonzero_rows_certificate` starts at [FinalityCertificates.lean:223](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/FinalityCertificates.lean:223).

The remaining source checks support these conclusions:

- The specified H, lex key, `F ⪯ J` filter, contest predicate, Z/lo table and D predicate match r148 and the spec on valid views. The arbitrary-view fallback and selector need G03.
- The chain transition preserves exact-entry matching, finality-before-justification order, timeout maturity and single-height advancement. Removing the NJ field and its guards is faithful to DC-fj.
- The body of `update_finality`, including write order and witness selection, matches the spec once G04’s admitted-tree boundary is supplied.
- The own `FGBlock` type is sound for these static proofs. The AP adapter must later preserve roots, parents, carried rows and derived states. Collision freedom remains an explicit assumption.
- The cited DC counting proofs at `Engine.lean:243/261`, `WholeRunFinalitySafety.lean:140/197`, and `FinalityComparison.lean:50` are independent of SG and NJ recovery. Extract their local dependencies; do not copy their broad import closures or the run-specific collision helper at line 97.
- No proposed mathematical statement needs `δ_t > 0`. The revised contest, genesis, lex-order and stale-cache tests have the correct expectations. The Mac throttle and per-task commit instructions are present.

Coverage below concerns the proposed statements. “Partial-correct” means a valid part remains after the stated interface fixes. “Wrong” means a false statement or a statement about a different subject.

```text
┌───────────────────────┬─────────────────────────────────────────┬──────────────────┐
│ Registry id           │ Lean statement                          │ Coverage verdict │
├───────────────────────┼─────────────────────────────────────────┼──────────────────┤
│ fj.frame.v1           │ fjFrame                                 │ partial-correct  │
│ fj.frame.v1           │ fjFrame_lo; fjFrame_D_viable             │ partial-correct  │
│ fj.frame.v1           │ frameViable_subset_accept;              │ partial-correct  │
│                       │ frameViable_eq_accept_of_noContest;     │                  │
│                       │ frameViable_eq_accept_cut               │                  │
│ fg.accountable.v1     │ accountable; update_finality_F_mono      │ partial-correct  │
│ fg.uniqueJust.v1      │ uniqueJust; uniqueJust_chains            │ partial-correct  │
│ fg.finalLock.v1       │ finalLock                               │ full             │
│ fg.frameCompat.v1     │ fBasis_lexMax                            │ partial-correct  │
│ fg.provenance.v2      │ provenance_honestRow;                    │ partial-correct  │
│                       │ provenance_entry                        │                  │
│ fg.provenance.v2      │ provenance_finality                     │ wrong            │
│ fg.causalCap.core.v1  │ causalCap; causalCap_notRoot             │ partial-correct  │
│ fj.crossingNoFinal.v1 │ crossingNoFinal; crossingNeedsTimeout    │ partial-correct  │
│ fj.inBandLock.v1      │ inBandLock                              │ partial-correct  │
│ fj.twoChanges.core.v1 │ twoChanges; frame_of_phase               │ partial-correct  │
│ fj.twoChanges.core.v1 │ twoChanges_Fmove                         │ wrong            │
│ fj.frameFeasible.v1   │ fjFrame_D_reachesLo;                     │ full             │
│                       │ fjFrame_D_nonempty (pins missing)        │                  │
└───────────────────────┴─────────────────────────────────────────┴──────────────────┘
```

`finalLock` fully covers the static crossing law through its slashable-or form: the registered slashable bound eliminates the evidence branch. `provenance_finality` can remain as an unpinned helper. The NJ entries and the AP head-selection implementation are correctly excluded.

**Verdict: REVISE.** The scope and main frame definition are sound. The client rule, false F-move theorem, missing store invariants and inaccurate coverage claims prevent adoption. These fixes can remain within the FG-only, fj-only scope.

AUDIT COMPLETE: 2 blocking, 8 major, 2 minor