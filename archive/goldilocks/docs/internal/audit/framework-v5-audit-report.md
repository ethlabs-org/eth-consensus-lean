**Verdict: REVISE.** v5 makes useful corrections, but several replacement statements are false or too weak for the proposed composition. I found **5 blocking, 6 major, and 1 minor findings**.

This was a read-only source audit. I did not edit files or run a build. These findings concern the proposed framework; they do not show that the existing Lean proofs are unsound.

I audited the 722-line [v5 design](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:1). The [project log](/Users/francesco/ethereum/lean/available-chain/log.md:78) lists further planned changes. I did not count those changes as fixes to v5.

In the tables:

- `D` means `lean/available-chain/docs/FRAMEWORK-DESIGN.md`.
- `Generic/` and `Strong/` mean the corresponding directories in `AvailableChainStatements/`.
- `GridCO/` and `SAPC/` mean `AvailableChainGridCO/` and `AvailableChainSAPC/`.
- Research filenames refer to `research/async-resilient-committees/tip-stability/codex/`.
- `consensus.tex` means `research/healing/rewrite/consensus.tex`.

The 17 v4 findings have the following disposition.

```text
┌─────┬──────────────┬──────────────────────────────────────────────────────────────┐
│ ID  │ v5 status    │ Reason                                                       │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B01 │ PARTLY FIXED │ Shared facets close the different-getter attack. But putting │
│     │              │ all claim bounds in Instance prevents the advertised Pareto  │
│     │              │ set for one instance. D:235, D:386. See V08.                  │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B02 │ PARTLY FIXED │ Exact inclusion and persistent inclusion are now separated  │
│     │              │ correctly. The schema still permits only up/down directions,│
│     │              │ with no fixed/non-monotone case. D:284, D:298. See V08.       │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B03 │ PARTLY FIXED │ Arbitrary-horizon witnesses close the particular short-run  │
│     │              │ attack. E4 is false for current handlers and still does not │
│     │              │ prove scheduler feasibility. D:172, D:362. See V01, V07.    │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B04 │ PARTLY FIXED │ ArmedRetained correctly focuses on the armed prefix. Retains│
│     │              │ omits the transfer boundary; Settled and HeightRetains have │
│     │              │ new defects. D:486, D:492, D:554. See V02, V04, V06.         │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B05 │ PARTLY FIXED │ P1–P3 separate source bodies, entries and finality origins. │
│     │              │ The AP contract and Harmless lemma still lack the history │
│     │              │ needed to retain other bodies. D:513, D:537. See V03.      │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ B06 │ PARTLY FIXED │ Output recovery, finality heads and recurrence are added.  │
│     │              │ Timed carrier service, full source recovery and the finality│
│     │              │ deadline construction remain open. D:578. See V05, V06.    │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M01 │ FIXED        │ The engine scope now excludes private VRF selection, local │
│     │              │ firing times and other unsupported models. The additive   │
│     │              │ cases need the qualifications below. D:50.                │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M02 │ PARTLY FIXED │ Atomic recording and durable F are specified. Isolation   │
│     │              │ does not cover restore or delivery hooks; label-family and│
│     │              │ rejoin semantics remain incomplete. D:185. See V11.       │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M03 │ FIXED        │ The proposed lift now names the required simulation and   │
│     │              │ claim equivalences. E4 separately blocks the promise to   │
│     │              │ transport every certificate. D:211. See V01.              │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M04 │ PARTLY FIXED │ R1 is correctly marked as a change to DC; the F basis is   │
│     │              │ retained. The anchor result still omits the root and its  │
│     │              │ stated equality names the wrong tree. D:446. See V09.    │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M05 │ PARTLY FIXED │ Minimum horizons are corrected. The new invariant is too  │
│     │              │ broad, and q_s < d_s alone does not supply a causal AP     │
│     │              │ theorem. D:311, D:570. See V02, V03.                     │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M06 │ PARTLY FIXED │ Pareto sets, checked attributes, valid refutations and    │
│     │              │ separate witness transport are correct choices. The typed│
│     │              │ order/transport interface is still absent. D:386. See V08.│
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M07 │ FIXED        │ LM removes the stated dependency on L5 definitions.      │
│     │              │ The resulting dependency graph can be acyclic. D:97–116.│
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M08 │ FIXED        │ Finite families are allowed; infinite liveness and lassos│
│     │              │ are explicitly outside this engine. D:371.              │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ M09 │ FIXED        │ Engine/module hashes, declaration dependencies, toolchain│
│     │              │ and manifest pins close the stated freeze gap. D:394.   │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ N01 │ PARTLY FIXED │ Several missing fields are added. r147 and the blueprint │
│     │              │ now exist, but v5 still treats them as pending inputs.   │
│     │              │ D:421, D:663. See V12.                                  │
├─────┼──────────────┼──────────────────────────────────────────────────────────────┤
│ N02 │ FIXED        │ The validity, availability and implementation-refinement │
│     │              │ exclusions are explicit. noFutureRead is listed. D:716. │
└─────┴──────────────┴──────────────────────────────────────────────────────────────┘
```

The new and remaining v5 findings are below. The IDs are separate from the v4 IDs.

```text
┌─────┬──────────┬─────────┬────────────────────────────────┬───────────────────────────────────┬─────────────────────────────────┐
│ ID  │ Severity │ Section │ Finding                        │ Evidence (file:line)              │ Proposed fix                    │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V01 │ BLOCKING │ E4, 8   │ The mandatory handler law is   │ D:172                             │ Separate handler invocation,    │
│     │          │         │ false for current instances.   │ GridCO/Model/Protocol.lean:300    │ temporary refusal, permanent    │
│     │          │         │ The dependency-origin rule is │ SAPC/Model/Handlers.lean:45       │ rejection and acceptance. Prove │
│     │          │         │ also too restrictive.         │ D:175                             │ actual delivery feasibility.    │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V02 │ BLOCKING │ 7.3     │ Retains is not the source-     │ D:492                             │ Use the explicit Ret predicate  │
│     │          │         │ preservation premise used by  │ fgsa-conditional.md:117           │ and include each source's first │
│     │          │         │ the proof. Its start boundary │ fgsa-conditional.md:140           │ transfer HEAD and view witness. │
│     │          │         │ and tree-membership test fail.│                                   │                                 │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V03 │ BLOCKING │ 7.3–7.5 │ The AP entries do not supply  │ D:513                             │ Specify body-level transfer,    │
│     │          │         │ the stated source-body        │ D:550                             │ compatible history and causal   │
│     │          │         │ induction. Its global scope   │ D:570                             │ cutoffs. Use separate clean,    │
│     │          │         │ is false during recovery and  │ fgsa-adjudicate.md:417            │ reset and Outage invariants.    │
│     │          │         │ can be false during Outage.   │                                   │                                 │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V04 │ BLOCKING │ 7.1,7.4 │ HeightRetains promises to keep│ D:434                             │ Separate harmless old evidence │
│     │          │         │ every valid high block. NJ and│ D:554                             │ above a height from retention  │
│     │          │         │ finalized crossing do not     │ consensus.tex:911                 │ of specified qualifying bodies.│
│     │          │         │ establish that statement.     │ fgsa-adjudicate.md:495            │                                 │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V05 │ BLOCKING │ 7.3–7.5 │ The recovery/finality chain   │ D:511                             │ Add timed row service, carrier │
│     │          │         │ still lacks closed interfaces │ D:578                             │ and source-window obligations; │
│     │          │         │ for several required steps.   │ fgsa-adjudicate.md:635            │ keep first finality conditional│
│     │          │         │                               │ fgsa-adjudicate.md:670            │ until all three timed gaps close.│
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V06 │ MAJOR    │ 7.3     │ Settled does not fix the      │ D:486                             │ State a numerical frontier and│
│     │          │         │ numerical band. Constant F    │ fgsa-conditional.md:127           │ a stopped interval. Prove repair│
│     │          │         │ also changes the recovery     │ fgsa-conditional.md:597           │ through lower F advances, or   │
│     │          │         │ interruption count.           │ fgsa-healing-blueprint.md:887     │ expose the M-dependent bound.  │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V07 │ MAJOR    │ 4–5     │ Long witnesses can still miss │ D:321                             │ Require claim-trigger witnesses│
│     │          │         │ every meaningful claim trigger.│ D:359                            │ and explicit feasibility scope.│
│     │          │         │ The profile equivalence cannot│ Generic/Claims.lean:23            │ Separate legacy holds-equivalence│
│     │          │         │ include new witness obligations│ Generic/Properties.lean:89       │ from certification eligibility.│
│     │          │         │ without extra hypotheses.     │                                   │                                 │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V08 │ MAJOR    │ 3–5     │ Instance-wide claim bounds    │ D:235                             │ Separate protocol parameters  │
│     │          │         │ conflict with Pareto reporting.│ D:280                            │ from certificate bounds. Add   │
│     │          │         │ Direction metadata is not a   │ D:386                             │ typed, proved transport and a  │
│     │          │         │ complete parameter order.     │                                   │ fixed/non-monotone case.       │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V09 │ MAJOR    │ 7.2     │ The anchor pair omits Z; the  │ D:446                             │ Return a duty frame with F, Z, │
│     │          │         │ correspondence confuses the   │ D:459                             │ H and its view. State separate │
│     │          │         │ viable and filtered trees.    │ consensus.tex:950                 │ viable/filtered correspondences.│
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V10 │ MAJOR    │ 3,7.2   │ HavocFG lacks a typed policy  │ D:235                             │ Define an AP template, policy  │
│     │          │         │ and certificate-family        │ D:472                             │ type, indexed facets and      │
│     │          │         │ interface. The cited research │ fgsa-conditional.md:36            │ uniform AP proofs. Specialize │
│     │          │         │ does not prove the ∀σ claim.  │ fgsa-conditional.md:60            │ before using Simplex laws.     │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V11 │ MAJOR    │ E5,E6   │ Record isolation omits restore│ D:193                             │ Extend projection laws to     │
│     │          │         │ and hooks. C* label scope and │ D:201                             │ restart and delivery semantics.│
│     │          │         │ cross-restart claims are not  │ D:615                             │ Define AP label families and  │
│     │          │         │ precise.                      │                                   │ read epochs explicitly.       │
├─────┼──────────┼─────────┼────────────────────────────────┼───────────────────────────────────┼─────────────────────────────────┤
│ V12 │ MINOR    │ 7,10,11 │ Research status and some      │ D:421                             │ Update the source-status map; │
│     │          │         │ statement references are stale│ D:517                             │ replace shorthand I1–I3 with  │
│     │          │         │ or incomplete.                │ D:663                             │ exact versioned statements.   │
└─────┴──────────┴─────────┴────────────────────────────────┴───────────────────────────────────┴─────────────────────────────────┘
```

**V01 — E4 cannot be proved for the existing handlers.** Deliver an unseen old Grid CO HEAD after its admission window. `wellFormed` and `depsPresent` are true, and `handles o o` holds. The handler leaves the state unchanged, `processed o` remains false, and `excludes` is always false. All three outcomes allowed by the new handler law therefore fail. SA uses this same handler. SA-PC gives another example: a PC can have its paths present but fail the slot test in `pcEnvelopeReady`. A future-label faulty HEAD and a third equivocation also expose this distinction between a handler call and acceptance. These are protocol behaviours, not merely malformed Lean states. [Grid CO handler](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:300), [Grid CO hooks](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:344), [SA-PC handler](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Model/Handlers.lean:45).

The deliverability clause has two further problems. An honest proposal can extend a previously accepted **faulty** proposal; its dependency need not have an honest emission origin. Also, dependencies emitted at equal times can form a cycle. Their emission does not establish an order in which the receiver can accept them. Use accepted dependency provenance, a finite delivery plan, and explicit readiness conditions. Do not strengthen the old hooks silently and then claim unchanged certificate transport. [Proposer code](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:287), [E4](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:175).

**V02 — `Retains` needs both the correct predicate and the correct time boundary.** An anchor comparable with B does not imply that B is present in the duty view. With anchor genesis, every possible B is comparable, including an unseen block. Nor does it imply that B belongs to the allowed tree: B can lie strictly below the current root. The correct predicate permits that case because the root already contains B:

`B ⪯ Z_d ∨ B ∈ D_d`.

For a fresh source selected at action `a_r=d_s`, the proof also needs this predicate at `q_s=a_r−Δ`. v5 does not define `u_B` to supply that boundary. Setting it to the action time is too late. Explicit X prevents an empty-set exception only when X is nonempty; it does not fix either defect. r147 states both requirements directly. [Ret predicate](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:117), [source boundary](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:140).

**V03 — The source-body induction needs stronger AP facts and narrower scope.** The referenced I1–I3 supply source possession, same-round compatibility, and later coverage of an **entry** T. They do not by themselves give later coverage of the whole source body C. Two bodies can conflict above the same entry T while both satisfy entry-level conclusions. Similarly, an arbitrary `Protected` getter does not establish that the supporter's actual HEAD contained the source. Sharing the getter between the two sides removes inconsistent meanings; it does not create the required semantic law. [I1–I3](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/dc-recovery-map.md:60), [AP entries](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:513).

The invariant at D:570 also needs a reset boundary and a per-body first-transfer time. It cannot retain all pre-reset sources: old-justification disclosure is a documented counterexample. During Outage, two partition branches can both extend an armed B; P1 protects B without ordering all later bodies. Thus the unqualified same-round compatibility clause and the global source-chain invariant cannot serve all listed regimes. The proof needs separate clean history, post-reset source history, and armed-prefix Outage history. `Harmless` must use compatibility with the body being protected, not just provenance of one row in the new quorum. [Actual history invariant](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:417), [Outage proof](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:366), [old-disclosure counterexample](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:553).

**V04 — Height-relative interference does not mean permanent retention of every high block.** The user's finalized-height rule is sound in its stated role: under the capped Simplex certificate assumptions, every valid block above `h*` extends F*, so disclosure of J at `h*` cannot remove such a block by selecting another predecessor branch.

But D:554 says more. Let two valid branches extend F* and reach height `m=h*+1`. Honest progress continues on one branch. Once its frontier reaches `m+2`, a block B left on the other branch at height m can have no descendant witness at height `m+1`. The height filter removes B. This is consistent with finality safety and with B extending F*. NJ likewise does not keep every unused branch forever. The supported conclusion concerns old control evidence and the specified compatible source history. It does not concern every processed block above m. [DC viability](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:911), [finalized-arm proof](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:495).

**V05 — The nine-step recovery plan still has open interfaces.** `ap.includesRows` needs an eligible-row window, a cutoff tied to the action time, and the alternative “already folded on the parent chain.” A cutoff with no lower bound can omit every useful row while satisfying the stated inclusion rule. Conversely, requiring every previously received row is stronger than DC's bounded inclusion rule. Steps 4–5 also need the selected carrier chain to keep the matching entry until consumption, or to have already achieved the required height rise. r147 proves these facts with explicit proposal times, maturity, parent-chain storage and two promotions. [Carrier construction](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:485).

Adding `ap.outputRecovered` is a valid way to expose an obligation, but it does not discharge it for FG-SA. Row-source retention alone does not cover qualifying fast bodies at every label, slow-source windows, or exact proposal-parent service. The new blueprint marks that composition gap OPEN. First finality still needs the permitted finality record, a usable non-NJ height, and timed target/justification/finality carriers. `ap.finalityHead` supplies only part of this. Keep these conclusions conditional until the required AP statements and FG constructions are complete. [Full output handoff](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:635), [remaining finality obligations](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:670), [blueprint interface gap](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:964).

**V06 — `Settled` is neither the proved static condition nor the proved effective condition.** A union of anchor sets can be an antichain while individual sets shrink or alternate. For example, `{X}` and `{Y}`, with X and Y incomparable, meet that test. The predicate also does not state a common numerical frontier H. Its following sentence assumes “the band fixed,” but that assumption is absent from the definition. r147 instead fixes H, F and Z and stops the argument at the first height rise. [v5 condition](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:486), [r147 N1](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:127).

Literal F constancy creates a separate bound issue. There is at most one branch-excluding top-J event at a fixed frontier, but there can be many lower F advances. Counting each as a new repair attempt gives an initial-frontier-dependent bound. The uniform bound requires a proof that exact service continues through harmless lower F advances. The blueprint marks that stronger interface SKETCH. v5 must select one form and its corresponding bound. [r147 count](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:597), [bound consequence](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:887).

**V07 — Arbitrary-horizon inhabitation is useful but does not prove meaningful coverage.** A witness can deliver heartbeats forever while having no eligible proposal, no non-genesis armed output, or no nonempty FG source. A protocol can also have long benign runs while a particular accepted input makes future synchrony impossible. Existential witnesses for each horizon do not prove continuation from that input. Witness obligations should be claim-specific and exercise the trigger and deadline; scheduler feasibility needs its own stated scope. [Witness requirement](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:359).

The promised equivalence to the old bundle must also be qualified. `AvailableChain` contains neither an emission witness nor `HooksSound`. For example, a v1 specification can schedule every proposal at a nonpositive time and emit nothing. Its clean inclusion triggers can be empty, while its genesis outputs satisfy safety. The new emission witness cannot follow from that bundle. Prove equivalence between the **claim propositions**, then prove certification eligibility separately for each migrated instance. [Old bundle](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Claims.lean:23), [inclusion trigger](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:89).

**V08 — Claim bounds must not be part of the fixed protocol identity.** With `I.params` fixed, one I cannot have two certified delay/budget tradeoffs. Creating a new Instance for each tuple restores representability but defeats the stated “per instance” Pareto set and requires a separate notion of equal protocol and facets. Keep protocol parameters and facets fixed; bind theorem bounds in certificates and coherent profiles. The project log already plans this correction, but v5 has not applied it. [Instance schema](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:235), [planned correction](/Users/francesco/ethereum/lean/available-chain/log.md:78).

Moreover, v5 has removed the explicit `Prem`, `Concl`, `monoPrem` and `monoConcl` interface. `dir` alone does not replace it. A checked transport must keep the protocol and facets fixed, check parameter validity, and prove `holds p → holds p'`. Exact-time D needs equality-only comparison unless a separate monotonicity certificate is supplied. Composite comparisons need reflexivity/transitivity or equivalent checked entailment composition. Inhabitation must remain a separate obligation.

**V09 — The anchor correspondence names the wrong set and loses a control value.** If root = J and `F ≺ J`, F can still belong to DC's viable tree. It does not belong to paths that start at J. Thus the equality at D:459 cannot literally describe `viable_tree_from`; it describes a representation of the **filtered** tree, with separate treatment of prefixes already covered by the root. [Viable tree](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:911), [filtered tree](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:950).

Also, `(F,{A})` does not identify whether the root is F or A: A can be the only band entry, or the active J. `Settled` nevertheless refers to that root. Return a frame containing the accepted F, Z, H and the duty view, or prove an explicit reconstruction theorem. The F basis, frozen branches and F-advance cut are correct ingredients. R1 remains a deliberate variant of DC, so the correspondence must name that variant rather than imply executable equivalence to live-cache DC.

**V10 — Universal Havoc policies need a separate typed proof boundary.** Quantification over σ is not inherently unsound. It is a useful robustness test. But σ must have a defined type and access boundary: which state it reads, which rows it emits, what record updates it can cause, and which AP transitions remain fixed. Each composite has a different `ProtocolSpec`; the certificate therefore needs an indexed instance/facet family or a separate AP-template certificate.

The cited r147 proof assumes the specified FG-SA client and honest non-equivocation. It cannot simply be reused as a proof for every equivocal σ. AP results must be proved using only the permitted filter conditions and AP facts. Simplex provenance, quorum uniqueness, causal-cap and no-slashing lemmas must be used **after** specialization. Conditional-regime inhabitation also needs an explicit quantifier order; a useful `Settled` interval need not exist under every policy. [Havoc definition](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:472), [r147 execution premises](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:36).

**V11 — Restart can bypass the proposed isolation law.** Consider a hidden record field containing a self-visible seat index. Let `recordOwn` change only that field, while all ordinary AP transitions and getters factor through `base`. Let `restore (durable st)` copy the hidden index into `base`. This satisfies the listed E5 equations, yet an AP proposal after restart can reveal and use the index. A restore projection law is required. Hook predicates also need a stated projection contract if the framework will transport delivery regimes between the composite and its AP projection. [Isolation and restart](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:195).

Use an explicit AP-label family for isolation. “Every C* label” is ambiguous because full-set Linked labels also have bijective seat assignments. Finally, excluding the rejoin interval does not define cross-restart monotonicity: a read before restart and a read after rejoin can both lie outside the excluded interval and still show a retreat. Use epoch-local comparisons or require catch-up to the last exposed output. Define the record fold order over both duties and seats.

The future-proofing result is mostly favourable **within the newly limited scope**. “Additive” below does not mean that an existing certificate covers the feature.

```text
┌───────────────────────────┬────────────────────────────┬─────────────────────────────────────────────────────────────┐
│ Feature                   │ Classification             │ Reason and required limit                                   │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Stake weights             │ Additive                   │ Integer seat multiplicity works. Add weighted authentication│
│                           │                            │ links, participation and quorum lemmas. It does not turn the│
│                           │                            │ fixed unit-weight FG proof into a weighted proof. D:137,161.│
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Finite sampled committees │ Additive, fixed size       │ Per-label assignments and Balanced ε can describe realized │
│ with ε                    │                            │ samples. Sampling probabilities and adaptive selection laws│
│                           │                            │ remain outside the deterministic certificate. D:44,137.    │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ VRF eligibility that      │ New engine for private     │ Fixed public age buckets are additive. Private credentials,│
│ grows with age            │ self-selection             │ variable membership and a holder-specific eligibility test │
│                           │                            │ are outside identity-free act st ℓ. D:50,61,72.           │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Inclusion-list committees │ Additive scheduled model  │ Add labels, list payloads, validity and inclusion claims.   │
│ / FOCIL                   │                            │ Actual private selection retains the VRF limit. D:130,153.│
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Multiple proposers        │ Additive                   │ Multiple labels/seats fit. Bind proposal IDs to emissions. │
│                           │                            │ A chain cannot include every conflicting honest proposal; │
│                           │                            │ add an appropriate selection/inclusion claim. D:130,257.  │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ DAG / leaderless          │ Additive when scheduled;  │ State and payload can contain a DAG. Add output facets and │
│ protocols                 │ new engine for immediate  │ claims; the fixed FG needs a chain projection. Receipt-time│
│                           │ signed responses           │ signing is outside the tick-only model. D:65,74.          │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Adaptive / mildly adaptive│ Additive trace abstraction│ New corruption-time, behaviour and authentication predicates│
│ corruption                │ with new regimes; engine  │ can constrain pre-corruption behaviour. Static certificates│
│                           │ version for explicit      │ do not transfer. Compromise, erasure and recovery transitions│
│                           │ compromise semantics      │ need explicit semantics. D:53,66,74.                     │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Late joiners and          │ Additive in fixed V, after│ Add readiness, checkpoint trust and transfer rules. “Asleep” │
│ state transfer            │ E6 is completed           │ currently still processes messages. Unbounded new membership│
│                           │                            │ is not covered. D:75,201; Model/Generic/Run.lean:53.       │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Clock drift               │ New engine for one duty  │ A label has one actTime. Different physical firing times for│
│                           │ firing at local times     │ the same logical authentication need local-time semantics. │
│                           │                            │ Renaming the labels is not a proved refinement. D:63.     │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Protocol-driven relay     │ Additive                   │ Gossip can carry signed objects. Add send provenance and   │
│                           │                            │ prove relay from scheduling/network assumptions, with the │
│                           │                            │ actual hop and tick delays. Run.lean:74; Conditions:118.  │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Signature aggregation     │ Additive abstract model   │ Payloads can carry an aggregate; prove signer/message      │
│                           │                            │ extraction and carries correspondence. Compact execution  │
│                           │                            │ needs a separate executable refinement. Run.lean:50,91.  │
├───────────────────────────┼────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Second, different FG      │ Usually additive LM/claims│ It needs new module and composition proofs. A gadget whose │
│                           │ within engine scope       │ private record controls AP proposals cannot satisfy E5 as │
│                           │                            │ written; its certification interface must change. D:97,195.│
└───────────────────────────┴────────────────────────────┴─────────────────────────────────────────────────────────────┘
```

These classifications follow from the arbitrary state/payload types, fixed duty times, seat assignment and emission interface in [Run.lean](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:46). The broad additive claim should always carry the engine scope and the applicable isolation interface.

The **v1 → v2 simulation is feasible**. The disjoint label sum and per-label seat counts give the correct authentication encoding:

- Old committee authentication maps to the old-label summand.
- `proposer s` maps to seat 0 of the singleton proposal label for s.
- `proposerOf s` is exactly the holder of that seat.
- Recovering old committee assignments requires the proved bijection, including the dependent `Fin` casts.
- With recording disabled, all duty and proposal payloads use the same post-clock state. Concatenating old duties and proposal duties in the old order preserves emissions.
- `NoRestart` permits the ordinary event-fold simulation. The wrappers must also transport carried authentication, hook predicates, root scope, proposal identifiers and regimes.

In particular, claims that quantify over `proposerOf` can transfer through the holder equivalence. A forward embedding alone is insufficient for universal claims: every v2 run in the lifted legacy regime needs a corresponding v1 run. Arbitrary v2 assignments outside that regime are not covered. The design now largely states the required work. [Lift proposal](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:211), [old emissions and holders](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:141), [proposal predicate](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:58).

I agree with **several engineer-weeks**, at medium confidence, for the simulation, adapters and representative claim transport. This estimate excludes repairing E4 and completing the new FG module. “Every v1 proposition transfers under equivalent regimes” is plausible; “every v1 certificate becomes a v2 `Cert`” is currently false because of the new eligibility obligations.

The monotonicity results below cover every field of the two current claim records. Arrows indicate a change that makes the claim **weaker**. Keep P, E and the facets fixed, and keep both parameter bindings valid. Let:

`R = {ρ ↑, θrec ↑, recoveryFull false→true, G ↓}`.

```text
┌──────────────────────────────┬────────────────────────────────┬───────────────────────────────────────────────────────┐
│ Current claim / field        │ Parameter change               │ Result                                                │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ Generic.constants            │ Any component                  │ No unrestricted product order. Validity couples Π≤η   │
│                              │                                │ and A_f≤A and bounds θ, θrec. Constants.lean:38.       │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ confirmedSafe                │ None                           │ No C parameter. Safe already includes monotonicity.  │
│ stableSafe                   │ None                           │ Same. Generic/Claims.lean:27.                        │
│ monotone                     │ None                           │ No C parameter; follows from the two Safe fields.   │
│ nested                       │ None                           │ No C parameter or execution-regime premise.          │
│                              │                                │ Generic/Claims.lean:31.                              │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ confirmedIncluded            │ D_c ↑                          │ Not monotone alone. True with confirmed monotonicity.│
│                              │                                │ Generic/Properties.lean:89.                          │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ stableIncluded               │ θ ↑; η ↑                       │ True: each strengthens the regime premise.          │
│                              │ D_s ↑                          │ Not monotone alone; needs stable monotonicity.       │
│                              │                                │ Generic/Regimes.lean:27; Properties.lean:89.         │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ stableIncludedFast           │ D_f ↑                          │ Not monotone alone; needs stable monotonicity.       │
│                              │                                │ Generic/Claims.lean:38.                              │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ stableResilient               │ A ↑; Π ↓; θ ↑; η ↑             │ True, separately in the valid domain.               │
│                              │                                │ Generic/Regimes.lean:44.                             │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ stableResilientFast           │ A_f ↑; Π ↓; θ ↑; η ↑           │ True. General A is replaced by A_f, not added.       │
│                              │                                │ Generic/Regimes.lean:61.                             │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ recovered.confirmedSafe      │ R                              │ True. Larger ρ also strengthens the horizon premise.│
│ recovered.stableSafe         │ R                              │ True. θ and η do not occur in RecoveryRegime.        │
│                              │                                │ Generic/Regimes.lean:72; Claims.lean:17.             │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ recovered.confirmedIncluded  │ R                              │ True.                                                │
│                              │ D_c ↑                          │ Not monotone alone; needs recovered monotonicity.   │
│                              │                                │ Generic/Claims.lean:19.                              │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ recovered.stableIncluded      │ R                              │ True.                                                │
│                              │ D_s ↑                          │ Not monotone alone; needs recovered monotonicity.   │
│                              │                                │ Generic/Claims.lean:20.                              │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ Strong.constants             │ strongDelay ↑                  │ Preserves nonnegativity. No faultCap validity bound.│
│                              │                                │ Strong/Constants.lean:13.                            │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ strongSafe                    │ faultCap ↓                     │ True: fewer faulty runs are included.               │
│                              │                                │ Strong/Claims.lean:20.                               │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ strongIncluded                │ faultCap ↓                     │ True. Full participation is a fixed premise.        │
│                              │ strongDelay ↑                  │ Not monotone alone; needs strong monotonicity.      │
│                              │                                │ Strong/Claims.lean:23.                               │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ strongResilient               │ faultCap ↓                     │ True. Arming is fixed at Δ; no A or finite Π occurs. │
│                              │                                │ Strong/Regimes.lean:19.                              │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ strongRecoveredSafe           │ R; faultCap ↓                  │ True. StrongClaims alone does not assert C.Valid;   │
│                              │                                │ a weakening theorem must supply its needed bounds. │
│                              │                                │ Strong/Claims.lean:30.                               │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ strongRecoveredIncluded       │ R; faultCap ↓                  │ True.                                                │
│                              │ strongDelay ↑                  │ Not monotone alone; needs recovered strong          │
│                              │                                │ monotonicity. Strong/Claims.lean:33.                │
├──────────────────────────────┼────────────────────────────────┼───────────────────────────────────────────────────────┤
│ New persistent inclusion      │ Corresponding D ↑              │ True if the statement retains the honest-proposal  │
│                              │                                │ obligation and quantifies over all honest readers  │
│                              │                                │ from the deadline through the horizon. D:303.     │
└──────────────────────────────┴────────────────────────────────┴───────────────────────────────────────────────────────┘
```

Parameters absent from a row do not affect that field. This table does not authorize changing a protocol parameter with the same name: changing the protocol's η can change P itself.

The logical premise/conclusion directions are straightforward. To transport a certificate from p to p′, prove that the new regime implies the old regime and that the old conclusion implies the new conclusion. Inhabitation does not follow from either implication. v5's direction list is correct for the listed scalar changes; its schema still needs those actual transport proofs.

The current regimes have the following prefix behaviour.

```text
┌───────────────┬─────────────────────────────────────────────────────────────────────┐
│ Regime        │ Prefix-closure status                                               │
├───────────────┼─────────────────────────────────────────────────────────────────────┤
│ Sleepy        │ Closed under complete time truncation to a nonnegative horizon.    │
│ StableSleepy  │ Same; preserve E and the awake history used by η.                  │
│ Fast          │ Same; full participation restricts to the shorter interval.        │
│ Outage        │ Not under arbitrary cuts. A cut must be at least b₁.               │
│ FastOutage    │ Same minimum horizon b₁.                                           │
│ Recovery      │ Not under arbitrary cuts. A cut must be at least GST+ρ.            │
│ StrongArmed   │ Not under arbitrary cuts. A cut must be at least b₀.               │
└───────────────┴─────────────────────────────────────────────────────────────────────┘
```

These facts concern complete time prefixes, with assignments unchanged. An event-list prefix halfway through equal-time events can fail `tick_total`. Causal induction therefore needs an execution-prefix interface distinct from the complete-run regimes. The inequality `q_s<d_s` is useful, but the AP theorem must also be usable before `d_s`; it cannot require an assumption about the whole future interval. [Schedule totality](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:38), [regimes](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:14), [StrongArmed](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Regimes.lean:19).

The FG facts **D, E and F have sound proof routes**, with qualifications. D needs the actual inclusive causal cut and the source-to-local-frontier bound. E needs the selected NJ prefix or the named finalized checkpoint and its crossing facts, not an arbitrary height with the right number. F correctly requires a source for both targets and timeouts; an empty height source can coexist with a nonempty finality pair. The source bodies must then be retained from their first transfer, as separate history data. These are consistent with DC and r146. They do not establish v5's universal `HeightRetains`. [Causal construction](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:563), [two-arm source history](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:394), [exact client](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:268).

The Lean mechanisms are feasible, with the following limits.

- **Freeze check:** `ConstantInfo.getUsedConstantsAsSet` exists in the pinned toolchain. It inspects types and values, including opaque values, and supplies inductive dependencies. A recursive walk with cycle detection can hash the dependency graph. The implementation must load the required private bodies, serialize declarations deterministically, and fail if a required body is unavailable. This is a syntactic artifact freeze; it can reject harmless refactoring and does not decide semantic equivalence. [Pinned implementation](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Util/FoldConsts.lean:65).
- **Registry attributes:** feasible through checked attributes and a persistent environment extension. Check the elaborated certificate type, including its instance and bounds. A theorem with extra unproved premises must not appear as an unconditional certificate. Persistent extensions support imported registry data. [Lean environment API](https://lean-lang.org/doc/api/Lean/Environment.html).
- **Kernel-checked refutations:** feasible for executable instance interfaces. `decide_cbv` does not require trust in compiled evaluation. A reflective checker needs a soundness theorem covering execution, regime and failed conclusion. Finite events alone do not make arbitrary hooks or function-valued environments decidable; use finite representations with equivalence proofs. [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/).
- **Lassos:** correctly deferred. A repeating trace needs infinite-run semantics, fairness and a repetition or simulation theorem. Growing clocks and block stores usually require an abstract cycle. Parameterized finite counterexamples already suffice to refute every finite delay. [Existing Sanity theorem](/Users/francesco/ethereum/lean/available-chain/AvailableChainWitnesses/Sanity.lean:295).

A lasting implementation also needs an explicit extensible representation for `FacetBundle`, `FacetNeeds` and `ParamBinding`. Extending a frozen Lean structure with another field changes its declaration. Typed maps, separate facet records or another extension mechanism should be selected in Phase 0. The registry should also preserve proof status, assumptions, applicable output names and module versions; a paper result must not appear as a Lean certificate.

For internal consistency, I found no stale operative `E7`, `LeftAlone` or `FGDomain` reference in v5. `Static` and `TargetPreserving` are no longer the actual v5 conditions. The material stale references are the pending r147/blueprint status and the unspecified I1–I3 shorthand. The current reports distinguish paper proofs, conditional implications and open Lean integration; the framework should retain those distinctions. [r147 report](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/r147-fgsa-conditional.md:3), [blueprint status](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:41).

**REVISE.** Keep the layer split, shared facets, finite refutations and versioned definitions. Before adoption, repair E4, replace the FG conditions with exact causal statements, restrict height-relative retention to its supported scope, and close the timed composition interfaces. The Phase 0 prototype should demonstrate these boundaries before the framework is frozen.

AUDIT COMPLETE: 5 blocking, 6 major, 1 minor