**Verdict: REVISE.** The layer structure is useful, but v4 is not ready to freeze. Several proposed guarantees are false as stated. Other guarantees need interfaces that the document does not yet define.

This was a source audit. I did not edit files or run a build. “Blocking” below means that the issue prevents adoption of the proposed contract. It does not mean that the existing Lean proofs are unsound.

In the tables, paths under `Generic/` and `Strong/` refer to `AvailableChainStatements/`. Research filenames refer to `research/async-resilient-committees/tip-stability/codex/`, except `consensus.tex`.

```text
┌─────┬──────────┬─────────┬──────────────────────────────────────┬────────────────────────────────┬──────────────────────────────────┐
│ ID  │ Severity │ Section │ Finding                              │ Evidence (file:line)           │ Proposed fix                     │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B01 │ BLOCKING │ 3–5     │ Separate certificates can assign     │ FRAMEWORK-DESIGN.md:344         │ Bind certificates and profiles   │
│     │          │         │ different meanings to one output.    │ Generic/Claims.lean:23         │ to one instance interface and    │
│     │          │         │ Profiles do not enforce coherence.   │ FRAMEWORK-DESIGN.md:299         │ shared parameter assignment.     │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B02 │ BLOCKING │ 4       │ Inclusion is not monotone in delay   │ Generic/Properties.lean:89     │ Keep exact-delay entries, or     │
│     │          │         │ D as an independent claim.           │ FRAMEWORK-DESIGN.md:270         │ require output monotonicity for  │
│     │          │         │                                      │                                │ delay weakening.                 │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B03 │ BLOCKING │ E4, 5   │ HooksSound and one finite witness    │ FRAMEWORK-DESIGN.md:133         │ Add semantic hook obligations    │
│     │          │         │ still permit empty long-run regimes  │ FRAMEWORK-DESIGN.md:351         │ and run extension or arbitrary-  │
│     │          │         │ and vacuous deadline claims.         │ Generic/Conditions.lean:110    │ horizon feasibility evidence.    │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B04 │ BLOCKING │ 7.2–7.3 │ Anchor conditions are not sufficient │ FRAMEWORK-DESIGN.md:501         │ Define causal, view-aware        │
│     │          │         │ as written. Outage does not preserve │ FRAMEWORK-DESIGN.md:507         │ retention conditions. Protect    │
│     │          │         │ one chain of all Protected blocks.   │ fgsa-adjudicate.md:366          │ the armed prefix during Outage.  │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B05 │ BLOCKING │ 7.4 C,F │ The honest-row premise confuses the  │ FRAMEWORK-DESIGN.md:559         │ Separate source bodies, height   │
│     │          │         │ source body, height entry, and       │ FRAMEWORK-DESIGN.md:476         │ pairs, finality pairs, and their  │
│     │          │         │ finality target. Simplex fails it.   │ consensus.tex:2139             │ provenance laws.                 │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ B06 │ BLOCKING │ 7.3–7.5 │ The AP interface does not imply the  │ FRAMEWORK-DESIGN.md:537         │ Add explicit progress, recovered │
│     │          │         │ claimed joint recovery and finality  │ FRAMEWORK-DESIGN.md:606         │ output, finality-head, and timed  │
│     │          │         │ conclusions.                         │ fgsa-adjudicate.md:670          │ carrier obligations.             │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M01 │ MAJOR    │ 2       │ The engine is not future-proof for   │ FRAMEWORK-DESIGN.md:48          │ State a bounded engine scope.    │
│     │          │         │ every listed key, eligibility, and   │ FRAMEWORK-DESIGN.md:93          │ Distinguish direct extensions    │
│     │          │         │ timing model.                        │ Generic/Run.lean:55            │ from encodings and new engines.  │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M02 │ MAJOR    │ E5, E6  │ Own-record execution is incomplete;  │ FRAMEWORK-DESIGN.md:169         │ Specify the atomic tick and      │
│     │          │         │ restart loses F. Isolation does not  │ FRAMEWORK-DESIGN.md:184         │ restart transitions, durable F,  │
│     │          │         │ cover all AP emission paths.         │ Generic/Run.lean:105           │ and complete projection laws.    │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M03 │ MAJOR    │ 2 lift  │ Equal reads alone do not transfer    │ FRAMEWORK-DESIGN.md:206         │ Prove translations for objects,  │
│     │          │         │ claims about emissions, signers,     │ Generic/Properties.lean:58     │ emissions, hooks, regimes,       │
│     │          │         │ proposals, and regimes.              │ Generic/Run.lean:141           │ facets, and claims.              │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M04 │ MAJOR    │ 7.2     │ The anchor interface is not an exact │ FRAMEWORK-DESIGN.md:442         │ Define View and the represented  │
│     │          │         │ restatement of DC. R1 changes DC's   │ consensus.tex:950              │ domain. Prove a versioned        │
│     │          │         │ control-cache semantics.             │ fgsa-fast.md:132                │ correspondence theorem.          │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M05 │ MAJOR    │ 4, 7.5  │ Several current regimes are not     │ Generic/Regimes.lean:53        │ Use bounded prefix predicates   │
│     │          │         │ prefix-closed at fixed parameters.  │ Generic/Regimes.lean:85        │ and prove causal step lemmas     │
│     │          │         │ Prefix closure alone is insufficient.│ Strong/Regimes.lean:29         │ for the joint induction.         │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M06 │ MAJOR    │ 4–5     │ Orders need not be decidable; best   │ FRAMEWORK-DESIGN.md:266         │ Use checked comparisons and      │
│     │          │         │ constants need not be unique.        │ FRAMEWORK-DESIGN.md:351         │ Pareto sets. Validate refutations│
│     │          │         │ Witnesses do not transport freely.   │ FRAMEWORK-DESIGN.md:380         │ and witness obligations.         │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M07 │ MAJOR    │ 1, 7    │ L1 conditions and L3 entries depend  │ FRAMEWORK-DESIGN.md:79          │ Put shared FG definitions below │
│     │          │         │ on anchorsOf and HavocFG in L5.      │ FRAMEWORK-DESIGN.md:442         │ the catalog; keep their proofs   │
│     │          │         │ This violates the import rule.       │ FRAMEWORK-DESIGN.md:494         │ in Kit.FG.                       │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M08 │ MAJOR    │ 5–6     │ Finite runs do not define infinite   │ FRAMEWORK-DESIGN.md:372         │ Add infinite-run or extension    │
│     │          │         │ liveness. Lassos are not necessary   │ Generic/Run.lean:114           │ semantics. Permit parameterized │
│     │          │         │ for all-constant refutations.        │ Witnesses/Sanity.lean:295       │ finite counterexamples.          │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ M09 │ MAJOR    │ 5       │ The freeze check trusts an unverified│ FRAMEWORK-DESIGN.md:387         │ Freeze the L0 version-to-content │
│     │          │         │ L0 version boundary and lacks a      │ FRAMEWORK-DESIGN.md:391         │ mapping and pin the complete     │
│     │          │         │ complete artifact identity.          │                                │ certificate dependency manifest.│
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ N01 │ MINOR    │ 3–5,10  │ The schema and source-status text    │ FRAMEWORK-DESIGN.md:259         │ Complete the schema and replace │
│     │          │         │ have missing fields and stale        │ FRAMEWORK-DESIGN.md:664         │ pending-source claims with the  │
│     │          │         │ references.                          │ reports/r146-fgsa-adjudicate.md:3│ current research status.         │
├─────┼──────────┼─────────┼──────────────────────────────────────┼────────────────────────────────┼──────────────────────────────────┤
│ N02 │ MINOR    │ 3–4     │ The catalog does not specify output  │ FRAMEWORK-DESIGN.md:317         │ Add validity, knowledge,         │
│     │          │         │ validity, data availability, or an   │ Generic/Properties.lean:113    │ causality, and implementation    │
│     │          │         │ implementation refinement boundary. │                                │ refinement entries.              │
└─────┴──────────┴─────────┴──────────────────────────────────────┴────────────────────────────────┴──────────────────────────────────┘
```

**B01. Certificate meanings must be shared.** `Cert` chooses its own facets. A profile is only a set of claim IDs. Thus one protocol can certify safety using an output that always returns genesis, then certify inclusion using a different getter under the same output name. For example, an output can show each of two conflicting honest proposals at its inclusion deadline. It can satisfy inclusion while failing safety; the genesis getter supplies the separate safety certificate. The current bundle instead uses one `I` and one `C` throughout. Profiles need a common instance interface, consistent parameter bindings, and explicit facet equality or refinement proofs. Cross-claim inequalities alone do not fix this. [Design:344](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:344), [current bundle:23](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Claims.lean:23).

**B02. Delay weakening is false for independent inclusion claims.** `IncludedFrom … D` requires containment at exactly `proposalTime + D`. It does not require containment at later reads. An output can contain B at `s + D`, then remove B before `s + D′`. This refutes the proposed generic implication for `D ≤ D′`. All current inclusion fields have this problem when separated from their safety fields. The complete bundles can supply monotonicity, but partial certification cannot assume that other certificate. Preserve the old exact-delay entry and use a relation theorem that requires the same output’s monotonicity certificate. Alternatively, introduce a new entry with persistent inclusion. [Properties:89](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:89), [design:286](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:286).

**B03. One witness does not prevent vacuity.** Consider a protocol that emits a valid heartbeat and an undeliverable object at time zero. Give the second object `depsPresent = false`, `excludes = false`, and no alternative handler. These hooks satisfy the listed monotonicity obligations. A short run can deliver the heartbeat and satisfy the proposed witness. However, once the broadcast deadline enters the horizon, synchrony requires a delivery that `DeliveryWellFormed` forbids. No longer synchronous run exists. Future inclusion obligations can therefore hold vacuously. The witness does not even depend on the conclusion delay. Require semantic links between hooks and execution, honest-emission admissibility, and feasibility beyond each relevant deadline—preferably a run-extension theorem. Also, `handles → equality ∨ carries` proves containment, not that the handler actually ran. [Design:133](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:133), [delivery checks:51](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:51), [broadcast:110](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:110).

**B04. The anchor predicates need a new statement.** Under the natural compatibility interpretation, `Static` permits arbitrary anchor changes while there are no honest targets: its exception is then vacuous. HavocFG can keep changing the effective choice domain before a source forms. This is not the fixed-domain interval used by the research repair proof. Conversely, literal equality of anchor sets can be too strong: new branches can enter a view without changing the effective root or numerical band. Define the effective controls and the retained paths, with explicit interval endpoints, settling bounds, and quantifiers over duties. Define HavocFG as a family indexed by a signing rule; the AP facets and certificates must be uniform across that family. [Design:481](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:481), [design:501](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:501), [fixed-frontier proof:513](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:513).

The Outage statement has a separate error. Persistence of an armed B does not imply that all later honest leases and stable tips remain on one chain. During a partition, nodes can adopt conflicting descendants X and Y of B while both retain B. The research proof protects **B**, using a first departure from B. It does not prove compatibility of every new protected descendant. Consequently, (C) cannot generally maintain the proposed global `ProtectedCompatible` predicate throughout Outage. Use a predicate indexed by the protected read or armed prefix. State same-round target compatibility only in regimes that establish it. [Design:507](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:507), [Outage proof:380](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:380).

**B05. Simplex does not satisfy the stated row premise.** A height pair names the immutable height entry of its source C; that entry need not equal C. A finality pair names the head-derived J. It can be nonempty when `FGTarget` is empty. The design correctly introduces `FinalityHead`, then incorrectly requires every honest row to name the AP target or be empty. Split the proof into height-source provenance, entry extraction, and finality provenance through an earlier justification quorum. Keep the source **body** in the proof history. The certified-pair rule supports the first NJ+1 transfer, but does not by itself prove the later history required by (F). [Design:559](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:559), [DC client:2139](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2139), [source-history requirement:417](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:417).

**B06. Joint recovery has missing interface obligations.** Safe, advancing FG targets do not imply recovery of every exposed AP output. An AP can retain the required target behavior while a separate output chooses conflicting descendants of F after an asynchronous prefix. `ap.floored` still holds. `ap.cleanCompatible` says nothing about this recovery execution. Add conditional recovery claims for the ordinary outputs, including their relationship to targets and the handoff state.

Finality also needs more than a head that descends the chosen anchor. The adjudication still requires the correct current-slot finality head, a usable non-NJ height, record permission, and timed carriers under strong proposer recurrence. Full participation alone supplies none of those proposer windows. The design must expose these requirements rather than hide them in “FG liveness premises.” [Design:517](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:517), [remaining finality obligations:670](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:670), [DC FinalityRegime:126](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Regimes.lean:126).

**M01. The engine needs a stated scope.** E1 and E2 support many finite scheduled-duty models. They do not establish the broader claim that every later key or eligibility scheme is an L1–L3 addition. Honest code still has no private key or random input; each label has a fixed act time and seat count. Genuine private VRF selection and drifted execution of one logical duty require more than a participation predicate. The feature table below distinguishes direct extensions from restricted encodings. [Design:88](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:88), [current duty interface:55](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:55).

**M02. E5 and E6 need executable semantics before the lift is frozen.** Today `World.step` has no environment or seat assignment argument. Recording emitted signatures makes the state transition depend on both. Specify whether all duty payloads use the same pre-record state, how records are folded, and how restart is ordered against ticks and deliveries. DC records before release. Moreover, resetting the base loses its accepted F; finalized monotonicity then fails across restart unless F is durable or the claim explicitly excludes the restart/rejoin interval. The isolation equations are sound for local reads, but an AP projection also needs laws for proposal emissions and gossip, which are not covered by “every C* act.” [Run:105](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:105), [design:175](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:175), [DC record-before-release:2188](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2188).

**M03. The lift is feasible, but the stated theorem is insufficient.** Use a disjoint label sum for old committee labels and proposal slots. Translate proposer authentication to seat zero of the corresponding singleton label. Recover `proposerOf s` from that seat’s holder. Recover each old seat equivalence from a proved bijection—not merely a seat-count equality. Preserve the order of duties and the tick-before-delivery rule. Translate outer objects and the `carries`/`handles` relations, including carried signatures. No self-visible labels and `NoRestart` then permit a state-fold simulation. Claim transport additionally needs emission, holder, proposal, root-scope, and regime equivalences. Equal output reads alone cannot transfer `HonestProposalAt`. [Design:206](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:206), [proposal predicate:58](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:58).

Every current claim can plausibly transfer through those adapters, including claims that quantify over `proposerOf`. Existing proof files can remain unchanged if the old engine remains available and new wrapper theorems transport them. This is not automatic reuse against renamed definitions. My planning estimate is **several engineer-weeks**, with medium confidence; proof-interface compatibility is likely to cost more than the event-fold induction.

**M04. The anchor representation needs a proved correspondence.** DC’s viable set includes processed ancestors and descendants, not just an antichain of entries. An anchor set can represent the permitted choice cones only together with the duty view, ancestry, admission rules, and root convention. Root = J gives `{J}` under the required entry invariants; that special case is reasonable. However, R1 recomputes control values from the duty view, while DC uses live control caches with an explicit processed-block view. The research calls R1 an explicit change. Preserve the accepted F and its basis across the F-advance cut, and specify how frozen branches contribute to maxima. Also distinguish finality-before-height in the **chain transition** from the store update, which updates `h_max`, then J, then F. [Design:452](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:452), [DC viable tree:911](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:911), [DC store update:937](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:937), [R1 change:132](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:132).

**M05. The proposed induction needs causal prefix statements.** Several regimes impose a minimum horizon, so they are not closed under arbitrary truncation with parameters held fixed. Also, a theorem conditional on `TargetPreserving` for an entire future interval cannot establish that same condition by merely invoking “induction on time.” State the induction invariant and a step lemma that uses only earlier sources, receipts, and duties. The research supplies the required ordering: the new row at the action cannot justify the earlier transfer HEAD. Outage has no `gst_zero` field; its clean history must follow from its healthy-prefix conditions. [Design:594](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:594), [causal ordering:279](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:279).

```text
┌───────────────┬──────────────────────────────────────────────────────────────────────────┐
│ Current regime│ Prefix-closure status                                                    │
├───────────────┼──────────────────────────────────────────────────────────────────────────┤
│ Sleepy        │ Yes, for complete time prefixes with a nonnegative horizon. Preserve E   │
│               │ and assignments; retain all events at the cutoff time.                   │
│ StableSleepy  │ Yes, on the same basis. Keep the same awake history used by η.            │
│ Fast          │ Yes, on the same basis. Full participation restricts to the prefix.       │
│ Outage        │ No for arbitrary cuts: b₁ ≤ horizon is required. Yes for cuts ≥ b₁.       │
│ FastOutage    │ Same restriction as Outage.                                              │
│ Recovery      │ No for arbitrary cuts: GST + ρ ≤ horizon is required. Yes above that      │
│               │ bound; recurrence only tests completed windows.                          │
│ StrongArmed   │ No for arbitrary cuts: b₀ ≤ horizon is required. Yes for cuts ≥ b₀.       │
└───────────────┴──────────────────────────────────────────────────────────────────────────┘
```

These results concern time truncation, not an arbitrary list prefix halfway through equal-time events. Such a list prefix can violate `tick_total`. [Schedule:38](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:38), [regimes:14](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:14), [StrongArmed:19](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Regimes.lean:19).

**M06. Mechanical comparison needs a smaller, checked interface.** Arbitrary `Prop` relations are not computable orders. The schema also omits reflexivity and transitivity laws. Multidimensional tradeoffs can have several incomparable best certificates, so the registry needs a Pareto set, not one “strongest” constant tuple. Attributes must be checked against the actual certificate type and its facets. `Refutation` needs valid parameters before the registry reports it as a valid cell.

Further, `monoPrem` transports `holds`, not `RegimeInhabited`. Strengthening a premise can remove every witness. The mandatory fault is impossible for `faultCap = 0`, and for the current Fast regime at n = 4, which requires fewer than one faulty validator. Allow boundary-case witnesses and keep witness transport as a separate obligation. [Design:259](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:259), [design:343](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:343), [BelowQuarter:209](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:209).

**M07. The proposed imports form a cycle.** L1 defines conditions using `anchorsOf` and runs of `AP ⊗ HavocFG`, but those definitions belong to L5. This directly conflicts with the L0–L3 import rule. Move the shared FG semantics and composition signatures to a lower definition layer. Leave implementation-specific proofs and derived theorems in the kits. This is an architectural issue, not a Lean limitation. [Import rule:79](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:79), [anchor ownership:442](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:442), [conditions:494](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:494).

**M08. Refutation forms need separate semantics.** A checked finite run can refute a current bounded claim. The finite `Run` type does not yet define unbounded “eventually.” A lasso requires an infinite-run interpretation, fairness conditions, and a proof that its repeated part remains valid. Exact repetition is unlikely when clocks, blocks, and records grow; an abstract cycle needs a simulation theorem. Also, a lasso is not necessary to prove that no constant works: the existing Sanity theorem already uses a parameterized family of finite runs. [Design:372](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:372), [Run:114](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:114), [all-delay refutation:295](/Users/francesco/ethereum/lean/available-chain/AvailableChainWitnesses/Sanity.lean:295).

**M09. The freeze boundary must itself be frozen.** Stopping dependency hashing at L0 is safe only if CI also verifies that each L0 version still names the same definitions. Otherwise an in-place engine edit escapes the catalog lock. Include declaration types and bodies, inductive definitions, opaque dependencies where relevant, and the pinned toolchain/dependency manifest. Separately identify the instance and facets used by each certificate. A semantic freeze is not a substitute for kernel checking. [Design:387](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:387).

For the two minor findings:

- **N01:** `ClaimSpec` has no `RegimeInhabited` field although `Cert` uses it. `FinalityHead` is absent from the facet table. The use of `ProtocolSpec n` needs reconciliation with the new per-label interface. `FGDomain` remains in the layer table. E7 and `LeftAlone` are clearly historical references, so their mere presence is not a defect. The r146 result now exists; r147’s requested output was not present in the inspected files. The “no design items open” statement is therefore premature. [Schema:259](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:259), [open items:664](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:664), [r146 report:3](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/r146-fgsa-adjudicate.md:3).
- **N02:** Safety, inclusion, and nesting do not by themselves certify valid execution data, possession of output data, or conformance to a deployed protocol. The existing `NoFutureRead` predicate is not a bundle field. Add explicit entries or scope statements for these properties. [Core tier:317](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:317), [NoFutureRead:113](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:113).

The future-proofing result is mixed. “Additive” below means that the feature has a direct model without changing L0. It does not mean that existing certificates cover it.

```text
┌───────────────────────────┬────────────────────────┬─────────────────────────────────────────────────────────────────┐
│ Feature                   │ Classification         │ Reason and limit                                                │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Stake weights             │ Additive for finite    │ Integer seat multiplicity works. Add weighted counts and fixed │
│                           │ integer weights        │ weighted identity links; Linked's bijection is insufficient.   │
│                           │                        │ Large multiplicities can make execution and exploration costly.│
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Finite sampled committees │ Additive for fixed     │ E2 supports c sampled seats. Balanced ε must cover the actual  │
│ and ε                     │ committee sizes        │ windows and counted sets. The external probability argument   │
│                           │                        │ needs a sampling/adversary model and a horizon or union bound. │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ VRF selection with        │ Engine change for the  │ Fixed-size age buckets can be labels. Private eligibility,    │
│ eligibility growing       │ general feature        │ random committee size, and a sender's credential test are not │
│ with age                  │                        │ supplied by fixed seats, fixed actTime, and identity-free code.│
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Inclusion-list committees│ Additive               │ Scheduled labels and payloads suffice. Add list-content,       │
│ such as FOCIL             │                        │ inclusion, eligibility, and proposer-compliance claims.        │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Multiple proposers        │ Additive               │ Multiple singleton labels or a multi-seat label work. The      │
│                           │                        │ present Proposals facet and inclusion claims need a proposal  │
│                           │                        │ identifier that distinguishes simultaneous proposals.         │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ DAG or leaderless         │ Additive at L0 for     │ State and payload can contain a DAG. Add DAG output facets and│
│ protocols                 │ scheduled models       │ claims. The fixed FG still needs a chain projection. Immediate│
│                           │                        │ signed responses to receipt need additional emission semantics.│
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Adaptive or mildly        │ Additive for a         │ A new honesty/corruption trace, schedule, and authentication  │
│ adaptive corruption       │ monotone trace model   │ conditions can model behavior before corruption. Current      │
│                           │                        │ static-honest claims do not transfer. Explicit compromise,    │
│                           │                        │ key-erasure, or recovery transitions can require engine work.│
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Late joiners and          │ Additive within a      │ New schedules and payloads can model joining and transfer.    │
│ state transfer            │ finite validator set   │ Add readiness and trusted-checkpoint rules. E6 needs the      │
│                           │                        │ durable-state repair in M02. New membership is not covered   │
│                           │                        │ merely by replaying history.                                  │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Clock drift               │ Engine change for      │ One logical label currently signs at one global actTime.     │
│                           │ drifted logical duties │ Distinct local firing times need local clock inputs and a    │
│                           │                        │ relation to network time. Encoding physical times as new keys│
│                           │                        │ changes authentication semantics and needs a refinement proof.│
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Protocol-driven relay     │ Additive               │ Gossip can carry prior signed objects. Add delivery provenance│
│                           │                        │ and prove relay from protocol behavior plus network fairness.│
│                           │                        │ Restricting delivery alone does not prove relay liveness.     │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ Signature aggregation     │ Additive as an         │ Payloads can contain aggregates with verified signer/payload  │
│                           │ authentication model   │ extraction. Bind carries to that relation. Compact execution  │
│                           │                        │ needs an executable representation and soundness proof.       │
├───────────────────────────┼────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ A second, different FG    │ Usually additive in    │ Add a separate module, facets, and claims. The current        │
│                           │ L2–L5                  │ composition theorem will not transfer automatically. An FG   │
│                           │                        │ whose private lock directly controls AP state can require a │
│                           │                        │ new isolation/certification interface.                       │
└───────────────────────────┴────────────────────────┴─────────────────────────────────────────────────────────────────┘
```

The main source constraints are fixed duty times and identity-free code, arbitrary state/payload types, the static run fields, and the new isolation rule. [Run:38](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:38), [Run:114](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:114), [design:104](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:104), [design:175](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:175). The broad “deferred without risk” claim should be replaced with these limits.

For monotonicity, the **directions of the two abstract implications are correct**: a theorem under a weaker premise applies under a stronger premise, and a stronger conclusion implies a weaker conclusion. The problem is whether each claimed parameter order supports those implications.

In this table, arrows describe changes that make the **whole claim weaker**. All changes must stay within valid parameter bounds and keep the protocol, environment, and facets fixed. `G` means `proposerGap`.

```text
┌──────────────────────────────┬────────────────────────────────────┬─────────────────────────────────────────────────────────────┐
│ Current claim                │ Parameter change                   │ Result                                                      │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Generic.constants            │ Arbitrary component changes        │ No product monotonicity. Valid includes coupled bounds.       │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ confirmedSafe                │ None                               │ C is not used by this field. Safe includes monotonicity.      │
│ stableSafe                   │ None                               │ Same.                                                        │
│ monotone                     │ None                               │ No constants occur. Redundant given both Safe fields.         │
│ nested                       │ None                               │ No constants or execution regime occur.                      │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ confirmedIncluded            │ D_c ↑                              │ FALSE in isolation. True with monotonicity of this output.    │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ stableIncluded               │ θ ↑; η ↑                           │ TRUE: each change strengthens the premise, for θ ≥ 0.         │
│                              │ D_s ↑                              │ FALSE in isolation; needs output monotonicity.                │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ stableIncludedFast           │ D_f ↑                              │ FALSE in isolation; needs output monotonicity.                │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ stableResilient               │ A ↑; Π ↓; θ ↑; η ↑                 │ TRUE, separately within the valid domain.                    │
│                              │                                    │ A restricts arming; Π restricts tested outage windows.        │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ stableResilientFast           │ A_f ↑; Π ↓; θ ↑; η ↑               │ TRUE. General A is replaced, not an additional premise.       │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ recovered.confirmedSafe       │ ρ ↑; θrec ↑; recoveryFull false→true│ TRUE. Also G ↓ is weaker: more frequent proposers are required.│
│ recovered.stableSafe          │ Same                               │ TRUE. θ and η are not used in RecoveryRegime.                 │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ recovered.confirmedIncluded   │ ρ ↑; θrec ↑; recoveryFull false→true│ TRUE; G ↓ also weakens the claim.                            │
│                              │ D_c ↑                              │ FALSE in isolation; needs recovered monotonicity.             │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ recovered.stableIncluded      │ ρ ↑; θrec ↑; recoveryFull false→true│ TRUE; G ↓ also weakens the claim.                            │
│                              │ D_s ↑                              │ FALSE in isolation; needs recovered monotonicity.             │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ Strong.constants             │ strongDelay ↑                      │ Preserves nonnegativity. No validity restriction on faultCap.│
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ strongSafe                    │ faultCap ↓                         │ TRUE: fewer faulty executions must be covered.                │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ strongIncluded                │ faultCap ↓                         │ TRUE. Full participation is a fixed additional premise.       │
│                              │ strongDelay ↑                      │ FALSE in isolation; needs strong-output monotonicity.         │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ strongResilient               │ faultCap ↓                         │ TRUE. Arming is fixed at Δ; there is no A or finite Π parameter.│
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ strongRecoveredSafe           │ faultCap ↓; ρ ↑; θrec ↑; G ↓;       │ TRUE.                                                        │
│                              │ recoveryFull false→true             │                                                             │
├──────────────────────────────┼────────────────────────────────────┼─────────────────────────────────────────────────────────────┤
│ strongRecoveredIncluded       │ faultCap ↓; ρ ↑; θrec ↑; G ↓;       │ TRUE for these changes.                                      │
│                              │ recoveryFull false→true             │                                                             │
│                              │ strongDelay ↑                      │ FALSE in isolation; needs recovered strong monotonicity.      │
└──────────────────────────────┴────────────────────────────────────┴─────────────────────────────────────────────────────────────┘
```

This covers every field of [Generic/Claims.lean](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Claims.lean:13) and [Strong/Claims.lean](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Claims.lean:15). The directions follow from [EtaSleepy:197](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:197), [recurrence:213](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:213), [Outage:44](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:44), and [Recovery:72](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:72).

Two details matter:

- Increasing ρ both narrows the conclusion interval and raises the minimum permitted horizon. Both changes weaken the current recovered claim.
- Increasing Π, increasing `faultCap`, or increasing G makes the corresponding claim stronger. Increasing θ, θrec, η, or an arming lag makes it weaker. Therefore “premise parameters are ordered opposite to conclusion parameters” is not a numerical ordering rule.

The proposed Lean mechanics are mostly feasible, with limits:

- **Dependency hashing:** feasible. Lean exposes declaration bodies and constant dependencies. The installed version includes opaque bodies in `ConstantInfo.getUsedConstantsAsSet`. Use a deterministic graph traversal with cycle handling and an explicit serialization policy. The missing L0 guard in M09 remains necessary. [Local API:65](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Util/FoldConsts.lean:65), [official declaration API](https://lean-lang.org/doc/api/Lean/Declaration.html).
- **Registry attributes:** feasible. `ParametricAttribute` and persistent environment extensions provide the mechanism. An attribute is metadata; its registration code must verify the theorem or certificate type. [Local API:242](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Attributes.lean:242).
- **Kernel-checked finite refutations:** feasible. The checker must establish the actual execution, regime, and failed conclusion—not only simulate the protocol. `Nat` and `Array` do not by themselves establish acceptable performance. The pinned toolchain already has `decide_cbv`, which can produce proofs without `native_decide`; test it on representative traces. A scaled trace refutes the original instance only with a scaling correspondence. [Local tactic:30](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Elab/Tactic/CBV.lean:30), [official tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/).
- **Universal executable checkers:** not guaranteed by the present types. `ProtocolSpec` permits arbitrary types and functions; hooks and `opening` can contain arbitrary propositions. Require an optional executable interface with equivalence proofs. Do not promise a finite checker for every future catalog entry.
- **Lasso refutations:** feasible for selected protocols after infinite execution, fairness, and abstraction semantics are defined. They are not a general replacement for parameterized finite witnesses.

For FG recovery, (D) and the two-arm structure of (E) are useful, but their scope must be precise. At the actual causal cut, the source-store argument bounds old honest row heights by M; old-only crossings can reach M+1. The design’s weaker row bound of M+1 does not state that distinction. NJ is established in the selected event prefix, not forever in every later state at H. The finalized arm needs the actual F*, its crossing properties, and a separate source-history argument. [Causal construction:783](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:783), [NJ scope:474](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:474).

The missing joint proof should expose this sequence:

1. Settle views at a fixed frontier under the recovery fault cap.
2. Bound effective root changes at that frontier.
3. Derive a sufficiently long repair interval without assuming global AP recovery.
4. Produce matching, nonempty progress rows despite old records.
5. Supply mature carriers and obtain a height rise.
6. Select the actual NJ or finalized base.
7. Prove the first-source transfer and retain all later source bodies.
8. Recover the ordinary AP outputs.
9. Establish the separate finality-head and strong-recurrence construction.

The research now supports a conservative paper recovery argument with repair costs per effective attempt. It does not support replacing this sequence with the present short application of (A)–(F), nor does it establish the full first-finality deadline. [Adjudication:509](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:509), [remaining finality work:670](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:670).

**Final verdict: REVISE.** Keep the catalog, partial certification, versioned entries, and optional kits. Before approval, require a coherent certificate/profile schema, correct parameter transport, stronger feasibility checks, executable E5/E6 semantics, and a typed FG interface that exposes the missing recovery obligations. A small compiled prototype of those interfaces should precede the promised migration.

AUDIT COMPLETE: 6 blocking, 9 major, 2 minor