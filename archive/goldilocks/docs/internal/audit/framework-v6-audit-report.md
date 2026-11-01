This is a read-only audit. I changed no files and ran no build. The findings concern the proposed framework, not the soundness of the existing Lean proofs.

The tables use these path abbreviations:

- **D**: [FRAMEWORK-DESIGN.md](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:1).
- **R**: [FG-COMPOSITION.md](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:1).
- **G**, **S**: `lean/available-chain/AvailableChainStatements/Generic/` and `Strong/`.
- **M**: `lean/available-chain/AvailableChainModel/Generic/`.
- Research filenames are under `research/async-resilient-committees/tip-stability/codex/`.
- **BP**: `fgsa-healing-blueprint.md`; **C147**: `fgsa-conditional.md`; **C149**: `fgsa-conditional-close.md`.
- **DC**: `research/healing/rewrite/consensus.tex`.

The requested log tail points to completed r149 and r148 work. I checked those sources too. They materially change the registry assessment.

**0. Disposition of the earlier findings**

“FIXED” means the stated design defect is corrected. It does not mean that the proposed Lean implementation exists.

```text
┌────────┬──────────────┬───────────────────────────────────────────────────────────────┐
│ ID     │ v6 status    │ Reason                                                        │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B01 │ FIXED        │ One instance binds its protocol and facets. Certificates bind  │
│        │              │ claim constants. Profiles require shared constants.           │
│        │              │ D:197, D:260, D:291.                                           │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B02 │ FIXED        │ Exact inclusion uses equality on D. Persistent inclusion has   │
│        │              │ its own order and a Safe-premised relation. D:241–253.          │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B03 │ PARTLY FIXED │ Trigger witnesses improve non-vacuity. The stated hook laws    │
│        │              │ still do not imply continuation feasibility. D:122, D:303; W01. │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B04 │ FIXED        │ Ret includes view membership and the first transfer boundary.  │
│        │              │ Outage protects the armed B. R:19, R:26, R:170.                 │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B05 │ PARTLY FIXED │ Source bodies, entries and finality origins are separated.     │
│        │              │ The composite still confuses row-source and all-body scope.    │
│        │              │ R:99, R:143; W05.                                             │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 B06 │ PARTLY FIXED │ Timed row service and carrier retention are exposed; finality  │
│        │              │ stays conditional. Recovery still uses a false service entry  │
│        │              │ and an incomplete base interface. R:62, R:128; W03, W09.       │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 M02 │ PARTLY FIXED │ Tick order, durable F, projection laws and epochs are added.   │
│        │              │ Receipt monotonicity conflicts with the proposed restart.     │
│        │              │ D:125, D:154, D:176; W04.                                     │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 M04 │ FIXED        │ The frame includes Z and the view. R1 is named as a variant.    │
│        │              │ Viable and filtered correspondences are separate. D:358.      │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 M05 │ PARTLY FIXED │ Minimum horizons and execution prefixes are distinguished.    │
│        │              │ The source scope and NJ-base dependency remain incomplete.    │
│        │              │ D:254, D:384; W05, W09.                                       │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 M06 │ FIXED        │ Decidable preorder, proved transport, valid refutations and    │
│        │              │ Pareto sets are explicit. Witness transport stays separate.   │
│        │              │ D:223, D:297, D:309, D:319.                                   │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ v4 N01 │ PARTLY FIXED │ The old shorthand is removed. The new registry has mutable     │
│        │              │ source references and stale statuses. R:5, R:52, R:62; W08.   │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V01    │ PARTLY FIXED │ Temporary refusal and faulty dependencies are permitted.      │
│        │              │ Receiver feasibility and acceptance relay remain unproved by  │
│        │              │ the required laws. D:111–149; W01.                            │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V02    │ FIXED        │ Ret and N2 now use the correct tree test and q_s boundary.     │
│        │              │ R:19, R:26; C147:117, C147:140.                               │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V03    │ PARTLY FIXED │ Three histories and body-level safety are now explicit.       │
│        │              │ ap.S.v1 still cannot supply the full advertised protected set.│
│        │              │ R:143, R:165; W05.                                           │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V04    │ FIXED        │ HeightRetains is withdrawn. HNI separates old evidence from   │
│        │              │ later retention of qualifying bodies. R:28, R:35; BP:790.    │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V05    │ PARTLY FIXED │ Row windows, parent-chain folding and carrier retention are  │
│        │              │ supplied. The exact-service entry is false. R:62–72; W03.    │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V06    │ PARTLY FIXED │ N1 now fixes the numerical frontier. Fixed-F and effective-N1│
│        │              │ results are separate, but the fixed-F bound is misstated.    │
│        │              │ R:57, R:60, R:148; W07.                                     │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V07    │ PARTLY FIXED │ Trigger witnesses and proposition-only profile equivalence   │
│        │              │ are correct changes. Continuation eligibility remains weak.  │
│        │              │ D:260, D:303; W01.                                          │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V08    │ FIXED        │ Bounds belong to certificates. The preorder has checked      │
│        │              │ transport and supports fixed coordinates. D:223–250, D:291. │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V09    │ FIXED        │ Z, duty views, the F basis and separate correspondences are   │
│        │              │ included. Executable equality with live-cache DC is no longer│
│        │              │ claimed. D:358–367.                                         │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V10    │ PARTLY FIXED │ Policy and template types are described. Universal policies  │
│        │              │ cannot satisfy the registered height-progress claim; Cert    │
│        │              │ also imposes the wrong witness quantifier. D:369–382; W02.   │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V11    │ PARTLY FIXED │ Restore, hooks, AP labels and epoch-local reads are covered.  │
│        │              │ E4 still conflicts with loss of receipt state at restart.    │
│        │              │ D:167–183; W04.                                             │
├────────┼──────────────┼───────────────────────────────────────────────────────────────┤
│ V12    │ PARTLY FIXED │ A registry replaces the stale prose, but it already disagrees│
│        │              │ with completed research and does not pin source versions.    │
│        │              │ R:5, R:52, R:62; C149:130, C149:463; W08.                    │
└────────┴──────────────┴───────────────────────────────────────────────────────────────┘
```

**1. New or remaining v6 findings**

```text
┌─────┬──────────┬────────────┬───────────────────────────────┬─────────────────────────┬────────────────────────────────┐
│ ID  │ Severity │ Section    │ Finding                       │ Evidence (file:line)    │ Proposed fix                   │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W01 │ BLOCKING │ D E4, §5   │ HooksSound and Deliverable    │ D:122, D:128, D:146;    │ Require emitted-wire validity, │
│     │          │            │ do not imply the claimed      │ G/Conditions.lean:52,   │ sound handler coverage and     │
│     │          │            │ run-extension theorem.        │ G/Conditions.lean:153   │ receiver delivery feasibility. │
│     │          │            │                               │                         │ Prove acceptance relay apart.  │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W02 │ BLOCKING │ D §7.3;    │ An arbitrary FG policy can    │ D:291, D:370–382;       │ Quantify AP service facts over │
│     │          │ R §2       │ withhold all progress rows.    │ R:57; C147:410          │ policies. Derive FG progress   │
│     │          │            │ Universal Cert also requires  │                         │ after Simplex specialization.  │
│     │          │            │ witnesses for every policy.   │                         │ Separate family proof/witness.│
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W03 │ BLOCKING │ R ap.X,    │ ap.X.v1 is false, although    │ R:62, R:79, R:146;      │ Withdraw X. Register X+ and    │
│     │          │ recovery   │ marked PROVED. The recovery   │ BP:248; C149:538–561,   │ prove its extra premises at    │
│     │          │            │ interface uses this entry.    │ C149:632                │ each composition call.         │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W04 │ MAJOR    │ D E4/E6    │ Global processed/depsPresent  │ D:125, D:176;           │ Make receipt monotonicity      │
│     │          │            │ monotonicity conflicts with   │ GridCO/Model/           │ epoch-local, or preserve the   │
│     │          │            │ restart that loses the store. │ Protocol.lean:344       │ complete required state.       │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W05 │ MAJOR    │ R §4       │ “ap.S.v1 enough” changes the  │ R:143; BP:520, BP:684,  │ Give row-only healing its own  │
│     │          │            │ protected set of fgHealed.    │ BP:1103; C147:170       │ entry, or require safety for   │
│     │          │            │                               │                         │ every fast and slow body.      │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W06 │ MAJOR    │ R §3;      │ FJ changes the fixed frame    │ D:360; R:119, R:128;    │ Use a separate module version │
│     │          │ D §7.2     │ rule. It is not merely a base │ fgsa-no-nj-opus.md:565, │ and a different noninterference│
│     │          │            │ selector satisfying HNI.      │ fgsa-no-nj-opus.md:619  │ interface for FJ.              │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W07 │ MAJOR    │ R §4       │ The stated fixed-F addition   │ R:148–150;             │ Copy the actual fixed-F bound.│
│     │          │            │ to the healing bound omits    │ BP:1038–1046           │ List effective-N1 liveness as  │
│     │          │            │ an entire repair term.        │                         │ a premise of the uniform bound.│
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W08 │ MAJOR    │ R sources  │ Immutable entry IDs refer to  │ R:5, R:40, R:52–65;    │ Pin source content and exact   │
│     │          │ and status │ mutable sections. Several     │ C149:130, C149:143,     │ statements. Track dependencies│
│     │          │            │ statuses are already stale.   │ C149:436, C149:463      │ and update status separately. │
├─────┼──────────┼────────────┼───────────────────────────────┼─────────────────────────┼────────────────────────────────┤
│ W09 │ MAJOR    │ R base     │ HNI alone is insufficient as  │ R:128; BP:138, BP:500,  │ Return the causal cut, fresh   │
│     │          │ interface  │ a recovery-base interface.    │ BP:790, BP:844         │ first-source facts and arm     │
│     │          │            │ The NJ form also depends on   │                         │ witnesses. Prove NJ persistence│
│     │          │            │ the joint source induction.   │                         │ in that joint induction.       │
└─────┴──────────┴────────────┴───────────────────────────────┴─────────────────────────┴────────────────────────────────┘
```

**2. Arguments and counterexamples**

**W01 — The continuation theorem needs stronger premises.** Consider a protocol that emits a malformed object after it accepts one trigger message. Give it no dependencies, monotone receipt flags, `excludes = false`, and `handles` equal to object equality. These choices satisfy the listed E4 laws and the accepted-dependency condition. A prefix that contains the trigger can be valid before the next broadcast deadline. It cannot extend past that deadline: synchrony requires a handler call for the emitted object, while `DeliveryWellFormed.wire` forbids its delivery. Benign runs that never receive the trigger can exist at every horizon. Thus trigger witnesses do not close this gap. Moreover, an emitter’s acceptance order need not make dependencies available at another receiver. E4 expressly limits its result to handler calls, but all current main regimes require **acceptance** relay. Those are different obligations. [E4](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:122), [delivery validity](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:52), [acceptance relay](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:153).

**W02 — Havoc makes the registered liveness conclusion impossible.** Choose a policy that always emits empty height pairs, and let faulty validators remain silent. Honest AP proposals can continue, but no progress quorum forms. At height 1, the frame can remain static forever. N1 and the AP delivery/proposer premises hold; `(L)` nevertheless requires a height rise. The research proof obtains matching rows by unfolding the **Simplex** record cases, which an arbitrary policy need not follow. The uniform AP obligation should establish repair, source production and carrier service. Simplex should supply permitted matching rows afterward. There is also a type-level contradiction: `∀ σ, Cert c (inst T σ)` includes `inhabited` for every σ, whereas §7.3 requires it only for Simplex. Use a family proof at fixed constants plus a separate Simplex witness. [Policy family](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:369), [Simplex cases used by L](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:451).

**W03 — The registry’s exact-service theorem has a reachable counterexample.** With `n=4`, `a=1`, and `Δ=16`, an honest proposer has a lease on K at time 640 and proposes P on K. The lease expires at the HEAD time 656. All live leases then precede K, vacuously; the genesis root and height-1 frame satisfy `(x2)`. But the previous votes give K score 1 and a conflicting branch Y score 3. Every HEAD selects Y, and every S still excludes P at its deadline 736. This is the completed r149 counterexample. The existing Lean service theorem also requires the parent to equal the ordinary proposal walk result. The proposed replacement `(X+)` adds that condition and a supported prefix that reaches the band. The composition must discharge both conditions; changing the registry status alone is insufficient. [Counterexample](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional-close.md:538), [existing Lean premise](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/ProposalHeads.lean:19), [X+](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional-close.md:632).

**W04 — Restart and receipt monotonicity conflict.** Before restart, a node can hold block B outside the retained F basis. Then `processed B` and the dependency test for a child of B are true. Restoring only Λ, F and its basis loses B, so those predicates become false under the current hook meanings. Making the flags remain true without retaining B instead breaks their meaning and can prevent necessary redelivery through the freshness check. Epoch-local output claims do not repair this hook conflict. Specify epoch-local receipt facts and explicit restart rules for delivery obligations. [Restart](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:176), [current hook meanings](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:344).

**W05 — The protected-set scope changes between input and output.** `ap.S.v1` covers selected row sources at FG action labels. The cited definition of `FG-healed` covers the set 𝒫 containing **every** fast body after the reset and every qualifying slow body. A body need not become a row source. The blueprint’s H17 reduction can support a restricted row-source theorem; it cannot establish the unchanged all-body definition. r149 now supplies paper safety statements for the larger set, but the registry must identify those inputs and their scope explicitly. [Registry claim](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:143), [protected set](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:520), [FG-healed definition](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:684).

**W06 — FJ needs a different module contract.** The fixed v6 frame selects J whenever `H=j+1` and uses threshold `H−1`. FJ adds a frontier test; in a contest it selects F and uses threshold **H**. Its source explicitly replaces these rules. Further, FJ can retain a height-`M+1` source that does not extend an old justified entry at M. That is precisely a failure of `HNI(M+1).h1`, even though FJ’s modified filter protects the source. Therefore `fg.base.fj.v1` cannot plug into the stated fixed frame and sole HNI obligation. This does not refute FJ; it refutes the proposed interchangeable interface. [Fixed frame](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:358), [FJ rules](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-no-nj-opus.md:563), [conflicting old J case](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-no-nj-opus.md:612).

**W07 — The fixed-F bound does not match its source.** Put `N=D+K+5`. The registry presents the uniform `2N(λ+θ)` bound with an extra `M(λ+θ)` for fixed F. The cited source instead gives an additional `(H+2−f₀)(λ+θ)`, or the conservative total `(3N+M)(λ+θ)`. The registry omits `N(λ+θ)` from that conservative form. In the shared example with `M=1`, the registry’s reading gives 5206Δ; the source’s sharper fixed-F calculation gives 7472Δ. Also list the effective-N1 version of `(L)` among the uniform bound’s hypotheses. That version remains open in r149. [Registry bound](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:146), [source bound](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:1026), [effective-N1 status](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional-close.md:432).

**W08 — The split lacks an immutable source boundary.** Moving exact statements out of the framework is reasonable. Referring to mutable research sections does not make an entry immutable or prevent drift. A later edit can change the proposition behind `.v1` without changing either registry file. The declaration freeze covers future Lean declarations, not these paper references. This has already produced status errors: r149 proves the broader `(S)` and `(S_slow)`, refutes `(X)`, and leaves effective `(L)` open. The registry still describes r149 as pending. Pin the complete statement, hypotheses, module version and source content hash for each entry. Keep later proof-status updates separate from statement changes. [Registry source policy](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:3), [r149 results](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional-close.md:23).

**W09 — HNI is a structural fact, not a complete recovery-base witness.** `HNI(1)` holds from the genesis conventions, but it does not make the first height-1 sources synchronous. The reset proof additionally uses a causal cut M, `x>M`, a first honest row above x after that cut, and its first-transfer view facts. These facts make `(S)` applicable. The NJ arm also cannot obtain run-wide HNI merely by selecting an NJ height: the blueprint proves its permanent absence of justification through Theorem N’s joint induction. Requiring that run-wide fact as an independent base input hides the dependency. Return the prefix NJ record facts or the actual finalized checkpoint, together with the cut and first-source facts. Derive permanent HNI in the joint proof. [Sole obligation](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md:128), [reset construction](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:500), [NJ dependency](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-healing-blueprint.md:844).

**3. Future-proofing**

“Additive” means that L0 need not change. It does not mean that existing certificates cover the feature.

```text
┌───────────────────────────┬───────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Feature                   │ Classification            │ Reason and limit                                             │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Stake weights             │ Additive for fixed        │ Integer seat multiplicity works. Add weighted assignment,    │
│                           │ integer weights           │ links, thresholds and quorum proofs. Unit-weight FG proofs   │
│                           │                           │ do not transfer automatically. Large weights can be costly.  │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Finite sampled committees │ Additive for fixed        │ Per-label seat counts suffice. Balanced-ε must cover the     │
│ and ε                     │ sizes per label           │ actual counted windows and sets. Probability, adversary      │
│                           │                           │ knowledge and horizon bounds remain external obligations.    │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ VRF self-selection with   │ New engine for private    │ Identity-free code has no private seed or local eligibility  │
│ age-growing eligibility   │ self-selection            │ state. Public fixed-size age buckets are additive, but do    │
│                           │                           │ not model that private process.                              │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ FOCIL / inclusion-list    │ Additive when scheduled   │ Add duties, list payloads, validation and proposer inclusion │
│ committees                │                           │ claims. The existing block-inclusion claim is insufficient.  │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Multiple proposers        │ Additive                  │ Use multiple proposal labels and identifiers. Selection and  │
│                           │                           │ fairness need new claims; every conflicting honest proposal  │
│                           │                           │ cannot satisfy the old chain-inclusion conclusion.          │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ DAG or leaderless         │ Additive when scheduled; │ State and payload types can contain DAGs. Add output facets. │
│ protocols                 │ new engine for immediate │ Simplex needs a proved chain projection. Receipt-triggered   │
│                           │ signed receipt responses │ signing falls outside tick-only emission.                   │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Adaptive or mildly        │ Additive for abstract    │ New regimes can constrain corruption times, pre-corruption │
│ adaptive corruption       │ corruption traces; new   │ behaviour and signature origins. Explicit compromise, key  │
│                           │ engine for key events    │ extraction or erasure requires new semantics. Current       │
│                           │                           │ static-honesty claims do not cover these additions.          │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Late joiners and state    │ Additive in a fixed      │ Use restart plus authenticated transfer objects and new     │
│ transfer                  │ population, after W04    │ readiness/catch-up regimes. Dynamic validator admission or  │
│                           │                           │ new key ownership needs a further model.                     │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Clock drift               │ New engine for direct   │ One label has one global act time. Local firing times and   │
│                           │ modelling                 │ clock-dependent transitions are absent.                     │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Protocol-driven relay     │ Additive for tick-based │ Add send queues and send provenance to delivery conditions. │
│                           │ relay                     │ Prove dissemination from protocol sends. Immediate signed   │
│                           │                           │ replies require the excluded receipt-signing extension.      │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Signature aggregation     │ Additive as an idealized│ Add aggregate objects and sound signer extraction, with     │
│                           │ object representation    │ duplicate control and signature-origin proofs. Compression  │
│                           │                           │ alone does not establish these facts.                       │
├───────────────────────────┼───────────────────────────┼──────────────────────────────────────────────────────────────┤
│ A second, different FG    │ Additive within E5 and   │ Give it separate module versions and composition proofs.    │
│                           │ scheduled-duty scope     │ A gadget whose private record controls AP choices needs a  │
│                           │                           │ different isolation interface; it cannot use E5 unchanged.  │
└───────────────────────────┴───────────────────────────┴──────────────────────────────────────────────────────────────┘
```

The bounded scope in v6 is much more credible than the original broad promise. The controlling restrictions are the duty schedule, identity-free honest code, run assignments and record isolation. [Scope](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:42), [current protocol interface](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:46).

**4. Monotonicity and catalog mechanics**

The old `Prem`/`Concl` fields are absent in v6. The single checked `transport` implication is a valid replacement. Conceptually, premise strengthening needs `Prem new → Prem old`; conclusion weakening needs `Concl old → Concl new`.

The arrows below make the **whole claim weaker**, with protocol, environment and facets fixed. Both parameter tuples must satisfy validity constraints.

```text
┌────────────────────────────────┬───────────────────────────────────────────────┬──────────────────────────────────────┐
│ Current claim                  │ Weakening direction                           │ Assessment                           │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ Generic.constants              │ No unrestricted product order                 │ Valid has coupled constraints.       │
│ confirmedSafe                  │ No claim constants occur                      │ Parameter-independent.               │
│ stableSafe                     │ No claim constants occur                      │ Parameter-independent.               │
│ monotone                       │ No claim constants occur                      │ Parameter-independent; already       │
│                                │                                               │ included in the two Safe fields.     │
│ nested                         │ No claim constants occur                      │ Parameter-independent.               │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ confirmedIncluded              │ D_c ↑                                         │ False alone for exact-time inclusion.│
│                                │                                               │ True with output monotonicity.       │
│ stableIncluded                 │ θ ↑; η ↑                                      │ True: stronger regime premises.      │
│                                │ D_s ↑                                         │ Needs output monotonicity.           │
│ stableIncludedFast             │ D_f ↑                                         │ Needs output monotonicity.           │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ stableResilient                 │ A ↑; Π ↓; θ ↑; η ↑                            │ True, separately in the valid domain.│
│ stableResilientFast             │ A_f ↑; Π ↓; θ ↑; η ↑                          │ True. General A is replaced by A_f.  │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ recovered.confirmedSafe        │ ρ ↑; θrec ↑; G ↓; recoveryFull false → true    │ True. θ and η are unused.            │
│ recovered.stableSafe           │ Same                                          │ True.                               │
│ recovered.confirmedIncluded    │ Same; D_c ↑ only with recovered monotonicity   │ True with that qualification.        │
│ recovered.stableIncluded       │ Same; D_s ↑ only with recovered monotonicity   │ True with that qualification.        │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ Strong.constants               │ strongDelay ↑ preserves validity              │ Only delay nonnegativity is required.│
│ strongSafe                     │ faultCap ↓                                    │ True.                               │
│ strongIncluded                 │ faultCap ↓                                    │ True. Full participation is fixed.  │
│                                │ strongDelay ↑                                 │ Needs strong-output monotonicity.    │
│ strongResilient                 │ faultCap ↓                                    │ True. Arming is Δ; no finite Π.      │
│ strongRecoveredSafe            │ faultCap ↓; ρ ↑; θrec ↑; G ↓;                 │ True.                               │
│                                │ recoveryFull false → true                     │                                     │
│ strongRecoveredIncluded        │ Same                                          │ True.                               │
│                                │ strongDelay ↑                                 │ Needs recovered strong monotonicity. │
├────────────────────────────────┼───────────────────────────────────────────────┼──────────────────────────────────────┤
│ New includedPersist variants   │ Corresponding D ↑                             │ True by interval restriction.        │
└────────────────────────────────┴───────────────────────────────────────────────┴──────────────────────────────────────┘
```

These checks cover every field in [Generic claims](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Claims.lean:13) and [Strong claims](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Claims.lean:15). The critical definitions are [exact-time inclusion](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Properties.lean:89), [η-sleepiness and recurrence](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:197), and [Recovery](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:72).

Increasing ρ both postpones the conclusion’s start and raises the regime’s minimum horizon. Both weaken the claim. Increasing Π, G or `faultCap` instead strengthens the corresponding claim. Numerical “up” is therefore not a general premise order.

The Lean mechanisms are feasible:

- **Dependency freeze:** Traverse declaration types and bodies transitively, with cycle handling and deterministic serialization. Include inductive/recursor metadata and distinguish legitimate axioms from unavailable bodies. The pinned Lean source exposes opaque bodies through `getUsedConstantsAsSet`; the [official API](https://lean-lang.org/doc/api/Lean/Util/FoldConsts.html) confirms the dependency mechanism. W08 concerns the separate paper-source boundary.
- **Registry attributes:** Persistent environment extensions and parametric attributes provide the required mechanism. Registration must check the elaborated certificate type, canonical claim identity, constants and allowed axioms. An attribute itself proves nothing. [Lean attribute API](https://lean-lang.org/doc/api/Lean/Attributes.html).
- **Finite refutations:** A proved Boolean checker can establish execution validity, regime membership and a failed conclusion. `decide_cbv` is available in the pinned toolchain. Arbitrary protocol functions and propositions still require executable representations and correspondence proofs, as v6 now states. [Pinned implementation](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Lean/Elab/Tactic/CBV.lean:30).
- **Lassos:** They are outside the present finite-run scope. A later lasso theorem needs infinite execution, fairness and a simulation for the repeated abstraction. Growing clocks, blocks and records prevent a general exact-state cycle check. Parameterized finite refutations remain valid without lassos.

The proposed **v1 → v2 lift is feasible**. Use disjoint old-duty and proposal labels, preserve old-duty/proposal/gossip order, and map `.proposer s` to seat 0 of the one-seat proposal label. Crucially, `CStar` must prove that the **actual `seatOf` function** is bijective; an unrelated equivalence between equally sized types is insufficient.

With no self-visible labels and no restarts, the state fold can match v1. The proof must also preserve signatures, embedded objects, handler relations, emissions and regimes. Then `proposerOf s` is recovered from the proposal seat holder, so proposer-quantified claims transfer too. Certificate eligibility remains separate. I agree with the estimate of several engineer-weeks; dependent casts and regime transport will likely cost more than the basic state simulation. [Lift proposal](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:185), [v1 emission order](/Users/francesco/ethereum/lean/available-chain/AvailableChainModel/Generic/Run.lean:141).

The FG checks have the following result:

- **Frames:** The new shape can represent R1 correctly. Its D is the filtered domain; the viable set omits the Z restriction. Keep the current accepted F and its acceptance basis, including the carrier and viability witness. Historical admitted branches can still affect maxima after their children fail admission. These details must remain in the correspondence theorem. The result is about **R1 DC**, as v6 now correctly says. [DC admission and updates](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex:921), [R1 basis rule](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:138).
- **Static and target preservation:** N1 is suitable for a stopped liveness interval; N2 is suitable for source safety. Neither should imply the other. During Outage, preserve the armed B. Do not require every later source body to form one chain: two partition branches can both extend B. The r146 proof follows this distinction. [Outage argument](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-adjudicate.md:366).
- **Causal cap and both base arms:** At the actual cut, earlier honest row heights are at most M; old-only carriers can reach M+1. The finalized arm uses the actual F* and the finalized-crossing theorem. The NJ arm initially gives prefix facts, extended by the joint induction. These are consistent with DC. [Cap](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-conditional.md:642), [DC finalized crossing](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50).
- **Certified pairs:** Requiring a source for every height pair, including repeats and timeouts, matches the FG-SA rule. Finality pairs instead use a justified head and the record permission checks. They do not require a fabricated fresh AP source. [Exact client](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-fast.md:268).
- **Internal facets:** Names such as `Protected` and `FGTarget` are not semantic evidence. Composition must use the actual source body, actual emitted row and actual HEAD conclusion. The new body-level source statements provide the right form; W02 and W05 prevent the present registry from being a complete generic certificate interface.

The current regime prefix results are:

```text
┌───────────────┬────────────────────────────────────────────────────────────────────┐
│ Regime        │ Closure under complete time truncation                             │
├───────────────┼────────────────────────────────────────────────────────────────────┤
│ Sleepy        │ Yes, at nonnegative cutoffs, with E and assignments unchanged.      │
│ StableSleepy  │ Yes; preserve the same awake history used by η.                     │
│ Fast          │ Yes, on the same basis.                                            │
│ Outage        │ Only at cutoffs ≥ b₁, with the original parameters fixed.           │
│ FastOutage    │ Same restriction as Outage.                                        │
│ Recovery      │ Only at cutoffs ≥ GST+ρ. Recurrence tests completed windows.        │
│ StrongArmed   │ Only at cutoffs ≥ b₀.                                              │
└───────────────┴────────────────────────────────────────────────────────────────────┘
```

An arbitrary event-list prefix can still omit another node’s tick at the same time and violate `tick_total`. v6 correctly introduces separate execution-prefix predicates. [Schedule](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:38), [regimes](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:14), [StrongArmed](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Regimes.lean:19).

The research’s first-failure induction can avoid circularity: it uses prior source coverage, same-label compatibility and prefix NJ facts to establish the next retention step. The registry must preserve those dependencies. Run-wide NJ HNI cannot replace the prefix facts at the start.

The joint recovery argument therefore remains conditional. Literal-N1 progress, timed carrier service, causal arrival and the two base arms have paper support. Full output recovery still needs the corrected `(X+)` calls. The uniform bound additionally needs effective-N1 liveness. First finality still needs record permission, a usable non-NJ height, the timed carriers and strong recurrence. Keeping those finality entries conditional is correct; I do not count that declared research work as another defect.

**5. Verdict: REVISE**

Keep the catalog structure, fixed instance facets, per-certificate constants, checked transports and versioned modules. The split into a stable framework and a research registry is useful only with pinned statements and complete dependency records.

Before adoption, close E4’s feasibility contract, replace the impossible universal-policy liveness obligation, withdraw `(X)`, reconcile restart with receipt state, and correct the registry’s scope, module boundaries and bounds. The Phase 0 prototype should exercise these interfaces before they are frozen.

AUDIT COMPLETE: 3 blocking, 6 major, 0 minor