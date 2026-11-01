The plan needs revision. L* has a permanent proposal refusal that the plan does not classify. Task 6 also has status and instance-identity defects.

No repository file was changed. Three scratch files under `/private/tmp` passed `lake env lean`. No full build was run.

In the table, `P` means the audited plan, and `G`, `L`, `F`, and `R` mean `AvailableChainGridCO`, `AvailableChainLStar`, `AvailableChainFramework`, and `AvailableChainRegistry`. Other paths are relative to the project root.

```text
┌────────┬──────────┬────────┬───────────────────────────────────┬──────────────────────────────────┬───────────────────────────────────┐
│ Id     │ Severity │ Task   │ Finding                           │ Evidence (file:line)              │ Proposed fix                      │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-01 │ BLOCKING │ 2      │ L* also permanently refuses a     │ L/Model/Protocol.lean:283,315;    │ Add proposal exclusion for a      │
│        │          │        │ different proposal envelope for   │ P:236                            │ known block and an unprocessed    │
│        │          │        │ an already stored block.          │                                  │ envelope; prove permanence.       │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-02 │ MAJOR    │ 6      │ Unchanged status rules mark all   │ scripts/Registry.lean:46,157;     │ Retain conditions, or define a    │
│        │          │        │ Task 5 theorem rows CONDITIONAL,  │ P:344,347                        │ checked policy for theorem        │
│        │          │        │ not the promised LEAN.            │                                  │ families. Check their axioms.     │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-03 │ MAJOR    │ 6      │ MATRIX has no status rule for     │ P:345;                           │ Gate result cells by status.      │
│        │          │        │ CONDITIONAL or UNSOUND rows. A    │ scripts/Registry.lean:157         │ Do not turn conditional or        │
│        │          │        │ map from kind alone can report    │                                  │ unsound rows into cert or holds   │
│        │          │        │ results that are not proved.      │                                  │ results.                          │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-04 │ MAJOR    │ 6      │ The current key for SA-PC base    │ scripts/Registry.lean:156;        │ Resolve the base projection to    │
│        │          │        │ rows is                           │ P:318,345                        │ its source instance. Test that    │
│        │          │        │ StrongInstance.toInstance, not    │                                  │ both SA-PC profiles share one     │
│        │          │        │ sapcInst.                         │                                  │ row.                              │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-05 │ MAJOR    │ 1 / I9 │ The promise that only             │ P:59,186,204;                    │ Use conditional relay interfaces  │
│        │          │        │ WindowMargin changes is false for │ G/Proofs/Paths.lean:333           │ for all object classes. Specify   │
│        │          │        │ proposal exclusions.              │                                  │ the I9 proof repairs.             │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-06 │ MINOR    │ 0      │ Kit.Core changes namespace        │ F/Kit/Core.lean:7;               │ Keep the existing namespace, or   │
│        │          │        │ despite the rule that moved names │ P:118,131                        │ list the rename and provide       │
│        │          │        │ stay unchanged.                   │                                  │ compatibility aliases.            │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-07 │ MINOR    │ 0 / 7  │ The Engine report row is closed   │ docs/PHASE0-REPORT.md:269;        │ Extract the remaining generic     │
│        │          │        │ although Counter helper           │ R/CounterRun.lean:36,63;          │ helpers, or leave that part of    │
│        │          │        │ extraction is absent.             │ P:352                            │ the row open for 1c.              │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-08 │ MINOR    │ Survey │ AcceptedObjectRelay also has      │ P:47,52;                         │ Say no regime field and no proved │
│        │          │        │ non-SA-PC uses. Missing run       │ R/CounterRun.lean:469;            │ general horizon family. Retain    │
│        │          │        │ proofs do not prove nonexistence. │ G/Proofs/HealthyPrefix.lean:93    │ the other theorem uses.           │
├────────┼──────────┼────────┼───────────────────────────────────┼──────────────────────────────────┼───────────────────────────────────┤
│ P1b-09 │ MINOR    │ Rules  │ The cited rules do not prohibit a │ P:60; AGENTS.md:7;               │ Describe this as the chosen       │
│        │          │        │ protocol library from importing   │ docs/FRAMEWORK-DESIGN.md:91;      │ import boundary, or add an        │
│        │          │        │ Framework.                        │ lakefile.toml:42                 │ explicit rule and check.          │
└────────┴──────────┴────────┴───────────────────────────────────┴──────────────────────────────────┴───────────────────────────────────┘
```

The following counterexamples and scratch results support the BLOCKING and MAJOR findings.

**P1b-01.** Take two well-formed proposals with the same block `B`, but different raw HEAD lists. Accept the first. For the second, dependencies are present, `processed = false`, and the planned exclusion is false. Its handler returns the state unchanged because `B` is stored. Every later state that retains `B` also refuses that envelope. L* never removes stored blocks or admits another envelope for a stored block. A faulty proposer can sign both envelopes.

[LStarRefusal.lean:4](/private/tmp/phase1b-audit-ge0rb359/LStarRefusal.lean:4) checks this with three seats and all ticks through time 4. It also proves the refusal for **any** state containing `B`; that theorem uses only `propext`. This is a handler counterexample, not a compiled complete regime run. `HooksSound` alone will not detect the missing classification: its fields require stability and inertness, but not completeness of exclusion. [Hooks.lean:31](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Hooks.lean:31)

**P1b-02.** The scanner sets `conditional := true` for any leading binder. Thus `p`, `G`, and `hG` already make Task 5’s rows conditional. The scratch scan returned:

```text
head = AvailableChain.Framework.Profile.holdsAt
conditional = true
```

The unchanged status branch then prints `CONDITIONAL (not a certificate)` and skips its axiom check. Task 6’s “all LEAN” checkpoint cannot pass as specified. [Audit.lean:46](/private/tmp/phase1b-audit-ge0rb359/Audit.lean:46), [Registry.lean:157](/Users/francesco/ethereum/lean/available-chain/scripts/Registry.lean:157)

**P1b-03.** This declaration compiles without a forbidden axiom:

```lean
def conditionalCert (h : False) :
    Cert includedConfirmed Sanity.sanity := False.elim h
```

It supplies no certificate. Sanity inclusion is already refuted. The scanner returns kind `cert` and status `CONDITIONAL`; a MATRIX mapping based only on kind would nevertheless print `cert`. Task 6 must specify status filtering before implementation. This is a defect in the proposed mapping, not a claim about an existing MATRIX implementation. [RegistryAudit.lean:8](/private/tmp/phase1b-audit-ge0rb359/RegistryAudit.lean:8), [Sanity.lean:83](/Users/francesco/ethereum/lean/available-chain/AvailableChainRegistry/Sanity.lean:83)

**P1b-04.** For the exact result shape `ac43.holdsAt (sapcInst p).toInstance C`, the scratch scan returned:

```text
instance head = AvailableChain.Framework.StrongInstance.toInstance
```

The existing extractor therefore cannot join this result to the proposed `sapcInst` row. It can also merge unrelated projected strong instances under that same name. The strong profile uses `sapcInst` directly, which makes the mismatch visible. [RegistryAudit.lean:14](/private/tmp/phase1b-audit-ge0rb359/RegistryAudit.lean:14)

**P1b-05.** Suppose I9 adds exclusion for an unprocessed proposal whose block fails `rootOK`. That proposal is a direct counterexample to Task 1’s unrestricted `excludes_proposal`: its hypothesis specifies only the payload constructor. Yet Step 4 uses that theorem inside proposal relay proofs instead of adding a conditional relay interface. Those proof bodies must change.

The SA-PC `rfl` calls at lines 265 and 275 also need replacement if its exclusion changes. For the proposed state-independent root check, source acceptance can supply root validity, including for a faulty proposer’s object. “Honest proposals have good roots” alone does not cover all accepted-object relays. The recommended r194/r196 wire-and-handler fix may avoid adding proposal exclusion for admissible deliveries, but it still requires admission-proof repairs. [ReceiptRelay.lean:260](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Proofs/ReceiptRelay.lean:260), [root-design.md:165](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/root-design.md:165), [root-nonce.md:110](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/root-nonce.md:110)

Answers to questions 1–9 follow.

1. **Premises and contract.** No regime field uses `AcceptedObjectRelay` or `HealthyAcceptedObjectRelay`. The five direct regimes use exempt handler-call delivery; derived regimes inherit it. Both delivery conditions have the exclusion premise. The stated E4 acceptance-coverage gap is therefore closed today: a late HEAD can receive a handler call that refuses it, without violating the regime. No remaining regime field carries that acceptance obligation. Survey finding 1 is correct on the contract, but incorrect about exclusive SA-PC use of the old predicates. [Conditions.lean:104](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:104), [Generic/Regimes.lean:14](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Regimes.lean:14), [Strong/Regimes.lean:19](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Strong/Regimes.lean:19), [QuorumRecovery.lean:11](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Statements/QuorumRecovery.lean:11)

2. **Grid CO exclusion.** Survey finding 3 is correct for unprocessed, admissible HEADs. `r + 1 < current` is equivalent to the old-label refusal, and the other permanent refusal is existing equivocation evidence. Votes only grow; valid schedules prevent clock reversal. Carried raw HEADs use the same `admitVote`, so they cannot bypass either refusal. The new membership conjunct keeps processed HEADs disjoint from exclusion. For a well-formed, dependency-ready, unprocessed proposal, only a future slot can delay admission. Malformed objects are outside the valid-delivery domain. The unrestricted handler-relay lemmas can become false, but the two faulty-HEAD callers already permit equivocation: `synchronous_accepted_head_before` and `stored_head_before_ready_proposal`. I found no additional contradiction in their public conclusions. [Protocol.lean:300](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:300), [CrossView.lean:62](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/CrossView.lean:62), [ProposalViewRelay.lean:64](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/ProposalViewRelay.lean:64)

3. **WindowMargin and relay.** A non-exclusion premise at the actual network deadline is sound. Time bounds suffice for the old-label case, but do not rule out equivocation. Faulty-HEAD callers must first split on equivocation and prove the stamped-evidence branch; they cannot always discharge `hx`. Their existing conclusions support that repair. For example, with `Δ = 2`, a label-1 HEAD accepted at time 23 has deadline 25, after its window closes at 24; an unconditional relay call can now be absent. The actual proof cutoffs remain within the safe margin. Specify both network branches’ deadlines, or use non-exclusion at a common cutoff with a proved stability bridge. The I9 promise needs P1b-05’s fix. [Proposals.lean:113](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/Proposals.lean:113), [ReceiptRelay.lean:133](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/ReceiptRelay.lean:133)

4. **SA-PC.** Survey finding 2 is correct on the valid-delivery domain. Old and third HEADs enter `receivedHeads` even when the base cache refuses them. Proposal `processed` means block membership, so a different envelope for a stored block is already processed. With `wellFormed` and `depsPresent`, a fresh PC envelope waits only for its time bound; retaining a better `bestPC` does not prevent `pcValid`. I found no additional permanent refusal requiring SA-PC exclusion today. The PC `handles` branch is also contained in `carries`. [Handlers.lean:9](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Model/Handlers.lean:9), [Handlers.lean:45](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Model/Handlers.lean:45), [Certificates.lean:33](/Users/francesco/ethereum/lean/available-chain/AvailableChainSAPC/Model/Certificates.lean:33)

5. **L*.** Survey finding 4 is false as a complete classification. The third distinct HEAD is permanently refused, and old HEADs remain admissible. But the proposal-envelope case in P1b-01 is another permanent refusal. The plan must address it before claiming E4 completion. The separate statement that L* has no contract proof is correct. [Protocol.lean:266](/Users/francesco/ethereum/lean/available-chain/AvailableChainLStar/Model/Protocol.lean:266), [Protocol.lean:312](/Users/francesco/ethereum/lean/available-chain/AvailableChainLStar/Model/Protocol.lean:312), [Contract.lean:58](/Users/francesco/ethereum/lean/available-chain/AvailableChainLStar/Statements/Contract.lean:58)

6. **Kit split.** Survey finding 7 is substantially correct. The selected engine declarations are generic; the Grid CO section of `Execution.lean` must remain. Replace the old transitive imports when moving the generic part. None of the five protected FG-SA module paths needs to move. The two transitivity statements are definitionally equivalent through `Block.Preceq`. The Core namespace and unfinished Counter extraction need the minor fixes above. These moves do not themselves require a changed lock line. [Execution.lean:6](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/Execution.lean:6), [Execution.lean:212](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/Execution.lean:212), [Kit/Core.lean:13](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Kit/Core.lean:13)

7. **Instances and `holdsAt`.** The four instance shapes type-check when supplied with hook proofs. Both `p.engine.Δ = p.Δ` and the SA-PC `sface` equality close by `rfl`. All four proposition adapters also elaborate against the current protocols. This does not validate the new hook proofs or the changed Grid CO implementation. The sample lambdas produce unused-`W` warnings; use `_` for `--wfail`. `holdsAt` has no inhabitation field and is correctly distinct from a certificate. The proposed kind mapping says `profile-holds → holds`, not `cert`, but Tasks 6’s status and identity handling remain defective. [Audit.lean:32](/private/tmp/phase1b-audit-ge0rb359/Audit.lean:32), [Profile.lean:28](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Profile.lean:28)

8. **Split into 1b and 1c.** Deferral is sound for a milestone limited to hooks, instances, and proposition proofs. Exclusion can be checked against transitions without first defining `RelayFeasible`. Survey finding 5 matches the code: the general eligibility definitions and extension theorem are absent; `runPrefix` restricts an existing run. Finding 6 should state a missing proof construction, not nonexistence. Its positive-budget restriction is correct; the selected constants then require `η > 0`. For 1c, specify admissible prefixes and outstanding delivery obligations, and account for every regime field. In particular, the four delivery obligations alone do not establish preservation of `RootInjective`. Do not present 1b instances as eligible candidates. [RunPrefix.lean:11](/Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/RunPrefix.lean:11), [Standard.lean:220](/Users/francesco/ethereum/lean/available-chain/AvailableChainFramework/Catalog/Standard.lean:220), [Conditions.lean:28](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:28)

9. **Lock and layering.** Source inspection supports ADDED lines only for Task 4 and no other required lock change. Kit and the sketch are excluded from locked roots; concrete protocol bodies are not in the current catalog closure. This is a dependency assessment, not a lock check of an implementation that does not yet exist. The protocol libraries currently do not import Framework. However, neither the cited `AGENTS.md`, the design’s directional rule, nor the Lake configuration imposes the claimed reverse-import prohibition. Protocol-local facts with Registry assembly remain a reasonable chosen boundary; document it accurately. [CatalogLock.lean:52](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean:52), [CatalogLock.lean:121](/Users/francesco/ethereum/lean/available-chain/scripts/CatalogLock.lean:121), [FRAMEWORK-DESIGN.md:91](/Users/francesco/ethereum/lean/available-chain/docs/FRAMEWORK-DESIGN.md:91)

REVISE

AUDIT COMPLETE: 1 blocking, 4 major, 4 minor