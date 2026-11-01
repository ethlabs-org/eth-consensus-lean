VERDICT: REVISE

The derived-root design is sound. The plan is not ready to implement: the codec exceeds its size limit, FG-SA packing lacks a required reconstruction check, and the statement restrictions conflict with necessary changes.

I audited `24ecaaa`. Checks included source inspection, Python arithmetic checks, and a read-only Lean scan of the compiled lock dependencies. The current lock check passed. No files changed.

Below, `Plan` means [the I9 plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-i9-derived-roots.md). Library prefixes such as `FGSA/` mean `AvailableChainFGSA/`.

```text
┌─────┬──────────┬────────────────────────────────────────────┬────────────────────────────────────────────────┐
│ Id  │ Severity │ Evidence file:line                         │ Fix                                            │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A01 │ BLOCKING │ Plan:44,89,91                              │ Replace the codec or its composition. Require   │
│     │          │ claude-files/i9/pairsize.py:13              │ both size checks and kernel evaluation.        │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A02 │ BLOCKING │ Plan:188,189                               │ Check full body reconstruction. Preserve the   │
│     │          │ FGSA/Proofs/Admission.lean:49               │ packed FG body, including signed rows.         │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A03 │ BLOCKING │ Plan:57,174                                │ Allow named statement changes for content and │
│     │          │ SAPC/Tests/Axioms.lean:440                  │ parent premises, and for codec parameters.     │
│     │          │ FGSA/Tests/Axioms.lean:138                  │                                                │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A04 │ MAJOR    │ Plan:107                                   │ Replace the three-case claim with a lookup     │
│     │          │ Statements/Generic/Conditions.lean:58,118   │ lemma. Prove no-op and relay facts separately. │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A05 │ MAJOR    │ Plan:106                                   │ Use the image of Block.root, with genesis      │
│     │          │                                            │ included. Limit the claimed wire equivalence. │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A06 │ MAJOR    │ Plan:172,182                               │ Add CausalCap and the omitted FG-SA callers    │
│     │          │ KitFG/CausalCap.lean:25                     │ to the task audit and repair lists.            │
│     │          │ FGSA/Model/Store.lean:44                    │                                                │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A07 │ MAJOR    │ FGSA/Tests/Smoke.lean:144,413,534            │ Rebuild fixtures from each signed row list.    │
│     │          │ SimplexFG/Frame.lean:178                    │ Split yB; preserve each refusal's cause.        │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A08 │ MAJOR    │ Plan:75,206                                │ Correct the prediction to 91 CHANGE / 159     │
│     │          │ Framework/Catalog/Strong.lean:85            │ KEEP. Check source changes as well as names.   │
│     │          │ scripts/CatalogLock.lean:132                │                                                │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A09 │ MINOR    │ AGENTS.md:7                                │ Put rootInjective_all in the Kit. The project │
│     │          │ Plan:98,108                                │ instructions keep proofs out of Statements.   │
├─────┼──────────┼────────────────────────────────────────────┼────────────────────────────────────────────────┤
│ A10 │ MINOR    │ Plan:67,68,71,122                          │ Correct task references, evidence paths, and   │
│     │          │                                            │ the distinction between statements and proofs.│
└─────┴──────────┴────────────────────────────────────────────┴────────────────────────────────────────────────┘
```

**1. Faithfulness to the user’s decision**

The store-only variant implements the decision **at the resolved-block boundary**:

- A node has no supplied own-root field.
- Its root is a function of its parent’s root, slot, and body.
- Universal injectivity makes exact parent membership equivalent to lookup by parent root.
- No parent-root equality check is added to wire validity.
- The existing `excludes` definitions can stay.

It does not implement a literal root-only wire. The payload still contains the complete structural parent. Thus every carried parent reference already denotes some finite `Block`, even if that block never enters a store. An arbitrary fabricated root that denotes no block cannot be expressed as that parent.

Task 1 Step 3 overstates the correspondence in two places:

1. The range of `nodeRoot` is not the image of `Block.root`. With the proposed codec, root `2` denotes no block, but `nodeRoot ⟨2⟩ 0 0 = ⟨5⟩`. Thus `5` is in the range of `nodeRoot` without denoting a block. Conversely, genesis root `0` resolves but is outside that range.
2. A future wire adapter needs more than a decoder and membership equivalence. It must preserve authentication, dependencies, handler calls, rejection, and proposal origin. r203 already states these obligations at `derived-root.md:106`.

Describe the present result as a resolved-block model with equivalent store lookup. Leave wire refinement open.

**2. Codec: injectivity, size, evaluation, and alternatives**

The proposed `lpair` is injective. Let `k = bitLen b`. Its arithmetic form is:

```text
lpair a b + 1 = 2^k · (2 · (a · 2^k + b) + 1).
```

The factor in parentheses is odd. Therefore the number of trailing zero bits of `lpair a b + 1` determines `k`. Equivalently, count the trailing one bits of `lpair a b`. Then recover `a · 2^k + b`, and use division and remainder by `2^k`. Since `b < 2^k`, both components are unique. This includes `b = 0`.

The bound in Task 0 is correct:

```text
bitLen (lpair a b) ≤ bitLen a + 2 · bitLen b + 1.
```

Except at `(0,0)`, equality holds. The earlier `+2` bound is a valid weaker bound.

**The problem is composition.** Each occurrence in the second argument doubles that argument’s bit length. The right-nested row and list encoders repeat this multiplication. A linear bound for one pair does not establish small roots for the complete chain.

My checks gave:

```text
┌─────────────────────────────────────────────────────┬────────┬────────────┬────────────────┐
│ Encoding with the proposed lpair                    │ B1 bits│ B2 bits    │ B3 bits        │
├─────────────────────────────────────────────────────┼────────┼────────────┼────────────────┤
│ Generic G02 FG shape; body 0; r203 row encoders       │  1,973 │  1,773,100 │  1,592,244,963 │
│ pairsize.py signed-row sketch; replace pair by lpair │  7,533 │ 20,267,804 │ 54,500,136,523 │
└─────────────────────────────────────────────────────┴────────┴────────────┴────────────────┘
```

The first row includes B3’s timeout and finality fields. Both constructions fail Task 0’s `10^6`-bit limit. Large results were checked with bit-length arithmetic; I did not allocate B3’s full integer.

The kernel acceleration claim is also incorrect. In v4.30.0-rc2, the kernel has special reduction for `Nat.succ`, addition, subtraction, multiplication, division, remainder, power, gcd, Boolean equality/order, bitwise AND/OR/XOR, and both shifts. The power fast path has an exponent limit of `2^24`. **`Nat.log2` has no such kernel reduction.** Its runtime external implementation helps `#eval`; kernel reduction uses its Lean definition. [Lean kernel source](https://raw.githubusercontent.com/leanprover/lean4/v4.30.0-rc2/src/kernel/type_checker.cpp), [installed `Nat.log2` definition](/Users/francesco/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Data/Nat/Log2.lean:41).

For a simpler proof, use the arithmetic factorization above instead of bitwise OR reasoning. To fix growth, encode the **length** with the delimiter:

```text
k := bitLen b
q := a · 2^k + b
epair a b := lpair q k
```

This gives:

```text
bitLen (epair a b) ≤ bitLen a + bitLen b
                     + 2 · bitLen (bitLen b) + 1.
```

Injectivity follows by recovering `(q,k)`, then division and remainder. With this alternative, the same signed-row sketch gives **337, 3,045, and 22,181 bits**. This is a candidate, not a checked Lean implementation. Task 0 must prove its laws and test actual kernel comparisons.

The survey’s `Nat.pair` estimate has the right scale **for its signed-row sketch**. Running `pairsize.py` gives B1 = 10,054 bits and a measured nesting factor near 32,768. Bounds put the corresponding B3 near `1.079·10^13` bits. However:

- The script does not compute B2 or B3.
- It is a sketch of signed-content packing, not the exact generic G02 encoder.
- With body 0 and the generic row encoding alone, the G02 B3 size is about `2.108·10^10` bits.

Both are impractical. Correct the attribution, and require `#eval` **and** kernel checks, not either one.

**3. Universal injectivity**

The induction is sound. Induct on the first block and generalize the second block:

- Genesis versus node is impossible because node roots are positive.
- For two nodes, cancel `+1`, apply pairing injectivity twice, and obtain equal parent roots, slots, and bodies.
- Apply the induction hypothesis to the parents.

No slot-order premise is needed. Slot-0 nodes remain distinct from genesis. This is necessary for `Counter`, `NoInput`, and `Accumulation`.

The FG proof has the same structure, with an additional application of `encFGBody` injectivity. It must use one fixed `RowCodec V`. Arbitrary `V : Type` does not supply an injective encoding into `Nat`.

I found no protocol requirement for a root independent of content. The uses that require free roots are collision fixtures or exact numeric-root formulas. Forks and competing blocks can use different bodies.

**4. The three-case lemma and delivery obligations**

The lemma is not true as an operational equivalence as written. If the parent is absent and `q` is false, “reject now” and “wait” are different outcomes. The model also has no pending-proposal queue that turns an ignored delivery into later processing.

The useful, statable lemma is:

```text
(b.parent ∈ blocks ∧ q b.parent)
  ↔ ∃ p ∈ blocks, p.root = b.parent.root ∧ q p.
```

This follows from injectivity. It needs no growing-store premise. It covers the parent-slot reads after keeping the child-shape and authentication checks separate.

The four sites need these distinctions:

```text
┌────────────┬───────────────────────────────────────────────────────────────────┐
│ Protocol   │ Missing-dependency handler behavior                               │
├────────────┼───────────────────────────────────────────────────────────────────┤
│ Grid CO/SA │ Missing parent makes admitProposal return st before carried votes.│
│ SA-PC      │ proposalEnters is false for a missing parent. A direct PC with    │
│            │ missing paths also returns st through pcEnvelopeReady.            │
│ L*         │ Missing parent returns st. Its handler does not repeat the        │
│            │ wellFormed parent-slot test; do not claim unrestricted equivalence.│
│ FG-SA      │ parentFG = none returns st before any write. There is no           │
│            │ ProtocolSpec.depsPresent yet. Relating base membership to parentFG │
│            │ needs the store correspondence, or its replacement proof.         │
└────────────┴───────────────────────────────────────────────────────────────────┘
```

Evidence: `GridCO/Model/Protocol.lean:319`, `SAPC/Model/Handlers.lean:38,54`, `LStar/Model/Protocol.lean:283`, and `FGSA/Model/Handlers.lean:62`.

**“Outside `ExecutionValid`” is not equivalent to “delivered but waits forever.”** `DeliveryWellFormed.deps` forbids a direct delivery with missing dependencies. `PartialSynchrony` and `HealthyPrefixDelivery` do not have a dependency guard on their broadcast or relay obligations. Their conclusions require `handlesAt`.

If one honest reader accepts an object, another reader can acquire a relay obligation while still lacking its parent. A hypothetical no-op delivery does not discharge that obligation in a valid run. If the parent never arrives, the combined premises can become unsatisfiable.

A fabricated object never emitted or accepted by an honest reader may have no relay trigger. That is a separate fact, not a consequence of missing dependencies. Keep the plan 1c feasibility work open and remove “no delivery obligation either way.”

**5. FG-SA packing, erasure, invariants, and `excludes`**

`packBody` can support the required proofs, but `rowsOk` is insufficiently specified.

The base body has two levels:

```text
x        = lpair app (encList encRowWire rw)
baseBody = encFGBody finCodec x (rw.filterMap RowWire.toRow?)
```

The FG node must store **`x`**, not just `app`.

Checking only the signed-row component does not establish erasure. For example, the body could contain the correct signed-row code but a different outer decoded-row list. Also, the proposed `lpair` is not surjective: its decoder’s left-inverse laws do not give reconstruction for arbitrary natural numbers.

Use a full reconstruction check, such as:

```text
rowsOk b rw :=
  decide (b.body = packBody (decodeApp b.body) rw)
```

Prove `decodeApp (packBody app rw) = app`. Build the FG node with the complete inner packed value and `rw.filterMap toRow?`. Then prove erasure under:

- `b ≠ genesis`;
- `eraseFG P = b.parent`;
- `rowsOk b rw = true`.

The global erasure law follows by structural induction when both root functions use the same outer codec.

Strengthened `MetaInv.wireTree` must record this complete content equality. Admission establishes it; other transitions preserve it because they retain the stored proposals. For two such stores, equal base roots imply equal blocks, hence equal bodies. Packing injectivity then gives equal ordered signed rows, including rounds. This proves `ContentAgree`; raw and support lists remain outside its conclusion.

A failed `rowsOk` check is permanent for that wire, but it need not add an `excludes` clause in T7. With `rowsOk` in `wellFormed`, such a wire cannot be directly delivered in an `ExecutionValid` run. Honest proposals and accepted proposals must be proved to satisfy it. Any future completeness rule for `excludes` must state its well-formed-input scope; otherwise it already conflicts with existing syntax refusals.

**6. Task order and build states**

All **14 Lake libraries** are present in the plan. The order is consistent with the imports, with one qualification: Registry and Witnesses are one task, but Witnesses must be repaired before the joint checkpoint. `AvailableChainRegistry/Sanity.lean:3` imports `AvailableChainWitnesses.Sanity`.

The dependency order is:

```text
Model → Statements → Kit / EngineV2 / Framework
                    → GridCO → SA → SAPC
                    → L*
                    → Witnesses → Registry
Model → SimplexFG → KitFG
GridCO / SA / SimplexFG / KitFG → FGSA
```

The order does not omit a library. It omits affected files, especially `KitFG/CausalCap.lean`.

Keep FG-SA signed-packing fixtures local to FG-SA, or provide a lower-layer generic fixture interface. Do not make SimplexFG import FG-SA to reuse `RowWire` packing.

The staged build rule is workable. It explicitly replaces the full-default-target checkpoint rule recorded in `PHASE1B-REPORT.md:120`; retain that explicit exception.

**7. Lock impact and stop rule**

The predicted set is wrong.

I ran the existing lock dependency algorithm against the compiled environment, through standard input. The baseline `CatalogLock --check` returned 0. Of 250 locked declarations, **91 reach `AvailableChain.Block`**. The other ten entries marked `CHANGE` are scalar theorems.

All names below have prefix `AvailableChain.Framework.Catalog.`:

```text
┌───────────────────┬───────────────────────────────────────┐
│ catalog.lock line │ Name that must move from CHANGE to KEEP│
├───────────────────┼───────────────────────────────────────┤
│ 43                │ includedStableFast_le_trans            │
│ 46                │ includedStable_le_trans                │
│ 54                │ persistOutageFast_le_trans              │
│ 58                │ persistOutage_le_trans                  │
│ 69                │ recovered_le_trans                     │
│ 90                │ strongIncluded_le_trans                │
│ 94                │ strongPersist_le_trans                 │
│ 98                │ strongRecoveredIncluded_le_trans       │
│ 102               │ strongRecoveredSafe_le_trans           │
│ 105               │ strongSafe_le_trans                    │
└───────────────────┴───────────────────────────────────────┘
```

Their statements depend on scalar constants and order relations. Their theorem proofs are excluded from lock hashes. Thus the corrected prediction is **91 CHANGED, 159 unchanged**, subject to checking the completed implementation.

No Framework declaration needs a text change for the store-only variant with regime fields retained. The two copies of `rootInjective` in `Catalog/Mono.lean` remain valid.

Task 11’s stop rule is insufficient. It permits unrelated changes inside an expected name and does not require every predicted change to occur. Require:

- The exact corrected changed-name set.
- No removed or added locked declaration.
- No unexplained Framework source or declaration-type change.
- Review of changed definitions in the dependency closures.
- Successful checker completion before interpreting its output.

Check additions by module ownership. The library is `AvailableChainFramework`; declaration names use `AvailableChain.Framework`.

**8. Statement changes and protected statements**

These changes exceed a mechanical replacement of an old root field or numeric value:

- `FGSA.eraseFG_fgBlock`, `Proofs/Admission.lean:49`: add content consistency.
- `FGSA.fgBlock_root`, `:64`: add parent and content consistency, and handle genesis. The present unconditional statement is false after the change.
- `FGSA.fgBlock_notMem`, `:70`: add the facts that connect the constructed FG root to `b.root`, or change its freshness premise.

For the last theorem, an arbitrary store can contain `fgBlock P b rows` while its root differs from `b.root`. The old freshness premise then holds but the conclusion fails.

Explicit codec propagation also changes generic theorem signatures. This includes `RootInjectiveOn.symm`, `uniqueJust_chains`, `finalLock`, `accountable`, `causalCap`, `causalCap_notRoot`, and the generic theorems whose statements use `derive`, frame selection, client construction, or store updates. Task 8 cannot both thread an explicit codec and preserve all public signatures.

All twelve generic Carrier theorems need the codec in their effective signatures: `eraseFG_slot`, `eraseFG_root`, `eraseFG_parent`, `eraseFG_eq_genesis`, `eraseFG_preceq`, `eraseFG_compatible`, `eraseFG_injOn`, `preceq_of_eraseFG_preceq`, `compatible_iff_eraseFG`, `viewRootInj_of_rootInj`, `rootInjectiveOn_of_viewRootInj`, and `erase_rootInjective`.

The protected-statement rule has direct conflicts:

- `SAPC.honest_proposal_views` must replace its old constructor formula, but `SAPC/Tests/Axioms.lean:440` prints it.
- The three FG-SA admission theorems above are printed at `FGSA/Tests/Axioms.lean:138,141,143`.
- The generic Carrier theorems are also printed there.

Do not remove audit entries to evade the rule. Add a precise exception list with old and new statements.

The five named contract theorems can keep their statement text. The existing sufficiency theorems can obtain `rowsOk` from their `wellFormed` premise. Cross-node theorems can retain redundant `ContentAgree` premises.

Also correct the survey and plan: the constructor expressions inside `GridCO.honest_proposal_exists` and `SAPC.honest_proposal_exists` are **proof terms**, not parts of their theorem statements.

**9. Fixtures**

The following covers every group in the survey’s §4 table.

```text
┌───────────────────────────────────────────┬──────────────────────────────────────────────────────┐
│ Fixture group                             │ Audit result                                         │
├───────────────────────────────────────────┼──────────────────────────────────────────────────────┤
│ Registry/Counter and CounterRun           │ Sufficient: retain the slot-0 first node; replace     │
│                                           │ numeric root proofs with structural/index proofs.   │
│ Registry/Gaps/NoInput                      │ Sufficient. Preserve the clock-only KNOWN-GAP result.│
│ Witnesses/Sanity                          │ Sufficient. Use body data and universal injectivity.│
│ Witnesses/Regimes                         │ Sufficient. Recode every repeated block literal.    │
│ Witnesses/Accumulation                    │ Sufficient. Keep the slot-0 parent and distinct      │
│                                           │ bodies for its two slot-1 children.                  │
│ EngineV2/Sketch                           │ Sufficient. Update both folds consistently.         │
│ GridCO/Tests/Smoke                         │ Sufficient. Preserve the sibling fork and badChild's│
│                                           │ equal parent/child slots.                            │
│ SA/Tests/Smoke                            │ Sufficient. B and X must remain distinct siblings.  │
│ SAPC/Tests/Smoke                          │ Add an explicit body-0 choice for x: completeRound-  │
│                                           │ Check compares x with the honest proposal at :179.  │
│ SAPC/CleanInvariantCounterexample         │ Sufficient if x.root > y.root is checked again and  │
│                                           │ the complete valid-run counterexample still holds. │
│ LStar/Tests/Smoke                         │ Sufficient. Its blocks come from propose.           │
│ FGSA/Tests/RootCollision                  │ The negative content-agreement and honest-collision │
│                                           │ refusal results become impossible. The proposed     │
│                                           │ positive replacements are appropriate.              │
│ FGSA/Smoke:24 and wProp/stA                │ Incomplete. Generic FG blocks need signed packing   │
│                                           │ consistent with each carried round and row list.    │
│ FGSA/Smoke literal proposal blocks        │ Pack each actual row list. Split yB between :415    │
│                                           │ and :534, which carry different lists.              │
│ FGSA/Smoke refusal fixtures               │ Make rowsOk true when testing another refusal.     │
│                                           │ Otherwise a test can pass for the wrong reason.     │
│ FGSA/Smoke:208                            │ Same-root distinct-block refusal is impossible.    │
│                                           │ Replace it with the declared duplicate test.        │
│ FGSA/Smoke:374                            │ Preserve a depth tie and prove the intended root   │
│                                           │ order before checking deepest.                      │
│ FGSA/Smoke:432–447,590–607                 │ Rebuild the expected packed proposal and root       │
│                                           │ references. Preserve the selected head and record. │
│ FGSA/Smoke:500–501,571–573                 │ Preserve the alternative winners that detect wrong │
│                                           │ controls, witnesses, or filtering. Check their order.│
│ SimplexFG/ChainState:176–191              │ Sufficient. Quorum and timeout intent survives.     │
│ SimplexFG/Frame:144–172                   │ Sufficient with a checked root order for B1a/B1b.   │
│ SimplexFG/Frame:176–200                   │ Collision-driven fallback is impossible. No fixture │
│                                           │ can preserve that cause under universal injectivity.│
│ SimplexFG/Frame:185–212                   │ Other intent survives: distinct B1c; childC         │
│                                           │ justification; Y contest; X viability change.        │
│ SimplexFG/Store:163–212                   │ Sufficient after retargeting rows to derived roots. │
│                                           │ Preserve finality and each separate refusal cause. │
│ SimplexFG/Client:176–199,238–250          │ Replace roots that name B1 or clientB1alt. Preserve │
│                                           │ the different-entry and lock/timeout guards.        │
│ KitFG/TwoChanges:757–767                  │ Sufficient. Keep K3's finality-only rows and the     │
│                                           │ Fmove_atTop witness; use universal ViewRootInj.      │
└───────────────────────────────────────────┴──────────────────────────────────────────────────────┘
```

Besides the two cited cases, the **negative cross-store results in `FGSA/Tests/RootCollision.lean`** cannot retain their old intent. Task 9 already proposes their replacement.

The shared `yB` identity with two different accepted signed-row lists also cannot survive. Its two row-selection tests can retain their intent by using separate blocks.

I found no further protocol counterexample whose essential intent must be lost. Task 7 must remove the instruction to preserve the collision-driven frame fallback with another possible fixture. An empty-candidate fallback is a different test.

**10. Missing sites**

Add these required or directly affected sites to the task lists:

- `AvailableChainKitFG/CausalCap.lean`: both theorems use `derive` and need the codec.
- `AvailableChainFGSA/Model/Store.lean`: `activeCompatible`, `normalizeS`, and their callers use erasure.
- `AvailableChainFGSA/Proofs/Fields.lean`, `Proofs/Reconcile.lean`, and `Proofs/Nesting.lean`: erasure statements and proofs need review and codec propagation.
- `AvailableChainSAPC/Model/Handlers.lean`: Task 4 requires an instantiation here but omits the file from its list.

Explicitly retain these omitted audit sites, even if no text change is needed:

- `AvailableChainFGSA/Model/Clock.lean` and `Statements/Store.lean`.
- `AvailableChainSAPC/Model/Objects.lean` and `Statements/QuorumRecovery.lean`.
- `AvailableChainStatements/Generic/Regimes.lean` and `Strong/Regimes.lean`.
- `AvailableChainKit/Engine/Execution.lean`; the survey correctly identifies its `Event.node` match as a false positive.
- The library root files and import coverage.

The actions mention, but their file lists omit, `docs/REGISTRY.md`, `docs/MATRIX.md`, `docs/catalog.lock`, and the new `docs/I9-REPORT.md`.

Finally, correct the task references: parent-slot instantiations belong to **Tasks 3, 4, 5, and 9**. `eraseFG_root` is repaired in Task 9, not Task 8. The r203 scratch evidence is under the research directory; `codex/scratch/r203/` does not exist relative to this repository.

AUDIT COMPLETE: 3 blocking, 5 major, 2 minor