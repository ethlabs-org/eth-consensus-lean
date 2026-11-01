Both blocking findings are fixed. I audited plan commit `62f6145` against the registry through `c995306`. I changed no files.

Evidence keys: **P** = [plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md), **R** = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md), **S** = [archived spec](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-ae4497ab.tex), **L** = [session log](/Users/francesco/ethereum/lean/available-chain/log.md). Numbers after keys are line numbers.

```text
┌─────┬──────────────┬────────────────────────┬──────────────────────────────────────────────────────┐
│ ID  │ Disposition  │ Evidence               │ Reason                                               │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G01 │ FIXED        │ P:1015; P:1051; P:1074 │ All record guards and client safety statements       │
│     │              │                        │ are present.                                         │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G02 │ FIXED        │ P:1470; P:1490;        │ Three valid F-move cases replace the false equality   │
│     │              │ P:1505; P:1510         │ of D. The counterexample is retained as a test.       │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G03 │ FIXED        │ P:673; P:691;          │ Tie failure is explicit. General selector lemmas     │
│     │              │ P:865; P:929           │ require ViewRootInj.                                 │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G04 │ FIXED        │ P:752; P:792           │ Raw T and admitted TF are separate. The F admission   │
│     │              │                        │ guard is enforced.                                   │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G05 │ FIXED        │ P:820; P:841; P:849    │ StoreInv preserves basis membership and carriers.    │
│     │              │                        │ fBasis_duty supplies the required view premises.     │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G06 │ FIXED        │ P:1028; P:1138;        │ Finality-row and QC provenance use actual head       │
│     │              │ P:1152                 │ fields and an explicit emission premise.             │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G07 │ FIXED        │ P:1386; P:1402;        │ Evidence persistence and normalized frames support   │
│     │              │ P:1432; P:1445         │ non-nested views.                                    │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G08 │ PARTLY FIXED │ P:1543; P:1650         │ Coverage is recorded per clause, but the crossing-QC │
│     │              │                        │ clause still overstates its theorem. See H03.        │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G09 │ PARTLY FIXED │ P:1588; P:1725;        │ Input guards and spec pins are added. Source binding │
│     │              │ P:1748                 │ and archive resolution need H01 and H04.             │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G10 │ PARTLY FIXED │ P:58; P:1778; P:1794  │ Root imports and the full build are required.         │
│     │              │                        │ Validation scripts need H02 and H06.                 │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G11 │ FIXED        │ P:1611; P:1697;        │ The previously missing registry entries and the AP   │
│     │              │ P:1815                 │ boundary are recorded.                               │
├─────┼──────────────┼────────────────────────┼──────────────────────────────────────────────────────┤
│ G12 │ FIXED        │ P:453; P:461;          │ Entry geometry precedes its consumers. The cited     │
│     │              │ P:517; P:1235          │ helper locations are corrected.                      │
└─────┴──────────────┴────────────────────────┴──────────────────────────────────────────────────────┘
```

The new findings are:

```text
┌─────┬──────────┬───────┬──────────────────────────────────┬────────────────────────┬──────────────────────────────────┐
│ ID  │ Severity │ Task  │ Finding                          │ Evidence               │ Fix                              │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H01 │ MAJOR    │ 14    │ Pin checker accepts wrong source │ P:1748; P:1751;        │ Parse exact source rows and      │
│     │          │       │ keys and invalid registry ids.   │ P:1755                 │ literal ids. Add negative tests  │
│     │          │       │                                  │                        │ for both cases.                  │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H02 │ MAJOR    │ 14    │ Axiom checker can omit public    │ P:1778; P:1780         │ Enumerate declarations from the  │
│     │          │       │ theorems.                        │                        │ Lean environment. Test that the  │
│     │          │       │                                  │                        │ enumeration is complete.         │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H03 │ MAJOR    │ 11/14 │ A theorem about a finalized      │ P:1251; P:1256;        │ Add a theorem over an arbitrary  │
│     │          │       │ chain is labelled as a theorem   │ P:1650; R:2829         │ finality QC with E1 evidence, or  │
│     │          │       │ about an arbitrary finality QC   │                        │ mark this coverage partial.      │
│     │          │       │ and E1 evidence.                 │                        │                                  │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H04 │ MINOR    │ 14    │ Research and DC pins read live   │ P:1578; P:1590;        │ Resolve research archives by     │
│     │          │       │ files instead of the registered  │ P:1719; R:37; R:72     │ hash and DC text by its          │
│     │          │       │ versions.                        │                        │ registered commit.               │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H05 │ MINOR    │ 8     │ The same-row test requires an    │ P:1027; P:1044         │ Test height_pair directly, or    │
│     │          │       │ impossible derived source.       │                        │ use different entries at         │
│     │          │       │                                  │                        │ height 2.                        │
├─────┼──────────┼───────┼──────────────────────────────────┼────────────────────────┼──────────────────────────────────┤
│ H06 │ MINOR    │ 7/14  │ The prohibited-proof scan        │ P:63; P:824; P:1798    │ Check proof syntax or Lean       │
│     │          │       │ rejects valid identifiers and    │                        │ dependencies. Exclude ordinary   │
│     │          │       │ comments.                        │                        │ identifiers and comments.        │
└─────┴──────────┴───────┴──────────────────────────────────┴────────────────────────┴──────────────────────────────────┘
```

**H01 — The source association check can return false success.**  
The `awk` command reads the matching row and unconditionally reads the next row. I tested the exact check in memory with key `r147`, path `fj-redteam.md`, and the `r148` hash. It returned **0** because the next row contains `r148`. The actual file-hash check also passes for this wrong association. Separately, the nonexistent id `fj.frame.v.` passes the heading check because `grep` interprets the dots as regular-expression operators. Require exact associations and literal ids. Also reject partially failed extraction; a nonempty result alone does not establish completeness.

The prescribed missing-file and empty-file guards now return **2**. All ten current source hashes match, and the plan contains eleven pin ids. These successful checks do not detect the cases above.

**H02 — The axiom check does not cover every public theorem.**  
`grep '^theorem '` omits declarations such as `@[simp] theorem ...`, `lemma ...`, and indented declarations. Its result count compares only the declarations that this same scan found. I tested the extraction with three public declarations; it found only the plain `theorem`. Thus an omitted public result can depend on a prohibited project axiom while this script reports success. Enumerate the compiled theorem declarations and check their dependencies.

**H03 — The clause label is stronger than the theorem.**  
The registry starts with a finality QC that exists before or after the crossing. Such a QC can exist in a row pool before a block carries it. `crossingNoFinal` instead requires a chain `D` with `derive D.F = J` and `derive D.h_F = j`. Its conclusion is general slashable weight between two chains, not E1-specific evidence against the supplied QC. The statement is useful and appears provable, but P:1650 claims the broader clause. Add the abstract QC theorem, or explicitly record the remaining QC/E1 part as paper or open coverage.

For **H05**, every derived state at height 1 has entry genesis. `T_h` changes only when the height advances. Therefore a source block at height 1 cannot have entry root `⟨7⟩`. The proposed expected result is correct for direct `height_pair` fields, but that source cannot pass through `createRow`’s block interface.

For **H06**, the required scan matches the valid field `StoreInv.admit` itself, as well as comments containing “admitted”. It therefore cannot produce the required empty output after Task 7.

The main mathematical checks support adoption:

- **F moves:** `Fmove_below` correctly states the cut at F′ and proves that removed blocks are ancestors of F′. The top-pair argument preserves the phase without preserving every lower lex pair. `Fmove_atTop` correctly requires a carrier with **finalized height** `m−1`; this gives `h_j(K)=m−1` and `J(K)=F′`. Keep that explicit height premise. `Fmove_atFrontier` follows directly from `h_F(K)<h(K)≤H`. These statements match the corrected reading at R:3143.
- **G02 test:** an independent in-memory evaluation gives old `D = {genesis, B1, B2, B3}` and new `D = {B1, B2, B3}`. Both frames have `H=4`, `j=2`, and `lo=3`. This confirms the revised expected values. It is not a Lean proof.
- **Store:** `basis` and `bF` now supply a finalizing carrier in each duty view. `derive_F_preceq_J` then supplies the qualifying J carrier. The `admit` field, parent premise, and monotone F update support closure of `TF`. The admission guard agrees with S:694; rejected branches cannot raise `h_max`. The separate `hext` premise for domain nonemptiness remains necessary.
- **Client:** `RecordInv` matches DC’s `LockCompatible`. The finality guards match S:1184, and the own-row lock matches S:1198. The proof of `clientRun_noSlash` needs both record compatibility and coverage of prior emissions; P:1081 explicitly includes both. Safety for arbitrary head fields is sound here. Justification provenance correctly requires `HeadFields.ofBlock`.
- **Evidence bits:** `effFrame_of_bits` and `twoChanges_count` are sound with their stated premises. Non-nested views are permitted. Persistent bits make phase rank monotone in `{0,1,2}`, and the normalized frame is fixed within each phase. This bounds changes of the normalized frame, not changes of D or arbitrary unsettled duty frames.
- **`2 ≤ m`:** this is sufficient for the stated arbitrary-view theorem. Without it, take `m=1` and an empty view. `EJ` is false, but fallback gives `j=0`, so `phaseOf` is uncontested rather than gap. The separate genesis-view test remains correct.
- **`ViewRootInj`:** the ancestor-inclusive definition is sufficient for the general selector and store claims. It agrees with the registry idealization on ancestor-closed duty views. It is stronger than necessary for some statements: domain nonemptiness can use the frontier witness directly, and explicit top-pair uniqueness already resolves the relevant selector tie in `effFrame_of_bits`. These extra hypotheses are safe.

The clause table now correctly separates output nesting into `comp.outputNesting.v1`, temporal provenance into the composition layer, and head selection into the AP layer. In addition to H03, apply the accepted registry updates: pin the two geometry helpers to `fj.frameFeasible.v1` parts (3) and (4), and update the carrier-above clause. Correct the source labels at P:1605 and P:1607: r148’s root/filter functions are at lines **171–175**, and its head function is at **177–185**.

The six open questions **do not block implementation**. L:228 and commit `c995306` supply the decisions:

1. Keep `m ≥ 2`; retain separate genesis-boundary tests.
2. Keep the explicit `ViewRootInj` hypotheses.
3. Keep the stated `fjFrame_D_nonempty` interface; its extra injectivity premise is safe.
4. Add `finalityPair_carrier_above` from head provenance and `justified_below_height`. Carrier retention stays in composition.
5. Pin `fjFrame_Z_mem_D` and `fjFrame_viable_child` to the new frame-feasibility clauses.
6. Record the agreed `frameCompat` split: step 1 and part (ii) in Lean; part (i) and step 4 on paper.

**Verdict: ADOPT WITH FIXES.** The revised mathematical statements address both blocking errors and the missing invariants. The remaining fixes concern validation, coverage, source resolution, and tests. Apply them before the affected task checkpoints. No further design decision is needed.

AUDIT COMPLETE: 0 blocking, 3 major, 3 minor