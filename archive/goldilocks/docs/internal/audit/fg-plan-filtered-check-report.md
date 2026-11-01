The FG definitions and invariant arguments survive this edit. I found one major and three minor issues. I changed no files. This is a plan audit, not a compiled Lean proof check.

Evidence keys: **P** = [proposed plan](/private/tmp/claude-501/-Users-francesco-ethereum/81138be2-3084-412a-91f7-34a802c39546/scratchpad/sdd-fg/fg-module-filtered.md), **R** = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md), **S** = [alfs4](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-bd942ca0.tex). Numbers are file lines.

```text
┌─────┬──────────┬──────────┬─────────────────────────────────┬─────────────────────┬─────────────────────────────────┐
│ ID  │ Severity │ Task     │ Finding                         │ Evidence            │ Proposed fix                    │
├─────┼──────────┼──────────┼─────────────────────────────────┼─────────────────────┼─────────────────────────────────┤
│ P01 │ MAJOR    │ 14       │ Valid Lean formatting can hide  │ P:2044; P:2046;     │ Read the elaborated pin list,   │
│     │          │          │ a superseded pin from both ID   │ P:2049; P:2072      │ or use an independent complete  │
│     │          │          │ extraction and its count check. │                     │ parser. Test compact syntax.   │
├─────┼──────────┼──────────┼─────────────────────────────────┼─────────────────────┼─────────────────────────────────┤
│ P02 │ MINOR    │ 12, 14   │ The “actual head reaches H”     │ P:1949; R:2850;     │ State the anchor condition for │
│     │          │          │ coverage label omits the v5     │ R:2852; P:1172      │ frozen HEAD, or name the full  │
│     │          │          │ condition and the head domain.  │                     │ tree and prove that condition. │
├─────┼──────────┼──────────┼─────────────────────────────────┼─────────────────────┼─────────────────────────────────┤
│ P03 │ MINOR    │ 7        │ The new active-view example is  │ P:1147; P:981;      │ Use a reachable F advance with │
│     │          │          │ not a reachable post-advance    │ P:983; P:1754       │ a finalizing carrier, or call  │
│     │          │          │ store. It fails pair and Fcar.  │                     │ this only an arbitrary literal.│
├─────┼──────────┼──────────┼─────────────────────────────────┼─────────────────────┼─────────────────────────────────┤
│ P04 │ MINOR    │ Overview │ The architecture still specifies│ P:8; P:903          │ Replace the two-tree text with │
│     │          │          │ raw and FG-admitted trees.      │                     │ one cumulative admitted tree. │
└─────┴──────────┴──────────┴─────────────────────────────────┴─────────────────────┴─────────────────────────────────┘
```

**P01 counterexample.** Replace the first pin’s `id := "fj.frame.v3"` with valid Lean syntax `id:="fj.frame.v2"`. The extraction finds 11 IDs. The “declared” count also becomes 11 because it uses the same formatting assumption. All remaining IDs pass. The superseded pin escapes the check. I reproduced this with the proposed extraction commands and Index parser, using memory-only inputs.

The Index check itself works: it reads the correct status column and rejects normally formatted `fj.frame.v2`. However, `.ap` and `.external` references are outside its scope. Replacing an active `.ap "ap.headReachesLo.v5 …"` reference with v4 leaves all 12 checked IDs unchanged. A dependency-status check should distinguish active references from historical entries in `notFormalized`.

For **P02**, v5 clause 1 guarantees the height only when the anchor belongs to the filtered domain or has an eligible child there. Clause 2 permits the anchor fallback. A late contest can give `lo = H` and an empty frozen domain; with no leases, the returned anchor can be `F` below `H`. The plan already states this at P:1172. The full-tree action head is a different application: name that domain and establish the anchor premise. This is a coverage-label problem; it does not refute `inBandLock`.

For **P03**, genesis, `B1`, and `B1'` all have derived finality equal to genesis. None supplies `Fcar` for `F = B1`. Their justified entries also do not supply the cached pair `(1, B1)`. The literal tests `activeView`, but cannot represent the claimed reachable state. A suitable transition test admits `B1'` before the `B2`/`B3` sequence at P:1754–1756 finalizes `B1`.

The Task 7 comparison gives these differences from the full spec:

- **`Store` and initialization:** `TF` names the spec’s `Σ.T`. All five retained fields and their initial values match S:474–482. The projection omits time, slot, stamps, the state map, pools, and SA fields. Parent closure is an invariant, not a restriction on arbitrary `Store` values.
- **`on_block` guards:** duplicate, missing-parent, and `F ⋠ B` refusals match S:794–796. The function omits the input validation, future-slot check, parent-slot check, signature check, and row-round check. The plan assigns these to the caller/AP boundary and explicitly documents the row-round precondition.
- **Accepted-block processing:** `derive B` replaces the cached parent-state transition. The plan constructs the enlarged tree before evaluating `update_finality`; the spec computes the state before insertion. This has no FG effect because `derive` does not read the store. Timestamp writes, carried-vote handlers before finality, and carried-row handlers after finality are omitted.
- **`update_finality`:** the height update, lexicographic J update, strict F advance, and acceptance-viability test match S:847–860, including their order. The function accepts a block instead of a state. Omitting reconciliation is valid for this projection: S:862–882 writes only SA fields.
- **`activeView`:** the compatibility filter exactly matches S:358, including stored ancestors of F. It does not delete blocks.

Every remaining `StoreInv` field has a preservation argument. The refused branch returns the same store. In the accepted branch, insertion preserves `closed` and `gen`; the acceptance test preserves `Fmem`; and the matching maximum update preserves `hmax`. The J guards and F-advance guard preserve `FJ`.

For `pair`, the selected maximum remains eligible after an F advance because `F′ ⪯ J`. Every candidate under F′ was already a candidate under F. A conflicting stored block cannot supply a J above F′ because its J is its ancestor. For `Fcar`, the accepting block supplies the new witness; otherwise the old witness remains. Thus cumulative storage preserves both fields.

`storeControls_eq_fjControls` follows directly from `hmax` and `pair`. It needs no additional injectivity premise once those equalities are supplied; preservation uses the stated `ViewRootInj` premise.

No removed field remains in Tasks 7, 12, 13, or 14. The former `closedF` use becomes `closed`. I found no theorem in Tasks 7, 12, or 13 made false or vacuous by this edit under its stated premises. In particular, their crossing and uniqueness hypotheses remain necessary; admission does not prove that every stored block extends current F.

The supplied diff applies exactly to commit `195d31a`. All 13 source hashes and registry source rows match. The edited `fj.frame.v3` line ranges match the registry and `alfs4`. The descriptions of `ap.headReachesLo.v5` clauses 1–3 match, apart from the coverage-label issue P02.

**Verdict: ADOPT WITH FIXES.**

AUDIT COMPLETE: 0 blocking, 1 major, 3 minor