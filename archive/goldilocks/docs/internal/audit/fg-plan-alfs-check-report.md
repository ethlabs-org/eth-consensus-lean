**Verdict: ADOPT WITH FIXES.** The changed FG definitions and theorem statements are sound under their stated premises. Two fixes remain in the interface for later SA work.

I checked the requested diff from `62f6145` to `HEAD` (`49b89cf`). I changed no files. This was a plan audit, not a compiled Lean proof check.

Evidence keys: **P** = [plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md), **R** = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md), **A** = [archived ALFS spec](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-183f2c40.tex), **L** = [ALFS proof text](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/fgsa-live-dc-port.md). Numbers are file lines.

```text
┌─────┬──────────┬─────────┬─────────────────────────────────┬──────────────────────┬─────────────────────────────────┐
│ ID  │ Severity │ Task    │ Finding                         │ Evidence             │ Fix                             │
├─────┼──────────┼─────────┼─────────────────────────────────┼──────────────────────┼─────────────────────────────────┤
│ K01 │ MAJOR    │ 14; SA  │ The ALFS handoff still requires  │ P:2046; P:2047;      │ Use ap.headReachesLo.v2 for      │
│     │          │         │ the unconditional v1 head       │ P:2048; P:2056;      │ ALFS. State its anchor-entry    │
│     │          │         │ guarantee. L5/L6 are also        │ P:2058; R:1942;      │ conditions and fallback cases.  │
│     │          │         │ described as nonemptiness       │ R:1953; L:354        │ Keep v1 references only for     │
│     │          │         │ guarantees without conditions.  │                      │ the view form.                  │
├─────┼──────────┼─────────┼─────────────────────────────────┼──────────────────────┼─────────────────────────────────┤
│ K02 │ MINOR    │ 7; SA   │ The weak root-membership lemma  │ P:1037; P:1056;      │ Add a filteredFrom helper:      │
│     │          │         │ was removed. Its replacement    │ P:1127; R:1969       │ ancestor closure, F ⪯ Z and     │
│     │          │         │ needs a finalizing carrier in   │                      │ D ≠ ∅ imply Z ∈ D. Keep the     │
│     │          │         │ the set and cannot directly     │                      │ current stronger results as     │
│     │          │         │ serve the frozen-tree proof.    │                      │ special cases.                  │
└─────┴──────────┴─────────┴─────────────────────────────────┴──────────────────────┴─────────────────────────────────┘
```

**K01 argument.** Let a late contest set the live controls to `lo = H`, while every block in the frozen set has height below `H`. No block has a qualifying witness, so `filteredFrom` is empty. The HEAD returns its anchor and cannot belong to that empty domain. This is explicitly allowed by L:354–356. Thus the unconditional v1 obligation at P:2056 is false for ALFS.

The registered v2 contract already handles this case. It also handles a live anchor outside a **nonempty** frozen domain when that anchor has no eligible child there (R:1942–1957). Replace “coming” and the unconditional L5/L6 descriptions with this contract. This affects the SA and Kit.Compose handoff; it does not require a change to the FG definitions.

For **K02**, the old `fjFrame_Z_mem_D` at baseline line 906 required only closure, `F ⪯ Z`, and nonemptiness. The new statement is true, but has stronger premises. Restore that weak geometry result for arbitrary controls and block sets. Its proof follows directly from `mem_filteredFrom`: take a member and its witness, use closure to obtain `Z ∈ blocks`, then reuse the witness. This is the argument needed at R:1969.

The other checks passed:

- **Definitions and source correspondence.** `Controls`, `storeControls`, the root and floor rules, `filteredFrom`, and `storeFrame` match A:910–965. `acceptViable` correctly retains `hmax−1`, including during a contest. `update_finality` matches A:809–822, including update order and all F-acceptance guards. `on_block` matches the FG part of A:747–779; its omitted slot, signature, round and pool operations are explicitly assigned to AP. `Store.init` matches A:429–437. `fjControls` correctly remains the archived **view form**, with a separate `fj.frame.v1` pin.

- **Central equality and invariant.** `storeControls_eq_fjControls` follows from `StoreInv.hmax` and `StoreInv.pair`; the contest expressions then coincide. It needs no separate injectivity premise once those invariant equalities are supplied. Preservation needs the stated `ViewRootInj`. When F advances, the cached maximum remains eligible because `F′ ⪯ J`; every remaining candidate was already eligible under F. The accepting block supplies `Fcar`. The duplicate and parent guards support `closedF`. I found no counterexample to initialization or preservation.

- **Frame forms.** `Fmove_filtered` is true for any block set under its stated `hband`, `hroot`, and `hext` premises. Its equality cuts the domain at F′; its witnesses come from that same set. `filteredFrom_viable_child` correctly requires ancestor closure. `fjFrame_D_nonempty` obtains a frontier witness using the carrier and `hext`. `storeFrame_feasible` correctly transfers this result to the full admitted tree through `Fcar` and closure. It does not establish frozen-tree feasibility. The controls-only phase results and the `fjFrame` F-move special cases retain their valid premises.

- **Prior findings and pins.** The restructure does not reopen the FG defects in G01–G07, G09–G10, G12, or H01–H06. K01 concerns the G08/G11 coverage and AP-interface boundary. The deleted F-basis machinery is correctly replaced for full-store use; K02 is the remaining reusable-helper loss. All 12 source hashes, registry path/hash associations, and 12 pin IDs match. The `fj.frame.v2` line ranges are correct. Its walk, anchor, frozen-set and HEAD-call clauses are correctly marked as AP data.

AUDIT COMPLETE: 0 blocking, 1 major, 1 minor