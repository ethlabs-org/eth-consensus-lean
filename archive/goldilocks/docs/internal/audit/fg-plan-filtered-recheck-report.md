I found **3 major and 4 minor issues**. I changed no files.

Evidence keys: **P** = [final plan](/private/tmp/claude-501/-Users-francesco-ethereum/81138be2-3084-412a-91f7-34a802c39546/scratchpad/sdd-fg/fg-module-filtered.md), **R** = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md), **S** = [alfs4](/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-bd942ca0.tex), **D** = [DC paper](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex). Numbers are file lines.

```text
┌─────┬──────────┬───────┬─────────────────────────────────┬─────────────────────────┬─────────────────────────────────┐
│ ID  │ severity │ task  │ finding                         │ evidence (file:line)     │ proposed fix                    │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q01 │ MAJOR    │ 14    │ Formatted active references     │ P:2052,2061,2078         │ Store reference IDs as data;    │
│     │          │       │ escape idTokens.                │                         │ test .ap and .external.         │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q02 │ MAJOR    │ 14    │ A nonempty partial ID list      │ P:2145,2154,2158         │ Check a complete manifest;      │
│     │          │       │ passes.                         │                         │ reject truncated input.         │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q03 │ MAJOR    │ 14    │ Compact Src syntax hides a      │ P:2139–2144              │ Read sources from elaborated    │
│     │          │       │ wrong source hash.              │                         │ data; check completeness.       │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q04 │ MINOR    │ 12,14 │ “Reaches H only if” reverses     │ P:1992; R:2868–2874      │ Use “if”; the fallback can      │
│     │          │       │ the service implication.        │                         │ also have height H.             │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q05 │ MINOR    │ 7     │ Refusal decide tests lack       │ P:912–919,1172–1174      │ Derive DecidableEq for Store.   │
│     │          │       │ DecidableEq Store.              │                         │                                 │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q06 │ MINOR    │ 14    │ The docstring before scoped     │ P:2012–2015,2206         │ Move the docstring after        │
│     │          │       │ open causes a Lean syntax       │                         │ open … in; rerun the test.      │
│     │          │       │ error.                          │                         │                                 │
├─────┼──────────┼───────┼─────────────────────────────────┼─────────────────────────┼─────────────────────────────────┤
│ Q07 │ MINOR    │ 7     │ DC:1722 does not contain the    │ P:944,1174;              │ Cite DC:2220 and retain         │
│     │          │       │ parent-slot test.               │ D:1722,2220              │ alfs4:798.                      │
└─────┴──────────┴───────┴─────────────────────────────────┴─────────────────────────┴─────────────────────────────────┘
```

**Q01 — counterexample.** Lean evaluation gives:

```text
idTokens "ap.headReachesLo.v4"   = ["ap.headReachesLo.v4"]
idTokens "_ap.headReachesLo.v4_" = []
idTokens "_fj.frame.v2_"        = []
```

Replace the active `.ap` references to v5 with `_ap.headReachesLo.v4_`, and replace `.external "fg.finalLock.v1"` with `.external "_fj.frame.v2_"`. Both superseded references disappear from the output. The remaining IDs pass the registry tests. I reproduced this with the plan’s `idTokens` and `emitIds`. Structured reference fields would remove this dependence on prose formatting.

**Q02 — counterexample.** An `IDS` file containing only:

```text
pin fj.frame.v3
```

passes the exact shell ID checks with `status=0` and `npin=1`. The script checks that at least one pin exists. It does not check that all pins, active references, or historical entries are present. The expected counts at P:2194 are printed expectations, not enforced conditions.

Missing and empty input is rejected. Nonempty partial input is not. Add tests for a truncated list and for omission of each reference category.

**Q03 — counterexample.** Rewrite `alfs4` with valid compact structure syntax, `def alfs4:Src:={…}`, and set its hash to 64 zeroes. The source extractor misses the declaration because it expects tuple syntax. The declaration count also misses it because it searches for `: Src :=`.

Both counts become **12**, so the completeness test passes. The other 12 sources remain valid, while the wrong `alfs4` hash is never checked. The elaborated pin IDs do not expose this error because `emitIds` emits no source data. This repeats the original shared-parser weakness in the source check.

**Q04** leaves part of P02 incorrectly applied. Registry clause 1 gives a sufficient condition for a head in `D_V` at height at least `lo`. It does not state the converse for height alone. At the function boundary, take `D_V = ∅` and a full-tree lease anchor `A` with height H. `ghost` returns A, although the stated frozen-domain condition fails. The coverage label must preserve the direction of the registry implication.

**Q05 and Q06** are reproducible Lean errors. The refusal equalities fail to synthesize `Decidable`. Adding `deriving instance DecidableEq for Store` makes those tests pass. The pin snippet, even with the documented single-backquote substitution, reports `unexpected token 'open'` at the docstring before `defPins`. Moving that docstring below `open … in` makes the snippet elaborate. Thus P:2206 overstates validation of the exact printed snippet.

The earlier findings have these final statuses:

- **P01:** the controller’s requirement is met for pin IDs. Compact `id:="fj.frame.v2"` is visible in elaborated data. Q01–Q03 remain gaps in the wider check.
- **P02:** the two head domains and anchor conditions are now separate, but Q04 remains.
- **P03 and async minor 3:** the new folds repair the unreachable-store example. Q05 affects the refusal test code.
- **P04, M1, M2, async minors 1–2 and 4–6, and the registry/createRow small items:** the requested substantive changes are applied. Q07 is a new citation error.

I found no new false or vacuous theorem in Tasks 7, 12, or 13. The four refusals have the spec’s relative order. The future-slot bound, signature, and row-round check are now one explicit FG admission input contract.

`StoreInv` remains preserved. Every refused branch returns the old store. In the accepted branch, insertion preserves closure and genesis; the cache updates preserve `hmax`, `pair`, and `FJ`; the finality acceptance test preserves `Fmem`; and the new carrier or the retained old carrier supplies `Fcar`. The parent-slot refusal introduces no new accepted case. The statements and proof guides for `activeView_subset`, `update_finality_TF`, and `on_block_TF_subset` are correct.

I checked both example folds in Lean through standard input. Both satisfy every `StoreInv` field. The active-view fold gives the stated `F = B1`, pair `(2, B1)`, `h_max = 4`, and membership results. I used distinct roots for B2 and B3, which the plan leaves unspecified.

The Trees, `on_block`, reconciliation, and head-function ranges match `alfs4`, apart from Q07’s DC citation. The Trees coverage split and the AP classification of reconciliation are correct. All 13 source hashes match. The supplied diff applies to `195d31a` and produces the final plan exactly. These were isolated checks, not a full project build or a completed general proof.

**Verdict: REVISE.** The store changes pass this re-check, but the pin check can still report success while required data escapes validation.

AUDIT COMPLETE: 0 blocking, 3 major, 4 minor