I found **2 major and 2 minor issues** at HEAD `dbd5860`. I changed no files.

Evidence keys: **P** = [plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-28-fg-module.md), **R** = [registry](/Users/francesco/ethereum/lean/available-chain/docs/FG-COMPOSITION.md). Numbers are file lines.

```text
┌─────┬──────────┬─────────────────────────────────┬──────────────────────┬───────────────────────────────────┐
│ ID  │ severity │ finding                         │ evidence (file:line) │ proposed fix                      │
├─────┼──────────┼─────────────────────────────────┼──────────────────────┼───────────────────────────────────┤
│ T01 │ MAJOR    │ Counts accept missing records   │ P:2168–2179          │ Compare exact records with the    │
│     │          │ when duplicates replace them.   │ P:2208–2211          │ elaborated table. Reject          │
│     │          │                                 │                      │ duplicate sources and historical  │
│     │          │                                 │                      │ IDs.                              │
├─────┼──────────┼─────────────────────────────────┼──────────────────────┼───────────────────────────────────┤
│ T02 │ MAJOR    │ A partial name list can pass    │ P:2104–2107          │ Check producer status and the     │
│     │          │ the axiom membership check.     │ P:2232–2234          │ complete name set, preferably     │
│     │          │                                 │                      │ inside Lean.                      │
├─────┼──────────┼─────────────────────────────────┼──────────────────────┼───────────────────────────────────┤
│ T03 │ MINOR    │ Malformed fields pass after     │ P:2165,2178          │ Use strict token grammars.        │
│     │          │ whitespace or escape            │ P:2196–2205          │ Preserve each value during        │
│     │          │ conversion.                     │                      │ lookup.                           │
├─────┼──────────┼─────────────────────────────────┼──────────────────────┼───────────────────────────────────┤
│ T04 │ MINOR    │ The split clauses mix the v1    │ P:1954–1955          │ State v1 with its view premises   │
│     │          │ and v5 head guarantees.         │ P:2002–2004          │ and no fallback. State v5 with    │
│     │          │                                 │ R:1819,1874          │ its anchor condition.             │
│     │          │                                 │ R:2868–2874          │                                   │
└─────┴──────────┴─────────────────────────────────┴──────────────────────┴───────────────────────────────────┘
```

**T01 — counterexample.** In the emitted manifest, replace the `src alfs4 ...` line with a second copy of `src ldp ...`. Keep the original trailer. The check returns:

```text
checked 13 sources, 12 pin ids, 8 active references and 9 historical ids
exit 0
```

The `alfs4` hash receives no check. Two further replacements also return exit 0:

- Replace `ap ap.fastSupport.v1` with another `ap ap.headReachesLo.v1`. The reported active-reference count falls to 7.
- Replace `notFormalized fj.frame.v2` with another `notFormalized ap.headReachesLo.v2`. The reported historical count falls to 8.

The trailer checks line counts. It does not bind record identities or values. A subset with one valid source, one valid pin, and a matching trailer also passes. Thus Q02 is only partly fixed.

**T02 — counterexample.** Use a name list containing `AvailableChain.SimplexFG.FGBlock` and `Nat.add_comm`. Let the producer print only the first name, then exit 7. The printed Step 3 code continues because `$names` is nonempty.

With a clean, isolated Objects import, I reproduced:

```text
Partial producer, exit 7:
checked 170 constants, 40 theorems
final exit 0

Complete expected-name list:
NOT CHECKED: Nat.add_comm
exit 2
```

The library-wide axiom scan still runs. The missing check is whether **every pinned name** belongs to its checked constants. The `--names` output has no trailer, and the command does not test producer failure.

**T03.** The grammar permits tabs and backslashes. Later parsing changes their meaning. I reproduced exit 0 for a trailing tab in a pin ID, active-reference ID, historical ID, and source root. This malformed pin line also passes:

```text
pin fj.frame.v\063
```

`awk -v` converts `\063` to `3`. The checker therefore validates `fj.frame.v3`, although the supplied ID is different.

**T04.** P:2002–2003 assigns the frozen-tree anchor condition and possible fallback to `ap.headReachesLo.v1`. Registry v1 guarantees a head in D at height ≥ lo under its stated view premises; its walk has no unfiltered fallback. Those fallback rules belong to v5. The separate ALFS “walk below lo” row at P:1955 should also state v5’s anchor condition.

The earlier findings have these results:

- **Q01:** the earlier decorated-ID counterexamples now fail. Structured `.ap` and `.external` fields fix that extraction gap.
- **Q02:** simple truncation now fails, but T01 remains.
- **Q03:** fixed. The compact `def alfs4:Src:={…}` with a zero hash elaborates and produces both hash errors.
- **Q05:** fixed. The printed `Store` declaration derives `DecidableEq`, and an equality test with `decide` passes.
- **Q06:** fixed. The printed Pins snippet elaborates with stub constants.

Missing records with an unchanged trailer, missing or duplicate trailers, and duplicate pin IDs fail. Reordering body records passes without losing validation. The `.apData` and `.runFact` changes correctly distinguish data without registry IDs.

I tested the printed emitter in Lean and the shell validation rules with pipes in place of temporary files.

**Verdict: REVISE.** Required records and pinned names can still escape validation while the check reports success.

AUDIT COMPLETE: 0 blocking, 2 major, 2 minor