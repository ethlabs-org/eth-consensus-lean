VERDICT: REVISE

Audited HEAD `5ec0dff`, read-only. `Plan` below means [the r3 plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-i9-derived-roots.md). Counts refer to the remaining findings, not the original findings.

```text
┌─────┬──────────┬──────────────────────────────┬──────────────────────────────────────────────┐
│ Id  │ Severity │ Evidence                     │ Fix                                          │
├─────┼──────────┼──────────────────────────────┼──────────────────────────────────────────────┤
│ R01 │ BLOCKING │ Plan:130–134, 151–154         │ Give bitLen global correctness. Specify      │
│     │          │ Bounded bitLen proof versus  │ fuel and exhaustion behaviour for both      │
│     │          │ unrestricted codec laws.     │ searches and tz. Prove unrestricted laws.    │
├─────┼──────────┼──────────────────────────────┼──────────────────────────────────────────────┤
│ R02 │ MAJOR    │ Plan:70, 85–103, 253–256;     │ Add metaInv_accepted with a rowsOk premise   │
│     │          │ FGSA/Proofs/Metadata:340–349  │ to the exception table. Also list wireTree   │
│     │          │ Required premise is absent.  │ strengthening and collision-test changes.   │
├─────┼──────────┼──────────────────────────────┼──────────────────────────────────────────────┤
│ R03 │ MINOR    │ Plan:275–281                 │ Check the lock on the final merged tree.    │
│     │          │ Merge trigger watches only   │ Imported Model and Statements definitions  │
│     │          │ Framework and catalog.lock.  │ can also change lock hashes.                │
└─────┴──────────┴──────────────────────────────┴──────────────────────────────────────────────┘
```

1. **A01–A10 dispositions**

“RESOLVED” means the plan specifies the required repair. It does not mean that the implementation proofs are complete.

```text
┌─────┬──────────┬────────────────────┬────────────────────────────────────────────────┐
│ Id  │ Status   │ Plan lines         │ Assessment                                     │
├─────┼──────────┼────────────────────┼────────────────────────────────────────────────┤
│ A01 │ PARTLY   │ 55–56, 130–139     │ epair fixes growth; kernel checks are required.│
│     │          │                    │ The new fixed-fuel specification has R01.      │
│ A02 │ RESOLVED │ 249–253, 258       │ Full reconstruction; FG body keeps packInner. │
│ A03 │ PARTLY   │ 70, 85–103         │ Original exceptions are present. R02 remains. │
│ A04 │ RESOLVED │ 61, 155–158, 177,  │ Lookup and no-op facts are separate. Relay    │
│     │          │ 188, 198, 254, 267 │ feasibility stays open.                       │
│ A05 │ RESOLVED │ 28–30, 158, 267    │ Uses the image of Block.root, with genesis.   │
│     │          │                    │ The root-only wire refinement stays open.     │
│ A06 │ RESOLVED │ 165–166, 184–185,  │ Missing files and audit sites are included.   │
│     │          │ 233, 243–245, 274  │ Final import coverage is required.            │
│ A07 │ RESOLVED │ 73, 110–111,       │ Signed packing, split yB, refusal causes,     │
│     │          │ 223–227, 255–258   │ and root-order checks are specified.          │
│ A08 │ PARTLY   │ 59, 115, 275–280   │ Exact 91-name set and closure review are      │
│     │          │                    │ correct. Final-merge coverage has R03.        │
│ A09 │ RESOLVED │ 147, 159           │ rootInjective_all is in Kit/Roots, with the   │
│     │          │                    │ correct Conditions import.                    │
│ A10 │ RESOLVED │ 11, 103, 177–198,  │ Evidence paths, task references, and the      │
│     │          │ 254                │ statement/proof distinction are corrected.    │
└─────┴──────────┴────────────────────┴────────────────────────────────────────────────┘
```

2. **Codec laws, size, and fuel**

The arithmetic codec is correct **with adequate bit lengths and exact trailing-zero decoding**.

Let `L = bitLen`, `k = L b`, `c = a * 2^k + b`, and `j = L k`. Then:

```text
epair a b + 1 = 2^j * (2 * (c * 2^j + k) + 1)
```

The parenthesized factor is odd. Thus `tz` recovers `j`. Division removes `2^j` and the odd tag. Division and remainder by `2^j` then recover `c` and `k`, because `k < 2^j`. Division and remainder by `2^k` recover `a` and `b`, because `b < 2^k`.

The stated size bound is correct for standard bit length:

```text
bitLen (epair a b)
  ≤ bitLen a + bitLen b + 2 * bitLen (bitLen b) + 1
```

I checked both round trips and this bound on 66,539 arithmetic cases, with inputs up to 100,001 bits. This is arithmetic evidence, not a Lean proof of the proposed implementation.

**The fixed fuel is the blocking issue.** Plan:130 permits a correctness proof only for `n < 2^(2^64)`. Plan:134 requires unrestricted laws, and Task 1 requires injectivity for every block. Bodies, slots, and chain depth have no such bound. Nested encodings also need not stay below that bound.

A fixed cutoff must not silently truncate the length. For example, if a fallback returns length `M` for both `2^(M−1)` and `2^M + 2^(M−1)`, then these distinct inputs collide:

```text
epair 1 (2^(M−1)) = epair 0 (2^M + 2^(M−1))
```

For the stated finite range, 64 search steps **can** suffice with suitable phase budgets and endpoint handling. The plan gives neither recurrence nor exhaustion behaviour. A search that tests `j = 0,…,63` must still handle the upper bracket at `2^64`. The exact implementation needs a fuel theorem.

For `tz`, Plan:133 specifies fuel recursion but **does not specify the fuel**. For nonzero input `m`, fuel `m + 1` is a sufficient conservative choice. A fixed fuel of 64 would not suffice: within the stated range for `b`, `bitLen b` can equal `2^64`, so the outer `epair` delimiter can have **65 trailing zeros**.

The fallback “prove only the two bounds” is mathematically sufficient **if those bounds hold globally** and `tz` is exact. The upper bound provides the remainder conditions needed for decoding and injectivity; the lower bound supports the size proof. It does not remove the fuel problem. Also specify `bitLen 0 = 0` if equivalence to standard bit length is required.

Fix R01 with a total search and a proved sufficient input-dependent fuel, or an exact continuation when the fast search exhausts its fuel. Keep the unrestricted codec and block laws.

3. **FG-SA packing and invariants**

The Task 9 construction is sufficient, subject to the codec laws and the missing proof premise in R02.

With the intended erasure definition:

```text
eraseFG (fgBlock P b rw)
  = Block.node (eraseFG P) b.slot
      (packBody (appOf b.body) rw)
```

The three stated premises—non-genesis, matching parent erasure, and `rowsOk`—make this equal to `b`. `appOf_packBody` makes honest packed proposals pass the check. No reconstruction law for arbitrary natural numbers is needed.

Admission can establish the stronger `MetaInv.wireTree`, because `blockAccepted` checks the same `rowsOk`. Other transitions preserve the content equality when they preserve stored proposals.

For `ContentAgree`, equal base roots give equal blocks and bodies. The two stored `rowsOk` facts give equal packed bodies. `packBody_inj` then gives equal ordered signed rows, including rounds. `MetaInv` at both stores is sufficient for this argument; retaining the stated `CStoreInv` premises is harmless.

However, [`metaInv_accepted`](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSA/Proofs/Metadata.lean:340) receives neither `blockAccepted = true`, `wellFormed = true`, nor `rowsOk = true`. Its field-equality premises allow an arbitrary new body with unrelated carried rows. They cannot establish the new content equality—or even the repaired erasure equality.

Add:

```lean
(hrows : rowsOk b rows = true)
```

Pass it from `hacc` in `metaInv_process`.

4. **Statement rule**

Yes, required changes fall outside classes (a)–(c).

The new premise on `metaInv_accepted` is not a root-field replacement, a codec binder, or a named table exception. Its axiom check must remain; it is printed at [Tests/Axioms.lean:227](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSA/Tests/Axioms.lean:227).

The table should also explicitly cover:

- The stronger `MetaInv.wireTree` field.
- The semantic fixture replacements required by Tasks 7 and 9, including `not_contentAgree`, the negative cross-store example, and the collision-driven frame fallback.

Plan:73 authorizes collision-test replacement, but Plan:103 restricts changes to the enumerated classes and table. Make these instructions consistent.

5. **Task 11 lock rule**

The expected set is correct. I reran the lock algorithm against the compiled environment, through standard input:

```text
┌────────────────────────────────────────┬────────┐
│ Check                                  │ Result │
├────────────────────────────────────────┼────────┤
│ Current locked declarations            │ 250    │
│ Current lock differences               │ 0      │
│ Closures that reach Block              │ 91     │
│ Expected TSV names                     │ 91     │
│ Missing / extra expected names         │ 0 / 0  │
└────────────────────────────────────────┴────────┘
```

The exact-name, no-addition/removal, source-review, and closure-review requirements are sound for the tree being checked. Before the authorized rewrite, expected `CHANGED` output gives exit code **1**; “exit normally” must allow that documented result and reject checker failures. After rewriting, require exit code 0 and no differences.

R03 concerns the final merge. Changes to imported Model or Statements definitions can affect hashes without changing either watched path. A full build does not check `catalog.lock`. Integrate main before final validation, or rerun the lock and closure checks on the exact merged tree.

6. **New or remaining defects**

R01 is introduced by r3’s fixed-fuel `bitLen` specification. R02 is an unresolved omission in the revised statement rules and invariant proof plan. R03 remains after r3’s partial merge-order repair.

I found no further defect in the packing equations or the corrected 91-name prediction.

7. **Can Task 0 start?**

**No, not under r3 as written.** Fix R01 and R02 first. This also satisfies the plan’s requirement at line 361 for no blocking or major finding. Fix R03 before final merge validation.

No repository files, state notes, or logs were changed.

RECHECK COMPLETE: 1 blocking, 1 major, 1 minor