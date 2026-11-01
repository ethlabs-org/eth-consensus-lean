# Astra audit report: I9 branch, Tasks 0–8 (pre-final)

_This file is the verbatim audit output (2026-09-29). The table widths,
the prose and the absolute links are as Astra wrote them. A link under
`/Users/francesco/worktrees/available-chain-i9/` refers to the same path
from the repository root. The prompt is `i9-branch-audit-0-8.md`. The
disposition of I9-A01 is in `docs/I9-REPORT.md` §7, decision 4._

VERDICT: READY WITH FIXES

This verdict covers `a5aaf3c..e42bb37`, Tasks 0–8 only. FG-SA was excluded. No files were changed.

```text
┌────────┬──────────┬───────────────────────────────────────────────────┬─────────────────────────────────────┐
│ ID     │ Severity │ File:line                                         │ Fix                                 │
├────────┼──────────┼───────────────────────────────────────────────────┼─────────────────────────────────────┤
│ I9-A01 │ MAJOR    │ AvailableChainSAPC/Tests/                          │ Restore the five deleted private    │
│        │          │ CleanInvariantCounterexample.lean:206,211,217,239 │ theorems, or record an explicit      │
│        │          │ AvailableChainWitnesses/Sanity.lean:217           │ named exception. Correct the        │
│        │          │ Lines above refer to a5aaf3c.                     │ statement-change records.           │
└────────┴──────────┴───────────────────────────────────────────────────┴─────────────────────────────────────┘
```

The reports identify these deletions as removal of unused helpers. However, [r4’s statement rule](/Users/francesco/worktrees/available-chain-i9/docs/plans/2026-09-29-i9-derived-roots.md:70) has no exception for private or unused theorems. These deletions do not replace a root field, root formula, or numeric root value. This is a plan-compliance defect; I found no resulting proof-soundness defect.

**1. Codec**

The required laws are correct and unrestricted over their stated inputs:

- `efst_epair`, `esnd_epair`, and `epair_inj` have no size or range premise.
- `bitLen_epair_le` proves exactly the planned bound.
- `encList_inj` preserves order and duplicates. Its element-injectivity premise is necessary and correct.
- The option and Boolean laws are correct.
- The nonzero and odd-factor premises on the trailing-zero laws are appropriate.

The evaluated definitions in [Codec.lean](/Users/francesco/worktrees/available-chain-i9/AvailableChainModel/Objects/Codec.lean:21) use structural recursion: `bitLenDouble`, `bitLenSearch`, and `tzAux` recurse on fuel; `encList` recurses on the list. `Nat.size` and `Nat.log2` occur only in proofs. There is no well-founded recursion on the evaluated codec path.

The fuel argument is complete:

- `bitLenDouble_spec` preserves `w / 2 < Nat.size n` and establishes the upper bound.
- `bitLenSearch_spec` proves the exact answer under its interval and fuel bounds.
- `bitLen_eq_size` supplies those bounds with fuel `n + 1`, using `Nat.size n ≤ n`. Thus fuel exhaustion cannot produce an incorrect public `bitLen` result.
- For `tz`, `k < 2^k ≤ 2^k*r` supplies enough fuel for every odd `r`. `tz_spec` extends the result to every nonzero input.

Practical kernel efficiency still has the documented limit: the fast path for `2^k` requires `k < 2^24`. Unrestricted mathematical laws do not imply unrestricted practical runtime. I found no violation of r4’s required implementation form.

**2. Block injectivity and lookup**

All four results are correct and match the plan.

- [`Block.root_injective`](/Users/francesco/worktrees/available-chain-i9/AvailableChainModel/Objects/Blocks.lean:85) separates genesis from every node through `+ 1`, including slot-0 nodes. Two applications of `epair_inj` recover the parent root, slot, and body; induction recovers the parent.
- `parent_mem_iff_root` works for every list, including lists with duplicates and genesis.
- `parent_mem_and_iff_root` works for any predicate `q`. Injectivity identifies the stored block with the carried parent before transferring `q`.
- [`rootInjective_all`](/Users/francesco/worktrees/available-chain-i9/AvailableChainKit/Roots.lean:14) needs no execution or run-validity premise.

These are results about the resolved-block model. They do not establish a root-only wire refinement; the source correctly states that limit.

**3. Complete statement-change classification**

I checked the `git diff a5aaf3c e42bb37` theorem/lemma lines and their complete statement spans. There are **18 retained named theorems with direct statement-text changes**, plus **seven deleted named theorems**.

In the following table, abbreviated paths have the prefix `AvailableChain`. Lines without `old` refer to `e42bb37`.

```text
┌─────────────────────────────────────────────┬───────────────────────────────────┬──────────────────────┐
│ File:line                                   │ Theorem                           │ Classification       │
├─────────────────────────────────────────────┼───────────────────────────────────┼──────────────────────┤
│ GridCO/Proofs/Proposals.lean:59              │ honest_proposal_views             │ Named exception      │
│ SAPC/Proofs/Proposals.lean:49                │ honest_proposal_views             │ Named exception      │
│ Witnesses/Regimes.lean:378                   │ recoveryProposalEmitted           │ (a)                  │
│ Registry/CounterRun.lean:299                 │ preceq_node                       │ (a)                  │
│ Registry/Gaps/NoInput.lean:203               │ preceq_node                       │ (a)                  │
│ KitFG/Accountable.lean:26                    │ RootInjectiveOn.symm              │ (b)                  │
│ KitFG/Certificates.lean:19                   │ preceq_node_of_preceq              │ (a)                  │
│ KitFG/Certificates.lean:26                   │ preceq_parent_node                │ (a)                  │
│ KitFG/Certificates.lean:31                   │ preceq_parent_of_preceq_node       │ (a)                  │
│ KitFG/Certificates.lean:46                   │ onChain_parent                    │ (a)                  │
│ KitFG/Certificates.lean:386                  │ chainOrder_foldRows               │ (b)                  │
│ KitFG/Certificates.lean:580                  │ derive_node                       │ (a), plus (b)        │
│ KitFG/Certificates.lean:705                  │ derive_node_height_entry_cases    │ (a), plus (b)        │
│ KitFG/Certificates.lean:720                  │ derive_node_height_cases          │ (a), plus (b)        │
│ KitFG/Certificates.lean:758                  │ node_entry_eq_of_height_eq        │ (a), plus (b)        │
│ KitFG/Certificates.lean:827                  │ folded_witnesses                  │ (a), plus (b)        │
│ KitFG/Certificates.lean:840                  │ crossing_matching_quorum          │ (a), plus (b)        │
│ KitFG/CrossingNoFinal.lean:128               │ crossing_maturity                 │ (a), plus (b)        │
├─────────────────────────────────────────────┼───────────────────────────────────┼──────────────────────┤
│ Registry/CounterRun.lean:287 old             │ chain_root                        │ (a); replacement     │
│ Registry/Gaps/NoInput.lean:191 old           │ clockBlock_root                   │ (a); replacement     │
│ SAPC/Tests/                                 │ delivered_blocks                  │ OUTSIDE; deleted     │
│ CleanInvariantCounterexample.lean:206 old   │                                   │                      │
│ Same file:211 old                           │ emitted_blocks                    │ OUTSIDE; deleted     │
│ Same file:217 old                           │ named_block                       │ OUTSIDE; deleted     │
│ Same file:239 old                           │ roots                             │ OUTSIDE; deleted     │
│ Witnesses/Sanity.lean:217 old                │ emitted_proposed                  │ OUTSIDE; deleted     │
└─────────────────────────────────────────────┴───────────────────────────────────┴──────────────────────┘
```

The two root-formula replacements are explicitly required by Task 6. They become `chain_depth`/`chain_injective` and `clockBlock_depth`/`clockBlock_injective`.

The seven constructor changes marked “plus (b)” also acquire an implicit `[RowCodec V]` through section variables. A theorem-line search alone misses such binders. I checked the compiled types: **141 existing KitFG theorems acquire `RowCodec`**, including nine already listed above. The other **132**, all class **(b)**, are listed here in full:

- **Accountable:** `accountable`, `accountable_oriented`, `finalLock`, `finalLock_e1`, `justification_certificate_rows`, `uniqueJust_chains`.
- **CausalCap:** `causalCap`, `causalCap_notRoot`.
- **Certificates:** `F_eq_J_of_heights`, `J_is_entry`, `chainOrder_derive`, `derive_F_preceq_J`, `derive_L`, `derive_anchors_preceq`, `derive_witnesses`, `entry_eq_of_preceq`, `entry_eq_on_plateau`, `entry_first`, `entry_height`, `entry_idem`, `entry_parent_height`, `entry_preceq`, `entry_same_height`, `finality_certificate`, `finalized_below_height`, `finalized_zero_is_genesis`, `foldRows_fields`, `foldRows_s`, `foldl_process_row_fields`, `foldl_process_row_s`, `h_mono`, `height_crossing`, `heights_ordered`, `justification_certificate`, `justified_below_height`, `justified_zero_is_genesis`, `one_le_h`, `process_row_fields`, `process_row_finalize`, `process_row_progress`, `process_row_target`, `witnesses_advance`, `witnesses_congr`, `witnesses_empty`, `witnesses_fold`, `witnesses_foldRows`, `witnesses_height_events`, `witnesses_mono`, `witnesses_process`.
- **ClientSafety:** `clientRun_covers`, `clientRun_noSlash`, `createRow_eq`, `createRow_noSelfSlash`, `recordInv_createRow`.
- **Correspondence:** `exists_frontier`, `filteredFrom_Z_mem`, `filteredFrom_reachesLo`, `filteredFrom_viable_child`, `fjControls_J_preceq_of_rootIsJ`, `fjFrame_D`, `fjFrame_D_nonempty`, `fjFrame_Z_mem_D`, `fjFrame_lo`, `frameViable_eq_accept_cut`, `frameViable_eq_accept_of_noContest`, `frameViable_subset_accept`, `frontier_insert`, `frontier_mono`, `fst_le_of_lexKey_le`, `hOf_eq`, `le_frontier`, `lexKey_fallback_le`, `lexMax_eq_of_greatest`, `lexMax_insert`, `lexMax_mono`, `lexMax_of_advance`, `lexMax_of_candidate`, `lexMax_of_none`, `lexMax_spec`, `mem_filteredFrom`, `on_block_F_mono`, `on_block_TF_subset`, `on_block_of_accepted`, `on_block_of_refused`, `pair_eq_of_lexKey_eq`, `storeControls_eq_fjControls`, `storeFrame_feasible`, `storeFrame_full`, `storeInv_accept`, `storeInv_init`, `storeInv_on_block`, `update_finality_F_cases`, `update_finality_F_mono`, `update_finality_TF`, `update_finality_h_max`, `update_finality_pair`, `viewRootInj_mono`.
- **CrossingNoFinal:** `crossingNeedsTimeout`, `crossingNoFinal`, `crossingNoFinal_QC`, `crossing_other_entry`.
- **InBandLock:** `finalityPair_carrier_above`, `inBandLock`.
- **Provenance:** `provenance_entry`, `provenance_finality`, `provenance_finalityQC`, `provenance_finalityRow`.
- **TwoChanges:** `Fmove_atFrontier`, `Fmove_atTop`, `Fmove_below`, `Fmove_filtered`, `effFrame_of_bits`, `evidence_mono`, `filteredFrom_congr`, `filteredFrom_move`, `fjControls_contest`, `gap_of_ne`, `lexMax_carrier_of_top`, `lexMax_fst_lt`, `lexMax_top_of_carrier`, `nFrame_eq`, `nFrame_eq_phaseFrame`, `one_le_frontier`, `phaseOf_eq`, `rootIsJ_iff`, `top_J_extends`, `top_contest`, `top_contested`, `top_uncontested`, `twoChanges`, `twoChanges_count`, `twoChanges_nested`.

Additional distinctions:

- The anonymous SimplexFG collision/fallback example changes under its **named exception**.
- Both `honest_proposal_exists` statements stay unchanged; their constructor edits are inside proofs.
- New codec laws and new helper theorems have no previous statement. They are excluded from the change count.
- Generated declarations and structure projections are excluded from the source theorem/lemma count.
- The protected contract statements and Framework declarations retain their source text.
- No `#print axioms` line was removed from a `Tests/Axioms.lean` file.

**4. Fixture causes**

I found no unintended change of cause.

```text
┌───────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Fixture group                 │ Result                                                       │
├───────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ Grid CO / SA                  │ Forks remain distinct. Recorded root orders are proved.      │
│ SAPC counterexample           │ y.root < x.root remains true; x still wins the score tie.    │
│ SAPC Smoke                    │ Honest x has body 0; proposal equality and checks remain.    │
│ L*                            │ One non-genesis block; output has no root-order dependency.  │
│ Witnesses / Registry          │ Sibling distinction, slot-0 node, and witness intent remain. │
│ SimplexFG B1a/B1b tie          │ B1b still wins; B1a.root < B1b.root is proved.                │
│ SimplexFG collision example   │ Declared change: distinct roots and selection of B1c replace │
│                               │ collision-driven fallback.                                  │
│ SimplexFG Store refusals      │ Duplicate, missing parent, F conflict, and parent-slot      │
│                               │ refusal retain their separate causes.                       │
│ SimplexFG Client              │ Entry difference, timeout guard, and lock guard remain.     │
│ KitFG K3                      │ Finality-only rows and the Fmove_atTop witness remain.       │
└───────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

`childA = B2` and `B1c = B1'` are new equalities caused by equal content. No audited fixture requires either pair to be distinct or places both into a test that needs two blocks. `clientB1alt = B1b` was already true before I9.

I independently checked these equalities, both SimplexFG root orders, and the other admission conditions for the duplicate and missing-parent fixtures with Lean through standard input.

**5. `encFGBody`, the tag, and erasure**

Yes. There is no obstacle, provided both sides use the same `RowCodec` instance and erasure uses:

```lean
| .genesis => .genesis
| .node p s x rows =>
    .node (eraseFG p) s (encFGBody x rows)
```

The node case reduces to:

```lean
nodeRoot (eraseFG p).root s (encFGBody x rows) =
nodeRoot p.root s (encFGBody x rows)
```

The induction hypothesis closes it. `fgBodyTag` is inside the same `encFGBody` expression on both sides.

I checked this exact structural-induction proof against the compiled Tasks 0–8 modules. It passed; its axiom list was `[propext]`. The global erasure-root law needs no `rowsOk`, store invariant, or admission premise.

**6. Other merge blockers and verification limits**

I found no further defect in Tasks 0–8 that should block the merge.

The changed-source scan found no `sorry`, `admit`, `native_decide`, or new axiom declaration. The independently inspected main laws use only the allowed axioms. The audited handlers, `blockKnown`, payload types, and exclusion rules retain the required behavior.

The saved Task 2 lock output contains exactly the expected **91 changed names**, with no set difference. Framework source, `catalog.lock`, `REGISTRY.md`, and `MATRIX.md` are unchanged in the audited range.

Resolve I9-A01 before final approval. Tasks 9–11 must still supply the real FG-SA process measurement, full build, and lock/closure checks on the final tree. This audit used the exact source diff and fresh Lean checks against existing compiled modules; it did not repeat a full Lake build.

AUDIT COMPLETE: 0 blocking, 1 major, 0 minor
