# G6 Opus review: Task 6 (frame reads and duties)

Range: `db90f32..e296dde` on `fgsa-composition` (`d5171fc` Task 6, `e8c0ba8`
G5 dispositions, `e296dde` docstring). Spec: `fgsa-protocol-2e884811.tex`.
Date: 2026-09-29.

## Verdict

**PASS WITH FIXES.** 0 blocking, 1 major, 6 minor.

Each definition of `Model/Frame.lean` agrees with its spec lines. I found no
off-by-one, no wrong strict or non-strict comparison, no missing F or Z
filter and no read of a model-only cache. The major finding is a test gap:
no test pins the HEAD view (`voterBlocks`) or the effect of the vote merges
on `headVote`.

## Build and validation

Scratch worktree at `e296dde` (build artifacts cloned from the main tree):

```text
┌──────────────────────────────────────┬───────────────────────────────────────┐
│ Command                              │ Result                                │
├──────────────────────────────────────┼───────────────────────────────────────┤
│ bash scripts/check-fgsa.sh (d5171fc) │ exit 0; 127 theorems axiom-checked    │
│ bash scripts/check-fgsa.sh (e296dde) │ exit 0; 408 constants, 127 theorems   │
│ lake env lean scratch/G6Check*.lean  │ mutation and hand-value checks below  │
└──────────────────────────────────────┴───────────────────────────────────────┘
```

No `sorry`, no native evaluation. Test (c) uses `decide +kernel` (risk R1
fallback; the kernel check adds no axiom). The plan code block of Task 6
Step 2 and `Model/Frame.lean` are identical (one blank line differs). All
34 lines of the planned Step 1 tests are in `Tests/Smoke.lean`.

## 1. Definitions against the spec

```text
┌─────────────────┬───────────────┬──────────────────────────────────────────────┐
│ Definition      │ Spec lines    │ Result                                       │
├─────────────────┼───────────────┼──────────────────────────────────────────────┤
│ controls        │ 616–633       │ agrees (live caches; contest on Σ.T)         │
│ fullTree        │ 1033–1037     │ agrees (storeFrame on TF: F⪯B, Z⪯B, witness) │
│ liveRoot        │ 648–655,      │ agrees; fold from Z is exact because every   │
│                 │ 1086–1098     │ target extends Z; `now < deadline` = lease≠⊥ │
│ eligible        │ 1063–1072     │ agrees: `<` lo, strict majority, B.slot=Σ.s  │
│ headInTree      │ 1074–1107     │ agrees (live root of the FULL tree)          │
│ getHead         │ 1109–1114     │ agrees                                       │
│ voterBlocks     │ 1219–1226     │ agrees: stamp < t_{s−1}+3Δ, or B ⪯ P, P∈Σ.T, │
│                 │               │ P.slot = s; viability inside the view        │
│ headVotes       │ 1283–1291     │ agrees: pool stamp < z_{s−1}; carried label  │
│                 │               │ s−1 of every admitted slot-s proposal        │
│ headSupport     │ 423–430,      │ agrees: resolvedBefore on CURRENT act(Σ);    │
│                 │ 1286–1293     │ carried: H' ∈ Σ.T, H'.slot ≤ s−1             │
│ headVote        │ 1276–1302     │ agrees (genesis at s = 0)                    │
│ proposerVotes/  │ 1240–1243     │ agrees: gfPool[s−1]; support = head in act,  │
│ proposerSupport │               │ slot ≤ s−1 (resolution < ∞)                  │
│ proposalRows    │ 544–556,      │ agrees: I = [max 0 (r−w_F), r] as r ≤ r'+w_F │
│                 │ 1255–1274     │ ∧ r' ≤ r; chain rows removed from A and A';  │
│                 │               │ A-rows removed from A'; pool rows first      │
│ propose         │ 1236–1253     │ agrees (root formula of GridCO, DQ10)        │
│ fgHead          │ 1318–1323     │ agrees: gfPool[Σ.s], head in act, slot ≤ Σ.s │
│ deepest         │ 260–262       │ agrees (depth, then greater root)            │
│ fgSource        │ 666–677,      │ agrees: full tree ∩ fastWrite[rR], lease >   │
│                 │ 1327–1335     │ Σ.t (strict); no fallback                    │
│ fgInputs        │ 1315–1338     │ agrees; fallback unreachable under CStoreInv │
│ attest          │ 1304–1313,    │ agrees as a projection (no emission, no      │
│                 │ 1391–1399     │ σ.nj: M13; Λ outside the store: DQ4)         │
└─────────────────┴───────────────┴──────────────────────────────────────────────┘
```

All docstring spec anchors point to the correct lines of `2e884811`.

## 2. Model-only caches and GridCO duties

`Model/Frame.lean` reads `base.blocks`, `base.blockStamp`, `base.voteStamp`,
`base.votes`, `base.obligations`, `base.now`, `st.fg`, `st.proposals`,
`st.rowPool` and `st.fastWrite`, directly or through `actView`,
`GridCO.{votesAt, stampBlock, stampVote, resolvedBefore, blockKnown,
goldfishScore, voterCount, ghost}`, `fastWriteAt`, `leaseOf`, `storeFrame`,
`storeControls` and `createRow`. None of these reads `frozen`, `early`,
`releaseSnapshots`, `goldfishRecord` or `base.proposals`. No definition calls
GridCO `act`, `voterView`, `voterSupportView`, `voterTree`, `forkChoice`,
`liveRoot`, `propose`, `proposalsAt`, `carriedRaw` or `carriedSupport`. The two
grep hits for `frozen` are local `let` names (MINOR 5). M11: every
definition with `{n : Nat}` takes no `p`.

## 3. Tests: mutation checks and hand computations

Hand values checked by `#eval` at `e296dde`: `σ[B1].h = 2`, `σ[B2].h = 3`,
`σ[B3].h = 4`; in `stA`: `H = 4`, `j = 2`, no contest, `lo = 3`, `Z = F = B1`;
`σ[B3].h_j = σ[B3].h_F = 2`; `stC0`: `fastWrite = [(2, [])]`, no lease,
`S = b1`, `genuine = [(2, none)]`; `stX`: the pool stamp of `vX` is 12;
`stP`: 11 pool rows, 10 block rows. Every docstring hand computation is
correct.

```text
┌──────────────────────────────────────┬───────────────────────────┬────────────┐
│ Wrong definition (scratch)           │ Test that catches it      │ Caught     │
├──────────────────────────────────────┼───────────────────────────┼────────────┤
│ headSupport resolved on base, not    │ (a) headSupport stH 3=[]  │ yes        │
│ act(Σ)                               │                           │            │
│ carried arm only for active blocks,  │ (b) vX ∈ headVotes stX 3  │ yes        │
│ or no carried arm                    │                           │            │
│ GridCO.liveRoot (no tree filter)     │ liveRoot, b1' lease       │ yes (b1')  │
│ band test `≤ lo`                     │ headVote at v_4           │ yes (b3)   │
│ lease `≥ Σ.t`                        │ expired-lease test        │ yes        │
│ proposalRows without chain removal,  │ (c)                       │ yes        │
│ block rows first, or no cap          │                           │            │
│ C_fg fallback to S or to Z           │ stC0 (S = Z = b1)         │ yes        │
│ C_fg fallback to an older set or a   │ stC0                      │ NO (MINOR1)│
│ slow lease; no full-tree filter      │                           │            │
│ head fields from the frame lex pair  │ fgInputs pT stA           │ NO (MINOR2)│
│ headVote on fullTree, not voterBlocks│ none                      │ NO (MAJOR1)│
│ headVote with empty merges           │ none                      │ NO (MAJOR1)│
│ gateStep without evaluate-once guard │ g'                        │ yes        │
└──────────────────────────────────────┴───────────────────────────┴────────────┘
```

## 4. G5 minors

The G5 minors are NOT in `d5171fc`. They are in `e8c0ba8` (after `d5171fc`),
and all five are present:

```text
┌─────┬──────────────────────────────────────────────────────────┬─────────────┐
│ G5  │ Item                                                     │ Status      │
├─────┼──────────────────────────────────────────────────────────┼─────────────┤
│ 1   │ test g' (Smoke.lean:449–458): evaluate-once guard        │ present;    │
│     │                                                          │ verified    │
│ 2   │ stQ docstring: hand-set, not reachable                   │ present     │
│ 3   │ freeze/early docstring: time set back; gate of label 1   │ present     │
│     │ at t = 10                                                │             │
│ 4   │ expiry docstring: release of label 4 at t = 21, no effect│ present     │
│ R1  │ risk R1: plain decide can fail on a true statement       │ present     │
└─────┴──────────────────────────────────────────────────────────┴─────────────┘
```

Verification of G5-1: I evaluated `gateStep` without the guard on `g'`. The
result has the leases `(b1, 2, 21)`, `(b2, 2, 21)` and `S = b2`. Both
conjuncts of the `g'` test are then false, so the test fails without the
guard. With the guard: no lease, `S = genesis`.

## Rulings on the six implementer points

1. `eligible` and `goldfishScore st.base.blocks`: correct. The `tree`
   argument of `goldfishScore` is used only in `target ∈ tree`. Spec
   `goldfish_score` (1039–1048) has no membership test. Each support list is
   filtered before: frozen arm and proposer and FG action to `act(Σ) ⊆ Σ.T`,
   carried arm to `Σ.T`. With the cumulative list the test has no effect,
   which agrees with the spec. The third disjunct `b.slot == st.slot p` is
   spec 1071 `B.slot = Σ.s`. It is the store slot, not the label `k`: correct
   for the HEAD (`Σ.s = s` at `v_s`), the proposer (`Σ.s = s` at `t_s`) and
   the FG action (`Σ.s = rR+1`). See MINOR 4 for a related condition.
2. `fgBlockOf` fallback: correct statement. `fgHead` is either `liveRoot`
   (a tree block, or `eraseFG Z` with `Z ∈ {F, J} ⊆ TF`) or an element of
   `erasedList`, which is the erasure of a TF block. `pickPair` is `some`
   when the erasure is injective on TF; DQ2 gives this (roots are unique in
   TF, and erasure keeps the root). The Task 11 obligations `fgHead_stored`
   and `fgBlockOf_spec` are the correct ones. They also need
   `base.blocks = erase TF` (CStoreInv `baseTree`).
3. `fgSource` round: correct. `a_r = d_{rR} = t_{rR+1} + 2Δ`, so
   `Σ.s = rR+1` and `round(rR+1) = r` for `R ≥ 2`. The tick runs the gate of
   `rR` before the duty (Clock). Smoke.lean:36 pins `slotOf 14 = 3`,
   `round 3 = 1`.
4. `proposalRows` has no cap of its own for pool rows: this is the literal
   spec (1266: "keep the rows of i and r' in A", comment "at most two, by
   the pool cap"). The rowPool is written only by `admitRow`, which has the
   cap, so the bound holds on every reachable store; a hand-set pool can
   break it. The Task 12 MetaInv is the correct place.
5. `erasedList` order: the order has NO effect on `GridCO.ghost`, also for
   equal score and equal root. `ghostStep` returns `none` (the walk stops)
   when a second distinct child has the same score and the same root as the
   best child, in any order. `ghost` also removes duplicates.
6. `voterBlocks`: correct (spec 1219–1233, 598–606). The set is the TF
   blocks with a stamp before `z_{s−1}` and all ancestors of every slot-`s`
   block in TF, before `storeFrame`. `filteredFrom` takes the viability
   witness from the view itself, so a late witness cannot make a pre-freeze
   block viable (spec 604–606). But no test pins it (MAJOR 1).

## Findings

### BLOCKING

None.

### MAJOR

**MAJOR 1. No test pins the HEAD view or the merges in `headVote`.**
`Tests/Smoke.lean:372` is the only `headVote` test. It has no votes, and all
blocks of `stA` have the stamp 12 < z_3 = 15. Thus (i) `headVote` on
`fullTree` in place of `voterBlocks` and (ii) `headVote` with empty merges
both pass every test. Tests (a) and (b) test `headVotes` and `headSupport`
alone, not their use in `headVote`. Spec: 598–606, 1219–1233, 1276–1302.
Scratch checks (both pass with plain `decide` or `#eval`) that fail for the
wrong definitions:

```lean
-- (i) the late block b2 (stamp 12 ≥ z_2 = 11) is not in the view of slot 3.
-- Two equivocating seats make every child eligible; the fullTree
-- definition gives b2.
def eqv (i : Fin 4) (b : Block) : Wire 4 := ⟨.seat (.head 2) i, .head b⟩
def stE : State pT.n :=
  atTime (process pT (atTime ([eqv 0 .genesis, eqv 0 b1, eqv 1 .genesis, eqv 1 b1].foldl
    (process pT) (atTime (process pT (atTime {} 8) (wProp B1 0)) 9)) 12) (wProp B2 1)) 13
example : headVote pT stE 3 = b1 := by decide
-- (ii) the two label-2 votes for b2 make b2 the head at v_3; with empty
-- merges the head is b1.
example : headVote pT (atTime stS 13) 3 = eraseFG B2 := by decide
```

Also recommended: a test of the proposal arm of `voterBlocks` (an ancestor of
a slot-`s` proposal, stamped after `z_{s−1}`, is in the view).

### MINOR

**MINOR 1. `stC0` does not test two of the four fallbacks that its
docstring names.** `Tests/Smoke.lean:352–357`. `stC0` has no older nonempty
fastWrite row and no lease, so a fallback to an older set or to a slow lease
still gives `none`. No test has a `fastWrite[rR]` member with a live lease
that is outside the full filtered tree. Spec 666–677, 1327–1329. Add a
variant with an older row such as `(0, [b1])` and a lease on b1, and a
variant with a member outside the filtered tree.

**MINOR 2. The `fgInputs` head-field test does not tell head-derived fields
from frame fields.** `Tests/Smoke.lean:438–440`. In `stA`,
`HeadFields.ofBlock B3 = (2, root 1, 2)`, and the live pair is
`(Σ.h_j, Σ.J) = (2, B1)`. A definition that reads the frame lex pair gives
the same `h_j` and `J`. Spec 1321–1322 ("finality stays head-derived"). Add
a fixture where `σ[H].J ≠ Σ.J` or `σ[H].h_j ≠ Σ.h_j`.

**MINOR 3. `headVote` and `propose` take `s`, but other reads use Σ.s.**
`Model/Frame.lean:88, 133`. `eligible` (line 32) reads `st.slot p`, and
`proposalRows` (line 121) reads `round(st.slot p)`. The spec sets
`s ← Σ.s` (1238, 1278). The definitions agree with the spec only when
`s = st.slot p`. The docstrings do not state this condition. Add it to the
docstrings or as a T7 caller obligation.

**MINOR 4. The score counts a supporter only if its seat is in the raw
list.** `GridCO.goldfishScore` filters `seats n raw`; spec 1041–1047 counts
every clean seat of `support_votes`. The two agree when support ⊆ raw. This
holds by construction for the frozen arm, the proposer and the FG action.
For the carried arm it needs `B.support ⊆ B.votes`, which `wellFormed` checks
but `process` does not run (DQ14). Inherited from GridCO; no model change.
Add a report line: the HEAD score equals the spec score only when T7 binds
the input check.

**MINOR 5. Local names `frozen` in `headVotes` and `headSupport`.**
`Model/Frame.lean:67, 77`. The name is also the model-only cache field. A
grep for cache reads (G6 Astra check, Task 13) hits these lines. Rename, for
example to `pre`.

**MINOR 6. `proposalRows` groups rows by `auth` equality, `admitRow` by the
decoded `(round, identity)`.** `Model/Frame.lean:128` and
`Model/Handlers.lean:20`. They agree for every candidate (each candidate has
`round? ∈ I`, so it decodes as an FG row). This is not a J1 violation (no
match on the auth). For consistency, use `decode?` in both places or state
the equivalence in the docstring.

## Housekeeping

The scratch worktree `/Users/francesco/.claude/jobs/22f59f85/tmp/g6wt` was
removed after the checks. I made no change in `~/worktrees/available-chain-fgsa`.
