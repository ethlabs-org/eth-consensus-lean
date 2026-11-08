# ½ pre-confirmations: statement plan for an anchor oracle in the AC cone

A plan only. No cone file changes with it; whether and when the cone is re-typed is decided with the cone's
owners, after the in-place write-mode re-typing has landed. The definitions it builds on are in
`ConsensusLean/Instances/Goldilocks/Milestones/Spec/Candidates/PreConfirmations/` (the PC store, the start
function `pcStart`, the core skeleton with a start `…EMAt`, the forgotten trace `projTracePC`). Paths below are
relative to `ConsensusLean/Instances/Goldilocks/`.

## What the PC changes in the cone

The ½-PC layer adds no write mechanism to the core: every core write is one of the core's own update functions
(`CoreStepAtCallStart` in `Candidates/PreConfirmations/Statements`). What it changes is the block the head walk
starts from: with an authoritative key, `pcAnchor A Φ t Y`, the deepest live lock block extending the base `Y`, or
`Y`; without one the parent's `getAnchor A Φ t`. The writes are not equal to the parent's at the parent's start: a
different start gives a different head of the own vote, which enters the pool before the same call's optimistic
confirmation, so the pool, the optimistic lock and its weight, `latestConfirmed` and, at later updates, the saved
rows and counts can differ. Only with no key in `pcs` is a call the core's (`CoreStepOfNoKeys`, a conditional
equality). So the cone splits into structural lemmas, which port as they are, and head-dependent invariants, which
need the new run and anchor hypotheses (question 3).

## The three questions

### 1. Does `getAnchor` keep its signature?

Yes. `getAnchor sp A Φ t` (`Spec/SA/Locks.lean`) stays the parent's anchor and is not changed. The PC start is
a separate function (`pcStart`), and the walk from an arbitrary start is `headFrom` (`getHead` is `headFrom` at
`getAnchor`, by definition). The handlers that walk take the start as an argument (`StartFn`), and the parent's
handlers are these at `parentStart` (`ParentStartIsCore`, by definition).

### 2. Is the ½-PC anchor a function of a lock set?

No: it is a function of a lock set **and a base**. `pcAnchor A Φ t Y` reads `A.locks`, `Φ`, `t` and `Y`. The
base `Y` is not a function of the locks: it reads the PC store (the keys with a quorum, the pair-evidence and
annihilation marks, the vote record, the window) and the call's view and slot (the D21 projection counts the
view's non-equivocating opponents). So a per-cut oracle that generalises `u` needs a second component.

Proposed shape, mirroring `u`:

- an oracle `a : Nat → Option (Blk sp.n FGP)`, the base of cut `i` (`none`: no authoritative key);
- the start of cut `i` is `startOf (u i) (a i)`: `getAnchor` of the read point's locks when `a i = none`,
  `pcAnchor` of the read point's locks and `Y` when `a i = some Y`;
- `AnchorRel`, the relation tying `a i` to the forgotten trace: `a i = none`, or `a i = some Y` with `Y` the D21
  projection, against the call's view and slot, of the target of a key `(s, X)` with `slot(t) ≤ s + e` that has
  an honest acker with a fast-test decision (`AckDecidedAt`, through `KeyProvenance`), all stated on the forgotten
  trace through the existing `confirmationScore`;
- the parent is `a := fun _ => none`. **Requirement:** `ACLocalRunU m u` stays the `a = none` case
  definitionally: either an `abbrev` of `ACLocalRunUA m u (fun _ => none)`, or a separate structure with an
  `Iff.rfl` equivalence. The cone's existing statements over `ACLocalRunU` then need no change.

The start of each call is named, not only asserted to exist: `callStartPC` is the PC start of the store evaluated
after the call's record and before its walk (`walkStorePC`), and `CoreStepAtCallStart` and `ProposalAtCallStart`
(the proposal's duty head and payload) tie the PC calls to the core skeleton at that start. `AnchorRel` is then a
statement about `walkStorePC`'s base, which the oracle `a` abstracts.

Because the oracle is a separate argument, it changes only the calls that walk (`tryVoteWithM`,
`acProposalWithM`) and the run law's `exec` field. A `WriteMode` field would instead change every `stepWithM`,
`callInputM` and `callViewM` call site, and the anchor is a read, not a write. Keeping `stepWithM m u` as an
abbreviation of the new step at `a = none` keeps the existing call sites unchanged.

**Reads are not cuts.** `ac_head` and `ac_confirmed` are functions of the state, the frame and the time of the read,
made at arbitrary points (by the FG, by the confirmed-tip lemmas). Under the PC they evaluate the store, which the
forgotten trace does not carry, and between calls the read's own inputs move: `latestView` switches slot at
`t_s + 2Δ`, and the window drops keys as the slot advances, so the base and the head of a read can change with no
call. A read oracle must therefore take the read time `T` with the frame and the state it reads (the state after
the node's last cut before `T`, the frame of that read), not only the node and the cut; or the read-side statements
are stated over the PC state with `Φ` and `T` explicit. The read-side consumer is
`Lemmas/Healing/AC/Confirmed.lean`: it proves that a block `P` is an ancestor of both the record and the head, and
hence of their deepest common ancestor, the confirmed tip (`head_extendsU` at the call's post-state, frame and
time). The confirmed tip does not in general extend the head.

### 3. Which read-side lemmas break, and what replaces them?

At the read point of a vote the locks are exactly the call's `u i` (`tryVote_readPoint_locks_eqWith`,
`Lemmas/AC/ReadPoint.lean:24`). That stays true; what changes is what the start is.

| Lemma | Status under the PC | Replacement |
|---|---|---|
| `anc_getAnchor` (`Lemmas/AC/LockStore/Chain.lean:91`): the anchor extends every live lock block and `fc_root` | breaks for `a i = some Y`: locks that do not extend `Y` are ignored | `StartChain`: if every live lock block and `Y` are pairwise compatible, the start extends every live lock block and `Y` (`PCAnchorFacts` plus the chain hypothesis) |
| `anc_getHead` (`Lemmas/AC/Steps/Core.lean:21`) | statement re-typed to `headFrom` at the start; the hypothesis "every live lock block is compatible with `C`" gains "and the base" | the same proof through `StartChain` |
| `anc_getHead_of_compat` (`Lemmas/AC/Steps/HeadLock.lean:24`) | the candidate `C` must be a live lock block, `fc_root` **or the base** | add the base arm; hypotheses as above |
| `getAnchor_viable` (`Lemmas/Healing/Geo.lean:485`) | holds at trivial frames only; with frames, the base must be clamped into the viable tree, which this layer does not model | out of scope until the frame clamp is modelled |
| the emission's `DutyHead.start` equal to `getAnchor` of the read point (`Lemmas/AC/ReadPoint.lean`, `Lemmas/AC/Steps/Emission.lean`) | breaks | `start = startOf (u i) (a i)` |
| Tier A's joint invariant (`anc_getHead_of_floorAC`, `vote_extends_of_protAC`, `readPoint_liveLockBlocks_compatible_atAC`) | breaks for the `some` arm: "the anchor extends every live floor block" read off the locks | `StartAboveFloor` for a live floor lock, `HeadAboveFloor` for a floor that is not a live lock (below) |
| the anchor cases (`Lemmas/Healing/AC/Unanimity/Anchor.lean`) | need a third arm, "the base `Y`, or a live lock extending `Y`" | consumes a settled field for bases (every base at a call from the floor on is extended by every later honest vote and proposal head), beside the settled locks |
| structural lemmas: handler shape, pool admission and views, lock-store laws, provenance of a write from its update, expiry arithmetic, the unlock relation | port as they are: they hold for every start | re-typing only |
| head-dependent invariants: every statement about which blocks honest votes, proposals, optimistic locks, records, saved rows and counts land on (vote transfer, drain and good-origin transfer, same-slot compatibility of results, settled locks, unanimity) | do not port as they are: the own vote's head, and through it the pool and the writes of the same call and of later updates, depend on the start | the same statements under the new run law with `a` and `AnchorRel`, plus the start fields below |

The replacement fields at the AC level are **sufficient obligations to establish**, not equivalent restatements of
the parent's facts:

- **`StartAboveFloor`** (for a floor block `P` that is a live lock at the read point): at every honest vote or
  proposal call from the floor slot on, the call's start extends `P`. Under the PC this follows, for a base `Y` of
  the call, from `Y` compatible with `P` together with the live lock blocks extending `Y` lying on one chain (then
  the start, the deepest of them or `Y`, extends `P` when `P ⪯ Y`, and is `⪰` the live lock `P` when `Y ⪯ P`).
- **`HeadAboveFloor`** (for a floor block `P` that is not a live lock): at every such call, the head extends `P`.
  This is a distinct obligation: it is the per-call condition PC-KEEP-FLOOR(P) (the base compatible with `P`, and
  the walk from the start reaching `P` when the base is a strict ancestor of `P`). That the walk reaches `P` does
  not make the start extend `P`.
- **`StartChain`** (the `anc_getAnchor` form): at the read point, every live lock block and every base are
  pairwise compatible. It follows from the settled locks and the settled bases as soon as a later honest vote
  exists, since every lock and every base is then an ancestor of that vote's head.

None of these is proved by this layer; they are the settling route's outputs. In a PC instance of Tier A's joint
invariant, `StartAboveFloor` is a second per-call premise beside the floor-keep premise; the generic induction is
unchanged.

**A later statement question: the Tier A read.** Tier A's read statement reads `acConfirmed` of the call's
post-state. Under the PC that read evaluates the store, so a PC Tier A profile needs the read oracle above (or a
read statement over the PC state with `Φ` and `T` explicit), and cannot reuse the protected-ready statement
verbatim.

## Lemmas this layer already gives the plan

- `PCPathSameState`: a start on the parent's walk changes no head (the memoryless walk).
- `PCAnchorFacts`, `PCBaseFacts`, `PCProjFacts`: the start extends the base; the base is the deepest D21
  projection of an authoritative key; the projection is the code's upward walk.
- `AuthorityCompatible`: authoritative targets are pairwise compatible (annihilation), so the projected targets
  of one call lie on one chain (both projections are ancestors of the deeper target).
- `KeyProvenance`: a key has an honest acker with a fast-test decision, the input of `AnchorRel`.
- `ProjStateCore` (proved): the forgotten trace's states are the core's.
- `CoreStepAtCallStart`, `ProposalAtCallStart` (stated, proofs pending): each call is the core skeleton at its named
  start `callStartPC`; `a` and `AnchorRel` abstract that start's base.

## Size

The second-pass estimate for this row stands at 3,500–5,500 lines (the census's 19 files that use `getAnchor` or
`getHead` in the AC and Healing cones, plus the mechanical re-typing of the rest); folding it into the write-mode
re-typing would have cost 2,000–3,500.
