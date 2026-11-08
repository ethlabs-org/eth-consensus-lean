# ½ pre-confirmations: statement plan for an anchor oracle in the AC cone

A plan only. No cone file changes with it; whether and when the cone is re-typed is decided with the cone's
owners, after the in-place write-mode re-typing has landed. The definitions it builds on are in
`ConsensusLean/Instances/Goldilocks/Milestones/Spec/Candidates/PreConfirmations/` (the PC store, the start
function `pcStart`, the core skeleton with a start `…EMAt`, the forgotten trace `projTracePC`). Paths below are
relative to `ConsensusLean/Instances/Goldilocks/`.

## What the PC changes in the cone

The ½-PC layer writes no lock, no record and no saved row (`CoreStepAtStart`, `CoreStepOfNoKeys` in
`Candidates/PreConfirmations/Statements`). It changes one input of the head walk: the block the walk starts from.
With an authoritative key, the start is `pcAnchor A Φ t Y`, the deepest live lock block extending the base `Y`,
or `Y`; without one it is the parent's `getAnchor A Φ t`. So every cone theorem about writes, the pool, lock
provenance, origins, expiry and same-slot compatibility is untouched; the head and anchor family is not.

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
- the parent is `a := fun _ => none`, and `ACLocalRunU m u` is `ACLocalRunUA m u (fun _ => none)` by `rfl` (or an
  `Iff.rfl` lemma if `ACLocalRunU` stays a separate structure).

Because the oracle is a separate argument, it changes only the calls that walk (`tryVoteWithM`,
`acProposalWithM`) and the run law's `exec` field. A `WriteMode` field would instead change every `stepWithM`,
`callInputM` and `callViewM` call site, and the anchor is a read, not a write. Keeping `stepWithM m u` as an
abbreviation of the new step at `a = none` keeps the existing call sites unchanged.

**Reads are not cuts.** `ac_head` and `ac_confirmed` are functions of the state, read at arbitrary points (by the
FG, by the confirmed-tip lemmas). Under the PC they evaluate the store, which the forgotten trace does not carry.
The cut oracle `a` covers the votes and proposals; a read needs either a read oracle indexed by node and cut, or
the read-side statements stated over the PC trace. `Lemmas/Healing/AC/Confirmed.lean` (the confirmed tip extends
the head) is the consumer that needs this.

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
| Tier A's joint invariant (`anc_getHead_of_floorAC`, `vote_extends_of_protAC`, `readPoint_liveLockBlocks_compatible_atAC`) | breaks for the `some` arm: "the anchor extends every live floor block" read off the locks | `StartAboveFloor`: at every honest head call from the floor slot on, the call's start extends every live floor block |
| the anchor cases (`Lemmas/Healing/AC/Unanimity/Anchor.lean`) | need a third arm, "the base `Y`, or a live lock extending `Y`" | consumes a settled field for bases (every base at a call from the floor on is extended by every later honest vote and proposal head), beside the settled locks |
| write, pool, provenance, origin, expiry and same-slot lemmas | untouched | none |

The replacement invariant at the AC level is therefore one field with two consumers:

- **`StartAboveFloor`** (the joint invariant's form): at every honest vote or proposal call from the floor slot
  on, the start extends every live floor block. Under the PC it needs, for every authoritative base `Y` of the
  call, `Y` compatible with the floor block `P`, and the walk from the start reaching `P` when `Y` is a strict
  ancestor of `P` (the per-call condition PC-KEEP-FLOOR(P)).
- **`StartChain`** (the `anc_getAnchor` form): at the read point, every live lock block and every base are
  pairwise compatible. It follows from the settled locks and the settled bases as soon as a later honest vote
  exists, since every lock and every base is then an ancestor of that vote's head.

Neither field is proved by this layer; both are the settling route's outputs.

## Lemmas this layer already gives the plan

- `PCPathSameState`: a start on the parent's walk changes no head (the memoryless walk).
- `PCAnchorFacts`, `PCBaseFacts`, `PCProjFacts`: the start extends the base; the base is the deepest D21
  projection of an authoritative key; the projection is the code's upward walk.
- `AuthorityCompatible`: authoritative targets are pairwise compatible (annihilation), so the projected targets
  of one call lie on one chain (both projections are ancestors of the deeper target).
- `KeyProvenance`: a key has an honest acker with a fast-test decision, the input of `AnchorRel`.
- `CoreStepAtStart`, `ProjStateCore`: the forgotten trace's states are the core's, and each call is the core
  skeleton at some start; with `a` and `AnchorRel` that start is named.

## Size

The second-pass estimate for this row stands at 3,500–5,500 lines (the census's 19 files that use `getAnchor` or
`getHead` in the AC and Healing cones, plus the mechanical re-typing of the rest); folding it into the write-mode
re-typing would have cost 2,000–3,500.
