# FG-SA blueprint: foundations

_Date: 2026-10-01. Authority and notation: [00-outline.md](00-outline.md)._

Rule authority: [the current spec](../spec/fgsa-protocol.tex), SHA-256
`a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.

The window rules use spec 031a7f9f, `par:r6-window` and `alg:chain-full`.
Explicit older line citations below retain their archive numbering.
[FW](../codex/reports/fdelay-window.md) §§1–5 and the
[review fixes](../codex/reports/spec-window-fix-full.md) §§3–5 supply the
window changes. Old Lean names below identify proof patterns, not window
implementations or a checked transfer. The HEIGHT BRIDGE below transfers
only height fields on fixed block data.

Historical spec line citations use the 4e85ff34 numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the earlier spec c1ea1db0 changed only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.
The no-round delta below uses frozen spec bf46ae7f; its citations name
that archive. Negative executions have the status stated in 00 §3.5.

Citations marked 4e85ff34 refer to the archived numbering above.

## 1. Proof boundary and elementary facts

This file proves the stage-1 foundation statements. “REUSE” identifies an
existing pure argument. “NEW” identifies a proof about the composed
transitions. Neither mark asserts a compiled FG-SA run theorem.
Sections 1.1–1.2 also state conditional services for the stage-2 healing
interface. Their T-ROWS proof does not use H2; 21 H.22 uses only that
proof, so these references do not form a proof cycle.

All tree reasoning uses these facts: ancestry is reflexive and transitive;
two ancestors of one block are comparable; an ancestor of an admitted
block is admitted; strict ancestry increases depth. The last storage fact
will be derived in §4 rather than assumed for arbitrary stores.

The C* bijection is used only in proofs to count seats. It preserves
cardinality, identifies at most a faulty seats at one label, and ensures
that an honest seat has at most one label vote. It is not read by base code.

**Count facts (NEW elementary arithmetic).**
If a<h≤n−a, then 2a<n. For integer a this gives
a<⌈n/2⌉=τ. Since n/2≤2n/3, τ≤q_F, so a<q_F.
If a≤f=⌊(n−1)/3⌋, write n as 3m, 3m+1, or 3m+2:

- n=3m: f=m−1, q_F=2m, 2q_F−n=m>a.
- n=3m+1: f=m, q_F=2m+1, 2q_F−n=m+1>a.
- n=3m+2: f=m, q_F=2m+2, 2q_F−n=m+2>a.

Thus a≤f implies 2q_F−n>a. This is distinct from the Clean inequality
a<q_F. The proof must not discard a slashing-evidence branch in Clean by
using the stronger inequality.

### 1.1 AC→FG values and the carrier chain

Outline id: `bp.channel.v2`.

The shared substrate is the cumulative admitted tree `Σ.T`, with immutable
chain states and receipt stamps. Write `D(X)` for the FG filter applied
to a block set X with the controls of the current event. This operator
does not compute its controls from X. The letter T in `T-SRC` and
`T-ROWS` names a channel; `Σ.T` names the stored tree.

Use this partition: the minimal AC→FG channel consists of source
candidates/C_fg and the carrier chain. The joint functions are
`live_root`, HEAD eligibility, `C_fg`, the proposer head, and the
finality head with its triple `(h_j,J,h_F)`. The finality pair is the
FG client function `finality_pair` applied to that triple (current spec
line 1668); it is not a separate selection. This composition layer
reads the
substrate vote pools directly where a selection needs votes, as the
spec's `get_fg_vote` and `propose_block` do. The individual functions
retain their specified arguments; this does not add a vote argument to
`live_root` or `C_fg`. The proposer head uses the previous-slot pool;
the finality head uses the current-slot pool.

The two AC→FG parts are:

1. **T-SRC — source candidates.** At an honest action `a_r`, AC supplies
   `X_r={B∈fastWrite[rR] : lease[B]>a_r}`. The joint selector returns
   `C_fg=deepest(X_r∩D(Σ.T))`, or none. Candidates are prefixes of one
   successful raw result, with surviving early support at least τ. A
   selected candidate is an actual source even if the FG client returns
   no row. Section 8.4 proves these source-origin facts.
2. **T-XFER and T-ROWS — carrier chain and row service.** Under the
   post-reset contract of 21 H.22, a high honest source K of label s
   satisfies `K⪯parent(Q)` for every honest proposal Q at slot `v≥s+2`.
   An honest proposal carries every honest row its proposer holds that
   is R6-valid for its parent. Here “holds” means in the pool or in an
   admitted block. The exception is an exact row already on its
   parent's chain, or a row whose every effect is already supplied as
   proved below. Thus a newly carried row is folded on a chain that
   extends K. The parent bound is essential: source compatibility alone
   does not put a row on this chain.

**Composition→FG values.** The joint selectors supply `C_fg`, the
finality-head triple `(h_j,J,h_F)`, and the carrier parent chosen by the
joint proposer head. The triple is an input to the FG client even when
there is no source. The carrier parent determines the chain with T-ROWS.

**T-ROWS — honest-row service.** Every honest proposal supplies every
effect of each held honest R6-window row, through carriage, a parent bit,
or the final effect-preserving selected set. Held means in the pool or
an admitted block. R6-window is HeightMatch or StaleUseful (01 §1.1).
The optional selection keeps at most 1+K_W rows per identity and every
candidate effect; it does not prune pools. No one-row-per-identity
reduction is allowed. An honest row sent at t is held at every honest
node before max(t,GST)+Δ_F. Honest acceptance starts the same relay
duty from its acceptance time. Receipt includes sleeping receivers.
At a_r≥GST the row is held before a_r+Δ_F≤T_r+β, where
κ=ceil((6Δ+Δ_F)/(4Δ)) and β=4κΔ=β_F. An honest proposal from
slot rR+κ supplies its effects when eligible. Under H2 its parent
extends the source K, since κ≥2. Height bits require HeightMatch and
persist while (h,T_h) matches; stale carriage gives no height bit.
An exact window-entry bit persists while that entry is retained.
Finality deletion gives coverage; capacity eviction does not. Finality
service needs retention or coverage, not fixed latest J. Exact-row
exclusion and optional omission are sound by 01 §1.1. There is no row
age or row-round premise. SO-COV gives height coverage only; a finality
batch needs actual fresh higher-height emissions. A carried row arrives
with its complete block under Δ.

**T-ROWS proof (R6-window and R7).** For one common parent post-state σ,
with its working slot set to the child slot, define

```text
HeightMatch(a,σ) := (a.h,a.T)=(σ.h,σ.T_h).
WindowMatch(a,σ) := a.finality_pair=(j,X) for some (j,X,Q_i)∈σ.𝒲.
StaleUseful(a,σ) := a has a nonempty height pair, a.h_f<a.h<σ.h,
                    and WindowMatch(a,σ).
R6W(a,σ) := HeightMatch(a,σ) or StaleUseful(a,σ).
```

Authentication, identity, and field checks still apply. The current-height
arm needs no finality match. The stale arm admits no future height and no
wrong entry at the current height. It sets no target or progress bit.
Thus R6 validity alone no longer implies a progress effect or independence
from the finality pair. Both old corollaries need HeightMatch.

R7 selects valid full-content rows from the pool and admitted blocks,
removes exact duplicates and exact rows already on the parent chain,
and leaves their order unspecified. There is no age test
or one-row-per-identity reduction. Several rows of one identity can serve
different retained entries and the current height.

C1 (§10) gives receipt before max(t,GST)+Δ_F for a row sent at t,
including sleeping receivers and pre-GST sends. Put
κ=ceil((6Δ+Δ_F)/(4Δ)) and β=4κΔ. For a_r≥GST, all honest nodes
hold the row before a_r+Δ_F≤T_r+β. An honest proposal from slot
rR+κ supplies its effects if R6-valid. Height coverage uses HeightMatch
and bits that persist while (h,T_h) remains fixed. Finality coverage uses
an exact retained entry (j,X), with bits that persist while it remains in
𝒲. Finality deletion gives ancestor coverage; capacity eviction does not.
The finality service therefore needs retention or prior finality coverage.

**Exact-row exclusion, including the stale arm.** At a row's first
carriage, a.h≤σ.h and, for a nonempty finality pair, a.h_f<a.h.
An empty finality pair has no finality effect. If its entry exists, the fold sets
its identity bit before height events. The bit persists while retained.
An entry deleted by finalization is covered by F; an entry evicted by
capacity never returns. If the entry was absent, later justifications
have height at least this σ.h, so cannot create the lower a.h_f entry.
Its height bit either persists at the same entry or its old height has
been left forever. A row first carried through the stale arm already has
an old height and cannot later acquire a height effect. Thus an exact
row on the parent chain has no missing later effect on that chain.
This proof uses monotone height and entry birth at the current height;
it would not justify future-height admission.

**Effect-preserving selection (optional).** The final selected set must
supply every candidate effect, together with bits already in the parent.
For each identity, choose one current-height target if needed (it gives
both target and progress), or one timeout for progress if no target is
needed. For each retained entry whose bit is still missing, choose one
row with that exact finality pair. There are at most 1+K_W selected rows
per identity. A chosen row can meet several of these obligations.
Validation uses the same parent, and the fold changes no entry keys.
It only takes unions of identity bits. Hence this selection gives exactly
the full candidate fold, including its pre-height marker reads, greatest-
ready test, and later height events. Two omitted rows cannot cover each
other unless the final selected set actually supplies their effects.
The preceding exclusion proof applies to every omitted row: covered bits
persist, old height effects cannot return, and missing lower entries cannot
be born later. This option changes the carried list, not pool retention.
It proves fold equivalence at fixed child geometry; it does not equate
roots of blocks with different committed bodies.

Pool pruning requires a separate proof that all admitted descendants keep
row service and required marker reads. A height cutoff is insufficient:
let immutable σ[X] have h=4 and retain (2,U,Q_i), and let a row of height 3
name (2,U) with its bit absent. Even after local Σ.F becomes X, a new child
of X can admit this stale row and change its bits and leak markers.
Deleting the row because 3<ht(X) loses that effect. The proposed
ancestor-or-equal, no-height-effect pruning rule remains OPEN.

H2′ and the HEAD clauses of H2.A and H3 are AC services to the joint
selections (not FG inputs). “HEAD votes are not a third AC→FG stream”
holds for this partition only: the finality head reads HEAD votes
through the joint function. It uses those votes and `live_root` with
the FG domain and band, then supplies its immutable `(h_j,J,h_F)` to
the FG client. In particular the finality head need not equal C_fg.

### 1.2 Composition services for the joint selections

Outline id: `bp.jointServices.v2`.

For the recovery services below use `a≤f`, `h=n−a`, all honest nodes
awake, and strict receipt after GST. Apply vote timing only to labels
whose vote times are after GST. The output claims require the healed
suffix or the exact-service range stated in 21 H.22.

`S` means the local available-output register, `latest_confirmed`. It
is written by the AC gate and by reconciliation with F. Its value and
the finality head are used through the following composition facts.
They are not extra values in the minimal AC→FG channel.

- **T-START.** At every event index e of an honest node x, every live
  lease target B satisfies `B⪯S_x(e)`. Evaluating `live_root` in this
  state gives Z or such a target B in `D(Σ.T)`. This is an invariant
  at all event reads, not only reads made by `get_head`.
- **T-SMONO.** On the healed suffix, each local S is monotone at event
  reads. This is the local clause of 21 H4, including reconciliation.
- **T-EXACT.** At an honest proposal Q of slot `v≥s*+2`, post-gate
  `S_x(d_v)=Q`; at an opening the joint selector gives `C_fg=Q`.
  H3 also gives exact slot-v HEADs, an AC service to the joint selections
  used by FF1, F6, F8, Q0 and QF4 S2, and a successful fresh fast write.
  These are
  separate fields of 21 H3. The gate value can bound an earlier S by
  T-SMONO; no earlier event reads it.
- **T-VOTE (composition service).** Proved from AC vote duties, pool
  admission and receipt. Under the awake and strict receipt premises,
  full proposal reads at t_v hold all honest label-(v−1) votes, and
  action reads at a_r hold all honest label-(rR+1) votes. Their heads
  resolve when the required paths are admitted; admission or finality
  coverage must be checked. A signed label-i vote names a block held
  at v_i. The proposal read is 3Δ after the preceding vote duty; the
  action read is Δ after its vote duty. Strict delivery precedes both.
- **T-WALK (composition).** Suppose Q is in the full filtered domain,
  the live start is compatible with Q, and all h honest votes at the
  read's label resolve to heads extending Q. Then the full head covers
  Q. If there is no admitted proper descendant of Q, the head is Q.
  At a read with all h honest seats participating, a selected child with
  no honest supporter needs the current-slot arm or a parent of height
  below the current lo.

**T-START lemma and proof (paper source for F1.8).** Use the initialized
run and the S-write rules of §7 and 22 I5. Initially there is no lease.
Induct on every local event index. Expiry and release only remove
leases. At a successful gate with result C, new targets precede C.
If `C⪯old S`, advance keeps S, so these targets precede S. Otherwise
advance sets `S=C`. The guard makes every old target compatible with C.
An old target strictly above C would put `C⪯old S` by the induction
hypothesis, which contradicts this branch. Hence each old target also
precedes C. Empty, vetoed, and saved gates add no target.
Reconciliation removes incompatible targets. If normalization sets
`S=F`, a surviving target B is compatible with F. If `F≺B`, then
`B⪯old S` implies `F⪯old S`, and normalization would not set S.
Thus `B⪯F`. This also covers normalization after an empty or vetoed
gate. All other handlers preserve S and add no lease. The definition
of `live_root` selects Z or a live target in the full filtered domain,
which proves its clause at every event index. No healed-suffix or
vote-timing premise is needed for T-START itself. ∎

**T-WALK proof.** If the start covers Q, every continuation covers Q.
Otherwise start⪯Q. Each path child to Q is viable, has score at least h,
and beats a competing child of score at most a. Its majority test passes
since `2h>n`. Induction reaches Q. No-descendant gives the exact form.
For a child with no honest supporter, let p≤a count its faulty supporters
and equivocators. All h honest seats participate and are disjoint from
these p seats, so the denominator is at least h+p. A strict majority
would require `2p>h+p`, hence p>h, which is false. The other two
eligibility arms are therefore necessary. These proofs use the current
FG floor at the same read. The exact form is 22 I8; the coverage and
unsupported-child forms are also needed in 22 F6/F8 and FL-T7.

This boundary permits a conditional FG kernel with explicit joint
selection services. Source candidates and carrier ancestry alone do
not prove the required action-head or carrier-parent state. Chapter
22 §2.1 lists each direct HEAD use in the present composition proof.

### 1.3 FG channel facts over run events

R-XING and R-CAP quantify over blocks that honest nodes hold at a read.
Each such block has an authenticated finite parent chain and row origins.
W and the accepted finalization carrier are honestly held; RD2 scope
therefore supplies RootInjectiveOn on both compared chains.
For a block first exposed at a later read, apply the same statement at
that later prefix. These statements require no extra "private block"
constructor or run log of faulty emissions.

**R-XING — finalized crossing.** Under `a≤f` and honest client
discipline, for every honest x and event index e, let W be a block
that an honest node holds at a read `e′≥e`. Then
`ht(W)>finheight(F_x(e))` implies `F_x(e)⪯W`. Here finheight is the
accepted certificate's entry height, with 0 for genesis. W can be
outside an active view. Proof: §8.2 (`fg.finalLock.v3`), 21 IF.3(c),
and 22 I4. If F is genesis, ancestry is immediate. Otherwise the
finality QC and the crossing QC have an honest common identity; an
incompatible entry would violate E1. All used rows have run origins.

**R-CAP — causal height cap.** Under `q_F>a` and authentic row origins,
for `y≥0`, every block W that an honest node holds at a read e′, with
`ht(W)≥y+2`, carries on its parent chain an honest height row at
height y+1. That row was emitted before e′. Hence, if no honest row at
height at least y+1 is emitted before t, no honest node holds a block
of height at least y+2 before t. Such a block held later carries a row
emitted at or after t.

**Proof.** Follow W's parent chain to the first crossing of y+1. I1
and certificate provenance give a target or progress QC with q_F
distinct identities. At least one is honest. Its height row at y+1
was emitted before the carrier, hence before the read e′. The row need
not be in an honest pool at e′. Uses in 21 H.11–H.12 and 22 FF1-A
compare the honest row's emission time with t; a block first held
later is checked at that later read.

## 2. Carrier bridge — bp.carrier.v1 (K5)

### 2.1 Two projections

FullBlock is the full recursive NamedProposal. It retains each ancestor's body, ordered signed
rows, raw HEAD list, and support list. HEADs name root identifiers. The six-field digest uses the
parent root, slot, application value, signed rows, raw HEADs, and support HEADs. Ingress and
admission check it and the body encoding. Define fg and erase by recursion through the named
parent; eraseFG(fg(B))=erase(B) on checked named chains. These projections retain geometry and
encoded row content but need not retain HEAD lists. The run scope starts with every delivered
named proposal and every proposal held by an honest node at an event prefix, then closes under
named ancestors. Equal roots in that scope imply equal full recursive proposals. There is no
global injectivity theorem for arbitrary Block, FGBlock, or NamedProposal values. A HEAD-only
identifier or an emitted-only tip is not an extra seed. Genesis enters through holding or ancestry.

### 2.2 Proof

**NEW, with the forward-recursion pattern reused from DC.**

1. Slot, root and parent preservation follow by cases on genesis/node.
   In the node case erase simply applies itself to the parent.
2. Suppose X⪯Y. Induct on Y. If X=Y, erasures are equal. Otherwise
   X⪯parent(Y). The induction hypothesis gives erased ancestry to
   erase(parent(Y)); append the last parent edge. This is the proof shape
   of DC.Proofs.NamedWire.erase_preceq.
3. For scoped named X,Y, equal erasures give equal roots, so the named premise gives X=Y, with
   every signed list at every ancestor. This is the named erasure-injection step.
4. To reflect erased ancestry, lift the erased ancestor to an actual named ancestor of Y.
   Both it and X are scoped. Equal erasures then give named equality by step 3.
5. The two ancestry directions give compatibility reflection.
6. For admitted FG projections, local admission gives ViewRootInj. Across stores, use full named
   scope and projection. A pure two-chain theorem takes RootInjectiveOn explicitly; the run premise
   supplies it only after both required chains are covered. Independently, eraseFG is structurally
   injective and reflects FGBlock ancestry through the retained BODY codec.

The projection does not change quorum signers or pair equality. It removes
no pair occurrence from the mathematical signed history. Use full row
positions to lift an FG certificate back to the real run.

## 3. Chain invariants and certificates — bp.chainCertificates.v2

Let σ_B be the deterministic post-state of B. Its derivation is independent
of when B is received. State is copied from the parent, with the new slot,
then full rows are folded, then L:=B and height events run.

### 3.1 Induction on the window chain (NEW)

Maintain F⪯J⪯T_h⪯L, 0≤h_F≤h_j<h, h≥1, ht(T_h)=h, and

```text
𝒲=[(j_0,J_0,Q_0),…,(j_m,J_m,Q_m)],  0≤|𝒲|≤K_W,
h_F<j_0<…<j_m≤h_j<h,  Q_i⊆V.
```

K_W≥2 is the window capacity, distinct from the lease parameter k.
Every retained pair is a justification that occurred on this chain.
Its entry is between F and J by ancestry. Entries increase by certificate
height along that path; they need not have distinct block bodies
(genesis can be justified at height 1). Maintain these witnesses:

- Each target bit has a carried target row for exactly (h,T_h).
- Each progress bit has a carried row for exactly (h,T_h), with either flag.
- Each identity in Q_i has a carried finality pair exactly (j_i,J_i),
  since that entry's birth; that birth supplies its target QC.

Initially 𝒲 is empty, all height bits are empty, all anchors are g,
h=1 and h_j=h_F=0. Validate all rows against one parent before folding.
The fold changes only bit sets. Attach the exact signed row as a witness
for every added bit and retain all old witnesses. A stale row changes
only its matching window bit. No entry is added during this fold.

At height events:

1. Choose the greatest j among ready entries (|Q_i|≥q_F). If there is
   one, set (h_F,F)=(j,J_i). It has its own earlier target QC and exact
   finality QC. Chain order gives old F⪯new F⪯J and increasing h_F.
2. Delete entries at heights ≤h_F. A deleted lower entry need not have
   its own finality QC: the chosen descendant covers its ledger content.
3. If target quorum holds, set (h_j,J)=(h,T_h), append (h,T_h,∅),
   and keep the newest K_W entries. The appended height exceeds every
   old entry height and h_F. Advance once, set T_h:=B, and clear only
   target/progress bits. No carried row is reapplied to the new entry.
4. Otherwise, mature progress advances once with the same height-bit
   clear, and with no window append or clear. With neither crossing,
   height and entry stay fixed.

These cases preserve order, ancestry, capacity, and all witnesses.
They also prove height monotonicity, the one-step bound, and constant
entry on an equal-height plateau. Latest (h_j,J) stays separate even
when its own window entry is deleted. A capacity-evicted entry cannot
return: every later birth has a greater certificate height. Eviction
is not finality. Each post-state retained entry is below quorum, since
the greatest ready test deletes every ready entry and a new entry is empty.
Old σ[B] values do not change when a local cache later advances F.

**Fold permutation and duplicates.** With parent keys fixed, each row
unions singleton identities into a fixed set of coordinates. Union is
commutative and idempotent. Induction over the row list gives the same
bit sets for any permutation or duplicate removal. All subsequent tests,
pruning, and capacity eviction are deterministic, so their results agree
at fixed child geometry. One identity still counts only once per entry,
although its rows can set bits in several entries. This also proves the
fold and marker-read equivalence used by §1.1.

### 3.1a HEIGHT BRIDGE — bp.heightBridge.v1 (PROVED-paper)

For the same original block tree, fixed parameters, and nj=false, the
height fields of the window derive equal those of the latest-only derive:

```text
H(σ) := (σ.h,σ.T_h,σ.h_j,σ.J,σ.target,σ.progress,σ.s,σ.L).
H(derive_window(B)) = H(derive_old(B)).
```

The old side is its total raw fold, not an assertion that it accepts all
window-valid wire blocks. No fault or timing premise is needed.

**Proof.** Genesis projections agree. Suppose parent projections agree.
Both folds set the slot to B.slot and use the same (h,T_h) test for each
row. A match sets the same progress bit and, for a target, the same target
bit. A nonmatch, including every stale row, counts nothing in these height
sets. Finality-bit writes preserve H. Induction over the row list therefore
preserves equality. Both transitions set L to the original B. Old finality
and window greatest-ready selection/pruning change no H field. Both then
test the equal target sets before the equal mature-progress test, with the
same slot, entry slot, and timeout. A target event writes the same old
(h,T_h) to (h_j,J); window append and eviction preserve H. Each advance
writes the same h+1 and original B entry and clears the same height bits.
With no advance both keep H. Induction over the original tree proves the
claim. Filtering nonmatching rows in this auxiliary evaluation also
preserves H, since each is an identity step on H. ∎

Do not rebuild a filtered block tree: rows commit to roots, and changing
a block would change the T_h written at its crossing. This bridge gives
no equality of F, h_F, window bits, accepted stores, heads, emissions,
or whole executions. Earlier window finality can change reconciliation.
Keep three interfaces: Height (this bridge and height QC origins), Chain
certificates (the new exact finality provenance), and Store/safety (§§4,8).
F-lock in the last interface keeps its fault and honest-record premises.

### 3.2 Certificate extraction (window provenance NEW; height argument REUSE)

For a crossing of height m on a chain, choose the first block whose state
height is greater than m. Its parent has height exactly m by the one-step
bound. Its target or mature-progress branch has at least q_F true bits.
Take the set Q of their distinct identities. For each identity select the
bit's row witness. Target bits are also progress bits, so both branches
give matching progress rows for the entry at m. This proves
KFG.height_crossing and crossing_matching_quorum.

For a nonzero justification (j,J), take the first chain state that assigns
that pair. It used a target quorum; each distinct identity has a matching
target witness. If a later state retains that pair, retain the witnesses.
If it changes the pair, select the new witnesses. This is
KFG.justification_certificate. J_is_entry identifies J as the height-j
entry, with the genesis convention handled separately.

For a positive finalized pair (m,F), take the first state that assigns it.
The finality branch ran before any new target event. Its greatest ready
entry supplies q_F distinct finality pairs for exactly (m,F). Entry birth
supplies the prior target justification for that same pair. It can be older
than the latest J. Pruning another entry gives no certificate for that entry.
This replaces the old KFG.finality_certificate supplier; the argument does
not apply that latest-only theorem directly to the window derive.

**NEW lift.** Each selected projected row came from a definite full row
position on the original path. Ingress authentication and causal origin
supply its signature and honest emission event when its signer is honest.
Certificate extraction uses full immutable block lists. No source is inferred from a finality pair alone.

## 4. Store and projection — bp.store.v2, bp.frame.v2 (K4)

### 4.1 Store invariant

Use the shape of KFG.StoreInv with σ[B]=derive_window(B), plus immutable
maps and stamps. The old concrete store is not a window implementation:

- T is parent-closed and contains g;
- F∈T;
- H is the maximum state height in T, with minimum 1;
- (j,J) is the lex maximum of all (h_j(B),J(B)) with B∈T and F⪯J(B);
- F⪯J;
- an admitted K satisfies σ[K].F=F.

The selected J is in T by chain order and ancestor closure.
The lex order compares height first, then root. Root uniqueness on the stored view resolves a tie
to one Block. The carrier for F is proof data, not an extra field of protocol state.

### 4.2 Transition proof (NEW)

Induct on completed local events.

**Initialization.** The only block is g. Its state has height 1 and both
checkpoint heights 0. All clauses follow by substitution. The F carrier
is g. Empty maps satisfy all origin and immutability clauses.

**Refused block.** Every refusal returns before insertion, derivation and
unpacking. Therefore every field equals its input value. A checked but
incompatible block supplies no vote or row handler call.

**Accepted block B.** Its parent is already in T. Insert B without removing
anything. Each ancestor of B is B or an ancestor of its parent, so parent
and ancestor closure persist. No old σ or stamp entry is overwritten:
the duplicate check precedes insertion. Its new σ is the same deterministic
chain derivation as in §3.

The base-vote calls do not change T,σ,F,J,j,H. Now consider update_finality:

1. H':=max(H,ht(B)) is precisely the maximum over T∪{B}. It is at least H.
2. Under the old F, old candidates are unchanged. The only new candidate
   is (σ[B].h_j,σ[B].J), and it is eligible exactly when F⪯σ[B].J.
   Comparing it with the previous maximum therefore gives the new maximum.
   The old maximum remains eligible, so the candidate set is nonempty.
   The chosen pair is lexicographically at least the old pair.
3. If the F test fails, F and its old carrier remain. The new maximum
   still extends F, so F⪯J persists.
4. If the F test succeeds, put F':=σ[B].F. Its guard gives F≺F',
   F'⪯J and F' in acceptance viability. Thus F'∈T∪{B}.
   B itself is the new carrier. Chain order also puts F' on B's path.
5. Changing the finality filter from F to F' removes candidates, since
   F⪯F'. It does not remove the selected maximum J, because the guard
   explicitly requires F'⪯J. A maximum over a set remains a maximum
   over a subset that still contains it. The cached pair is therefore
   the correct lex maximum for the new F; no recomputation is needed.
6. Reconcile writes no field used above. The later row-pool calls write
   no such field either.

Thus every admission preserves StoreInv. T grows by at most B. F moves
only to a strict descendant or stays fixed. The pair and H never decrease.

**Vote and row deliveries.** They change only their admitted pools and
new-key stamps. Rejection is a stutter. Existing keys keep their stamps.

**Tick.** The tick changes time/slot and SA fields, and can record the own
FG row. Base self emission is not admission. No tick changes the FG
projection. The next handler still starts with StoreInv.

These cases are exhaustive. They prove local monotonicity and cumulative
storage without a fault bound or synchrony.

### 4.3 Controls and exact projection (NEW)

The projected store is the window store with TF=T, F=F, J=J, h_j=j,
h_max=H and the window derive at every block-state lookup.
For an accepted block, erase base data for the static fold. Row
order and relevant pair fields remain, so induction over the rows gives
σ[B] projected = derive_window(fg(B)). Every guard in the window
on_block is the corresponding composed guard. The old FG.derive and
old store update cannot supply this equation: finality fields can differ.

The composite has extra future-slot, signature and R6 parent-state checks.
If one fails, its projection stutters; do not claim equality with a
static on_block call that omits that input check. If all pass, insertion
and update_finality give exactly the static result.

From StoreInv, the cached H and pair equal frontier and lexMax over T.
Substitution gives storeControls=fjControls(F,T). Contest uses this same
T and the same H,J. A duty then applies filteredFrom to its supplied X.
The live controls must not be recomputed from X.

Reconcile writes no input to this equation. Therefore it cannot change
the frame by itself. An enclosing F update can change the frame; this is
a different operation. The model preserves the cumulative proposal and
row metadata reads. No physical-pruning equivalence is part of K4.

The old KFG.storeInv_on_block and storeControls_eq_fjControls have source proofs.
They had placeholders on an earlier read and were completed in that pass.
That final read checked their accepted/refused cases and maximum-preservation
argument against §4.2. The paper proof adds immutable maps, pools, exact
composite admission checks, and the reconcile projection.

## 5. Active view — bp.activeView.v2

**NEW.** A={B∈T:B⪯F or F⪯B} is a view, not storage.

1. Membership directly gives A⊆T. Since g⪯F and F⪯F, g,F∈A.
2. Let B∈A and C⪯B. C∈T by store closure. If B⪯F, then C⪯F.
   If F⪯B, then C and F are ancestors of B and are comparable.
   Thus C∈A in both cases.
3. Fix T and F⪯F'. If B⪯F', B and F are ancestors of F',
   hence comparable. If F'⪯B, transitivity gives F⪯B.
   Thus A(T,F')⊆A(T,F). New admission can enlarge the actual view,
   so this is not a claim that A shrinks over every event.
4. If F⪯B⪯K with K∈T, then F⪯K; K is active. Every intermediate
   path vertex from F to K is active.
5. If B#F and F⪯F', compatibility of B,F' would imply compatibility
   of B,F: either F'⪯B, or B,F are ancestors of F'. Contradiction.
   Thus a removed conflicting target can never be written again.
6. If K⪯F, every active head is compatible with K. Its active release
   count is zero, and its lease cannot veto an active genuine result.

For unchanged pool and stamps, a retained head keeps its resolution time;
a removed head changes from a finite value to infinity. Late participation
and equivocation are unchanged. An original carried HEAD support declaration
still uses T. A removed head cannot support candidate B≥F: B⪯head
would imply F⪯head. This proves zero contribution on the retained suffix,
not equality of all support sets.

## 6. Leases and reconcile — bp.leaseOrigins.v2, bp.reconcile.v2

### 6.1 Lease shape and origins (NEW port of the SA argument)

Induct over writes, release, expiry and reconcile.

A passing gate has a single result C compatible with every live target.
All new targets are prefixes of C. Hence old and new targets are pairwise
compatible; on a rooted tree they form a chain.

If B is fast-admissible, each non-genesis ancestor A has at least B's
surviving support, so it is fast-admissible too. If B is slow-admissible,
every saved result in its window covers B and therefore A; hence A is
slow-admissible. The write loop contains A by active ancestor closure.
Both get the same new deadline. Taking max preserves the inequality
deadline(A)≥deadline(B) from an earlier write.

If a clean active vote conflicts with A⪯B, it also conflicts with B:
compatibility with B would make it comparable with A. The release-seat
set for A is a subset of that for B, with the same equivocation exclusion.
Thus release of A releases B too. Expiry of A cannot leave B live because
deadline(A)≥deadline(B). Reconcile cannot delete A and retain B:
if B∥F, every ancestor A of B is compatible with F.

Deletion creates no target. Each retained lease retains its earlier
successful-gate origin; each new or renewed lease gets this gate as its
latest origin. This proves the source property, including renewal when
the numerical max did not change.

A fastWrite entry is created only by the fast predicate inside a passing
gate. Initially its label's set is empty. Each member B is a prefix of that
saved genuine body C. Later reconcile can remove B, not insert a new one.
If it empties C for conflict with F, any retained B from that set must
already be compatible with F. Thus the exact persistent origin statement
is historical: there was a successful gate with B⪯C. If C remains
nonempty, it is still that same C. We do not require every historical
fastWrite member to have a present lease.

### 6.2 Exact effects

Let pre be the state immediately after assigning a new F and before
reconcile; let post be its result. For every label r and target B:

- post.lease(B)=pre.lease(B) if B∥F, otherwise absent.
- post.fastWrite(r)={B∈pre.fastWrite(r):B∥F}, with the same domain of labels.
- A missing genuine label remains missing. A present empty label remains
  present and empty. A present body C remains C if C∥F, otherwise becomes
  present and empty.
- post.S=pre.S if F⪯pre.S, otherwise post.S=F.
- T, σ, all stamps, both signed pools, time/slot, Λ, F,J,j,H are equal.

These equations follow by reading the three loops and the final assignment.
They prove evaluated-label preservation, no invented result, no new lease,
and no new fast source. Apply the equations twice: every remaining target
and body is compatible with F and the output extends F. The second
application changes nothing. This proves idempotence.

### 6.3 Harmless reconcile (K1)

Assume the new F is compatible with every live lease, every nonempty saved
result, and S. Live leases and saved bodies survive by §6.2.

For a historical fastWrite member B, select its original successful
result C. If C has never been emptied, the premise gives C∥F, and
B⪯C gives B∥F by comparability of ancestors or transitivity.
If C was emptied by an earlier F₀, then B survived only if B∥F₀.
Since C#F₀ and B⪯C, this forces B⪯F₀: the alternative F₀⪯B
would imply F₀⪯C. Local F monotonicity gives B⪯F₀⪯F.
Thus such an old fastWrite member survives too. This is the needed
historical case; it cannot be omitted from K1.

For S, if F⪯S it stays fixed. Otherwise compatibility gives S⪯F,
so S:=F extends it. No other SA value changes.
K3 is unconditional: reconcile never writes a frame input.

### 6.4 Difference from DC clipping

DC.Protocol.clipGrade walks a conflicting grade back through parents until
it is compatible. clipCache applies grade clipping to cached frames.
FG-SA does not move a conflicting lease to an ancestor and does not replace
a saved result by F. Its analogue is only the separation between cumulative
FG storage and the available-layer state repair. Reuse no DC clipping
equality that would create a new SA source or fill a missing slow-window slot.

### 6.5 Start at F — bp.genuineFromF.v2 (NEW, PROVED-paper)

**Statement.** Compare the genesis-start rule with the F-start rule, each
with the final strict-majority test. On the same legal gate input, with
F fixed at that gate, their results satisfy

```text
C_F = C_g  if C_g ≠ ⊥ and F ⪯ C_g;
C_F = ⊥    otherwise.
```

Pair executions from the same initialization with equal public ticks,
awake schedules, checked inputs, delivery order, choices of block contents,
and signing randomness. At every completed event:

- Trees, chain states, pools, stamps, clocks, F, J, h_max, S, and Λ agree.
- Evaluated genuine labels agree. A saved-result difference has the form
  old=C, new=⊥, where C is a strict ancestor of current F.
- On D_F={B∈Σ.T:F⪯B}, leases, exact deadlines, and every fastWrite set
  agree. Any difference lies on a strict ancestor of F.
- External traces agree: available and finalized outputs, honest messages,
  and honest duty choices are equal.

**Proof.** At each strict ancestor of F, the active tree has exactly one
active child, toward F. Confirmation support has at most one vote per
seat and is used in both score arguments. Thus the score is prefix
support p, without an equivocation bonus, and cannot increase down a path.
The late denominator N is fixed. If 2p(F)>N, every ancestor of F is
eligible, so the genesis walk reaches F. The two suffix walks then agree.
If 2p(F)≤N, no descendant of F is eligible. The new final test returns
⊥, and the old result is either ⊥ or a strict ancestor of F. This proves
the gate relation without a synchrony or fault premise.

Induct over complete events for the execution relation. At a retained
gate, old lease differences are ancestors of F and cannot veto the result.
For B∈D_F, fast support agrees. A lost saved result C_j obeys
C_j≺F_j⪯F_now⪯B, so it could not cover B in the old slow test either.
Thus slow tests and all writes on D_F agree. At a dropped gate, the old
result C≺F⪯S cannot advance S; all its writes lie strictly below F.
The new empty branch leaves S fixed too. Both versions normalize S alike.
Local differences include dropped ancestor fastWrite entries and lease
writes, and lost ancestor slow renewals even at retained gates.

Expiry and release use the same time and evidence. Reconciliation uses
the same new F. Since F moves only forward, no ancestor difference can
enter a later D_F. All choice trees contain only descendants of F, so
their live roots, HEADs, proposal parents, and fresh FG sources agree.
Signed pools, carried support, rows, chain transitions, Λ, and ledger
inputs therefore agree. This closes the event induction in both directions.
The prefix-write loop is unchanged, so §6.1's full ancestor closure holds.

**Transfer.** Equal external traces under equal schedules transfer every
output-level theorem, bound, and lower-bound witness. Local-state claims
use equality on D_F. In particular, new H3 implies old H3 in the paired
execution: a nonempty new result Q is the same old result, its guard
and fast write agree, and C_fg=Q agrees. Thus the conditional general-delay
claims transfer too. This is a paper correspondence, not a Lean check.
Sources: [r208 §§2–3](../codex/sa-walk-from-f.md) and
[its review §§4–5](../codex/review-sa-walk-from-f.md).

### 6.6 Finality before an honest proposal gate

If an honest slot-s proposal P is active at an honest gate d_s and q_F>a,
then F≺P at that gate. Activity excludes a conflicting F. If P⪯F,
a justification for an entry at or above P needs an honest target row
with a source at or above P. That source belongs to fastWrite[rR] with
rR≥s, so its action is at or after d_s, after the gate in tick order.
It cannot cause F at the gate input. This proves the strict bound.
It applies in Clean, where a<τ≤q_F, and in Recovery.

## 7. Nesting — comp.outputNesting.v3 (K2)

The accessor statement v1 (historical pin) is a two-case proof. If F⪯S, return S.
If not, return F and use reflexivity.

For the window stored statement v3, induct over completed local events.

- Initially F=S=g.
- An F update reconciles before the handler returns. If the old S extends
  the new F it stays; otherwise S is set to that F. In both cases F⪯S.
- A gate result C lies in A. If C⪯F, then C⪯S by the input nesting
  invariant, so advance keeps S. If F⪯C, advance returns either the
  old S or C, both of which extend F. Empty and vetoed results keep S.
  The final normalization also enforces nesting in any input state.
- Expiry, release, pool processing and duties do not change S or F.

Therefore every public read has F⪯S, and the current accessors both return
S. In a reachable normalized state, the final normalization after a gate
is redundant; after an F move it can be necessary. This proves no global
safety or unconditional monotonicity: §11 N1 changes S to a conflicting F.

## 8. FG safety and source discipline

### 8.1 Client safety — bp.clientSafety.v1

**REUSE of a pure client theorem, with an explicit composed-run lift.**
The client guards inspect any supplied source and head fields. They do not
assume a good SA history.

For each height maintain: the first recorded target never changes; a true
timeout bit never becomes false; the first lock cannot change to another
entry; a lock implies no timeout and no different recorded target.
Initially these statements are immediate.

The finality-pair test allows a lock only if the recorded target is empty
or identical, no timeout exists, and the old lock is empty or identical.
The height-pair test first applies this row's own finality lock. It returns
a target only at the source entry. If a lock exists, a different target
is refused. Without a lock, height_pair may return the same target, adopt an empty
target record, or time out; this permission does not imply a new send. Once timeout is true, no later finality pair
at that height is allowed. Recording a permitted row preserves all four
invariants.

For E2, two targets at the same height must equal the first recorded target.
For E1, consider the order of the two relevant emissions. If finality came
first, its permanent lock forbids a timeout or different target. If the
conflicting height pair came first, a timeout bit or different first target
forbids finality. The own-row lock handles both pairs in one emitted row.

These invariants correspond to KFG.RecordInv, RecordExtends, Covers,
not_slashable_of_covers, createRow_noSelfSlash and clientRun_noSlash.
RESTATE (no-round): the proof port must account for the sent set, the
h≤h_f strip before recording, and no row for an empty height pair.
A suppressed send makes no record write. A stripped finality pair makes
no lock write. Apply the record invariant to the rows actually released;
do not identify this client run directly with the old DC run.
Other handlers and reconcile do not write Λ.
Sleep inserts no client input. Therefore honest run signatures cannot be
the slashable identities extracted below.

### 8.2 Crossing and accountability — fg.finalLock.v3, fg.accountable.v2

**REUSE of the certificate argument; window suppliers from §3.**
KFG.finalLock_e1 and accountable are old-fold references, not window imports.
`KFG.accountable` requires `KFG.RootInjectiveOn`.
Supply RootInjectiveOn on the compared FG ancestor chains explicitly. Section 2 derives it from
the full named run premise only when both chains are covered. Unit weights give the identity count.
`DecoupledConsensusModel.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt`
requires `SlashableBound` and root-collision freedom. It proves the
fault-bounded ancestry clause only. The evidence alternative below uses
`KFG.finalLock_e1`. The finalized height is the carrier's `h_F`;
for genesis this can be 0 initially or 1 after its height-1 finalization.
For two quorums Q₁,Q₂⊆V,
|Q₁∩Q₂|=|Q₁|+|Q₂|−|Q₁∪Q₂|≥2q_F−n.

Let D finalize F at height m, and ht(W)>m. Assume RootInjectiveOn D W. If m=0, F=g by the
genesis invariant, so F⪯W. If m>0, §3 supplies a finality quorum
Q_f for (m,F) on D and a progress quorum Q_c matching the height-m
entry E on W. If E=F, that entry is an ancestor of W, so F⪯W.
If E≠F, collision freedom on the compared chains gives different roots. For each i∈Q_f∩Q_c,
select its finality row on D and matching progress row on W.
If the progress row is a timeout, the pair is E1. If it is a target,
it targets E≠F, so the pair is E1. Distinct identities count once.
This proves the evidence alternative of finalLock without any time bound.

**fg.finalLock.v3 — accepted-finalization threshold — PROVED-paper.**
Let an honest node's accepted finalized block at e be F. Define
`finheight(F,e)=0` for genesis, and otherwise the entry height of its
accepted certificate. For every authenticated run block W emitted by
e, assume RootInjectiveOn D W for its accepted certificate carrier D
when F is non-genesis.
If `ht(W)>finheight(F,e)`, then `F⪯W` or the certificate carrier
and W expose at least `2q_F−n` slashable identities. This statement
has no fault bound for the evidence alternative; under `a≤f` and
honest client discipline it gives `F⪯W`.
Premises: Base, RootInjectiveOn D W for non-genesis F, any δ_t≥0, any a, no synchrony.
This explicit premise matches Lean main e1d4232:
`AvailableChainFGSAClaims/Claims/Foundations.lean:260–265` (PureAccountableClaim),
`AvailableChainKitFG/Accountable.lean:223–246,300–301` (finalLock/accountable),
and `AvailableChainKitFG/AccountableCore.lean:75–77` (window certificate form).
Section 2 supplies it when D and W are in the ancestor-closed RD2 run
scope: directly delivered full proposals, honestly held full proposals
at any event prefix, and their ancestors; emission alone is insufficient.

For non-genesis F, its admitted certificate carrier D has
`σ[D].h_F=finheight(F,e)` by provenance; the proof above applies.
For genesis, every block extends F, also when a carrier has `h_F=1`.
This proves exactly the 4e85ff34 threshold (current spec lines 611–614; archive lines 494–497).
The external registry's v1 is pinned to the carrier h_F and to the
DC fault-bounded ancestry theorem. It does not state this normalized
threshold and evidence alternative. Keep that pin as historical text;
v3 supplies the window clause; v1 and v2 stay historical. Lean reuse: `KFG.finalLock_e1` for evidence,
`KFG.finalLock` for the bounded corollary, and an accepted-carrier
wrapper with the genesis case. The wrapper still needs a Lean proof.

Now suppose D₁,D₂ finalize incompatible F₁,F₂, with RootInjectiveOn D₁ D₂.
Premises: Base, RootInjectiveOn D₁ D₂, any δ_t≥0, any a, no synchrony.
Orient their finalized
heights so m₁≤m₂. Since m₂<ht(D₂), apply the crossing result to
D₁,D₂. Its extension alternative would give F₁⪯D₂. Chain order gives
F₂⪯D₂; two ancestors of D₂ are comparable, contrary to F₁#F₂.
Thus evidence of at least 2q_F−n identities exists. This even produces
E1 evidence; the registered E1-or-E2 conclusion is weaker.

For live accepted values, choose the F carriers from §4. The evidence
uses their full authentic rows via §2. These carriers are honestly held,
so RD2 scope supplies RootInjectiveOn. No pool retention or current
active-view membership is needed to establish the mathematical evidence.

### 8.3 Finalized safety — bp.finalizedSafety.v2

At a≤f, §1 gives 2q_F−n>a. §8.1 says every slashable signer is faulty.
A set of more than a such identities cannot fit in the faulty set.
The evidence alternative is impossible, so accepted finalizations are
compatible. Local monotonicity was proved directly from the F guard.
No assumption on δ_t, synchrony, SA leases, or source freshness was used
to close this safety theorem.

A useful Recovery corollary is: an inactive admitted block has height at
most the accepted finalized height m. It cannot supply a maximizing
maximum witness once a carrier above m is present. This is a geometric fact.
It does not say that its carried votes or rows are irrelevant. The
replacement N2 (§11.2) changes HEAD at 720 and S at 800 when metadata
is deleted.

### 8.4 Source discipline — bp.sourceDiscipline.v2 (K6)

**NEW composition proof using the certificate lemmas.**
At action a_r, the preceding scheduled gate is exactly d_(rR).
Its fastWrite[rR] is created even if empty. The selector takes the deepest
member of D_Σ(T)∩fastWrite[rR] whose lease deadline exceeds a_r.
If there is none, the client sends no row. There is no older-set fallback.

If it selects C, §6 gives an actual successful fast write at this gate,
with p(rR,C)≥τ and C a prefix of its genuine result. The selector returns
(ht(C),σ[C].T_h). Inspection of every branch of height_pair shows that
a nonempty output uses this supplied height and this supplied entry:
a repeated timeout names the current entry; a repeated target requires
equality with the record; a lock elsewhere returns empty. The same-row
lock does not invent a different entry. These candidate-level repetitions
do not imply a send. Entry ancestry follows from §3.
The source body is unique by the live target chain and root order.

For a QC with q_F>a, choose a signer outside Faulty. Lift its exact
certificate row to an honest emission (§3.2), then apply the preceding
action proof. Emission precedes the block that consumes the row.
For a window finalization, trace its retained entry to its earlier target
justification and select an honest target signer there. It need not be the
latest J at finalization. Only HeightMatch rows supply a crossing QC; stale
rows supply no height bits. A finality row has a height pair, but that pair
is at a strictly higher height than the finality pair.

At time q_s=t_s+5Δ, every already emitted source gate d_u satisfies
d_u≤q_s, so 4u+6≤4s+5 and u≤s−1. At an honest slot-s proposal
or its same-slot HEAD v_s, the corresponding inequality gives u≤s−2
for s≥1. Before a local gate at d_s, no delivered same-time source row
can be present because the local tick precedes same-time deliveries.
An own action follows that gate. These strict origin inequalities are
the well-founded input of the Clean proof.

## 9. Exact Lean reuse and proof state

Paths below are relative to AC unless marked DC. Declarations in this list
were read; absence of a composed theorem is not absence of the component
arguments. No build or axiom audit was run in this document-only task.

```text
┌────────────────────────────────────────────┬─────────────────────────────────────┐
│ File                                       │ Exact declarations / use            │
├────────────────────────────────────────────┼─────────────────────────────────────┤
│ AvailableChainSimplexFG/Objects.lean       │ FGBlock.preceq; Electorate.q        │
│ AvailableChainSimplexFG/ChainState.lean    │ derive; process_height_events;      │
│                                            │ process_row; advance_height         │
│ AvailableChainSimplexFG/Store.lean         │ Store; on_block; update_finality;   │
│                                            │ activeView; storeControls           │
│ AvailableChainSimplexFG/Frame.lean         │ ViewRootInj; filteredFrom; lexMax   │
│ AvailableChainKitFG/Certificates.lean      │ height_crossing; h_mono;            │
│                                            │ entry_eq_on_plateau;                │
│                                            │ justification_certificate;          │
│                                            │ finality_certificate                │
│ AvailableChainKitFG/Accountable.lean       │ accountable; finalLock;             │
│                                            │ finalLock_e1; RootInjectiveOn       │
│ AvailableChainKitFG/ClientSafety.lean      │ clientRun_noSlash;                  │
│                                            │ createRow_noSelfSlash; RecordInv    │
│ AvailableChainKitFG/Correspondence.lean    │ StoreInv; storeInv_init;            │
│                                            │ storeInv_on_block;                  │
│                                            │ storeControls_eq_fjControls;        │
│                                            │ filteredFrom_Z_mem/viable_child     │
│ AvailableChainGridCO/Proofs/GenuineHistory │ gate_target_origin;                 │
│ .lean                                      │ run_target_genuine_origin           │
│ AvailableChainGridCO/Proofs/ReceiptRelay   │ accepted_head_receipt_before;       │
│ .lean                                      │ handled_head_stamped_or_equivocates │
│ AvailableChainGridCO/Proofs/Transfer.lean  │ TransferReceipts and its algebra    │
│ AvailableChainStatements/Generic/Regimes   │ SleepyRegime; OutageRegime;         │
│ .lean                                      │ FastOutageRegime                    │
│ DC: DecoupledConsensusProofs/Execution/    │ Proofs.NamedWire.erase_preceq;      │
│ Wire.lean                                  │ erase_root/erase_slot/erase_parent  │
│ DC: DecoupledConsensusModel/Execution/     │ Execution.NamedReceipt.excludes,    │
│ Node.lean                                  │ depsPresent, processed              │
│ DC: DecoupledConsensusModel/Protocol/      │ Protocol.clipGrade; clipCache       │
│ Grades.lean                                │ (comparison, not SA implementation) │
│ DC: DecoupledConsensusProofs/Protocol/     │ Proofs.NamedFinalizationBridge.     │
│ ChainState/FinalityComparison.lean         │ finalized_preceq_of_height_lt       │
└────────────────────────────────────────────┴─────────────────────────────────────┘
```

The inspected Certificates, Accountable and ClientSafety theorem bodies
supply the cited pure arguments. Correspondence was completed during this
task; the final read checked storeInv_init, storeInv_on_block,
storeControls_eq_fjControls, filteredFrom_Z_mem and filteredFrom_viable_child.
No sorry/admit proof body remained in AvailableChainKitFG in that check.
This is source inspection, not a new build or composed run certificate.
The current SA regimes use PartialSynchrony and HealthyPrefixDelivery.
The old claim that they still need AcceptedObjectRelay is stale.

## 10. Admission or coverage — bp.receiptCoverage.v2 (K8)

This is a transport lemma, not a compatibility theorem. Fix a protected B,
a receiver y and a required deadline c. Assume B∥F_y at every relevant
transport state, authentic valid paths, receipt premises for the specific
objects, and the required slot windows.

### 10.1 Split at the receiving read (NEW)

If B⪯F_y(c), nesting gives B⪯S_y(c).
Every FG root is F or J with F⪯J. The live root is that root or a
descendant in D(T), and the walk only descends. Thus every FG-domain
HEAD covers B even if its walked tree is empty. Any lease K#B also
conflicts with F_y(c), so it was deleted no later than this coverage.
No new path admission is needed.

Otherwise B∥F_y(c) gives F_y(c)⪯B, strictly when unequal.
Monotonicity gives F_y(t)⪯F_y(c)⪯B for earlier transport times t.
For each required head K≥B, F_y(c)⪯K. DC's relay exclusion is read
at its deadline state; it is false there. Local monotonicity gives
F_y(t)⪯F_y(c)⪯K at every earlier handler call. Apply the same test
to each required path vertex; ancestors below finality are already stored.
Vertices strictly below F_y(t) are already stored, because F_y(t) is
stored with its complete parent path. Do not try to re-admit them with
the strict descendant admission test.

Process remaining path blocks in parent order, with the checked dependencies
guaranteed by the receipt premise. A block that is already held needs no
call. An absent block has its parent, is at a valid nonfuture slot, has a
valid proposer signature and R6 parent-state check, and extends the current F, so it is admitted.
These are the on_block guards, not merely a raw receipt assumption.
The specified dependency-bearing receipt deadline pays no extra Δ per edge.

If F passes B during transport, switch permanently to the first case:
later F only extends it. That switch does not extend c. If compatibility
were to fail, this lemma would no longer apply; Clean and Recovery supply
separate compatibility proofs.

### 10.2 Vote or equivocation (REUSE with new handler-call provenance)

A required slot-r vote is handled at t<c within the current/previous-slot
window. If absent and fewer than two distinct same-seat votes are stored,
it is inserted. If already stored, its original stamp is early enough.
If the cap refuses it, two distinct same-seat votes already exist and have
stamps no later than this pre-cutoff handler call. Those two signatures
remain. This proves exact vote membership or stamped equivocation.
The receiver exclusion never applies to a vote.

A carried vote creates such a call only if its containing block was admitted.
The HEAD merge may read the carried original signature even if that call
was refused by the cap. For reverse relay, either that signature was accepted
at the reader and relayed, or the two earlier cap signatures were accepted
and relayed. At the source, each of those is retained or encounters an
already full cap. In every case the source has the desired signature or
two distinct same-seat signatures by the cutoff.

This is the composed producer for G.accepted_head_receipt_before and
handled_head_stamped_or_equivocates. It does not assume every receipt is
an acceptance. For a clean surviving supporter, the equivocation alternative
is impossible at its source late pool; this will yield exact forward
support in 02 §4.2.

### 10.3 Strict timing used later

**C1, family deadlines.** Honest blocks and HEADs sent at t have strict
receipt deadline max(t,GST)+Δ; honest FG rows use max(t,GST)+Δ_F,
where Δ_F≥Δ>0. Both include pre-GST sends and sleeping receivers.
Relay uses the same family bound from acceptance time, including accepted
objects from faulty senders. Dependencies are present at each handler call.
Only blocks have the stated receiver exclusion; rows never do. Own FG rows
are processed in the action tick; own blocks and HEADs follow receipt.
A complete committed block body, including its rows, arrives within the
block's Δ deadline. There is no later fetch charged to Δ_F. A refused
block supplies no carried-object handler calls. For finite horizons, each
full deadline must fit. P1 uses the corresponding healthy-prefix deadlines,
not a new GST or outage-delivery premise.

The following vote/path inequalities therefore retain Δ. Row service uses
§1.1 instead. Clean, P1, and safety need no Δ_F≤2Δ restriction; their
ports through the revised certificate/store interface are not reviewed.

An early label-s vote/head has receipt before e_s. Its relay deadline is
before e_s+Δ=z_s. A vote in the label-(s+1) HEAD merge is present through
a frozen receipt or an admitted current proposal before or at q_s.
Relay of its vote or its earlier cap evidence is before q_s+Δ=d_s.
The sender tick at q_s precedes same-time deliveries, so its read has no
object first received after that cutoff. Thus forward support and reverse
late evidence coexist at the needed strict times. They are two directions
of a proof, not two sequential delays on one message.

## 11. Exact negatives and their limits

Section 11.2 is an old-fold no-round replacement. All §11 window replays
remain OPEN; these executions give no new window lower bound. Sections 11.1 and 11.3 retain
their REVALIDATE status. The executions use definitions in SA/GridCO,
the FG fold/client, and DC admission, receiver exclusion and finalLock.
They are counterexamples to stronger claims, not to Clean.
The verification record is the integer schedule, the derived tuples,
and the explicit gate counts below. These are paper executions of the
frozen rules, not full FG-SA Lean executions.

All three executions use integer time:
Δ=16,k=2,L=112,R=3,δ_t=6,GST=1000,n=4,a=f=1,
τ=2,q_F=3. Honest identities U=0,V₁=1,V₂=2 are awake; D=3 is faulty.
The proposer slots listed below are faulty. Unlisted proposals can be silent.
All ticks and honest duties run. Delay every unlisted receipt beyond the
prefix. Per-slot seats are the images of identities under the hidden
bijections; honest base code is not given the map. Faulty D may sign each
listed base vote. Full FG rows have no round; the listed actions give their emission times.

### 11.1 N1 — comp.leaseVsFinal.v1

**REVALIDATE (no-round).** The review found no R6 failure here; the
paper argument is retained. A complete current-rule replay remains open.

Roots: g=0,A=10,X=20,Y=30,Y₁=50,Y₂=60.

```text
┌──────┬────────────────────────────────────────────────────────────────────┐
│ Time │ Event                                                              │
├──────┼────────────────────────────────────────────────────────────────────┤
│ 192  │ Propose A, slot 3, parent g.                                       │
│ 200  │ Deliver A to all honest nodes.                                     │
│ 208  │ Honest HEADs A; deliver their votes at 216. Repeat at 272/280.     │
│ 288  │ Gate 3 fast-writes A; action emits honest targets (1,g).           │
│ 384  │ Propose X,Y, slot 6, parent A, each with a height-1 target quorum. │
│ 392  │ Deliver X to U, Y to V₁,V₂. Both states have height 2.             │
│ 400  │ U votes X, V nodes vote Y; D supplies each branch's matching vote. │
│ 408  │ Deliver group batches; repeat label 7 at 464/472.                  │
│ 480  │ Gate 6 fast-writes X/Y. U targets (2,X); V₁,V₂,D target (2,Y).     │
│      │ Honest rows also contain permitted finality (1,g).                 │
│ 512  │ Propose Y₁, slot 8, parent Y, with the three full Y rows.          │
│ 520  │ Deliver Y₁ to V₁,V₂.                                               │
│ 528  │ HEADs X/Y₁; deliver at 536. Repeat 592/600 and 656/664.            │
│ 672  │ Gate 9 renews X/Y₁ to deadline 784. V₁,V₂,D supply target          │
│      │ (3,Y₁) and finality (2,Y).                                         │
│ 704  │ Propose Y₂, slot 11, parent Y₁, carrying those full rows.          │
│ 712  │ Give U Y,Y₁,Y₂ in parent order.                                    │
└──────┴────────────────────────────────────────────────────────────────────┘
```

The exact post-state tuples (h,T_h,h_j,J,h_F,F) are
Y=(2,Y,1,g,0,g), Y₁=(3,Y₁,2,Y,1,g), Y₂=(4,Y₂,3,Y₁,2,Y).
At 712, H=4,J=Y₁. Y is viable through Y₂ above acceptance floor 3.
F=g≺Y⪯J, so the finality test accepts Y. U's X lease is live until
784 and has no conflicting release batch. Reconcile deletes it, removes
incompatible fastWrite members, empties incompatible saved bodies, and
sets S=Y. Before this S extended X, so this is a reorganization.

There is no honest E1/E2 violation. No honest identity targets both X and Y.
Finality (1,g) and finality (2,Y) are allowed by the respective records.
The attack uses no timeout. It refutes unconditional local lease retention
and unconditional monotone S. Healthy delivery from genesis fails, so it
does not meet Clean or P1.

### 11.2 N2 — bp.noPhysicalPruning.v1 — REPLACED

**PROVED-paper (old fold); REPLACED. Window replay OPEN.**
**historical (pre-no-round rules).** The old run is in
[01-foundations-68b0537a.md](archive/01-foundations-68b0537a.md), §11.2.

Both competing children are below the same height-3 entry. The finality
carrier’s rows match its parent state.

Use `Δ=16,k=2,L=112,R=3,GST=1000,n=4,q_F=3,τ=2`. Honest identities are `U,V1,V2`; `D` is faulty. All listed proposers are faulty, so R7 imposes no selection requirement on them.

**Rows and block states.**

Write `T_i(h,X;f)` for a target row, with empty finality pair `f=—`.
Use distinct roots in order `g<A<X<Y<Y1<W<Z1<Z2<Q`. Each block
contains its declared raw/support votes; unlisted base lists are empty.

The complete honest `sent` records through time 800 are:

```text
┌────────────┬──────┬─────────────────┐
│ Identities │ Time │ New row         │
├────────────┼──────┼─────────────────┤
│ U,V1,V2    │ 288  │ T_i(1,g;—)      │
│ U          │ 480  │ T_U(2,X;(1,g))  │
│ V1,V2      │ 480  │ T_i(2,Y;(1,g))  │
│ V1,V2      │ 672  │ T_i(3,Y1;(2,Y)) │
└────────────┴──────┴─────────────────┘
```

`D` signs one matching height-2 Y row at 480 and one matching height-3 Y1 row at 672, with the same finality pairs. U’s repeated height-2 candidate at 672 is suppressed.

Let `Q1` be the three honest height-1 targets, `QY` the two V rows plus D’s height-2 Y row, and `Q3` the two V rows plus D’s height-3 Y1 row.

```text
┌───────┬──────┬────────┬─────────────┬──────┬──────────────────────┐
│ Block │ Slot │ Parent │ Parent pair │ Rows │ Post (h,T;j,J;h_F,F) │
├───────┼──────┼────────┼─────────────┼──────┼──────────────────────┤
│ A     │ 3    │ g      │ (1,g)       │ None │ (1,g;0,g;0,g)        │
│ X     │ 6    │ A      │ (1,g)       │ Q1   │ (2,X;1,g;0,g)        │
│ Y     │ 6    │ A      │ (1,g)       │ Q1   │ (2,Y;1,g;0,g)        │
│ Y1    │ 8    │ Y      │ (2,Y)       │ QY   │ (3,Y1;2,Y;1,g)       │
│ W     │ 9    │ Y1     │ (3,Y1)      │ None │ (3,Y1;2,Y;1,g)       │
│ Z1    │ 10   │ Y1     │ (3,Y1)      │ None │ (3,Y1;2,Y;1,g)       │
│ Q     │ 11   │ X      │ (2,X)       │ None │ (2,X;1,g;0,g)        │
│ Z2    │ 11   │ Z1     │ (3,Y1)      │ Q3   │ (4,Z2;3,Y1;2,Y)      │
└───────┴──────┴────────┴─────────────┴──────┴──────────────────────┘
```

In particular, `Z2`’s parent pair is `(3,Y1)`. Its rows pass R6. The fold finalizes Y before it justifies Y1 and advances height.

**Source history and decisive receipts.**

Deliver A at 200, and its honest votes at 216 and 280. At 392, U receives X; V1,V2 receive Y. At labels 6 and 7, each group receives its own honest votes plus D’s matching branch vote. Deliver Y1 to V at 520 and W at 580. V then votes Y1 at label 8 and W at labels 9 and 10. U continues to vote X. Each group receives its branch batches eight ticks after emission.

Thus gates 3, 6, and 9 supply the actual sources for all listed honest rows.

At U:

```text
┌──────┬──────────────────────────────────────────────────────────────┐
│ Time │ Event                                                        │
├──────┼──────────────────────────────────────────────────────────────┤
│ 664  │ Receive label-10 U→X and D→X.                                │
│ 680  │ Receive Y,Y1,W, with dependencies first.                     │
│ 688  │ Freeze label 10.                                             │
│ 700  │ Receive Z1.                                                  │
│ 708  │ Receive Q. Its raw/support lists contain V1→W,V2→W,D→W.      │
│ 712  │ Receive Z2. Accept F=Y; live J=Y1,H=4,root=Y1,floor=3.       │
│ 720  │ Compare HEAD with cumulative storage and after deleting X,Q. │
│ 728  │ Receive U's own label-11 vote and D→W in each execution.     │
│ 800  │ Gate 11 gives S=W with retention, but S=Y1 after deletion.   │
└──────┴──────────────────────────────────────────────────────────────┘
```

Defer all other relevant receipts past 800. This is before GST, so the delay is permitted.

With cumulative storage, the label-10 merge is:

```text
{U→X,D→X,V1→W,V2→W,D→W}.
```

D equivocates. There are four seats. Therefore:

```text
score(W)=3; score(Z1)=1.
```

W is eligible and HEAD is W.

After deleting inactive X and Q, retain all signed pools and their original stamps. Q’s pool copies have stamp 704, after freeze 688. The merge is only `{U→X,D→X}`. Neither child of Y1 is current, below the floor, or supported by a majority. HEAD stops at Y1.

At gate 11:

- Retention has two clean W votes out of two, so `S=W`.
- Deletion has one Y1 vote and one W vote. W fails the strict majority; `S=Y1`.

Both guards pass. Q’s declared votes have head W at slot 9≤10; its
declaration is valid. Z2’s base lists are empty. Q has height 2, equal
to Y’s finalized entry height. Thus the example remains within the intended `finalLock` limit.

The current spec requires cumulative storage. Metadata deletion can change
HEAD at 720 and S at 800, even when all signed pools are retained.
After this prefix, deliver the deferred pre-GST objects before `GST+Δ`,
with dependencies first and the stated receiver exclusions.

### 11.3 N3 — bp.slowWindowLoss.v1

**REVALIDATE (no-round).** The review found no R6 failure here; the
paper argument is retained. A complete current-rule replay remains open.

Use N1 with the following changes. At U withhold its own label-10 X vote
and D's label-10 X vote past gate 10. Deliver Y,Y₁ at 660 and only
D's label-10 Y₁ vote at 664. Label-9 X votes still arrive at 600.
Thus gate 9 at 672 saves X and renews its lease. J has moved, but while
F=g that does not restrict the SA confirmation walk from F (here g).
U has no X source in the FG domain at its action; V₁,V₂,D still supply
the independent Y finalization.

Y₂ has empty base-vote and support lists. Deliver Y₂ at 712. Reconcile changes genuine[9]=X to present-empty.
At gate 10, time 736, the single early/late participant is D→Y₁:
p=1,D_late=1, so Y₁ is genuine but p<τ=2. For common ancestor A:

```text
┌──────────────────────────────────────────┬────────┐
│ Test                                     │ Result │
├──────────────────────────────────────────┼────────┤
│ slow_admissible(10,A) with saved 9=X     │ true   │
│ slow_admissible(10,A) with saved 9=empty │ false  │
│ label 9 is still evaluated               │ true   │
└──────────────────────────────────────────┴────────┘
```

The changed predicate does not prevent record advancement. A⪯F=Y,
so finality already protects A; its old lease deadline is still 784.
For B strictly above F, any saved result covering B also extends F,
so it cannot be one of the results emptied for conflict with F.
This restricted slow-window preservation is valid; unconditional
slow-window preservation is false.

## 12. Results and limits

The window chain and HEIGHT BRIDGE, store, active view, exact reconcile
effects, nesting, carrier bridge, source discipline, accountable safety
and finalized safety have the paper arguments above. Clean/P1
consumers still need the window provenance port and review; healing uses 21 W1–W3. The negatives are exact executions at a≤f, not threshold-only
count profiles. The remaining Lean obligation in this file is the composed run
model and its projection/origin/receipt producers. The cited old static store/frame
proofs were checked in the earlier pass. Clean compatibility, which K8
needs, is proved for the old fold in the next file; its window port is pending.
