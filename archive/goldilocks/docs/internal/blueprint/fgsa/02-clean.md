# FG-SA blueprint: Clean safety

_Date: 2026-09-28. Authority: [00-outline.md](00-outline.md).
Foundations: [01-foundations.md](01-foundations.md)._

Rule authority: [the current spec](../spec/fgsa-protocol.tex), SHA-256
`a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.
Window authority: C1 and R6-window; the current spec changes only reviewed
status text from this rule pin. Positive proof/status claims below retain their
old-fold scope; the marked window ports are pending. Historical line citations
keep their archive basis. Current registry successors are in 00.

Citations explicitly marked 4e85ff34 use that archive's numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the adopted spec c1ea1db0 changes only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.

Unqualified absolute spec line citations below use the dbcb7f05 archive;
the r214 paragraph above applies only to citations explicitly marked 4e85ff34.

## 1. Target, scope, and induction data

This file proves bp.cleanSafety.v1: all honest available outputs in Clean
are compatible across nodes and times, and each local output is monotone.
Clean means healthy from genesis, with a<h_t≤n−a. It does not mean
a≤f, h_t≥τ, or a healthy interval after an arbitrary damaged prefix.

The proof includes empty and vetoed gate branches, finality moves at arbitrary
deliveries, sleeping readers, current-proposal metadata outside the active
view, and same-time event order. It does not assume exact proposal adoption.
Therefore the 6Δ inclusion proof remains in stage 2a.

Let C_(x,s) be the actual raw genuine result computed at honest x's gate d_s,
before the guard. This is an event value, not a later lookup in the mutable
saved-result map. Write C_(x,s)=⊥ for an empty result.
Let VHead_(y,s+1) be y's actual post-release HEAD computation at q_s.
For an asleep y, define this as the result of the same deterministic read;
only awake nodes emit it. Receipt relay is a run premise for every honest
acceptor, including an asleep acceptor (spec 197–204). Sleep suppresses
duties; it does not narrow that delivery premise.

We will maintain facts over a finite execution prefix. The main history
assertions are:

- **Ordered:** if gates s<r have occurred and C_(x,s)=B≠⊥,
  C_(y,r)=C≠⊥, then B⪯C.
- **Same:** nonempty results at the same label are compatible.
- **Continues:** after a gate computes C_(x,s)=B, certify retrospectively
  B⪯VHead_(y,s+1) for every honest y. The HEAD time q_s is earlier
  than d_s, so all these reads already exist.
- **Origins:** every honest fast source and live lease target is a prefix
  of an actual successful genuine event; every accepted F,J has an
  earlier honest target-source origin or is g; S has a gate or F origin.
- **Chain:** these result bodies, their prefixes, honest F,J and S are on
  one chain. Saved nonempty results retain their event values in Clean.

window port: 01 §3.1 window target-source origins (Origins/Chain) (pending)

“On one chain” means pairwise compatibility, not membership in every
node's store. For finitely many compatible blocks, their deepest member
contains all the others. The proof does not choose a future canonical tip.

The distinction between a source event and a mutable saved result is required
for the general foundations. Clean will prove that reconcile empties none.
The distinction between time order and proof order is also required:
Continues is established after its source gate, about an earlier HEAD.
It is never used as an input to that earlier protocol action.

## 2. Counts, same-label safety, and release

### 2.1 Exact honest-origin count

**NEW use of unchanged SA counting.**
At label s, let h=h_s>a. Every awake honest seat emits one vote at v_s.
Its signature reaches every honest late pool before d_s. Whether its head
resolves does not affect late participation. No honest seat emits twice.
Thus every late denominator D contains these h distinct seats.

Suppose a candidate B has only faulty surviving support P of size p≤a.
These p seats are disjoint from the h honest seats and are in the same
late pool. Therefore D≥h+p. A genuine strict majority requires 2p>D,
which gives p>h>a≥p, a contradiction. Thus each genuine nonempty body
has an honest supporting HEAD. A fresh fast source has at least τ>a
surviving supporters, so it too has an honest supporter.

This proof does not replace D by n, and does not use h>2a.
The profile n=7,a=2,h=3 has h≤2a and still satisfies its hypotheses.
This is a count illustration, not a protocol counterexample.

For an honest batch all supporting B, honest votes cannot equivocate.
Assume that their heads extend current F, as proved in §5.4.
Then p(F)≥h, p(B)≥h, and D≤h+a, so both F and B pass the strict
majority test. Since B and F are ancestors of each honest head, they
are comparable. If F⪯B, the F-to-B suffix has honest support at least h;
every competing branch has only faulty support. Active path closure
therefore makes the walk reach B. If B⪯F, the eligible F and every
returned descendant already cover B. The final test gives a nonempty
result extending B in both cases.

This last claim is the mathematical content of
G.confirmation_covers_early_honest_batch and
G.preserve_of_early_delivery. The stronger premise that honest heads
extend current F is supplied by the joint source-history proof.

### 2.2 Same-label safety — bp.sameLabel.v1

**REUSE of the SA receipt/count argument, with active support.**
For two honest label-s gates, let B and C be their results, with surviving
supporter sets P_B and P_C. Denote their late-seat sets by L_x,L_y.
The raw confirmation walk gives
2|P_B|>|L_x| and 2|P_C|>|L_y|.

Relay here includes objects accepted by asleep honest nodes.
Every early supporter at one node arrives at the other node's late pool
as that vote or as two distinct votes of its seat. Therefore
P_B∪P_C⊆L_x and P_B∪P_C⊆L_y.
This statement concerns seat presence. It does not require the opposing
head to resolve.

Suppose B#C and i belongs to both support sets. Select i's supporting
head K≥B at x and head K'≥C at y. Both resolutions are honestly held,
so both are in run scope. One signed root resolves to one body at all
honest stores. Thus distinct bodies require distinct signed roots.
They cannot be the same head:
otherwise B,C are ancestors of one block. Relay of i's distinct y vote,
or equivalent two-vote evidence, reaches x before d_s. Thus x sees
two distinct votes of i in its late pool, contradicting survival in P_B.
Hence P_B and P_C are disjoint.

The union inclusions now give
|L_x|≥|P_B|+|P_C| and |L_y|≥|P_B|+|P_C|.
The first strict majority gives |P_B|>|P_C|; the second gives the
opposite strict inequality. Contradiction. Thus B∥C.

Removing inactive support can only reduce P_B or P_C. It does not remove
seats from L_x,L_y or erase a second signature. Therefore the proof is
unchanged under act(Σ). The guard is not used: this is about raw results.

Exact SA declarations: G.synchronous_early_vote_late,
synchronous_support_subset_late, synchronous_support_disjoint,
cleanSupport_not_equivocating, and sameLabel_from_engine.
The new producer proves receipt with the composite handler rules; the
set/count argument itself is reused.

### 2.3 Release — bp.release.v1 (K11)

**NEW active-view lemma.**
Fix signed pool U and its receipt stamps before q_s. Let E be its set of
equivocating seats. For an active view A, define
R_A(B)={i∉E: some (i,s,K)∈U resolves before q_s in A and K#B}.

If A'⊆A with the same retained-head stamps, each witness for R_A'(B)
is also a witness for R_A(B). Hence R_A'(B)⊆R_A(B) and the count
cannot increase. Raw E is unchanged. An unresolved or inactive opposing
vote must not be removed from E before this comparison.

If all honest label-s heads are compatible with B, no honest seat belongs
to R_A(B). Thus |R_A(B)|≤a<τ, and release cannot remove B's lease.
If B⪯F, every active head is compatible with B, so the count is zero.

An ancestor A⪯B has R_Aview(A)⊆R_Aview(B), which is the deadline
and ancestor-lease preservation argument in 01 §6.
Expiry is a separate tick operation. This lemma gives no claim that a
Clean lease never expires. Clean safety does not require such a claim.

## 3. Source history and the live frame — bp.cleanFrame.v1

### 3.1 Equal-height source entries (NEW, reusing pure geometry)

window port: 01 §3.1a HEIGHT BRIDGE (pending)

Assume all relevant honest fresh-source bodies are compatible.
If two such bodies C,D have ht(C)=ht(D)=m, one precedes the other.
Apply KFG.entry_eq_on_plateau to their intervening chain segment:
σ[C].T_h=σ[D].T_h.

StaleUseful sets no height bits. Thus every target QC or height crossing
has an honest HeightMatch source at that height, since q_F>a.
A justified entry J at m has an honest target row because q_F>a. By K6 its source C has height m
and names J. A progress crossing has an honest source D at height m and names its chain entry E.
The source and certificate carriers put both named entries in run scope. Use the named root
premise to identify matching names, then the plateau argument gives E=J.
The proof needs neither quorum intersection nor a≤f.

This is stronger under Clean history than the usable part of
KFG.uniqueJust_chains: at equal justified heights, with
RootInjectiveOn, that theorem gives equality OR slashing weight.
At a>f its evidence branch cannot in general be eliminated by counting.
Use the source-body argument above instead.

### 3.2 F and J origins (K7 Clean)

window port: 01 §§3.1,4,8.4 window provenance/store (pending)

Consider a new admitted block with a justification J.
If its justified height is zero, J=g. Otherwise extract its target
certificate and an honest source C by K6. Establish scope for the certificate
entry and the source entry before matching their roots; then J⪯C. A finalized
window entry (x,X) has its own earlier target QC for (x,X), so the same
origin argument applies to X. It need not be the latest J (window provenance).
It follows that every disclosed J,F is on the ancestor closure of
the honest-source chain.

The live cache selects one of these justifications. An F acceptance
selects one of these finalized entries. Selection does not create a new
branch. In the joint induction below, every source used here precedes
the receiving event; a source from that event's future gate is impossible.

This also handles a privately carried certificate. Its disclosure can be
new, but its honest signature and source events are already in the prefix.
It does not obtain a fresh honest origin when disclosed.

### 3.3 No contest (K9)

window port: 02 §§3.1–3.2 window suppliers; 01 K6/K8/K9 (pending)

If H≠j+1, the contest test is false by definition.
Suppose H=j+1. If j=0, J=g and every W extends it.
If j>0, choose any W∈T with ht(W)=H.
Its chain crossed j. Extract the honest source of that progress quorum.
Extract the honest target source of the cached justification (j,J).
By §3.1 their height-j entries agree. The crossed entry on W is therefore
J, so J⪯W. This holds for every height-H witness, and the existential
contest test is false.

Consequently Clean uses lo=H−1 throughout. The root is J if H=j+1,
otherwise F. Both are on the historical source chain.
This argument examines the cumulative T, including inactive old blocks.
There is no implicit active filter in the contest test.

### 3.4 Full-domain retention

window port: 02 §§3.1–3.2 window suppliers; 01 K6/K8/K9 (pending)

Let B∈T be compatible with every relevant source body.
By §3.2 it is compatible with F and J, hence with Z.
If B⪯F or B⪯Z, the root and all HEADs already cover it.
In the remaining case F⪯Z⪯B.

If H=1, ht(B)≥1≥H−1, so B witnesses its own viability.
If H>1, choose a maximal-height W∈T and its crossed height-(H−1)
entry E. StaleUseful sets no progress bits, so the crossing has an honest
HeightMatch source at height H−1. Its entry is E, so E is comparable with B.

- If B⪯E, then B⪯E⪯W. The stored W witnesses B.
- If E⪯B, height monotonicity gives ht(B)≥ht(E)=H−1.
  B witnesses itself.

Thus B∈D_Σ(T). Each intermediate vertex between Z and B shares that
witness. This proves the full-domain clause of K9 without a HEAD-height
assumption.

This lemma requires compatibility with all relevant source bodies.
An arbitrary active block does not meet that premise. It is not a claim
that every admitted branch is viable.

### 3.5 Exact transfer-time frame

window port: 02 §§3.1–3.2 window suppliers; 01 K6/K8/K9 (pending)

Fix the actual q_s read and a later actual source result C_(x,s)=B.
Assume ordered history at labels below s, so every earlier-label result
precedes B. The following claims concern the stored read at q_s.

1. Every honest source row already usable at q_s has source label u≤s−1,
   by 01 §8.4. Its source body is a prefix of its genuine result C_(z,u),
   hence a prefix of B.
2. K6 then puts F and J at or below B. Thus Z⪯B. This applies also to
   certificates admitted between freeze z_s and the read q_s.
3. If H>1, a maximal-height W has an honest crossing source at height H−1.
   That source body precedes B. Thus ht(B)≥H−1. For H=1 the inequality
   follows from ht(B)≥1.
4. Every lease present at q_s has a source gate strictly earlier than q_s,
   hence label below s. Its target precedes B. Expiry and release cannot
   add a target. The live root is Z or a target in D(T), so it too
   precedes B and lies at or above Z.
5. B has a surviving early supporter K≥B at the source. Its head and path
   were present before e_s. Since receiving F at q_s is below B, all
   earlier receiving F values are below B. K8 admits this path before
   z_s. Thus B and all its ancestors are in the cumulative pre-freeze
   arm V_(s+1). Any needed already stored ancestor retains its stamp.
6. Each vertex after live_root through B extends F and Z and is in V.
   B itself, with ht(B)≥lo, is a witness in that same V.
   Therefore each such vertex belongs to D_Σ(V_(s+1)).

This is a proof inside the actual duty view. It does not infer
D(V)=D(T)∩V and does not import a late witness from outside V.
The maximal crossing is used to bound ht(B); B supplies the local witness.
This distinction removes the apparent need for a new block-view arm.

## 4. Walk and score infrastructure

### 4.1 Suffix walk — bp.suffixWalk.v1

G.ghost_covers_of_path_dominance is generic in score, eligibility and anchor,
but its path premise asks for EVERY non-genesis ancestor of B in the walked
tree. An FJ domain omits ancestors below Z. That theorem cannot be applied
literally to D(V) with this premise left unproved.

**NEW suffix form.**
Let A be the anchor. If B⪯A, the result extends A because each walk
step selects a child. Transitivity gives B⪯result.

Otherwise A≺B. List the unique path A=C₀,C₁,...,C_m=B.
Assume for each 1≤i≤m that C_i belongs to the walked tree, is eligible,
and its score strictly exceeds each other eligible child of C_(i−1).
At C_(i−1), the candidate set contains C_i. Strict score dominance means
the argmax is exactly C_i, irrespective of root tie-breaking. This is
G.ghostStep_of_strict_dominance. Thus the first m steps are exactly
C₁,...,C_m, by induction on i. At B, all later steps are descendants.
The walk therefore returns a descendant of B.

For a fuel-based Lean implementation, these m path vertices are distinct
members of the finite walked tree. Hence m≤its cardinality. The engine's
tree-size fuel suffices to reach B. Further fuel cannot remove the prefix.
Alternatively adapt G.ghostWalk_covers_path to start its induction at A
instead of requiring the path below A.

This proof uses only child membership, eligibility and strict dominance.
Adding low-parent band eligibility to rival children does not invalidate
it, because the dominance premise ranges over every eligible rival.

Concrete reason the whole-path premise is unsuitable: in 01 N1 after
time 712, F=Y while A is a non-genesis ancestor of Y. The filtered domain
omits A. A transfer target above Y cannot supply the old full-path premise.
This is not a failure of the walk; the suffix proof is the repair.

### 4.2 Genuine transfer — bp.cleanTransfer.v1 (K10 Clean)

window port: 01 §10 window admission-or-coverage; block/HEAD Δ (pending)

Fix C_(x,s)=B and an honest reader y's q_s view. Write P_B for x's
surviving early support of B, p=|P_B|, D for its late denominator,
U for y's merged raw votes, V for its support declarations,
N for the merged participant count, and T_y for cumulative admitted storage.
The source's strict majority gives 2p>D.

**Forward receipt.** For o∈P_B with head K≥B, early acceptance and head
resolution at x occurred before e_s. The forward deadline is before z_s.
K9 gives F_y(q_s)⪯B, so all earlier receiving F values are below B.
K8 admits K and its path. For the vote, cap-aware relay gives o or two
same-seat votes. If o were missing at y's next raw view because of its cap,
its two cap votes would each return to x before d_s; at least one differs
from o, or x already has two copies. This contradicts o surviving in P_B.
Thus o is in the frozen support view with its valid retained head.
Both honestly held resolutions are in run scope. The same signed root
therefore names the same body at source and receiver, including its path.

**Backward receipt.** Relay applies also when the acceptor is asleep. Every vote in U is frozen before z_s or occurs in
an admitted current proposal read before q_s. Its local vote handler
accepted it or already held two cap signatures. Receipt relay puts the
vote or that evidence at x before d_s. A refused proposal is never used
as a producer for this call. A now-inactive admitted proposal is still used:
T is cumulative and its metadata was not deleted.

Therefore the three TransferReceipts conditions hold, with support-head
resolution tested in T_y for the HEAD scoring function:

1. each source surviving supporter of B is in V with its head in T_y;
2. each U vote is in x's late pool or that pool already has same-seat
   equivocation;
3. V⊆U, because frozen support is a raw subset and every original carried
   support subset is part of its original carried raw list.

A source supporter cannot have any different same-seat vote in U:
the backward condition would contradict its source late non-equivocation.
Thus all p source seats score for B, no such seat equivocates in U, and
no such seat scores for a block conflicting with B. Every U seat is in
the source late seat set. Hence N≤D and:

- score(B)≥p;
- for any C#B, p+score(C)≤D;
- 2score(B)≥2p>D≥N;
- score(C)≤D−p<p≤score(B).

These are precisely G.TransferReceipts.seat_unique, participants_subset,
conflict_disjoint, conflicting_score_bound and majority. They count
equivocators on every ordinary branch; no equivocator is silently dropped.

For each path vertex E⪯B after the live root, support is monotone toward
ancestors, so score(E)≥score(B). Its strict majority makes it eligible
even when the band arm is false. Every sibling D≠E conflicts with B,
so score(D)<score(B)≤score(E). K9 supplies the path membership and
the live root below B. Apply bp.suffixWalk.v1: B⪯VHead_(y,s+1).

A carried inactive support head cannot undermine this count. If it supported
a path vertex ≥F, it would extend F and would be active. Its raw seat still
contributes to the backward participant bound and equivocation test.
This is exactly the current carried-support exception of the spec.

The proof is valid for faulty proposal slots and for a result that is not
fast. It uses 2p>D, not p≥τ. It does not assume all nodes have a lease on B.
It is a relation from a later gate result to an earlier read, obtained by
the two strict relay directions described in 01 §10.3.

### 4.3 Retained-suffix score equality — algebra of bp.scoreSuffix.v1

This algebra is proved now; its full honest-proposal producer is stage 2a.

Let U⊆U' be raw vote sets. Assume each extra U' vote either occurs in U
or its seat already equivocates in U. Then participant sets are equal:
an extra vote's seat is already in U through the two evidence votes.
Equivocator sets are equal: an initially non-equivocating seat receives
no genuinely new vote, while an existing equivocator retains its two votes.

Fix a candidate B≥F. Assume that for each non-equivocating seat i the
existence of a declared, valid-slot support head K≥B is the same in both
views. The score of an equivocating seat is one in both views. The score
of a non-equivocating seat is the support-incidence Boolean, equal by
premise. Summing over the equal participant sets proves equal scores.

One way to supply the support premise is
G.ScorePreservingViewExtension plus the explicit `ht` premise of
`.score_eq`: each source support target belongs to `tree` iff it belongs
to `tree'`. Its `.support_subset` is a structure field, not a theorem.
The incidence proof above is used when full target membership differs.
When support sets lose heads incompatible with new F, literal
support_subset may fail. Prove incidence equality instead: an excluded head
cannot extend B≥F, so its contribution was zero already.
Original proposal containers remain in T in this argument.

With equal scores and counts, the majority eligibility arm agrees.
Current-slot eligibility agrees on the same candidate. The low-parent arm
depends on the live band; equal scores alone do not prove that arm equal.
Stage 2a must prove the path comparison with the possibly different bands.

### 4.4 Scope of the unproved exact-proposal step

The Clean proof below does not use
G.clean_honest_proposal_heads or SA.included_from_engine as black boxes.
Their run type is plain SA/GridCO. The FG-SA HEAD uses a different root,
a live frame, and a filtered duty tree.

For bp.exactProposal.v1, stage 2a must establish:

- the honest proposal's parent covers every relevant earlier source;
- its path stays in each voter's domain, using a witness in that view;
- every eligible rival in that view reflects to the proposer, or strict
  dominance rejects the new low-parent eligibility case;
- scores agree on the compared suffix, with cap evidence rather than
  literal vote-set equality;
- the live start is on the selected parent path;
- the unique current-slot proposal is selected at the parent.

DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer supplies the
precise persist/reflect interface, not these composed run producers.
This is a deferred proof obligation, not a claimed counterexample.
The 6Δ inclusion theorem then needs the pending label-(s−1) gate and
the subsequent honest P batch. It is not needed to close stage 1.

## 5. Joint induction over execution prefixes

### 5.1 Prefix invariant and proof order

window port: 01 §§3–4,7–8 window origins/store/frame/nesting (I2–I4) (pending)

Fix any finite Clean trace Γ with sufficient horizon for its asserted reads.
Induct over its actual event list. Within a tick, use the fixed subevent order:
clock, expiry, release if due, gate if due, then duty and own-row processing.
Within a block handler use admission, vote calls, cache update, immediate
reconcile, row calls. Do not expose the temporary F-before-reconcile state
as a public output.

For the current prefix maintain:

I1. Every completed genuine gate event has the Ordered, Same and Continues
properties of §1 relative to other completed gates. Every Clean gate is
nonempty; label 0 has result g and starts the induction.

I2. Every honest emitted nonempty height row has the K6 source event, already
completed, and its source body is on the chain of I1. Every nonzero
justification/finalization disclosed in an accepted state has an earlier
such target origin. The current live F,J are on that chain or are g.

I3. Each live target has its actual gate origin. Every saved nonempty body
equals its event value. Historical fastWrite membership has an actual
fast-write origin. S has an earlier gate-result or accepted-F origin.
All these values are compatible with the I1 chain.

I4. Local nesting, store/frame invariants, and client safety hold.
Every S transition so far has been an extension.

The induction stores assertions about past HEAD reads in I1. At the event
that computes a new result B at d_s, its q_s read is already in the prefix.
We prove a new fact about that old read using the completed gate's late
evidence. This is a standard assertion about two trace positions.
It does not alter q_s or require the node at q_s to know B.

For partial same-time gate batches, only gates already executed are in I1.
All inputs to any local gate at d_s exclude same-time local deliveries.
Therefore the same-label proof compares the actual completed gates without
requiring a total order of different nodes' ticks beyond their trace order.

### 5.2 Initialization and ordinary events

At initialization, there are no gate events, leases, fast writes, or signed
honest rows. F=J=S=g. I1–I4 hold, with all origin clauses empty.

A vote receipt may insert a signature and stamp. A row receipt may insert
a full row. Neither changes SA origins, outputs or frame. Refusal changes
nothing. Such events supply transport evidence for future gates.

A proposal or base-vote duty emits an authentic object but does not process
it locally until delivery. It creates no S, lease, result, or source.
No invariant requires all unconstrained HEADs before the first gate to
form a chain. Their required continuations will be certified when the
corresponding gate result is computed.

Expiry and release delete targets. They cannot create a conflicting origin
or change S. Ancestor closure survives by 01 §6.1. K11 supplies the
non-release fact when an already protected path's honest batch is being
used, but the basic prefix invariant is preserved even by deletion.

### 5.3 Block admission, finality, and reconcile

window port: 01 §§3.1,4,6,8.4 window derive/QCs/reconcile (steps 2–6) (pending)

Assume I1–I4 before a checked block receipt.

1. If any admission test fails, no carried-object calls or state changes
   occur. The invariant is unchanged.
2. If it is admitted, 01 §4 proves all store and projection clauses.
3. Each new nonzero justification in its immutable chain state has a target
   certificate. Since q_F>a, select an honest signer. By authentic origin
   this signer emitted the row at an earlier real action. I2 identifies
   its already completed fast gate. Thus its named entry is a prefix of
   a body already on the I1 chain.
4. Each finalized window entry (x,X) traces to its own earlier target QC
   for (x,X) and its honest HeightMatch target source. The entry need not
   be the latest J; window provenance supplies this origin.
5. The new cached J is one of the old or new justified entries. If F advances,
   its new value is one of these finalized entries. Hence both are
   compatible with every existing I1 result and I3 target/body/S.
6. Reconcile therefore preserves all live targets and saved nonempty
   bodies by K1. Its only possible output change is to a descendant F.
   It preserves all client/source evidence. I4 nesting holds after it.
7. Later row-pool calls do not change these facts.

This proves the receive side of K7 without an a≤f argument.
A late private carrier obeys exactly the same origin proof.

### 5.4 Gate event: establish the new history

window port: 01 §8.4 window F origins; 02 §5.3 event port (pending)

Let honest x run gate d_s. No result has yet been saved at that local label.
If the label is already evaluated, the body is not recomputed and normalization
preserves the invariant; scheduled reachable execution takes the first case.

For s=0, the honest label-0 votes are for g. No valid non-genesis block has
slot ≤0 with an increasing parent slot. Honest votes reach the early pool,
do not equivocate, and give a strict majority at g since h₀>a.
Thus the genuine result is g. Its continuation holds because every HEAD
extends g. No non-genesis lease prefix is written.

Now let s>0. All label-(s−1) gates precede d_s by 4Δ and have run.
By induction they are nonempty (starting from the label-0 case).
Choose one such result D. For every older genuine B at label r<s−1,
I1 gives B⪯D. For every label-(s−1) result D' at any honest reader,
its Continues certificate gives D'⪯every honest VHead_s, because
q_(s−1)=v_s.

We must prove that the honest label-s heads remain active at x's gate.
At every time before that local gate, any usable honest FG source has
label at most s−1. Such a source is a prefix of some earlier result.
If its label is below s−1, that result precedes D. If its label is s−1,
its result is one of the D'. Every honest label-s head extends all
these D' and D, by their retrospective continuation certificates.
K6 therefore puts every intervening F at or below each such honest head.
No such head is excluded. Their paths and votes are admitted before e_s
by strict honest delivery and K8, or the necessary ancestors were stored
already. Their original early stamps remain.

This gives p(F)≥h_s and D_late≤h_s+a<2h_s, so F is eligible.
Apply §2.1 with this honest batch above F. For each earlier result B,
all h_s honest heads extend B. They contribute at least h_s surviving
support on B, while at most a other seats exist. The confirmation walk
therefore returns a nonempty C with B⪯C. This proves Ordered for
the new result against every earlier label.

For any already computed result C' of label s, apply §2.2 to the two
real gate inputs. Thus C∥C'. We have extended the global result chain.
This proof includes the raw result before the whole-result guard.

Now establish the new retrospective Continues certificate.
At q_s all source labels are below s. We have just proved that their
genuine bodies precede C. All required data at q_s are past trace states.
Apply §3.5 for its frame and path, then §4.2 for cap-aware majority
transport and suffix dominance. Conclude
C⪯VHead_(y,s+1) for every honest y.

There is no cycle: the new Ordered fact used Continues only for label s−1,
which was proved at an earlier gate. The new Continues fact uses Ordered
only for labels below s and the new result's own strict majority.
It uses no label-(s+1) gate or later source.

This is the event-prefix version of G.genuine_history_induction.
Its abstract preserve step is §2.1; its transfer step is §4.2.
The engine theorem itself is not instantiated with the FG-SA run.

### 5.5 Gate event: guard, leases, and S

window port: 01 §8.4 window F origins; 02 §5.3 event port (pending)

Continue within the same d_s tick.

Every input live lease has an earlier gate origin. Its label is below s,
because the current gate has not written and no future gate has run.
Its target is a prefix of an earlier genuine result, hence a prefix of C.
Therefore the whole-result guard passes. This proves that veto cannot
actually occur in Clean, while the invariant proof still includes the
veto branch as a harmless no-write branch.

Every new lease target is a prefix of C and stays on the result chain.
FastWrite contains precisely successful fast prefixes. A slow write uses
the saved window; every saved nonempty body is still its actual earlier
result by I3. The proof does not need a slow-write existence claim.

S before the gate is a gate result or an F assignment. A gate-origin S is
on the existing result chain. An F-origin S is a prefix of an earlier
honest fresh-source body and hence of an earlier result. All are compatible
with C. The advance rule keeps S if C⪯S and otherwise assigns C.
In the latter case compatibility implies S⪯C, so the write extends S.
Final normalization is redundant by 01 §7. It cannot create a retreat.

If the genuine result were empty, saving empty and keeping S would preserve
the assertions; the count above proves it does not occur in Clean.
The empty/veto cases therefore require no unproved origin inference.

### 5.6 FG action after the gate

window port: 01 §8.4 window F origins; 02 §5.3 event port (pending)

If this is a_r=d_(rR), the action runs after all steps in §§5.4–5.5.
If no eligible fresh fast prefix exists, the client sends no row. The
head-derived finality pair is not released on its own.

If C_fg exists, it is an actual prefix written by this gate, belongs to the
current full domain, and has a live deadline. The new result was just added
to the I1 chain. Its source entry therefore belongs to that chain's ancestor
closure. Only when create_attestation returns a row does record-before-release
update Λ and own-row processing run; bp.clientSafety.v1 still holds.
Own-row pool processing changes no F or S.

A different node can later receive this row at the same integer time.
Its local tick at that time must already have run, so this receipt cannot
enter that node's just-completed gate input. If a faulty carrier uses the
row later at that time, admission is handled by §5.3 with an already
completed source event. This is why same-time source creation is
well-founded.

### 5.7 Closure and finite-prefix endpoints

window port: 01 §8.4 window F origins; 02 §5.3 event port (pending)

Every event type has been covered. Thus I1–I4 hold at every completed
execution prefix. A prefix ending between q_s and d_s contains no new
label-s result yet; it is covered by the already established invariant,
without assuming how the pending gate will turn out. When a gate is
present, its earlier q_s reads and all strict-cutoff receipts used in its
Continues proof are also present.

No extension of the run beyond the asserted read is needed for safety.
For any source gate used in a continuation claim, require d_s within the
horizon. This is the same finite-horizon discipline as the SA clean proof.

The induction proves bp.cleanHistory.v1 and discharges K7/K9/K10 in the
Clean scope. It also proves that all Clean reconcile calls are harmless.
It does not derive a Recovery theorem from a Clean suffix.

## 6. Clean safety and monotonicity — bp.cleanSafety.v1

window port: 02 §5 window F-origin invariant at q_F>a (pending)

Fix arbitrary honest reads S_x(t),S_y(u) in a Clean trace.

Each non-genesis S value has an event origin. If it is a gate-origin value,
it equals a genuine result selected by advance. If it is an F-origin value,
it is a finalized entry that precedes an earlier genuine source body.
The prefix invariant puts all such bodies and their prefixes on one chain.
Thus S_x(t)∥S_y(u). Genesis is a prefix of every block, so it causes no
exception. This proves cross-node, cross-time safety.

For a fixed node, enumerate its events between t and u≥t.

- An ordinary receipt, duty, expiry or release leaves S unchanged.
- A gate changes S only to a compatible result. The ancestor case keeps S;
  the other compatible case is an extension.
- An F advance keeps S if the new F precedes it. If normalization changes S,
  new F is compatible with old S but does not precede it. Therefore
  old S⪯new F, so this change also extends S.

Compose these prefix relations by transitivity. Hence S_x(t)⪯S_x(u).
This proof includes F moves between public labels; it does not reduce all
reads to the most recent gate as the plain-SA proof can.

By comp.outputNesting.v3, both available accessors equal S and local F⪯S.
The conclusions hold at every a<h_t≤n−a. All uses of a were a<τ,
a<q_F, and h_s>a. The proof never invokes global finalized safety to
obtain the Clean chain, never uses h>2a, and never discards evidence
through the a≤f bound.

The 6Δ inclusion theorem is not part of this induction: its proof needs
exact honest-proposal adoption, while this proof needs only transferred
strict-majority prefixes at the next HEAD.

## 7. Geometry clauses 1–3 of ap.headReachesLo.v5 and v6

window port: 01 §4.3 window store/frame wrappers (pending)

These pure clauses are useful in stage 2b. They do not assert a Recovery
run producer. Clauses 1–3 are unchanged between v5 and v6.

Fix live controls with F⪯Z, an ancestor-closed finite X, domain D=D_Σ(X),
and the actual live anchor A. Height is nondecreasing along parents.

If B∈D and ht(B)<lo, select its witness W∈X with B⪯W and
ht(W)≥lo. W≠B. The first child C of B on the path to W belongs to X
by ancestor closure, extends F and Z, and has the same witness W.
Thus C∈D. Its parent B is below lo, so C is eligible irrespective of
scores.

If the walk starts in D, or takes one eligible child in D, every later
walked block is in D. A terminal block below lo would have the eligible
child just constructed, contradiction. Thus the returned head is in D
and has height at least lo.

If A∉D and has no eligible child in D, the first candidate set is empty,
so HEAD=A. D itself can be nonempty elsewhere. No global height bound on
this returned A follows.

If A=Z and D is nonempty, choose B∈D and its witness W. Since
Z⪯B⪯W and X is ancestor-closed, Z∈X. The same W witnesses Z
and F⪯Z, so Z∈D.

These paper proofs agree with KFG.filteredFrom_Z_mem and
filteredFrom_viable_child, whose source proofs were completed and re-read
during this task, followed by
G.ghost_result_no_eligible_child for the termination argument.
They prove clauses 1–3 of ap.headReachesLo.v5 and v6. The current v6
phase transport, settled-proposal and event-cost clauses are proved in
21 H.3, H.5–H.6, H.8 and H.21.

## 8. Exact SA/GridCO reuse map

window port: 01 window suppliers; 02 port status; 01 §11 old negatives (pending)

The distinction in the last column is material: a pure lemma can be applied
to supplied sets. A theorem quantified over Run(gridCO p) cannot simply be
applied to Run(FGSA).

```text
┌──────────────────────────────┬──────────────────────────────────────────┬─────────────────────────────────────┐
│ File under AC                │ Declaration                              │ Composed proof use / change         │
├──────────────────────────────┼──────────────────────────────────────────┼─────────────────────────────────────┤
│ GridCO Proofs/CrossView      │ synchronous_early_vote_late;             │ Port call producer; retain raw late │
│ .lean                        │ synchronous_support_subset_late;         │ seats even for inactive heads.      │
│                              │ synchronous_support_disjoint             │ Count proof unchanged.              │
│ GridCO Proofs/ReceiptRelay   │ accepted_head_receipt_before;            │ New composite receipt origins;      │
│ .lean                        │ handled_head_stamped_or_equivocates      │ block-only exclusion.               │
│ GridCO Proofs/Transfer.lean  │ TransferReceipts.seat_unique;            │ Pure sets/counts reused. Forward    │
│                              │ participants_subset; conflict_disjoint;  │ heads admitted by K8; cumulative    │
│                              │ conflicting_score_bound; majority        │ carried metadata in reverse relay.  │
│ GridCO Proofs/TransferViews  │ synchronous_early_path_in_voterTree      │ Port to cumulative V; then prove    │
│ .lean                        │                                          │ D(V) membership with B witness.     │
│ GridCO Proofs/MergedViews    │ transferReceipts_from_engine;            │ Run producers re-proved for FG-SA.  │
│ .lean                        │ transfer_from_engine                     │ Do not apply plain-run theorem.     │
│ GridCO Proofs/Walk.lean      │ ghostStep_of_strict_dominance;           │ Pure reuse; whole-path covering     │
│                              │ ghost_covers_of_path_dominance           │ lemma replaced by suffix variant.   │
│ GridCO Proofs/Preservation   │ preserve_of_early_delivery;              │ New active-head premise discharged  │
│ .lean                        │ preserve_from_engine                     │ by earlier-source bound.            │
│ GridCO Proofs/History        │ genuine_history_induction                │ Exact logical pattern; outer proof  │
│ Induction.lean               │                                          │ is over composite event prefixes.   │
│ GridCO Proofs/GenuineHistory │ run_target_genuine_origin;               │ Add reconcile and fastWrite cases;  │
│ .lean                        │ nextHeadState_target_genuine_origin;     │ preserve event origins separately   │
│                              │ clean_genuine_history                    │ from mutable saved bodies.          │
│ GridCO Proofs/CleanSafety    │ clean_gate_record_monotone;              │ Add F-origin S and inter-gate       │
│ .lean                        │ clean_gate_reads_compatible              │ finality updates.                   │
│ SA Proofs/Clean.lean         │ clean_safety_from_engine;                │ Target shape only; these are        │
│                              │ monotone_from_engine                     │ plain-SA run theorems.              │
│ GridCO Proofs/ScoreExtension │ ScorePreservingViewExtension.score_eq;   │ Pure algebra; support incidence on  │
│ .lean                        │ .count_eq; .equivocates_eq               │ retained suffix needs new producer. │
│ GridCO Proofs/WalkTransport  │ ghost_adopts_fresh_child; ghost_reanchor │ Stage 2a comparison tools.          │
│ .lean                        │                                          │ Not needed for stage-1 safety.      │
│ GridCO Proofs/CleanInclusion │ clean_honest_proposal_heads;             │ Stage 2a targets; root, domain and  │
│ .lean                        │ clean_honest_proposal_repair             │ live-band producers must change.    │
└──────────────────────────────┴──────────────────────────────────────────┴─────────────────────────────────────┘
```

“GridCO Proofs” denotes AvailableChainGridCO/Proofs; “SA Proofs” denotes
AvailableChainSA/Proofs. The namespace prefixes are G=AvailableChain.GridCO and
SA=AvailableChain.SA. In particular, `SA.included_from_engine`,
`SA.clean_safety_from_engine`, and `SA.monotone_from_engine` refer to
the SA declarations, not the GridCO or SAPC declarations of the same name.
The actor mapping uses the existing C* proof bijection, not a fixed-identity
assumption for the base protocol.

## 9. Findings and deferred obligations

window port: 01 window suppliers; 02 port status; 01 §11 old negatives (pending)

No counterexample to Clean was found. The proof above supplies the missing
Clean source/frame and filtered suffix steps without adding a fault premise.

The following proof limitations remain explicit:

1. The composed run and its receipt producers are paper constructions here.
   No existing SA run theorem alone certifies the changed handlers.
2. The static store/frame Correspondence proofs were completed during this
   task and re-read. The new composite projection and receipt producers
   still need formalization; no composed Lean certificate is claimed.
3. Exact proposal adoption, its score/path producer, pending-gate 6Δ
   inclusion, and both P1 arming proofs remain stage 2a.
4. Recovery and finality are proved in 21 and 22. Their common
   HEALING_INPUT interface is listed under one id in 00 §3.4.
5. A direct whole-genesis-path walk instantiation would miss a premise.
   Section 4.1 closes it with a proved suffix variant.
6. Exact raw/support set equality is not assumed. Counts and score incidence
   are the relevant equalities. A low-parent eligibility change still needs
   its own path comparison in stage 2a.
7. FinalLock and accountable safety are not used to narrow Clean to a≤f.
   Equal-height entry agreement comes from compatible honest source bodies.

The exact negative executions are in 01 §11: N1 permits unprotected
asynchronous lease/S override; N2 forbids physical deletion of cumulative
metadata (REPLACED under no-round rules: 01 §11.2 N2, HEAD differs at 720 and S at 800); N3 forbids unconditional preservation of all slow predicates.
The current spec already resolves the r164 textual faults. Older reports
and registry pins that contain those claims do not override it.
