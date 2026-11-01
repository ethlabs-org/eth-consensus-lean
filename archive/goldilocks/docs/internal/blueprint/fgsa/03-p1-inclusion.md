# FG-SA blueprint: inclusion and global P1

_Date: 2026-09-28. Stage 2a. Status: paper proofs; no composed Lean certificate._

## 1. Authority, statements, and proof boundary

window port: 01 §10 C1 family deadlines and guarded healthy prefix (pending)

The authority is [fgsa-protocol.tex](../spec/fgsa-protocol.tex), SHA-256
`a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.
Window authority: C1 and R6-window; the current spec changes only reviewed
status text from this rule pin. Positive proofs below retain their
old-fold scope; their window ports are pending. Section 10 negatives are
window checked. Historical line citations
keep their archive basis. Current registry successors are in 00.

Citations explicitly marked 4e85ff34 use that archive's numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the adopted spec c1ea1db0 changes only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.

Unqualified absolute spec line citations refer to the 2e884811 archive;
the r214 paragraph above applies only to citations explicitly marked 4e85ff34.
The rule change and execution transfer are proved in 01 §6.5.
The ids and target statements are from [00-outline.md](00-outline.md).
The proofs below use the proved lemmas of [01-foundations.md](01-foundations.md)
and [02-clean.md](02-clean.md) by id. Earlier reports supplied proof ideas
only. No proof step depends on an earlier report or on a repair in another
report. This file changes no protocol rule.

The positive targets below match 00 §3.3. This file makes the historical
“arming boundary” precise: the lease clause of bp.outageCompatibility.v2
starts at the **pending gate**, not at the outage start. Section 10.1 refutes
its interpretation as a lease-or-finality assertion at b₀. Sections 6–8
prove the corrected statement, including retention before that pending gate. Both P1 statements
keep their original lags, premises, budget, and global conclusion.

```text
┌───────────────────────────────┬────────────────────────────────────────┐
│ Id                            │ Status in this file                    │
├───────────────────────────────┼────────────────────────────────────────┤
│ bp.cleanPrefixTruncation.v2   │ PORT PENDING; old-fold proof, §1.3     │
│ bp.scoreSuffix.v2             │ PORT PENDING; old-fold proof, §3       │
│ bp.exactProposal.v2           │ PORT PENDING; old-fold proof, §4       │
│ bp.cleanInclusion.v2          │ PORT PENDING; old-fold proof, §5       │
│ bp.cleanGrowth.v1             │ PORT PENDING; proof, §5.1              │
│ bp.outageCompatibility.v2     │ PORT PENDING; old-fold proof, §8       │
│ bp.fastP1.v2                  │ PORT PENDING; old-fold proof, §9.1     │
│ bp.slowP1.v2                  │ PORT PENDING; old-fold proof, §9.2     │
│ fj.armedSafe.v2               │ PORT PENDING; old-fold proof, §9.3     │
│ bp.pendingBoundaryNegative.v1 │ PROVED-paper (window checked), §10.1   │
│ bp.targetExtensionNegative.v1 │ PROVED-paper (window checked), §10.2   │
└───────────────────────────────┴────────────────────────────────────────┘
```

00 lists the truncation and both negative ids. The positive window targets
retain PORT PENDING; this file keeps their old-fold proofs. Section 5.1 adds
bp.cleanGrowth.v1 with the same port boundary. The two §10 negatives are
checked for the window; their PROVED-paper status includes that scope.
The statements agree with 00 §3.3 with the explicit read convention and
arming boundary below. The broader whole-event read wording in 00 §2.1
does not specify the inclusive time cut; §1.1 below supplies that limit. The HEAD and F clauses in §9 are additional results.
The mapping table in 00 §3.4 concerns stages 2b and 3; it supplies no new
stage-2a id. The external registry is unchanged. Neither negative refutes service or P1.

### 1.1 Exact premises and notation

window port: 01 §10 C1 family deadlines and guarded healthy prefix (pending)

Use the outline's Base trace model, checked objects, static faulty set,
hidden per-slot seat bijections, parent paths, collision freedom on full recursive named proposals in the delivered/held/ancestor run scope,
and atomic handlers. All honest nodes run all scheduled ticks, including
sleeping nodes. Only awake nodes emit duties. A public read at integer time
t includes **all events with time ≤t**, in their trace order. Thus S_y(t),
F_y(t), and the lease state at t include every tick and delivery at y through
t. This is `Run.readAt` in AC `AvailableChainModel/Generic/Run.lean:130`.
A cut between events at the same time is only a proof device; it is not a
public read at that time. Duty and gate inputs refer to their actual local
execution positions, before any later same-time delivery. Write F_y^HEAD(s)
for F at y's label-s HEAD input. At a given node, the tick precedes
deliveries at the same time. Thus a row emitted by an action at a gate time
cannot affect another node's input to that gate. No future gate is presumed
to exist beyond the finite proof horizon.

Let n≥1, Δ>0, Δ_F≥Δ, k≥2, R≥max(2,κ), and δ_t≥0 be integers,
where κ=ceil((6Δ+Δ_F)/(4Δ)). Put
τ=⌈n/2⌉, q_F=⌈2n/3⌉, L=(4k−1)Δ and Π=min(η,L), with η≥0.
There are a faulty identities. On the healthy interval, the awake honest
count satisfies h_t>a at **every integer time**, not only at vote times.
The bound h_t+a≤n follows from disjoint honest and faulty seats and the
seat bijection. It is a model fact, as proved by
`SA.awake_add_faults_le_seats` in `AvailableChainSA/Proofs/FastOutage.lean:13`;
it is not an extra OutageRegime field. Therefore 2a<n, a<τ, and a<q_F.
No proof below requires a≤⌊(n−1)/3⌋, h>2a, R≥3, or δ_t=2R.

Write g for genesis, X⪯Y for ancestry with equality, X∥Y for
compatibility, and X#Y for conflict. Write ht(X)=σ[X].h. A result
C_(x,r) is the actual genuine result at x's gate, before its guard.
An empty result is ⊥. This event value differs from its later mutable saved
body. Source means an actual successful fresh fast-write source for an
honest FG height pair, as in bp.sourceDiscipline.v2.

The times are
`t_r=4rΔ`, `v_r=t_r+Δ`, `e_r=t_r+2Δ`, `z_r=t_r+3Δ`,
`q_r=t_r+5Δ=v_(r+1)`, and `d_r=t_r+6Δ=e_(r+1)`.
A gate d_r precedes the FG action there, if any.

Clean means Base, healthy emission and checked receipt delivery from genesis,
and a<h_t≤n−a throughout the required horizon. A receipt promise gives a
checked handler call with dependencies in less than Δ for blocks and HEAD
votes, and less than Δ_F for FG rows (C1). Only a block
incompatible with receiving F is excluded. A vote or row has no exclusion.
A cap can refuse an exact signature; it does not remove the evidence already
in the pool. A refused block creates no carried-object calls.

For P1, use exactly the fields of
`AvailableChain.Statements.Generic.OutageRegime` and `FastOutageRegime`,
with the FG-SA interface and the SA constants:

- valid execution and the Base₂ full named run collision premise; geometric root identity follows
  only on its projected scope, which does not automatically equal a generic emitted-body scope;
- `HealthyPrefixDelivery` to b₀, including receipt relay;
- 0≤T≤b₀≤b₁≤horizon, T+A≤b₀, and b₁−b₀≤Π;
- `sleepyBefore`: a<h_t for every integer 0≤t<b₀;
- at these times, `2|H_t| > |(⋃_(u∈[t−η,t]) H_u) ∪ Faulty|`;
- for fast P1, h_t≥τ on that whole healthy prefix.

Here A=4Δ for fast P1 and A=L−3Δ=4(k−1)Δ for slow P1.
No delivery or participation premise is added inside [b₀,b₁). In particular,
b₀ need not be a public time. The η condition is retained as a contract
premise; the proof below only uses its stated budget bound and the separate
awake majority. The definition of healthy delivery requires a delivery only
when its full deadline is at most b₀. Every use below checks that condition.

### 1.2 Exact reused facts

window port: 01 §§3–4,6–8,10 window origins/store/frame/receipt (pending)

`bp.cleanHistory.v2` gives nonempty ordered Clean genuine history, same-label
compatibility, and retrospective transfer: C_(x,r)⪯every honest label-(r+1)
HEAD at q_r. Every Clean source, saved body, lease target, F, J and S lies
on the ancestor closure of that history. Reconcile removes none of those
Clean bodies. `bp.cleanSafety.v2` gives global output compatibility and
local output monotonicity in Clean.

`bp.sourceDiscipline.v2` gives a successful gate origin for every honest
actually emitted height pair, including permitted timeouts at new entries. A nonzero justified
entry has q_F target signers; a crossing has q_F progress signers; finality
has its own earlier target QC as a window entry, not necessarily the
latest J. StaleUseful sets no height bits, so every target QC and crossing
has an honest HeightMatch source at that height, since q_F>a. Its named entry is a prefix of its source body. A source
usable before the gate d_r has a label below r.

`bp.chainCertificates.v2` gives monotone chain height, a unique entry on an
equal-height plateau, and the certificate extraction just stated.
`bp.store.v2` gives cumulative parent-closed T, immutable states and first
stamps, monotone F, and an admitted carrier K with σ[K].F=F.
`bp.frame.v2` gives the exact live frame and its full-store reads.
`bp.leaseOrigins.v2` gives the chain of live targets and their successful
gate origins. `bp.reconcile.v2` gives the exact deletions and normalization.
`comp.outputNesting.v3` gives stored F⪯S after every completed event.

`bp.receiptCoverage.v2` transports required paths by checked calls: if
F⪯B, paths above B admit; if B⪯F, output and every rooted walk cover B
already. It also gives vote-or-two-signatures within the slot window.
`bp.release.v1` bounds release by a when honest votes are compatible with
B. `bp.suffixWalk.v1` proves that strict dominance on an eligible suffix
makes the walk cover it. These are current statement ids; the concrete Clean/P1 suppliers remain
PORT PENDING. The retained proof uses their old-fold instances.

### 1.3 Clean prefix truncation — bp.cleanPrefixTruncation.v2

window port: 02 §5 window prefix replay through b₀ (pending)

**Statement.** Assume Base, 0≤b₀≤horizon, healthy emission and receipt
relay to b₀, and h_t>a for every integer 0≤t<b₀. The Clean lemmas of 02 apply on [0,b₀]:
its event-prefix invariant holds through all events with time ≤b₀, and
bp.cleanSafety.v2 holds for public reads in that interval. In particular,
for every label r with d_r≤b₀, bp.cleanHistory.v2 gives nonempty results,
ordered history, same-label compatibility, and bp.cleanTransfer.v2 to the
actual HEAD inputs at q_r. Origins, frames, leases, saved bodies, F,J and
S have the Clean properties of 02 for these prefixes. No participation at
or after b₀ is required. No delivery deadline beyond b₀ is used.

**Proof.** Restrict the event induction of 02 §5 to the prefix with event
times ≤b₀. Base, authentic origins, the handler order, and stored evidence
restrict to this prefix. At each included gate d_r≤b₀, the delivery uses
in 02 §§2–4 have the following bounds:

- The honest label-r emission at v_r has deadline e_r<d_r. If the next
  label's honest batch is used, its deadline is e_(r+1)=d_r.
- Same-label safety relays early votes accepted before e_r. Their receipt
  deadlines are before e_r+Δ=z_r<d_r.
- Forward transfer relays votes and paths accepted before e_r, with
  deadlines before z_r. Frozen votes accepted before z_r have reverse
  deadlines before z_r+Δ=t_r+4Δ<q_r. Carried votes and cap evidence
  accepted before the HEAD input at q_r have reverse deadlines before
  q_r+Δ=d_r. The strict stamp and tick-before-delivery rules exclude a
  receipt at q_r from that HEAD input.

Thus every delivery obligation used for label r has its full deadline
≤d_r≤b₀. HealthyPrefixDelivery supplies each checked call. The relevant
honest vote times are v_r<d_r and, when needed, v_(r+1)=q_r<d_r, so all
participation uses are strictly before b₀, even when d_r=b₀.

The gate proof in 02 §5.4 uses earlier labels and those local receipt
facts. Its retrospective transfer refers to q_r<d_r, already in the
prefix. The gate guard, lease and S steps, source action, and block
handlers use earlier origins and the current prefix invariant. They need
no future receipt. A same-time source row can affect a receiver only after
its tick. Such later deliveries are covered by the block-handler induction
in 02 §5.3. Consequently the invariant holds through **all** events at b₀.
Expiry and release only delete targets; ordinary events preserve the
invariant as in 02 §5.2. This proves prefix closure as in 02 §5.7.
The compatibility and monotonicity proof of 02 §6 now applies to any two
public reads in [0,b₀]. This proves the statement without extending the run.

The Lean analogue is `G.cleanThroughLabel_of_outage` in
`AvailableChainGridCO/Proofs/Regimes.lean:136`, using
`G.synchronousLabel_of_outage`. It gives CleanThroughLabel for d_r≤b₀.
The argument above supplies the composed handler and read cases; it does
not apply a plain GridCO run theorem directly to FG-SA.

## 2. A common Clean comparison prefix

### 2.1 The comparison prefix D for slot s

window port: 01 §8.4 prior target source of each window finalization (pending)

Fix an honest awake proposal slot s>0. For s=1 put D=g. For s≥2 let D
be the deepest genuine result among all honest gates with labels at most
s−2. Those gates precede t_s. There are finitely many results; they are
nonempty and compatible by bp.cleanHistory.v2. Hence D exists and contains
every such result. The last label suffices to find the maximum.

At every event from the proposal input at t_s through the HEAD inputs at
v_s, each usable honest FG source has label at most s−2. The next gate is
d_(s−1)=t_s+2Δ. Thus each such source body, each live lease target, and each
accepted or disclosed justified/finalized entry is a prefix of D. In
particular F⪯Z⪯D and the live root is a prefix of D.

There is no contest in this interval, by bp.cleanFrame.v2. Moreover each
local floor satisfies lo=H−1≤ht(D). For H=1 this follows from ht(D)≥1.
For H>1, choose a stored maximal-height block W and extract its crossing
of H−1. StaleUseful sets no height bits. Thus an honest HeightMatch source of
that crossing has height H−1 and is a prefix of D. Height monotonicity gives the inequality. This argument is valid for
late disclosures after t_s too; their signature origins still precede the
next gate. It uses full T, not the HEAD view.

Every honest label-(s−1) HEAD extends D. For s≥2 this is exactly the
transfer clause of bp.cleanHistory.v2 for every label-(s−2) result. For
s=1 the label-0 HEAD is g. These honest signatures and heads reach all
honest stores before e_(s−1)=t_s−2Δ, and remain active because F⪯D.
They therefore belong to both the proposal pool and the HEAD's frozen
previous-slot support. No honest seat equivocates. At either read the
number of participants is at most h_(s−1)+a. Thus each path vertex toward
D has score at least h_(s−1), and each branch conflicting with D has score
at most a, including equivocators. Strict majority and strict dominance
follow from h_(s−1)>a.

D and its required path are known before z_(s−1). To verify this without
assuming that a gate broadcasts its result, choose a surviving early
supporter of the non-genesis result D. Its head contains D and was admitted
before e_(s−2). Receipt relay carries that path before z_(s−2), which is
strictly before z_(s−1). All receiving F values are below D. Genesis needs
no receipt. The same proof covers each ancestor of D.

At both reads, D itself supplies a witness of height at least lo. Every
vertex after the live root through D is in the appropriate filtered domain:
in full T for the proposer, and in the pre-freeze arm for the voter. The
strict score inequalities and bp.suffixWalk.v1 make each walk reach D.
This proof permits different starting roots and different live floors.

## 3. Score algebra and its run producer — bp.scoreSuffix.v2

window port: 03 §2.1 window frame and 01 §10 receipt (pending)

**Exact statement.** Let U⊆U' be raw sets. Suppose every vote in U' is in
U or has a seat with two distinct votes in U. For every candidate X in a
specified suffix above receiving F, suppose support incidence agrees for
each seat that does not equivocate in U. Then participant sets, equivocation
sets, and scores on that suffix agree. In Clean, at each admitted honest
proposal P of slot s, its carried raw/support sets and the receiver's
freeze-plus-P merge satisfy these conditions on every candidate X⪰D,
where D is the common comparison prefix of §2.1. This is the suffix
used by exact proposal adoption. No ordering of F_p and F_y is needed.
The support incidence includes valid head slots and head membership.

**Algebra.** A new raw vote contributes no new seat, since its seat already
has two signatures in U. Conversely U⊆U' preserves every old seat. The
participant sets agree. Equivocators of U remain equivocators in U'. A
seat that was not an equivocator cannot get a genuinely new signature,
by the reverse condition. Thus the equivocator sets agree too.

For a fixed X, an equivocating seat contributes one in both scores. A
nonequivocating seat contributes the Boolean statement that a declared,
valid-slot head stored in the relevant view extends X. These Booleans agree
by hypothesis. Sum over the common finite participant set. This proves the
score equality and also the common majority threshold.

**Run producer.** Let U be the complete previous-slot pool copied into P,
and Q its originally declared resolved subset. Authentication makes P the
only current-slot proposal in the receiver's admitted T. Its carried U is
included literally in U', even when a local carried-vote handler refused a
copy. Cumulative storage retains that original metadata.

Each extra vote of U' is a frozen previous-slot vote, accepted at the
receiver before z_(s−1)=t_s−Δ. Its receipt deadline at the proposer is
strictly before t_s. The checked call is within the current/previous-slot
window. If it is absent from U, the proposer has two distinct same-seat
signatures by then. This proves raw-back-or-equivocation. It makes no
assumption that a refused signature became accepted.

Fix X⪰D and a nonequivocating seat i in U. Section 2.1 gives
F_p⪯Z_p⪯D⪯X and F_y^HEAD(s)⪯Z_y^HEAD(s)⪯D⪯X.
Monotonicity of F gives the same bounds at the earlier receipt reads.
There are two directions for support incidence.

1. If the proposer's declared head K extends X, it was stored and active
   at the proposal read. Its slot is at most s−1. Receipt relay of its
   earlier block acceptance carries K to the receiver before v_s. Since
   all receiving F values through that read are below X≤K, K admits or
   is already stored. Its original declaration is still read from P.
   Thus i supports X at the receiver.
2. A receiver support from P's original declaration was already declared
   by the proposer; if K≥X its original support remains a witness there.
   For an extra frozen support, both the raw signature and resolved head
   existed before z_(s−1). Relay puts the signature or cap evidence and
   the head at the proposer before t_s. Cap evidence is impossible for
   this nonequivocating i. Also K≥X≥F_p, so head exclusion is impossible;
   dependencies give admission or prior storage. The valid slot is
   unchanged. Hence that signature was resolved at the proposal read and
   belongs to Q.

Both honestly held resolutions of each signed root are in run scope.
Injectivity makes them the same body at the proposer and receiver, so the
ancestry tests in both directions agree.
This proves the required incidence equality. Heads excluded by F_y cannot
support X⪰D⪰F_y. They may still affect raw participation and equivocation;
those effects have already been counted. We neither delete containers nor
claim literal equality of raw sets or support sets.

The pure algebra corresponds to
`G.ScorePreservingViewExtension.count_eq`, `.equivocates_eq`, and `.score_eq`
in `AvailableChainGridCO/Proofs/ScoreExtension.lean`. Here G denotes
`AvailableChain.GridCO`. The new producer above handles the different
active views. The full support-subset hypothesis of that Lean structure is
replaced, where necessary, by the proved per-candidate incidence equality.
Also, `.score_eq` at `ScoreExtension.lean:145` requires its explicit `ht`
premise: for each source support vote with target K,
`K ∈ tree ↔ K ∈ tree'`. The structure alone does not supply this premise.
A Lean port must prove it together with the structure fields, or prove a
restricted `score_eq_on` from the incidence argument above. No such new
Lean declaration is claimed here.
Equal scores do not by themselves give equal band eligibility. Section 4
supplies that separate argument.

## 4. Exact proposal adoption — bp.exactProposal.v2

window port: 01 §§1.1,4 window R6/store and source bounds (pending)

**Exact statement.** In Clean, for each honest awake proposal P at t_s,
s>0, every honest node admits P before v_s. Every honest awake label-s
HEAD equals P. The deterministic HEAD read of a sleeping honest node also
equals P, although it emits no vote.

Let Q=P.parent, and let D be the prefix of §2.1. The proposer's full-tree
walk reaches D, so D⪯Q. Every receiving F before v_s is below D, by the
source-label bound. Thus P extends receiving F. Honest emission delivers
P with dependencies before v_s. A current honest proposer signs only this
P. It has a strictly earlier-slot parent, R6-window-valid carried rows,
and a valid signature. R7 tests each row against σ[Q], the deterministic
post-state of the exact named parent. Every receiver has that same state;
all rows pass before the fold, so row order cannot change admission.
Both honestly held resolutions of P and Q are in run scope: each signed
root names one body at every honest store. If P is absent, all admission checks pass. If P is present,
admission has already occurred. There is no finality-coverage alternative
that loses the exact block: receiving F is below D≤Q≺P.

At a voter's read, every prefix of P is in its current-proposal path arm.
For every path vertex X from D through P, ht(P)≥ht(D)≥lo_y. Hence P
is a witness for X inside that very HEAD view. Also F_y⪯Z_y⪯D⪯X.
Thus this path is in D_y(V_s). This proves path persistence with an
internal witness, not by intersecting V_s with D_y(T).

Both walks first reach D by §2.1. Reanchor their remaining walks at D.
For every parent X≥D, ht(X)≥ht(D)≥lo_p,lo_y. The low-parent eligibility
arm is therefore false in both walks. For an old child, the current-slot
arm is false too. Old-child eligibility is exactly the majority test,
which agrees by §3.

Now fix X on the selected proposer path from D to Q.

- **Persistence.** A selected child C toward Q is a prefix of P, so is
  in the receiving domain by the P witness just proved. It is an old
  child and has the same score and count, so remains eligible.
- **Reflection.** An old eligible child C of X in the receiving HEAD
  view either belongs to the path of P or was admitted before z_(s−1).
  A path child of P is in the proposer's parent path. A frozen child
  reaches the proposer before t_s by receipt relay. It extends X≥D≥F_p,
  so it is not excluded. In both cases it is stored at the proposer.
  Since ht(C)≥ht(D)≥lo_p, C witnesses its own full-domain viability;
  it extends Z_p. Its majority eligibility agrees by §3.

At each such X before Q, the two walks compare the same scores and the
same root order on all relevant competitors. Every winning proposer child
persists, and every receiving competitor reflects. Thus the receiving
winner is the same child. Induction over the finite path reaches Q. This
is the persist/reflect proof, not an appeal to equal whole domains.

At Q, P is present, viable, and eligible by its current slot. No old
eligible child of Q can exist at the receiver: reflection would make it
an eligible child at the proposer's terminal Q. No other current-slot
child exists because the proposer is honest. Thus the next step is P.
No child of P can be present at v_s: its slot would have to exceed s,
and future blocks are refused. The returned HEAD is exactly P.

The finite path has distinct blocks by increasing parent slots. Its length
is at most the cardinality of the walked finite view, so the usual GHOST
fuel suffices. Reanchoring does not assert that the initial live root belongs
to the walked view. Section 2 proved its suffix to D instead.

The pure proof shape is `G.ghost_adopts_fresh_child` and `G.ghost_reanchor`
from `Proofs/WalkTransport.lean`, and DC's
`Proofs.HealingSurface.NamedProposalPivotSuffixTransfer.persist/reflect`.
The producers above establish the changed FG-SA domain, band, root, and
receipt premises. They do not instantiate a plain-SA run theorem with a
mixed run.

## 5. Pending-label inclusion — bp.cleanInclusion.v2

window port: 01 §6.6 and 02 §6 window monotonicity; 6Δ (pending)

**Exact statement.** In Clean, P as in §4 satisfies P⪯S_y(d_s) for every
honest y, and P⪯S_y(t) at all later reads within the Clean horizon.
Since d_s=t_s+6Δ, this is the stated 6Δ service bound.

The gate of label s−1 is still pending when the label-s HEADs vote. For
each of its results C_(x,s−1), bp.cleanTransfer.v2 states retrospectively
that C_(x,s−1) is a prefix of every honest label-s HEAD. Section 4 makes
those heads P. Thus **every pending result is a prefix of P**, including
a result computed after those votes. This use has no circular dependency:
§4 used only labels at most s−2; stage 1 proved transfer without exact
proposal adoption or inclusion.

Before the input to d_s, each usable source has label at most s−1.
Every earlier result is below a label-(s−1) result, and each such result
is below P. Consequently every receiving F and J, every lease target,
and every successful previous gate body is a prefix of P. Honest label-s
votes therefore keep their active head P. The block and signatures arrived
before e_s by honest delivery; the original strict stamps remain. There
are h_s non-equivocating honest supporters and at most a other seats.
For every prefix of P, 2p≥2h_s>h_s+a≥D_late. No branch conflicting with
P, and no strict descendant of P, has more than a surviving supporters;
its support p would require 2p>D_late≥h_s+p, which is impossible.

By 01 §6.6, F≺P at the gate; the confirmation walk from the eligible F therefore returns exactly P. The guard
passes because all existing live targets are prefixes of P. The gate
saves P, advances the old S to a value containing P, and writes any leases
whose tests pass. The record advance does not require either lease test.
Normalization cannot remove P, since F⪯P. At the action after this gate,
a fresh source can be P or a prefix of P; it cannot change the preceding
gate input. Same-time deliveries after the tick preserve the Clean chain.

Finally bp.cleanSafety.v2 supplies local monotonicity at every later read,
including delivery events and normalization. Hence P remains in every
honest S. This also covers sleeping readers and an S whose previous origin
was F normalization. The proof is the composed replacement for
`G.clean_honest_proposal_repair` and `SA.included_from_engine`.

### 5.1 Clean strict growth — bp.cleanGrowth.v1 — PORT PENDING

Assume Clean₂ from time 0, awake-proposer recurrence on every (t,t+G]
within the horizon, G≥4Δ, 0≤t, and t+G+6Δ≤horizon. There is one
honest proposal P, at t<t_s≤t+G, such that both available accessors
satisfy output_x(t)≺P and P⪯output_y(t+G+6Δ) for every honest x,y.
The following proof uses the pending window producers in §§2.1,4,5.

1. Awake-proposer recurrence supplies an honest awake slot s with
   t<t_s≤t+G. The proposal duty emits P there; t≥0 gives s>0.
2. Each gate origin of S_x(t) has d_r=4rΔ+6Δ≤t<t_s=4sΔ,
   hence r≤s−2. For an F origin, window provenance gives the entry
   its own earlier target QC and honest HeightMatch source. That source
   is below its successful gate result, whose gate occurred by t.
   Genesis is immediate; at s=1 no non-genesis gate origin exists.
   The full S/F origin argument is in §6 (lines 507–524); the source
   and monotonicity facts are in §1.2.
3. Section 2.1 defines D to contain every such result and makes the
   proposer walk reach D. Thus S_x(t)⪯D⪯parent(P)≺P for every x.
   This proves strict growth at the earlier read, which inclusion alone
   does not supply.
4. Section 5 gives P⪯S_y(d_s), where d_s=t_s+6Δ≤t+G+6Δ.
   Clean monotonicity preserves this prefix through the shared deadline.
   comp.outputNesting.v3 identifies both available accessors with S.

This is CleanGrowthClaim and AvailableGrowthConcl in
AvailableChainFGSAClaims/Claims/Outage.lean at e1d4232. It includes
sleeping readers and uses no delivery or gate beyond the stated horizon.

## 6. From an arbitrary protected read to the pending gate

window port: 01 §§3.1,8.4 window target-QC origin and F coverage (pending)

Fix B⪯S_x(T), with x honest, in either outage regime. Genesis is immediate;
assume B≠g below. Let s be an actual honest successful gate origin with
B⪯C_(u,s) and d_s≤T. Such an origin exists even when the protected read
was created by finality. Here is the complete origin argument.

An S write is either a successful gate advance or normalization to F. If
an advance kept the old value, trace the old value backwards in the finite
local event list. A new gate value has the required genuine origin. For an
F value, extract the finalized window entry (x,X) and its own earlier
target QC for (x,X), one honest HeightMatch target signer since q_F>a,
and its actual successful fast source by bp.sourceDiscipline.v2. The
entry need not be the latest J; window provenance supplies this origin.
That source is a prefix of its gate result C, and F is a prefix of that
source. Its gate occurred no later than the F read. At that gate the
successful advance made its honest source node's S contain C. Thus B has
the required gate origin, possibly at another honest node and earlier than
T. Genesis is the only origin with no such nontrivial gate. This argument
does not use the plain-SA assertion that S changes only at gates.

Let l be the last gate label with d_l≤b₀, and put j=l+1. It exists
because d_s≤T≤b₀. The lag gives

- fast: l≥s+1;
- slow: l≥s+k−1, and hence l≥s+1.

For example, the slow inequality follows from
`d_(s+k−1)=d_s+4(k−1)Δ≤T+A≤b₀` and strict increase of gate times.
Consequently

```text
 e_j = d_l ≤ b₀ < d_j = d_l+4Δ,
 j ≥ s+2  (fast),             j ≥ s+k  (slow).
```

Let D be the deepest genuine result through label l, over all honest nodes.
Those results obey the Clean lemmas by bp.cleanPrefixTruncation.v2 (§1.3).
Its deadline bound includes d_l=b₀ and requires no participation at b₀.
By ordered history, B⪯D and every label-l result contains B. Each honest
gate makes its S contain its own label-l result. The remaining same-time
events preserve that coverage by the prefix invariant. Thus every public
S_y(d_l), after all events through d_l, contains B.

Every honest label-j HEAD, emitted at q_l=v_j<e_j≤b₀, extends every
label-l result and hence D. The retrospective stage-1 transfer uses receipt
deadlines at most d_l, so the healthy prefix supplies it. These heads and
votes arrive before e_j=d_l≤b₀. This is the **last complete healthy batch**.
Its awake count h_j exceeds a. Fast additionally gives h_j≥τ. All nodes,
including sleepers, receive it.

### 6.1 The interval before d_j

window port: 01 §§3.1,8.4 window target-QC origin and F coverage (pending)

Before time d_j, any usable FG source has label at most l. No gate or FG
action occurs strictly between d_l and d_j. Thus every source body and
lease target in this interval is a prefix of D; all F,J are also prefixes
of D. The Clean source-entry argument still proves no contest and
H−1≤ht(D), even for blocks disclosed during this part of the outage.
Only its signature origins are used; no outage relay is assumed.

The honest label-j heads extend D, so they remain active throughout this
interval and at the input to each gate d_j. Their early stamps are retained.
No new faulty signature can equivocate an honest seat. At any reader's
pending gate, support on D is at least h_j and late participation is at
most h_j+a. Each branch conflicting with D has only faulty support and
cannot obtain a strict majority. Since F⪯D, those votes also make F
eligible. The confirmation walk from F reaches D, so C_j exists and
extends D. Every pre-gate lease target is below D, so its whole-result
guard passes.

There is no gate strictly inside (d_l,d_j), so S changes there only by
F normalization. Its old value and F are on the ancestor closure of the
Clean results through l. They are compatible; normalization can only
extend S. Therefore all S retain B on [b₀,d_j), whether or not a lease
has yet been written on B.

We also need the HEAD emitted at q_j=d_j−Δ, before the safe gate. Its
frozen pool contains the complete honest label-j batch with heads above
D. Those heads arrived before e_j<z_j. Extra frozen or admitted-carried
votes have only the other a seats; authentication prohibits an extra
honest label-j signature. Each edge toward D therefore has score at least
h_j and each conflicting edge at most a. The participant count is at
most h_j+a. D is in the frozen block arm: each reader already stored the
complete batch above D before e_j. It witnesses its own height against
the floor H−1≤ht(D). The live root is a prefix of D. The suffix walk
therefore covers D and B. This uses only local stored data, not relay
between q_j and d_j. It is the composed `SA.pending_heads_cover` step.

The only proposal time strictly between d_l and d_j is
`t_(j+1)=d_l+2Δ=d_j−2Δ`. If an honest awake proposer acts there, it
reads its current full pool `gf_votes[j]` through that duty input, including
receipts after the freeze; it does not read only the frozen pool. All h_j
honest label-j votes and their heads were stored before e_j=d_l. Each head
extends D and remains active because F⪯D; its slot is valid. Thus those
votes resolve as support in the proposer's active full tree. Authentication
allows no further honest label-j signature, and faulty signatures add at
most a seats. Participation is therefore at most h_j+a. Every path vertex
toward D has score at least h_j, while each branch conflicting with D has
score at most a, including equivocators. Since h_j>a, the path has a strict
majority and strictly greater score than every competing branch.

D is stored in full T. The frame has no contest, F⪯Z⪯D, and
lo=H−1≤ht(D). Thus D witnesses every vertex from the live root through D
in the full filtered tree. Every live lease target is below D, so the live
root is below D too. Apply bp.suffixWalk.v1: the proposal parent extends D
and hence B. If t_(j+1)<b₀, this same local argument still proves coverage;
if it is beyond the horizon, no such duty is asserted. There is no FG
action strictly between the two gates. Together with the HEAD step above,
this proves coverage for all honest duties in [b₀,d_j). Reads after b₁
are not required.

These arguments do not evaluate a gate beyond the horizon. If the requested
time t satisfies t<d_j, the already received batch, prior origins, and
local read at t suffice. Use the pending-gate proof only if d_j≤t<horizon.

### 6.2 The pending write at d_j

window port: 01 §§4,6 window F-advance/reconcile and lease-or-F (pending)

Consider each node's gate tick at d_j. A newly emitted label-j source row
at this time cannot be delivered before this local tick. Its pre-gate
sources thus still have labels at most l. Section 6.1 gives C_j≥D≥B,
a passing guard, and prefix support p(j,B)≥h_j.

In fast mode h_j≥τ, so B passes fast admission. In slow mode the previous
k−1 labels are `j−k+1,…,j−1`. Since j≥s+k, every such label u satisfies
u≥s+1. Its actual genuine result at every honest reader contains B by
Clean ordered history. Each was evaluated and saved. Before this pending
tick all disclosed source bodies are still on the Clean chain, so reconcile
has not emptied one of those saved bodies. Thus the slow test passes.
The current result C_j contains B as required by the caller.

B is stored and active. The gate writes its deadline at least
`D_exp=d_j+L`, and advances S to contain B. Expiry runs before this write,
so expiry at d_j cannot delete the new lease. A max-renewal cannot shorten
it. These statements hold for every honest reader.

After the tick, an F delivery at the same time might empty a saved result
above B or remove a lease above B. The induction in §§7–8 proves that it
either keeps B's lease or gives B⪯F. It never requires all saved bodies
above B to survive such later events. Evaluated labels remain evaluated.

The deadline is strictly beyond the whole requested outage:
`b₁≤b₀+L<d_j+L=D_exp`. This strict inequality is valid also when
b₀=d_l=e_j. No endpoint convention is hidden in the calculation.

## 7. A frame lemma for sources compatible with B

window port: 01 §§3.1–3.1a,8.4 window provenance/height plateau (pending)

This section does not assume Clean or a single chain of sources above B.
Assume every honest FG source in the current event prefix is compatible
with B, and q_F>a. Then every disclosed justified or finalized entry is
compatible with B. To prove it, extract an honest target source from each
justification, using its actual signature origin. Its entry is a prefix of
that source. A prefix of a block compatible with B is compatible with B.
A finalized entry has an earlier justification, so it has the same property.
This also applies to privately carried and previously unseen certificates.

Suppose B is stored and F⪯B. Then either B⪯Z, or B belongs to the full
filtered domain D_Σ(T). Here is the witness proof for every frame case.

If B⪯Z, every walk extends Z or a descendant of Z, so covers B.
Otherwise Z⪯B, because Z is F or J and is compatible with B.

If the frame is not contested, lo=H−1. For H=1, B witnesses itself.
For H>1 take W∈T of height H and its crossed entry E at height H−1.
A crossing quorum has an honest source, so E∥B. If B⪯E, W witnesses
B. If E⪯B, ht(B)≥H−1 and B witnesses itself. All intermediate
vertices from Z through B have that same witness and extend F.

In a contest H=j+1, choose W of height H with J⋠W, as the definition
requires. The case j=0 is impossible since J=g. Let E be W's crossed
height-j entry. Both J and E are entries at height j. If comparable they
are equal by the plateau lemma, which would give J⪯W. Hence E#J.
Both E and J are compatible with B by their honest certificate sources.
In a parent tree, two conflicting blocks compatible with B must both
extend B: if either preceded B, compatibility with the other would make
them comparable. Thus B⪯E⪯W and B⪯J. In this case Z=F and
lo=H. W is the required height-H witness for B in full T.

This proves the claim also at the raised contest floor. It is not a claim
that an arbitrary HEAD has height at least lo, nor that W belongs to a
frozen HEAD view. Only the full-domain membership of the live lease is
needed for outage protection.

If B has a live lease and is in D_Σ(T), the deepest in-domain live target
contains B because live targets form a chain. The live root therefore
contains B. If B⪯Z, the same conclusion holds without a lease in the
domain. If B⪯F, it holds by F⪯Z. Every walk extends its start, even
when the start is outside the particular walked view or that view is empty.
Thus every one of these cases keeps all HEAD choices above B.

## 8. Joint outage induction — bp.outageCompatibility.v2

**Corrected exact statement.** Under either regime, for B⪯S_x(T), every
honest F at every read before b₁ is compatible with B. Every honest S
contains B on [b₀,b₁), and every honest HEAD or proposal parent chosen
there contains B. With l,j from §6, the interval [b₀,d_j) has the complete
healthy-batch protection of §6.1. At every honest public read with
d_j≤t<b₁, after all events with time ≤t, the node either has B⪯F_y(t)
or has a live lease on B with deadline at least d_j+L. In the latter case
B is in the full filtered domain or below Z. There is no first conflicting
successful result/source, or first departing honest HEAD, after this arming. If d_j is beyond the requested
horizon, only the first interval is needed.

The outline's phrase “from the arming boundary” means d_j in this precise
statement. Replacing d_j by b₀ in the lease clause is false in slow mode;
§10.1 gives an exact execution. Output and duty coverage nevertheless start
at b₀, so this correction does not weaken either P1 conclusion.

### 8.1 Initial data, and the one in-flight label

window port: 01 §§4,6–8 window frame/store at every event (pending)

All healthy-prefix F values are compatible with B by bp.cleanHistory.v2 and
the origin in §6. Section 6.1 extends that compatibility and output/duty
coverage to the input of d_j. Section 6.2 supplies the lease write and
record at every honest gate tick d_j.

For any label r whose vote has been emitted at or before d_j but whose
release is after d_j, the inequalities
`v_r≤d_j<q_r` give `r=j+1` by substituting the schedule. Its honest HEADs
were emitted at q_j, and §6.1 proved that they contain B. Thus no earlier
honest conflicting signature can later cause a release of B. This is the
premise represented by `G.ArmingHeadsCompatible` and proved arithmetically
by `G.in_flight_label_at_gate` and `armingHeadsCompatible_of_heads`.

Cuts among the events at d_j are proof devices, not public reads at d_j.
Before a node's tick, use the batch argument; after its tick, use the
lease-or-F invariant below. A newly emitted row cannot reach a receiver
before that receiver's tick. Interleave the pending-tick proof of §6.2
with the event cases of §§8.2–8.4 for nodes whose ticks have run. Thus a
same-time delivery after a tick either preserves the new lease or gives
F coverage. Once all events at d_j have run, every honest node satisfies
the lease-or-F clause. This is the public read at d_j. Apply the same
induction through all events at each later read time t<b₁.

### 8.2 Induction invariant and ordinary events

window port: 01 §§4,6–8 window frame/store at every event (pending)

Induct on causally ordered events with time less than b₁, including the
remaining deliveries at d_j. During time d_j, apply the invariant to each
node after its tick; use §6.1 for nodes whose ticks have not yet run. After
all events at d_j, maintain it at every honest node. In clauses 1 and 3,
“boundary” means d_j. These event cuts establish the public reads of §1.1:

1. B⪯S; every actual honest duty head emitted since the boundary covers B.
2. Either B⪯F, or F≺B and B has a lease with deadline at least D_exp.
3. Every actual successful gate body and honest FG source introduced after
   the boundary is compatible with B; all older sources are compatible
   with B as well. Raw vetoed results need not be compatible.
4. Every disclosed justified/finalized entry is compatible with B, and the
   full-frame coverage of §7 holds.

Unchanged-state receipt branches preserve these facts. Votes and row-pool
insertion do not write S, F, or leases. Cumulative block insertion can
change H,J,F; that case is handled separately below.

A tick first expires deadlines. Its time is less than b₁<D_exp, so it
cannot expire the selected B lease. Other expiries do not affect it.
At release, all relevant honest signatures either belong to the one
in-flight label proved above or to later duties already covered by the
induction. No honest signature conflicts with B. Therefore the release
count is at most a<τ. Active filtering can only reduce this count, and
raw equivocation evidence is kept. Release cannot remove B's lease.

At any HEAD or full-tree proposal/finality-head read, §7 gives a start
containing B, from its lease or its F coverage. Every subsequent step
extends that start. The duty therefore cannot be the first departure.
This proof places no conditions on the vote merge during the outage.

### 8.3 Gate and source events

window port: 01 §§4,6–8 window frame/store at every event (pending)

In the lease branch, a result C#B fails the whole-result guard. The node
can save that raw result, but cannot use it to change S, write a lease, or
create a fresh source. In the F-coverage branch B⪯F, all active heads
are compatible with B. A block C#B is not in the active tree, so cannot
be a genuine result at all. Genesis and ancestors below F cause no loss.

A passing result compatible with B preserves B in S. If C⪯B, then
C⪯S and `advance` keeps S. If B⪯C, either the old S already covers
C or the new S is C. All prefixes written by that gate are compatible
with B. A max-write cannot shorten the selected B lease. An empty or
vetoed gate makes no such writes. Slow windows containing empty or
conflicting raw saved bodies do not bypass the outer guard.

The fresh set is populated only on the successful gate branch, with fast
prefixes of C. Its source C_fg is one of those prefixes. Therefore it is
compatible with B. The action follows this gate atomically. Every nonempty
honest height pair, including a timeout, has this origin. The honest
finality-head read also starts above B, as proved in §8.2. Its justified
entry may be an ancestor of B, but cannot conflict with B.

Thus no first conflicting successful source can be created. Notice that
this is stronger than retaining only the local output, and weaker than
claiming that every raw result during an outage is compatible.

### 8.4 A block delivery that moves F: exact handler order

window port: 01 §§1.1,3–4,8.4 window derive/exact QCs; HeightMatch (pending)

Consider one block delivery in the induction. Validate the object and
parent before any admission or unpacking. A refused block changes nothing.
For an admitted block, compute its chain state from the admitted parent
and its full carried rows; insert it and its first stamp; then handle its
carried base votes. These steps do not yet change F or S.

Every certificate in the derived state has actual earlier signature
origins. A new justified entry X#B would require q_F target signers and
therefore an honest target signer. That signer's source contains X, hence
conflicts with B. It cannot be a healthy source, a pending source from
§6, or a later successful source allowed by §8.3. This is a contradiction.
A newly disclosed finalized window entry (x,X) has its own earlier
target QC for (x,X), so trace it to its honest HeightMatch target source;
X need not be the latest J. StaleUseful sets no height bits. Thus every
height crossing has an honest HeightMatch source at that height, compatible
with B. Every finality row has a height pair at a higher height. This rules out a first conflicting certificate by its
origin, before any decision to admit a relayed path or reconcile.

Next update H and J. The certificate facts just proved imply that all
entries used in the new frame are compatible with B. Section 7 supplies
the full witness in either the contested or uncontested frame. This covers
a rise of H without an F move.

If finality acceptance now assigns F':

- If F'≺B, every body or target K≥B is compatible with F'. In particular
  reconcile keeps B's lease. It also keeps every saved body containing B.
  Since F'⪯B⪯S, normalization leaves S unchanged.
- If B⪯F', reconcile can remove some branches strictly above B. It keeps
  B itself compatible, and normalization either keeps an S extending F'
  or assigns S:=F'. Either way B⪯S. Future F values extend F', so this
  node has permanent F coverage throughout the remaining induction.

There is no external event between F:=F' and reconcile. Reconcile leaves T,
chain states, original stamps, signed pools, and evaluated labels intact.
It does not replace a saved body by F'. After it finishes, the row handlers
run. They cannot change F, S, or leases. This completes the event proof.

Different nodes may take these two branches at different times. The proof
keeps a separate lease-or-F disjunction for each node and does not use any
message delivery inside the outage. The first-departure induction closes.

## 9. P1 and the assembled result

window port: 03 preceding window ports and review; no Δ_F restriction (pending)

### 9.1 bp.fastP1.v2

**Statement.** Under Outage(4Δ) and h_t≥τ throughout 0≤t<b₀,
for all honest x,y, all B⪯S_x(T), and all b₀≤t<b₁,
B⪯S_y(t). Here b₁−b₀≤min(η,L). This output clause is the Lean
conclusion `PersistsThrough`, defined in
`AvailableChainStatements/Generic/Properties.lean:107`.

**Additional conclusions.** Honest emitted HEADs and proposal parents in
[b₀,b₁) extend B, and honest F at every public read before b₁ is compatible
with B. These clauses are proved here but are not fields of PersistsThrough.

**Proof.** For g the claim is immediate. Otherwise §6 finds an actual
successful source label s with d_s≤T. The lag gives l≥s+1 and hence
common output coverage at d_l. Section 6.1 protects the possibly unarmed
interval to d_j. At d_j the complete label-j batch has h_j≥τ, so §6.2
writes B at every node with deadline d_j+L>b₁. Sections 7–8 retain the
lease or replace its role with F coverage, preserve the record, and prevent
every departing duty. This proves all quantifiers, including sleeping
readers and an S read originating in F normalization.

`SA.pending_fast_protection` and `SA.fastP1_from_engine` in
`AvailableChainSA/Proofs/FastOutage.lean` supply the SA template. The
composite proof above supplies the new source-origin, frame, and reconcile
cases; no plain-SA finality-free state equality was used.

### 9.2 bp.slowP1.v2

**Statement.** The same PersistsThrough output conclusion holds under
Outage(L−3Δ), without high participation. The budget remains min(η,L).

**Additional conclusions.** The HEAD, proposal-parent, and F-compatibility
clauses of §9.1 also hold. They are not part of the Lean PersistsThrough
conclusion.

**Proof.** The origin reduction is unchanged. The lag gives
l≥s+k−1 and j≥s+k. Every saved result in the preceding k−1 positions
at the pending gate therefore has label strictly greater than s and
contains B. Section 6.2 verifies the evaluated-label tests and shows that
no body in this particular window was emptied before it was used. The
current result also contains B and passes the whole-result guard. Thus B
gets its lease by the slow rule, even when every support count is below τ.
Section 6.1 supplies record and duty coverage before that write. The
remaining proof is exactly the event induction in §§7–8.

The lease is not presumed to exist at b₀. Nor is arbitrary preservation of
all future slow windows presumed: if a later F empties a body above B,
that F must already contain B, by the two ancestry cases in §8.4. Evaluated
labels remain evaluated and empty results are never recomputed. This is
sufficient for P1 and does not assert a false general slow-window invariant.

The corresponding SA declarations are `SA.clean_result_after_stable`,
`SA.pending_heads_cover`, `SA.stable_resilient_from_engine` in
`AvailableChainSA/Proofs/Outage.lean`, and
`SA.slowEligible_of_input_covers` in `Proofs/SlowWindow.lean`.

### 9.3 fj.armedSafe.v2

**Statement.** For the frozen FJ FG-SA protocol, the conjunction consists
of Clean global safety and local monotonicity, Clean 6Δ honest-proposal
inclusion, global fast P1 at lag 4Δ with the stated healthy high count,
and global slow P1 at lag L−3Δ, for every a<h and budget min(η,L).

**Proof.** Apply bp.cleanSafety.v2 to the two safety clauses, §5 to
inclusion, §9.1 to fast P1, and §9.2 to slow P1. Both available accessors
return stored S. comp.outputNesting.v3 holds at every completed event.
The field premises match §1.1; there is no additional quorum-intersection,
recovery, or finality-liveness premise. This completes the conjunction.

## 10. Exact negative executions and their scope

These checks were made after reading the current SA and DC Lean definitions
listed in §11. They are paper executions of the frozen FG-SA spec, with
integer times and explicit receipt schedules. They are not claimed to be
executed by a composed Lean model, which does not yet exist. The arming
bounds follow symbolically: d_s≤T and T+A≤b₀ give d_(s+1)≤b₀ in fast
mode and d_(s+k−1)≤b₀ in slow mode. The definition of l gives
l≥s+1 or l≥s+k−1 respectively, and d_l≤b₀<d_(l+1).
For j=l+1, the slow-window lower label obeys j−k+1≥s+1, and
b₁≤b₀+L<d_j+L. These inequalities apply to every allowed integer
parameter; no finite case count is used. Neither execution uses a
fabricated local state.

### 10.1 bp.pendingBoundaryNegative.v1: no lease at the slow boundary

**PROVED-paper (window checked).** The second Opus report replays this
execution after removal of the inert empty-row events. No row is sent, so
the window fold preserves the listed states and the negative conclusion.

**Refuted statement.** Under the slow regime, every reader already has
B⪯F or a live lease on B in the full domain or below Z at b₀=T+A_slow.
**Correct replacement:** §§6–8, with batch protection until d_j.

Set Δ=4, k=2, L=28, η=28, n=5, a=1, τ=3, q_F=4,
R=3, δ_t=6. Honest u,v are always awake. Two other honest
nodes are always asleep but run all ticks and handlers. The fifth identity
is faulty. The per-slot seat assignments can be any bijections; assign
votes by their actual holders. The faulty identity is proposer in all
positive slots through the horizon and is silent except for block B in
slot 1. B is a child of g with empty carried votes, support, and rows.
These empty lists are valid for a faulty proposer. Assign root 0 to g
and root 1 to B.

Every honest label-0 vote is for g at time 4 and reaches all nodes at 5.
All label-0 gates at 24 return g. There is no non-genesis fast source at
a₀=24, so the awake honest clients send no row.
There is no own-row processing or remote row-handler call at 25.
No chain state changes. No other FG action occurs before 72.

```text
┌──────┬──────────────────────────────────────────────────────────────┐
│ Time │ Event                                                        │
├──────┼──────────────────────────────────────────────────────────────┤
│ 19   │ u admits B.                                                  │
│ 20   │ HEADs: u votes B; v votes g.                                 │
│ 21   │ Both honest label-1 signatures reach every honest node.      │
│ 22   │ Every other honest node admits B, before relay deadline 23.  │
│ 23   │ u accepts the faulty label-1 vote for B.                     │
│ 26   │ All other honest nodes accept that vote, before deadline 27. │
│ 28   │ Freeze: everyone has those three signatures and B.           │
│ 36   │ No slot-2 block; both awake HEADs choose B.                  │
│ 37   │ Both label-2 votes for B reach every node.                   │
│ 40   │ Gate 1: u saves B; every other node saves g. Set T=40.       │
│ 52   │ No slot-3 block; both awake label-3 HEADs choose B.          │
│ 53   │ Both label-3 votes reach every node.                         │
│ 56   │ Gate 2: every node saves B. Set b₀=56=T+16.                  │
│ 72   │ Pending gate 3: every node saves B and can slow-write B.     │
│ 84   │ Set b₁=84; the requested outage has length 28.               │
└──────┴──────────────────────────────────────────────────────────────┘
```

All public ticks occur. Every unlisted honest base emission is delivered
one time unit later. After 56, retain this delivery schedule; an outage
permits it. The faulty base signer is silent after its one label-1 vote.
Continue the stated always-awake set through horizon 84. The faulty
proposer emits no further blocks, so no row can change a chain state.
Honest clients send no row at 72: p(3,B)=2<τ, and a slow
write alone does not enter fastWrite. There is no row-handler call at 73.

At gate 1, the late denominator is 3 everywhere. At u, B has two early
non-equivocating supporters, so 4>3 and the result is B. At the other
nodes B has only one early supporter, so 2≤3. Genesis has both honest
early supporters, so 4>3 and their result is g. At u even B's count 2
is below τ=3; its previous label-0 result is g, so it gets no B lease.
The other nodes get no B lease either.

At time 36 the frozen B score is 2, genesis participation is 3, and B
is eligible by 4>3; there is no competing block. Thus the asserted
label-2 heads are derived from the actual view. At gate 2 the two honest
supporters give result B and p(2,B)=2<3. Node v's slow test reads its
saved label-1 body g and fails B⪯g. Hence at the public boundary read
at 56, after every event with time ≤56, S_v=B, F_v=Z_v=g,
and v has **no live non-genesis lease**.
B is viable, but B is not below Z. This refutes the displayed statement.
At u the slow test succeeds, which does not give v a lease.

All later awake HEADs still choose B from the complete frozen honest batch.
At gate 3, v's previous result is now B, so its slow test succeeds and
writes deadline 72+28=100>84. At the public read at 72, every node has
processed gate 3 and has a live lease on B. No row is sent or processed
at 72, and no remote row-handler call occurs at 73.
Thus these actions change no F, S, or lease.
A cut before v's tick at 56 or 72 is not either public read. Thus the
negative still refutes lease-or-F coverage at b₀=56 under the inclusive read convention,
while it satisfies the corrected lease clause from d_j=72. P1 holds
throughout the example.
The hypotheses are exact: h=2>a=1, h+a=3≤5, the η inequality is
2·2>2+1, A_slow=16, and b₁−b₀=Π=28. All required healthy receipts
finish before their strict deadlines. Unlisted compulsory duties were
specified, not suppressed. F=J=g and H=1 throughout this execution.

SA check: `GridCO.slowEligible`, `admissionLevels`, `gate`, and
`releaseThreshold` give precisely the failed label-1 test and successful
label-2 test used at gates 2 and 3. This agrees with the pending-gate
branch of `SA.stable_resilient_from_engine`. DC check: the admitted
proposal view, current-slot eligibility, genesis chain state, and checked
receipt exclusion add no rejection or height change here. DC's
`stableAsynchronyResilient` has a different regime and no assertion about
SA leases at b₀; this trace does not refute that theorem.

### 10.2 bp.targetExtensionNegative.v1: target entries can be ancestors

Window check: 01 §8.4 unchanged latest-J client; n=1 replay closes the port.

**PROVED-paper (window checked).** The second Opus report replays this
execution after removal of the inert empty-row events. Here n=1 and the
first target uses HeightMatch. The window fold preserves the listed states
and the negative conclusion.

**Refuted auxiliary assertion.** Every honest FG target emitted during
a protected outage extends the protected block B.
**Correct replacement:** every such entry is compatible with B. Every
honest duty HEAD extends B. These are distinct assertions because an
entry is an ancestor of its source body.

Set n=1, a=0, Δ=4, k=2, L=28, η=28, R=3, δ_t=6.
The one validator is always awake and is every proposer. All base objects
are delivered to it one unit after emission; its own FG rows are recorded
and processed immediately, as required. Run all public ticks through
horizon 84. Assign root 0 to g and root i to Pᵢ. All parent chains,
carried votes, declared support and rows are the ones produced by the
frozen duties. There is no selective omission.

The label-0 vote at 4 reaches at 5 and gate 0 at 24 returns g. Its FG
action has no non-genesis fresh source and sends no row. Proposals
P₁,P₂,P₃,P₄,P₅ are made at 16,32,48,64,80 respectively, each extending
the previous proposal (P₁ extends g); they arrive at 17,33,49,65,81.
Their HEADs are emitted at 20,36,52,68,84; in-horizon deliveries are at
21,37,53,69. The final HEAD's delivery need not be inside horizon 84.
Gates 1,2,3 at 40,56,72 return P₁,P₂,P₃ respectively and fast-write
all their non-genesis prefixes, since τ=1. No earlier FG row was sent
or processed. Therefore P₁ through P₄ still have h=1, T_h=g,
h_j=h_F=0, and nj=false. P₅, proposed after the target row below,
can carry that row; its later state is not used at the action at 72.

Take B=P₁, T=40, b₀=56 and b₁=84. Both arming lags are 16 and
Π=28; h=1>a and h≥τ, and the η inequality is 2>1. The continued
healthy schedule is permitted inside the outage.

At a₁=d₃=72, the gate has just fast-written P₃ with deadline 100.
The full domain contains it, and it is the deepest member of fastWrite[3].
Thus C_fg=P₃. The full current-slot head is P₄, whose justified height
is zero, so the finality pair is empty. The height input is
(h_c,T_c,ν)=(1,g,false), with no prior target, lock, or timeout at
height 1. The client emits the honest target **(1,g,false)**.
Here g≺B, so B⋠g. All honest outputs and HEADs nevertheless retain B.

SA check: the threshold, early/late support, gate timing, max deadline,
and fresh fast-write test give the values just listed. DC check:
`Protocol.ChainState.initial` has h=1,T_h=g,nj=false;
`Protocol.height_pair` with the stated empty record and input returns
`.target 1 g`. This is a check of the shared client and chain definitions,
not a claim that DC uses the FG-SA fresh-source selector. The certified
DC outage theorem states persistence of the stable output; it does not
require every target entry to extend that output. Thus this negative is
compatible with both Lean interfaces and does not affect §8.4's origin proof.

## 11. Lean reuse, checks, and remaining gaps

window port: 01 window suppliers and 03 port review; no Lean transfer (pending)

The review-fix source check read AC at commit
`6e51216b70c8f30c606dc093b4b0eb0251bbbd7e`. The SA, GridCO, generic
statement directories, and generic Run.lean have no committed changes from
the outline's pin `3eb1889cd7e231d33e7edb96762b0ebd641825cb`.
DC was at `b241081d344555797205f8718eeb23a8a0e3eb4c`.
AC is `/Users/francesco/ethereum/lean/available-chain`.
DC is `/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus`.
No Lean file was edited or built for this document. A source declaration
proves its own typed statement; a plain protocol run is not a composed run.

```text
┌────────────────────────────────────────────┬─────────────────────────────────────────────┐
│ Source / declaration                       │ Use in this proof                           │
├────────────────────────────────────────────┼─────────────────────────────────────────────┤
│ AC Statements/Generic/Regimes              │ Exact OutageRegime/FastOutageRegime fields  │
│ AC Statements/Generic/Conditions           │ Checked HealthyPrefixDelivery; η window     │
│ SA Statements/Contract.saConstants         │ 6Δ, 4Δ, 4(k−1)Δ, min(η,L)                   │
│ SA Proofs/Contract.saContract_from_engine  │ Plain-SA bundle; comparison only            │
│ SA Proofs/Clean.included_from_engine       │ Plain-SA inclusion shape                    │
│ SA Proofs/FastOutage.fastP1_from_engine    │ Fast pending protection and P1 template     │
│ SA Proofs/Outage.pending_heads_cover       │ Pending HEAD before a new lease             │
│ SA Proofs/Outage                           │ Slow arming and finite-horizon cases        │
│ .stable_resilient_from_engine              │                                             │
│ SA Proofs/SlowWindow                       │ Every previous saved label must cover B     │
│ .slowEligible_of_input_covers              │                                             │
│ G Proofs/Transfer.TransferReceipts         │ Seat uniqueness and strict score counts     │
│ .majority/.conflicting_score_bound         │                                             │
│ G Proofs/ScoreExtension                    │ Raw cap evidence; score incidence algebra   │
│ .ScorePreservingViewExtension              │                                             │
│ G Proofs/ReceiptRelay                      │ Handler call gives vote or equivocation     │
│ .handled_head_stamped_or_equivocates       │                                             │
│ .accepted_head_receipt_before              │ Strict receipt window                       │
│ G Proofs/Outage.pending_gate_guard         │ Earlier origins cannot veto pending batch   │
│ .in_flight_label_at_gate                   │ Only label j+1 is in flight at d_j          │
│ .stable_resilient_from_engine              │ Grid retention template; no direct port     │
│ G Proofs/Protection                        │ Expiry, release, max-write, gate induction  │
│ .protection_from_armed_read                │ New FG frame/reconcile cases in §8          │
│ DC Internal/Definitions/NamedProposalPivot │ persist/reflect suffix interface in §4      │
│ .NamedProposalPivotSuffixTransfer          │                                             │
│ DC Statements/Generic/Claims.Consensus     │ stableAsynchronyResilient target shape      │
│ DC Proofs/Bridge/StandardVocabulary        │ Declares outage_stablePersists at :618      │
│ .outage_stablePersists                     │ Stable persistence through the horizon      │
│ DC Proofs/ReviewTheorem.concreteConsensus  │ Declared at :288; uses that theorem at :426 │
│ DC Model/Execution/Node                    │ NamedReceipt namespace; .excludes is        │
│ .NamedReceipt.excludes / .depsPresent      │ block-only; .depsPresent checks the parent  │
│ DC Statements/Generic/Conditions           │ DeliveryWellFormed.deps requires the        │
│ .DeliveryWellFormed.deps                   │ protocol dependency test at each delivery   │
│ DC Model/Protocol/ValidatorClient          │ Ancestor target is permitted, §10.2         │
└────────────────────────────────────────────┴─────────────────────────────────────────────┘
```

In the table, `SA` paths start at `AvailableChainSA`, `G` paths at
`AvailableChainGridCO`, and AC `Statements` at `AvailableChainStatements`.
DC paths start at their named `DecoupledConsensus…` directories. Namespace
prefixes are `AvailableChain.SA`, `AvailableChain.GridCO`, and
`DecoupledConsensusModel` (with `Proofs.HealingSurface` for the pivot).

`DecoupledConsensusModel.Execution.NamedReceipt` is a namespace in
`DecoupledConsensusModel/Execution/Node.lean:55`. Its `.depsPresent`
(:67) checks only the exact named parent of a block; it returns true for
votes and attestations. The run-level obligation is
`Statements.Generic.DeliveryWellFormed.deps` in
`DecoupledConsensusStatements/Generic/Conditions.lean:54`. It requires the
protocol's dependency test before each delivery. It does not add checks
for all objects referenced by a block to NamedReceipt.depsPresent.

DC's generic `Consensus.stableAsynchronyResilient` concludes `PersistsFrom`
under `DecoupledConsensusStatements/Generic/Regimes.lean:139` OutageRegime.
Its fields require:

- valid execution, PartialSynchrony, and `gst : t_GST≤b₁`;
- `committees : HonestCommittees`, healthy prefix delivery to b₀,
  `0≤b₀≤b₁≤horizon`, and a public boundary b₀;
- FreshMajority at every t with
  `participationLag≤t≤horizon+participationLag`, and SlashableBound;
- `outageStart T≤b₀`, `b₁+Δ≤expiry T`, and `b₁+Δ≤horizon`.

DC's PersistsFrom reads every t with b₀≤t≤horizon, including the period
after b₁ (`DecoupledConsensusStatements/Generic/Properties.lean:124`).
The bridge theorem `outage_stablePersists` is declared in
`DecoupledConsensusProofs/Bridge/StandardVocabulary.lean:618`.
`ReviewTheorem.concreteConsensus` uses it at :426; it does not declare it.
SA's PersistsThrough instead uses b₀≤t<b₁ and the premises in §1.1.
We do not import DC's extra premises, its post-outage conclusion, or its
SG/NJ rules into FG-SA.

The stage-1 deferred obligations are discharged on paper as follows:
proposal score producer in §§2.1,3; proposal path/edge producer and exact
adoption in §§2.1,4; pending-label inclusion in §5; arbitrary-read origin,
pending batch, slow history, and P1 arming in §§6–8. No paper proof gap
remains for the seven stage-2a claims with the explicit corrected boundary.

The remaining limits and all findings of this stage are:

1. **Negative:** the slow regime does not imply a covering lease or F
   coverage at b₀. Section 10.1 proves this with an exact valid execution.
   The corrected pending-gate clause is sufficient for global P1.
2. **Negative:** honest target entries need not extend B. Section 10.2
   proves this with an exact valid execution. Compatibility and earlier
   honest source origins exclude conflicting finality, even for a>f.
3. **Formalization gap:** no composed FG-SA run, checked receipt producer,
   or composed Lean theorem is certified here. All PROVED statuses mean
   complete paper proofs against the frozen spec and the stage-1 lemmas.
   In particular the common-prefix comparison, contest witness, and
   joint F/reconcile induction still need Lean code.
4. **Scope:** persistence after b₁, arbitrary-damage recovery, healing, and
   first or recurring finality are not conclusions of these proofs. This
   stage does not adjudicate the other blueprint files or broaden a P1
   premise to a healthy interval after arbitrary damage.
5. No counterexample to Clean 6Δ service or either global P1 statement was
   found. No unconditional preservation of local leases, arbitrary saved
   slow windows, or equal literal vote sets was used. The earlier N1–N3
   executions are not reasserted as new findings or used as proof steps.
