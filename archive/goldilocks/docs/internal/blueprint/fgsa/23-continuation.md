# FG-SA blueprint: sleepy safety and inclusion after recovery

_Date: 2026-10-01. Writer brief: FROZEN r1._

Current spec SHA-256: `a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.

Rule authority: the [current window specification][spec], with the
frozen [window rules](../codex/reports/fdelay-window.md) §§1–2 and
[recovery delta](../codex/reports/rec-df-integrate.md) §6. The recovery
review closures are stated in §16. R7's optional omission keeps every
effect (01 §1.1), so the carriage arguments below are unchanged.
Earlier proof source:
[wc-paper-proof, W1–W5][paper]. Independent reviews:
[Astra, CONFIRMED WITH GAPS][astra] and
[Opus, CONFIRMED WITH GAPS][opus]. Neither review found a breaking run.
This chapter closes their listed gaps at paper level. It adds the claim
bp.weakContinuationAvailable.v2 and, in §17, its growth
field bp.weakContinuationGrowth.v2. It uses the revised timing clauses below
for the window protocol. It does not assert that the old single-delay
premise records apply unchanged. PROVED-paper means a paper proof from the cited
foundations, including H.22. It does not mean a checked Lean theorem.

Sections 18–19 add the outage and corruption-growth companions. Their
Lean branch status is stated separately from the historical paper status.
Section 20 records the P3 proof-interface errata. Section 17 already
contains the WC-LIVE growth statement requested by the earlier erratum.

Blueprint citations give the claim label and the inspected line numbers.
The current spec controls the window rules. Older archive citations
identify the unchanged gate, frame, client, and tick rules by name.
The names wc.* refer to the W5 plan in the source report.

## 1. Scope and exact statement

### 1.1 Existing premises and the selected cut

Fix the parameters, application codec, identities, and seat maps of the
existing [WeakContinuation statements, lines 23–73][wc-premises].
Write a for the static faulty count and h_t for the awake honest count.
Use C1, integer Δ_F≥Δ>0, k≥2, K≥2, R≥max(2,κ), and δ_t=2R,
where κ=ceil((6Δ+Δ_F)/(4Δ)). K is the spec's K_W. Put

~~~text
t_s = 4sΔ;  v_s = t_s+Δ;  e_s = t_s+2Δ;
z_s = t_s+3Δ;  q_s = t_s+5Δ;  d_s = t_s+6Δ;
P_act = 4RΔ;  a_r = d_(rR).

T_F = GST+B_H^F.
~~~

P_act denotes the action period called P in 21. We reserve P for a
proposal block in the inclusion proof.

Assume the existing outer premise δ_t=2R. It is outside Recovery₂ in the
statement file. It is required by H.22/H-time and is kept outside the
records here. See [Claims/WeakContinuation, WeakContinuationClaim, lines 13–15][wc-claim],
[Regimes, lines 64–75][wc-regimes], and
[21 H.22, bp.healingInput.v2, H-time, lines 3441–3462][h-time].
This closes Astra G1.

Use StrongRecoverySearchPrefix₂ with C1 and the revised finite
Recovery₂ timing clauses of 21 §2. Its horizon is T_F. These premises
include Base₂,
partial synchrony, a≤f=⌊(n−1)/3⌋, all honest nodes awake on [GST,T_F],
and the strict honest-proposal gap with finite G≥4Δ and its finite-horizon guard.
The source supplies every guarded gap and receipt interval used by H-time.
In detail, the gap is used for triggers t with GST≤t and t+G≤T_F.
There is no extra opening recurrence. Base₂ includes valid execution,
Linked and CStar seats, no restart, E.Δ=p.Δ, and
idealization : NamedRootCollisionFree.
See [Regimes, lines 18–75][wc-base] and
[RecoveryCore, lines 76–80][recovery-core].

A signed HEAD identifier is (seat, slot, root identifier).
Repeated copies count as one vote. Equivocation requires two different
root identifiers for the same seat and slot. Resolve identifiers in the
cumulative store domain, then apply the active-view filter.

Use CleanContinuation₂ with the same revised timing clauses:

1. Base₂ holds for its environment E' and run ρ.
2. AgreesThrough₂ preserves honest identities, GST, the full seat map,
   parameters, inputs, and awake values through T_F, and the exact source
   event list.
   Every added event has time strictly greater than T_F.
3. T_F≤ρ.horizon. C1 continues, with the original deadlines of pending
   receipt obligations triggered before T_F and delivery to sleeping honest nodes.
4. At each t with T_F<t≤ρ.horizon, a<h_t.

Therefore a≤f still holds, and a<h_t holds from GST through the
continuation horizon. Only the source needs full participation and the
gap. Participation can decrease strictly after T_F, not immediately after
an earlier healing gate d_u<T_F. This is Astra S1.

Sleep suppresses proposal, vote, and FG duties. It does not stop ticks,
gates, receipts, or state processing. A sleeper's HEAD means the same
deterministic duty read, without an emitted vote. The proof permits no
crash, restart, change of honest identities, or loss of stored state.
See [de183d7d, Tick order, lines 857–868][spec-tick].

Use B_H^F and the eligible repair allowances from 21 H.22/H-time:
ρΓ always, and ρ₁ when k≤2R+1. For Δ_F≤2Δ, B_H^F=B_H, with the
old values 295Δ (R=2) and 343Δ (R=3) at k=2,G=8Δ. For κ>2 use
the F form; at R=3, 2Δ<Δ_F≤6Δ, those parameters give 351Δ.

The definition below is copied from 21 H-time; P=P_act and β_F=4κΔ.
Set L=(4k−1)Δ, Γ=4Δ ⌈G/(4Δ)⌉, and ε=β_F−8Δ.

```text
B_H,F^(2) = max(12L+12Γ+12P+49Δ+2ε, 8L+10Γ+14P+19Δ).
B_H,F^(1) = max(6L+12Γ+12P+61Δ+2ε, 4L+10Γ+14P+27Δ)  (requires k≤2R+1).
B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
```

Choose the H.22 witnesses on the source once. They include

~~~text
ht(C*)=M+1;  C*⪯Q*;  s*=r*R;  u≥s*+2;
Q* is the actual honest proposal at slot u;
v_(u+1)≥GST (from H0 v_(s*)≥GST and u≥s*+2);
GST≤t₀=d_u<T_F;  i*=afterTicksIdx(source,d_u).
~~~

See [21 H.22, bp.healingInput.v2, H0, lines 3324–3333](21-healing.md:3324).
The grid gives v_(u+1)≥v_(s*)≥GST. At `e1d4232`, Lean carries this as
[WCSeed.firstVoteAfterGST, lines 122–126](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Statements/WeakContinuation.lean:122),
derived in [wc_heightSeed, lines 499–509](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:499).

C1 gives blocks, complete bodies, SA votes, and their relays delay Δ.
Standalone FG rows and their relays use Δ_F. Sends at t arrive strictly
before max(t,GST) plus the family bound; relays use acceptance time.
Dependencies are present. Only blocks have the receiver exclusion.
Pre-GST objects and sleeping receivers retain these duties. A carried
row arrives with its complete block under Δ.

The cut follows all honest gate/action ticks at d_u. It excludes the
following deliveries at that time. S_x(i) and F_x(i) denote states after
the first i events, with complete local handlers. Public S_x(t) is the
inclusive read through time t. The temporary F assignment before its
immediate reconcile is not an output read.
See [21 H.22, event cuts, lines 3262–3272][h-cut] and
[WeakContinuation, BoundedHealingCut₂, lines 83–89][wc-cut].

### 1.2 New claim — bp.weakContinuationAvailable.v2

**Statement.** In the fixed parameter context, the following proposition
holds. The premise names below use the revised C1 and T_F timing
clauses of §1.1. They are paper instances, not unchanged Lean records.
Suppressed parameters are p and the codec, as in WeakContinuation.

~~~text
δ_t = 2R →
  ∀ E source,
    StrongRecoverySearchPrefix₂ E source G →
    ∃ u Q* i*,
      BoundedHealingCut₂ E source u Q* i* ∧
      ∀ E' ρ,
        CleanContinuation₂ E source E' ρ →
          SSafeFromCut₂ E' ρ i* Q* ∧
          IncludedFromCut₆Δ E' ρ d_u.
~~~

SSafeFromCut₂ has exactly the existing fields
([WeakContinuation, lines 105–120][wc-safe]). For all honest x,y and
valid suffix event indices i,j:

~~~text
i*,i,j within ρ.events.length;  i*≤i;  i*≤j:
  S_x(i) ∥ S_y(j).                       (compatibility)
i*≤i≤j≤ρ.events.length:
  S_x(i) ⪯ S_x(j).                       (local monotonicity)
i*≤i≤ρ.events.length:
  Q* ⪯ S_x(i),  F_x(i) ⪯ S_y(i).         (seed; finalBelow)
~~~

It also has the stated compatibility and monotonicity projections for
both public accessors, stable and confirmed, at timeIdx≥i*. Both
accessors equal S by [01, comp.outputNesting.v3, lines 774–793][nesting].

Here is the exact new inclusion field, including persistence:

~~~text
IncludedFromCut₆Δ E' ρ t₀ :=
  ∀ s P,
    HonestProposal E' ρ (fgsaInterface p c) s P →
    t₀ ≤ t_s → d_s ≤ ρ.horizon →
    ∀ y ∈ ρ.honest, ∀ g ∈ {stable,confirmed}, ∀ t : Time,
      d_s ≤ t → t ≤ ρ.horizon → P ⪯ outputAt(g,y,t),
  where d_s=t_s+6Δ and S_y(t) is the inclusive public read.
~~~

Here outputAt(g,y,t) is the public accessor g at timeIdx(t).
By [comp.outputNesting.v3][nesting], outputAt(g,y,t)=S_y(t)
for both accessors, so §13 proves this field through S.

At t₀=d_u, the slot grid gives s≥u+2. Slot u+1 has
t_(u+1)=d_u−2Δ and is outside this inclusion field. Its pending HEAD
batch is still required for safety. The field concerns each actual
honest proposal; it does not assume future proposer recurrence.

Lean `WeakContinuationLiveAt₂` guards every field by gateTime u≤ρ.horizon
and states inclusion with u+2≤s. The guard follows from d_u<T_F≤ρ.horizon.
On the slot grid, d_u≤t_s is equivalent to u+2≤s; see §17.2 step 4.
Thus these Lean and paper forms are equivalent under the selected witnesses.

**Proof.** Sections 3–14 below choose the witnesses, transfer the finite
seed, and prove both conclusions for every continuation.

**Dependencies.** WeakContinuation premises with §1.1's timing clauses; H.22/H-time with
δ_t=2R; the lemmas below.

**Status.** PROVED-paper. Astra G1, S1, S2 and V5; Opus F5 and V5 are
addressed explicitly. BoundedSafetyRecovery₂ is a corollary: project the
safety conjunct with the same u,Q*,i*. Inclusion is a new protocol
theorem, not a consequence of the old safety proposition alone.

### 1.3 DC counterpart and deliberate differences

The counterpart is [DC Generic Claims, Consensus.available,
line 67][dc-claims], under [SleepyRegime, lines 92–103][dc-regimes],
using RecoveredBy.recovered at lines 74–79. AvailableAt at
Claims lines 27–36 gives safe confirmed and stable outputs and inclusion
for both. The following differences are part of this statement.

~~~text
┌────────────────────┬─────────────────────────────┬────────────────────────────────┐
│ Item               │ FG-SA statement             │ Reason for the difference      │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Start              │ Selected completed d_u<T_F  │ H.22 gives an actual common    │
│                    │ with seed Q*                │ stored output at that gate.    │
│ DC start           │ recoveryEnd of recovered    │ DC has its own bounded         │
│                    │                             │ preparation and read times.    │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Fixed-start        │ Corollary: t₀=T_F; reads at │ d_u<T_F; both fields hold from │
│ corollary          │ timeIdx≥timeIdx(T_F);       │ a later start. This gives      │
│                    │ proposals with t_s≥T_F.     │ the fixed-start DC shape.      │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Agreement          │ Inclusive exact prefix T_F; │ Replay reads seats, inputs,    │
│                    │ fixed honest set and seats  │ and awake values. Static       │
│                    │                             │ identities retain a≤f.         │
│ DC Generic         │ Per retained honest node,   │ Generic AgreesUntil allows     │
│                    │ time<cut, honest subset     │ an honest-set subset.          │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Continuation range │ Covers T_F; weak after T_F  │ The cut lies before T_F. No    │
│                    │                             │ later search is necessary.     │
│ DC Generic         │ Covers recoveryEnd          │ RecoveredBy names that end.    │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Participation      │ Point condition a<h_t       │ HEAD pools use slot labels,    │
│                    │                             │ not an SG window.              │
│ DC SleepyRegime    │ WindowMajority, with lag    │ SG votes have window life.     │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Committees         │ Fixed CStar seat map in     │ These replace DC               │
│                    │ Base₂ and                   │ SleepyRegime.committees        │
│                    │ AgreesThrough₂.seats.       │ (HonestCommittees).            │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Fault evidence     │ Inherited a≤f and honest    │ Fixed identities, Linked,      │
│                    │ client safety               │ and authentication suffice.    │
│ DC recovered       │ Explicit SlashableBound     │ Its constructor exposes it.    │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Source search      │ Gap G; δ_t=2R; bound B_H^F  │ These are the proved H-time    │
│                    │                             │ premises and constants.        │
│ DC recovery        │ MultiProposerRecurrence;    │ Different search protocol      │
│                    │ prefixEnd and recoveryEnd   │ and timing constants.          │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Outputs and delay  │ stable=confirmed=S; 6Δ      │ One stored available output    │
│                    │ for both, with persistence  │ is advanced at the gate.       │
│ DC AvailableAt     │ Separate output fields and  │ DC retains separate records    │
│                    │ protocol-specific delays    │ and their preparation.         │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Additional fields  │ Seed retention; F_x⪯S_y     │ Exact SSafeFromCut₂ contract   │
│                    │ at one event prefix         │ needs more than SafeFrom.      │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Conclusion scope   │ S-safety; inclusion/growth  │ Other FGSAClaims fields give   │
│                    │                             │ finality safety and vote reads │
│ DC bounded safety  │ PhaseShiftSafety:           │ BoundedSafetyRecovery gives    │
│                    │ finality =                  │ these fields together.         │
│                    │ WholeRunFinalitySafety;     │                                │
│                    │ seedAtVote, liveAtVote,     │                                │
│                    │ honestProposalLive,         │                                │
│                    │ honestProposalReads,        │                                │
│                    │ genuine                     │                                │
├────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ Scope              │ Recovered branch, no        │ Genesis is covered by 02/03.   │
│                    │ restart or later outage     │ This proof keeps synchrony.    │
└────────────────────┴─────────────────────────────┴────────────────────────────────┘
~~~

For conclusion scope, see [DC Statements.BoundedSafetyRecovery, lines 56–61](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusInternal/Legacy/Definitions/NamedVoteConsumers.lean:56)
and [PhaseShiftSafety, lines 97–124](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusInternal/Legacy/Definitions/SafetyRegimes.lean:97).

The DC premise locations are Generic Regimes lines 28–43, 59–79,
and 89–103. One further quantifier difference matters. DC's
[Generic Properties, IncludedFrom, lines 112–120][dc-inclusion] uses
t₀<t_s and an honest designated proposer, then concludes that an
actual proposed block exists and is included at the deadline. The
FG-SA field starts from an actual HonestProposal and uses t₀≤t_s,
as required by Opus F5. It makes no proposal-existence claim at a
silent slot. Equality t_s=d_u cannot occur on this slot grid, so the
weak boundary inequality adds no slot at the selected start. Persistence
is explicit here; in DC it follows from inclusion and SafeFrom.

This is a correspondence of claims, not an application of a DC run
theorem to an FG-SA run. Neither availability field imposes a later
proposer-recurrence premise. This chapter also proves no sleepy finality
liveness and no new post-recovery P1 outage theorem.

## 2. Internal seed, controls, and proof order

Let HS be the following finite assertion about the selected source cut.
It is internal proof data, not a new field of CleanContinuation₂.

1. Each honest label-u raw result is Q*, its guard passed, and S=Q*
   at i*. The raw result is its actual event value.
2. Each honest label-(u+1) HEAD at q_u=d_u−Δ extends Q*. Store paths,
   receipt stamps, and pending relay obligations keep their actual origins.
3. Every honest nonempty height row emitted through i* at height ≥M+1
   has its actual selected source body K⪯Q*. This includes rows that
   later occur in a private certificate, regardless of disclosure time.
4. Each honest reader stores C*, has H≥M+1 and F⪯Q*, and each live
   lock target precedes Q*.
5. The store, certificate, client, and source-origin invariants hold,
   with their original event indices and scheduled source labels. Use
   21 W1–W3 for window certificate origins and separate bit effects.

HS concerns original signed-row and source occurrences, including rows
later used through stale carriage. It requires neither receipt of all
old rows by the cut nor empty window entries.

High means height ≥M+1. A low finalized or justified entry has height
≤M. HS does not order all old raw results, old saved bodies, low source
bodies, or cached low J. In particular, low J need not precede C*.
Only a low J that is the uncontested active root must do so.

At a reader's input, call an honest source **usable by a controlling
certificate** if its signed height row occurs in a target certificate
for a justification in the reader's stored chain states or live J, in
the target justification of a finalized entry in those states or live F,
or in a height crossing on the ancestry of any block in cumulative T.
Include each such honest row occurrence and its original emission.
The last class includes an off-J crossing used by a contest witness,
even if that block is inactive or outside the frozen duty view.
For finality, the target row's source is distinct from the potentially
different, higher source used when a signer later attaches finality.

The frame lemma uses all high sources in this set. A later disclosure
adds a use of an earlier signature; it never changes the signature's
origin. This definition closes Opus F2.

The seeded history consists of Q* and honest raw results at labels
s>u. A pre-cut row or saved object keeps its real origin. A result
value is not defined by a later mutable saved confirmation lookup.
The source and frame lemmas below are conditional steps. The event
induction proves their premises before it applies them.

## 3. Prefix replay — bp.wcPrefixReplay.v2

**Statement (wc.prefixReplay).** Source states, actual event values,
emissions, receipt stamps, duty reads, and i* are the same in every
agreed continuation through T_F.

**Proof.** Induct on the length of the agreed event prefix. Initial
states use the same protocol and parameters. At each event the node,
time, object, and event constructor agree. For a delivery, the input
state agrees, so the deterministic checked window handler and its
substeps agree. For a tick, seats, input, clock parameters, and awake values agree
at that time; the ordered tick and any duty therefore agree. Honest
membership also agrees, including for authentication and scheduling.
Thus the next state and each intermediate duty input agree.

This proves equality of historical event values, not just final stores.
Every added event has time>T_F>d_u. It cannot change the count or position
of events used by afterTicksIdx at d_u. Hence i* agrees. The same
argument transfers each finite HS assertion and each already emitted
row's origin. PartialSynchrony in the continuation supplies any later
receipt deadline; replay alone is not a new delivery premise.

**Dependencies.** [AgreesThrough₂, lines 41–50][wc-premises];
deterministic frozen handlers and [Tick order, lines 857–868][spec-tick].

**Status.** PROVED-paper; Astra V1/S2 and Opus V1. No Lean replay lemma
or bridge is asserted here.

## 4. The height seed — bp.wcHeightSeed.v2

**Statement (wc.heightSeed).** The witnesses selected by H.22/H-time
under the source premises and δ_t=2R satisfy HS.

**Proof.** Apply H-time to the finite source search. It chooses the
reset C* and first honest proposal Q* at u≥s*+2, with d_u<T_F.
Use only conclusions whose events or reads lie through i*:

1. [21 H.17, fj.Xplus.v1, lines 3037–3140][h17]
   gives exact label-u HEADs, exact raw results, successful guards,
   and S=Q*. These are H3 and the cut clause of H4
   ([21 H.22, H3–H4, lines 3395–3406][h3]).
2. Apply [21 H.16, Corollary U′, lines 3015–3036][h16] to these raw
   results. Its first transfer, H5, gives every label-(u+1) HEAD
   above Q* at q_u. That time is before d_u, so this is finite seed
   evidence, even though the proof uses the later gate's late pool.
3. Take a high honest height row emitted through i*. Its source label
   r satisfies r≥s* by [21 H.14, fj.theoremN.v1,
   lines 2903–2972][h14]. Its actual action time gives r≤u.
   If r<u, H2.A puts its source K below every honest label-u HEAD;
   H.17 makes those HEADs Q*. Equivalently, apply H.16 to its raw
   source result and then take the prefix K. See
   [21 H.22, H2.A, lines 3382–3388][h2a].
   If r=u, source discipline takes K from fastWrite[u]. Every member
   is a prefix of the exact raw result Q*. Thus K⪯Q* in both cases.
   The argument quantifies over emissions, so private use is covered.
4. [21 H.12, source timing and initial reset transfer, lines 2721–2752][h12] puts C* in every honest store at
   q_(s*). The cumulative tree retains it. It gives H≥M+1 thereafter.
   Local F⪯S and S=Q* give F⪯Q*. The live-target bound
   target⪯S gives every live target⪯Q*. These are
   [22 I5, store, nesting, and lock bounds, lines 633–677][i5]. Parent closure also supplies C* from
   a stored Q*, since C*⪯Q*.
5. The window invariants are 21 W1–W3 and [21 IF.1–IF.3][if123],
   [22 I5][i5], and [01 bp.sourceDiscipline.v2,
   lines 919–953][source-discipline].
   These invariants use honestly stored carriers and honestly held source paths.

All cited transfers here end by the selected cut. We do not apply an
all-awake HEALED conclusion to the unknown sleepy suffix. Section 3
transfers these finite facts to each continuation.

**Dependencies.** H.22/H-time with δ_t=2R; H.12, H.14, H.16, H.17;
H2.A, H3, H4, H5 at the stated finite reads; 21 W1–W3, I5,
and source discipline.

**Status.** PROVED-paper; Astra G1/S2 and Opus F1/F4, V1. The cut is
the selected H.22 cut. An arbitrary BoundedHealingCut₂ with only a
refresh equality is not asserted to imply HS.

## 5. Low finalizations — bp.wcLowFinalized.v2

Every window finalization selects an actual finality quorum for an
earlier justified entry, even when it is not latest J. 21 W1 supplies
the crossing and target-QC witnesses. For causal order, 21 W3 uses the
justification read by an honest finality signer. Its honest target
source was emitted at least one action period earlier. Stale carriage
and retention change neither occurrence. Thus low finalized entries
precede C*. A high target source reaches every output in 4Δ by §8,
before its finality action since P_act>4Δ. No retention premise is
needed for this safety argument.

**Statement (wc.lowFinalized).** Any finalized entry E at height x≤M
whose carrier is in the RD2 run scope satisfies E⪯C*⪯Q*.
The scope contains directly delivered full proposals, honestly held full
proposals at any event prefix, and their ancestors. A private carrier must
meet this condition; a later-disclosed carrier qualifies through delivery.

**Proof.** E's carrier is in scope by the statement; C* is honestly held
by HS. Scope is ancestor-closed, so both full chains are covered and equal
roots identify equal full entries before the quorum comparison.
If x=0, E is genesis. Otherwise C* has crossed x because
ht(C*)=M+1>x. Let A be the entry on its chain at that crossing.
The crossing has q_F height pairs for (x,A); the finalization has
q_F finality pairs for (x,E). Since a≤f and identities are fixed,
2q_F−n>a. The quorums share an honest identity. If A≠E, that identity
has a timeout or a different target at x and a finality pair for E.
This is E1, forbidden by honest client safety. Thus A=E and E⪯C*.
The proof uses signed occurrences, not receipt order. Delayed disclosure
supplies scope through delivery and does not change signed origins.

**Dependencies.** [21 IF.2 and IF.3(c), lines 435–507][if123];
HS and the inherited a≤f.

**Status.** PROVED-paper; Astra V1/V2.2 and Opus V1. No corresponding
claim is made for an arbitrary low justification.

## 6. Source origins — bp.wcSourceOrigin.v2

**Statement (wc.sourceOrigin).** An honest row emitted after opening
gate d_r has a selected source K in that gate's fresh fastWrite[r],
with K⪯C_(x,r). A carried old row keeps its original source and
emission time. The source-label bounds of 01 §8.4 remain valid.

**Proof.** The gate sets fastWrite[r] to empty before it adds successful
fast prefixes of its current nonempty result. The action reads exactly
this scheduled set. If it has no eligible member with a live lock,
there is no row. The selector cannot use S, a slow lock, or an older
fastWrite set. Thus each newly selected K precedes this gate's result.
The height pair, if nonempty, names ht(K) and K's entry. A lock can
suppress it; it cannot replace its source.

The final no-round client applies its sent-set check and the h>h_f
test before recording and signing. These tests can remove a send or
its finality pair. They cannot create an earlier emission or replace
the current source. An old retained row still has its original signed
content and origin. R6-window admits a current HeightMatch or an
older height pair useful for a retained finality entry. Only HeightMatch
sets height bits. Exact-row exclusion and window bits create no new
attestation. Rows have no clock expiry; finality bits can be removed by
finalization/pruning or capacity eviction, as 21 W2 states.
R7's optional omission keeps every effect; the signed-origin argument is unchanged.

At q_s, d_r≤q_s implies r≤s−1. At t_s or v_s it implies
r≤s−2. A local gate input at d_s cannot contain a row created by
that gate's subsequent action, or a delivery at the same time.
After a gate, an own-row call follows the action read. A later delivery
at that time is handled after the recipient's tick.

**Dependencies.** [01 bp.sourceDiscipline.v2, lines 919–953][source-discipline];
[de183d7d, FG action, lines 839–855][spec-source];
[gate, lines 928–955][spec-gate];
[client, lines 1549–1566][spec-client].

**Status.** PROVED-paper; Astra V1/V2.4–5 and Opus V1. This is a rule
lemma. Its claim that a new source is on the seeded chain is supplied
by the induction when the source gate occurs.

## 7. Seeded frame — bp.wcSeededFrame.v2

**Statement (wc.seededFrame).** At a reachable honest duty input, assume
HS's C*,M,Q*, that the reader stores C*, and that Q*⪯B. Assume each
high honest source usable by a controlling certificate at this input
precedes B, with “usable” as defined in §2. Then

~~~text
F ⪯ Z ⪯ B;  lo≤ht(B).
~~~

If every live lock target at this input also precedes B, the live
walk start A satisfies Z⪯A⪯B. If B belongs to the duty's block view,
each path vertex from A through B belongs to its filtered domain.

Low F has a carrier in the honest reader's store; HS supplies the held C*.
**Proof.** The stored C* gives H≥M+1. A low F precedes C* by §5.
A high F has a prior justification with an honest high target source K;
its finalized entry precedes K⪯B. Thus F⪯B. The same target-source
argument gives J⪯B when J is high.

If a low J is the active root, the frame requires H=j+1 with no
contest. Since j≤M and H≥M+1, j=M and H=M+1. C* is a stored
height-H block. If J did not precede C*, C* would witness a contest.
Thus this active J precedes C*⪯B. When the test is contested, or
H≠j+1, Z=F. In all cases F⪯Z⪯B. A conflicting cached low J is
permitted in the latter cases.

Q*⪯B and C*⪯Q* give ht(B)≥M+1 by IF.1 height monotonicity.
If H=M+1, the floor is H or H−1, so lo≤M+1≤ht(B).
Now suppose H≥M+2. If there were a contest, j=H−1≥M+1.
Choose an honest target row for J and an honest crossing row at H−1
on a height-H witness W that does not extend J. Let their sources be
K_J and K_W. Both have height H−1 and precede B by the premise.
They are therefore comparable. Both source paths are honestly held;
the controlling J and W carriers are in honest cumulative stores.
Along a comparable chain segment of
constant height, the entry is unchanged. Their source entries are equal.
The source paths and controlling carriers give scope for the compared entries.
Base₂.idealization identifies equal roots with equal full blocks, as in §5.
The crossing entry on W is consequently J, which implies J⪯W.
This contradicts the contest witness.

Thus in this case lo=H−1. Choose a stored maximal-height block.
Its crossing of H−1 has an honest source K with
ht(K)=H−1 and K⪯B. Height monotonicity gives lo≤ht(B).
This crossing may be in an inactive or recently admitted block; §2's
definition includes it.

The live start is Z or a live target in the full filtered tree.
The added lock premise puts it below B and above Z. When B is in
the duty view, B itself witnesses height at least lo for every vertex
on this suffix. All such vertices extend F and Z and are in the
parent-closed view. The witness is in that same view. No late maximal
carrier is inserted into the frozen HEAD view by this proof.

**Dependencies.** §§5–6; [21 IF.1/IF.3][if123];
[02 bp.cleanFrame.v1, equal-height source entries, §3.1, lines 171–192][plateau];
[de183d7d, Frame and Walk start, lines 789–837][spec-frame].

**Status.** PROVED-paper; Astra V1 and Opus F1/F2. Storage of C* is
an explicit internal lemma premise, supplied by §4 and cumulative T.

## 8. Joint suffix induction — bp.wcSeededInduction.v2

### 8.1 Statement and exact substitutions

**Statement (wc.seededInduction).** At each completed suffix event prefix:

I1. All honest raw results at completed labels s>u are nonempty and
extend Q*. Results at increasing labels extend all earlier results;
results at the same label are compatible.

I2. Each such result C_(x,s) precedes every honest deterministic
label-(s+1) HEAD at q_s. These are retrospective facts about actual reads.

I3. Pre-cut high emitted sources precede Q*. Each post-cut selected
source precedes its own completed suffix result. Each disclosed high
justification or finalization has an earlier honest target source on
this chain. Each low finalization precedes Q*. Low J is unrestricted
except when §7 selects it as the active root.

I4. Live targets, suffix saved confirmations, and suffix fastWrite members are
prefixes of the seed/result chain with actual origins. Old targets that
remain live precede Q*. An S value has origin Q*, a suffix gate result,
or a compatible finalized entry. Q*⪯S, and each S transition extends
its previous value. Old saved confirmations remain outside this history.

I5. Store invariants, local nesting, client safety, and the actual
origin/deadline facts hold. Every honest reader still stores C*.

For completed next gates, I1–I4 also imply that each result and each
source at label s is in all honest outputs by d_(s+1)=d_s+4Δ.

The following table specifies every changed Clean premise used here
or in inclusion. It replaces a full-history Clean invocation.

~~~text
┌──────────────────────────┬───────────────────────────────────────────────────┐
│ Reused step and lines    │ Substitution in this chapter                      │
├──────────────────────────┼───────────────────────────────────────────────────┤
│ 02 §2.1, 74–106          │ Same h_s>a and honest-origin counts. Establish    │
│                          │ active heads by I3 and low finalized crossing.    │
│ 02 bp.sameLabel.v1,      │ Same receipt, seat-union, and disjoint-support    │
│ §2.2, 108–146            │ proof for actual suffix raw gates.                │
│ 02 bp.release.v1,        │ Deletions preserve I4. Compatible honest heads    │
│ §2.3, 148–167            │ give opposing count≤a<τ when needed.              │
├──────────────────────────┼───────────────────────────────────────────────────┤
│ 02 §3.1, 171–192         │ Equal-height geometry only for high sources       │
│                          │ below B. No condition on all low sources.         │
│ 02 §3.2–3.4, 194–258     │ Low F⪯C*; high F/J from earlier sources; active   │
│                          │ low J⪯C* or contested Z=F. Use §7, not global     │
│                          │ no-contest or retention of all old bodies.        │
│ 02 §3.5 items 1–3,       │ Bound high usable sources by B. Reader stores C*. │
│ 268–275                  │ §7 gives Z⪯B and lo≤ht(B), including low contest. │
│ 02 §3.5 items 4–6,       │ Old live targets⪯Q*; new ones from earlier        │
│ 276–287                  │ suffix gates. Relay B; use B in the duty view.    │
├──────────────────────────┼───────────────────────────────────────────────────┤
│ 02 bp.suffixWalk.v1,     │ Same finite suffix proof from A; dominance also   │
│ §4.1, 296–329            │ defeats any rival enabled by a low-parent arm.    │
│ 02 bp.cleanTransfer.v1,  │ Same cap-aware receipts. Receiving F⪯B follows    │
│ §4.2, 331–397            │ from §7; new proof is §8.4 below.                 │
│ 02 §4.3, 399–428         │ Same per-candidate score algebra; §12 supplies    │
│                          │ incidence on X⪰D and separate band agreement.     │
├──────────────────────────┼───────────────────────────────────────────────────┤
│ 02 §5.1–5.2, 456–515     │ Initialize at HS, not genesis. Keep only Q* and   │
│                          │ suffix results in I1; retain old event origins.   │
│ 02 §5.3 items 3–6,       │ High certificates have I3 origins; low F⪯Q*.      │
│ 526–539                  │ Low J can conflict. Reconcile can empty old       │
│                          │ incompatible data, but no suffix result or S.     │
│ 02 §5.4, 545–602         │ First batch uses HS at u+1. Later batches use     │
│                          │ earlier I2; bound F by low/high split.            │
│ 02 §5.5, 604–631         │ Old targets⪯Q*. Old saved bodies can affect slow  │
│                          │ tests only. An old low F cannot normalize S.      │
│ 02 §5.6–5.7, 633–672     │ Fresh scheduled sources; final no-round client;   │
│                          │ own rows after the action read. Finite horizon.   │
│ 02 bp.cleanSafety.v1,    │ S origins: Q*, suffix result, or high F below a   │
│ §6, 674–708              │ seed/suffix source. Low F stays below Q*.         │
├──────────────────────────┼───────────────────────────────────────────────────┤
│ 03 §2.1, 229–275         │ D=max({Q*}∪suffix results through s−2). §7 gives  │
│                          │ F⪯Z⪯D and lo≤ht(D); no no-contest premise.        │
│ 03 bp.scoreSuffix.v2,    │ Retain raw containers and cap evidence. Prove     │
│ §3, 277–359              │ both incidence directions on X⪰D in §12.          │
│ 03 bp.exactProposal.v2,  │ Both starts below D; low-parent arm false above   │
│ §4, 361–431              │ D even in a low contest. Persist and reflect.     │
│ 03 bp.cleanInclusion.v2, │ Pending s−1 results transfer below P. Only        │
│ §5, 433–472              │ relevant roots, high J, and F need lie below P.   │
└──────────────────────────┴───────────────────────────────────────────────────┘
~~~

Each “Same” row uses only Δ-family block/HEAD receipt, seat counts,
or tree/score algebra. None reads F/J provenance, the row fold, or R6.
Rows that read them are proved again here (§§5–8.4). The 02/03
window-port markers therefore do not apply to these reused steps.

Sources: [02 §§2–3][clean-count], [02 §§4–5][clean-transfer],
[02 §6][clean-safety], and [03 §§2–5][proposal-pivot].
A low inactive or contested J is not silently included in “all F,J
are on the chain.” This distinction is needed in the Opus F3 substitution.

### 8.2 Initialization and events other than gates

**Proof.** Induct on the actual event prefix after i*. Within a tick
use clock, expiry, release if due, gate if due, then duties and own-row
processing. Within a block handler use admission, carried-vote calls,
cache update and immediate reconcile, then row calls. This is the
order used in [02 §5.1, lines 456–495][clean-induction].

At i*, there are no suffix results. HS supplies I1's separate seed,
the pending batch for the first gate, I3's pre-cut high sources, and
I4–I5. An old saved body may conflict with Q*. It is not an I1 member.

A direct vote or row receipt adds checked objects and stamps, or refuses
them. It does not change S, F, or the gate origins. A proposal or HEAD
duty emits its object without immediate local block/vote processing.
Expiry and release only delete targets. None of these steps invalidates
I1–I5. Old Λ records can suppress an FG send, but §6 excludes a source
substitution.

The new low-finalization carrier is delivered and then honestly stored; HS supplies C*.
For a block receipt, refusal causes no carried-object calls. On
admission, cumulative T and immutable states are preserved. Take any
new high justification in the stored state. Its target quorum has an
honest signer since q_F>a. Authentication supplies its actual earlier
row emission. By §6 and I3 its source precedes Q* if pre-cut, or a
completed suffix result if post-cut. The justified entry is a prefix
of that source. A high finalized entry has the same type of earlier
target origin. A low finalized entry precedes Q* by §5. Thus every
possible new F is compatible with all protected results, targets, and S.

The cached J can be a low conflicting entry. Its cache assignment does
not itself write S. Section 7 treats its later use by a duty. If F
advances, reconcile deletes only data incompatible with that F. No live
protected target or suffix saved confirmation conflicts with it. Old saved
bodies or old fastWrite members can be removed, with the evaluated label
retained. Signed objects, stamps, Λ, H, and T remain.

If F⪯old S, normalization keeps S. Otherwise compatibility gives
old S⪯F, so the assignment extends S and retains Q*. This preserves
I4 without assuming finalBelow across different nodes. Row-pool calls
after reconcile do not change this argument. A private carrier, when delivered, is in scope and has
the same signed origins as a public one.

### 8.3 A gate: active honest heads, order, and same-label safety

Let honest x execute its gate at d_s, s>u. If s=u+1, all honest
label-s HEADs extend Q* by HS. If s>u+1, every label-(s−1) gate is
complete. Its I2 certificate puts each of its results below every
honest label-s HEAD. I1 orders all still earlier results below them.
Thus every honest label-s HEAD covers Q* and every earlier suffix result.

At any receipt input through this gate, each usable source has label
≤s−1 by §6. A high pre-cut target source lies below Q*. A high
post-cut source precedes its earlier result. A low F precedes Q*.
Consequently every intervening F precedes each of these honest HEADs.
Their heads and dependencies are admitted by honest delivery and receipt
relay; an excluded branch cannot occur here. The votes and resolved
heads arrive before e_s, with their original strict stamps.

By §1.1, v_(u+1)≥GST, so v_s≥GST for every s>u, including s=u+1.
If v_s≤T_F, prefix agreement and Recovery₂.awake give full participation;
if T_F<v_s, continuation participation gives h_s>a. Thus set h=h_s>a.
Each of the h awake honest seats emits once. Every honest
late pool includes them, even if a head elsewhere becomes unresolved.
It has at most a other seats. At this gate the h heads are active, so
each protected prefix and F has at least h surviving early supporters:

~~~text
h ≤ D_late ≤ h+a < 2h.
~~~

The confirmation walk is on act(Σ), starts at F, and has no FJ band.
F passes its final strict-majority test. For any earlier protected
block B, all h honest heads contain B. If B⪯F, every returned
descendant covers B. If F≺B, all vertices from F to B are stored,
active, and have at least h support. An off-path child has only faulty
support. If its surviving support count is p≤a, then
D_late≥h+p>2p, so it cannot pass the strict-majority test. Each
path edge is selected. The result C is therefore nonempty, extends
Q*, and extends every earlier suffix result.

For another completed label-s result C', use their actual surviving
sets P_C,P_C' and late seat sets L_x,L_y. Early-to-late receipt puts
P_C∪P_C' in each late seat set. If C and C' conflict, a shared surviving
seat would require different heads. Relay of the vote for the different root identifier or its
cap evidence would remove that seat from surviving support. The sets
are therefore disjoint. Strict majority at x gives |P_C|>|P_C'|;
strict majority at y gives the reverse inequality. Contradiction.
So same-label results are compatible. Active filtering can remove
support but cannot remove a raw seat or equivocation evidence.
This is [02 bp.sameLabel.v1, lines 108–146][same-label] with all its
receipt premises supplied.

### 8.4 A gate: complete retrospective transfer

Fix this actual C at x,d_s, and honest y's earlier read q_s.
At q_s, every usable source has label<s. The newly proved order
therefore bounds each high source by C; old high sources precede Q*.
All live targets at that read are old targets below Q* or prefixes
of results at labels<s. They too precede C. The reader still stores C*.
Section 7 gives F_y⪯Z_y⪯A_y⪯C and lo_y≤ht(C).

Let P_C be x's surviving early support for C, p=|P_C|, and D its
late denominator. Let U be y's merged raw label-s set at q_s, V its
support declarations, and N its participant count. We have 2p>D.

For each supporting vote o with resolved head K⪰C, both o and K
were accepted at x before e_s. Strict forward relay puts K and its path
at y before z_s. F_y(q_s)⪯C and local F monotonicity exclude no
required K or path suffix; an already stored ancestor needs no new
admission. Relay puts o or same-seat cap evidence in y's pool.
If o were missing because y had its two distinct same-seat, same-slot
HEAD identifiers, those votes would relay back to x before d_s. At least one differs from o. That
would contradict o's survival at x. Hence o and its retained head occur
in y's frozen support view.

Conversely, every raw vote in U is either frozen before z_s or carried
in an admitted current proposal used by the q_s read. Its checked
handler accepted the signature, or the vote was already pooled,
or it already held two distinct same-seat, same-slot HEAD identifiers.
Receipt relay of that vote or that evidence reaches x before d_s.
A refused proposal supplies no such premise. An admitted but now
inactive proposal still supplies it because its original metadata remains
in cumulative T. Thus every U seat occurs in x's late set and N≤D.
Also V⊆U by the frozen and original carried declarations.

No source supporter can equivocate in U: backward relay would again
contradict its survival at x. Each of the p source seats supports every
path vertex toward C and no conflicting block. Since these p seats
are in U, each conflicting branch scores at most N−p, including
equivocators among the other seats. Therefore

~~~text
score(path vertex) ≥ p;  N ≤ D < 2p;
score(conflicting child) ≤ N−p ≤ D−p < p.
~~~

C and the required path are in the pre-freeze block arm just proved.
C itself supplies the height witness in that view. Every vertex after
A_y through C is in the filtered duty domain, is majority-eligible,
and strictly beats every eligible rival. This also covers a rival
enabled by the current-slot or low-parent arm. The finite suffix-walk
argument selects each edge toward C, then can only extend it. Its
distinct path vertices are in the finite view, so the usual tree-size
fuel suffices. Hence C⪯HEAD_y(q_s).

This proves I2 even for sleeping y and faulty proposal slots, without
p≥τ. The strict timings are
[01 §10.3, strict timing, lines 1071–1097][strict-relay]; the algebra and walk are
[02 bp.cleanTransfer.v1, lines 331–397][clean-transfer] and
[bp.suffixWalk.v1, lines 296–329][suffix-walk].
The current gate uses transfer only from earlier labels to prove order.
Only then does it prove its own transfer about an earlier read. It uses
no future result and supplies no future data to the protocol.

### 8.5 Guard, writes, actions, and finite endpoints

At the gate input, every old live target precedes Q*⪯C. Every target
written after the cut has an earlier local label and precedes an earlier
result, hence C. The whole-result guard passes.

The gate advances S to C unless C⪯old S. Existing S and C are
compatible, so either it keeps S or extends S to C. Fast and slow
lock loops range only over prefixes of C. Old saved bodies can affect
whether a slow test passes; they do not select the raw result or enlarge
the set of possible targets. No slow-write existence claim is used.
The newly saved confirmation and every new fastWrite member have this actual
gate origin. Final normalization preserves nesting and monotonicity.

An action at the same tick follows this gate. Section 6 supplies its
fresh source, or no row is emitted. If a row is emitted, its source
precedes C, now in I1. Client recording and own-row processing preserve
I3–I5. A different node's earlier tick at this time cannot read that
row. Later deliveries use an already completed source origin. Same-label
raw results remain comparable by §8.3 regardless of the order in which
the trace lists the local ticks.

This covers every event type. Empty or vetoed branches would keep S
and add no lock; the active-batch argument proves that they do not
occur at these suffix gates. A prefix ending before a pending gate
needs no claim about that gate's result. Every completed gate's q_s
read and strict-cutoff evidence already lie in the prefix.

At each next gate d_(s+1) within the horizon, its result extends every
label-s result and its update contains that result. Subsequent local
events extend S. Thus all honest outputs at d_s+4Δ contain every
label-s result and its source prefixes. This conclusion requires that
next gate within the horizon; no finite trace is extended to obtain it.

**Dependencies.** HS; §§5–7 as conditional steps; exact substitution
table in §8.1; counts, receipt, suffix-walk and event-order proofs cited
above; the frozen gate and reconcile handlers.

**Status.** PROVED-paper; Astra V1 and Opus F3/F7. The gate, transfer,
admission, reconciliation, and action steps are written out here.
This replaces the source report's outline over 02.

## 9. Seeded output safety — bp.wcSeededSafety.v2

**Statement (wc.seededSafety).** At all completed event reads from i*,
honest S outputs are compatible across nodes and times, each local S is
monotone, and Q* remains a prefix of every S.

**Proof.** At the cut, S=Q*. After the cut, trace any S value back
through the finite local event list. A keep branch preserves its origin.
A gate assignment has a suffix raw-result origin. A normalization has a
finalized-entry origin. A low finalized entry is below Q* and cannot
trigger normalization once Q*⪯S. A high entry has a target source
below Q* or a suffix result. Section 8 puts all these possible values
in the ancestor closure of one compatible chain. Given two read indices,
use the longer of their finite prefixes to obtain compatibility.

For monotonicity, each event either leaves S unchanged, advances it to
a compatible result, or normalizes it to compatible F. In the latter
two cases the assignment is made only when the new value is not below
old S. Compatibility then makes it an extension. Compose these prefix
relations over the finite interval between reads. Equality to Q* at
i* gives seed retention. Local nesting makes both public accessors S.

**Dependencies.** §8; [01 comp.outputNesting.v3][nesting];
the modified origin proof of [02 bp.cleanSafety.v1,
lines 674–708][clean-safety].

**Status.** PROVED-paper; Astra V1 and Opus F3/V1. This proves all
SSafeFromCut₂ fields except cross-node finalBelow, which needs §10.

## 10. Finality below every available output — bp.wcFinalBelow.v2

**Statement (wc.finalBelow).** For each completed suffix event index i
and honest x,y, F_x(i)⪯S_y(i).

E has an honestly stored controlling carrier; HS supplies the honestly held C*.
**Proof.** Use the window origins in §5 and 21 W3. A low finalized
entry E precedes Q* by §5. For a high E,
extract an honest signer of its finality certificate. That signer read
a justification for E before attaching its finality pair. Extract an
honest target signer from that justification and let K be the actual
source body for its target row, emitted after gate d_r.

If this target row is pre-cut, HS gives E⪯K⪯Q*. Otherwise r>u.
Section 8 gives K⪯C_(z,r). Its transfer makes every label-(r+1)
HEAD cover K, and the next nonempty gate at each y advances S above K.
Thus K⪯S_y(d_r+4Δ).

The finality signer's action input must already contain the justification
with this target evidence. Rows from an action at d_r cannot enter
another node's earlier action read at d_r. The target signer's own-row
processing also follows its action read. A target certificate must first
be consumed in a block state; own-row processing alone does not update
the head's chain state. Hence the finality action is strictly later than
the target action. Actions have spacing P_act, so

~~~text
finality action time ≥ d_r+P_act;
P_act=4RΔ≥8Δ>4Δ.
~~~

Before that action, every honest output already covers K and therefore E.
A finalization cannot be accepted before its honest finality signature
exists. A private carrier can delay acceptance but cannot advance it.
Section 9 preserves the coverage thereafter. If the accepted finalization
lies within the horizon, the strictly earlier d_r+4Δ also lies within
the horizon, so this use of the next gate is justified.

The final no-round rule only attaches finality to a new height vote
with h>h_f. It can postpone this action or suppress it. It cannot
shorten the strict action separation. No resend is used. Already accepted
high finalizations at i* have target rows through that cut, so the
pre-cut case covers them. Thus every possible value of F_x(i) precedes
every S_y(i), including at partial later batches of ticks.

**Dependencies.** §§4–6, 8–9; [21 IF.3][if123];
[01 bp.sourceDiscipline.v2][source-discipline];
[de183d7d Tick order][spec-tick] and [final client][spec-client].

**Status.** PROVED-paper; Astra V1/V2.8 and Opus V1. Compatibility alone
would not imply this field; the 4Δ versus P_act argument is necessary.

## 11. Proposal comparison prefix — bp.wcProposalPivot.v2

**Statement (wc.proposalPivot).** For an actual honest proposal P at
slot s with t_s≥d_u and d_s≤ρ.horizon, define

~~~text
D = deepest member of {Q*} ∪
    {C_(x,r) : x honest, u<r≤s−2}.
~~~

This finite maximum exists. At the proposal and each slot-s HEAD input,
F⪯Z⪯D, lo≤ht(D), and the live start precedes D.
Every honest label-(s−1) HEAD covers D, and both compared walks reach D.

**Proof.** The time grid gives s≥u+2. Section 8 makes the set nonempty
and compatible. Every gate with r≤s−2 is already complete before t_s.
At every read from t_s through v_s, the next pending gate is
d_(s−1)=t_s+2Δ. All usable sources and new lock writes therefore
have labels≤s−2. Old high sources and old live targets are below Q*;
new ones precede results in the defining set. Low F precedes C*.
The stored C* and §7 give the root and floor bounds at each read,
including reads after late certificate disclosures.

By §1.1, v_(s−1)≥v_(u+1)≥GST, already for s=u+2. Thus the
previous-label votes and their relay windows use the post-GST Δ deadlines.
If s=u+2, D=Q*, and HS supplies label-(s−1) HEAD coverage.
Otherwise I2 at label s−2 gives coverage of every result there;
I1 gives the earlier prefixes, including Q*. Thus all h_(s−1)
awake honest votes support D. They and their head paths arrive before
e_(s−1)=t_s−2Δ. Their active status persists because all receiving
F values at the compared reads precede D. Local F monotonicity gives
the same bound at earlier relay inputs.

D is stored in full T at the proposer and before z_(s−1) at each
voter. For D=Q*, storage at d_u precedes z_(s−1), already for
s=u+2. For a suffix result D at label r≤s−2, take one surviving
early supporter of that result. Relay of its resolved head and path
before e_r+Δ=z_r supplies D before z_(s−1). This proves path
availability without an assumed broadcast of the gate result.

At either read the previous-label raw set has at most h_(s−1)+a
seats. Authentication permits no extra honest signature at that label.
Each edge toward D has score at least h_(s−1); every conflicting
edge has score at most a, including equivocators. Since h_(s−1)>a,
the path has strict majority and strict dominance. D is a height
witness in each actual view by lo≤ht(D). The live starts precede D.
The suffix-walk proof therefore makes both walks reach D. In particular
the proposal's parent Q satisfies D⪯Q.

**Dependencies.** §§7–8; [03 §2.1, comparison prefix D, lines 229–275][proposal-pivot],
with the substitutions above; [02 bp.suffixWalk.v1][suffix-walk].

**Status.** PROVED-paper; Astra V1/V4 and Opus F3/V1. No no-contest
assumption and no bound h_(s−1)>2a is used.

## 12. Exact proposal adoption — bp.wcExactProposal.v2

**Statement (wc.exactProposal).** Under §11's premises, every honest
node admits P before v_s. Its deterministic label-s HEAD is exactly P,
including when the node is asleep.

**Proof: admission.** Section 11 gives F_y⪯D⪯Q=P.parent throughout
delivery. C1 delivers the complete honest block body and dependencies to every
honest node before v_s. Carried rows add no Δ_F wait. R7's optional omission keeps every effect, so this admission argument is unchanged. The honest proposal has an earlier-slot full named parent and satisfies
the signature, carried-object, body-encoding, and digest checks.
C1 supplies its exact full named parent before admission. If it is not already stored,
its admission tests pass. In particular, a finality exclusion cannot
remove P or its required path. Single-proposer authentication makes P
the only slot-s proposal in each admitted tree.

**Proof: full score producer.** Let U be the set of signed HEAD identifiers
in P's ordered previous-slot raw list. Its ordered support list records
exactly the identifiers resolved at the proposal read.
Let U' be the receiver's frozen previous-slot pool merged with P's
original carried raw pool. There is no other current-slot proposal.
Original metadata is retained, even when an individual carried-vote
handler refuses a copy, so U⊆U'.

By §1.1, GST≤v_(u+1)≤z_(s−1)=t_s−Δ, already for s=u+2.
Hence the backward cutoff and the forward proposal relay window are after GST.
Take an extra vote in U'. It was accepted at the receiver before
z_(s−1)=t_s−Δ. Strict receipt relay calls the proposer before t_s.
The vote has a current/previous-slot label at that call. If it is absent
from U, the proposer already has two distinct HEAD identifiers for that seat and slot.
Therefore every extra vote's seat already equivocates in U. This proves
equality of participant sets and equivocation sets, without requiring
literal equality of raw sets.

Fix X⪰D and a seat that does not equivocate in U. We prove equality
of support incidence in both directions.

1. If the proposer declared a valid-slot head K⪰X, K was admitted
   by its proposal read. Its acceptance and path relay reach the
   receiver before v_s. Receiving F through this interval is below
   D⪯X⪯K, so K is admitted or already stored; excluded ancestors
   are already present by parent closure. P retains the original
   declaration. Thus the receiver counts that support.
2. Support at the receiver from P's original declaration was already
   declared by the proposer, with the same K and slot. For extra
   frozen support, both its vote and resolved head existed before
   z_(s−1). Relay puts the vote or cap evidence, and K, at the
   proposer before t_s. Cap evidence is impossible for this
   nonequivocating seat in U. Since K⪰X⪰D⪰F_p, exclusion of
   the needed head is impossible. The vote is therefore resolved
   at the proposal read with the same valid slot, and is in the
   originally declared subset.

Each equivocating seat scores one in both views. Each other seat
contributes the equal incidence just proved. Sum over the equal finite
participant set. Counts, scores on every X⪰D, and majority thresholds
agree. A head excluded by F cannot support such X; its raw seat and
equivocation evidence are still counted. This is the complete seeded
producer for [03 bp.scoreSuffix.v2, lines 277–359][score-suffix],
including the head-membership premise that a formal score lemma needs.

**Proof: paths, eligibility, and competitors.** Both walks reach D.
At a voter, every prefix of P belongs to its current-proposal path arm.
For every vertex X from D through P, P is a witness in that view
with ht(P)≥ht(D)≥lo_y. Also F_y⪯Z_y⪯D⪯X. Thus the entire
required suffix is in the voter's filtered domain.

At each parent X⪰D, ht(X)≥lo_p,lo_y. The low-parent eligibility
arm is false in both walks, even if a low contest remains. For an old
child, the current-slot arm is also false. Its eligibility is exactly
the common majority test.

Follow the selected proposer path from D to Q. A selected child toward
Q persists at the voter because it is on P's admitted path and has
the same score and majority. Conversely, an old eligible child at the
voter is either on P's path or in the pre-freeze arm. The path case is
already stored by the proposer. In the frozen case, receipt relay puts
it and its dependencies at the proposer before t_s. It extends
X⪰D⪰F_p, so it is not excluded. Its own height is at least ht(D),
so it witnesses its own viability in the proposer's full tree. It
extends Z_p and passes the same majority test. Thus every receiving
eligible competitor is also a proposer candidate.

At each parent before Q, persistence and reflection give the same
winning child under the common score and root order. Induction along
the finite path reaches Q. At Q, P is present and current-slot
eligible. An old eligible receiving child would reflect to an eligible
child at the proposer's terminal Q, a contradiction. No different
current-slot child exists. The next step is P. No child of P can be
present at v_s, since it would have slot>s and future blocks are
refused. The returned HEAD is exactly P.

The distinct vertices of this path lie in the finite walked view, so
the walk has sufficient fuel. The proof uses no equality of whole
domains and does not assume that the initial live start belongs to
the HEAD view. Section 11 proves the required suffix from that start.

**Dependencies.** §11; [03 bp.scoreSuffix.v2][score-suffix] and
[bp.exactProposal.v2, lines 361–431][exact-proposal];
strict receipt, authentication, and cumulative metadata.

**Status.** PROVED-paper; Astra V1/V4, Opus F3/V1, and the score-producer
limitation stated in Opus “Not checked,” line 188, are addressed here.

## 13. Inclusion within 6Δ — bp.wcInclusion6.v2

**Statement (wc.inclusion6).** Each actual honest P in the field of
§1.2 satisfies P⪯S_y(d_s) at every honest y, and remains in S_y at
every later public read through the horizon.

**Proof.** The gate at label s−1 is pending when label-s HEADs are
read. For each of its eventual raw results C_(x,s−1), §8 proves
retrospectively

~~~text
C_(x,s−1) ⪯ HEAD_y(v_s) = P.
~~~

This uses no exact adoption in the proof of transfer. Section 12 used
only results through s−2, so there is no cycle. Every earlier suffix
result precedes these pending results, and Q*⪯P.

Before a gate input at d_s, usable sources have labels≤s−1.
High pre-cut sources precede Q*; later sources precede the just-bounded
results. Low finalizations precede C*. Thus every F at these inputs
precedes P, and each live target precedes P. A low conflicting cached
J need not precede P; the confirmation walk uses F and act(Σ) with
no FJ band. Such J cannot invalidate this step.

All h_s honest votes have head exactly P and reach every early pool
before e_s. They remain active through d_s because F⪯P. No honest
seat equivocates. For each prefix of P above F,

~~~text
2p ≥ 2h_s > h_s+a ≥ D_late.
~~~

A conflicting branch or strict descendant of P has only faulty
surviving support p≤a. Its late denominator includes those p seats
and all h_s honest seats, so D_late≥h_s+p>2p. It cannot pass.
Also F≺P at the input: if P⪯F, a justification at or above P
would need an honest target source at or above P, with source label
at least s. That row's action is at or after d_s, after the local
gate, and cannot be in the input. This is
[01 §6.6, finality before an honest proposal gate, lines 764–772][before-gate].

The confirmation walk from eligible F therefore returns exactly P.
The guard passes because all live targets precede P. The gate saves P
and advances S to a value containing P. This update is before the lock
tests and does not require a fast write. Final normalization cannot
remove P because F⪯P. Same-time actions and deliveries preserve §8's
invariant. Hence the inclusive public read at d_s contains P.
Section 9 supplies persistence at every later read.

The delay is d_s−t_s=6Δ. The proof uses h_s>a, not h_s≥τ,
2h_s>n, or h_s>2a. Sleepers execute the same gate and receive the
same required honest batch. No later honest proposal is needed.

**Dependencies.** §§8–12; [03 bp.cleanInclusion.v2,
lines 433–472][inclusion]; [de183d7d gate][spec-gate].

**Status.** PROVED-paper; Astra V1/V4 and Opus F5/V1/V4. This supplies
the pending-gate frame and exact inclusion step under weak participation.

## 14. Bounded wrapper — bp.weakContinuationAvailable.v2

**Statement (wc.boundedAvailable).** The proposition in §1.2 holds
with t₀=d_u, the revised B_H^F, and one u,Q*,i* for both conclusions
and for every continuation.

**Proof.** Fix the outer premise δ_t=2R and any source satisfying
StrongRecoverySearchPrefix₂. H.22/H-time selects u,Q*,i* with
BoundedHealingCut₂ and d_u<T_F. Section 4 derives HS for this selection.
Only now fix arbitrary E',ρ with CleanContinuation₂. Section 3
transfers the selected cut and HS to ρ. Its fixed identities preserve
a≤f. Section 1.1 gives v_(u+1)≥GST, including the first gate label s=u+1.
Prefix agreement and later participation therefore give h_s>a
for every gate used after the cut. Synchrony covers pending receipts.

Apply §§8–10 to obtain every SSafeFromCut₂ field. Apply §§11–13 to
each proposal with d_u≤t_s and d_s≤ρ.horizon. This gives the exact
IncludedFromCut₆Δ field, with persistence, for the same witnesses.
The event proof includes pairs with one read in [d_u,T_F] and the
other after T_F. It makes no independent witness choice for inclusion.
This proves the quantified statement and its safety projection.

**Dependencies.** H.22/H-time with C1, K≥2, R≥max(2,κ), δ_t=2R; §§3–13.

**Status.** PROVED-paper; Astra G1/S1/S2/V5 and Opus F5/V5.
No SeedClosed, HealingInput, desired suffix invariant, extra all-awake
period, or later proposal gap is added to a continuation premise.

## 15. Why no extra recovery window

DC's finite preparation is substantive. In its notation, let
D_F=fgSafetyProgressDeadline and ℓ=progressLag' gap extra. Then

~~~text
seedLag gap extra = 4·gap+12+2·extra;
ℓ = seedLag gap extra+3·gap+10+2·extra;
base = D_F+2ℓ+1;
n = D_F+2ℓ+max(1+η_SG, gap+3).
~~~

[DC RecoveryWindowClosure, lines 16–36][dc-window] supplies this
inequality from the strong prefix. The prepared seed is
[SettledBootstrapPreparedV4, lines 16–44][dc-prepared]; LatestSeed is
separate at lines 46–55. The source report's W1 and both reviews'
V3 sections give the comparison used below. Each field is listed
separately, including fields grouped in the review table.

~~~text
┌──────────────────────────┬────────────────────────────────────────┬────────────┐
│ DC field                 │ FG-SA reason                           │ Extra wait │
│                          │                                        │ after d_u  │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ settled                  │ No SG. Slot pools admit only current/  │ 0          │
│                          │ previous labels. Old live locks        │            │
│                          │ already precede Q* by HS and I5.       │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ basePost                 │ H0 gives v_(s*)≥GST and u₀≥GST+2P_act. │ 0          │
│                          │ Reset search is already inside B_H^F.  │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ seed                     │ H3 gives the exact honest label-u      │ 0          │
│                          │ HEAD batch Q*.                         │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ seedAll                  │ H3 includes all honest HEAD reads;     │ 0          │
│                          │ H5 gives the pending u+1 batch above   │            │
│                          │ Q*. Both reads precede the cut.        │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ confirmationSeedPrepared │ H.17 gives raw result, guard, and      │ 0          │
│                          │ actual post-gate S=Q* at every node.   │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ LatestSeed               │ FG-SA has one S record. Both public    │ 0          │
│ (separate from V4)       │ accessors read it. H.17 refreshes it   │            │
│                          │ in the same gate. No second refresh.   │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ runBlock                 │ BoundedHealingCut₂.actualProposal:     │ 0          │
│                          │ Q* is an actual honest emitted block.  │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ oldRows                  │ H0 caps rows through u₀ by M. H.14     │ 0          │
│                          │ puts every high source at label≥s*.    │            │
│                          │ HS bounds high pre-cut rows by Q*.     │            │
│                          │ The finite preparation is in B_H^F.    │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ heightCap                │ ht(Q*)≥ht(C*)=M+1. Low finalized       │ 0          │
│                          │ entries are below C* by §5.            │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ frontierSeed             │ No cap+1<H premise. At H=M+1, a        │ 0          │
│                          │ low active J precedes stored C*, or    │            │
│                          │ a contest roots at F with lo=M+1.      │            │
│                          │ If H=M+1 and j<M, Z=F and lo=M.        │            │
│                          │ At higher H, §7 excludes a contest.    │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ sgBoot                   │ No SG boot interval. Slot labels and   │ 0          │
│                          │ the seeded pending HEAD batch remove   │            │
│                          │ the corresponding choice duty.         │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ confBoot                 │ Only Q* and suffix results enter the   │ 0          │
│                          │ history. Old saved bodies can affect   │            │
│                          │ slow tests, not new result choice.     │            │
├──────────────────────────┼────────────────────────────────────────┼────────────┤
│ fgAll                    │ HS bounds old high row sources. The    │ 0          │
│                          │ induction bounds new sources. Low F    │            │
│                          │ uses crossing; low J uses §7.          │            │
└──────────────────────────┴────────────────────────────────────────┴────────────┘
~~~

In particular, retained FG rows do not expire. Their height and actual
emission origins control their effects. Historical fastWrite sets are
not fresh sources. Old Λ locks and sent records can stop an action
from sending; they cannot move S onto an old conflicting body.
The frame reads cumulative T, so a stored C* remains a low-contest
witness. These are protocol reasons, not assumptions that old state
was erased.

Thus W=0 is relative to the selected completed H.22 gate. The B_H^F
recovery interval already pays for reset progress and the proposal
search Γ. It replaces the relevant DC preparation duties; it is not
a claim that recovery has no window. The source still stays fully
awake through T_F. Pending C1 row obligations retain their original
deadlines; no Δ_F drain is added at T_F. This addresses Astra S1/V3 and Opus F6/V3. DC's SG
expiry, two-height frontier margin, and stronger LatestSeed refresh do
not require an additional FG-SA wait.

## 16. Status, review closure, and limits

The proof order is exactly W5. Conditional source and frame lemmas
are closed jointly by the event induction. All statuses below depend
on the cited H.22 and foundation results as supplied paper inputs.

~~~text
┌─────────────────────────────────┬──────────────────────────────┬──────────────┬──────────────────────┐
│ Claim id                        │ Statement                    │ Status       │ Review items closed  │
├─────────────────────────────────┼──────────────────────────────┼──────────────┼──────────────────────┤
│ bp.wcPrefixReplay.v2            │ Preserve source and cut      │ PROVED-paper │ A:V1,S2; O:V1        │
│ bp.wcHeightSeed.v2              │ Selected H.22 cut has HS     │ PROVED-paper │ A:G1,S2; O:F1,F4     │
│ bp.wcLowFinalized.v2            │ Low finalized E⪯C*⪯Q*        │ PROVED-paper │ A:V1,V2.2; O:V1      │
│ bp.wcSourceOrigin.v2            │ Fresh gate; fixed old origin │ PROVED-paper │ A:V1,V2.4–5; O:V1    │
│ bp.wcSeededFrame.v2             │ F⪯Z⪯B; lo≤ht(B)              │ PROVED-paper │ A:V1; O:F1,F2        │
│ bp.wcSeededInduction.v2         │ Ordered results and transfer │ PROVED-paper │ A:V1; O:F3,F7        │
│ bp.wcSeededSafety.v2            │ Safe, monotone S; seed stays │ PROVED-paper │ A:V1; O:F3,V1        │
│ bp.wcFinalBelow.v2              │ F_x(i)⪯S_y(i)                │ PROVED-paper │ A:V1,V2.8; O:V1      │
│ bp.wcProposalPivot.v2           │ Common prefix and floors     │ PROVED-paper │ A:V1,V4; O:F3,V1     │
│ bp.wcExactProposal.v2           │ All slot-s HEADs equal P     │ PROVED-paper │ A:V1,V4; O:F3,V1,188 │
│ bp.wcInclusion6.v2              │ Include P by d_s and retain  │ PROVED-paper │ A:V1,V4; O:F5,V4     │
│ bp.weakContinuationAvailable.v2 │ Same bounded safety/service  │ PROVED-paper │ A:G1,S1,S2; O:F5,V5  │
│                                 │ witnesses for every suffix   │              │ A:V3/O:F6 in §15     │
│ bp.weakContinuationGrowth.v2    │ Same witnesses: joint growth │ PROVED-paper │ §17; Astra review    │
│                                 │ by t+G'+6Δ (§17)             │              │ bp23growth-astra     │
└─────────────────────────────────┴──────────────────────────────┴──────────────┴──────────────────────┘
~~~

A means [Astra review][astra]; O means [Opus review][opus].
Opus findings F1–F7 are at lines 19–58; its V1 is at lines 62–100,
V3 at 146–167, and V5 at 181–183. Astra's findings G1/S1/S2 are
at the start of its Findings table; its V1, V3, and V5 give the
corresponding lemma and statement checks. The reviews checked the
source report, not this later chapter. The closure arguments are here.

**Unclosed listed paper gaps: none.** The preceding entries state the
paper proof status. The WC-LIVE Lean names are in §17; the new companion
branch results and their pending landing work are in §§18–19.
The chapter does not independently reprove the entire H.22 bounded
search or the DC prepared-seed theorems. These are cited dependencies,
not missing steps in the continuation induction.

Relative to wc-paper-proof.md, the chapter makes these repairs:

1. Restore δ_t=2R in the displayed wrapper. This is an existing outer
   premise, required by H-time. This window port uses the revised
   timing clauses and B_H^F from §1.1.
2. State the exact inclusion field, t₀=d_u, same witnesses, and the
   participation boundary T_F. State the safety-only projection.
3. Add the reader-stores-C* premise and define every controlling
   certificate use, including cumulative off-J crossings.
4. Correct the H.12/H.14/H2.A/H.16/H.17 seed citations. Preserve old
   event origins and exclude low old J from the chain invariant.
5. Give the complete Clean substitution table and write out the event
   induction, cap-aware transfer, score producer, and pending gate.
6. Compare every DC prepared field, with B_H^F preparation kept explicit.

The window continuation is **PROVED-paper** from the revised H.22.
The uniform T_F endpoint, reference bound, replay, wrapper, and table
entries close Opus recovery finding F5. W1–W3 and the original-source
seed close the continuation obligations in delta §6. Astra V5 identified
no further chapter-23 gap. The historical review verdicts at the start
refer to wc-paper-proof; their quoted status has not been changed.
The old Lean premise records need the timing instance described in §1.1;
this chapter makes no claim that their code has changed.

## 17. Growth after the selected cut — bp.weakContinuationGrowth.v2

### 17.1 Scope and exact statement

Use the parameter context, source premises, and continuation premises of §1.1. Time is an integer; slots are natural numbers; Δ>0. The specification gives

```text
t_s = 4sΔ;    d_s = t_s+6Δ.
```

See [spec, Schedule, lines 282–290](../spec/fgsa-protocol.tex:282). Thus `SA.gateTime p.toParams u` is d_u, and `V2.D.proposalTime (fgsaInterface p c) s` is t_s.

**Statement.** The witnesses selected in §14 also give growth. The complete bounded statement has the following order. This is `BoundedSafetyLivenessRecovery₂` at `be214b3`, [WeakContinuationLive.lean, lines 64–72](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/WeakContinuationLive.lean:64):

```lean
p.δt = 2 * p.R →
∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
  StrongRecoverySearchPrefix₂ p c E source G ΔF →
  ∃ (u : Slot) (Q : Block) (iStar : Nat),
    BoundedHealingCut₂ p c E source u Q iStar ΔF ∧
    ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      CleanContinuation₂ p c E source E' rho ΔF →
      WeakContinuationLiveAt₂ p c E' rho u Q iStar ΔF
```

Choose u,Q,iStar once on the source. Use this same choice for safety, inclusion, and growth in every continuation. In the chapter notation, Q=Q* and iStar=i*.

For a fixed continuation environment E and run rho, the exact `growth` field of `WeakContinuationLiveAt₂` is [lines 46–53](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/WeakContinuationLive.lean:46):

```lean
growth :
  SA.gateTime p.toParams u ≤ rho.horizon →
  ∀ G' : Time, 4 * p.Δ ≤ G' →
    AwakeProposerRecurrenceFrom p c E rho (SA.gateTime p.toParams u) G' →
  ∀ t : Time,
    SA.gateTime p.toParams u ≤ t →
    t + G' + 6 * p.Δ ≤ rho.horizon →
    JointGrowthAt p c E rho t (t + G' + 6 * p.Δ)
```

The source gap G does not fix G'. Each continuation can satisfy recurrence for its own G'. `AwakeProposerRecurrenceFrom` means that, for every t with d_u≤t and t+G'≤rho.horizon, there is a positive honest slot s such that

```text
t < t_s ≤ t+G',
and the slot-s proposer is awake at t_s.
```

See [Regimes.lean, lines 93–105](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/Regimes.lean:93), inspected at `be214b3`.

`JointGrowthAt E rho t D` means that one slot s and one actual honest proposal B satisfy

```text
t < t_s;
HonestProposal E rho (fgsaInterface p c) s B;

for each g ∈ {stable,confirmed}:
  ∀ x ∈ rho.honest, outputAt(g,x,t) ≺ B;
  ∀ x ∈ rho.honest, B ⪯ outputAt(g,x,D).
```

Here D is a deadline, and ≺ is strict ancestry: A≺B means A⪯B and A≠B. The proposal B is the same for both getters and all honest readers. This is the exact body of [OutputReads.lean, JointGrowthAt, lines 39–48](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/OutputReads.lean:39), inspected at `be214b3`.

### 17.2 Proof

**Proof.** Follow the source-witness order of [§14, bp.weakContinuationAvailable.v2, lines 1162–1188](23-continuation.md:1162). Fix δ_t=2R and a source satisfying `StrongRecoverySearchPrefix₂`. Select its u,Q*,i* once. Only then fix an arbitrary continuation E',ρ satisfying `CleanContinuation₂`.

The existing wrapper supplies safety and inclusion for this same choice. We prove its growth field as follows.

1. **Transfer the cut and discharge gate coverage.**

   The source cut satisfies d_u<T_F=source.horizon. Continuation coverage gives source.horizon≤ρ.horizon. Hence d_u≤ρ.horizon.

   By [§3, bp.wcPrefixReplay.v2, lines 350–376](23-continuation.md:350), the cut transfers exactly:

   ```text
   i* = afterTicksIdx(ρ,d_u).
   ```

   Apply [§9, bp.wcSeededSafety.v2, lines 863–890](23-continuation.md:863) and [§13, bp.wcInclusion6.v2, lines 1102–1160](23-continuation.md:1102). These give suffix monotonicity and persistent proposal inclusion. No new source witness is selected.

2. **Fix the gap and trigger; check all time bounds.**

   Fix any G' with 4Δ≤G' and `AwakeProposerRecurrenceFrom E' ρ d_u G'`. Then fix any t with d_u≤t and t+G'+6Δ≤ρ.horizon. Define

   ```text
   D = t+G'+6Δ.
   ```

   Since u≥0 and Δ>0,

   ```text
   d_u = 4uΔ+6Δ ≥ 6Δ > 0.
   ```

   Therefore 0≤t. Also G'≥4Δ>0 and 6Δ>0, so

   ```text
   d_u ≤ t ≤ t+G' ≤ D ≤ ρ.horizon.
   ```

   In particular, t+G'≤ρ.horizon. This is the finite-window guard needed to apply recurrence. It follows from the stated growth deadline; it is not an additional premise.

3. **Obtain a future awake honest slot and its actual proposal.**

   Apply recurrence at t. It gives a positive slot s, an honest slot-s proposer, and awake evidence at t_s, with

   ```text
   t < t_s ≤ t+G' ≤ ρ.horizon.
   ```

   `CleanContinuation₂.base.valid` gives a well-formed schedule, and its `base.delta` gives E'.Δ=p.Δ. The honest proposer therefore has its scheduled tick at t_s: this is public tick number 4s, since t_s=(4s)Δ. The tick lies within the horizon.

   Since s>0 and the proposer is awake, the proposal duty emits an actual block B with B.slot=s. The spec states this duty at [lines 1044–1045](../spec/fgsa-protocol.tex:1044) and sets the new block's slot to s at [lines 1567–1583](../spec/fgsa-protocol.tex:1567).

   This step mirrors `fgsa_honestProposal_exists_of_awake_slot`, [P/Shared/OutputGrowthProposal.lean:57](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthProposal.lean:57), at `be214b3`. Its premises are exactly the schedule, Δ equality, honest slot, awake evidence, and covered proposal time established above.

4. **Check the inclusion start and proposal deadline.**

   From d_u≤t<t_s,

   ```text
   4uΔ+6Δ < 4sΔ.
   ```

   To check the natural-number slot bound, suppose s≤u+1. Then, since 4Δ>0,

   ```text
   t_s = 4sΔ
       ≤ 4(u+1)Δ
       = 4uΔ+4Δ
       < 4uΔ+6Δ
       = d_u.
   ```

   This contradicts d_u<t_s. Thus s>u+1, and the natural-number order gives u+2≤s. This argument uses no truncated natural subtraction.

   Also,

   ```text
   d_s = t_s+6Δ ≤ t+G'+6Δ = D ≤ ρ.horizon.
   ```

   Apply bp.wcInclusion6.v2 to the actual proposal B. Its paper start guard d_u≤t_s follows from d_u≤t<t_s. Its Lean slot guard u+2≤s was proved explicitly. Its gate and read guards follow from d_s≤D≤ρ.horizon. Hence, for every honest x,

   ```text
   B ⪯ S_x(D).
   ```

   This includes sleeping honest readers.

5. **Put both public reads within the suffix and apply monotonicity.**

   By definition, timeIdx(ρ,a) counts all events with time≤a. The post-tick cut counts events through ticks at d_u and excludes later same-time deliveries. Thus

   ```text
   i* = afterTicksIdx(ρ,d_u) ≤ timeIdx(ρ,d_u).
   ```

   This is the **second conjunct** of `preIdx_le_afterTicksIdx`, [P/Shared/Reads.lean:93](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Shared/Reads.lean:93), at `be214b3`.

   Since d_u≤t≤D, inclusion of the corresponding event filters gives

   ```text
   i* ≤ timeIdx(ρ,d_u) ≤ timeIdx(ρ,t)
      ≤ timeIdx(ρ,D) ≤ ρ.events.length.
   ```

   The last bound holds because a filtered list has length at most the original list. Thus both indices are valid suffix indices, even when t=d_u or D=ρ.horizon. Same-time deliveries at d_u are after the cut and within the suffix.

   Apply bp.wcSeededSafety.v2 at these indices. For every honest x,

   ```text
   S_x(t) ⪯ S_x(D).
   ```

   Both getters equal this inclusive S read. See [01, comp.outputNesting.v3, lines 774–793](01-foundations.md:774) and its Lean read bridge `fgsa_outputAt_eq_S_at`, [P/Shared/OutputGrowthReads.lean:12](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthReads.lean:12), at `be214b3`.

6. **Exclude B from the trigger output.**

   We have a well-formed schedule, 0≤t, t<t_s, and s≤B.slot because B.slot=s. Apply `fgsa_output_noFuture_of_slot`, [P/Shared/OutputGrowthCausal.lean:25](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthCausal.lean:25), at `be214b3`. For either getter and every reader x, it gives

   ```text
   ¬ B ⪯ outputAt(g,x,t).
   ```

   The causal arithmetic is as follows. Define `slotOf(a)` as Lean's natural conversion of the integer quotient a/(4Δ). If B were a prefix of S_x(t), stored ancestor closure would put B in the stored tree. The scheduled store-slot bound and the inclusive read clock bound would then give

   ```text
   B.slot ≤ slotOf(local clock) ≤ slotOf(t).
   ```

   The local clock at this read is at most t: it is either the initial clock 0 or the time of an event included in the read. The initial case uses the explicitly proved 0≤t.

   Since 4Δ>0 and t<4sΔ, integer division gives

   ```text
   t/(4Δ) < s.
   ```

   Since t≥0, this quotient is nonnegative. Its natural conversion therefore preserves the inequality; s>0 is already known. Hence slotOf(t)<s. Together with B.slot=s, this yields s≤slotOf(t)<s, a contradiction.

   The spec's acceptance rule excludes blocks with slot greater than the store slot and requires the exact full named parent; see [lines 802–809](../spec/fgsa-protocol.tex:802). The pinned causal producer supplies the corresponding stored-tree and clock facts.

7. **Use the common descendant to obtain strict growth.**

   Fix an honest x. Steps 4 and 5 give

   ```text
   S_x(t) ⪯ S_x(D),    B ⪯ S_x(D).
   ```

   Two ancestors of one block are ordered on its parent path. Thus S_x(t)⪯B or B⪯S_x(t). Step 6 excludes the second case. It also excludes equality, since equality would give B⪯S_x(t) by reflexivity. Therefore

   ```text
   S_x(t) ≺ B ⪯ S_x(D).
   ```

   This is the common-descendant argument in `jointGrowthAt_of_inclusion`, [P/Shared/OutputGrowth.lean:12](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAProofs/Proofs/Shared/OutputGrowth.lean:12), at `be214b3`.

8. **Return the joint witness and close the bounded statement.**

   Both getters equal S at both inclusive reads. Return the same s,B from step 3 for every honest reader and both getters. We have t<t_s, an actual honest proposal, strict ancestry at t, and inclusion at D. These are exactly the fields of

   ```text
   JointGrowthAt E' ρ t (t+G'+6Δ).
   ```

   G' and t were arbitrary after the continuation was fixed. The continuation was arbitrary after the source witnesses were selected. Safety, inclusion, and growth therefore use the same u,Q*,i*, in the exact order of `BoundedSafetyLivenessRecovery₂`.

### 17.3 DC counterpart and intentional differences

The counterpart is `DC AvailableChainGrowth.afterGST`, [DecoupledConsensusInternal/Legacy/Liveness.lean, lines 46–51](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusInternal/Legacy/Liveness.lean:46). DC also selects its recovery witness before every continuation, then universally quantifies the continuation gap. The source gap and continuation gap can differ in both statements.

The intentional differences are:

```text
┌──────────────────┬──────────────────────────┬─────────────────────────────┐
│ Item             │ DC counterpart           │ FG-SA                       │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Recovery witness │ A bounded round m for    │ One completed d_u and       │
│                  │ this growth property     │ u,Q*,i* shared with safety  │
│                  │                          │ and inclusion               │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Start            │ opening_slot m           │ The completed gate d_u      │
│                  │                          │ below T_F                   │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Recurrence       │ Opening/carrier pattern  │ One positive honest slot,   │
│                  │ over round windows       │ awake at its proposal time  │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Gap and triggers │ A round gap; round       │ Integer G'≥4Δ; every time   │
│                  │ triggers                 │ t≥d_u                       │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Deadline         │ Covered action time      │ Covered t+G'+6Δ, using the  │
│                  │ S.a(r+gap)               │ proposal gate d_s=t_s+6Δ   │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Inclusion start  │ DC's own slot boundary   │ s≥u+2; slot u+1 starts      │
│                  │                          │ before the selected gate    │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Growth outputs   │ Raw confirmation growth; │ One actual proposal grows   │
│                  │ confirmed persistence    │ both stable and confirmed   │
├──────────────────┼──────────────────────────┼─────────────────────────────┤
│ Exact result     │ Exact confirmation at    │ Prefix inclusion at the     │
│                  │ the proposal deadline    │ shared deadline             │
└──────────────────┴──────────────────────────┴─────────────────────────────┘
```

The named DC recurrence is `ProposerOpeningCarrierRecurrence`, [Legacy/Assumptions/Recurrence.lean, lines 34–46](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusInternal/Legacy/Assumptions/Recurrence.lean:34). It requires two earlier honest openings and an honest opening plus two carrier slots. The conclusion of `AvailableChainGrowth.afterGST` is `AvailableChainGrowthFrom`, [Legacy/Definitions/NamedHeadReads.lean, lines 79–92](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusInternal/Legacy/Definitions/NamedHeadReads.lean:79).

FG-SA needs only one future awake honest proposal because bp.wcInclusion6.v2 serves that proposal within 6Δ. Its recurrence has the single-proposer form of [DC Generic/Conditions.lean, lines 207–211](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Conditions.lean:207), with the added awake condition. Both FG-SA getters expose S, so the same proof gives their joint growth.

The agreement, participation, and receipt differences remain those stated in §1.3. Growth adds recurrence as a conditional field premise; it does not add recurrence to `CleanContinuation₂`.

**Status.** PROVED-paper from the cited chapter lemmas and pinned shared producers. No paper arithmetic or read bridge remains open.

Growth is a field of [FGSAClaims.weakContinuationLive, line 113](/Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/FGSAClaims.lean:113) at `e1d4232`.
This paper edit did not run a Lean build or axiom audit.

The WC-LIVE erratum is the complete statement in §17.1, not a separate
choice of growth witnesses. Its Lean names are
`WeakContinuationLiveClaim`, `BoundedSafetyLivenessRecovery₂`, and
`WeakContinuationLiveAt₂.growth`. The source cut is chosen before the
continuation and before its gap G'. Section 19 keeps this order while
allowing the honest set to decrease.

## 18. Outage continuation — OutageContinuationClaim

**Statement.** Use the healthy prefix, stable read, and fast or slow lag
of `Outage₂`. Fix honest x and B⪯S_x(T). Replace the old budget by

```text
b₁ − b₀ + ((b₀ − 6Δ) mod 4Δ) ≤ L.                 (V)
L = (4k−1)Δ.
```

Assume full-run `PartialSynchronyBy` with acceptance relay, GST≤b₁,
and h_t>a for b₁≤t≤ρ.horizon. Participation is not required in
[b₀,b₁); all honest validators can sleep there. No
`FinalitySlashableBound` premise is required. For every honest y and
b₀≤t≤ρ.horizon, at the inclusive read,

```text
B ⪯ S_y(t),  B ⪯ stable_y(t),  B ⪯ confirmed_y(t),  B ∥ F_y(t).
```

The conclusion permits honest HEADs to regress below B. It does not
require a common local frame, renewed B lock, or common S value.

**Proof sketch.** Genesis is immediate. For non-genesis B, arming gives
6Δ≤b₀. Put j=floor((b₀−6Δ)/(4Δ))+1, e₀=d_j+L, and
r=min{s:b₁≤v_s}. Condition (V) gives r≤j+k and v_r<e₀.
Pre-expiry protection covers every old gate. The first restored batch
extends B before expiry. In the boundary case r=j+k, the next HEAD is
at e₀ and the restored gate is at e₀+Δ; renewal before that HEAD is
not assumed.

Induct jointly over events, honest source history, and scheduled HEADs.
A first restored regression gives a justified entry above B. Its
carrier reaches every honest reader by acceptance relay before the next
HEAD, and protects later frame reads even after the contest ends.
The full active-store gate count excludes a conflicting result. An old
saved confirmation can affect renewal but cannot write a conflicting
lock: new writes use prefixes of the current passed result. Source
history preserves compatibility of accepted finality. Both public
outputs equal S, so the event invariant gives the inclusive conclusion.
The proof applies to sleeping receivers and includes horizon deliveries.

**Old-budget erratum.** The old b₁−b₀≤min(η,L) is insufficient for
continuation after b₁. The Lean counterexample is on
`fgsa-outage-cex` at `583cee0`. The reserve draft gives a boundary run
with Δ=1, L=7, b₀=17, b₁=22: the outage length is 5, but (V) has
left side 5+3=8. One integer time unit beyond (V) loses B in that run.
The old interval-only P1 theorem does not assert retention after b₁.

**Sources:** [output proof, §§1,10](../spec/drafts/outage-output-direct.md)
and [timing and counterexample](../spec/drafts/outage-persist-reserve.md).
The earlier reserve draft's general-frame gap is closed by the later
output proof; frozen HEAD coverage is not the output conclusion.
**Lean:** `OutageContinuationClaim`, proved in Lean, landing pending,
on branch `fgsa-outage-v`. This is a companion to the frozen interval
claim. Its statement omits `FinalitySlashableBound`.

## 19. Corruption growth — WeakContinuationGrowthClaim

**Source and witness order.** Keep §1.1's strong healing prefix with
source faulty count at most floor((n−1)/3), full participation through
T_F=GST+B_H^F, and δ_t=2R. Choose u,Q,iSource once on the source,
before the continuation. The selected cut remains d_u<T_F. Corruption
growth starts after T_F, not after the earlier selected healing gate.

**Continuation premises.** Replace equal honest sets and global event
agreement by a retained honest set and per-validator agreement:

1. ρ.honest⊆source.honest. GST, parameters, and the complete FG, HEAD,
   and proposer seat maps agree. The continuation satisfies Base₂ and
   covers T_F.
2. For every retained validator v, inputs and awake values agree for
   t≤T_F. The ordered local event lists through the inclusive endpoint
   agree, with exact signed objects and receipt order:

   ```text
   filter(e.node=v ∧ e.time≤T_F, ρ.events)
     = filter(e.node=v ∧ e.time≤T_F, source.events).
   ```

   Equality of only S or the final store is insufficient. Named bodies,
   rows, votes, stamps, equivocation data, locks, fast writes, and saved
   confirmations are replayed through their actual local events.
3. Full-run `PartialSynchronyBy` with acceptance relay holds, with
   Δ_F≥Δ. Pending source emissions and acceptances keep their original
   deadlines; receiver exclusion is tested at the processed state.
   A change of honest set does not restart those network duties at T_F.
4. Put a=|faulty ρ|. Require 2a<n at handover and a<h_t for
   T_F<t≤ρ.horizon. Thus a≤floor((n−1)/2). The handover bound also
   covers an empty suffix; it cannot be inferred from participation
   quantified over an empty interval. Retained validators are fully
   awake before T_F by source participation and local replay.
5. Keep `FinalitySlashableBound` for the continuation. It excludes
   slashable weight at least 2q_F−n between each pair of relevant
   `FinalityBlock` carrier chains. It includes historical rows disclosed
   after T_F. It permits evidence below the threshold and requires no
   completed slashing transaction. It does not impose the source's
   one-third cap on the continuation.

**Conclusion.** For each continuation set
iρ=afterTicksIdx ρ (gateTime u). Keep the source index only in the
source's `BoundedHealingCut₂`. The same u,Q give
`WeakContinuationLiveAt₂` at iρ: available-output compatibility and
local monotonicity, seed Q, `finalBelow`, persistent proposal inclusion
from s≥u+2 by t_s+6Δ, and §17's joint growth for every admissible
continuation gap G'. All conclusions concern retained honest validators.
The growth deadline t+G'+6Δ must be within the horizon. Local replay
does not imply equality of global event indices.

**Proof sketch.** Replay the retained validators' finite prefix and
transfer their healing seed. The half bound and awake honest majority
give FaultQ, since a<q_F, for honest certificate origins and HEAD counts.
They do not give FaultX. Replace the low-historical-finalization
intersection argument by `KitFG.finalized_preceq_of_no_evidence`, using
`FinalitySlashableBound` against the healing carrier. Then run the
seeded induction, proposal service, and conditional growth proof with
iρ. No suffix invariant is added as a premise.

**Scope.** The slashing premise is required by this proof. Its logical
necessity for the full bounded-source theorem remains open; the attack
sketch is not a checked full-run refutation. Weak participation alone
does not force a new FG quorum, so this adds no finality liveness.
The retained-set model does not give a time-indexed guarantee through
each validator's individual corruption time.

**Sources:** [corruption-growth design, §§2.2–5](../spec/drafts/wc-corruption-growth.md)
and [slashing study](../spec/drafts/wc-slashing-necessity.md).
**Lean:** `WeakContinuationGrowthClaim`, proved in Lean on branch
`wc-growth`, landing pending a non-vacuity witness. This branch status
is later than the design drafts' unproved status. The existing
`FGSAClaims.weakContinuationLive` field keeps its fixed-honesty statement.

## 20. P3 producer and dependency errata

Use the source-frame definitions and explicit premises in chapter 22
§2.2. The [collected P3 errata](../codex/scratch/p3-errata-2026-10-01.md)
also correct the following producer dependencies. These are corrections
to the old P3 plan, not changes to the protocol or new run assumptions.

- F1b.1 includes both a store wrapper and the run's active-batch part.
  `sExtends_upTo` keeps the `FGFoundation` and `SrcFrameAboveStmt`
  premises. F2.4 proves the state steps relative to `CleanActionStep`;
  F2.6 discharges the action premise. The order is F2.4 then F2.6.
- `bp.cleanTransfer.v1` uses the public `cleanTransfer` statement in
  `Clean/Transfer`. The b₀ split is in `Proofs/Assembly/Clean.lean`;
  the old plan's `Assembly/CleanCut` file does not exist.
- F1b.6 row service belongs in `Proofs/Foundations/RowService.lean`.
  `RowServiceBaseClaim` supplies `RowServiceClaim` through
  `rowService_of_base`. Shared does not import Foundations.
  `fgsa_store_cumulative` and its helpers belong in `Shared/StoreRun`.
  FG-SA proofs may import Generic `Proofs.*`.
- F1b.5 precedes F1b.8 because `KeepExact` uses `HeadGeometry`.
  G06 uses the k-fold `chainSearch` with its range guard at each
  application. G04's usable HEAD threshold is v_b≥w+3Δ for the
  proposal at w+2Δ.
- F1b.4b's G25 incidence and G11 reflection producers require endpoint
  geometry and the comparison-prefix facts, as stated in 22 §2.2.
  `Proofs/Shared/GateReceipt.lean` supplies the regime-independent
  gate receipt from `LabelSync` and that geometry bundle before the
  `ExactService` gate clauses are discharged.
- G11-EXT supplies retained ancestry from each actual live root, both
  start orders, reflection and persistence, below-band eligibility,
  candidate-local score transport, admission, the unique eligible child,
  and the stop condition. Its reader wrapper supplies
  `fgsa_headVote_exact_of_covered_parent`. A bare anchor disjunction or
  a global start≤D premise does not supply these facts.

The genesis correction, exact named row premise, and universal contest
witness conclusion come from [P3 r3.5.7](../codex/jobs/p3-r357-errata.md).
These dependencies apply to the retained continuation proof as well as
to the original Clean and outage proofs.

[spec]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex
[paper]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/wc-paper-proof.md:1
[astra]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/wc-proof-review.md:1
[opus]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/wc-proof-review-opus-full.md:1
[wc-premises]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/WeakContinuation.lean:23
[wc-claim]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Claims/WeakContinuation.lean:13
[wc-cut]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/WeakContinuation.lean:83
[wc-safe]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/WeakContinuation.lean:105
[wc-regimes]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/Regimes.lean:64
[wc-base]: /Users/francesco/ethereum/lean/available-chain/AvailableChainFGSAClaims/Statements/Regimes.lean:18
[recovery-core]: /Users/francesco/ethereum/lean/available-chain/AvailableChainGeneric/Statements/V2/Regimes.lean:76
<!-- links checked against available-chain 19acc98 (2026-10-05) -->
[dc-claims]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Claims.lean:27
[dc-regimes]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Regimes.lean:28
[dc-inclusion]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Properties.lean:112
[dc-prepared]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Execution/HandoverPreparedV4.lean:16
[dc-window]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Execution/RecoveryWindowClosure.lean:16
[h-time]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3441
[h-cut]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3262
[h12]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:2721
[h14]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:2903
[h16]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3015
[h17]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3037
[h2a]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3382
[h3]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:3395
[if123]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/21-healing.md:409
[i5]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/22-finality.md:633
[source-discipline]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/01-foundations.md:919
[nesting]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/01-foundations.md:774
[before-gate]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/01-foundations.md:764
[strict-relay]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/01-foundations.md:1071
[clean-count]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:74
[same-label]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:108
[plateau]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:171
[suffix-walk]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:296
[clean-transfer]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:331
[clean-induction]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:456
[clean-safety]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/02-clean.md:674
[proposal-pivot]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/03-p1-inclusion.md:229
[score-suffix]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/03-p1-inclusion.md:277
[exact-proposal]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/03-p1-inclusion.md:361
[inclusion]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/blueprint/03-p1-inclusion.md:433
[spec-tick]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-de183d7d.tex:857
[spec-source]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-de183d7d.tex:839
[spec-gate]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-de183d7d.tex:928
[spec-frame]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-de183d7d.tex:789
[spec-client]: /Users/francesco/ethereum/research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-de183d7d.tex:1549
