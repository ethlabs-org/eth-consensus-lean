# FG-SA blueprint: outline and fixed statements

_Date: 2026-10-01. Window registry and slow-row consistency pass._

## 0. Authority, scope, and status

This is the entry point for the canonical proof document. Rule authority:
[current spec a926aae5](../spec/fgsa-protocol.tex), SHA-256
`a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.
The current spec includes ROOT-DIGEST-2 and the bounded finality window;
entry rule pin 031a7f9f remains historical.

Historical spec line citations use the 4e85ff34 numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the earlier spec c1ea1db0 changed only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.
The current model uses C1, R6-window, and the bounded finality window.
Earlier citations name their archive. Negative executions keep their old-fold
evidence; §3.5 names the checked window cases and the refuted N2.

The r210 rule starts the genuine-result walk at F with the final test.
The paired executions of bp.genuineFromF.v1 have equal external traces.
Historical absolute spec line citations retain their historical archive
basis; they are not line numbers of this revision. The r197 proof
update changes the healing bounds, not the rules.

[01-foundations.md](01-foundations.md) gives the foundations.
[02-clean.md](02-clean.md) contains the old-fold Clean safety proof; its window port is pending.
[03-p1-inclusion.md](03-p1-inclusion.md) contains the old-fold inclusion and P1 proofs; window ports are pending.
[21-healing.md](21-healing.md) proves recovery and the common interface.
[22-finality.md](22-finality.md) proves finality from that interface.
[23-continuation.md](23-continuation.md) proves sleepy safety and inclusion after recovery.
Stage 2a below includes 03's inclusive reads, pending-gate boundary,
truncation lemma, and two negative statements.

Current chapter SHA-256 prefixes (full hashes in codex/reports/bp-window-fix-full.md):
`01-foundations: 7a160200`; `02-clean: 7ff9bc70`; `03-p1-inclusion: abdc5e3e`; `21-healing: eaef7cfe`; `22-finality: 8b7eaffe`; `23-continuation: 7332c7a0`.

Status in this document has these meanings:

- PROVED-paper: a complete paper proof is given here, with explicit reuse.
- SKETCH: the stated proof is incomplete; the stronger-gap QF route has this status.
- PORT PENDING: an old-fold proof is retained; it is not window evidence.
- OPEN: this blueprint gives neither a proof nor a refutation.

QF2/QF4 are dropped open extensions, outside the claim set (user, 2026-10-01).
Finality liveness is FF5–FF7 under Rec_FE_W or Rec_F4_W, with
FGoodE_W/FGood4_W/Tail_W kernels.

No status asserts a checked composed FG-SA Lean theorem. A negative is an
existence statement and can have status PROVED-paper. NEW marks a proposed
id, not a change to the external registry.

External registry ids keep their pinned statements. The blueprint
restatements do not edit the registry. In particular:

1. comp.outputNesting.v1 is the old accessor statement. The stronger stored
   old-fold statement is comp.outputNesting.v2; the window version is v3.
2. fj.frame.v3 is WITHDRAWN for current use (2026-09-29); successor
   fj.frame.v4. Its bd942ca0 pins stay historical. The v4 statement
   uses 4e85ff34, forbids deletion by protocol rules, and starts the
   SA walk at F.
3. fj.armedSafe.v1 combines Clean, service and P1 for the old fold.
   The window target fj.armedSafe.v2 has the pending 02/03 ports below.
4. ap.headReachesLo.v5 has an explicit anchor premise. It does not state that
   every HEAD has height at least lo.
5. NJ ids, including comp.clean.v1 and comp.healedUnif.v1, are not silently
   changed to FJ statements.
6. The 2026-09-29 r212 restatements add fj.descent.v2,
   fj.twoChanges.core.v2, and ap.headReachesLo.v6. The old FJ v1
   forms and head-service v5 are all WITHDRAWN for current use.
   The v5 statement stays true in its stated scope; v6 changes hypotheses.
   FG-COMPOSITION
   needs a separate registry edit. Section 3.4 gives the statements
   and proof locations.

**Window version policy (2026-10-01).** Each changed current statement or
protocol/receipt hypothesis gets a new version below. Its preceding version
stays in [the entry archive](archive/00-outline-acba299d.md), with its old
evidence and scope; it is WITHDRAWN for current window use. No external
registry, Lean pin, or evidence is changed. Old concrete Lean declarations
are proof patterns only. The Height, Chain-certificate, and Store/safety
interfaces require separate window suppliers; HEIGHT BRIDGE is not a
whole-run transfer. Clean/P1 suppliers remain pending in 02/03.

The claims marked **RESTATE (no-round)** require new Lean statements or
wire/handler premises. The marker does not rename or edit a pinned claim.
For carrier, store and receiptCoverage, the conclusion is unchanged;
the row representation and R6/R7 handler premises change. SourceDiscipline
now has a nonempty height pair on every sent row. The finality claims
historically used FGoodE/Rec_FE, Rec_sT or Rec_skipT. Current claims use
the W predicates below. FL-T7 remains an old-fold proof, PORT PENDING.

## 1. Sources and declaration conventions

AC = /Users/francesco/ethereum/lean/available-chain.
DC = /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus.
G, SA, FG, and KFG abbreviate the namespaces AvailableChain.GridCO,
AvailableChain.SA, AvailableChain.SimplexFG, and AvailableChain.KitFG.

The retained foundation source check was at AC `3eb1889cd7e231d33e7edb96762b0ebd641825cb`
and DC `b241081d344555797205f8718eeb23a8a0e3eb4c`. AC includes the
`b5f0d328` revision identified during review; the earlier `bc3b5bf1`
pin predates that audit. The historical AC snapshot was ab6e51a; no new
Lean certificate is asserted. No Lean source is changed or built in this pass.
Unqualified declarations in a reuse list inherit its stated namespace:
GridCO files use G, SA files use SA, KitFG files use KFG, and
SimplexFG files use FG. DC's namespace prefix is
`DecoupledConsensusModel`, not an abbreviation for an arbitrary module.

The seven chapters state their proof arguments in full. The frozen spec
is the rule authority. Lean declarations are reuse or comparison points;
they are not a checked mixed FG-SA execution theorem. The DC comparison
paper is [consensus.tex](/Users/francesco/ethereum/research/healing/rewrite/consensus.tex).
Its grade layer and NJ rule are not protocol premises here. Registry ids
identify related statements; the explicit statements in this outline
control their use in this blueprint. No historical report is required.

## 2. Model

### 2.1 Objects, runs, and notation

Fix integers n≥1, Δ_F≥Δ>0, k≥2, K_W≥2, R≥2, δ_t≥0.
Put κ=ceil((6Δ+Δ_F)/(4Δ)), β=β_F=4κΔ, ε=β−8Δ.
Recovery and the aligned window kernels require R≥max(2,κ), δ_t=2R.
Safety retains every δ_t≥0; block variables K and W keep their meanings.
Set τ=⌈n/2⌉, q_F=⌈2n/3⌉, f=⌊(n−1)/3⌋, L=(4k−1)Δ,
and P=4RΔ. Faulty identities form a static set of size a.
Each slot has a fresh hidden bijection between its n seats and fixed
identities. FG uses the full fixed validator set and one fixed
seat-to-validator map. Only the FG client reads the fixed identity.
An FG row is `(valindex,h,T,χ,h_f,T_f)`, signed by that fixed identity,
with no round. Its height pair has h≥1 and T≠⊥; a nonempty finality pair
requires h>h_f. The client and ingress check enforce this form. The action stays scheduled per round. No finality-only
row exists.

A full named proposal contains its full named parent, slot, root, application content, ordered
signed FG rows, ordered raw HEAD list, and ordered support list. HEAD targets are root identifiers.
The fixed digest takes parent root, slot, app, signed rows, raw HEADs, and support HEADs in that order.
List order and duplicates are part of content. Write g for genesis and use named ancestry on full
proposals; the Block and FGBlock projections supply proof geometry. Base includes collision freedom
on directly delivered full proposals and honest prefix-held full proposals, with named ancestor
closure. Equal roots in that scope imply equality of the entire recursive proposal. HEAD-only names
and emitted-only tips are not extra seeds. Keep the other Base conditions and proof horizon.
No statement about arbitrary fabricated local state is inferred from Base.

A trace is a finite causally ordered list of local tick and delivery events.
A public read at integer time t includes all events with time ≤t in trace
order, as in AC AvailableChainModel/Generic/Run.lean:130 (Run.readAt).
Thus S_y(t), F_y(t), and leases include every local tick and delivery
through t. A cut between same-time events is a proof cut, not that public
read. Duty and gate inputs use their actual local execution positions,
before later same-time deliveries. Write F_y^HEAD(s) for the label-s
HEAD input. Recovery also uses the explicit post-gate event cuts in §2.5
and quantifies over later completed-event reads. No read is inside a handler.
“Every node” means every store that follows the specified transitions;
a Byzantine process can print an arbitrary output.
Asleep honest nodes run ticks and handlers but emit no duty objects.

### 2.2 Store and handlers

Σ=(t,s,T,timestamp,σ,gf_votes,attestations,genuine,lease,fastWrite,S,F,J,j,H).
T is cumulative admitted storage. Old σ values and first stamps are
immutable. Λ=(target,timeout,lock,timeouts,sent) is separate and persistent.
The sent set records full row contents before release. At each action,
recompute finality_pair from that action's head; use it as the current
action lock in height_pair. Send no row if the height pair is empty.
If that height was already sent, only a timeout whose entry differs from
every row already sent at that height can be sent. Strip the finality pair if h≤h_f. Send only content absent
from sent, and record before release. No pending-pair field is used.
The pre-GST delivery clause below makes resending unnecessary.
Initially T={g},F=J=S=g,j=0,H=1, with empty pools and SA maps.
The genesis chain state has h=1 and h_j=h_F=0, with 𝒲=[].
Each immutable state keeps latest J separately from the ordered window
𝒲=[(j_i,X_i,Q_i)], of at most K_W entries, with identity-bit sets Q_i.
Its keys satisfy h_F<j_0<…<j_m≤h_j<h. Target/progress bits are separate.

A(Σ)={B∈T:B∥F}. For any block set X, define
D_Σ(X)={B∈X:F⪯B ∧ Z⪯B ∧ ∃W∈X,B⪯W ∧ ht(W)≥lo}.
The live frame is:

- contest iff H=j+1 and some W∈T has ht(W)=H and J⋠W;
- (Z,lo)=(J,H−1) when H=j+1 and not contest;
- (Z,lo)=(F,H) in a contest;
- (Z,lo)=(F,H−1) otherwise.

Finality acceptance uses the separate viability floor H−1, also in a contest.

A new block B is refused before computation or unpacking if it is future,
duplicate, lacks an admitted parent, fails F⪯B, has a non-increasing
parent slot, lacks the proposer signature, or fails R6-window. Every row
uses the same parent post-state with σ.s:=B.slot. HeightMatch means
(a.h,a.T)=(σ.h,σ.T_h). StaleUseful means a nonempty height pair with
a.h_f<a.h<σ.h and an exact finality-pair match in parent 𝒲.
R6-window is HeightMatch or StaleUseful; field/authentication checks remain.
Only HeightMatch sets height bits. Either arm can set its exact window bit.
R7 selects eligible rows from pools and admitted blocks, removes exact
duplicates and exact rows on the parent chain.
The order of the remaining rows is not specified; every guarantee reads the selected rows as a set (the Lean model keeps arrival order).
Optional omission must preserve every candidate effect in parent bits or
the final selected set; at most 1+K_W rows per identity suffice (01 §1.1).
It does not prune pools. No one-row-per-identity reduction is allowed.
On success: derive σ[B] from the parent and full rows; insert and stamp B;
call base-vote handlers; update H, then J, then possibly F; immediately
reconcile after an F move; call row handlers. The chain fold uses full rows
even when the inclusion pool refuses them. Fold bits against the fixed
parent window; select the greatest ready entry above h_F and delete entries
through that height. Then consume target justification, otherwise mature
progress. Justification appends an empty entry and keeps the newest K_W;
mixed progress adds none. Height advance clears only height bits. No row
is reapplied to a new entry. One block raises height at most once and sets
the new height entry to that block. Capacity eviction gives no F coverage.

Reconcile removes incompatible leases and members of every fastWrite set,
empties incompatible saved genuine results but keeps their evaluated labels,
and assigns S:=F if F⋠S. It writes no T, σ, stamp, pool, Λ, F,J,j,H.
It never replaces a saved result by F.

A gate saves its genuine result once, also if empty or vetoed. The guard
tests every live lease. A passing result advances S and writes admissible
non-genesis prefixes. A fast renewal enters fastWrite even if max leaves the
deadline unchanged. A slow-only renewal does not. The gate normalizes S last.

### 2.3 Event order and receipt

t_s=4Δs, v_s=t_s+Δ, e_s=t_s+2Δ, z_s=t_s+3Δ,
q_s=t_s+5Δ=v_(s+1), d_s=t_s+6Δ=e_(s+1).
The FG action is a_r=t_(rR)+6Δ=d_(rR).

```text
┌───────────┬────────────────────────────────────────────────────────┐
│ Event     │ Local order                                            │
├───────────┼────────────────────────────────────────────────────────┤
│ Each tick │ Set time and slot; expire deadlines ≤ time.            │
│ t_s       │ Then proposal if s>0 and proposer is awake.            │
│ t_s+Δ     │ Release s−1 first if s>0; then HEAD if awake.          │
│ t_s+2Δ    │ Gate s−1 first if s>0; then FG action if awake at a_r. │
│ t_s+3Δ    │ Clock; this is the strict freeze cutoff for label s.   │
│ Delivery  │ Handler order above; F can move at any delivery time.  │
└───────────┴────────────────────────────────────────────────────────┘
```

Each local tick precedes local deliveries at the same time. A handler or tick
is atomic relative to external events. Base self blocks and votes are
processed on delivery. The own FG row is recorded before emission, emitted,
then processed in the action tick. No event intervenes between the gate and
action, or between F:=F' and reconcile.

All cutoffs are strict. Stamps are the last public tick, not arrival times.
For a public cutoff c, stamp<c means receipt before c. An admitted block
causes real carried-object handler calls; a refused block causes none.
The base pool admits current/previous-slot votes and at most two distinct
votes per seat. The row pool stores one copy per checked full content,
without an age test, clock expiry, or per-identity quota.

C1 applies to Clean (GST=0) and Recovery₂. P1 keeps its own healthy
prefix and outage premises. An honest send at t arrives strictly before
max(t,GST)+Δ for a block, complete body, or SA vote, and before
max(t,GST)+Δ_F for a standalone FG row. An honest acceptance creates
the corresponding relay duty from its acceptance time. Dependencies
are present; pre-GST objects and sleeping receivers are included.
Only blocks have the deadline-state F exclusion. A carried row arrives
with its complete block under Δ. Handler order stays unchanged.

### 2.4 Tree-read inventory

```text
┌───────────────────────────┬───────────────────────────────────────────────┐
│ Consumer                  │ Exact read                                    │
├───────────────────────────┼───────────────────────────────────────────────┤
│ Confirmation / gate       │ A(Σ), walk from F, no FJ band.                │
│ Release / resolution      │ Active heads, original stamps, signed pool.   │
│ Late count / equivocation │ Signed votes; no active-head requirement.     │
│ H / contest / frame       │ Cumulative T and live caches.                 │
│ V_s block view            │ Pre-z_(s−1) blocks plus admitted current      │
│                           │ proposal paths; witnesses inside this view.   │
│ HEAD raw merge            │ Frozen votes plus all current proposals in T. │
│ Frozen support            │ Active resolution before z_(s−1).             │
│ Carried support           │ Original declaration; head in T, valid slot.  │
│ Proposal / finality head  │ Full D_Σ(T), active resolved support.         │
│ live_root                 │ Deepest live lease in D_Σ(T), else Z.         │
│ C_fg at a_r               │ Deepest live fastWrite[rR] member in D_Σ(T).  │
│ Row inclusion             │ Pools plus original rows of blocks in T.      │
│ Chain finality test       │ Parent 𝒲, exact Q_i bits; greatest ready.     │
│ Leak Qfin                 │ Latest pair’s retained Q_i, or ∅.             │
└───────────────────────────┴───────────────────────────────────────────────┘
```

An excluded support head contributes zero to a candidate above F.
This fact does not permit deletion of its proposal container.
A HEAD can start outside its walked domain and return that start.
There is no extra F-carrier path, frozen-domain anchor, or unfiltered fallback.

### 2.5 Regimes and later-stage constants

Clean = Base + GST=0 + C1 emission/receipt delivery from genesis +
a<h_t≤n−a at every time. No a≤f or h_t≥τ is added.
At v_s let h_s be the honest awake count. A late label-s pool has all h_s
honest seats and at most a other seats.

Outage(A_lag) = Base + healthy delivery from genesis to b₀ +
a<h_t≤n−a there + the SA η-sleepy inequality
2|H_t|>|(∪_(u∈[t−η,t])H_u)∪Faulty| for t<b₀ +
0≤T≤b₀≤b₁, T+A_lag≤b₀, b₁−b₀≤min(η,L).
Delivery is arbitrary on [b₀,b₁). Outage (P1) does not assume the pre-GST delivery clause
and puts no bound on GST. Its healthy-prefix delivery uses Δ for blocks/HEADs
and Δ_F for standalone rows, with each required interval inside the horizon;
outage delivery is arbitrary. The concrete 02/03 proof ports are pending. Fast uses A_lag=4Δ and h_t≥τ
through the whole healthy prefix. Slow uses A_lag=L−3Δ.
Retain the complete window and horizon premises of AC OutageRegime and
FastOutageRegime. This is not a healthy interval after arbitrary damage.

Recovery₂ = Base + a≤f + arbitrary pre-GST history + all honest awake
after GST + C1 + K_W≥2 + R≥max(2,κ), δ_t=2R.
For each t≥GST an honest proposal has t<t_s≤t+G, with the guarded
finite horizon and finite G≥4Δ. Every used gap search and receipt interval must fit.
κ=ceil((6Δ+Δ_F)/(4Δ)); K_W is the finality-window capacity.
No opening recurrence is required.

Put `T_q=qP`. Round `r≥1` is **qualified** when the slot proposers
`rR,rR+1,rR+2` are honest. It is **strong** when, in addition, `r≥2`
and the opening proposers `(r−2)R,(r−1)R` are honest. All quantifiers
require the stated window in the proof horizon.

- `Rec_s(g)`: for every integer round `q≥1` with `T_q≥GST`, a
  qualified round lies in `{q,…,q+g−1}`. Require `g≥1`. The optional
  qualified-round healing bound uses this premise; the dropped open
  extension 22 QF2 also requires Tail witnesses, as Rec_sT below.
- `StrongRec_w(g)`: for every such `q`, a strong round `r`
  satisfies `T_q+2P≤T_r≤T_q+gP`. Require `g≥3`, so the window
  contains at least two possible central openings. The three openings
  lie within `{q,…,q+g}`, a window of `g+1` rounds.
  `StrongPair` means that, for every such `q`, one of rounds
  `q+2,q+3` is strong. Thus `StrongRec_w(3)=StrongPair`.
- `Lit(g)`: for every such `q`, a strong round has all three
  openings `r−2,r−1,r` in `{q,…,q+g−1}`; equivalently,
  `T_q+2P≤T_r≤T_q+(g−1)P`. Require `g≥3`. This states the
  earlier 2e884811 spec's literal “three consecutive honest openings …
  within every g rounds” premise (archive lines 1467–1470), with the whole triple in that window.
- `Rec_c(g)`: for every integer time `t≥max(GST,1)`, a strong round
  satisfies `t+2P≤T_r≤t+gP`. Require `g≥3`. On infinite runs this is
  `DecoupledConsensusModel.Statements.Generic.StrongMultiProposerRecurrence`
  in [Conditions.lean:232](/Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusStatements/Generic/Conditions.lean:232),
  with period `P`, start `max(GST,1)`, and three slot proposers (on a finite run, it implies Rec_c).

Healing requires only the strict honest-proposal gap `G`. It requires
no opening recurrence. For the optional qualified-round proof, use
`g_h`: `Rec_s(g_h)` supplies an opening within `(g_h−1)P` of an
aligned search; that proof budgets `g_h P`. `Rec_c(g_h)` also supplies
this search but need not imply `Rec_s(g_h)`. `Lit(g_h)` implies it.

For Δ_F≤2Δ, the old predicates below are the κ=2 instances of the
window predicates. Equality of predicates is not equality of transitions.
For finality at `δ_t=2R`, define the forward predicates

```text
FGood(r)  := Honest(rR) ∧ Honest((r+1)R) ∧ Honest((r+2)R+2).
FGood4(r) := FGood(r) ∧ Honest((r+1)R+2).
FGoodE(r) := FGood(r) ∧ ∃s∈[(r+1)R+2,(r+2)R], Honest(s).
Rec_F(g)  := ∀q≥1 with T_q≥GST, ∃r∈[q,q+g−1], FGood(r).
Rec_F4(g) := ∀q≥1 with T_q≥GST, ∃r∈[q,q+g−1], FGood4(r).
Rec_FE(g) := ∀q≥1 with T_q≥GST, ∃r∈[q,q+g−1], FGoodE(r).
```

Here `g≥1`, `Honest(s)` means that `s>0` and slot `s` has an honest proposer,
and the horizon contains the complete window and its final carrier.
Use `Rec_FE(g_f)`, or its special case `Rec_F4(g_f)`, for any finite `G≥4Δ`.
FGood4 implies FGoodE; they coincide at R=2. Include the receipt interval
in the horizon. The old FGood case c=z+1 is WITHDRAWN (no-round):
a source can lag the head and cannot carry finality at the same height.

Tail(r) means Honest(rR), an honest s∈[rR+2,(r+1)R], and
Honest((r+1)R+2). Rec_sT(g) requires Rec_s(g) and a Tail witness in
every [q,q+g−1]; the witnesses can differ. Rec_skipT(g) requires one
Skip(p)∧Tail(p+3) witness in that window, where
Skip(p)=Honest(pR)∧Honest((p+2)R+2). Use the same start conventions;
Rec_skipT includes slot (p+4)R+2 and receipt in its horizon.
Rec_sT and Rec_skipT are used only by the dropped QF2/QF4 extensions,
which are outside the claim set (user, 2026-10-01).

For all aligned row delays, use the receipt-ready predicates (22 §1):

```text
FGoodE_W(p) := Honest(pR) ∧ Honest((p+1)R)
  ∧ (∃c∈[(p+1)R+κ,(p+2)R], Honest(c)) ∧ Honest((p+2)R+κ).
FGood4_W(p) := FGoodE_W(p) ∧ Honest((p+1)R+κ).
Tail_W(r) := Honest(rR) ∧ (∃c∈[rR+κ,(r+1)R], Honest(c))
  ∧ Honest((r+1)R+κ).
Qual_W(p) := Honest(pR) ∧ Honest(pR+1) ∧ Honest(pR+κ).
Skip_W(p) := Honest(pR) ∧ Honest((p+2)R+κ).
Rec_FE_W(g) / Rec_F4_W(g): the respective witness in every [q,q+g−1].
Rec_sT_W(g): a Qual_W witness and a Tail_W witness in each interval;
            the witnesses can differ.
Rec_skipT_W(g): a Skip_W(p) ∧ Tail_W(p+3) witness in each interval.
Rec_sT_W and Rec_skipT_W: dropped open extensions, outside the claim set.
```

Require g≥1 and the full search and receipt horizon. Local FGoodE_W,
FGood4_W, Tail_W and FF5–FF7 are PROVED-paper in 22. QF2/QF4 are
OPEN extensions, outside the claim set (user, 2026-10-01). The κ=2
QF2-W text is a sketch; it is not reviewed and no claim uses it. With an actual strict Recovery gap throughout
the horizon, β+Γ−4Δ≤P and R>κ, the stronger-gap route is a SKETCH:
trigger anchors, faulty-middle H6 sources, and both horizons remain open.
Strong alternatives, HP, leak fairness, and FL-W/RF/D/T7 keep old-fold
proofs only until their window ports are complete.

At `R=2`, the final carrier is the opening of round `r+3`.
StrongRec_w, Lit, and Rec_c remain alternative finality premises.
The general-delay results FL-W, FL-RF, FL-D, and FL-T7 keep their
strong windows; the FGoodE proof here uses `δ_t=2R`.

For a finality trigger `t≥max(GST,1)`, align upward to `t≤T_q<t+P`.
Under `StrongRec_w(g_f)`, the central opening is before
`t+(g_f+1)P`; under `Lit(g_f)`, it is before `t+g_f P`.
In both cases its first opening is at least `t`. Under `Rec_c(g_f)`,
the central opening is at most `t+g_f P` without alignment.
Thus `γ(g_f)=g_f+1` for `StrongRec_w`, and `γ(g_f)=g_f` for
`Lit` or `Rec_c`. Also `Lit(g)` implies `StrongRec_w(g)`;
the converse need not hold. In the optional qualified-search proofs write `g=g_h`;
in the local finality proofs write `g=g_f`.

The `g=3` values are the optimistic end. Under `Lit(3)`, each
`q≥max(1,ceil(GST/P))` forces `r=q+2`, so every round from
`max(3,ceil(GST/P)+2)` is strong. Under `Rec_c(3)`, put
`q₀=max(0,ceil((GST−1)/P))`. For `q≥q₀`, the trigger `T_q+1`
leaves only `T_(q+3)` in its window, so every round from `q₀+3`
is strong. At `R=2,3`, the three qualified slot proposers cover
every slot of that round. Both premises therefore force all slot
proposers honest from about `GST+3P`; these are degenerate cases.

`StrongPair` permits faulty slot proposers. For an integer example,
take `Δ=1,R=3,P=12,GST=0`. Let every opening proposer be honest,
the slot-`(3r+1)` proposer be faulty in each odd round `r`, and
all other slot proposers be honest. Exactly the even rounds `r≥4`
are strong. Every pair `q+2,q+3` contains one, so `StrongPair`
holds; `Rec_s(3)` and `G=8Δ` hold too. But `Lit(3)` at `q=1`
requires the non-strong round 3, and `Rec_c(3)` at `t=1` has
window `[25,37]`, whose sole opening is `T_3=36`.
The same pattern satisfies `Rec_c(4)`: every interval
`[t+24,t+48]` contains an even-round opening. At `R=2`, the
corresponding pattern with faulty slot `2r+1` in odd rounds also
works; the third slot of an even qualified round is the next honest
opening. Each extra unit of `g_h` adds `13P` to the optional old bound.

r_G is the first action round at/after GST; u₀=a_(r_G+2), including
all events at that time. M=max_x H_x(u₀) over honest x. The first action
round that emits an honest row at M+1 is r*; s*=r*R; b=s*. Select one fresh source
C* of such a row. High means height at least M+1. A settled phase fixes
the global honest frontier m, top justification at m−1 if present,
and contest status after the evidence settles. Local H can lag during
settlement. A rise, first top justification, or first contest ends it;
lower F moves do not. H.6 uses the separate repair label β. H.6-S
uses a local first-HEAD label b, distinct from the reset label b=s*.

HEALED(t) uses the post-gate cut of 21 §2: a gate boundary is after all
honest gate ticks, excluding partial tick batches, and includes later
receipt states. It gives compatible honest outputs, monotone local S,
local F⪯S, and 6Δ honest-proposal inclusion. The finality interface is
HEALING_INPUT(t*) of 21 H.22, copied verbatim in 22 §1; it also contains
H0–H6, including H2.A/H2′ internal support and H5/H6 gate service.
Its witness, T-stream, AC-output and FG parts share one event cut.
Output safety alone does not supply it.

The next reset terms are the Δ_F≤2Δ specialization; use F forms below otherwise.
θ=3Δ requires strict delivery <Δ; τ_t=2; Γ=4Δ ⌈G/(4Δ)⌉.
ρΓ=2L+Γ+8Δ; ρ₁=L+Γ+10Δ when H.6-S's synchronous-window premise holds.
H.6-C supplies that premise for every reset attempt when k≤2R+1.
Use r̄=ρΓ generally, or ρ₁ under that condition:
E_g=r̄+2P+Γ−Δ; E_j=max(r̄+P+Γ+3Δ,2P+Γ−4Δ);
B_c=r̄+2P+Γ−6Δ; D_c=r̄+P−Δ.
B_reset(r̄)=3P+2E_g+2E_j+B_c+D_c; B'_reset is the minimum
of eligible bounds. HG.1 preserves service through same-frontier events
once a served proposal reaches that frontier. HG.2 uses the entry slot.
HG.3–HG.6 give the shorter search and retain both max branches.
For optional qualified search retain θ_Q=4Δ, ρ=2L+G+8Δ,
A_d=ρ+[1+(d+1)g_h+2d]P+10Δ and
B_reset=6ρ+(23+13g_h)P+60Δ. The old δ_H=2L+G−2Δ stays valid.

For Δ_F≤2Δ, the old bound formulas are below. Healing and forward
Rec_FE/Rec_F4 have window proofs. B_Q and B_skip are dropped open
extensions, outside the claim set. Strong alternatives remain old-fold targets, PORT PENDING.

```text
Γ = 4Δ ⌈G/(4Δ)⌉; ρ = 2L+G+8Δ.
B_H^(2) = max(12L+12Γ+12P+49Δ, 8L+10Γ+14P+19Δ).
B_H^(1) = max(6L+12Γ+12P+61Δ, 4L+10Γ+14P+27Δ)  (requires k≤2R+1).
B_H = min({B_H^(2)} ∪ {B_H^(1) if k≤2R+1}).
W_F(g_f) = (g_f+2)P+9Δ.  (Rec_FE or Rec_F4; any finite G≥4Δ.)
B_F(g_f) = B_H+W_F(g_f).
B_heal(g_h) = 6ρ+(23+13g_h)P+G+64Δ.
B_best(g_h) = min(B_heal(g_h),B_H).
B_first,strong = B_best(g_h)+γ(g_f)P+9Δ.
γ(g_f) = g_f+1 under StrongRec_w; g_f under Lit or Rec_c.
B_Q(g) = B_best(g)+(2g+2)P+9Δ  (Rec_sT(g), G≤P; dropped open extension).
B_skip(g) = B_H+(g+4)P+9Δ     (Rec_skipT(g), G≤P; dropped open extension).
```

For all C1 delays with R≥κ, the definition copied from 21 H-time is
(β_F=β, ε=β_F−8Δ):

```text
B_H,F^(2) = max(12L+12Γ+12P+49Δ+2ε, 8L+10Γ+14P+19Δ).
B_H,F^(1) = max(6L+12Γ+12P+61Δ+2ε, 4L+10Γ+14P+27Δ)  (requires k≤2R+1).
B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
E_g^F=ρ̄+2P+Γ−Δ; E_j^F=max(ρ̄+P+Γ+3Δ+ε, 2P+Γ−4Δ).
B_c^F=ρ̄+2P+Γ−6Δ; D_c^F=ρ̄+P−Δ.
B_reset^F(ρ̄)=3P+2E_g^F+2E_j^F+B_c^F+D_c^F.
B'_reset^F = min of eligible B_reset^F(ρ̄) = B_H^F−Γ−4Δ.
B_best^F(g_h)=min(B_heal(g_h),B_H^F)  (qualified search required).
W_W(g)=(g+2)P+β+Δ; B_F^W(g)=B_H^F+W_W(g).
```

The eligible repairs are ρΓ always and ρ₁ when k≤2R+1; both bound
the same witness tuple. B_H≤B_H^F≤B_H+2ε. At k=2,G=8Δ,
R=3, 2Δ<Δ_F≤6Δ: healing 351Δ; HG.7 324Δ; HG.8a 252Δ.
W_W and B_F^W require Rec_FE_W or Rec_F4_W. Other finality families
cannot be ported by replacement of the healing term alone.

B_best requires qualified search. Without it, use B_H for healing.
With both finality premises, take the smaller local deadline. The
optional qualified healing bound remains valid; it is larger than
B_H at the reference values below for every g_h≥1. For other parameters,
take the minimum only over bounds whose premises hold.
For integer time the strict healing gate gives an upper deadline one
tick earlier. Under FF5 the two strict inequalities give a GST first-
finality deadline `B_F(g_f)−2` ticks. These savings are ticks, not Δ.

At `k=2,G=8Δ,Δ_F≤2Δ`, values below are in units of Δ. G≤P holds at both R.
The table uses the scale-uniform coefficients before those tick savings.
The last row varies G and uses the symbolic healing bound. 22 QF1 refutes
the unrestricted-gap implication for g≥4 at R=2,3. The dropped open extensions 22 QF2 and 22 QF4 retain old-fold arguments for
first non-genesis finality with a finalized entry of height at least
M+1; they do not assert FF5's conclusion for an arbitrary trigger.
Rec_skipT(g) and its old-fold argument are retained in 22 §5A, outside the claim set. Open unrestricted-gap
cases are g=3 at R=2, g∈{2,3} at R=3, and all g at R≥4 (22 N5).
The opening-deletion negatives of 22 QF3 and 22 QF5 are also OPEN at R≥4.
Each ‡ negative retains old-fold evidence; N1's window replay is pending.
The R=3 gap-only question is OPEN, and N2 is refuted for the window.
The QF2/skip rows are dropped open extensions, outside the claim set.
The strong rows are old-fold values, PORT PENDING.

```text
┌───────────────────────────┬────────────────┬─────────────────────────────────────┐
│ Additional premise        │ Heal R=2 / R=3 │ First R=2 / R=3                     │
├───────────────────────────┼────────────────┼─────────────────────────────────────┤
│ None                      │ 295 / 343      │ R=2: N1 pending; R=3: OPEN ‡        │
│ Rec_FE(3)                 │ 295 / 343      │ 344 / 412                           │
│ Rec_FE(4)                 │ 295 / 343      │ 352 / 424                           │
│ Rec_sT(3), G≤P            │ 295 / 343      │ 368 / 448; dropped extension        │
│ Rec_sT(4), G≤P            │ 295 / 343      │ 384 / 472; dropped extension        │
│ Rec_skipT(3), G≤P         │ 295 / 343      │ 360 / 436; dropped extension        │
│ Lit(3) or Rec_c(3)        │ 295 / 343      │ 328 / 388                           │
│ Rec_s(3) + StrongRec_w(3) │ 295 / 343      │ 336 / 400                           │
│ Rec_c(4)                  │ 295 / 343      │ 336 / 400                           │
│ Rec_s(g≥4), finite G      │ B_best(g)      │ No general guarantee (22 QF1, G=2P)‡│
└───────────────────────────┴────────────────┴─────────────────────────────────────┘
```

For the historical κ=2 comparison, at `δ_t=2R`, every strong round r gives FGoodE(r−2): its opening
is an early carrier. Hence `StrongRec_w(g) ⇒ Rec_FE(g−1)` and
`Lit(g) ⇒ Rec_FE(g−2)`:
the possible first rounds are respectively `[q,q+g−2]` and
`[q,q+g−3]`. These implications give the same local bound
`γ(g)P+9Δ`. Thus FF3–FF4 gives no smaller bound for these two forms.
It still gives a smaller bound for Rec_c without alignment, and remains
useful when G>P or the delay differs from 2R.

Lit(3) and Rec_c(3) force every later slot proposer honest at R=2,3,
as proved in the recurrence section. They are stronger assumptions.
The general-delay results in 22 retain their strong-window premises.

## 3. Fixed statement list

Unless stated otherwise, all claims quantify over Base traces, honest reads
and their complete proof horizons. Dependencies name lemmas, not new run
axioms. Conditional Clean lemmas are discharged by the induction in 02 §5.

### 3.1 Foundations — stage 1

**bp.channel.v2 — RESTATE (no-round) — PROVED-paper.** At an honest action a_r,
`X_r={B∈fastWrite[rR] : lease[B]>a_r}` and
`C_fg=deepest(X_r∩D(Σ.T))`, or none. Under H2, each high honest source
K of label s precedes parent(Q) for every honest proposal at v≥s+2.
Each honest proposal supplies every effect of held honest R6-window rows
by carriage, parent bits, or the final R7 selection (≤1+K_W rows/identity).
Rows use max(t,GST)+Δ_F; after a_r≥GST, eligibility permits service
from rR+κ. Height bits require HeightMatch; finality bits need the exact
retained entry or finality coverage. Eviction gives no coverage.
The joint selectors also supply FG with the finality-head triple,
including when no source exists, and the carrier parent.
Dependencies: source origins (01 §8.4), the selector and strict receipt,
H2 for source ancestry, and chain-state persistence for bits. Proof:
01 §1.1. The T-ROWS proof does not depend on H2 or H.22.

**bp.jointServices.v2 — NEW — PROVED-paper.** Under the awake,
strict-receipt and quorum premises of 01 §1.2, the live start is Z or
a live target below S at every event index (T-START). On H4's suffix,
S is locally monotone
(T-SMONO). H3 gives post-gate S=Q and opening C_fg=Q for an honest
proposal at v≥s*+2 (T-EXACT). At synchronous reads, proposal and action
pools hold all honest votes at their respective read labels; the caller
must prove head resolution (T-VOTE, a composition service). If Q is in
the full filtered domain, the live start is compatible with Q, and all
h honest heads cover Q, the full head covers Q and equals Q if no
proper descendant is admitted. With all h honest seats participating,
a selected child without an honest supporter requires the current-slot
or below-floor arm (T-WALK).
Dependencies: lease origins and live_root, H3/H4 for healed service,
AC vote duties, pool admission, receipt, and the walk count h>a with
2h>n. Proof: 01 §1.2, with the T-START induction in 22 I5. This
conditional interface does not import recovery into stage-1 proofs.

**bp.carrier.v1 — RESTATE (no-round), K5 — PROVED-paper.**
For full named proposals X,Y in the run scope, erasure is injective and reflects ancestry and
compatibility. It preserves parent, slot, and root. This uses full named collision freedom.
The separate map eraseFG from FGBlock to Block is structurally injective through the BODY codec.
Local admission proves root uniqueness of the stored FG view. Equal roots across scoped stores
identify the full named proposals, including all ancestor lists. Two-chain FG comparisons retain
their explicit RootInjectiveOn premise.
Proof: 01 §2.

**bp.chainCertificates.v2 — NEW — PROVED-paper.**
Along a block path, height is nondecreasing and rises at most once per block;
the current entry is an ancestor at that height. Comparable equal-height
states have the same entry. A crossing of m≥1 has q_F distinct matching
progress signers; a justification has q_F target signers for its entry;
a positive-height finalization selects the greatest ready window entry,
with q_F exact finality signers and its earlier birth target QC.
Pruning lower entries creates no certificate. Capacity eviction is not coverage.
Premises: Base, no synchrony.
Dependencies: bp.carrier.v1.
Lean reuse: KFG.height_advance_step, h_mono, entry_same_height,
entry_eq_on_plateau, height_crossing, justification_certificate,
finality_certificate, J_is_entry. Proof: 01 §3.

**bp.heightBridge.v1 — NEW — PROVED-paper.** On the same original block
tree, the old side is the total raw fold; an auxiliary evaluation that drops
nonmatching rows gives the same H=(h,T_h,h_j,J,target,progress,s,L).
The window fold has the same H. Induct on the path and fixed-parent
bit unions; stale rows set no height bits and finality is not read by height
events. No block is rebuilt. There is no equality of finality, admission,
reconciliation, sources, or whole runs. Proof: 01 §3.1a.
Interface split: Height uses this bridge; Chain certificates use 01 §3.1;
Store/safety use 01 §§4,8 and their window provenance. No old pin transfers.

**bp.store.v2 — RESTATE (no-round), K4 — PROVED-paper.**
At each completed local event: T is cumulative, parent-closed and contains g;
old states/stamps are unchanged; F,J∈T and F⪯J;
H=max_(B∈T)ht(B); (j,J) is the lex maximum of admitted-state
justifications extending F; some admitted carrier K has σ[K].F=F.
Local F, lex pair (j,J), and H are monotone in their respective orders.
Premises: Base and initialization.
Dependencies: bp.carrier.v1, bp.chainCertificates.v2.
Lean reuse: FG.Store/on_block/update_finality; KFG.StoreInv,
storeInv_on_block and storeControls_eq_fjControls now have source proofs.
The lift to the complete composite state is new.
Proof: 01 §4.

**bp.activeView.v2 — NEW — PROVED-paper.**
A⊆T is ancestor-closed and contains g,F. For fixed T and F⪯F',
A(T,F')⊆A(T,F). Heads above a retained B≥F are active.
A block removed for conflict never returns under descendant F moves.
View restriction changes no signed pool or stamp.
Premises: bp.store.v2.
Dependencies: bp.store.v2.
Lean reuse: FG.activeView; new ancestry proof. Proof: 01 §5.

**bp.leaseOrigins.v2 — NEW — PROVED-paper.**
Every live target has a successful gate origin and is a prefix of that
genuine result. Live targets form one chain. Each non-genesis ancestor has
a lease with at least the descendant's deadline. Each fastWrite member
has a fast-write origin at that label, but need not still have a lease.
Premises: Base, actual write origins.
Dependencies: bp.activeView.v2 geometry.
Lean reuse: G.gate_target_origin, clock_target_origin,
run_target_genuine_origin; new fastWrite/reconcile cases. Proof: 01 §6.1.

**bp.genuineFromF.v2 — NEW — PROVED-paper.**
At a gate, C_F=C_g when C_g≠⊥ and F⪯C_g, and C_F=⊥ otherwise.
Paired executions with equal external inputs have equal evaluated labels,
leases and fastWrite sets on descendants of current F, and external
traces. Only strict-ancestor saved results and writes can differ.
Every output-level theorem transfers; new H3 implies old H3 in the pair.
Premises: same initialization, ticks, awake schedule, checked inputs,
delivery order, block contents, and signing randomness.
Dependencies: bp.activeView.v2, gate rules, forward F, and choice domains.
Proof: 01 §6.5; spec sec:filtered-proofs.

**bp.reconcile.v2 — NEW, K1,K3 — PROVED-paper.**
Reconcile has exactly the writes in §2.2, preserves evaluated labels,
and is idempotent for fixed F. If all live leases, saved nonempty bodies,
and S are compatible with new F, it deletes no target or body and only
extends S. FastWrite origin witnesses imply preservation of those sets too.
Premises: reachable state and actual origins.
Dependencies: bp.activeView.v2, bp.leaseOrigins.v2.
Lean reuse: new; DC.Protocol.clipGrade/clipCache are comparisons only.
Proof: 01 §6.

**comp.outputNesting.v1 — PROVED-paper.**
For any F,S, F⪯(if F⪯S then S else F).
Premises: none beyond ancestry. Dependencies: none.
Lean reuse: new two-case proof of the registered statement. Proof: 01 §7.

**comp.outputNesting.v3 — NEW, K2 — PROVED-paper.**
At every completed local event F⪯S and both available accessors equal S,
for every a and without synchrony, including empty and vetoed gates.
Premises: Base initialized execution.
Dependencies: bp.store.v2, bp.activeView.v2, bp.reconcile.v2.
Lean reuse: new composed invariant. Proof: 01 §7.

**bp.frame.v2 — NEW, current fj.frame.v5 store clauses — PROVED-paper.**
The projection onto (T,F,J,j,H) is the window store on successful admission and
stutters on SA-only changes and refusals. Its controls and D_Σ(X) are §2.2.
Reconcile does not change them. The cumulative metadata reads in §2.4 remain.
Premises: store invariant. Dependencies: bp.store.v2, bp.reconcile.v2.
Lean reuse: FG.storeControls, filteredFrom, storeFrame are old patterns only;
window projection and frame proof: 01 §4.3.
Proof: 01 §4.3. This statement excludes the old deletion sentence.

**fj.frame.v5 — NEW — PROVED-paper (window store clauses).** Use the
window store and provenance of bp.store.v2, bp.frame.v2, and 01 §§3–4,8.
The cumulative tree, F-start walk, live-cache controls, and read domains
are unchanged. No deletion rule is added. The v4 deletion example below
is old-fold evidence; its window replay is OPEN. Old v4 pins do not prove v5.

**fj.frame.v4 — historical old-fold evidence; WITHDRAWN for current use — NEW — PROVED-paper (2026-09-29); clause 2 deletion remark: REPLACED (01 §11.2; HEAD 720, S 800).**
Authority: spec 4e85ff34, Trees at lines 480–507, controls at 747–792.
Keep v3's unchanged store projection, cumulative-cache controls, and
FJ-domain clauses with their existing proofs. Replace its Trees clauses
as follows. **fj.frame.v3: WITHDRAWN for current use (2026-09-29)**
under registry §0; successor fj.frame.v4. Not true as pinned: its
deletion clause permits the metadata deletion refuted by replacement
01 §11.2 N2: HEAD differs at 720 and S at 800. Also, 4e85ff34 502–504
changes its genesis-walk clause.
Its other clauses carry into v4. Retain its old pins.
The clauses below are separate so that each has its own evidence kind.

```text
┌────┬──────────────────────────────────────────┬───────────────────────────────┐
│ #  │ Clause (4e85ff34 lines)                  │ Evidence                      │
├────┼──────────────────────────────────────────┼───────────────────────────────┤
│ 0  │ Σ.T is parent-closed and cumulative;     │ unchanged: keep v3 .leanHyp   │
│    │ a new block enters only if it extends F  │ evidence: Store,              │
│    │ (480–483).                               │ storeInv_init,                │
│    │                                          │ storeInv_on_block,            │
│    │                                          │ on_block_TF_subset,           │
│    │                                          │ update_finality_TF            │
│ 1  │ An inactive stored block with state      │ .external fg.finalLock.v2;    │
│    │ height above the accepted certificate's  │ normalized threshold and      │
│    │ entry height (0 for genesis) requires    │ evidence alternative, 01 §8.2 │
│    │ a slashable conflict (494–497).          │                               │
│ 2  │ No rule deletes a block of Σ.T           │ .lean process_cumulative,     │
│    │ (497–502). Deletion† can change HEAD and │ clock_cumulative (TF grows);  │
│    │ S, also at a≤f. Pruning is a retention   │ .paper remark FR M1/N2, †     │
│    │ item.                                    │ 01 §11.2 N2 †                 │
│ 3a │ The confirmation walk starts at Σ.F in   │ .lean after the F-start sync; │
│    │ act(Σ). Its result must pass strict      │ confirmationFrom, gateStep,   │
│    │ majority, also at Σ.F (502–504).         │ fastSet and clock bridge      │
│ 3b │ The FJ viability/band filter does not    │ .apData; separate HEAD/FG     │
│    │ restrict that walk (505–506).            │ and SA call paths             │
│ 4  │ act(Σ) is a view of Σ.T; only the SA     │ unchanged: .lean activeView,  │
│    │ base reads act(Σ) (484–490).             │ activeView_subset; .apData    │
│    │                                          │ for which module reads it     │
└────┴──────────────────────────────────────────┴───────────────────────────────┘
```

Clause 1 uses v2 because the external v1 states the carrier-h_F,
fault-bounded DC theorem. For genesis the ancestry alternative is
immediate. For non-genesis F, certificate provenance identifies the
threshold with the carrier h_F. An inactive block conflicts with F,
so the ancestry alternative fails and the evidence alternative follows.
The stored block and accepted F carrier are honestly held; RD2 scope
supplies RootInjectiveOn on their chains.
Clause 2’s deletion remark (†) is REPLACED by 01 §11.2 N2: different
HEAD at 720 and different S at 800.
Clause 2’s cumulative-storage invariant follows by event induction from `process_cumulative` and
`clock_cumulative`; `st.fg.TF` is monotone. Its deletion remark is a
counterexample fact (01 §11.2 N2; HEAD 720, S 800), not an output-preservation claim. Clause 3a is
proved on paper by 01 §6.5–§6.6 and current spec 1460–1477. The Lean pin needs
`SA.confirmationFrom`, `FGSA.gateStep`, `fastSet`, and
`clock_eq_saClockFrom_gate` after the sync. It is not discharged by the
current genesis-walk code. Clause 3b follows from the separate filter
arguments; clause 4 keeps the existing active-view proof and read audit.

**fg.finalLock.v3 — NEW — PROVED-paper (window provenance).** For accepted F, put
`finheight=0` for genesis and otherwise use its certificate entry height.
For an authenticated run block W emitted by the event read, assume
RootInjectiveOn on W and the accepted F carrier D for non-genesis F. With
`ht(W)>finheight`, either `F⪯W` or its rows with the F carrier expose
at least `2q_F−n` slashable identities. Under a≤f and client discipline,
`F⪯W`. Premises: Base, RootInjectiveOn D W for non-genesis F, any δ_t≥0, any a, no synchrony.
RD2 scope supplies this premise for delivered/held/ancestor chains.
Proof and the genesis normalization: 01 §8.2. Dependencies:
bp.carrier.v1, bp.chainCertificates.v2, bp.clientSafety.v1 (last clause).
Keep fg.finalLock.v1 and v2 pinned text and evidence as history; v3 uses
the exact window QCs of 01 §§3,8. No old concrete pin proves v3.

**fg.finalLock.v3-held — PROVED-paper (fault-bounded, honest-held corollary).**
Under `BaseSet` and `a≤f=⌊(n−1)/3⌋`, for every event index `i≤i′`,
honest nodes x,y, and blocks K,W, if `K∈TF_x(i)`, `σ[K].F=F_x(i)`,
and `W∈TF_y(i′)` with `ht(W)>σ[K].h_F`, then `F_x(i)⪯W`. Here TF_x(i)
is x's accepted set T at event index i.
The threshold is the accepted carrier K's certificate h_F, also for genesis.
This is the held-block branch of the full `fg.finalLock.v3` above (01 §8.2).
`FGSAClaims.finalLock` exports this corollary as `FinalLockClaim`/`RXing`
at Lean b15feea (`AvailableChainFGSAClaims/Claims/Foundations.lean:384–387`;
RXing body `AvailableChainFGSAClaims/Statements/ChannelProps.lean:701–705`).
The per-lock evidence alternative of v3 is not exported; the exported
accountability is the finalized-pair form, `finality.accountable`/`runAccountable`.

**bp.clientSafety.v1 — RESTATE (no-round) — PROVED-paper.**
No two honest emitted rows, including the pairs of a single row, violate
E1 or E2. An action without a height pair sends no row.
Premises: Base, persistent Λ, atomic record-before-emission, and
create_attestation with the sent set and the h≤h_f strip before recording.
Port note: account for suppressed sends, stripped pairs, and no row for
an empty pair; the safety conclusion is unchanged (01 §8.1).
New lemma (no-round): send-once coverage, 22 SO-COV; premises are the
client, the 01 §8.1 record invariants, and atomic record_attestation only.
Dependencies: none.
Lean reuse: KFG.RecordInv, RecordExtends, createRow_noSelfSlash,
clientRun_noSlash. Proof: 01 §8.1.

**fg.accountable.v2 — PROVED-paper.**
With RootInjectiveOn on the two carrier chains, conflicting finalizations expose E1/E2 evidence against at
least 2q_F−n identities in their authentic rows. This applies to accepted
F values by selection of their admitted carriers.
Premises: Base, RootInjectiveOn on the two carrier chains, any δ_t≥0, any a, no synchrony.
The admitted carriers of accepted F values are honestly held, so RD2 scope supplies it.
Dependencies: bp.carrier.v1, bp.chainCertificates.v2, bp.store.v2.
Lean reuse: KFG.accountable, accountable_oriented, with RootInjectiveOn.
Their conclusion is slashable weight 2q≤W+w(S); unit weights give the
count above. Proof: 01 §8.2.

**fg.finalLock.v1 — historical carrier-height form; WITHDRAWN for current use.**
If D finalizes F at m=σ[D].h_F and ht(W)>m, then F⪯W or the rows of
D,W expose at least 2q_F−n slashable identities. At a≤f, F⪯W.
Premises: Base; client discipline and a≤f only for the last clause.
Dependencies: bp.carrier.v1, bp.chainCertificates.v1, bp.clientSafety.v1.
Lean reuse: KFG.finalLock_e1/finalLock; DC
Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt.
The old mathematical statement remains true. Current window consumers use v3.
The DC declaration requires SlashableBound and root-collision freedom;
it supports only the fault-bounded clause. Proof: 01 §8.2. Use the
carrier h_F: it is 0 or 1 for genesis, whose state height is 1.

**bp.finalizedSafety.v2 — NEW — PROVED-paper.**
At a≤f, honest accepted F values at all nodes and times are compatible;
local F only extends. This holds for every δ_t≥0.
Dependencies: fg.accountable.v2, bp.clientSafety.v1, bp.store.v2.
Lean reuse: new run corollary. Proof: 01 §8.3.

Historical conditional port note (O-N18): the no-round audit concerned
fg.accountable.v1, fg.finalLock.v2, and bp.finalizedSafety.v1 if the KFG Row type has a round
field. Read-only check, 2026-10-01: AvailableChainSimplexFG/Objects.lean:37
has signer, height_pair, and finality_pair only; this condition is absent.
No Lean build or complete emission-contract check is claimed.

**bp.sourceDiscipline.v2 — RESTATE (no-round), K6 — PROVED-paper.**
Each honest nonempty height pair at a_r names (ht(C),σ[C].T_h) for the
actual deepest live C∈D_Σ(T)∩fastWrite[rR], from that tick's successful
fast gate. Its entry precedes C. At q_F>a, each target/progress QC
contains an honest row with such an earlier source. Each non-genesis
finalization has such a target origin through its justification, also
with its finality rows at strictly higher height.
Dependencies: bp.chainCertificates.v2, bp.leaseOrigins.v2.
Lean reuse: KFG certificate lemmas and height_pair_vote_fields;
the composed get_fg_vote origin proof is new. Proof: 01 §8.4.

**bp.receiptCoverage.v2 — RESTATE (no-round), K8 — PROVED-paper.**
For protected B compatible with receiving F throughout the transport:
at the deadline read either B⪯F, so output and every FG HEAD cover B
and conflicting leases are absent, or F⪯B and the required authentic
support paths above B are admitted by their original receipt deadlines.
An in-window required vote is retained or has two retained distinct
same-seat votes before the cutoff. No extra delay is added.
Premises: Base receipt, correct windows and dependencies; compatibility
is an input, not a conclusion.
Dependencies: bp.store.v2, bp.activeView.v2, bp.reconcile.v2,
comp.outputNesting.v3.
Lean reuse: G.accepted_head_receipt_before,
handled_head_stamped_or_equivocates; DC.NamedReceipt.excludes.
Proof: 01 §10.

### 3.2 Clean — stage 1

**Scope of §§3.2–3.3:** retained statements and proofs are for the old fold.
All concrete window uses are PORT PENDING at the marked 02/03 sites.
The v2 entries are window targets; 03 cites these successors, while 02
retains v1 labels on its old-fold proofs. Both keep the proof scope explicit.
Pure tree/count/score arguments keep their scope; no current Clean/P1
PROVED status follows before the provenance/store and event ports close.

**bp.sameLabel.v1 — NEW — PROVED-paper (pure conditional argument).**
Two honest genuine results of one synchronous label are compatible,
including results whose guards would veto them.
Premises: label receipt and both gate reads in the horizon.
Dependencies: raw vote-or-equivocation part of bp.receiptCoverage.v2.
Lean reuse: G.synchronous_support_subset_late,
synchronous_support_disjoint, sameLabel_from_engine. Proof: 02 §2.
One signed root resolves to one body at all honest stores: both honestly
held resolutions are in the injective run scope. Thus conflicting supporting
heads have distinct signed roots, as required by the equivocation step.

**bp.release.v1 — NEW, K11 — PROVED-paper (pure conditional argument).**
At fixed pools and stamps, restriction of active heads cannot increase
release_count(B). If every honest vote is compatible with B, the count
is at most a<τ and cannot release B. If B⪯F, the count is zero.
Premises: Base; a<τ for non-release. Expiry is separate.
Dependencies: bp.activeView.v2.
Lean reuse: G release definitions; new set inclusion. Proof: 02 §2.3.

**bp.cleanFrame.v2 — NEW, K7 Clean/K9 — PORT PENDING (old-fold proof retained).**
If all earlier honest fast-source bodies lie on one chain, every
disclosed justified/finalized entry is on its ancestor closure and
there is no contest. For an admitted protected B compatible with that
chain, either Z covers B, F covers B, or F⪯Z⪯B∈D_Σ(T).
At q_s, if all earlier-label genuine results precede the label-s result B,
then Z⪯B, ht(B)≥H−1, and the path from live_root to B lies in
D_Σ(V_(s+1)).
Premises: q_F>a, source history, and timely path receipt in the last clause. A bounding body used
by CPPrefix must be the erasure of a full named proposal in the run scope. Establish that membership
before identifying a named entry by root. Emitted-only observations do not supply it automatically.
Dependencies: bp.sourceDiscipline.v2, bp.chainCertificates.v2,
bp.receiptCoverage.v2, bp.frame.v2.
Lean reuse: KFG.entry_eq_on_plateau and height_crossing; new no-contest
argument, not the evidence branch of uniqueJust_chains. Proof: 02 §3.

**bp.suffixWalk.v1 — NEW, K10 geometry — PROVED-paper (pure conditional argument).**
For a finite parent tree and anchor∥B, if every edge strictly after
anchor through B is present, eligible and strictly dominates eligible
siblings, then B⪯ghost(anchor). If B⪯anchor, no path condition is needed.
Premises: root uniqueness on the walked tree and increasing depth. Retained transport requires
root uniqueness on its target tree. Obtain these facts from the local store or covered named scope.
Dependencies: bp.carrier.v1.
Lean reuse: G.ghostStep_of_strict_dominance, ghost_extends,
ghostWalk_covers_path; new suffix variant. Proof: 02 §4.1.

**bp.cleanTransfer.v2 — NEW, K10 Clean — PORT PENDING (old-fold proof retained).**
Each honest genuine result B of label s precedes every honest
label-(s+1) HEAD at q_s. This is a retrospective relation between
actual reads; q_s is before the gate d_s.
Premises: Clean through d_s, ordered history below s, and every
earlier-label result preceding B. The joint induction supplies these.
Dependencies: bp.sameLabel.v1, bp.cleanFrame.v2, bp.suffixWalk.v1,
bp.receiptCoverage.v2, bp.release.v1.
Lean reuse: G.TransferReceipts.majority/seat_unique/conflicting_score_bound;
new producers on D_Σ(V). Proof: 02 §4.2.

**bp.cleanHistory.v2 — NEW — PORT PENDING (old-fold proof retained).**
For s<r in Clean, every genuine result of s precedes every result of r;
every gate is nonempty, starting with the label-0 result g.
Same-label results are compatible. Actual fast sources, lease targets,
saved nonempty results, accepted F,J and S lie on their common
ancestor-closed chain. Reconcile deletes no Clean target or saved body.
Each result satisfies bp.cleanTransfer.v2.
Premises: Clean from genesis and event order.
Dependencies: the preceding conditional Clean lemmas, closed by the
joint prefix/label induction in 02 §5.
Lean reuse: G.genuine_history_induction as the logical pattern,
preserve_of_early_delivery and clean_genuine_history as proof templates.

**bp.cleanSafety.v2 — NEW, Clean clause of fj.armedSafe.v2 — PORT PENDING (old-fold proof retained).**
For honest x,y and all Clean reads t,u, S_x(t)∥S_y(u).
For honest x and t≤u, S_x(t)⪯S_x(u). Both available accessors obey
these properties. No a≤f or h≥τ premise is added.
Dependencies: bp.cleanHistory.v2, comp.outputNesting.v3.
Lean reuse: G.clean_gate_reads_compatible/clean_gate_record_monotone,
with new finality-origin cases. Proof: 02 §6.

### 3.3 Stage 2a — window targets; old-fold proofs in 03

These statements use the inclusive public reads in §2.1. All conclusions
are restricted to their proof horizons. No a≤f, h>2a, R≥3, δ_t=2R,
or recovery premise is added to Clean or either Outage regime.

**bp.cleanPrefixTruncation.v2 — NEW — PORT PENDING (old-fold proof retained).**
Assume Base, 0≤b₀≤horizon, healthy emission and receipt relay to b₀,
and h_t>a at every integer 0≤t<b₀. The Clean event-prefix invariant
holds through all events with time ≤b₀; Clean safety holds at every
public read in [0,b₀]. For d_r≤b₀, genuine results are nonempty,
ordered and same-label compatible, and transfer to the actual HEAD
inputs at q_r. Origins, frames, leases, saved bodies, F,J,S retain the
Clean properties. No participation at b₀ or later, and no delivery
deadline beyond b₀, is required.
Dependencies: bp.cleanHistory.v2, bp.cleanTransfer.v2, bp.cleanSafety.v2,
and their prefix/label induction in 02 §5.
Lean reuse: G.cleanThroughLabel_of_outage, G.synchronousLabel_of_outage.
Proof: 03 §1.3.

**bp.scoreSuffix.v2 — PORT PENDING for its window run producer; pure algebra unchanged.**
Let U⊆U' be raw sets. Each vote in U' must belong to U or have a seat
with two distinct votes in U. On each candidate X in the specified suffix
above receiving F, assume equal support incidence for every seat that does
not equivocate in U. Then participant sets, equivocation sets and scores
agree on that suffix. In Clean, an admitted honest proposal's carried
raw/support sets and the receiver's freeze-plus-proposal merge satisfy
these premises on X⪰D, where 03 §2.1 gives F⪯Z⪯D at both
reads. Incidence includes valid head slots and stored head membership.
Dependencies: bp.receiptCoverage.v2, bp.activeView.v2,
bp.cleanHistory.v2, bp.sourceDiscipline.v2, bp.chainCertificates.v2,
and the comparison-prefix bounds in 03 §2.1. No remote finality-acceptance
argument or ordering of the two F values is required.
Lean reuse: G.ScorePreservingViewExtension.count_eq/equivocates_eq/score_eq.
The score_eq theorem also needs its explicit ht membership equivalence.
The paper producer proves per-candidate incidence equality; a restricted
Lean score_eq_on still needs code. Proof: 03 §3; algebra also in 02 §4.3.

**bp.exactProposal.v2 — NEW, remaining K10 — PORT PENDING (old-fold proof retained).**
In Clean, every honest awake proposal P at t_s, s>0, is admitted
before v_s at every honest node. Every honest awake label-s HEAD equals
P. A sleeping honest node's deterministic HEAD read also equals P;
it emits no vote.
Dependencies: bp.cleanHistory.v2, bp.cleanFrame.v2,
bp.receiptCoverage.v2, bp.suffixWalk.v1, bp.scoreSuffix.v2.
Lean reuse: G.ghost_adopts_fresh_child, G.ghost_reanchor,
clean_honest_proposal_heads;
DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer
(DecoupledConsensusInternal/Definitions/NamedProposalPivot.lean:68).
Proof: 03 §§2.1,4, including path persistence and competitor reflection
with the receiving HEAD view's own witness.

**bp.cleanInclusion.v2 — NEW — PORT PENDING (old-fold proof retained).**
In Clean, each honest awake P at t_s, s>0, precedes every honest
S_y(d_s), where d_s=t_s+6Δ, and every later public read within the
Clean horizon. Include sleeping readers, pending-label results,
same-time deliveries after the gate, and output origins from F.
Dependencies: bp.exactProposal.v2, bp.cleanHistory.v2,
bp.cleanTransfer.v2, bp.cleanSafety.v2, comp.outputNesting.v3.
Lean reuse: G.clean_honest_proposal_repair, SA.included_from_engine.
Proof: 03 §5.

**bp.cleanGrowth.v1 — NEW — PORT PENDING.**
Under Clean₂ from time 0, awake-proposer recurrence on (t,t+G], G≥4Δ,
0≤t and t+G+6Δ≤horizon, there is one honest proposal P at t<t_s≤t+G.
For both available accessors and every honest x,y, output_x(t)≺P and
P⪯output_y(t+G+6Δ). The proposal and both reads share this deadline.
Proof: (1) recurrence supplies P; (2) all gate origins of S_x(t) have
labels ≤s−2, and an F origin is below its own earlier window target-QC
source result; (3) 03 §2.1 gives S_x(t)⪯D⪯parent(P)≺P;
(4) 03 §5 gives P⪯S_y(d_s), d_s≤t+G+6Δ, then monotonicity and
comp.outputNesting.v3 give both accessor clauses. Full proof: 03 §5.1.
Dependencies: bp.cleanHistory.v2, bp.exactProposal.v2, bp.cleanInclusion.v2,
bp.cleanSafety.v2, comp.outputNesting.v3; window producers remain pending.
Lean statement: CleanGrowthClaim and AvailableGrowthConcl,
AvailableChainFGSAClaims/Claims/Outage.lean at e1d4232.

**bp.outageCompatibility.v2 — NEW, K7/K9 P1 — PORT PENDING (old-fold proof retained).**
In either Outage regime, for B⪯S_x(T), every honest F at every
public read before b₁ is compatible with B. Every honest S on
[b₀,b₁), and every honest HEAD or proposal parent chosen there,
contains B. For B≠g, let l be the last gate label with d_l≤b₀
and j=l+1. The lag gives such an l from a successful gate origin
s with d_s≤T. The interval [b₀,d_j) has complete healthy-batch
protection. At each honest public read d_j≤t<b₁, after all events
with time ≤t, either B⪯F_y(t), or a live lease on B has deadline
at least d_j+L and B is in the full filtered domain or below Z.
There is no first conflicting successful result/source or departing
honest HEAD after this arming. If d_j is beyond the requested horizon,
only the first interval is needed. Genesis has immediate F coverage.
The lease-or-F clause starts at d_j; it need not hold at b₀.
Dependencies: bp.cleanPrefixTruncation.v2, bp.cleanHistory.v2,
bp.sourceDiscipline.v2, bp.chainCertificates.v2, bp.store.v2,
bp.receiptCoverage.v2, bp.release.v1, bp.frame.v2,
bp.leaseOrigins.v2, bp.reconcile.v2, bp.suffixWalk.v1,
comp.outputNesting.v3.
Lean reuse: SA pending-gate templates; new joint event induction.
Proof: 03 §§6–8, with the source-compatible frame lemma in §7.

**bp.fastP1.v2 — NEW — PORT PENDING (old-fold proof retained).**
Under Outage(4Δ) and h_t≥τ throughout 0≤t<b₀,
for all honest x,y, all B⪯S_x(T), and b₀≤t<b₁, B⪯S_y(t).
The budget is min(η,L). This is PersistsThrough. In addition, honest
HEADs and proposal parents chosen in [b₀,b₁) extend B, and every
honest F at every public read before b₁ is compatible with B.
These additional duty and F clauses are not fields of PersistsThrough.
Dependencies: bp.outageCompatibility.v2, bp.cleanPrefixTruncation.v2,
bp.cleanHistory.v2, bp.receiptCoverage.v2, bp.release.v1.
Lean reuse: SA.pending_fast_protection, SA.fastP1_from_engine
(Proofs/FastOutage.lean). Proof: 03 §9.1.

**bp.slowP1.v2 — NEW — PORT PENDING (old-fold proof retained).**
The same output, HEAD, proposal-parent and F-compatibility conclusions
hold under Outage(L−3Δ), without h_t≥τ. The budget is min(η,L).
The lease clause starts at the pending gate d_j; prior output and duty
coverage use the complete healthy batch. No arbitrary saved-window
preservation is asserted.
Dependencies: bp.outageCompatibility.v2, bp.cleanPrefixTruncation.v2,
bp.cleanHistory.v2, bp.receiptCoverage.v2, bp.release.v1, bp.reconcile.v2.
Lean reuse: SA.clean_result_after_stable, SA.pending_heads_cover,
SA.stable_resilient_from_engine (Proofs/Outage.lean),
SA.slowEligible_of_input_covers (Proofs/SlowWindow.lean).
Proof: 03 §9.2.

**fj.armedSafe.v2 — PORT PENDING (old-fold proof retained).**
For frozen FJ FG-SA, the conjunction is Clean global safety and local
monotonicity, Clean 6Δ honest-proposal inclusion, global fast P1 at
lag 4Δ with high participation through the healthy prefix, and global
slow P1 at lag L−3Δ, for a<h and budget min(η,L).
Both available accessors return stored S. No recovery or finality
liveness premise is used.
Dependencies: bp.cleanSafety.v2, bp.cleanInclusion.v2,
bp.fastP1.v2, bp.slowP1.v2, comp.outputNesting.v3.
Lean reuse: new composite assembly; no checked composed run theorem.
Proof: 03 §9.3.

### 3.4 Stage 2b — exact statements proved in 21 and 22

The current recovery and forward-window entries below are **PROVED-paper**
under their stated premises. QF2/QF4 are dropped open extensions, outside the claim set. Other unported finality alternatives are
PORT PENDING or OPEN, as stated separately. Registry names are cross-references. Recovery₂ and the chosen
recurrence form are as in §2.5. A stopped phase claim ends at the first
effective event; it does not assume service across that event.

**bp.phaseWitness.v2.** In a settled phase at u≥GST, each honest HEAD K
at v_s≥u is in the full domain and has W⪰K of height ≥lo. Every honest
receiver admits W and its needed path before e_s, or already covers a
protected prefix through F. No ht(K)≥lo premise is required.
Dependencies: finalLock, frame, receiptCoverage. Proof: 21 H.3.

**ap.headReachesLo.v7 — NEW window version, 2026-10-01.** If live start
A is in D(V_s), or has an eligible child there, the HEAD is in D(V_s)
at height ≥lo. Otherwise it returns A. If A=Z and the domain is nonempty,
Z is in it. The phase clauses use Recovery₂ with C1 and R≥max(2,κ), full-store witness
transfer, H.6's two-lease repair, and H.8's strict settlement θ=3Δ.
The complete six-clause statement and proof are in 21 after H.8.
2026-09-29. ap.headReachesLo.v5 is WITHDRAWN for current use under
registry §0: changed statements or hypotheses get a new id. It is still
true in its stated scope (R≥3, 4Δ, spec bd942ca0). The HEAD functions
are unchanged in 4e85ff34. Clause 5 transfers by bp.genuineFromF.v2
(01 §6.5) with F⪯P in a settled phase: a lower F has certificate height
below lo≤ht(P), and in top J one has F⪯J⪯P. Strict 3Δ settlement also
implies the weaker 4Δ bound. Keep its old pins. Successor:
ap.headReachesLo.v6 (spec 4e85ff34, R≥2, strict receipt, θ=3Δ).
The v6 phase hypotheses are historical; v7 uses C1 and the window W1–W3
proofs in 21. Geometry does not depend on phaseRepair. Old v6 pins do not transfer.

**fj.twoChanges.core.v3 — NEW window version, 2026-10-01.** At a fixed
frontier m, evidence in cumulative Σ.T and its live caches gives gap →
top J → contest, with phases possibly absent and at most two changes.
Lower F moves add no phase; the fixed-set domain identity removes only
a trunk below F′. Acceptance at m−1 supplies top-J evidence if absent;
count that event once. Frozen views supply D(V)'s witnesses, not its
controls. Proof and exact premises: 21 H.7 and its restatement after H.8.
The v2 old-fold proof remains historical; v3 uses 21 W1 and H.7–H.8.
As of 2026-09-29, `fj.twoChanges.core.v1` is WITHDRAWN for use under
4e85ff34: duty-view evidence cannot determine the live-cache frame when
Σ.T has newer evidence outside that view. Keep its pins and partial
Lean coverage as history. H.8 supplies the C1 timing for v3.

**fj.descent.v3 — NEW window version, 2026-10-01.** At an alleged first
loss of a synchronous source above μ, cumulative-frame exclusion gives
an earlier loss or an earlier incompatible-source pair. For a conflicting
source C′ with s′>s, its supporter is an earlier loss of C (case (2));
for s′<s, C's supporter is an earlier loss of C′. Old sources and equal
labels are excluded. A late contested carrier is handled by the earlier
incompatible pair, not assumed frozen. The measure is the event index.
Proof and full cases: 21 H.13 and the restatement immediately after it.
The v2 old-fold proof remains historical; v3 uses W3 and the revised H.13.
As of 2026-09-29, `fj.descent.v1` is WITHDRAWN for use under 4e85ff34:
its controlling-QC-in-HEAD-view conclusion is unusable when live-cache
controls read evidence outside that frozen view. Keep its old pins.

**bp.phaseSourcePermanence.v2 — NEW.** In a settled phase, a
synchronous fast body or a successful slow body with a wholly synchronous
window whose current HEAD label is in the settled phase has H.2 S1–S3 until the phase ends. A prefix passed by
finality retains coverage. Dependencies: bp.phaseWitness.v2, 21 H.1–H.2,
and 21 IF.3, IF.5–IF.7. Proof: 21 H.4 and H.4-S.

**bp.phaseRepair.v2.** Let a settled phase start at u≥GST. Let β be the
first proposal label strictly after u and ℓ=β+2k−1. Each honest P at
t_s>t_ℓ, while the phase persists through d_s, is every honest HEAD
and has a successful fresh fast write at d_s. If the phase persists
through u+ρΓ, such a gate occurs by u+ρΓ; otherwise it ends within the
budget. The same service holds for later honest proposals in that phase.
It does not preserve damaged earlier outputs.
Alternatively let b=min{label:v_b≥u} and require v_(b−k+1)≥GST.
Then set ℓ=b+k and use the strict bound u+ρ₁. H.6-C supplies this
premise after settlement for every reset attempt if k≤2R+1.
Dependencies: phaseWitness, 21 H.1–H.5. Proof: 21 H.6, H.6-S/C.

**bp.phaseEvents.v2.** At fixed frontier m, phases are gap, uncontested
top J, contest, in that order, with at most two changes. Lower F moves
add no phase. Evidence first accepted at w≥GST reaches full stores
before w+Δ and every HEAD at v_s≥w+3Δ, unless the task ends first.
Dependencies: finalLock, clientSafety, frame, receiptCoverage.
Proof: 21 H.7–H.8. The settlement allowance is θ=3Δ and requires strict delivery <Δ.

**bp.rowPermission.v2 — RESTATE (no-round).** In a settled phase, a common
fresh source at c∈[lo,m] makes height_pair return a nonempty progress pair
for its entry E. Each honest identity either sends a row for (c,E) at
this action or has already sent a matching row (22 SO-COV). Strict receipt
and R6/R7 supply matching progress coverage; a new emission is not required.
Dependencies: chainCertificates, clientSafety, phaseEvents, 22 SO-COV, bp.rowService.v2. Proof: 21 H.7.

**bp.rowService.v2 — PROVED-paper.** Use the exact T-ROWS statement in
01 §1.1, copied into 21 IF.5/H.22 and 22 §1/I6. C1 has separate
standalone-row Δ_F and complete-block Δ deadlines. R7 supplies every
effect, including optional omission; height and retained-entry persistence
are separate. SO-COV alone does not supply fresh finality signatures.
Dependencies: receiptCoverage, chainCertificates, R6-window/R7.
Proof: 01 §1.1 and 22 I6; no healing premise in the row-service proof.

**bp.commonEntry.v2 — NEW.** After the H.6 repair gate in a settled
phase, one of the first two opening actions gives a common source
height c≥lo and entry E, within 2P−4Δ. The first opening is within
P−4Δ: either all sources have one low entry, or a source is at m.
If the repair is already at m, that first opening has common entry. A phase event stops the attempt
sooner. No honest opening is required. Lower F cannot pass the repaired
pivot; a higher source in the two-height band transfers by the next
opening. Dependencies: bp.phaseRepair.v2, bp.phaseEvents.v2,
bp.phaseSourcePermanence.v2, bp.rowPermission.v2, 21 H.2 S1,
and 21 IF.1, IF.3–IF.4, IF.6.
Proof: 21 H.9, common-entry proof.

**bp.renewedPromotion.v2 — RESTATE (no-round).** After an H.6 or H.6-S repair gate,
let a_r be a common-entry action in a persisting settled phase. The
proposal-grid trigger T_r+2P−4Δ supplies an honest X with
T_r+2P≤t_X≤a_r+2P+Γ−10Δ. Fixed starting action r coverage
uses earlier or new matching rows (22 SO-COV), held before T_r+β≤T_(r+1). Each required progress effect is supplied by HeightMatch, a parent bit,
or R7's final selected set, unless height has
advanced. A higher source lies below its parent; otherwise the matching
progress bits are above the common entry and mature.
Thus ht(X)≥c+1. A terminal phase event is accepted before t_X+Δ,
within D=2P+Γ−9Δ of a_r. If the phase persists, its exact service
gate is within C=2P+Γ−4Δ. A served height-m proposal needs only
P−4Δ more for a common-entry action or the first height-m row.
Dependencies: commonEntry, rowPermission, phaseRepair, rowService,
phaseSourcePermanence, 21 H.2 S2, chainCertificates, 22 SO-COV. Full proof: 21 H.9(b).

**bp.qualifiedOpening.v2 — retained alternative.** With qualified
search bound g_h P, a qualified opening r′∈[r+2,r+g_h+1] consumes
the fixed starting coverage or its progress bits, unless its parent crossed c.
The opening is mature; no +2 receipt claim is used for κ>2. Each promotion and next served
opening costs at most (2+g_h)P. This is no longer a premise of the
primary healing proof. Proof: 21 H.9-Q–H.11-Q.

Port note for bp.progressAttempt.v2 / fj.rise.movingF.v1: SO-COV gives
a row sent by the deadline. RESTATE (no-round) only if the Lean statement
requires a new emission at the selected action; no Lean check is made here.

**bp.progressAttempt.v2.** Start at an effective event or u₀. Before a
served frontier proposal, HG.3 gives E_g^F, E_j^F, and K=r̄+3Δ for gap,
top J, and contest. An intervening event ends that attempt. After such
a proposal, HG.1 preserves service through same-frontier events.
HG.4 gives tails 2P+Γ−9Δ for a rise and P−4Δ for a row. HG.5 sums
E_g^F+E_j^F+B_c^F for a rise and E_g^F+E_j^F+D_c^F for a row. Skipped phases
remove allowances. H.10's older per-phase bounds remain valid.
Dependencies: phaseEvents, phaseRepair, rowPermission, commonEntry,
renewedPromotion, HG.1 frontier service, HG.2 entry age.
Full proof: 21 HG.1–HG.5.

**bp.resetArrival.v2 — RESTATE (no-round).** Keep the §2.5 cut and witnesses. All honest
rows through u₀ have height ≤M; μ≤M; GST+2P≤u₀<GST+3P. A first
row at M+1 is first emitted at action r*, with fresh source C* and synchronous
label s*. HG.5 bounds the work after u₀ by 2E_g^F+2E_j^F+B_c^F+D_c^F.
Thus a_(r*)<GST+B'_reset^F, where B_reset^F(r̄)=3P+2E_g^F+2E_j^F+B_c^F+D_c^F;
take the minimum over eligible repairs. At k=2,G=8Δ, B'_reset^F is
283Δ for R=2 and 331Δ for R=3 at Δ_F≤2Δ;
339Δ at R=3, 2Δ<Δ_F≤6Δ. Up to six repair charges remain;
same-frontier events after frontier service add no repair charge.
Dependencies: progressAttempt, sourceDiscipline, chainCertificates.
Full proof: 21 H.11 and HG.6. Five charged restarts after u₀ and six
maximum repair costs are not shown to be necessary.

**bp.postResetKeep.v2.** Put b=s*. Protect successful fast bodies with
s≥b and successful slow bodies with all k labels ≥b. At each later
duty they have a witness in that duty's domain, are below its root,
or have root/anchor coverage. A full-domain witness alone is not a
HEAD witness. Each body B has S1–S3: HEAD coverage from q_s,
proposal-parent coverage for slots ≥s+2, output coverage from d_s+4Δ.
C* has these clauses too. Every high selected source, even with an empty
height pair, has label ≥s*. High sources are compatible; high rows name
one entry per height and are targets. Each post-reset duty holding C*
has H≥M+1, contest ⇒ H=M+1, and lo≤max(M+1,H−1).
Dependencies: resetArrival, 21 H.1–H.2,H.12–H.13. Proof: 21 H.14.

**bp.universalLeases.v2 — NEW.** If C*≺B, no honest store held B through
u₀. Each result in a successful lease window on B is synchronous.
Every successful write on B, including one before the reset, gives S1–S3;
later genuine results cover B or have finality coverage.
Dependencies: postResetKeep, 21 H.1–H.2. Proof: 21 H.15 (Lemma U).

**bp.rawResultTransfer.v2 — NEW.** Every nonempty raw genuine result at
j≥s* transfers at q_j and has S1–S3, including low-support and vetoed
results. Dependencies: postResetKeep, universalLeases.
Proof: 21 H.16 (Corollary U′).

**bp.postResetService.v2 — NEW.** Every honest proposal Q of slot
v≥s*+2 is every honest HEAD. Each raw result at d_v is Q, its guard
passes, it fast-writes Q, and post-gate S=Q. At an opening, C_fg=Q.
Dependencies: postResetKeep, universalLeases,
the score algebra of 02 §4.3, and the run producer in 21 H.5.
Proof: 21 H.17, including an off-path child below a high proposer F.

**bp.localHealing.v2.** For the first honest proposal slot u≥s*+2,
HEALED(d_u), cross-node F_x(t)⪯S_y(t) from that cut, and
 d_u≤q_(s*)+Γ+5Δ=a_(r*)+Γ+4Δ.
If 2τ−2≤n−a, HEALED(q_(s*)+5Δ) also holds. That earlier all-fast
cut does not replace the interface's repair-gate witness.
Dependencies: rawResultTransfer, postResetService, postResetKeep, nesting.
Proof: 21 H.18–H.19. Replacement 21 N.1 refutes healing at q_(s*) with local delay G+5Δ.

**bp.uniformHealing.v2 — PROVED-paper.** HEALED(GST+B_H^F) under
Recovery₂ with G alone, with one actual healing gate strictly before
that deadline. Qualified search also permits B_best^F(g_h).
At k=2,G=8Δ: 295Δ at R=2 and 343Δ at R=3 for Δ_F≤2Δ;
351Δ at R=3 for 2Δ<Δ_F≤6Δ. Both branches and the eligible minimum
are defined in 21 §1/H-time. Dependencies: resetArrival, localHealing,
HG.1–HG.6 and W1–W3. Proof: 21 H.20–H.21.

**bp.healingInput.v2 — RESTATE (no-round); sole healing→finality export.** Under Recovery₂
there exists the repair cut t*=d_u with HEALING_INPUT(t*) and t*<GST+B_H^F,
or GST+B_best^F(g_h) under qualified search. The exact H0–H6 package is
proved in 21 H.22 and copied in 22 §1. Its four parts are the common
witness, T-stream (actual sources, carrier ancestry and T-ROWS), AC-output
service, and FG foundations. H2′ and the HEAD clauses of H2.A and H3
are AC services to the joint selections. H3/H4 supply T-EXACT/T-SMONO
for joint functions. H5 transfers every nonempty post-reset raw result;
H6 supplies the unanimous covered-prefix
gate write. The source selector still checks D(T). All parts use the
same witnesses and post-gate cut. H-time is the theorem's time bound;
HEALED alone is insufficient.
Dependencies: resetArrival, postResetKeep, universalLeases,
rawResultTransfer, postResetService, localHealing, and 01 §1.1 T-ROWS;
the optional time bound also uses qualifiedOpening. H.16 proves H5;
H5 and the H.2 count prove H6 within H.22. Consumers in 22 need neither
healing lemma directly. Proof: 21 H.22 and its full dependency list.

**bp.finalityKernel.v2 — PROVED-paper.** Under the full window
HEALING_INPUT(t*), Base/quorum/awake/C1 premises of 22 §1, K_W≥2,
R≥max(2,κ), δ_t=2R, T_p≥t*, and FGoodE_W(p), put d=ht(A).
The second opening gives a fresh U≻A at d+1. An honest target carrier
c∈[(p+1)R+κ,(p+2)R] justifies U; FGood4_W fixes c=(p+1)R+κ.
Fresh action-(p+2) rows carry U's finality pair. Before the terminal
carrier e=(p+2)R+κ, at most one newer justification can occur. Thus
K_W≥2 retains U or F covers it. Stale carriage supplies its exact bits.
The greatest-ready test and acceptance give U⪯F at every honest node
before T_(p+2)+β+Δ. This includes κ=R; no G≤P premise is needed.
Dependencies: H0–H6, H2.A/H2′/H3 HEAD services; 01 §1.2 T-START,
T-SMONO/T-EXACT/T-VOTE/T-WALK; 22 I1–I7, FF2/FF2-C, FF1-A,
Q0 when c<z, F1–F7, F8-W retention, F9/FF4-W acceptance.
F8-X is only the retained old +2 proof. Proof: 22 §4a.

**bp.tailWindow.v1 — NEW — PROVED-paper.** Used only by the dropped QF2/QF4 extensions. With the full interface,
Tail_W(r), δ_t=2R, K_W≥2 and R≥κ, a high latest entry at the
honest first opening, or the stated earlier honest witness for it,
is finalized or covered everywhere before T_(r+1)+β+Δ.
Dependencies: Q0, F8-W, I6/I7 and F9 acceptance. Proof: 22 FT-Tail-W.

**bp.firstFinality.v2 — PROVED-paper.** Under Recovery₂ and
Rec_FE_W(g_f) or Rec_F4_W(g_f), every honest F covers a new common
entry before GST+B_F^W(g_f), where B_F^W=B_H^F+W_W and
W_W=(g_f+2)P+β+Δ. Qualified healing search permits B_best^F
in place of B_H^F. Dependencies: healingInput, finalityKernel.
Proof: 21 H-time and 22 FF5. Strong alternatives remain PORT PENDING.

**bp.finalityLiveness.v2 — PROVED-paper.** With the full window
interface, δ_t=2R, K_W≥2, R≥κ and Rec_FE_W(g_f) or Rec_F4_W(g_f),
each t≥t* gives a canonical entry strictly above every S_i(t) and the
finalized height at t before t+W_W(g_f). FF6 finalizes a specified
post-healing honest proposal X before t_X+W_W; FF7 exceeds the archival
frontier at t before t+2W_W. Proof: 22 FF5–FF7. Strong alternatives,
HP, and FL-W/RF/D/T7 remain old-fold proofs, PORT PENDING.

**FF6 / FF7 window instances.** Use Rec_FE_W or Rec_F4_W:
FF6 has W_W=(g_f+2)P+β+Δ; FF7 has 2W_W. No SO-COV-only
finality batch or whole-run height transfer is used.

Stage 1 additions (the channel and joint services are conditional):

```text
┌─────────────────────┬────────────────────────────────────────┐
│ Id                  │ Proof                                  │
├─────────────────────┼────────────────────────────────────────┤
│ bp.channel.v2       │ 01 §1.1; RESTATE (no-round)            │
│ bp.jointServices.v2 │ 01 §1.2 (conditional joint services)   │
│ bp.genuineFromF.v2  │ 01 §6.5; spec sec:filtered-proofs      │
│ fj.frame.v5         │ 00 §3; 01 §4, §6, §11                  │
│ fg.finalLock.v3     │ 01 §8.2                                │
│ fg.finalLock.v3-held│ 01 §8.2; R-XING in 01 §1.3             │
└─────────────────────┴────────────────────────────────────────┘
```

Stage 2a target mapping (positive window run ports pending; negatives in §3.5):

```text
┌───────────────────────────────┬─────────────────────────────┐
│ Outline id                    │ Local proof                 │
├───────────────────────────────┼─────────────────────────────┤
│ bp.cleanPrefixTruncation.v2   │ 03 §1.3                     │
│ bp.scoreSuffix.v2             │ 03 §§2.1,3                  │
│ bp.exactProposal.v2           │ 03 §§2.1,4                  │
│ bp.cleanInclusion.v2          │ 03 §5                       │
│ bp.cleanGrowth.v1             │ 03 §5.1; PORT PENDING       │
│ bp.outageCompatibility.v2     │ 03 §§6–8 (pending gate d_j) │
│ bp.fastP1.v2                  │ 03 §9.1                     │
│ bp.slowP1.v2                  │ 03 §9.2                     │
│ fj.armedSafe.v2               │ 03 §9.3; 02 §6              │
│ bp.pendingBoundaryNegative.v1 │ 03 §10.1; window checked    │
│ bp.targetExtensionNegative.v1 │ 03 §10.2; window checked    │
└───────────────────────────────┴─────────────────────────────┘
```

Stage 2b statement mapping:

```text
┌─────────────────────────────┬────────────────────────────────────┐
│ Outline id                  │ Local proof                        │
├─────────────────────────────┼────────────────────────────────────┤
│ bp.phaseWitness.v2          │ 21 H.3                             │
│ ap.headReachesLo.v7         │ 21 H.3,H.6,H.8; 02 §7 historical   │
│ fj.twoChanges.core.v3       │ 21 H.7; restatement after H.8      │
│ fj.descent.v3               │ 21 H.13 and its restatement        │
│ bp.phaseSourcePermanence.v2 │ 21 H.4, H.4-S                      │
│ bp.phaseRepair.v2           │ 21 H.6, H.6-S/C                    │
│ bp.phaseEvents.v2           │ 21 H.7–H.8                         │
│ bp.rowPermission.v2         │ 21 H.7; RESTATE (no-round)         │
│ bp.rowService.v2            │ 22 I6; RESTATE (no-round)          │
│ bp.commonEntry.v2           │ 21 H.9, common-entry proof         │
│ bp.renewedPromotion.v2      │ 21 H.9(b); RESTATE (no-round)      │
│ bp.qualifiedOpening.v2      │ 21 H.9-Q (optional)                │
│ bp.progressAttempt.v2       │ 21 H.10, HG.1–HG.5                 │
│ bp.resetArrival.v2          │ 21 H.11; RESTATE (no-round)        │
│ bp.postResetKeep.v2         │ 21 H.14 (uses H.12–H.13)           │
│ bp.universalLeases.v2       │ 21 H.15                            │
│ bp.rawResultTransfer.v2     │ 21 H.16                            │
│ bp.postResetService.v2      │ 21 H.17                            │
│ bp.localHealing.v2          │ 21 H.18–H.19                       │
│ bp.uniformHealing.v2        │ 21 H.20–H.21                       │
│ bp.healingInput.v2          │ 21 H.22; C1/window                 │
│ bp.finalityKernel.v2        │ 22 F1–F9, F8-W                     │
│ bp.firstFinality.v2         │ 22 FF5; B_F^W                      │
│ bp.finalityLiveness.v2      │ 22 §5; FF5–FF7 window              │
└─────────────────────────────┴────────────────────────────────────┘
```

Export note: `FGSAClaims.finalityLivenessGSTRecFE` and
`FGSAClaims.finalityLivenessGSTRecF4` export the FF5 clause of
`bp.finalityLiveness.v2` only for triggers with `GST+B_HF≤t` (premise
`late`, `AvailableChainFGSAClaims/Statements/Packages/FinalityGST.lean:14–20`;
claim `AvailableChainFGSAClaims/Claims/Finality.lean:157–167`), where
`B_HF` is the paper's B_H^F. The fields `proposalFinalGSTRecFE/F4` export
the FF6 clause and `aboveFrontierGSTRecFE/F4` the FF7 clause, with the
same trigger condition (`FinalityGST.lean:30`, `:42`;
fields `AvailableChainFGSAClaims/FGSAClaims.lean:103–108`).
The GST form takes Recovery₂ (`FinalitySet_W.core`,
`AvailableChainFGSAClaims/Statements/Packages/Finality.lean:31–36`) and
δ_t=2R in place of HEALING_INPUT, and returns a HealingInput witness with
`tstar w<GST+B_HF`. Triggers in `[t*, GST+B_HF)` are not exported;
the local FF5–FF7 forms stay Claims-module interfaces
(Lean b15feea, `AvailableChainFGSAClaims/FGSAClaims.lean:14–15`).

### 3.4a Continuation — FGSAClaims field and proof helpers

All 12 entries below have status **PROVED-paper**: one FGSAClaims field and 11 proof helpers.
The field is `weakContinuationLive : ∀ G, WeakContinuationLiveClaim p G`. Reviews: [Astra ADOPT](../codex/reports/wc-blueprint-review.md),
[Opus ADOPT WITH FIXES](../codex/reports/wc-blueprint-review-opus-full.md).
Chapter 23 applies Opus R1–R8 as editorial fixes. The window source and
F-advance arguments are in 23 §§5–8,10,12; C1 and T_F are in §1.1.
The recovery-integration reviews and 21 H.21 close the later healing gaps.
The earlier continuation reviews do not certify unchanged old premise records.
The DC counterpart is Generic Claims `available`, with start
RecoveredBy.recovered (23 §1.3).

**bp.weakContinuationAvailable.v2 — FGSAClaims.weakContinuationLive field (user 2026-10-05) — PROVED-paper.**
With δ_t=2R, each StrongRecoverySearchPrefix₂ source selects one u,Q*,i*
with BoundedHealingCut₂ before every CleanContinuation₂ is quantified.
Every such continuation has SSafeFromCut₂ and IncludedFromCut₆Δ from d_u,
for both stable and confirmed outputs, with persistence through its horizon.
The same witnesses give the safety projection. The fixed-start corollary
uses t₀=T_F=GST+B_H^F, reads at timeIdx≥timeIdx(T_F), and proposals
at t_s≥T_F. The premise instances use C1, K_W≥2, and R≥max(2,κ);
all prefix, agreement, and all-awake endpoints are T_F.
Dependencies: H.22/H-time, 01 window foundations, pure 02/03 walk/score
arguments, and the 11 claims below; 23 supplies its own seeded event induction.
Proof: 23 §§1.2,14; DC comparison and preparation: 23 §§1.3,15.
Growth field (bp.weakContinuationGrowth.v2): the same witnesses give
JointGrowthAt t (t+G'+6Δ) for every G'≥4Δ with an awake-proposer
recurrence from d_u, and every covered t≥d_u. Proof: 23 §17.

**bp.wcPrefixReplay.v2 — PROOF HELPER — PROVED-paper.**
Through T_F, each agreed continuation has the same source states, actual
event values, emissions, receipt stamps, duty reads, and cut i*.
Proof: 23 §3; premises and dependencies as stated there.

**bp.wcHeightSeed.v2 — PROOF HELPER — PROVED-paper.**
Under the source premises and δ_t=2R, the selected H.22/H-time
witnesses satisfy the finite height seed HS of 23 §2.
Proof: 23 §4; premises and dependencies as stated there.

**bp.wcLowFinalized.v2 — PROOF HELPER — PROVED-paper.**
Every finalized entry E at height x≤M satisfies E⪯C*⪯Q*,
including entries with private or later disclosed carriers.
Proof: 23 §5; premises and dependencies as stated there.

**bp.wcSourceOrigin.v2 — PROOF HELPER — PROVED-paper.**
An honest row emitted after gate d_r uses K∈fastWrite[r] with
K⪯C_(x,r); a carried old row keeps its source, emission time, and label bounds.
Proof: 23 §6; premises and dependencies as stated there.

**bp.wcSeededFrame.v2 — PROOF HELPER — PROVED-paper.**
Under HS, stored C*, Q*⪯B, and usable high sources below B,
F⪯Z⪯B and lo≤ht(B). Live targets below B give Z⪯A⪯B.
Proof: 23 §7; premises and dependencies as stated there.

**bp.wcSeededInduction.v2 — PROOF HELPER — PROVED-paper.**
Under the selected HS and continuation premises, every completed
suffix event prefix satisfies I1–I5 of 23 §8.1.
Proof: 23 §8; premises and dependencies as stated there.

**bp.wcSeededSafety.v2 — PROOF HELPER — PROVED-paper.**
From i*, honest S outputs are compatible across nodes and times,
each local S is monotone, and Q* remains a prefix of every S.
Proof: 23 §9; premises and dependencies as stated there.

**bp.wcFinalBelow.v2 — PROOF HELPER — PROVED-paper.**
At each completed suffix event index i and honest x,y,
F_x(i)⪯S_y(i).
Proof: 23 §10; premises and dependencies as stated there.

**bp.wcProposalPivot.v2 — PROOF HELPER — PROVED-paper.**
For an actual honest proposal P with t_s≥d_u and d_s≤ρ.horizon,
the common prefix D gives F⪯Z⪯D, lo≤ht(D), and both walks reach D.
Proof: 23 §11; premises and dependencies as stated there.

**bp.wcExactProposal.v2 — PROOF HELPER — PROVED-paper.**
Under 23 §11, every honest node admits P before v_s and its
deterministic label-s HEAD is exactly P, including asleep nodes.
Proof: 23 §12; premises and dependencies as stated there.

**bp.wcInclusion6.v2 — PROOF HELPER — PROVED-paper.**
Each actual honest P with d_u≤t_s and d_s≤ρ.horizon satisfies
P⪯S_y(d_s) at every honest y and remains included through the horizon.
Proof: 23 §13; premises and dependencies as stated there.

Continuation statement mapping (same review verdicts as above):

```text
┌─────────────────────────────────┬────────────────┬──────────────┬───────────────────────────┐
│ Outline id                      │ Local proof    │ Status       │ Marker                    │
├─────────────────────────────────┼────────────────┼──────────────┼───────────────────────────┤
│ bp.weakContinuationAvailable.v2 │ 23 §§1.2,14    │ PROVED-paper │ FGSAClaims field          │
│ bp.wcPrefixReplay.v2            │ 23 §3          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcHeightSeed.v2              │ 23 §4          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcLowFinalized.v2            │ 23 §5          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcSourceOrigin.v2            │ 23 §6          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcSeededFrame.v2             │ 23 §7          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcSeededInduction.v2         │ 23 §8          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcSeededSafety.v2            │ 23 §9          │ PROVED-paper │ PROOF HELPER              │
│ bp.wcFinalBelow.v2              │ 23 §10         │ PROVED-paper │ PROOF HELPER              │
│ bp.wcProposalPivot.v2           │ 23 §11         │ PROVED-paper │ PROOF HELPER              │
│ bp.wcExactProposal.v2           │ 23 §12         │ PROVED-paper │ PROOF HELPER              │
│ bp.wcInclusion6.v2              │ 23 §13         │ PROVED-paper │ PROOF HELPER              │
└─────────────────────────────────┴────────────────┴──────────────┴───────────────────────────┘
```

### 3.5 Negatives and open boundaries

**Historical-negative scope.** Every execution and lower-bound status in
this section is old-fold evidence unless an explicit window proof is named.
REPLACED/WEAKER/REVALIDATE refer to the no-round revision, not the window.
The 03 §10 and 21 §10 checks establish the stated window negatives;
22 N2 is refuted. Other current-window negatives remain OPEN. HEIGHT BRIDGE
cannot replay admission, live F changes, sources, or output histories.

**bp.pendingBoundaryNegative.v1 — NEW — PROVED-paper (window checked).**
A valid slow-Outage execution has B⪯S_x(T), but at b₀=T+L−3Δ
one honest reader has neither B⪯F nor a live lease on B, even at the
inclusive public read. Thus lease-or-F coverage at b₀ is false.
The example has n=5,a=1,Δ=4,k=2,T=40,b₀=56,b₁=84;
its pending gate is d_j=72. P1 holds throughout.
Dependencies: exact duty, gate, receipt and client rules.
Lean reuse: SA slowEligible/admissionLevels/gate; DC admission and
initial chain state. Proof: 03 §10.1.

**bp.targetExtensionNegative.v1 — NEW — PROVED-paper (window checked).**
A valid protected outage has an honest FG target whose entry does not
extend B. At n=1,a=0,Δ=4,k=2,R=3,δ_t=6,
take B=P₁,T=40,b₀=56,b₁=84. At a₁=72 the source is P₃,
but the honest target is (1,g,false), with g≺B.
The entry is compatible with B, and honest outputs and HEADs retain B.
Dependencies: exact gate, fresh-source selector and height_pair rules.
Lean reuse: DC ChainState.initial and height_pair; SA gate and lease.
Proof: 03 §10.2.

**comp.leaseVsFinal.v1 — PROVED-paper (old fold); REVALIDATE (no-round).**
A Base execution at a≤f has a live honest lease and local S that
conflict with a later accepted F. Proof: 01 §11 N1.
Dependencies: handler definitions. Lean reuse: FG fold/client and SA gate.

**bp.noPhysicalPruning.v1 — PROVED-paper (old fold); REPLACED.**
A Base execution at n=4,a=f=1 changes HEAD and then S if inactive
block metadata is deleted while signed pools are retained.
Proof: replacement 01 §11.2 N2. HEAD differs at 720 and S at 800.
The current algorithm requires cumulative storage.
Dependencies: current read definitions. Lean reuse: G scores and gate.

**bp.slowWindowLoss.v1 — NEW — PROVED-paper (old fold); REVALIDATE (no-round).**
A Base execution has a saved evaluated result emptied by reconcile,
which changes a common ancestor's slow-admissible test from true to false.
The label stays evaluated. Proof: 01 §11 N3.
Dependencies: reconcile and slow test. Lean reuse: SA engine definitions.

**bp.healedAtResetNegative.v1 — PROVED-paper (old fold); REPLACED.**
At n=7,a=2,k=13,R=3, a reachable Rec_s(3) execution reorganizes at
q_(s*)+G+5Δ, so HEALED(q_(s*)) is false. Proof: replacement 21 N.1 (G+5Δ local delay).

**bp.weakFinalityNegative.v1 — NEW — PROVED-paper (old fold); REVALIDATE (no-round).**
For each R≥2 and 0≤δ_t≤R+1, an exact synchronous integer execution
with Rec_s(3), G=4RΔ, a=f=1 has no positive justification or finality.
Proof: 22 N4. It does not refute the δ_t=2R slice.

**bp.gapFinalityNegative.v1 — R=2 old-fold negative; window replay pending; R=3 OPEN.**
At R=2,δ_t=4,G=8Δ, one honest proposer per round can give no positive
justification or finality (22 N1; replay pending). N2 is REFUTED for the
window: Z retains U's bits, v's missing row is StaleUseful, and R7 gives
the honest slot-12 carrier q_F bits and finality of U. No R=3 witness remains.
At every R≥2, Δ_F′=(4R−6)Δ≥Δ_F gives κ′=R and β=P; four
consecutive honest openings give FGoodE_W. FF5 applies if these windows
recur under HEALING_INPUT (22 N2 corollary). A new R=3 negative needs
faulty openings. No G≤P premise is needed.

**bp.qualifiedFirstFinality.v2 — OPEN extension, outside the claim set (user, 2026-10-01).**
The κ=2 text is a sketch; it is not reviewed and no claim uses it. Under Recovery₂,
δ_t=2R, Rec_sT_W(g), G≤P and κ=2, first non-genesis finality of
height at least M+1 occurs before GST+B_best^F(g)+(2g+2)P+9Δ.
Rec_sT_W supplies the qualified healing search. This is not FF5's
arbitrary-trigger conclusion. Sketch: 22 QF2-W, FT-Tail-W and 21 H-time.
The v1 old-fold evidence is retained in the entry archive.

**bp.skipFirstFinality.v2 — OPEN extension, outside the claim set (user, 2026-10-01).**
The target is first high finality under Recovery₂, Rec_skipT_W(g), G≤P,
δ_t=2R before GST+B_H^F+(g+4)P+β+Δ. Old QF4 at δ_t=2R
does not prove the window target; its v1 evidence stays historical.
The stronger-gap route has only the sketch status stated in §2.5.

**bp.qualifiedGapNegative.v1 — NEW — PROVED-paper (old fold); REVALIDATE (no-round).**
For R=2,3 and g≥4, exact executions with n=4,a=f=1,k=2,
δ_t=2R,G=2P satisfy Rec_s(g) and never justify or finalize a
non-genesis entry. Proof with tick stamps: 22 N5 / 22 QF1. This does not
refute every version with other fixed parameters.

**bp.openingDeletion.v1 — RESTATE (no-round) — PROVED-paper (old fold); REVALIDATE (no-round).**
At R=2,3, deleting the first FGood opening fails even with recurrence
g=2,G=P.
Deleting its middle opening invalidates the original local deadline
T_(p+2)+9Δ, although the dropped extension 22 QF4 retains an old-fold argument for eventual first finality under
Rec_skipT(g) with G≤P.
Proof with tick stamps: 22 N6 / 22 QF3 and 22 N7 / 22 QF5.

```text
┌────────┬──────────────────────────────────────────┬────────────────────────────────┐
│ ID     │ Statement and scope                      │ Status / bound                 │
├────────┼──────────────────────────────────────────┼────────────────────────────────┤
│ 22 QF1 │ Rec_s(g≥4), unrestricted finite G; R=2,3 │ REVALIDATE (no-round)          │
│ 22 QF2 │ Rec_sT_W(g), G≤P; κ=2                    │ OPEN; dropped extension        │
│ 22 QF3 │ Delete first FGood opening; R=2,3        │ REVALIDATE (no-round)          │
│ 22 QF4 │ Rec_skipT_W(g), G≤P                      │ OPEN; dropped extension        │
│ 22 QF5 │ Delete either opening; R=2,3             │ REVALIDATE (no-round)          │
└────────┴──────────────────────────────────────────┴────────────────────────────────┘
```

**bp.sourceAgreementNegative.v1 — NEW — PROVED-paper (old fold); REVALIDATE (no-round).**
At a faulty opening, fresh sources can split in height despite an honest
next-slot proposal. Proof: 22 N3 using the complete N1 execution.
This does not refute the two-action common-entry theorem.

**bp.mixedLean.v1 — NEW — OPEN.**
A composed checked Lean run model derives the current FG-SA contract
without new axioms. Dependencies: all targets above. Lean source: new.

**bp.recoveryExtensions.v1 — NEW — OPEN.**
The remaining targets are uniform recovery/first-finality bounds at
δ_t≠2R and a healing bound that pays the initial 2L repair only once,
with later work bounded independently of L. The optimal uniform
healing bound is also OPEN. H.4-S/H.6-S prove shorter conditional
repairs; replacement 21 N.3 refutes unconditional pivot persistence
across events with a full L lifetime and 88 ticks after settlement
(`L−24 ticks` in N.3.4). It does not refute the fixed-R one-repair target. R=2 at δ_t=2R is proved
in 21–22 under Recovery₂. The remaining targets need new analysis.

### Open negative results (no-round)

The historical replacement runs use spec de183d7d; 21 §10 records their
window checks and delay bounds. REPLACED retains the stated claim; WEAKER
establishes the new bound. For each WEAKER numerical claim,
the old larger bound remains OPEN (not established, not refuted).

```text
┌──────────────────────┬──────────────────┬────────────────────────────────────┬──────────┐
│ Claim                │ Old bound        │ Run / window check                 │ Status   │
├──────────────────────┼──────────────────┼────────────────────────────────────┼──────────┤
│ Metadata deletion    │ HEAD/S change    │ 01 §11.2: HEAD 720; S 800          │ REPLACED │
│ Healing at reset     │ G+5Δ local delay │ 21 N.1: G+5Δ = 208 ticks           │ REPLACED │
│ Uniform healing      │ 46/58/62/78 Δ    │ 21 N.2.5: 38/46/54/62 Δ            │ WEAKER   │
│ First finality       │ 56/72/80/92 Δ    │ 21 N.2.6: 48/64/68/80 Δ            │ WEAKER   │
│ Private evidence     │ μ=4              │ 21 HG.N1: μ=4                      │ REPLACED │
│ Five changes / lower │ 77/93; 89/105    │ 21 HG.N2: five; 45Δ−1 / 61Δ−1 tick │ WEAKER   │
│ Later expiry wait    │ L lifetime       │ 21 N.3: L; wait 88=L−24 ticks      │ REPLACED │
│ B1 common Rec_FE(5)  │ 72/92/56/80 Δ    │ 22 B1: 60/80/48/68 Δ               │ WEAKER   │
│ Spec lower endpoints │ 46/74/62/90 Δ    │ 21 N.2.5: 38/46/54/62 Δ            │ WEAKER   │
└──────────────────────┴──────────────────┴────────────────────────────────────┴──────────┘
```

N.2 values use `(R,G/Δ)=(2,4),(2,8),(3,4),(3,8)`. B1 uses
`(2,8),(3,8),(2,4),(3,4)` and a common Rec_FE(5) premise. HG.N2
has five changes after GST, five after u₀ at R=2 and four at R=3;
it does not establish five charged repair waits.

**historical (pre-no-round rules).** The old status inventory is in
[00-outline-8c178793.md](archive/00-outline-8c178793.md), §3.5.

The second Opus report checks 03 §10.1/§10.2 and the listed 21 §10
events for the window. N.2 supplies 38/46/54/62 Δ lower endpoints,
with Δ_F≤2Δ at R=2 and Δ_F≤6Δ at R=3; see 21 §10 for scope.
Other REVALIDATE claims retain their old-fold arguments: 01 §11.1/§11.3
and 22 N1,N3–N7. Their complete window replay remains open. N2 is refuted.

Old-fold status (the no-round run has not been replayed with the window):

```text
┌────────────────────────────┬─────────┐
│ Claim                      │ Status  │
├────────────────────────────┼─────────┤
│ FGood c=z+1 local deadline │ REFUTED │
└────────────────────────────┴─────────┘
```

The FGood counterexample is in fg-noround-bcheck-opus-full §A; its run is
not ported to 22. The withdrawn deadline is T_(p+2)+9Δ at R=2,3.

## 4. Dependency graph

```text
Base / authentic origins / exact event order
  ├── carrier ── HEIGHT BRIDGE (height only)
  ├── window chainCertificates ── window store ── activeView
  │                 │                  ├── leaseOrigins ── reconcile ── nesting
  │                 │                  └── frame
  │                 ├── accountable / finalLock ── finalizedSafety (a≤f)
  │                 └── sourceDiscipline
  └── receipt + caps ── receiptCoverage ── sameLabel / transfer counts

Conditional Clean step at s (window concrete suppliers PORT PENDING):
  history below s ── sourceDiscipline ── cleanFrame
  cleanFrame + transfer counts + suffixWalk ── cleanTransfer(s)
  cleanTransfer(s−1) + honest batch ── genuine history at s
  sameLabel(s) + origin/event cases ── prefix invariant through d_s
  close the induction ── cleanHistory ── cleanSafety
      ├── comparison prefix D + scoreSuffix / reflection
      │     └── exactProposal + pending-label transfer ── cleanInclusion
      └── cleanPrefixTruncation + source origins + healthy batch
            └── pending gate + frame / F / reconcile event induction
                  └── outageCompatibility ── fastP1 / slowP1
  cleanSafety + cleanInclusion + fastP1 + slowP1 ── fj.armedSafe.v2

Recovery₂ (a≤f, C1, K_W≥2, R≥max(2,κ), δ_t=2R; strict gap G):
  finalLock + receiptCoverage ── phaseWitness / geometry
  phaseWitness + H.1–H.2 + IF.3,IF.5–IF.7 ── phaseSourcePermanence
  phaseSourcePermanence + two-lease repair + H.5 score transport ── phaseRepair
  phaseRepair + phaseSourcePermanence + rowPermission ── commonEntry
  commonEntry + phaseSourcePermanence + H.2 S2 + rowService ── renewedPromotion
  phaseRepair + HG.1 frontier service + HG.2 entry-slot maturity
    + phaseEvents + rowPermission + commonEntry + renewedPromotion ── progressAttempt
  progressAttempt + causal cut ── resetArrival ── postResetKeep
  postResetKeep ── universalLeases ── postResetService
  postResetKeep + universalLeases ── rawResultTransfer
  postResetService + rawResultTransfer ── localHealing ── uniformHealing
  postResetKeep + postResetService ── H2′ (all honest proposals)
  rawResultTransfer ── H5; H5 + unanimous count ── H6
  reset + T-stream + AC-output/H5/H6 + FG facts ── healingInput (21 H.22)
  H.22 + window origins + seeded induction ── 23 weakContinuationAvailable (FGSAClaims.weakContinuationLive field)
  H2.A/H2′/H3 + T-START/SMONO/EXACT/VOTE/WALK ── joint selection facts
  healingInput + I1–I7 + records/cap + joint selection facts ── finalityKernel
  healingInput H5/H6 + joint selection facts ── Q0 ── F7 / FT-Tail (QF extension only)
  QF2-W + Rec_sT_W + FT-Tail-W ── qualifiedFirstFinality (OPEN, dropped extension)
  QF4 / Rec_skipT_W ── skipFirstFinality (OPEN, dropped extension)
  healingInput + F1–F9/F8-W + Rec_FE_W or Rec_F4_W ── finality
  old FF3–FF4 + strong recurrence ── alternative finality (PORT PENDING)
```

The Clean cycle is a well-founded label/prefix induction, not two
whole-run theorems that assume one another. In particular, the result at
d_s can prove a fact about q_s retrospectively; the protocol never reads it
at q_s. See 02 §5 for the exact induction cuts.

## 5. Gaps and disagreements to carry forward

Stage 2a has old-fold paper proofs in 03 with inclusive public reads and the
pending-gate lease boundary. Its marked window ports in 02/03 are pending. Section 3.3 and the mapping include all
seven positive claims, the truncation lemma, and the two negatives.
The recovery and forward-window paper proofs are in 21–22; QF2/QF4 are
dropped open extensions. Strong alternatives, HP, leak, and general-timeout window ports are pending.
General-delay recovery and one-repair bounds remain open problems.

The final source check found implemented KFG Correspondence proofs, including
storeInv_on_block and storeControls_eq_fjControls. That earlier audit found that their placeholders had been replaced. The SA receipt-premise migration is also
implemented. The mixed run model remains open; no composed Lean certificate
is claimed.

The historical external registry and FG plan quoted optional physical pruning. The current
spec rejects it; replacement 01 §11.2 N2 changes HEAD at 720 and S at 800. Old exact vote-set equality,
undefined store field Σ.h_F, and old SA relay status are not used.

A direct application of G.ghost_covers_of_path_dominance to an FJ domain
misses its whole-path premise. The suffix lemma in 02 §4.1 repairs this proof
issue. N1–N3 prohibit unconditional local lease/S preservation, metadata
deletion (replacement 01 §11.2 N2; HEAD 720, S 800), and unrestricted slow-window preservation. None refutes Clean.

## 6. Historical review disposition (before the window pass)

Each finding below was checked against the frozen rules and the relevant
proof or Lean declaration before the edit. FIXED means that the stated
defect is corrected or, for a bound improvement, its retained slack is
explicit. No finding is disputed or deferred. The ids m9 and m10 do not
exist in the 00–02 review and are not counted.

```text
┌────────┬─────────┬───────┬─────────────────────────────────────────────────┐
│ Review │ Finding │ State │ Repair                                          │
├────────┼─────────┼───────┼─────────────────────────────────────────────────┤
│ 00–02  │ M1      │ FIXED │ Row time, GST, and inclusion window: 00; 22 I6  │
│ 00–02  │ M2      │ FIXED │ Post-GST task start and ≤ endpoint: 21 H.10     │
│ 00–02  │ M3      │ FIXED │ b=s* throughout                                 │
│ 00–02  │ M4      │ FIXED │ Phase repair is HEAD/fast-write service         │
│ 00–02  │ M5      │ FIXED │ Settlement, GST, and persistence premises       │
│ 00–02  │ M6      │ FIXED │ One H.22 export and exact dependency path       │
│ 00–02  │ M7      │ FIXED │ Finality quantified at t≥t* with full import    │
│ 00–02  │ M8      │ FIXED │ Duty-domain keep, S1–S3, and frame bounds       │
│ 00–02  │ M9      │ FIXED │ Row permission and qualified-opening ids        │
│ 00–02  │ m1      │ FIXED │ Relay includes asleep honest acceptors          │
│ 00–02  │ m2      │ FIXED │ Earlier results explicitly precede B            │
│ 00–02  │ m3      │ FIXED │ N3 Y₂ base and support lists are empty          │
│ 00–02  │ m4      │ FIXED │ Awake duties; record before emission            │
│ 00–02  │ m5      │ FIXED │ Genesis certificate height is 0 or 1            │
│ 00–02  │ m6      │ FIXED │ Exclusion uses deadline-state F                 │
│ 00–02  │ m7      │ FIXED │ Every Clean gate nonempty, starting at g        │
│ 00–02  │ m8      │ FIXED │ Current AC pin 3eb1889 includes b5f0d328        │
│ 00–02  │ m11     │ FIXED │ DC finalLock citation is fault-bounded only     │
│ 00–02  │ m12     │ FIXED │ Weighted accountability and root premise        │
│ 00–02  │ m13     │ FIXED │ Full HealingSurface pivot namespace             │
│ 00–02  │ m14     │ FIXED │ score_eq ht premise; support_subset field       │
│ 00–02  │ m15     │ FIXED │ uniqueJust_chains needs equal heights           │
│ 00–02  │ m16     │ FIXED │ SA/GridCO namespaces explicit                   │
│ 00–02  │ m17     │ FIXED │ Scope, witnesses, cuts, DAG, bounds, negatives  │
│ 21     │ M1      │ FIXED │ H.18 exports cross-node F_x⪯S_y                 │
│ 21     │ M2      │ FIXED │ H.14 labels every high selected source          │
│ 21     │ M3      │ FIXED │ H.11 exports the inclusive row cap              │
│ 21     │ M4      │ FIXED │ Identical post-gate cut in H.22 and 22          │
│ 21     │ M5      │ FIXED │ Exact raw result, C_fg, and definition of high  │
│ 21     │ m1      │ FIXED │ H.17 excludes the off-path high-F candidate     │
│ 21     │ m2      │ FIXED │ H.5 path premises and H.6 trunk step            │
│ 21     │ m3      │ FIXED │ Relay call has lower bound t≤t′                 │
│ 21     │ m4      │ FIXED │ First-failure event measure replaces labels     │
│ 21     │ m5      │ FIXED │ Spec citations; Recovery₂ marked as extension   │
│ 21     │ m6      │ FIXED │ O.2 records retained alignment/search slack     │
│ 21     │ m7      │ FIXED │ N.1: both b leases expire at 1040; G+5Δ †       │
│ 22     │ MAJOR-1 │ FIXED │ Both recurrence forms and g=3 forced honesty    │
│ 22     │ MAJOR-2 │ FIXED │ HP start cut, records, horizon, indexed entries │
│ 22     │ m1      │ FIXED │ Initialization and scope line citations         │
│ 22     │ m2      │ FIXED │ Cross-node clause exported by 21 H.18/H.22      │
│ 22     │ m3      │ FIXED │ Exact row-service statement retained as I6      │
│ 22     │ m4      │ FIXED │ FF1-A excludes actual run blocks above cap      │
│ 22     │ m5      │ FIXED │ FF7 uses the preceding opening label            │
│ 22     │ m6      │ FIXED │ Undefined historical labels removed             │
│ 22     │ m7      │ FIXED │ Unarchived replay count removed                 │
│ 22     │ m8      │ FIXED │ Spec R=3 refutation and general open scope      │
│ 22     │ m9      │ FIXED │ Rule citations at their proof uses              │
└────────┴─────────┴───────┴─────────────────────────────────────────────────┘
```

For 00–02 m17, the fixed subitems are R≥2 extension status, the explicit
g ranges, the first-round definition of r*, a selected C*, inclusive u₀,
separate weak/strong recurrence, phase label β, acyclic geometry reuse,
global frontier m, the reset cut and synchronous label, proved stage-2b
status, conditional general-delay recurring finality, and ids for both
negative executions. Same-time compatibility plus monotonicity already
gives the across-time HEALED form, so that equivalence needs no change.

The follow-up findings were checked against the current text and sources.
The † run remarks cite replacements: N.1 gives G+5Δ local delay;
N.2 gives 38/46/54/62 Δ healing and 48/64/68/80 Δ first finality.
The old larger N.2 bound remains OPEN (not established, not refuted).

```text
┌─────────┬───────┬──────────────────────────────────────────────────────────────────┐
│ Finding │ State │ Repair                                                           │
├─────────┼───────┼──────────────────────────────────────────────────────────────────┤
│ N-M1    │ FIXED │ Explicit Rec_s, StrongPair, StrongRec_w, Lit and Rec_c; g_h/g_f  │
│ n1      │ FIXED │ FL-W uses h_B; FL-T7 uses s_B                                    │
│ n2      │ FIXED │ H0 cites H.18/H.14 S2; H1 proves sources synchronous             │
│ n3      │ FIXED │ H.5 defines the selected path and retained pivot; proof aligned  │
│ n4      │ FIXED │ H.14 states duty-domain keep; outline pointers agree             │
│ n5      │ FIXED │ StrongRec_w requires g≥3                                         │
│ n6      │ FIXED │ N.1 G+5Δ; N.2 heal 38/46/54/62 Δ; FE 2/8/2/5 †                   │
│ n7      │ FIXED │ Active recurrence link at line 232; I6 has no stray sublabel     │
│ n8      │ FIXED │ HP premise 3 has no undefined event-history phrase               │
│ 00 ↔ 03 │ FIXED │ Seven PROVED-paper statuses, three local ids, exact reads/arming │
└─────────┴───────┴──────────────────────────────────────────────────────────────────┘
```

### Weaker-recurrence review disposition

The proof changes below are in this blueprint. The review is an edit
checklist, not a premise. No statement uses a report verdict as proof.

```text
┌─────────┬───────┬───────────────────────────────────────────────────────┐
│ Finding │ State │ Proof or change                                       │
├─────────┼───────┼───────────────────────────────────────────────────────┤
│ m1      │ FIXED │ 21 H.9: lower F, mixed batch label bound, H.7 renewal │
│ m2      │ FIXED │ 22 F8: FF2-C before lo≤d+2                            │
│ m3      │ FIXED │ R=2 honest openings imply FGood4 (=FGoodE)            │
│ m4      │ FIXED │ R=2 N1 replay pending; R=3 OPEN; N2 window refuted    │
│ m5      │ FIXED │ 22 B1-P compares the old strong finality premise      │
│ m6      │ FIXED │ 21 H.9-Q–H.11-Q; H.20 uses min(B_heal,B_H)            │
│ m7      │ FIXED │ 22 §6 keeps strong windows for general delay          │
│ m8      │ FIXED │ 22 FF5/FF6/FL-RF: W_F; FF7: 2W_F                      │
│ m9      │ FIXED │ 21 H.9 cites process_height_events at line 508        │
└─────────┴───────┴───────────────────────────────────────────────────────┘
```

OPEN: a necessary proposer pattern; unrestricted-gap Rec_s(g) at
δ_t=2R for g=3 at R=2, g∈{2,3} at R=3, and all g at R≥4
(22 QF1); both opening-deletion negatives at R≥4 (22 QF3, 22 QF5);
the smallest gap above P that permits a qualified negative; optimal
constants; general-delay healing; and composed Lean verification.
22 QF1–QF5 settle the broader qualified-recurrence and opening-deletion
claims stated above at R=2,3. For the window, QF2/QF4 are dropped open extensions at every κ.
Both remain OPEN at κ>2 with only G≤P.
These open statements do not weaken the proved sufficient results.
