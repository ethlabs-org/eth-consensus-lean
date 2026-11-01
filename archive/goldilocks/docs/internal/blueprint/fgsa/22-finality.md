# 22. Finality of the frozen FG-SA protocol

_Date: 2026-10-01. Status: paper proof with explicit imports; not a checked FG-SA Lean theorem._

Authority: [the current spec](../spec/fgsa-protocol.tex), SHA-256
`a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.

Window authority: spec 031a7f9f, `par:r6-window`, `alg:chain-full`,
`par:window-kernels`, and its status rows. Explicit older line citations
retain their archive numbering. [FW](../codex/reports/fdelay-window.md)
means the window report; [RD](../codex/reports/row-delay.md) means C1 and
case S of the row-delay report. Use the
[review fixes](../codex/reports/spec-window-fix-full.md) §§3–5 where they
qualify FW. Old concrete Lean declarations are not proofs of the new fold.

Historical spec line citations use the 4e85ff34 numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the earlier spec c1ea1db0 changed only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.
The no-round delta below uses frozen spec bf46ae7f; its citations name
that archive. Negative executions have the status stated in 00 §3.5.

Historical absolute spec line citations refer to the
[dbcb7f05 archive](../spec/archive/fgsa-protocol-dbcb7f05.tex).
The paired executions of 01 §6.5 have equal external traces, so all
output-level results and bounds transfer for that confirmation-walk change.
New H3 implies old H3 in the pair, which also transfers the conditional
general-delay results. This is not a transfer proof for the no-round or window delta.
Earlier reports supply questions to check; their verdicts are not premises.
PROVED means PROVED-paper: a full argument is present or explicitly
imported from the named reviewed source, within its stated scope. It does not assert a composed Lean proof.

With the full window `HEALING_INPUT(t*)`, K_W≥2, R≥κ, δ_t=2R,
and Rec_FE_W(g) or Rec_F4_W(g), new common finality is accepted before
`t*+W_W(g)`, where `W_W(g)=(g+2)P+β+Δ`. The local proof is F1–F9
below (FW §5, checked in both spec-window reviews). Its GST form adds
B_H^F and is **PROVED-paper**, using the revised 21 H.22/H-time.

QF2/QF4 are dropped open extensions, outside the claim set (user, 2026-10-01).
Finality liveness is FF5–FF7 under Rec_FE_W or Rec_F4_W, with
FGoodE_W/FGood4_W/Tail_W kernels.

Case S is Δ≤Δ_F≤2Δ, hence κ=2 and β+Δ=9Δ. Keep every old +2
proof below as a case-S result of the **old fold** unless a window proof
is expressly given. Local FGoodE/FGood4, Tail, and FF5–FF7
have window arguments. QF2/QF4 are dropped open extensions; strong alternatives, HP, and FL-*
need separate window ports. Changing the receipt offset alone is no proof.
For every κ, QF2/QF4 are OPEN extensions outside the claim set at δ_t=2R. The stronger-gap
route is a sketch, not reviewed. Historical negative runs and lower bounds
remain old-fold results until replayed with the window.

## 1. Execution model, notation, and proof boundary

Except in the safety lemma and the negative execution, assume a reachable
execution of the frozen spec, with these premises:

1. `n≥1`, a static faulty set of size `a≤f=⌊(n−1)/3⌋`, authentic signatures,
collision freedom on full recursive named proposals in the delivered/held/ancestor run scope,
and strictly increasing parent slots. Every honest
   validator is awake after GST. Thus `h=n−a` honest seats and identities
   participate. State is produced by actual protocol events from genesis;
   arbitrary damage means arbitrary permitted scheduling before GST.
2. Integer `Δ_F≥Δ>0`, `R≥max(2,κ)`, `K_W≥2`, `k≥2`,
   `L=(4k−1)Δ`, and C1 strict delivery
   and dependency-ready receipt after GST. Use DC's receiver exclusion for
   blocks. A handler call is not an unconditional acceptance guarantee.
   Blocks and HEADs use Δ; FG rows use Δ_F. Both deadlines include
   pre-GST sends and sleeping receivers. Relay starts at acceptance.
   Complete block bodies, including rows, still use Δ (01 §10.3).
   Honest votes and rows cannot be forged or equivocated. Each honest
   identity runs one FG action per round and sends at most one new row.
   Rows have no round; send-once uses the durable sent-content record.
   A sent row has a nonempty height pair, and carries a finality pair only
   at a strictly later height h>h_f. No finality-only row is sent.
3. The spec's tick and receipt order holds. Records persist. An honest
   proposer occurs at a slot with `t<t_s≤t+G` for each permitted trigger
   `t≥GST`, with finite `G≥4Δ`. Healing uses this gap. FGoodE supplies the early
   justification carrier; FGood4 is its special case.
4. All times and deliveries used by a conclusion lie in the execution
   horizon. Recurring liveness without an endpoint assumes an unbounded
   post-GST horizon. A finite-horizon theorem asserts only the instances
   whose displayed deadlines fit inside that horizon.

Write `ht(B)=σ[B].h`, `ent(B)=σ[B].T_h`, and `B⪯C` for ancestry.
Write `fh_i(t)` for the certificate height of accepted `F_i(t)`;
`fh_i` is read from the accepted certificate carrier: genesis has
height 0 initially and can later be finalized at height 1. Its state
height is always `ht(genesis)=1`. Do not identify these quantities. For a non-genesis entry at height `y`, `ht(E_y)=y`.

\[
 t_s=4s\Delta,\quad v_s=t_s+\Delta,\quad e_s=t_s+2\Delta,
 \quad z_s=t_s+3\Delta,\quad q_s=t_s+5\Delta,\quad d_s=t_s+6\Delta;
 \qquad P=4R\Delta,\quad T_r=rP,\quad a_r=T_r+6\Delta.
\]

Put `κ=ceil((6Δ+Δ_F)/(4Δ))`, `β=4κΔ`, and `ε=β−8Δ`.
Thus `a_r+Δ_F≤T_r+β≤T_(r+1)`. Row-ready carriers have slot at
least rR+κ; their strict block-receipt tail is β+Δ. The timeout domain
is δ_t≥0, but Recovery and all GST bounds here use δ_t=2R.

### Recurrence forms

The unsuffixed predicates and +2 proofs below retain the case-S old-fold
meaning. The current window predicates are stated after them.

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

FF5–FF7 use forward Rec_FE or Rec_F4 windows. FF5-S also retains the
strong recurrence alternatives. General-delay FL-RF uses strong windows.

### Receipt-ready window predicates

Use the same q≥1, T_q≥GST, and complete receipt-horizon conventions.

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

At κ=2 the predicates coincide with the old ones. This equality does not
identify the two transitions. The kernel below uses the window at κ=2 too.

### H.22 — One exported healing interface — PROVED-paper

**Mirror of 21 H.22.** The package below is byte-identical to its owner.
The producer uses 21 W1–W3, HG.2–HG.6, H.9(b), and H.21.

<!-- BEGIN HEALING_INPUT -->
A read is indexed by an event prefix as well as by its integer time.
A public gate boundary denotes the cut after all honest gate ticks at
that time. Each node runs its tick before its same-time receipts. Thus
`HEALED(d_s)` starts at that completed gate cut; it makes no assertion
about a partial execution of the boundary's ticks. Include every receipt
state after that cut in the suffix. At other integer times use the
inclusive event-prefix state. This convention also defines the service
read `S_x(d_s)`. No message processed at a strict cutoff contributes to
that cutoff. A Lean model with pre-tick reads must use the explicit
post-gate event cut, not substitute its pre-tick time accessor.

`HEALED(t*)` means: all honest outputs at each suffix event read are
compatible; each honest local `S` is monotone on the suffix; local
`F⪯S` holds; and every honest proposal `Q` at `t_v≥t*` satisfies
`Q⪯S_x(d_v)` at every honest node `x`, where `d_v=t_v+6Δ`.

`HEALING_INPUT(t*)` means `HEALED(t*)`, H0–H6 (including H2.A and H2′),
and T-ROWS below, with one tuple of witnesses `(r_G,u₀,M,r*,s*,b,C*,u,Q*)`. A **high**
source, row,
entry, or certificate has height at least `M+1`.

`μ=μ(run,GST)` is a function of the run and GST, not an existential
witness field. It is defined in 21 H.11 as
`max({1} ∪ {height of an honest row whose source vote time is <GST})`.
All uses of μ, including H0 and the search lemmas, use this same value.

The package has four parts: the common witness, the T-stream into FG,
the AC-output service used by the composition, and the FG foundations.
The parts use the same event reads. This is a composed export, not a
claim that AC and FG have separate unconditional healing theorems.

**Map from spec 4e85ff34 to the adopted spec c1ea1db0.** The table
maps the clauses of 4e85ff34 §Healing interface to the blueprint names
used in the adopted spec. The witness tuple and event cuts are the same.

```text
┌───────────────────────────┬───────────────────────────────────────────────────────────────────┐
│ Spec clause               │ Blueprint clause                                                  │
├───────────────────────────┼───────────────────────────────────────────────────────────────────┤
│ Healing from t*           │ HEALED(t*)                                                        │
│ H0: cut and reset         │ H0, with the same inclusive cut and witnesses                     │
│ H1: actual sources        │ H1                                                                │
│ H2: HEAD coverage         │ H2.A, HEAD clause                                                 │
│ H2: proposal parent       │ H2 (T-XFER)                                                       │
│ H2: output coverage       │ H2.A, output clause                                               │
│ H2, all three clauses     │ H2 ∧ H2.A, including faulty openings and finality advances        │
│ H2′: proposal HEADs       │ H2′                                                               │
│ H3: exact service         │ H3: exact HEAD, raw result, guard, fast write, S, and opening     │
│                           │ C_fg                                                              │
│ H4: output history        │ H4: common cut, chain, local monotonicity, and cross-node F       │
│                           │ coverage                                                          │
└───────────────────────────┴───────────────────────────────────────────────────────────────────┘
```

The adopted spec c1ea1db0 implements H2 and H2.A, T-ROWS, H5, H6,
and the FG foundations in this `HEALING_INPUT` package. The interface
alignment is complete; see
[CHANGES-4e85ff34-to-c1ea1db0](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md).

**Witness part.**

**H0 — inclusive cut and reset.** `r_G` is the first action round at or
after GST; `u₀=a_(r_G+2)` includes all events at that time;
`M=max_x H_x(u₀)` over honest nodes. Every honest height row emitted
through `u₀` has height at most `M`. Also `μ≤M`, where `μ` is the
maximum of 1 and the heights of honest rows whose source vote time is
before GST. `GST+2P≤u₀<GST+3P`. The first action round that emits an honest row
at height `M+1` is `r*`; `s*=r*R`, `b=s*`, and `C*` is one actual
fresh source of such a row. `ht(C*)=M+1` and `v_(s*)≥GST`.
The first honest proposal slot `u≥s*+2` has block `Q*`; `t*=d_u≥GST`
and `C*⪯Q*`.

**T-stream part — source candidates and carrier chains.**

**H1 — actual sources.** A source is the block selected by `get_fg_vote`
from the action's opening-label `fastWrite` set, with a live lock in
the full filtered tree. Its label `s` is an opening label and its action
is `d_s`. This definition includes selected sources whose action sends
no row. Every high honest source has label `s≥s*`.
All high honest sources in the whole execution prefix and continuation
are pairwise compatible and compatible with `C*`.

**H2 — carrier-chain transfer (T-XFER).** For every high honest source
`K` of label `s`, every honest proposal `Q` at slot `v≥s+2` satisfies
`K⪯parent(Q)`. This includes faulty opening labels, persists under
finality advances, and applies in particular to `C*`.

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

**AC-output part — service facts used by the joint functions.**

These facts include AC HEAD evidence, which the joint selections use
directly (22 §2.1). H2′ and the HEAD clauses of H2.A and H3 are AC
services to the joint selections. They prove the composition services
of 01 §1.2; they do not add HEAD votes to the T-stream. T-VOTE is a
composition service. `S` is `latest_confirmed`. T-START, T-SMONO and
T-EXACT connect this local output with `live_root` and the joint
finality-head selection.

**H2.A — source support and output transfer.** For every high
honest source K of label s, all honest HEADs at labels `i≥s+1` cover K,
and every honest output from `d_s+4Δ` covers K. Both clauses include
faulty opening labels and persist under finality advances. They apply
to C*. H2.A is the support proof for H2. Its HEAD clause is also used
directly by F8, Q0 and QF4 S2. It does not replace the carrier-parent
conclusion.

**H2′ — honest-proposal HEAD coverage.** For every honest proposal `Q`
at slot `v≥s*+2`, all honest HEADs at labels `i≥v+1` cover `Q`.
This holds even when `Q` is not an FG source, and persists under
finality advances.

**H3 — exact service.** For every honest proposal `Q` at slot `v≥s*+2`,
all honest slot-`v` HEADs equal `Q`. At `d_v`, each honest raw genuine
result is `Q`, its whole-result guard passes, it fast-writes `Q`, and
its post-gate `S` equals `Q`. If `v=rR`, every honest action at
`a_r=d_v` selects `C_fg=Q`. These conclusions therefore apply to every
honest proposal at `t_v≥t*`.

**H4 — output history.** At the cut `t*`, every honest `S` equals `Q*`.
At all later event reads, honest outputs form one chain and each local
`S` is monotone. For every suffix read `t≥t*` and all honest `x,y`,
`F_x(t)⪯S_y(t)`. Include silent and faulty proposal labels and all
assignments to `S` by reconciliation.

H5 and H6 below are interface clauses. They are distinct from healing
lemmas H.5 (lower F moves) and H.6 (two-lock repair).

**H5 — raw-result transfer.** Under the Recovery₂ premises of 21 §2,
every nonempty honest raw genuine result C at label `j≥s*` has no
conflicting live lock after release at q_j.
All honest HEADs at labels `i≥j+1` cover C; all honest proposal parents
at slots `v≥j+2` cover C; all honest outputs from `d_j+4Δ` cover C.
This includes results with support below τ and results whose guard
was not assumed to pass. The lock claim concerns the release state;
the result is evaluated at d_j and is not read by the earlier release.

**H6 — unanimous gate service.** Under the Recovery₂ premises of 21 §2,
let `j≥s*` be synchronous. Suppose every honest label-j HEAD covers a
non-genesis block D, and `F_x⪯D`
at every honest gate read d_j. Then at each such gate the raw result
is nonempty and covers D, its whole-result guard passes, and D is in
`fastWrite[j]` with a live lock of deadline at least `d_j+L>d_j`.
No honest proposer at j is needed. This is an AC gate statement; it
does not assert membership in the FG filter or selection as C_fg.

**FG part — common foundations.** The package uses immutable chain
states, certificate provenance, finalized crossing, monotone F, and the
live-cache FJ frame from IF.1–IF.4 and W1–W3 (01 §§3–4 and §8).
Each selected window entry has its own target and finality QCs.
Pruning lower entries creates no QCs; W3 gives each finalization's
earlier target source, including when the entry is older than J. These are proved
FG/substrate facts under the stated quorum premises, not extra healing
or finality-liveness assumptions. The FG client reads the source and
the immutable `(h_j,J,h_F)` of the joint finality head. H1 supplies
the high-source history for the record induction in 22 FF2. No claim
equates that head with C_fg or supplies a high finality certificate.

**H-time — theorem, not a premise of the local finality kernel.** Under
Recovery₂ with C1, K≥2, R≥max(2,κ), `δ_t=2R`, and the strict
honest-proposal gap `G` alone,
there exists this `t*` with `HEALING_INPUT(t*)` and
`t*≤a_(r*)+Γ+4Δ<GST+B_H^F`, where
`Γ=4Δ ⌈G/(4Δ)⌉`, `L=(4k−1)Δ`, `P=4RΔ`,
κ=ceil((6Δ+Δ_F)/(4Δ)), β_F=4κΔ, ε=β_F−8Δ, and

```text
B_H,F^(2) = max(12L+12Γ+12P+49Δ+2ε, 8L+10Γ+14P+19Δ).
B_H,F^(1) = max(6L+12Γ+12P+61Δ+2ε, 4L+10Γ+14P+27Δ)  (requires k≤2R+1).
B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
```

Both eligible bounds concern this same witness tuple. The strict
integer deadline also gives `t*≤GST+B_H^F−1`.
H.18 also gives `t*=d_u≤a_(r*)+G+4Δ` using the original G-gap.
With an additional qualified-opening search bound `g_h P`, the same
`t*` is before `GST+min(B_heal(g_h),B_H^F)`, where
`B_heal(g_h)=6ρ+(23+13g_h)P+G+64Δ` and `ρ=2L+G+8Δ`.
For another timeout `δ_t`, a local finality theorem must assume the
package for that timeout; H-time is not proved for it here.

<!-- END HEALING_INPUT -->

**Producer proof — PROVED-paper from revised 21 W1–W3 and H.22.**
H.11 proves H0 through the reset source and inclusive row cap.
For H0's last sentence, H.18 chooses u,Q* and t*=d_u≥GST; H.14 S2
gives C*⪯parent(Q*)⪯Q*. H.14 proves H1's source-label bound.
Every high source has label s≥s*, and v_(s*)≥GST, so v_s≥GST:
every high source is synchronous. H.13 therefore applies and gives
their compatibility, including compatibility with C*. H.14 with H.2
gives H2 (S2) and H2.A (S1 and S3). T-ROWS follows from the selector
and receipt proof in 01 §1.1, with effect-specific persistence from
21 W2 and 01 §3.1.

For H2′, fix an honest proposal Q at slot v≥s*+2. H.17 gives a
successful fast write of Q at every honest gate d_v. Its label v is
at least b=s*, so Q is a protected fast body in H.14. H.14 applies
H.2 S1 and gives every honest HEAD at label i≥v+1 coverage of Q,
starting at q_v=v_(v+1). Its kept-path and finality-coverage clauses
preserve this conclusion at every later duty. This proof uses actual
fast writes, not the opening selector, so Q need not be an FG source.
The first HEAD, at q_v, is before d_v. Its input to H.1 is H.17's h
clean slot-v votes for Q, which exist at q_v; the write at d_v is not
read there. Thus no event prefix needs to contain d_v.

H.17 proves every field of H3, including
the raw result and the opening selector. H.18 proves HEALED and H4,
including cross-node finality coverage and previously accepted finality.

H.16 proves H5, including the no-conflicting-lock statement in its
proof at q_j. For H6, F monotonicity puts every earlier receiving F
below D. Each honest vote is sent at `v_j=t_j+Δ`; its signer already
holds its head. Strict receipt and IF.5 deliver all h votes and their
head paths before `t_j+2Δ`, so they are in each early pool. No honest
signer can equivocate. For each path block B with `F⪯B⪯D`,
`p(j,B)≥h≥τ` and `2h>n≥D_j`. Here D_j is the gate denominator,
not the block D. Each path child has honest score at least h and each
off-path child at most a<h. The final eligibility test also applies to
F, genesis included: `p(j,F)≥h`, so `2p(j,F)>n≥D_j` and F is
eligible. Thus the confirmation walk from F has a nonempty raw result
C⪰D. This is the count and walk argument of H.2, without an assumption
that its transfer conclusion holds.
Apply H5 to this C. No lock conflicts with it after q_j. No gate runs
strictly between q_j and d_j; expiry, release, and reconciliation can
only remove locks there. Its guard therefore passes. The prefix loop
writes D because it lies on C's path, remains active, and has at least
τ surviving early supporters. Its deadline is at least d_j+L.
This proves H6 without an FG source-selection or finality theorem.

H.18 also gives the local deadline. Add H.11's strict reset bound to get
H-time, as in H.20; H.11-Q gives its optional smaller bound. No finality liveness fact from 22 is used. ∎

**Dependencies.** H2′ uses H.17 (exact fast write) and H.14 with
H.2 S1 (kept-path transfer). Their preceding proofs use IF.1–IF.7 and
H.1–H.13, plus H.15 in H.17; no result from 22 is required. For the
whole package, the direct proof references are H.2, H.11, H.13,
H.14, H.16, H.17, H.18, and H.20, plus IF.1–IF.5 and 01 §1.1;
H.21 checks the range R≥max(2,κ). The complete
preceding proof chain is IF.1–IF.7, H.1–H.18, and HG.1–HG.6. The optional smaller
time bound also uses H.9-Q–H.11-Q. In outline ids the package depends
on resetArrival, postResetKeep, universalLeases, rawResultTransfer,
postResetService, and localHealing. H2′ is supplied by postResetService
and postResetKeep; rawResultTransfer supplies H5, and H5 with the
H.2 count supplies H6. It is also used in localHealing.

`HEALED` alone does not imply H0–H6, including H2.A and H2′. This single export
replaces the separate RESET_HISTORY package. Its outline id is `bp.healingInput.v2`.

## 2. Imported foundations

Each fact below is stated independently so that the foundation documents
can reconcile their statements with this file. Proofs refer to current
rules. “Proved” means a paper proof, not an existing mixed Lean instance.

### I1. Quorum arithmetic — PROVED

For `q=⌈2n/3⌉`, `τ=⌈n/2⌉`, and `a≤⌊(n−1)/3⌋`,
`h=n−a≥q≥τ>a`, `h>2a`, and `2q−n>a`. Two subsets of `V` of size at
least `q` intersect in at least `2q−n` identities. Every such quorum has
an honest member.

**Proof.** `3a≤n−1`, so `n−a≥⌈2n/3⌉` and `n−a>2a`.
`q≥τ` follows from `2n/3≥n/2`. Also `2a<n`, hence `τ>a`.
Write `n=3m,3m+1,3m+2`. Respectively `(q,f,2q−n)` is
`(2m,m−1,m)`, `(2m+1,m,m+1)`, or `(2m+2,m,m+2)`. Thus `2q−n>a`.
Finally `|A∩B|=|A|+|B|−|A∪B|≥2q−n`, and `q>a` excludes an
all-faulty quorum. The assumptions include `n≥1`, so the first case
starts at `m≥1`.

### I2. Chain certificates and exact entries — PROVED

In every reachable window chain state, height starts at 1, never decreases,
and increases by at most one per block. A crossing at y has q distinct
matching progress identities for that chain's height-y entry. A justification
(y,E) has q distinct exact target identities. Every positive finalization
(x,X) has an earlier target justification of that same pair and q distinct
signed finality pairs exactly (x,X). It need not finalize the latest J.
Always h_F≤h_j<h and F⪯J⪯T_h. The ordered window has at most K_W
entries, with h_F<j_0<…<j_m≤h_j. At fixed height, the entry is fixed.
Height bits persist until that height is left. Entry bits persist until
that entry is finalized/pruned or capacity-evicted; mixed progress leaves
them unchanged. Capacity eviction is not finality coverage.

**Proof.** Apply the chain induction and certificate extraction in 01 §3.
Each entry is born empty at an actual target QC. The fold only adds exact-
pair identity bits to existing entries, independently of height matching.
The greatest ready entry has its own quorum and prior target QC. Deletion
below it needs no other finality QC. Target consumption appends an empty
entry after finalization, so rows are not applied to that new entry.
The current-height target/progress tests and the single advance are unchanged;
01 HEIGHT BRIDGE proves their geometry on fixed block data. Monotone
height prevents a deleted entry from returning. Authentication lifts each
bit witness to its signed occurrence. No latest-only bit history is used.

DC port: paper [consensus.tex:2229][dc-paper-transition]; Lean
`Protocol.process_attestation`, `progReady`, `advance_height`, and
`process_height_events` in [ChainState.lean:423][dc-state]. Use named,
entry-bound timeouts, unit weights, and set `nj=false`. Remove the NJ
assignment, not the exact-entry checks or finality-first order.
Registry: `bp.chainCertificates.v2`.

### I3. Honest anti-slashing and accountable safety — PROVED

For every `δ_t≥0`, every `R` for which the execution is defined, and
without synchrony or recurrence, honest emitted rows give neither E1 nor
E2 evidence. With RootInjectiveOn on their two certificate-carrier chains,
two conflicting finalized checkpoints expose at least
`2q−n` distinct slashable identities. Consequently finality is compatible
across all honest reads if `a<2q−n`, in particular if `a≤f`.
Premises for the evidence bound: Base, RootInjectiveOn on the two carrier
chains, any δ_t≥0, any a, no synchrony. For honest accepted reads, the
carriers are honestly held; ancestor-closed RD2 scope supplies this premise.

**Proof.** Fix a validator and a height. Its first target is write-once.
After that target, `height_pair` can repeat it, time out, or abstain; it
cannot target a different entry. A finality pair requires no earlier
timeout and requires an empty or matching target and lock. Its record
then locks that entry. Future height pairs at this height can only repeat
the locked target or abstain. A timeout cannot first appear after a lock:
the earlier-timeout branch is false when the lock is first written and
the lock branches do not write a timeout. Within a single row, the newly
chosen finality pair overrides the lock before the height pair is chosen.
Thus no temporal ordering, including a single-row ordering, permits E1;
write-once targets exclude E2. This is induction on `record_attestation`
at current spec lines 1718–1732, using lines 1653–1716. In the adopted
send-once client, suppression makes no record or emission, and stripping
a finality pair writes no lock. The same induction therefore applies only
to released rows and their atomic record writes; neither step adds evidence.

Let conflicting finalized entries have certificate heights `x≤y`.
Genesis cannot conflict. If `x=y`, their distinct entries have two target
QCs by I2. Intersect their identity sets: each common identity signed two
different targets at the same height, which is E2. If `x<y`, the chain
that finalizes at `y` crossed height `x`. Its entry at `x` differs from
the first finalized entry, since the chains conflict. Intersect that
crossing's progress QC with the first checkpoint's finality QC. A common
identity signed a timeout at `x` or a different target at `x`, and also
signed finality for the first entry. This is E1. I1 gives the evidence
count. Honest compliance and `a<2q−n` exclude the conflict. No step reads
timeout maturity or a fork-choice rule.

DC foundations: paper [lines 718–729][dc-paper-evidence] and
[lines 2139–2209][dc-paper-client]; Lean
`create_attestation_no_self_E1`, `no_timeout_against_finality`,
`e2Fields_false_of_admissibleCore`, and
`justification_unique_per_height_slashable` in the validator-client
proofs. The cross-height extraction is
`NamedFinalizationBridge.finalized_preceq_of_height_lt`
[FinalityComparison.lean:50][dc-crossing]. Changes: remove the safe-field
projection, use fixed unit identities, and replace source selection only.
Neither SA reconciliation nor FJ can alter a signed row or chain certificate.
I2 supplies these certificates also when the greatest ready entry is older
than latest J. The E1/E2 cases and evidence bound are therefore unchanged
for the window (FW §4; both spec-window reviews C3).
Registry: `fg.accountable.v2`. This is the safety theorem used below.

### I4. Finalized crossing — PROVED

Assume I3's honest compliance and `a<2q−n`. If an honest node holds
a block `D` with a finality certificate `(x,F)` at read e, every block
`W` that an honest node holds at a read `e′≥e`, with `ht(W)>x`,
extends `F`. This includes blocks outside an active view (01 R-XING).
The certificate proof uses authenticated row origins.
Both carriers are honestly held; RD2 scope supplies RootInjectiveOn.

**Proof.** For `x=0`, `F` is genesis. For `x>0`, I2 supplies a height-`x`
crossing on `W`'s chain. If its entry is `F`, ancestry gives the result.
If it is not `F`, intersect its progress quorum with `D`'s finality quorum.
Each common identity supplies E1 as in I3, contradicting the fault bound.
This proves the statement before any network-delivery argument.

DC port: the certificate rules at [paper line 2229][dc-paper-transition]
and the declaration [FinalityComparison.lean:50][dc-crossing] just named.
The proof does not need NJ, grades, or a lower bound on `δ_t`.
Registry: `fg.finalLock.v3` (accepted-finalization threshold; 01 §8.2).

### I5. Store, active view, nesting, and lock bounds — PROVED

At every reachable local read: `Σ.T` is cumulative and parent-closed;
computed block states are immutable; `F` advances only to a descendant;
`hmax` is the greatest admitted height; `F⪯J`; `F⪯S`; live lock targets
form an ancestor-closed chain and each target precedes `S`. Reconciliation
changes only the specified SA fields and does not change `T`, states,
pools, stamps, `Λ`, or `hmax`. Its saved confirmation deletion preserves the
evaluated label. Ancestor closure for locks excludes genesis, which has
no lock write.

**Proof.** Use the window derive and store induction in 01 §4. These
are induction invariants of the same handler order (current spec lines 1012–1204). `on_block` tests `F⪯B` before state computation and before
unpacking. It adds one block with an admitted parent and deletes none.
`update_finality` first raises `hmax`, then conditionally replaces `J`
with a greater compatible justification, then accepts only a descendant
`F'⪯J`. No other operation writes those caches. Every `F` assignment and
every gate ends with the output normalization, so `F⪯S` is preserved.

For locks, initially the set is empty. Expiry and release delete only.
A successful gate checks all live targets against its whole result `C`.
Old and new targets are then comparable; new targets are prefixes of `C`.
If `C⪯old S`, `advance` keeps `S`; otherwise it sets `S=C`. In the latter
case an old target extending `C` would force `C⪯old S`, a contradiction;
thus all old targets precede the new `S`. Prefix writes give each ancestor
at least the descendant's deadline. Release against an ancestor implies
release against its descendant. Hence expiry and release preserve ancestor
closure. Reconciliation deletes incompatible targets. If normalization
sets `S=F`, a surviving target, formerly below old `S`, must precede `F`:
a target extending `F` would imply `F⪯old S`, which would suppress the
assignment. This proves the lock bound after the assignment too.

The explicit reconciliation loop gives the remaining field claims. The
SA confirmation walk reads `act(Σ)`; FJ reads the cumulative tree. A
carried vote on an inactive admitted proposal remains in the HEAD merge.
An inactive vote head cannot support a candidate above `F`, but its signed
vote still contributes participation and equivocation. These last facts
follow from the ancestry test, not from deletion of the proposal.

DC port: [paper lines 1720–1737][dc-paper-admission] and
[1768–1784][dc-paper-acceptance], with SA normalization and reconciliation
in place of grade clipping. This lemma asserts no unconditional monotonicity
of `S` during damage. Registry: the store and nesting part of
`fg.accountable.v2`; compare `comp.leaseVsFinal.v1`, which is refuted.

### I6. Honest-row receipt and coverage — PROVED

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

**Proof.** C1 gives strict receipt, including old sends and sleepers, with
no row exclusion. The pool has no age or identity quota. Apply the R6/R7
selection and exact-row exclusion proofs in 01 §1.1 and I2's separate bit
persistence laws. The optional 1+K_W selection has the same bit union
and marker reads as full inclusion. A new missing finality bit still needs
a selected signed row from that identity. Stale carriage has no height
effect. This proves row-or-bit coverage, not new emission at each action.

DC port: receipt in [paper line 203][dc-paper-receipt], and proposal
inclusion at [line 2041][dc-paper-inclusion]; Lean `NamedReceipt.excludes`,
`PartialSynchrony.relay`, and `actionAttestationAt_coveredAtProposal`
in [RawHeightCoverage.lean:1011][dc-coverage]. Replace grades by the
explicit source and path premises, use full-row deduplication, and use
unit identities. This asserts coverage of honest rows only.

### I7. Exact quorum consumption — PROVED

Let a child D have parent state of height y, entry E, and nj=false.
If every honest identity has a target bit already present or a selected
exact target row (y,E,false), D justifies E and has height y+1.
Separately, let (z,K,Q_i) be a retained parent entry. If every honest
identity has its bit in Q_i or supplies that exact finality effect in D,
then the finality test gives K⪯F_D and h_F(D)≥z. Exact equality is not
required: a higher entry can also be ready. These conclusions hold for
every δ_t. Prior finality coverage is a separate already-covered case.

**Proof.** During the fold all keys stay fixed and bits only increase.
Thus each specified set contains h≥q honest identities. The greatest ready
entry has certificate height at least z and, by chain order, extends K.
It finalizes before pruning and before the target test. The target quorum
then writes (h_j,J)=(y,E), appends (y,E,∅), keeps the newest K_W entries,
and advances once, clearing only height bits. It cannot undo F_D. If the
higher ready entry did not exist, the write is exactly (z,K). Union of bits
also proves independence from row order and repeated rows (01 §3.1).

DC port: [paper lines 2247–2278][dc-paper-transition]; Lean
`namedJustifiedAt_of_targetQuorumCoveredByChild`
[W4FKChainJustification.lean:185][dc-justify] and
`namedFinalizedAt_of_finalityQuorumCoveredByChild`
[W4FKChainFinalityWrite.lean:177][dc-final-write]. Their quorum coverage
premises are discharged pointwise here; `nj=false` is unconditional.
Those old exact-write declarations are proof patterns only. The window
supplier must prove coverage and a height lower bound, not exact equality.

### I8. Uniform-vote walk — PROVED

At a full-tree proposal or action read, suppose a block `Q` is in the
filtered tree, the live root precedes `Q`, all `h` honest votes at the
read's label resolve to `Q`, and no admitted proper descendant of `Q`
exists. Then the selected head is exactly `Q`.

**Proof.** At a strict ancestor of `Q`, the child on its path has score
at least `h`. A conflicting child has score at most `a`, since only faulty
seats can support it or equivocate. Thus the path child has strictly
greater score. It passes the relative-majority test because the total
number of participating seats is at most `n=h+a<2h`; if the band exempts
this child from that test, it remains eligible. Full-tree viability of
`Q` makes every intervening path child viable, and the root constraint
retains it. Induct on the finite parent distance from the live root to
`Q`. Each step chooses that path child. At `Q` there is no proper
descendant, so the walk stops. This also covers live root `Q`.

SA check: `AvailableChain.GridCO.honest_proposal_heads_of_ordinary_parent`
[ProposalHeads.lean:19][sa-heads] has explicit parent, root, and transport
premises; it is not an unconditional FG theorem. The exact-gate counterpart
is `AvailableChain.GridCO.clean_honest_proposal_repair` [CleanInclusion.lean:143][sa-clean].
The present lemma discharges its own full-tree premises; H3 supplies the
separate frozen-HEAD service. The spec's full live-root rule is retained.

### 2.1 Channel boundary and direct HEAD uses

The minimal AC→FG values are source candidates/C_fg and the carrier
chain, as defined in 01 §1.1. H2 states `K⪯parent(Q)` from slot s+2;
T-ROWS states row inclusion on that chain. I6 proves its receipt and
matching-bit use. Neither value identifies the finality head or the
pending J on a later carrier parent. Those are joint selections. The
composition→FG values include the finality-head triple `(h_j,J,h_F)`
even when C_fg is absent, and the selected carrier parent (01 §1.1).

The composition therefore supplies T-START, T-SMONO, T-EXACT, T-VOTE
and T-WALK from 01 §1.2. `S=latest_confirmed` bounds a live start at an
earlier or later read, including a gate between proposal and action.
T-WALK includes coverage and unsupported-child exclusion. I8 is only
its exact-head case; I8 alone does not prove F6 or F8.

The proofs use HEAD evidence directly in the following joint
selection steps. These are exceptions to a claim that source candidates
and carrier transfer alone prove the whole kernel. H2′ and the HEAD
clauses of H2.A and H3 are AC services to the joint selections;
they are not additional FG wire inputs. T-VOTE is a composition service.

```text
┌──────────────────┬───────────────────────────────────────────────────────────────────┐
│ Step             │ Direct HEAD use and the joint function it proves                  │
├──────────────────┼───────────────────────────────────────────────────────────────────┤
│ FF1              │ Exact H3 votes give τ early support and the fresh source. With I8 │
│                  │ they give Q1’s parent, action head Q1, and Q2’s parent. No        │
│                  │ proposal occurs between Q1’s HEAD and the action.                 │
│ F6               │ H2′ or H3 covers X_D at label z+1. T-VOTE and T-WALK give pending │
│                  │ J=U at the action; no honest proposer at z or z+1 is needed.      │
│ F7               │ H3 gives source X_D if c=z; H2′ and Q0 give height d+2 if c<z.    │
│ F8-X (old fold)   │ H2′/H3 keeps the path; H2.A puts new source entries on it. T-VOTE │
│                  │ gives honest participation. Vote origins and T-WALK’s             │
│                  │ unsupported-child clause exclude late crossings from parent(X_E). │
│ Q0               │ H6 supplies the gate write; H2.A puts cached high J on the        │
│                  │ supported path for C_fg. The second consequence uses T-VOTE and   │
│                  │ T-WALK for the pending action head. If D is in the action's slot  │
│                  │ +1, H3 gives D's exact HEADs before its gate                      │
│                  │ (second consequence).                                             │
│ QF2 Q1 (dropped) │ H2′ covers the served U at opening b and discharges the HEAD      │
│                  │ premise of Q0.                                                    │
│ QF4 S1 (dropped) │ H2′ discharges Q0’s HEAD premise for U or D1 at b and for D1 at   │
│                  │ z. If c1=b, H3 gives the source directly.                         │
│ QF4 S2-X dropped │ F8-X proves only the local exclusion; S2 emission is withdrawn.   │
│ FT-Tail (old)     │ H2′/H3 and Q0 give fresh sources and the common pending head.     │
│                  │ H2.A, T-VOTE and F8-X exclude a second-carrier crossing.          │
│ FL-T7            │ H2′ gives label-(s_B+1) coverage. T-VOTE, vote origins and T-WALK │
│                  │ exclude late crossings from parent(C), also for arbitrary delay.  │
└──────────────────┴───────────────────────────────────────────────────────────────────┘
```

For the window F8-W, H2′ and the H3/H4 ancestry of honest proposals put
X_D on the carrier parent. Retention replaces the old F8-X HEAD/lock
exclusion. FT-Tail-W keeps the source/action-head uses in Tail steps 1–4
and uses F8-W for final carriage. Q0's cap concerns height; I2 supplies
all earlier-finalization origins under the window.

FF3–FF4, FL-W, FL-RF and HP consume FF1's results; they do
not use HEAD facts directly. The H.22 producer, I8, and the negative
executions N1–N5 are outside this audit.

Thus HEAD coverage cannot be deleted from the composition proof. The
FG chain fold and record kernel consume the resulting source, parent,
and action-head facts. For F1–F9, FF3–FF4, QF2/QF4, and FL-T7, the
interface includes the T-stream, the AC HEAD services and the composition
services listed above. Q0 in F7 (c<z), QF2-W and FT-Tail-W uses
H5/H6 gate service through the same interface. The remaining inputs are
FG/substrate facts, the schedule and strict receipt, and the stated
proposer recurrence. The
separate healthy-pipeline theorem HP has the explicit startup conditions
of §7. H-time is needed only for GST bounds.
The proof copy of H.22 above records its producer; consumers below do
not import H.16 or the H.2 count directly.

### 2.2 P3 source-frame errata

These corrections apply to the proof interfaces. They change no protocol
rule. Sources: [P3 r3.5.7 rulings](../codex/jobs/p3-r357-errata.md),
[F1.5 design](../codex/reports/f15-bodies-design.md), and the
[collected P3 errata](../codex/scratch/p3-errata-2026-10-01.md).

1. `SrcFrameAbove` requires `c₀ ≤ ht(genesis) → Φ genesis` before
   its event quantifiers. `AncestorClosed Φ` alone is insufficient.
   At the initial read, `Φ=False` has a vacuous row premise but genesis
   is certified and stored. The Lean test
   `source_stmt_initial_obstruction` records this defect in the old form.
2. `certified W` is the set of every ancestral state's J, F, and T_h
   whose state height is below ht(W), with J and F included regardless
   of that height test. Thus `certified W = {genesis} ∪ crossedEntries W`.
   `RStrat` excludes genesis. Its row premise uses
   `namedEntry a.payload.height_pair = some (hOf e, e.root)` for an
   actual block e. Timeout rows name their entry too.
3. `FrameBelow Φ c₀ R` is the conjunction of
   `c₀ ≤ ht(R.F) → Φ R.F`, `c₀ ≤ ht(R.J) → Φ R.J`, and
   `c₀ ≤ ht(R.Z) → Φ R.Z`. The producers
   `cpPrefix_of_srcFrame` and `cpCompat_of_srcFrame` also require
   `RStore` and `RFrameExact`. `CPCompat` covers every contest witness,
   not only one selected witness.
4. Retained reflection, score transport, and gate receipts require
   endpoint geometry `F_src ⪯ D`, `F_dst ⪯ D`, and the comparison-prefix
   facts where used. `LabelSync` supplies timing only. Consumers derive
   geometry from their frame bounds; they cannot infer it from timing.
   The general extension supplier must cover each reader's actual live
   root, both source-start orders, and below-band transport. A common
   global bound on every live root is not a replacement.

Chapter 23 §20 records the producer homes and proof-order corrections.
These explicit premises also apply when the finality proof uses the
continuation's source history.

## 3. Records and the action cap

### FF2. High-entry records and certificate identity — PROVED from HEALING_INPUT

For each height `y≥M+1` at which an honest source exists, let `E_y` be its
entry. It is independent of the chosen honest source. Every honest record
at that height satisfies

\[
 target[y]\in\{\bot,E_y\},\quad timeout[y]=false,\quad
 lock[y]\in\{\bot,E_y\}.
\]

Every QC at such a height names `E_y`. A fresh source there permits the
exact target; SO-COV below supplies an earlier target if send-once suppresses it.
If the action head has `h_j=y`, `J=E_y`, and `h_F<y`, finality_pair
permits `(y,E_y)` for every honest identity. Emission also requires a new
height row at h>y. This invariant concerns target, timeout and lock; it
does not assert that sent permits a new row at each action.

**Proof.** Comparable source bodies of equal height have the same entry
by I2. H1 gives comparability, so `E_y` is well-defined. Initially no
record exists there. H0 excludes an old high target or timeout at the cut.
An old high lock is also impossible: a finality pair requires a justification
at that height, whose target QC has an honest height row there by I1–I2.
That row would contradict H0.

Induct on subsequent record writes, including writes before `t*`. The
source entry in a high height-pair call is `E_y`
(`height_pair`, current spec 1666–1696). If the record is empty,
`nj=false` selects that target. A matching recorded target repeats it. A
matching lock repeats it. The earlier-timeout branch is false by the
induction hypothesis. No branch creates the first high timeout or a
different target. A finality pair must name a justified entry. Its target
QC has an earlier honest source at height `y`, so the entry is `E_y`.
The finality guard therefore permits only that entry; recording a released
pair writes that lock, and suppression leaves the record unchanged. Within the same row the lock override has this same value.
This proves the invariant. Every progress or target QC contains an honest
height row and therefore matches `E_y`; finality QCs inherit that entry
from justification. Substitution in each guard of `finality_pair` proves
the stated finality permission, including an empty prior target.

The DC port is the unchanged record guard at [paper line 2139][dc-paper-client]
and `actionAttestation_finality_pair_of_recordGuard`
[W4FKChainFinalityRows.lean:115][dc-final-rows]. Changes: H1 and the
record induction supply the guard; no SG grade is invoked.

**SO-COV — send-once coverage — PROVED.** Suppose height_pair returns
(h,T,χ)≠⊥ at an honest action, and create_attestation returns ⊥.
Then Λ.sent holds a row b, sent at an earlier action, with b.h=h and
b.T=T. If χ=false, b is a target.
This lemma uses no HEALING_INPUT premise.

*Proof.* With a nonempty height pair, create_attestation returns ⊥ only
if some b∈sent has b.h=h and (¬χ or b.T=T), or if the full content is
already in sent. For a timeout (χ=true), either test gives an earlier
row naming (h,T). For a target (χ=false), timeout[h] is false, or
height_pair would return a timeout. The atomic record_attestation step
(spec de183d7d) gives two sent-set facts: a sent timeout at h implies
timeout[h]=true; every sent target at h names target[h]. Thus every sent
row at h is a target. These facts and the persistent record invariants
(01 §8.1) make all such targets name target[h],
which is write-once. A stored lock (h,T′), or the current-action lock
(h,T′), requires target[h]∈{⊥,T′}; 01 §8.1 excludes a different
recorded target, so each recorded target names T′. height_pair
returns a target at h only through lock=T, target[h]=T, or target[h]=⊥.
The last case contradicts the sent target b. Thus b=(h,T,false,·).
Suppression therefore preserves matching progress coverage, and target
coverage when χ=false. Before the first honest row at a height exists,
no honest sent record contains that height, so send-once cannot suppress
that first row.

Under the strict receipt premise, b is held at every honest node before
max(t_b,GST)+Δ_F. The HeightMatch arm accepts b where (h,T)=(σ.h,σ.T_h). R7 carries it
if it is absent from the parent chain; I6 preserves its matching bits
while height and entry remain fixed. This does not supply a new finality
pair on an earlier row. ∎

**Corollary FF2-C — no high contest.** A contested frame has `H≤M+1`.
If instead `H=j+1>M+1`, then `j≥M+1`. The cached justification is
`E_j`. Every height-`H` witness crosses `j` with a quorum naming `E_j`
by FF2 and thus extends it. The contest predicate is false. This proves
the corollary even for a delayed witness in cumulative `T`.

### FF1-A. Causal height cap — PROVED from HEALING_INPUT

Let `Q` be an honest opening at `T_p≥t*`, and let `d=ht(Q)`. Then
`d≥M+1`. Before `a_p`, every honest height row has height at most `d`.
At any read, an honest node holds no block of height at least `d+2`
whose chain has no honest row emitted at or after `a_p` (01 R-CAP).
Thus no honest node holds a block at that height before `a_p`.
Once FF1 below establishes source `Q` at `a_p`, this cap on blocks
held by honest nodes continues until, but excludes, `a_(p+1)`.

**Proof.** H2 puts `C*` below `Q`. An honest height row at height at most
`M` satisfies the cap directly. A row at greater height has an actual
source `K` with label `s≤(p−1)R≤pR−2`, since it was emitted at a prior
action and `R≥2`. H2 puts `K⪯parent(Q)`, so `ht(K)≤d` by I2. This
covers every honest row emitted before `a_p`, including a row first
disclosed in a block held at a later read. It does not require that
row to be in an honest pool. A held block of height at least `d+2`
needs a crossing at `d+1`, with an honest row there by I1–I2. The row
cap excludes such a block whose chain has no honest row emitted at
or after `a_p`. At `a_p`, all new honest height rows use source `Q`
once FF1 is proved. They have height
`d`; no further honest action occurs before `a_(p+1)`. The same crossing
contradiction therefore preserves the cap. This order avoids circularity:
FF1 uses the pre-action cap first and establishes the source before it
uses the post-action extension.

### FF1. Fresh source and exact adjacent heads — PROVED from HEALING_INPUT

For an honest opening `Q` at `T_p≥t*`, every honest fresh source at `a_p`
is exactly `Q`. If the next slot proposer is honest, write its block as
`Q1`; then `parent(Q1)=Q`, and every honest full action head at `a_p`
is exactly `Q1`. If the slot `pR+2` proposer is also honest, its block
`Q2` has `parent(Q2)=Q1`. Finality inputs at `a_p` are the immutable
`σ[Q1].(h_j,J,h_F)`, not the fields of `Q` and not the entry of `Q1`.

**Proof.** H3 supplies slot-`pR` HEADs equal to `Q`, the raw gate result
`Q`, successful guard, and post-gate `S=Q`. Their `h` honest votes arrive
before `e_(pR)` and cannot be equivocated. Hence surviving early support
on every non-genesis prefix of `Q` is at least `h≥τ`. The gate writes
`Q` into `fastWrite[pR]` with deadline `a_p+L>a_p`.

We now check the live FJ frame (current spec 922–952, 1293–1334) at each read,
including intervening block receipts. Until this action the cap gives `H≤d+1`. In an uncontested or
gap frame `lo=H−1≤d`. In a contest FF2-C gives `lo=H≤M+1≤d`.
At the next-slot proposal and the action read the full store contains
`Q`, by strict proposal delivery. Thus `Q` is a viability witness for
itself whenever `F⪯Q` and the root is below it.

For these last properties, any high justified entry at such a read has
an honest source from an earlier action. H2 puts that source below
`parent(Q)`, and hence its entry below `Q`. A positive high finalization
is one of these justified entries. Low finalizations have certificate
height at most `M`, so I4 applied to `C*` puts them below `C*⪯Q`.
If a low `J` is the root, the root rule requires `H=j+1` and no contest.
Since `Q` is admitted and `ht(Q)≥M+1`, this can occur only at
`H=M+1,j=M,ht(Q)=M+1`; absence of a contest then says `J⪯Q`.
All other low-root cases use `F`, already below `Q`. Thus every root and
`F` used here precedes `Q`.

At `T_p+4Δ`, T-START bounds each live target by the current S. Monotonicity
of healed `S` up to its exact later gate value `S(a_p)=Q` puts every such
lock below `Q`. At the action, T-START and that gate value give the same
bound directly. The live root, whether it is one of these locks or the
FG root, therefore precedes `Q`. This argument includes a lock written
at the preceding-label gate after `Q` was proposed. It uses the full
filtered tree to select the live root.

At `T_p+4Δ`, all previous-label honest votes resolve to `Q`. A proper
descendant of `Q` must have a greater slot. No earlier such slot exists;
the unique honest current proposer has not yet emitted `Q1`, and future
blocks are refused. I8 therefore gives `parent(Q1)=Q`. H3 applied to
`Q1` gives exact slot-`pR+1` HEADs. They arrive strictly before
`T_p+6Δ=a_p`. At that action read there is no admitted proper descendant
of `Q1`, since the next slot has not started and its own honest slot has
one proposal only. `Q1` is viable because it extends `Q` and has height
at least `d≥lo`. I8 gives the exact action head `Q1`.

At the opening gate, every newly fast-written block is a prefix of its
raw result `Q`. We already proved `Q` itself is fresh, live, and filtered.
It is therefore the deepest eligible source (`get_fg_vote`, current spec
1622–1645). This proves `C_fg=Q` and
allows the post-action extension of FF1-A. New rows at `a_p` can move
`H` only up to `d+1`; a new justification can only name `E_d⪯Q`.
Finality at that height, if already possible from earlier rows, also
names `E_d`. Thus the root and finality bounds below `Q` persist through
`T_p+8Δ`. No gate after the opening gate has yet run, so live locks
still precede `Q`. Slot-`pR+1` honest votes resolve to `Q1`. With no
admitted proper descendant before the unique honest `Q2` is emitted,
I8 gives `parent(Q2)=Q1`.

At every public time the tick runs before receipts at that same time
(current spec 990–1001).
In particular the opening gate precedes the action, and rows first
emitted at `a_p` cannot enter another honest action's read at `a_p`.
When an intervening block is received, it is admitted before its
`hmax`, then `J`, then `F` updates; the bounds above apply after each
such update. No frozen HEAD view is reused for an action read.

Registry comparison: `ap.source.v1`, `ap.finalityHead.v2`, and FF1 of
`fj.firstFinality.v1`. The pinned `ap.finalityHead.v2` is an NJ entry;
it is not a proof import for this FJ joint function. DC uses its full
current-slot action head at
[paper line 2111][dc-paper-action]; FG-SA replaces the grade source with
the gate write and replaces the SG anchor with the full-tree live lock.
The SA walk references in I8 explain why those extra premises must be
proved rather than inherited from a plain-SA theorem.

## 4. Retained strong-window kernel: FF3 and FF4

**Old fold, case S: PROVED; window port pending.** The indexed adjacent
+2 proof below is retained. Its receipt inequalities use
`a_r+Δ_F≤T_r+8Δ`, so rows arrive strictly before the +2 carrier in
case S. For Δ_F=Δ this recovers the original strict T_r+7Δ receipt.
The +2 carrier and its 9Δ block-receipt tail stay unchanged.
The old exact C2 state equations are not supplied by I7's window conclusion.
The receipt-ready window FF4 conclusion is F9 below, at β+Δ.

Assume `δ_t=2R`. For a trigger `t≥t*`, choose a strong window and write
`p=r−2`. Use these block names:

```text
┌───────┬────────┬────────────┬──────────────────────────┐
│ Block │ Slot   │ Time       │ Required honest proposer │
├───────┼────────┼────────────┼──────────────────────────┤
│ A     │ pR     │ T_p        │ First opening            │
│ B     │ (p+1)R │ T_p+P      │ Second opening           │
│ C     │ (p+2)R │ T_p+2P=T_r │ Central opening          │
│ C1    │ rR+1   │ T_r+4Δ     │ Action-head body         │
│ C2    │ rR+2   │ T_r+8Δ     │ Finality carrier         │
└───────┴────────┴────────────┴──────────────────────────┘
```

H2 and FF1 give `A⪯parent(B)`, `B⪯parent(C)`,
`parent(C1)=C`, and `parent(C2)=C1`. The first two use only `R≥2`.
Let `d=ht(A)`.

### FF3. The fresh middle entry is justified by C — PROVED (old fold, case S)

There are entries `U,V` such that

\[
 ht(B)=d+1,\quad ent(B)=U,\quad A\prec U\preceq B,
 \quad pR<slot(U)\le(p+1)R,
\]
\[
 ht(C)=ht(C1)=d+2,\quad ent(C)=ent(C1)=V,
 \quad \sigma[C].J=\sigma[C1].J=U,
 \quad h_j(C)=h_j(C1)=d+1,
 \quad h_F(C1)<d+1.
\]

**Proof.** At `a_p`, FF1, FF2 and SO-COV give complete target coverage for the
height-`d` entry of `A`, from earlier or new rows. These rows reach the honest proposer of `B`
before `a_p+Δ_F≤T_p+8Δ≤T_p+P`; they remain stored without clock expiry.
If `parent(B)` is still at height `d`, each row is in `B` or has its bit
in the parent, by I6. I7 forces the crossing. If the parent has already
left `d`, it has crossed it on the path above `A`. The action cap excludes
height `d+2` before `a_(p+1)`. Thus in both cases `ht(B)=d+1`.
Its first height-`d+1` block `U` is a proper descendant of `A`, so
`pR<slot(U)≤(p+1)R`. The first crossing may be mixed; we do not claim
that it justified the entry of `A`.

At `a_(p+1)`, every honest source is `B`, and FF2 makes all its honest
rows target `(d+1,U)`. No honest height-`d+1` row existed before this
action: FF1-A for `A` caps earlier rows at `d`. These rows arrive before
`a_(p+1)+Δ_F≤T_(p+1)+8Δ≤T_r` and are retained for `C`.
For any carrier on this path with slot `x≤(p+2)R`,

\[
 x\le(p+2)R<pR+1+2R\le slot(U)+\delta_t.
\]

Its mixed-progress test at height `d+1` is false. If `parent(C)` remains
there, row-or-parent-bit coverage and I7 make `C` justify `U`. If the
path already left that height, the first crossing had to use a target QC
and already justified `U`. The cap from source `B` excludes height
`d+3` before `a_r`, so no later justification can replace `U` before
`C1`; it also gives the exact heights `d+2` in the statement.

A finality QC for `U` before `a_r` would require an honest finality row
at `d+1`. Before `a_(p+1)`, even its target QC is impossible because no
honest height row at `d+1` exists. At `a_(p+1)`, all actions read before
receipt of that action's new targets; a private carrier cannot obtain an
honest signature before it is emitted. There is no intervening action.
Thus no honest finality row for `U` exists before `a_r`, and
`h_F(C1)<d+1`. This argument includes all non-opening carriers.

### FF4. Finality is accepted before T_r+9Δ — PROVED (old fold, case S)

At every honest action in round `r`, the emitted row contains finality
pair `(d+1,U)` and target pair `(d+2,V)`. Block `C2` has

\[
 ht(C2)=d+3,\quad (h_F(C2),F(C2))=(d+1,U),
 \quad (h_j(C2),J(C2))=(d+2,V).
\]

Every honest store has `U⪯F` strictly before `T_r+9Δ`, permanently.

**Proof.** FF1 identifies the action head as `C1` and the fresh source
as `C`. FF3 gives its pending justification. FF2 permits the finality
pair and the target pair. Their heights differ, so the own-row lock at
`d+1` cannot block the target at `d+2`.

All honest rows arrive before `a_r+Δ_F≤T_r+8Δ`. `C1` predates their emission,
so none is already on its parent chain. `C2` includes each complete row
by I6: each row is R6-valid and absent from the parent chain.
The height d+2 is fresh, so send-once suppresses none. The parent is exactly `C1` by
FF1. Apply I7: the row fold first makes both quorums ready, finality
writes `U`, then justification writes `V`, and the single height advance
yields `d+3`. Clearing the finality bits after the write cannot undo it.

It remains to prove acceptance, not only chain-state finalization.
Until `a_(r+1)=T_r+P+6Δ`, FF1-A for `C` excludes every run block
of height greater than `d+3`. This cap holds for cumulative `hmax`, including
private disclosures and inactive admitted blocks. Since `9<P/Δ+6` for
`R≥2`, it holds throughout the final delivery interval.
No honest finality pair above `d+1` exists during this interval. A
justification at `d+2` needs the new action's height rows; no honest
action can read that justification until the next action. Hence all
existing accepted finalizations have certificate height at most `d+1`.
By I4, `C2` and its ancestors of sufficient height extend each receiver's
`F`. Any receiver that already covers `U` is done. At another receiver,
I3 and the height bound give `F≺U`, so every block from `U` through
`C2` extends `F`. Dependencies below `F` were already admitted with its
finality carrier. DC's block exclusion therefore cannot remove the
needed path. Strict receipt supplies `C2` before `T_r+9Δ`.

At its handler, the block enters cumulative `T` before `hmax` and `J`
are updated. The new `hmax` is at most `d+3`. Since `U⪯C2` and
`ht(C2)=d+3≥hmax−1`, this admitted carrier witnesses the unmodified
finality-acceptance viability of `U`. No contest floor is substituted
for this `hmax−1` threshold.

The cache update sees `σ[C2].J=V` at height `d+2` and `F⪯U⪯V`.
No justified height above `d+2` is possible under the row cap. Any
already cached justification at `d+2` is this same `V` by FF2.
Therefore after that update the cached `J` is `V`. All three finality
guards hold: `F≺U`, `U⪯J`, and viability. The handler accepts `U` by `update_finality` (current spec 1159–1172) and
reconciles only the SA fields. I5 gives permanent local extension of `F`;
I3 excludes a conflicting later finalization elsewhere. This completes
the receipt and acceptance proof without assuming admission of any
`F`-conflicting block.

DC port: [paper line 1768][dc-paper-acceptance] and I7's named
finality-write declaration. The acceptance cap and FJ/source facts are
proved here; the DC grade call-site theorem is not used as a black box.

## 4a. Forward window kernel — PROVED for FGoodE_W from HEALING_INPUT

Assume `K_W≥2`, `R≥κ`, `δ_t=2R` and `T_p≥t*`. Put `b′=(p+1)R`, `z=(p+2)R`.
FGoodE_W(p) supplies honest proposals A at pR, B at b′, and X_E at z+κ,
and an honest slot in [b′+κ,z]. Let c be the first such slot and X_D
its honest block. Thus b′+κ≤c≤z. FGood4_W(p) uses c=b′+κ.
Neither case requires G≤P.
Let `d=ht(A)≥M+1`. The claim is that a fresh entry U with
`A≺U` and `ht(U)=d+1` is accepted in every honest F before
`T_(p+2)+β+Δ`. At R>2 this kernel need not have an honest proposal at z or z+1.

**FGood-late — WITHDRAWN (no-round):** the old case c=z+1 does not
supply a fresh higher-height source at the final action. A same-height
row cannot carry (d+1,U), and send-once can suppress that row.
The run in fg-noround-bcheck-opus-full §A refutes the old local deadline;
a sufficient Tail after that case costs 2P, not one extra round.

**F1 — first exact source.** H3 gives opening source A. FF1-A caps
all honest height rows emitted before a_p at d, including rows first
disclosed in blocks held at a later read. Thus, at any read, an honest
node holds no block of height at least d+2 whose chain has no honest
row emitted at or after a_p (01 R-CAP). Such a block needs an honest
crossing row at d+1, so no honest node holds one before the action.
FF2 and SO-COV give target coverage for `(d,ent(A))` from earlier or new rows. The height
cap persists until action p+1.
This use of H3 needs only the honest opening under test; it does not
use FF1's adjacent-slot hypotheses.

**F2 — fresh middle entry.** H2 gives `A⪯parent(B)` since R≥2.
The full target coverage from SO-COV is held before
`a_p+Δ_F≤T_p+β≤T_(p+1)` and remains
stored without clock expiry. If its parent stays at d, I6 gives each
row or its parent bit, and I7 forces a crossing. Otherwise the parent
already crossed above A. The cap excludes d+2. Therefore
`ht(B)=d+1`, `ent(B)=U`, `A≺U⪯B`, and `pR<slot(U)≤b′`.
No justification claim about the first crossing is needed.

**F3 — second exact source.** H3 gives source B at action p+1.
FF2 makes all honest rows target `(d+1,U)`. F1 shows that no honest
row at d+1 existed earlier. The new rows arrive before `a_(p+1)+Δ_F≤T_(p+1)+β≤t_c`.
Until action p+2 no row at d+2 exists, so no run block exceeds d+2.

**F4 — exclude an early mixed crossing.** Maturity for U requires
`slot≥slot(U)+2R≥pR+1+2R=z+1`. Any block on parent(X_D) has slot
at most `c−1≤z`, so that path cannot cross d+1 by mixed progress.
This is the step that uses δ_t=2R. It cannot be reused at arbitrary delay.

**F5 — X_D justifies U.** H2 puts B below parent(X_D), because c≥b′+2.
If that parent has left d+1, F4 shows that its crossing used a target
QC and justified U. Otherwise X_D includes all targets from action p+1,
or their matching bits are already present, by I6 and R6/R7.
The rows do not expire. I7 justifies U before the progress test.
The cap gives `ht(X_D)=d+2`, `J(X_D)=U`, and `h_j(X_D)=d+1`.
No honest finality row for U yet exists: its justification first becomes
possible after the action-p+1 reads, and there is no intervening action.
Thus `h_F(X_D)<d+1`. H3 gives exact service for X_D.

**F6 — common pending justification at the final action (composition).** At the
label-(z+1) HEAD, every honest head covers X_D by H2′,
since z+1≥c+1. This includes
c<z when X_D is not an opening source. F3 excludes any crossing of d+2
before action p+2. Thus all these heads have height d+2 and J=U,
with h_F<d+1. T-VOTE puts all their votes in the full action walk
before its read.

The full walk keeps this pending justification. Every reader holds X_D
by this action, so H≥d+2 and its cached justification is at least d+1.
F3 bounds H≤d+2 and excludes any justification above d+1. FF2 makes
that cached justification U. I4 puts F below X_D; the absence of finality
rows for U puts its certificate height below d+1, hence F⪯U.
FF2-C excludes a high contest. Thus H=d+2, the active root is U,
and lo=d+1. X_D and the common heads are viable in the full domain.
Honest score
dominance forces the path through X_D unless the live start is already
above it. T-START bounds a lock start K by S_x(a_(p+2)).
H3 and H4 give X_D=S_x(d_c)⪯S_x(a_(p+2)) since c≤z.
All these reads are after t*, because T_p≥t*.
Thus each live target is compatible with X_D. The
fallback root U also precedes X_D. The row cap bounds every live start,
since it is an admitted block in the full domain (T-START).
T-WALK gives coverage of X_D. A continuation can change the body, but
cannot change its pending J or cross d+2. The action head therefore has
height d+2 and pending J=U.
No exact action-head identity C1 is asserted.

**F7 — unanimous finality pair.** Every action-(p+2) source has fresh
height d+2. If c=z, H3 gives source X_D. If c<z, H2′ gives opening-z
HEAD coverage of X_D; apply Q0 with D=X_D, y=d+2, j=z and cap H≤d+2.
F6 gives pending (d+1,U) at each action head, and FF2 permits that pair.
No honest identity has sent at d+2. Each therefore sends its first
height-(d+2) target with finality (d+1,U); d+2>d+1 permits the pair.
The old permission-only step is WITHDRAWN (no-round): permission for a
finality pair does not imply emission without a new higher-height row.

**F8-W — retention and stale carriage.** Use the fresh unanimous action
p+2 of F7. At that action U is latest at height d+1 and cannot yet have
been finalized by honest rows. Its entry is present: it was appended by
the target QC and no newer justification exists yet. Between this action
and terminal slot z+κ, no next action occurs. Every new honest height row
has height d+2, so the causal cap is H≤d+3. Only one newer justification,
at d+2, can be appended before this carrier. With K_W≥2 it cannot evict U.
A finalization that prunes U already covers it by chain ancestry.

H2′ and honest-proposal ancestry put X_D below parent(X_E): its slot is
at most z and z+κ≥z+2. For each F7 row, strict receipt is before
`a_(p+2)+Δ_F≤T_(p+2)+β=t_(z+κ)`. If the parent still has height
d+2, its entry is the same high entry, so HeightMatch holds. If the parent
has crossed it, the row has d+1<d+2<parent.h and matches retained U;
it passes StaleUseful. Earlier carriage or effect-preserving omission
already set that identity bit, which persists while U is retained.
I6/R7 supplies every remaining bit. Thus all honest identities count for
U, even if latest J changed. No finality-only row or repeat send is needed.
This replaces F8-X as a dependency of the window kernel. Late target
crossings are allowed; they cannot erase U before this fold.

**F9 / FF4-W — greatest-ready fold and acceptance.** In the retained case
I7 gives U⪯F(X_E) and h_F(X_E)≥d+1 before the target event. In the
already-covered case chain monotonicity gives the same ancestry conclusion.
Do not require the exact write to U if a higher entry is ready.
The carrier has height at least d+2. Since κ≤R,
`T_(p+2)+β+Δ<T_(p+3)+6Δ=a_(p+3)`; the cap H≤d+3 lasts through
its strict block receipt. It supplies viability at H−1≤d+2.

Before that next action no honest finality pair above d+1 exists: a target
QC at d+2 needs this action's rows, and no action can read it and sign the
next pair in this interval. Thus I3/I4 put each receiving F below U or
already covering U. In the former case the needed path extends F; ancestors
below F are already stored. C1 delivers the full carrier and dependencies
before T_(p+2)+β+Δ. Its own J extends U. Any competing high cached J
has an honest target source on this same path by H1/H2 and FF2; the source
labels precede the terminal slot by at least two slots. A maximal such
cached pair therefore also extends U. The ancestry, cached-J and viability
guards accept the carrier's covering finalization. I3/I5 make coverage
common and permanent. This is the local window conclusion of FW §5,
including κ=2, checked in both spec-window reviews. ∎

### Retained +2 crossing proof (case S, old fold)

For the following proof only, restore the old FGoodE notation, X_E at
z+2 and b′+2≤c≤z. Rows arrive before a_(p+2)+Δ_F≤T_(p+2)+8Δ.
It proves the old +2 result. It is not the window kernel's F8 dependency.

**F8 (old fold, case S) — exclude late blocks from parent(X_E) (composition).** Put y=d+2,
τ=a_(p+2)=d_z, Q=X_D. Honest label-(z+1) HEADs cover Q by H2′
and precede τ, at T_(p+2)+5Δ. F3 caps earlier honest rows below y;
the action sources have height y, so H≤y+1 through the carrier read.
The old future-row/older-slot step is WITHDRAWN (no-round): a row has
no round, and R6 does not bound its carrier's slot from below.

**F8-X — slot-free first crossing (old fold, case S).** This is the replacement argument
of frozen spec bf46ae7f, “First crossing without a row round”, with
fg-noround-crossing and crossing-opus findings CR1–CR3/G1
(the reports call them N1–N3; these are not the §8 negatives).

1. On a candidate path above height y, choose its first crossing C and
   P=C.parent. I2 gives ht(P)=y and ht(C)=y+1. The quorum contains
   an honest height-y row, possibly in an ancestor whose bit persists.
   Authentic origins, immutable bodies and parent commitments place its
   emission at or after τ. No honest HEAD emitted before τ can cover
   C or a descendant, whatever C's declared slot.
2. The cap and FF2-C give lo≤y, including low contested frames. Thus
   the below-floor arm fails. Acceptance requires slot≤z+2 and the
   slot proposer's signature (bf46ae7f, Acceptance, lines 685–700).
   The honest slot-(z+2) block does not exist at its proposal read, so
   C.slot<z+2; the current-slot arm fails. With p_C≤a faulty supporters
   and equivocators, score≤p_C and T-VOTE gives at least h+p_C
   participants. Unresolved honest votes still count. Strict majority
   would require p_C>h, which is impossible.
3. The live start cannot bypass C. Lower cached roots precede Q; H2.A
   and the height-y HEADs put a new justified entry at y at or below Q.
   This entry is not its height-(y+1) crossing block. The cap excludes
   a higher justification. Finality either already covers U or preserves
   this path. T-START and H3/H4 make locks compatible with Q. Tick order
   runs the gate d_z=τ before the action and same-time receipts
   (bf46ae7f, Tick order, lines 857–871). No later gate precedes t_(z+2).
   Thus no lock can cover C; reconciliation only removes locks.
4. T-WALK gives coverage of Q and excludes side branches before Q.
   Every first crossing after the start fails all three eligibility arms.
   Hence the selected parent has height y and retains J=U, unless U is
   already finalized. The argument includes target and mixed crossings,
   old declared slots, and rows accumulated in ancestors.

**F9 (old fold, case S) — fold and acceptance.** I6 puts each honest finality row in X_E
or its bit on the parent while J=U persists. The fold has h≥q_F
matching finality bits. I7 writes U before a possible new justification
clears these bits. X_E has height at least d+2. The cap H≤d+3 holds
through its receipt, since the next action is at `T_(p+2)+P+6Δ`,
later than `T_(p+2)+9Δ` for R≥2. No finality above d+1 can yet exist;
that would need a later action after a justification using the new rows.
I3–I4 put any receiver's F below U or already above it and exclude a
conflicting required path. Strict receipt therefore supplies X_E and its
dependencies before `T_(p+2)+9Δ`. X_E witnesses viability of U at the
acceptance floor H−1≤d+2. Its J update extends U: at d+1 uniqueness
names U, and a new d+2 justification names an entry on this path by
FF2 and H1. Thus the ancestry, J, and viability guards all hold.
Every honest store accepts U, and I3/I5 retain it permanently. ∎

## 5. Deadlines: FF5, FF6, and FF7

### FF5 / fj.firstFinality.v1. New common finality — PROVED from HEALING_INPUT

For every `t≥t*`, assume K_W≥2, R≥κ, δ_t=2R and Rec_FE_W(g), or its special case
Rec_F4_W(g), with finite G and G ≥ 4Δ. There are an entry U and a time
`t_f<t+(g+2)P+β+Δ` such that all honest F(t_f) contain U permanently.
U strictly extends every S_i(t), and ht(U)>fh_i(t) for every honest i.

Export note: `FGSAClaims.finalityLivenessGSTRecFE` and
`FGSAClaims.finalityLivenessGSTRecF4` export this liveness statement only
for triggers with `GST+B_HF≤t` (premise `late`,
`AvailableChainFGSAClaims/Statements/Packages/FinalityGST.lean:14–20`;
claim `AvailableChainFGSAClaims/Claims/Finality.lean:157–167`), where
`B_HF` is the paper's B_H^F. The GST form takes Recovery₂
(`FinalitySet_W.core`,
`AvailableChainFGSAClaims/Statements/Packages/Finality.lean:31–36`) and
δ_t=2R in place of HEALING_INPUT, and returns a HealingInput witness with
`tstar w<GST+B_HF`. `FGSAClaims.firstFinalityRecFE/F4`
(`AvailableChainFGSAClaims/Claims/Finality.lean:82–96`) export the FF5
conclusion at that trigger `tstar w<GST+B_HF`, but with deadline
`GST+B_HF+W_W`, not `t*+W_W`. Thus triggers in `[t*, GST+B_HF)` are
not exported only at FF5's exact deadline;
the local FF5–FF7 forms stay Claims-module interfaces
(Lean b15feea, `AvailableChainFGSAClaims/FGSAClaims.lean:14–15`).

**Proof.** FF5-S below supplies a forward window starting at T_p≥t.
F1–F9 give A≺U and ht(U)=ht(A)+1, with acceptance before
T_(p+2)+β+Δ. H3 gives the exact gate S_i(a_p)=A. H4 and monotonicity
put S_i(t)⪯A and F_i(t)⪯S_i(t). I2 gives
fh_i(t)≤ht(A)<ht(U), including the genesis convention. FF5-S gives
the deadline. Apply t=t* and H-time to obtain

```text
W_W(g)=(g+2)P+β+Δ; B_F^W(g)=B_H^F+W_W(g).
```

This is a new finalization, not necessarily finalization of C*. The local
proof uses the full H.22 interface, including H2′. Its GST use has status
PROVED-paper through revised H-time. Under qualified healing search,
B_best^F may replace B_H^F. At κ=2 the local tail is 9Δ and this window proof gives the
old numerical local bound. ∎

### FF5-S. Forward windows — PROVED; strong alternatives — old fold

For Rec_FE_W(g), align t to the first T_q≥t, so T_q<t+P. Choose
p∈[q,q+g−1]. Then
`T_(p+2)≤T_(q+g+1)<t+(g+2)P`. F1–F9 give the FF5 deadline.
Rec_F4_W has the same alignment and uses X_D at b′+κ. At R=2 the final
carrier is at T_(p+3); its receipt before T_(p+2)+β+Δ is included.
All searches require that full forward horizon. This proves the conversion.

**Strong alternatives (old fold, case S; window port pending).**
The retained FF3–FF4 kernel also gives FF5's conclusion under a strong
window with first opening T_(r−2)≥t, before T_r+9Δ. Its proof is the
same output comparison: H3–H4 give S_i(t)⪯A, FF3 gives A≺U and
ht(U)=ht(A)+1, and FF4 supplies acceptance and retention. Under Rec_c(g_f)
the central opening is at most t+g_f P. Under StrongRec_w(g_f), align
as above and obtain `T_r≤T_q+g_f P<t+(g_f+1)P`. Under Lit(g_f),
`T_r≤T_q+(g_f−1)P<t+g_f P`. In each case its first opening is at
least t. Thus the strong alternative has deadline `t+γ(g_f)P+9Δ`.
At g_f=3, StrongRec_w is StrongPair. These are complete alternative
proofs using FF3–FF4, not implications from Rec_F to a strong recurrence.

With qualified search parameter g_h the GST bound is
`B_best(g_h)+γ(g_f)P+9Δ`; without that search it is
`B_H+γ(g_f)P+9Δ`. If both finality premises hold, use the smaller
local deadline. For arbitrary delay, keep the strong premises of §6.

### FF6. A specified honest proposal — PROVED from HEALING_INPUT

Under FF5's forward premises, each honest X proposed at t_X≥t* is
in every honest finalized ledger before `t_X+(g+2)P+β+Δ`.

**Proof.** Trigger FF5 at t_X. If T_p=t_X, A=X. Otherwise both honest
proposals have exact gates by H3, and H4 orders those gates, so X⪯A.
F2 gives A≺U and F9 gives U⪯F by the deadline. X need not itself
be the chosen checkpoint. Choosing X within G after t* gives the GST
bound `B_H^F+G+(g+2)P+β+Δ`, with the revised PROVED-paper H-time.
For the old-fold case-S strong alternative of FF5-S, the same proof with FF3–FF4
gives `t_X+γ(g_f)P+9Δ`. An arbitrarily late X has no fixed GST deadline. ∎

### FF7. Above the starting archival frontier — PROVED from HEALING_INPUT

Let H_t be the greatest honest admitted state height through t≥t*.
Under the forward FF5 premises, a common finalized entry above H_t
is accepted before `t+2((g+2)P+β+Δ)`.

**Proof.** In the first window, ht(U)≥H_t. If H_t≤M+1 this follows
from ht(U)=ht(A)+1≥M+2. Otherwise a block witnessing H_t crossed
H_t−1≥M+1. Its QC contains an honest row with source K at H_t−1,
emitted by t. For its opening label s, d_s≤t≤T_p implies
s≤(p−1)R≤pR−2. H2 gives K⪯parent(A), so ht(A)≥H_t−1.
Thus ht(U)≥H_t, but equality is possible.

Set t_1=T_(p+2)+β+Δ<t+(g+2)P+β+Δ. F9 gives U⪯F_i(t_1).
Apply FF5 again at t_1. Its A' covers U by H4, and its new entry U'
has ht(U')=ht(A')+1>ht(U)≥H_t. Acceptance is before
`t_1+(g+2)P+β+Δ<t+2((g+2)P+β+Δ)`. Both triggers are aligned forward.
For old-fold case-S strong recurrence, use FF5-S for each window; the same proof gives
`t+2γ(g_f)P+18Δ`. Both window applications require their full receipt
horizons; the second is not implied by a horizon for the first alone. ∎

### B1. Reference arithmetic — case S, old fold

The following +2/9Δ bounds and tables retain their old-fold proof scope.
Window local FGood/Tail/FF5–FF7 specialize to the same numbers at κ=2.
GST numbers use the PROVED-paper window H-time; at κ=2, B_H^F=B_H. The lower runs and
QF2/QF4 are dropped open extensions; strong, FL-* and HP rows are not window results. Their window status
is pending or OPEN as specified in §10; no lower bound transfers by the
HEIGHT BRIDGE.

Substitute k=2,L=7Δ,G=Γ=8Δ,g=3,ρ₁=25Δ into H-time and FF5–FF7:

```text
┌──────────────────────────────────┬─────────────────┬──────┬────────────────┐
│ Quantity                         │ Formula         │ R=2  │ R=3            │
├──────────────────────────────────┼─────────────────┼──────┼────────────────┤
│ Healing                          │ B_H             │ 295Δ │ 343Δ           │
│ Forward first/recurring, local   │ (g+2)P+9Δ       │ 49Δ  │ 69Δ            │
│ Forward first after GST          │ B_F(g)          │ 344Δ │ 412Δ           │
│ X within G after healing         │ B_F(g)+G        │ 352Δ │ 420Δ           │
│ Above frontier, local            │ 2(g+2)P+18Δ     │ 98Δ  │ 138Δ           │
│ Above frontier after GST         │ B_H+2(g+2)P+18Δ │ 393Δ │ 481Δ           │
│ General delay, Rec_c(3), local   │ 2gP+9Δ          │ 57Δ  │ 81Δ            │
│ R=2 all-delay strong improvement │ gP+9Δ           │ 33Δ  │ Not applicable │
│ Healthy proposal latency         │ 8RΔ             │ 16Δ  │ 24Δ            │
│ Healthy acceptance latency       │ <(8R+1)Δ        │ <17Δ │ <25Δ           │
└──────────────────────────────────┴─────────────────┴──────┴────────────────┘
```

The general-delay rows require HEALING_INPUT for that delay and strong
windows. They are not Rec_FE consequences. All values are substitutions
in proved formulas; no simulation estimate is used.

The gap-only healing bound and forward finality bounds are

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

B_best requires qualified search. Without it, use B_H for healing.
With both finality premises, take the smaller local deadline. The
optional qualified healing bound remains valid; it is larger than
B_H at the reference values below for every g_h≥1. For other parameters,
take the minimum only over bounds whose premises hold.
For integer time the strict healing gate gives an upper deadline one
tick earlier. Under FF5 the two strict inequalities give a GST first-
finality deadline `B_F(g_f)−2` ticks. These savings are ticks, not Δ.

At `k=2,G=8Δ`, values below are in units of Δ. G≤P holds at both R.
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

At `δ_t=2R`, every strong round r gives FGoodE(r−2): its opening
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

#### First-finality values for the four parameter cases

Under Rec_FE(g) (or Rec_F4(g)), FF5 and H-time give:

```text
┌───┬─────┬───────┬──────────┬──────────┐
│ R │ G/Δ │ B_H/Δ │ B_F(g)/Δ │ B_F(3)/Δ │
├───┼─────┼───────┼──────────┼──────────┤
│ 2 │ 8   │ 295   │ 320+8g   │ 344      │
│ 3 │ 8   │ 343   │ 376+12g  │ 412      │
│ 2 │ 4   │ 247   │ 272+8g   │ 296      │
│ 3 │ 4   │ 295   │ 328+12g  │ 364      │
└───┴─────┴───────┴──────────┴──────────┘
```

**B1 lower runs: PROVED-paper (old fold); WEAKER.** Window lower bounds
are OPEN pending a full fold/run check.
**historical (pre-no-round rules).** The old lower table is in
[22-finality-0569f4c8.md](archive/22-finality-0569f4c8.md), B1.

Use 21 N.2.4–N.2.6 for the replacement rows, states, and receipts. For the `R=2,G=8Δ` row, replace its silent slot 36 with silent slot 38:

```text
Silent slots: 28,33,38.
```

This variant has:

```text
┌─────────┬────────────────────────┬─────────────────────────────────────┐
│ Time /Δ │ Slot / event           │ Parent pair / rows / state          │
├─────────┼────────────────────────┼─────────────────────────────────────┤
│ 135     │ Reveal K4              │ Root becomes W3.                    │
│ 136     │ E=P34, parent W3       │ (3,W3); Q_W → (4,E).                │
│ 142     │ Height-4 target action │ T_i(4,E;—), for all three honest i. │
│ 144     │ B=P36, parent P35      │ (4,E); three targets → (5,B).       │
│ 150     │ Height-5 target action │ T_i(5,B;(4,E)); 5>4.                │
│ 152     │ Slot 38                │ Faulty and silent.                  │
│ 156     │ P39, parent P37        │ (5,B); three rows → (6,P39), F=E.   │
└─────────┴────────────────────────┴─────────────────────────────────────┘
```

First finality minus `GST=96Δ` is `60Δ`.

R7 is unchanged: P36 carries the height-4 targets; P39 carries the height-5 rows. Their parent pairs are `(4,P34)` and `(5,P36)`. The latter rows satisfy `5>4`.

The least `Rec_FE` parameter is 5. In particular, the window starting at round 16 first succeeds at round 20. All later slots are honest. The strict `8Δ` proposal-gap premise holds.

All four lower runs satisfy the same `Rec_FE(5)` premise:

```text
┌───┬─────┬──────────────────┬─────────────────┬─────────────────┐
│ R │ G/Δ │ Finality lower/Δ │ Upper at g=5 /Δ │ Coefficient gap │
├───┼─────┼──────────────────┼─────────────────┼─────────────────┤
│ 2 │ 8   │ 60               │ 360             │ 300             │
│ 3 │ 8   │ 80               │ 436             │ 356             │
│ 2 │ 4   │ 48               │ 312             │ 264             │
│ 3 │ 4   │ 68               │ 388             │ 320             │
└───┴─────┴──────────────────┴─────────────────┴─────────────────┘
```

These are coefficient differences. The integer upper deadline is two ticks
earlier. For the old 72/92/56/80 values in B1 order, the old larger bound remains OPEN (not established, not refuted).
No matching-premise lower bound at G=8Δ,g=3 is claimed. Optimal healing
and first-finality bounds remain OPEN.

The stronger N.2 `R=2,G=8Δ` replacement gives `64Δ`, but requires `Rec_FE(8)`. It must not be compared with the `g=5` upper bound.

### B1-P. Fixed-window risk comparison — PROVED arithmetic only

For independent honest proposer indicators with p=2/3, define the failure
of a finite family of slot sets S_i by

```text
Fail(S_1,…,S_j) = 1 − Σ[∅≠I⊆{1,…,j}] (−1)^(|I|+1) p^|∪[i∈I]S_i|.
```

This is inclusion-exclusion: simultaneous success for I requires exactly
the distinct slots in its union to be honest. For Rec_F(3) take
`S_i={iR,(i+1)R,(i+2)R+2}`, i=1,2,3. For one StrongRec_w(3)
search take central rounds 3 and 4, with
`S_r={(r−2)R,(r−1)R,rR,rR+1,rR+2}`. The resulting exact failures are

```text
┌───┬──────────────────┬──────────────────────┐
│ R │ Rec_F(3)         │ StrongRec_w(3) alone │
├───┼──────────────────┼──────────────────────┤
│ 2 │ 305/729 ≈ 0.418  │ 1739/2187 ≈ 0.795    │
│ 3 │ 883/2187 ≈ 0.404 │ 5089/6561 ≈ 0.776    │
└───┴──────────────────┴──────────────────────┘
```

For example the strong success is `2p⁵−p⁷` at R=2 and `2p⁵−p⁸`
at R=3; substitution gives the table. For FGood the three pair unions
have sizes 5,5,5 at R=2 and 5,6,5 at R=3; the triple unions have
sizes 6 and 7. Thus success is `3p³−3p⁵+p⁶` or
`3p³−2p⁵−p⁶+p⁷`, respectively.
The former first-finality premise included both Rec_s(3) and
StrongRec_w(3). Comparing only against Rec_s(3) compares against its
healing premise, not its full finality premise. Failure of that full
conjunction is at least the strong failure shown here. These are
unconditional fixed-window values, not probabilities of an infinite
recurrence. They do not include gap-G failures or condition on G≤P.
Use p=(n−a)/n for an actual finite fault-bounded system.
These FGood slot sets are unchanged historical arithmetic; they do not
give the failure probability of FGoodE or its recurrence.

## 5A. Qualified recurrence and first non-genesis finality

This section uses δ_t=2R and the full H.22 interface. Local window
claims assume its witness; GST use applies the PROVED-paper H-time producer in 21 H.22.
QF2/QF4 below are dropped open extensions, outside the claim set.
The retained old-fold proofs use case S. R≥2 suffices for those proofs; the exact
negative executions N5–N7 use R=2 and R=3 separately.

### Q0. Fresh write of a covered honest block at a faulty opening — PROVED

Let D be an honest proposal after t*, of high height y, and let
j=rR>slot(D) be an opening label. Suppose every honest label-j HEAD
covers D, the causal cap through a_r is H≤y+1, and F⪯D at every
honest gate and source read. Then the gate freshly fast-writes D.
Every honest source at a_r exists
and covers D. In particular, if the cap is H≤y, every such source
has height y and the entry of D. No honest proposer at j is required.

**Proof.** Since `t*=d_u` with `u≥s*+2`, the honest proposal D after
t* has `slot(D)≥s*+2`. Thus `j>slot(D)≥s*+2` is synchronous,
and D≠genesis. H6 applies to D and the gate premise F⪯D. It gives a
nonempty raw result C⪰D, a successful whole-result
guard, and D∈fastWrite[j] with lock deadline at least d_j+L>d_j.
H5 is the raw-result transfer fact used to prove that H6 guard. Thus
this gate step uses only the exported package; it needs no healing
proof lemma outside H.22. The source selection remains a separate
composition step.

Check the selector in the full filtered tree, as in FF1. The cap gives
lo=H−1≤y in gap and uncontested frames; FF2-C bounds a low contest
by lo≤M+1≤y. The served D is a height-y witness since F⪯D.
High cached J comes from an
honest target source. Before this action its opening label is at most
j−R, so H2.A puts that source in the label-j heads. Such a J is on the
covered path. A low F precedes C* by I4. A low J can control the root
only in the no-contest case H=j_cache+1, where absence of a contest
puts it below the witness. Hence the filtered tree keeps D.
For a live lock start K, T-START gives K⪯S; H3 and H4 make S compatible
with D. These locks cannot force a conflicting
start. The gate writes one chain, and its fresh live set contains
this covered candidate. Its deepest eligible member also covers D.
Under H≤y, height monotonicity forces height y and the same entry. ∎

At each use below, H3 and H4 make F compatible with the honest
block D. A finalized proper descendant of D must be an entry at
height at least y+1, by I2. Its justification needs an honest row at
that height. The row bounds at each use exclude such a row before
the gate and source read. Thus F⪯D there.

Two consequences fix the action arguments used below. Honest proposals
after t* are ordered by ancestry: their exact H3 gate values are
ordered by H4. Thus an honest proposal's high J persists into every
later honest proposal or is replaced by a higher J.

For the second consequence, let all current honest HEADs cover a
served high D of height y, with pending J=K, and suppose no block can
exceed y before the action. The same cap prevents a target crossing
that could replace K. Every honest head has height y and J=K. The
full store contains D, so H=y, lo≤y−1 by FF2-C, and D witnesses the
path. A high cached J has a target source in this path by H2.A; low roots
obey the no-contest check above. T-VOTE supplies all h honest votes at
the action read. Honest score h exceeds every off-path score at most a
and passes strict majority since 2h>n, as in T-WALK. T-START, H3 and H4
make every live start compatible with D. The full action walk therefore
covers D and keeps J=K, unless it already carries a finalization of K,
which suffices. A continuation at unchanged height cannot replace J.
If D is in the action's slot +1, H3 gives the exact HEADs before its
future gate: H4 bounds current locks by that later exact gate value.
This proof does not require the future gate to run before the action.

### QF2. Qualified recurrence with G≤P — dropped OPEN extension, outside the claim set; case S, old fold

**OPEN extension, outside the claim set (user, 2026-10-01).** The old-fold
proof is retained below. The κ=2 window text is an unreviewed sketch. For κ>2 under only G≤P and
δ_t=2R, QF2 is OPEN; see QF-W after QF4. In the retained +2 proof,
read each batch deadline as a_r+Δ_F≤T_r+8Δ.

**Statement.** Under Recovery₂, δ_t=2R, Rec_sT(g), and G≤P,
every honest node accepts one common finalized entry of height at least
M+1 strictly before `GST+B_Q(g)`, where
`B_Q(g)=B_best(g)+(2g+2)P+9Δ` and B_best is defined in 21 H.20.
This implies first non-genesis finality. It does not assert FF5's
conclusion that the entry strictly extends all outputs at an arbitrary
trigger time. M and t* are the H.22 witnesses.

**Proof.** A complete target batch below means earlier rows plus new rows by SO-COV,
with R6-valid carriage or retained matching bits by I6; it does not mean
a new row from each identity at that action. Fix a qualified round p
with T_p≥t*. Write s=pR, b=(p+1)R and
z=(p+2)R. Let A, A1 and A2 be its honest proposals at s,s+1,s+2,
and let d=ht(A)≥M+1. The entry of a block of high height d is
non-genesis: genesis is the entry at height 1 only.

#### Q1. A qualified round produces a high justification in time

FF1 gives parent(A1)=A and parent(A2)=A1. FF1-A caps all earlier
honest rows at d and all blocks before the next action at d+1. All
action-p height pairs target the entry of A; SO-COV gives complete
target coverage from earlier or new matching rows.

If A1 is still at d, A2 folds that complete batch and justifies the
entry of A. If A1 crossed by a target quorum, it already has that high
justification. These two cases give an honest proposal with high J by
slot s+2.

The remaining case is a mixed crossing in A1. Its new entry is
U=A1, at height d+1 and slot s+1. No honest row at d+1 exists through
action p, since its source is A. Before the gate and source read
at action p+1, no honest row at height d+2 exists. The criterion
after Q0 gives F⪯A1. H2′ and Q0, with D=A1 and y=d+1, put A1
below every source at action p+1. The cap forbids a higher source there.
Consequently all honest action-(p+1) rows target (d+1,U).

Let D be the first honest proposal strictly after t_(b+1). The gap gives

```text
b+2 ≤ slot(D) ≤ z+1 = slot(U)+2R.
```

H2 puts every label-b source below parent(D), since slot(D)≥b+2.
Thus parent(D) contains the height-(d+1) entry U.
The parent of D has slot at most z. It cannot leave height d+1 by
mixed progress. If it has left that height, it already justified U.
Otherwise I6 supplies the full target batch in D or its parent bits.
I7 justifies U, including when D itself is at the maturity endpoint.
I6 uses earlier or new rows, R6 validity, and retained matching bits;
no row-round bound is needed.

In every case an honest D with a high justification exists at a slot
at most z+1. The only gap used here is G≤P.

#### Q2. A later qualified round consumes the finality batch

**WITHDRAWN (no-round):** the old qualified witness alone need not
supply a new height vote above the head's finality pair. FF2 permission
does not imply the complete finality batch. Use Q2-T below.

**Q2-A — acceptance from a high carrier.** Let the honest carrier C2
retain a finalized high entry K, have height at least e+1, and arrive
while H≤e+2. It witnesses viability at H−1. I3 compares each receiver's
F with K. A receiver already above K is done; otherwise F precedes K
and C2. I4 supplies admission or finality coverage of the needed path.
FF2 and H2 put every high cached J on the carrier path: each source
has label at most the last opening and precedes the carrier parent.
A low J controls the root only with H=j+1 and no contest, which also
puts it below C2. The carrier's own J extends K; after the cache update,
K⪯J. Thus ancestry, J and viability give acceptance. Strict receipt
and I3/I5 give common permanent coverage. This is the old Q2 acceptance
argument with the Tail carrier's cap; it does not assume emission.

**FT-Tail (old fold, case S) — Tail finality lemma.** Assume HEALING_INPUT(t*), δ_t=2R,
T_r≥t*, and Tail(r). Suppose each honest proposal from rR onward has
J covering a high U (height at least M+1), or has finalized U. Then
all honest nodes have U⪯F before T_(r+1)+9Δ.

The witness form requires: **the opening at rR has height ≥M+1
(H2 with C*)**, and the stated high coverage holds from the honest
witness s∈[rR+2,(r+1)R] onward. This form extends bcheck §D in frozen
spec bf46ae7f, “Tail lemma”; round-3 review O3 checks the extension.
It is not attributed to bounds/bcheck alone.

1. H3 gives unanimous opening sources at (e,E_e). Since e≥M+1, FF2
   permits targets. SO-COV gives complete coverage from earlier or new rows
   after a_r. Send-once suppression loses no retained matching bit (I6).
2. The honest witness s follows a_r. Its block Q folds this batch or
   inherits a crossing, so ht(Q)=e+1. The cap excludes a higher block
   and any earlier honest row at e+1. Steps 1–2 need the high opening,
   not an already high J at that opening.
3. At z=(r+1)R, use H3 if s=z, otherwise H2′ for HEAD coverage of Q.
   Q0 and the cap give unanimous sources at fresh height e+1.
4. At a_(r+1), the head consequence after Q0 gives common pending
   J=K⪰U, or a finalized K relayed before a_(r+1)+Δ. FF2 permits the
   high pair. No honest identity has used height e+1.
5. In the pending case each sends (e+1,E_(e+1),false,h_K,K), with
   h_K≤e. Apply F8-X at the second carrier: y=e+1, z=(r+1)R,
   τ=a_(r+1)=d_z, Q the honest witness at s. H2′ gives label-(z+1)
   coverage; H≤e+2 and FF2-C give lo≤e+1. The last gate before t_(z+2)
   is τ and precedes the new rows. Thus no late crossing enters the
   parent and clears the finality bits (crossing review G1). I6 and I7
   fold the complete batch, finality before justification. Q2-A accepts
   before T_(r+1)+9Δ. The already-finalized case retains and exposes
   that finalization by the same deadline.

**Q2-T — second search with Tail.** Define

```text
Tail(r) := Honest(rR) ∧ (∃s∈[rR+2,(r+1)R], Honest(s))
           ∧ Honest((r+1)R+2).
Rec_sT(g) := Rec_s(g) ∧ a Tail witness in each [q,q+g−1].
```

Use the same q≥1, T_q≥GST and complete-horizon conventions. The
qualified and Tail witnesses can differ. Q1 supplies a high justification
in D by slot (p+2)R+1. Choose Tail(r) with r∈[p+2,p+g+1]. Its witness
s≥rR+2 is later than D and covers its high entry by honest ancestry.
H2 with C* puts C* below the opening at rR, so its height is at least
M+1. This discharges FT-Tail's witness premise even when r=p+2 and
D is at rR+1. Apply FT-Tail.

Align t*≤T_q<t*+P. Rec_s(g) gives T_p<t*+gP; the second search gives

```text
t_f < T_(r+1)+9Δ ≤ T_(p+g+2)+9Δ < t*+(2g+2)P+9Δ.
```

H-time supplies B_best(g). At k=2,G=8Δ, B_best(3)=B_best(4)=B_H:
295Δ at R=2 and 343Δ at R=3. For g=3 add 73Δ or 105Δ, giving
368Δ or 448Δ. For g=4 add 89Δ or 129Δ, giving 384Δ or 472Δ. ∎

### QF4. Rec_skip with G≤P — dropped OPEN extension, outside the claim set; case S, old fold

**OPEN extension, outside the claim set (user, 2026-10-01).** The old-fold proof is retained below.
FW's simple QF4 route needs δ_t≥2R+κ−1, which at κ=2 is 2R+1.
It does not prove the retained δ_t=2R extension. For κ>2 with
only G≤P, the window claim is OPEN. Keep the +2 proof below with strict
batch receipt before a_r+Δ_F≤T_r+8Δ; do not promote it to a window proof.

Define the two-slot predicate and its sampled recurrence by

```text
Skip(p) := Honest(pR) ∧ Honest((p+2)R+2).
Rec_skip(g) := ∀ q≥1 with T_q≥GST, ∃ p∈[q,q+g−1], Skip(p).   (g≥1)
Rec_skipT(g) := ∀ q≥1 with T_q≥GST, ∃ p∈[q,q+g−1], Skip(p) ∧ Tail(p+3).
```

**Statement.** Under Recovery₂, δ_t=2R, Rec_skipT(g), and G≤P,
every honest node accepts one common finalized entry of height at least
M+1 strictly before `GST+B_skip(g)`, where `B_skip(g)=B_H+(g+4)P+9Δ`.
This is first non-genesis finality, not FF5's arbitrary-trigger claim.
The stronger premise includes Tail(p+3); its horizon includes slot
(p+4)R+2 and receipt. One Skip window gives a high justification, then
that Tail gives finality. This is not an improvement under Rec_skip.

#### S1. A Skip window produces a high justification

Write s=pR, b=(p+1)R, z=(p+2)R, A=P_s, E=P_(z+2), and d=ht(A).
Choose the first honest D1 strictly after t_(s+1), and the first honest
D2 strictly after t_(b+1). Then

```text
s+2 ≤ c1=slot(D1) ≤ b+1;
b+2 ≤ c2=slot(D2) ≤ z+1.
```

The action-p batch and FF1-A give ht(D1)=d+1. Its entry U strictly
extends A and has s<slot(U)≤c1. All honest rows through action p have
height at most d. Thus no honest row at d+1 exists before action p+1,
and all blocks before that action have height at most d+1.

If D1 already has a high justification, it persists into E and the
claim holds. Otherwise the path crossed d by mixed progress.

First suppose slot(U)=s+1. If that proposer is honest, U is its served
proposal. If it is faulty, the gap triggered at t_s supplies an honest
proposal by t_b; since slot s+1 is faulty, D1 has c1≤b. No honest row
at height d+2 exists before the opening-b gate and source read. Thus
the criterion after Q0 gives F⪯U when U is honest, and F⪯D1 otherwise.
If U is honest, use H2′ and Q0 with D=U and y=d+1. Otherwise use
H2′ and Q0 with D=D1 and y=d+1 when c1<b, or H3 when c1=b.
In each case all opening-b sources have height d+1 and entry U.
The full action-(p+1) batch targets U. Its maturity is z+1. No block on parent(D2) is mature, and the
complete batch makes D2 justify U. This includes c2=z+1.

Now suppose slot(U)≥s+2. Maturity is at least z+2. If parent(E)
already has a high J, there is nothing more to prove. Otherwise ancestry
puts D1 on that parent path, and no mixed crossing of d+1 is possible
on it: every parent slot is at most z+1. A target crossing would give
a high J. Hence parent(E) still has height d+1 and entry U.

All honest rows through action p+1 have height at most d+1.
No honest row at d+2 exists before the opening-z gate and source read,
so the criterion after Q0 gives F⪯D1. Every opening-z source covers
D1, by H2′ and Q0 with D=D1 and y=d+1; z≥c1+1.
If any such source had height d+2, it would have justified U, since its
slot is at most z. H2 would then put it in parent(E), contrary to the
case under consideration. Thus all these sources have height d+1 and
entry U. Their complete target batch is in E or in its parent bits.
I7 justifies U in E, even if E is the first mature slot.

The argument used no honest opening at b. It proves that E has a high
justification, or has already finalized an entry of height at least
M+1. It does not prove that this first window finalizes U.

#### S2. A Skip window with high J at A produces finality

**WITHDRAWN (no-round):** the old emission steps at p+1 and p+2
inferred complete finality batches from FF2 permission. Sources can lag
heads, and R3/send-once do not permit those batches. S3 uses FT-Tail.

**S2-X — retained local crossing exclusion.** This step is used by no current claim.
In S2's crossing case,
D2 is the honest block at c2 defined in S1, with height d+2 and J=U.
Assume its stated cap and label-(z+1) HEAD coverage; when c2=z+1,
that coverage comes from H3, not H2′. Apply F8-X with
Q=D2, y=d+2, z=(p+2)R, τ=a_(p+2), and honest carrier E at z+2.
An honest row in the first crossing or its ancestors originates at or
after τ. No earlier honest HEAD covers it, for any declared slot.
The cap H≤d+3 and FF2-C give lo≤d+2. Acceptance and the honest
carrier key exclude the current-slot arm; faulty score fails majority.
H2.A bounds cached roots; T-START/H3/H4 and tick order bound locks.
Thus parent(E) keeps J=U or already finalized U. This local exclusion
uses crossing-review CR1/CR2's acceptance and tick-order citations in F8-X. It does not
restore S2's emission claim. If a row is already on the parent chain,
its bit persists while height and entry match; R6-valid absent rows
are carried by I6. There is no future-row/older-slot exclusion.

#### S3. Recurrence bound and minimality

Choose one Rec_skipT witness p after t*. S1 gives high justification
or finalization in E at (p+2)R+2. Every honest proposal from (p+3)R
onward covers E (at R=2 that opening is E itself). Apply FT-Tail at
r=p+3. Its deadline is T_(p+4)+9Δ. Since T_p<t*+gP,

```text
t_f < T_(p+4)+9Δ < t*+(g+4)P+9Δ < GST+B_skip(g).
```

Thus the middle opening can be omitted under Rec_skipT with G≤P.
One search and the stronger Tail premise replace the old two-search
argument. N7's old local negative is unchanged. At k=2,G=8Δ,g=3,
the bounds are 295Δ+65Δ=360Δ and 343Δ+93Δ=436Δ. ∎

### FT-Tail-W — receipt-ready Tail (PROVED-paper from HEALING_INPUT; dropped QF extensions only)

Used only by the dropped QF2/QF4 extensions, outside the claim set.

Assume K_W≥2, R≥κ, δ_t=2R, T_r≥t*, and Tail_W(r). The opening
has height e≥M+1. From its honest witness c∈[rR+κ,(r+1)R] onward,
every honest proposal has J covering a fixed high U or already finalizes U.
Then all honest F cover U before T_(r+1)+β+Δ.

**Proof.** FF1-A, FF2 and SO-COV give the complete height-e target batch,
held before a_r+Δ_F≤t_c. The witness Q consumes it or inherits a
crossing, so ht(Q)=e+1; the cap excludes an earlier row at e+1.
At the next opening z=(r+1)R, H3 if c=z, or H2′ and Q0 if c<z,
give sources at fresh height e+1. The cap and the action-head argument
after Q0 give a common pending (h_K,K), K⪰U and h_K≤e, or an
already-finalized covering entry. In the pending case the latest entry
is retained: no justification above e can yet exist, and this latest
entry was not pruned while h_F<h_K. FF2 permits finality; fresh height
e+1 ensures that send-once suppresses none. Each honest identity sends
the exact finality pair in its new higher-height row.

Before the terminal z+κ carrier there is at most one newer justification,
at e+1. Apply F8-W with this latest K, height e+1, and the same fresh
unanimous-action cap. K remains in two entries or is already covered.
I6 and I7 give K⪯F of the carrier. The cap is H≤e+2 through receipt,
while the carrier height is at least e+1. The I3/I4 admission split,
high-source cached-J argument and viability proof in F9 apply, giving
acceptance before T_(r+1)+β+Δ. The mixed-state case also needs the
certificate relay below; retention on one head alone does not supply
the certificate to the terminal carrier. ∎

**Mixed-finality erratum — K-TAIL r3.** At a_(r+1), an honest head H
can have finalized (h_K,K) while another honest head still has K pending.
H need not be an ancestor of the terminal carrier X. Let S be the
quorum that finalized K on H's chain.

1. Each signer in S has its finality bit on Q or an exact finality row
   in a block on Q⪯·⪯H. This includes faulty signers. Extract the
   whole certificate, not only the new rows sent by honest validators.
2. H is held after GST at a_(r+1). Acceptance relay delivers it to the
   terminal proposer by a_(r+1)+Δ≤t_(z+κ). The action cap excludes any
   honest row at height at least e+1 before a_(r+2). Every held finality
   certificate therefore has h_F<e+1=ht(H); R-XING gives the receiver's
   F⪯H. H and its ancestral rows are admitted and held.
3. Each extracted row was R6W-valid on its height-e+1 parent. It remains
   valid at X.parent by StaleUseful or by HeightMatch on the e+1 plateau.
   At most one newer justification exists, so K remains in the window
   unless finality already covers it.
4. R7 preserves the effects of every held valid row, regardless of its
   signer. The terminal fold thus covers K by quorum. The existing
   receipt adapter gives the same strict T_(r+1)+β+Δ acceptance deadline.

No premise H⪯X or honest signer condition on S is used.
**Lean:** `TailKernelClaim_W`; the mixed case is closed in
`Proofs/Finality/TailMixed.lean` by K-TAIL r3 (`15b9dc6`). The complete
tail assembly also discharges the batch obligation (K-TAIL r4).
**Source:** [stage-5 paper errata, E1](../codex/reports/s5-paper-errata.md)
and the K-TAIL entries in `log.md` on 2026-10-03. This closes the mixed
case; the dropped QF2/QF4 recurrence extensions keep their stated scope.

### QF2-W at κ=2 — OPEN extension, outside the claim set (user, 2026-10-01)

The κ=2 text is a sketch; it is not reviewed and no claim uses it.

Assume the full window interface, K_W≥2, δ_t=2R, G≤P and
Rec_sT_W(g), with κ=2. The strict Recovery gap holds throughout the
search and receipt horizon. The local bound from t* is (2g+2)P+9Δ.

**Sketch (not reviewed).** Q1's source and cap arguments use height geometry, exact adjacent
HEADs, and the interface. With κ=2, strict receipt precedes A2. Its
HeightMatch target batch gives a high J unless A1 made a mixed crossing.
In that case U=A1, slot(U)=pR+1. H2′ and Q0 supply fresh height-d+1
sources at action p+1. The strict gap gives an honest carrier D in
[(p+1)R+2,(p+2)R+1]. Its parent slot is less than slot(U)+2R, so
mixed progress cannot precede it. The complete batch is held by its read;
I7 or an earlier target crossing gives high J. Earlier window F advances
are handled by Q0's F⪯D premise and the already-covered branch, not by
an equality to an old execution. Honest proposal ancestry keeps that high
J or finality into later honest proposals.
Choose a Tail_W witness r∈[p+2,p+g+1]. Its first witness is later than
D, even when D has slot (p+2)R+1. Apply FT-Tail-W in its witness form.
Align t*≤T_q<t*+P and p∈[q,q+g−1]; then
`t_f<T_(r+1)+9Δ<t*+(2g+2)P+9Δ`. This is FW §5's QF2 route
with δ_t≥2R+κ−2=2R. GST use applies the PROVED-paper H-time producer of 21. ∎

### QF-W for κ>2 — dropped OPEN extension, outside the claim set; only G≤P at δ_t=2R

A receipt-ready gap carrier can be as late as (p+2)R+κ−1. The old Q1
maturity comparison no longer follows from G≤P. The simple FW §5 routes
need δ_t≥2R+κ−2 for QF2 and δ_t≥2R+κ−1 for QF4. No such timeout
change is adopted here; Recovery and GST claims keep δ_t=2R.

**Stronger-gap route: dropped OPEN extension, outside the claim set; sketch, not reviewed.** In addition to the strict
Recovery proposer gap G throughout the search horizon, assume
β+Γ−4Δ≤P and R>κ. A gap triggered at T_r+β−4Δ would supply an
honest carrier in [rR+κ,(r+1)R]. The proposed local bounds are
(2g+2)P+β+Δ for Rec_sT_W and (g+4)P+β+Δ for Rec_skipT_W.
The missing proof steps are: prove each trigger is ≥GST and ≥t*;
prove the action-(p+1) source step through H6 when the Skip_W middle
opening is faulty; and check both complete search/receipt horizons.
At R=κ the numerical condition forces Γ≤4Δ; this route uses R>κ.
A GST form would add the PROVED-paper bound B_H^F; the local
stronger-gap QF argument retains its separate sketch status. These are not PROVED
window bounds (spec review Opus F4 and fix §5).

## 6. Recurring finality and the timeout scope

**Scope: old fold, case S; window ports pending.** The forward window
recurrence follows from FF5 with W_W. The retained +2 proofs below do not
establish the strong-window or arbitrary-timeout claims for 𝒲.

FL-W, the general-delay clause of FL-RF, FL-D, and FL-T7 retain the
strong windows of §4. Their central opening C and adjacent honest
proposals are still premises. FGoodE is used here only at δ_t=2R.
For strong recurrence write γ=g for Rec_c or Lit, and γ=g+1 for
StrongRec_w. The proofs below display Rec_c endpoints; FF5-S's
alignment applies at each trigger for the other strong forms.

### FL-W. A strong window justifies for every δ_t≥0 — PROVED (old fold, case S) from HEALING_INPUT

Supply HEALING_INPUT for the chosen delay. In a strong window let `B` be the
previous honest opening, `C` the central one, and put `h_B=ht(B)`.
Then `ht(C)=h_B+1`; `C1` keeps that height and entry `E`; and `C2`
justifies `E`, for every `δ_t≥0`.

**Proof.** FF1 and FF2 do not use timeout maturity. The source at the
previous action is exactly `B`, whose honest rows all target its entry.
H2 gives `B⪯parent(C)`. If the path has not left height `h_B`, I6 and I7
force `C` to leave it. If it already left, it is at least `h_B+1`.
FF1-A for `B` excludes `h_B+2` before the central action, so
`ht(C)=h_B+1`. Also no honest row at `h_B+1` exists before that action.
Any progress crossing at `h_B+1` needs an honest row, even when `δ_t=0`.
Therefore `C1`, proposed before the action, keeps the height and entry.
At the action all honest sources equal `C`; all target `(h_B+1,E)`.
Its exact finality head is `C1`, and `parent(C2)=C1`, by FF1.
I6 supplies all rows, and I7 justifies `E` in `C2`. This proof permits
an earlier mixed crossing at height `h_B`; it does not need to forbid it.

### FL-RF. Recurring finality — PROVED (old fold, case S) from HEALING_INPUT

For each t≥t*, with δ_t=2R and Rec_FE(g), or Rec_F4(g),
FF5 gives a common checkpoint strictly above all finalized heights at t
before `t+(g+2)P+9Δ`. It strictly extends every S_i(t).

Separately, for any δ_t≥0, strong recurrence and HEALING_INPUT for
that delay give deadline `t+2γ(g)P+9Δ`. At δ_t=2R the strong
alternative of FF5-S improves it to `t+γ(g)P+9Δ`. FL-D gives the
same strong-window improvement for δ_t≥2R−1; at R=2 FL-T7 gives
it for every delay. Each clause gives unbounded finalized height in
an unbounded run.

For the forward clause, repeat FF5 at each previous deadline. Its
strict height increase gives an unbounded sequence. The following
proof is the separate general-delay strong-window argument.

**Proof.** Choose the first window at trigger `t`, central opening
`T_r≤t+gP`. FL-W justifies the central entry `E` in `C2`. Since
`ht(C)=ht(B)+1`, its entry `E` is a proper descendant of `B`. H4 and
its exact gate put `S_i(t)⪯B`, so `E` strictly extends those tips and
has height greater than their finalized heights.

Choose a second strong window with trigger `T_r`, not the later receipt
endpoint. Its central opening `T_v` satisfies
`T_r+2P≤T_v≤T_r+gP`. The first `C2` is an honest proposal at `T_r+8Δ`.
Its exact gate is `T_r+14Δ<T_r+2P`, since `R≥2`. H3–H4 order this
proposal below the second central proposal: compare their exact gate
values. Thus the second action-head body extends the first `C2`.
Its chain has `h_j≥ht(E)`. If its `h_F≥ht(E)`, it already carries a
finalization covering `E`. If `h_F<ht(E)`, its latest justification
`(z,K)` has `z≥ht(E)` and is pending. FF2 makes all honest identities
sign finality for exactly that head's `(z,K)`. The second central height c is
fresh (cap below), so z≤c−1 and send-once suppresses none (SO-COV).

The second `+1` body is the exact parent of its `+2` carrier by FF1.
It was emitted before these rows, so I6 puts each whole row in the carrier.
In the pending case I7 finalizes `K`; in the already-finalized case the
chain retains its existing finalization or advances it. Hence the carrier
has `F_D` covering `E` in both cases. FL-W also makes this carrier
justify its own central entry, and gives it height `c+1`, where `c`
is the second central height.

For store acceptance, FF1-A bounds cumulative `hmax≤c+1` until the next
action. No honest row at height `c` existed before the central action,
by the previous honest opening's cap. Thus no honest finality row at
height `c` exists yet, and every finalization during this delivery
interval has height at most `c−1`. I4 admits the carrier above the
receiving `F`; if the receiver already covers `E`, no further update is
needed. Otherwise safety makes its `F` a prefix of `F_D`. The carrier
witnesses viability, since its height is `c+1≥hmax−1`. Its new
justification at height `c` dominates all lower cached justifications;
a competing one at `c` is the same entry by FF2. It extends `F_D`.
The three acceptance guards (current spec 1159–1172) therefore hold as in FF4. Every
honest store covers `E` before
`T_v+9Δ≤t+2gP+9Δ`.

The entries `E` and all later high justified entries lie on the source
chain by FF2 and H1, so height at least `ht(E)` on that chain means
ancestry above `E`. This discharges the coverage assertions in both
cases, even if several justifications replaced one another between the
windows. Repeating the theorem after its previous deadline produces a
strictly increasing sequence of finalized heights. For `δ_t=2R`, use
the strong alternative in FF5-S at each trigger to obtain its smaller
recurring bound. The forward Rec_FE clause follows separately from FF5.

This reconstructs the carrier argument behind DC's recurring finality,
without NJ spacing or grade premises. It does not instantiate DC's
`commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins_preparedFactsGradeCallsite`
[W4D2GradeCallsite.lean:431][dc-kernel]. That theorem has additional
execution and grade call-site premises which FG-SA has not supplied.

### FL-D. Sufficient one-window delay — PROVED (old fold, case S), no necessity claim

With HEALING_INPUT supplied for that delay and the strong windows of §4,
FF3–FF4 and the strong alternatives of FF5-S and FF6 hold for `δ_t≥2R−1`
for all `R≥2`. At `R=2`, they hold for every `δ_t≥0`. These are
sufficient conditions; necessity at `R≥3` is not claimed.

**Proof.** In FF3 only a carrier before the honest `C` can skip `U`
without folding the full batch. Such a carrier has slot at most
`(p+2)R−1`. Since `slot(U)≥pR+1`, its age is at most `2R−2`, below
`δ_t≥2R−1`. If the path stays at `d+1` until `C`, `C` has the complete
target coverage and takes the target branch before the maturity test.
This proves the stated sufficient condition. FF4 then uses the resulting
justification, record permission, height cap, and acceptance witness;
FF5-S and the strong clause of FF6 use the unchanged strong endpoints.

### FL-T7. One-window finality at R=2 for every delay — PROVED (old fold, case S) from healing imports

Assume `R=2`, any `δ_t≥0`, HEALING_INPUT for that delay, and the strong
window of Section 4. FF3–FF4 and the strong clauses of FF5-S/FF6 hold, with local deadline
`t+γ(g)P+9Δ`. No FGood general-delay conclusion is asserted.

**Proof.** The first crossing argument in FF3 uses no maturity lower
bound. Thus `ht(B)=d+1`, with entry `U` above `A`. Put `s_B=(p+1)R`.
Before `a_(p+1)=t_(s_B)+6Δ`, no honest height row at `d+1` exists, by the
cap for `A`. In particular, no block can cross `d+1` before this action.
After the action, a faulty block can fold a partial batch and, if mature,
cross without justification. We must exclude that block from the parent
chosen by the honest opening `C` at slot `s_B+2`; absence of another slot
boundary before `C` does not alone exclude it.

The old previous-round exclusion is WITHDRAWN (no-round): a carrier
can declare an older slot. Apply F8-X with Q=B, y=d+1,
τ=a_(p+1)=d_(s_B) and carrier slot s_B+2. Its first crossing needs
an honest row at y, possibly retained from an ancestor. No such row
exists before τ. Honest label-(s_B+1) HEADs at t_(s_B)+5Δ cannot
cover that crossing or a descendant, whatever its declared slot.
Acceptance and the honest carrier key give slot<s_B+2 (CR1); the gate
at τ precedes the new rows and same-time receipts (CR2).

H2′ gives coverage of B at the next HEAD duty, label s_B+1, before
the action. The cap is `H≤d+1`, so all these heads still have height
d+1. This uses the H2′ clause of the supplied healing package, an AC
service to the joint selections. T-VOTE and the admission bounds below
resolve these votes at the proposer of C
before t_C. Their origin before the action still excludes late blocks.

Between the action and `t_C`, the row cap gives `H≤d+2`. FF2-C excludes
a high contest, so `lo≤d+1`. If a mixed crossing gives H≠j+1,
then the root is F⪯B by I4 and lo=H−1=d+1 (CR3). If a private block justified at `d+1`, that
justification is `U⪯B`; every lower active root also precedes `B` by
FF1's certificate cases. No finality above `B` is possible: a finality
row for `U` needs a later action. All live locks precede `B` just after
its exact gate, by T-START, and no later gate runs before `C`. Thus the live
root still precedes `B`, and `B` is viable.

At the proposal read for `C`, the honest votes above `B` force the walk
to reach `B`. A late first crossing of any declared slot has only faulty score,
at most `a`, with at least `h` honest participating seats in the pool.
Since `2a<h+a` and the total denominator is at least `h` plus the faulty
seats counted in its score, it cannot have a strict majority. More
explicitly, for faulty supporter/equivocator count `p≤a`, the denominator
is at least `h+p`, so `2p>h+p` would require `p>h`, which is impossible.
Its parent has height `d+1`, so the parent-height exemption is false when
`lo≤d+1`. Its slot is below `s_B+2` by acceptance and the honest key, so the
current-slot exemption is also false. The walk cannot select it.
A crossing on a side branch not above `B` is already excluded by the
strict dominance of the honest votes on the path to `B`.

The selected parent is therefore `B` or a noncrossing child at slot
`s_B+1`, with unchanged entry `U` and height `d+1`. It cannot have lost
its target bits through an advance. The honest proposer holds the full
action-`(p+1)` target batch. I6 and I7 make `C` justify `U` and enter
`d+2`, for any delay. FF3's no-earlier-finality-row argument is unchanged:
the justification first becomes possible after `a_(p+1)`, and `a_r` is
the next action. FF1 gives the honest `C1` and `C2` parents, FF2 permits
the finality rows, and FF4 accepts their carrier before `T_r+9Δ` using
the same cap `d+3`. FF5-S and the strong clause of FF6 then give the claimed deadlines.

This covers faulty proposals emitted after the action.
The check uses the actual SA `admitProposal` rule
[Protocol.lean:313][sa-admission], DC `on_block_using`
[Handlers.lean:192][dc-handlers], and DC `progReady`; it does not add a
rule which forces a faulty proposer to send at the opening tick.

## 7. Healthy pipeline

**Window port pending, including κ=2.** The old indexed +2 proof and
latency below use case S. For κ>2, HP and leak fairness/zero charges
remain OPEN; no new leak cut is adopted.

### HP. Two-round entry latency — PROVED (old fold, case S) under explicit start premises

Fix any `δ_t≥0`, `R≥2`. Assume the execution and strict
receipt premises of §1, `a=0`, and HEALING_INPUT(t*) for this delay.
This is a conditional theorem for delays other than `2R`; it does not
import H-time for those delays. Let `r₀` satisfy `T_(r₀)≥t*` and
write `Q₀` for its honest opening, `d=ht(Q₀)≥M+1`. Assume:

1. Every block emitted before `T_(r₀)` is an ancestor of `Q₀`.
2. No honest height row at height at least `d` was emitted before
   `a_(r₀)`. Just before `T_(r₀)`, every record at each height `y≥d`
   is `(target[y],timeout[y],lock[y])=(⊥,false,⊥)`.
   No timeout pair or sent content at those heights is recorded.
3. Every slot from `r₀R` onward has its prescribed honest proposal,
   and all nodes remain awake with strict delivery.

Define `E_r` to be the block proposed at slot `rR+2`, for each `r≥r₀`.
Then `E_r` is the new entry of height `d+(r−r₀)+1`. Its first
justification is in `E_(r+1)` and its first chain finalization is in
`E_(r+2)`. Every honest store accepts it before `t_(rR+2)+2P+Δ`.
Thus entry-to-finalizing-proposal latency is exactly `2R` slots,
`8RΔ`, and entry-to-all-store acceptance is `<(8R+1)Δ`.
The word “entry” in this theorem means exactly this indexed family;
no unspecified startup round is excluded.

**Proof.** H1–H3 are explicit premises, so FF2 gives the exact high
record invariant and FF1 gives the opening source and next-slot action
head. Consecutive honest proposals are on one chain: H3 makes each
one an exact gate value, H4 orders those values, and increasing slots
fix the ancestry direction. With `a=0`, there are no faulty rows or
proposals. Premises 1–2 exclude an old side chain or an old height-d
quorum at the start. No block can cross d before the first new action.

At `a_(r₀)` all n identities target the entry of Q₀. Their rows arrive
before `a_(r₀)+Δ_F≤T_(r₀)+8Δ` in case S. The first proposal after this action is E_(r₀)
at `T_(r₀)+8Δ`; the intervening +1 block was proposed before the
action. I6 puts every row in E_(r₀), or preserves its parent bit.
I7 justifies the old entry and creates the new entry E_(r₀) at d+1.
No higher row existed earlier, so no earlier crossing is possible.

Induct on r. The next opening is at least slot `rR+2`, with equality
when R=2, and contains E_r and its pending lower justification. No
row at E_r's new height exists until action r+1. FF1 makes its source
the next opening; FF2 makes every height pair a target for E_r. The
next +2 proposal E_(r+1) receives all rows and justifies E_r by I7.
The same fold finalizes a pending previous entry before it writes the
new justification. A finality row for E_r requires this justification;
no action can read it before action r+2. At that action FF1's exact
head has it, FF2 permits every matching finality pair, and E_(r+2)
folds the full batch. It finalizes E_r first, then justifies E_(r+1)
and creates the next entry. This proves both first-occurrence claims
and the stated height by induction. All progress rows are targets, so
the target test always succeeds first, for every δ_t.

For acceptance, during each +2 delivery interval the action cap bounds
all block heights by the carrier's height. The carrier thus witnesses
`hmax−1` viability. All blocks are on the proved chain, so the receiving
F precedes the carrier; its new justification extends its finalized
entry and dominates the cache. `on_block` and all three finality guards
(current spec 1111–1137, 1159–1172) pass, unless F already covers the entry.
Strict delivery gives acceptance less than Δ after the proposal.
At R=2 the +2 carrier is the next opening; I6 supplies its R6-valid rows.

A non-entry proposal of slot `s≥r₀R+2` precedes the next E_r, at
most `R−1` slots later. Its finality inclusion therefore takes
`<(12R−3)Δ`: `<21Δ` at R=2 and `<33Δ` at R=3. Entry acceptance
is `<17Δ` and `<25Δ`, respectively. These are conditional latency
bounds under the exact start premises above, not GST recovery bounds.

## 8. Negative executions and their exact scope

**Historical old-fold evidence in N1–N7.** N2 is REFUTED for the window
by the check below. N1 and N3–N7, including recurrence failures and B1's
lower bounds, remain OPEN until a full window-fold/run check. The HEIGHT
BRIDGE alone cannot transfer them.
The new capacity conclusions are in §8W below.

**REVALIDATE (no-round), N1 and N3–N7.** The named fixes use earlier
matching rows when repeats are suppressed. These runs lose target bits,
not finality bits: J stays genesis and every finality pair is empty.
StaleUseful requires a matching window entry and sets no height bits, so
it cannot restore these lost targets. Their mechanisms survive this check;
a complete current-rule replay remains open. N2 fails the window check.
The old checker records below are not a new replay of R6/R7/send-once.

### N1. R=2: one honest proposer per round — PROVED counterexample (old fold); REVALIDATE (no-round)

This is an infinite execution at `δ_t=2R`. Set

```text
n=4, a=f=1, honest={u1,u2,v}, faulty={b}, q_F=3, τ=2,
Δ=16, R=2, δ_t=4, k=2, L=112, GST=0, G=128=8Δ.
```

Every odd slot has an honest proposer, cycling through the three honest
identities. Every positive even slot has proposer `b`. In round `2m`
(`m≥1`), slot `4m` emits a split block `X_m`. At the other even slots,
`b` is silent. There is one honest proposer in every round, and honest
proposals are spaced by exactly two slots. Thus the strict trigger gap
is `G=8Δ`. All honest nodes are always awake. All blocks are on one
chain, so no finality exclusion or incompatible lock is used.

Ordinary honest proposals, votes, and rows arrive at all other readers
8 ticks after emission. The sender processes its FG row immediately.
The faulty seat votes for the common head in ordinary slots, with the
same delay. At slot zero all HEADs name genesis and the source is empty.
At the round-1 action, the honest slot-1 block is the common source;
all three rows target the initial entry genesis at height 1.

For split slot `x=4m`, set `t=64x`. Let `Y` be the current chain tip.
The block `X_m` contains the previous action's target rows from `u1,u2`
for `Y`'s current entry and one faulty matching timeout sent by that action.
It omits `v`'s target. It has an empty carried base-vote set; old votes
are already frozen. Deliver `X_m` to `u1,u2` at `t+12` and to `v`
at `t+20`. At the HEAD tick `t+16`, `u1,u2` vote for `X_m`, while
`v` votes for `Y`. Those honest votes arrive everywhere at `t+24`.
The faulty seat votes for `X_m`, delivered to `u1,u2` at `t+24` and
to `v` at `t+36`. Relays take 8 or 12 ticks, all less than 16.
The body dependency at `v` is ready at `t+20<t+32`.

The early cutoff is `t+32`, and the gate is `t+96`.
At `u1,u2`, `X_m` has early support 3 against late denominator 4.
At `v`, it has early support 2 against 4. The faulty vote there has
tick stamp `t+32`, at the excluded early boundary. Therefore the raw
results are `X_m,X_m,Y`; all are fresh fast sources. At the next
honest proposal, the full previous vote set gives score 3 on `X_m`.
It selects `X_m` as parent, and its own honest slot has exact service.

The split HEADs use the actual filter: `J=F=genesis`; the new maximum
makes `lo` the previous height. The current-slot child `X_m` is
eligible at readers that received it; the other reader has no such
child. Both the old parent and new block are viable. No score or
admission premise is assumed away.

Inductively `X_m` enters height `m+1` at slot `4m`, without a
justification. The split action emits two targets at that height;
send-once suppresses v's repeat target at height `m`. The odd-slot carrier after it folds
only those two new targets. At the next, silent opening `4m+2`, all
honest HEADs cover the same tip above `X_m`; every source has height
`m+1`, so its action has three matching targets from earlier or new rows;
only v sends a new row. The next proposal
is the faulty split at `4m+4`. It folds only two targets plus its timeout.
Its entry age is exactly 4 slots, so it crosses before any honest
carrier can fold the complete batch. The following odd-slot carrier
finds those complete old targets stale. This proves the induction.

```text
┌──────┬──────┬─────────────────────────────────────────────────────┐
│ Tick │ Slot │ Event                                               │
├──────┼──────┼─────────────────────────────────────────────────────┤
│ 224  │ 3    │ Action 1: three targets at height 1, entry genesis  │
│ 256  │ 4    │ X1: 2 targets + timeout; height 2, entry slot 4     │
│ 268  │ 4    │ u1,u2 receive X1                                    │
│ 272  │ 4    │ HEADs X1,X1,Y                                       │
│ 276  │ 4    │ v receives X1                                       │
│ 280  │ 4    │ Honest HEADs everywhere; faulty vote early at u1,u2 │
│ 292  │ 4    │ Faulty vote reaches v after early cutoff 288        │
│ 320  │ 5    │ Honest child of X1                                  │
│ 352  │ 5    │ Action 2: two new targets; v repeat suppressed      │
│ 448  │ 7    │ Honest carrier has only two height-2 targets        │
│ 480  │ 7    │ Action 3: new v row; earlier u1,u2 rows at 2        │
│ 512  │ 8    │ X2: age 8−4=4; mixed crossing to height 3           │
│ 608  │ 9    │ Action 4: two new targets; v repeat suppressed      │
│ 736  │ 11   │ Action 5: new v row; earlier u1,u2 rows at 3        │
│ 768  │ 12   │ X3: age 12−8=4; mixed crossing to height 4          │
└──────┴──────┴─────────────────────────────────────────────────────┘
```

`J=F=genesis` forever. No finality pair is emitted. Faulty timeouts
do not conflict with any faulty finality pair, since there are none.
Honest records only target the one entry at each height. Thus E1/E2,
send-once, R6/R7, emission-action timing, and `a≤f` all hold. This refutes first
finality from: one honest proposer per round; an honest proposer within
the first two slots; and honest spacing at most two slots, for `R=2`.
It does **not** refute healing, honest-opening recurrence, `Rec_s(g)`,
or the same claims restricted to `R=3`. The gap-only negative is restricted
to R=2 (N1, window replay pending). The R=3 gap-only question is OPEN;
N2 is refuted for the window fold.

### N2. R=3: honest openings can stall finality — REFUTED for the window fold

**Window check.** Z does not clear U's finality bits. With K_W≥2, its
post-state has h=4 and window [(2,U,{u1,u2}),(3,V,∅)]. The missing row
of v is (3,V;(2,U)): 2<3<4 and its finality pair matches (2,U). It
therefore passes StaleUseful. R7 includes that stale arm, so the honest
slot-12 proposer at tick 768 carries the row (or an equal effect). The
fold gives U three bits, q_F=3, and finalizes U. U is viable and below
J=V on this chain, so the acceptance guards pass. The repeated invariant
below fails at its first step. The following text is retained only as the
historical old-fold execution; its bit-clearing and R6 claims are false
under R6-window. This supplies no R=3 gap-only negative.

**Honest-opening corollary, every R≥2.** Under the full window
HEALING_INPUT, K_W≥2, R≥κ and δ_t=2R, use the larger row-delay bound
Δ_F′=(4R−6)Δ. Since κ=ceil((6Δ+Δ_F)/(4Δ))≤R,
Δ_F≤(4R−6)Δ; also Δ_F′≥2Δ≥Δ. This valid weaker receipt bound gives
κ′=ceil((6Δ+Δ_F′)/(4Δ))=R and β′=4RΔ=P.
The carrier interval in FGoodE_W(p) is then the singleton {(p+2)R};
four consecutive honest openings pR,(p+1)R,(p+2)R,(p+3)R give
FGoodE_W(p). FF5 applies with β=P whenever these windows recur,
including g=1 if every opening is honest. A new R=3 gap-only negative
under these premises must therefore have faulty openings.

First check one lost batch; then repeat the construction forever. Use
`n=4,a=f=1,Δ=16,R=3,δ_t=6,k=2,G=128,GST=0`. All proposers
through slot 10 are honest, with ordinary delivery delay 8. The faulty
identity withholds FG rows and can vote for the common base head. At
action 1 (tick 288), all honest rows target genesis at height 1.
Slot 5 (tick 320) carries them, justifies genesis at height 1, and
enters height 2 with entry `U=P5`. At action 2 (tick 480), all honest
rows finalize genesis at height 1 and target `(2,U)`. Slot 8 (tick 512)
folds the full batch: `h_F=1,F=genesis`, `h_j=2,J=U`, and height 3
with entry `V=P8`. This is a reachable healthy prefix, and `U` is a
non-genesis block.

Slots 9 and 10 are honest. At action 3, tick 672, every honest row has
finality pair `(2,U)` and target pair `(3,V)`. Slot 11 is faulty.
Its block `Z` at tick 704 extends the honest slot-10 block and includes
two complete honest action-3 rows, plus a faulty row which targets
`(3,V)` but has no finality pair. Its fold gives 2 finality bits and
3 target bits. It does not finalize `U`; it justifies `V`, clears
those finality bits, and enters height 4. Deliver `Z` everywhere at
tick 712. All honest slot-11 HEADs at 720 vote for `Z` and arrive by
728. The honest slot-12 proposer at 768 selects `Z`. The missing
honest action-3 row has height pair `(3,V)`. Z has height 4, so R6
makes the row invalid there; no valid child of Z can carry it.
Finality remains genesis.

All paths and locks are on this one chain. At slot 11 the sole current
block is eligible and reaches all readers before their HEADs. At slot
12 the previous votes give it strict majority support. Each row is sent
at its stated action time, all dependencies precede their use, and all
delays are 8 ticks. The only faulty slot can be followed by honest
proposers forever; the strict gap stays `8Δ`, and sampled Qualified
and Strong recurrence both hold for a sufficiently large finite `g`.
Thus all other Recovery conditions can hold in this local failure.

This exactly loses the pending non-genesis finality batch for `U`.
It refutes the local assertion that a later honest carrier must
consume that old batch.

Now make slot `3r+2` faulty for every `r≥3`, and every other slot
honest. At each action `r≥3`, the opening source is unanimous at
height `r`, with entry the preceding `+2` block. The pending
justification is at height `r−1`. Each honest row has the finality
pair for that pending entry and the target pair for the current entry.
The faulty `+2` block includes the rows of `u1,u2` and its own matching
target with an empty finality pair. Hence targets reach 3, finality
reaches only 2, and the block replaces `J` and clears those two bits.
Its honest next-opening child cannot carry the missing row, because R6
makes its stale height invalid. This proves the invariant for
the next action. Each entry is justified exactly once; none of these
non-genesis entries is finalized. `F=genesis,h_F=1` forever.

The first repeated steps are action 4 at tick 864, faulty carrier
slot 14 at 896, honest carrier slot 15 at 960; then action 5 at 1056,
faulty carrier slot 17 at 1088, honest carrier slot 18 at 1152. All
emissions and deliveries use the same 8-tick rule. The faulty identity
signs one target per height, never a finality pair or a timeout. Honest
locks concern the preceding height and agree with its unique entry.
There is no E1/E2 violation. Every block is admitted and the ordinary
current-child and unanimous-vote walks produce the stated parents.

Every opening is honest. There are two honest proposers in every
three-slot round, and the largest honest-proposal gap is two slots,
so `G=8Δ`. This satisfies honest-opening recurrence even at `g=1`,
any first-j-slots condition, one honest proposer per round, and a
count requirement of two honest proposers per round. It also satisfies
arbitrarily strong recurrence of the first two honest slots. None of
these conditions implies first finality at `R=3,δ_t=6`.

The recurring `+2` fault makes Qualified and FGood fail. Thus this does
not refute their full premises. At R=3 it proves that simply deleting the
last carrier requirement from FGood or from Strong is unsound, even
with every other named proposer honest. A later carrier cannot use a
row that R6 makes invalid on its parent to repair the cleared epoch
on the selected chain.

At R=2, every-round honest openings instead imply FGood4(r)
(=FGoodE(r)) for every r≥1, since its slots are 2r,2r+2,2r+4,2r+6.
No G≤P premise is needed.
Thus FF5 proves first finality with g=1. N2 makes no R=2 claim.

### N3. Split fresh sources — PROVED counterexample (old fold); REVALIDATE (no-round)

The split stanza of N1 is also an exact negative for this assertion.
At tick 352 the honest sources are `X1,X1,Y`, at heights `2,2,1`,
despite a timely honest next-slot proposal and full participation.
The threshold `τ=2` does not force `X1` to be the genuine result at
`v`: its strict majority test is `2·2>4`, which is false. The honest
slot-5 block's gate occurs at tick 416, after the action at 352. It
cannot replace that action's source.

This also shows why the exact single-slot HEAD adoption statement in
03 needs honesty at the queried slot. It does not show that an honest
opening is essential for healing. 21 H.9 permits this split and waits for a common entry at a later action.

### N4. Small-delay qualified recurrence — PROVED counterexample (old fold); REVALIDATE (no-round)

For every integer `R≥2` and each integer `0≤δ_t≤R+1`, there is an
infinite synchronous execution from genesis with `a=f=1`, full honest
participation, `Rec_s(3)`, and `G=4RΔ`, in which no positive-height entry
is ever justified or finalized. The available chain keeps growing.
Thus weak recurrence cannot replace strong recurrence in a general
finality theorem for these parameters.

**Parameters and all timing rules.** Set `Δ=16` ticks, `k=2`, `L=112`,
`n=4`, `τ=2`, `q=3`, `GST=0`. Identities `u1,u2,v` are honest;
`b` is faulty. All are always awake. Choose any legal hidden seat
bijection each slot. The description uses identities only to specify
which signatures occupy the seats; the base algorithm does not read
these names. Slot `s` starts at `64s`; round length is `64R` ticks.
Every unlisted block has the preceding emitted block as parent. Give
all block roots distinct values. No conflicting block is emitted.
Honest proposers follow the full proposal inclusion rule.

For every `j≥0`, `b` is the proposer at slot `(3j+2)R` and at each
slot in the interval `[(3j+1)R+2,(3j+2)R−1]`. It emits nothing in this
interval. It emits the split block `X_(j+1)` at `(3j+2)R`. All other
slot proposers are honest, chosen cyclically from `u1,u2,v`. The interval
is empty at `R=2`. All honest blocks and honest HEAD votes are delivered
to all readers 8 ticks after emission. Honest FG rows are processed
locally at the action and reach the other readers 8 ticks later. Except
at a split slot, `b` casts one base vote for the common honest head and
delivers it 8 ticks after the vote time. At silent slots the common head
is the last emitted block. At slot 0 every head is genesis.

At a split slot `x=(3j+2)R`, put `t=64x` and let `Y` be its parent.
The split block contains exactly the preceding action's two honest target
rows from `u1,u2` for `Y`'s height and entry, and one matching faulty
timeout. The timeout is sent by that preceding action time. The block can
omit `v`'s row because its proposer is faulty. Its base vote set and
support subset can be empty; all previous honest votes were already
received before the freeze and suffice for the walk. Deliver this block
to `u1,u2` at `t+12` and to `v` at `t+20`. The first two honest HEADs
at `t+16` name `X`; `v`'s names `Y`. They reach every reader at `t+24`.
The faulty seat's single vote names `X`; deliver it to `u1,u2` at
`t+24` and to `v` at `t+36`.

These times satisfy receipt: relay of `X` from its first honest receipt
at `t+12` reaches `v` in 8 ticks, and relay of the faulty vote from
`t+24` reaches `v` in 12 ticks, each less than 16. Copies not otherwise
listed may be delivered 8 ticks after honest acceptance; duplicates have
no effect. Missing dependencies are delivered first at the listed time.
`v`'s unresolved early dependency is ready at `t+20<t+32=e_x`.
There is no finality exclusion because `F` stays genesis.

The early support on `X` at `u1,u2` is 3 seats; at `v` it is 2 seats.
The late denominator is 4 everywhere. With tick stamps, the first faulty
vote stamp is `t+16<e_x`, whereas `v`'s is `t+32=e_x` and is late.
Thus the gate at `t+96` has `2·3>4` at `u1,u2` and `2·2=4` at `v`.
The genuine results are respectively `X` and `Y`, and each is a fresh
fast source there. The threshold 2 alone does not make `X` the genuine
result at `v`. All locks are on this one chain, so no guard veto or
release changes these results. Slow writes cannot add `X` to a gate
whose whole result is `Y`.

At the honest next-slot proposal, all four previous votes and paths are
present. The child above `Y` has score 3, so the parent is `X`; the
current proposal then has exact honest HEAD support. FJ does not exclude
this path: `J=F=genesis`, and each new maximum raises `lo` to the old
height, for which `X` is a descendant witness. All live roots precede
`Y` or `X`. At the split HEAD, a reader that holds `X` can take the
last edge even though previous-label votes name `Y`: the explicit
`B.slot=Σ.s` disjunct of `goldfish_eligible` admits the sole current-slot
child `X`. The admitted-proposal arm puts it in the HEAD domain. A reader
which has not received it has no such child and stops at `Y`. Thus the
stated base heads follow the actual filtered walks.
All other honest labels have unanimous support and exact gates. The
split action sends new-entry targets from `u1,u2`; sent suppresses v's
old-entry repeat. Its earlier row remains held. All finality pairs are empty because `h_j=h_F=0`.

**Initialization and induction.** The opening of round 1 is honest and
still at `(1,genesis)`. Its action supplies three targets. No block after
that action is emitted before the split at slot `2R`: the possible slots
`R+2,…,2R−1` are silent. The split uses two of these targets and one
timeout, so `targets=2`, `progress=3`. It is mature since
`2R≥δ_t`, and therefore enters height 2 with entry `X_1`. The split
source calculation above leaves only the two targets for `X_1` in later
honest blocks.

For `m≥1`, at the central honest opening `P0` of slot `3mR`, the exact
induction invariant is

\[
 ht(P0)=2m,\quad ent(P0)=X_m,\quad slot(X_m)=(3m-1)R,
 \quad Q_{target}=Q_{prog}=\{u1,u2\},\quad J=F=genesis.
\]

At `64(3mR)+4`, in action round `3m`, `b` releases a timeout for `(2m,X_m)`;
deliver it to every honest node 8 ticks later. It is after `P0`'s
proposal read and before the honest next-slot proposal `P1`. That
proposal has target count 2 and progress count 3. Its entry age is

\[
 (3mR+1)-(3m-1)R=R+1\ge\delta_t.
\]

It crosses without justification to height `2m+1`, with entry `P1`.
The action at `64(3mR)+96` still uses the opening `P0`, so all its
height-`2m` target coverage uses earlier u1,u2 rows and v's new row;
all are R6-invalid on the new path. The honest `P2` at slot
`3mR+2` cannot use them to justify anything.

The next honest opening, slot `(3m+1)R`, has height `2m+1` and entry
`P1`. Its action targets that entry unanimously. No later honest block
can fold the complete batch before the next split: slots
`(3m+1)R+2,…,(3m+2)R−1` are silent. At slot `(3m+2)R`, the split block
uses two targets and the faulty timeout for `P1`. The entry age is

\[
 (3m+2)R-(3mR+1)=2R-1\ge R+1\ge\delta_t,
\]

where the middle inequality uses `R≥2`. Thus it enters height `2m+2`
with entry `X_(m+1)`, again without justification. Its split gate emits
only two targets at that new height. The following honest blocks preserve
these two bits up to opening `3(m+1)R`, which proves the invariant for
`m+1`. At no step are three matching target identities folded before a
mixed crossing. No finality pair or positive justification ever exists.
The faulty identity signs only timeouts, not conflicting targets or
finality pairs, so it supplies no E1/E2 evidence either.

Here are the first events for `R=3,δ_t=4` in integer ticks:

```text
┌──────┬──────┬───────────────────────────────────────────────────────┐
│ Tick │ Slot │ Event                                                 │
├──────┼──────┼───────────────────────────────────────────────────────┤
│ 288  │ 4    │ Round-1 action targets genesis; source is slot 3      │
│ 320  │ 5    │ Faulty proposer is silent                             │
│ 384  │ 6    │ X1: two targets plus timeout; height 2, entry X1      │
│ 396  │ 6    │ u1,u2 admit X1                                        │
│ 400  │ 6    │ HEADs: u1,u2 to X1; v to parent Y                     │
│ 404  │ 6    │ v admits X1                                           │
│ 408  │ 6    │ Honest HEADs everywhere; faulty X1 vote at u1,u2      │
│ 420  │ 6    │ Faulty X1 vote at v, after early cutoff 416           │
│ 448  │ 7    │ Honest child of X1                                    │
│ 480  │ 7    │ Gate 6/action 2: sources X1,X1,Y                      │
│ 512  │ 8    │ Honest carrier folds the two height-2 targets         │
│ 576  │ 9    │ P0: height 2, entry X1, two target bits               │
│ 580  │ 9    │ b releases height-2 timeout; all receive at 588       │
│ 640  │ 10   │ P1 crosses to height 3; 10−6=4=δ_t                    │
│ 672  │ 10   │ Action 3: new v row; earlier u rows; R6-stale         │
│ 704  │ 11   │ Honest P2; no justification                           │
│ 864  │ 13   │ Action 4 targets height-3 entry P1                    │
│ 896  │ 14   │ Faulty proposer is silent                             │
│ 960  │ 15   │ X2 crosses to height 4; split receipts at 972 and 980 │
│ 1056 │ 16   │ Gate 15/action 5: only u1,u2 target height 4          │
│ 1152 │ 18   │ Next P0: height 4, entry X2, two target bits          │
└──────┴──────┴───────────────────────────────────────────────────────┘
```

The honest three-slot windows start at `3mR`, m≥1. They recur every `3P`,
so the strict weak recurrence holds with `g=3`. Every third opening is
faulty, so no three consecutive honest openings exist and strong
recurrence fails. The longest gap between honest proposals is `R` slots,
so the strict honest-gap premise holds with `G=4RΔ`: `8Δ` at `R=2`,
`12Δ` at `R=3`. This does not refute a theorem which additionally fixes
`G=8Δ` at `R=3`. At `R=2` the first split is slot 4, the central opening
is slot 6, and its next-slot crossing has age `7−4=3`; the same integer
schedule proves the R=2 case for `0≤δ_t≤3`.

**Checks against Lean before the negative verdict.** The early/late
split uses SA `earlyVotes`, `lateVotes`, `cleanSupport`, `confirmation`,
`prefixSupport`, and `gate` in [GridCO/Model/Protocol.lean:370][sa-gate],
with the SA adapter's threshold. The height calculation uses DC
`Protocol.progReady` and `process_height_events`
[ChainState.lean:472][dc-state]. In the current spec no branch conflicts
with `F`, so the active view equals the cumulative tree and the finality
filter changes none of these reads. No unsafe import of an unfiltered-SA
execution is needed. The symbolic induction and the integer event table
above are the verification record. No unarchived replay count is used
as evidence.

### N5 / QF1. Unrestricted finite gap does not suffice — PROVED negative (old fold); REVALIDATE (no-round)

For R=2 and R=3, and each g≥4, Recovery₂ with Rec_s(g) does
not imply first non-genesis finality. The executions below have G=2P,
n=4, a=f=1, and k=2. This is an existential refutation;
it does not refute a claim with other parameters fixed in advance.

#### N5.1 Parameters and proposer schedule

Use these parameters in both executions:

```text
n=4; a=f=1; honest={u1,u2,v}; faulty={b}; q_F=3; τ=2;
Δ=16; t_s=64s; a_r=64rR+96; GST=0;
k=2; L=112; δ_t=2R; G=128R=2P.
```

All honest nodes are always awake. All blocks are on one chain and have
distinct roots. Honest proposer duties cycle through the three honest
identities. In base-vote descriptions, a validator name denotes its seat
at that label only. The base algorithm does not link seats across slots.
Honest(0) is false by definition. Emit no slot-0 block, as
the protocol requires. Slot-0 HEADs name genesis and action 0 has no
non-genesis source.

For every m≥0 use this four-round pattern:

```text
┌───────┬────────────────┬─────────────────┬─────────────────┐
│ Round │ Slot +0        │ Slot +1         │ Slot +2, if R=3 │
├───────┼────────────────┼─────────────────┼─────────────────┤
│ 4m    │ Honest         │ Honest          │ Honest          │
│ 4m+1  │ Honest         │ Honest          │ Faulty, silent  │
│ 4m+2  │ Faulty, silent │ Faulty, entry X │ Faulty, partial │
│ 4m+3  │ Faulty, split  │ Honest          │ Honest          │
└───────┴────────────────┴─────────────────┴─────────────────┘
```

At R=2 the third slot of qualified round 4m is the honest opening of
round 4m+1. Thus rounds 4,8,12,… are qualified at both R. Every four
consecutive rounds q,…,q+3 with q≥1 contain one. Rec_s(4), and hence Rec_s(g) for g≥4,
holds. The largest honest-proposal spacing is from (4m+1)R+1 to
(4m+3)R+1, exactly 2R slots. This proves the strict trigger with G=2P,
including a trigger at an honest proposal time.

#### N5.2 Ordinary deliveries and the delayed confirmation of X

An ordinary honest proposal, HEAD vote, or row reaches all other readers
8 ticks after emission. Proposals and HEADs are also processed by their
sender on delivery. A sender processes its own FG row at once. The faulty
seat ordinarily votes for the common head with the same 8-tick delay.

Put e=(4m+2)R+1 and b₀=(4m+3)R. Let Y be the last common tip before
slot e. At tick 64e, the faulty proposer creates X above Y. Its body
contains the preceding action's target rows from u1,u2 for Y's entry,
and a matching faulty timeout of round 4m+2. Its carried base-vote set
is empty. N5.3 checks maturity.

From label e through label b₀−1, keep honest HEADs at
`new tip, new tip, Y`. At each such label j:

* The faulty seat's first vote names Y. It reaches all readers at
  64j+24, with tick stamp 64j+16.
* Its second vote names that label's new tip. It is first disclosed in
  the next slot's faulty proposal, at time 64(j+1)+4. That proposal
  carries the second vote as both a vote and declared support. It reaches
  u1,u2 at 64(j+1)+12 and v at 64(j+1)+20.
* The three honest label-j votes reach all readers at 64j+24.

X itself reaches u1,u2 at 64e+12 and v at 64e+20. At its own HEAD
tick the current-slot eligibility arm admits X at the first two readers;
v does not yet have it. Every following partial proposal extends the
previous new tip and carries the second previous-label faulty vote just
described. It has no FG rows.

At the next HEAD, u1,u2 count the faulty seat as an equivocator. Their
score above Y is 2+1=3 out of 4. At v the second vote and the current
proposal have not arrived; its score above Y is 2 out of 4. Therefore
v stops at Y. This validates the continuing split with the actual
strict-majority walk. Omitting the first faulty vote for Y would be
wrong: v would see 2 supporters out of 3 and would adopt the new path.

At each gate for j<b₀, the second faulty vote has reached everyone
before d_j=64j+96. Both faulty votes are excluded from clean support.
X and its descendants have only two clean early supporters against four
late participants. The genuine result is Y at every node. No fast or
slow write can put X above that whole result. This is how X can age
without yet becoming a common opening source.

At opening b₀, emit one more descendant W at 64b₀+4. Its carried
previous-label vote continues the same HEAD split. For label b₀ itself,
however, the faulty seat signs only one vote, for W. Deliver it at
64b₀+24 to u1,u2 and at 64b₀+36 to v. The honest votes arrive at +24.
Their scores at the opening gate are now:

```text
┌────────┬───────────────────────┬────────────────────────┬────────────────┐
│ Reader │ W clean early support │ Late participant count │ Genuine result │
├────────┼───────────────────────┼────────────────────────┼────────────────┤
│ u1,u2  │ 3                     │ 4                      │ W              │
│ v      │ 2                     │ 4                      │ Y              │
└────────┴───────────────────────┴────────────────────────┴────────────────┘
```

The faulty vote has stamp 64b₀+16 at u1,u2, but stamp 64b₀+32 at v.
The latter equals the excluded early cutoff. Each displayed genuine
result passes the guard and is freshly fast-written. Every lock is on
this chain. The next honest proposal at b₀+1 sees score 3 on W and
extends it. At action 4m+3, only u1,u2 send targets for X's new entry;
sent suppresses v's repeat for Y's old entry. The honest +2 carrier, where present, folds only those
two new targets.

All receipt bounds are strict. For a split block, the first honest
receipt is +12 and the last is +20, an 8-tick relay. The split faulty
vote is relayed from +24 to +36, a 12-tick relay. A second faulty vote
carried by a partial proposal has the same 8-tick relay as that proposal.
Dependencies arrive before their handlers use them. Each carried vote
has the previous slot label; its late receipt remains within the pool's
current-or-previous-slot admission window. There are at most two votes
per faulty seat and label.

#### N5.3 Height induction and exact maturity

Initialization is from genesis. All proposals through slot R+1 are
honest. Action 1 emits three targets for genesis at height 1. No honest
proposal follows that action before slot 3R+1. X₀ at e₀=2R+1 uses two
of those rows and the faulty timeout. Its age is 2R+1≥δ_t. It enters
height 2 without justification. The partial-vote construction above
keeps action 2 at the old entry; sent suppresses those repeat rows.
Action 3 supplies exactly two new targets
at height 2, entry X₀.

At qualified round r=4m, m≥1, the opening A has

```text
height 2m; entry X_(m−1); slot(X_(m−1))=(4m−2)R+1;
target bits {u1,u2}; progress bits {u1,u2}; J=F=genesis.
```

At T_r+4 the faulty identity releases a timeout for this height and
entry, during action round r. Every honest node receives it at T_r+12, after
the opening proposal read and before the honest +1 proposal.

The opening's entry age is 2R−1, so it does not cross. Its honest +1
child has age

```text
(4mR+1) − ((4m−2)R+1) = 2R = δ_t.
```

It has only two targets but three progress identities, and crosses by
mixed progress to height 2m+1. Its entry is that honest +1 block.
Action r still uses opening A. Earlier u1,u2 targets and v's new target
give coverage, but R6 excludes all these rows at the honest +2 carrier. No justification occurs.

Action r+1 targets the new entry unanimously. There is no honest carrier
after this action until the next split has been selected. At
e_m=(4m+2)R+1, X_m folds two targets and a faulty timeout. Its age is
again exactly 2R. It enters height 2m+2 without justification. Action
r+2 uses its older opening source, while X_m is still only partially
supported; sent suppresses the repeats. Action r+3 sends two targets
for X_m and suppresses v's stale repeat.
This is the invariant at the next qualified opening.

Thus no block ever folds three targets at its current height. No J
above genesis exists; every finality pair is empty. Honest records use
one target per height. Faulty FG rows are timeouts only. Base-vote
equivocation is permitted for the one faulty seat and does not increase
a. There is no E1 or E2 conflict in the FG rows.

#### N5.4 Separate integer traces

For R=2, δ_t=4, P=128, G=256:

```text
┌──────┬──────┬────────────────────────────────────────────────────────────┐
│ Tick │ Slot │ Event                                                      │
├──────┼──────┼────────────────────────────────────────────────────────────┤
│ 224  │ 3    │ Action 1: three height-1 targets, entry genesis            │
│ 320  │ 5    │ X0 mixed-crosses to height 2; entry slot 5                 │
│ 336  │ 5    │ HEADs X0,X0,Y; first faulty vote names Y                   │
│ 352  │ 5    │ Action 2: all height pairs still name the old entry        │
│ 388  │ 6    │ W emitted with second faulty label-5 vote                  │
│ 396  │ 6    │ u1,u2 receive W; v receives at 404, after HEAD tick 400    │
│ 408  │ 6    │ Label-6 faulty W vote at u1,u2; reaches v at 420           │
│ 416  │ 6    │ Gate 5: late equivocation removes b; all results are Y     │
│ 448  │ 7    │ Honest proposal extends W                                  │
│ 480  │ 7    │ Gate 6/action 3: source heights 2,2,1                      │
│ 512  │ 8    │ Qualified opening: height 2, entry slot 5, age 3           │
│ 516  │ 8    │ Faulty timeout released; all receive at 524                │
│ 576  │ 9    │ Honest +1: age 9−5=4; mixed crossing to height 3           │
│ 608  │ 9    │ Action 4: new v row; earlier u rows; R6-stale              │
│ 640  │ 10   │ Honest +2: no target or finality quorum at height 3        │
│ 736  │ 11   │ Action 5: three targets at height 3, entry slot 9          │
│ 832  │ 13   │ X1: age 13−9=4; mixed crossing to height 4                 │
│ 992  │ 15   │ Action 7: source heights 4,4,3                             │
│ 1088 │ 17   │ Next qualified +1: age 17−13=4; mixed crossing to height 5 │
└──────┴──────┴────────────────────────────────────────────────────────────┘
```

For R=3, δ_t=6, P=192, G=384:

```text
┌──────┬──────┬────────────────────────────────────────────────────────────┐
│ Tick │ Slot │ Event                                                      │
├──────┼──────┼────────────────────────────────────────────────────────────┤
│ 288  │ 4    │ Action 1: three height-1 targets, entry genesis            │
│ 448  │ 7    │ X0 mixed-crosses to height 2; entry slot 7                 │
│ 480  │ 7    │ Action 2: sent suppresses all repeat rows                  │
│ 516  │ 8    │ Partial proposal carries second faulty label-7 vote        │
│ 544  │ 8    │ Gate 7: all genuine results are Y                          │
│ 580  │ 9    │ Split opening carries second faulty label-8 vote           │
│ 588  │ 9    │ u1,u2 receive it; v receives at 596, after HEAD tick 592   │
│ 600  │ 9    │ Label-9 faulty vote at u1,u2; reaches v at 612             │
│ 608  │ 9    │ Gate 8: all genuine results are Y                          │
│ 640  │ 10   │ Honest proposal extends the split opening                  │
│ 672  │ 10   │ Gate 9/action 3: source heights 2,2,1                      │
│ 768  │ 12   │ Qualified opening: height 2, entry slot 7, age 5           │
│ 772  │ 12   │ Faulty timeout released; all receive at 780                │
│ 832  │ 13   │ Honest +1: age 13−7=6; mixed crossing to height 3          │
│ 864  │ 13   │ Action 4: new v row; earlier u rows; R6-stale              │
│ 896  │ 14   │ Honest +2: no target or finality quorum at height 3        │
│ 1056 │ 16   │ Action 5: three targets at height 3, entry slot 13         │
│ 1216 │ 19   │ X1: age 19−13=6; mixed crossing to height 4                │
│ 1440 │ 22   │ Action 7: source heights 4,4,3                             │
│ 1600 │ 25   │ Next qualified +1: age 25−19=6; mixed crossing to height 5 │
└──────┴──────┴────────────────────────────────────────────────────────────┘
```

### N6 / QF3. Deleting the first opening — PROVED negative (old fold); REVALIDATE (no-round)

Define DropFirst(p)=Honest((p+1)R)∧Honest((p+2)R+2). Modify N1
of this section as follows, separately for R=2,3.
Keep n=4, a=f=1, Δ=16, k=2, GST=0 and δ_t=2R.

At every positive even round 2m, the opening x=2mR is a faulty split
block X_m. Its body contains the previous action's two target rows from
u1,u2 and one matching faulty timeout. Its deliveries are exactly N1's:
block at t_x+12,t_x+12,t_x+20; honest votes at +24; single faulty
X_m vote at +24,+24,+36. No base equivocation is needed here.
Every slot +1 is honest. Every odd-round opening is honest. For R=3,
slot +2 is honest in even rounds and faulty/silent in odd rounds.
At R=2 the next odd opening is itself the even round's +2 carrier.

X_m has entry slot 2mR and height m+1. The split action emits two targets
at height m+1; sent suppresses v's repeat at height m. Subsequent honest carriers fold only the first two.
At the next, honest opening, the entry age is R<2R. Its action gives
complete target coverage from earlier u1,u2 rows and v's new row. The next emitted carrier after that batch is X_(m+1),
whose entry age is exactly 2R. It discards the third target and crosses
by mixed progress. The following honest proposal sees the discarded
batch as stale. Initialization uses action 1's genesis targets, just as
in N1. Hence J=F=genesis forever.

The largest honest gap is R slots: G=P, namely 128 ticks at R=2 and
192 ticks at R=3. For each even p, opening p+1 and carrier (p+2)R+2
are honest. DropFirst therefore recurs with g=2. Its missing first
opening p is faulty. This is an infinite negative for the weakened
recurrence, not just a missed local deadline.

The following ticks show the first repeated cycle. Action 0 has an
empty fresh set; slot 0 emits no block. Ordinary deliveries use the
8-tick rule in N5. For a split opening x, block receipts at +12,+20
have stamps t_x,t_x+16. Its HEAD tick is +16. The faulty vote
receipts at +24,+36 have stamps +16,+32; the latter equals e_x
and is excluded from early support. The gate at +96 therefore
writes X1 at u1,u2 and the old entry at v. All writes pass the guard,
since all blocks and locks are on one chain.

```text
┌───┬──────┬──────┬────────────────────────────────────────────────┐
│ R │ Tick │ Slot │ Event                                          │
├───┼──────┼──────┼────────────────────────────────────────────────┤
│ 2 │ 224  │ 3    │ Action 1: three genesis targets                │
│ 2 │ 256  │ 4    │ X1: two targets plus timeout; height 2         │
│ 2 │ 268  │ 4    │ u1,u2 receive X1; v at 276; HEAD at 272        │
│ 2 │ 280  │ 4    │ Faulty vote at u1,u2; v at 292; stamps 272,288 │
│ 2 │ 352  │ 5    │ Gate 4/action 2: source heights 2,2,1          │
│ 2 │ 384  │ 6    │ Honest opening: entry age 2<4                  │
│ 2 │ 480  │ 7    │ Action 3: new v row; old u rows for X1         │
│ 2 │ 512  │ 8    │ X2: age 8−4=4; mixed crossing to height 3      │
│ 3 │ 288  │ 4    │ Action 1: three genesis targets                │
│ 3 │ 384  │ 6    │ X1: two targets plus timeout; height 2         │
│ 3 │ 396  │ 6    │ u1,u2 receive X1; v at 404; HEAD at 400        │
│ 3 │ 408  │ 6    │ Faulty vote at u1,u2; v at 420; stamps 400,416 │
│ 3 │ 480  │ 7    │ Gate 6/action 2: source heights 2,2,1          │
│ 3 │ 576  │ 9    │ Honest opening: entry age 3<6                  │
│ 3 │ 672  │ 10   │ Action 3: new v row; old u rows for X1         │
│ 3 │ 768  │ 12   │ X2: age 12−6=6; mixed crossing to height 3     │
└───┴──────┴──────┴────────────────────────────────────────────────┘
```

The first X1 consumes held action-1 rows that are R6-valid for its parent,
with genesis age 2R≥δ_t. In each later cycle replace X1 by X_m
and shift all ticks by 2(m−1)P. Its parent has just two matching
target bits. The third target in the odd action's batch is not folded
before the next mixed crossing; after that crossing it is stale.
This proves the infinite induction, not only the displayed prefix.

At R=3 it uses G=12Δ, not the smaller reference gap 8Δ. It is a
counterexample within the full stated G≤P range. No smaller-gap negative
is claimed for this deletion.

### N7 / QF5. Both openings are needed for the local deadline — PROVED negative (old fold); REVALIDATE (no-round)

Use the same infinite prefix from N6. Choose any sufficiently late
odd p. Its opening A is honest; opening p+1 is a faulty split X.
Now make E at slot (p+2)R+2 honest, instead of the scheduled faulty
proposer. This does not increase G.

Through the split action p+1 only two targets exist for X's entry U.
The next action p+2 gives three matching targets: two earlier rows and
v's new row, with matching bits retained until the crossing. Before E, no honest carrier has folded
that batch. E now includes all three and **justifies** U. No positive
justification existed before E, so no finality pair for U can exist in
E. The next action is later than T_(p+2)+9Δ. Thus common finality is
still genesis at the original FGood deadline.

For p=101 the exact checked carrier values are:

```text
┌───┬────────┬────────────────────┬────────┬────────┬────────────┬───────────────┐
│ R │ A slot │ Faulty middle slot │ E slot │ E tick │ Entry slot │ Deadline tick │
├───┼────────┼────────────────────┼────────┼────────┼────────────┼───────────────┤
│ 2 │ 202    │ 204                │ 208    │ 13312  │ 204        │ 13328         │
│ 3 │ 303    │ 306                │ 311    │ 19904  │ 306        │ 19920         │
└───┴────────┴────────────────────┴────────┴────────┴────────────┴───────────────┘
```

Both first openings occur after the live H-time bound. At k=2,G=P,
B_H is 295Δ for R=2 and 391Δ for R=3; T_101 is 808Δ or 1212Δ.
Thus T_101≥t* in each execution. Thus this is also a counterexample to the
local conclusion with its healing interface, not an initialization
artifact. The first tests in E have zero finality bits and three target
bits. Its receipt is at E_tick+8. No finality occurs in the remaining
8 ticks before the displayed deadline.

This finite modification is not an infinite negative for Rec_skip.
The dropped extension QF4 retains the old-fold first-finality argument under Rec_skipT with G≤P.


For the local deadline, choose any sufficiently late even p in N6.
It satisfies DropFirst(p) and T_p≥t*, yet finality stays genesis at
T_(p+2)+9Δ and forever. N7 supplies the separate middle-deletion
case. Together they prove QF5 for the original FGood local theorem.

The remaining unrestricted-gap cases at these R values are g=3 at
R=2 and g∈{2,3} at R=3. At R=2, Rec_s(g) for g≤2 covers each
qualified triple and leaves at most one intervening faulty slot:
consecutive qualified starts differ by at most four slots, so the
honest-proposal gap is at most two slots, P. At R=3, g=1 makes every
slot honest. Thus the qualified suffix has gap at most P in those cases.
With the required horizon, Rec_s(g) implies Rec_sT(g) at R=2 for g≤2:
the next qualified witness makes the required later opening honest.
At R=3, Rec_s(1) makes every slot honest and supplies Tail. Thus the old-fold QF2 argument (dropped extension)
applies after any finite initial prefix, even if the original gap
allowance G is larger. N5 proves no negative for
the remaining small g cases. The smallest gap above P permitting a
negative and the optimal first-finality constants also remain OPEN.
At R≥4, unrestricted-gap Rec_s(g) for all g (QF1) and both
opening-deletion negatives (QF3, QF5) remain OPEN. The positive
QF2 and QF4 retain old-fold arguments for every R≥2; both are dropped open extensions.

#### Checker scope for N5–N7

The integer scripts in `../codex/scratch/r181/` are supplementary
checks of the exact schedules and induction above. `check.py` checks
40 rounds at each R, including the first-to-last honest relay interval.
`minimality.py` checks 32 rounds for N6 and the p=101 carrier for N7.
It overrides run() and does not execute check.py's relay assertion.
The stated offsets give relay intervals of 8 or 12 ticks, strictly
below Δ=16, also in N6–N7.

Neither script models finality pairs or honest timeouts. In the infinite
negative prefixes J stays at genesis, so finality pairs are empty.
The source assertions keep one target per honest identity and height;
with nj=false, no conflicting record, and no lock, height_pair returns
a target. The client sends it only if sent permits it; otherwise the
earlier matching row supplies coverage. No honest timeout is sent. These facts justify the omitted fields
for N5 and N6. In N7 the check stops at the first high justification:
there was no earlier finality pair for its entry, and no further action
occurs by the deadline. It makes no claim about later finality. These
checks are not a full protocol model or a Lean proof. The infinite
negative statements use the complete inductions above.


## 8W. Retention capacity and exact negative conclusions

Start at a healed fresh unanimous action a_r with U latest, and use its
causal cap. If N(U,c) newer justifications are appended before a later
honest carrier c's finality test, K_W≥1+N(U,c) retains U unless F already
covers it. With no intervening finalization this is exact: K_W newer
appends evict U. Count justifications, not blocks. The carrier's own target
append occurs after its finality test. For t_c≤T_r+B, the cap permits at
most one new level per action and gives the sufficient bound
`K_W≥2+floor((B−6Δ)/P)` (FW §3).

The receipt-ready +κ carrier needs only K_W=2. A later strict-gap carrier
uses B_gap=β+Γ−4Δ and K_gap=2+floor((β+Γ−10Δ)/P), with its trigger
and receipt interval inside the theorem horizon. With only an opening
recurrence of gap g, upward alignment from a_r+Δ_F gives
`t_c<a_r+Δ_F+gP` and
`K_rec=g+1+ceil(Δ_F/P)=g+2` under R≥κ. This last formula requires
U latest at the fresh unanimous action and its causal cap. It is not a
retention theorem for arbitrary damaged prefixes with stored old rows.

**Slow receipt capacity loss (FW §3).** In the N1 one-chain pattern with
n=4,q_F=3,Δ=2,P=24, let one honest row arrive 100 ticks after each
action and set Δ_F=101. With K_W=4, four newer target justifications
evict each entry before its missing bit arrives, so finality stays at 0.
All proposers can be honest. This refutes a fixed capacity without a
restriction on Δ_F/P; it violates R≥κ and does not refute this kernel.
The source's reduced fold check covers 16 actions; its repeated paper
pattern supplies the infinite run, not a complete AC simulation.

**Faulty withholding (FW §3).** After a complete batch for U is emitted,
faulty proposers can omit its missing finality bit and append K_W newer
justifications in K_W actions before the next honest carrier, when the
proposer premises permit that gap. U is then absent forever on that chain.
The checked K_W=4 segment finalizes height 4 at its later honest carrier
after height 1 was evicted. This proves loss of the selected certificate,
not permanent failure of ledger finality: that descendant covers height 1.
No universal lower bound on K_W for eventual finality follows.

**Target loss is separate.** If an entry at slot u can make a mixed
crossing before the complete target carrier c, no window can restore its
missed target justification. The kernel needs c−1<u+δ_t, equivalently
δ_t≥c−u, and receipt by t_c. Merely shifting a terminal deadline fails.

**Leak read.** Qfin is the latest pair's retained bit set, or ∅. The
adopted first-replacement marker uses its specified pre-height snapshot.
Union with an old pair's later retained markers is only an OPEN option;
it is not the live ledger. A retained post-state entry is below quorum,
but that fact alone does not prove the fairness or row-pool pruning ports.

## 9. Scope, source disagreements, and remaining obligations

The table and numbered notes in this section retain the old-fold case-S
comparison only. Current window statements and statuses are in §10.
No negative or unported GST conclusion below overrides that status.

```text
┌────────────────────────────┬────────────────────────────────────┬────────────────────────────────────────┐
│ Claim                      │ Premise                            │ Delay / bound                          │
├────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ I3 safety                  │ No recurrence                      │ Every δ_t≥0                            │
│ H-time                     │ Recovery₂, strict G only           │ δ_t=2R; B_H                            │
│ F1–F9, FF5/FF6             │ Rec_FE, or Rec_F4                  │ δ_t=2R; (g+2)P+9Δ local                │
│ FF7                        │ Same forward premise               │ δ_t=2R; 2(g+2)P+18Δ                    │
│ FF3–FF4, FF5-S alternative │ Strong window/recurrence           │ δ_t=2R; γ(g)P+9Δ                       │
│ FL-W, general-delay FL-RF  │ Strong windows + interface         │ Every δ_t; 2γ(g)P+9Δ recurring         │
│ FL-D                       │ Strong windows + interface         │ δ_t≥2R−1; γ(g)P+9Δ                     │
│ FL-T7                      │ R=2, strong windows + interface    │ Every δ_t; γ(g)P+9Δ                    │
│ N1                         │ G=8Δ; one honest per round         │ R=2,δ_t=4; fails finality              │
│                            │                                    │ REVALIDATE (no-round)                  │
│ N2                         │ G=8Δ; honest openings and +1       │ REFUTED window: U finalized at slot 12 │
│                            │                                    │ R=3 gap-only negative OPEN             │
│ N3                         │ Actual split sources               │ R=2; exact agreement fails             │
│                            │                                    │ REVALIDATE (no-round)                  │
│ N4                         │ Rec_s(3),G=4RΔ                     │ R≥2,δ_t≤R+1; fails finality            │
│                            │                                    │ REVALIDATE (no-round)                  │
│ Q0                         │ §5A; covered honest D, F⪯D; H≤y+1  │ R≥2,δ_t=2R; fresh source covers D      │
│ Q1, Q2-T / QF2             │ Rec_sT(g), G≤P; §5A interface      │ B_Q(g): dropped OPEN extension         │
│ S1                         │ Skip window, G≤P; §5A interface    │ R≥2,δ_t=2R; high J in E                │
│ S2                         │ WITHDRAWN (no-round): emission     │ S2-X keeps only the crossing exclusion │
│ S3 / QF4                   │ Rec_skipT(g), G≤P; §5A interface   │ B_skip(g): dropped OPEN extension      │
│ N5 / QF1                   │ Rec_s(g≥4), G=2P                   │ R=2,3; δ_t=2R; no non-genesis finality │
│                            │                                    │ REVALIDATE (no-round)                  │
│ N6 / QF3                   │ DropFirst recurrence, g=2, G=P     │ R=2,3; δ_t=2R; no non-genesis finality │
│                            │                                    │ REVALIDATE (no-round)                  │
│ N7 / QF5                   │ Delete either FGood opening; N6–N7 │ R=2,3; δ_t=2R; local deadline fails    │
│                            │                                    │ REVALIDATE (no-round)                  │
└────────────────────────────┴────────────────────────────────────┴────────────────────────────────────────┘
```

1. H.22 in §1 is byte-identical to the current 21 package. HEALED
   alone does not supply its
   source and proposal history. H2.A covers high honest sources.
   H2′ covers every honest proposal at slot v≥s*+2, whether or not it
   is an FG source.
2. Current Recovery uses C1, K_W≥2, R≥max(2,κ), δ_t=2R, and
   gap G alone. Revised HG.1–HG.6 prove B_H^F; this registry pass
   aligns the spec statuses and current statement versions.
3. At R=2 the final +2 carrier belongs to the next round. I6 uses R6/R7.
   At every R≥2, four honest openings give FGoodE_W at κ′=R and β=P.
   N2 is refuted for the window. Only the R=2 gap-only negative (N1)
   remains, with replay pending; R=3 is OPEN.
4. N4 concerns δ_t≤R+1, not δ_t=2R. At R=3 it also uses G=12Δ.
   It does not refute qualified recurrence at the reference delay and gap.
5. FL-W, the general-delay FL-RF clause, FL-D, and FL-T7 keep strong
   windows and a separate healing interface for the chosen delay. The
   FGoodE maturity proof uses δ_t=2R. No general-delay B_H is proved.
6. QF1–QF5 settle the stated qualified-recurrence and opening-deletion
   questions at R=2,3. QF2 and QF4 retain old-fold arguments for every R≥2; both are dropped open extensions.
   OPEN: unrestricted-gap g=3 at R=2, g∈{2,3} at R=3, and all g
   at R≥4 (QF1); both opening-deletion negatives at R≥4 (QF3, QF5);
   a complete characterization of sufficient schedules; optimal bounds;
   necessary delay for all R≥3; and mixed Lean composition.
   The frozen spec records a separate R=3 small-delay refutation, but that
   record is not used as a proof here.

## 10. Verification and statement index

Retained proof audit, DC checkout: `b241081d344555797205f8718eeb23a8a0e3eb4c`.
Retained proof audit, SA checkout: `3eb1889cd7e231d33e7edb96762b0ebd641825cb`.
That historical read confirmed DC at that commit and AC HEAD at ab6e51a.
The sources of every port are given at the corresponding proof step.
The finite in-memory checks also verified the displayed reference bounds,
`7<4R`, `9<4R+6`, and every fresh-entry slot in the FF3 inequality for
`2≤R≤100`. These checks supplement the symbolic proofs. They are not
an execution proof or a substitute for the named import. Those historical checks accompanied an earlier three-chapter edit.
This registry pass does not rerun N5–N7 or inspect Lean.
No Lean build is claimed.

B1 lower runs are WEAKER: `60/80/48/68 Δ` under common `Rec_FE(5)`.
For the old 72/92/56/80 values, the old larger bound remains OPEN (not established, not refuted).

The current window status is:

```text
┌────────────────────────────────┬─────────────────────────────────────────────────────┐
│ Item                           │ Status and source                                   │
├────────────────────────────────┼─────────────────────────────────────────────────────┤
│ I1–I8; 01 HEIGHT BRIDGE        │ PROVED-paper: explicit window proofs, §§2 and 01 §3 │
│ FF2/FF2-C, FF1-A, FF1, Q0      │ PROVED from full window interface; same source/cap  │
│ F1–F9 / FF4-W                  │ PROVED-paper: FGoodE_W/FGood4_W, K_W≥2, R≥κ, 2R     │
│ FT-Tail-W                      │ PROVED; Lean TailKernelClaim_W; K-TAIL r3 relay     │
│ FF5–FF7, forward recurrence    │ PROVED locally: W_W or 2W_W; full receipt horizons  │
│ H.22 / H-time, C1              │ PROVED-paper: 21 W1–W3, HG.2–HG.6, H.22             │
│ B_H^F; B_F^W and GST uses      │ PROVED-paper: H-time and window recurrence          │
│ QF2-W at κ=2                   │ OPEN, dropped extension; κ=2 sketch unreviewed      │
│ QF4 at κ=2, δ_t=2R             │ OPEN, dropped extension; old-fold text retained     │
│ QF2/QF4, κ>2, only G≤P         │ OPEN, dropped extension at δ_t=2R                   │
│ Stronger-gap QF route          │ Dropped OPEN extension; sketch, not reviewed        │
│ FF3–FF4, strong alternatives   │ Old fold case S PROVED; window port pending         │
│ FL-W/RF/D/T7, HP               │ Old fold case S PROVED; window port pending         │
│ Leak fairness / HP zero charge │ Old fold case S only; κ>2 OPEN                      │
│ B1 upper GST numbers           │ Healing/forward proved; QF2/QF4 dropped             │
│ B1-P                           │ PROVED arithmetic only for its displayed old sets   │
│ N1,N3–N7; QF1/3/5; B1 lower    │ Old-fold scopes retained; window conclusions OPEN   │
│ N2                             │ REFUTED window; R=3 gap-only question OPEN          │
│ Capacity / selected retention  │ FW §3, §8W; no universal eventual-finality negative │
│ Lean composition / optimality  │ OPEN; no Lean work in this pass                     │
└────────────────────────────────┴─────────────────────────────────────────────────────┘
```

No PROVED label on an old-fold section establishes a window theorem.
Clean/P1 still need the marked provenance/store ports and review. Healing
and continuation use the revised 21/23 arguments. A common source history
or an unchanged height projection
alone does not identify the two executions.

[dc-state]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusModel/Protocol/ChainState.lean:423
[dc-crossing]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50
[dc-coverage]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/RawHeightCoverage.lean:1011
[dc-justify]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/W4FKChainJustification.lean:185
[dc-final-write]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ChainState/W4FKChainFinalityWrite.lean:177
[dc-final-rows]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Protocol/ValidatorClient/W4FKChainFinalityRows.lean:115
[dc-kernel]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusProofs/Execution/W4D2GradeCallsite.lean:431
[sa-heads]: /Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/ProposalHeads.lean:19
[sa-clean]: /Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Proofs/CleanInclusion.lean:143
[sa-gate]: /Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:370
[dc-paper-transition]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2229
[dc-paper-evidence]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:718
[dc-paper-client]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2139
[dc-paper-admission]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:1720
[dc-paper-acceptance]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:1768
[dc-paper-receipt]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:203
[dc-paper-inclusion]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2041
[dc-paper-action]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:2111
[dc-paper-delay]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:772
[dc-paper-grades]: /Users/francesco/ethereum/research/healing/rewrite/consensus.tex:1211

[sa-admission]: /Users/francesco/ethereum/lean/available-chain/AvailableChainGridCO/Model/Protocol.lean:313
[dc-handlers]: /Users/francesco/ethereum/lean/decoupled-consensus/verified-consensus/DecoupledConsensusModel/Protocol/Handlers.lean:192
