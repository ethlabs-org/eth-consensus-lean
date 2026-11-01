# 21 — Healing of the available chain and the FJ frame

_Date: 2026-10-01. Part 2b-i. Paper proof blueprint; not a Lean certificate._

Current spec SHA-256: `a926aae541941d14627f7cbc51ef9747762018f3babb74b4f092779d38c6c1fc`.

## 1. Authority, scope, and result

The positive recovery results use C1 and the finality window with K≥2,
R≥max(2,κ), and δ_t=2R. The rule names are those of
[the current specification](../spec/fgsa-protocol.tex): R6-window,
Inclusion (R7), and the state transition. K is its K_W; β_F is its β.
The frozen delta is [rec-df-integrate](../codex/reports/rec-df-integrate.md),
with [Astra's review](../codex/reports/rec-df-integrate-review.md) and
[Opus's review](../codex/reports/rec-df-integrate-review-opus-full.md).
W1–W3 below supply the window foundations. R7's optional omission keeps
every effect (01 §1.1), so each positive carriage argument below is unchanged. Healing needs no finality
recurrence or window-retention premise. The historical negative runs
retain their old rule basis; this edit does not validate them for the window.

The earlier rule authority is [the adopted specification](../spec/archive/fgsa-protocol-de183d7d.tex), SHA-256
`de183d7d140233e1ca193717bb1da8c5d19b0602bcc71abde2a9546e16a8b966`.

The final de183d7d spec changes wording only from bf46ae7f. Explicit
bf46ae7f line citations below retain that archive numbering.

Spec line citations use the 4e85ff34 numbering
([spec/archive/fgsa-protocol-4e85ff34.tex](../spec/archive/fgsa-protocol-4e85ff34.tex));
the earlier spec c1ea1db0 changed only the delivery premise and the
healing-interface names
([spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md](../spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md)).
This is the r214 citation basis. Explicit older archive bases below
remain in effect for their existing citations.
The no-round delta below uses frozen spec bf46ae7f; its citations name
that archive. Negative executions have the status stated in 00 §3.5.

Existing absolute spec line citations refer to the
[42d557a2 archive](../spec/archive/fgsa-protocol-42d557a2.tex), except
an explicitly named archive. The F-start rule and its execution transfer
are proved in 01 §6.5. Equal external traces preserve all healing bounds,
including HG.7. Window-checked lower witnesses are N.2 (WEAKER: 38/46/54/62 Δ)
and HG.N2 (WEAKER: 45Δ−1 / 61Δ−1 tick; five changes). HG.8’s r213
citations use 4e85ff34 line numbers and override the historical default.
HG.1–HG.6 integrate the corrected r193 proofs. HG.7 integrates [r206](../codex/healing-gap-close.md) with the fixes in
[its review](../codex/review-healing-gap-close.md). Earlier reports
are evidence records; the proof steps are stated here.

Under `Recovery₂`, defined below, the available chain is healed from
`GST+B_H^F`, without an opening recurrence. PROVED in this chapter means
PROVED-paper: a full paper proof is present. It does not mean a checked
composed FG-SA Lean theorem.

```text
Δ_F≥Δ>0; integer time; k≥2; K≥2; R≥max(2,κ); δ_t=2R.
κ = ceil((6Δ+Δ_F)/(4Δ)); β_F = 4κΔ; ε = β_F−8Δ.
P = 4RΔ; T_r = rP; a_r = T_r+6Δ.
D_F(r) = a_r+Δ_F; C_F(r) = T_r+β_F.
D_F(r)≤C_F(r)≤T_(r+1); C_F(r)+Δ<a_(r+1).
L = (4k−1)Δ; Γ = 4Δ ⌈G/(4Δ)⌉; θ = 3Δ.
ρΓ = 2L+Γ+8Δ; ρ₁ = L+Γ+10Δ; ρ = 2L+G+8Δ.
B^F(ρ̄) = max(6ρ̄+12P+6Γ+Δ+2ε, 4ρ̄+14P+6Γ−13Δ).
B_H,F^(2) = B^F(ρΓ); B_H,F^(1) = B^F(ρ₁).
B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
E_g^F=ρ̄+2P+Γ−Δ; E_j^F=max(ρ̄+P+Γ+3Δ+ε, 2P+Γ−4Δ).
B_c^F=ρ̄+2P+Γ−6Δ; D_c^F=ρ̄+P−Δ.
B_reset^F(ρ̄)=3P+2E_g^F+2E_j^F+B_c^F+D_c^F.
B'_reset^F = min of eligible B_reset^F(ρ̄) = B_H^F−Γ−4Δ.
```

For Δ_F≤2Δ, κ=2 and ε=0: the F bounds equal the old B_H,
B_reset, E_g, E_j, B_c, and D_c values. For κ>2 use the displayed
F forms. Before alignment simplifies the maxima, the same constants are

```text
E_g^F = ρ̄+Γ+max(P+3Δ+ε, 2P−Δ).
B_c^F = ρ̄+Γ+max(P−2Δ+ε, 2P−6Δ).
```

R≥κ gives 0≤ε≤P−8Δ, so these equal the simpler forms above.
At fixed R and other parameters, B_H≤B_H^F≤B_H+2ε.
The window adds no K term to healing. Put T_F=GST+B_H^F.
The eligible minimum bounds the same first reset row and healing gate.

The superscript (1) or (2) counts the lease allowances per repair, not the number
of repairs. HG.1–HG.6 and H.11 permit up to six repair charges.
After a served proposal reaches the frontier, same-frontier top-J and
contest events add no repair charge. Five charged restarts after the
cut are not shown to be necessary. H.6-S has
an explicit synchronous-window premise (S); H.6-C proves it for all
reset attempts when `k≤2R+1`. Since `k≥2`, `ρ₁<ρΓ`.
The general bound remains available for every k. All uses of the gap
in H.6, H.6-S, H.9, and H.18 start on the proposal grid.
Since G≤Γ, each gap witness at G also satisfies the bound Γ.
Recovery₂ requires finite G≥4Δ, hence Γ≥4Δ.
Strict delivery `<Δ` is required for θ.

For Δ_F≤2Δ, at `k=2,G=8Δ`, the adopted `B_H^F` is `295Δ` for R=2 and `343Δ`
for R=3. HG.7 adds a separate bound `B_H^ph,F` under `k≤2R+1`:
`268Δ` for R=2 and `312Δ` for R=3 at these parameters. The same
H.22 witnesses satisfy `t*<GST+B_H^ph,F`. N.2.5 gives window-checked lower endpoints `46Δ` and `62Δ` (WEAKER).
HG.7’s coefficient intervals are `[46,268]` and `[62,312]`; the integer
upper endpoints are one tick smaller. For the old 89/105 coefficients,
the old larger bound remains OPEN (not established, not refuted).

HG.8a adds the stronger separate bound `B_H^8a,F`, on the full Recovery₂
range `k≤2R+1`, for any finite G≥4Δ. For Δ_F≤2Δ its values at k=2, G=8Δ are
204Δ and 240Δ for R=2 and R=3. The old-fold integer intervals for Δ≥1 are
`[46Δ,204Δ−1 tick]` and `[62Δ,240Δ−1 tick]`, from N.2.5 and HG.8a.
HG.N2 retains five changes, with lower bounds `45Δ−1 tick` and
`61Δ−1 tick`; N.2 gives larger bounds at both parameter pairs.
For the old 77/93 coefficients, the old larger bound remains OPEN (not established, not refuted).

For R=3, 2Δ<Δ_F≤6Δ (κ=3), at k=2,G=8Δ, the corresponding
values are B_H^F=351Δ, B_H^ph,F=324Δ, and B_H^8a,F=252Δ.
The lower-bound intervals above retain their historical execution basis;
they are not new window lower bounds.

HG.7 and HG.8a do not redefine `B_H^F`. H.21 uses the adopted general bound; chapter 22, the outline, and the
spec must use the same bound. All retain the cut `u₀=a_(r_G+2)`. Its H.22 witnesses still satisfy
`t*<GST+B_H^F` and `HEALED(GST+B_H^F−1 tick)` in integer time.
Under an additional qualified-opening search bound `g_h P`, retain
`B_heal(g_h)=6ρ+(23+13g_h)P+G+64Δ` and use
`B_best^F(g_h)=min(B_heal(g_h),B_H^F)`. The optional proof retains its
looser settlement allowance `θ_Q=4Δ` and repair allowance ρ.

The current Recovery premise uses C1, K≥2, R≥max(2,κ), and δ_t=2R.
The adopted bound here is B_H^F. HG.7 and HG.8a remain separate
bounds. The registry pins older spec hashes.
Registry ids below identify the corresponding statements, with their
current-spec restatements given here. They do not silently change those pins.

The proof uses 01, 02 §3.1 plateau geometry via 01 §3.1a, and
02 §4.3 score algebra. These 02 imports do not read the row fold, R6,
or F/J provenance. Section 8 exports one theorem,
`HEALING_INPUT(t*)`, with its time bound. Chapter 22 imports that exact
statement. Output safety alone is not the finality interface.

## 2. Definitions and event order

`Recovery₂` consists of these premises:

1. The model, checked objects, authentic complete paths, collision freedom on full recursive
   named proposals in the delivered/held/ancestor run scope, increasing parent slots, actual event
   origins, honest stores that persist (no restart; cumulative storage), and the sufficient proof horizon of the current spec model.
2. The faulty identities form a static set of size
   `a≤f=⌊(n−1)/3⌋`. After GST all `h=n−a` honest identities are awake.
3. C1: blocks, complete block bodies, SA votes, and their relays use Δ.
   Standalone FG rows and their relays use Δ_F. DC receipt relay applies
   to accepted objects, with dependencies and its receiver exclusion:
   only a block incompatible with the receiver's `F` at the relay
   deadline can be excluded. Acceptance at time `t` supplies a handler
   call at `t′` with `t≤t′<max(t,GST)+Δ` for a block or SA vote, and
   `t≤t′<max(t,GST)+Δ_F` for an FG row, with dependencies present.
   These duties include pre-GST sends and acceptances, and sleeping
   receivers. A carried row is available with its complete block under Δ.
   Honest sends use the same family deadlines; relays use acceptance time.
   Votes and rows have no such exclusion. A handler call need
   not accept a third base vote from one seat. Checked FG rows have no
   identity quota.
4. Require finite `G≥4Δ`. For every trigger `t≥GST`, some honest
   proposal time satisfies `t<t_s≤t+G`. No opening recurrence is required.
5. Δ and Δ_F are positive integers with Δ_F≥Δ. Use k≥2, K≥2,
   R≥max(2,κ), and δ_t=2R. The time horizon contains all gap searches
   and all row, block, and SA-vote receipt intervals used in the claim. For an
   infinite-suffix statement, use an infinite run or all finite prefixes.

A signed HEAD identifier is (seat, slot, root identifier).
Repeated copies count as one vote. Equivocation requires two different
root identifiers for the same seat and slot. Resolve identifiers in the
cumulative store domain, then apply the active-view filter.

### Recurrence forms

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

For finality at `δ_t=2R` and `Δ_F≤2Δ`, define the forward predicates

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
For `Δ_F≤2Δ`, use `Rec_FE(g_f)`, or its special case `Rec_F4(g_f)`,
for any finite `G≥4Δ`. For κ>2 use the receipt-ready window predicates below.
FGood4 implies FGoodE; they coincide at R=2. Include the receipt interval
in the horizon. The old FGood case c=z+1 is WITHDRAWN (no-round):
a source can lag the head and cannot carry finality at the same height.

For κ>2, the forward window predicates are

```text
FGoodE_W(p) := Honest(pR) ∧ Honest((p+1)R)
  ∧ (∃c∈[(p+1)R+κ,(p+2)R], Honest(c)) ∧ Honest((p+2)R+κ).
FGood4_W(p) := FGoodE_W(p) ∧ Honest((p+1)R+κ).
Rec_FE_W(g) := ∀q≥1 with T_q≥GST, ∃p∈[q,q+g−1], FGoodE_W(p).
Rec_F4_W(g) := ∀q≥1 with T_q≥GST, ∃p∈[q,q+g−1], FGood4_W(p).
```

Require g≥1 and the complete carrier, receipt, and service horizon.
At κ=2 these reduce to the old predicates. The terminal +κ carrier
needs the window-retention proof in 22; transport alone is insufficient.
The old qualified search for healing keeps its definition for all κ.
The finality uses of Tail, Skip, and the strong predicates below are
restricted here to Δ_F≤2Δ; no large-delay port is inferred from them.

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

Write `ht(B)=σ[B].h`. Write `finheight(D)=σ[D].h_F` for a
finalization certificate carrier. Do not replace this by `ht(σ[D].F)`
without the entry lemma. Genesis has state height 1 and initial finalized
height 0. A later justification can name genesis at height 1.

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

```text
┌────────────────┬────────┬──────────────────────────────────────────┐
│ Time in slot s │ Offset │ Order                                    │
├────────────────┼────────┼──────────────────────────────────────────┤
│ t_s            │ 0      │ clock, expiry, proposal                  │
│ v_s=q_(s−1)    │ Δ      │ clock, expiry, release s−1, HEAD         │
│ e_s=d_(s−1)    │ 2Δ     │ clock, expiry, gate s−1, possible action │
│ z_s            │ 3Δ     │ strict freeze threshold                  │
│ q_s=v_(s+1)    │ 5Δ     │ expiry, release s, then next HEAD        │
│ d_s            │ 6Δ     │ gate s; FG action if s=rR                │
└────────────────┴────────┴──────────────────────────────────────────┘
```

Acceptance also checks the body encoding and full proposal digest and
requires the exact full named parent in the store.
Every receipt of a new block first checks `F⪯B`. A refusal returns before
any unpacking. Acceptance computes its state from its parent, adds and
stamps the block, handles carried base votes, and calls `update_finality`.
That call first updates `H=hmax`, then `(j,J)`, then tests and updates `F`,
then reconciles SA fields. Only after it returns are carried FG rows sent
to their pool handler. The immutable chain transition validates every row against the same
parent post-state. It sets height bits only for HeightMatch and finality
bits only for the exact WindowMatch. The window stays fixed during the
row fold. It selects the greatest ready entry above h_F, updates F, and
prunes entries at or below the new h_F. It then applies target
justification, otherwise mature progress. A target justification appends
an empty entry and retains the newest K entries. A mixed crossing adds
no entry. Height advance clears only target/progress bits. No row is
applied again to the new entry. Height advances at most once per block. A carried row
can affect this transition even if its pool handler later refuses it.

Reconciliation deletes incompatible leases and fast-write members, empties
incompatible saved results without reopening their labels, and sets `S:=F`
if necessary. It does not change the cumulative tree, stamps, signed pools,
client records, or `H`. The next duty reads the resulting live caches.
There is no tick or gate between the proposal at `t_s` and HEAD at `v_s`;
there can be receipts and an `F`, `J`, or `H` change. There is a pending
gate at `t_s+2Δ` between that HEAD and its release at `q_s`.

For a block set `V`, define

```text
contest := H=j+1 and ∃W∈Σ.T, ht(W)=H and J⋠W
(Z,lo)  := (J,H−1)  if H=j+1 and not contest
           (F,H)    if contest
           (F,H−1)  otherwise
D(V)    := {B∈V : F⪯B, Z⪯B, ∃W∈V, B⪯W and lo≤ht(W)}
A       := deepest live lease target in D(Σ.T), or Z if none
V_s     := {B∈Σ.T : stamp(B)<z_(s−1)}
           ∪ {B∈Σ.T : B⪯P for some admitted slot-s proposal P}.
```

The HEAD walks `D(V_s)` from `A`. Its score is the number of equivocating
seats plus clean declared supporters above the candidate. Its eligible
children have parent height `<lo`, strict score majority, or current slot.
The proposer uses `D(Σ.T)`. The SA confirmation walk uses `act(Σ)` from
F, with a strict majority of surviving early votes against all late
participants. Its final eligibility test also applies to F; a failed
test returns ⊥. It does not use `D`.

A block `B` is **kept at a duty** when either `B⪯Z`, or `Z⪯B` and `B`
has a witness in that duty's walk domain. A full-domain lease start above
`B` also suffices for a walk to cover `B`, even if the start has no child
in the frozen domain. Each use below specifies the applicable alternative.

A label `s` is synchronous when `v_s≥GST`. A **fast body at label s**
is a prefix `B` of an honest genuine result with `p(s,B)≥τ`. A successful
write additionally requires the whole-result guard. A **slow body** has
an actual successful write and all `k` genuine results in its local
window above `B`. Neither definition replaces a vetoed genuine result
by an output, nor requires that every result in a slow window wrote `S`.

A **settled phase** fixes the global honest frontier `m`, the presence
and identity of its top justification at `m−1`, and its contest status,
after their evidence has settled. Lower finalizations can move. The phase
stops at a rise, the first top justification, or the first contest.
The word “permanent” within a phase always stops at that endpoint.

Define `HEALED(t*)` exactly as the following suffix property:

```text
For all honest x,y and all event states at times t≥t*:
  S_x(t) and S_y(t) are compatible;
  F_x(t) ⪯ S_x(t).
For all honest x and states t*≤t≤u:
  S_x(t) ⪯ S_x(u).
For each honest proposal P of slot s with t_s≥t*, and every honest x:
  P ⪯ S_x(d_s), where d_s=t_s+6Δ.
```

Compatibility is ancestry comparability, not equality. Monotonicity
starts at `t*`; it does not preserve arbitrary outputs from before `t*`.
This is the spec's healing predicate (lines 1897–1901). It makes the
base safety and `6Δ` proposal service available again. It does not state
that all nodes have equal caches, that finality has advanced, or that a
new outage has the genesis-based P1 premises. Section 8 also supplies the
source-history clauses in the single finality interface.

## 3. Imported foundations

These are the full interfaces used from foundations. Their short proofs
are included to avoid dependence on a parallel document's completion.
All facts refer to reachable event prefixes of the adopted spec.

### IF.1 — Tree, state, and event origins — PROVED

**Statement.** The admitted tree is cumulative and parent closed. Every
stored state is its block's immutable derived state. State height is
nondecreasing along ancestry and changes by at most one on an edge.
An entry at height `c` stays fixed until that height is crossed. Every
successful lease deadline has a last actual write label `w` and value
`d_w+L=q_(w+k)`. Every saved nonempty result is an actual gate result at
its label; a later reconciliation can only empty it. Each non-finality
origin of `S` is a successful gate result, of block slot at most its label.

**Proof.** Induct over events. Initialization has only genesis. A block
handler inserts only after checking its parent, never changes an existing
state, and has no deletion branch. Its transition changes height only in
`advance_height`, once, and assigns its own block as the new entry.
Between advances it leaves the entry unchanged. A gate saves its result
once and writes deadlines `d_w+L` by maximum. Since labels and gate times
increase, a maximum deadline has the stated actual last write. Expiry,
release, and reconciliation only remove it. The saved-result and output
claims follow by enumerating the gate and reconciliation assignments.
A vote resolving for label `w` has head slot at most `w`. Every nonempty
result, including F itself, passes the final strict-majority test and
has a surviving support head K above it. Thus F.slot≤K.slot≤w, and
every returned descendant has that slot bound too. Spec
lines 473–612, 867–1072, 1081–1350 give all these assignments. ∎

### IF.2 — Counts and honest client safety — PROVED

**Statement.** Under `a≤f`,
`h≥q_F≥τ>a`, `h>2a`, `2h>n`, and `2q_F−n>a`.
Two quorums of size at least `q_F` intersect in an honest identity.
No two honest row occurrences satisfy E1 or E2.

**Proof.** `3a≤n−1` gives `h=n−a>2a` and `h>n/2`.
The ceiling definitions give `h≥⌈2n/3⌉≥⌈n/2⌉>a` and
`2⌈2n/3⌉−n≥⌈n/3⌉>a`. For two subsets of `n` identities,
`|Q∩Q'|=|Q|+|Q'|−|Q∪Q'|≥2q_F−n>a`.
For E2, the first target is recorded before release; a later different
source cannot produce a different target. It produces a timeout or an
empty pair. For E1, a recorded timeout prevents a finality pair at that
height. A prior different target prevents that pair too. Conversely, a
recorded finality lock forces a matching target or an empty height pair
and excludes a timeout. The same-row finality pair is used as a lock
before the height pair is formed. The final create_attestation adds two
cases (spec de183d7d, attestation client): the sent-set test sends no row,
and h≤h_f removes the finality pair before recording. Neither case creates
E1 or E2. Sleep and reconciliation do not erase the record. ∎

### IF.3 — Certificates, uniqueness, and finalized crossing — PROVED-paper

**Statement.** (a) Each crossing of height `c` has an ancestor entry `E`
at that height and at least `q_F` distinct height pairs naming `(c,E)`.
Each justification has `q_F` target pairs for its entry. Each nonzero
finalization has a preceding justification and `q_F` matching finality
pairs. Each such height quorum has an honest row and its genuine fast
source. (b) There is at most one justified entry at each height.
(c) If a block `D` finalizes `F` at height `x` and `ht(C)>x`, then
`F⪯C`, provided D and C are in the RD2 run scope.
For (b) and (c), the compared carriers must be directly delivered full
proposals, full proposals held by an honest node at some event prefix,
or ancestors of such proposals. A private carrier qualifies only through
one of these scope seeds; later disclosure qualifies through delivery.

**Proof (W1 — window certificate origins).** For (a), induct along a
block's ancestors and within each row fold. A set bit has a matching signed occurrence. Bits are indexed by
identity, so repetitions do not add signers. Target and progress bits are set only by HeightMatch and cleared on
a height change. Each finality bit belongs to one window entry and is
set only by a signed pair for that exact entry. Each entry was created
by a target quorum on this chain. The greatest-ready test selects an
actual finality quorum. Pruning a lower entry creates no certificate
for it. Inherited finality keeps its original witnesses. Stale height
pairs enter neither height quorum. Thus all three threshold tests have
the stated distinct signed witnesses. An honest nonempty height pair uses a
fresh fast body at the immediately preceding opening gate by the selector.
For (b) and (c), scope covers both full ancestor chains, so equal roots
identify equal full entries before IF.2 is used.
For (b), intersect two different target quorums at one height. IF.2 gives
an honest signer of both different targets, which is E2.
For (c), if `x=0`, `F` is genesis. Otherwise follow `C`'s path to its
crossing of `x`, and call its entry `E`. Intersect that progress quorum
with the finality quorum for `(x,F)`. If `E≠F`, each intersection signer
has either a timeout at `x` or a different target there, and a finality
pair for `F`. This is E1, contradicting IF.2. Hence `E=F` and `F⪯C`.
This proves the in-scope private-carrier case; honest holding or ancestry
can supply scope without direct delivery. ∎

**DC port.** DC paper lines 698–779 and 2213–2279 give the state and
certificate rules; lines 717–729 give E1/E2. The checked declaration is
`DecoupledConsensusModel.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt`
in `DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50`.
Its inputs include collision freedom on the compared ancestor chains and a slashable bound.
D and C are in the stated RD2 run scope, which is ancestor-closed;
this supplies collision freedom on both compared full ancestor chains.
Here use fixed unit weights and IF.2 for that bound; deleting the NJ latch
does not change this certificate proof. The current SA repository also
has `height_crossing`, `finality_certificate`, and
`justification_certificate` in `AvailableChainKitFG/Certificates.lean`.
This is a certificate port, not an import of DC recovery.

### IF.4 — Live caches, lease chain, and output nesting — PROVED-paper

**Statement.** At a node, `F` only advances by ancestry, `(j,J)` only
increases lexicographically, `H` never decreases, `F⪯J`, and `j<H`.
Under Recovery, a maximum-height carrier extends the node's current `F`.
Live lease targets are on one ancestor-closed chain (apart from omitted
genesis), and every live target precedes `S`. At every node, for every
fault count, `F⪯S` after each event.

The finalization and height-H carriers are held in honest cumulative stores.
**Proof (W1 continued).** Window entries and the latest J are justified
ancestors in increasing certificate-height order. Selection of an entry
older than J therefore preserves h_F≤h_j<h and F⪯J on the chain.
The cache assignments and their tests give monotonicity.
Every justification at `j` has a carrier at height at least `j+1`,
so `j<H`. A new `F` is tested below current `J`; a new `J` is tested
above current `F`. A finalization has height below its carrier's state
height, which is at most `H`. IF.3(c) puts every height-`H` carrier above
it. Before a lease write the whole-result guard checks all live targets.
Every written target is a prefix of the same result; thus the chain
property persists. A prefix has at least its descendant's support and
all its slow-window inclusions. It receives a deadline at least as large.
A vote conflicting with a prefix also conflicts with the descendant;
release cannot remove a prefix and retain that descendant. Expiry has
the same implication. Reconciliation preserves ancestor closure on the
remaining compatible chain. A new target precedes its gate result and
therefore the resulting `S`. For a retained target `K⪯S`, a later
successful result `C` is compatible with K. If `C⪯K`, then `C⪯S`
and `advance` keeps S. If `K⪯C`, its possible new output covers K.
On normalization to a new F, a retained K is compatible with F; if
`F⪯K⪯S`, normalization would not be needed. Hence in the normalization
case `K⪯F`, so the target still precedes S. Removals have no adverse
effect. This proves the target-to-output invariant. For nesting, a gate
either keeps `S` or uses `advance`, then normalizes. An `F` advance normalizes in its handler.
All other events leave both fields unchanged. ∎

### W3 — Causal origin of window finality — PROVED-paper

Let a window transition finalize E at certificate height x>0. W1 gives
its target and finality QCs. Select an honest finality signer. Use the
justification read by that signer at its action; it need not be the
literal carrier of the eventual window entry. Select an honest target
row in that justification, with actual source K at height x and E⪯K.
The target action strictly precedes the finality action. Action reads
precede own-row processing and same-time deliveries, and a target QC
must first enter a derived block state. Thus the actions obey

```text
target action d_s < finality action ≤ accepted finalization;
finality action ≥ d_s+P;  P≥8Δ>4Δ.
```

The low-F carrier is honestly stored; C* is an honestly held source.
Stale carriage, greatest-ready selection, and late disclosure change
neither signed origin. IF.3(c) puts a low F below C*. For a high F,
H.13–H.18 use this earlier target source: it transfers to every output
by d_s+4Δ, before finality can be accepted. These facts also cover an F
accepted before the healing cut. The selected entry need not be latest J.

### IF.5 — Receipt transport and admission or coverage — PROVED-paper

**Statement.** Suppose a required prefix `B` is compatible with the
receiver's `F` at a read. If `F⪯B`, a relayed support head above `B` and
its required path can be admitted by the receipt deadline. If `B⪯F`,
that receiver's output and every choice head cover `B`, and it has no
live lease conflicting with `B`. For a vote in its admission window,
a required handler call leaves either that vote or two distinct votes
of its seat in the retained pool. Every checked honest row is retained
without clock expiry. Its standalone send and relay use C1's
`max(t,GST)+Δ_F` deadline; blocks and SA votes use Δ. None of these claims asserts acceptance of every
faulty signature.

**Proof.** In the first case the receiver exclusion cannot reject a head
above `B`; its missing suffix extends `F`. Process dependencies in parent
order. A stored ancestor requires no new acceptance. In the second case,
IF.4 and the root/anchor rules give coverage, while reconciliation deleted
every incompatible lease. If `F` changes during transport, apply this
split at the read: a move past `B` changes the obligation to coverage,
without extending the deadline. For votes, the only remaining refusal
cases are duplicate and cap two. A duplicate is already held; cap two
provides the two distinct signed HEAD identifiers. For an honest row, checked full-content
deduplication retains the row; there is no age test or identity quota.
Use 01 §1.1 T-ROWS and the current spec, Pools, R6-window, and Inclusion. ∎

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

### W2 — Carriage and separate bit effects — PROVED-paper

Fix selected rows for (c,E). If the final parent still has height c
and entry E, new carriage uses HeightMatch and sets progress. If an
exact row is already on that parent path, its earlier occurrence could
not use the stale arm: that would require an ancestor height above c,
contrary to nondecreasing height and the final height c. It therefore
used HeightMatch above E. No height advance has cleared its bit. If
the final parent crossed c, the required progress is already complete.
R6-window validity alone does not imply a height bit.

A matching finality bit persists with its exact window entry until
finalization/pruning or capacity eviction. If an earlier occurrence
found no matching entry, that lower certificate height cannot be
created later: its signed h_f<h, and either admission arm has chain
height at least h. Height never decreases. An evicted entry never
returns. Thus exact-row exclusion removes no later useful effect;
it does not prove retention after eviction.

R7 selects all eligible full-content rows from pools and admitted
blocks, except exact duplicates and exact rows on the parent chain.
One identity can have several useful old finality rows and a separate
current-height row. R7's optional omission keeps every effect (01 §1.1),
so this argument is unchanged.

### IF.6 — Same-label compatibility and honest support — PROVED

**Statement.** At a synchronous label, all honest nonempty genuine results
are pairwise compatible, including vetoed results. Every such result has
an honest supporter. Every fast body has an honest supporter.

**Proof.** Let two conflicting results have surviving supporter sets
`U,V`, of sizes `p,q`. If one seat belongs to both, its two different
signed heads relay into both late pools before the cutoff, either as
those signatures or as equivocation evidence by IF.5. That seat could
not survive either support test. Thus `U,V` are disjoint. Every seat
in their union participates in both late pools: early acceptance before
`e_s` relays before `e_s+Δ=z_s<d_s`; the label is still current or
previous. Hence `D_x,D_y≥p+q`. The two genuine tests give `2p>D_x`
and `2q>D_y`, whence `p>q` and `q>p`, a contradiction. Head exclusion
does not remove participation or equivocation evidence. Finally all `h`
honest votes are in each late pool. Faulty-only support would have
`p≤a` and `D≥h+p`, contradicting `2p>D` and `h>a`. Fast support
has `p≥τ>a` directly. ∎

### IF.7 — Reconciliation preserves required slow histories — PROVED

**Statement.** If `F⪯B`, a saved result covering `B` cannot be emptied
by reconciliation with that `F`. If a later `F` covers `B`, the lease
protection obligation for `B` is discharged by finality. Removing active
heads incompatible with `F` contributes zero clean score on every
candidate above `F`; their signed votes still contribute participation
and equivocation. The carried-support arm continues to read `Σ.T`.

**Proof.** A saved result above `B` also extends `F`, so the deletion
predicate is false. In the second case apply IF.5. A head incompatible
with `F` cannot descend from a candidate above `F`, by transitivity.
Its support indicator for that candidate is zero. The spec retains
signatures and the admitted proposal containers, so the remaining score
terms are unchanged. This proof makes no assertion about a slow predicate
for a strict ancestor of `F`; its renewal may be lost and is unnecessary
for choice protection. For comparison with the genesis walk, a result
lost at its original gate satisfies C_j≺F_j⪯F_now. It cannot cover a
target B with F_now⪯B, so the slow test for B agrees in both executions.
If finality has passed B, use coverage instead (01 §6.5). ∎

## 4. SA transfer and the full-store witness

### H.1 — Majority transfer, release, and the pending gate — PROVED

**Statement.** Let `s` be synchronous, `C` a genuine result at honest `x`,
and `B⪯C`. Put `p=p_x(s,B)` and `D=D_x(s)`, so `2p>D`.
Suppose `B` is kept at the next honest HEAD reads, or covered by their
root/anchor, and no conflicting lease survives their expiry/release.
Then all honest HEADs at `q_s=v_(s+1)` cover `B`. If `p≥τ`, the
no-conflicting-lease premise follows from release. If `B` has a slow
window of synchronous results, that premise follows from the window.

**Proof.** Consider a receiving HEAD that is not already covered by
finality. Each of the `p` clean early votes and its head is present before
`e_s+Δ=z_s` by IF.5. Suppose one such seat has a second vote in that
reader's frozen pool or an admitted current proposal before `q_s`.
The second signed HEAD identifier was accepted there, or the pool already
has two distinct identifiers for that seat and slot. Relay of those votes reaches `x` before
`q_s+Δ=d_s`, while the admission window remains open. Thus `x`'s
supporter could not survive. All `p` seats are clean at the HEAD.
Every participating HEAD seat occurs in `x`'s late denominator, by the
same reverse relay, with cap-two evidence allowed. If `V` is the HEAD
participant count, then `V≤D<2p`. Each child toward `B` has score at
least `p`. A conflicting child has score at most `V−p<p`, including
all equivocators. The path to `B` is eligible and wins each comparison.
A compatible anchor is either above `B`, which gives the conclusion at
once, or on its ancestor path, where this edge argument applies.

For release, the same `p` resolved nonequivocating votes conflict with
any target conflicting with `B`. Thus the count is at least `p≥τ`.
If finality already covers `B`, reconciliation has removed the conflict.
For the slow case, let a surviving conflicting lease have last write
label `w`. The release precedes gate `d_s`, so `w≤s−1`. Its deadline
is `q_(w+k)>q_s`, so `w+k>s`, and hence `s−k+1≤w≤s−1`.
The source's saved result at `w` covers `B`; that lease's genuine origin
at `w` covers its conflicting target. IF.6 forbids these two results.
A write with `w+k≤s` expired before the HEAD at equality. IF.7 handles
reconciliation of the saved results. These cases exhaust all live leases.
The pending gate `d_s` occurs **after** this transfer HEAD. Its result is
compatible with `C` by IF.6, so it cannot install a conflict. ∎

**SA comparison.** This is the argument behind
`AvailableChain.GridCO.transfer_of_stronger_rows_from_engine`,
`AvailableChain.SA.fast_source_permanent_support`, and `AvailableChain.SA.slow_window_rows_compatible`.
Their Lean run parameter is the plain SA engine. Here IF.5 replaces
unfiltered head transport and the kept-path premise replaces its unrestricted
tree. No invocation substitutes FG-SA for that engine parameter.

### H.2 — Continued support under kept paths — PROVED

**Statement.** Under H.1, if `B` remains kept and compatible with finality
at every later choice duty in an interval, then throughout that interval:

```text
S1: all honest HEADs at labels i≥s+1 cover B;
S2: every honest proposal parent at slots u≥s+2 covers B;
S3: all honest outputs from d_(s+1)=d_s+4Δ cover B.
```

This applies to fast bodies and fully synchronous slow bodies, and to
a genuine body whose first transfer has no conflicting lease.

**Proof.** H.1 is S1's first label. Its pending gate cannot write a
conflicting lease. All `h` honest next-label votes are early and clean
where `F⪯B`; they give `p(i,B)≥h≥τ`, `2h>n≥D_i`, and release every
conflict at the next release. Where `B⪯F`, use coverage. The confirmation
walk from the eligible `F` must pass the suffix to `B` when `F⪯B`:
each such edge has honest score at least `h`, and each conflicting edge
at most `a<h`. Thus its result extends `B`; when `B⪯F`, coverage suffices. If the guard passes, `advance` either
keeps an extension of `B`, extends it, or replaces a conflicting old
output by this result. If the guard fails, a live target K conflicts with
that result but is compatible with B. It cannot precede B, since B
precedes the result. Therefore `B≺K⪯S` by IF.4, and the unchanged output
already covers B. Normalization also covers B. This proves S3 at the
first such gate and at every subsequent event, provided finality stays
compatible. An incompatible finality was explicitly excluded by the
premise; a compatible one leaves the output above `B`.

At a proposal of slot `u≥s+2`, the previous batch already covers `B`.
All leases that survived the first transfer are compatible; later writes
have genuine origins in these batches or in the initial same-label batch.
Thus the anchor is compatible. Honest score `h` beats every off-path
score, at most `a`, along the kept path. The parent covers `B`. This
proves S2. The next release and H.1 give S1's next label. Induction on
labels, with the intervening receipt, release, and gate cases just given,
proves all three statements. ∎

### H.3 — Anchor geometry and witness W (`ap.headReachesLo.v7`, 1–4) — PROVED

**Statement.** For any HEAD, if `A∈D(V_s)` or `A` has an eligible child
there, its result belongs to `D(V_s)` and has height at least `lo`.
Otherwise it returns `A`, even if `D(V_s)` is nonempty. If `A=Z` and
`D(V_s)` is nonempty, then `Z∈D(V_s)`.
In a settled Recovery phase with settlement time `u≥GST`, every
honest HEAD `K` at `v_s≥u` is in the **full**
domain and has a full-store witness `W⪰K` of height at least `lo`.
Every honest receiver admits that witness and its needed path before
`e_s=v_s+Δ<z_s`. For a source `B⪯K`, the receiver either retains this
witness path or already covers `B` through finality.

**Proof.** Once the walk is in its domain, a returned node below `lo`
would have a proper descendant witness. The first child on that path
belongs to the domain by ancestor closure and has a below-band parent.
It is eligible, contrary to termination. If there is no first eligible
child from an outside start, the loop returns that start. For `A=Z`,
any domain witness has `Z` on its admitted ancestor path; `Z` itself
therefore belongs to the domain.

For the full-domain claim, select a height-`H` carrier from the cumulative
store. IF.4 puts it above `F`. If the frame roots at `J`, absence of a
contest puts it above `J`. It witnesses a nonempty full domain and its
root. Thus `A` is in the full domain. The frozen domain is a subset of
that domain, because each of its witnesses is also in `Σ.T`. Every step
from `A`, including a zero-step return, remains in the full domain.
Its membership provides `W`.

W is in the honest HEAD holder's tree; the receiver holds its F carrier.
In a gap or contested phase a receiving finalized height is `<lo`.
IF.3(c) gives `F_receiver⪯W`. In a top-J phase all such witnesses extend
common `J`, which extends every receiving `F`. Hence DC's receiver
exclusion cannot exclude `W`. The witness was admitted by the honest
HEAD holder no later than `v_s`; strict relay supplies it before `e_s`.
Apply IF.5 to each needed prefix `B`. The proof does not claim
`ht(K)≥lo` when `K` is an outside anchor. ∎

**DC port.** DC paper lines 875–901, 1953–2000 and 2006–2018;
`fixedHeight_voterCandidateTree_subset_filtered` in
`RecoveryStableProposalCapture.lean:50` and `Protocol.get_sg_root_with` and `Protocol.get_head_in_tree_with_layer`
in `ForkChoice/Head.lean:38–49`. The domain-subset proof is unchanged. Replace
DC's grade-1 active prefix by the deepest live lease in the full filtered
tree. FJ supplies `lo` to both viability and eligibility. The current
`AvailableChainKitFG/Correspondence.lean` has `mem_filteredFrom`,
`filteredFrom_Z_mem`, and `filteredFrom_viable_child`; none by itself
states that an outside-anchor HEAD reaches `lo`.

### H.4 — Source permanence in one settled phase — PROVED

Outline id: `bp.phaseSourcePermanence.v2`.

**Statement.** A synchronous fast body, or a successful slow body with a
wholly synchronous in-phase window, satisfies S1–S3 until the phase ends.
For a prefix overtaken by finality, interpret those conclusions as coverage.

W is honestly held by H.3; every lower-F carrier is honestly stored.
**Proof.** IF.6 gives an honest supporter `K` of its genuine result.
H.3 gives `B⪯K⪯W` and transports `W` before the next freeze.
The root is unchanged except for lower `F`. In an F-root phase IF.3(c)
keeps `W` above each such `F`; in a top-J phase `J⪯W` throughout.
Thus `B` is kept at the first transfer, or covered. H.1 supplies release
or slow-window expiry and the first common HEAD batch. For each later
batch, an honest HEAD is itself below some full witness by H.3. Transport
that witness before the next freeze. The common HEAD extends `B`, so its
witness does too. This supplies the kept-path premise afresh for the next
step of H.2. A full proposal read contains these relayed witnesses.
IF.7 preserves any still-needed slow history. Induction by labels now
proves the statement without assuming that a low HEAD is itself a witness at the floor. At an effective event stop the induction; its next phase starts
with a new repair. ∎

### H.4-S — Source permanence with an earlier synchronous window — PROVED

**Statement.** In H.4, replace “wholly synchronous
in-phase window” by the following weaker premise for a successful slow
body B at label s:

1. Every label in `[s−k+1,s]` is synchronous.
2. The HEADs of label s are in the settled phase.
3. That phase persists for the part of S1–S3 being asserted.

The earlier `k−1` window labels may be in earlier phases. A fast body
still needs only a synchronous current label in the settled phase.

**Proof.** IF.6 applies at each synchronous label independently of its
frame. Let a conflicting lease survive the release at `q_s`. By IF.1,
its last write w satisfies `w≤s−1` and its deadline is `q_(w+k)>q_s`.
Thus `s−k+1≤w≤s−1`. The slow source's saved result at w covers B.
The conflicting lease has an actual genuine origin at that same label
which covers its target. These two results conflict, contrary to IF.6.
If `w+k≤s`, expiry removed the lease before the HEAD, including equality.
This is the slow case of H.1. It never compares the frames at w and s.
IF.7 supplies the same reconciliation cases as in H.1.

At the current label s, IF.6 supplies an honest supporting HEAD K for
B. Since this label is in the settled phase, H.3 gives a full-store
witness `B⪯K⪯W`, with height at least lo. Its relay makes B kept at
the next HEAD, or finality covers B. Thus H.1 gives the first transfer.
For a fast body, H.1 instead uses its threshold release.

The compared witness and lower-F carriers are held in honest stores.
The gate at `d_s` is pending at that transfer. IF.6 makes its result
compatible with the source result, so it cannot write a conflicting
lease. From this point H.2 and the witness induction in H.4 apply in
the fixed phase. Every new batch supplies the next witness by H.3.
Lower F moves are handled by IF.3, IF.5, IF.7 and H.5. This proves
S1–S3 until the phase ends. No previous-window frame premise is used. ∎

This lemma does not assert permanence across the **next** phase change.
It only removes a premise about the source's earlier slow-window labels.

### H.5 — Lower F moves and score transport — PROVED

**Statement.** For a fixed ancestor-closed duty set `V` in one phase,
a move `F⪯F'` deletes from `D(V)` only the strict ancestors of `F'`
in an F-root phase, and leaves `D(V)` unchanged in a top-J phase.
Write D_F(V) and D_F′(V) for the domains before and after the move.
For the walk comparison, assume a settled phase at `u≥GST` and
nonempty domains. The **selected path** is the finite sequence
`π=(X₀,…,X_m)` visited by the lower-start deterministic walk, with
each next vertex the chosen eligible child. A **common retained pivot**
is a vertex `K=X_i∈D_F(V)∩D_F′(V)` whose suffix
`X_i,…,X_m` stays in both domains. Assume that the lower start
reaches K and that the other start is `X_j` for some `j≥i`.
The retained path has its witnesses in V. The walks choose the same
continuation from `X_j` and have the same endpoint. The pivot can
be F′ when F′ is retained. Compatible starts on different branches
do not satisfy these path premises. At an honest
proposal, merged HEAD participation, equivocation, and scores on retained
candidates agree with the proposer's values, even when the raw vote sets
are different.

V is an honest duty set, so its witness and the F' carrier are honestly held.
**Proof.** A witness of height at least `lo` extends `F'` by IF.3(c)
in the F-root case. A former member and `F'` are both ancestors of that
witness, so a removed member is a strict ancestor of `F'`. No block can
enter on strengthening the ancestry test. A top-J domain already extends
`J⪰F'`. On a nonempty removed trunk there is one domain child toward
`F'`, eligible below `lo`. A start below `F'` reaches it. On the retained
suffix, both domains have the same candidate children:
only the trunk below F′ was removed. Their scores are unchanged by IF.7;
the floor, child slots, and root tie order are unchanged in the fixed
phase. At X_j, both walks therefore choose the same next child, or both
stop. Repeat this argument along the finite suffix of π to X_m.
The assumed lower-start path supplies the steps to K and then to X_j;
the unique-trunk argument supplies them when that path runs to F′.
Thus the proof uses the stated pivot and continuation premises, including
a start strictly above K. Coverage handles a start already beyond a
protected prefix. An empty frozen domain is
outside this walk-equality conclusion; no equality of fallback returns
is used.

Let the honest proposal carry ordered signed raw HEAD and support lists.
Write Q and U for their sets of signed HEAD identifiers, with U⊆Q.
The signed lists retain their order and repeated entries.
Its admission returns both as metadata, even if vote handlers refuse
individual third copies. Every extra frozen vote in a receiver's merge
was accepted before `z_(s−1)` and reaches the proposer before `t_s`,
or finds two distinct signed HEAD identifiers there. If it is not in `Q`, its seat
already equivocates in `Q`. Each extra frozen support vote on a retained
candidate has a head above the relevant `F`; relay of that head makes
it resolved at the proposer, or its seat already equivocates. Hence
additional signed HEAD identifiers cannot add participants or equivocating seats.
For a clean seat the support indicator on the retained suffix is the
same. For an equivocator its score was already one on every branch.
These exhaustive seat cases prove equal scores and majority eligibility.
The original signed support list supplies the support set; the receiver never recomputes it. ∎

### H.6 — Two-lease repair and common pivot — PROVED

Registry counterparts: `ap.repair.movingF.v1` and `ap.headReachesLo.v7`,
clause 5.

**Statement.** Let a settled phase start at time `u≥GST`. Let `β` be the
first proposal label strictly after `u`, and `ℓ=β+2k−1`. Every honest
proposal `P` at `t_s>t_ℓ`, while the phase persists through its gate,
is the exact HEAD at every honest reader and has a successful fresh
fast write at `d_s`. If the phase persists through `u+ρΓ`, such a gate
occurs by `u+ρΓ`, where `ρΓ=2L+Γ+8Δ`; otherwise the phase has ended within this budget.
After that first gate the same service holds for every later honest
proposal in the phase. No assertion here preserves all earlier damaged
outputs.

**Proof.** A lease with last write label `w≤β+k−2` expires by

```text
d_(β+k−2)+L = t_(β+2k−1)+Δ = t_ℓ+Δ,
t_ℓ = t_β+2L−2Δ.
```

A later lease is either fast with label at least `β`, or slow with all
window labels at least `β`. H.4 supplies its common honest support.
If `F` passes its target, IF.5 supplies coverage instead. An honest
proposal strictly after `t_ℓ` is on the slot grid and has time at least
`t_ℓ+4Δ`, after the expiry boundary. The preceding honest vote batch
covers every remaining lease at every reader. Before each such target,
the ordinary full-domain walk from the FG root has score at least `h`
on its path and at most `a` on a competing edge. Its kept path is
eligible and wins. Therefore all those targets precede the ordinary
parent `A_P`. The proposer's actual lease start is on that same walk,
so its parent is also `A_P`. At the same-slot HEAD, no new gate has
run; expiry, release, and reconciliation only remove leases or supply
finality coverage. Its live start is on this parent path as well. This
is the common pivot.

The full proposer domain is nonempty by H.3 and its walk ends at height
at least `lo`.

**Receiver exclusion.** A_P is the selected parent in the proposer's
full admitted tree, before P is created; thus it is honestly held.
H.3 and the nonempty full proposer domain give `ht(A_P)≥lo` at this
proposal duty, without using P's admission or its gate. A_P and each
reader's stored finalization carrier are in the ancestor-closed RD2 scope.
While the phase persists, in a gap or contest each reader's finalized
height is `<lo` (H.3), so scoped IF.3(c) gives `F⪯A_P`. In top J,
IF.4 and membership in the J-rooted parent domain give `F⪯J⪯A_P`.
Thus `F⪯A_P≺P` at every receiving read before the HEAD. Receiver
exclusion cannot reject P or its needed parent path. C1 strict delivery
with dependencies present therefore admits P before `t_s+Δ=v_s`.

Each frozen old competitor at a HEAD, together with its
in-view witness, was accepted before `z_(s−1)` and relays to the proposer
before `t_s`, or lies on the current proposal's path. At an honest slot
there is exactly one authenticated current proposal. Thus every off-path
competitor was already a proposer competitor. If a reader starts below
the proposer's `F_p`, H.5's trunk argument
first takes the unique domain child at each strict ancestor of `F_p`;
its parent is below `lo`, so that child is eligible. On the retained
suffix H.5 gives the same scores, eligibility, and root tie order. The
selected path persists in
the HEAD view through `A_P`, whose own height witnesses that path.
Starting at the common pivot, induction on the finite parent path keeps
the proposer's chosen maximum at each edge: it remains present, and all
other HEAD candidates belong to the proposer's set. At `A_P` no old
eligible child exists. The sole current-slot child `P` is present and
eligible. No valid child of `P` has slot at most `s`. The HEAD is `P`.

All `h` votes for `P` are early and clean. At `q_s` they release all
conflicts, including any lease from the pending gate at `t_s+2Δ`.
No gate intervenes between `q_s` and `d_s`.
By 01 §6.6, `F≺P` at `d_s`; the h votes make F eligible, so the genuine walk from F reaches `P`; a proper child would have slot greater
than `s`, so cannot have valid slot-s support. The result is exactly `P`,
the guard passes, and `p(s,P)≥h≥τ` gives a fresh fast write.

The trigger t_ℓ is on the proposal grid. The proposer-gap premise supplies `t_ℓ<t_s≤t_ℓ+G≤t_ℓ+Γ`. Since
`t_β≤u+4Δ`, its gate satisfies
`d_s≤u+4Δ+2L−2Δ+G+6Δ=u+ρ≤u+ρΓ`. Repeating the same last-write and
path argument at any later honest slot proves the last assertion. ∎

**DC port.** Paper lines 211–230, 2006–2038, 2055–2075;
`DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer.persist` and `.reflect` in
`DecoupledConsensusInternal/Definitions/NamedProposalPivot.lean:69`, and
`fixedHeightJustificationRoot_namedOpeningVoteStoresExtend` in
`RecoveryStableProposalCapture.lean:78`. The finite walk comparison is
DC's. H.4 and the deadline calculation replace its SG pivot premises.
The SA comparisons are `AvailableChain.SA.recoveryBoundary_time`,
`AvailableChain.SA.admitted_sources_after_two_leases`, and
`AvailableChain.GridCO.honest_proposal_heads_of_ordinary_parent`; H.3–H.5 discharge the new
filtered-domain obligations; H.6's receiver-exclusion step discharges
P's admission obligation explicitly.

### H.6-S — Repair after synchronous slow windows are available — PROVED

**Statement.** Let a phase be settled at `u≥GST`.
Let b be the first HEAD label with `v_b≥u`. Assume

```text
v_(b−k+1) ≥ GST.                                      (S)
```

Put `ℓ=b+k`. Each honest proposal P at `t_s>t_ℓ`, if the phase
persists through its gate, is the exact HEAD at all honest nodes and
has a successful fresh fast write there. The first such gate is
strictly before `u+ρ₁`, or an effective event ends the phase within
that budget. The same service holds for later honest proposals in the
phase. This is H.6's conclusion with a different expiry calculation.

**Proof.** Separate live leases by their last actual write label w.

If `w<b`, IF.1 bounds the deadline by

```text
d_(b−1)+L = t_b+L+2Δ = t_(b+k)+Δ = t_ℓ+Δ.             (1)
```

If `w≥b`, a fast body has its current HEADs in this phase. A slow body
has all window labels synchronous by (S), even if some precede this
phase. H.4-S gives the common support needed for both kinds of lease.
It also handles every renewal: use the last actual write, not the
lease's first appearance. Finality coverage supplies the usual exception.

For an honest proposal strictly after `t_ℓ`, the slot grid gives
`t_s≥t_ℓ+4Δ`. Its preceding HEAD time is
`v_(s−1)=t_s−3Δ≥t_ℓ+Δ`. Thus every lease in the first case has
expired **before this HEAD duty**, not merely before the proposal.
Equality is valid because expiry precedes the HEAD. Every lease in
the second case is covered by this preceding honest batch, by H.4-S.
This includes a last write at `s−2`: its H.1 transfer is precisely
that preceding HEAD, before the pending gate which writes the lease.

Now use the common-pivot part of H.6. Each remaining target is on the
ordinary full-domain parent walk: along its kept path, honest score h
beats every competing score, at most a. The actual lease start is on
that walk. Between the proposal and its HEAD, expiry, release and
reconciliation cannot add a lease. H.3 makes the full parent a witness
at the floor. H.5 transports scores to the retained suffix. Every
frozen competitor was already a proposer competitor. H.6's receiver-exclusion
step applies to the honestly held full parent at height at least lo,
so P is admitted before v_s and supplies its complete path. The same finite walk therefore
ends at P for each honest HEAD.

The h votes for P are early and clean. Their release at `q_s` removes
every conflict, including one from the intervening gate at `t_s+2Δ`.
There is no gate between this release and `d_s`.
By 01 §6.6, F≺P at `d_s`; the h votes make F eligible, so the walk from F returns exactly P; its guard passes and it fast-writes P. This is
the last part of H.6 without a change.

Finally, the definition of b gives `t_b<u+3Δ`. Apply the gap at
`t_ℓ=t_b+L+Δ`, a proposal-grid time. The selected honest gate obeys

```text
d_s ≤ t_ℓ+Γ+6Δ = t_b+L+Γ+7Δ < u+L+Γ+10Δ = u+ρ₁.
```

If the phase ends earlier, stop the attempt at that effective event.
The same last-write split proves service for each later honest proposal
while the phase persists. ∎

The extra L in the original `2L` proof aged out slow writes whose
windows started before its chosen boundary. H.4-S removes that need
when those earlier labels were already synchronous. It does not remove
the last-write class `w<b` in (1). Replacement N.3 gives an obstruction
from that class: a lease lives for L, with 88 ticks of wait after
settlement in the displayed instance (`L−24 ticks` in N.3.4).

### H.6-C — The unchanged causal cut supplies (S) — PROVED

**Statement.** If `k≤2R+1`, every attempt started at or
after u₀ can use H.6-S after its `3Δ` settlement. In particular this
holds for `k=2` at R=2 and R=3. The b in H.6-S is local to
that repair; it is not the reset label b=s* in H.11.

**Proof.** Let t_att be the attempt start and put `u=t_att+3Δ`. Then

```text
v_(b−k+1) = v_b−4(k−1)Δ
          ≥ GST+2P+3Δ−4(k−1)Δ
          ≥ GST,
```

because `k≤2R+1` and `2P=8RΔ`. Every later attempt starts no earlier.
H.8 proves the evidence claim with strict `3Δ` settlement.
An event during settlement ends that attempt sooner. ∎

For larger k, H.6-S is still valid with its explicit premise (S).
H.10 substitutes ρ₁ only when (S) holds at every attempt.
Use ρΓ when this cut test fails.

## 5. FJ height progress and the uniform reset deadline

### H.7 — Contest, in-band locks, and phases — PROVED-paper

Registry counterparts: `fj.crossingNoFinal.v1`, `fj.inBandLock.v1`,
`fj.twoChanges.core.v3`, `fj.frame.v5`.

**Statement.** At a fixed global frontier `m`, a top justification at
`m−1` is unique. A contest against that top `J` excludes any finalization
of `J`, including a private one. The effective phases occur in the order

```text
gap (lo=m−1) → uncontested top J (lo=m−1) → contest (lo=m),
```

with phases possibly absent. Each phase occurs at most once before a
frontier rise. **RESTATE (no-round)** for bp.rowPermission.v2: in a settled
phase, a common fresh source at height c∈[lo,m] makes height_pair return
a nonempty progress pair for its entry E. Each honest identity either
sends a row for (c,E) at this action or has already sent a matching row
(SO-COV, 22). Send-once does not imply a new emission.

The top-J and off-J witness carriers are held in honest cumulative stores.
**Proof.** IF.3(b) gives unique top `J`. A height-`m` witness off `J`
crosses `m−1` on a different entry `E`. If `J` finalized at `m−1`,
its signed finality quorum, including in a private carrier, would
intersect W's crossing quorum in an honest identity (IF.3(a), IF.2).
J and E are in RD2 scope through the held carriers and their ancestors,
so their different full entries have different roots. The intersection
signer has a finality pair for J at `m−1` and either a timeout at
that height or a target for E, an E1 offense. This argument needs no
scope for the private finalization carrier. Cumulative
storage never removes the witness. At fixed `m`, no higher justification
can be admitted because its carrier has height at least `m+1`.
Lower justifications cannot displace a top one. Thus the three-phase
order follows, even though a lower `(j,J)` can change in a gap.

Every lock justification was read from an honestly held carrier; so was J.
For the permission claim consider source height `c`. The only height_pair
branch that returns an empty pair for an available source is a mismatched
finality lock at `c`. A sent-set test can also suppress emission; SO-COV
(22) supplies an earlier matching row in that case.
Such a lock, including one proposed by the current row's finality pair,
requires a justification at `c` already read in a carrier of height at
least `c+1`. If `c=m`, this contradicts the cap. If `c=m−1`, a gap
phase has no such top justification. In the top-J phase every in-domain
height-`m−1` source extends `J` and has its entry equal to `J` by IF.1.
IF.3(b) forces every lock at that height to be this `J`. A contested
phase has `c=m`, already handled. Therefore no mismatched lock occurs.
A matching lock returns a target; a matching old target repeats; an old
timeout repeats for the current entry; a different old target produces
a timeout; no history produces a target because NJ is false. Each case
is a nonempty progress pair on the common entry. SO-COV gives a new or
earlier matching row. At action r with a_r≥GST, select each honest
identity's SO-COV row sent at t_i≤a_r. It is held everywhere before
max(t_i,GST)+Δ_F≤a_r+Δ_F. At a later carrier with the same height and
entry, W2 and R7 supply the row or its persistent progress bit. R7's optional omission keeps every effect (01 §1.1), so this argument is unchanged. If the
parent crossed c, progress is already complete. Stale validity alone
gives no progress bit. ∎

**DC port.** Paper lines 1004–1146 and 2139–2208 specify the unchanged
record and client. `fixedRootWindowRows_of_source` in
`Protocol/ValidatorClient/HeightProgressFixedRoot.lean:879` is the
corresponding DC row lemma. Replace its SG source premise by the fresh
SA opening source. The top-J lock case is unchanged; the contested
case is new and uses `lo=m`, which rules out the lower locked height.
No NJ hypothesis is imported.

### H.8 — One settlement per effective event — PROVED

Registry counterpart: `ap.headReachesLo.v7`, clause 6; `comp.settle.v1`
only as a timing comparison, not as a new NJ assumption.

**Statement.** An effective event first accepted by an honest node at
`w≥GST` has its required evidence in all full stores before `w+Δ` and
in every HEAD with `v_s≥w+3Δ`. Unless another effective event occurs,
all these reads have the new effective phase. Thus `θ=3Δ` is a valid
settlement allowance. Lower `F` moves do not add attempts.

The relayed frontier evidence is honestly held; each receiving F carrier is stored.
**Proof.** Relay supplies the frontier carrier, top-J carrier, or contest
carrier before `w+Δ`. IF.3 and H.7 prevent lower finality from excluding
the needed frontier evidence. If a receiver has already seen a higher
frontier, the stopped task has ended. The HEAD freeze for `v_s` is
`v_s−2Δ`. For `v_s≥w+3Δ` this freeze is at least `w+Δ`. Every required
receipt stamp is strictly below it because delivery is `<Δ`. Equality
at `v_s=w+3Δ` is valid. A message stamped at the freeze is excluded.
This 3Δ bound is not proved for delivery at exactly Δ. The stored path
is therefore in the frozen arm.
Monotone caches and unique top `J` give the common effective phase.
Receipts can change caches between a proposal and its HEAD inside this
allowance; no equal-frame argument is made for those duties. Start H.6
only after settlement. H.5 handles any number of lower `F` advances on
the retained suffix. Once the phase's frontier evidence has settled, an empty
frozen-domain exception cannot be generated afresh by a lower `F` move:
the settled frontier witness remains above it by IF.3(c). ∎
The settled frontier witness and each lower-F carrier are honestly stored.

**DC port.** DC paper lines 854–870, 2006–2018 give the cumulative-cache
and view mechanism. `frontierRegime_after_oneDelay` in
`Protocol/ForkChoice/Goldfish/HeightProgressSeedRegime.lean:274` gives
DC's fixed-root/gap alternative after relay. Here the alternative has a
third, contested case. The explicit relay-and-freeze inequalities above
replace any graded-readiness delay. No count per outside-anchor return
or per lower finalization is used.

### Registry restatement — fj.twoChanges.core.v3 — PROVED-paper

_2026-09-29. fj.twoChanges.core.v1 is WITHDRAWN for use under 4e85ff34.
Its duty-view evidence does not determine the current live-cache frame:
new evidence can be in Σ.T but outside the frozen view. Its fixed-view
algebra and Lean coverage remain historical. Use fj.twoChanges.core.v3
with its cumulative-store premises; do not change the old pins._

Assume IF.1–IF.4, the full named run collision premise with scope coverage of the bodies used below,
unique justification at the top height,
and finalized crossing at `a≤f`. Fix a no-rise interval at frontier
`m≥2`. If a justification at m−1 exists, denote its unique entry by
J_(m−1); otherwise both evidence bits are false. At a local read with
`H_x=m`, define E_J from a carrier of this justification in cumulative
`Σ.T_x`. Define E_C
from a height-m off-J block in that same `Σ.T_x`. The live caches and
these evidence predicates give the effective phases

```text
┌─────────┬───────────────────┬─────┬────────────────┐
│ Phase   │ Evidence in Σ.T_x │ lo  │ Effective root │
├─────────┼───────────────────┼─────┼────────────────┤
│ Gap     │ ¬E_J              │ m−1 │ F              │
│ Top J   │ E_J ∧ ¬E_C        │ m−1 │ J_(m−1)        │
│ Contest │ E_J ∧ E_C         │ m   │ F              │
└─────────┴───────────────────┴─────┴────────────────┘
```

1. The frame reads `Σ.T_x` and its caches. It does not recompute E_J,
   E_C, H, J, Z, or lo from a frozen duty view. A duty view V only
   supplies the arguments and witnesses of `D(V)` with those controls.
2. At each store both evidence bits persist once true. Thus the phase
   order is gap → top J → contest, with phases possibly absent. There
   are at most two evidence changes at one frontier. Stores can differ
   during delivery. The bound for common settled phases uses H.8; the
   pure core makes no claim that every successive duty has one frame.
3. Lower F moves add no phase. At a fixed block set V, once top-J
   evidence is accounted for, an F-only move to F′ below height m−1
   gives `D_new(V)={B∈D_old(V):F′⪯B}` in an F-root phase.
   A removed member is a strict ancestor of F′: its band witness has
   height at least m−1 and extends F′ by finalized crossing. A top-J
   domain is unchanged. Here the height of an F move is its certificate
   height. No step asserts that the whole domain stays unchanged.
4. Acceptance of finality at m−1 brings a finality carrier into Σ.T_x.
   It therefore also supplies top J if absent. Count that top-J evidence
   event once. W1 puts its justification on the carrier's ancestor path.
   At frontier m its latest J is this unique top F′, and contest is
   impossible by H.7.
   If the top phase was already present, its domain is unchanged.
   Finality at height m requires a carrier above m and ends the interval.

**Proof.** H.7 proves uniqueness, contest exclusion, and the phase order
from cumulative evidence. IF.4 gives the cache invariant. H.5 proves the
fixed-set domain identity and the retained-suffix statement. A finality
carrier has `h_F≤h_j<h`, so one at m−1 with height at most m also carries
the unique top justification. These facts prove items 1–4. H.8 alone
adds the common settlement deadline. At m=1 no positive lower F move
acts. This statement does not import the old duty-view evidence premise.

### Registry restatement — ap.headReachesLo.v7 — PROVED-paper

_2026-09-29. ap.headReachesLo.v5 is WITHDRAWN for current use under
registry §0: changed statements or hypotheses get a new id. It is still
true in its stated scope (R≥3, 4Δ, spec bd942ca0). The HEAD functions
are unchanged in 4e85ff34. Clause 5 transfers by bp.genuineFromF.v2
(01 §6.5) with F⪯P in a settled phase: a lower F has certificate height
below lo≤ht(P), and in top J one has F⪯J⪯P. Strict 3Δ settlement also
implies the weaker 4Δ bound. Keep its old pins. Successor:
ap.headReachesLo.v7 (current window spec, R≥max(2,κ), C1, θ=3Δ).
This is WITHDRAWN, not SUPERSEDED._

Authority is the current window spec; 4e85ff34 is a historical pin. Clauses 1–3 use its live-cache
FJ frame, frozen voter domain, full-domain live start, and exact HEAD
merge. Clauses 4–6 use Recovery₂ (`a≤f`, `R≥max(2,κ)`, `δ_t=2R`), C1
(blocks and SA votes use Δ, standalone FG rows use Δ_F), and the stated phase premises.

1. If start A is in `D(V_s)`, or has an eligible child there, the HEAD
   is in `D(V_s)` at height at least lo.
2. Otherwise the HEAD is A, including when `D(V_s)` is nonempty.
3. If A=Z and `D(V_s)` is nonempty, Z belongs to `D(V_s)`.
4. In a settled phase, every honest HEAD K has a full-store witness
   `W⪰K` with `ht(W)≥lo`. Every honest receiver admits W and its path
   before `e_s`; for a protected prefix of K use admission or finality
   coverage. This does not assert `ht(K)≥lo` for an outside start.
5. Let β be the first proposal label strictly after settlement u and
   `ℓ=β+2k−1`. Every honest P at `t_s>t_ℓ` has exact HEAD and fresh
   fast-write service if the phase persists through d_s. Such a gate
   occurs by `u+ρΓ`, or the phase stops sooner. Service continues for
   later honest proposals in that phase. Equal scores are required
   only on the retained comparison suffix, with H.5's path premises.
6. Evidence first accepted at `w≥GST` is in all full stores before
   `w+Δ`, and in every HEAD view with `v_s≥w+3Δ`, unless a frontier
   rise ends the task. Thus one effective event costs `θ=3Δ` before
   repair starts. Lower F moves and individual outside-start returns
   do not add event charges. A later effective event stops the attempt.

**Proof.** H.3 proves 1–4; H.5–H.6 prove 5; H.8 proves 6, including
equality at `v_s=w+3Δ` under strict delivery. H.21 checks `R≥max(2,κ)`.
This is a paper theorem. It does not assert a new Lean discharge.

### H.9 — Common entry and renewed-row promotion — PROVED-paper

The repair gate below can be supplied by H.6 or H.6-S. In both cases
its exact service and continued pivot are required. Part (a) proves
common entry within 2P−4Δ, with a first-opening alternative within
P−4Δ. Part (b) proves the served-promotion bound C and the terminal
bound D from such an action.

Q is honestly held: exact service makes Q every honest node's genuine result; each finality-origin carrier is honestly stored.
**Proof: common entry (bp.commonEntry.v2).** Let `Q` be the repaired
honest proposal. H.6 puts its parent walk at height at least `lo`;
height is nondecreasing on a path, so `c₀=ht(Q)≥lo`. The phase frontier
bounds `c₀≤m`. At its gate H.6 gives the exact genuine result `Q`
and a successful guard. Any earlier gate-origin output has block slot
less than Q's slot. A finality-origin output precedes Q: IF.3(c) gives
this in a gap or contest, and `F⪯J⪯Q` gives it in a top-J phase.
Thus no old `S` is a proper descendant of `Q`. The successful `advance`
returns `Q`, and normalization leaves it there. Hence every honest
post-gate `S=Q`; IF.4 puts every live lease below `Q`. H.4 and H.2 transfer
`Q` to all later HEADs. Each later raw gate covers `Q`, since its
honest support is `h>n/2`. Old live leases precede `Q`; later live
leases have already transferred to these HEADs, and same-label origins
are compatible by IF.6. Thus every guard passes and freshly fast-writes
`Q` and its non-genesis prefixes with support at least `h`.

Q is honestly held after its repair gate; each lower-F carrier is honestly stored.
This fresh set is nonempty in the full filtered tree. In a gap or
contest, every lower finality certificate has height below `lo≤ht(Q)`;
IF.3(c) puts `F⪯Q`. In a top-J phase, `F⪯J⪯Q`. Thus a lower `F`
cannot pass `Q` while the phase persists. The full-domain witness of
H.3 keeps `Q` viable; a changed frontier, top J, or contest instead
ends this attempt. The selector therefore chooses a descendant of `Q`.

**(a) First opening and common entry.**

**Statement.** Suppose Q is the H.6 or H.6-S repaired proposal, of slot q and
gate time `d_q`, and the effective phase persists. Let `s=rR` be the
least opening label with `s≥q`. Then

```text
0 ≤ a_r−d_q ≤ P−4Δ.
```

At `a_r`, every honest source exists, extends Q, and gives a
nonempty height pair, with earlier or new row coverage by SO-COV (22). If `ht(Q)=m`, all these sources have height m
and the same entry. If `ht(Q)=m−1`, either all sources have that height
and one entry, or at least one source has height m. In the last case,
all sources at `a_(r+1)` have height m and the same entry.

**Proof.** If q is an opening, the repair gives exact result Q at its gate,
and the selector chooses Q. Otherwise `q<s≤q+R−1`, which gives the
displayed inequality. The first transfer of Q is at label `q+1` by
H.4 and H.1. Thus the opening's HEADs cover Q even if that transfer
precedes Q's gate.

Use the pivot proof above. At the
repair gate all outputs equal Q, and all live leases precede Q.
Subsequent raw gates cover Q. Their guards pass, and they fast-write
Q with honest support at least h. Q remains in the full domain, or
the phase has ended. Thus the opening selector is nonempty and chooses
a descendant of Q. IF.6 gives compatible sources at the opening.
IF.1 gives one entry when their heights agree. H.7 gives a nonempty
progress pair from each source; SO-COV (22) supplies earlier or new rows.

K is an honestly held source, and accepted F has an honestly stored carrier.
The phase cap and floor leave at most the heights `m−1,m`. If a source
K at `a_r` has height m, H.4 transfers this fast body at label `s+1`.
The next opening has label `s+R≥s+2`. Its genuine results cover K;
F⪯Q follows from the common-entry proof above, and F⪯K follows from
IF.3(c)'s bound on accepted F below every in-scope height-m block (restated in HG.1). Thus
the same guard argument freshly writes K there. The selectors then
have height m and K's entry. The first opening costs at most P−4Δ;
the additional opening costs P. Thus common entry costs at most 2P−4Δ after the repair gate. ∎

This gives a general common-entry bound `2P−4Δ` after a repair gate.
More usefully, it gives a first common low entry within `P−4Δ`, or
an observed higher source. The attempt proof below uses that dichotomy.
It does not charge a second opening when the first one is sufficient.

**(b) Promotion at maturity.**

**Statement.** Let `a_r=T_r+6Δ` be an action with all honest sources
at height c and entry E, in a persisting settled phase **after an
H.6 or H.6-S repair gate**. Then a selected honest proposal X has height at least `c+1` by proposal time

```text
t_X ≤ a_r+2P+Γ−10Δ.                         (1)
```

If that height ends the phase, its first honest acceptance is before
`t_X+Δ`, hence within

```text
D := 2P+Γ−9Δ                               (2)
```

of `a_r`. If the phase persists through the gate, X has the H.6 exact
service and repair properties by

```text
d_X ≤ a_r+C,  C := 2P+Γ−4Δ.                 (3)
```

As elsewhere, an intervening effective event is an earlier endpoint.

**Proof.** Every source is a prefix of its opening's genuine result,
so `E.slot≤rR`. The entry is mature at all slots at least `rR+2R`.
Apply the strict proposal-gap premise at the preceding proposal-grid
time

```text
T_r+2P−4Δ.
```

The trigger is after GST. It supplies an honest X with

```text
T_r+2P ≤ t_X ≤ T_r+2P−4Δ+Γ.
```

This proves (1). Fix the SO-COV coverage of starting action r.
Each selected row was sent at t_i≤a_r, with a_r≥GST, and is held
before a_r+Δ_F≤T_r+β_F≤T_(r+1)<t_X. Its entry is mature.
Protected-source transfer puts E on the parent path, since
X.slot≥rR+2R≥rR+2. If the parent crossed c, the conclusion already
holds. Otherwise its height and entry are (c,E). W2 and R7 give each
selected row's progress bit, by new HeightMatch carriage or an earlier
HeightMatch occurrence with no height advance. Thus X has h≥q_F
progress bits. The target test or mature-progress test advances.
Window finalization changes neither height, entry, nor progress bits.
Stale validity alone is not used.
R7's optional omission keeps every effect (01 §1.1), so this argument is unchanged.

Let A be X's parent, already held in the proposer's full tree.
Before the stopping event, H.6's parent-walk argument (also used in
H.6-S) gives `ht(A)≥lo` at the proposal duty, without using X's gate.
A and each receiver's stored finalization carrier are in RD2 scope.
In a gap or contest, the finalized height is `<lo` (H.3), so scoped
IF.3(c) gives `F⪯A`. In top J, IF.4 and the parent domain give
`F⪯J⪯A`. Thus `F⪯A⪯X` rules out receiver exclusion before the
phase stops. If another effective event occurs first, it is the earlier
endpoint. Otherwise C1 supplies strict honest-block delivery and an
honest acceptance of X before `t_X+Δ`, which stops the terminal phase.
This proves (2). This part does not need exact service for X after
the phase changes.

In the nonterminal case, the selected repair theorem applies through
X's gate. X is later than its repair threshold, so its later-proposal
service clause applies. Its exact result
and successful write give the same pivot properties used in H.9(a).
Adding `6Δ` to (1) proves (3). ∎

If X has height m, the next common-entry action is only one opening
away. H.9(a) then costs `P−4Δ`, not `2P−4Δ`. If the task only needs
one row at the new height, it also stops at that first opening.

### H.10 — Retained per-phase bounds without opening search — PROVED

Start an attempt at an effective event w≥GST, or restart the phase
clock at the inclusive cut u₀ of H.11. An event during any step ends
the attempt earlier. Never use service through that event.
Let `r̄=ρΓ`; alternatively let `r̄=ρ₁` if H.6-S's (S) holds after
settlement. H.6-C supplies this alternative for every reset attempt
when `k≤2R+1`. Put `K_rep=3Δ+r̄`.

```text
┌────────────────────┬──────────────┬─────────────────┐
│ Task               │ Phase        │ Budget          │
├────────────────────┼──────────────┼─────────────────┤
│ Raise frontier m   │ Gap or top J │ A=r̄+6P+2Γ−18Δ   │
│ Raise frontier m   │ Contest      │ B=r̄+3P+Γ−10Δ    │
│ First row at m=M+1 │ Gap or top J │ C_row=r̄+4P+Γ−9Δ │
│ First row at m=M+1 │ Contest      │ D_row=r̄+P−Δ     │
└────────────────────┴──────────────┴─────────────────┘
```

**Proof.** H.8 supplies settlement, including evidence already present
at u₀. H.6 or H.6-S supplies the repair within r̄. Each budget includes K_rep.

**Rise, gap or top J.** Repair at height at least `m−1`. Let a be
the first opening in H.9(a). If all sources there have height `m−1`,
apply H.9(b). Either the phase ends, or its served proposal reaches m.
If it exceeded m, the rise would already end the attempt. At height m,
the next opening has a common entry. Apply H.9(b) once more and stop at
the first honest acceptance of the rise. Measured from the repair
gate, the total is at most

```text
(P−4Δ) + (2P+Γ−4Δ) + (P−4Δ) + (2P+Γ−9Δ)
= 6P+2Γ−21Δ.
```

Adding K_rep gives A. If a source at a already has height m, H.9(a) gives
a common height-m batch by `a+P`. The remaining cost from the repair
gate is at most `4P+Γ−13Δ`. This is no larger than
`6P+2Γ−21Δ`, because `2P+Γ≥8Δ`. If the repaired proposal itself has
height m, a is already common and the cost is smaller again. These
cases cover the whole band. At m=1 the height-0 case cannot occur;
the same upper bound remains valid.

**Rise, contest.** The repair has height m. H.9(a) costs `P−4Δ` and
the terminal part of H.9(b) costs `2P+Γ−9Δ`. Adding K_rep gives B.

**Row at M+1, gap or top J.** Put `m=M+1`. At the first opening,
any source at height m gives an honest row sent now or earlier by H.7
and SO-COV (22), so stop. Before the stopping row exists, no honest sent
record contains that height; send-once cannot suppress this first row.
Otherwise all sources have height `m−1` and one entry. H.9(b) either
ends the phase or supplies a served height-m proposal. Its first
opening supplies the required row. The cost from the repair gate is

```text
(P−4Δ) + (2P+Γ−4Δ) + (P−4Δ) = 4P+Γ−12Δ.
```

Adding K_rep gives C_row. No all-reader source agreement is required at
the final action; one height-m row is enough.

**Row at M+1, contest.** The repair already has height m. Its first
opening supplies a row. The cost is `K_rep+P−4Δ=D_row`. ∎

These are bounds on an interrupted task as well as a completed task:
if a step cannot use its persisting-phase premise, the event that
invalidates it has occurred by that step's endpoint. This is the
stopping argument used here. In particular, a promotion that changes J
ends the old attempt even if it does not raise the frontier.

The H.10 bounds remain valid. H.11 uses the shorter HG.1–HG.5
accounting below. An effective event need not be a charged restart.

### HG.1 — Service after a repaired frontier proposal — PROVED-paper

**Statement.** Let Q be an honest height-m proposal of slot q,
with H.6 or H.6-S service through its gate `d_q`, in a phase whose
global honest frontier is m. Assume that phase persists through `d_q`. From that
gate until the first honest frontier rise above m:

1. Q retains H.2's support, proposal-parent, and output conclusions.
2. Every later honest proposal has exact HEADs, exact genuine results,
   a passing guard, and fresh fast service, as in H.6.
3. Every opening action from the first opening label `s≥q` has a
   nonempty source at height m, with Q's entry, at every honest node.

The first such action is at most `P−4Δ` after `d_q`. Changes of top J
and contest status at frontier m do not stop these conclusions. A rise
ends the statement. No assumption about the next frontier is made.

**Proof.** H.9's repair-gate argument gives `S_x=Q` for every honest x,
and puts every live lease target below Q. In particular, this is an
actual common output and lease state, not only a fast source at one
reader. H.1 already transfers Q at `v_(q+1)=q_q`, before `d_q`.

Q is honestly held; accepted F carriers are stored, and other compared blocks are in scope.
While the global frontier stays m, every locally accepted finalization
has certificate height at most `m−1`. A higher one would require an
accepted carrier of height at least `m+1`. IF.3(c) therefore puts every
such F below Q and below every in-scope block of height m. A reader that holds
a height-m block B has local H=m. If it uses an uncontested top J,
that J precedes B: otherwise B itself makes a contest. In every other
case the root is F. Its floor is at most m. Thus B belongs to the full
choice domain and witnesses itself. After B is present in a HEAD's
frozen or current path, the same argument puts B in that HEAD domain.
It does not require the new frame evidence to have settled.

Apply this observation first to Q. Its honest proposal delivery and
H.1 put its path in time for subsequent HEADs. A new root is an
ancestor of Q. A changed floor cannot remove Q. Thus the H.1–H.2
induction for Q continues through each top-J or contest event.

Now consider leases written after `d_q`. Targets below Q are compatible
with every later genuine result that covers Q. A target B strictly
above Q has height m under the cap. If its write is fast, its own
honest supporter transports B before the next freeze. The preceding
paragraph keeps B, so H.1 transfers it and H.2 continues that support.
If its write is slow, every result in its successful window covers B.
No result at a label before q can cover Q or B: Q is an honest slot-q
block, and a valid earlier HEAD cannot contain that block. Hence the
whole slow window is synchronous. H.1's last-write-label argument
removes conflicting leases. B again witnesses itself and transfers.
A same-label pending gate cannot write a conflict, by IF.6.

These arguments form an induction on labels and receipt events. At a
later label, all current lease targets above Q have already transferred
to that label's honest HEADs. Their confirmation path covers those
targets. Targets below Q are also covered. Thus each whole-result guard
passes, and every gate freshly fast-writes Q with all h honest votes.
This also proves the induction step for later lease writes and renewals.

For exact honest-proposal service, all live starts are on the ordinary
parent path. Below Q, honest score h makes that path eligible and beats
each conflicting score, at most a. Above Q, every block has height m;
each block is its own floor witness. Both possible floors, `m−1` and m,
therefore give the same eligibility tests on this suffix. A root change
cannot remove a suffix above Q. H.5's score-transport argument applies
there without a change. Each frozen competitor was a proposer
competitor. The selected parent extends Q and has height m≥lo; the
parent and each finalization carrier are honestly held. Every finalized
height is <m by the bound above, so scoped IF.3(c) gives `F⪯A_P`.
Thus H.6's receiver-exclusion step admits P before its HEAD
and supplies its path. The finite walk argument of H.6 gives the exact proposal at each HEAD.
Its h votes release conflicts, including the pending gate's conflicts;
its gate then has the exact result and a passing guard. These facts
also hold for later proposals at slots at least `q+2`.

If slot `q+1` has an honest proposal, its proposal and HEAD precede
`d_q`, in the persisting phase. Its gate reads only leases written at
or before `d_q`, all at or below Q. Its h votes give the exact result
and a passing guard. This holds even if an event occurs in
`(d_q,d_(q+1)]`.

At an opening with label at least q, the fresh set contains Q. Each
selected source extends Q, has height m, and has its entry by IF.1.
H.7's height-m client case gives a nonempty pair and an honest row sent
now or earlier (SO-COV, 22). A lock at m would
require an accepted justification carrier above the frontier. The
first opening label is at most `q+R−1`, so its action is at most
`P−4Δ` after `d_q`. The case where q is itself an opening uses Q's
exact repair gate. This proves all three claims. ∎

Replacement N.3 refutes unconditional repair persistence across later
frontier changes: the early repaired proposal P566 has height 4; the
attack raises the frontier to 5. Its lease-expiry wait is 88 ticks after
settlement (`L−24 ticks` in N.3.4). This run does not refute HG.1, whose
premise keeps the frontier at m. A counterexample that isolates the
height premise at one fixed frontier remains OPEN.

### HG.2 — Promotion with a known entry age — PROVED-paper

**Statement.** Suppose a common-entry action at `a_r=T_r+6Δ` follows
a repair, with all honest sources at height c and entry E. Retain the
source and service premises of H.9(b), or those of HG.1 at the capped
frontier. Write `t_E=4Δ·E.slot`. Unless the task ends earlier, an
honest proposal X reaches height at least `c+1`, with

```text
U_F = max(T_r+β_F−4Δ, t_E+2P−4Δ),
U_F < t_X ≤ U_F+Γ.
```

For a terminal rise, its first honest acceptance is strictly before

```text
max(a_r+Γ−Δ+ε, t_E+2P+Γ−3Δ).                 (HG.2a_F)
```

If the phase persists and X needs service, its exact gate is at most

```text
max(a_r+Γ+4Δ+ε, t_E+2P+Γ+2Δ).                (HG.2b_F)
```

For Δ_F≤2Δ these reduce to the old HG.2a/HG.2b endpoints.

**Proof.** U_F is on the proposal grid and at or after GST: action r
follows a synchronous repaired proposal. The strict gap supplies X.
The grid gives t_X≥T_r+β_F≥a_r+Δ_F and t_X≥t_E+2P.
Thus every row selected from starting action r's SO-COV coverage is
held, including a matching emission before that action. Its source is
at least κ≥2 slots before X. Protected transfer puts E on X's parent
path, and the entry is mature.

If the parent crossed c, height progress is complete. Otherwise W2
supplies every matching progress bit by new carriage or an earlier
HeightMatch occurrence. A stale occurrence above c is impossible on
a path still at c. Distinct honest identities give h≥q_F bits. The
target test or mature-progress test advances. Window finalization
changes neither height, entry, nor progress bits.
R7's optional omission keeps every effect (01 §1.1), so this argument is unchanged.

Add less than Δ for acceptance, or 6Δ for continuing exact service.
Admission or finality coverage is unchanged. An earlier stopping event
ends the task. Under HG.1, same-frontier top-J and contest events do
not stop the source or service. This proves both endpoints. ∎

### HG.3 — Reach a repaired frontier proposal, or stop — PROVED-paper

Start at an effective event w, or the inclusive H.11 cut. Use H.8's
`3Δ` settlement. Let `ρ̄` be an allowed repair allowance, and put
`K_rep=3Δ+ρ̄`. The following budgets end at a repaired proposal of height m,
a frontier rise, or an earlier effective event. The low phases stop
at any such event until the repaired frontier proposal exists.

```text
┌───────────────────┬──────────────────────────────────┐
│ Starting phase    │ Budget from w                    │
├───────────────────┼──────────────────────────────────┤
│ Gap               │ E_g^F = ρ̄+2P+Γ−Δ                 │
│ Uncontested top J │ E_j^F = max(ρ̄+P+Γ+3Δ+ε, 2P+Γ−4Δ) │
│ Contest           │ K_rep = ρ̄+3Δ                     │
└───────────────────┴──────────────────────────────────┘
```

**Proof: gap.** If the initial repaired Q has height m, stop at its
gate. Otherwise it has height `m−1`. Let a be its first opening action.
H.9(a) gives `a≤d_q+P−4Δ`. If all sources there are low, they have Q's
entry E, so `t_E≤t_q=d_q−6Δ`. HG.2b_F gives a served height-m proposal
by

```text
max(d_q+P+Γ+ε, d_q+2P+Γ−4Δ) = d_q+2P+Γ−4Δ.
```

The equality uses `ε≤P−8Δ≤P−4Δ`. A higher proposal instead raises the frontier
and ends the task. If that first opening has a higher source B, H.4
and H.2 put B below every honest proposal at slot at least `rR+2`.
Apply the gap at `T_r+4Δ`. Such an honest proposal has its gate by
`a+Γ+4Δ≤d_q+P+Γ`, which is no later than the displayed bound.
Both X from HG.2b_F and this higher-source proposal use H.6's
later-proposal clause (or H.6-S): `t_X>a_r≥d_q>t_ℓ`. Thus the
persisting service supplies its exact gate, and HG.1 applies there.
An event before that gate is an earlier stop. Adding K_rep proves E_g^F.

**Proof: top J.** In the low-source case the entry is exactly J.
The top justification has an actual honest target source, whose row
was emitted at least `6Δ` after J's slot time. Its carrier has been
accepted by w. Thus `t_J≤w−6Δ`, even for a private old certificate.
At the inclusive cut the same inequality holds for the already-known
certificate. HG.2b_F now gives the bound

```text
max(w+ρ̄+P+Γ+3Δ+ε, w+2P+Γ−4Δ).
```

The higher-source alternative costs at most the first term, by the
same gap argument as above. An initially high repair costs only K_rep.
This proves E_j^F. In a contest the repair has height m because its
floor is m, so K_rep suffices. Events during settlement or repair end
the attempt earlier. ∎

### HG.4 — Remaining work after that proposal — PROVED-paper

**Statement.** After an HG.1 proposal Q at height m, the remaining
rise time is strictly less than, or bounded by the stopping allowance

```text
T_rise = 2P+Γ−9Δ.
```

The first honest height-m row is within
`T_row=P−4Δ`. No top-J or contest restart is charged in either tail.

**Proof.** HG.1 supplies a common height-m action by
`a≤d_q+P−4Δ`, and its entry E has `t_E≤d_q−6Δ`.
HG.2a_F bounds the rise acceptance by

```text
max(d_q+P+Γ−5Δ+ε, d_q+2P+Γ−9Δ)
= d_q+2P+Γ−9Δ.
```

The second term dominates since `ε≤P−8Δ≤P−4Δ`. HG.1 preserves all required
sources until the rise, including through changes of J and contest.
For a row, its first opening suffices by HG.1 and SO-COV (22). Before
the stopping row exists, no honest sent record contains its height, so
send-once cannot suppress this first row. ∎

### HG.5 — Combined search at one frontier — PROVED-paper

**Statement.** From a task start at frontier m, raising m costs at
most `E_g^F+E_j^F+B_c^F`, where `B_c^F=ρ̄+2P+Γ−6Δ`.
Finding its first honest height-m row costs at most
`E_g^F+E_j^F+D_c^F`, where `D_c^F=ρ̄+P−Δ`.

**Proof.** Before an HG.1 proposal exists, H.7 orders the phases as
gap, top J, contest, with each occurring at most once. HG.3 charges
at most E_g^F to a failed gap phase and E_j^F to a failed top phase.
In a contest it charges at most K_rep to reach the repaired frontier.
Then HG.4 adds T_rise or T_row. These sums give B_c^F and D_c^F.

If a repaired frontier proposal occurs in a gap or top phase, HG.1
continues the task through subsequent same-frontier events. Add the
HG.4 tail at once; there is no second repair for those events. This
cost is no larger than the displayed sum, since omitted phase and K_rep
allowances are nonnegative. A rise ends the rise task; a rise past m
already needs an earlier honest height-m row by IF.3(a), so also ends
the row task. An event which skips a phase only removes an allowance.
These cases cover every event order. ∎
The rise carrier is honestly stored, so its crossing path is in scope.

### H.11 — Causal cut and reset arrival (`fj.reset.v1`) — PROVED-paper

**Statement.** Let `r_G` be the first action round at or after GST,
`u₀=a_(r_G+2)` with its inclusive event prefix, and
`M=max_x H_x(u₀)` over honest nodes. Let

```text
μ = max({1} ∪ {height of an honest row whose source vote time is <GST}).
```

Here μ is determined by the run and GST; it is not a witness field (only rows with a nonempty height pair count).
Then `μ≤M`, `GST+2P≤u₀<GST+3P`, and every honest height row
emitted through the inclusive cut `u₀` has height at most `M`.
There is a first round `r*` with an honest row at height `M+1`.
Put `s*=r*R`, `b=s*`, and select one fresh source `C*` of such a row. It has height `M+1`, its label is synchronous,
and

```text
a_(r*) < GST+B'_reset^F,
B_reset^F(r̄) = 3P+2E_g^F+2E_j^F+B_c^F+D_c^F.
E_g^F=r̄+2P+Γ−Δ; E_j^F=max(r̄+P+Γ+3Δ+ε, 2P+Γ−4Δ).
B_c^F=r̄+2P+Γ−6Δ; D_c^F=r̄+P−Δ.
B'_reset^F = min({B_reset^F(ρΓ)} ∪ {B_reset^F(ρ₁) if k≤2R+1}).
```

**Proof.** Actions have period `P`. The first one after GST is in
`[GST,GST+P)`, which proves the cut inequalities. An old-source row
acts at most `5Δ` after its vote time. Since `2P≥16Δ>5Δ`, its honest
source was held before `u₀`. Cumulative storage means that source's
height is included in its holder's `H(u₀)`, even if it later leaves
`act(Σ)`. Thus `μ≤M`. Receipt in other pools is not required at u₀.

A row at height above `M+1` requires a path crossing `M+1`, hence an
earlier honest row there by IF.3. A row at `M+1` at or before `u₀`
would itself have a stored source that raises `M`, a contradiction.
Hence a first such row, if produced, has `r*≥r_G+3` and
`t_(s*)=a_(r*)−6Δ≥GST+3P−6Δ≥GST+2P` for `R≥2`.
The row's source is honestly held, so its crossing path is in scope.

Start from the greatest frontier M at the cut. HG.5 bounds the rise
from M by E_g^F+E_j^F+B_c^F. It bounds the first honest row at M+1 by
E_g^F+E_j^F+D_c^F. A rise past M+1 already needs that row by IF.3(a).
Before a served frontier proposal, H.7 orders gap, top J, and contest;
HG.3 bounds each interrupted phase. After that proposal, HG.1 preserves
service through same-frontier changes, and HG.4 bounds the remaining
work. Thus an effective event need not cause a charged restart.
Skipped phases only remove allowances. This covers all event orders.
Any rise carrier is honestly stored, so its crossing path is in scope.

For either permitted value of r̄, HG.5 gives a total after u₀ of at
most `2E_g^F+2E_j^F+B_c^F+D_c^F`. Add `u₀<GST+3P`. H.6-C permits r̄=ρ₁
at every task start if k≤2R+1; H.6 permits r̄=ρΓ for every k.
Both arguments bound the same first row. Take their minimum when both
premises hold. This proves existence and the displayed deadline. ∎

The selected C* is any actual fresh source of the first M+1 row.
Its opening can be faulty and its action can have mixed source heights.
No exact opening proposal is used here or in H.12: an honest supporter
of C* supplies the receipt path for its initial transfer.

**DC port.** DC paper lines 1158–1214 explain its source readiness and
round action; its Lean `gstLagged`/`GradeRoundReady` interfaces
(`DecoupledConsensusInternal/HealingSurface.lean:145,150`) and
`frontierRegime_after_oneDelay` are the comparison points. Here the
inclusive cut is retained, but SA's two-lease repair replaces grade
readiness. The stop is the first honest `M+1` row; there is no NJ-selected
height, no DC NJ parameter, and no invocation of a DC NJ handoff theorem.

### HG.6 — Reset and healing deadline — PROVED-paper

Retain exactly H.11's `r_G,u₀,M,r*,s*,b,C*` and the run function μ. In particular, do not
move the cut or change the meaning of “high”. Define

```text
B_reset^F(ρ̄) = 3P + 2E_g^F + 2E_j^F + B_c^F + D_c^F,
B^F(ρ̄)       = B_reset^F(ρ̄) + Γ + 4Δ
                = max(6ρ̄+12P+6Γ+Δ+2ε, 4ρ̄+14P+6Γ−13Δ).

B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
```

Then `a_(r*)<GST+B_reset^F(ρ̄)` for either allowed ρ̄. The same H.22
witness tuple has `HEALING_INPUT(t*)` and `t*<GST+B_H^F`.

**Proof.** H.11's causal proof gives `μ≤M`, its inclusive row cap, and
`u₀<GST+3P`. It is unchanged. Apply HG.5 to the rise from M and then
to the first row at M+1. A skipped frontier already requires that row.
The total after the cut is at most
`2E_g^F+2E_j^F+B_c^F+D_c^F`. This proves the strict reset bound.

H.6 works for every k. H.6-C supplies (S) at every task start when
`k≤2R+1`, so H.6-S permits ρ₁ in every HG.3 repair in that case.
HG.1 tails require no further repair premise. Both arguments bound
the same first height-(M+1) row, so take their minimum.

H.12–H.18 then apply without a change to the selected C*. H.18 adds
at most `Γ+4Δ` to the reset action. H.22 keeps all its witnesses and
H0–H4, including H2′. Its H-time field gets the new deadline. Increasing
a healing start preserves HEALED, so `HEALED(GST+B_H^F)` follows, as does
`HEALED(GST+B_H^F−1)` in integral time. ∎

Expanded forms, useful for checking the coefficient of L, are

```text
B_H,F^(2) = max(12L+12Γ+12P+49Δ+2ε, 8L+10Γ+14P+19Δ),
B_H,F^(1) = max( 6L+12Γ+12P+61Δ+2ε, 4L+10Γ+14P+27Δ).
```

At k=2, G=8Δ, with the delay ranges shown:

```text
┌───┬───────────┬─────┬───────┬───────┬───────┬───────┬─────────────┬───────┐
│ R │ Δ_F range │ ρ₁  │ E_g^F │ E_j^F │ B_c^F │ D_c^F │ Reset bound │ B_H^F │
├───┼───────────┼─────┼───────┼───────┼───────┼───────┼─────────────┼───────┤
│ 2 │ Δ_F≤2Δ    │ 25Δ │ 48Δ   │ 44Δ   │ 43Δ   │ 32Δ   │ 283Δ        │ 295Δ  │
│ 3 │ Δ_F≤2Δ    │ 25Δ │ 56Δ   │ 48Δ   │ 51Δ   │ 36Δ   │ 331Δ        │ 343Δ  │
│ 3 │ 2Δ<Δ_F≤6Δ │ 25Δ │ 56Δ   │ 52Δ   │ 51Δ   │ 36Δ   │ 339Δ        │ 351Δ  │
└───┴───────────┴─────┴───────┴───────┴───────┴───────┴─────────────┴───────┘
```

For κ>2 the first expanded constant is `49Δ+2ε`. At R=3, κ=3,
k=2, G=8Δ, E_j^F=52Δ, B_reset^F(ρ₁)=339Δ, and B_H^F=351Δ.
For Δ_F≤2Δ, the first expanded constant for ρΓ is `49Δ`: it includes `6·8Δ+Δ`.
The checks retain both max branches, even though the first branch
controls both numerical cases above.

### HG.7 — Phase-exact composition — PROVED-paper

**Statement and scope.** Assume Recovery₂ and `k≤2R+1`. Keep H.11's
`r_G,u₀,M,r*,s*,b,C*` and the run function μ and the H.22 witness tuple. In particular,
`u₀≡6Δ (mod P)` and `u₀<GST+3P`. Define the following functions of
absolute time. Here `G_F(U)` is a deadline function; the scalar G remains
the proposer-gap parameter. Likewise `J_F(U)` is a deadline function,
not a justification block.

```text
A(x) = 6Δ + P ceil((x−6Δ)/P),
D(U) = 4Δ ceil((U+2Δ)/(4Δ)) + 4kΔ + Γ + 6Δ,
G_F(U) = D(U) + 2P + Γ − 4Δ,
J_F(U) = max(A(D(U)) + Γ + 4Δ + ε,
           4Δ floor((U−6Δ)/(4Δ)) + 2P + Γ + 2Δ),
C(U) = D(U),
T_F^rise(V) = max(A(V) + Γ − Δ + ε, V + 2P + Γ − 9Δ).

V₁ = C(J_F(G_F(u₀))),       U₁ = T_F^rise(V₁),
V₂ = C(J_F(G_F(U₁))),       A₂ = A(V₂),
B_H^ph,F = 3P + (A₂−u₀) + Γ + 4Δ.
```

Then `a_(r*)≤A₂`, `t*<GST+B_H^ph,F`, and `B_H^ph,F≤B_H,F^(1)`.
Each function commutes with translation by P. Thus `A₂−u₀` depends
only on the parameters and the fixed action phase, not on the round
of u₀. This defines a uniform bound. The numerical results here are
for `k=2,G=8Δ,R=2,3`. This proof gives no ρΓ analogue for
`k>2R+1`. The all-parameter closed form `B_H^F` remains unchanged.

**Repair deadline.** Let w be a task start or an effective event at or
after u₀, with `w≤U`. H.8 settles its evidence by `w+3Δ`. If b is
the first HEAD label with `v_b≥w+3Δ`, then

```text
t_b = 4Δ ceil((w+2Δ)/(4Δ))
    ≤ 4Δ ceil((U+2Δ)/(4Δ)).
```

H.6-C supplies (S) for every attempt because `k≤2R+1`. H.6-S uses
`ℓ=b+k`. A lease last written at a label below b expires by
`t_ℓ+Δ`, before the preceding HEAD of the selected proposal. This
includes an old label whose gate is pending at the phase change.
For later labels, H.4-S supplies common support while the phase
persists. Apply the strict proposer gap at `t_ℓ`. The selected honest
proposal has gate at most `t_b+4kΔ+Γ+6Δ≤D(U)`. Its h clean votes
release any conflict from the pending gate `d_(s−1)=t_s+2Δ` at q_s.
No gate occurs between q_s and d_s. Thus H.6-S gives exact HEADs,
a passing guard, and a fresh fast write. If an effective event occurs
first, that event stops the attempt by the same deadline. The later
proposal service is also the H.6-S service.

At `k=2,G=8Δ`, `D(U)=U+24Δ` for a gate time U. For other times,
the ceiling is necessary. For example, the first rise need not be on
the gate grid.

**Phase and tail deadlines.** A gap repair at gate `d≤D(U)` either
serves the frontier or has a low entry E with `t_E≤d−6Δ`. Its first
opening action is at most A(d). HG.2b_F gives a served frontier proposal
or an earlier effective event by

```text
max(A(d)+Γ+4Δ+ε, d+2P+Γ−4Δ)
= d+2P+Γ−4Δ ≤ G_F(U).
```

For a gate d, `A(d)−d≤P−4Δ`; `ε≤P−8Δ≤P−4Δ` gives this equality.
The higher-source alternative in HG.3 costs only the first term.

In a top-J phase, the low entry is J itself. A target row for its
certificate acts at least `6Δ` after J's slot time. Therefore
`t_J≤w−6Δ≤U−6Δ`. Since t_J is on the proposal grid,
`t_J≤4Δ floor((U−6Δ)/(4Δ))`. HG.2b_F and the next-action deadline
give J_F(U), including the higher-source alternative. A repair already
at the frontier needs only `D(U)≤J_F(U)`.

In a contest, the floor is the frontier, so C(U)=D(U) suffices.
After a served frontier proposal at a gate at most V, HG.1 preserves
its service through later events at that frontier. Its first opening
is at most A(V), which bounds the first row there. HG.2a_F and
`t_E≤V−6Δ` give the strict rise deadline T_F^rise(V). Neither tail needs
another repair. These steps keep the same fresh opening source and
the same entry-specific progress rows as HG.2–HG.4.

**Composition and comparison.** Before a served frontier proposal,
H.7 orders the possible phases as gap, top J, then contest. If a phase
ends early, pass its event time to the next function. Each function is
nondecreasing, and `G_F(U)≥D(U)≥U`, `J_F(U)≥D(U)≥U`. If service at the
frontier occurs first, HG.1 permits the tail at once. Inserting a
skipped phase only increases the deadline. A rise ends the first task.
A rise past M+1 already requires an honest row at M+1, by IF.3, so
it also ends the second task. This covers events during settlement,
repair, or promotion. It gives a rise strictly before U₁ and a first
honest height-(M+1) row by A₂. Using the strict U₁ as a weak input
to the second task is valid.
The rise carrier is honestly stored, so its crossing path is in scope.

For comparison with HG.6, use its budgets with ρ̄=ρ₁. The ceiling
in D gives `D(U)<U+3Δ+ρ₁`. D(U) is a gate time. The action-grid
inequality above and the floor in J then give

```text
G_F(U) ≤ U+E_g^F,       J_F(U) ≤ U+E_j^F,
T_F^rise(C(U)) ≤ U+B_c^F,    A(C(U)) ≤ U+D_c^F.
```

For the third inequality, `ε≤P−8Δ≤P−4Δ` lets the second term control
T_F^rise(C(U)). Compose these four inequalities to get
`A₂−u₀≤2E_g^F+2E_j^F+B_c^F+D_c^F`. Therefore `B_H^ph,F≤B_H,F^(1)`.
H.12–H.18 keep the same reset source and add at most `Γ+4Δ` to
its action time. Since `u₀<GST+3P`, H.22 gives
`t*≤A₂+Γ+4Δ<GST+B_H^ph,F`, with H0–H4 and H2′ unchanged. ∎

At `k=2,G=8Δ`, the first two columns use Δ_F≤2Δ.
The last column uses 2Δ<Δ_F≤6Δ. The deadlines are as follows. All rows before the
last two are offsets from u₀ in units of Δ. U₁ is strict; the other
intermediate rows are weak deadlines.

```text
┌──────────────────────────────────────┬─────┬─────┬──────────┐
│ Deadline                             │ R=2 │ R=3 │ R=3, κ=3 │
├──────────────────────────────────────┼─────┼─────┼──────────┤
│ G_F(u₀): first gap                   │ 44  │ 52  │ 52       │
│ J_F(G_F(u₀)): first top J            │ 84  │ 96  │ 100      │
│ V₁: first contest / served frontier  │ 108 │ 120 │ 124      │
│ U₁: first rise, strict               │ 123 │ 143 │ 147      │
│ G_F(U₁): second gap                  │ 168 │ 196 │ 200      │
│ J_F(G_F(U₁)): second top J           │ 204 │ 240 │ 244      │
│ V₂: second contest / served frontier │ 228 │ 264 │ 268      │
│ A₂: first height-(M+1) row           │ 232 │ 264 │ 276      │
│ A₂+Γ+4Δ: full healing                │ 244 │ 276 │ 288      │
│ B_H^ph,F/Δ: add 3P, strict from GST  │ 268 │ 312 │ 324      │
│ Adopted B_H^F/Δ                      │ 295 │ 343 │ 351      │
└──────────────────────────────────────┴─────┴─────┴──────────┘
```

For Δ_F≤2Δ, the integer deadlines are `GST+268Δ−1 tick` and `GST+312Δ−1 tick`.
For R=3, κ=3, k=2, G=8Δ, the deadline is `GST+324Δ−1 tick`.
For Δ_F≤2Δ the savings over the adopted bound are 27Δ and 31Δ;
for R=3, κ=3 they are 27Δ. The composition
still permits six repair charges. It does not prove that all six are
necessary, or that one repair suffices. The lower witnesses release
conflicts promptly; they do not attain six repair waits.

### HG.8 — Three-charge bound with the unchanged cut

All functions are of absolute time. `𝒜` is the next-action function;
it is not a proposal. `D` is HG.7's H.6-S repair deadline. `S`
is the L2 service gate. `J₀_F` is the top-J deadline with the L2 service
gate in place of HG.7's repair gate.

```text
𝒜(x)       = 6Δ + P·ceil((x−6Δ)/P)
t_b(x)     = 4Δ·ceil((x+2Δ)/(4Δ))        (first slot time ≥ x+2Δ)
D(x)       = t_b(x) + 4kΔ + Γ + 6Δ
S(x)       = t_b(x) + Γ + 2Δ
top_F(rd,w)  = max(𝒜(max(rd,S(w))) + Γ + 4Δ + ε,
                 4Δ·floor((w−6Δ)/(4Δ)) + 2P + Γ + 2Δ)
J₀_F(x)      = top_F(−∞, x)
A_p        = 2P + Γ − 4Δ
T_F^rise(V)       = max(𝒜(V) + Γ − Δ + ε, V + 2P + Γ − 9Δ)    (HG.7, strict rise)
```

Each function is nondecreasing, and `D(x),S(x),J₀_F(x)≥x`. If `rd≤S(x)`
and `w≤x`, then `top_F(rd,w)≤J₀_F(x)`.

**Phases.** At frontier m: gap(m) has frame `(F,m−1)`, top J(m) has
`(J,m−1)` with `ht(J)=m−1`, contest(m) has `(F,m)` (spec 747–768).

**Stops used by L4-R.** `w_a` is the first event at which some honest
node has `j≥M`. `w_b` is the first emission of an honest height row at
height M+1. The H.11 search ends at `w_b`.

Here `𝒜` is HG.7's `A(x)`, not the live start A of §2. `D(x)`
is a time, not the filtered domain `D(V)`. `S(x)` is a deadline,
not the available-output register S. `J₀_F(x)` differs from HG.7's
`J_F(x)`: it uses S in place of D. `top_F(−∞,x)` means that no inherited
deadline is present. All spec citations in HG.8 refer to 4e85ff34.

#### HG.8-SI — Service interface — PROVED-paper

Let V be an honest proposal, with the frontier and finality conditions
of the HG.1/H.9 application. At its serving gate `d_V`, suppose every
honest node has exact genuine result V and a passing whole-result guard. Suppose also that later
honest proposals have exact HEADs when their HEAD duty precedes the
next stop. Then HG.1, HG.2, and H.9 apply from `d_V`, with their stated
frontier and stop conditions. In particular, `S=V` at every honest node,
every live lease precedes V, and HG.1 can start at frontier `ht(V)`.

**Proof.** H.9's gate-origin argument puts every earlier gate-origin
output at a slot below V's slot; its finality-origin argument puts that
output below V. Thus old S cannot be a proper descendant of V.
The exact result and guard give S=V. IF.4 puts every surviving target
below V. The gate writes its supported prefixes. These are HG.1's initial
facts. Its induction uses the stated later HEADs, including the
slot immediately after V whose HEAD precedes `d_V`; it does not use
the name of the repair lemma. HG.2 uses that induction and the fresh
source at the next opening. H.9 uses the same gate and guard facts.
Thus H.6, H.6-S, L2, and L4-R(iii) can each supply the interface.
The conclusions stop where the supplying lemma stops. ∎

#### L2-W — Witnesses across a change into a top-J frame — PROVED-paper

**Statement.** Let `w≥GST` be the first honest acceptance of the
evidence that starts the **global** top J(m) phase: some honest node
then has `j=m−1`, `H=m`, root J with `ht(J)=m−1`, and floor `m−1`
(spec 747–768). At `w`, no honest node is contested at frontier m, and
no honest node has `H>m`. (If an honest node is already contested, that
contest is an earlier effective event, and L2 does not apply.) Consider
an event after `w` and before the next effective event, and an honest
reader y. The frame of y is then gap(m), top J(m), or a frame of
frontier at most m−1; a reader can lag by more than one frontier. Then:

1. **Self-witness.** Each in-scope block B with `J⪯B` has `ht(B)≥m−1≥lo_y`.
   Thus B witnesses itself in every block set of y that contains B.
2. **Finality.** `F_y⪯B` for each such B.
3. **Kept path.** Let B be a fast body or a slow-window target with an
   honest supporter K, `B⪯K`, and let B be compatible with J.
   - If `J⪯B`, B is kept at every duty of y whose view contains B's
     path: B is above the root `Z_y`, and B witnesses itself. H.3's
     witness-path clause holds with `W=B`.
   - If `B⪯J`, B is below the root `Z=J` at every duty from `w+Δ`.
     L2 needs no transfer for B: the lease is already satisfied and
     compatible with every J-extending result.
   - If B conflicts with J, B is not kept at a top-J reader. This is
     L2's released class.

Thus H.1–H.2, and H.4-S's induction, continue for a body B with `J⪯B`
across the change, with no new settlement and no new witness.

**Proof.** State height is nondecreasing on a path (IF.1), and J is the
entry at height `j=m−1`, so `ht(B)≥ht(J)=m−1` for `J⪯B`. Before the
next effective event, no honest reader at frontier m is contested, so
its floor is `m−1` (gap(m) or top J(m)). A reader with `H_y≤m−1` has
`lo_y≤H_y≤m−1` in every row of the frame table (spec 747–768).
Viability needs only `F⪯B` and a member of height at least `lo` above B
(spec 1131–1137). This proves 1 once 2 holds.

B is in scope by the statement; F_y and J have honestly stored carriers.
For 2, `j_y<H_y≤m`, so `j_y≤m−1`. The finalized certificate height
`x_F` of `F_y` is at most `j_y` (spec 990–1003, 1064–1069). If
`x_F<m−1`, IF.3(c) gives `F_y⪯B`, since `ht(B)>x_F`. If `x_F=m−1`,
IF.3(b) makes `F_y` the unique justified entry J at `m−1`, so
`F_y=J⪯B`.

Both the global J carrier and y's live-J carrier are honestly stored.
For 3, B is in the view by H.1's relay step: the head of each early
supporting vote is admitted before the next freeze (IF.5). Part 2 shows
that receiver exclusion (spec 213–217) cannot skip it. B extends the
root `Z_y` in every case. If `Z_y=F_y`, part 2 gives `Z_y⪯B`. If y is
in top J(m), uniqueness (IF.3(b)) gives `Z_y=J⪯B`. Otherwise y is a
lagging reader in an uncontested top-J frame with a lower root `J_y`;
since y holds B, `m−1≤ht(B)≤H_y≤m−1`, so `ht(B)=H_y`, and the absence
of a contest gives `J_y⪯B` (spec 747–757, 1113–1119). So B is in the
filtered set by 1. For `B⪯J`: the carrier of J reaches every honest
store before `w+Δ` (relay, spec 204–217). The root reads the live
caches, not the frozen view (spec 747–768, 779–792, 1217–1229).
Thus every duty from `w+Δ` has root J before the next effective event.
The lease on `B⪯J` is already satisfied and cannot block a result
extending J. No transfer is needed for this class. The serving proposer
can act at `w+2Δ`; its preceding HEAD batch can be before `w+Δ`.
This proof does not assume otherwise. ∎

#### L2 — Service through a change into top J(m) — PROVED-paper

Use L2-W's global phase start w. The inherited state is either an
H.6-S repair with deadline rd, or the continuous service of HG.1 through
HG.8-SI. In the latter case rd is the earlier serving gate. Old readers
may have any floor at most `m−1`. This includes a floor increase after
L4-R's `w_a`: a reader still at frontier M moves from floor M−1 to M
when the global phase enters top J(M+1). Assume (S) for the inherited
repair. Before the next effective event, service is available by
`max(rd,S(w))`; the served frontier-m proposal is available by
`top_F(rd,w)`, or an effective event occurs by that deadline. Later honest
proposals have the exact HEAD service of HG.8-SI until the stop.

**Proof.** A lease conflicting with J loses walk-start authority: it is
outside the J-rooted domain (spec 1156–1168, 1217–1229). Before `w+Δ`,
relay puts J's carrier in every honest store. Each later honest HEAD
extends J. Its h votes release all conflicting leases at its release
cut (spec 875–883, 1328–1339). A pending previous-label gate is at
`t_v+2Δ`, before `q_v=t_v+5Δ`; the same release removes its conflicting
writes. No gate runs between q_v and d_v (spec 814–825).

For a compatible target above J, L2-W supplies its own witness, its
path, and receiver admission at every floor at most `m−1`. The
H.1–H.2 and H.4-S transfer induction therefore continues. A target
below J needs no transfer from `w+Δ`. These facts cover writes in the
transition interval as well as older writes. Loss of authority,
release, and the pending-gate order do not read the floor. Thus the
argument also covers the stated floor increase and inherited HG.1
service. Any unresolved earlier repair keeps rd; this lemma does not
cancel it.

For an honest proposal at `t_P≥w+2Δ`, the evidence is in the full
proposer store and in the HEAD freeze at `t_P−Δ≥w+Δ`. H.5's retained
scores and H.6's receiver-exclusion step apply: the honestly held parent
is in the J-rooted domain, so `F⪯J⪯A_P≺P` admits P before its HEAD.
H.6's finite walk comparison then gives exact HEADs once both the
inherited service and this root condition hold. Their h early votes
release conflicts and give the exact F-start result and passing guard
(01 §6.6; spec 1280–1297). The same induction gives later service.
Apply the strict proposer gap at the last proposal-grid time strictly
below `w+2Δ`, namely `t_b(w)−4Δ`. The gate is at most
`t_b(w)−4Δ+Γ+6Δ=S(w)` (spec 238–246, 1892–1898).

For frontier promotion, the first fresh opening is at most
`𝒜(max(rd,S(w)))`. J's target certificate has `t_J≤w−6Δ`, hence
`t_J≤4Δ floor((w−6Δ)/(4Δ))`. HG.2b_F gives the maximum of the two
terms in `top_F(rd,w)`. A proposal already at the frontier needs only
service. Every bound is stopped at the next effective event. ∎

#### L3 — At most two floor increases — PROVED-paper

During the search from u₀ to the first honest row at M+1, the global
floor is monotone in `[M−1,M+1]`. Gap(M) and top J(M) have floor M−1;
contest(M), gap(M+1), and top J(M+1) have floor M; contest(M+1) has
floor M+1 (spec 747–770). Contest evidence stays in the cumulative
tree, and the justified entry is unique at each height when `a≤f`.
Thus a contest cannot disappear at the same frontier (H.7). A rise
past M+1 needs an earlier honest row at M+1 (IF.3(a)), which stops the
search. There are at most two floor increases. A rise from a low
M-phase uses the first increase in place of contest(M). A later witness
can restore a target and its earlier repair debt; it adds no new floor
increase. H.13 excludes contest(M+1) when `M>μ` and contest(M) when
`μ≤M−2`; these exclusions only remove stages. ∎
The rise carrier is honestly stored, so its crossing path is in scope.

#### L4-R — A rise after a served frontier proposal adds no repair charge — PROVED-paper

**Premises.** Recovery₂: `a≤f`, C1, K≥2, the
strict proposer gap with finite `G≥4Δ`, `R≥max(2,κ)`, `δ_t=2R`. Let Q be
an honest proposal of slot q with `ht(Q)=M`. Q has exact HG.8-SI service
through its gate `d_q`, in a phase whose global honest frontier is M,
and that phase persists through `d_q`. This is the HG.1 premise. The
phase at `d_q` can be gap (floor M−1), top J (floor M−1), or contest
(floor M).

**Statement.** For every event e with `d_q≤e<min(w_a,w_b)`:

1. **Frame set.** Every honest x has `M≤H_x≤M+1`, `j_x≤M−1`, `F_x⪯Q`,
   root `Z_x⪯Q`, and floor `lo_x∈{M−1,M}`.
2. **HG.1 continues through the rise.** HG.1(1) and HG.1(2) hold.
   HG.1(3) holds in this form: every honest source at an opening with
   label at least q extends Q, and has either height M and Q's entry E,
   or height M+1. In the second case its row is at height M+1, so
   `w_b` has occurred.
3. **Service at M+1.** Put `B₄=d_q+A_p`. One of these occurs:
   (i) `w_b≤B₄`; if the first opening with label at least q already
   has a height-(M+1) source, then `w_b≤d_q+P−4Δ`;
   (ii) `w_a≤B₄`;
   (iii) before both stops, an honest proposal X with `ht(X)≥M+1` has
   exact HG.8-SI service (exact HEADs, exact genuine result, passing guard,
   fresh fast write, and `S=X` at every honest node) at `d_X≤B₄`.
4. **No charge.** No H.6 or H.6-S repair starts at the rise. The rise
   is not a charged event of the H.11 search.

**Exclusion.** The lemma does **not** assert `F⪯Q`, HEAD coverage of Q,
or any other property of Q at or after `w_a`. After `w_a`, a height-M
finalization that conflicts with Q is possible. Its reconciliation can
delete Q's leases and set `S:=F` (spec 1005–1025).

**Proof.**

Any carrier raising honest H_x is honestly stored, so its crossing path is in scope.
*Step 1 (frame set).* Every honest node holds Q before `t_q+Δ<d_q`
(relay, spec 204–217), so `H_x≥M` (spec 990–993). A carrier of height
at least M+2 has crossed M+1. By IF.3(a) that crossing has `q_F`
height pairs at M+1, and one of them is an honest row. That row
precedes the carrier. Thus `w_b` precedes any `H_x≥M+2`, and
`H_x≤M+1`. IF.4 gives `j_x<H_x`, and `j_x≠M` before `w_a`; hence
`j_x≤M−1`. The finalized certificate height of `F_x` is at most `j_x`
(spec 990–1003, 1064–1069), hence at most `M−1<ht(Q)`. IF.3(c) gives
`F_x⪯Q`. Now read the frame table (spec 747–768):
Q is honestly held: exact service makes Q every honest node's genuine result; F_x has an honestly stored carrier.

```text
┌───────────────────────────┬─────────────┬─────┐
│ Local state of x          │ Root Z      │ lo  │
├───────────────────────────┼─────────────┼─────┤
│ H=M+1 (then H≠j+1)        │ F           │ M   │
│ H=M, j<M−1                │ F           │ M−1 │
│ H=M, j=M−1, contested     │ F           │ M   │
│ H=M, j=M−1, not contested │ J, with J⪯Q │ M−1 │
└───────────────────────────┴─────────────┴─────┘
```

In the last row `J⪯Q`, because the held height-M block Q would
otherwise make a contest (spec 1113–1119). This proves 1.

*Step 2 (the Q-cone is in every domain).* Let `K(Q)` be the set of
blocks B with `Z_x⪯B⪯Q` or `Q⪯B`. Let V be a block set of x that
contains B and, when `B⪯Q`, also Q. Then `B∈D(V)`: `F_x⪯Z_x⪯B` or
`F_x⪯Q⪯B`; Q witnesses each `B⪯Q`, because `ht(Q)=M≥lo_x`; and each
`B⪰Q` witnesses itself, because state height is nondecreasing on a path
(IF.1), so `ht(B)≥M≥lo_x` (spec 1131–1137, 1156–1168). For a child B
with `Q⪯parent(B)`, `ht(parent(B))≥M≥lo_x`, so the below-band arm of
eligibility is false (spec 769–770, 1194–1203). These facts hold at
both floors, at every reader, and at every time before
`min(w_a,w_b)`. They need no settlement of the rise evidence and no
common frame across readers.

*Step 3 (leases).* At `d_q`, H.9's repair-gate argument gives `S_x=Q`
at every honest x and puts every live lease target below Q (spec
885–918; IF.4). Run HG.1's lease induction on labels and receipt
events. Each step of that induction uses only these facts: the live
root is in `K(Q)` or is the root `Z⪯Q`; a target below Z is covered
(a lease on an ancestor of Z is "already satisfied", spec 790–792,
and it is compatible with Q); every other target on Q's branch is in
`K(Q)`; `F⪯Q`; honest score h against at most a; IF.6 for a pending
gate; and H.1's last-write argument for slow windows at labels at
least q. Steps 1 and 2 supply each fact for every frame in the table.
Thus every write after `d_q` is a prefix of a genuine result that covers Q (spec 896–901). A
target above Q is in `K(Q)`, witnesses itself, and transfers by H.1
and H.2 from the label after its write. The whole-result guard (spec
892–893) passes at every honest gate, and each gate fast-writes Q with h
supporters. An F advance deletes no live lease, because every target
is compatible with `F⪯Q` (spec 1005–1025). This proves HG.1(1) and the
lease part of HG.1(2).

*Step 4 (exact service).* Take a later honest proposal P, so
`t_P>d_q` and P's slot is at least `q+2`, with `d_P<min(w_a,w_b)`. The
proposer and each honest HEAD reader start at a live root in `K(Q)`
(spec 779–792, 1217–1229), or at a root `Z⪯Q`. A root change J→F at a
rise only moves a start down Q's path. On Q's path below Q, the child
toward Q has at least h clean honest supporters by H.2 S1. It is
eligible by majority, because `2h>n` (IF.2). Every other child has
score at most `a<h` (spec 1170–1203). Thus every start on Q's path
reaches Q. Above Q, Step 2 makes viability and eligibility the same at
both floors. H.5 transports the scores on this retained suffix. Each
frozen competitor was a proposer competitor. Step 1 gives `F_x⪯Q`,
and the selected parent extends Q; both compared carriers are honestly held.
Thus `F_x⪯Q⪯A_P≺P`, as in H.6's receiver-exclusion step, admits P
before its HEAD and supplies its path (spec 1352–1359, 1409–1435). The finite
walk argument of H.6 gives HEAD = P at every honest reader. The h votes
for P release every conflict at `q_P`, including one from the pending
gate at `t_P+2Δ` (spec 814–825, 875–883, 1328–1339). No gate runs
between `q_P` and `d_P`. By 01 §6.6, `F⪯P` at `d_P`, and the
confirmation walk returns exactly P. Its guard passes and it
fast-writes P. The slot-(q+1) case is HG.1's own paragraph: its
proposal and HEAD precede `d_q`. This proves HG.1(2).

The carrier is held by the honest reader; F_x also has a stored carrier.
*Step 5 (sources).* Let s be an opening label with `s≥q`. The gate
`d_s` has fast-written Q with a lease that is live after `a_s`, and Q
is in the full filtered tree (Step 2). Thus the selector (spec
1448–1471) returns the deepest fresh block, and that block extends Q.
Its height is M or M+1 (Step 1). At height M, IF.1 gives the entry E.
A lock at M needs a finality pair `(M,·)`, which the action reads from
its head's state (spec 1452–1458, 1479–1491). A held carrier with
`h_j=M` has its J above `F_x` by IF.3(c), so `update_finality` sets
`j_x=M` (spec 994–997). That event is `w_a`. W1 also puts a finalization at height M
at this justification stop. It adds no event before the stop. Thus there is no lock at
M before `w_a`, and H.7's client cases give a nonempty height pair
(spec 1492–1522). At height M+1, a lock needs a justification at M+1,
hence a carrier of height at least M+2, hence `w_b` first (Step 1).
The pair is nonempty, so SO-COV (22) gives a row sent now or earlier.
Before `w_b`, no honest sent record contains height M+1. Thus send-once
cannot suppress this first row, and its emission is `w_b`. This proves 2.

*Step 6 (promotion).* HG.1 bounds the first opening with label at
least q by `a_r≤d_q+P−4Δ`. If a source there has height M+1, the
subcase of (i) holds. Otherwise all honest sources name `(M,E)`, with
`t_E≤t_q=d_q−6Δ`. HG.2 applies with `c=M`. Its row argument uses the
source clause of 2 and the service clause of Step 4; it does not read
the frame. If `w_b` or `w_a` occurs before the gate below, case (i) or
(ii) holds, because that gate is at most `B₄`; do not use Step 4 past
a stop. Otherwise HG.2 gives an honest X with `ht(X)≥M+1` and

```text
d_X ≤ max(a_r+Γ+4Δ+ε, t_E+2P+Γ+2Δ)
    ≤ d_q+max(P+Γ+ε, 2P+Γ−4Δ) = d_q+A_p,
```

because `ε≤P−8Δ≤P−4Δ` (HG.2b_F). If X reaches M+1 by the target test (spec
1070–1077), its state has `h_j=M`. Its first honest acceptance, before
`t_X+Δ<d_X`, sets `j=M` at that node. That is case (ii). Otherwise
Step 4 applies to X through `d_X`: case (iii). At `d_X`, H.9's
repair-gate argument applies to X: the exact result and the passing
guard give `S=X` at every honest node, and IF.4 puts every live lease
below X. A height above M+1 at X needs `w_b` first (Step 1). At equal
public times the gate precedes the FG action (spec 814–825), so a row
emitted at `a=d_X` does not undo service that the gate completed. This
proves 3.

*Step 7 (no charge).* Steps 1–6 use no settlement of the rise and no
repair that starts at the rise. The deadlines are functions of `d_q`
only. This proves 4. ∎

**Unchanged-frame claim after service.** If Q is served in contest(M)
and the frontier then rises to gap(M+1), L4-R applies. Both frames are
`(F,M)`. The stop `w_a` is still necessary: equal frames alone do not
extend HG.1 past a rise.

#### L4-C — Unchanged-frame carry before service — PROVED-paper

Let `w_c≥u₀` be the first honest acceptance of contest(M), and start
the H.6-S attempt there with label b and `ℓ=b+k`. Suppose the frontier
rises to M+1 before any served height-M proposal and before `w_a`.
The attempt keeps b and deadline `D(w_c)`. Each honest proposal P with
`t_P>t_ℓ` and `d_P<min(w_a,w_b)` has exact service. The repaired
proposal has height at least M. If its height is M, HG.2b_F promotes it
by its gate plus A_p, or a stop occurs first.

The block raising honest H is stored there, so its crossing path is in scope.
**Proof.** From `w_c+Δ` until `min(w_a,w_b)`, every honest H is M or
M+1: relay supplies the height-M contest witness, and a block at M+2
needs the stopping row first (IF.3(a); spec 204–217). Every honest
`j≤M−1`, and the finalized certificate height `x_F≤M−1`, before
`w_a` (spec 990–1003). A node with H=M holds the cumulative contest
evidence and has frame `(F_x,M)`. A node with H=M+1 has `H≠j+1`, so it
also has frame `(F_x,M)` (spec 747–768, 1113–1119).

H.3's witness is honestly held; F has an honestly stored carrier.
Every H.3 witness for a label at least b has height at least M,
strictly above x_F; IF.3(c) puts it above F. Receiver exclusion cannot
skip it. H.4-S, H.5, and
H.6-S's last-write split use only the root/floor at each reader,
`x_F<lo`, and b. The rise changes none of these facts. A HEAD with
`v≥w_c+3Δ` satisfies H.8 for the contest evidence; no settlement of
the rise evidence is needed. Labels before b expire by `t_ℓ+Δ`;
later labels keep the H.4-S induction. The strict gap then gives the
same D(w_c), exact HEADs, release, and passing guard. The floor is M,
so the repaired proposal has height at least M. HG.2b_F gives the stated
promotion, stopped at `w_a` or `w_b`, with L4-R Step 6's ε inequality.
W1 puts height-M finalization at the existing w_a stop. ∎

#### HG.8a — Three-charge composition at the H.11 cut — PROVED-paper

**Premises.** Recovery₂: `a≤f`; after GST all honest identities awake
and C1; the strict proposer gap with finite `G≥4Δ`;
integer `Δ_F≥Δ≥1`, K≥2, `R≥max(2,κ)`, `δ_t=2R`. In addition `k≤2R+1`, so
H.6-C gives (S) at every attempt at or after `u₀=a_(r_G+2)`. Keep
H.11's witnesses `r_G,u₀,M,r*,s*,b,C*` and run function μ and the H.22 witness tuple
without a change.

**Statement.** Put

```text
g₁ = D(u₀)+A_p,   j₁ = J₀_F(g₁),   c₁ = D(j₁),
g₂ = c₁+A_p,      j₂ = J₀_F(g₂),   c₂ = D(j₂),
A₂′ = 𝒜(c₂),      B_H^8a,F = 3P + (A₂′−u₀) + Γ + 4Δ.
```

Then `a_(r*)≤A₂′` and `t*≤A₂′+Γ+4Δ<GST+B_H^8a,F`. In integer time,
`t*≤GST+B_H^8a,F−1 tick`. Each function commutes with translation by P,
and `u₀≡6Δ (mod P)`; thus `A₂′−u₀` depends only on the parameters. At
`k=2,G=8Δ`, Δ_F≤2Δ: `B_H^8a,F=204Δ` at R=2 and `240Δ` at R=3.
For R=3, 2Δ<Δ_F≤6Δ (κ=3), B_H^8a,F=252Δ.

**Proof.** Start the search at `u₀`, with frontier M. Use H.8's `3Δ`
settlement at each charged event. The initial attempt has an H.6-S
repair gate at most `D(u₀)` (H.6-C gives (S)). Follow the stages; an
event in a stage passes its time to the next stage.

1. **gap(M).** HG.3's gap proof in HG.7's function form: a served
   frontier proposal, or an event, by `D(u₀)+A_p=g₁`.
2. **top J(M)** at `w≤g₁` (or at `u₀`). L2 with the inherited deadline
   `rd≤D(u₀)≤S(g₁)`: a served frontier proposal by
   `top_F(rd,w)≤J₀_F(g₁)=j₁`.
3. **contest(M)** at `w≤j₁`. L3: a charged floor increase. H.6-S gives
   the repair gate at most `D(w)≤c₁`. The floor is the frontier, so this
   gate serves the frontier.
4. **A rise to M+1 before service.** From gap(M) or top J(M) at
   `w≤j₁`: the floor rises M−1→M, and L3 charges the skipped contest,
   `D(w)≤c₁`. From contest(M) at `w≤c₁`, with no justification at M:
   L4-C keeps the contest repair deadline `≤c₁`. In both cases the
   M+1 stages below start with a repair deadline at most `c₁`. If the rise already
   brings `j=M`, go directly to stage 7 (top J(M+1), with `rd≤c₁`) or
   stage 8 (contest(M+1)).
5. **A served frontier proposal Q at M,** with `d_q≤c₁` (stages 1–3).
   HG.1 removes every same-frontier charge. L4-R bounds the M+1 service
   by `d_q+A_p≤g₂`, or gives a stop.
6. **gap(M+1).** From stage 4, HG.2b_F gives the M+1 service by at most
   `c₁+A_p=g₂`. From stage 5, L4-R gives the same bound.
7. **top J(M+1)** at `w≤g₂`. L2 (with L2-W for a node that jumps from
   frontier M): `top_F(rd,w)≤J₀_F(g₂)=j₂`, since `rd≤c₁<S(g₂)`.
8. **contest(M+1)** at `w≤j₂`. L3: the second floor charge, `D(w)≤c₂`.
9. **Row.** After a served M+1 proposal at gate `d_V≤c₂` (stages 6–8),
   HG.8-SI starts HG.1 at frontier M+1. HG.1(3)
   gives a nonempty honest row at M+1 sent at or before the first opening
   (SO-COV, 22), by `𝒜(d_V)≤𝒜(c₂)=A₂′`. Before the stopping row exists,
   no honest sent record contains M+1; this first row cannot be suppressed. A rise past M+1 needs that row first (IF.3(a)).
   Any rise carrier is honestly stored, so its crossing path is in scope.

The stop `w_b` in any stage ends the search earlier. The stop `w_a`
after stage 5 or 6, but before M+1 service, passes to stage 7 or 8.
After M+1 service, HG.1 at M+1 continues through top J(M+1) and
contest(M+1); no stage restarts.

Each function is nondecreasing and at least the identity. A skipped
stage only removes an allowance. An earlier event only moves a deadline
earlier. Thus `a_(r*)≤A₂′` for every event order. H.13's exclusions
(no contest(M) when `μ≤M−2`, no contest(M+1) when `M>μ`) only remove
stages; the upper bound does not use them. H.12–H.18 apply to `C*`
unchanged, and H.18 gives `t*≤a_(r*)+Γ+4Δ`. Finally `u₀<GST+3P`
(H.11). ∎

**Scope and comparison.** This bound holds for every Recovery₂ point
with `k≤2R+1` and every finite `G≥4Δ`. Only the values 204Δ and 240Δ
are restricted to `k=2,G=8Δ,R=2,3,Δ_F≤2Δ`. The proof uses `ε≤P−8Δ`,
`Γ≥4Δ`, (S), and the monotonicity of the deadline functions.
Pointwise `S≤D`, so `J₀_F≤J_F` in HG.7. Thus `c₁≤V₁`.
Since `2P+Γ≥9Δ`, HG.7's `T_F^rise(V)≥V`, and `D≥id` gives
`g₂=c₁+A_p≤D(T_F^rise(V₁))+A_p=G_F(U₁)`. Monotonicity gives `c₂≤V₂`
and `A₂′≤A₂`. Therefore, at every parameter point in this scope,

```text
B_H^8a,F ≤ B_H^ph,F ≤ B_H,F^(1).
```

There is no claim of a ρΓ analogue when `k>2R+1`. At k=2 and G=8Δ,
the following offsets are in units of Δ from u₀. The first two
columns use Δ_F≤2Δ; the last uses 2Δ<Δ_F≤6Δ.

```text
┌─────────────────────┬─────────────┬─────────────┬─────────────┐
│ Deadline            │ R=2         │ R=3         │ R=3, κ=3    │
├─────────────────────┼─────────────┼─────────────┼─────────────┤
│ g₁, j₁, c₁          │ 44,68,92    │ 52,84,108   │ 52,88,112   │
│ g₂, j₂, c₂          │ 112,140,164 │ 136,168,192 │ 140,172,196 │
│ A₂′                 │ 168         │ 192         │ 204         │
│ A₂′+Γ+4Δ            │ 180         │ 204         │ 216         │
│ B_H^8a,F/Δ (add 3P) │ 204         │ 240         │ 252         │
└─────────────────────┴─────────────┴─────────────┴─────────────┘
```

### Optional qualified-round alternative

The next three proofs retain the extra search premise. In these proofs
`g=g_h`, `θ_Q=4Δ`, `ρ=2L+G+8Δ`, `A_d=ρ+[1+(d+1)g_h+2d]P+10Δ`, and
`B_reset=6ρ+(23+13g_h)P+60Δ`. They are not premises of H.9–H.11.

### H.9-Q — Qualified opening, carrier retention, and mature promotion — PROVED-paper

Registry counterparts: `ap.source.v1`, `ap.rowService.v1`,
`ap.carrierKeep.v2`.

**Statement.** Suppose a settled phase persists after its H.6 repair.
At a qualified opening `s=rR`, every honest fresh height source is exactly
its proposal `P_s`. For Δ_F≤2Δ, earlier or new SO-COV rows reach
the honest slot-s+2 proposer before t_(s+2). For all κ in this theorem,
let r′ be the qualified opening found by a search from r+2. Then
2≤r′−r≤g+1. Its honest proposal carries the starting coverage or
inherits its matching progress bits, unless its parent crossed c.
If the parent remains at c, the entry is mature and the opening
advances height. Its exact gate/action gives the next common source.
A phase event is an earlier stop. Each promotion and next served
opening costs at most (2+g)P.

**Proof.** H.6 makes the genuine opening result exactly `P_s` with a
fresh fast lease. The phase is unchanged at the action, so `P_s` remains
in its full domain. Every fast-write target is a prefix of `P_s`;
therefore the deepest one is `P_s`. H.7 permits progress for all `h≥q_F`
honest identities. SO-COV (22) and T-ROWS use earlier or new rows for its exact entry.
Keep this starting SO-COV coverage. Its rows are held before
a_r+Δ_F≤T_r+β_F≤T_(r+1)<T_(r′). Continuing service and H.4 put
P_s below the new opening's parent. If that parent crossed c=ht(P_s),
promotion is complete. Otherwise W2 and R7 supply q_F matching
progress bits. Since E.slot≤rR and r′≥r+2,

```text
r′R≥rR+2R≥E.slot+2R,
```

the opening is mature.
R7's optional omission keeps every effect (01 §1.1), so this argument is unchanged.
Target processing or mature progress advances
height. Exact service at this opening gives its new common source at
the gate/action. A phase event ends the attempt sooner. The wait is
at most (g+1)P, within the retained (2+g)P budget. For κ>2 this proof
uses no complete +2 carrier. For Δ_F≤2Δ such a carrier, if used,
keeps its matching bits by W2 until height progress is complete. ∎

**DC port.** Paper line 772 and lines 2218–2279 give exact-entry progress,
maturity, and bitmap reset. `Protocol.progReady`,
`Protocol.process_height_events`, and `fixedRootProgress_of_rows`
(`HeightProgressFixedRoot.lean:2112`) are the relevant Lean declarations.
The bitmap reasoning is unchanged. The SA fast write and H.4 replace
DC grade/lifecycle retention. R6/R7 and retained matching bits also
apply at `R=2`; there is no row-round check.

### H.10-Q — Attempt and rise budgets — PROVED-paper

Registry counterpart: `fj.rise.movingF.v1`, with current rules and
`Recovery₂`.

**Statement.** Under Recovery₂ and a qualified-opening search bound
`g_h P` (for example Rec_s(g_h)), start a task at `u≥GST` with the
current frontier evidence. For the reset search take `u≥u₀`: if the
phase began before `u₀`, restart its clock at `u₀`. A task that needs
at most `d∈{0,1,2}` promotions either encounters an effective phase
end, or, while that phase persists, an honest row at the required height
is sent at some time at most `u+A_d` (SO-COV, 22), where

```text
A_d = θ_Q+ρ+[1+(d+1)g+2d]P+6Δ.
```

A frontier observed at a task start `u≥GST` rises within `2A_2+A_1`,
unless the target reset row already exists.

**Proof.** Pay `θ_Q` to settle the evidence and `ρ` for H.6. Use the original
G-gap in H.6: `d_s≤u+4Δ+2L−2Δ+G+6Δ=u+ρ` at H.6's settled start u. If the phase
ends during either interval, charge elapsed time, which is less than or
equal to that attempt budget, and stop. Otherwise align once to an opening
within `P`, and find a qualified opening within `gP`. H.9-Q supplies its
source. Each of `d` promotions and the next served opening costs at most
`(2+g)P`. Its final action adds `6Δ`. Addition gives the formula.
If any of these steps changes the phase, it is again an early endpoint,
not permission to use service across that change.

At frontier `m`, an ordinary source has height at least `m−1`; two
promotions suffice to reach `m+1`. A contested source has height `m`;
one suffices. H.7 permits at most one gap, one top-J, and one contest
attempt. Sum the two ordinary and one contested budgets. No carrier
count appears in this sum; disclosure of more old carriers within one
phase is already covered by H.6 and H.9-Q. For `m=1`, heights are at
least 1, so two is an overestimate and remains valid. ∎

### H.11-Q — Causal cut and reset arrival (`fj.reset.v1`) — PROVED-paper

**Statement.** Add the qualified-opening search premise of H.10-Q.
Let `r_G` be the first action round at or after GST,
`u₀=a_(r_G+2)` with its inclusive event prefix, and
`M=max_x H_x(u₀)` over honest nodes. Let

```text
μ = max({1} ∪ {height of an honest row whose source vote time is <GST}).
```

Here μ is determined by the run and GST; it is not a witness field (only rows with a nonempty height pair count).
Then `μ≤M`, `GST+2P≤u₀<GST+3P`, and every honest height row
emitted through the inclusive cut `u₀` has height at most `M`.
There is a first round `r*` with an honest row at height `M+1`.
Put `s*=r*R`, `b=s*`, and select one fresh source `C*` of such a row. It has height `M+1`, its label is synchronous,
and

```text
a_(r*) < GST+B_reset,
B_reset = 3P+2A_2+3A_1+A_0
        = 6ρ+(23+13g)P+60Δ.
```

**Proof.** Actions have period `P`. The first one after GST is in
`[GST,GST+P)`, which proves the cut inequalities. An old-source row
acts at most `5Δ` after its vote time. Since `2P≥16Δ>5Δ`, its honest
source was held before `u₀`. Cumulative storage means that source's
height is included in its holder's `H(u₀)`, even if it later leaves
`act(Σ)`. Thus `μ≤M`.

A row at height above `M+1` requires a path crossing `M+1`, hence an
earlier honest row there by IF.3. A row at `M+1` at or before `u₀`
would itself have a stored source that raises `M`, a contradiction.
Hence a first such row, if produced, has `r*≥r_G+3` and
`t_(s*)=a_(r*)−6Δ≥GST+3P−6Δ≥GST+2P` for `R≥2`.
The row's source is honestly held, so its crossing path is in scope.

Start from the greatest frontier `M` at the cut. H.8 settles its evidence,
unless a rise already occurs. H.10-Q needs at most `A_2,A_2,A_1` for
its gap, top-J, and contest phases. At frontier `M+1`, stop at the first
honest row at that height. An ordinary common source starts at height
at least `M`; one promotion suffices. A contested source is already
at `M+1`, so no promotion is needed. The remaining budgets are
`A_1,A_1,A_0`. A jump to `M+2` has already used the required honest
row and ends the search. Therefore the row exists within
`2A_2+3A_1+A_0` of the cut. The strict cut bound supplies the strict
GST bound. Expanding the six attempts gives `6ρ+(20+13g)P+60Δ`;
adding `3P` gives the displayed result. ∎

**DC port.** DC paper lines 1158–1214 explain its source readiness and
round action; its Lean `gstLagged`/`GradeRoundReady` interfaces
(`DecoupledConsensusInternal/HealingSurface.lean:145,150`) and
`frontierRegime_after_oneDelay` are the comparison points. Here the
inclusive cut is retained, but SA's two-lease repair replaces grade
readiness. The stop is the first honest `M+1` row; there is no NJ-selected
height, no DC NJ parameter, and no invocation of a DC NJ handoff theorem.

## 6. Source retention after the reset

This section proves the frame property before using any full-healing
conclusion. The causal order is: retain high fast sources; deduce unique
high entries; then retain all base bodies. No step assumes exact repaired
proposal service to establish high-source retention.

### H.12 — Source timing and initial reset transfer — PROVED

**Statement.** An honest controlling row present before the proposal or
HEAD of slot `u` has source label `s≤u−2`. Its synchronous source body
and entry are in all required frozen paths before `z_(u−1)`, unless
finality already covers the needed prefix. At `q_(s*)`, every honest
reader holds `C*` and has `H=M+1`. It keeps `C*` at that first transfer,
regardless of differences in old top-J or contest evidence.

**Proof.** The row's action is `d_s=t_s+6Δ`. For `s=u−1` this is
`t_u+2Δ`, after both duty reads. Later labels are later still. Thus
`s≤u−2`. The fast source has an honest supporting HEAD at `v_s` by
IF.6, so its full body relays before `e_s=t_s+2Δ≤t_u−6Δ<z_(u−1)`
where admission is required. For old bodies use their honest acceptance
before GST and relay by `GST+Δ`; duties after the cut are later than
that deadline. Compatibility is established by the certificate cases
below before applying IF.5.

C* is an honestly held source; the lower finalization has a stored carrier.
For `C*`, the same fast-support argument supplies its body before
`e_(s*)`, hence before `q_(s*)`. Before action `d_(s*)` there can be
no carrier above `M+1`: its crossing requires an earlier honest row at
`M+1`, contrary to the definition of `r*`. Thus at `q_(s*)` the
admitted `C*` gives exactly `H=M+1`. A lower finalized checkpoint
precedes `C*` by IF.3(c). An uncontested top `J` at height `M` must
precede `C*`, since `C*` itself would otherwise be a contest witness.
In a contest `lo=M+1=ht(C*)`; outside a contest `lo≤M`.
Consequently `C*` is kept, with itself as witness. H.1 releases conflicts
at `q_(s*)` using the eventual surviving fast supporters. The gate's
future late test is evidence about this execution, not an input read
early by the code. ∎

### H.13 — Source retention above μ (`fj.descent.v3`, `fj.canonical.v1`) — PROVED

**Statement.** Every synchronous honest FG fast source `C` of height
`c>μ` retains all honest HEAD support from `q_s`, where `s` is its
source label. Such sources are pairwise compatible. At each height
`c>μ`, all honest height rows name one entry and are targets. A contest
with top justification height `j>μ` is impossible, including one from
private evidence.

**Proof.** Work in a finite event prefix containing an alleged first
failure; induction on event index then extends the result to the run.
A failure means an honest choice HEAD at or after `q_s` does not cover
`C`, a body selected as a source above `μ` somewhere in the run (the selection may come before or after the failure). At the first transfer H.1 releases every conflicting lease. At a
later transfer an old surviving lease was either present after that
release, or has a genuine origin at a later label. The first kind is
compatible. A same-label origin is compatible by IF.6. A later
conflicting genuine origin would have an honest supporter that already
departed `C`, at an earlier vote. It cannot precede the chosen first
failure. Thus an incompatible lease or an unfavourable score cannot be
the first cause when `C` is kept: H.1 and its `h`-vote continuation apply.

The body `C` is in every relevant admitted path before its first
transfer by its honest supporter and relay. At a read, either finality
covers it, or analyze its possible exclusion as follows.

  C is an honestly held source; F's controlling carrier is honestly stored.
* If finalized `F` conflicts with `C`, IF.3(c) implies its certificate
  height `x≥c`. Its justification has an honest target source on `F`'s
  branch, conflicting with `C`, at height `x`.
* If an uncontested top `J` conflicts with `C`, its height is `H−1`.
  If `c=H`, the admitted `C` makes a contest, so this case is impossible.
  Hence `H−1≥c`. An honest target in the justification gives a
  conflicting source at that height.
* If the ordinary band removes `C`, then `c<H−1`. Take a height-`H`
  carrier and an honest row in its crossing of `H−1`. Its source has
  height `H−1>c`. If that source were compatible with `C`, its entry
  at the greater height would extend `C`. Its source body, present
  before this duty's freeze by H.12, would witness `C` at the floor.
  This contradicts exclusion. Thus it is a conflicting source.
* If the contested floor removes `C`, then `c≤H−1`. There are two
  different entries at `H−1`: top `J` and the entry of the off-J
  crossing. If `c<H−1` and both were compatible with `C`, both extend
  `C`; the disclosed crossing supplies a height-`H` witness in the
  full domain. If its carrier misses the freeze, its honest source
  body at `H−1` alone is not a height-`H` witness. Instead apply the
  following first-failure argument to the two source entries: at a
  height `H−1>μ`, their honest sources cannot coexist, as shown in the
  next paragraph. If `c=H−1`, at least one entry conflicts with `C`:
  two distinct entries of the same height cannot lie on its one path.
  That entry's honest row supplies a conflicting source at height `c`.

To make the contested subcase and uniqueness noncircular, choose the
first event among (i) a loss of a body selected as a source above `μ` somewhere in the run (its selection need not precede the loss), and (ii) the emission
of two incompatible honest sources above `μ`. For (ii), equal labels are
excluded by IF.6. At different labels `s<s'`, the honest supporter of
the later body votes at `v_(s')≥q_s`; it is already a loss of the
earlier body, strictly before the later action. Hence (ii) cannot be
first. In the contested case with `c<H−1`, both certificate sources
have height above `μ`. Their entries are distinct, so their bodies
conflict. Both emissions precede the contest read, and (ii) would already
have occurred. This resolves the missing frozen-carrier case without
assuming that the carrier is in the view.

In each remaining exclusion case obtain an honest conflicting source
`C'`, of height `c'≥c`, and label `s'`, whose row was already emitted
before the failing duty. If its vote time is before GST, `c'≤μ`,
contrary to `c'≥c>μ`. If `s'=s`, IF.6 excludes the conflict. If
`s'>s`, its honest supporter at `v_(s')`, before its row and before
the failing duty, is an earlier loss of `C`. If `s'<s`, the honest
supporter of `C` at `v_s≥q_(s')` is an earlier loss of `C'`, which is
also above `μ`. Both contradict the first-failure choice. The decreasing
measure is
failure event index, not source label: the case `s′>s` gives an earlier
loss of the same source. Thus no source above `μ` is lost and no
incompatible pair above `μ` is emitted.

Both honest source paths are held; part (a) extracts the crossing's signed witnesses.
Compatible sources at one state height have the same entry by IF.1.
No honest target or timeout at a height above `μ` can have an old
source. A finality lock created before GST requires a prior
justification with an honest target row at that height. That target's
source vote is before GST, so its height is at most μ. Thus there is
no pre-GST lock above `μ`. At the first target, timeout, or lock in the event
induction, any lock has a prior honest
target for this unique entry, and an honest conflicting target is
impossible. With NJ false, a fresh client targets it and subsequent
clients either first target it or have an earlier matching target.
Send-once suppression makes no record write. No first timeout can occur:
its client would need an earlier different target or timeout. Thus all
rows above `μ` are targets. Two different crossing entries at such a height
would need incompatible honest sources by IF.3(a). Therefore there is
no contest with `j>μ`. ∎

**Port boundary.** DC's paper state and client rules (lines 772–847,
1048–1146) and its certificate declarations provide the cause analysis.
DC uses an NJ height to remove its descending J-root case. FJ instead
makes `c=H` a contest and raises the floor in both tests. The descent
above is a new FJ proof; no DC theorem proves this replacement by itself.
The finite event-index formulation is the Lean induction measure. A
standalone claim that a late maximum carrier is already frozen is not used.

### Registry restatement — fj.descent.v3 — PROVED-paper

_2026-09-29. fj.descent.v1 is WITHDRAWN for use under 4e85ff34.
Its conclusion puts the controlling QC in the failing HEAD view, but
live-cache controls can use evidence outside that frozen view. Thus its
pinned descent step is unusable here. Keep its old pins as history;
use fj.descent.v3 with cumulative controls and the event-index measure._

Use H.13's reachable-run premises, IF.1–IF.6, and μ as the maximum of
1 and the heights of honest rows with source vote before GST. An
abandonment of source C of synchronous label s is an honest HEAD at
label i≥s+1 that does not cover C. Choose the first event among a loss
of a source above μ and the emission of two incompatible sources above μ.
Controls F,J,H,Z,lo come from cumulative Σ.T and its live caches. They
are not duty-view controls, and a controlling QC need not be frozen.

For an alleged loss of C at height c>μ, a lease or score failure cannot
be first while C is kept, by H.1–H.2 and same-label compatibility. The
remaining cause analysis gives a conflicting honest source C′ at
height c′≥c, whose row precedes the failing duty, in the following cases:
conflicting F; conflicting uncontested top J; ordinary-band exclusion;
or contested exclusion with c=H−1. For ordinary-band exclusion c′=H−1>c;
for top J and the equal-height contested case c′=H−1≥c.

1. If C′ has a pre-GST source vote, `c′≤μ`, which contradicts c′≥c>μ.
2. If its synchronous source label `s′>s`, its honest supporter voted
   at `v_(s′)≥q_s`. That vote is an earlier abandonment of C, before
   the row of C′ and before this failing duty. v1 excluded this case
   by its per-source first-abandonment definition; v2 needs it because
   its measure is the global event index, not the source label.
3. If `s′<s`, C's honest supporter at `v_s≥q_(s′)` is an earlier
   abandonment of C′. Equal labels are excluded by IF.6.

For contested exclusion with `c<H−1`, do not infer a frozen height-H
witness from a source body of height H−1. The two different entries
at H−1 have incompatible honest sources above μ. Both rows precede
the contest read, so their emissions give an earlier bad event. If a
pair emission is the proposed first bad event, equal labels contradict
IF.6; at different labels the later source's supporter already abandoned
the earlier source before the pair emission. This closes that case too.

Controlling carriers are honestly stored; all compared honest source paths are held.
**Proof.** These are the four exclusion cases and the joint first-event
argument of H.13. Source-body timing is H.12; certificate provenance and
crossing are IF.3. The earlier event in every case contradicts the choice
of the first bad event. Hence no high synchronous source is lost and no
incompatible pair above μ is emitted. The proof uses the source body
when it needs a frozen witness; it never substitutes a late carrier.

### H.14 — Kept-path lemma after reset (`fj.theoremN.v1`) — PROVED

**Statement.** Let `b=s*`. Protect all successful fast bodies with labels
`s≥b`, and all successful slow bodies whose whole window lies in
`[b,∞)`. Each such body B remains kept at every later choice duty
used in H.2: it has a witness in that duty's own domain, is below its
root, or has root/anchor coverage. For a HEAD, the witness must be in
its HEAD view; a full-domain witness alone is not sufficient.
For each B, S1–S3 of H.2 hold for all later times. These kept-path and
transfer clauses also apply to the selected reset source `C*`.
Every actual honest selected fresh source of height at least `M+1`
has label at least `b`, including a source whose action sends no row. Every nonempty honest height row at that height therefore
has label at least `b`. In this chapter and in 22, **high** means height
at least `M+1`; H.13 proves the stronger range `c>μ`. For every
post-reset duty that holds `C*`,

```text
H≥M+1;  contest ⇒ H=M+1;  lo≤max(M+1,H−1).
```

The selected source is honestly held, so its crossing path is in scope.
**Proof.** H.13 applies to `C*`, because `M+1>μ`, and proves its
continued HEAD support. H.2 supplies its parent and output clauses.
Consider a selected source before `b`. If its height exceeds `M+1`,
its path has crossed `M+1`, which needs an earlier honest row there
by IF.3. If its height is `M+1` and the action sends a row, it
contradicts the definition of `r*`. If send-once suppresses the row,
SO-COV (22) gives an earlier honest row at M+1 in the sent record,
which gives the same contradiction. If height_pair is empty because
of a mismatched effective lock, the lock requires a prior justification
at M+1 and hence an earlier honest target row there. Thus every selected
high source has action label at least s*, including actions that send no row. The
displayed frame inequalities
follow from the admitted `C*` and H.13's high-contest exclusion.

C* is an honestly held source; the lower finalization has an honestly stored carrier.
Here is the exact geometric kept-path step. Suppose `B` is compatible
with `C*` and with every earlier controlling high source, and its
support path is present. A lower finalization precedes `C*` by IF.3(c).
A high finalization or high active justification is a prefix of an honest
high source. Thus its root is compatible with `B`. An active top `J`
at height `M` precedes the admitted `C*`, or it would cause a contest.
If a root covers `B`, the duty covers it. Otherwise that root precedes
`B`. At `H=M+1`, a body of height at least `M+1` witnesses itself;
a lower compatible body is a prefix of `C*`, which witnesses it.
At `H≥M+2` there is no contest. If `ht(B)≥H−1`, use `B` itself.
If it is lower, take an honest source in a maximizing carrier's crossing
of `H−1`. The source body has height `H−1≥M+1`, is already available
before the freeze by H.12, and, by compatibility and height, extends `B`.
It is the required witness even if the maximizing carrier arrived late.

Induct jointly on labels and event prefixes of the protected bodies.
The first-transfer release or slow-window step is H.1. An honest
supporter of a new body shares its path with each earlier protected body,
by that body's S1. Equal-label bodies are compatible by IF.6.
A controlling high source already emitted before a duty has an earlier
source label; at the first transfer for label `s`, that label is at most
`s−1`. Its S1 puts it in the new body's honest supporter's HEAD. The
geometric step just proved therefore keeps the new body. Transport of
its honest support path gives presence. H.2 gives continued support,
parents, and outputs; when it needs keep at a later duty, the same
geometric step applies to its earlier, same-label, and later controlling
sources. Earlier sources were in the original supporter's HEAD;
same-label sources use IF.6; later sources have an honest supporter in
a batch already covering `B`. Each invocation is to an earlier event
in this joint induction. A conflicting `F` would be a conflicting
honest high target source, which these cases exclude, or a lower `F`
preceding `C*`. Thus reconciliation cannot invalidate the induction.
This proves every claim without an assumption of full healing. ∎

## 7. Local full healing: Lemma U and Theorem H′

### H.15 — Causality above C* and universal leases (Lemma U) — PROVED

**Statement.** If `C*≺B`, no honest node held `B` at or before `u₀`.
Every honest genuine-result label covering `B`, and every label in a
successful slow window covering `B`, is synchronous. If an honest gate
of label `s` writes or renews a lease on `B`, then B has S1–S3 from that
label, including a write before the reset action. All subsequent genuine
results at labels `i≥s+1` extend `B` or have finality coverage of it.

C* is an honestly held source; each then-current F has an honestly stored carrier.
**Proof.** `ht(B)≥ht(C*)=M+1`. Honest admission before or at `u₀`
would raise the cumulative cut maximum above `M`. It cannot be a
raw-only stored body: there is no raw tree. IF.3(c) also puts every
then-current honest finality below `C*`. Thus it was not held.
A gate covering `B` has `d_s>u₀≥GST+2P`, hence
`v_s=d_s−5Δ>GST+2P−5Δ>GST` for `R≥2`. Apply this calculation to
each actual saved result in a slow window. It makes no assumption on
`k/R`.

For the first transfer of a successful write, H.1 excludes all conflicting
leases by fast release or by the slow last-write-label argument. IF.6
gives an honest supporter. If `q_s≤q_(s*)`, no carrier above `M+1`
exists yet. Any read holding `B` has frontier `M+1` and floor at most
`M+1`. A lower `F` precedes `C*`; an active top `J` must precede `B`
or `B` itself causes a contest. Thus `B` is kept and witnesses itself.
If the first transfer is after `q_(s*)`, each controlling high row has
source label at most `s−1`; H.14 puts its body in the label-s honest
supporter's HEAD. It is compatible with `B`. H.14's geometric step
keeps `B` at that duty. In both cases the honest support path is frozen
in time and H.1 gives the first common batch.

For each next batch all `h` honest votes cover `B`, so H.2's release,
gate, and parent proof applies. At a later duty its controlling high
source has already transferred by the preceding batch. That batch also
covers `B`, and gives their compatibility in one actual HEAD. The same
geometric step keeps `B`. A lower finalization precedes `C*`; a higher
one has its target source in this history, so neither can conflict.
This closes the induction for every subsequent label and for all the
intervening `F` assignments. ∎

### H.16 — Every post-reset genuine result transfers (Corollary U′) — PROVED

**Statement.** Every nonempty genuine result `C` at an honest node at
label `j≥s*` transfers from `q_j` and thereafter has S1–S3. This includes
results with support below `τ`, and vetoed results.

**Proof.** At `j=s*`, IF.6 compares `C` with the reset emitter's result,
which extends `C*`, and gives compatibility. At later labels, the honest
supporter of `C` covers `C*` by H.14, so compatibility still holds.
At `q_j`, any lease has last write label at most `j−1`. A lease
conflicting with `C*` was released at `q_(s*)`, or was subsequently
deleted by finality; it cannot be rewritten from a same-label or later
conflicting result, by IF.6 and H.14. A lease below `C*` is compatible
with `C`. A lease strictly above `C*` is in every label-j honest HEAD
by H.15, hence compatible with `C` in its honest supporter's HEAD.
There is no conflicting live lease. If `C⪯C*`, coverage of `C*`
suffices. If `C*≺C`, H.15's geometric first-transfer proof applies
using earlier controlling high sources. H.1 transfers `C` without
requiring `p≥τ`, and H.2 with the same kept-path induction gives its
continuation. A vetoed result is still an actual saved genuine result,
so all the count and path premises used here remain true. ∎

### H.17 — Exact service after the reset — PROVED

Registry counterpart: `fj.Xplus.v1`, with the cumulative live frame.

**Statement.** At every honest proposal `P` of slot `u≥s*+2`, every
honest HEAD equals `P`; its gate is successful and every honest output
contains `P` at `d_u`. The raw genuine result is exactly `P`, each
gate fast-writes `P`, and every honest post-gate `S` equals `P`.
If `u=rR` is an opening, each action at `a_r=d_u` selects `C_fg=P`.
These claims use the post-gate cut and permit frame changes between
proposal and HEAD.

**Proof.** A lease present at `t_u` or after the release at `v_u` has
last write label at most `u−2`. Classify its target: a conflict with
`C*` is already removed; a prefix of `C*` is covered by H.14; a strict
descendant is covered by H.15. Therefore all previous-label honest HEADs
cover every such target. The ordinary proposer walk passes through all
of them by score `h>a`. Its actual lease start is on this ordinary path,
so its parent `A_P` equals the ordinary result. Every same-slot honest
HEAD start lies below `A_P`. This proves the common-pivot conditions
without another two-lease wait.

Let `m` be the greatest live `H` among the proposal and all its honest
HEAD reads. If `m=M+1`, put `T=C*`. If `m≥M+2`, select an honest
row in a maximizing carrier's crossing of `m−1` and let `T` be its
source **body**. It has height `m−1≥M+1` and source label at most
`u−2` by H.12. H.14 gives `T⪯A_P`, puts `T` in all preceding-label
honest HEADs, and keeps it at each compared read. Its path was relayed
before the relevant freeze even when the carrier was not. In both cases

```text
T⪯A_P,    ht(T)=max(M+1,m−1)≥lo_d for each compared read d.
```

Each root is below `A_P`: a lower `F` is below `C*`; a higher `F` or
`J` precedes its earlier high source, which is below `A_P` by S2;
a top `J` at height `M` must precede `C*` if active. Thus before `T`
all walks follow its honest-supported path. At and above `T`, every
parent is at or above every compared floor, so the below-band eligibility
clause is off in all compared reads.

It remains to compare old candidate children above `T`. A HEAD candidate
not on `P`'s path is from the frozen arm, so its path reaches the proposer
before `t_u`. Above `T` it witnesses itself for every smaller floor.
Its eligibility depends only on majority, since it is old. If it
extends the proposer's `F_p`, H.5 gives equal retained scores and it
is a proposer candidate. The missing case is a child `c` that conflicts
with a high `F_p` strictly between `T` and `A_P`. A lower `F_p` is below
`C*⪯T` and cannot cause this case. The justification for high `F_p`
has an honest target source of label at most `u−2`; H.14's S1 puts
that source, and hence `F_p`, in every honest label-`u−1` HEAD.
No honest vote can support `c`. Its score consists only of faulty
supporters or equivocators, at most `a`, while all `h>2a` honest seats
participate. It cannot have a majority. Its parent is at or above `T`,
so the band arm is false; its old slot makes the current-slot arm false.
Thus this extra reader candidate is ineligible. These two cases give
reflection of every eligible reader child. Conversely, each chosen
proposer-path child
is on `P`'s admitted path, is above `T`, and remains eligible with the
same score. Induction along that path proves identical choices. At the
parent the only new eligible child is `P`; it has no valid same-slot
child. Each HEAD is `P`.

A possible finality change during P's delivery is also covered by these
root arguments: the receiving `F` precedes `A_P`, or equals a prefix
already on it. Thus P is admitted by strict delivery before the HEAD;
this is not assumed merely from its honest signature.

C* is an honestly held source; each finality-origin carrier is honestly stored.
Release of all conflicts at `q_u` and exact genuine result `P` at `d_u`
follow from the `h` votes, including the pending-gate case of H.6.
By 01 §6.6, F≺P at `d_u`; these votes make F eligible, so the walk from F returns P.
Before this gate any gate-origin `S` has label at most `u−1`, so its
block slot is less than `u` and it cannot be a proper descendant of `P`.
For an `F`-origin output already available before `d_u`, choose an honest
target source in a justification used by an honest finality signer for
that checkpoint. That target row precedes the signer's action by at least
one round. If the finality is available before this gate, that source's
label is at most `u−2` (an action of label `u−1` is at `t_u+2Δ` and
cannot yield an honest finality row before a further `P≥8Δ`). A high
source is below `A_P` by S2; a low finalization is below `C*` by IF.3(c).
Thus this output origin cannot be a strict extension of `P` either.
`advance` with exact candidate `P` therefore returns `P`, and current
`F⪯P` leaves it unchanged. This establishes equality at each post-gate
state.

At an opening gate, any new controlling row since the compared HEADs
comes from the preceding opening, of label at most `u−2`; same-time
new rows follow all local action reads. Its high source is below `A_P`
by H.14 S2. A maximizing crossing source thus has height at most
`ht(A_P)`; a remaining contest has floor `M+1≤ht(P)`. Consequently
`ht(P)≥lo` at the action. The same source argument puts all roots and
`F` below `P`, so `P` witnesses its own full-domain membership.
Its successful fast write has deadline `d_u+L>d_u`. Every other member
of `fastWrite[u]` is a prefix of `P`, so `get_fg_vote` (spec 1434–1457)
selects exactly `P`. ∎

**DC port.** Paper lines 211–230, 889–901, 2006–2075;
`DecoupledConsensusModel.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer` and
`fixedHeightJustificationRoot_namedOpeningVoteStoresExtend` are the
comparison interfaces. Here the common high body `T` handles unequal
live frames. The argument uses the two DC view arms; it has no support-path,
lease-path, or finality-basis addition to the HEAD view.

### H.18 — Full healing (Theorem H′, `fj.healed.v1`) — PROVED

**Statement.** Let `u` be the first honest proposal slot at least `s*+2`.
Then `HEALED(d_u)`. At every suffix event read `t≥d_u` and for all
honest `x,y`, `F_x(t)⪯S_y(t)`. This includes a finalization accepted
before `d_u` that is still current. Moreover,

```text
d_u ≤ q_(s*)+Γ+5Δ = a_(r*)+Γ+4Δ.
```

Every honest proposal strictly after `q_(s*)` already has `6Δ` service.
Full healing at `q_(s*)` itself is not a consequence.

**Proof.** H.17 starts all honest outputs at the same block `P` at `d_u`.
H.16 protects every genuine result from label `u` onward, including
low-support results in slots with a faulty or silent proposer. Equal-label
results are compatible by IF.6. At different labels, the later result's
honest supporter covers the earlier one by H.16, so the results lie on
one chain. Each new nonempty genuine result at labels after `u`
extends `P`: if F⪯P, honest score h makes F eligible and forces the
F-to-P path; if P⪯F, every nonempty result already covers P.
The result can be ⊥ if F has passed the honest heads. An empty gate
keeps S, with F⪯S; a vetoed gate also keeps S. A candidate below `S`
also leaves it unchanged; any other successful candidate on this chain
extends it. This proves common-chain outputs and local monotonicity for
gate events.

The assigned F has an honestly stored carrier; C* is an honestly held source.
Consider an `F` assignment. For a finalization of height at most `M`,
IF.3(c) puts it below `C*⪯P`. For a higher finalization, take an honest
finality signer and an honest target row in the justification known to
that signer before its action. Call the target source `C_J` and its
action `d_s`. It is a protected high source. The finality action is in
a strictly later round, because rows created at one public action cannot
be folded into that action's earlier read. Thus it is at least `d_s+P`.
H.14's S3 puts `C_J` in all honest outputs by `d_s+4Δ`, and
the round length satisfies `4RΔ≥8Δ>4Δ`. Before this finalization can
be used, all readers
already cover its target. The protected source history continues that
coverage. Consequently `F_x(t)⪯S_y(t)` for every honest pair `x,y` after the
healing cut. For an `F` already accepted before that cut, the same
source-transfer deadline is before its acceptance; protected coverage
persists to the cut. Low finalizations precede `C*⪯P`, which every
output contains from the cut. This proves cross-node coverage, not only
local nesting. Normalization cannot cause a reorganization. IF.4 supplies local
nesting at all other times. This proves the remaining event case and all
safety clauses of `HEALED`.

H.17 applies to each later honest proposal and proves the service clause.
For the deadline, use the proposal-grid strict trigger `t_(s*+1)`. It supplies
`t_(s*+1)<t_u≤t_(s*+1)+G`; the slot grid implies `u≥s*+2`.
Adding `6Δ` gives `d_u≤q_(s*)+G+5Δ=a_(r*)+G+4Δ`, hence the stated Γ bound. A proposal strictly after
`q_(s*)` has slot at least `s*+2`, so H.17 gives its service even before
this full-healing gate. The old outputs before that gate have not been
included in the monotonicity claim. ∎

### H.19 — All-fast corollary — PROVED

**Statement.** If, in addition, `2τ−2≤h=n−a`, then
`HEALED(d_(s*+1))=HEALED(q_(s*)+5Δ)`.

**Proof.** At any synchronous genuine result, `2p>D≥h≥2τ−2`.
If `p≤τ−1`, then `2p≤2τ−2`, a contradiction. Thus every such result
has fast support. By H.14, all honest `S` values cover `C*` from
`d_(s*+1)`. A prior gate-origin value strictly above `C*` has a
synchronous origin by H.15. Its successful gate wrote a fast lease on
that value; H.15 makes it universal from its next vote. Values from
labels at least `s*` are universal by H.16. These universal bodies all
occur on a common later honest HEAD, so they are mutually compatible
and every subsequent genuine result extends them. Finality-origin values
are prefixes of the protected sources described in H.18. The same gate
and finality event cases therefore give monotone common-chain outputs
from `d_(s*+1)`. Each honest proposal from that time is in a slot at
least `s*+3`, so H.17 gives service. IF.4 gives nesting. ∎

Under this count condition, H.11 and H.19 give the output-healing
bound B_H^F−Γ. It does not replace H.22's actual-proposal witness gate.

## 8. Interface and uniform theorem

### H.20 — Uniform healing (`fj.healedUnif.v1`) — PROVED-paper

**Statement.** Under `Recovery₂`, `HEALED(GST+B_H^F)` holds for

```text
B_H,F^(2) = max(12L+12Γ+12P+49Δ+2ε, 8L+10Γ+14P+19Δ).
B_H,F^(1) = max(6L+12Γ+12P+61Δ+2ε, 4L+10Γ+14P+27Δ)  (requires k≤2R+1).
B_H^F = min({B_H,F^(2)} ∪ {B_H,F^(1) if k≤2R+1}).
```

There is a first proved healing gate strictly before this deadline.
The statement and proof are independent of `M`, the amount of private
old evidence, and the number of lower finalizations.

**Proof.** H.11 gives `a_(r*)<GST+B'_reset^F`. H.18 supplies an actual
healing gate `d_u≤a_(r*)+Γ+4Δ`. Add the inequalities for each eligible repair
bound in H.11.
Both proofs use the same first reset row and the same first honest
healing gate, so their minimum bounds that gate. `HEALED` is
closed under increasing its start time: each of its four quantified
clauses then ranges over a subset of the original events or proposals.
This gives the named deadline. The HG.5 search in H.11 uses only
the two frontiers and their three possible phases, not their numerical
height or the number of stored carriers. H.5 removes lower finalizations
from the phase count. ∎

Under the qualified-search premise, H.11-Q and H.18 also give a healing
gate before `GST+B_heal(g_h)`. Both proofs use the same first reset row
and repair gate. Therefore `HEALED(GST+B_best^F(g_h))` holds, where
`B_best^F(g_h)=min(B_heal(g_h),B_H^F)`.

All event times and these bounds are integers. Therefore the strict
gate deadline gives `t*≤GST+B_H^F−1` and `HEALED(GST+B_H^F−1)`.
With qualified search, use B_best^F instead. The tables report the
scale-uniform Δ coefficients; subtract one integer tick for this
refinement. Optimality remains OPEN. HG.1 removes same-frontier repair charges after a served frontier
proposal. A single initial repair for the whole search remains OPEN.

### H.22 — One exported healing interface — PROVED-paper

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
from the action's opening-label `fastWrite` set, with a live lease in
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
lemmas H.5 (lower F moves) and H.6 (two-lease repair).

**H5 — raw-result transfer.** Under the Recovery₂ premises of 21 §2,
every nonempty honest raw genuine result C at label `j≥s*` has no
conflicting live lease after release at q_j.
All honest HEADs at labels `i≥j+1` cover C; all honest proposal parents
at slots `v≥j+2` cover C; all honest outputs from `d_j+4Δ` cover C.
This includes results with support below τ and results whose guard
was not assumed to pass. The lease claim concerns the release state;
the result is evaluated at d_j and is not read by the earlier release.

**H6 — unanimous gate service.** Under the Recovery₂ premises of 21 §2,
let `j≥s*` be synchronous. Suppose every honest label-j HEAD covers a
non-genesis block D, and `F_x⪯D`
at every honest gate read d_j. Then at each such gate the raw result
is nonempty and covers D, its whole-result guard passes, and D is in
`fastWrite[j]` with a live lease of deadline at least `d_j+L>d_j`.
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

**Proof.** H.11 proves H0 through the reset source and inclusive row cap.
For H0's last sentence, H.18 chooses u,Q* and t*=d_u≥GST; H.14 S2
gives C*⪯parent(Q*)⪯Q*. H.14 proves H1's source-label bound.
Every high source has label s≥s*, and v_(s*)≥GST, so v_s≥GST:
every high source is synchronous. H.13 therefore applies and gives
their compatibility, including compatibility with C*. H.14 with H.2
gives H2 (S2) and H2.A (S1 and S3). T-ROWS follows from the selector
and receipt proof in 01 §1.1, with effect-specific persistence from
W2 and 01 §3.1.

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

H.16 proves H5, including the no-conflicting-lease statement in its
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
Apply H5 to this C. No lease conflicts with it after q_j. No gate runs
strictly between q_j and d_j; expiry, release, and reconciliation can
only remove leases there. Its guard therefore passes. The prefix loop
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

## 9. All-R check and numerical values

### H.21 — Parameter extension to every R≥max(2,κ) — PROVED-paper

**Statement.** All statements H.1–H.20, HG.1–HG.6, and H.22 hold for every integer `R≥max(2,κ)`
with C1, K≥2, and `δ_t=2R`; the general bound adds neither an independent `R≥3` condition nor `k≤R`.
The shorter bound has the separate condition `k≤2R+1` from H.6-C.

**Proof.** The uses of round length in those proofs are exhaustive here.
At action `T_r+6Δ`, `⌊6/4⌋=1<R`, so the action still has round `r`
and reads the scheduled `fastWrite[rR]` after that gate. Its current-slot
HEADs were emitted at `T_r+5Δ` and arrive strictly before the action.
For every action a_r≥GST,

```text
a_r+Δ_F≤T_r+β_F≤T_(r+1).
```

Receipt is strict, so equality of the cutoff and proposal time is safe.
A required honest +κ carrier arrives before T_r+β_F+Δ<a_(r+1),
including κ=R. This is a transport fact. Height consumption uses W2;
finality consumption needs the kernel's window-retention proof.
For Δ_F≤2Δ, κ=2: the carrier is at T_r+8Δ and arrives before
T_r+9Δ. At R=2 it is the next opening, before the next action
T_r+14Δ. GateAfterCarrier2 remains the +2 clock fact; it is not a
+κ fact.

H.9(b) fixes starting action r's coverage. It is held before
T_r+β_F≤T_(r+1)<T_r+2P≤t_X. The selected source is at least two
slots before X, and W2 supplies the progress bits or the already-crossed
case. Its C,D constants stay unchanged. H.9-Q consumes the same fixed
coverage at a qualified opening r′≥r+2, not necessarily at +2.
A source selected at opening rR transfers from label rR+1; the next
opening's HEADs cover it before the renewal gate. R≥2 supplies the
parent-transfer distance when needed.

A source row needed at a slot-u proposal or HEAD has label at most
`u−2`, by the action offset, independently of `R` (H.12). The cut
uses `P≥8Δ`, so `2P>5Δ` and `3P−6Δ≥2P`. These inequalities prove
both the old-source cap and the synchronous reset origins, including all
labels of a large slow window (H.11 and H.15). Maturity after two rounds
is exactly `2R` slots, for every `R`, not an inequality requiring three
slots in a round (H.9). Finally `P≥8Δ>4Δ` places the high-source output
transfer before a possible honest finality action (H.18).

HG.1 uses the first opening label s≤q+R−1, so its action is within
P−4Δ of d_q. HG.2 fixes action r's coverage, held before T_r+β_F.
Its grid trigger gives X.slot≥rR+κ≥rR+2 and X.slot≥E.slot+2R.
HG.3 and HG.4 use ε≤P−8Δ≤P−4Δ for their max equalities. HG.5
sums nonnegative allowances and permits skipped phases. HG.6 keeps
the cut and both max branches. The first branch dominates exactly
when ρ̄+7Δ+ε≥P. No proof assumes this inequality for all R.

Everything else uses ancestry, quorum counts, slot-label induction,
`L=(4k−1)Δ`, or `θ=3Δ` (the optional Q proof retains `θ_Q=4Δ`). The phase and attempt counts are independent
of round size. This proves the extension.

DC paper lines 1209–1214 require the different inequality
`7−4R≤−5` to deliver an SG row before the next grade-2 early cutoff.
It fails at `R=2`. FG-SA has no such cutoff. H.3, H.6, and H.9 provide
its source and pivot facts from actual SA votes and gates instead.
Thus that failed DC inequality is not a gap in this proof. ∎

For Δ_F≤2Δ, at `k=2,L=7Δ,G=8Δ`, Γ=8Δ, ρΓ=30Δ, and ρ₁=25Δ.
The condition k≤2R+1 holds for both R values.

```text
┌───────────────────────────┬───────────────────────────────┬──────┬──────┐
│ Quantity                  │ Formula                       │ R=2  │ R=3  │
├───────────────────────────┼───────────────────────────────┼──────┼──────┤
│ Round                     │ P=4RΔ                         │ 8Δ   │ 12Δ  │
│ General repair            │ ρΓ=2L+Γ+8Δ                    │ 30Δ  │ 30Δ  │
│ Synchronous-window repair │ ρ₁=L+Γ+10Δ                    │ 25Δ  │ 25Δ  │
│ Gap to frontier service   │ E_g=ρ₁+2P+Γ−Δ                 │ 48Δ  │ 56Δ  │
│ Top J to frontier service │ E_j=max(ρ₁+P+Γ+3Δ,2P+Γ−4Δ)    │ 44Δ  │ 48Δ  │
│ Contest plus rise tail    │ B_c=ρ₁+2P+Γ−6Δ                │ 43Δ  │ 51Δ  │
│ Contest plus row tail     │ D_c=ρ₁+P−Δ                    │ 32Δ  │ 36Δ  │
│ One frontier rise         │ E_g+E_j+B_c                   │ 135Δ │ 155Δ │
│ Reset                     │ B'_reset=3P+2E_g+2E_j+B_c+D_c │ 283Δ │ 331Δ │
│ Local H′ after action     │ Γ+4Δ                          │ 12Δ  │ 12Δ  │
│ General healing           │ B_H^(2)                       │ 325Δ │ 373Δ │
│ Conditional healing       │ B_H^(1)=B_H                   │ 295Δ │ 343Δ │
└───────────────────────────┴───────────────────────────────┴──────┴──────┘
```

For κ>2 use the F forms in §1. At R=3, 2Δ<Δ_F≤6Δ, k=2,
G=8Δ, they give:

```text
┌───────────────────┬──────────┐
│ Quantity          │ R=3, κ=3 │
├───────────────────┼──────────┤
│ E_g^F, E_j^F      │ 56Δ, 52Δ │
│ B_c^F, D_c^F      │ 51Δ, 36Δ │
│ One frontier rise │ 159Δ     │
│ B_reset^F(ρ₁)     │ 339Δ     │
│ Local tail        │ 12Δ      │
│ B_H,F^(2)         │ 381Δ     │
│ B_H,F^(1)=B_H^F   │ 351Δ     │
│ B_H^ph,F          │ 324Δ     │
│ B_H^8a,F          │ 252Δ     │
└───────────────────┴──────────┘
```

H′ does not pay another repair after reset. The uniform proof permits
up to six repair charges before reset. HG.1 removes later charges at a
served frontier. The old local allowance δ_H=2L+G−2Δ is
still valid, since Γ<G+4Δ and
Γ+4Δ<G+8Δ≤2L+G−2Δ using L≥7Δ.

For Δ_F≤2Δ, the retained healing and finality values are

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

For κ>2 the proved healing and receipt-ready forward forms are

```text
B_H^F: §1 and H-time; B_best^F(g_h)=min(B_heal(g_h),B_H^F).
W_W(g_f)=(g_f+2)P+β_F+Δ.
B_F^W(g_f)=B_H^F+W_W(g_f).
Premise for W_W and B_F^W: Rec_FE_W(g_f) or Rec_F4_W(g_f).
```

The forward kernel needs 22's two-entry retention argument and its
target-carrier upper endpoint. No large-delay strong, QF2, skip, or HP
bound follows by changing only B_H. These families need separate ports.
For Δ_F≤2Δ, the old finality families below retain their cited proof
scope; this chapter adds no independent window proof for them.

B_best requires qualified search. Without it, use B_H for healing
when Δ_F≤2Δ, and B_H^F for κ>2.
With both finality premises, take the smaller local deadline. The
optional qualified healing bound remains valid; it is larger than
B_H at the reference values below for every g_h≥1. For other parameters,
take the minimum only over bounds whose premises hold.
For integer time the strict healing gate gives an upper deadline one
tick earlier. Under FF5 the two strict inequalities give a GST first-
finality deadline `B_F(g_f)−2` ticks. These savings are ticks, not Δ.

For Δ_F≤2Δ, at `k=2,G=8Δ`, values below are in units of Δ. G≤P holds at both R.
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

For Δ_F≤2Δ at `δ_t=2R`, every strong round r gives FGoodE(r−2): its opening
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

Replacement N.1 has an unqualified round 5 (faulty slot 17), although
q₀≤2; its local delay is G+5Δ. N.2 gives healing 38/46/54/62 Δ and
first finality 48/64/68/80 Δ (WEAKER), with least Rec_FE parameters
2/8/2/5. Its G=8Δ traces have faulty slots after the point where Rec_c(3)
would force all slots honest. Replacement N.3 uses R=20,G=12Δ and
waits 88 ticks after settlement. The old larger N.2 bounds remain
OPEN (not established, not refuted).

The recovery results above are **PROVED-paper**. The fixed starting
batch and W2 close the HG.2 and H.9(b) gaps accepted by both reviews.
H.9-Q closes the statement and consumption gap. The full H.21 update
closes Astra V5 H.21 and Opus F1; the post-GST guard closes Opus F4.
The scoped values and recurrence text close Opus F6–F8.

## 10. Exact negative executions and slack

Window check: the second Opus report replays the listed events of N.1,
N.2, HG.N1, HG.N2, and N.3 with R6-window, R7, and send-once. It finds
no failed step and recomputes N.2's 38/46/54/62 Δ healing endpoints
and 48/64/68/80 Δ first-finality endpoints. These paper endpoints are
PROVED for the window: R=2 requires Δ_F≤2Δ; R=3 requires Δ_F≤6Δ,
so the R=3 runs also hold at κ=3. The full HEAD/gate/lease state of every
prefix label was not checked. Upper values at κ=2 use Δ_F≤2Δ; for
κ>2 use §§1,5,8–9. No Lean run certificate is claimed.

Historical check basis: spec de183d7d; the window check is stated above. Rows use `T_i(h,X;f)` for targets and
`O_i(h,X;f)` for timeouts; `f=—` is an empty finality pair. Each Q is
a set of distinct signed rows. These abbreviations have no round field.
After each finite Recovery prefix, use honest proposers, keep all honest
identities awake, deliver within the stated delay, and disclose no further
private evidence.

### N.1 — Healing at q_(s*) (`fj.healedAtQ.v1`) — REPLACED

**PROVED-paper; REPLACED.**
**historical (pre-no-round rules).** The old runs are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §10.

R7 advances both W children to height 2. The decisive HEADs and outputs
remain as stated below.

Set:

```text
Δ=16, n=7, a=2, q_F=5, τ=4,
k=13, L=816, R=3, G=128, GST=192.
```

Use honest groups `A={a1,a2,a3}` and `B={b1,b2}`, and faulty identities `z1,z2`.

Slots 1 and 2 are faulty. Use distinct roots
`g=0,G1=101,W=20,C_s=100+s,Wb_s=100+s,P18=118`. There are no C15
or C16 blocks, so these roots are injective. Use
`t_s=64s,v_s=64s+16,q_s=64s+80,d_s=64s+96` and `δ_t=6`.

All honest nodes tick at every public time. They sleep through label 0.
All are awake at slot-1 vote 80; deliver G1 at 68 and their five G1 votes
at 84. At label 2 only b1,b2 among the honest are awake. Deliver W to
those two at 132; at 144 they vote W, and z1,z2 also sign W votes.
Deliver those four votes to b1,b2 at 148. Hold W and these four votes
from a1–a3 until 193. No other pre-GST base messages are delivered.
At GST all honest nodes become awake. All subsequent honest objects,
and the faulty label-15 votes specified below, arrive four ticks after
emission. All required dependencies arrive first. Every object accepted
before GST but still missing elsewhere arrives at 193, before
`GST+Δ=208`. Thus receipt relay and strict delivery hold.

Slots 3–14 have an a-group proposer; choose `a_(1+(s mod 3))`.
Slot 15 has proposer b1; slot 16 has proposer b2; slot 17 is faulty
and silent; slot 18 has proposer a1. From slot 19 all proposers are
honest. This satisfies every strict G trigger: the largest honest-proposal
gap is 128. Rounds 1–4 and every round from 6 onward have qualified
openings, so Rec_s(3) holds. The one awake predicate is respected.

#### N.1.1 Blocks, rows, and parent states

```text
┌────────────┬─────────┬─────────────┬──────────────────────┬───────────┐
│ Block      │ Parent  │ Parent pair │ Carried rows         │ Post pair │
├────────────┼─────────┼─────────────┼──────────────────────┼───────────┤
│ G1, slot 1 │ g       │ (1,g)       │ None                 │ (1,g)     │
│ W, slot 2  │ G1      │ (1,g)       │ None                 │ (1,g)     │
│ C3,C4      │ G1,C3   │ (1,g)       │ None                 │ (1,g)     │
│ C5         │ C4      │ (1,g)       │ Three A targets      │ (1,g)     │
│ C6–C10     │ Prior C │ (1,g)       │ None; rows inherited │ (1,g)     │
│ C11        │ C10     │ (1,g)       │ Two faulty targets   │ (2,C11)   │
│ C12–C14    │ Prior C │ (2,C11)     │ None                 │ (2,C11)   │
│ Wb15       │ W       │ (1,g)       │ All five targets     │ (2,Wb15)  │
│ Wb16       │ W       │ (1,g)       │ All five targets     │ (2,Wb16)  │
│ P18        │ C13     │ (2,C11)     │ Five honest targets  │ (3,P18)   │
│ C19        │ P18     │ (3,P18)     │ None                 │ (3,P18)   │
└────────────┴─────────┴─────────────┴──────────────────────┴───────────┘
```

The height-1 targets have empty finality pairs. The height-2 targets have finality pair `(1,g)`.

The complete `sent` records through action 6 are:

```text
┌────────────┬──────┬────────────────────┐
│ Identities │ Time │ New row            │
├────────────┼──────┼────────────────────┤
│ A, each    │ 288  │ T_i(1,g;—)         │
│ z1,z2      │ 672  │ T_i(1,g;—)         │
│ All honest │ 1056 │ T_i(2,C11;(1,g))   │
│ All honest │ 1248 │ T_i(3,P18;(2,C11)) │
└────────────┴──────┴────────────────────┘
```

A’s repeated height-1 candidates are suppressed. Before 1056, B has no height pair because its gates are vetoed. There are no timeout rows.

`C11,Wb15,Wb16` justify genesis and have `(h_F,F)=(0,g)`. `P18` first finalizes genesis, then justifies `C11`; its state is `(3,P18;2,C11;1,g)`. No non-genesis finalization occurs in the prefix.

#### N.1.2 Decisive events

```text
┌──────┬──────────────────────────────────────────────────────────────┐
│ Time │ Event and state                                              │
├──────┼──────────────────────────────────────────────────────────────┤
│ 160  │ Gate 1: p=D=5; S=G1 everywhere; G1 lease ends at 976.        │
│ 192  │ C3 has parent G1; its proposer has not received W.           │
│ 193  │ A receives W and its four slot-2 votes, after freeze 176.    │
│ 208  │ HEAD 3: A→C3; B→W from four frozen votes. No W lease yet.    │
│ 224  │ Gate 2: B writes W to deadline 1040; A has no early support. │
│ 272  │ Only three C3 votes conflict with W; 3<τ=4. No release.      │
│ 288  │ Gate 3: C3 has p=3,D=5; A sets S=C3; B vetoes on W.          │
│ 4–14 │ HEADs: A→C_s, B→W. C_s has p=3,D=5; faulty seats silent.     │
└──────┴──────────────────────────────────────────────────────────────┘
```

```text
┌──────┬────────────────────────────────────────────────────────────────┐
│ Time │ Event                                                          │
├──────┼────────────────────────────────────────────────────────────────┤
│ 672  │ Inclusive cut u₀: M=1. Faulty height-1 rows are emitted.       │
│ 704  │ C11 consumes the inherited three targets plus two new targets. │
│ 960  │ Wb15 is proposed on W and reaches height 2.                    │
│ 976  │ A votes C14; B votes Wb15; faulty seats vote C13.              │
│ 992  │ A has S=C14; B still has S=W.                                  │
│ 1024 │ Wb16 is proposed on W and reaches height 2.                    │
│ 1040 │ W expires. Every HEAD is C13. This is q_(s*).                  │
│ 1056 │ Gate/action 5: A keeps C14; B advances to C13; all target C11. │
│ 1152 │ P18 is proposed on C13 and reaches height 3.                   │
│ 1168 │ Every HEAD is P18.                                             │
│ 1248 │ Gate 18 changes A's output from C14 to its sibling P18.        │
└──────┴────────────────────────────────────────────────────────────────┘
```

At expiry 1040, both B-group leases, W and the renewed G1 prefix,
expire. Honest proposals include their previous-slot raw vote pool, its
resolved subset, and all rows required by R7.

The frame and walk checks are:

- The frame is `H=2,J=g,lo=1` after either W child.
- At proposal 16, Wb15 has only two of seven previous-slot supporters. It is old, and its parent has height equal to the floor. It is ineligible. Thus Wb16 still has parent `W`.
- At HEAD 16, C13 has five of seven supporters; C14 has only three. The walk stops at C13.
- C14 has no lease: its support is below `τ`, and its thirteen-result slow window is absent.

The reset is:

```text
r_G=1, u₀=672, M=1, r*=5, s*=15, C*=C13.
q_(s*)=1040.
1248 = q_(s*)+G+5Δ.
```

Therefore `HEALED(q_(s*))` is false. The local delay is `G+5Δ=208` ticks.
At 1040 the outputs C14 and W conflict. The gate at 1248 also breaks
suffix monotonicity for every proposed start in `[1040,1248)`. H′ gives
healing from 1248, so no smaller all-parameter local constant works in
this family. This is not a tightness claim for `k=2`.

### N.2 — Four uniform lower bounds — WEAKER

**PROVED-paper; WEAKER.**
**historical (pre-no-round rules).** The old runs are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §10.

R7 advances the first honest child of `W3` to height 4 after the `K4`
reveal. There is no `D4`. One late reorganization gives the bounds below.

#### N.2.1 Parameters and block states

Use `n=4`, honest identities `u,v,w`, faulty identity `z`, `q_F=3`,
`τ=2`, `k=2`, `L=7Δ`, `δ_t=2R`, and any integer `Δ≥1`. Times in
N.2 are in units of Δ; set `GST=96Δ`.

All pre-GST proposers are faulty. Honest identities are awake only for the listed source HEADs and actions. From GST, all are awake. Public messages arrive everywhere at emission, after the tick. Private `K4` has no honest receipt before its reveal.

```text
┌───────┬──────────────┬────────┬─────────────┬──────────────┬───────────┐
│ Block │ Slot R=2/R=3 │ Parent │ Parent pair │ Carried rows │ Post pair │
├───────┼──────────────┼────────┼─────────────┼──────────────┼───────────┤
│ E1    │ 2 / 3        │ g      │ (1,g)       │ None         │ (1,g)     │
│ A2    │ 6 / 6        │ g      │ (1,g)       │ Q_E          │ (2,A2)    │
│ B2    │ 10 / 9       │ g      │ (1,g)       │ Q_E          │ (2,B2)    │
│ W3    │ 14 / 15      │ B2     │ (2,B2)      │ Q_B          │ (3,W3)    │
│ V3    │ 18 / 18      │ B2     │ (2,B2)      │ Q_B          │ (3,V3)    │
│ K4    │ 16 / 17      │ W3     │ (3,W3)      │ Q_W          │ (4,K4)    │
│ C2    │ 24 / 24      │ g      │ (1,g)       │ Q_E          │ (2,C2)    │
└───────┴──────────────┴────────┴─────────────┴──────────────┴───────────┘
```

#### N.2.2 Actual pre-GST sources and rows

For each `i∈{u,v,w}`, the complete pre-GST `sent` sequence is:

```text
┌────────┬──────────────────┬───────────────┐
│ Source │ New row          │ Batch name    │
├────────┼──────────────────┼───────────────┤
│ E1     │ T_i(1,g; —)      │ Q_E           │
│ A2     │ T_i(2,A2; (1,g)) │ Q_A, not used │
│ B2     │ O_i(2,B2; (1,g)) │ Q_B           │
│ W3     │ T_i(3,W3; —)     │ Q_W           │
│ V3     │ O_i(3,V3; —)     │ Q_V, not used │
└────────┴──────────────────┴───────────────┘
```

The timeout rows name entries different from the earlier target entries. Thus send-once permits them.

`A2` and `B2` have `(j,J;h_F,F)=(1,g;0,g)`. `W3` and `V3` have `(1,g;1,g)`: their carried `Q_B` rows finalize genesis before the mature timeout crossing. `K4` has `(3,W3;1,g)`. No non-genesis entry is finalized.

Under RD2, the digest is any function injective on the run scope; the
execution fixes one such function with this root order:

```text
g < E1 < A2 < B2 < W3 < V3 < C2 < K4 < all P_s.
```

All five blocks are public at their proposal time. Their vote times
are `4s+1`, gates and actions `4s+6`, and fast-lease deadlines `4s+13`.
Consecutive active labels differ by at least three slots. Thus the
previous leases have expired by the next vote, including equality.
There are no intervening honest votes. A2 and B2 are current eligible
children of g. At the later height-3 votes, the floor is 2; the root
order picks B2 over A2 below the band, and the current child W3 or V3
is eligible. The old sibling at height 3 has no support and is not
current. All three HEADs equal the stated block.

Each gate has `p=D=3`, so it writes the exact block and every
non-genesis prefix. E1's target quorum gives both A2 and B2 height 2.
B2's timeout quorum gives W3 and V3 height 3, because their slots are
at least `B2.slot+2R`. A2's target batch is never folded into a public
block. The allowed finality pairs on the early rows can finalize only
genesis. They create no lock at heights 2 or 3.

At GST, the state before C2's receipt is therefore

```text
H=3; j=1; J=F=g; root g; floor 2; S=V3; no live leases;
target[2]=A2; timeout[2]=true;
target[3]=W3; timeout[3]=true;
no lock at height 2 or 3.
```

#### N.2.3 Recovery schedule

All slots from 25 onward are honest, except:

```text
┌──────────┬─────────────────────┐
│ Case     │ Silent faulty slots │
├──────────┼─────────────────────┤
│ G=4Δ     │ None                │
│ R=2,G=8Δ │ 28,33,36            │
│ R=3,G=8Δ │ 26,30,32,37,41      │
└──────────┴─────────────────────┘
```

At action time `102Δ`, every honest identity sends `O_i(2,C2;(1,g))`.

#### N.2.4 Event times and R7 states

Let `A` be the first height-3 entry on the `C2` branch, `E` the first honest child of `W3`, `B` the block that consumes the height-4 target quorum, and `C` the first finality carrier.

```text
┌────────────────────────────┬───────┬───────┬───────┬───────┐
│ Event or block             │ R2,G4 │ R2,G8 │ R3,G4 │ R3,G8 │
├────────────────────────────┼───────┼───────┼───────┼───────┤
│ First C2-row carrier       │ P26   │ P26   │ P26   │ P27   │
│ A: first height-3 entry    │ P28   │ P29   │ P30   │ P31   │
│ O_i(3,A;—) action          │ 118   │ 126   │ 126   │ 138   │
│ First carrier of that row  │ P30   │ P32   │ P32   │ P35   │
│ K4 reveal                  │ 127   │ 135   │ 143   │ 151   │
│ E: first W3 child          │ P32   │ P34   │ P36   │ P38   │
│ Gate of E                  │ 134   │ 142   │ 150   │ 158   │
│ T_i(4,E;—) action          │ 134   │ 142   │ 150   │ 162   │
│ B: height-4 target carrier │ P34   │ P37   │ P38   │ P42   │
│ T_i(5,B;(4,E)) action      │ 142   │ 158   │ 162   │ 174   │
│ C: first finality carrier  │ P36   │ P40   │ P41   │ P44   │
│ First finality time        │ 144   │ 160   │ 164   │ 176   │
└────────────────────────────┴───────┴───────┴───────┴───────┘
```

The following rules specify the parent post-state and row selection for **every honest proposal in these prefixes**:

1. Before `A`, each proposal extends the last selected `C2` descendant. Its parent pair is `(2,C2)`. The first listed carrier includes the three `C2` timeout rows. Later proposals exclude those exact rows because they are already on the chain. The inherited progress quorum crosses at `A`, when maturity permits it.
2. From `A` until the reveal, each parent pair is `(3,A)`. The first listed carrier includes the three `O_i(3,A;—)` rows. Later proposals inherit their progress bits. The reveal occurs before the next honest proposal can consume that quorum at maturity.
3. `E` has parent `W3`, whose post-state pair is `(3,W3)`. **R7 includes all three old `Q_W` targets.** Thus `E` has pair `(4,E)` and justification `(3,W3)`.
4. Descendants of `E` have parent pair `(4,E)` until `B`. Only the three new height-4 targets match. `B` includes them and becomes `(5,B)`, with justification `(4,E)`.
5. Descendants of `B` have parent pair `(5,B)` until `C`. `C` includes the three height-5 rows, first finalizes `E`, then justifies `B` and advances to `(6,C)`.

These are all the post-GST additions to each honest identity’s `sent` record through first finality. Other actions either have no source or attempt an already recorded height/entry and send nothing. `z` sends no FG row.

#### N.2.5 Frame change and healing lower bounds — WEAKER

At the reveal, `K4` gives an uncontested top justification `W3`. It excludes the `C2` branch. The unsupported old child `K4` is ineligible at parent height 3 and floor 3. The next honest proposal therefore has parent `W3`.

The height advance in `E` does not prevent its HEAD votes or its gate. The three new votes release the conflicting old leases. At the gate of `E`, the output changes from the `C2` branch to the conflicting `W3` branch.

Thus no healing start before those gates works:

```text
Healing lower bounds:       38Δ, 46Δ, 54Δ, 62Δ.
```

The bounds are in order `(R,G/Δ)=(2,4),(2,8),(3,4),(3,8)`.
For the old 46/58/62/78 healing coefficients, the old larger bound remains OPEN (not established, not refuted).

#### N.2.6 First finality and recurrence — WEAKER

The first-finality lower bounds are `48Δ,64Δ,68Δ,80Δ` in the same order.
For the old 56/72/80/92 coefficients, the old larger bound remains OPEN (not established, not refuted).
These bounds come from the rows and carriers in N.2.4, rather than an
addition of a positive finality tail to a healing lower bound.

Rule checks:

- Every carried height pair equals its parent’s post-state pair.
- R7 carries the old targets into `E`; it does not omit them.
- No renewed timeout for `(3,W3)` is sent.
- `timeout[3]` blocks finality for `W3`.
- The first non-genesis finality pair is `(4,E)`, carried on a new height-5 row.
- Every nonempty finality pair satisfies `h>h_f`.
- There is no finality-only row.

The schedules have least `Rec_FE` parameters `2,8,2,5`. Thus the
R=2,G=8Δ finality value needs `Rec_FE(8)`. Chapter 22 B1 supplies a
variant for a common `Rec_FE(5)` comparison. The G=8Δ traces do not
satisfy Rec_c(3), which would force all later proposers honest.

#### N.2.7 G=8Δ witnesses and their limits — WEAKER

N.2.5 gives the current-rule healing bounds `46Δ` and `62Δ` at G=8Δ.
They exceed HG.N2’s `45Δ−1 tick` and `61Δ−1 tick` for every integer Δ≥1.
N.2 is the source of all four spec lower endpoints `38/46/54/62 Δ`.
For the old spec values 46/74/62/90 and the old stronger 89/105 coefficients,
the old larger bound remains OPEN (not established, not refuted).
HG.N1–HG.N2 give the separate five-change claim and the weaker bounds below.

#### HG.N1 — Reachable prefix and private evidence — REPLACED

**PROVED-paper; REPLACED.**
**historical (pre-no-round rules).** The old runs are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §10.

N.3 uses this same prefix, with its own R and GST.

Use honest identities `U={0,1}`, `V={2,3,4}`, and faulty identities `z=5,z′=6`. Thus `q_F=5` and `τ=4`.

All pre-GST proposers are faulty. At each listed source opening, all five honest identities are awake for its HEAD and action. They sleep at other pre-GST duties. Public objects arrive everywhere at emission, after the tick.

Define the honest batches:

```text
┌────────┬────────────────────────┐
│ Action │ Row from each honest i │
├────────┼────────────────────────┤
│ 1      │ T_i(1,g;—)             │
│ 4      │ T_i(2,A2;(1,g))        │
│ 7      │ O_i(2,B2;(1,g))        │
│ 10     │ T_i(3,J3;—)            │
│ 13     │ O_i(3,V3;—)            │
│ 16     │ No send                │
│ 19     │ T_i(4,E4;—)            │
│ 22     │ O_i(4,V4;—)            │
│ 25     │ No send                │
└────────┴────────────────────────┘
```

Call each emitted five-row batch `Q_r`. Each honest `sent` record contains exactly these seven rows at the end of the prefix.

Each faulty identity sends exactly these two FG rows:

```text
O_z(3,J3;—),  O_z(4,E4;—)
```

and likewise for `z′`. Send the first pair at `(40R+8)Δ` and the second pair at `(76R+8)Δ`.

Define:

```text
M3 = the three V-identity rows from Q_10
     plus the two faulty O(3,J3;—) rows.

M4 = the three V-identity rows from Q_19
     plus the two faulty O(4,E4;—) rows.
```

Each mixed batch has five progress identities but only three target identities.

```text
┌───────┬───────┬────────┬─────────────┬──────┬───────────┬─────────┐
│ Block │ Slot  │ Parent │ Parent pair │ Rows │ Post pair │ Post J  │
├───────┼───────┼────────┼─────────────┼──────┼───────────┼─────────┤
│ E1    │ R     │ g      │ (1,g)       │ None │ (1,g)     │ g, h=0  │
│ A2    │ 4R    │ g      │ (1,g)       │ Q_1  │ (2,A2)    │ g, h=1  │
│ B2    │ 7R    │ g      │ (1,g)       │ Q_1  │ (2,B2)    │ g, h=1  │
│ J3    │ 10R   │ B2     │ (2,B2)      │ Q_7  │ (3,J3)    │ g, h=1  │
│ V3    │ 13R   │ B2     │ (2,B2)      │ Q_7  │ (3,V3)    │ g, h=1  │
│ U3    │ 16R   │ J3     │ (3,J3)      │ None │ (3,J3)    │ g, h=1  │
│ E4    │ 19R   │ J3     │ (3,J3)      │ M3   │ (4,E4)    │ g, h=1  │
│ V4    │ 22R   │ J3     │ (3,J3)      │ M3   │ (4,V4)    │ g, h=1  │
│ U4    │ 25R   │ E4     │ (4,E4)      │ None │ (4,E4)    │ g, h=1  │
├───────┼───────┼────────┼─────────────┼──────┼───────────┼─────────┤
│ K4    │ 10R+2 │ J3     │ (3,J3)      │ Q_10 │ (4,K4)    │ J3, h=3 │
│ D4    │ 15R   │ V3     │ (3,V3)      │ Q_13 │ (4,D4)    │ g, h=1  │
│ K5    │ 19R+2 │ E4     │ (4,E4)      │ Q_19 │ (5,K5)    │ E4, h=4 │
│ D5    │ 24R   │ V4     │ (4,V4)      │ Q_22 │ (5,D5)    │ g, h=1  │
│ T5    │ 25R+2 │ E4     │ (4,E4)      │ M4   │ (5,T5)    │ g, h=1  │
└───────┴───────┴────────┴─────────────┴──────┴───────────┴─────────┘
```

The bottom five blocks are private. N.3 discloses only `K4` and `K5`.

All states from `J3` onward have `(h_F,F)=(1,g)`. The earlier `A2,B2` states have `(0,g)`.

Under RD2, the digest is any function injective on the run scope; the
execution fixes one such function with distinct roots in this order:

```text
g < E1 < A2 < B2 < J3 < V3 < U3 < E4 < V4 < U4
  < C3 < K4 < D4 < T5 < K5 < D5 < all P_s.
```

Each continuation sets k, L, Δ, and R; use `δ_t=2R`. Emit each block
at its slot time. Each listed source HEAD is at `(4s+1)Δ`, its gate
and action at `(4s+6)Δ`, and its fast-lease deadline at `(4s+6)Δ+L`.
The previous leases expire before the next source opening.
Before slots `16R,19R,22R`, `z` supplies one previous-slot steering
vote for `J3`; before `25R`, it supplies one for `E4`. These votes reach
the frozen pool and select the required path. They do not create a fast
lease. The preceding empty result prevents a slow lease. Each selected
opening then has five honest early votes and an exact fast source.

**R6 and send-once check.** Every row in the table matches its parent pair. `M3` and `M4` cross by mature progress, without a target quorum. The faulty proposer can select these subsets; R7 applies to honest proposals. At actions 16 and 25, the candidate timeout names an earlier target entry. `sent` suppresses it. Neither nonexistent batch is used.

The honest pre-GST maximum source height is `μ=4`. Both private evidence
frontiers are reachable. All public height-4 blocks extend J3; all nonempty
pre-GST finality pairs are `(1,g)` on height-2 rows.

#### HG.N2 — Schedule, stamps, and the two lower bounds — WEAKER

**PROVED-paper; WEAKER.** Five changes remain reachable.
**historical (pre-no-round rules).** The old runs are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §10.

Use the HG.N1 prefix, `k=2`, `L=7Δ`, `δ_t=2R`, `G=8Δ`, any
integer `Δ≥1`, and:

```text
s₀=40R.
GST=(4s₀−3)Δ+1 tick.
```

At slot `s₀`, publish `C3`, a child of `B2` carrying `Q_7`. Its parent pair is `(2,B2)` and its post pair is `(3,C3)`.

Keep these silent faulty slots:

```text
R=2: 82,84,88,92,96,99.
R=3: 123,126,130,138,140,143.
```

All other slots after `s₀` are honest. There is no `N4`.

All honest identities remain awake from GST. The slot-(s₀−1) HEAD is
before GST and has no honest vote. At R=2, action 39 at 318Δ has an
empty fastWrite[78] and sends nothing; at R=3, no extra action is between
GST and C3's receipt. Before C3, all stores have H=4,j=1,J=F=g, S=U4,
and no live lease. C3 is current and wins the root comparison below the
floor, so its HEADs and gate select it.

All public receipts are at emission after the tick. At a common reveal time, process the listed blocks in order.

```text
┌───────────────────────────┬──────────┬───────────┐
│ Event                     │ R=2, /Δ  │ R=3, /Δ   │
├───────────────────────────┼──────────┼───────────┤
│ C3 published              │ 320      │ 480       │
│ O_i(3,C3;—) action        │ 326      │ 486       │
│ K4: top J3 at H=4         │ 339      │ 507       │
│ A: first honest J3 child  │ P85, 340 │ P127, 508 │
│ First late reorganization │ 346      │ 514       │
│ O_i(4,A;—) action         │ 350      │ 522       │
│ D4: contest at H=4        │ 355      │ 523       │
│ T5: rise to H=5, gap      │ 355      │ 531       │
│ K5: top E4 at H=5         │ 355      │ 531       │
│ E: first honest E4 child  │ P89, 356 │ P133, 532 │
│ Last reorganization       │ 362      │ 538       │
│ D5: contest at H=5        │ 363      │ 543       │
│ First honest height-5 row │ 366      │ 546       │
└───────────────────────────┴──────────┴───────────┘
```

**Parent states, R7, and `sent`.**

- Before `A`, every honest parent has pair `(3,C3)`. `P83` at R=2, or `P122` at R=3, first carries the five C3 timeouts. Later proposals inherit those progress bits. `K4` arrives before a mature honest crossing.
- `A` has parent `J3`, pair `(3,J3)`. R7 includes all five `Q_10` targets and the two faulty matching timeouts. It becomes `(4,A)`, with justification `J3`.
- Later proposals on that branch have parent pair `(4,A)`. At R=2, no honest proposal carries the new A timeouts before the next root change. At R=3, `P131` carries them and `P132` inherits them; neither is mature.
- `E` has parent `E4`, pair `(4,E4)`. R7 includes all five `Q_19` targets and the two faulty matching timeouts. It becomes `(5,E)`, with justification `E4`.
- Through the first height-5 action, later honest proposals extend E’s chain, have parent pair `(5,E)`, and carry no rows.

Each honest identity adds exactly these rows through that action:

```text
O_i(3,C3;—), O_i(4,A;—), T_i(5,E;—).
```

All name new permitted height/entry combinations. The permanent timeout flags at heights 3 and 4 block finality for `J3` and `E4`. Every finality pair in this part is empty.

The five frame changes are:

```text
H=4 gap → H=4 top J3 → H=4 contest
        → H=5 gap → H=5 top E4 → H=5 contest.
```

All five precede the first honest height-5 row. At R=2, all five are after `u₀=334Δ`. At R=3, four are after `u₀=510Δ`.

The two root changes cause the two late reorganizations. The contests do not remove the new honest branches, because those branches already have the required heights.

Hence the replacement lower bounds are:

```text
R=2: 362Δ−(317Δ+1 tick) = 45Δ−1 tick.
R=3: 538Δ−(477Δ+1 tick) = 61Δ−1 tick.
```

These hold for every integer `Δ≥1`. For the old 77/93 and 89/105
coefficients, the old larger bound remains OPEN (not established, not refuted).
Five frame changes do not establish five complete repair waits. N.2.5
gives the larger current-rule G=8Δ lower bounds, `46Δ` and `62Δ`.

### N.3 — A later lease-expiry wait — REPLACED

**PROVED-paper; REPLACED.** Full lease lifetime L; 88 ticks after settlement
in the displayed instance, and `L−24 ticks` in N.3.4.
**historical (pre-no-round rules).** The old runs are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §10.

#### N.3.1 Parameters and honest continuation

Use the HG.N1 prefix with R=20.

Set:

```text
Δ=16, k=2, L=112, R=20, δ_t=40, G=192.
GST=t_561=35904.
α=562, A=P562.
w=601, Q=P600, T=t_601=38464.
```

Slot 561 and every unlisted slot before 562 are faulty and silent.
Disclose `K4` everywhere at GST. K4 sets the root to J3. J3’s children
have no votes and are not below the floor. Thus the slot-561 HEAD is J3,
and P562 has parent J3. All honest identities remain awake thereafter. All proposal slots from 562 onward are honest except 601 and 602. Assign honest proposals to identity 2.

Ordinary honest messages arrive eight ticks after emission.

The complete honest row additions through the attack are:

- Action 28: no row; its opening has no honest HEAD votes and no fresh source.
- Action 29, at `37216`: each honest identity sends `O_i(4,A;—)`.
- Action 30, at `T+32`: the same candidate is suppressed by `sent`.
- No later FG action occurs before the displayed recovery.

Finality for `J3` is blocked by `timeout[3]`. All these height-4 timeout rows have empty finality pairs.

```text
┌───────────────────┬─────────────┬───────────────────┬───────────────────┐
│ Block or range    │ Parent pair │ R7 rows           │ Post-state        │
├───────────────────┼─────────────┼───────────────────┼───────────────────┤
│ A=P562, parent J3 │ (3,J3)      │ Q_10 plus the two │ (4,A), j=3,J=J3   │
│                   │             │ faulty timeouts   │                   │
│ P563–P581         │ (4,A)       │ None              │ (4,A)             │
│ P582              │ (4,A)       │ Five O_i(4,A;—)   │ (4,A), progress=5 │
│ P583–P600         │ (4,A)       │ None; inherited   │ (4,A), progress=5 │
│                   │             │ exact rows        │                   │
│ K, slot 601       │ (4,A)       │ None; faulty      │ (4,A), progress=5 │
│ B, slot 602, Q    │ (4,A)       │ None; faulty      │ (5,B), j=3,J=J3   │
│ W, slot 602, K    │ (4,A)       │ None; faulty      │ (5,W), j=3,J=J3   │
│ P603, parent B    │ (5,B)       │ None              │ (5,B)             │
│ P604,P605         │ (5,B)       │ None              │ (5,B)             │
└───────────────────┴─────────────┴───────────────────┴───────────────────┘
```

Here `B`’s parent is `Q`, and `W`’s parent is `K`. Every ordinary proposal extends the previous selected proposal.

`A.slot+δ_t=562+40=602`. Thus `K` does not advance, but both `B` and `W` consume the **inherited** progress quorum at maturity. Their row lists are empty and pass R6.

An original H.6 repair occurs at `d_566=36320`: all nodes have exact result `P566` and a fresh fast write. The phase remains unchanged until the later attack.

#### N.3.2 Faulty slots and exact receipt times

The two faulty seats sign one slot-601 vote each for `K`. They do not equivocate and send no later HEAD votes.

```text
┌──────────┬─────────────────────────────────────────────────────────────┐
│ T offset │ Event                                                       │
├──────────┼─────────────────────────────────────────────────────────────┤
│ +12      │ U receives K.                                               │
│ +16      │ HEAD 601: U→K; V→Q.                                         │
│ +20      │ V receives K.                                               │
│ +24      │ All honest votes arrive everywhere; faulty K votes reach U. │
│ +32      │ Gate 600 writes Q everywhere. Action 30 sends nothing.      │
│ +36      │ Faulty K votes reach V; stamp equals the early cutoff.      │
│ +72      │ V receives K5, then B: H=5, top E4, then contest, floor 5.  │
│ +80      │ HEAD 602: U→K; V→B.                                         │
│ +84      │ U receives K5, then B.                                      │
│ +88      │ Everyone receives W and the five slot-602 honest votes.     │
│ +96      │ Gate 601: U writes K; V writes Q. K deadline is T+208.      │
│ +120     │ Three Δ after the first new-frame receipt.                  │
│ +128     │ Honest P603 extends B.                                      │
│ +144     │ Release count against K is 3<4. HEAD: U→W; V→P603.          │
│ +160     │ Gate 602 has result B. U's K lease vetoes it; V sets S=B.   │
│ +192     │ Honest P604 extends P603.                                   │
│ +208     │ K expires before release and HEAD. All HEADs select P604.   │
│ +224     │ Gate 603 sets S=P603 everywhere; B gets its slow lease.     │
│ +288     │ Gate 604 gives exact fresh fast P604 everywhere.            │
└──────────┴─────────────────────────────────────────────────────────────┘
```

#### N.3.3 Walks, guards, and expiry

At `T+72`, `B` is off `E4`, so its height-5 state creates the contest. `Q` remains viable through `B`. `K` has no height-5 witness in the V view until `W` arrives. This gives the required split HEADs at `T+80`.

At gate 601:

- U has four early `K` supporters out of seven late participants: `8>7`, and `4=τ`.
- V has only two early `K` supporters. Its genuine result is `Q`.
- Both guards pass.

After `W` arrives, `K` is viable again. U therefore keeps its live `K` start. V starts at `Q` and chooses the B branch by score `3>2`.

The next batches have only three votes conflicting with `K`. No release removes it. No finality change occurs. Its deadline remains:

```text
d_601+L = T+96+112 = T+208 = 38672.
```

The lease is written after the first contest receipt and survives its full lifetime. At `T+160`, the honest outputs `K` and `B` conflict. The wait from the three-Δ settlement point to expiry is **88 ticks**.

All relay delays are strict: ordinary honest delay is 8; the longest exceptional relay delay is 12; both are below `Δ=16`.

#### N.3.4 Parameter family and limits

For every integer `k≥2`, use:

```text
R=8k+4, Δ=16, G=12Δ,
α=28R+2, GST=t_(α−1), w=30R+1, T=t_w.
```

The first height-4 timeout batch is still at action 29. Its first carrier is `P_(29R+2)`. Maturity is exactly `α+2R=w+1`. Action 30 repeats the same entry and is suppressed.

The lease expires at:

```text
T+(4k+5)Δ = d_w+L.
```

The post-settlement wait is `L−24 ticks`. The slot and maturity equations give the family.

This refutes persistence after an earlier post-GST H.6 repair. It does not prove that each later repair needs a separate additive `L` charge. Here `R` grows with `k`. Also, `u₀=a_30=T+32`; the earlier repair is before that cut, and the obstruction is before the first completed repair in the search from that cut.

#### Uniform intervals at k=2 — window-checked lower endpoints

```text
┌───┬─────┬─────────┬─────────┬───────┬────────────────────┐
│ R │ G/Δ │ Lower/Δ │ Upper/Δ │ Gap/Δ │ Interval in rounds │
├───┼─────┼─────────┼─────────┼───────┼────────────────────┤
│ 2 │ 8   │ 46      │ 204     │ 158   │ [23/4,51/2]        │
│ 3 │ 8   │ 62      │ 240     │ 178   │ [31/6,20]          │
│ 3 │ 8   │ 62      │ 252     │ 190   │ [31/6,21] (κ=3)    │
│ 2 │ 4   │ 38      │ 247     │ 209   │ [19/4,247/8]       │
│ 3 │ 4   │ 54      │ 295     │ 241   │ [9/2,295/12]       │
└───┴─────┴─────────┴─────────┴───────┴────────────────────┘
```

The κ=3 row uses 2Δ<Δ_F≤6Δ; the other upper endpoints use κ=2.
N.2.5 supplies all four window-checked lower endpoints. At G=8Δ, HG.8a
supplies the tighter upper endpoints. The spec B_opt table quotes the
H.20/HG.6 bounds instead: 247/295/295/343 in (R,G/Δ) order
(2,4)/(2,8)/(3,4)/(3,8); the G=8Δ entries here are 204/240. HG.7 gives the separate coefficient
intervals `[46,268]` and `[62,312]`. At G=4Δ, H.20 and HG.6 supply
the upper endpoints. For all integer Δ≥1, only the upper endpoints
lose one tick. The old spec lower values are 46/74/62/90 in
(R,G/Δ) order (2,4)/(2,8)/(3,4)/(3,8), as in the spec's lower-bound
paragraph and 00 §3.5; these are separate from HG.N2's old 89/105
and 77/93 forms. Each old larger bound remains OPEN (not established, not refuted).
Neither endpoint is proved optimal. The adopted `B_H` is unchanged.

## 11. Audit, gaps, and statement list

The negative-run and registry history below retains its earlier rule
basis. Positive recovery now uses C1, K≥2, R≥max(2,κ), and B_H^F.

N.1, HG.N1, and N.3 are REPLACED. N.2 and HG.N2 lower bounds are
WEAKER; their old larger bounds remain OPEN (not established, not refuted).
The current-rule runs and their bounds are in §10.

The following distinctions are necessary for the claims in this file.
They are not additional run premises.

1. **Spec and bound scope:** Recovery₂ uses C1, K≥2, R≥max(2,κ),
   δ_t=2R, and B_H^F. HG.7/HG.8a add B_H^ph,F/B_H^8a,F for
   k≤2R+1 and G≥4Δ. The old values apply to Δ_F≤2Δ. For R=3,
   κ=3, k=2, G=8Δ, the bounds are 351Δ, 324Δ, and 252Δ.
   Neither optional bound redefines B_H^F or changes the cut.
2. **Registry scope:** the window restatements use fj.descent.v3,
   fj.twoChanges.core.v3, and ap.headReachesLo.v7 for the current spec.
   As of 2026-09-29, all three old ids are WITHDRAWN for current use;
   none is SUPERSEDED. The v5 statement stays true in its stated scope,
   with clause 5 transferred by bp.genuineFromF.v2 and F⪯P.
   The old pins stay unchanged. The separate FG-COMPOSITION registry
   still needs these edits; see codex/lean-composition-plan.md, r213 list. No Lean discharge
   is claimed by this paper version change.
3. **Outside anchors:** H.3 does not claim that every HEAD is at height
   `lo`, or that an outside-anchor return implies an empty frozen domain.
   Its valid replacement is the full-store witness W. Lower-F domain
   equality alone is not equality of empty-domain fallback returns.
4. **Receipt and tree reads:** No step assumes acceptance of every relay,
   equal raw vote sets, deletion from `Σ.T`, or use of `act(Σ)` for
   the carried-support container scan. Only the retained-suffix score
   equality in H.5 is needed. Reconciliation can remove an unnecessary
   slow history below F; IF.7 states the needed stronger-target case.
5. **Reset versus full healing:** Replacement N.1 refutes full healing
   at `q_(s*)` and attains `G+5Δ=208` ticks of local delay at `k=13`.
   The slot-3 HEAD at 208 uses four frozen W votes; its W lease is
   written only at 224. Lemma U excludes an unsupported old lease
   strictly above C*; a low-support old output can remain there.
6. **Mechanical gap:** There is no checked mixed FG-SA execution theorem
   for H.1–H.22 in the inspected Lean sources. The present result is a
   paper proof blueprint. Plain SA's `AvailableChain.SA.recovered_from_engine` is a theorem
   about `Run V (sa p)`; DC's corresponding recovery theorems are about
   its graded protocol. Neither signature admits direct substitution of
   this spec. The current `AvailableChainSimplexFG` and `AvailableChainKitFG`
   files provide useful FG definitions and certificate/store lemmas;
   they are not yet the composed healing theorem. No unproved producer,
   same-view hypothesis, or inherited recovery theorem is used here.
7. **O.2 — one-repair theorem and optimal bound: OPEN.** H.4-S and
   H.6-S remove one L charge per attempt when their slow windows are
   synchronous. They do not give a single initial 2L charge followed
   by work bounded independently of L. Replacement N.3 refutes persistence
   across arbitrary later events, with 88 ticks of post-settlement wait
   (`L−24 ticks` in N.3.4), but not that uniform theorem. HG.1 proves
   persistence after a served height-m proposal while the frontier stays
   m. Current-rule HG.N2 reaches five effective changes after GST
   (WEAKER lower bounds: 45Δ−1 / 61Δ−1 tick). At R=2,
   all five are after u₀; at R=3, four are after u₀. They do not prove
   five charged restarts or six maximum repair costs. HG.7 retains
   six allowances and removes timing slack. A smaller causal-cut
   allowance and optimal bounds remain OPEN. HG.8a reduces the
   accounting to the initial repair and at most two floor charges.
   At k=2,G=8Δ, N.2.5 and HG.8a give coefficient intervals
   `[46,204]` / `[62,240]`, with gaps 158 / 178. Only the upper
   endpoints lose one tick in integer time. For the old 89/105 and
   77/93 forms, the old larger bound remains OPEN (not established, not refuted).
   Local tightness remains OPEN.
8. **Cut option B — NOT ADOPTED.** HG.8b would use
   `u₀=a_(r_G+1)` with k≤R+1 and give 196Δ/228Δ at k=2,G=8Δ.
   HG.8c is the proposed transfer from the internal old cut for the
   larger k≤2R+1 range. This option changes the meaning of u₀ and M
   and needs coordinated H0, spec, and Lean changes. It is recorded
   only as an option (codex/scratch/hg8-draft.md §5). The current cut,
   H.22 and the cut retain their witness meanings; current H-time uses B_H^F.

Deleting a lease when its target leaves the choice domain is not an
adopted change. It would need new proofs of the SA transfer premises
under asynchrony, as well as source retention and recovery. No failure
execution or replacement safety proof for that change is established
here. It therefore supplies no one-repair theorem.

The negative statement rows cite the current-rule runs in §10.
The qualified statements in items 3–4 are the interfaces proved here.

```text
┌──────────┬───────────────────────────────────────────────┬──────────┐
│ Local id │ Registry id / statement                       │ Status   │
├──────────┼───────────────────────────────────────────────┼──────────┤
│ IF.1     │ Tree, immutable states, actual origins        │ PROVED   │
│ IF.2     │ Honest client and quorum counts               │ PROVED   │
│ IF.3     │ bp.chainCertificates.v2, fg.uniqueJust.v1,    │ PROVED   │
│          │ fg.finalLock.v3: certificates and crossing    │          │
│ IF.4     │ fg.frame monotonicity; lease chain;           │ PROVED   │
│          │ comp.outputNesting.v3                         │          │
│ IF.5     │ Receipt: admission or coverage                │ PROVED   │
│ IF.6     │ Same-label genuine compatibility              │ PROVED   │
│ IF.7     │ Required history after reconciliation         │ PROVED   │
│ H.1      │ Release and majority transfer                 │ PROVED   │
│ H.2      │ ap.S.v2, ap.Sslow.v1: S1–S3 with keep         │ PROVED   │
│ H.3      │ ap.headReachesLo.v7, clauses 1–4: anchor/W    │ PROVED   │
│ H.4      │ bp.phaseSourcePermanence.v2                   │ PROVED   │
│ H.4-S    │ Synchronous slow window; current phase only   │ PROVED   │
│ H.5      │ fg.trunk.v1 scope; retained-score equality    │ PROVED   │
│ H.6      │ ap.repair.movingF.v1; v6 clause 5: ρΓ         │ PROVED   │
│ H.6-S/C  │ ρ₁ repair; cut condition k≤2R+1               │ PROVED   │
│ H.7      │ fj.crossingNoFinal.v1; inBandLock.v1;         │ PROVED   │
│          │ twoChanges.core.v3; frame.v5                  │          │
│ H.8      │ ap.headReachesLo.v7, clause 6: θ=3Δ           │ PROVED   │
│ H.9      │ bp.commonEntry.v2;                            │ PROVED   │
│          │ bp.renewedPromotion.v2                        │          │
│ H.10     │ fj.rise.movingF.v1: retained phase budgets    │ PROVED   │
│ HG.1–6   │ bp.progressAttempt.v2, bp.resetArrival.v2;    │ PROVED   │
│          │ registry id —: frontier service, new bounds   │          │
│ HG.7     │ Phase-exact B_H^ph,F; k≤2R+1                  │ PROVED   │
│ HG.8-SI  │ Service interface for HG.1/HG.2/H.9           │ PROVED   │
│ L2-W     │ Self-witness and root coverage at w+Δ         │ PROVED   │
│ L2       │ Top-J service, inherited repair, floor rise   │ PROVED   │
│ L3       │ At most two floor increases                   │ PROVED   │
│ L4-R     │ Served frontier rise: no repair charge        │ PROVED   │
│ L4-C     │ Pre-service contest carry                     │ PROVED   │
│ HG.8a    │ Three-charge B_H^8a,F; k≤2R+1, G≥4Δ           │ PROVED   │
│ H.11     │ fj.reset.v1: B_reset^F                        │ PROVED   │
│ H.9-Q    │ ap.source.v1; rowService.v1; carrierKeep.v2   │ PROVED   │
│ H.10-Q   │ fj.rise.movingF.v1: qualified-search budget   │ PROVED   │
│ H.11-Q   │ fj.reset.v1: qualified-search reset bound     │ PROVED   │
│ H.12     │ Causal source timing and first transfer       │ PROVED   │
│ H.13     │ fj.descent.v3; fj.canonical.v1                │ PROVED   │
│ H.14     │ fj.theoremN.v1: all protected bodies          │ PROVED   │
│ H.15     │ Lemma U: universal leases above C*            │ PROVED   │
│ H.16     │ Corollary U′: all post-reset raw results      │ PROVED   │
│ H.17     │ fj.Xplus.v1: exact post-reset service         │ PROVED   │
│ H.18     │ fj.healed.v1, H′: q_(s*)+Γ+5Δ                 │ PROVED   │
│ H.19     │ All-fast corollary: q_(s*)+5Δ                 │ PROVED   │
│ H.20     │ fj.healedUnif.v1: HG.6 B_H^F                  │ PROVED   │
│ H.22     │ bp.healingInput.v2: HEALED; H0–H6;            │ PROVED   │
│          │ H2.A/H2′, T-ROWS, H-time                      │          │
│ H.21     │ Every R≥max(2,κ), δ_t=2R                      │ PROVED   │
│ N.1      │ fj.healedAtQ.v1: HEALED(q_(s*)) false; N.1    │ REPLACED │
│ N.1a     │ G+5Δ local delay at n=7,k=13,R=3; N.1         │ REPLACED │
│ N.2      │ Healing 38/46/54/62 Δ; N.2.5                  │ WEAKER   │
│ HG.N1–2  │ μ=4; five changes; 45Δ−1 / 61Δ−1 tick; HG.N2  │ WEAKER   │
│ N.3      │ L lifetime; wait 88=L−24 ticks; N.3.3–N.3.4   │ REPLACED │
│ O.1      │ Checked mixed-protocol Lean theorem           │ OPEN     │
│ O.2      │ One-repair / optimal uniform upper bound      │ OPEN     │
│ O.3      │ Local tightness; matching optimal lower bound │ OPEN     │
└──────────┴───────────────────────────────────────────────┴──────────┘
```

**Earlier checks (historical record).** The spec and archive hashes were verified. The SA
checkout read was `3eb1889cd7e231d33e7edb96762b0ebd641825cb`; the DC Lean
checkout read was `b241081d344555797205f8718eeb23a8a0e3eb4c`. The DC
paper file read had SHA-256
`dc471b47a46896fe0a3df300c188fef1512f475615ce0fc0df18dbea6d2e5517`.
Declaration names and critical definitions were read from those checkouts;
a file-level declaration is not reported as a newly built certificate.
In-memory arithmetic checked the reference values, the two-lease identity,
the reset sum, and all R-dependent inequalities for R=2 through 1000;
the algebraic proofs above cover every integer R≥2.
The window check of the listed §10 events uses R6-window, R7,
send-once, and `h>h_f`, with the delay bounds and check limits in §10.
N.1 gives G+5Δ; N.2 gives healing 38/46/54/62 Δ and first finality
48/64/68/80 Δ; HG.N1 gives μ=4; HG.N2 gives five changes and
45Δ−1 / 61Δ−1 tick; N.3 gives an L lifetime and an L−24 tick wait.
**historical (pre-no-round rules).** The old run and replay notes are in
[21-healing-6aecd21b.md](archive/21-healing-6aecd21b.md), §11.
No Lean build or complete FG-SA model check was run. The edit report
is separate from the blueprint and is not a proof premise.

The r213 fold adds HG.8-SI, L2-W, L2, L3, L4-R, L4-C, and HG.8a
with all fixes of review-hg8-draft. Current-rule HG.N1–HG.N2 state the
n=7 prefix and five-change run with weaker 45Δ−1 / 61Δ−1 tick bounds.
The old larger bound remains OPEN (not established, not refuted).
Spec citations in these additions use 4e85ff34. No protocol,
cut, or B_H change is made. The Pins/FG-COMPOSITION handoff is in
codex/lean-composition-plan.md under r213.
