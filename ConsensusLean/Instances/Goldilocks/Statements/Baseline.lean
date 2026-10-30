module
public import ConsensusLean.Instances.Goldilocks.Spec.Baseline
public import Mathlib.Tactic

@[expose] public section

/-! # The Goldilocks properties sheet

**Round-model FG-SA, `Δ_F = Δ`, slow arming, `κ = 2`.** These pins (the
intended properties allow `Δ_F ≥ Δ`, other `κ` and fast arming, and the final
heal point couples the healing gap to `gf·R`) are instance restrictions of this
target, not limits of the intended properties. `GoldilocksTarget F pp`
is a *reviewed target*, not a proof that FG-SA meets it: the reviewed bindings
(`GoldilocksBindings`: the skeleton), acceptance at the pinned numbers
(`Accepted F (goldilocksContract pp)`, which gives the L0 `Good`), and the
Goldilocks-specific extras (`GoldilocksExtra`). It states Goldilocks'
**intended** properties (`intended-opus.md` / `intended-astra.md` ids), not only
what FG-SA proves today. A failed FG-SA feasibility gate or migration
obligation leaves this target unproved and goes back to Francesco; the target
is never changed to fit FG-SA.

Ids such as `L1 / P-SYNC-AV-INCLUDE` are intended-property ids from those
files, not the layer names L0/L1/L2.

**OD-23 (answered by Francesco, 2026-10-28).** The fixed regimes are the
definition; Goldilocks pins only numbers: the outage regime is η-sleepy, with
Goldilocks' look-back `η = eta` (`FGSAParams.params`). The healthy regime
(Francesco, 2026-10-29) is full participation: every honest validator awake
from `max g 0`, with fewer than `β·n` faulty (`β = ⅓`), which is the premise of
FG-SA's recovery proof (obligations (1) and (9) below are closed).

**Where the dispositions are.** §1, proved from `Accepted`: the theorems in
namespace `GoldilocksTarget` (below). §2, stated only: the fields of
`GoldilocksExtraAt`. Each of those declarations' docstrings starts with its
intended ids; §3 and the weaker-than-intended rows are listed here.

Every §1 theorem takes `h : GoldilocksTarget F pp` and a finite validator type `V`;
the system is `Sys F V` (the compiled family), the excuse is an observed hash
collision (`HC`), the catch-up is `gc r = 18·Δ`, the heal points are
`gHeal k = max g 0 + (29 + B_H^F(k))·Δ` (available, stable) and
`gHealFin gf = max g 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ` (final), each the L0
quantity at the pinned numbers (`gc_eq`, `gHeal_eq`, `gHealFin_eq`). Stable is aliased to
confirmed by the schema, so every stable row is a confirmed row. Non-framing
and accountability are **for this family's `conflicts` predicate** until the
E1/E2 evidence binding exists (obligation (7)).

## §3 Not yet stated (with reason)

* A6 / P-WEAK-CORRUPTION: a two-run statement (a retained set compared
  across a run and its corrupted continuation; its one-run form needs "honest
  until `T_F`"). It is the only intended *available*-output "or ⅓ slashable"
  result; the definition has accountability for the final output only.
* P-OUT-AV-FAST (fast arming: `T + 4Δ ≤ b₀` with at least `⌈n/2⌉` awake
  before `b₀`; FG-SA's `FastP1Claim`): the fixed outage regime has one arming
  lag, and the pin is slow arming; fast arming needs a second lag with a
  half-committee participation premise. A later extra.
* P-NV-CONTINUATION: `WeakPremise` is inhabited (`weakPremise_inhabited` in
  `ConsensusLeanTest/Goldilocks.lean`: the generic healthy witness, everyone
  awake), so the weak extras are not vacuous.
* P-MODEL-WELLFORMED: covered by `Valid` (`ExecutionValid`) and the L1 model.
* P-TX-SCOPE: the intended guarantees stop at proposal inclusion; this target
  goes further, to transaction liveness (`confirmed_txLive_*`,
  `finalized_txLive`). This costs FG-SA nothing beyond the block-level
  `ShapeClaims`: the generic bridge `proposalLive_txLive` turns proposal
  liveness into transaction liveness through the engine-written payload
  (`encodeTxs mempool`) and the L0 transaction relay (`Delivers.txs`).
* Weak continuation, uniform cut/seed (one gate and seed fixed before the
  continuation, for every continuation): a two-run statement; obligation (10).
* FL3, FL4 / P-GST-FIN-INCLUDE, -FRONTIER: per-proposal finality and finality
  above the frontier; a later extra.
* FL7, FL8 / P-FIN-HEALTHY-LATENCY: paper only (not in FG-SA's Lean).
* L2 / P-SYNC-HEAD-ADOPT, HEAD outputs: HEAD is protocol-internal (M39).
* N4, F3, F4, H1–H5; P-ANY-{CERTIFICATES, CROSSING, FILTER, HEAD-GEOMETRY,
  SOURCE-ORIGIN, LOCK-PROTECTION}; P-GST-{EXACT-SERVICE, SOURCE-TRANSFER,
  RAW-TRANSFER, UNANIMOUS-GATE, FG-SERVICE, HEAL-EXISTS, HEAL-IMPROVED};
  P-LABEL-RAW-SAFE, P-LOCAL-FIN-KERNEL, P-FIN-STRONG-ALTERNATIVES:
  protocol-internal.
* P-NEW-*: the fast path is not in the Lean model. **Newer spec, binding of
  `available`:** in fgsa-spec.tex (989–993) the read-time tip `ac_confirmed =
  dca(latestConfirmed, head)`. Under synchrony `head` extends
  `latestConfirmed`, so `ac_confirmed = latestConfirmed`, which is monotone.
  It can step back only under asynchrony, where per-reader monotonicity of
  `available` is not required: `ReadySafe` (which includes per-reader
  monotonicity) is asked only by `sleepySafe`, from time 0 in sleepy
  (synchronous) runs, and by `healedSafe`, from the heal point (after GST) in
  healthy runs, and monotonicity compares cuts within that interval only. So
  `available` may bind to `ac_confirmed`, provided the protocol establishes
  the synchronous invariant (`head` extends `latestConfirmed`) (Francesco,
  2026-10-29). There is no FG-SA bridge yet.
* K1–K5 / P-LEAK-*: leak accounting (optional extra).
* E1/E2 `conflicts` binding: needs an evidence block (migration step 0;
  obligation (7)).
* P-OUT-DUTY-EXTEND, P-OUT-LEASE: protocol-internal.
* P-OUT-PROGRESS-LIMIT, A2-limit, A7, L7, N7, FL-neg, FL-scope: negative or
  not-claimed facts, consistent with the sheet.

## Weaker than intended (accepted)

* A3 / P-OUT-CONTINUE (`confirmed_persists`): (a) η-sleepy participation
  holds *during* the window (the prose assumes no participation during the
  outage; the fixed outage regime is η-sleepy throughout, Francesco's
  decision); (b) the budget is `min eta (4·lockK − 5)`: the η cap is A2's
  (P1) restriction, A3 alone needs only (V); (c) retention is for
  `ResilienceReader`s only, where the prose says every honest reader,
  sleepers included.
* P-OUT-FIN-COMPAT (`outage_final_compatible`): stated for reading times
  `t ≥ b₀` under the full outage regime, for eligible readers; the intended
  `0 ≤ t < b₀` part under the P1 premise (no assumption after the window) is
  not stated; a later extra.
* Readers and proposers are `Ready` (awake for the catch-up `18·Δ`) where
  intended rows say "joined" (obligation (3)).

## Migration obligations

Each is a gate the FG-SA migration must pass **against this unchanged
target**; a failure leaves `GoldilocksTarget` unproved and goes back to
Francesco.

1. Closed (Francesco, 2026-10-29): the healthy regime is full participation
   (every honest validator awake throughout `[max g 0, horizon]`, so no
   restart after GST; fewer than `n/3` faulty), FG-SA Recovery₂'s premise; no
   recovery from partial participation is owed.
2. GST shift to `max g 0` plus catch-up (gate F-1).
3. `Ready` at catch-up `18·Δ` ⇒ joined / confirmed reader; ready at `b₀` and
   awake ⇒ covered (F-3). `IncludesFrom` and `ProposalLiveReady` require the
   proposer to be ready, where the intended rows say "joined" (awake since the
   previous slot start): a weaker claim, accepted.
4. Outage continuation under η-sleepy participation (`η = eta`) throughout
   and cover ½ at `b₀`, partially synchronous with GST `b₁` after the window,
   vs FG-SA `OutageE` and its after-window premise (F-4); for A2
   (`outageWindow`), η-sleepy on `[0, b₀]` only, vs FG-SA's prefix premise.
   Startup alignment: the contract's look-back is clamped at `0` (no
   participation history before time `0`), FG-SA's is not; the bridge either
   takes FG-SA environments asleep before `0` or proves the clamped premise
   implies FG-SA's. With `η > 0` the contract's denominator (ready ∪ awake in
   the look-back ∪ faulty) is stronger than plain sleepy participation.
   The cover ½ at `b₀` gives FG-SA's `OutageE1` (faulty validators and
   uncovered wakers are fewer than half): `EnvPoint.two_mul_card_faulty_union_lt`
   (tests: `ConsensusLeanTest/Goldilocks`).
5. Readers caught up after the window (FG-SA proves repair-ready readers only).
6. Ready-vs-awake counting (M25).
7. E1/E2 evidence binding (`conflicts` = FG-SA's slashing rule).
8. Hash/digest (F-7); relay of accepted objects across sleep (F-8);
   receipt-to-processing under endpoint delivery (F-9: FG-SA timing assumed
   receipt strictly before the deadline; endpoint receipt costs one time
   unit, at most `Δ`, absorbed by the `Δ`-rounded numbers or re-proved).
9. Closed (Francesco, 2026-10-29): finality liveness is owed under the
   full-participation healthy regime, FG-SA's all-awake premise.
10. Weak continuation: uniform cut/seed preservation.
11. FL1/FL2 (`finalFirst`, `finalRecur`) are stated in the intended forms:
    strictly above the ready confirmed reads at the healing cut
    `finalCut = max g 0 + (29 + B_H^F(gf·R))·Δ` (intended `t_ready + B_H^F`),
    by `finalCut + W_W` (FL1), and from every `t ≥ finalCut` by `t + W_W`
    (FL2). The migration proves them from FG-SA's
    `FirstFinalityRecFEClaim_W` / `FinalityLivenessGSTClaim_W` under the
    contract's progress premise (`finRec gf`). `W_W(gf)` is shorter than one
    guarded window of `finRec gf` by `4R − 5` (`finalRecur_delay_vs_window`),
    so the proof must use FG-SA's own recurrence analysis, not one fresh
    window; if `finRec gf` does not give FG-SA's `Rec_{FE,W}(gf)`, the gate
    fails and goes back to Francesco.
12. Prefix forms: FG-SA's `CleanPrefixTruncation` matches `Adequate.prefixClosed`
    on the FG-SA run model. -/

namespace Consensus

namespace Shape

open Blocks
open Consensus.Model (pubOf sysOf)

/-! ## Numbers

Proved: `reference_bounds`, `goldilocks_admissible` (in `Goldilocks.lean`),
`budget_implies_V`, `range_head` (with the span loss),
`final_latency_covers_window`, `final_heal_covers_window` (the final latency and
heal point cover one window plus the pattern span, for every `R` and `gf`),
`finalRecur_delay_vs_window` (the intended FL2 delay `W_W` does not), and
`EnvPoint.two_mul_card_faulty_union_lt` (tests: `ConsensusLeanTest/Goldilocks`). -/

/-- The outage budget implies FG-SA's condition (V):
`b₁ − b₀ + ((b₀ − 6Δ) mod 4Δ) ≤ L·Δ`. -/
theorem budget_implies_V (pp : FGSAParams) {Δ b₀ b₁ : Time} (hΔ : 0 < Δ)
    (hb : b₁ - b₀ ≤ (pp.budget : Time) * Δ) :
    b₁ - b₀ + (b₀ - 6 * Δ) % (4 * Δ) ≤ (pp.L : Time) * Δ := by
  have hm : (b₀ - 6 * Δ) % (4 * Δ) < 4 * Δ := Int.emod_lt_of_pos _ (by linarith)
  have hl := pp.hLock
  have hbud : pp.budget ≤ 4 * pp.lockK - 5 := min_le_right _ _
  have hbud' : (pp.budget : Time) ≤ 4 * (pp.lockK : Time) - 5 := by
    have : ((4 * pp.lockK - 5 : Nat) : Time) = 4 * (pp.lockK : Time) - 5 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast hbud
  have hL : (pp.L : Time) = 4 * (pp.lockK : Time) - 1 := by
    unfold FGSAParams.L; rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hL]
  nlinarith

/-- The finality pattern's span, `3R + 1` slots. -/
theorem finRec_span (pp : FGSAParams) (gf : ℕ+) : (pp.finRec gf).pattern.span = 3 * pp.R + 1 := by
  refine (Pattern.span_range
    (⟨3 * pp.R + FGSAParams.κ, by unfold FGSAParams.κ; omega⟩ : ℕ+)).trans ?_
  change 3 * pp.R + FGSAParams.κ - 1 = _
  unfold FGSAParams.κ; omega

/-- Head extraction for the finality recurrence: `3R + κ` consecutive honest
ready proposers in every window of `gf·R` slots give one honest ready
proposer in every window of `gf·R` slots, losing the pattern's span
`3R + 1` slots at the end of the window. -/
theorem range_head (pp : FGSAParams) (gf : ℕ+) {V : Type} [Fintype V] {p : EnvPoint V}
    {key : Fin (Fintype.card V) ≃ V} {sel : Slot → Finset (Fin (Fintype.card V))}
    {G : TimeGrid} {c start stop : Time}
    (h : PatternRecurrence p key sel G (pp.finRec gf) c start stop) :
    PatternRecurrence p key sel G ⟨Pattern.single, (pp.finRec gf).gap⟩ c start
      (min stop p.horizon - ((3 * pp.R + 1 : Nat) : Time) * G.slotLen p.env.Δ) := by
  have hspan := finRec_span pp gf
  have h0 : 0 ∈ (pp.finRec gf).pattern.offsets :=
    List.mem_range.mpr (by simp [FGSAParams.κ])
  have := PatternRecurrence.single_of_zero h0 h
  rwa [hspan] at this

/-- `B_H^F` is at least `12·P = 48·R` (`Δ`-coefficient), at every gap. -/
private theorem bhf_ge (pp : FGSAParams) (k : Nat) : 48 * pp.R ≤ pp.bhf k := by
  have h1 : 48 * pp.R ≤ pp.bhf1 k := by
    unfold FGSAParams.bhf1 FGSAParams.P; omega
  have h2 : 48 * pp.R ≤ pp.bhf2 k := by
    unfold FGSAParams.bhf2 FGSAParams.P; omega
  unfold FGSAParams.bhf; split_ifs <;> omega

/-- The guarded finality window (`Δ`-coefficient): one window of `gf·R` slots
plus the pattern's span, `4·gf·R + 4·(3R + 1)`. -/
def finWindow (pp : FGSAParams) (gf : ℕ+) : Nat :=
  4 * (gf * pp.R) + 4 * (pp.finRec gf).pattern.span

/-- The final latency covers the guarded finality window, for every `R` and
`gf` (it exceeds it by `4R(gf − 1) + 11`). -/
theorem final_latency_covers_window (pp : FGSAParams) (gf : ℕ+) :
    finWindow pp gf + 4 * pp.R * (gf - 1) + 11 = pp.latency .final gf := by
  have hg := gf.pos
  unfold finWindow
  rw [finRec_span]
  simp only [FGSAParams.latency, FGSAParams.wW, FGSAParams.P, FGSAParams.κ]
  obtain ⟨m, hm⟩ : ∃ m, (gf : Nat) = m + 1 := ⟨gf - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel]; ring

/-- The final heal point covers readiness (`catchUp + 1`) plus the guarded
finality window, for every `R` and `gf`. -/
theorem final_heal_covers_window (pp : FGSAParams) (gf : ℕ+) :
    FGSAParams.catchUp + 1 + finWindow pp gf ≤ pp.heal .final gf := by
  have hb := bhf_ge pp (gf * pp.R)
  unfold finWindow
  rw [finRec_span]
  simp only [FGSAParams.heal, FGSAParams.wW, FGSAParams.P, FGSAParams.κ, FGSAParams.catchUp]
  have : (gf : Nat) * pp.R ≤ (gf + 2) * (4 * pp.R) := by nlinarith
  nlinarith

/-- The intended recurring-finality delay `W_W(gf)` (`finalRecur`) is shorter
than one guarded finality window by `4R − 5`: `W_W(gf) + 4R = finWindow + 5`.
The contract's recurrence alone does not put a whole window inside `W_W`; the
intended FL2 relies on FG-SA's own analysis (obligation (11)). -/
theorem finalRecur_delay_vs_window (pp : FGSAParams) (gf : ℕ+) :
    pp.wW gf + 4 * pp.R = finWindow pp gf + 5 := by
  unfold finWindow
  rw [finRec_span]
  simp only [FGSAParams.wW, FGSAParams.P, FGSAParams.κ]
  ring

/-! ## Bindings, chain-level vocabulary, extras, target -/

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- The confirmed output (available and stable). -/
abbrev gConfirmed : goldilocksSchema.Id := GOut.confirmed

/-- The finalized output (final). -/
abbrev gFinalized : goldilocksSchema.Id := GOut.finalized

/-- The reviewed bindings: the Goldilocks skeleton (grid of `4·Δ` slots, one
proposer per slot). The E1/E2 `conflicts` binding is obligation (7). -/
def GoldilocksBindings (F : ShapeFamily goldilocksSchema Info) : Prop :=
  ∀ pub, (F pub).skel = goldilocksSkeleton pub.n

section Vocabulary

variable {O : OutputSchema} {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

/-- Inclusion of honest proposals from `start`: every honest proposal released
at `τ ≥ start` by a key ready at `τ` is in the `g`-read of every ready node at
every time of `[τ + D·Δ, horizon]` (persistently). -/
def IncludesFrom (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time)
    (D : Nat) : Prop :=
  ∀ τ k h, start ≤ τ → rho.point.Ready c (rho.key k) τ → HonestProposal rho τ k h →
    ∀ t, τ + (D : Time) * E.Δ ≤ t → t ≤ rho.horizon → InBy rho c g h t

/-- `h` is a new common `dst` entry at `d` above the `src` reads at `t` of the
nodes satisfying `A`: it is in the `dst`-read of every node ready at `d`, in
none of those `src` reads, and each of those is a prefix of each ready
`dst`-read at `d`. -/
def NewAbove (rho : Model.Run (compiled F) E) (c : Time) (src dst : O.Id) (A : V → Prop)
    (t d : Time) (h : Header Info) : Prop :=
  InBy rho c dst h d ∧ ∀ x, A x → h ∉ (chainTrace rho).readAt src x t ∧
    ∀ y, rho.point.Ready c y d → (chainTrace rho).readAt src x t <+: (chainTrace rho).readAt dst y d

/-- Joint strict growth from `src` into `dst` from `start` with delay `D·Δ`
(reader-conditional, like `ProposalLiveReady`): for every `t ≥ start` with
`t + D·Δ` in the horizon and some node ready at `t + D·Δ`, one honest
proposal, released after `t` by a key ready at its release, is a new common
`dst` entry at `t + D·Δ` above every ready `src` read at `t`. `src = dst`:
chain growth (one proposal common to all ready readers). -/
def CrossGrowth (rho : Model.Run (compiled F) E) (c : Time) (src dst : O.Id) (start : Time)
    (D : Nat) : Prop :=
  ∀ t, start ≤ t → t + (D : Time) * E.Δ ≤ rho.horizon →
    (∃ v, rho.point.Ready c v (t + (D : Time) * E.Δ)) →
    ∃ τ k h, t < τ ∧ rho.point.Ready c (rho.key k) τ ∧ HonestProposal rho τ k h ∧
      NewAbove rho c src dst (fun x => rho.point.Ready c x t) t (t + (D : Time) * E.Δ) h

/-- Cross nesting from `start`: at every time of `[start, horizon]`, every
ready `src` read is a prefix of every ready `dst` read. -/
def ReadyNestedFrom (rho : Model.Run (compiled F) E) (c : Time) (src dst : O.Id)
    (start : Time) : Prop :=
  ∀ t, start ≤ t → t ≤ rho.horizon → ∀ x y, rho.point.Ready c x t → rho.point.Ready c y t →
    (chainTrace rho).readAt src x t <+: (chainTrace rho).readAt dst y t

end Vocabulary

/-! ### The pinned durations at a run

Each is the L0 quantity of the compiled system at `goldilocksContract pp`,
with its pinned number shown (`gc_eq`, `gReady_eq`, `gHeal_eq`,
`gHealFin_eq`, `gProg_eq`: `rfl`). -/

section Pinned

variable (pp : FGSAParams) {F : ShapeFamily goldilocksSchema Info} {V : Type} [Fintype V]
  [DecidableEq V]

/-- The catch-up `c = 18·Δ` of run `r`. -/
abbrev gc (r : (Sys F V).Run) : Time := ((18 : Nat) : Time) * ((Sys F V).pt r).env.Δ

/-- The start of progress windows after GST `gst`: `max gst 0 + c + 1`. -/
abbrev gReady (gst : Time) (r : (Sys F V).Run) : Time := max gst 0 + gc r + 1

/-- The available and stable heal point at gap `k` slots after GST `gst`:
`max gst 0 + (29 + B_H^F(k))·Δ`. -/
abbrev gHeal (k : Nat) (gst : Time) (r : (Sys F V).Run) : Time :=
  max gst 0 + ((29 + pp.bhf k : Nat) : Time) * ((Sys F V).pt r).env.Δ

/-- The final heal point (first finality) at index `gf` after GST `gst`:
`max gst 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ`. -/
abbrev gHealFin (gf : ℕ+) (gst : Time) (r : (Sys F V).Run) : Time :=
  max gst 0 + ((29 + pp.bhf (gf * pp.R) + pp.wW gf : Nat) : Time) * ((Sys F V).pt r).env.Δ

/-- The healing cut for finality at index `gf` after GST `gst`: the available
heal point at gap `gf·R`, `max gst 0 + (29 + B_H^F(gf·R))·Δ`, which is the final
heal point minus `W_W(gf)·Δ` (intended: `t_ready + B_H^F`). -/
abbrev finalCut (gf : ℕ+) (gst : Time) (r : (Sys F V).Run) : Time := gHeal pp (gf * pp.R) gst r

/-- The progress requirement of `cap` at index `k` on `[start, stop]`. -/
abbrev gProg (cap : Capability) (k : ℕ+) (start stop : Time) (r : (Sys F V).Run) : Prop :=
  (Sys F V).prog (shapeProgress F V) (goldilocksContract pp) cap k start stop r

theorem gc_eq (r : (Sys F V).Run) : (Sys F V).cDur (goldilocksContract pp) r = gc r := rfl

theorem gReady_eq (gst : Time) (r : (Sys F V).Run) :
    (Sys F V).ready (goldilocksContract pp) gst r = gReady gst r := rfl

theorem gHeal_eq (cap : Capability) (hcap : cap ≠ .final) (k : ℕ+) (gst : Time)
    (r : (Sys F V).Run) :
    (Sys F V).heal (goldilocksContract pp) cap k gst r = gHeal pp k gst r := by
  cases cap <;> first | rfl | exact absurd rfl hcap

theorem gHealFin_eq (gf : ℕ+) (gst : Time) (r : (Sys F V).Run) :
    (Sys F V).heal (goldilocksContract pp) .final gf gst r = gHealFin pp gf gst r := rfl

end Pinned

/-- The weak-continuation premise at gap `k` after GST `gst`: partially
synchronous with GST `gst` (the whole run), healthy (every honest validator
awake, fewer than `β·n` faulty) up to the heal point, one honest
ready proposer per window of `k` slots on `[ready, heal]`, and sleepy
participation from the heal point to the horizon. No recurrence after the
heal point. -/
def WeakPremise {F : ShapeFamily goldilocksSchema Info} {V : Type} [Fintype V] [DecidableEq V]
    (pp : FGSAParams) (gst : Time) (k : ℕ+) (r : (Sys F V).Run) : Prop :=
  CommLog.PSync r.2.point r.2.log gst ∧
    ((Sys F V).pt r).HealthyOn (goldilocksContract pp).params.β gst (gHeal pp k gst r) ∧
    gProg pp .available k (gReady gst r) (gHeal pp k gst r) r ∧
    ((Sys F V).pt r).SleepyOn (goldilocksContract pp).params.θ (gc r) (gHeal pp k gst r)
      ((Sys F V).pt r).horizon

/-- The Goldilocks extras at validators `V`: intended properties beyond the
fixed L0 table (statements; FG-SA's migration proves them). Every claim is
`System.Holds` on the compiled system: on every valid run satisfying the
premise, "or an observed hash collision". Regimes are the L0 ones at the pinned
numbers (`goldilocksContract pp`); `gc = 18·Δ`; heal points from `max g 0`. -/
structure GoldilocksExtraAt (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams)
    (V : Type) [Fintype V] [DecidableEq V] : Prop where
  /-- **L1 / P-SYNC-AV-INCLUDE.** Sleepy: every honest proposal released at
  `τ` by a key ready at `τ` is in every ready confirmed read at every
  `t ∈ [τ + 6Δ, horizon]`. -/
  includeSleepy : (Sys F V).Holds ((Sys F V).Sleepy (goldilocksContract pp)) fun r =>
    IncludesFrom r.2 (gc r) gConfirmed 0 6
  /-- **L4 / P-GST-AV-INCLUDE.** Healthy from `gst` with one honest ready
  proposer per window of `k` slots on `[ready, heal]`: the same for
  proposals released at `τ ≥ heal`. -/
  includeHealed : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .available k (gReady gst r) (gHeal pp k gst r) r)
    fun r => IncludesFrom r.2 (gc r) gConfirmed (gHeal pp k gst r) 6
  /-- **L3 / P-SYNC-AV-GROW** (block level). Sleepy with one honest ready
  proposer per window of `k` slots: joint strict growth of the confirmed
  output by `t + (4k + 6)·Δ`. -/
  growSleepy : ∀ k : ℕ+, (Sys F V).Holds
    (fun r => (Sys F V).Sleepy (goldilocksContract pp) r ∧
      gProg pp .available k 0 ((Sys F V).pt r).horizon r)
    fun r => CrossGrowth r.2 (gc r) gConfirmed gConfirmed 0 (4 * k + 6)
  /-- **L5 / P-GST-AV-GROW** (block level). Healthy from `gst` with the
  recurrence of `k` from `ready`: joint strict growth from the heal
  point. -/
  growHealed : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .available k (gReady gst r) ((Sys F V).pt r).horizon r)
    fun r => CrossGrowth r.2 (gc r) gConfirmed gConfirmed (gHeal pp k gst r) (4 * k + 6)
  /-- **FL1 / P-GST-FIN-FIRST.** Healthy from `gst` with the finality
  recurrence of `gf` on `[ready, heal]`: a new finalized entry, strictly
  above every ready confirmed read at the healing cut
  `finalCut = max gst 0 + (29 + B_H^F(gf·R))·Δ`, is in every ready finalized
  read at the first-finality point `finalCut + W_W(gf)·Δ` (the final heal
  point). -/
  finalFirst : ∀ (gf : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .final gf (gReady gst r) (gHealFin pp gf gst r) r ∧
      gHealFin pp gf gst r ≤ ((Sys F V).pt r).horizon)
    fun r => ∃ h, NewAbove r.2 (gc r) gConfirmed gFinalized
      (fun x => r.2.point.Ready (gc r) x (finalCut pp gf gst r)) (finalCut pp gf gst r)
      (gHealFin pp gf gst r) h
  /-- **FL2 / P-GST-FIN-RECUR.** Healthy from `gst` with the finality
  recurrence of `gf` from `ready`: for every `t` from the healing cut
  `finalCut`, a new finalized entry strictly above every ready confirmed read
  at `t` is in every ready finalized read at `t + W_W(gf)·Δ`. -/
  finalRecur : ∀ (gf : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .final gf (gReady gst r) ((Sys F V).pt r).horizon r)
    fun r => ∀ t, finalCut pp gf gst r ≤ t →
      t + ((pp.wW gf : Nat) : Time) * ((Sys F V).pt r).env.Δ ≤ ((Sys F V).pt r).horizon →
      ∃ h, NewAbove r.2 (gc r) gConfirmed gFinalized (fun x => r.2.point.Ready (gc r) x t) t
        (t + ((pp.wW gf : Nat) : Time) * ((Sys F V).pt r).env.Δ) h
  /-- **FL5 / P-GST-FIN-GROW** (LiveDC). Healthy from `gst` with the finality recurrence of
  `gf` from `ready`: for every `t` from the first-finality point, an
  honest proposal released after `t` strictly extends every ready confirmed
  read at `t` and is in every ready finalized read by
  `t + (2·W_W(gf) + 4·gf·R)·Δ`. -/
  liveDC : ∀ (gf : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .final gf (gReady gst r) ((Sys F V).pt r).horizon r)
    fun r => CrossGrowth r.2 (gc r) gConfirmed gFinalized (gHealFin pp gf gst r)
      (2 * pp.wW gf + 4 * (gf * pp.R))
  /-- **A4 part / P-GST-CROSS-NEST.** Healthy from `gst` with the recurrence of
  `k` on `[ready, heal]`: from the heal point, every ready finalized read
  is a prefix of every ready confirmed read at the same time. -/
  crossNest : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy (goldilocksContract pp) gst r ∧
      gProg pp .available k (gReady gst r) (gHeal pp k gst r) r)
    fun r => ReadyNestedFrom r.2 (gc r) gFinalized gConfirmed (gHeal pp k gst r)
  /-- **A2 / P-OUT-AV-SLOW.** Outage times, synchronous for deadlines up to
  `b₀`, η-sleepy on the prefix `[0, b₀]` only, more than half ready at `b₀`,
  and **no** assumption after `b₀` (neither network nor participation:
  participation may collapse inside the outage): what a node ready at `T`
  reads as confirmed is kept by every eligible reader (ready at `b₀` and awake
  since) at every time of `[b₀, b₁)` within the horizon. -/
  outageWindow : ∀ T b₀ b₁ : Time, (Sys F V).Holds
    (fun r => OutageTimes (goldilocksContract pp).params ((Sys F V).pt r).env.Δ T b₀ b₁ ∧
      CommLog.SyncUntil r.2.point r.2.log b₀ ∧
      ((Sys F V).pt r).EtaSleepyOn (goldilocksContract pp).params.θ
        (((goldilocksContract pp).params.η : Time) * ((Sys F V).pt r).env.Δ) (gc r) 0 b₀ ∧
      ((Sys F V).pt r).ReadyOfAll (goldilocksContract pp).params.cover (gc r) b₀)
    fun r => (chainTrace r.2).ProtectedUpTo (gc r) gConfirmed gConfirmed T b₀ b₁
      (min (b₁ - 1) ((Sys F V).pt r).horizon)
  /-- **P-WEAK-AV-SAFE.** Under the weak-continuation premise (healthy up to
  the heal point, sleepy after it, no recurrence after it): ready-reader
  safety of the confirmed output from the heal point. -/
  weakSafe : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds (WeakPremise pp gst k) fun r =>
    (chainTrace r.2).ReadySafe (gc r) gConfirmed (gHeal pp k gst r)
  /-- **P-WEAK-AV-SAFE, nesting conjunct.** Under the weak-continuation
  premise: from the heal point, every ready finalized read is a prefix of every
  ready confirmed read at the same time (`F_x ⪯ S_y`). -/
  weakCrossNest : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds (WeakPremise pp gst k) fun r =>
    ReadyNestedFrom r.2 (gc r) gFinalized gConfirmed (gHeal pp k gst r)
  /-- **P-WEAK-AV-INCLUDE.** Under the weak-continuation premise: every honest
  proposal released at `τ ≥ heal + 2` slots (`8Δ`) by a key ready at `τ` is in
  every ready confirmed read at every `t ∈ [τ + 6Δ, horizon]`. -/
  weakInclude : ∀ (k : ℕ+) (gst : Time), (Sys F V).Holds (WeakPremise pp gst k) fun r =>
    IncludesFrom r.2 (gc r) gConfirmed (gHeal pp k gst r + 8 * ((Sys F V).pt r).env.Δ) 6
  /-- **P-WEAK-AV-GROW.** Under the weak-continuation premise and one honest
  ready proposer per window of `k'` slots from the heal point: joint strict
  growth of the confirmed output from the heal point by `t + (4k' + 6)·Δ`. -/
  weakGrow : ∀ (k k' : ℕ+) (gst : Time), (Sys F V).Holds
    (fun r => WeakPremise pp gst k r ∧
      gProg pp .available k' (gHeal pp k gst r) ((Sys F V).pt r).horizon r)
    fun r => CrossGrowth r.2 (gc r) gConfirmed gConfirmed (gHeal pp k gst r) (4 * k' + 6)

/-- The Goldilocks extras: at every finite validator type. -/
def GoldilocksExtra (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], GoldilocksExtraAt F pp V

/-- **The Goldilocks target** at the pinned FG-SA numbers `pp`: the reviewed
bindings, acceptance (hence the L0 `Good`), and the extras. A reviewed target,
not a proof that FG-SA meets it; never weakened to fit FG-SA. -/
def GoldilocksTarget (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) : Prop :=
  GoldilocksBindings F ∧ Accepted F (goldilocksContract pp) ∧ GoldilocksExtra F pp

/-! ## §1: corollaries of `Accepted` (via `Good`)

In namespace `GoldilocksTarget`: for `h : GoldilocksTarget F pp`,
`h.confirmed_persists V …` etc. -/

namespace GoldilocksTarget

variable {F : ShapeFamily goldilocksSchema Info} {pp : FGSAParams}
  (h : GoldilocksTarget F pp) (V : Type) [Fintype V] [DecidableEq V]

include h

/-- **P-NV-LATE-GST.** The compiled Goldilocks family is a good protocol at the
pinned numbers (realizable at every `Δ`, every GST and arbitrarily late
outages). -/
theorem goldilocks_good : Good (Sys F V) (shapeProgress F V) (goldilocksContract pp) :=
  h.2.1.good V

/-- **N1 / P-ANY-NEST.** finalized ⪯ confirmed (= stable), every honest read,
every cut. -/
theorem nested (r : (Sys F V).Run) (hv : (Sys F V).Valid r) :
    ((Sys F V).trace r).Nested gFinalized gConfirmed :=
  (goldilocks_good h V).behaviour.nested .final .available gFinalized gConfirmed (by decide)
    rfl rfl r hv

/-- **N2 / P-ANY-FIN-MONO.** The finalized output never rolls back. -/
theorem finalized_monotone (r : (Sys F V).Run) (hv : (Sys F V).Valid r) :
    ((Sys F V).trace r).Monotone gFinalized 0 :=
  (goldilocks_good h V).behaviour.finalMonotone gFinalized rfl r hv

/-- **N3 / P-ANY-FIN-NONFRAMING** — for this family's `conflicts` predicate:
no honest validator is convicted by what the honest nodes saw. -/
theorem nonFraming (r : (Sys F V).Run) (hv : (Sys F V).Valid r) : (Sys F V).NonFraming r :=
  (goldilocks_good h V).behaviour.nonFraming r hv

/-- **N5 / P-ANY-FIN-ACCOUNTABLE, -LOCAL-EVIDENCE** — for this family's
`conflicts` predicate: two honest finalized reads are compatible, or their
joint views convict at least a third of all validators. -/
theorem finalized_accountable (r : (Sys F V).Run) (hv : (Sys F V).Valid r) :
    (Sys F V).AccountablySafe r (1 / 3) gFinalized 0 ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.finalAccountable gFinalized rfl r hv trivial

/-- **F1, F2 / P-ANY-FIN-SAFE.** With fewer than a third faulty, the finalized
output is safe, under any network and participation. -/
theorem finalized_safe_below_third (r : (Sys F V).Run) (hv : (Sys F V).Valid r)
    (hb : ((Sys F V).pt r).FaultsBelow (1 / 3)) :
    ((Sys F V).trace r).Safe gFinalized 0 ∨ (Sys F V).Excuse r :=
  ((goldilocks_good h V).final_agree (g := gFinalized) rfl r hv hb).imp
    (fun ha => Trace.safe_iff.mpr ⟨ha, finalized_monotone h V r hv⟩) id

/-- **A1 / P-SYNC-AV-SAFE, -MONO, -DYNAMIC.** Sleepy: ready-reader safety of the
confirmed (= stable) output, catch-up `18·Δ`. -/
theorem confirmed_safe_sleepy (r : (Sys F V).Run) (hv : (Sys F V).Valid r)
    (hs : (Sys F V).Sleepy (goldilocksContract pp) r) :
    ((Sys F V).trace r).ReadySafe (gc r) gConfirmed 0 ∨
      (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.sleepySafe .available gConfirmed (Or.inl rfl) rfl r hv hs

/-- **A1′ / P-SYNC-PREFIX.** Synchronous for deadlines up to `b` and ½-sleepy on
`[0, b]`: the past up to `b` is safe for ready confirmed readers, whatever
happens after `b`. -/
theorem confirmed_safe_sleepy_prefix (r : (Sys F V).Run) (hv : (Sys F V).Valid r) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ ((Sys F V).pt r).horizon)
    (hs : ((Sys F V).log r).SyncUntil ((Sys F V).pt r) b)
    (hθ : ((Sys F V).pt r).SleepyOn (1 / 2) (gc r) 0 b) :
    ((Sys F V).trace r).ReadySafeUpTo (gc r)
      gConfirmed 0 b ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).sleepySafe_prefix (cap := .available) (Or.inl rfl) rfl r hv hb0 hbh hs hθ

/-- **A4 / P-GST-AV-SAFE, -MONO.** Healthy from `gst` with one honest ready
proposer per window of `k` slots on `[ready, heal]`: ready-reader safety of
the confirmed output from the heal point
`max gst 0 + (29 + B_H^F(k))·Δ`. -/
theorem confirmed_safe_healed (k : ℕ+) (gst : Time) (r : (Sys F V).Run)
    (hv : (Sys F V).Valid r) (hH : (Sys F V).Healthy (goldilocksContract pp) gst r)
    (hp : gProg pp .available k
      (gReady gst r)
      (gHeal pp k gst r) r) :
    ((Sys F V).trace r).ReadySafe (gc r) gConfirmed
      (gHeal pp k gst r) ∨
      (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.healedSafe .available gConfirmed (Or.inl rfl) rfl k gst r hv
    ⟨hH, hp⟩

/-- **A4, prefix form.** The healed safety of the past: partially synchronous
with GST `gst` and healthy up to `b ≥ heal`, with the recurrence on
`[ready, heal]`: ready confirmed readers are safe at cuts in `[heal, b]`,
whatever happens after `b`. -/
theorem confirmed_safe_healed_prefix (k : ℕ+) (gst : Time) (r : (Sys F V).Run)
    (hv : (Sys F V).Valid r) {b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ ((Sys F V).pt r).horizon)
    (hs : ((Sys F V).log r).Delivers ((Sys F V).pt r)
      (fun a => max a gst + ((Sys F V).pt r).env.Δ) b)
    (hH : ((Sys F V).pt r).HealthyOn (1 / 3) gst b)
    (hp : gProg pp .available k
      (gReady gst r)
      (gHeal pp k gst r) r)
    (hhb : gHeal pp k gst r ≤ b) :
    ((Sys F V).trace r).ReadySafeUpTo (gc r)
      gConfirmed (gHeal pp k gst r) b ∨
      (Sys F V).Excuse r :=
  (goldilocks_good h V).healedSafe_prefix (cap := .available) (Or.inl rfl) rfl r hv k gst hb0 hbh
    hs hH hp hhb

/-- **A3 / P-OUT-CONTINUE** (stable retention; M14 closed: stable =
confirmed). In the outage regime, what a node ready at `T` reads as confirmed
(= stable) is kept by every eligible honest reader at every time from `b₀` to
the horizon. -/
theorem confirmed_persists (T b₀ b₁ : Time) (r : (Sys F V).Run) (hv : (Sys F V).Valid r)
    (hO : (Sys F V).Outage (goldilocksContract pp) T b₀ b₁ r) :
    ((Sys F V).trace r).ProtectedThrough (gc r)
      gConfirmed gConfirmed T b₀ b₁ ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.persists gConfirmed rfl T b₀ b₁ r hv hO

/-- **P-OUT-FIN-COMPAT** (for `ResilienceReader`-eligible readers). In the
outage regime, what a node ready at `T` reads as confirmed is compatible with
the finalized read of every eligible honest reader from `b₀` on. -/
theorem outage_final_compatible (T b₀ b₁ : Time) (r : (Sys F V).Run) (hv : (Sys F V).Valid r)
    (hO : (Sys F V).Outage (goldilocksContract pp) T b₀ b₁ r) {v w : V}
    (hvr : ((Sys F V).pt r).Ready (gc r) v T)
    (hwh : w ∈ ((Sys F V).pt r).honest) {t : Time} (ht : b₀ ≤ t)
    (hth : t ≤ ((Sys F V).pt r).horizon)
    (hr : ((Sys F V).trace r).ResilienceReader (gc r)
      b₀ b₁ w t) :
    Compatible (((Sys F V).trace r).readAt gConfirmed v T)
      (((Sys F V).trace r).readAt gFinalized w t) ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).persists_final_compatible (g := gConfirmed) (gf := gFinalized) rfl rfl r hv
    hO hvr hwh ht hth hr

/-- **Tx-level consequence of L3** (P-SYNC-AV-GROW; and of the
intended-but-unclaimed L8; intended-opus calls L8 "not claimed", this target
claims it: P-TX-SCOPE).
Sleepy with one honest ready proposer
per window of `k` slots: every submitted transaction is in every ready
confirmed read from `t + Δ + (4k + 6)·Δ` (not strict block growth: that is the
extra `growSleepy`). -/
theorem confirmed_txLive_sleepy (k : ℕ+) (r : (Sys F V).Run) (hv : (Sys F V).Valid r)
    (hs : (Sys F V).Sleepy (goldilocksContract pp) r)
    (hp : gProg pp .available k 0
      ((Sys F V).pt r).horizon r) :
    ((Sys F V).trace r).TxLive (gc r) gConfirmed 0
      (((4 * k + 6 : Nat) : Time) * ((Sys F V).pt r).env.Δ) ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.sleepyLive .available gConfirmed (Or.inl rfl) rfl k r hv
    ⟨hs, hp⟩

/-- **Tx-level consequence of L5.** Healthy from `gst` with the recurrence of
`k` from `ready`: every submitted transaction is in every ready confirmed
read from `max t heal + Δ + (4k + 6)·Δ`. -/
theorem confirmed_txLive_healed (k : ℕ+) (gst : Time) (r : (Sys F V).Run)
    (hv : (Sys F V).Valid r) (hH : (Sys F V).Healthy (goldilocksContract pp) gst r)
    (hp : gProg pp .available k
      (gReady gst r) ((Sys F V).pt r).horizon r) :
    ((Sys F V).trace r).TxLive (gc r) gConfirmed
      (gHeal pp k gst r)
      (((4 * k + 6 : Nat) : Time) * ((Sys F V).pt r).env.Δ) ∨ (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.healthyLive .available gConfirmed rfl k gst r hv ⟨hH, hp⟩

/-- **Tx-level consequence of FL1, FL2.** Healthy from `gst` with the finality
recurrence of `gf` from `ready`: every submitted transaction is in every
ready finalized read from `max t heal + Δ + latency`, with heal
`max gst 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ` and latency
`(4·gf·R + 6 + W_W(gf))·Δ` (not FL1's first-finality deadline, not FL2's
overtaking: those are the extras `finalFirst`, `finalRecur`). -/
theorem finalized_txLive (gf : ℕ+) (gst : Time) (r : (Sys F V).Run)
    (hv : (Sys F V).Valid r) (hH : (Sys F V).Healthy (goldilocksContract pp) gst r)
    (hp : gProg pp .final gf
      (gReady gst r) ((Sys F V).pt r).horizon r) :
    ((Sys F V).trace r).TxLive (gc r) gFinalized
      (gHealFin pp gf gst r)
      (((4 * (gf * pp.R) + 6 + pp.wW gf : Nat) : Time) * ((Sys F V).pt r).env.Δ) ∨
      (Sys F V).Excuse r :=
  (goldilocks_good h V).behaviour.healthyLive .final gFinalized rfl gf gst r hv ⟨hH, hp⟩

end GoldilocksTarget

end Shape

end Consensus

end
