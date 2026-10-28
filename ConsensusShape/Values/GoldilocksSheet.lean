module
public import ConsensusShape.Values.Goldilocks
public import Mathlib.Tactic

@[expose] public section

/-! # The Goldilocks properties sheet

**Round-model FG-SA, `Δ_F = Δ`, slow arming, `κ = 2`.** `GoldilocksTarget F pp`
is a *reviewed target*, not a proof that FG-SA meets it: the reviewed bindings
(`GoldilocksBindings`: the skeleton), acceptance at the pinned numbers
(`Accepted F (goldilocksContract pp)`, which gives the L0 `Good`), and the
Goldilocks-specific extras (`GoldilocksExtra`). It states Goldilocks'
**intended** properties (`intended-opus.md` / `intended-astra.md` ids), not only
what FG-SA proves today. A failed FG-SA feasibility gate or migration
obligation leaves this target unproved and goes back to Francesco; the target
is never changed to fit FG-SA.

**OD-23 (answered by Francesco, 2026-10-28).** The fixed regimes are the
definition; Goldilocks pins only numbers: the outage regime is η-sleepy, with
Goldilocks' look-back `η = eta` (`FGSAParams.params`); the healthy regime is a
fixed set of more than ⅔ of all validators, honest and continuously awake from
`max g 0` (no churn). FG-SA's current recovery proof assumes every honest
validator awake: obligation (1) below.

Every §1 theorem (namespace `GoldilocksTarget`) takes `h : GoldilocksTarget F pp`
and a finite validator type `V`;
the system is `gSys F V` (the compiled family), the excuse is an observed hash
collision (`HC`), the catch-up is `c = 18·Δ`, the heal points are
`max g 0 + (29 + B_H^F(k))·Δ` (available, stable) and
`max g 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ` (final). Stable is aliased to
confirmed by the schema, so every stable row is a confirmed row. Non-framing
and accountability are **for this family's `conflicts` predicate** until the
E1/E2 evidence binding exists (obligation (7)).

## §1 From `Accepted` (corollaries of `Good`, proved here)

* N1 / P-ANY-NEST: `nested` (finalized ⪯ confirmed = stable, every honest
  read, every cut).
* N2 / P-ANY-FIN-MONO: `finalized_monotone`.
* N3 / P-ANY-FIN-NONFRAMING: `nonFraming`, for this family's `conflicts`.
* N5 / P-ANY-FIN-ACCOUNTABLE, -LOCAL-EVIDENCE: `finalized_accountable` (joint
  views convict ≥ n/3 under this family's `conflicts`, ∨ HC).
* F1, F2 / P-ANY-FIN-SAFE: `finalized_safe_below_third` (any network).
* A1 / P-SYNC-AV-SAFE, -MONO, -DYNAMIC: `confirmed_safe_sleepy`.
* A1′ / P-SYNC-PREFIX: `confirmed_safe_sleepy_prefix`.
* A4 / P-GST-AV-SAFE, -MONO: `confirmed_safe_healed`,
  `confirmed_safe_healed_prefix`.
* A3 / P-OUT-CONTINUE (stable retention), P-OUT-FIN-COMPAT:
  `confirmed_persists` (stable = confirmed: M14 closed),
  `outage_final_compatible` (for `ResilienceReader`-eligible readers).
* Tx-level consequence of L3, L8: `confirmed_txLive_sleepy` (latency
  `(4k+6)·Δ`; not strict block growth).
* Tx-level consequence of L5: `confirmed_txLive_healed`.
* Tx-level consequence of FL1, FL2: `finalized_txLive` (every submitted
  transaction finalized by `max t heal + Δ + latency`; not FL1's
  first-finality deadline, not FL2's overtaking).
* P-NV-LATE-GST: `GoldilocksTarget.goldilocks_good` (realizable at every `Δ`,
  every GST and arbitrarily late outages).
* Numbers: `reference_bounds`, `goldilocks_admissible`, `budget_implies_V`,
  `range_head` (with the span loss), `EnvPoint.two_mul_card_faulty_union_lt`.

## §2 From the extras (`GoldilocksExtra` fields; statements only)

* L1 / P-SYNC-AV-INCLUDE: `includeSleepy`.
* L4 / P-GST-AV-INCLUDE: `includeHealed`.
* L3, L8 / P-SYNC-AV-GROW (block level): `growSleepy`.
* L5 / P-GST-AV-GROW (block level): `growHealed`.
* FL1 / P-GST-FIN-FIRST: `finalFirst`.
* FL2 / P-GST-FIN-RECUR: `finalRecur`.
* FL5: `liveDC`.
* A4 part / P-GST-CROSS-NEST: `crossNest`.
* A2 / P-OUT-AV-SLOW: `outageWindow` (no post-window network).
* P-WEAK-AV-SAFE: `weakSafe` (no suffix recurrence).
* P-WEAK-AV-INCLUDE: `weakInclude` (every qualifying honest proposal,
  persistent).
* P-WEAK-AV-GROW: `weakGrow` (suffix recurrence `k'`).

## §3 Not yet stated (with reason)

* A6 / P-WEAK-CORRUPTION: static adversary (the definition's scope).
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
* P-NEW-*: the fast path is not in the Lean model.
* K1–K5 / P-LEAK-*: leak accounting (optional extra).
* E1/E2 `conflicts` binding: needs an evidence block (migration step 0;
  obligation (7)).
* P-OUT-DUTY-EXTEND, P-OUT-LEASE: protocol-internal.
* P-OUT-PROGRESS-LIMIT, A2-limit, A7, L7, N7, FL-neg, FL-scope: negative or
  not-claimed facts, consistent with the sheet.

## Migration obligations

Each is a gate the FG-SA migration must pass **against this unchanged
target**; a failure leaves `GoldilocksTarget` unproved and goes back to
Francesco.

1. Healthy regime (a fixed set of more than ⅔ of all validators, honest and
   continuously awake from `max g 0`, no churn) vs FG-SA Recovery₂ (every
   honest validator awake, no restart after GST): prove FG-SA's recovery from
   the ⅔-continuous condition.
2. GST shift to `max g 0` plus catch-up (gate F-1).
3. `Ready` at catch-up `18·Δ` ⇒ joined / confirmed reader; ready at `b₀` and
   awake ⇒ covered (F-3).
4. Outage continuation under η-sleepy participation (`η = eta`) throughout
   and cover ½ at `b₀`, partially synchronous with GST `b₁` after the window,
   vs FG-SA `OutageE` and its after-window premise (F-4).
5. Readers caught up after the window (FG-SA proves repair-ready readers only).
6. Ready-vs-awake counting (M25).
7. E1/E2 evidence binding (`conflicts` = FG-SA's slashing rule).
8. Hash/digest (F-7); relay of accepted objects across sleep (F-8);
   receipt-to-processing under endpoint delivery (F-9: FG-SA timing assumed
   receipt strictly before the deadline; endpoint receipt costs one time
   unit, at most `Δ`, absorbed by the `Δ`-rounded numbers or re-proved).
9. Finality liveness under the ⅔-continuous healthy regime vs FG-SA's
   all-awake premise.
10. Weak continuation: uniform cut/seed preservation.
11. FL1/FL2 block-level forms (`finalFirst`, `finalRecur`) vs FG-SA's
    `FinalityLivenessGSTClaim_W`.
12. Prefix forms: FG-SA's `CleanPrefixTruncation` matches `Adequate.prefixClosed`
    on the FG-SA run model. -/

namespace Consensus

namespace Blocks

/-- A pattern's span is at most any bound on its offsets. -/
theorem Pattern.span_le {P : Pattern} {b : Nat} (h : ∀ j ∈ P.offsets, j ≤ b) : P.span ≤ b := by
  unfold Pattern.span
  generalize P.offsets = l at h ⊢
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- `n` consecutive slots span `n − 1`. -/
theorem Pattern.span_range (n : ℕ+) : (Pattern.range n).span = n - 1 :=
  le_antisymm (Pattern.span_le fun j hj => by
      have := List.mem_range.mp hj; omega)
    (Pattern.le_span (List.mem_range.mpr (by have := n.pos; omega)))

end Blocks

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] {p : EnvPoint V}

/-- If every validator ready at `t` is in an honest set `C`, and `W` avoids
`C`, then more than half of all validators ready gives `2·|faulty ∪ W| < n`
(the outage cover at `b₀` with `cover = ½` gives FG-SA's `OutageE1`: faulty
validators and uncovered wakers are fewer than half). -/
theorem two_mul_card_faulty_union_lt {c t : Time} {C W : Finset V}
    (hR : p.readyAt c t ⊆ C) (hC : C ⊆ p.honest) (hW : Disjoint W C)
    (h : p.ReadyOfAll (1 / 2) c t) : 2 * (p.faulty ∪ W).card < Fintype.card V := by
  have hdis : Disjoint (p.faulty ∪ W) C := by
    refine Finset.disjoint_union_left.mpr ⟨?_, hW⟩
    refine Finset.disjoint_left.mpr fun v hv hvC => ?_
    exact (Finset.mem_sdiff.mp hv).2 (hC hvC)
  have hsum : (p.faulty ∪ W).card + C.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hRC : (p.readyAt c t).card ≤ C.card := Finset.card_le_card hR
  have h' : (Fintype.card V : ℚ) < 2 * (p.readyAt c t).card := by
    unfold ReadyOfAll at h; linarith
  have h'' : Fintype.card V < 2 * (p.readyAt c t).card := by exact_mod_cast h'
  omega

end EnvPoint

namespace Shape

open Blocks
open Consensus.Model (pubOf sysOf)

/-! ## Numbers -/

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

/-- Head extraction for the finality recurrence: `3R + κ` consecutive honest
ready proposers in every window of `gf·R` slots give one honest ready
proposer in every window of `gf·R` slots, losing the pattern's span
`3R + 1` slots at the end of the window. -/
theorem range_head (pp : FGSAParams) (gf : ℕ+) {V R : Type} [Fintype V] {p : EnvPoint V}
    {key : Fin (Fintype.card V) ≃ V} {sel : R → Finset (Fin (Fintype.card V))}
    {lead : Slot → R} {G : TimeGrid} {c start stop : Time}
    (h : PatternRecurrence p key sel lead G (pp.finRec gf) c start stop) :
    PatternRecurrence p key sel lead G ⟨Pattern.single, (pp.finRec gf).gap⟩ c start
      (min stop p.horizon - ((3 * pp.R + 1 : Nat) : Time) * G.slotLen p.env.Δ) := by
  have hspan : (pp.finRec gf).pattern.span = 3 * pp.R + 1 := by
    refine (Pattern.span_range
      (⟨3 * pp.R + FGSAParams.κ, by unfold FGSAParams.κ; omega⟩ : ℕ+)).trans ?_
    change 3 * pp.R + FGSAParams.κ - 1 = _
    unfold FGSAParams.κ; omega
  have h0 : 0 ∈ (pp.finRec gf).pattern.offsets :=
    List.mem_range.mpr (by simp [FGSAParams.κ])
  have := PatternRecurrence.single_of_zero h0 h
  rwa [hspan] at this

/-! ## Bindings, chain-level vocabulary, extras, target -/

variable {Info : Type} [DecidableEq Info] [Encodable Info]

/-- The confirmed output (available and stable). -/
abbrev gConfirmed : goldilocksSchema.Id := GOut.confirmed

/-- The finalized output (final). -/
abbrev gFinalized : goldilocksSchema.Id := GOut.finalized

/-- The compiled Goldilocks system at validators `V`. -/
abbrev gSys (F : ShapeFamily goldilocksSchema Info) (V : Type) [Fintype V] [DecidableEq V] :
    System V :=
  sysOf goldilocksSchema (compiled F) V

/-- The reviewed bindings: the Goldilocks skeleton (grid of `4·Δ` slots, one
proposer per slot). The E1/E2 `conflicts` binding is obligation (7). -/
structure GoldilocksBindings (F : ShapeFamily goldilocksSchema Info) : Prop where
  skel : ∀ pub, (F pub).skel = goldilocksSkeleton pub.n

section Vocabulary

variable {O : OutputSchema} {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

/-- Persistent inclusion: header `h` is in the `g`-read of every node ready at
every time of `[d, horizon]`. -/
def ServedFrom (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (h : Header Info)
    (d : Time) : Prop :=
  ∀ t, d ≤ t → t ≤ rho.horizon → InBy rho c g h t

/-- Inclusion of honest proposals from `start`: every honest proposal released
at `τ ≥ start` by a key ready at `τ` is served (persistently) from
`τ + D·Δ`. -/
def IncludesFrom (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time)
    (D : Nat) : Prop :=
  ∀ τ k h, start ≤ τ → rho.point.Ready c (rho.key k) τ → HonestProposal rho τ k h →
    ServedFrom rho c g h (τ + (D : Time) * E.Δ)

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

end Vocabulary

section Extras

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The weak-continuation premise at gap `k` after GST `gst`: partially
synchronous with GST `gst` (the whole run), healthy (a fixed set of more than
`φ·n` honest validators continuously awake) up to the heal point, one honest
ready proposer per window of `k` slots on `[readyFrom, heal]`, and sleepy
participation from the heal point to the horizon. No recurrence after the
heal point. -/
def WeakPremise {F : ShapeFamily goldilocksSchema Info} (pp : FGSAParams)
    (rho : Model.Run (compiled F) E) (gst : Time) (k : ℕ+) : Prop :=
  CommLog.PSync rho.point rho.log gst ∧
    rho.point.HealthyOn (goldilocksContract pp).params.φ gst
      (shapeHeal (goldilocksContract pp) rho .available k gst) ∧
    ShapeProg (goldilocksContract pp) rho .available k
      (shapeReady (goldilocksContract pp) rho gst)
      (shapeHeal (goldilocksContract pp) rho .available k gst) ∧
    rho.point.SleepyOn (goldilocksContract pp).params.θ (shapeC (goldilocksContract pp) rho)
      (shapeHeal (goldilocksContract pp) rho .available k gst) rho.horizon

end Extras

/-- The Goldilocks extras: intended properties beyond the fixed L0 table
(statements; FG-SA's migration proves them). Every claim is on every valid
run of the compiled family, for every finite validator set and environment,
"or an observed hash collision". Regimes are the L0 ones at the pinned
numbers (`ShapeSleepy`, `ShapeHealthy`, `ShapeProg` at
`goldilocksContract pp`); `c = 18·Δ`; heal points from `max g 0`. -/
structure GoldilocksExtra (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) : Prop where
  /-- **L1 / P-SYNC-AV-INCLUDE.** Sleepy: every honest proposal released at
  `τ` by a key ready at `τ` is in every ready confirmed read at every
  `t ∈ [τ + 6Δ, horizon]`. -/
  includeSleepy : AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeSleepy (goldilocksContract pp) rho →
    IncludesFrom rho (shapeC (goldilocksContract pp) rho) gConfirmed 0 6 ∨ rho.HashCollision
  /-- **L4 / P-GST-AV-INCLUDE.** Healthy from `gst` with one honest ready
  proposer per window of `k` slots on `[readyFrom, heal]`: the same for
  proposals released at `τ ≥ heal`. -/
  includeHealed : ∀ (k : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .available k (shapeReady (goldilocksContract pp) rho gst)
      (shapeHeal (goldilocksContract pp) rho .available k gst) →
    IncludesFrom rho (shapeC (goldilocksContract pp) rho) gConfirmed
      (shapeHeal (goldilocksContract pp) rho .available k gst) 6 ∨ rho.HashCollision
  /-- **L3, L8 / P-SYNC-AV-GROW** (block level). Sleepy with one honest ready
  proposer per window of `k` slots: joint strict growth of the confirmed
  output by `t + (4k + 6)·Δ`. -/
  growSleepy : ∀ k : ℕ+, AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeSleepy (goldilocksContract pp) rho →
    ShapeProg (goldilocksContract pp) rho .available k 0 rho.horizon →
    CrossGrowth rho (shapeC (goldilocksContract pp) rho) gConfirmed gConfirmed 0 (4 * k + 6) ∨
      rho.HashCollision
  /-- **L5 / P-GST-AV-GROW** (block level). Healthy from `gst` with the
  recurrence of `k` from `readyFrom`: joint strict growth from the heal
  point. -/
  growHealed : ∀ (k : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .available k (shapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    CrossGrowth rho (shapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      (shapeHeal (goldilocksContract pp) rho .available k gst) (4 * k + 6) ∨ rho.HashCollision
  /-- **FL1 / P-GST-FIN-FIRST.** Healthy from `gst` with the finality
  recurrence of `gf` on `[readyFrom, heal]`: a new finalized entry, above the
  finalized read of every honest node at `max gst 0`, is in every ready
  finalized read at the first-finality point
  `max gst 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ`. -/
  finalFirst : ∀ (gf : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .final gf (shapeReady (goldilocksContract pp) rho gst)
      (shapeHeal (goldilocksContract pp) rho .final gf gst) →
    shapeHeal (goldilocksContract pp) rho .final gf gst ≤ rho.horizon →
    (∃ h, NewAbove rho (shapeC (goldilocksContract pp) rho) gFinalized gFinalized
      (· ∈ rho.honest) (max gst 0) (shapeHeal (goldilocksContract pp) rho .final gf gst) h) ∨
      rho.HashCollision
  /-- **FL2 / P-GST-FIN-RECUR.** Healthy from `gst` with the finality
  recurrence of `gf` from `readyFrom`: for every `t` from the first-finality
  point, a new finalized entry at `t + (W_W(gf) + 4·gf·R)·Δ` above every
  ready confirmed read at `t`. -/
  finalRecur : ∀ (gf : ℕ+) (gst : Time), AllRuns F fun E rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .final gf (shapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    (∀ t, shapeHeal (goldilocksContract pp) rho .final gf gst ≤ t →
      t + ((pp.wW gf + 4 * (gf * pp.R) : Nat) : Time) * E.Δ ≤ rho.horizon →
      ∃ h, NewAbove rho (shapeC (goldilocksContract pp) rho) gConfirmed gFinalized
        (fun x => rho.point.Ready (shapeC (goldilocksContract pp) rho) x t) t
        (t + ((pp.wW gf + 4 * (gf * pp.R) : Nat) : Time) * E.Δ) h) ∨ rho.HashCollision
  /-- **FL5** (LiveDC). Healthy from `gst` with the finality recurrence of
  `gf` from `readyFrom`: for every `t` from the first-finality point, an
  honest proposal released after `t` strictly extends every ready confirmed
  read at `t` and is in every ready finalized read by
  `t + (2·W_W(gf) + 4·gf·R)·Δ`. -/
  liveDC : ∀ (gf : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .final gf (shapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    CrossGrowth rho (shapeC (goldilocksContract pp) rho) gConfirmed gFinalized
      (shapeHeal (goldilocksContract pp) rho .final gf gst) (2 * pp.wW gf + 4 * (gf * pp.R)) ∨
      rho.HashCollision
  /-- **A4 part / P-GST-CROSS-NEST.** Healthy from `gst` with the recurrence of
  `k` on `[readyFrom, heal]`: from the heal point, every ready finalized read
  is a prefix of every ready confirmed read at the same time. -/
  crossNest : ∀ (k : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    ShapeHealthy (goldilocksContract pp) rho gst →
    ShapeProg (goldilocksContract pp) rho .available k (shapeReady (goldilocksContract pp) rho gst)
      (shapeHeal (goldilocksContract pp) rho .available k gst) →
    (∀ t, shapeHeal (goldilocksContract pp) rho .available k gst ≤ t → t ≤ rho.horizon →
      ∀ x y, rho.point.Ready (shapeC (goldilocksContract pp) rho) x t →
        rho.point.Ready (shapeC (goldilocksContract pp) rho) y t →
        (chainTrace rho).readAt gFinalized x t <+: (chainTrace rho).readAt gConfirmed y t) ∨
      rho.HashCollision
  /-- **A2 / P-OUT-AV-SLOW.** Outage times, synchronous for deadlines up to
  `b₀`, η-sleepy on `[0, b₁ − 1]`, more than half ready at `b₀`, and **no**
  network assumption after `b₀`: what a node ready at `T` reads as confirmed
  is kept by every eligible reader at every time of `[b₀, b₁)` within the
  horizon. -/
  outageWindow : ∀ T b₀ b₁ : Time, AllRuns F fun E rho => rho.ExecutionValid →
    OutageTimes (goldilocksContract pp).params E.Δ T b₀ b₁ →
    CommLog.SyncUntil rho.point rho.log b₀ →
    rho.point.EtaSleepyOn (goldilocksContract pp).params.θ
      ((goldilocksContract pp).params.ηDur E.Δ) (shapeC (goldilocksContract pp) rho) 0 (b₁ - 1) →
    rho.point.ReadyOfAll (goldilocksContract pp).params.cover
      (shapeC (goldilocksContract pp) rho) b₀ →
    (chainTrace rho).ProtectedUpTo (shapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      T b₀ b₁ (min (b₁ - 1) rho.horizon) ∨ rho.HashCollision
  /-- **P-WEAK-AV-SAFE.** Under the weak-continuation premise (healthy up to
  the heal point, sleepy after it, no recurrence after it): ready-reader
  safety of the confirmed output from the heal point. -/
  weakSafe : ∀ (k : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    WeakPremise pp rho gst k →
    (chainTrace rho).ReadySafe (shapeC (goldilocksContract pp) rho) gConfirmed
      (shapeHeal (goldilocksContract pp) rho .available k gst) ∨ rho.HashCollision
  /-- **P-WEAK-AV-INCLUDE.** Under the weak-continuation premise: every honest
  proposal released at `τ ≥ heal + 2` slots (`8Δ`) by a key ready at `τ` is in
  every ready confirmed read at every `t ∈ [τ + 6Δ, horizon]`. -/
  weakInclude : ∀ (k : ℕ+) (gst : Time), AllRuns F fun E rho => rho.ExecutionValid →
    WeakPremise pp rho gst k →
    IncludesFrom rho (shapeC (goldilocksContract pp) rho) gConfirmed
      (shapeHeal (goldilocksContract pp) rho .available k gst + 8 * E.Δ) 6 ∨ rho.HashCollision
  /-- **P-WEAK-AV-GROW.** Under the weak-continuation premise and one honest
  ready proposer per window of `k'` slots from the heal point: joint strict
  growth of the confirmed output from the heal point by `t + (4k' + 6)·Δ`. -/
  weakGrow : ∀ (k k' : ℕ+) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
    WeakPremise pp rho gst k →
    ShapeProg (goldilocksContract pp) rho .available k'
      (shapeHeal (goldilocksContract pp) rho .available k gst) rho.horizon →
    CrossGrowth rho (shapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      (shapeHeal (goldilocksContract pp) rho .available k gst) (4 * k' + 6) ∨ rho.HashCollision

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
theorem goldilocks_good : Good (gSys F V) (shapeProgress F V) (goldilocksContract pp) :=
  h.2.1.good V

/-- **N1 / P-ANY-NEST.** finalized ⪯ confirmed (= stable), every honest read,
every cut. -/
theorem nested (r : (gSys F V).Run) (hv : (gSys F V).Valid r) :
    ((gSys F V).trace r).Nested gFinalized gConfirmed :=
  (goldilocks_good h V).behaviour.nested .final .available gFinalized gConfirmed (by decide)
    rfl rfl r hv

/-- **N2 / P-ANY-FIN-MONO.** The finalized output never rolls back. -/
theorem finalized_monotone (r : (gSys F V).Run) (hv : (gSys F V).Valid r) :
    ((gSys F V).trace r).Monotone gFinalized 0 :=
  (goldilocks_good h V).behaviour.finalMonotone gFinalized rfl r hv

/-- **N3 / P-ANY-FIN-NONFRAMING** — for this family's `conflicts` predicate:
no honest validator is convicted by what the honest nodes saw. -/
theorem nonFraming (r : (gSys F V).Run) (hv : (gSys F V).Valid r) : (gSys F V).NonFraming r :=
  (goldilocks_good h V).behaviour.nonFraming r hv

/-- **N5 / P-ANY-FIN-ACCOUNTABLE, -LOCAL-EVIDENCE** — for this family's
`conflicts` predicate: two honest finalized reads are compatible, or their
joint views convict at least a third of all validators. -/
theorem finalized_accountable (r : (gSys F V).Run) (hv : (gSys F V).Valid r) :
    (gSys F V).AccountablySafe r (1 / 3) gFinalized 0 ∨ (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.final gFinalized rfl).accountable r hv trivial

/-- **F1, F2 / P-ANY-FIN-SAFE.** With fewer than a third faulty, the finalized
output is safe, under any network and participation. -/
theorem finalized_safe_below_third (r : (gSys F V).Run) (hv : (gSys F V).Valid r)
    (hb : ((gSys F V).pt r).FaultsBelow (1 / 3)) :
    ((gSys F V).trace r).Safe gFinalized 0 ∨ (gSys F V).Excuse r :=
  ((goldilocks_good h V).final_agree (g := gFinalized) rfl r hv hb).imp
    (fun ha => ⟨ha, finalized_monotone h V r hv⟩) id

/-- **A1 / P-SYNC-AV-SAFE, -MONO, -DYNAMIC.** Sleepy: ready-reader safety of the
confirmed (= stable) output, catch-up `18·Δ`. -/
theorem confirmed_safe_sleepy (r : (gSys F V).Run) (hv : (gSys F V).Valid r)
    (hs : (gSys F V).Sleepy (goldilocksContract pp) r) :
    ((gSys F V).trace r).ReadySafe (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) gConfirmed 0 ∨
      (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.da .available gConfirmed (Or.inl rfl) rfl).sleepySafe r hv hs

/-- **A1′ / P-SYNC-PREFIX.** Synchronous for deadlines up to `b` and ½-sleepy on
`[0, b]`: the past up to `b` is safe for ready confirmed readers, whatever
happens after `b`. -/
theorem confirmed_safe_sleepy_prefix (r : (gSys F V).Run) (hv : (gSys F V).Valid r) {b : Time}
    (hb0 : 0 ≤ b) (hbh : b ≤ ((gSys F V).pt r).horizon)
    (hs : ((gSys F V).log r).SyncUntil ((gSys F V).pt r) b)
    (hθ : ((gSys F V).pt r).SleepyOn (1 / 2) (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) 0 b) :
    ((gSys F V).trace r).ReadySafeUpTo (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      gConfirmed 0 b ∨ (gSys F V).Excuse r :=
  (goldilocks_good h V).sleepySafe_prefix (cap := .available) (Or.inl rfl) rfl r hv hb0 hbh hs hθ

/-- **A4 / P-GST-AV-SAFE, -MONO.** Healthy from `gst` with one honest ready
proposer per window of `k` slots on `[readyFrom, heal]`: ready-reader safety of
the confirmed output from the heal point
`max gst 0 + (29 + B_H^F(k))·Δ`. -/
theorem confirmed_safe_healed (k : ℕ+) (gst : Time) (r : (gSys F V).Run)
    (hv : (gSys F V).Valid r) (hH : (gSys F V).Healthy (goldilocksContract pp) gst r)
    (hp : (gSys F V).prog (shapeProgress F V) (goldilocksContract pp) .available k
      ((gSys F V).ready (goldilocksContract pp) gst r)
      ((gSys F V).heal (goldilocksContract pp) .available k gst r) r) :
    ((gSys F V).trace r).ReadySafe (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) gConfirmed
      (max gst 0 + ((29 + pp.bhf k : Nat) : Time) * ((gSys F V).pt r).env.Δ) ∨
      (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.da .available gConfirmed (Or.inl rfl) rfl).healedSafe k gst r hv
    ⟨hH, hp⟩

/-- **A4, prefix form.** The healed safety of the past: partially synchronous
with GST `gst` and healthy up to `b ≥ heal`, with the recurrence on
`[readyFrom, heal]`: ready confirmed readers are safe at cuts in `[heal, b]`,
whatever happens after `b`. -/
theorem confirmed_safe_healed_prefix (k : ℕ+) (gst : Time) (r : (gSys F V).Run)
    (hv : (gSys F V).Valid r) {b : Time} (hb0 : 0 ≤ b) (hbh : b ≤ ((gSys F V).pt r).horizon)
    (hs : ((gSys F V).log r).Delivers ((gSys F V).pt r)
      (fun a => max a gst + ((gSys F V).pt r).env.Δ) b)
    (hH : ((gSys F V).pt r).HealthyOn (2 / 3) gst b)
    (hp : (gSys F V).prog (shapeProgress F V) (goldilocksContract pp) .available k
      ((gSys F V).ready (goldilocksContract pp) gst r)
      ((gSys F V).heal (goldilocksContract pp) .available k gst r) r)
    (hhb : max gst 0 + ((29 + pp.bhf k : Nat) : Time) * ((gSys F V).pt r).env.Δ ≤ b) :
    ((gSys F V).trace r).ReadySafeUpTo (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      gConfirmed (max gst 0 + ((29 + pp.bhf k : Nat) : Time) * ((gSys F V).pt r).env.Δ) b ∨
      (gSys F V).Excuse r :=
  (goldilocks_good h V).healedSafe_prefix (cap := .available) (Or.inl rfl) rfl r hv k gst hb0 hbh
    hs hH hp hhb

/-- **A3 / P-OUT-CONTINUE** (stable retention; M14 closed: stable =
confirmed). In the outage regime, what a node ready at `T` reads as confirmed
(= stable) is kept by every eligible honest reader at every time from `b₀` to
the horizon. -/
theorem confirmed_persists (T b₀ b₁ : Time) (r : (gSys F V).Run) (hv : (gSys F V).Valid r)
    (hO : (gSys F V).Outage (goldilocksContract pp) T b₀ b₁ r) :
    ((gSys F V).trace r).ProtectedThrough (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      gConfirmed gConfirmed T b₀ b₁ ∨ (gSys F V).Excuse r :=
  (goldilocks_good h V).behaviour.persists gConfirmed rfl T b₀ b₁ r hv hO

/-- **P-OUT-FIN-COMPAT** (for `ResilienceReader`-eligible readers). In the
outage regime, what a node ready at `T` reads as confirmed is compatible with
the finalized read of every eligible honest reader from `b₀` on. -/
theorem outage_final_compatible (T b₀ b₁ : Time) (r : (gSys F V).Run) (hv : (gSys F V).Valid r)
    (hO : (gSys F V).Outage (goldilocksContract pp) T b₀ b₁ r) {v w : V}
    (hvr : ((gSys F V).pt r).Ready (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) v T)
    (hwh : w ∈ ((gSys F V).pt r).honest) {t : Time} (ht : b₀ ≤ t)
    (hth : t ≤ ((gSys F V).pt r).horizon)
    (hr : ((gSys F V).trace r).ResilienceReader (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      b₀ b₁ w t) :
    Compatible (((gSys F V).trace r).readAt gConfirmed v T)
      (((gSys F V).trace r).readAt gFinalized w t) ∨ (gSys F V).Excuse r :=
  (goldilocks_good h V).persists_final_compatible (g := gConfirmed) (gf := gFinalized) rfl rfl r hv
    hO hvr hwh ht hth hr

/-- **Tx-level consequence of L3, L8.** Sleepy with one honest ready proposer
per window of `k` slots: every submitted transaction is in every ready
confirmed read from `t + Δ + (4k + 6)·Δ` (not strict block growth: that is the
extra `growSleepy`). -/
theorem confirmed_txLive_sleepy (k : ℕ+) (r : (gSys F V).Run) (hv : (gSys F V).Valid r)
    (hs : (gSys F V).Sleepy (goldilocksContract pp) r)
    (hp : (gSys F V).prog (shapeProgress F V) (goldilocksContract pp) .available k 0
      ((gSys F V).pt r).horizon r) :
    ((gSys F V).trace r).TxLive (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) gConfirmed 0
      (((4 * k + 6 : Nat) : Time) * ((gSys F V).pt r).env.Δ) ∨ (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.da .available gConfirmed (Or.inl rfl) rfl).sleepyLive k r hv
    ⟨hs, hp⟩

/-- **Tx-level consequence of L5.** Healthy from `gst` with the recurrence of
`k` from `readyFrom`: every submitted transaction is in every ready confirmed
read from `max t heal + Δ + (4k + 6)·Δ`. -/
theorem confirmed_txLive_healed (k : ℕ+) (gst : Time) (r : (gSys F V).Run)
    (hv : (gSys F V).Valid r) (hH : (gSys F V).Healthy (goldilocksContract pp) gst r)
    (hp : (gSys F V).prog (shapeProgress F V) (goldilocksContract pp) .available k
      ((gSys F V).ready (goldilocksContract pp) gst r) ((gSys F V).pt r).horizon r) :
    ((gSys F V).trace r).TxLive (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) gConfirmed
      (max gst 0 + ((29 + pp.bhf k : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      (((4 * k + 6 : Nat) : Time) * ((gSys F V).pt r).env.Δ) ∨ (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.da .available gConfirmed (Or.inl rfl) rfl).healedLive k gst r hv
    ⟨hH, hp⟩

/-- **Tx-level consequence of FL1, FL2.** Healthy from `gst` with the finality
recurrence of `gf` from `readyFrom`: every submitted transaction is in every
ready finalized read from `max t heal + Δ + latency`, with heal
`max gst 0 + (29 + B_H^F(gf·R) + W_W(gf))·Δ` and latency
`(4·gf·R + 6 + W_W(gf))·Δ` (not FL1's first-finality deadline, not FL2's
overtaking: those are the extras `finalFirst`, `finalRecur`). -/
theorem finalized_txLive (gf : ℕ+) (gst : Time) (r : (gSys F V).Run)
    (hv : (gSys F V).Valid r) (hH : (gSys F V).Healthy (goldilocksContract pp) gst r)
    (hp : (gSys F V).prog (shapeProgress F V) (goldilocksContract pp) .final gf
      ((gSys F V).ready (goldilocksContract pp) gst r) ((gSys F V).pt r).horizon r) :
    ((gSys F V).trace r).TxLive (((18 : Nat) : Time) * ((gSys F V).pt r).env.Δ) gFinalized
      (max gst 0 + ((29 + pp.bhf (gf * pp.R) + pp.wW gf : Nat) : Time) * ((gSys F V).pt r).env.Δ)
      (((4 * (gf * pp.R) + 6 + pp.wW gf : Nat) : Time) * ((gSys F V).pt r).env.Δ) ∨
      (gSys F V).Excuse r :=
  ((goldilocks_good h V).behaviour.final gFinalized rfl).live gf gst r hv ⟨hH, hp⟩

end GoldilocksTarget

/-! ## §2: the extras, as stated by the target (projections) -/

/-- The extras of a target. -/
theorem GoldilocksTarget.extra {F : ShapeFamily goldilocksSchema Info} {pp : FGSAParams}
    (h : GoldilocksTarget F pp) : GoldilocksExtra F pp :=
  h.2.2

/-- The bindings of a target. -/
theorem GoldilocksTarget.bindings {F : ShapeFamily goldilocksSchema Info} {pp : FGSAParams}
    (h : GoldilocksTarget F pp) : GoldilocksBindings F :=
  h.1

/-- A target's family has one proposer per slot, so the progress fits (the
bindings imply the `ProgressFits` part of acceptance). -/
theorem GoldilocksBindings.progressFits {F : ShapeFamily goldilocksSchema Info}
    (hb : GoldilocksBindings F) (pp : FGSAParams) : (goldilocksContract pp).ProgressFits F :=
  goldilocks_progressFits pp F fun pub => by rw [hb.skel pub]; rfl

end Shape

end Consensus

end
