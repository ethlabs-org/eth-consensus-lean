module
public import ConsensusShape.Values.Common

@[expose] public section

/-! # Goldilocks as a value (D-16, D-17)

The Goldilocks skeleton and contract: three outputs (`confirmed`, `stable`,
`finalized`) serving the available, resilient and final capabilities; slot
proposals by one selected key per slot on a grid of `4·Δ` slots; polling
disabled. The committee kinds `head`/`fin`, their phases and the finality
pattern are placeholders until the FG-SA migration fixes them.

The contract's named numbers are `GoldilocksParams`. Premises:
* available and resilient safety: the sleepy model `sleepy θ`;
* available and resilient liveness at gap `k`: `sleepy θ` and one honest
  ready proposer in every window of `k` slots from time 0;
* resilience (parameters `protectedAt`, `outageStart`, `outageEnd`): the
  pre-window arming (outage window, synchrony up to the outage start, `θ` and
  `η`-sleepy participation before it), `coverMajority` at the outage start (it
  gives FG-SA's outage bound once every ready validator is covered, D-17), and
  the post-window regime (partial synchrony, GST at most `restoreLag·Δ` after
  the outage end, participation above `afterAbove` from then on);
* recovery at gap `k` (also of the available output): partial synchrony,
  ready participation above `recoveryAbove` from GST (optionally full
  participation and no wakes), and recurrence from GST; escape `accFrac`;
* final: safety with escape `accFrac`, local accountability for `accFrac`,
  liveness under the recovery premise, `finalityReadyOfAll` participation
  from GST and recurrence of the finality pattern from GST.

`goldilocks_realizable` certifies non-vacuity for every family with the
skeleton's proposer selection size and grid. FG-SA migration obligations
(README): (i) a validator ready at the outage start is covered
(`OutageE1` then follows by `EnvPoint.two_mul_card_faulty_union_lt`); (ii)
persistence after the window for continuously awake readers under the
post-window terms. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public SelSpec pubOf)
open Consensus.Premise (sleepy fromGST after before outageWindow coverMajority)

/-- The Goldilocks output identifiers. -/
inductive GOut where
  | confirmed
  | stable
  | finalized
  deriving DecidableEq, Repr

/-- The Goldilocks schema: `confirmed` is available, `stable` resilient,
`finalized` final. -/
def goldilocksSchema : OutputSchema :=
  ⟨GOut, fun
    | .available => some .confirmed
    | .resilient => some .stable
    | .final => some .finalized⟩

/-- Placeholder committee kinds (the FG-SA migration fixes them). -/
inductive GKind where
  | head
  | fin
  deriving DecidableEq, Repr

/-- Slots of `4·Δ`. -/
def goldilocksGrid : TimeGrid := ⟨4, by decide⟩

/-- The Goldilocks skeleton: one proposer per slot, polling disabled, the two
placeholder committee kinds at phases 1 and 2, every key in each. -/
def goldilocksSkeleton (n : Nat) : Skeleton n where
  grid := goldilocksGrid
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := GKind
  decKind := inferInstance
  kinds := [.head, .fin]
  kinds_nodup := by decide
  kinds_complete := fun k => by cases k <;> simp
  phase := fun | .head => 1 | .fin => 2
  kindSel := fun _ => .all

/-- The named numbers of a Goldilocks instance (fractions default to the
standard values; durations are `Δ`-coefficients). -/
structure GoldilocksParams where
  /-- Readers' catch-up (shared by every claim, D-1). -/
  catchUp : Nat
  /-- The sleepy threshold `θ`. -/
  sleepyAbove : ℚ := 1 / 2
  /-- The `η` window of the pre-window participation. -/
  eta : Nat
  /-- The `η`-sleepy threshold before the outage. -/
  stableEtaAbove : ℚ
  /-- The arming lag between the protected read and the outage start. -/
  armingLag : Nat
  /-- The longest outage. -/
  outageBudget : Nat
  /-- After the outage, GST and participation from `outageEnd + restoreLag·Δ`. -/
  restoreLag : Nat
  /-- The participation threshold after the outage. -/
  afterAbove : ℚ := 1 / 2
  /-- The participation threshold of recovery. -/
  recoveryAbove : ℚ
  /-- Recovery assumes full participation from GST. -/
  recoveryFull : Bool
  /-- Recovery assumes no wakes from GST. -/
  noWakeAfterGST : Bool := true
  /-- The finality participation (fraction of all validators). -/
  finalityReadyOfAll : ℚ := 2 / 3
  /-- The accountable (and escape) fraction. -/
  accFrac : ℚ := 1 / 3
  /-- The finality pattern (placeholder until the FG-SA migration). -/
  finPattern : Pattern := Pattern.single
  /-- Latencies at gap `k`: confirmed and stable growth. -/
  growth : Affine
  stableGrowth : Affine
  /-- The recovery point after GST, and growth after it. -/
  recovery : Affine
  recGrowth : Affine
  /-- The finality start after GST, and the finality delay. -/
  finStart : Affine
  finDelay : Affine

/-- Ranges of the named numbers. -/
structure GoldilocksParams.WellFormed (P : GoldilocksParams) : Prop where
  catchUp_pos : 1 ≤ P.catchUp
  outageBudget_pos : 1 ≤ P.outageBudget
  sleepyAbove : 0 ≤ P.sleepyAbove ∧ P.sleepyAbove < 1
  stableEtaAbove : 0 ≤ P.stableEtaAbove ∧ P.stableEtaAbove < 1
  afterAbove : 0 ≤ P.afterAbove ∧ P.afterAbove < 1
  recoveryAbove : 0 ≤ P.recoveryAbove ∧ P.recoveryAbove < 1
  finalityReadyOfAll : 0 ≤ P.finalityReadyOfAll ∧ P.finalityReadyOfAll < 1
  accFrac : 0 < P.accFrac ∧ P.accFrac ≤ 1

/-- Standard Goldilocks numbers: default fractions (`θ = ½`, after-window
`½`, finality `⅔`, accountability `⅓`), no wakes after GST during recovery,
placeholder finality pattern. -/
def GoldilocksParams.standard (catchUp eta armingLag outageBudget restoreLag : Nat)
    (stableEtaAbove recoveryAbove : ℚ) (recoveryFull : Bool)
    (growth stableGrowth recovery recGrowth finStart finDelay : Affine) : GoldilocksParams where
  catchUp := catchUp
  eta := eta
  stableEtaAbove := stableEtaAbove
  armingLag := armingLag
  outageBudget := outageBudget
  restoreLag := restoreLag
  recoveryAbove := recoveryAbove
  recoveryFull := recoveryFull
  growth := growth
  stableGrowth := stableGrowth
  recovery := recovery
  recGrowth := recGrowth
  finStart := finStart
  finDelay := finDelay

/-- `A ∧ X` if `b`, else `X`. -/
def optConj {Prog : Type} (b : Bool) (A X : Premise Prog) : Premise Prog :=
  if b then .conj A X else X

namespace GoldilocksParams

variable (P : GoldilocksParams)

/-- One honest proposer in every window of `k` slots. -/
def headReq (k : ℕ+) : ProgressReq := ⟨Pattern.single, k⟩

/-- The finality pattern in every window of `k` slots. -/
def finReq (k : ℕ+) : ProgressReq := ⟨P.finPattern, k⟩

/-- Liveness of the available and resilient outputs at gap `k`. -/
def livePremise (k : ℕ+) : Premise ProgressReq :=
  .conj (sleepy P.sleepyAbove) (.progress (headReq k) .zero)

/-- Resilience: pre-window arming, the cover term, and the post-window
regime. -/
def resiliencePremise : Premise ProgressReq :=
  .conj (outageWindow P.armingLag P.outageBudget) <|
  .conj (.syncUntil .outageStart) <|
  .conj (before .outageStart (.readyAbove P.sleepyAbove)) <|
  .conj (before .outageStart (.etaSleepy P.stableEtaAbove P.eta)) <|
  .conj coverMajority <|
  .conj .sync <|
  .conj (.le .gst (.addΔ .outageEnd P.restoreLag)) <|
  after (.addΔ .outageEnd P.restoreLag) (.readyAbove P.afterAbove)

/-- Recovery at gap `k`. -/
def recoveryPremise (k : ℕ+) : Premise ProgressReq :=
  .conj .sync <|
  .conj (fromGST (.readyAbove P.recoveryAbove)) <|
  optConj P.recoveryFull (fromGST .full) <|
  optConj P.noWakeAfterGST (fromGST .noWake) <|
  .progress (headReq k) .gst

/-- The recovery spec (shared by the available and resilient outputs). -/
def recoverySpec : RecoverySpec ProgressReq ℕ+ where
  premise := P.recoveryPremise
  start k := .addΔ .gst (P.recovery.eval k)
  latency k := P.recGrowth.eval k
  escape := some P.accFrac

/-- Finality liveness at gap `k`. -/
def finalPremise (k : ℕ+) : Premise ProgressReq :=
  .conj (P.recoveryPremise k) <|
  .conj (fromGST (.readyOfAll P.finalityReadyOfAll)) <|
  .progress (P.finReq k) .gst

end GoldilocksParams

/-- The Goldilocks contract (index: the recurrence gap `k : ℕ+`). -/
def goldilocksContract (P : GoldilocksParams) : Contract goldilocksSchema ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  catchUp := P.catchUp
  spec
    | .available => some
        { safety := { premise := sleepy P.sleepyAbove }
          live := ⟨P.livePremise, fun _ => .zero, fun k => P.growth.eval k⟩
          recovery := some P.recoverySpec }
    | .resilient => some
        { safety := { premise := sleepy P.sleepyAbove }
          live := ⟨P.livePremise, fun _ => .zero, fun k => P.stableGrowth.eval k⟩
          resilience := some P.resiliencePremise
          recovery := some P.recoverySpec }
    | .final => some
        { safety := { premise := .truth, escape := some P.accFrac }
          live := ⟨P.finalPremise, fun k => .addΔ .gst (P.finStart.eval k),
            fun k => P.finDelay.eval k⟩
          accountable := some P.accFrac }

namespace GoldilocksParams

variable {P : GoldilocksParams}

theorem recoveryPremise_wellFormed (hP : P.WellFormed) (k : ℕ+) :
    (P.recoveryPremise k).WellFormed := by
  unfold recoveryPremise optConj
  cases P.recoveryFull <;> cases P.noWakeAfterGST <;>
    simp [Premise.WellFormed, fromGST, EnvAtom.WellFormed, TimeExpr.HorizonFree,
      hP.recoveryAbove]

end GoldilocksParams

open GoldilocksParams in
theorem goldilocksContract_wellFormed (P : GoldilocksParams) (hP : P.WellFormed) :
    (goldilocksContract P).WellFormed := by
  have hl : ∀ k, (P.livePremise k).WellFormed := fun k => by
    simp [livePremise, Premise.WellFormed, sleepy, Premise.always, EnvAtom.WellFormed,
      TimeExpr.HorizonFree, TimeExpr.Fixed, hP.sleepyAbove]
  have hs : (sleepy P.sleepyAbove : Premise ProgressReq).WellFormed := by
    simp [Premise.WellFormed, sleepy, Premise.always, EnvAtom.WellFormed, TimeExpr.HorizonFree,
      TimeExpr.Fixed, hP.sleepyAbove]
  have ha : FracWF (some P.accFrac) := fun α h => by cases h; exact hP.accFrac
  have hr : ∀ R, some P.recoverySpec = some R → (∀ i, (R.premise i).WellFormed) ∧ FracWF R.escape :=
    fun R h => by cases h; exact ⟨recoveryPremise_wellFormed hP, ha⟩
  have hst : ∀ R, some P.recoverySpec = some R → ∀ i, (R.start i).HorizonFree :=
    fun R h i => by cases h; trivial
  constructor
  intro c s h
  cases c <;> obtain rfl := Option.some.inj h
  · exact ⟨hs, (fun _ h => nomatch h), hl, (fun _ h => nomatch h), (fun _ h => nomatch h), hr,
      fun _ => trivial, hst⟩
  · refine ⟨hs, (fun _ h => nomatch h), hl, (fun _ h => nomatch h), ?_, hr, fun _ => trivial,
      hst⟩
    intro R h
    cases h
    norm_num [resiliencePremise, Premise.WellFormed, outageWindow, before, after, coverMajority,
      EnvAtom.WellFormed, TimeExpr.HorizonFree, TimeExpr.Fixed, hP.sleepyAbove, hP.stableEtaAbove,
      hP.afterAbove]
  · refine ⟨trivial, ha, fun k => ?_, ha, (fun _ h => nomatch h), (fun _ h => nomatch h),
      fun _ => trivial, (fun _ h => nomatch h)⟩
    exact ⟨recoveryPremise_wellFormed hP k, by
      simp [Premise.WellFormed, fromGST, EnvAtom.WellFormed, TimeExpr.HorizonFree,
        hP.finalityReadyOfAll], trivial⟩

section Realizable

variable {Info : Type} [DecidableEq Info] [Encodable Info]

open GoldilocksParams

/-- Every progress window of `w` slots (gap plus span) from a start `≤ 0`
fits a horizon `H ≥ 4w` on the Goldilocks grid at the extremal point. -/
theorem goldilocks_window (F : ShapeFamily goldilocksSchema Info)
    (hG : ∀ pub, (F pub).skel.grid = goldilocksGrid) {n : Nat} {H : Time}
    {submit : Fin (n + 1) → Time → List Tx} {w : Nat} (hk : 4 * (w : Time) ≤ H)
    {s : Time} (hs : s ≤ 0) :
    max s 0 + (w : Time) *
      (F (pubOf (EnvPoint.extremal n H 0 submit).env)).skel.grid.slotLen
        (EnvPoint.extremal n H 0 submit).env.Δ ≤ H := by
  rw [hG, max_eq_right hs]
  simp only [TimeGrid.slotLen, goldilocksGrid, EnvPoint.extremal]
  push_cast
  linarith

/-- The head requirement's window: its gap (its pattern has span 0). -/
theorem headReq_window (k : ℕ+) :
    (((headReq k).gap : Nat) + (headReq k).pattern.span : Nat) = (k : Nat) := rfl

/-- Non-vacuity of the Goldilocks contract for every family with the
skeleton's proposer selection size and grid. -/
theorem goldilocks_realizable (P : GoldilocksParams) (hP : P.WellFormed)
    (F : ShapeFamily goldilocksSchema Info)
    (hsel : ∀ pub, (F pub).skel.proposerSel = .sized 1)
    (hG : ∀ pub, (F pub).skel.grid = goldilocksGrid) :
    (goldilocksContract P).Realizable F := by
  have hwf := goldilocksContract_wellFormed P hP
  have hs1 : ∀ (Q : Premise ProgressReq), Q.UsesProgress →
      ∃ m, 1 ≤ m ∧ ∀ pub, (F pub).skel.proposerSel = .sized m := fun _ _ => ⟨1, le_rfl, hsel⟩
  have hk0 (k : ℕ+) : (0 : Time) ≤ 4 * ((k : Nat) : Time) := by positivity
  have hnn (m : Nat) : (0 : Time) ≤ (m : Time) := by positivity
  -- Every recovery-premise progress window at the extremal point.
  have hrecW (k : ℕ+) (H : Time) (hk : 4 * ((k : Nat) : Time) ≤ H) (n : Nat) submit :
      ProgressActive (F (pubOf (EnvPoint.extremal n H 0 submit).env)).skel.grid
        (EnvPoint.extremal n H 0 submit) (fun _ => 0) (P.recoveryPremise k) := by
    unfold ProgressActive recoveryPremise optConj
    cases P.recoveryFull <;> cases P.noWakeAfterGST <;>
      simp only [Premise.ProgressAll, fromGST, Bool.false_eq_true, ↓reduceIte, true_and] <;>
      exact goldilocks_window F hG (by rw [headReq_window]; exact hk)
        (by simp [TimeExpr.eval, EnvPoint.extremal])
  have hrecT (k : ℕ+) (H : Time) (n : Nat) submit :
      (P.recoveryPremise k).TimesHold (EnvPoint.extremal n H 0 submit) (fun _ => 0) := by
    unfold recoveryPremise optConj
    cases P.recoveryFull <;> cases P.noWakeAfterGST <;>
      simp [Premise.TimesHold, fromGST]
  have hliveW (k : ℕ+) (H : Time) (hk : 4 * ((k : Nat) : Time) ≤ H) (n : Nat) submit :
      ProgressActive (F (pubOf (EnvPoint.extremal n H 0 submit).env)).skel.grid
        (EnvPoint.extremal n H 0 submit) (fun _ => 0) (P.livePremise k) :=
    ⟨Premise.progressAll_of_not_usesProgress
        (by simp [sleepy, Premise.UsesProgress, Premise.always]),
      goldilocks_window F hG (by rw [headReq_window]; exact hk) (by simp [TimeExpr.eval])⟩
  constructor
  · -- Safety premises.
    intro c s h
    have hw := (hwf.caps c s h).safety
    cases c <;> obtain rfl := Option.some.inj h
    all_goals
      refine witness_realizable F _ _ hw (hs1 _) (fun _ => 0) 0 0 le_rfl (fun n submit => ?_)
        (fun n submit => Premise.progressAll_of_not_usesProgress ?_)
    all_goals simp [Premise.TimesHold, Premise.UsesProgress, sleepy, Premise.always,
      TimeExpr.eval, EnvPoint.extremal]
  · -- Liveness premises at every gap `k`.
    intro c s h k
    change ℕ+ at k
    have hw := (hwf.caps c s h).live k
    cases c <;> obtain rfl := Option.some.inj h
    · refine live_realizable F _ _ hw (hs1 _) _ _ (fun _ => 0)
        (1 + 4 * ((k : Nat) : Time) + ((P.growth.eval k : Nat) : Time)) 0 0
        (fun n submit => ?_) (fun n submit => ?_) (fun n => ?_) le_rfl ?_
      · simp [livePremise, Premise.TimesHold, sleepy, Premise.always, TimeExpr.eval,
          EnvPoint.extremal]
      · exact hliveW k _ (by linarith [hk0 k]) n submit
      · simp [TimeExpr.eval]
      · simp
    · refine live_realizable F _ _ hw (hs1 _) _ _ (fun _ => 0)
        (1 + 4 * ((k : Nat) : Time) + ((P.stableGrowth.eval k : Nat) : Time)) 0 0
        (fun n submit => ?_) (fun n submit => ?_) (fun n => ?_) le_rfl ?_
      · simp [livePremise, Premise.TimesHold, sleepy, Premise.always, TimeExpr.eval,
          EnvPoint.extremal]
      · exact hliveW k _ (by linarith [hk0 k]) n submit
      · simp [TimeExpr.eval]
      · simp
    · have hsp : (0 : Time) ≤ 4 * ((P.finPattern.span : Nat) : Time) := by positivity
      have hW : 4 * ((((P.finReq k).gap : Nat) + (P.finReq k).pattern.span : Nat) : Time) ≤
          1 + ((P.finStart.eval k : Nat) : Time) +
          4 * (((k : Nat) + P.finPattern.span : Nat) : Time) +
          ((P.finDelay.eval k : Nat) : Time) := by
        change 4 * (((k : Nat) + P.finPattern.span : Nat) : Time) ≤ _
        linarith [hnn (P.finStart.eval k), hnn (P.finDelay.eval k)]
      have hH : 4 * ((k : Nat) : Time) ≤ 1 + ((P.finStart.eval k : Nat) : Time) +
          4 * (((k : Nat) + P.finPattern.span : Nat) : Time) +
          ((P.finDelay.eval k : Nat) : Time) := by
        push_cast
        linarith [hnn (P.finStart.eval k), hnn (P.finDelay.eval k)]
      refine live_realizable F _ _ hw (hs1 _) _ _ (fun _ => 0) _ 0
        ((P.finStart.eval k : Nat) : Time)
        (fun n submit => ⟨hrecT k _ n submit, trivial, trivial⟩)
        (fun n submit => ⟨hrecW k _ hH n submit, trivial,
          goldilocks_window F hG hW (by simp [TimeExpr.eval, EnvPoint.extremal])⟩)
        (fun n => ?_) (hnn _) ?_
      · simp [TimeExpr.eval, EnvPoint.extremal]
      · rw [max_eq_left (hnn _)]; push_cast; linarith [hk0 k, hnn P.finPattern.span]
  · -- The resilience premise, at the sleeper point.
    intro c s Q h hQ
    have hw := (hwf.caps c s h).resilience Q hQ
    cases c <;> obtain rfl := Option.some.inj h <;> cases hQ
    let L : Time := P.armingLag
    let σ : Nat → Time := fun i => if i = 0 then 1 else L + 1 + i
    have hb := hP.outageBudget_pos
    refine resilience_realizable F _ _ hw ?_ (hs1 _) σ (L + 3 + P.restoreLag) 0
      (fun n submit => ?_)
      (fun n submit => Premise.progressAll_of_not_usesProgress ?_) ?_
    · simp [resiliencePremise, Premise.AtomsAll, EnvAtom.Counting, outageWindow, before, after,
        coverMajority]
    · have : (1 : Time) ≤ P.outageBudget := by exact_mod_cast hb
      simp only [resiliencePremise, Premise.TimesHold, outageWindow, TimeExpr.eval,
        EnvPoint.sleeper, σ, L]
      push_cast
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩ <;>
        norm_num <;> linarith [hnn P.restoreLag, hnn P.armingLag]
    · simp [resiliencePremise, Premise.UsesProgress, outageWindow, before, after, coverMajority]
    · simp only [σ, L]
      norm_num
      linarith [hnn P.restoreLag]
  · -- Recovery premises at every gap `k`.
    intro c s R h hR k
    change ℕ+ at k
    have hw := ((hwf.caps c s h).recovery R hR).1 k
    cases c <;> obtain rfl := Option.some.inj h <;> cases hR
    all_goals
      have hH : 4 * ((k : Nat) : Time) ≤ 1 + ((P.recovery.eval k : Nat) : Time) +
          4 * ((k : Nat) : Time) + ((P.recGrowth.eval k : Nat) : Time) := by
        linarith [hnn (P.recovery.eval k), hnn (P.recGrowth.eval k)]
      refine live_realizable F _ _ hw (hs1 _) _ _ (fun _ => 0) _ 0
        ((P.recovery.eval k : Nat) : Time) (hrecT k _) (hrecW k _ hH) (fun n => ?_) (hnn _) ?_
      · simp [recoverySpec, TimeExpr.eval, EnvPoint.extremal]
      · simp only [recoverySpec]
        rw [max_eq_left (hnn _)]; linarith [hk0 k]

end Realizable

end Consensus.Shape

end
