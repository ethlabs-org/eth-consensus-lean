module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Positive controls

The refutations of the other test modules must not come from premises that no
run can meet. `positive_controls` exhibits one canonical run of a family with
the Goldilocks skeleton that, at the concrete index `k = 1`, satisfies every
capability premise of `goldilocksContract ctrlParams` (standard numbers),
each as a full realizability `Witness` (a faulty validator, valid, no
collision, no conviction, active progress windows), with

* a relayed submission: an honest reader that was never submitted the
  transaction receives it by relay;
* ready readers and in-horizon deadlines: every liveness and recovery
  premise is `LiveActive` (L0 `TxLiveActive` with the real deadline);
* an active outage: the resilience premise is `ResilienceActive`
  (`T = 1 < b₀ = 3 < b₁ = 4 ≤ horizon`, a continuously eligible reader).

The point is the extremal point with five validators (validator 0 faulty),
`Δ = 1`, GST 0, horizon 20 and transaction `42` submitted to validator 1 at
time 10. Every other index is covered by `goldilocks_realizable` (a single
finite run cannot serve all indices). -/

namespace Consensus.Shape.Tests.Controls
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

/-! ## Concrete atoms at the extremal point -/

/-- The fraction conditions under which an atom holds at the extremal point
with `n + 1` validators (one faulty, every other ready). -/
def Fits (n : Nat) : EnvAtom → Prop
  | .faultsBelow β => 1 < β * ((n : ℚ) + 1)
  | .readyAbove θ => θ * ((n : ℚ) + 1) < n
  | .readyOfAll φ _ => φ * ((n : ℚ) + 1) < n
  | .etaSleepy θ _ => θ * ((n : ℚ) + 1) < n
  | .full => True
  | .noWake => True

/-- An atom that fits holds at the extremal point, at every time and
catch-up. -/
theorem holds_of_fits {n : Nat} {H g : Time} {submit : Fin (n + 1) → Time → List Tx}
    (a : EnvAtom) (h : Fits n a) (c t : Time) : a.holds (EnvPoint.extremal n H g submit) c t := by
  have card : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by simp
  cases a with
  | faultsBelow β =>
    change (EnvPoint.extremal n H g submit).FaultsBelow β
    unfold EnvPoint.FaultsBelow
    rw [EnvPoint.extremal_faulty]
    simpa [Fits] using h
  | readyAbove θ =>
    change (EnvPoint.extremal n H g submit).ReadyAbove θ c t
    unfold EnvPoint.ReadyAbove
    rw [EnvPoint.extremal_faulty, EnvPoint.extremal_readyAt, card]
    simpa [Fits] using h
  | readyOfAll φ inc =>
    have h' : φ * (Fintype.card (Fin (n + 1)) : ℚ) <
        ((EnvPoint.extremal n H g submit).readyAt c t).card := by
      rw [EnvPoint.extremal_readyAt, card]; simpa [Fits] using h
    cases inc
    · exact h'
    · exact h'.le
  | etaSleepy θ η =>
    change (EnvPoint.extremal n H g submit).EtaSleepy θ ((η : Time) * _) c t
    unfold EnvPoint.EtaSleepy
    have hη : t - (η : Time) * (EnvPoint.extremal n H g submit).env.Δ ≤ t := by
      simp [EnvPoint.extremal]
    rw [EnvPoint.extremal_awakeIn _ _ _ _ _ _ hη, EnvPoint.extremal_faulty,
      EnvPoint.extremal_readyAt, card]
    have hu : Finset.univ.erase (0 : Fin (n + 1)) ∪ {0} = Finset.univ := by
      ext v; by_cases hv : v = 0 <;> simp [hv]
    rw [hu]
    simpa [Fits] using h
  | full => exact fun v _ => rfl
  | noWake =>
    intro v _ hw
    have := hw.2
    simp [EnvPoint.extremal] at this

/-- Every atom of the premise fits. -/
def AllFit {Prog : Type} (n : Nat) : Premise Prog → Prop
  | .atTime _ a => Fits n a
  | .throughout _ _ a => Fits n a
  | .conj P Q => AllFit n P ∧ AllFit n Q
  | _ => True

/-- The environment part of a premise whose atoms fit and whose timing
constraints hold is met at the extremal point. -/
theorem evalEnv_of_allFit {Prog : Type} {n : Nat} {H g : Time}
    {submit : Fin (n + 1) → Time → List Tx} {σ : Nat → Time} {c : Time} (P : Premise Prog)
    (hf : AllFit n P) (ht : P.TimesHold (EnvPoint.extremal n H g submit) σ) :
    P.evalEnv (EnvPoint.extremal n H g submit) c σ := by
  unfold Premise.evalEnv
  induction P with
  | truth => trivial
  | le a b => exact ht
  | atTime t a => exact holds_of_fits a hf c _
  | throughout lo hi a => exact fun t _ _ => holds_of_fits a hf c t
  | sync => trivial
  | syncUntil b => trivial
  | progress π s => trivial
  | conj P Q ihP ihQ => exact ⟨ihP hf.1 ht.1, ihQ hf.2 ht.2⟩

/-! ## The control family, contract and point -/

/-- A Goldilocks-skeleton shape that does nothing (premises do not depend on
the protocol's behaviour). -/
def ctrlShape (pub : Public) : ChainShape pub GOut Unit where
  skel := goldilocksSkeleton pub.n
  State := Unit
  Body := Unit
  Durable := Unit
  decBody := inferInstance
  init := fun _ => ()
  clock := fun s _ => s
  propose := fun _ _ => none
  act := fun _ _ _ => none
  pollPropose := fun _ _ => none
  poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s _ _ => s
  durable := fun s => s
  restore := fun _ d _ => d
  out := fun _ _ => []
  conflicts := fun _ _ => false

/-- The control family. -/
def ctrlFamily : ShapeFamily goldilocksSchema Unit := ctrlShape

/-- Standard Goldilocks numbers: catch-up, `η`, arming lag, outage budget and
restore lag `1`; `η`-sleepy and recovery thresholds `½`; full participation in
recovery; latencies `1 + k` (stable growth `2 + k`). -/
def ctrlParams : GoldilocksParams :=
  GoldilocksParams.standard 1 1 1 1 1 (1 / 2) (1 / 2) true
    ⟨1, 1⟩ ⟨2, 1⟩ ⟨1, 1⟩ ⟨1, 1⟩ ⟨1, 1⟩ ⟨1, 1⟩

theorem ctrlParams_wellFormed : ctrlParams.WellFormed := by
  constructor <;> norm_num [ctrlParams, GoldilocksParams.standard]

/-- The control contract. -/
abbrev ctrlK : Contract goldilocksSchema ProgressReq := goldilocksContract ctrlParams

/-- The concrete index `k = 1`. -/
def k1 : ctrlK.Idx := (1 : ℕ+)

/-- Five validators (0 faulty), `Δ = 1`, GST 0, horizon 20, transaction `42`
submitted to validator 1 at time 10. -/
abbrev pt : EnvPoint (Fin 5) := EnvPoint.extremal 4 20 0 (submit42 10)

/-- Parameters of the non-resilience premises (unused). -/
def σ0 : Nat → Time := fun _ => 0

/-- Resilience parameters: `T = 1`, `b₀ = 3`, `b₁ = 4`. -/
def σR : Nat → Time
  | 0 => 1
  | 1 => 3
  | _ => 4

/-! ## The control -/

/-- One canonical run satisfies, at index `1`, every capability premise of the
control contract as an active witness, and relays the submitted transaction
to an honest reader that was never submitted it. -/
theorem positive_controls :
    ∃ rho : Model.Run (compiled ctrlFamily) pt.env, rho.point = pt ∧
      (∀ c s, ctrlK.spec c = some s → Witness ctrlFamily ctrlK s.safety.premise σ0 rho) ∧
      (∀ c s, ctrlK.spec c = some s →
        Witness ctrlFamily ctrlK (s.live.premise k1) σ0 rho ∧
          LiveActive ctrlFamily ctrlK (s.live.start k1) (s.live.latency k1) σ0 rho) ∧
      (∀ c s P, ctrlK.spec c = some s → s.resilience = some P →
        Witness ctrlFamily ctrlK P σR rho ∧ ResilienceActive ctrlFamily ctrlK σR rho) ∧
      (∀ c s R, ctrlK.spec c = some s → s.recovery = some R →
        Witness ctrlFamily ctrlK (R.premise k1) σ0 rho ∧
          LiveActive ctrlFamily ctrlK (R.start k1) (R.latency k1) σ0 rho) ∧
      (∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ) := by
  let hash : (protoOf (compiled ctrlFamily) pt.env).Item → Nat := fun x => Encodable.encode x + 1
  obtain ⟨relay, events, hv, hps, hhp, hc⟩ :=
    Model.canonical_run_causal goldilocksSchema (compiled ctrlFamily) (Fin 5) pt.env pt.honest
      pt.horizon (show (0 : Time) ≤ 20 by norm_num) (extremalKey 4) (extremalSel ctrlFamily pt.env)
      (extremalSel_admits ctrlFamily pt.env) pt.submit hash
  let rho := Model.mkRun (F := compiled ctrlFamily) (E := pt.env) pt.honest pt.horizon
    (extremalKey 4) (extremalSel ctrlFamily pt.env) pt.submit relay hash events
  have hpt : rho.point = pt := rfl
  -- Every premise whose atoms fit, whose timing constraints hold and whose
  -- progress windows fit in the horizon has a witness on `rho`.
  have wit : ∀ (P : Premise ProgressReq) (σ : Nat → Time), P.WellFormed → AllFit 4 P →
      P.TimesHold pt σ →
      ProgressActive (ctrlFamily (pubOf pt.env)).skel.grid pt σ P →
      Witness ctrlFamily ctrlK P σ rho := by
    intro P σ _ hf ht hact
    have henv : P.evalEnv pt (((ctrlK.catchUp : Nat) : Time) * pt.env.Δ) σ :=
      evalEnv_of_allFit P hf ht
    have hprog : P.UsesProgress → ∀ π s,
        PatternRecurrence (R := ShapeRole (ctrlFamily (pubOf pt.env)).skel.Kind) pt
          (extremalKey 4) (extremalSel ctrlFamily pt.env) ShapeRole.proposer
          (ctrlFamily (pubOf pt.env)).skel.grid π
          (((ctrlK.catchUp : Nat) : Time) * pt.env.Δ) s := by
      intro _ π s
      apply patternRecurrence_of_all pt.env.Δ_pos
      intro s j _
      exact extremalSel_proposers ctrlFamily (m := 1) le_rfl (by norm_num) rfl _ _ _
    refine ⟨?_, hv, ?_, ?_, ?_, hact⟩
    · rw [hpt, EnvPoint.extremal_faulty]; exact Finset.singleton_nonempty _
    · apply Model.Run.not_hashCollision_of_injective
      intro a b hab
      exact Encodable.encode_injective (Nat.add_right_cancel hab)
    · exact Model.convicted_honestEvidence_eq_empty rho (rho.not_slashable_of_causal hv hc)
    · exact Consensus.Premise.eval_of_evalAt hps (fun b => hhp b)
        (Premise.evalAt_of_evalEnv henv hprog)
  have live : ∀ (start : TimeExpr) (D : Nat), start.eval pt σ0 ≤ 10 → 10 + 1 + D ≤ (20 : Time) →
      LiveActive ctrlFamily ctrlK start D σ0 rho := fun start D hτ hD =>
    extremal_liveActive ctrlFamily ctrlK start D σ0 (by norm_num) hτ (by norm_num)
      (by simpa using hD) rho hpt
  have hlive : Witness ctrlFamily ctrlK (ctrlParams.livePremise 1) σ0 rho := by
    apply wit
    · exact ((goldilocksContract_wellFormed ctrlParams ctrlParams_wellFormed).caps .available _
        rfl).live k1
    · norm_num [AllFit, Fits, GoldilocksParams.livePremise, Premise.sleepy, Premise.always,
        ctrlParams, GoldilocksParams.standard]
    · simp [GoldilocksParams.livePremise, Premise.TimesHold, Premise.sleepy, Premise.always,
        TimeExpr.eval, EnvPoint.extremal]
    · refine ⟨Premise.progressAll_of_not_usesProgress
        (by simp [Premise.sleepy, Premise.UsesProgress, Premise.always]), ?_⟩
      simp [Premise.ProgressAll, TimeExpr.eval, GoldilocksParams.headReq, ctrlFamily, ctrlShape,
        goldilocksSkeleton, goldilocksGrid, TimeGrid.slotLen, EnvPoint.extremal]
  have hrec : Witness ctrlFamily ctrlK (ctrlParams.recoveryPremise 1) σ0 rho := by
    apply wit
    · exact GoldilocksParams.recoveryPremise_wellFormed ctrlParams_wellFormed 1
    · norm_num [AllFit, Fits, GoldilocksParams.recoveryPremise, optConj, Premise.fromGST,
        ctrlParams, GoldilocksParams.standard]
    · simp [GoldilocksParams.recoveryPremise, optConj, Premise.TimesHold, Premise.fromGST,
        ctrlParams, GoldilocksParams.standard]
    · simp [ProgressActive, GoldilocksParams.recoveryPremise, optConj, Premise.ProgressAll,
        Premise.fromGST, ctrlParams, GoldilocksParams.standard, TimeExpr.eval,
        GoldilocksParams.headReq, ctrlFamily, ctrlShape, goldilocksSkeleton, goldilocksGrid,
        TimeGrid.slotLen, EnvPoint.extremal]
  have hsafe : Witness ctrlFamily ctrlK (Premise.sleepy ctrlParams.sleepyAbove) σ0 rho := by
    apply wit
    · exact ((goldilocksContract_wellFormed ctrlParams ctrlParams_wellFormed).caps .available _
        rfl).safety
    · norm_num [AllFit, Fits, Premise.sleepy, Premise.always, ctrlParams,
        GoldilocksParams.standard]
    · simp [Premise.TimesHold, Premise.sleepy, Premise.always, TimeExpr.eval, EnvPoint.extremal]
    · exact Premise.progressAll_of_not_usesProgress
        (by simp [Premise.sleepy, Premise.UsesProgress, Premise.always])
  refine ⟨rho, hpt, ?_, ?_, ?_, ?_, ?_⟩
  · -- Safety premises.
    intro c s h
    cases c <;> obtain rfl := Option.some.inj h
    · exact hsafe
    · exact hsafe
    · apply wit
      · trivial
      · trivial
      · trivial
      · trivial
  · -- Liveness premises at index 1.
    intro c s h
    cases c <;> obtain rfl := Option.some.inj h
    · exact ⟨hlive, live _ _ (by simp [TimeExpr.eval]) (by
        norm_num [ctrlParams, GoldilocksParams.standard, k1, Affine.eval])⟩
    · exact ⟨hlive, live _ _ (by simp [TimeExpr.eval]) (by
        norm_num [ctrlParams, GoldilocksParams.standard, k1, Affine.eval])⟩
    · refine ⟨?_, live _ _ ?_ ?_⟩
      · apply wit
        · exact ((goldilocksContract_wellFormed ctrlParams ctrlParams_wellFormed).caps .final _
            rfl).live k1
        · refine ⟨?_, ?_, trivial⟩
          · norm_num [AllFit, Fits, GoldilocksParams.recoveryPremise, optConj, Premise.fromGST,
              ctrlParams, GoldilocksParams.standard, k1]
          · norm_num [AllFit, Fits, Premise.fromGST, ctrlParams, GoldilocksParams.standard]
        · exact ⟨by simp [k1, GoldilocksParams.recoveryPremise, optConj, Premise.TimesHold,
            Premise.fromGST, ctrlParams, GoldilocksParams.standard], trivial, trivial⟩
        · refine ⟨?_, trivial, ?_⟩
          · simp [k1, GoldilocksParams.recoveryPremise, optConj,
              Premise.ProgressAll, Premise.fromGST, ctrlParams, GoldilocksParams.standard,
              TimeExpr.eval, GoldilocksParams.headReq, ctrlFamily, ctrlShape,
              goldilocksSkeleton, goldilocksGrid, TimeGrid.slotLen, EnvPoint.extremal]
          · simp [k1, Premise.ProgressAll, TimeExpr.eval, GoldilocksParams.finReq, ctrlFamily,
              ctrlShape, ctrlParams, GoldilocksParams.standard,
              goldilocksSkeleton, goldilocksGrid, TimeGrid.slotLen, EnvPoint.extremal]
      · norm_num [k1, TimeExpr.eval, ctrlParams, GoldilocksParams.standard, Affine.eval,
          EnvPoint.extremal]
      · norm_num [k1, ctrlParams, GoldilocksParams.standard, Affine.eval]
  · -- The resilience premise.
    intro c s P h hP
    cases c <;> obtain rfl := Option.some.inj h <;> cases hP
    refine ⟨?_, extremal_resilienceActive ctrlFamily ctrlK σR (by norm_num)
      (by norm_num [σR]) rho hpt⟩
    apply wit
    · exact ((goldilocksContract_wellFormed ctrlParams ctrlParams_wellFormed).caps .resilient _
        rfl).resilience _ rfl
    · norm_num [AllFit, Fits, GoldilocksParams.resiliencePremise, Premise.outageWindow,
        Premise.before, Premise.after, Premise.coverMajority, ctrlParams,
        GoldilocksParams.standard]
    · norm_num [GoldilocksParams.resiliencePremise, Premise.TimesHold, Premise.outageWindow,
        Premise.before, Premise.after, Premise.coverMajority, TimeExpr.eval, σR, ctrlParams,
        GoldilocksParams.standard, EnvPoint.extremal]
    · exact Premise.progressAll_of_not_usesProgress
        (by simp [GoldilocksParams.resiliencePremise, Premise.UsesProgress, Premise.outageWindow,
          Premise.before, Premise.after, Premise.coverMajority])
  · -- Recovery premises at index 1.
    intro c s R h hR
    cases c <;> obtain rfl := Option.some.inj h <;> cases hR
    all_goals
      refine ⟨hrec, live _ _ ?_ ?_⟩
      · norm_num [k1, GoldilocksParams.recoverySpec, TimeExpr.eval, ctrlParams,
          GoldilocksParams.standard, Affine.eval, EnvPoint.extremal]
      · norm_num [k1, GoldilocksParams.recoverySpec, ctrlParams, GoldilocksParams.standard,
          Affine.eval]
  · -- The relayed submission.
    exact active_relay rho hps (fun _ _ => rfl)
      (live (.zero) 2 (by simp [TimeExpr.eval]) (by norm_num))

end Consensus.Shape.Tests.Controls

end
