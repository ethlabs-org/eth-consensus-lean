module
public import ConsensusShapeTests.Values
public import Mathlib.Tactic
@[expose] public section

/-! # Equivalence record of the simplicity passes

Each definition that was reformulated rather than moved or deleted is
restated here in its old form (`Old*`, body verbatim; deleted helpers are
inlined), with a lemma `new ↔ old` (or `new = old`) checked by Lean.

* B1: the wrapper `System.convicted` was inlined at its uses;
  `GoldilocksBindings` is a `def` instead of a one-field structure;
  `streamletContract`/`tendermintContract` are the specializations of the
  shared `bftContract`.
* B2 (L0, one body per notion): `OutputSchema.Serves` without the
  `BFTCore`/`DACore` packages; `Agree`, `Monotone`, `Safe` and `ReadySafe`
  through `AgreeAmong`/`MonotoneAmong`; `ProtectedThrough` through
  `ProtectedUpTo`; the wrappers `EnvPoint.Sleepy`, `EnvPoint.EtaSleepy`,
  `EnvPoint.HealthyFrom` and `EnvPoint.WellFormed` inlined; `TxLiveActive`
  on the environment point, and `Realizable` through `SleepyLive` and
  `HealthyLive`. (`Contract` lost its unused schema parameter; it carried no
  data, so no lemma.)
* B4 (L1): `Protocol.SelAdmits`; `SelSpec.all` replaced by `.fixed univ`;
  `Obj.Contains` is membership in `parts`; `ExecutionValid` flat;
  `Run.signerOf` on objects; the `sysOf` log is the tagged run log.
* B5 (L2): `ShapeClaims` through `sysOf` (`System.Holds`, the L0 regimes),
  without `AllRuns` and the seven regime abbreviations. -/

namespace Consensus.Shape.Tests.Reformulations

open Consensus Blocks Shape

/-! ## B1 -/

section Accountable

variable {V : Type} [Fintype V] (S : System V) (r : S.Run)

/-- The old `System.convicted`. -/
noncomputable def OldConvicted (A : Set S.Obs) : Finset V :=
  Consensus.convicted (S.convicts r) A

theorem convicted_eq (A : Set S.Obs) :
    Consensus.convicted (S.convicts r) A = OldConvicted S r A := rfl

end Accountable

section Bindings

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- The old one-field structure. -/
structure OldGoldilocksBindings (F : ShapeFamily goldilocksSchema Info) : Prop where
  skel : ∀ pub, (F pub).skel = goldilocksSkeleton pub.n

theorem goldilocksBindings_iff (F : ShapeFamily goldilocksSchema Info) :
    GoldilocksBindings F ↔ OldGoldilocksBindings F :=
  ⟨fun h => ⟨h⟩, fun h => h.skel⟩

end Bindings

section Values

/-- The old Streamlet contract (with `streamletPattern := Pattern.range 5`
inlined). -/
def OldStreamletContract (catchUp : Nat) (heal latency : Affine) :
    Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ k => catchUp + 1 + heal.eval k)
    (fun _ k => latency.eval k)
  progress _ k := .recur ⟨Pattern.range 5, k⟩

/-- The old Tendermint contract. -/
def OldTendermintContract (catchUp : Nat) (heal latency : Affine) :
    Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := Params.standard catchUp 0 1 (fun _ m => catchUp + 1 + heal.eval m)
    (fun _ m => latency.eval m)
  progress _ m := .notReadyAtMost m

theorem streamletContract_eq (catchUp : Nat) (heal latency : Affine) :
    streamletContract catchUp heal latency = OldStreamletContract catchUp heal latency := rfl

theorem tendermintContract_eq (catchUp : Nat) (heal latency : Affine) :
    tendermintContract catchUp heal latency = OldTendermintContract catchUp heal latency := rfl

end Values

/-! ## B2 -/

section Serves

/-- The old schema packages and `Serves`. -/
def OldBFTCore (O : OutputSchema) : Prop := (O.output .final).isSome

def OldDACore (O : OutputSchema) : Prop :=
  (O.output .available).isSome ∧ O.output .final = none

def OldServes (O : OutputSchema) : Prop := OldBFTCore O ∨ OldDACore O

theorem serves_iff (O : OutputSchema) : O.Serves ↔ OldServes O := by
  unfold OutputSchema.Serves OldServes OldBFTCore OldDACore
  cases O.output .final <;> simp

end Serves

section Safety

variable {V α Id : Type} (tr : Trace V α Id)

/-- The old bodies of `Agree`, `Monotone`, `Safe` and `ReadySafe`. -/
def OldAgree (g : Id) (t₀ : Time) : Prop :=
  ∀ u ∈ tr.point.honest, ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
    Compatible (tr.read g u i) (tr.read g v j)

def OldMonotone (g : Id) (t₀ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
    tr.read g v i <+: tr.read g v j

def OldSafe (g : Id) (t₀ : Time) : Prop := OldAgree tr g t₀ ∧ OldMonotone tr g t₀

def OldReadySafe (c : Time) (g : Id) (t₀ : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

theorem agree_iff (g : Id) (t₀ : Time) : tr.Agree g t₀ ↔ OldAgree tr g t₀ :=
  ⟨fun h u hu v hv i j hi hj => h u v i j hi hj hu hv,
    fun h u v i j hi hj hu hv => h u hu v hv i j hi hj⟩

theorem monotone_iff (g : Id) (t₀ : Time) : tr.Monotone g t₀ ↔ OldMonotone tr g t₀ :=
  ⟨fun h v hv i j hi hij hj => h v i j hi hij hj hv hv,
    fun h v i j hi hij hj hv _ => h v hv i j hi hij hj⟩

theorem safe_iff (g : Id) (t₀ : Time) : tr.Safe g t₀ ↔ OldSafe tr g t₀ :=
  and_congr (agree_iff tr g t₀) (monotone_iff tr g t₀)

theorem readySafe_iff (c : Time) (g : Id) (t₀ : Time) :
    tr.ReadySafe c g t₀ ↔ OldReadySafe tr c g t₀ := Iff.rfl

/-- The old body of `ProtectedThrough`. -/
def OldProtectedThrough (c : Time) (src dst : Id) (T b₀ b₁ : Time) : Prop :=
  ∀ v, tr.point.Ready c v T → ∀ t, b₀ ≤ t → t ≤ tr.point.horizon →
    ∀ w ∈ tr.point.honest, tr.ResilienceReader c b₀ b₁ w t →
    tr.readAt src v T <+: tr.readAt dst w t

theorem protectedThrough_iff (c : Time) (src dst : Id) (T b₀ b₁ : Time) :
    tr.ProtectedThrough c src dst T b₀ b₁ ↔ OldProtectedThrough tr c src dst T b₀ b₁ := Iff.rfl

/-- The old trace-level `TxLiveActive` (it reads only `tr.point`). -/
def OldTxLiveActive (c : Time) (start D : Time) : Prop :=
  ∃ (x : Tx) (t t' : Time) (u w : V), 0 ≤ t ∧ u ∈ tr.point.honest ∧
    tr.point.env.awake u t = true ∧ x ∈ tr.point.submit u t ∧ w ∈ tr.point.honest ∧ w ≠ u ∧
    (∀ τ, x ∉ tr.point.submit w τ) ∧
    max t start + tr.point.env.Δ + D ≤ t' ∧ t' ≤ tr.point.horizon ∧
    tr.point.Ready c w t'

theorem txLiveActive_iff (c start D : Time) :
    tr.point.TxLiveActive c start D ↔ OldTxLiveActive tr c start D := Iff.rfl

end Safety

section Wrappers

variable {V M Idx : Type} [Fintype V] [DecidableEq V]
  (P : Params Idx) (p : EnvPoint V) (L : CommLog V M)

/-- The inlined wrappers. -/
def OldSleepy (θ : ℚ) (c : Time) : Prop := p.SleepyOn θ c 0 p.horizon

def OldEtaSleepy (θ : ℚ) (η c : Time) : Prop := p.EtaSleepyOn θ η c 0 p.horizon

def OldHealthyFrom (φ : ℚ) (g : Time) : Prop := p.HealthyOn φ g p.horizon

def OldWellFormed : Prop := 0 ≤ p.horizon

theorem regime_sleepy_iff :
    Regime.Sleepy P p L ↔ L.PSync p 0 ∧ OldSleepy p P.θ (P.cDur p.env.Δ) := Iff.rfl

omit [DecidableEq V] in
theorem regime_healthy_iff (g : Time) :
    Regime.Healthy P p L g ↔ L.PSync p g ∧ OldHealthyFrom p P.φ g := Iff.rfl

theorem regime_outage_iff (T b₀ b₁ : Time) :
    Regime.Outage P p L T b₀ b₁ ↔ OutageTimes P p.env.Δ T b₀ b₁ ∧ L.OutageNet p b₀ b₁ ∧
      OldEtaSleepy p P.θ (P.ηDur p.env.Δ) (P.cDur p.env.Δ) ∧
      p.ReadyOfAll P.cover (P.cDur p.env.Δ) b₀ := Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem wellFormed_iff : OldWellFormed p ↔ 0 ≤ p.horizon := Iff.rfl

end Wrappers

section Good

variable {V : Type} {Prog : Type}

/-- The old `Adequate` (coverage over `WellFormed` points). -/
structure OldAdequate (S : System V) (X : Progress S Prog) : Prop where
  admits : ∀ E : Env V, ∃ e : X.Ext E, X.Admits E e
  covers : ∀ p : EnvPoint V, OldWellFormed p → ∀ e : X.Ext p.env, X.Admits p.env e →
    ∀ g : Time,
    ∃ r, S.Valid r ∧ ¬ S.Excuse r ∧ S.pt r = p ∧ (S.log r).EagerFrom (S.pt r) g ∧
      ∀ π c s t, X.holds π c s t p e → X.holds π c s t (S.pt r) (X.ext r)
  prefixClosed : ∀ r, S.Valid r → ∀ b : Time, 0 ≤ b → b ≤ (S.pt r).horizon → ∃ r', S.Valid r' ∧
    (S.trace r').PrefixOf (S.trace r) b ∧
    (∀ v i, i ≤ (S.trace r').cuts → S.view r' v i = S.view r v i) ∧
    (S.log r').AgreesUpTo (S.log r) b ∧ (S.Excuse r' → S.Excuse r) ∧
    ∀ π c s t, t ≤ b → X.holds π c s t (S.pt r) (X.ext r) → X.holds π c s t (S.pt r') (X.ext r')

theorem adequate_iff (S : System V) (X : Progress S Prog) : S.Adequate X ↔ OldAdequate S X :=
  ⟨fun h => ⟨h.admits, h.covers, h.prefixClosed⟩, fun h => ⟨h.admits, h.covers, h.prefixClosed⟩⟩

variable [Fintype V] [DecidableEq V]

/-- The old `Realizable` (flat conjunctions, trace-level `TxLiveActive`). -/
structure OldRealizable (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  sleepy : ∀ cap i (Δ : Time), 0 < Δ → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧ S.Sleepy K r ∧
    S.prog X K cap i 0 (S.pt r).horizon r ∧
    OldTxLiveActive (S.trace r) (S.cDur K r) 0 (S.lat K cap i r)
  healthy : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    (S.log r).EagerFrom (S.pt r) g ∧ S.Healthy K g r ∧
    S.prog X K cap i (S.ready K g r) (S.pt r).horizon r ∧
    OldTxLiveActive (S.trace r) (S.cDur K r) (S.heal K cap i g r) (S.lat K cap i r) ∧
    SafeActive (S.cDur K r) (S.heal K cap i g r) (S.pt r)
  sleepyStress : ∀ cap, (cap = .available ∨ cap = .stable) → (S.schema.output cap).isSome →
    ∀ Δ : Time, 0 < Δ → ∃ i r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧ S.Sleepy K r ∧
      S.prog X K cap i 0 (S.pt r).horizon r ∧
      OldTxLiveActive (S.trace r) (S.cDur K r) 0 (S.lat K cap i r) ∧
      (S.pt r).AwakeAtMost (2 * Fintype.card V / 3)
  healthyStress : ∀ cap, (S.schema.output cap).isSome → ∀ (Δ g : Time), 0 < Δ → 0 ≤ g →
    ∃ i r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧ (S.log r).EagerFrom (S.pt r) g ∧
      S.Healthy K g r ∧ S.prog X K cap i (S.ready K g r) (S.pt r).horizon r ∧
      OldTxLiveActive (S.trace r) (S.cDur K r) (S.heal K cap i g r) (S.lat K cap i r) ∧
      (S.pt r).AwakeAtMost (2 * Fintype.card V / 3 + 1)
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    S.Outage K T b₀ b₁ r ∧ OutageActive (S.cDur K r) T b₀ b₁ (S.pt r) ∧ (k : Time) * Δ ≤ T

/-- `Realizable` is the old structure up to the association of `∧`. -/
theorem realizable_iff (S : System V) (X : Progress S Prog) (K : Contract Prog) :
    Realizable S X K ↔ OldRealizable S X K := by
  constructor
  · intro h
    refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_, fun cap hc ho Δ hΔ => ?_,
      fun cap ho Δ g hΔ hg => ?_, h.outage⟩
    · obtain ⟨r, hw, hd, hs, hp, ht⟩ := h.sleepy cap i Δ hΔ
      exact ⟨r, hw, hd, hs, hp, ht⟩
    · obtain ⟨r, hw, hd, ⟨he, hH, hp, ht⟩, hsa⟩ := h.healthy cap i Δ g hΔ hg
      exact ⟨r, hw, hd, he, hH, hp, ht, hsa⟩
    · obtain ⟨i, r, hw, hd, ⟨hs, hp, ht⟩, ha⟩ := h.sleepyStress cap hc ho Δ hΔ
      exact ⟨i, r, hw, hd, hs, hp, ht, ha⟩
    · obtain ⟨i, r, hw, hd, ⟨he, hH, hp, ht⟩, ha⟩ := h.healthyStress cap ho Δ g hΔ hg
      exact ⟨i, r, hw, hd, he, hH, hp, ht, ha⟩
  · intro h
    refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_, fun cap hc ho Δ hΔ => ?_,
      fun cap ho Δ g hΔ hg => ?_, h.outage⟩
    · obtain ⟨r, hw, hd, hs, hp, ht⟩ := h.sleepy cap i Δ hΔ
      exact ⟨r, hw, hd, hs, hp, ht⟩
    · obtain ⟨r, hw, hd, he, hH, hp, ht, hsa⟩ := h.healthy cap i Δ g hΔ hg
      exact ⟨r, hw, hd, ⟨he, hH, hp, ht⟩, hsa⟩
    · obtain ⟨i, r, hw, hd, hs, hp, ht, ha⟩ := h.sleepyStress cap hc ho Δ hΔ
      exact ⟨i, r, hw, hd, ⟨hs, hp, ht⟩, ha⟩
    · obtain ⟨i, r, hw, hd, he, hH, hp, ht, ha⟩ := h.healthyStress cap ho Δ g hΔ hg
      exact ⟨i, r, hw, hd, ⟨he, hH, hp, ht⟩, ha⟩

end Good

/-! ## B4 -/

section Model

open Consensus.Model

/-- `SelAdmits` is the per-role admissibility it names. -/
theorem selAdmits_iff {pub : Public} {Out : Type} (P : Protocol pub Out)
    (sel : P.Role → Finset (Fin pub.n)) :
    P.SelAdmits sel ↔ ∀ r, (P.selSpec r).Admits (sel r) := Iff.rfl

/-- The deleted `SelSpec.all` admitted exactly `univ`; so does `.fixed univ`. -/
theorem fixed_univ_admits {n : Nat} (S : Finset (Fin n)) :
    (SelSpec.fixed Finset.univ).Admits S ↔ S = Finset.univ := Iff.rfl

variable {n : Nat} {Role Item Body : Type}

/-- The old inductive `Obj.Contains`. -/
inductive OldContains : Obj n Role Item Body → Obj n Role Item Body → Prop
  | refl (o : Obj n Role Item Body) : OldContains o o
  | step {o c d : Obj n Role Item Body} : c ∈ o.carried → OldContains c d → OldContains o d

theorem oldContains_iff (o d : Obj n Role Item Body) : OldContains o d ↔ Obj.Contains o d := by
  constructor
  · intro h
    induction h with
    | refl o => exact .refl o
    | step hc _ ih => exact .step hc ih
  · intro h
    rcases h.cases with rfl | ⟨c, hc, hcd⟩
    · exact .refl _
    · exact .step hc ((oldContains_iff c d).mpr hcd)
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (Obj.carried_size_lt _)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

/-- The old `Run.signerOf`, on authentications. -/
def OldSignerOf (rho : Run F E) : Auth (Fintype.card V) (protoOf F E).Role → Option V
  | .signed k _ => some (rho.key k)
  | .none => none

theorem signerOf_eq (rho : Run F E) (o : (protoOf F E).Object) :
    rho.signerOf o = OldSignerOf rho o.auth := by
  obtain ⟨a, m, cs⟩ := o
  cases a <;> rfl

/-- The old `ScheduleWellFormed`. -/
structure OldScheduleWellFormed (rho : Run F E) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_total : ∀ v ∈ rho.honest, ∀ t, 0 ≤ t → t ≤ rho.horizon →
    E.awake v t = true → Event.tick v t ∈ rho.events

/-- The old `SleepWellFormed`. -/
structure OldSleepWellFormed (rho : Run F E) : Prop where
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_at_wake : ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t
  wake_restart : ∀ v ∈ rho.honest, ∀ t, 0 < t → t ≤ rho.horizon →
    Wakes E v t → Event.restart v t ∈ rho.events

/-- The old nested `ExecutionValid`. -/
structure OldExecutionValid (rho : Run F E) : Prop extends
  OldScheduleWellFormed rho, OldSleepWellFormed rho where
  unforgeable : rho.Unforgeable
  selValid : rho.SelValid
  credentials : rho.Credentials

theorem executionValid_iff (rho : Run F E) : rho.ExecutionValid ↔ OldExecutionValid rho :=
  ⟨fun h => ⟨⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, ⟨h.7, h.8, h.9, h.10⟩, h.11, h.12, h.13⟩,
    fun h => ⟨h.1.1, h.1.2, h.1.3, h.1.4, h.1.5, h.1.6, h.2.1, h.2.2, h.2.3, h.2.4, h.3, h.4,
      h.5⟩⟩

/-- The old `sysOf` log, written out. -/
theorem sysOf_log_eq (r : (sysOf O F V).Run) :
    (sysOf O F V).log r = ⟨fun v m t => ∃ o, m = ⟨r.1, o⟩ ∧ r.2.releases v o t,
      fun v m t => ∃ o, m = ⟨r.1, o⟩ ∧ r.2.receives v o t, r.2.inbox⟩ := rfl

end Model

/-! ## B5 (L2): shape claims through `sysOf` -/

section Claims

open Consensus.Model (sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

section Abbrevs

variable {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The catch-up duration `catchUp·Δ`. -/
abbrev OldShapeC (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) : Time := (sysOf O (compiled F) V).cDur K ⟨E, rho⟩

/-- The sleepy regime (L0 `Regime.Sleepy`). -/
abbrev OldShapeSleepy (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) : Prop := (sysOf O (compiled F) V).Sleepy K ⟨E, rho⟩

/-- The healthy regime from GST `gst` (L0 `Regime.Healthy`). -/
abbrev OldShapeHealthy (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) (gst : Time) : Prop := (sysOf O (compiled F) V).Healthy K gst ⟨E, rho⟩

/-- The outage regime (L0 `Regime.Outage`). -/
abbrev OldShapeOutage (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) (T b₀ b₁ : Time) : Prop :=
  (sysOf O (compiled F) V).Outage K T b₀ b₁ ⟨E, rho⟩

/-- The heal point of `cap` at `i` after GST `gst`. -/
abbrev OldShapeHeal (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) (cap : Capability) (i : K.Idx) (gst : Time) : Time :=
  (sysOf O (compiled F) V).heal K cap i gst ⟨E, rho⟩

/-- The start of progress windows after GST `gst`. -/
abbrev OldShapeReady (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) (gst : Time) : Time := (sysOf O (compiled F) V).ready K gst ⟨E, rho⟩

/-- The progress requirement of `cap` at `i` holds on `[start, stop]`. -/
abbrev OldShapeProg (K : Contract ProgressReq) (rho : Model.Run (compiled F) E) (cap : Capability) (i : K.Idx) (start stop : Time) : Prop :=
  (sysOf O (compiled F) V).prog (shapeProgress F V) K cap i start stop ⟨E, rho⟩

end Abbrevs

/-- A property of every run of the compiled family, over every finite
validator set and every environment. -/
def OldAllRuns (F : ShapeFamily O Info)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Env V), Model.Run (compiled F) E → Prop) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Env V) (rho : Model.Run (compiled F) E), Q E rho

/-- The chain-level claims of a shape family for contract `K`. -/
structure ShapeClaimsOld (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- Every provided output is valid in every valid run. -/
  outputValid : OldAllRuns F fun _ rho => rho.ExecutionValid →
    ∀ c g, O.output c = some g → OutputValid rho g
  /-- Lower-rank chains are prefixes of higher-rank ones. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    OldAllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Nested g₁ g₂
  /-- The final chain never rolls back. -/
  finalMonotone : ∀ g, O.output .final = some g →
    OldAllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Monotone g 0
  /-- Local accountability of the final chain for fraction `α`, in every
  environment: conflicting honest reads convict `α` from their own views. -/
  finalAccountable : ∀ g, O.output .final = some g → OldAllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable K.params.α g 0 ∨
      rho.HashCollision
  /-- Final liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  finalLive : ∀ g, O.output .final = some g → ∀ (i : K.Idx) (gst : Time),
    OldAllRuns F fun _ rho => rho.ExecutionValid → OldShapeHealthy K rho gst →
      OldShapeProg K rho .final i (OldShapeReady K rho gst) rho.horizon →
      ProposalLiveReady rho (OldShapeC K rho) g (OldShapeHeal K rho .final i gst)
        (K.params.latency .final i) ∨ rho.HashCollision
  /-- Sleepy safety of an available or stable chain, for ready readers. -/
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    OldAllRuns F fun _ rho => rho.ExecutionValid → OldShapeSleepy K rho →
      (chainTrace rho).ReadySafe (OldShapeC K rho) g 0 ∨ rho.HashCollision
  /-- Sleepy liveness, with progress on the whole run. -/
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ i : K.Idx, OldAllRuns F fun _ rho => rho.ExecutionValid → OldShapeSleepy K rho →
      OldShapeProg K rho cap i 0 rho.horizon →
      ProposalLiveReady rho (OldShapeC K rho) g 0 (K.params.latency cap i) ∨ rho.HashCollision
  /-- Healed safety: healthy from `gst` with progress on `[readyFrom, heal]`,
  ready readers are safe from the heal point. -/
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
      OldShapeHealthy K rho gst →
      OldShapeProg K rho cap i (OldShapeReady K rho gst) (OldShapeHeal K rho cap i gst) →
      (chainTrace rho).ReadySafe (OldShapeC K rho) g (OldShapeHeal K rho cap i gst) ∨ rho.HashCollision
  /-- Healed liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  healedLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
      OldShapeHealthy K rho gst → OldShapeProg K rho cap i (OldShapeReady K rho gst) rho.horizon →
      ProposalLiveReady rho (OldShapeC K rho) g (OldShapeHeal K rho cap i gst) (K.params.latency cap i) ∨
        rho.HashCollision
  /-- Outage resilience of the stable chain, into the resilience target. -/
  persists : ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
    OldAllRuns F fun _ rho => rho.ExecutionValid → OldShapeOutage K rho T b₀ b₁ →
      (chainTrace rho).ProtectedThrough (OldShapeC K rho) g (resilienceTarget O g) T b₀ b₁ ∨
        rho.HashCollision

/-- `ShapeClaims` through `sysOf` is the old `AllRuns` form: `Holds` is
"every valid run satisfying the regime, or a collision", the regime premises
are curried there, and a system run is a pair `⟨E, rho⟩`. -/
theorem shapeClaims_iff (F : ShapeFamily O Info) (K : Contract ProgressReq) :
    ShapeClaims F K ↔ ShapeClaimsOld F K := by
  constructor
  · intro h
    exact ⟨fun V _ _ E rho hv => (h V).outputValid ⟨E, rho⟩ hv,
      fun c₁ c₂ g₁ g₂ hlt h₁ h₂ V _ _ E rho hv =>
        (h V).nested c₁ c₂ g₁ g₂ hlt h₁ h₂ ⟨E, rho⟩ hv,
      fun g hg V _ _ E rho hv => (h V).finalMonotone g hg ⟨E, rho⟩ hv,
      fun g hg V _ _ E rho hv => (h V).finalAccountable g hg ⟨E, rho⟩ hv trivial,
      fun g hg i gst V _ _ E rho hv hH hp => (h V).finalLive g hg i gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun cap g hc hg V _ _ E rho hv hS => (h V).sleepySafe cap g hc hg ⟨E, rho⟩ hv hS,
      fun cap g hc hg i V _ _ E rho hv hS hp =>
        (h V).sleepyLive cap g hc hg i ⟨E, rho⟩ hv ⟨hS, hp⟩,
      fun cap g hc hg i gst V _ _ E rho hv hH hp =>
        (h V).healedSafe cap g hc hg i gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun cap g hc hg i gst V _ _ E rho hv hH hp =>
        (h V).healedLive cap g hc hg i gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun g hg T b₀ b₁ V _ _ E rho hv hO => (h V).persists g hg T b₀ b₁ ⟨E, rho⟩ hv hO⟩
  · intro h V _ _
    exact ⟨fun r hv => h.outputValid V r.1 r.2 hv,
      fun c₁ c₂ g₁ g₂ hlt h₁ h₂ r hv => h.nested c₁ c₂ g₁ g₂ hlt h₁ h₂ V r.1 r.2 hv,
      fun g hg r hv => h.finalMonotone g hg V r.1 r.2 hv,
      fun g hg r hv _ => h.finalAccountable g hg V r.1 r.2 hv,
      fun g hg i gst r hv hA => h.finalLive g hg i gst V r.1 r.2 hv hA.1 hA.2,
      fun cap g hc hg r hv hS => h.sleepySafe cap g hc hg V r.1 r.2 hv hS,
      fun cap g hc hg i r hv hA => h.sleepyLive cap g hc hg i V r.1 r.2 hv hA.1 hA.2,
      fun cap g hc hg i gst r hv hA => h.healedSafe cap g hc hg i gst V r.1 r.2 hv hA.1 hA.2,
      fun cap g hc hg i gst r hv hA => h.healedLive cap g hc hg i gst V r.1 r.2 hv hA.1 hA.2,
      fun g hg T b₀ b₁ r hv hO => h.persists g hg T b₀ b₁ V r.1 r.2 hv hO⟩

end Claims

/-! ## B5 (sheet): extras through `sysOf`, `ServedFrom` inlined, shared
`ReadyNestedFrom`, the pinned durations at a run -/

section Sheet

open Consensus.Model (sysOf)

variable {Info : Type} [DecidableEq Info] [Countable Info]

/-- The healing cut for finality at index `gf` after GST `gst`:
`max gst 0 + (29 + B_H^F(gf·R))·Δ`, the final heal point minus `W_W(gf)·Δ`
(intended: `t_ready + B_H^F`). -/
def OldFinalCut (pp : FGSAParams) (gf : ℕ+) (gst Δ : Time) : Time :=
  max gst 0 + ((29 + pp.bhf (gf * pp.R) : Nat) : Time) * Δ

section Vocab

variable {O : OutputSchema} {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

/-- Persistent inclusion: header `h` is in the `g`-read of every node ready at
every time of `[d, horizon]`. -/
def OldServedFrom (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (h : Header Info)
    (d : Time) : Prop :=
  ∀ t, d ≤ t → t ≤ rho.horizon → InBy rho c g h t

/-- Inclusion of honest proposals from `start`: every honest proposal released
at `τ ≥ start` by a key ready at `τ` is served (persistently) from
`τ + D·Δ`. -/
def OldIncludesFrom (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time)
    (D : Nat) : Prop :=
  ∀ τ k h, start ≤ τ → rho.point.Ready c (rho.key k) τ → HonestProposal rho τ k h →
    OldServedFrom rho c g h (τ + (D : Time) * E.Δ)

theorem includesFrom_iff (rho : Model.Run (compiled F) E) (c : Time) (g : O.Id) (start : Time)
    (D : Nat) : IncludesFrom rho c g start D ↔ OldIncludesFrom rho c g start D := Iff.rfl

end Vocab

section Extras

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The weak-continuation premise at gap `k` after GST `gst`: partially
synchronous with GST `gst` (the whole run), healthy (a fixed set of more than
`φ·n` honest validators continuously awake) up to the heal point, one honest
ready proposer per window of `k` slots on `[readyFrom, heal]`, and sleepy
participation from the heal point to the horizon. No recurrence after the
heal point. -/
def OldWeakPremise {F : ShapeFamily goldilocksSchema Info} (pp : FGSAParams)
    (rho : Model.Run (compiled F) E) (gst : Time) (k : ℕ+) : Prop :=
  CommLog.PSync rho.point rho.log gst ∧
    rho.point.HealthyOn (goldilocksContract pp).params.φ gst
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) ∧
    OldShapeProg (goldilocksContract pp) rho .available k
      (OldShapeReady (goldilocksContract pp) rho gst)
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) ∧
    rho.point.SleepyOn (goldilocksContract pp).params.θ (OldShapeC (goldilocksContract pp) rho)
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) rho.horizon

end Extras

/-- The Goldilocks extras: intended properties beyond the fixed L0 table
(statements; FG-SA's migration proves them). Every claim is on every valid
run of the compiled family, for every finite validator set and environment,
"or an observed hash collision". Regimes are the L0 ones at the pinned
numbers (`OldShapeSleepy`, `OldShapeHealthy`, `OldShapeProg` at
`goldilocksContract pp`); `c = 18·Δ`; heal points from `max g 0`. -/
structure OldGoldilocksExtra (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) : Prop where
  /-- **L1 / P-SYNC-AV-INCLUDE.** Sleepy: every honest proposal released at
  `τ` by a key ready at `τ` is in every ready confirmed read at every
  `t ∈ [τ + 6Δ, horizon]`. -/
  includeSleepy : OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeSleepy (goldilocksContract pp) rho →
    OldIncludesFrom rho (OldShapeC (goldilocksContract pp) rho) gConfirmed 0 6 ∨ rho.HashCollision
  /-- **L4 / P-GST-AV-INCLUDE.** Healthy from `gst` with one honest ready
  proposer per window of `k` slots on `[readyFrom, heal]`: the same for
  proposals released at `τ ≥ heal`. -/
  includeHealed : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .available k (OldShapeReady (goldilocksContract pp) rho gst)
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) →
    OldIncludesFrom rho (OldShapeC (goldilocksContract pp) rho) gConfirmed
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) 6 ∨ rho.HashCollision
  /-- **L3 / P-SYNC-AV-GROW** (block level). Sleepy with one honest ready
  proposer per window of `k` slots: joint strict growth of the confirmed
  output by `t + (4k + 6)·Δ`. -/
  growSleepy : ∀ k : ℕ+, OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeSleepy (goldilocksContract pp) rho →
    OldShapeProg (goldilocksContract pp) rho .available k 0 rho.horizon →
    CrossGrowth rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gConfirmed 0 (4 * k + 6) ∨
      rho.HashCollision
  /-- **L5 / P-GST-AV-GROW** (block level). Healthy from `gst` with the
  recurrence of `k` from `readyFrom`: joint strict growth from the heal
  point. -/
  growHealed : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .available k (OldShapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    CrossGrowth rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) (4 * k + 6) ∨ rho.HashCollision
  /-- **FL1 / P-GST-FIN-FIRST.** Healthy from `gst` with the finality
  recurrence of `gf` on `[readyFrom, heal]`: a new finalized entry, strictly
  above every ready confirmed read at the healing cut
  `OldFinalCut = max gst 0 + (29 + B_H^F(gf·R))·Δ`, is in every ready finalized
  read at the first-finality point `OldFinalCut + W_W(gf)·Δ` (the final heal
  point). -/
  finalFirst : ∀ (gf : ℕ+) (gst : Time), OldAllRuns F fun E rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .final gf (OldShapeReady (goldilocksContract pp) rho gst)
      (OldShapeHeal (goldilocksContract pp) rho .final gf gst) →
    OldShapeHeal (goldilocksContract pp) rho .final gf gst ≤ rho.horizon →
    (∃ h, NewAbove rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gFinalized
      (fun x => rho.point.Ready (OldShapeC (goldilocksContract pp) rho) x (OldFinalCut pp gf gst E.Δ))
      (OldFinalCut pp gf gst E.Δ) (OldShapeHeal (goldilocksContract pp) rho .final gf gst) h) ∨
      rho.HashCollision
  /-- **FL2 / P-GST-FIN-RECUR.** Healthy from `gst` with the finality
  recurrence of `gf` from `readyFrom`: for every `t` from the healing cut
  `OldFinalCut`, a new finalized entry strictly above every ready confirmed read
  at `t` is in every ready finalized read at `t + W_W(gf)·Δ`. -/
  finalRecur : ∀ (gf : ℕ+) (gst : Time), OldAllRuns F fun E rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .final gf (OldShapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    (∀ t, OldFinalCut pp gf gst E.Δ ≤ t → t + ((pp.wW gf : Nat) : Time) * E.Δ ≤ rho.horizon →
      ∃ h, NewAbove rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gFinalized
        (fun x => rho.point.Ready (OldShapeC (goldilocksContract pp) rho) x t) t
        (t + ((pp.wW gf : Nat) : Time) * E.Δ) h) ∨ rho.HashCollision
  /-- **FL5** (LiveDC). Healthy from `gst` with the finality recurrence of
  `gf` from `readyFrom`: for every `t` from the first-finality point, an
  honest proposal released after `t` strictly extends every ready confirmed
  read at `t` and is in every ready finalized read by
  `t + (2·W_W(gf) + 4·gf·R)·Δ`. -/
  liveDC : ∀ (gf : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .final gf (OldShapeReady (goldilocksContract pp) rho gst)
      rho.horizon →
    CrossGrowth rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gFinalized
      (OldShapeHeal (goldilocksContract pp) rho .final gf gst) (2 * pp.wW gf + 4 * (gf * pp.R)) ∨
      rho.HashCollision
  /-- **A4 part / P-GST-CROSS-NEST.** Healthy from `gst` with the recurrence of
  `k` on `[readyFrom, heal]`: from the heal point, every ready finalized read
  is a prefix of every ready confirmed read at the same time. -/
  crossNest : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldShapeHealthy (goldilocksContract pp) rho gst →
    OldShapeProg (goldilocksContract pp) rho .available k (OldShapeReady (goldilocksContract pp) rho gst)
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) →
    (∀ t, OldShapeHeal (goldilocksContract pp) rho .available k gst ≤ t → t ≤ rho.horizon →
      ∀ x y, rho.point.Ready (OldShapeC (goldilocksContract pp) rho) x t →
        rho.point.Ready (OldShapeC (goldilocksContract pp) rho) y t →
        (chainTrace rho).readAt gFinalized x t <+: (chainTrace rho).readAt gConfirmed y t) ∨
      rho.HashCollision
  /-- **A2 / P-OUT-AV-SLOW.** Outage times, synchronous for deadlines up to
  `b₀`, η-sleepy on the prefix `[0, b₀]` only, more than half ready at `b₀`,
  and **no** assumption after `b₀` (neither network nor participation:
  participation may collapse inside the outage): what a node ready at `T`
  reads as confirmed is kept by every eligible reader (ready at `b₀` and awake
  since) at every time of `[b₀, b₁)` within the horizon. -/
  outageWindow : ∀ T b₀ b₁ : Time, OldAllRuns F fun E rho => rho.ExecutionValid →
    OutageTimes (goldilocksContract pp).params E.Δ T b₀ b₁ →
    CommLog.SyncUntil rho.point rho.log b₀ →
    rho.point.EtaSleepyOn (goldilocksContract pp).params.θ
      ((goldilocksContract pp).params.ηDur E.Δ) (OldShapeC (goldilocksContract pp) rho) 0 b₀ →
    rho.point.ReadyOfAll (goldilocksContract pp).params.cover
      (OldShapeC (goldilocksContract pp) rho) b₀ →
    (chainTrace rho).ProtectedUpTo (OldShapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      T b₀ b₁ (min (b₁ - 1) rho.horizon) ∨ rho.HashCollision
  /-- **P-WEAK-AV-SAFE.** Under the weak-continuation premise (healthy up to
  the heal point, sleepy after it, no recurrence after it): ready-reader
  safety of the confirmed output from the heal point. -/
  weakSafe : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldWeakPremise pp rho gst k →
    (chainTrace rho).ReadySafe (OldShapeC (goldilocksContract pp) rho) gConfirmed
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) ∨ rho.HashCollision
  /-- **P-WEAK-AV-SAFE, nesting conjunct.** Under the weak-continuation
  premise: from the heal point, every ready finalized read is a prefix of every
  ready confirmed read at the same time (`F_x ⪯ S_y`). -/
  weakCrossNest : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldWeakPremise pp rho gst k →
    (∀ t, OldShapeHeal (goldilocksContract pp) rho .available k gst ≤ t → t ≤ rho.horizon →
      ∀ x y, rho.point.Ready (OldShapeC (goldilocksContract pp) rho) x t →
        rho.point.Ready (OldShapeC (goldilocksContract pp) rho) y t →
        (chainTrace rho).readAt gFinalized x t <+: (chainTrace rho).readAt gConfirmed y t) ∨
      rho.HashCollision
  /-- **P-WEAK-AV-INCLUDE.** Under the weak-continuation premise: every honest
  proposal released at `τ ≥ heal + 2` slots (`8Δ`) by a key ready at `τ` is in
  every ready confirmed read at every `t ∈ [τ + 6Δ, horizon]`. -/
  weakInclude : ∀ (k : ℕ+) (gst : Time), OldAllRuns F fun E rho => rho.ExecutionValid →
    OldWeakPremise pp rho gst k →
    OldIncludesFrom rho (OldShapeC (goldilocksContract pp) rho) gConfirmed
      (OldShapeHeal (goldilocksContract pp) rho .available k gst + 8 * E.Δ) 6 ∨ rho.HashCollision
  /-- **P-WEAK-AV-GROW.** Under the weak-continuation premise and one honest
  ready proposer per window of `k'` slots from the heal point: joint strict
  growth of the confirmed output from the heal point by `t + (4k' + 6)·Δ`. -/
  weakGrow : ∀ (k k' : ℕ+) (gst : Time), OldAllRuns F fun _ rho => rho.ExecutionValid →
    OldWeakPremise pp rho gst k →
    OldShapeProg (goldilocksContract pp) rho .available k'
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) rho.horizon →
    CrossGrowth rho (OldShapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      (OldShapeHeal (goldilocksContract pp) rho .available k gst) (4 * k' + 6) ∨ rho.HashCollision


theorem weakPremise_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {F : ShapeFamily goldilocksSchema Info} (pp : FGSAParams)
    (rho : Model.Run (compiled F) E) (gst : Time) (k : ℕ+) :
    WeakPremise pp gst k (⟨E, rho⟩ : (Sys F V).Run) ↔ OldWeakPremise pp rho gst k := Iff.rfl

theorem finalCut_eq {V : Type} [Fintype V] [DecidableEq V] (pp : FGSAParams) {F : ShapeFamily goldilocksSchema Info} (gf : ℕ+)
    (gst : Time) (r : (Sys F V).Run) :
    finalCut pp gf gst r = OldFinalCut pp gf gst ((Sys F V).pt r).env.Δ := rfl

/-- The extras through `sysOf` are the old `AllRuns` form (curried premises,
`ServedFrom`, the cross-nesting conclusion written out, the regime
abbreviations). -/
theorem goldilocksExtra_iff (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) :
    GoldilocksExtra F pp ↔ OldGoldilocksExtra F pp := by
  constructor
  · intro h
    exact ⟨fun V _ _ E rho hv hS => (h V).includeSleepy ⟨E, rho⟩ hv hS,
      fun k gst V _ _ E rho hv hH hp => (h V).includeHealed k gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun k V _ _ E rho hv hS hp => (h V).growSleepy k ⟨E, rho⟩ hv ⟨hS, hp⟩,
      fun k gst V _ _ E rho hv hH hp => (h V).growHealed k gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun gf gst V _ _ E rho hv hH hp hh => (h V).finalFirst gf gst ⟨E, rho⟩ hv ⟨hH, hp, hh⟩,
      fun gf gst V _ _ E rho hv hH hp => (h V).finalRecur gf gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun gf gst V _ _ E rho hv hH hp => (h V).liveDC gf gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun k gst V _ _ E rho hv hH hp => (h V).crossNest k gst ⟨E, rho⟩ hv ⟨hH, hp⟩,
      fun T b₀ b₁ V _ _ E rho hv hT hs hη hc =>
        (h V).outageWindow T b₀ b₁ ⟨E, rho⟩ hv ⟨hT, hs, hη, hc⟩,
      fun k gst V _ _ E rho hv hW => (h V).weakSafe k gst ⟨E, rho⟩ hv hW,
      fun k gst V _ _ E rho hv hW => (h V).weakCrossNest k gst ⟨E, rho⟩ hv hW,
      fun k gst V _ _ E rho hv hW => (h V).weakInclude k gst ⟨E, rho⟩ hv hW,
      fun k k' gst V _ _ E rho hv hW hp => (h V).weakGrow k k' gst ⟨E, rho⟩ hv ⟨hW, hp⟩⟩
  · intro h V _ _
    exact ⟨fun r hv hS => h.includeSleepy V r.1 r.2 hv hS,
      fun k gst r hv hA => h.includeHealed k gst V r.1 r.2 hv hA.1 hA.2,
      fun k r hv hA => h.growSleepy k V r.1 r.2 hv hA.1 hA.2,
      fun k gst r hv hA => h.growHealed k gst V r.1 r.2 hv hA.1 hA.2,
      fun gf gst r hv hA => h.finalFirst gf gst V r.1 r.2 hv hA.1 hA.2.1 hA.2.2,
      fun gf gst r hv hA => h.finalRecur gf gst V r.1 r.2 hv hA.1 hA.2,
      fun gf gst r hv hA => h.liveDC gf gst V r.1 r.2 hv hA.1 hA.2,
      fun k gst r hv hA => h.crossNest k gst V r.1 r.2 hv hA.1 hA.2,
      fun T b₀ b₁ r hv hA => h.outageWindow T b₀ b₁ V r.1 r.2 hv hA.1 hA.2.1 hA.2.2.1 hA.2.2.2,
      fun k gst r hv hW => h.weakSafe k gst V r.1 r.2 hv hW,
      fun k gst r hv hW => h.weakCrossNest k gst V r.1 r.2 hv hW,
      fun k gst r hv hW => h.weakInclude k gst V r.1 r.2 hv hW,
      fun k k' gst r hv hA => h.weakGrow k k' gst V r.1 r.2 hv hA.1 hA.2⟩

end Sheet

/-! ## B5 (L2): `RealizableActive` over system runs, and `regimes_realizable` -/

section Realize

open Consensus.Model (sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- The old `RealizableActive` (environment and run separately, the regime
abbreviations). -/
structure OldRealizableActive (F : ShapeFamily O Info) (K : Contract ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] : Prop where
  sleepyActive : ∀ cap i (Δ : Time), 0 < Δ → ∃ (E : Env V) (rho : Model.Run (compiled F) E),
    (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧ OldShapeSleepy K rho ∧
      OldShapeProg K rho cap i 0 rho.horizon ∧ ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive (OldShapeC K rho) 0
        ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩)
  healthyActive : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g →
    ∃ (E : Env V) (rho : Model.Run (compiled F) E),
      (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧
      CommLog.EagerFrom ((sysOf O (compiled F) V).pt ⟨E, rho⟩)
        ((sysOf O (compiled F) V).log ⟨E, rho⟩) g ∧ OldShapeHealthy K rho g ∧
      OldShapeProg K rho cap i (OldShapeReady K rho g) rho.horizon ∧
      ProgressActive F K cap i (OldShapeReady K rho g) rho ∧
      rho.point.TxLiveActive (OldShapeC K rho)
        (OldShapeHeal K rho cap i g) ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩) ∧
      SafeActive (OldShapeC K rho) (OldShapeHeal K rho cap i g) rho.point
  /-- Sleepy liveness and progress are active below an awake supermajority. -/
  sleepyStress : ∀ cap, (cap = .available ∨ cap = .stable) → (O.output cap).isSome →
    ∀ Δ : Time, 0 < Δ → ∃ (i : K.Idx) (E : Env V) (rho : Model.Run (compiled F) E),
      (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧ OldShapeSleepy K rho ∧
      OldShapeProg K rho cap i 0 rho.horizon ∧ ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive (OldShapeC K rho) 0
        ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩) ∧
      rho.point.AwakeAtMost (2 * Fintype.card V / 3)
  /-- Healthy liveness and progress are active at a minimal awake supermajority. -/
  healthyStress : ∀ cap, (O.output cap).isSome → ∀ (Δ g : Time), 0 < Δ → 0 ≤ g →
    ∃ (i : K.Idx) (E : Env V) (rho : Model.Run (compiled F) E),
      (sysOf O (compiled F) V).Witness ⟨E, rho⟩ ∧ E.Δ = Δ ∧
      CommLog.EagerFrom ((sysOf O (compiled F) V).pt ⟨E, rho⟩)
        ((sysOf O (compiled F) V).log ⟨E, rho⟩) g ∧ OldShapeHealthy K rho g ∧
      OldShapeProg K rho cap i (OldShapeReady K rho g) rho.horizon ∧
      ProgressActive F K cap i (OldShapeReady K rho g) rho ∧
      rho.point.TxLiveActive (OldShapeC K rho)
        (OldShapeHeal K rho cap i g) ((sysOf O (compiled F) V).lat K cap i ⟨E, rho⟩) ∧
      rho.point.AwakeAtMost (2 * Fintype.card V / 3 + 1)
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁,
    (sysOf O (compiled F) V).Witness r ∧ ((sysOf O (compiled F) V).pt r).env.Δ = Δ ∧
      (sysOf O (compiled F) V).Outage K T b₀ b₁ r ∧
      OutageActive ((sysOf O (compiled F) V).cDur K r) T b₀ b₁ ((sysOf O (compiled F) V).pt r) ∧
      (k : Time) * Δ ≤ T

theorem realizableActive_iff (F : ShapeFamily O Info) (K : Contract ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] : RealizableActive F K V ↔ OldRealizableActive F K V := by
  constructor
  · intro h
    refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_, fun cap hc ho Δ hΔ => ?_,
      fun cap ho Δ g hΔ hg => ?_, h.outage⟩
    · obtain ⟨⟨E, rho⟩, hw, hd, ⟨hs, hp, ht⟩, hpa⟩ := h.sleepy cap i Δ hΔ
      exact ⟨E, rho, hw, hd, hs, hp, hpa, ht⟩
    · obtain ⟨⟨E, rho⟩, hw, hd, ⟨he, hs, hp, ht⟩, hsa, hpa⟩ := h.healthy cap i Δ g hΔ hg
      exact ⟨E, rho, hw, hd, he, hs, hp, hpa, ht, hsa⟩
    · obtain ⟨i, ⟨E, rho⟩, hw, hd, ⟨hs, hp, hl⟩, hb, hpa⟩ := h.sleepyStress cap hc ho Δ hΔ
      exact ⟨i, E, rho, hw, hd, hs, hp, hpa, hl, hb⟩
    · obtain ⟨i, ⟨E, rho⟩, hw, hd, ⟨he, hs, hp, hl⟩, hb, hpa⟩ := h.healthyStress cap ho Δ g hΔ hg
      exact ⟨i, E, rho, hw, hd, he, hs, hp, hpa, hl, hb⟩
  · intro h
    refine ⟨fun cap i Δ hΔ => ?_, fun cap i Δ g hΔ hg => ?_, fun cap hc ho Δ hΔ => ?_,
      fun cap ho Δ g hΔ hg => ?_, h.outage⟩
    · obtain ⟨E, rho, hw, hd, hs, hp, hpa, ht⟩ := h.sleepyActive cap i Δ hΔ
      exact ⟨⟨E, rho⟩, hw, hd, ⟨hs, hp, ht⟩, hpa⟩
    · obtain ⟨E, rho, hw, hd, he, hs, hp, hpa, ht, hsa⟩ := h.healthyActive cap i Δ g hΔ hg
      exact ⟨⟨E, rho⟩, hw, hd, ⟨he, hs, hp, ht⟩, hsa, hpa⟩
    · obtain ⟨i, E, rho, hw, hd, hs, hp, hpa, hl, hb⟩ := h.sleepyStress cap hc ho Δ hΔ
      exact ⟨i, ⟨E, rho⟩, hw, hd, ⟨hs, hp, hl⟩, hb, hpa⟩
    · obtain ⟨i, E, rho, hw, hd, he, hs, hp, hpa, hl, hb⟩ := h.healthyStress cap ho Δ g hΔ hg
      exact ⟨i, ⟨E, rho⟩, hw, hd, ⟨he, hs, hp, hl⟩, hb, hpa⟩

/-- The old conclusion of `regimes_realizable` (`Realizable ∧ RealizableActive`)
follows from the new one. -/
theorem regimes_realizable_old (F : ShapeFamily O Info) (K : Contract ProgressReq)
    (ha : K.params.Admissible) (hf : ProgressFits K F) (ht : ProgressTolerant O K)
    (V : Type) [Fintype V] [DecidableEq V] (hn : 5 ≤ Fintype.card V) :
    Realizable (sysOf O (compiled F) V) (shapeProgress F V) K ∧ OldRealizableActive F K V :=
  ⟨(regimes_realizable F K ha hf ht V hn).toRealizable,
    (realizableActive_iff F K V).mp (regimes_realizable F K ha hf ht V hn)⟩

end Realize

/-! ## B5 (Blocks): recurrence over a slot selection, `Ready` includes honest,
one window premise -/

section Recurrence

variable {V : Type} [Fintype V] {R : Type}

/-- The old `HonestReadyIn` (role selection, separate honesty conjunct). -/
def OldHonestReadyIn (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (r : R) (c t : Time) : Prop :=
  (sel r).Nonempty ∧ ∀ k ∈ sel r, key k ∈ p.honest ∧ p.Ready c (key k) t

/-- The old `PatternRecurrence` (roles `lead s`, window premise
`start ≤ t → 0 ≤ t`). -/
def OldPatternRecurrence (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (lead : Slot → R) (G : TimeGrid)
    (ρ : Recurrence) (c start stop : Time) : Prop :=
  ∀ t, start ≤ t → 0 ≤ t → t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop →
    t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon →
    ∃ s, t < G.slotTime p.env.Δ s ∧
      G.slotTime p.env.Δ s ≤ t + ((ρ.gap : Nat) : Time) * G.slotLen p.env.Δ ∧
      ∀ j ∈ ρ.pattern.offsets,
        OldHonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j))

theorem honestReadyIn_iff (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (lead : Slot → R) (s : Slot) (c t : Time) :
    HonestReadyIn p key (fun s => sel (lead s)) s c t ↔ OldHonestReadyIn p key sel (lead s) c t :=
  and_congr_right fun _ => forall₂_congr fun _ _ => ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

theorem patternRecurrence_iff (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (lead : Slot → R) (G : TimeGrid)
    (ρ : Recurrence) (c start stop : Time) :
    PatternRecurrence p key (fun s => sel (lead s)) G ρ c start stop ↔
      OldPatternRecurrence p key sel lead G ρ c start stop := by
  unfold PatternRecurrence OldPatternRecurrence
  simp only [max_le_iff, honestReadyIn_iff]
  exact forall_congr' fun t => ⟨fun h h1 h2 => h ⟨h1, h2⟩, fun h hm => h hm.1 hm.2⟩

end Recurrence

end Consensus.Shape.Tests.Reformulations

end
