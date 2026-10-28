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
  `Run.signerOf` on objects; the `sysOf` log is the tagged run log. -/

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

variable {Info : Type} [DecidableEq Info] [Encodable Info]

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

end Consensus.Shape.Tests.Reformulations

end
