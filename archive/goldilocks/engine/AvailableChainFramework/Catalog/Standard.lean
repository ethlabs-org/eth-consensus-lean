module
public import AvailableChainFramework.Catalog.Core
public import AvailableChainFramework.Catalog.Mono

@[expose] public section

/-! The standard tier (design §4). Each claim restates one field of the v1
bundle `AvailableChain` (`AvailableChainStatements/Generic/Claims.lean`). The
constant of a claim holds exactly the constants that its regime and its
conclusion read; the other fields of `Constants` come from `zeroConstants`.
The `le_trans` and `transport` proofs are named theorems, so that the lock
hashes their statements only. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- The constant of the Stable Sleepy inclusion claim. -/
structure EtaConst where
  η : Time
  θ : ℚ
  D : Time

/-- The bounds of `Constants.Valid` on the fields of `EtaConst`. -/
def EtaConst.Valid (k : EtaConst) : Prop :=
  0 ≤ k.η ∧ (1 / 2 : ℚ) ≤ k.θ ∧ k.θ ≤ (3 / 4 : ℚ) ∧ 0 ≤ k.D

/-- `b` is at least as weak as `a`: η ↑, θ ↑, the delay is fixed. -/
def EtaConst.le (a b : EtaConst) : Bool :=
  decide (a.η ≤ b.η ∧ a.θ ≤ b.θ ∧ a.D = b.D)

/-- The constant of the two persistence claims. -/
structure OutageConst where
  η : Time
  θ : ℚ
  /-- The arming lag (`armingLag`, or `fastArmingLag` for the fast claim). -/
  lag : Time
  /-- Π, the outage budget. (`Π` is a Lean keyword, so the field is `budget`.) -/
  budget : Time

/-- The bounds of `Constants.Valid` on the fields of `OutageConst`. -/
def OutageConst.Valid (k : OutageConst) : Prop :=
  0 ≤ k.η ∧ (1 / 2 : ℚ) ≤ k.θ ∧ k.θ ≤ (3 / 4 : ℚ) ∧ 0 ≤ k.lag ∧ 0 ≤ k.budget ∧
    k.budget ≤ k.η

/-- `b` is at least as weak as `a`: η ↑, θ ↑, lag ↑, budget ↓. -/
def OutageConst.le (a b : OutageConst) : Bool :=
  decide (a.η ≤ b.η ∧ a.θ ≤ b.θ ∧ a.lag ≤ b.lag ∧ b.budget ≤ a.budget)

/-- The constant of the recovery claim. -/
structure RecoveryConst where
  θrec : ℚ
  full : Bool
  G : Time
  ρ : Time
  D_c : Time
  D_s : Time

/-- The bounds of `Constants.Valid` on the fields of `RecoveryConst`. -/
def RecoveryConst.Valid (k : RecoveryConst) : Prop :=
  (1 / 2 : ℚ) ≤ k.θrec ∧ k.θrec ≤ (3 / 4 : ℚ) ∧ 0 < k.G ∧ 0 ≤ k.ρ ∧ 0 ≤ k.D_c ∧
    0 ≤ k.D_s

/-- `b` is at least as weak as `a`: θrec ↑, `full` false → true, G ↓, ρ ↑, the
delays are fixed. -/
def RecoveryConst.le (a b : RecoveryConst) : Bool :=
  decide (a.θrec ≤ b.θrec ∧ (a.full = true → b.full = true) ∧ b.G ≤ a.G ∧ a.ρ ≤ b.ρ ∧
    a.D_c = b.D_c ∧ a.D_s = b.D_s)

/-! ### `includedStable`: the bundle field `stableIncluded` -/

theorem includedStable_le_trans (a b c : EtaConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂, h₃⟩ := of_decide_eq_true hab
  obtain ⟨h₄, h₅, h₆⟩ := of_decide_eq_true hbc
  exact decide_eq_true ⟨h₁.trans h₄, h₂.trans h₅, h₃.trans h₆⟩

theorem includedStable_transport (I : Instance) (k k' : EtaConst) (hk : k.Valid)
    (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      StableSleepyRegime I.P x.E I.iface { zeroConstants with η := k.η, θ := k.θ } x.rho
        t₀ →
      IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ k.D) :
    ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      StableSleepyRegime I.P x.E I.iface { zeroConstants with η := k'.η, θ := k'.θ } x.rho
        t₀ →
      IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ k'.D := by
  obtain ⟨hη, hθ, hD⟩ := of_decide_eq_true hle
  intro W x hx t₀ hr
  rw [← hD]
  exact h W x hx t₀ (stableSleepyRegime_mono hθ hη (le_trans (by norm_num) hk.2.1) hr)

/-- Exact-time inclusion of honest proposals in `stable`, Stable Sleepy regime. -/
def includedStable : ClaimSpec ClaimDomain.v1 where
  id := `std.included.stable.v1
  Const := EtaConst
  valid := EtaConst.Valid
  le := EtaConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl, rfl⟩
  le_trans := includedStable_le_trans
  Point := Time
  regime := fun I k _ x t₀ =>
    StableSleepyRegime I.P x.E I.iface { zeroConstants with η := k.η, θ := k.θ } x.rho t₀
  conclusion := fun I k _ x t₀ => IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ k.D
  trigger := fun I k _ x t₀ H =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + k.D ≤ x.rho.horizon
  transport := includedStable_transport
  refutable := .family

theorem includedStable_trigger_late {I : Instance} {k : EtaConst} {H : Time}
    (h : includedStable.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-! ### `includedStableFast`: the bundle field `stableIncludedFast` -/

theorem includedStableFast_le_trans (a b c : Time) (hab : decide (a = b) = true)
    (hbc : decide (b = c) = true) : decide (a = c) = true :=
  decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))

theorem includedStableFast_transport (I : Instance) (k k' : Time) (_hk : 0 ≤ k)
    (_hk' : 0 ≤ k') (hle : decide (k = k') = true)
    (h : ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      FastRegime I.P x.E I.iface x.rho t₀ →
      IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ k) :
    ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      FastRegime I.P x.E I.iface x.rho t₀ →
      IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ k' := by
  have : k = k' := of_decide_eq_true hle
  subst this; exact h

/-- Exact-time inclusion of honest proposals in `stable`, Fast regime. `D` is
fixed: `le` is equality. -/
def includedStableFast : ClaimSpec ClaimDomain.v1 where
  id := `std.included.stableFast.v1
  Const := Time
  valid := fun D => 0 ≤ D
  le := fun a b => decide (a = b)
  le_refl := fun _ => decide_eq_true rfl
  le_trans := includedStableFast_le_trans
  Point := Time
  regime := fun I _ _ x t₀ => FastRegime I.P x.E I.iface x.rho t₀
  conclusion := fun I D _ x t₀ => IncludedFrom I.P x.E I.iface x.rho I.iface.stable t₀ D
  trigger := fun I D _ x t₀ H =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + D ≤ x.rho.horizon
  transport := includedStableFast_transport
  refutable := .family

theorem includedStableFast_trigger_late {I : Instance} {D : Time} {H : Time}
    (h : includedStableFast.inhabited I D) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-! ### `persistOutage`: the bundle field `stableResilient` -/

theorem persistOutage_le_trans (a b c : OutageConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := of_decide_eq_true hab
  obtain ⟨h₅, h₆, h₇, h₈⟩ := of_decide_eq_true hbc
  exact decide_eq_true ⟨h₁.trans h₅, h₂.trans h₆, h₃.trans h₇, h₈.trans h₄⟩

theorem persistOutage_transport (I : Instance) (k k' : OutageConst) (hk : k.Valid)
    (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ p : Time × Time × Time,
      OutageRegime I.P x.E I.iface
        { zeroConstants with η := k.η, θ := k.θ, armingLag := k.lag, budget := k.budget }
        x.rho p.1 p.2.1 p.2.2 →
      PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2) :
    ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ p : Time × Time × Time,
      OutageRegime I.P x.E I.iface
        { zeroConstants with η := k'.η, θ := k'.θ, armingLag := k'.lag, budget := k'.budget }
        x.rho p.1 p.2.1 p.2.2 →
      PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2 := by
  obtain ⟨hη, hθ, hA, hB⟩ := of_decide_eq_true hle
  intro W x hx p hr
  exact h W x hx p (outageRegime_mono hθ hη (le_trans (by norm_num) hk.2.1) hA hB hr)

/-- The trigger of a persistence claim at `p = (T, b₀, b₁)`: the protected
read is at a time of at least `H`, the outage window is not empty (Review
Focus 6), and some honest read of `stable` at `T` is not genesis. -/
def persistTrigger (I : Instance) (W : Validators) (x : V1Ctx I W)
    (p : Time × Time × Time) (H : Time) : Prop :=
  H ≤ p.1 ∧ p.2.1 < p.2.2 ∧
    ∃ v ∈ x.rho.honest, readAt I.P x.rho I.iface.stable v p.1 ≠ .genesis

/-- Persistence of `stable` through an outage window, Outage regime. -/
def persistOutage : ClaimSpec ClaimDomain.v1 where
  id := `std.persist.outage.v1
  Const := OutageConst
  valid := OutageConst.Valid
  le := OutageConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans := persistOutage_le_trans
  Point := Time × Time × Time
  regime := fun I k _ x p =>
    OutageRegime I.P x.E I.iface
      { zeroConstants with η := k.η, θ := k.θ, armingLag := k.lag, budget := k.budget }
      x.rho p.1 p.2.1 p.2.2
  conclusion := fun I _ _ x p => PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2
  trigger := fun I _ W x p H => persistTrigger I W x p H
  transport := persistOutage_transport
  refutable := .run

theorem persistOutage_trigger_late {I : Instance} {k : OutageConst} {H : Time}
    (h : persistOutage.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (T b₀ b₁ : Time),
      H ≤ T ∧ b₀ < b₁ ∧
        ∃ v ∈ x.rho.honest, readAt I.P x.rho I.iface.stable v T ≠ .genesis := by
  obtain ⟨W, x, ⟨T, b₀, b₁⟩, _, _, _, hH, hb, hv⟩ := h H
  exact ⟨W, x, T, b₀, b₁, hH, hb, hv⟩

/-- Review Focus 6: at `budget = 0` the regime forces `b₁ ≤ b₀`, and the
trigger needs `b₀ < b₁`, so no inhabitation witness exists. -/
theorem persistOutage_no_witness_at_zero_budget (I : Instance) (k : OutageConst)
    (hk : k.budget = 0) : ¬ persistOutage.inhabited I k := by
  intro h
  obtain ⟨_, _, _, _, _, hr, _, hb, _⟩ := h 0
  have hw := hr.withinBudget
  simp only [hk] at hw
  linarith

/-! ### `persistOutageFast`: the bundle field `stableResilientFast` -/

theorem persistOutageFast_le_trans (a b c : OutageConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true :=
  persistOutage_le_trans a b c hab hbc

theorem persistOutageFast_transport (I : Instance) (k k' : OutageConst) (hk : k.Valid)
    (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ p : Time × Time × Time,
      FastOutageRegime I.P x.E I.iface
        { zeroConstants with η := k.η, θ := k.θ, fastArmingLag := k.lag, budget := k.budget }
        x.rho p.1 p.2.1 p.2.2 →
      PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2) :
    ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ p : Time × Time × Time,
      FastOutageRegime I.P x.E I.iface
        { zeroConstants with
          η := k'.η, θ := k'.θ, fastArmingLag := k'.lag, budget := k'.budget }
        x.rho p.1 p.2.1 p.2.2 →
      PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2 := by
  obtain ⟨hη, hθ, hA, hB⟩ := of_decide_eq_true hle
  intro W x hx p hr
  exact h W x hx p (fastOutageRegime_mono hθ hη (le_trans (by norm_num) hk.2.1) hA hB hr)

/-- Persistence of `stable` through an outage window, Fast Outage regime. The
`lag` of the constant is the fast arming lag. -/
def persistOutageFast : ClaimSpec ClaimDomain.v1 where
  id := `std.persist.outageFast.v1
  Const := OutageConst
  valid := OutageConst.Valid
  le := OutageConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans := persistOutageFast_le_trans
  Point := Time × Time × Time
  regime := fun I k _ x p =>
    FastOutageRegime I.P x.E I.iface
      { zeroConstants with η := k.η, θ := k.θ, fastArmingLag := k.lag, budget := k.budget }
      x.rho p.1 p.2.1 p.2.2
  conclusion := fun I _ _ x p => PersistsThrough I.P x.rho I.iface.stable p.1 p.2.1 p.2.2
  trigger := fun I _ W x p H => persistTrigger I W x p H
  transport := persistOutageFast_transport
  refutable := .run

theorem persistOutageFast_trigger_late {I : Instance} {k : OutageConst} {H : Time}
    (h : persistOutageFast.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (T b₀ b₁ : Time),
      H ≤ T ∧ b₀ < b₁ ∧
        ∃ v ∈ x.rho.honest, readAt I.P x.rho I.iface.stable v T ≠ .genesis := by
  obtain ⟨W, x, ⟨T, b₀, b₁⟩, _, _, _, hH, hb, hv⟩ := h H
  exact ⟨W, x, T, b₀, b₁, hH, hb, hv⟩

/-- Review Focus 6, for the fast claim. -/
theorem persistOutageFast_no_witness_at_zero_budget (I : Instance) (k : OutageConst)
    (hk : k.budget = 0) : ¬ persistOutageFast.inhabited I k := by
  intro h
  obtain ⟨_, _, _, _, _, hr, _, hb, _⟩ := h 0
  have hw := hr.withinBudget
  simp only [hk] at hw
  linarith

/-! ### `recovered`: the bundle field `recovered` -/

theorem recovered_le_trans (a b c : RecoveryConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := of_decide_eq_true hab
  obtain ⟨h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := of_decide_eq_true hbc
  exact decide_eq_true
    ⟨h₁.trans h₇, fun h => h₈ (h₂ h), h₉.trans h₃, h₄.trans h₁₀, h₅.trans h₁₁, h₆.trans h₁₂⟩

theorem recovered_transport (I : Instance) (k k' : RecoveryConst) (_hk : k.Valid)
    (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.iface
        { zeroConstants with
          θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
          recoveryBound := k.ρ } x.rho →
      RecoveredAt I.P x.E I.iface { zeroConstants with D_c := k.D_c, D_s := k.D_s } x.rho
        (x.E.t_GST + k.ρ)) :
    ∀ (W : Validators) (x : V1Ctx I W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.iface
        { zeroConstants with
          θrec := k'.θrec, recoveryFull := k'.full, proposerGap := k'.G,
          recoveryBound := k'.ρ } x.rho →
      RecoveredAt I.P x.E I.iface { zeroConstants with D_c := k'.D_c, D_s := k'.D_s } x.rho
        (x.E.t_GST + k'.ρ) := by
  obtain ⟨hθ, hfull, hG, hρ, hc, hs⟩ := of_decide_eq_true hle
  intro W x hx p hr
  exact recoveredAt_mono (by linarith) hc hs (h W x hx p (recoveryRegime_mono hθ hfull hG hρ hr))

/-- After GST, within ρ: both outputs are safe and include honest proposals
(Recovery regime). -/
def recovered : ClaimSpec ClaimDomain.v1 where
  id := `std.recovered.v1
  Const := RecoveryConst
  valid := RecoveryConst.Valid
  le := RecoveryConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, id, le_rfl, le_rfl, rfl, rfl⟩
  le_trans := recovered_le_trans
  Point := Unit
  regime := fun I k _ x _ =>
    RecoveryRegime I.P x.E I.iface
      { zeroConstants with
        θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
        recoveryBound := k.ρ } x.rho
  conclusion := fun I k _ x _ =>
    RecoveredAt I.P x.E I.iface { zeroConstants with D_c := k.D_c, D_s := k.D_s } x.rho
      (x.E.t_GST + k.ρ)
  trigger := fun I k _ x _ H =>
    ∃ s : Slot, x.E.t_GST + k.ρ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧
      I.P.proposalTime s + max k.D_c k.D_s ≤ x.rho.horizon
  transport := recovered_transport
  refutable := .family

theorem recovered_trigger_late {I : Instance} {k : RecoveryConst} {H : Time}
    (h : recovered.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, _, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-! ### Tests: the direction of `le` (design §4) -/

-- η ↑ and θ ↑ are weaker; the delay is fixed.
example : includedStable.le ⟨0, 1/2, 3⟩ ⟨1, 3/4, 3⟩ = true := by
  simp [includedStable, EtaConst.le]; norm_num
example : includedStable.le ⟨1, 3/4, 3⟩ ⟨0, 1/2, 3⟩ = false := by
  simp [includedStable, EtaConst.le]
example : includedStable.le ⟨0, 1/2, 3⟩ ⟨0, 1/2, 4⟩ = false := by
  simp [includedStable, EtaConst.le]

-- The fast delay is fixed.
example : includedStableFast.le (3 : Time) (3 : Time) = true := by
  simp [includedStableFast]
example : includedStableFast.le (3 : Time) (4 : Time) = false := by
  simp [includedStableFast]

-- lag ↑ and budget ↓ are weaker.
example : persistOutage.le ⟨0, 1/2, 1, 5⟩ ⟨0, 1/2, 2, 4⟩ = true := by
  simp [persistOutage, OutageConst.le]
example : persistOutage.le ⟨0, 1/2, 2, 4⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutage, OutageConst.le]
example : persistOutageFast.le ⟨0, 1/2, 1, 5⟩ ⟨1, 3/4, 2, 4⟩ = true := by
  simp [persistOutageFast, OutageConst.le]; norm_num
example : persistOutageFast.le ⟨0, 3/4, 1, 5⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutageFast, OutageConst.le]; norm_num

-- θrec ↑, full false → true, G ↓, ρ ↑ are weaker; the delays are fixed.
example : recovered.le ⟨1/2, false, 4, 1, 2, 3⟩ ⟨3/4, true, 2, 5, 2, 3⟩ = true := by
  simp [recovered, RecoveryConst.le]; norm_num
example : recovered.le ⟨1/2, true, 4, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 2, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 4, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 4⟩ = false := by
  simp [recovered, RecoveryConst.le]

/-! ### Tests: each ordered field alone (review R1)

Each example reverses one field and keeps the other fields equal. A missing
conjunct in `le` makes one of them fail. -/

example : includedStable.le ⟨1, 1/2, 3⟩ ⟨0, 1/2, 3⟩ = false := by
  simp [includedStable, EtaConst.le]
example : includedStable.le ⟨0, 3/4, 3⟩ ⟨0, 1/2, 3⟩ = false := by
  simp [includedStable, EtaConst.le]; norm_num
example : includedStable.le ⟨0, 1/2, 4⟩ ⟨0, 1/2, 3⟩ = false := by
  simp [includedStable, EtaConst.le]

example : persistOutage.le ⟨1, 1/2, 1, 5⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutage, OutageConst.le]
example : persistOutage.le ⟨0, 3/4, 1, 5⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutage, OutageConst.le]; norm_num
example : persistOutage.le ⟨0, 1/2, 2, 5⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutage, OutageConst.le]
example : persistOutage.le ⟨0, 1/2, 1, 4⟩ ⟨0, 1/2, 1, 5⟩ = false := by
  simp [persistOutage, OutageConst.le]

example : recovered.le ⟨3/4, false, 4, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]; norm_num
example : recovered.le ⟨1/2, false, 4, 5, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 2, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, true, 4, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 4, 1, 2, 3⟩ ⟨1/2, false, 4, 1, 5, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 4, 1, 5, 3⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]
example : recovered.le ⟨1/2, false, 4, 1, 2, 4⟩ ⟨1/2, false, 4, 1, 2, 3⟩ = false := by
  simp [recovered, RecoveryConst.le]

end AvailableChain.Framework.Catalog

end
