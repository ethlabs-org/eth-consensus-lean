module
public import AvailableChainFramework.Catalog.Mono
public import AvailableChainFramework.Facets.Strong
public import AvailableChainStatements.Strong.Claims

@[expose] public section

/-! The strong tier (design §4). Each claim restates one field of the bundle
`StrongClaims` (`AvailableChainStatements/Strong/Claims.lean`) over the strong
claim domain. The regimes and conclusions read the strong interface `I.sface`
and the base instance `I.toInstance`. The fault cap is weaker when it goes
down (`faultCap ↓`).

`StrongClaims` has no `C.Valid` field: only `SC.Valid` (`0 ≤ strongDelay`).
Thus the recovery constants of the strong claims have no validity condition
(`valid := True`, and `0 ≤ D` for the inclusion claims). With a condition,
the equivalence with the bundle fails for a `C` that is not valid. The
`transport` proofs do not need a sign of `θrec`: only the factor changes, and
the count that it multiplies is `≥ 0`.

The `le_trans` and `transport` proofs are named theorems, so that the lock
hashes their statements only. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- The constant of the strong inclusion claim. -/
structure StrongIncConst where
  /-- The fault cap. -/
  f : Nat
  D : Time

/-- The bound of `StrongConstants.Valid` on the delay. -/
def StrongIncConst.Valid (k : StrongIncConst) : Prop :=
  0 ≤ k.D

/-- `b` is at least as weak as `a`: f ↓, the delay is fixed. -/
def StrongIncConst.le (a b : StrongIncConst) : Bool :=
  decide (b.f ≤ a.f ∧ a.D = b.D)

/-- The constant of the strong recovered safety claim. -/
structure StrongRecConst where
  /-- The fault cap. -/
  f : Nat
  θrec : ℚ
  full : Bool
  G : Time
  ρ : Time

/-- No bound: `StrongClaims` has no `C.Valid` field. -/
def StrongRecConst.Valid (_k : StrongRecConst) : Prop :=
  True

/-- `b` is at least as weak as `a`: f ↓, θrec ↑, `full` false → true, G ↓,
ρ ↑. -/
def StrongRecConst.le (a b : StrongRecConst) : Bool :=
  decide (b.f ≤ a.f ∧ a.θrec ≤ b.θrec ∧ (a.full = true → b.full = true) ∧ b.G ≤ a.G ∧
    a.ρ ≤ b.ρ)

/-- The constant of the strong recovered inclusion claim. -/
structure StrongRecIncConst extends StrongRecConst where
  D : Time

/-- The bound of `StrongConstants.Valid` on the delay. -/
def StrongRecIncConst.Valid (k : StrongRecIncConst) : Prop :=
  0 ≤ k.D

/-- `b` is at least as weak as `a`: as `StrongRecConst.le`, and the delay is
fixed. -/
def StrongRecIncConst.le (a b : StrongRecIncConst) : Bool :=
  decide (b.f ≤ a.f ∧ a.θrec ≤ b.θrec ∧ (a.full = true → b.full = true) ∧ b.G ≤ a.G ∧
    a.ρ ≤ b.ρ ∧ a.D = b.D)

/-- The trigger of a strong inclusion claim from `t₀` with delay `D`: a slot
after `t₀` with an honest awake proposer, at a time of at least `H`, with its
deadline inside the run. -/
def strongIncludedTrigger (I : StrongInstance) (W : Validators) (x : V1Ctx I.toInstance W)
    (t₀ D H : Time) : Prop :=
  ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
    HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + D ≤ x.rho.horizon

/-! ### `strongSafe`: the bundle field `strongSafe` -/

theorem strongSafe_le_trans (a b c : Nat) (hab : decide (b ≤ a) = true)
    (hbc : decide (c ≤ b) = true) : decide (c ≤ a) = true :=
  decide_eq_true ((of_decide_eq_true hbc).trans (of_decide_eq_true hab))

theorem strongSafe_transport (I : StrongInstance) (k k' : Nat) (_hk : True)
    (_hk' : True) (hle : decide (k' ≤ k) = true)
    (h : ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P k x.rho →
      SafeFrom I.P x.rho I.sface.strong t₀) :
    ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P k' x.rho →
      SafeFrom I.P x.rho I.sface.strong t₀ := by
  intro W x hx t₀ hr
  exact h W x hx t₀ ⟨hr.1, le_trans hr.2 (of_decide_eq_true hle)⟩

/-- The strong output is safe in the Sleepy regime, with at most `f` faulty
validators. -/
def strongSafe : ClaimSpec ClaimDomain.strong where
  id := `extra.strong.safe.v1
  Const := Nat
  valid := fun _ => True
  le := fun a b => decide (b ≤ a)
  le_refl := fun _ => decide_eq_true le_rfl
  le_trans := strongSafe_le_trans
  Point := Time
  regime := fun I f _ x t₀ =>
    SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P f x.rho
  conclusion := fun I _ _ x t₀ => SafeFrom I.P x.rho I.sface.strong t₀
  trigger := fun _ _ _ _ _ _ => True
  transport := strongSafe_transport
  refutable := .run

/-! ### `strongIncluded`: the bundle field `strongIncluded` -/

theorem strongIncluded_le_trans (a b c : StrongIncConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂⟩ := of_decide_eq_true hab
  obtain ⟨h₃, h₄⟩ := of_decide_eq_true hbc
  exact decide_eq_true ⟨h₃.trans h₁, h₂.trans h₄⟩

theorem strongIncluded_transport (I : StrongInstance) (k k' : StrongIncConst)
    (_hk : k.Valid) (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P k.f x.rho ∧
        FullParticipation x.E x.rho t₀ →
      IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong t₀ k.D) :
    ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ t₀ : Time,
      SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P k'.f x.rho ∧
        FullParticipation x.E x.rho t₀ →
      IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong t₀ k'.D := by
  obtain ⟨hf, hD⟩ := of_decide_eq_true hle
  intro W x hx t₀ hr
  rw [← hD]
  exact h W x hx t₀ ⟨hr.1, le_trans hr.2.1 hf, hr.2.2⟩

/-- Exact-time inclusion of honest proposals in the strong output, in the
Sleepy regime with full participation and at most `f` faulty validators. -/
def strongIncluded : ClaimSpec ClaimDomain.strong where
  id := `extra.strong.included.v1
  Const := StrongIncConst
  valid := StrongIncConst.Valid
  le := StrongIncConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, rfl⟩
  le_trans := strongIncluded_le_trans
  Point := Time
  regime := fun I k _ x t₀ =>
    SleepyRegime I.P x.E I.sface.toInterface x.rho t₀ ∧ FaultBound I.P k.f x.rho ∧
      FullParticipation x.E x.rho t₀
  conclusion := fun I k _ x t₀ =>
    IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong t₀ k.D
  trigger := fun I k W x t₀ H => strongIncludedTrigger I W x t₀ k.D H
  transport := strongIncluded_transport
  refutable := .family

theorem strongIncluded_trigger_late {I : StrongInstance} {k : StrongIncConst} {H : Time}
    (h : strongIncluded.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.strong.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-! ### `strongPersist`: the bundle field `strongResilient` -/

theorem strongPersist_le_trans (a b c : Nat) (hab : decide (b ≤ a) = true)
    (hbc : decide (c ≤ b) = true) : decide (c ≤ a) = true :=
  strongSafe_le_trans a b c hab hbc

theorem strongPersist_transport (I : StrongInstance) (k k' : Nat) (_hk : True)
    (_hk' : True) (hle : decide (k' ≤ k) = true)
    (h : ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ p : Time × Time,
      StrongArmedRegime I.P x.E I.sface k x.rho p.1 p.2 →
      PersistsFrom I.P x.rho I.sface.strong p.1 p.2) :
    ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ p : Time × Time,
      StrongArmedRegime I.P x.E I.sface k' x.rho p.1 p.2 →
      PersistsFrom I.P x.rho I.sface.strong p.1 p.2 := by
  intro W x hx p hr
  exact h W x hx p { hr with faultBound := le_trans hr.faultBound (of_decide_eq_true hle) }

/-- Persistence of the strong output from `b₀` to the horizon, after sound
arming at `T`, with at most `f` faulty validators. The window `[b₀, horizon]`
is not empty, because the regime has `b₀ ≤ horizon`. Thus the trigger needs
no condition on the window. -/
def strongPersist : ClaimSpec ClaimDomain.strong where
  id := `extra.strong.persist.v1
  Const := Nat
  valid := fun _ => True
  le := fun a b => decide (b ≤ a)
  le_refl := fun _ => decide_eq_true le_rfl
  le_trans := strongPersist_le_trans
  Point := Time × Time
  regime := fun I f _ x p => StrongArmedRegime I.P x.E I.sface f x.rho p.1 p.2
  conclusion := fun I _ _ x p => PersistsFrom I.P x.rho I.sface.strong p.1 p.2
  trigger := fun I _ _ x p H =>
    H ≤ p.1 ∧ ∃ v ∈ x.rho.honest, readAt I.P x.rho I.sface.strong v p.1 ≠ .genesis
  transport := strongPersist_transport
  refutable := .run

theorem strongPersist_trigger_late {I : StrongInstance} {f : Nat} {H : Time}
    (h : strongPersist.inhabited I f) :
    ∃ (W : Validators) (x : ClaimDomain.strong.Ctx I W) (T : Time),
      H ≤ T ∧ ∃ v ∈ x.rho.honest, readAt I.P x.rho I.sface.strong v T ≠ .genesis := by
  obtain ⟨W, x, ⟨T, _⟩, _, _, _, hH, hv⟩ := h H
  exact ⟨W, x, T, hH, hv⟩

/-! ### `strongRecoveredSafe`: the bundle field `strongRecoveredSafe` -/

theorem strongRecoveredSafe_le_trans (a b c : StrongRecConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := of_decide_eq_true hab
  obtain ⟨h₆, h₇, h₈, h₉, h₁₀⟩ := of_decide_eq_true hbc
  exact decide_eq_true
    ⟨h₆.trans h₁, h₂.trans h₇, fun h => h₈ (h₃ h), h₉.trans h₄, h₅.trans h₁₀⟩

theorem strongRecoveredSafe_transport (I : StrongInstance) (k k' : StrongRecConst)
    (_hk : k.Valid) (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.sface.toInterface
        { zeroConstants with
          θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
          recoveryBound := k.ρ } x.rho ∧ FaultBound I.P k.f x.rho →
      SafeFrom I.P x.rho I.sface.strong (x.E.t_GST + k.ρ)) :
    ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.sface.toInterface
        { zeroConstants with
          θrec := k'.θrec, recoveryFull := k'.full, proposerGap := k'.G,
          recoveryBound := k'.ρ } x.rho ∧ FaultBound I.P k'.f x.rho →
      SafeFrom I.P x.rho I.sface.strong (x.E.t_GST + k'.ρ) := by
  obtain ⟨hf, hθ, hfull, hG, hρ⟩ := of_decide_eq_true hle
  intro W x hx p hr
  exact safeFrom_mono (by linarith)
    (h W x hx p ⟨recoveryRegime_mono hθ hfull hG hρ hr.1, le_trans hr.2 hf⟩)

/-- After GST, within ρ: the strong output is safe (Recovery regime, at most
`f` faulty validators).

The tag is `.run`, not `.family`. `valid` is `True`, so a constant with
`θrec ≥ 1` and `ρ ≥ 0` is valid, and its Recovery regime is empty: the regime
has `GST + ρ ≤ horizon`, so it reads the participation bound at `GST`, and the
awake count cannot exceed `θrec` times itself plus the faulty count. Thus
`holds` is vacuous there, and no refutation family can exist. (With `ρ < 0`,
a run with `GST + ρ ≤ horizon < GST` can be in the regime.) -/
def strongRecoveredSafe : ClaimSpec ClaimDomain.strong where
  id := `extra.strong.recoveredSafe.v1
  Const := StrongRecConst
  valid := StrongRecConst.Valid
  le := StrongRecConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl, id, le_rfl, le_rfl⟩
  le_trans := strongRecoveredSafe_le_trans
  Point := Unit
  regime := fun I k _ x _ =>
    RecoveryRegime I.P x.E I.sface.toInterface
      { zeroConstants with
        θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
        recoveryBound := k.ρ } x.rho ∧ FaultBound I.P k.f x.rho
  conclusion := fun I k _ x _ => SafeFrom I.P x.rho I.sface.strong (x.E.t_GST + k.ρ)
  trigger := fun _ _ _ _ _ _ => True
  transport := strongRecoveredSafe_transport
  refutable := .run

/-! ### `strongRecoveredIncluded`: the bundle field `strongRecoveredIncluded` -/

theorem strongRecoveredIncluded_le_trans (a b c : StrongRecIncConst) (hab : a.le b = true)
    (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := of_decide_eq_true hab
  obtain ⟨h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := of_decide_eq_true hbc
  exact decide_eq_true
    ⟨h₇.trans h₁, h₂.trans h₈, fun h => h₉ (h₃ h), h₁₀.trans h₄, h₅.trans h₁₁, h₆.trans h₁₂⟩

theorem strongRecoveredIncluded_transport (I : StrongInstance) (k k' : StrongRecIncConst)
    (_hk : k.Valid) (_hk' : k'.Valid) (hle : k.le k' = true)
    (h : ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.sface.toInterface
        { zeroConstants with
          θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
          recoveryBound := k.ρ } x.rho ∧ FaultBound I.P k.f x.rho →
      IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong (x.E.t_GST + k.ρ) k.D) :
    ∀ (W : Validators) (x : V1Ctx I.toInstance W), x.E.Δ = I.Δ → ∀ _ : Unit,
      RecoveryRegime I.P x.E I.sface.toInterface
        { zeroConstants with
          θrec := k'.θrec, recoveryFull := k'.full, proposerGap := k'.G,
          recoveryBound := k'.ρ } x.rho ∧ FaultBound I.P k'.f x.rho →
      IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong (x.E.t_GST + k'.ρ)
        k'.D := by
  obtain ⟨hf, hθ, hfull, hG, hρ, hD⟩ := of_decide_eq_true hle
  intro W x hx p hr
  rw [← hD]
  exact includedFrom_mono (by linarith)
    (h W x hx p ⟨recoveryRegime_mono hθ hfull hG hρ hr.1, le_trans hr.2 hf⟩)

/-- After GST, within ρ: the strong output includes honest proposals within
`D` (Recovery regime, at most `f` faulty validators).

The tag is `.run`, not `.family`, as for `strongRecoveredSafe`: `valid` has
no bound on `θrec` or `ρ`, so a constant with `θrec ≥ 1` and `ρ ≥ 0` is
valid, and its Recovery regime is empty. Thus `holds` is vacuous there. -/
def strongRecoveredIncluded : ClaimSpec ClaimDomain.strong where
  id := `extra.strong.recoveredIncluded.v1
  Const := StrongRecIncConst
  valid := StrongRecIncConst.Valid
  le := StrongRecIncConst.le
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl, id, le_rfl, le_rfl, rfl⟩
  le_trans := strongRecoveredIncluded_le_trans
  Point := Unit
  regime := fun I k _ x _ =>
    RecoveryRegime I.P x.E I.sface.toInterface
      { zeroConstants with
        θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G,
        recoveryBound := k.ρ } x.rho ∧ FaultBound I.P k.f x.rho
  conclusion := fun I k _ x _ =>
    IncludedFrom I.P x.E I.sface.toInterface x.rho I.sface.strong (x.E.t_GST + k.ρ) k.D
  trigger := fun I k W x _ H => strongIncludedTrigger I W x (x.E.t_GST + k.ρ) k.D H
  transport := strongRecoveredIncluded_transport
  refutable := .run

theorem strongRecoveredIncluded_trigger_late {I : StrongInstance} {k : StrongRecIncConst}
    {H : Time} (h : strongRecoveredIncluded.inhabited I k) :
    ∃ (W : Validators) (x : ClaimDomain.strong.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  obtain ⟨W, x, _, _, _, _, s, _, hH, hp, _⟩ := h H
  exact ⟨W, x, s, hH, hp⟩

/-! ### Tests: the direction of `le` (design §4)

Each `false` example reverses one field and keeps the other fields equal. A
missing conjunct in `le` makes one of them fail. -/

-- f ↓ is weaker.
example : strongSafe.le (3 : Nat) (2 : Nat) = true := by simp [strongSafe]
example : strongSafe.le (2 : Nat) (3 : Nat) = false := by simp [strongSafe]
example : strongPersist.le (3 : Nat) (2 : Nat) = true := by simp [strongPersist]
example : strongPersist.le (2 : Nat) (3 : Nat) = false := by simp [strongPersist]

-- f ↓ is weaker; the delay is fixed.
example : strongIncluded.le ⟨3, 2⟩ ⟨2, 2⟩ = true := by
  simp [strongIncluded, StrongIncConst.le]
example : strongIncluded.le ⟨2, 2⟩ ⟨3, 2⟩ = false := by
  simp [strongIncluded, StrongIncConst.le]
example : strongIncluded.le ⟨2, 2⟩ ⟨2, 3⟩ = false := by
  simp [strongIncluded, StrongIncConst.le]
example : strongIncluded.le ⟨2, 3⟩ ⟨2, 2⟩ = false := by
  simp [strongIncluded, StrongIncConst.le]

-- f ↓, θrec ↑, full false → true, G ↓, ρ ↑ are weaker.
example : strongRecoveredSafe.le ⟨3, 1/2, false, 4, 1⟩ ⟨2, 3/4, true, 2, 5⟩ = true := by
  simp [strongRecoveredSafe, StrongRecConst.le]; norm_num
example : strongRecoveredSafe.le ⟨2, 1/2, false, 4, 1⟩ ⟨3, 1/2, false, 4, 1⟩ = false := by
  simp [strongRecoveredSafe, StrongRecConst.le]
example : strongRecoveredSafe.le ⟨2, 3/4, false, 4, 1⟩ ⟨2, 1/2, false, 4, 1⟩ = false := by
  simp [strongRecoveredSafe, StrongRecConst.le]; norm_num
example : strongRecoveredSafe.le ⟨2, 1/2, true, 4, 1⟩ ⟨2, 1/2, false, 4, 1⟩ = false := by
  simp [strongRecoveredSafe, StrongRecConst.le]
example : strongRecoveredSafe.le ⟨2, 1/2, false, 2, 1⟩ ⟨2, 1/2, false, 4, 1⟩ = false := by
  simp [strongRecoveredSafe, StrongRecConst.le]
example : strongRecoveredSafe.le ⟨2, 1/2, false, 4, 5⟩ ⟨2, 1/2, false, 4, 1⟩ = false := by
  simp [strongRecoveredSafe, StrongRecConst.le]

-- As above; the delay is fixed.
example : strongRecoveredIncluded.le ⟨⟨3, 1/2, false, 4, 1⟩, 2⟩
    ⟨⟨2, 3/4, true, 2, 5⟩, 2⟩ = true := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]; norm_num
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩
    ⟨⟨3, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]
example : strongRecoveredIncluded.le ⟨⟨2, 3/4, false, 4, 1⟩, 2⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]; norm_num
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, true, 4, 1⟩, 2⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, false, 2, 1⟩, 2⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, false, 4, 5⟩, 2⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 3⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]
example : strongRecoveredIncluded.le ⟨⟨2, 1/2, false, 4, 1⟩, 3⟩
    ⟨⟨2, 1/2, false, 4, 1⟩, 2⟩ = false := by
  simp [strongRecoveredIncluded, StrongRecIncConst.le]

end AvailableChain.Framework.Catalog

end
