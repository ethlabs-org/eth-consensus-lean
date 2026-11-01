module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSAClaims.Statements.Bounds
public import AvailableChainKitV2.DutyExecution

public section

/-! Plan O-ARM §2, §6.1 and §10 "Origin s = 1": label arithmetic, deadlines
and read indices of the arming certificate. Every subtraction of slots is
guarded by an explicit bound. -/

namespace AvailableChain.FGSA.Run

/-! ### Slot times -/

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the gate time formula. -/
theorem arming_gate_eq (p : Params) (r : Slot) :
    SA.gateTime p.toParams r = 4 * p.Δ * (r : Time) + 6 * p.Δ := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the vote time formula. -/
theorem arming_vote_eq (p : Params) (r : Slot) :
    SA.voteTime p.toParams r = 4 * p.Δ * (r : Time) + p.Δ := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the early time formula. -/
theorem arming_early_eq (p : Params) (r : Slot) :
    SA.earlyTime p.toParams r = 4 * p.Δ * (r : Time) + 2 * p.Δ := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the freeze time formula. -/
theorem arming_freeze_eq (p : Params) (r : Slot) :
    SA.freezeTime p.toParams r = 4 * p.Δ * (r : Time) + 3 * p.Δ := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the release time formula. -/
theorem arming_release_eq (p : Params) (r : Slot) :
    SA.releaseTime p.toParams r = 4 * p.Δ * (r : Time) + 5 * p.Δ := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the proposal time formula. -/
theorem arming_proposal_eq (p : Params) (r : Slot) :
    SA.proposalTime p.toParams r = 4 * p.Δ * (r : Time) := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the lease lifetime is L. -/
theorem arming_lifetime_eq (p : Params) : SA.lifetime p.toParams = L p := rfl

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; gate times are strictly
increasing in the label. -/
theorem arming_gate_le_iff (p : Params) (r r' : Slot) :
    SA.gateTime p.toParams r ≤ SA.gateTime p.toParams r' ↔ r ≤ r' := by
  rw [arming_gate_eq, arming_gate_eq]
  have hd := p.deltaPos
  constructor
  · intro h
    by_contra hn
    have hlt : (r' : Time) + 1 ≤ (r : Time) := by exact_mod_cast Nat.lt_of_not_ge hn
    nlinarith
  · intro h
    have hle : (r : Time) ≤ (r' : Time) := by exact_mod_cast h
    nlinarith

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; strict form of
`arming_gate_le_iff`. -/
theorem arming_gate_lt_iff (p : Params) (r r' : Slot) :
    SA.gateTime p.toParams r < SA.gateTime p.toParams r' ↔ r < r' := by
  rw [← not_le, arming_gate_le_iff, not_le]

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; e(l + 1) = d(l). -/
theorem arming_early_next (p : Params) (l : Slot) :
    SA.earlyTime p.toParams (l + 1) = SA.gateTime p.toParams l := by
  rw [arming_early_eq, arming_gate_eq]
  push_cast
  ring

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; v(r) + Δ = e(r). -/
theorem arming_vote_add (p : Params) (r : Slot) :
    SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r := by
  rw [arming_vote_eq, arming_early_eq]
  ring

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; v(r) < e(r) < z(r). -/
theorem arming_vote_lt_early (p : Params) (r : Slot) :
    SA.voteTime p.toParams r < SA.earlyTime p.toParams r ∧
      SA.earlyTime p.toParams r < SA.freezeTime p.toParams r := by
  rw [arming_vote_eq, arming_early_eq, arming_freeze_eq]
  have hd := p.deltaPos
  constructor <;> linarith

/-! ### The cut label -/

/-- Plan O-ARM §2, §6.1. Class (iii). DC: INTENTIONAL; with a gate time at
or before the cut, `l` is the last gate label at or before the cut. -/
theorem arming_label (p : Params) (b₀ : Time) (h : 6 * p.Δ ≤ b₀) :
    SA.gateTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) ≤ b₀ ∧
      b₀ < SA.gateTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) := by
  have hd : 0 < 4 * p.Δ := by have := p.deltaPos; linarith
  have hn : 0 ≤ b₀ - 6 * p.Δ := by linarith
  rw [arming_gate_eq, arming_gate_eq]
  push_cast
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
  have hlo := Int.ediv_mul_le (b₀ - 6 * p.Δ) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (b₀ - 6 * p.Δ) hd
  constructor <;> nlinarith

/-- Plan O-ARM §2, §6.1. Class (iii). DC: INTENTIONAL; a gate is at or before
the cut exactly when its label is at most `l`. -/
theorem arming_le_label (p : Params) (b₀ : Time) (h : 6 * p.Δ ≤ b₀) (r : Slot) :
    SA.gateTime p.toParams r ≤ b₀ ↔ r ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat := by
  obtain ⟨hlo, hhi⟩ := arming_label p b₀ h
  constructor
  · intro hr
    have := (arming_gate_lt_iff p _ _).mp (lt_of_le_of_lt hr hhi)
    simp only [Slot] at this ⊢
    omega
  · intro hr
    exact ((arming_gate_le_iff p _ _).mpr hr).trans hlo

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; a gate strictly before the
pending gate has a label at most `l`. -/
theorem arming_lt_pending (p : Params) (l r : Slot)
    (h : SA.gateTime p.toParams r < SA.gateTime p.toParams (l + 1)) : r ≤ l := by
  have := (arming_gate_lt_iff p _ _).mp h
  simp only [Slot] at this ⊢
  omega

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; no gate lies strictly
between d(l) and d(l + 1). -/
theorem arming_gate_window (p : Params) (l r : Slot)
    (h₁ : SA.gateTime p.toParams l ≤ SA.gateTime p.toParams r)
    (h₂ : SA.gateTime p.toParams r < SA.gateTime p.toParams (l + 1)) : r = l := by
  have h₃ := (arming_gate_le_iff p _ _).mp h₁
  have h₄ := (arming_gate_lt_iff p _ _).mp h₂
  simp only [Slot] at h₃ h₄ ⊢
  omega

/-- Plan O-ARM §2, §6.2 step 6. Class (iii). DC: INTENTIONAL; the only HEAD
time in [d(l), d(l + 1)) is v(l + 2). -/
theorem arming_vote_window (p : Params) (l r : Slot)
    (h₁ : SA.gateTime p.toParams l ≤ SA.voteTime p.toParams r)
    (h₂ : SA.voteTime p.toParams r < SA.gateTime p.toParams (l + 1)) : r = l + 2 := by
  rw [arming_gate_eq, arming_vote_eq] at h₁ h₂
  push_cast at h₂
  have e₁ : (4 * (l : Int) + 6) * p.Δ ≤ (4 * (r : Int) + 1) * p.Δ := by linarith
  have e₂ : (4 * (r : Int) + 1) * p.Δ < (4 * (l : Int) + 10) * p.Δ := by linarith
  have f₁ := le_of_mul_le_mul_right e₁ p.deltaPos
  have f₂ := lt_of_mul_lt_mul_right e₂ p.deltaPos.le
  simp only [Slot] at *
  omega

/-- Plan O-ARM §2, §6.2 step 6. Class (iii). DC: INTENTIONAL; the only
proposal time in [d(l), d(l + 1)) is t(l + 2). -/
theorem arming_proposal_window (p : Params) (l r : Slot)
    (h₁ : SA.gateTime p.toParams l ≤ SA.proposalTime p.toParams r)
    (h₂ : SA.proposalTime p.toParams r < SA.gateTime p.toParams (l + 1)) : r = l + 2 := by
  rw [arming_gate_eq, arming_proposal_eq] at h₁ h₂
  push_cast at h₂
  have e₁ : (4 * (l : Int) + 6) * p.Δ ≤ (4 * (r : Int)) * p.Δ := by linarith
  have e₂ : (4 * (r : Int)) * p.Δ < (4 * (l : Int) + 10) * p.Δ := by linarith
  have f₁ := le_of_mul_le_mul_right e₁ p.deltaPos
  have f₂ := lt_of_mul_lt_mul_right e₂ p.deltaPos.le
  simp only [Slot] at *
  omega

/-- Plan O-ARM §4 field 8. Class (iii). DC: INTENTIONAL; the only label whose
HEAD is signed by d(j) and released after d(j) is j + 1. -/
theorem arming_inflight (p : Params) (j r : Slot)
    (h₁ : SA.voteTime p.toParams r ≤ SA.gateTime p.toParams j)
    (h₂ : SA.gateTime p.toParams j < SA.releaseTime p.toParams r) : r = j + 1 := by
  rw [arming_gate_eq, arming_vote_eq] at h₁
  rw [arming_gate_eq, arming_release_eq] at h₂
  have e₁ : (4 * (r : Int) + 1) * p.Δ ≤ (4 * (j : Int) + 6) * p.Δ := by linarith
  have e₂ : (4 * (j : Int) + 6) * p.Δ < (4 * (r : Int) + 5) * p.Δ := by linarith
  have f₁ := le_of_mul_le_mul_right e₁ p.deltaPos
  have f₂ := lt_of_mul_lt_mul_right e₂ p.deltaPos.le
  simp only [Slot] at *
  omega

/-- Plan O-ARM §4 field 8. Class (iii). DC: INTENTIONAL; v(j + 1) ≤ d(j) < q(j + 1). -/
theorem arming_inflight_window (p : Params) (j : Slot) :
    SA.voteTime p.toParams (j + 1) ≤ SA.gateTime p.toParams j ∧
      SA.gateTime p.toParams j < SA.releaseTime p.toParams (j + 1) ∧
      SA.voteTime p.toParams (j + 1) < SA.gateTime p.toParams j := by
  rw [arming_gate_eq, arming_vote_eq, arming_release_eq]
  push_cast
  have hd := p.deltaPos
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Plan O-ARM §6.2 steps 3, 6. Class (iii). DC: INTENTIONAL; d(l) ≤ t(l + 2)
and v(l + 2) < d(l + 1); the duty times of label l + 2 are in the window. -/
theorem arming_duty_window (p : Params) (l : Slot) :
    SA.gateTime p.toParams l ≤ SA.proposalTime p.toParams (l + 2) ∧
      SA.proposalTime p.toParams (l + 2) < SA.voteTime p.toParams (l + 2) ∧
      SA.voteTime p.toParams (l + 2) < SA.gateTime p.toParams (l + 1) ∧
      SA.earlyTime p.toParams (l + 1) < SA.proposalTime p.toParams (l + 2) := by
  rw [arming_gate_eq, arming_gate_eq, arming_proposal_eq, arming_vote_eq, arming_early_eq]
  push_cast
  have hd := p.deltaPos
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Plan O-ARM §6.1 step 3, §10 "Origin s = 1". Class (iii). DC: INTENTIONAL;
an action strictly before the pending gate reads a gate of label at most `l`. -/
theorem arming_action_label (p : Params) (l r : Nat)
    (h : p.actionTime r < SA.gateTime p.toParams (l + 1)) : r * p.R ≤ l :=
  arming_lt_pending p l (r * p.R) h

/-! ### Mode gaps -/

/-- Plan O-ARM §2, §10 "Origin s = 1". Class (iii). DC: INTENTIONAL; the fast
lag 4Δ gives s + 1 ≤ l, hence s + 2 ≤ j. -/
theorem arming_fast_gap (p : Params) (s : Slot) (T b₀ : Time)
    (hs : SA.gateTime p.toParams s ≤ T) (hlag : T + 4 * p.Δ ≤ b₀) :
    s + 2 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 := by
  have hd := p.deltaPos
  have h6 : 6 * p.Δ ≤ b₀ := by
    rw [arming_gate_eq] at hs
    have : (0 : Time) ≤ 4 * p.Δ * (s : Time) := by positivity
    linarith
  have hnext : SA.gateTime p.toParams (s + 1) ≤ b₀ := by
    rw [arming_gate_eq] at hs ⊢
    push_cast
    linarith
  have := (arming_le_label p b₀ h6 (s + 1)).mp hnext
  simp only [Slot] at this ⊢
  omega

/-- Plan O-ARM §2, §6.4, §10 "Origin s = 1". Class (iii). DC: INTENTIONAL;
the slow lag L − 3Δ = 4(k − 1)Δ gives s + k − 1 ≤ l, hence s + k ≤ j. -/
theorem arming_slow_gap (p : Params) (s : Slot) (T b₀ : Time)
    (hs : SA.gateTime p.toParams s ≤ T) (hlag : T + (L p - 3 * p.Δ) ≤ b₀) :
    s + p.k ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 := by
  have hd := p.deltaPos
  have hk := p.kLarge
  have hk1 : (1 : Time) ≤ (p.k : Time) - 1 := by
    have : (2 : Time) ≤ (p.k : Time) := by exact_mod_cast hk
    linarith
  have hL : L p - 3 * p.Δ = 4 * ((p.k : Time) - 1) * p.Δ := by
    change (4 * (p.k : Time) - 1) * p.Δ - 3 * p.Δ = _
    ring
  have h6 : 6 * p.Δ ≤ b₀ := by
    rw [arming_gate_eq] at hs
    have : (0 : Time) ≤ 4 * p.Δ * (s : Time) := by positivity
    rw [hL] at hlag
    nlinarith
  have hnext : SA.gateTime p.toParams (s + (p.k - 1)) ≤ b₀ := by
    rw [arming_gate_eq] at hs ⊢
    rw [hL] at hlag
    have hcast : ((s + (p.k - 1) : Nat) : Time) = (s : Time) + ((p.k : Time) - 1) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    nlinarith
  have := (arming_le_label p b₀ h6 (s + (p.k - 1))).mp hnext
  simp only [Slot] at this ⊢
  omega

/-- Plan O-ARM §6.4, §10 "Origin s = 1". Class (iii). DC: INTENTIONAL; every
slow-window label j − (a + 1), a < k − 1, lies in [s + 1, l]. The natural
subtraction is used only under s + k ≤ j. -/
theorem arming_slow_window_label (p : Params) (s l a : Nat) (hs : 1 ≤ s)
    (hgap : s + p.k ≤ l + 1) (ha : a < p.k - 1) :
    s + 1 ≤ l + 1 - (a + 1) ∧ l + 1 - (a + 1) ≤ l ∧ 2 ≤ l + 1 - (a + 1) := by
  omega

/-- Plan O-ARM §4 field 3. Class (iii). DC: INTENTIONAL; the outage budget ends
strictly before the pending lease deadline d(j) + L. -/
theorem arming_end_lt_deadline (p : Params) (l : Slot) (b₀ b₁ : Time)
    (hcut : b₀ < SA.gateTime p.toParams (l + 1)) (hbudget : b₁ - b₀ ≤ min p.η (L p)) :
    b₁ < SA.gateTime p.toParams (l + 1) + L p := by
  have := min_le_right p.η (L p)
  linarith

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; L is positive. -/
theorem arming_L_pos (p : Params) : 0 < L p := by
  change 0 < (4 * (p.k : Time) - 1) * p.Δ
  have hd := p.deltaPos
  have hk : (2 : Time) ≤ (p.k : Time) := by exact_mod_cast p.kLarge
  nlinarith

/-! ### Read indices -/

section Indices

variable {V : Type} {In : Type} {P : V2.ProtocolSpecD In}

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; an event is inside the
inclusive read at t exactly when its time is at most t. -/
theorem arming_lt_timeIdx_iff {E : Generic.Env V} {rho : V2.D.Run V P}
    (hs : V2.D.ScheduleWellFormed E rho) (t : Time) {i : Nat} {e : V2.Event V P.Object}
    (hi : rho.events[i]? = some e) : i < timeIdx rho t ↔ e.time ≤ t :=
  V2.D.Engine.index_lt_read_length_iff hs t hi

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; the inclusive read index is
monotone in time. -/
theorem arming_timeIdx_mono (rho : V2.D.Run V P) {t u : Time} (h : t ≤ u) :
    timeIdx rho t ≤ timeIdx rho u := by
  change (rho.events.filter _).length ≤ (rho.events.filter _).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true ((of_decide_eq_true he).trans h))

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; I(t) ≤ I⁻(u) for t < u. -/
theorem arming_timeIdx_le_idxBefore (rho : V2.D.Run V P) {t u : Time} (h : t < u) :
    timeIdx rho t ≤ V2.D.Run.idxBefore rho u := by
  change (rho.events.filter _).length ≤ _
  rw [V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_le_of_lt (of_decide_eq_true he) h))

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; I⁻(t) ≤ I(t). -/
theorem arming_idxBefore_le_timeIdx (rho : V2.D.Run V P) (t : Time) :
    V2.D.Run.idxBefore rho t ≤ timeIdx rho t := by
  change _ ≤ (rho.events.filter _).length
  rw [V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true (of_decide_eq_true he).le)

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; every read index is at most
the event count. -/
theorem arming_timeIdx_le_length (rho : V2.D.Run V P) (t : Time) :
    timeIdx rho t ≤ rho.events.length := by
  change (rho.events.filter _).length ≤ _
  exact List.length_filter_le _ _

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; every strict read index is at
most the event count. -/
theorem arming_idxBefore_le_length (rho : V2.D.Run V P) (t : Time) :
    V2.D.Run.idxBefore rho t ≤ rho.events.length := by
  rw [V2.D.Run.idxBefore_def]
  exact List.length_filter_le _ _

end Indices

end AvailableChain.FGSA.Run
end
