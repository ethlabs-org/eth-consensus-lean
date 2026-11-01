module
public import AvailableChainFGSAClaims.Statements.OutageContinuation
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith

public section

namespace AvailableChain.FGSA.Run

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; (V) ends at vote j+K. -/
theorem outageV_iff_vote_bound (p : Params) (b₀ b₁ : Time) (h₀ : 6 * p.Δ ≤ b₀) :
    OutageLengthV p b₀ b₁ ↔
      b₁ ≤ SA.voteTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 + p.k) := by
  rw [OutageLengthV_def, arming_vote_eq]
  change _ ↔ b₁ ≤ 4 * p.Δ * (↑(((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 + p.k) : Int) + p.Δ
  have hd : 0 < 4 * p.Δ := by have := p.deltaPos; linarith
  have hq := Int.ediv_nonneg (show 0 ≤ b₀ - 6 * p.Δ by linarith) hd.le
  have he := Int.emod_add_mul_ediv (b₀ - 6 * p.Δ) (4 * p.Δ)
  push_cast
  rw [Int.toNat_of_nonneg hq]
  change b₁ - b₀ + (b₀ - 6 * p.Δ) % (4 * p.Δ) ≤ (4 * (p.k : Int) - 1) * p.Δ ↔ _
  constructor <;> intro h <;> nlinarith

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; the first restored vote label
exists for each endpoint. The minimum is independent of the run horizon. -/
theorem outageV_first_restored_exists (p : Params) (b₁ : Time) :
    ∃ r : Slot, ∀ s, b₁ ≤ SA.voteTime p.toParams s ↔ r ≤ s := by
  have hex : ∃ s : Nat, b₁ ≤ SA.voteTime p.toParams s := by
    by_cases hb : b₁ ≤ 0
    · refine ⟨0, ?_⟩
      rw [arming_vote_eq]
      have := p.deltaPos
      norm_num
      linarith
    · refine ⟨b₁.toNat, ?_⟩
      rw [arming_vote_eq, Int.toNat_of_nonneg (by linarith : 0 ≤ b₁)]
      have hd : (1 : Int) ≤ p.Δ := by
        have h := p.deltaPos
        change (0 : Int) < p.Δ at h
        omega
      nlinarith
  refine ⟨Nat.find hex, fun s => ⟨fun h => Nat.find_min' hex h, ?_⟩⟩
  intro h
  have ht := Nat.find_spec hex
  rw [arming_vote_eq] at ht ⊢
  have hcast : ((Nat.find hex : Nat) : Int) ≤ (s : Int) := by exact_mod_cast h
  have := p.deltaPos
  nlinarith

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; characterize the first restored
label by its minimum property, without a horizon assumption. -/
theorem outageV_iff_restored_label (p : Params) (b₀ b₁ : Time)
    (h₀ : 6 * p.Δ ≤ b₀) (r : Slot)
    (hr : ∀ s, b₁ ≤ SA.voteTime p.toParams s ↔ r ≤ s) :
    OutageLengthV p b₀ b₁ ↔
      r ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 + p.k :=
  (outageV_iff_vote_bound p b₀ b₁ h₀).trans (hr _)

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; the restored vote precedes expiry. -/
theorem outageV_vote_before_expiry (p : Params) (j r : Slot) (hr : r ≤ j + p.k) :
    SA.voteTime p.toParams r < SA.gateTime p.toParams j + L p := by
  rw [arming_vote_eq, arming_gate_eq]
  change _ < 4 * p.Δ * (j : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
  have hcast : (r : Int) ≤ (j : Int) + (p.k : Int) := by exact_mod_cast hr
  have := p.deltaPos
  nlinarith

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; old-label gates precede expiry. -/
theorem outageV_old_gate_before_expiry (p : Params) (j r s : Slot)
    (hr : r ≤ j + p.k) (hs : s < r) :
    SA.gateTime p.toParams s < SA.gateTime p.toParams j + L p := by
  rw [arming_gate_eq, arming_gate_eq]
  change _ < 4 * p.Δ * (j : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
  have hcast : (s : Int) + 1 ≤ (j : Int) + (p.k : Int) := by
    exact_mod_cast ((Nat.succ_le_of_lt hs).trans hr)
  have := p.deltaPos
  nlinarith

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; the boundary HEAD occurs at expiry,
before the gate that reads the last protected batch. -/
theorem outageV_boundary (p : Params) (j : Slot) :
    SA.gateTime p.toParams (j + p.k - 1) = SA.gateTime p.toParams j + L p - 3 * p.Δ ∧
    SA.voteTime p.toParams (j + p.k + 1) = SA.gateTime p.toParams j + L p ∧
    SA.gateTime p.toParams (j + p.k) = SA.gateTime p.toParams j + L p + p.Δ := by
  have hk := p.kLarge
  have hsub : ((j + p.k - 1 : Nat) : Int) = (j : Int) + (p.k : Int) - 1 := by omega
  rw [arming_gate_eq, arming_gate_eq, arming_vote_eq, arming_gate_eq, hsub]
  change _ = _ + (4 * (p.k : Int) - 1) * p.Δ - _ ∧
    _ = _ + (4 * (p.k : Int) - 1) * p.Δ ∧
    _ = _ + (4 * (p.k : Int) - 1) * p.Δ + _
  push_cast
  constructor
  · ring
  constructor <;> ring

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; use the old arming producer at
an auxiliary zero-length endpoint. Its eta budget is then automatic. -/
theorem outageV_arming_prem {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF) :
    Outage₂ p c fast E rho T b₀ b₀ ΔF := by
  refine ⟨h.pre, h.sleepy, ⟨h.order.1, h.order.2.1, le_rfl,
    h.order.2.2.1.trans h.order.2.2.2⟩, h.lag, ?_, h.fastPart⟩
  have hL := (arming_L_pos p).le
  have hη := p.etaNonneg
  exact (sub_self b₀).symm ▸ le_min hη hL

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; acceptance at the early boundary
still relays strictly before the freeze. -/
theorem outageV_source_relay_before_freeze (p : Params) (s : Slot) (u gst : Time)
    (hu : u ≤ SA.earlyTime p.toParams s)
    (hg : gst ≤ SA.voteTime p.toParams s) :
    max u gst + p.Δ ≤ SA.freezeTime p.toParams s := by
  rw [arming_early_eq] at hu
  rw [arming_vote_eq] at hg
  rw [arming_freeze_eq]
  have := p.deltaPos
  rcases max_cases u gst with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; even an old acceptance has a relay
bound strictly before the next HEAD once GST precedes this HEAD. -/
theorem outageV_regression_relay_bound (p : Params) (s : Slot) (u gst : Time)
    (hu : u ≤ SA.voteTime p.toParams s) (hg : gst ≤ SA.voteTime p.toParams s) :
    max u gst + p.Δ ≤ SA.voteTime p.toParams s + p.Δ ∧
    SA.voteTime p.toParams s + p.Δ < SA.voteTime p.toParams (s + 1) := by
  refine ⟨by have := max_le hu hg; linarith, ?_⟩
  rw [arming_vote_eq, arming_vote_eq]
  push_cast
  have := p.deltaPos
  nlinarith

/-- The approved handover is exactly v(r+k+1), also the last old gate's expiry. -/
theorem outage_handover_time (p : Params) (r : Slot) :
    OutageEnd p r = SA.voteTime p.toParams (r + p.k + 1) ∧
      OutageEnd p r = SA.gateTime p.toParams r + L p := by
  change 4 * p.Δ * ((r + p.k : Nat) : Int) + 5 * p.Δ =
      4 * p.Δ * ((r + p.k + 1 : Nat) : Int) + p.Δ ∧
    4 * p.Δ * ((r + p.k : Nat) : Int) + 5 * p.Δ =
      4 * p.Δ * (r : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
  push_cast
  constructor <;> ring

end AvailableChain.FGSA.Run
end
