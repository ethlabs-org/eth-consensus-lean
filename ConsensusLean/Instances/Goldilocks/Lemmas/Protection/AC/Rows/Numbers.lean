module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: the outage numbers at the AC windows

The arithmetic rows of the outage arming (`Obligations/OutageArming`), at the parameters `sp` and
the AC no-sleep window `[protStartAC sp q b₀, protEndAC sp q b₁]` (no horizon):

* (A1) the profile's lag at a point of the contract's outage is the node lag `(4k + 6)Δ`
  (`outage_node_lagAC`, from `protLagAC0 sp q = c` and `T + c·Δ ≤ b₀`);
* (A4)/(A5) under that lag, with `4k + 6 ≤ q.noSleep`, the window starts at or after `0` and by
  `t_{j₀−k}`, and ends at or after `t_{j₀} + 6Δ`, for the cover label `j₀ = coverLabel sp b₀`
  (`outage_window_coverAC`).

The cover label and its arithmetic (`Compose.coverLabel`, `Compose.coverLabel_gates`,
`Compose.armed_label_lt`, `Obligations/OutageArmingSteps`) are stated over `sp : SAParams` alone
and are reused here as they are. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams}

/-- **(A1) The node lag**: a lag `c` of the default profile (`protLagAC0 sp q = c`) with
`T + c·Δ ≤ b₀` is the node lag `T + (4k + 6)Δ ≤ b₀`. -/
theorem outage_node_lagAC {q : ProtQ} {c : ℕ} (hc : protLagAC0 sp q = c) {T b₀ : Time}
    (hlag : T + (c : Time) * sp.Δ ≤ b₀) : T + (4 * sp.k + 6) * sp.Δ ≤ b₀ := by
  unfold protLagAC0 at hc
  split_ifs at hc
  · have hc' : 4 * sp.k + 6 = c := by exact_mod_cast hc
    subst hc'
    push_cast at hlag
    exact hlag
  · exact absurd hc WithTop.top_ne_coe

/-- **(A4)/(A5) The no-sleep window covers the arming labels**: under the node lag, with
`0 ≤ T`, `b₀ ≤ b₁` and `4k + 6 ≤ q.noSleep`, the window `[protStartAC sp q b₀, protEndAC sp q b₁]`
starts at or after `0` and by `t_{j₀−k}`, and ends at or after every time up to the update
`t_{j₀} + 6Δ` of the cover label `j₀ = coverLabel sp b₀`. -/
theorem outage_window_coverAC {q : ProtQ} (hns : 4 * sp.k + 6 ≤ q.noSleep) {T b₀ b₁ : Time}
    (hT : 0 ≤ T) (hlag : T + (4 * sp.k + 6) * sp.Δ ≤ b₀) (hb : b₀ ≤ b₁) :
    0 ≤ protStartAC sp q b₀ ∧
      protStartAC sp q b₀ ≤ sp.ts ((Compose.coverLabel sp b₀ : Int) - sp.k) ∧
      ∀ d ≤ 6 * sp.Δ, sp.ts (Compose.coverLabel sp b₀) + d ≤ protEndAC sp q b₁ := by
  have hΔ := sp.toParams.hΔ
  have hk : (0 : Time) ≤ sp.k := by positivity
  have hkj := (Compose.armed_label_lt (sp := sp) (σ := 0) hT hlag
    (by simp [SAParams.ts]; exact hT)).2
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := sp) (b₀ := b₀) (by
    have : (0 : Time) ≤ (4 * sp.k + 4) * sp.Δ := by positivity
    linarith)
  set j₀ := Compose.coverLabel sp b₀
  have hkj' : (sp.k : Int) < j₀ := by exact_mod_cast hkj
  have hns' : (4 * (sp.k : Time) + 6) ≤ q.noSleep := by exact_mod_cast hns
  have hN := mul_le_mul_of_nonneg_right hns' hΔ.le
  have hkΔ := mul_nonneg hk hΔ.le
  simp only [protStartAC, protEndAC, SAParams.ts] at hg₁ hg₂ ⊢
  refine ⟨le_max_left _ _, max_le ?_ ?_, fun d hd => ?_⟩
  · have : (0 : Time) ≤ (j₀ : Int) - sp.k := by linarith
    positivity
  · linarith
  · linarith

end Consensus.Goldilocks.Comparison

end
