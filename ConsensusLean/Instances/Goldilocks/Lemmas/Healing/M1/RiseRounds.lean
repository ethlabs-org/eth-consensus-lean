module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Key-dependent rise rounds

recovery_time_savings item 1, piece (2). The rise reset stops after 0 or 1 rounds when the
warm proposal is high. `FrameWindow.rise_reset_rounds` makes the round count `r ≤ 2` explicit:
with `HZ + 1 ≤ σ[P].h + r` and `u + r·ρ + 1 ≤ N`, a reset by `t_{u+r·ρ+1} + 2Δ`.
The proof uses the same public steps (`reset_of_height_advance`,
`FrameWindow.reset_of_high_proposal`, `FrameWindow.round_of_warm`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **`r` rounds and the rise reset.** With the round count `r ≤ 2`:
from the actual warm proposal `P` of slot `u` with `HZ + 1 ≤ σ[P].h + r` and
`u + r·ρ + 1 ≤ N` (`ρ = δ_t + G − 1`), a reset by `t_{u+r·ρ+1} + 2Δ`. -/
theorem FrameWindow.rise_reset_rounds
    {g ΔF b : Time} {s₀ u N G floor r : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧ proposer x ∈ H ∧
      ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x)
    (hr : r ≤ 2)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r) :
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ := by
  classical
  have hk := sp.two_le_k
  have hΔ := sp.toParams.hΔ
  set ρ := sp.toParams.fg.δt + G - 1 with hρ
  set T := sp.ts (u + r * ρ + 1 : Nat) + 2 * sp.Δ with hTdef
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have htlt {a c : Nat} (h : a < c) : sp.ts a < sp.ts c :=
    (SA.ts_lt_iff sp).2 (by exact_mod_cast h)
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  -- an honest signature above `HZ` before `T` is already a reset
  by_cases hadv : ∃ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k < T ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨y, hy, k, att, hs, hkT, hh⟩ := hadv
    obtain ⟨a, ha, hak⟩ := reset_of_height_advance hrun hq hy hs hh
    exact ⟨a, ha, by linarith⟩
  have hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g :=
    fun v hv k att hs hkT => by
      by_contra h
      exact hadv ⟨v, hv, k, att, hs, hkT, by omega⟩
  -- a high warm proposal of slot `w` gives the reset (`FrameWindow.reset_of_high_proposal`)
  have hF : ∀ w, s₀ + 2 * sp.k ≤ w → w + 1 ≤ u + r * ρ + 1 → ∀ Q kQ,
      tr.ProposesAt (proposer w) kQ Q → Q.slot = w → proposer w ∈ H →
      HZ tr H g + 1 ≤ ((tr.state (proposer w) (kQ + 1)).fg.σ Q.root).h →
      ∃ a, IsReset tr H g a ∧ a ≤ T := by
    intro w hw hwN Q kQ hQ hQs hpw hh
    obtain ⟨t, rfl⟩ : ∃ t, w = t + 1 := ⟨w - 1, by omega⟩
    obtain ⟨-, hQm, -⟩ := accept_of_proposesAt hrun hnc hpw hQ
    obtain ⟨a, ha, hat⟩ := hframe.reset_of_high_proposal hrun hnc hsvc hawake hf hcatch hnr
      hm hw (by omega) hmb hpw rfl hQ hQs hpw hQm hh
    exact ⟨a, ha, hat.trans (by linarith [hts (show t + 2 ≤ u + r * ρ + 1 by omega)])⟩
  have hPm := (accept_of_proposesAt hrun hnc hz hP).2.1
  set h₀ := ((tr.state z (kP + 1)).fg.σ P.root).h with hh₀
  by_cases hhigh : HZ tr H g + 1 ≤ h₀
  · subst hdes
    exact hF u hwarm (by omega) P kP hP hPs hz hhigh
  -- round 1
  have hr1 : 0 < r := by omega
  have hρr : ρ ≤ r * ρ := Nat.le_mul_of_pos_left ρ hr1
  obtain ⟨x₁, hx₁l, hx₁r, hp₁, k₁, X₁, hX₁, hX₁s⟩ := hgp (u + sp.toParams.fg.δt)
    (by omega) (by omega)
  have hσy : ∀ y ∈ H, ∀ i, P ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ P.root).h = h₀ := fun y hy i hPy =>
    congrArg FG.ChainState.h (σ_eq_honest hrun hnc hy hz hPy hPm)
  obtain ⟨hPm₁, hXm₁, hr₁⟩ := hframe.round_of_warm hrun hnc hsvc hawake hf hcatch hnr hm hwarm
    hδ hΔF hx₁l (by omega) hmb hna
    (by rw [hTdef]; linarith [htlt (show u + 1 < u + r * ρ + 1 by omega)])
    hz hdes hP hPs hp₁ rfl hX₁ hX₁s
  rw [hσy _ hp₁ _ hPm₁] at hr₁
  set h₁ := ((tr.state (proposer x₁) (k₁ + 1)).fg.σ X₁.root).h with hh₁
  by_cases hhigh₁ : HZ tr H g + 1 ≤ h₁
  · exact hF x₁ (by omega) (by omega) X₁ k₁ hX₁ hX₁s hp₁ hhigh₁
  -- round 2
  have hr2 : r = 2 := by omega
  have h2ρ : r * ρ = 2 * ρ := by rw [hr2]
  obtain ⟨x₂, hx₂l, hx₂r, hp₂, k₂, X₂, hX₂, hX₂s⟩ := hgp (x₁ + sp.toParams.fg.δt)
    (by omega) (by omega)
  have hσy₁ : ∀ y ∈ H, ∀ i, X₁ ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ X₁.root).h = h₁ := fun y hy i hy' =>
    congrArg FG.ChainState.h (σ_eq_honest hrun hnc hy hp₁ hy' hXm₁)
  obtain ⟨hXm₁', -, hr₂⟩ := hframe.round_of_warm hrun hnc hsvc hawake hf hcatch hnr hm
    (by omega) hδ hΔF hx₂l (by omega) hmb hna
    (by rw [hTdef]; linarith [htlt (show x₁ + 1 < u + r * ρ + 1 by omega)])
    hp₁ rfl hX₁ hX₁s hp₂ rfl hX₂ hX₂s
  rw [hσy₁ _ hp₂ _ hXm₁'] at hr₂
  exact hF x₂ (by omega) (by omega) X₂ k₂ hX₂ hX₂s hp₂ (by omega)

end Consensus.Goldilocks.Healing

end
