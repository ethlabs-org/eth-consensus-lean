module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Generic healing assembly edges

The assembly edges over any node AC, from the generic healing leaves (`HealingLeaves` and
`HealingRounds`).

`reset_or_noAdvance` is proved: a high signing before `T` by a signer honest at it and at `c_z`
gives a reset no later (leaf 1, `reset_of_height_advance_at_from`); without one, `NoAdvance` holds
at `T`.

`highCanonical` is proved over any `ACHealing`: by the horizon of a premised reset, honest stores
have no high contest (leaf 13), high signings come from high origins (leaf 12), and self-entries of
equal height below two high origins are equal (leaf 14, `high_entry_eq_at_of_healing`).

`rise_reset_rounds_at_of` proves the rise contract `rise_reset_rounds_at` over any `ACHealing`, by
induction on the remaining rounds: a warm high proposal gives the reset (leaf 10); a lower one is
crossed by the next honest proposal `δt` to `δt + G - 1` slots later (leaf 11), which is one round
closer.

The remaining definitions are UNPROVED implication contracts, not theorem evidence.
Old-premise leaves remain primary; bundled-premise forms are conditional corollaries.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
open Healing (cutZ)
open Healing.Growing (HZ IsReset)

section Proved

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

/-- Reset or no advance: by a horizon of the bundled premises, either a reset happens by `T` or
no signer honest at its signing and at `c_z` signs above `HZ` before `T`. A high signing gives
the reset by leaf 1, with fewer than `q` faulty nodes at `max c_z t_k ≤ b` (`Premises.faults`,
`Premises.snapshot`). -/
theorem reset_or_noAdvance :
    ∀ {cm βK tr H proposer dg g ΔF b T},
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → T ≤ b →
      (∃ a, IsReset tr H g a ∧ a ≤ T) ∨ NoAdvance tr H g T := by
  intro cm βK tr H proposer dg g ΔF b T hrun hP hTb
  by_cases hadv : ∃ v k att, v ∈ H (max (cutZ P g) (tr.time k)) ∧ tr.SignAt v k att ∧
      tr.time k < T ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨v, k, att, hv, hs, hk, hh⟩ := hadv
    have hrl := runs.run_local hrun
    obtain ⟨j, hj, hjb⟩ := hP.snapshot
    have hmax : max (cutZ P g) (tr.time k) ≤ b := max_le (hj.2.le.trans hjb) (hk.le.trans hTb)
    obtain ⟨a, ha, hak⟩ := reset_of_height_advance_at_from hrl
      (faults_lt_q hP.faults ((hrl.time_nonneg k).trans (le_max_right _ _)) hmax) hv hs hh
    exact Or.inl ⟨a, ha, hak.trans hk.le⟩
  · refine Or.inr fun v k att hv hs hk => ?_
    by_contra h
    exact hadv ⟨v, k, att, hv, hs, hk, by omega⟩

/-- Canonical high entries by the horizon of a premised reset, field by field from leaves 13, 12
and 14 over the supplier `O`. -/
theorem highCanonical (O : ACHealing A sg runs) :
    ∀ {cm βK tr H proposer dg g ΔF b a}, βK ≤ 1 / 2 →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b →
      IsReset tr H g a → a ≤ b → HighCanonical O.Origin tr H g b := by
  intro cm βK tr H proposer dg g ΔF b a hβ hrun hP hr hab
  refine ⟨fun _ _ hp hib => no_high_contest_at_of_healing O hβ hrun hP hr hab hp hib,
    fun _ _ _ hy hs hkb hh => ?_, ?_⟩
  · obtain ⟨r, hrk, l, Og, ⟨hyr, hO, hOh⟩, E, hE, hEO, hEr, hEh, hET⟩ :=
      high_row_source_at_of_healing O hβ hrun hP hr hab hy hkb hs hh
    exact ⟨r, hrk, l, Og, hO, hyr, hOh, E, hE, hEO, hEr, hEh, hET⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx hO hib hBh hx' hO' hi'b hB'h h₁ h₂ ht₁ hle₁ hy₁
      ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
    exact high_entry_eq_at_of_healing O hβ hrun hP hr hab ⟨hx, hO, hBh⟩ hib ⟨hx', hO', hB'h⟩
      hi'b h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

/-- The rise contract over the supplier `O`, by induction on the remaining rounds `r`. A warm
proposal at or above `HZ + 1` gives the reset by leaf 10. Otherwise the proposal gap gives an
honest proposal `x` in `[u + δt, u + δt + G - 1]`; leaf 11 puts it one height above the warm
proposal in its proposer's store, which has the warm proposal's replay state
(`proposal_mem_at_from`, `σ_eq_honest_at_from`), and the induction hypothesis applies at `x`.
The spacing gives `δt ≥ 2` with `ΔF > 0`, and every slot time is read from `ProposesAt`. -/
theorem rise_reset_rounds_at_of (O : ACHealing A sg runs) : rise_reset_rounds_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b T s₀ N G floor kindJ J hβ hcom hframe hrun hnc hsvc
    hawake hf hcatch hnr hsl hsp hsnap hm hfol hG htd hgp hmb hHb hTb hna r
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  have hdF := hsvc.deltaF
  have hmono := P.slotTime_strictMono.monotone
  have hδ2 : 2 ≤ P.δt := by
    by_contra h1
    have h := hsp 0
    have := hmono (show 0 + P.δt ≤ 0 + 1 by omega)
    linarith
  induction r with
  | zero =>
    intro u z kB B hs₀u hwarm hN hT hz hdes hB hBs hrise
    simpa only [Nat.zero_mul, Nat.add_zero] using
      reset_of_high_proposal_at_of_healing O hβ hcom hframe hrun hnc hsvc hawake hf hcatch hnr
        hsl htd hsnap hm hs₀u hwarm (by simpa using hN) hmb hHb hz hdes hB hBs
        (by simpa using hrise)
  | succ r ih =>
    intro u z kB B hs₀u hwarm hN hT hz hdes hB hBs hrise
    have hmul : (r + 1) * (P.δt + G - 1) = r * (P.δt + G - 1) + (P.δt + G - 1) :=
      Nat.succ_mul r _
    by_cases hh : HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h
    · obtain ⟨a, ha, hat⟩ := reset_of_high_proposal_at_of_healing O hβ hcom hframe hrun hnc hsvc
        hawake hf hcatch hnr hsl htd hsnap hm hs₀u hwarm (by omega) hmb hHb hz hdes hB hBs hh
      exact ⟨a, ha, hat.trans (by
        linarith [hmono (show u + 1 ≤ u + (r + 1) * (P.δt + G - 1) + 1 by omega)])⟩
    obtain ⟨x, hxl, hxr, hpx, kX, X, hX, hXs⟩ := hgp (u + P.δt) (by omega) (by omega)
    have htX : tr.time kX = P.slotTime x := by rw [hX.2.2, hXs]
    have hpx0 : proposer x ∈ H (tr.time kX) := hrl.antitone (by rw [htX]; linarith) hpx
    have hstrict : P.slotTime (u + 1) + 2 * P.Δ < T := by
      have := P.slotTime_strictMono (show u + 1 < u + (r + 1) * (P.δt + G - 1) + 1 by omega)
      linarith
    obtain ⟨hBp, -, hcross⟩ := round_of_warm_at_of_healing O hβ hcom hframe hrun hnc hsvc hawake
      hf hcatch hnr hsl hsp hsnap hm hs₀u hwarm hfol htd hxl (by omega) hmb hHb hTb hna hstrict
      hz hdes hB hBs hpx0 rfl hX hXs
    have htB : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
    have hz0 : z ∈ H (tr.time kB) := hrl.antitone (by rw [htB]; linarith) hz
    have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc
      hz0 hB
    have hσ := σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB)
      (fun q hq => hrl.time_mono (by omega)) hz0 (hrl.time_nonneg kX)
      (fun q hq => hrl.time_mono (by omega)) hpx0 hBm hBp
    rw [← hσ] at hcross
    have hnext : x + r * (P.δt + G - 1) + 1 ≤ u + (r + 1) * (P.δt + G - 1) + 1 := by omega
    obtain ⟨a, ha, hat⟩ := ih (u := x) (by omega) (by omega) (hnext.trans hN)
      (by linarith [hmono hnext]) hpx rfl hX hXs (by omega)
    exact ⟨a, ha, hat.trans (by linarith [hmono hnext])⟩

end Proved

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg}

/-- UNPROVED whole-run endpoint assembly; no bundled premise replaces the endpoint's inputs. -/
def exists_reset_of_drain_rounds_noRestartAfter_at_of (O : ACHealing A sg runs) : Prop :=
  reset_of_height_advance_at A sg runs → hmax_le_of_noAdvance_at A sg runs →
  snapshotCall_of_awake_at A sg runs → callLag_of_awake_at A sg runs →
  exists_slot_align (P := P) →
  rounds_le_warm_proposal_at A sg O → rise_reset_rounds_at A sg O →
    exists_reset_of_drain_rounds_noRestartAfter_at A sg O

/-- UNPROVED slot-budget reset assembly; it is not the old real-time endpoint. -/
def exists_reset (O : ACHealing A sg runs) : Prop :=
  rounds_le_warm_proposal_at A sg O → rise_reset_rounds_at A sg O →
  ∀ {cm βK tr H proposer dg g ΔF b G s}, βK ≤ 1 / 2 →
    (∀ u, P.slotTime (u + 1) + 2 * P.Δ + ΔF ≤ P.slotTime (u + P.δt)) →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt)

/-- UNPROVED proposal-chaining assembly; no confirmed-tip guarantee is asserted. -/
def generic_healing (O : ACHealing A sg runs) : Prop :=
  exists_reset A sg O →
  ∀ {cm βK tr H proposer dg g ΔF b G s}, βK ≤ 1 / 2 →
    (∀ u, P.slotTime (u + 1) + 2 * P.Δ + ΔF ≤ P.slotTime (u + P.δt)) →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt) ∧
      HealedFrom tr H proposer (P.slotOf a + O.drain) b

end Consensus.Goldilocks.Generic

end
