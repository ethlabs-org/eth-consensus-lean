module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds

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

end Proved

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg}

/-- UNPROVED rise assembly from original leaves and the protocol warmth obligations. Proposal
membership is no longer a premise: `proposal_mem_at_from` (`HealingLeaves`) proves it at any start,
and the run supplies the start, requirements and genesis root (`ACRun.run_local`,
`ACRun.run_requirements`, `ACRun.run_root`). -/
def rise_reset_rounds_at_of (O : ACHealing A sg runs) : Prop :=
  reset_of_high_proposal_at A sg O → round_of_warm_at A sg O → rise_reset_rounds_at A sg O

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
