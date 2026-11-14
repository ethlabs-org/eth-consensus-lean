module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation

public section

/-! # Open generic healing assembly edges

All definitions below are UNPROVED implication contracts, not theorem evidence.
Old-premise leaves remain primary; bundled-premise forms are conditional corollaries.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
open Healing (cutZ)
open Healing.Growing (HZ IsReset)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg}

/-- UNPROVED reset-or-no-advance corollary of the high-signing leaf. -/
def reset_or_noAdvance : Prop :=
  reset_of_height_advance_at A sg runs →
  ∀ {cm βK tr H proposer dg g ΔF b T},
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → T ≤ b →
    (∃ a, IsReset tr H g a ∧ a ≤ T) ∨ NoAdvance tr H g T

/-- UNPROVED rise assembly from original leaves and the protocol warmth obligations. -/
def rise_reset_rounds_at_of (O : ACHealing A sg runs) : Prop :=
  reset_of_high_proposal_at A sg O → round_of_warm_at A sg O →
    proposal_mem_at A sg runs → rise_reset_rounds_at A sg O

/-- UNPROVED whole-run endpoint assembly; no bundled premise replaces the endpoint's inputs. -/
def exists_reset_of_drain_rounds_noRestartAfter_at_of (O : ACHealing A sg runs) : Prop :=
  reset_of_height_advance_at A sg runs → hmax_le_of_noAdvance_at A sg runs →
  snapshotCall_of_awake_at A sg runs → callLag_of_awake_at A sg runs →
  exists_frameWindow_seq_of_service_at A sg → exists_slot_align (P := P) →
  rounds_le_warm_proposal_at A sg runs → rise_reset_rounds_at A sg O →
    exists_reset_of_drain_rounds_noRestartAfter_at A sg O

/-- UNPROVED canonical-high assembly, including independently bounded historical readers. -/
def highCanonical (O : ACHealing A sg runs) : Prop :=
  high_row_source_at A sg O → no_high_contest_at A sg runs → high_entry_eq_at A sg O →
  ∀ {cm βK tr H proposer dg g ΔF b a}, βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → HighCanonical O.Origin tr H g b

/-- UNPROVED slot-budget reset assembly; it is not the old real-time endpoint. -/
def exists_reset (O : ACHealing A sg runs) : Prop :=
  reset_or_noAdvance A sg (runs := runs) → exists_frameWindow_seq_of_service_at A sg →
  rounds_le_warm_proposal_at A sg runs → rise_reset_rounds_at A sg O →
  ∀ {cm βK tr H proposer dg g ΔF b G s}, βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt)

/-- UNPROVED proposal-chaining assembly; no confirmed-tip guarantee is asserted. -/
def generic_healing (O : ACHealing A sg runs) : Prop :=
  exists_reset A sg O → highCanonical A sg O →
  ∀ {cm βK tr H proposer dg g ΔF b G s}, βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt) ∧
      HealedFrom tr H proposer (P.slotOf a + O.drain) b

end Consensus.Goldilocks.Generic

end
