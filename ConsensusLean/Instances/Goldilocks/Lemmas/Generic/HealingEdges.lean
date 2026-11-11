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

/-- UNPROVED reset-or-no-advance corollary of the high-signing leaf. -/
def reset_or_noAdvance : Prop :=
  reset_of_height_advance_at A sg →
  ∀ {tr H proposer dg g ΔF b T}, Premises tr H proposer dg sg g ΔF b → T ≤ b →
    (∃ a, IsReset tr H g a ∧ a ≤ T) ∨ NoAdvance tr H g T

/-- UNPROVED rise assembly from original leaves and the protocol warmth obligations. -/
def rise_reset_rounds_at_of (O : ACHealing A sg) : Prop :=
  reset_of_high_proposal_at A sg O → round_of_warm_at A sg O →
    proposal_mem_at A sg → rise_reset_rounds_at A sg O

/-- UNPROVED whole-run endpoint assembly; no bundled premise replaces the endpoint's inputs. -/
def exists_reset_of_drain_rounds_noRestartAfter_at_of (O : ACHealing A sg) : Prop :=
  reset_of_height_advance_at A sg → hmax_le_of_noAdvance_at A sg → HZ_le_hmax_at A sg →
  snapshotCall_of_awake_at A sg → callLag_of_awake_at A sg →
  exists_frameWindow_seq_of_service_at A sg → exists_slot_align (P := P) →
  rounds_le_warm_proposal_at A sg O → rise_reset_rounds_at A sg O →
    exists_reset_of_drain_rounds_noRestartAfter_at A sg O

/-- UNPROVED finite-horizon assembly through the protocol's run and warmth truncation laws. -/
def exists_reset_of_drain_rounds_awake_at_of (O : ACHealing A sg) : Prop :=
  exists_reset_of_drain_rounds_noRestartAfter_at A sg O →
  resetService_truncH A → catchRun_truncH A → proposalGap_truncH A →
  drainOutputs_truncH A sg O → isReset_of_truncH A →
    exists_reset_of_drain_rounds_awake_at A sg O

/-- UNPROVED bundled rise corollary, retaining the exact proposal and cutoff inputs. -/
def rise_reset_rounds (O : ACHealing A sg) : Prop :=
  rise_reset_rounds_at A sg O →
  ∀ {tr H proposer dg g ΔF b s₀ N G floor kindJ J T},
    O.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b →
    SlotWindow tr H s₀ N floor kindJ J → gbar g + 4 * P.Δ ≤ P.slotTime s₀ →
    1 ≤ G → ProposalGap tr H proposer G s₀ N → P.slotTime N + 2 * P.Δ ≤ b →
    T ≤ b → NoAdvance tr H g T → ∀ (r : Nat) {u z k X},
      s₀ ≤ u → O.Warm tr H s₀ u → u + r * (P.δt + G - 1) + 1 ≤ N →
      P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ ≤ T →
      HonestProposal tr H proposer u z k X →
      HZ tr H g + 1 ≤ ((tr.state z (k + 1)).fg.σ X.root).h + r →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ

/-- UNPROVED canonical-high assembly, including independently bounded historical readers. -/
def highCanonical (O : ACHealing A sg) : Prop :=
  high_row_source_at A sg O → no_high_contest_at A sg O → high_entry_eq_at A sg O →
  ∀ {tr H proposer dg g ΔF b a},
    O.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → HighCanonical O.Origin tr H g b

/-- UNPROVED slot-budget reset assembly; it is not the old real-time endpoint. -/
def exists_reset (O : ACHealing A sg) : Prop :=
  reset_or_noAdvance A sg → exists_frameWindow_seq_of_service_at A sg →
  rounds_le_warm_proposal_at A sg O → rise_reset_rounds A sg O →
  ∀ {tr H proposer dg g ΔF b G s},
    O.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt)

/-- UNPROVED proposal-chaining assembly; no confirmed-tip guarantee is asserted. -/
def generic_healing (O : ACHealing A sg) : Prop :=
  exists_reset A sg O → highCanonical A sg O →
  ∀ {tr H proposer dg g ΔF b G s},
    O.Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b → 1 ≤ G →
    gbar g ≤ P.slotTime s → cutZ P g ≤ P.slotTime s →
    ProposalGap tr H proposer G s (s + resetSlots O.warmup G P.δt) →
    P.slotTime (s + resetSlots O.warmup G P.δt) ≤ b →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (s + resetSlots O.warmup G P.δt) ∧
      HealedFrom tr H proposer (P.slotOf a + O.drain) b

end Consensus.Goldilocks.Generic

end
