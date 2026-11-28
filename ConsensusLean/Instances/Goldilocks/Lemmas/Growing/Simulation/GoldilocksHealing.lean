module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LaterHead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalPersistence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.BoundariesCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.HealedCoverSupply
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks healing fields at committee size

Fields of the committee-indexed Goldilocks healing supplier (`goldilocksACHealing`) over the shared
run interface `goldilocksRunInterface`, whose runs start each node with its committee permission
and carry the committee facts under collision freedom:

* `report_in_frame`: `goldilocks_report_in_frame`, the report's finalized-root ancestry
  (`Shadow.PU.Growing.report_root_at` at the committee start);
* `heal_after_reset`: `goldilocks_heal_after_reset`, at the drain `2k + 5` of
  `GoldilocksHealingData`, by `honest_proposal_below_next_upTo_at` and
  `honest_proposal_below_later_upTo_at`.

`heal_after_reset` reads the bundled premises through the finite reset record
`resetPremisesUpTo_of_premises_budget`. `follow_le` is the explicit timeout bound `3 ≤ δt` itself.
-/

namespace Consensus.Goldilocks.Generic

open AC (ACParams Payload)
open Healing (cutZ)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {sign : Fin sp.n → Time → Bool} {G : Nat}


/-- The time `t_{slot c_z + m}` is at most `c_z + 4mΔ`: `c_z ≥ 0` is at or after the start of its
own slot. -/
private theorem slotTime_cutZ_add_le (g : Time) (m : Nat) :
    sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + m) ≤
      cutZ sp.toParams g + 4 * m * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hz0 : 0 ≤ cutZ sp.toParams g := by
    have := Healing.lt_cutZ sp g; linarith [AC.gbar_nonneg g]
  have hfl : sp.ts (sp.slot (cutZ sp.toParams g)) ≤ cutZ sp.toParams g :=
    (AC.ts_le_iff_le_slot sp hz0 _).2 le_rfl
  have : sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + m) =
      sp.ts (sp.slot (cutZ sp.toParams g)) + 4 * m * sp.Δ := by
    rw [sp.slotTime_eq]; simp only [ACParams.ts]; push_cast
    change 4 * sp.Δ * ((sp.slot (cutZ sp.toParams g) + m : Nat) : Int) = _
    push_cast; ring
  linarith

/-- The per-slot timeout delay of the bundled premises, on the four-`Δ` slot grid. -/
private theorem timeoutDelay_scalar {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g ΔF b hold : Time}
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold) :
    6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time) := by
  have h := hp.timeoutDelay 0
  rw [sp.slotTime_eq, sp.slotTime_eq] at h
  have hδ : (sp.toParams.δt : Time) = sp.toParams.fg.δt := rfl
  rw [← hδ]
  push_cast at h
  linarith

/-- **The bundled premises with a reset in the deep budget**: the finite reset record through the
horizon, its deep cover built inside (`resetPremisesUpTo_of_reset_cover_at`): the quarantine arm
when the horizon is inside `c_z + 4DΔ`; otherwise the record restricted to `T = c_z + 4DΔ`, with
the drain of `a` at least `4Δ` before `T` (the budget: `slot a + drain + 1 ≤ slot c_z + D`), gives
the high-source cover through the horizon (`healthy_high_source_cover_at`). -/
theorem resetPremisesUpTo_of_premises_budget {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbud : ResetInBudget sp.toParams sp.deepDepth (2 * sp.k + 5) g a) :
    Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold := by
  have hrun' := (goldilocksRunInterface_run_iff cm).mp hrun
  have hΔ := sp.toParams.hΔ
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, q, _, _, _, _, hqa⟩, _⟩ := hr
    rw [← hqa]; exact hrun'.1.time_nonneg q
  have hΔF := timeoutDelay_scalar hp
  have hsvc : Healing.Growing.ResetService tr H g ΔF b hold :=
    ⟨hp.sync.deltaF, hp.sync.message, hp.sync.block, hp.sync.relay, hp.sync.signedRow,
      hp.sync.hold_le⟩
  refine Healing.Growing.resetPremisesUpTo_of_reset_cover_at hrun'.1 hp.noColl hsvc hp.awake
    hp.faults hr ha0 hab hp.snapshot hp.catchUp
    (Healing.Growing.noRestartUpTo_iff.2 fun y q hy hq _ => hp.noRestart y q hy hq) hΔF
    hp.nonempty (hrun'.2.2.2.1 hp.noColl) hβ hrun'.2.1 hp.committee (fun D hD => ?_)
    fun T hpT hT hd hTb => Healing.Growing.healthy_high_source_cover_at hpT hT hd hTb hsvc.toAC
      hp.awake hp.faults hp.committee
  -- the budget: `t_{slot a + 2k + 6} ≤ t_{slot c_z + D} ≤ c_z + 4DΔ`
  have hb := hbud D hD
  have hsl : sp.toParams.slotOf a = sp.slot a := rfl
  rw [hsl] at hb
  have hle := slotTime_cutZ_add_le (sp := sp) g D
  have hmono : sp.ts (sp.slot a + 2 * sp.k + 6 : Nat) ≤
      sp.toParams.slotTime (sp.toParams.slotOf (cutZ sp.toParams g) + D) := by
    rw [sp.slotTime_eq]
    exact (AC.ts_le_iff sp).2 (by exact_mod_cast (show sp.slot a + 2 * sp.k + 6 ≤
      sp.toParams.slotOf (cutZ sp.toParams g) + D by omega))
  have hts : sp.ts (sp.slot a + 2 * sp.k + 6 : Nat) =
      Healing.drainTime sp a + 4 * sp.Δ := by
    rw [Healing.drainTime_eq]; simp only [ACParams.ts]; push_cast; ring
  linarith

/-- `report_in_frame`: an honest report lies in its reporter's tree above the finalized root. -/
theorem goldilocks_report_in_frame {cm : Time → Finset (Fin sp.n)}
    {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hy : y ∈ H (tr.time i)) (hR : ReportAt tr y i R) :
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.F R := by
  have hrun := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  obtain ⟨ell, hc, hto, hret⟩ := hR
  refine Shadow.PU.Growing.report_root_at hrun hy
    ⟨Compose.projAC_callAt.mpr hc, hto, ?_⟩
  rw [Compose.Growing.projAC_state_at hrun hy]
  exact hret

/-- `heal_after_reset` at the drain `2k + 5`: honest proposals from `2k + 5` slots after the
reset's slot are chained through the horizon, one slot on with the service reserve and two or
more slots on. -/
theorem goldilocks_heal_after_reset {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF a b hold : Time} (hβ : βK ≤ 1 / 2)
    (hrun : (goldilocksRunInterface sp sign G).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b hold)
    (hr : Healing.Growing.IsReset tr H g a) (hab : a ≤ b)
    (hbudget : ResetInBudget sp.toParams sp.deepDepth (2 * sp.k + 5) g a) :
    HealedFrom tr H proposer (sp.toParams.slotOf a + (2 * sp.k + 5)) b := by
  have hq := resetPremisesUpTo_of_premises_budget hβ hrun hp hr hab hbudget
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts (u : Nat) : sp.toParams.slotTime u = sp.ts u := by
    rw [sp.slotTime_eq]; simp [ACParams.ts]
  have hpr {u : Nat} {w : Fin sp.n} {kw : Nat} {Y : AC.Blk sp.n (List (FG.Att sp.n))}
      (hY : HonestProposal tr H proposer u w kw Y) :
      Healing.Growing.HonestProposalRun tr H proposer u Y :=
    Healing.Growing.honestProposalRun_of_proposesAt_at hq.run hq.noColl
      (by rw [← hts]; exact hY.honest) hY.designated hY.proposes hY.slot
  intro s s' z z' k k' X X' hs hss hb hX hX'
  have hs' : sp.slot a + 2 * sp.k + 5 ≤ s := by
    have : sp.toParams.slotOf a = sp.slot a := rfl
    omega
  have hR : Healing.drainTime sp a ≤ sp.ts s := by
    rw [Healing.drainTime_eq]
    exact (AC.ts_le_iff sp).2 (by exact_mod_cast hs')
  rw [hts] at hb
  rcases Nat.lt_or_ge (s + 1) s' with h | h
  · exact Obligations.Growing.honest_proposal_below_later_upTo_at hq (hpr hX) hR (hpr hX')
      (by omega) (by linarith)
  · obtain rfl : s' = s + 1 := by omega
    have hle : sp.ts s ≤ sp.ts (s + 1 : Nat) := (AC.ts_le_iff sp).2 (by push_cast; omega)
    exact Obligations.Growing.honest_proposal_below_next_upTo_at hq (hpr hX) hR (hpr hX')
      (by linarith)

end Consensus.Goldilocks.Generic

end
