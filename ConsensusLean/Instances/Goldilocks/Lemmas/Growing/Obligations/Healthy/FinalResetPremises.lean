module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalDutyProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalQueryTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HonestNonempty
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset premises and the placement of a final query, under growing faults

The growing form of `Obligations/FinalResetPremises`, with each node honest at its own cut and
the fault bound per time:

* `final_query_gap_at` (`final_query_gap`): the honest-proposer gap of a final query, as the
  kernel's `ProposalGap` (the designated proposer honest through its slot's hold);
* `final_reset_premises_of_shared_at` (`final_reset_premises_of_shared`): from the shared HS
  premises at a forwarding delay `ΔF` and the final pattern `[0, c, 2c, 3c]` with `2 ≤ c` and
  `3c ≤ δ_t`, a reset `a` with its finite premises through the horizon and the placement;
* `final_reset_premises_at`: its instance at the FG gap `c = fgSlots` and the protocol FG delay.

The reset is the growing kernel's `exists_reset_of_drain_rounds_awake_at` on the drain
`drainOutputs_of_service_at`; the snapshot is the static `snapshot_of_awake` on the prefix through
the horizon. The ready scalar, the reset bound, the horizon of the gap and the placement are the
static `final_reset_bounds`, the duties of the gap the static `final_query_duty`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The honest-proposer gap of a final query**, under growing faults: every slot window
`[x₀, x₀ + X)` inside `[s₀, N]` has an actual designated proposal whose proposer is honest
through its slot's hold. -/
theorem final_query_gap_at (Q : FinalQueryAt S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer ⟨S, stock⟩ Q.run.2 Q.hn x ∈ Q.keys (Q.params.ts x + Q.params.Δ) ∧
      ∃ k P, Q.trace.ProposesAt (runProposer ⟨S, stock⟩ Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx0, hxh, hx⟩ :=
    final_query_duty S A V Q.run Q.hn Q.index Q.gst Q.progress hpat hs hN x₀ hx₀ hxN
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := final_duty_proposal_run_at S A V Q hx0 hxh hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`**, under growing faults. -/
theorem final_reset_premises_of_shared_at (Q : FinalQueryAt S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔF
      Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer ⟨S, stock⟩ Q.run.2 Q.hn)
        (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen := by
  classical
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  set H := Q.keys
  have hD : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hk : Q.params.k = S.k := rfl
  obtain ⟨hr0, hgr, hcz, h4B, hBh, hgapN, hplace⟩ :=
    final_reset_bounds S A V Q.run Q.hn Q.index Q.gst Q.query Q.mature Q.bounded hc2 h3c
  have hb0 : (0 : Time) ≤ Q.run.2.horizon := by linarith only [hr0, h4B, hBh, hD]
  have hH : (H Q.run.2.horizon).Nonempty :=
    nonempty_of_fault_bound (hs.faults Q.run.2.horizon hb0 le_rfl) Q.params.toParams.hn
  -- Catch with `κ = 2Δ`
  have hcatch : Healing.Growing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid hs.noColl hnet
      (fun v t ht hb _ hv => Q.healthy.2.1.2 v t ht hb hv)
  -- the drain
  have hdrain : Healing.Growing.DrainOutputs Q.trace (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) H Q.gst
      (Q.index : Nat) (healthyDrainLen S Q.index) Q.run.2.horizon :=
    Healing.Growing.drainOutputs_of_service_at hrun hs.noColl hs.sync hs.awake hs.faults hcatch
      (by rw [healthyDrainLen_val, hk]; exact Nat.le_succ _)
  -- the reset
  obtain ⟨a, ha, hab⟩ := Healing.Growing.exists_reset_of_drain_rounds_awake_at hrun hs.noColl
    hs.faults hs.sync hs.awake hcatch (Healing.Growing.noRestartUpTo_iff.mpr hs.noRestart) hH
    (by rw [hδeq]; exact (Nat.le_mul_of_pos_right 3 ((by decide : 0 < 2).trans_le hc2)).trans h3c)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz hBh
    (fun s₀ N hs₀ hN => Healing.Growing.proposalGap_iff.mpr <| final_query_gap_at S A V Q hpat
      (by rw [max_eq_left hr0]; exact hs₀) (hgapN N hN))
    hdrain rfl
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake (hrun.upTo hb0)
    (fun y hy t ht htb => ⟨hs.awake y t (hrun.antitone htb hy) ht htb, htb⟩) hH
    (b := Q.run.2.horizon) (by linarith only [hcz, h4B, hBh])
  refine ⟨ΔF, a, ⟨hrun, hs.noColl, hs.sync, hs.awake, hs.faults, ha, hab.trans hBh,
    ⟨j, hj, hjt⟩, rfl⟩, ?_⟩
  -- the placement (H3)
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  exact hplace a ha0 hab

/-- **The reset premises and the placement of a final query**, under growing faults. -/
theorem final_reset_premises_at (Q : FinalQueryAt S A V) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer ⟨S, stock⟩ Q.run.2 Q.hn)
        (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen :=
  final_reset_premises_of_shared_at S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
    (FinalQueryAt.hsSharedUpTo_at Q)

end Consensus.Goldilocks.Obligations.Growing

end
