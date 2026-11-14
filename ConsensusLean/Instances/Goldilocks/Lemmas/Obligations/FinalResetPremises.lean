module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalHealHorizon
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalQueryTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HonestNonempty
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Obligations: the reset premises and the placement of a final query

Route A. `final_reset_premises_of_query` has the
statement of the leaf `final_reset_premises` (Concrete.lean): one reset `a` with (H1) its premises
`ResetPremisesUpTo` through the horizon at GST `Q.gst`, and (H3) the placement with
`u_min = finalSeedMin Q a = slot a + 2k + 5`. It is the instance at the protocol FG delay
`ΔF := protoFGDelay` and the gap `c = fgSlots` of `final_reset_premises_of_shared`, which takes the
shared HS premises at a forwarding delay `ΔF` and the final pattern `[0, c, 2c, 3c]` with `2 ≤ c`
and `3c ≤ δ_t`.

The reset is `exists_reset_of_drain_rounds_awake` (the rise-round route) at the ready scalar
`ready` (`ready ≥ 1`), the gap `G = X = Q.index`, the drain length
`L_drain = healthyDrainLen = 2k + X`, `λ = 2Δ` and the service horizon `b = horizon`; its bound is
`B = ready + healthyResetCoeff·Δ`.
The run premises come from the shared HS premises at `Δ_F`, Catch from `catchRun_of_psync`, the
drain from `drainOutputs_of_service`. The gap is `final_query_gap`: the duties of
`final_query_duty` (`recurrence_gap` on the final pattern, span `3c`) with the guarded duty →
proposal adapter `duty_proposal_run`.

The scalar bounds are `final_reset_bounds` (FinalQueryTiming.lean), from the coefficient input
`contract_heal_ge_final` (ContractDefs.lean): the heal coefficient of
the final capability is at least `catchUp + M_f`, `M_f = 20 L_drain + 8k + 28δ_t + 28X + 56`
(in node delays `Δ = Δe`). With it,
`B + (8k + 20)Δ + 4(X + δ_t − 1)Δ − 1 = ready + M_f·Δ − 1 ≤ heal ≤ query`, which is (H3), and
`B + (12c − 2)Δ ≤ heal ≤ horizon` (`final_heal_horizon_fit`, for every `c` with `3c ≤ δ_t`),
which pays the gap's horizon. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The honest-proposer gap of a final query** (premise `hgp` of the rise at `G = X`): for the
final pattern `[0, c, 2c, 3c]` (`hpat`, span `3c`), with `max ready 0 + 4Δ ≤ t_{s₀}` and
`t_{N + 3c} ≤ horizon`, every slot window `[x₀, x₀ + X)` inside `[s₀, N]` has an actual honest
designated proposal. -/
theorem final_query_gap (Q : FinalQuery S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer ⟨S, stock⟩ Q.run.2 Q.hn x ∈ honestKeys ⟨S, stock⟩ Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer ⟨S, stock⟩ Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx0, hxh, hx⟩ :=
    final_query_duty S A V Q.run Q.hn Q.index Q.gst Q.progress hpat hs hN x₀ hx₀ hxN
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := duty_proposal_run S A V Q.run Q.hn Q.constant Q.valid
    Q.noCollision hx0 hxh hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`.** From the shared HS premises `hs` at `ΔF` (whose `timeoutDelay` is `6Δ + ΔF ≤ 4Δ·δ_t`),
the final pattern `[0, c, 2c, 3c]` (`hpat`) with `2 ≤ c` and `3c ≤ δ_t`: a reset `a` with its
premises through the horizon at GST `Q.gst` and `ΔR = ΔF`, and the placement `(P)` with
`u_min = finalSeedMin Q a`. The scalar bounds, with the horizon of the gap, are
`final_reset_bounds`. -/
theorem final_reset_premises_of_shared (Q : FinalQuery S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) (digestOf ⟨S, stock⟩ Q.run.2)
        Q.gst ΔF
      Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys ⟨S, stock⟩ Q.run.2)
        (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔR a
            Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen := by
  classical
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  set H := honestKeys ⟨S, stock⟩ Q.run.2
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hk : Q.params.k = S.k := rfl
  obtain ⟨hr0, hgr, hcz, h4B, hBh, hgapN, hplace⟩ :=
    final_reset_bounds S A V Q.run Q.hn Q.index Q.gst Q.query Q.mature Q.bounded hc2 h3c
  -- whole-run no restart: a restart is a labelled call, at a time `≤ horizon`
  have hnr : Healing.NoRestartAfter Q.trace H (gbar Q.gst) :=
    fun y hy k hk => hs.noRestart y hy k hk
      (simTrace_labelled_time_le ⟨S, stock⟩ Q.run.2 Q.hn Q.valid (by
        obtain ⟨ℓ, hc, -⟩ := hk
        obtain ⟨_, hl⟩ := hc
        intro hn
        rw [hn] at hl
        cases hl))
  have hH : H.Nonempty := nonempty_of_fault_bound hs.faults Q.params.toParams.hn
  -- Catch with `κ = 2Δ`
  have hcatch : Healing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync S Q.run.2 Q.hn Q.constant Q.valid
      (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision) hnet
      (fun v hv t ht hb => Q.healthy.2.1.2 v t ht hb
        ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hv))
  -- the drain
  have hdrain : DrainOutputs Q.trace (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) H Q.gst (Q.index : Nat)
      (healthyDrainLen S Q.index) Q.run.2.horizon :=
    drainOutputs_of_service hrun hs.noColl hs.sync hs.awake hs.faults hcatch hnr
      (by rw [healthyDrainLen_val, hk]; exact Nat.le_succ _) rfl
  -- the reset
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_awake hrun hs.noColl hs.faults hs.sync
    hs.awake hcatch hnr hH
    (by rw [hδeq]; exact (Nat.le_mul_of_pos_right 3 ((by decide : 0 < 2).trans_le hc2)).trans h3c)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz hBh
    (fun s₀ N hs₀ hN => final_query_gap S A V Q hpat (by rw [max_eq_left hr0]; exact hs₀)
      (hgapN N hN))
    hdrain rfl
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake hrun hs.awake hH (b := Q.run.2.horizon)
    (by linarith only [hcz, h4B, hBh])
  refine ⟨ΔF, a, ⟨hrun, hs.noColl, hs.sync, hs.awake, hs.faults, ha, hab.trans hBh,
    ⟨j, hj, hjt⟩, rfl⟩, ?_⟩
  -- the placement (H3)
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, _, k, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  exact hplace a ha0 hab

/-- **The reset premises and the placement of a final query** (the leaf `final_reset_premises`,
Concrete.lean): a reset `a` with its premises through the horizon at GST `Q.gst`, and the
placement `(P)` with `u_min = finalSeedMin Q a`. `final_reset_premises_of_shared` at the gap
`c = fgSlots` of `finalWindow` and the protocol FG delay `ΔF := protoFGDelay`
(`FinalQuery.hsSharedUpTo`). -/
theorem final_reset_premises_of_query (Q : FinalQuery S A V) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys ⟨S, stock⟩ Q.run.2)
        (runProposer ⟨S, stock⟩ Q.run.2 Q.hn) (digestOf ⟨S, stock⟩ Q.run.2) Q.gst ΔR a
            Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen :=
  final_reset_premises_of_shared S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
    Q.hsSharedUpTo

end Consensus.Goldilocks.Obligations

end
