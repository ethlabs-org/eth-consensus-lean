module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetOfDrain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposerGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Lemmas.Blocks.Facts

public section

/-! # Goldilocks Refinement: the reset premises and the placement of a final query (#136)

consensus-lean#136, route A, workbench `heal_bound.md`. `final_reset_premises_of_query` has the
statement of the leaf `final_reset_premises` (Accepted.lean): one reset `a` with (H1) its premises
`ResetPremisesUpTo` through the horizon at GST `Q.gst`, and (H3) the placement with
`u_min = finalSeedMin Q a = slot a + 2k + 5`. It is the instance at the protocol row delay
`ΔF := rowDelay` and the gap `c = cF r` of `final_reset_premises_of_shared`, which takes the shared
HS premises at a forwarding delay `ΔF` and the final pattern `[0, c, 2c, 3c]` with `2 ≤ c` and
`3c ≤ δ_t` (workbench `two_bound_network.md` §4).

The reset is `exists_reset_of_drain_awake` at the ready scalar `ready` (`ready ≥ 1`), the gap
`G = X = Q.index`, the drain length `L_drain = healthyDrainLen = 2k + X`, `λ = 2Δ` and the service
horizon `b = horizon`; its bound is `B = ready + healthyResetCoeff·Δ`. The run premises come from
the shared HS premises at `Δ_F`, Catch from `catchRun_of_psync`, the drain from
`drainOutputs_of_service`. The gap is `final_query_gap`: `recurrence_gap` on the final pattern
(span `3c`) with the guarded duty → proposal adapter `duty_proposal_run`. (`reset_of_drain`,
HealCompose.lean, takes an unguarded duty → proposal premise, which the guarded (H2) does not
supply.)

The coefficient input is `accepted_heal_ge_final` (AcceptanceDefs.lean): the heal coefficient of
the final capability is at least `catchUp + 2·M_f`, `M_f = 24 L_drain + 8k + 52δ_t + 52X + 44`
(in node delays `Δ = Δe + 1 ≤ 2Δe`). With it,
`B + (8k + 20)Δ + 4(X + δ_t − 1)Δ − 1 = ready + M_f·Δ − 1 ≤ heal ≤ query`, which is (H3), and
`B + (12c − 2)Δ ≤ heal ≤ horizon` (`final_heal_horizon_fit`, for every `c` with `3c ≤ δ_t`),
which pays the gap's horizon. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The final heal margin covers a window of span `3c`** (symbolic in `c`). With the reset bound
`B = ready + (24 L_drain + 48δ_t + 48X + 28)·Δ` and `M_f = 24 L_drain + 8k + 52δ_t + 52X + 44`
(`accepted_heal_ge_final`), the horizon step of a gap-`c` window, `B + (12c − 2)·Δ`, stays below
`ready + M_f·Δ − 1` for every `c` with `3c ≤ δ_t`: the slack `M_f − (B − ready)/Δ − 12c + 2 =
8k + 4δ_t + 4X + 18 − 12c ≥ 8k + 4X + 18` is positive. So `accepted_heal` needs no change for a
gap `c` with `3c ≤ δ_t`. -/
theorem final_heal_horizon_fit {D Ld k δt X c : Time} (hD : 0 < D) (hk : 0 ≤ k) (hX : 0 ≤ X)
    (h3c : 3 * c ≤ δt) :
    (24 * Ld + 48 * δt + 48 * X + 28 + (12 * c - 2)) * D + 1 ≤
      (24 * Ld + 8 * k + 52 * δt + 52 * X + 44) * D := by
  have h1 : 0 ≤ (4 * δt - 12 * c) * D := mul_nonneg (by linarith) hD.le
  have h2 : 0 ≤ k * D := mul_nonneg hk hD.le
  have h3 : 0 ≤ X * D := mul_nonneg hX hD.le
  have key : (24 * Ld + 8 * k + 52 * δt + 52 * X + 44) * D -
      ((24 * Ld + 48 * δt + 48 * X + 28 + (12 * c - 2)) * D + 1) =
      8 * (k * D) + (4 * δt - 12 * c) * D + 4 * (X * D) + 18 * D - 1 := by ring
  have hD1 : (1 : Time) ≤ D := by change (0 : ℤ) < D at hD; change (1 : ℤ) ≤ D; omega
  linarith

/-- **The honest-proposer gap of a final query** (premise `hgp` of the rise at `G = X`): for the
final pattern `[0, c, 2c, 3c]` (`hpat`, span `3c`), with `max ready 0 + 4Δ ≤ t_{s₀}` and
`t_{N + 3c} ≤ horizon`, every slot window `[x₀, x₀ + X)` inside `[s₀, N]` has an actual honest
designated proposal. -/
theorem final_query_gap (Q : FinalQuery S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (finalGrid S A V Q) ⟨finalWindow A, Q.index⟩
      ((Sys (family S) V).cDur (K S A) Q.run) ((Sys (family S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using Q.progress
  have hL : (finalGrid S A V Q).slotLen = 4 * Q.params.Δ := by
    have h1 := finalGrid_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith
  have hspan : (finalGrid S A V Q).slotTime N +
      (((⟨finalWindow A, Q.index⟩ : Recurrence).pattern.span : Nat) : Time) *
        (finalGrid S A V Q).slotLen = Q.params.ts (N + 3 * c : Nat) := by
    rw [← finalGrid_slotTime S A V Q, (finalGrid S A V Q).slotTime_add]
    simp [finalWindow_span_of_offsets S A hpat]
  have hgap := recurrence_gap hrec (by rw [hpat]; simp) (s₀ := s₀) (N := N)
    (by rw [hL, finalGrid_slotTime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN)
  have hΔ := Q.params.toParams.hΔ
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap x₀ hx₀ hxN
  have hxr : x < x₀ + (Q.index : Nat) := hxr
  have hxN : x₀ + (Q.index : Nat) ≤ N + 1 := hxN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := by omega
      subst hs0
      have := le_max_right ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0
      simp only [SA.SAParams.ts] at hs
      push_cast at hs
      linarith
    · exact h
  have hxts : Q.params.ts x ≤ Q.params.ts (N + 3 * c : Nat) :=
    (SA.ts_le_iff Q.params).2 (by exact_mod_cast (show x ≤ N + 3 * c by omega))
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := duty_proposal_run S A V Q.run Q.hn Q.valid
    Q.noCollision hx0 (hxts.trans hN) hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`.** From the shared HS premises `hs` at `ΔF` (whose `timeoutDelay` is `6Δ + ΔF ≤ 4Δ·δ_t`),
the final pattern `[0, c, 2c, 3c]` (`hpat`) with `2 ≤ c` and `3c ≤ δ_t`: a reset `a` with its
premises through the horizon at GST `Q.gst` and `ΔR = ΔF`, and the placement `(P)` with
`u_min = finalSeedMin Q a`. The horizon of the gap uses `final_heal_horizon_fit`. -/
theorem final_reset_premises_of_shared (Q : FinalQuery S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen := by
  sorry

/-- **The reset premises and the placement of a final query** (the leaf `final_reset_premises`,
Accepted.lean): a reset `a` with its premises through the horizon at GST `Q.gst`, and the
placement `(P)` with `u_min = finalSeedMin Q a`. `final_reset_premises_of_shared` at the gap
`c = cF r` of `finalWindow` and the protocol row delay `ΔF := rowDelay`
(`FinalQuery.hsSharedUpTo`). -/
theorem final_reset_premises_of_query (Q : FinalQuery S A V) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen :=
  final_reset_premises_of_shared S A V Q A.two_le_cF A.timeout (finalWindow_offsets A)
    Q.hsSharedUpTo

end Consensus.Goldilocks.Refinement

end
