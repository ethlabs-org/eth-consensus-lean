module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthySuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyConfirmedEndpoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyResetEnvelope
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Confirmed-chain endpoint suppliers

`healthy_confirmed_supply` joins finite healthy preparation to selected-proposal coverage;
`confirmed_payload_projection` converts that coverage to the engine payload obligation.
`SleepySafetyQuery` and `sleepy_safety_inputs` supply the separate sleepy safety inputs.
Available and stable reads share the confirmed-chain projection, not an extra run premise. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Healthy selected-proposal service. This is a joint existential, not
coverage of every ready proposal before the deadline. Exact cDur readiness,
freshness and the actual proposal/acceptance event are retained. Finite Healthy
preparation and frozen service must produce this witness; the endpoint acquires
no extra invariant or whole-run progress premise. -/
theorem healthy_confirmed_supply (Q : ConfirmedQuery S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query) :
    ∃ P : ConfirmedProposal S A V Q,
      ∀ y j, Regimes.ReadyAt Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) :=
  healthy_confirmed_supply_of_initializer S A V Q hh hp ht (healthy_preparation_initialize S A V)

/-- The common projection is proved from actual production and selected coverage.
Both regimes retain their own cap/index budget and the engine-scaled deadline. -/
theorem confirmed_payload_projection (Q : ConfirmedQuery S A V)
    (h0 : 0 ≤ Q.query) (P : ConfirmedProposal S A V Q)
    (coverage : ∀ y j,
      Regimes.ReadyAt Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys ⟨S, stock⟩ Q.run.2)) P.block
        (Regimes.readAfter Q.trace y j Q.deadline)) :
    ∃ τ k h, Q.query < τ ∧ Q.run.2.point.Ready Q.duration (Q.run.2.key k) τ ∧
      HonestProposal Q.run.2 τ k h ∧ InBy Q.run.2 Q.duration .confirmed h Q.deadline := by
  have hτ := h0.trans P.fresh.le
  have hprop : Regimes.ReadyProposalAt Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) Q.duration
      (Q.trace.time P.cut) P.block := ⟨_, P.cut, P.ready, P.proposal, rfl⟩
  obtain ⟨k, hk, hr⟩ := ready_proposal S Q.run.2 Q.hn Q.constant Q.valid hτ
    (P.bounded.trans Q.bounded) hprop
  refine ⟨_, k, headerOf Q.params P.block, P.fresh, hk, hr, ?_⟩
  exact confirmed_inBy S Q.run.2 Q.hn Q.constant Q.valid
    (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision)
    (mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le)
    hτ P.bounded Q.bounded hprop coverage

/-- Safety has no progress/query/ready-reader existence premise. Its service
supplier must therefore cover the whole finite execution independently of the
liveness query supplier. The coefficient inequality is directional. -/
structure SleepySafetyQuery where
  run : (Sys (goldilocks S) V).Run
  constant : run.2.point.ConstantFaults
  hn : 1 ≤ Fintype.card V
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  sleepy : (Sys (goldilocks S) V).Sleepy (K S A) run

/-- Finite safety service, population and joint duration production.
No recurrence is needed or assumed. Arbitrary-cut output transport remains the
existing sleepy_safe_engine leaf, not an endCut-only assertion. -/
theorem sleepy_safety_inputs (Q : SleepySafetyQuery S A V) :
    Regimes.catchUp (S.params (Model.pubOf Q.run.1) Q.hn) + 1 ≤
      (Sys (goldilocks S) V).cDur (K S A) Q.run ∧
    Compose.SleepyServiceBefore (simTrace ⟨S, stock⟩ Q.run.2 Q.hn) (honestKeys ⟨S, stock⟩ Q.run.2)
      (S.params (Model.pubOf Q.run.1) Q.hn).Δ Q.run.2.horizon ∧
    (∀ s : Nat, ∀ d ∈ ({0, (S.params (Model.pubOf Q.run.1) Q.hn).Δ,
      2 * (S.params (Model.pubOf Q.run.1) Q.hn).Δ} : Set Time),
      (S.params (Model.pubOf Q.run.1) Q.hn).ts s + d ≤ Q.run.2.horizon →
      (simTrace ⟨S, stock⟩ Q.run.2 Q.hn).FaultBound (honestKeys ⟨S, stock⟩ Q.run.2)
        ((S.params (Model.pubOf Q.run.1) Q.hn).ts s + d)) := by
  have hduration : Regimes.catchUp (S.params (Model.pubOf Q.run.1) Q.hn) + 1 ≤
      (Sys (goldilocks S) V).cDur (K S A) Q.run := by
    have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
      exact_mod_cast contract_catchUp_ge_sleepy S A
    have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
    simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
    change 18 * Q.run.1.ΔAC + 1 ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
    linarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : Time) ≤ Q.run.1.ΔAC)]
  refine ⟨hduration, ?_, ?_⟩
  · exact sleepyServiceBefore_of_syncUntil S Q.run.2 Q.hn Q.constant Q.valid
      (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision) le_rfl
      (sleepy_raw_syncUntil S A V Q.run Q.valid Q.sleepy Q.run.2.horizon)
  · apply sleepy_faultBound S Q.run.2 Q.hn Q.constant Q.valid
      (W := (Sys (goldilocks S) V).aheadDur (K S A) Q.run) le_rfl
    apply (Q.run.2.point.sleepyOn_iff Q.constant _ _ _ _ _).mpr
    intro t ht hth
    exact half_ready_of_duration V Q.run.2.point (by linarith)
      ((Q.run.2.point.sleepyOn_iff Q.constant _ _ _ _ _).mp Q.sleepy.2 t ht hth)

end Consensus.Goldilocks.Obligations
end
