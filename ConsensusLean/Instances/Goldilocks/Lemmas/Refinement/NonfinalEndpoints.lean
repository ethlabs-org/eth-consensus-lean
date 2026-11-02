module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyConfirmedEndpoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyResetEnvelope

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Healthy selected-proposal service. This is a joint existential, not
coverage of every ready proposal before the deadline. Exact cDur readiness,
freshness and the actual proposal/acceptance event are retained. Finite Healthy
preparation and frozen service must produce this witness; the endpoint acquires
no extra invariant or whole-run progress premise. -/
theorem healthy_confirmed_supply (Q : ConfirmedQuery S A V)
    (hh : (Sys (family S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index ((Sys (family S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (family S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query) :
    ∃ P : ConfirmedProposal S A V Q,
      ∀ y j, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) :=
  healthy_confirmed_supply_of_initializer S A V Q hh hp ht (healthy_preparation_initialize S A V)

/-- The common projection is proved from actual production and selected coverage.
Both regimes retain their own cap/index budget and the engine-scaled deadline. -/
theorem confirmed_payload_projection (Q : ConfirmedQuery S A V)
    (h0 : 0 ≤ Q.query) (P : ConfirmedProposal S A V Q)
    (coverage : ∀ y j,
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
        (Regimes.readAfter Q.trace y j Q.deadline)) :
    ∃ τ k h, Q.query < τ ∧ Q.run.2.point.Ready Q.duration (Q.run.2.key k) τ ∧
      HonestProposal Q.run.2 τ k h ∧ InBy Q.run.2 Q.duration .confirmed h Q.deadline := by
  have hτ := h0.trans P.fresh.le
  have hprop : Regimes.ReadyProposalAt Q.trace (honestKeys S Q.run.2) Q.duration
      (Q.trace.time P.cut) P.block := ⟨_, P.cut, P.ready, P.proposal, rfl⟩
  obtain ⟨k, hk, hr⟩ := ready_proposal S Q.run.2 Q.hn Q.valid hτ
    (P.bounded.trans Q.bounded) hprop
  refine ⟨_, k, headerOf Q.params P.block, P.fresh, hk, hr, ?_⟩
  exact confirmed_inBy S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
    (mul_nonneg (Int.natCast_nonneg _) Q.run.1.Δ_pos.le)
    hτ P.bounded Q.bounded hprop coverage

/-- Safety has no progress/query/ready-reader existence premise. Its service
supplier must therefore cover the whole finite execution independently of the
liveness query supplier. The coefficient inequality is directional. -/
structure SleepySafetyQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  sleepy : (Sys (family S) V).Sleepy (K S A) run

/-- Finite safety service, population and joint duration production.
No recurrence is needed or assumed. Arbitrary-cut output transport remains the
existing sleepy_safe_engine leaf, not an endCut-only assertion. -/
theorem sleepy_safety_inputs (Q : SleepySafetyQuery S A V) :
    Regimes.catchUp (S.params (Model.pubOf Q.run.1) Q.hn) + 1 ≤
      (Sys (family S) V).cDur (K S A) Q.run ∧
    Compose.SleepyServiceBefore (simTrace S Q.run.2 Q.hn) (honestKeys S Q.run.2)
      (S.params (Model.pubOf Q.run.1) Q.hn).Δ Q.run.2.horizon ∧
    (∀ s : Nat, ∀ d ∈ ({0, (S.params (Model.pubOf Q.run.1) Q.hn).Δ,
      2 * (S.params (Model.pubOf Q.run.1) Q.hn).Δ} : Set Time),
      (S.params (Model.pubOf Q.run.1) Q.hn).ts s + d ≤ Q.run.2.horizon →
      (simTrace S Q.run.2 Q.hn).FaultBound (honestKeys S Q.run.2)
        ((S.params (Model.pubOf Q.run.1) Q.hn).ts s + d)) := by
  have hduration : Regimes.catchUp (S.params (Model.pubOf Q.run.1) Q.hn) + 1 ≤
      (Sys (family S) V).cDur (K S A) Q.run := by
    have hc : (37 : Time) ≤ (accepted_catchUp S A : Nat) := by
      exact_mod_cast accepted_catchUp_ge_sleepy S A
    have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
    simp only [System.cDur, Params.standard, accepted_coefficients_catchUp]
    change 18 * (Q.run.1.Δ + 1) + 1 ≤ (accepted_catchUp S A : Nat) * Q.run.1.Δ
    nlinarith
  refine ⟨hduration, ?_, ?_⟩
  · exact sleepyServiceBefore_of_syncUntil S Q.run.2 Q.hn Q.valid
      (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) le_rfl
      (sleepy_raw_syncUntil S A V Q.run Q.valid Q.sleepy Q.run.2.horizon)
  · apply sleepy_faultBound S Q.run.2 Q.hn Q.valid le_rfl
    intro t ht hth
    exact half_ready_of_duration V Q.run.2.point (by linarith) (Q.sleepy.2 t ht hth)

end Consensus.Goldilocks.Refinement
end
