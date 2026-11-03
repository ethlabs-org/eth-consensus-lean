module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Goldilocks outage: the reader's latest gate (O4, E0–E4) and the source prefix

Workbench `notes/outage/outage_reader_bridge.md` (35ec2da), §2, §3 and §10.2. A reader ready at
`t` from the recovery point `b₁ + 18Δe` has its latest gate `s = slot(t − 6Δ)`: `b₁ ≤ t_s + Δ`,
the update of slot `s` at `d_s = t_s + 6Δ ≤ t < t_s + 10Δ` before the read cut, no restart after
`t_s` up to `t`, and the latest view at `t` of label `s + 1`. Only readiness, joining, the gate
tick and the read cut are used: no vote, frame walk or voter tree. `outage_reader_prefix` turns
ancestry of the two read tips into the prefix of the engine reads. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- E0–E4: the latest gate of a ready reader from the recovery point. -/
structure OutageReaderGate (Q : OutageQuery S A V) (w : V) (t : Time) where
  slot : Nat
  restored : Q.stop ≤ Q.params.ts slot + Q.params.Δ
  gate_le : Q.params.ts slot + 6 * Q.params.Δ ≤ t
  lt_next : t < Q.params.ts slot + 10 * Q.params.Δ
  cut : Nat
  label : ACLabel (SA.goldilocksSA Q.params (List (FG.Att Q.params.n)) (S.ro Q.params.n))
  update : SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) cut slot label
  cut_lt : cut < cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)
  restarts : ∀ k, Q.trace.projAC.RestartAt (Q.run.2.ownKey w) k → Q.trace.time k ≤ t →
    Q.trace.time k ≤ Q.params.ts slot
  read : Regimes.CutAfter Q.trace (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t
  view : (SA.latestView Q.params
      (Q.trace.state (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).ac
      (Node.frame (Q.trace.state (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)))) t).2 = ((slot + 1 : Nat) : Int)

/-- The query's catch-up duration covers the node catch-up `18Δ` (G1, local copy). -/
private theorem duration_ge (Q : OutageQuery S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  sorry

/-- The outage's end is not before `0`. -/
private theorem stop_nonneg (Q : OutageQuery S A V) : 0 ≤ Q.stop := by
  obtain ⟨⟨hT, hlag, h01, -⟩, -⟩ := Q.outage
  have : (0 : Time) ≤ ((K S A).params.lag : Time) * Q.run.1.Δ := by
    have := Q.run.1.Δ_pos; positivity
  change Q.T + _ * Q.run.1.Δ ≤ Q.start at hlag
  change Q.start ≤ Q.stop at h01
  linarith

theorem outage_reader_gate (Q : OutageQuery S A V) {t : Time}
    (ht : (Sys (family S) V).recoveryAt (K S A) Q.stop Q.run ≤ t) (hth : t ≤ Q.run.2.horizon)
    {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    Nonempty (OutageReaderGate S A V Q w t) := by
  sorry

/-- §2: ancestry of the two tips is the engine read prefix. -/
theorem outage_reader_prefix (Q : OutageQuery S A V) {v : V}
    (hv : Q.run.2.point.Ready Q.duration v Q.T) {t : Time} (hTt : Q.T ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t)
    (h : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.T)) Q.T)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey w)
        (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t)) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  have hT0 : 0 ≤ Q.T := Q.outage.1.1
  have hc : 0 ≤ Q.duration := le_trans (by
    change (0 : Time) ≤ 18 * Q.params.Δ
    have := Q.params.toParams.hΔ; positivity) (duration_ge S A V Q)
  obtain ⟨-, -, hvT⟩ := ready_read_cut S Q.run.2 Q.hn Q.valid hc hT0 (hTt.trans hth) hv
  obtain ⟨-, -, hwt⟩ := ready_read_cut S Q.run.2 Q.hn Q.valid hc (hT0.trans hTt) hth hw
  refine confirmed_prefix_of_anc (simTrace_simulates S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) hv.1 hw.1
    (Nat.findGreatest_le _) (Nat.findGreatest_le _) ?_
  rw [hvT, hwt]
  exact h

end Consensus.Goldilocks.Refinement

end
