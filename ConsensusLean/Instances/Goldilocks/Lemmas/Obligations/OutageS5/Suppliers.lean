module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageReaderGate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Arming
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageMajority
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageService
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Step
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks outage: the query-level suppliers of the reader bridge

At the lock module's premise
package `outageLockPremises_of_arming` of an armed ready source:

* `outage_s5_step_query`: the lock module's step `OutageS5Step`;
* `outage_restored_votes`: the extending majority (`ExtendingMajority` at the origin) at every
  restored label with an honest call past its vote time;
* `outage_reader_head`, `outage_reader_early`, `outage_reader_late`: the bridge's `hhead`,
  `hearly` and `hlate`.

The step and the extending majority come from `Compose.outage_s5_step` and
`Compose.restored_majority` (`Obligations/OutageS5/Step.lean`), the early record from
`Compose.record_above_of_update_r` (`Obligations/OutageS5/Record.lean`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

section Suppliers

variable (Q : OutageQuery S A V)
  (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
  {v : V} (hv : Q.run.2.point.Ready Q.duration v Q.T) (hTh : Q.T ≤ Q.run.2.horizon)
  (hsh : Q.start ≤ Q.run.2.horizon) (ar : OutageArming S A V Q v)

/-- The hypothesis `hS` of `Compose.outage_s5_step` at the premise package: receiver service from
`D.b₁ = Q.stop`. -/
private theorem premises_service :
    ∀ y ∈ honestKeys S Q.run.2, Compose.ReceiverServiceAfter (honestKeys S Q.run.2)
      (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (outageLockPremises_of_arming Q service hv hTh hsh ar).b₁ y Q.trace.projAC := by
  rw [outageLockPremises_of_arming_b₁]
  exact outage_receiver_service S A V Q

/-- **The step `OutageS5Step` in query form** (the lock module's `hS5`), from
`Compose.outage_s5_step (D) (hS) : OutageS5StepAt D`. -/
theorem outage_s5_step_query : OutageS5Step Q service hv hTh hsh ar := by
  have h := Compose.outageS5StepAt_iff.1
    (Compose.outage_s5_step (outageLockPremises_of_arming Q service hv hTh hsh ar)
      (premises_service Q service hv hTh hsh ar))
  rw [outageLockPremises_of_arming_P, outageLockPremises_of_arming_j₀] at h
  exact h

/-- **The extending majority at every restored label** with an honest call past its vote time, from
`Compose.restored_majority (D) (hS) (hinv) q (hq : D.r ≤ q) hcall`. -/
theorem outage_restored_votes (hS5 : OutageS5Step Q service hv hTh hsh ar)
    (q : Nat) (hq : Q.stop ≤ Q.params.ts q + Q.params.Δ)
    (hcall : ∃ x ∈ honestKeys S Q.run.2, ∃ i, Q.trace.IsCall x i ∧
      Q.params.ts q + Q.params.Δ ≤ Q.trace.time i) :
    Compose.ExtendingMajority Q.trace (honestKeys S Q.run.2) ar.origin q := by
  have h := Compose.restored_majority (outageLockPremises_of_arming Q service hv hTh hsh ar)
    (premises_service Q service hv hTh hsh ar)
    (outage_locks Q service hv hTh hsh ar hS5) q
    (by rw [outageLockPremises_of_arming_r]; exact (restoredLabel_spec Q).2 q hq) hcall
  rwa [outageLockPremises_of_arming_P] at h

/-- The reader's latest gate gives an honest call past the vote time of its label and of the
next one. -/
private theorem gate_call {t : Time} {w : V} (hw : Q.run.2.point.Ready Q.duration w t)
    (G : OutageReaderGate S A V Q w t) {q : Nat} (hq : q ≤ G.slot + 1) :
    ∃ x ∈ honestKeys S Q.run.2, ∃ i, Q.trace.IsCall x i ∧
      Q.params.ts q + Q.params.Δ ≤ Q.trace.time i := by
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hGt : Q.trace.time G.cut = Q.params.ts G.slot + 6 * Q.params.Δ := G.update.2.2.1
  have hts : Q.params.ts (G.slot + 1 : Nat) = Q.params.ts G.slot + 4 * Q.params.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hle := Compose.ts_le_ts (sp := Q.params) hq
  refine ⟨_, honest_ownKey (S := S)
    ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hw.1),
    G.cut, ⟨_, Compose.projAC_callAt.1 G.update.1⟩, ?_⟩
  rw [hGt]
  linarith

/-- **The head input** (`hhead`): `ExtendingMajority` at the read label. -/
theorem outage_reader_head (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {t : Time} {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    ∀ G : OutageReaderGate S A V Q w t,
      Compose.ExtendingMajority Q.trace (honestKeys S Q.run.2) ar.origin (G.slot + 1) ∨
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) ar.origin
          (SA.acHead Q.params
            (Q.trace.state (Q.run.2.ownKey w)
              (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).ac
            (Node.frame (Q.trace.state (Q.run.2.ownKey w)
              (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)))) t) := by
  intro G
  left
  refine outage_restored_votes Q service hv hTh hsh ar hS5 (G.slot + 1) ?_
    (gate_call Q hw G le_rfl)
  exact G.restored.trans (by linarith [Compose.ts_le_ts (sp := Q.params) (Nat.le_succ G.slot)])

/-- **The early record** (`hearly`), from
`Compose.record_above_of_update_r (D) (hS) (hinv) hw hu`. -/
theorem outage_reader_early (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {t : Time} {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    ∀ c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c Q.restoredLabel ℓ →
      ∀ c', c < c' → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) ar.origin
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey w) c'))
          (Q.trace.state (Q.run.2.ownKey w) c').ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey w) c').fg.F) := by
  intro c ℓ hu c' hcc'
  have h := Compose.record_above_of_update_r (outageLockPremises_of_arming Q service hv hTh hsh ar)
    (premises_service Q service hv hTh hsh ar) (outage_locks Q service hv hTh hsh ar hS5)
    (honest_ownKey (S := S) ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hw.1))
    (by rw [outageLockPremises_of_arming_r]; exact hu) c' hcc'
  rw [outageLockPremises_of_arming_P] at h
  exact h

/-- **The late record** (`hlate`): a reader without an update of the first restored label has its
latest gate at a later label, where `ExtendingMajority` holds. -/
theorem outage_reader_late (hS5 : OutageS5Step Q service hv hTh hsh ar)
    {t : Time} (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon) {w : V} (hw : Q.run.2.point.Ready Q.duration w t) :
    (¬ ∃ c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c Q.restoredLabel ℓ) →
      (∃ s' c ℓ, SA.UpdateAt Q.trace.projAC (Q.run.2.ownKey w) c s' ℓ ∧ Q.restoredLabel < s' ∧
          Q.trace.time c ≤ t ∧
          Compose.ExtendingMajority Q.trace (honestKeys S Q.run.2) ar.origin s') ∨
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) ar.origin
          (Q.trace.state (Q.run.2.ownKey w)
            (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t))).fg.F := by
  intro hE
  obtain ⟨G⟩ := outage_reader_gate S A V Q ht hth hw
  have hGt : Q.trace.time G.cut = Q.params.ts G.slot + 6 * Q.params.Δ := G.update.2.2.1
  have hrs : Q.restoredLabel < G.slot := by
    refine lt_of_le_of_ne ((restoredLabel_spec Q).2 G.slot G.restored) fun h => hE ?_
    exact ⟨G.cut, G.label, h ▸ G.update⟩
  exact Or.inl ⟨G.slot, G.cut, G.label, G.update, hrs, hGt ▸ G.gate_le,
    outage_restored_votes Q service hv hTh hsh ar hS5 G.slot G.restored
      (gate_call Q hw G (Nat.le_succ G.slot))⟩

end Suppliers

end Consensus.Goldilocks.Obligations

end
