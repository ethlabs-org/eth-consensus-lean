module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyRecordGeometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock

/-! # Finite adoption of an operational confirmed proposal

The same-time suffix after an actual update preserves the selected proposal in
the confirmed read. Later deadline coverage consumes an explicit continuation;
it does not construct the independent healthy preparation or repair suppliers.
-/

public section
namespace Consensus.Goldilocks.Refinement

section FiniteSupply
variable {sp : SA.SAParams}
  {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {g ΔF a b : Time}

/-- An actual update's fresh lock and effective record cover every read after
all calls at the update time, even if finalization has passed the proposal. -/
theorem operational_update_read_after
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell)
    (hlock : ∃ e, (⟨P.root, u, true, e⟩ : SA.Lock) ∈
      (tr.projAC.post j).locks)
    {J : Nat} (hJ : Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ)) :
    Anc (tr.HonestBlocks H) P
      (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  sorry

/-- Every honest reader adopts the actual proposal at the end of its update time. -/
theorem operational_proposal_read_after
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    (hlocks : ∀ y ∈ H, ∀ j (ell : ACLabel (goldilocksNode sp ro)),
      SA.UpdateAt tr.projAC y j u ell →
      ∃ e, (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks) :
    ∀ y ∈ H, ∀ J,
      Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ) →
      Anc (tr.HonestBlocks H) P
        (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  intro y hy J hJ
  have hstart : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hg := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr le_rfl
    have hbound : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) =
        sp.ts (sp.slot (SA.gbar g)) + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hbound]
    linarith
  obtain ⟨j, ell, -, hup, -⟩ := hp.update_toFG_calls hy hstart hTb
  exact operational_update_read_after hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
    (hlocks y hy j ell hup) hJ

end FiniteSupply

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Initial finite adoption and an independent later-read continuation give
deadline coverage for the same actual confirmed proposal. -/
theorem healthy_confirmed_coverage_of_service
    (Q : ConfirmedQuery S A V) (P : ConfirmedProposal S A V Q)
    {a ΔF : Time} {u : Nat}
    (hp : Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2)
      Q.gst ΔF a Q.run.2.horizon)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2)
      Q.gst (2 * Q.params.Δ))
    (hdesignated : P.block.proposer = runProposer S Q.run.2 Q.hn u)
    (hPs : P.block.slot = u)
    (hR : Healing.drainTime Q.params a ≤ Q.params.ts u)
    (hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts u)
    (hmargin : Q.params.ts u + 6 * Q.params.Δ ≤ Q.deadline)
    (hlocks : ∀ y ∈ honestKeys S Q.run.2, ∀ j ell,
      SA.UpdateAt Q.trace.projAC y j u ell →
      ∃ e, (⟨P.block.root, u, true, e⟩ : SA.Lock) ∈ (Q.trace.projAC.post j).locks)
    (hcut : ∃ i, Regimes.CutAfter Q.trace i (Q.params.ts u + 6 * Q.params.Δ))
    (hcontinue : ∀ y i j,
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace i (Q.params.ts u + 6 * Q.params.Δ) →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        (Regimes.readAfter Q.trace y i (Q.params.ts u + 6 * Q.params.Δ))
        (Regimes.readAfter Q.trace y j Q.deadline)) :
    ∀ y j, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
        (Regimes.readAfter Q.trace y j Q.deadline) := by
  obtain ⟨i, hi⟩ := hcut
  intro y j hy hj
  exact (operational_proposal_read_after hp hc P.ready.1 hdesignated P.proposal hPs hR hgu
    (hmargin.trans Q.bounded) hlocks y hy.1 i hi).trans (hcontinue y i j hy hi hj)

end Consensus.Goldilocks.Refinement
