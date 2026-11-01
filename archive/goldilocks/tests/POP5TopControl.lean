module
import all AvailableChainFGCompose.Tests.PopulationSearchPhase
import all AvailableChainFGCompose.Proofs.Population.FrontierSearchTop

-- Standalone test module: imports private declarations to exercise the actual helper.
-- Compiled explicitly by the POP-5 acceptance manifest, outside library targets.
noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchPhase
open AvailableChain.SimplexFG AvailableChain.KitFG
open Fixture

private theorem mixed_top_low :
    ∃ t, (0 : Time) ≤ t ∧ t ≤ 46 ∧
      StrongServedFG (core true) reads env run (obs true) d5cTiming iface wire.heightPair
        0 1 2 t ∧ 26 ≤ t ∧ V2.D.proposerOf run iface 2 = 7 ∧
      HonestRowAt reads env run d5cTiming 13 9 0 firstRow := by
  obtain ⟨cert, obsLaws, inv, _, _, _, _, _, _, phase⟩ := geometry_premises_sat true
  obtain ⟨gap, slotProposal, read, sourceParent, signer, rowsReceipt⟩ :=
    transport_premises_sat true
  obtain ⟨order, coverage, hfold⟩ := progress_premises_sat true
  obtain ⟨floor, copy, allowance, _, _⟩ := repair_premises_sat true
  obtain ⟨service, common⟩ := branch_premises_sat true
  obtain ⟨_, sourceSlot, ancestorSlot, entryAgreement, _, _⟩ := source_premises_sat true
  have age : ∀ q Q Qfg, HonestProposal env run iface q Q → c5erase Qfg = Q →
      (0 : Time) ≤ d5cTiming.proposal q → d5cTiming.gate q ≤ 46 → (c5H Qfg).h = 2 - 1 →
      d5cTiming.proposal (c5H Qfg).T_h.slot ≤ (6 : Time) - 6 * d5cTiming.delta := by
    intro q Q Qfg hp he _ _ hl
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB] at hl ⊢
    rcases hq with rfl | rfl | rfl
    · decide +kernel
    · exact absurd hl (by decide +kernel)
    · exact absurd hl (by decide +kernel)
  obtain ⟨t, ht0, ht46, hs⟩ := p0d5c_top_phase_holder
    (R := core true) (S := reads) (O := obs true) (T := d5cTiming)
    (E := env) (rho := run) (I := iface) (D := wire) (Ef := c5E)
    (decodeProposal := decodeProposal) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
    (blockWireRows := fun _ => [firstRow, nextRow]) (parentFG := parentFG)
    (parentHeight := parentHeight) (validFor := validFor) (fold := fold) (Jst := 0)
    (leaseSlots := 1) (obs := obsLaws) (cert := cert) (inv := inv)
    (hT := d5cTimingLaws) (hk := le_rfl) (schedule := execution_premises_sat.1)
    (faultWeight := execution_premises_sat.2.2.1) (G := 20) (ΔF := 1)
    (ρbar := 14) (u := 0) (Dl := 46) (w := 6) (deltaF := le_rfl) (hdelta := rfl)
    (gap := gap) (hJst := le_rfl) (hG := by decide) (slotProposal := slotProposal)
    (read := read) (order := order) (signer := signer) (sourceParent := sourceParent)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := rowsReceipt)
    (progressCoverage := coverage) (hfold := hfold)
    (honestQuorum := ⟨{0}, fun _ _ => by change (9 : Nat) ∈ {7, 9}; decide, by decide⟩)
    (entryAgreement := entryAgreement) (sourceSlot := sourceSlot) (ancestorSlot := ancestorSlot)
    (eraseInj := c5erase_inj) (eraseReflect := m9erase_reflect) (floor := floor)
    (gateCopy := copy) (service := service) (common := common)
    (J := .genesis) (m := 2) (hready := le_rfl) (hp := phase)
    (allowance := allowance) (hrepairBudget := by decide) (hopeningBudget := by decide)
    (hentryBudget := by decide) (hentryAge := age)
  refine ⟨t, ht0, ht46, hs, ?_, by decide, execution_premises_sat.2.2.2.1⟩
  obtain ⟨u, J, c, q, Q, Qfg, _, hp, he, hh, _, _, _, _, hg, _⟩ := hs
  obtain ⟨hq, hQ⟩ := proposal_unique hp
  have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
  rw [hB] at hh
  change (c5H (chainAt q)).h = 2 at hh
  rcases hq with rfl | rfl | rfl
  · exact absurd hh (by decide +kernel)
  · exact hg
  · exact (by decide : (26 : Time) ≤ d5cTiming.gate 7).trans hg

#print axioms mixed_top_low

#print axioms p0d5c_top_phase_holder

namespace High

private theorem high_nonholder_source_progress :
    (¬ OpeningEntry (core true) env run c5H d5cTiming 1 1) ∧
    (∀ j t a, run.events[j]? = some (.tick 7 t) →
      reads.encode a ∉ V2.D.Run.emitsAt env run j) ∧
    ∃ t, (0 : Time) ≤ t ∧ t ≤ 46 ∧
      StrongServedFG (core true) reads env run (obs true) d5cTiming iface wire.heightPair
        0 1 2 t ∧ 26 ≤ t ∧ V2.D.proposerOf run iface 2 = 7 ∧
      HonestRowAt reads env run d5cTiming 13 9 0 firstRow := by
  obtain ⟨_, _, _, _, _, _, _, _, hnotLow, _, _, _, hsilence⟩ :=
    high_source_premises_sat
  refine ⟨hnotLow, hsilence, ?_⟩
  obtain ⟨cert, obsLaws, inv, _, _, _, _, _, _, phase⟩ := geometry_premises_sat true
  obtain ⟨gap, slotProposal, read, sourceParent, signer, rowsReceipt⟩ :=
    transport_premises_sat true
  obtain ⟨order, coverage, hfold⟩ := progress_premises_sat true
  obtain ⟨floor, copy, allowance, _, _⟩ := repair_premises_sat true
  obtain ⟨service, common⟩ := branch_premises_sat true
  obtain ⟨_, sourceSlot, ancestorSlot, entryAgreement, _, _⟩ := source_premises_sat true
  have age : ∀ q Q Qfg, HonestProposal env run iface q Q → c5erase Qfg = Q →
      (0 : Time) ≤ d5cTiming.proposal q → d5cTiming.gate q ≤ 46 → (c5H Qfg).h = 2 - 1 →
      d5cTiming.proposal (c5H Qfg).T_h.slot ≤ (6 : Time) - 6 * d5cTiming.delta := by
    intro q Q Qfg hp he _ _ hl
    obtain ⟨hq, hQ⟩ := proposal_unique hp
    have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
    rw [hB] at hl ⊢
    rcases hq with rfl | rfl | rfl
    · decide +kernel
    · exact absurd hl (by decide +kernel)
    · exact absurd hl (by decide +kernel)
  obtain ⟨t, ht0, ht46, hs⟩ := p0d5c_top_phase_holder
    (R := core true) (S := reads) (O := obs true) (T := d5cTiming)
    (E := env) (rho := run) (I := iface) (D := wire) (Ef := c5E)
    (decodeProposal := decodeProposal) (bodyErase := c5erase) (bodyRows := FGBlock.rows)
    (blockWireRows := fun _ => [firstRow, nextRow]) (parentFG := parentFG)
    (parentHeight := parentHeight) (validFor := validFor) (fold := fold) (Jst := 0)
    (leaseSlots := 1) (obs := obsLaws) (cert := cert) (inv := inv)
    (hT := d5cTimingLaws) (hk := le_rfl) (schedule := execution_premises_sat.1)
    (faultWeight := execution_premises_sat.2.2.1) (G := 20) (ΔF := 1)
    (ρbar := 14) (u := 0) (Dl := 46) (w := 6) (deltaF := le_rfl) (hdelta := rfl)
    (gap := gap) (hJst := le_rfl) (hG := by decide) (slotProposal := slotProposal)
    (read := read) (order := order) (signer := signer) (sourceParent := sourceParent)
    (deltaT := 4) (hδ := rfl) (hbound := ⟨by decide⟩) (rowsReceipt := rowsReceipt)
    (progressCoverage := coverage) (hfold := hfold)
    (honestQuorum := ⟨{0}, fun _ _ => by change (9 : Nat) ∈ {7, 9}; decide, by decide⟩)
    (entryAgreement := entryAgreement) (sourceSlot := sourceSlot) (ancestorSlot := ancestorSlot)
    (eraseInj := c5erase_inj) (eraseReflect := m9erase_reflect) (floor := floor)
    (gateCopy := copy) (service := service) (common := common)
    (J := .genesis) (m := 2) (hready := le_rfl) (hp := phase)
    (allowance := allowance) (hrepairBudget := by decide) (hopeningBudget := by decide)
    (hentryBudget := by decide) (hentryAge := age)
  refine ⟨t, ht0, ht46, hs, ?_, by decide, execution_premises_sat.2.2.2.1⟩
  obtain ⟨u, J, c, q, Q, Qfg, _, hp, he, hh, _, _, _, _, hg, _⟩ := hs
  obtain ⟨hq, hQ⟩ := proposal_unique hp
  have hB : Qfg = chainAt q := c5erase_inj (he.trans hQ)
  rw [hB] at hh
  change (c5H (chainAt q)).h = 2 at hh
  rcases hq with rfl | rfl | rfl
  · exact absurd hh (by decide +kernel)
  · exact hg
  · exact (by decide : (26 : Time) ≤ d5cTiming.gate 7).trans hg


#print axioms high_nonholder_source_progress

end High

end AvailableChain.FGCompose.Tests.PopulationSearchPhase
