module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture
import all tests.POP6bMixedFacts
import all tests.POP6bMixedControl

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bNegative
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db POP6bMixed

private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (hj : run.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    reads.encode a ∉ V2.D.Run.emitsAt env run j := by
  intro ha
  rw [emissions_premises_sat j 7 t hj] at ha
  unfold output at ha
  by_cases owner : (if protocol.signLabel t = 6 then 9 else 7) = 7
  · rw [ite_eq_left owner] at ha
    obtain ⟨p, _, he⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp ha)
    have hl := congrArg (fun o : protocol.Object => match o.auth with
      | .seat l _ => some l | .none => none) he
    change some (protocol.signLabel t) = some 6 at hl
    have eq := Option.some.inj hl
    rw [eq] at owner
    norm_num at owner
  · rw [ite_eq_right owner] at ha
    cases ha

#print axioms nonholder_no_encoded

private theorem old_coverage_rejected : ¬ OpeningCovered core reads env run obs.height
    v5T wire.heightPair 3 (v5erase (chain 6)) := by
  intro hc
  obtain ⟨K, nd, j, r, a, _, _, _, _, _, row, _⟩ := hc 7 (by decide)
  exact nonholder_no_encoded j _ row.2.1 a row.2.2

#print axioms old_coverage_rejected

-- All common-supplier antecedents are inhabited by active_premises_sat.
-- Its sole failed output is the legacy row requirement at honest nonholder 7.
private theorem old_owner_common_rejected : ¬ (∀ u m J c q Q Qfg r,
    (12 : Time) ≤ u → HonestProposal env run iface q Q → v5erase Qfg = Q →
    FrontierProposalService core env run v5T q Q →
    FrontierSeedQualification v5T 1 env.t_GST u q → u ≤ v5T.proposal q →
    q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' * v5T.roundSlots → r ≤ r') →
    PhaseInterval core env run obs u (v5T.action r) m J c →
    OpeningCovered core reads env run obs.height v5T wire.heightPair r Q ∧
    ((obs.height Qfg).h = m - 1 → OpeningEntry core env run obs.height v5T r (m - 1) ∨
      ∃ x K, x ∈ run.honest ∧ actionSourceFG core env run v5T x r = some (some K) ∧
        (obs.height K).h = m)) := by
  intro common
  obtain ⟨_, _, _, _, prop, seed, phase, svc, _, _, _, _, _, _, _⟩ := active_premises_sat
  have h := common 17 2 none false 6 (v5erase (chain 6)) (chain 6) 3 (by decide)
    prop rfl svc seed (by decide) (by decide) (fun r hr => by
      change 6 ≤ r * 2 at hr
      simp only [Slot] at *
      omega) phase
  exact old_coverage_rejected h.1

#print axioms old_owner_common_rejected

end AvailableChain.FGCompose.Tests.POP6bNegative
end
