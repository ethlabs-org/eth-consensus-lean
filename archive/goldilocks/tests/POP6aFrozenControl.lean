module
import all AvailableChainFGCompose.Tests.P0d5c
import AvailableChainFGCompose.Proofs.Population.FrontierSearchTail
import AvailableChainFGCompose.Proofs.Population.FrontierSearchBridges

-- Standalone all-holder specialization on the accepted exact row-tail event fold.
noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6aFrozen
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5c

private abbrev holderEquiv : Fin 1 ≃ Unit := Equiv.ofUnique _ _

private theorem frozen_premises_sat :
    FGCertificateLaws c5E r6O.height r6O.finality ∧
    (∀ i x, FGStoreInvariant r6O.height r6O.finality
      (r6R.core (r6rho.stateBefore c5env i x)).fg) ∧
    FGTimingLaws d5cTiming ∧ V2.D.ScheduleWellFormed c5env r6rho ∧
    FGRunOrderLaws c5env r6rho r6R ∧
    RCap r6R r6S c5env r6rho r6O d5cTiming
      (fun a => namedEntry (Row.height_pair a)) r6chain ∧
    PhaseInterval r6R c5env r6rho r6O 8 14 2 (some .genesis) false ∧
    HonestProposal c5env r6rho r6I 2 (c5erase c5x1) ∧
    (FGHonestSeats r6S r6rho).Nonempty ∧
    (∀ i, safetyHolder r6S r6rho i = holderEquiv i) ∧
    (∀ v, d5cTiming.gate 2 ≤ v → v ≤ r6rho.horizon →
      (∀ i x, timeIdx r6rho 8 ≤ i → i ≤ timeIdx r6rho v → x ∈ r6rho.honest →
        (r6R.core (r6rho.stateBefore c5env i x)).fg.h_max ≤ 2) →
      FrontierLocalServiceFG r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair
        2 (c5erase c5x1) c5x1 2 v) ∧
    14 + (FGCompose.P d5cTiming - 4 * d5cTiming.delta) ≤ r6rho.horizon := by
  have he : ∀ i, safetyHolder r6S r6rho i = holderEquiv i :=
    fun _ => Subsingleton.elim _ _
  refine ⟨r6cert, r6inv, d5cTimingLaws, r6schedule, r6mono, r6cap, r6phase, r6proposal,
    ⟨0, by decide⟩, he, ?_, by decide⟩
  intro v hv hh hcap
  exact (frontierLocalServiceFG_frozen_iff r6R r6S c5env r6rho r6O d5cTiming r6I
    Row.height_pair holderEquiv he 2 (c5erase c5x1) c5x1 2 v).2 (r6service v hv hh hcap)

#print axioms frozen_premises_sat

private theorem frozen_tail_bridge :
    FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2 18 ∧
    (∃ r j a, HeightRow r6S c5env r6rho d5cTiming
      (fun a => namedEntry (Row.height_pair a)) r 2 ∧
      HonestRowAt r6S c5env r6rho d5cTiming j () r a ∧
      j = 15 ∧ r = 1 ∧ a = r6row2 ∧ d5cTiming.action r = 14) := by
  obtain ⟨cert, inv, ht, schedule, mono, cap, phase, proposal, hne, _, service, hhor⟩ :=
    frozen_premises_sat
  have result := healing_frontierTail_row_holder r6R r6S c5env r6rho r6O d5cTiming r6I
    Row.height_pair r6chain c5E cert inv ht schedule hne mono cap phase proposal
    (le_rfl : d5cTiming.gate 2 ≤ (14 : Time)) service hhor
  refine ⟨result, ?_⟩
  obtain ⟨r, hr, _, _⟩ := result
  obtain ⟨j, y, a, e, hrow, hn⟩ := hr
  cases y
  rcases r6rows hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · change some (1, genesisRoot) = some (2, e) at hn
    cases hn
  · exact ⟨1, 15, r6row2, ⟨15, (), r6row2, e, hrow, hn⟩,
      hrow, rfl, rfl, rfl, rfl⟩

#print axioms frozen_tail_bridge

end AvailableChain.FGCompose.Tests.POP6aFrozen
end
