module
public import AvailableChainFGCompose.Statements.Population.FrontierSearch

public section
namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads Prot n Base Proposal Wire} {S : FGSafetyReads Prot n Wire}
variable {E : Generic.Env V} {rho : V2.D.Run V Prot}
variable {O : FGObservationReads R} {T : FGTiming} {I : V2.D.Interface Prot}
variable {pair : Wire → NamedHeightPair} {Jst : Time} {leaseSlots : Nat}

/-- Restrict the opening rows; the selected proposal and all receiver clauses stay fixed. -/
theorem frontierLocalService_to_holder_core {q : Slot} {Q : Block}
    {Qfg : FGBlock (Fin n)} {m : Nat} {v : Time}
    (h : FrontierLocalService R S E rho O T I pair q Q Qfg m v) :
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro r hr ht
  obtain ⟨hc, rest⟩ := h.2.2.2.2 r hr ht
  exact ⟨fun i hi => hc _ (Finset.mem_filter.mp hi).2, rest⟩

/-- The existing all-node service supplier restores the same saved holder seed. -/
theorem strongServed_of_holder_service_core
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalService R S E rho O T I pair q Q Qfg m v)
    {m : Nat} {t : Time} (h : StrongServedFG R S E rho O T I pair Jst leaseSlots m t) :
    StrongServed R S E rho O T I pair Jst leaseSlots m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hr, hQ, he, hh, hs, hseed, hu, hp, hg, ht, hc, _⟩ := h
  exact ⟨u, J, contested, q, Q, Qfg, hr, hQ, he, hh, hs, hseed, hu, hp, hg, ht, hc,
    service u t m J contested q Q Qfg hr hQ he hh hs hseed hu hp hg ht hc⟩

end AvailableChain.FGCompose
end
