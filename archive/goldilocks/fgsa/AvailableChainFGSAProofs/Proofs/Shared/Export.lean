module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry
public import AvailableChainFGSAProofs.Proofs.Shared.Release
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAClaims.Claims.Shared

public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.2, blueprint 02 §2.2 and 21 IF.6. Class (ii), frozen claim assembly.
DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405 `eligible_compatible`.
INTENTIONAL: optional F-anchored active-view results and label-local synchronization
(spec/fgsa-protocol.tex:2496–2513). Export boundary: SYN L50. -/
theorem fgsa_sameLabelClaim (p : Params) : SameLabelClaim p := by
  intro V _ _ In c E rho pt h
  exact fgsa_sameLabel_on p c E rho h.set.valid pt.s
    (fgsa_sameLabel_serviceScope E rho h.set.valid h.set.restartsAtWakes
      h.set.delta pt.s h.sync) h.set.idealization

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.3, bp.release.v1(a,c), blueprint 01 §5.
Class (iii), store wrapper. DC counterpart: none; INTENTIONAL SA lifecycle,
spec/fgsa-protocol.tex:2514–2515. Export boundary: SYN L50. -/
theorem fgsa_releaseStoreClaim (p : Params) : ReleaseStoreClaim p :=
  fgsa_release_store p

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.3, bp.release.v1(a–c), blueprint 02 §2 and 21 H.1.
Class (ii), v2 authenticity/CStar instance and store assembly.
DC counterpart: none; INTENTIONAL SA lifecycle, spec/fgsa-protocol.tex:2514–2515.
Export boundary: SYN L50. -/
theorem fgsa_releaseClaim (p : Params) : ReleaseClaim p := by
  intro V _ _ In c E rho pt h
  refine ⟨fgsa_releaseStoreClaim p, ?_⟩
  intro i x s B _ _ hheads
  exact ⟨fgsa_release_bound_restart (hroots := h.set.idealization) p c E rho h.set.valid
    h.set.cstar h.set.delta i x s B hheads, h.lt⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.5, ap.headReachesLo.v6 clauses 1–3; bp02 §7.
Class (iii), Claims wrapper through the L42 Export boundary.
DC: Goldfish/Walk.lean:197 `ghost_step_none`, :433 `ghost_reaches`.
INTENTIONAL: the FJ floor and duty-view witness give the height bound
(bp02 §7); the internal proof uses only store reachability. -/
theorem fgsa_headReachesLoClaim (p : Params) : HeadReachesLoClaim p := by
  delta HeadReachesLoClaim HeadReachesLoAt
  simpa only [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p),
    KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] using
    fgsa_headReachesLo p

end AvailableChain.FGSA.Run
end

#print axioms AvailableChain.FGSA.Run.fgsa_sameLabelClaim
#print axioms AvailableChain.FGSA.Run.fgsa_releaseStoreClaim
#print axioms AvailableChain.FGSA.Run.fgsa_releaseClaim
#print axioms AvailableChain.FGSA.Run.fgsa_headReachesLoClaim
