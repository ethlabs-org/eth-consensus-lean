module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJointStep2 -- shake: keep (D5 tests)

set_option linter.privateModule false

public section

/-! Blueprint 21 H.17:2946–3040; plan RE-BIND T; DC: SAME steps for every cut. -/

namespace AvailableChain.FGSA.Run.Tests.HealingPostResetJointStep2
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21 H.17:2946–3040; plan RE-BIND T/D1; DC: SAME bounded projection. -/
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) {i : Nat} {v : Slot}
    (hcone : PostResetRetainedConeP p c E rho w i)
    (hcut : timeIdx rho (SA.voteTime p.toParams v) ≤ i) :
    PostResetConeAt p c E rho w v :=
  postResetConeAt_of_cut p c E rho w hcone hcut

variable [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec hreset cap rowCovered

/-- Blueprint 21 H.17:2946–3040; plan RE-BIND T/D5 O1; DC: SAME every-cut producer. -/
example (mono : RMonoAll p c E rho) (xing : RXing p c E rho) (origin : RQCOrigin p c E rho) :
    ∀ i, PostResetOpeningDomainStep₂ p c E rho w i :=
  fun i => healing_postReset_openingDomainStep₂ E rho hrec w hreset cap rowCovered
    mono xing origin i

/-- Blueprint 21 H.17:2946–3040; plan RE-BIND T/D5 O2; DC: SAME every-cut producer. -/
example (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C) :
    ∀ i, PostResetServiceStep₂ p c E rho w i :=
  fun i => healing_postReset_serviceStep₂ E rho hrec w hreset cap rowCovered mono writes i

end AvailableChain.FGSA.Run.Tests.HealingPostResetJointStep2
end
