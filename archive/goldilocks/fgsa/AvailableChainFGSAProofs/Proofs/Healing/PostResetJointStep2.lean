module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConeAt
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetService

public section

/-! Blueprint 21 H.17:2946–3040; plan RE-BIND D5; DC: SAME cone at the step cut.
The successor cone supplies each bounded HEAD label. The opening producer
uses the prior invariant and opening cut. Service uses only successor inputs. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section JointSteps
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3031–3040; plan RE-BIND D5 O1; ruling R3.
DC: SAME the opening-domain step, from the prior PostResetInv and opening cut.
Producer: healing_postReset_openingDomain_step_at; cone from the successor cut. -/
theorem healing_postReset_openingDomainStep₂
    (mono : RMonoAll p c E rho) (xing : RXing p c E rho) (origin : RQCOrigin p c E rho) (i : Nat) :
    PostResetOpeningDomainStep₂ p c E rho w i := by
  rw [PostResetOpeningDomainStep₂_def]
  rintro ⟨hinv, -, hod, -⟩ - - - - hcone
  exact healing_postReset_openingDomain_step_at E rho hrec mono w hreset cap rowCovered
    xing origin i (fun v hv => postResetConeAt_of_cut p c E rho w hcone
      (hv.trans (Nat.le_succ i))) hinv.high_compatible hinv.fprov hinv.raw_transfer hod

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3040; plan RE-BIND D5 O2; ruling R3.
DC: SAME the service step, from the successor F provenance, raw transfer and
opening cut. Producer: healing_postReset_service_step_at at i + 1; cone from that cut. -/
theorem healing_postReset_serviceStep₂
    (mono : RMonoAll p c E rho)
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (i : Nat) :
    PostResetServiceStep₂ p c E rho w i := by
  rw [PostResetServiceStep₂_def]
  intro _ _ _ hfp hraw hcone hod
  exact healing_postReset_service_step_at E rho hrec w hreset cap rowCovered mono writes
    (i + 1) (fun _ hv => postResetConeAt_of_cut p c E rho w hcone hv) hfp hraw hod

end JointSteps

end AvailableChain.FGSA.Run
end
